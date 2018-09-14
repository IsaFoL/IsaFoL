theory Watched_Literals_Watch_List_Domain_Restart
  imports Watched_Literals.Watched_Literals_Watch_List_Domain Watched_Literals_Watch_List_Restart
begin

locale isasat_restart_ops =
  twl_restart_ops + isasat_input_ops

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

text \<open>As we have a specialised version of \<^term>\<open>correct_watching\<close>, we defined a special version for
the inclusion of the domain:\<close>
definition literals_are_\<L>\<^sub>i\<^sub>n' :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<equiv>
     is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm ((\<lambda>C. mset (fst C)) `# init_clss_l (get_clauses_wl S)
        + get_unit_init_clss_wl S)) \<and>
     blits_in_\<L>\<^sub>i\<^sub>n S\<close>

lemma literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff:
  assumes
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs xa\<close>
  shows  \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n S\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of xa)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>\<And>L. L \<in> atm_of ` lits_of_l (get_trail_wl S) \<Longrightarrow> L \<in> atms_of_ms
      ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m (get_clauses_wl S) \<and> snd a}) \<union>
      atms_of_mm (get_unit_init_clss_wl S)\<close> and
    alien_learned: \<open>atms_of_mm (learned_clss (state\<^sub>W_of xa))
      \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of xa))\<close>
    using Sx x_xa unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp add: twl_st twl_st_l twl_st_wl)

  have \<open>set_mset
     (all_lits_of_mm
       ({#mset (fst C). C \<in># init_clss_l (get_clauses_wl S)#} +
        get_unit_init_clss_wl S)) = set_mset
     (all_lits_of_mm
       ({#mset (fst C). C \<in># ran_m (get_clauses_wl S)#} +
        get_unit_clauses_wl S))\<close>
    apply (subst (2) all_clss_l_ran_m[symmetric])
    using alien_learned Sx x_xa
    unfolding image_mset_union all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def
      twl_st twl_st_l twl_st_wl get_learned_clss_wl_def)
  then have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l
     (all_lits_of_mm
       ({#mset (fst C). C \<in># init_clss_l (get_clauses_wl S)#} +
        get_unit_init_clss_wl S)) \<longleftrightarrow>
    is_\<L>\<^sub>a\<^sub>l\<^sub>l
     (all_lits_of_mm
       ({#mset (fst C). C \<in># ran_m (get_clauses_wl S)#} +
        get_unit_clauses_wl S))\<close>
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by presburger
  then show ?thesis
    using Sx x_xa unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_\<L>\<^sub>i\<^sub>n'_def
      literals_are_\<L>\<^sub>i\<^sub>n_def
    by auto
qed

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


lemma cdcl_twl_restart_is_\<L>\<^sub>a\<^sub>l\<^sub>l':
  assumes
    ST: \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close> and
    struct_invs_S: \<open>twl_struct_invs S\<close> and
    L: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (get_all_init_clss S))\<close>
  shows  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (get_all_init_clss T))\<close>
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
  then show ?thesis
    using L
    by argo
qed

end

context isasat_restart_ops
begin

definition (in isasat_restart_ops) remove_all_annot_true_clause_imp_wl_D_inv
  :: \<open>nat twl_st_wl \<Rightarrow> _ \<Rightarrow> nat \<times> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_inv S xs = (\<lambda>(i, T).
     remove_all_annot_true_clause_imp_wl_inv S xs (i, T) \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>


definition remove_all_annot_true_clause_imp_wl_D_pre
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_pre L S \<longleftrightarrow> (L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

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
        let (C, _ , _) = xs ! i;
        if C \<in># dom_m N
        then do {
          (N, NE) \<leftarrow> remove_all_annot_true_clause_one_imp (C, N, NE);
          RETURN (i+1, N, NE)
        }
        else
          RETURN (i+1, N, NE)
      })
      (0, N0, NE0);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>


lemma remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp:
  \<open>(uncurry remove_all_annot_true_clause_imp_wl_D, uncurry remove_all_annot_true_clause_imp_wl) \<in>
   {(L, L'). L = L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l} \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  have [refine0]:
    \<open>remove_all_annot_true_clause_one_imp S \<le>
       \<Down> {((N, NE), (N', NE')). N = N' \<and> NE = NE'
        \<and> mset `# init_clss_lf (fst (snd S)) + snd (snd S) = mset `# init_clss_lf N + NE'}
        (remove_all_annot_true_clause_one_imp S')\<close>
    if \<open>(S, S') \<in> Id\<close>
    for S S'
    using that unfolding remove_all_annot_true_clause_one_imp_def
    by (cases S) (auto simp: init_clss_l_fmdrop_irrelev init_clss_l_fmdrop image_mset_remove1_mset_if)

  show ?thesis
    supply [[goals_limit=1]]
    unfolding uncurry_def remove_all_annot_true_clause_imp_wl_D_def
      remove_all_annot_true_clause_imp_wl_def
    apply (intro frefI nres_relI)
    apply clarify
    subgoal for L M N0 D NE0 UE Q W L' M' N0' D' NE0' UE' Q' W'
      apply (refine_vcg
          WHILEIT_refine[where R = \<open>{((i, N, NE), (i', N', NE')). i = i' \<and> N=N' \<and>NE=NE' \<and>
            literals_are_\<L>\<^sub>i\<^sub>n' (M, N, D, NE, UE, Q, W)}\<close>])
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_pre_def by force
      subgoal by auto
      subgoal
        unfolding remove_all_annot_true_clause_imp_wl_D_inv_def by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_inv_def literals_are_\<L>\<^sub>i\<^sub>n'_def
        blits_in_\<L>\<^sub>i\<^sub>n_def
        by auto
      subgoal by auto
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_pre_def by auto
      done
    done
qed

definition remove_one_annot_true_clause_one_imp_wl_D_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_D_pre i T \<longleftrightarrow>
     remove_one_annot_true_clause_one_imp_wl_pre i T \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' T\<close>

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
   nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
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
      L: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N0', D', NE0', UE', Q', W')\<close>
    for x1 L' N0' D' NE0' UE' Q' W' M' x2
  proof -
    obtain x xa where
      x: \<open>((M', N0', D', NE0', UE', Q', W'), x) \<in> state_wl_l None\<close> and
      \<open>correct_watching'
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
       apply (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[THEN iffD1])
         apply (rule x)
        apply (rule x_xa)
       apply (rule struct_invs_xa)
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
          (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
    if
      eq': \<open>((L, M, N0, D, NE0, UE, Q, W), L', M', N0', D', NE0', UE', Q', W') \<in> nat_rel \<times>\<^sub>f
        {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
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
      L: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, N0, D, NE0, UE, Q, W)\<close> and
      x: \<open>((M, N0, D, NE0, UE, Q, W), x) \<in> state_wl_l None\<close> and
      \<open>correct_watching' (M, N0, D, NE0, UE, Q, W)\<close> and
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
       apply (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[THEN iffD1])
         apply (rule x)
        apply (rule x_xa)
       apply (rule struct_invs_xa)
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
          image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n_def)
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
     remove_one_annot_true_clause_imp_wl_inv S (i, T) \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

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
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding uncurry_def remove_one_annot_true_clause_imp_wl_D_def
      remove_one_annot_true_clause_imp_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where R=\<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>]
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
  \<open>mark_to_delete_clauses_wl_D_pre S \<longleftrightarrow> mark_to_delete_clauses_wl_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S\<close>

definition mark_to_delete_clauses_wl_D_inv where
  \<open>mark_to_delete_clauses_wl_D_inv = (\<lambda>S xs0 (i, T, xs).
       mark_to_delete_clauses_wl_inv S xs0 (i, T, xs) \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

definition mark_to_delete_clauses_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl_D  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_D_pre S);
    xs \<leftarrow> collect_valid_indices_wl S;
    l \<leftarrow> SPEC(\<lambda>_::nat. True);
    (_, S, xs) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_D_inv S xs\<^esup>
      (\<lambda>(i, _, xs). i < length xs)
      (\<lambda>(i, T, xs). do {
        if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
          ASSERT(get_clauses_wl T\<propto>(xs!i)!0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
             (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
              \<not>irred (get_clauses_wl T) (xs!i));
          ASSERT(i < length xs);
          if can_del
          then
            RETURN (i, mark_garbage_wl (xs!i) T, delete_index_and_swap xs i)
          else
            RETURN (i+1, T, xs)
        }
      })
      (l, S, xs);
    RETURN S
  })\<close>

(* TODO Move *)
lemma (in -) Union_bool_expand: \<open>(\<Union>can_del\<in>{b::bool. P b}. f can_del) =
   ((if P True then f True else {}) \<union> (if P False then f False else {})) \<close>
  apply auto
  apply (case_tac can_del; solves \<open>auto\<close>)
  apply (case_tac can_del; solves \<open>auto\<close>)
  apply (case_tac can_del; solves \<open>auto\<close>)
  apply (case_tac x; solves \<open>auto\<close>)
  done
(* End Move *)

lemma mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl:
  \<open>(mark_to_delete_clauses_wl_D, mark_to_delete_clauses_wl) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S \<le> \<Down> Id (collect_valid_indices_wl T)\<close>
    if \<open>(S, T) \<in> Id\<close> for S T
    using that by auto
  have [iff]: \<open>(\<forall>(x::bool) xa. P x xa) \<longleftrightarrow> (\<forall>xa.( P True xa \<and> P False xa))\<close> for P
    by metis
  have in_Lit: \<open>get_clauses_wl T' \<propto> (xs ! j) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if
      \<open>(l, l') \<in> nat_rel\<close> and
      rel: \<open>(st, st') \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<times>\<^sub>r Id\<close> and
      inv_x: \<open>mark_to_delete_clauses_wl_D_inv S ys st\<close> and
      \<open>mark_to_delete_clauses_wl_inv S' ys' st'\<close> and
      dom: \<open>\<not> xs ! j \<notin># dom_m (get_clauses_wl T')\<close> and
      \<open>\<not> xs' ! i \<notin># dom_m (get_clauses_wl T)\<close> and
      assert: \<open>0 < length (get_clauses_wl T \<propto> (xs' ! i))\<close> and
      st: \<open>st' = (i, sT)\<close> \<open>sT = (T, xs)\<close> \<open>st = (j, sT')\<close> \<open>sT' = (T', xs')\<close> and
      le: \<open>case st of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>case st' of (i, S, xs') \<Rightarrow> i < length xs'\<close> and
      \<open>0 < length (get_clauses_wl T' \<propto> (xs ! j))\<close>
    for S S' xs' l l' st st' i T j T' sT xs sT' ys ys'
  proof -

    have lits_T': \<open>literals_are_\<L>\<^sub>i\<^sub>n' T'\<close>
      using inv_x unfolding mark_to_delete_clauses_wl_D_inv_def prod.simps st
      by fast
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close>
    proof -
      obtain x xa xb where
        lits_T': \<open>literals_are_\<L>\<^sub>i\<^sub>n' T'\<close> and
        Ta_x: \<open>(S, x) \<in> state_wl_l None\<close> and
        Ta_y: \<open>(T', xa) \<in> state_wl_l None\<close> and
        \<open>correct_watching' S\<close> and
        rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* x xa\<close> and
        list: \<open>twl_list_invs x\<close> and
        x_xb: \<open>(x, xb) \<in> twl_st_l None\<close> and
        struct: \<open>twl_struct_invs xb\<close> and
        confl: \<open>get_conflict_l x = None\<close> and
        upd: \<open>clauses_to_update_l x = {#}\<close>
        using inv_x unfolding mark_to_delete_clauses_wl_D_inv_def st prod.case
          mark_to_delete_clauses_wl_inv_def mark_to_delete_clauses_l_inv_def
        by blast


      obtain y where
        Ta_y': \<open>(xa, y) \<in> twl_st_l None\<close>  and
        struct': \<open>twl_struct_invs y\<close>
        using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list confl upd x_xb
          struct] by blast

      have \<open>literals_are_\<L>\<^sub>i\<^sub>n T'\<close>
        by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[THEN iffD1,
          OF Ta_y Ta_y' struct' lits_T'])
      then show ?thesis
        using rel by (auto simp: st)
    qed
    then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl T' \<propto> (xs ! j)))\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of \<open>xs!i\<close> \<open>T\<close>] rel dom
      by (auto simp: st)
    then show ?thesis
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l) (use le assert rel dom in \<open>auto simp: st\<close>)
  qed
  have final_rel_del:
    \<open>((j, mark_garbage_wl (xs ! j) T', delete_index_and_swap xs j),
         i, mark_garbage_wl (xs' ! i) T, delete_index_and_swap xs' i)
        \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<times>\<^sub>r Id\<close>
    if
      rel: \<open>(st, st') \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<times>\<^sub>r Id\<close> and
      \<open>case st of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>case st' of (i, S, xs') \<Rightarrow> i < length xs'\<close> and
      inv: \<open>mark_to_delete_clauses_wl_D_inv S ys st\<close> and
      \<open>mark_to_delete_clauses_wl_inv S' ys' st'\<close> and
      st: \<open>st' = (i, sT)\<close> \<open>sT = (T, xs)\<close> \<open>st = (j, sT')\<close> \<open>sT' = (T', xs')\<close> and
      dom: \<open>\<not> xs ! j \<notin># dom_m (get_clauses_wl T')\<close> and
      \<open>\<not> xs' ! i \<notin># dom_m (get_clauses_wl T)\<close> and
      le: \<open>0 < length (get_clauses_wl T \<propto> (xs' ! i))\<close> and
      \<open>0 < length (get_clauses_wl T' \<propto> (xs ! j))\<close> and
      \<open>get_clauses_wl T' \<propto> (xs ! j) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      \<open>(can_del, can_del') \<in> bool_rel\<close> and
      can_del: \<open>can_del
      \<in> {b. b \<longrightarrow>
            Propagated (get_clauses_wl T' \<propto> (xs ! j) ! 0) (xs ! j)
            \<notin> set (get_trail_wl T') \<and>
            \<not> irred (get_clauses_wl T') (xs ! j)}\<close> and
      \<open>can_del'
      \<in> {b. b \<longrightarrow>
            Propagated (get_clauses_wl T \<propto> (xs' ! i) ! 0) (xs' ! i)
            \<notin> set (get_trail_wl T) \<and>
            \<not> irred (get_clauses_wl T) (xs' ! i)}\<close> and
      i_le: \<open>i < length xs'\<close> and
      \<open>j < length xs\<close> and
      [simp]: \<open>can_del\<close> and
      [simp]: \<open>can_del'\<close>
    for S S' xs xs' l l' st st' i T j T' can_del can_del' sT sT' ys ys'
  proof -
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n' (mark_garbage_wl (xs' ! i) T)\<close>
      using can_del inv rel unfolding mark_to_delete_clauses_wl_D_inv_def st mark_garbage_wl_def
      by (cases T)
       (auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_def init_clss_l_fmdrop_irrelev mset_take_mset_drop_mset'
         blits_in_\<L>\<^sub>i\<^sub>n_def)
    then show ?thesis
      using inv rel unfolding st
      by auto
  qed

  show ?thesis
    unfolding uncurry_def mark_to_delete_clauses_wl_D_def mark_to_delete_clauses_wl_def
      collect_valid_indices_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
      remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl[THEN fref_to_Down_curry]
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<times>\<^sub>r Id\<close>])
    subgoal
      unfolding mark_to_delete_clauses_wl_D_pre_def by auto
    subgoal by auto
    subgoal for x y xs xsa l la xa x'
      unfolding mark_to_delete_clauses_wl_D_inv_def by (cases x') auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S S' xs xs' l l' st st' i T j T'
      by (rule in_Lit; assumption?) auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S S' xs xs' l l' st st' i T j T' can_del can_del'
      by (rule final_rel_del; assumption?) auto
    subgoal by auto
    subgoal by auto
    done
qed

(*

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
     (rewatch_clauses_prog_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

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
      } else RETURN(i+1, W)
    })
    (0, W0);
  RETURN (M, N, D, NE, UE, Q, W)
})\<close>


lemma rewatch_clauses_prog_D_rewatch_clauses_prog:
  \<open>(rewatch_clauses_prog_D, rewatch_clauses_prog) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
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
*)

definition mark_to_delete_clauses_wl_D_post where
  \<open>mark_to_delete_clauses_wl_D_post S T \<longleftrightarrow>
     (mark_to_delete_clauses_wl_post S T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition cdcl_twl_full_restart_wl_prog_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>cdcl_twl_full_restart_wl_prog_D S = do {
   \<comment> \<open>\<^text>\<open>S \<leftarrow> remove_one_annot_true_clause_imp_wl_D S;\<close>\<close>
    ASSERT(mark_to_delete_clauses_wl_D_pre S);
    T \<leftarrow> mark_to_delete_clauses_wl_D S;
    ASSERT (mark_to_delete_clauses_wl_post S T);
    RETURN T
  }\<close>

lemma cdcl_twl_full_restart_wl_prog_D_final_rel:
  assumes
    \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre S\<close> and
    \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close> and
    post: \<open>mark_to_delete_clauses_wl_post Sa Ta\<close> and
    \<open>mark_to_delete_clauses_wl_post S T\<close>
  shows \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
proof -
  have lits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n' Ta\<close> and T: \<open>T = Ta\<close>
    using assms by auto
  obtain x xa xb where
    Sa_x: \<open>(Sa, x) \<in> state_wl_l None\<close> and
    Ta_x: \<open>(Ta, xa) \<in> state_wl_l None\<close> and
    corr_S: \<open>correct_watching Sa\<close> and
    corr_T: \<open>correct_watching Ta\<close> and
    x_xb: \<open>(x, xb) \<in> twl_st_l None\<close> and
    rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* x xa\<close> and
    list: \<open>twl_list_invs x\<close> and
    struct: \<open>twl_struct_invs xb\<close> and
    confl: \<open>get_conflict_l x = None\<close> and
    upd: \<open>clauses_to_update_l x = {#}\<close>
    using post unfolding mark_to_delete_clauses_wl_post_def mark_to_delete_clauses_l_post_def
    by blast
  obtain y where
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* x xa\<close> and
    Ta_y: \<open>(xa, y) \<in> twl_st_l None\<close>  and
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* xb y\<close> and
    struct: \<open>twl_struct_invs y\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list confl upd x_xb
       struct]
    by blast

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n Ta\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[THEN iffD1,
       OF Ta_x Ta_y struct lits_T])
  then show ?thesis
    using T by auto
qed


lemma cdcl_twl_full_restart_wl_prog_D_cdcl_twl_restart_wl_prog:
  \<open>(cdcl_twl_full_restart_wl_prog_D, cdcl_twl_full_restart_wl_prog) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding uncurry_def cdcl_twl_full_restart_wl_prog_D_def cdcl_twl_full_restart_wl_prog_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
      remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl[THEN fref_to_Down_curry]
      mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl[THEN fref_to_Down])
    subgoal for S T
      unfolding mark_to_delete_clauses_wl_D_pre_def by blast
    subgoal by auto
    subgoal for x y S Sa
      by (rule cdcl_twl_full_restart_wl_prog_D_final_rel)
    done
qed

definition (in isasat_input_ops) restart_abs_wl_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_D_pre S brk \<longleftrightarrow>
    (restart_abs_wl_pre S brk \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition (in isasat_input_ops) cdcl_twl_local_restart_wl_D_spec
  :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>cdcl_twl_local_restart_wl_D_spec = (\<lambda>(M, N, D, NE, UE, Q, W). do {
      ASSERT(restart_abs_wl_D_pre (M, N, D, NE, UE, Q, W) False);
      (M, Q') \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#}) \<or> (M' = M \<and> Q' = Q));
      RETURN (M, N, D, NE, UE, Q', W)
   })\<close>

lemma cdcl_twl_local_restart_wl_D_spec_cdcl_twl_local_restart_wl_spec:
  \<open>(cdcl_twl_local_restart_wl_D_spec, cdcl_twl_local_restart_wl_spec)
    \<in> [\<lambda>S. restart_abs_wl_D_pre S False]\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>
      \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -

  show ?thesis
    unfolding cdcl_twl_local_restart_wl_D_spec_def cdcl_twl_local_restart_wl_spec_def
      rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def
      literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)
    done
qed

definition cdcl_twl_restart_wl_D_prog where
\<open>cdcl_twl_restart_wl_D_prog S = do {
   b \<leftarrow> SPEC(\<lambda>_. True);
   if b then cdcl_twl_local_restart_wl_D_spec S else cdcl_twl_full_restart_wl_prog_D S
  }\<close>

lemma cdcl_twl_restart_wl_D_prog_final_rel:
  assumes
    post: \<open>restart_abs_wl_D_pre Sa b\<close> and
    \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
  shows \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
proof -
  have lits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and T: \<open>S = Sa\<close>
    using assms by auto
  obtain x xa where
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
    S_x: \<open>(S, x) \<in> state_wl_l None\<close> and
    \<open>correct_watching S\<close> and
    x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs xa\<close> and
    list: \<open>twl_list_invs x\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>twl_stgy_invs xa\<close> and
    confl: \<open>\<not>b \<longrightarrow> get_conflict xa = None\<close>
    using post unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def T by blast

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[THEN iffD2,
       OF S_x x_xa struct lits_T])
  then show ?thesis
    using T by auto
qed

lemma cdcl_twl_restart_wl_D_prog_cdcl_twl_restart_wl_prog:
  \<open>(cdcl_twl_restart_wl_D_prog, cdcl_twl_restart_wl_prog)
    \<in> [\<lambda>S. restart_abs_wl_D_pre S False]\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>
      \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_D_prog_def cdcl_twl_restart_wl_prog_def
    rewatch_clauses_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      cdcl_twl_local_restart_wl_D_spec_cdcl_twl_local_restart_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_D_cdcl_twl_restart_wl_prog[THEN fref_to_Down])
  subgoal by (auto simp: state_wl_l_def)
  subgoal by (auto simp: state_wl_l_def)
  subgoal for x y b b'
    by (rule cdcl_twl_restart_wl_D_prog_final_rel)
  done

definition restart_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat twl_st_wl \<times> nat) nres" where
  \<open>restart_prog_wl_D S n brk = do {
     ASSERT(restart_abs_wl_D_pre S brk);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_D_prog S;
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>


lemma restart_prog_wl_D_restart_prog_wl:
  \<open>(uncurry2 restart_prog_wl_D, uncurry2 restart_prog_wl) \<in>
     {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>restart_required_wl x1c x2b \<le> \<Down> Id (restart_required_wl x1a x2)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close> \<open>(x2b, x2) \<in> Id\<close>
    for x1c x1a x2b x2
    using that by auto
  have restart_abs_wl_D_pre: \<open>restart_abs_wl_D_pre x1c x2c\<close>
    if
      \<open>(x, y) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      pre: \<open>restart_abs_wl_pre x1a x2a\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c
  proof -
    have \<open>restart_abs_wl_pre x1a x2c\<close> and lits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n x1a\<close>
      using pre that
      unfolding restart_abs_wl_D_pre_def
      by auto
    then obtain xa x where
        S_x: \<open>(x1a, x) \<in> state_wl_l None\<close> and
        \<open>correct_watching x1a\<close> and
        x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
        struct: \<open>twl_struct_invs xa\<close> and
        list: \<open>twl_list_invs x\<close> and
        \<open>clauses_to_update_l x = {#}\<close> and
        \<open>twl_stgy_invs xa\<close> and
        \<open>\<not> x2c \<longrightarrow> get_conflict xa = None\<close>
      unfolding restart_abs_wl_pre_def restart_abs_l_pre_def restart_prog_pre_def by blast

    show ?thesis
      using pre that literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[THEN iffD2,
       OF S_x x_xa struct lits_T]
      unfolding restart_abs_wl_D_pre_def
      by auto
  qed

  show ?thesis
    unfolding uncurry_def restart_prog_wl_D_def restart_prog_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
      cdcl_twl_restart_wl_D_prog_cdcl_twl_restart_wl_prog[THEN fref_to_Down])
    subgoal by (rule restart_abs_wl_D_pre)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition cdcl_twl_stgy_restart_prog_wl_D
  :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres"
where
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

lemma (in isasat_restart_ops) cdcl_twl_stgy_restart_prog_wl_D_cdcl_twl_stgy_restart_prog_wl:
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

end