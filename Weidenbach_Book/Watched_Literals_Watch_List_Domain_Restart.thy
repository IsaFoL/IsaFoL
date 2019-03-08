theory Watched_Literals_Watch_List_Domain_Restart
  imports Watched_Literals.Watched_Literals_Watch_List_Domain Watched_Literals_Watch_List_Restart
begin

lemma cdcl_twl_restart_get_all_init_clss:
  assumes \<open>cdcl_twl_restart S T\<close>
  shows \<open>get_all_init_clss T = get_all_init_clss S\<close>
  using assms by (induction rule: cdcl_twl_restart.induct) auto

lemma rtranclp_cdcl_twl_restart_get_all_init_clss:
  assumes \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close>
  shows \<open>get_all_init_clss T = get_all_init_clss S\<close>
  using assms by (induction rule: rtranclp_induct) (auto simp: cdcl_twl_restart_get_all_init_clss)


text \<open>As we have a specialised version of \<^term>\<open>correct_watching\<close>, we defined a special version for
the inclusion of the domain:\<close>

definition all_init_lits :: \<open>(nat, 'v literal list \<times> bool) fmap \<Rightarrow> 'v literal multiset multiset \<Rightarrow>
   'v literal multiset\<close> where
  \<open>all_init_lits S NUE = all_lits_of_mm ((\<lambda>C. mset C) `# init_clss_lf S + NUE)\<close>

abbreviation all_init_lits_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal multiset\<close> where
  \<open>all_init_lits_st S \<equiv> all_init_lits (get_clauses_wl S) (get_unit_init_clss_wl S)\<close>

definition all_init_atms :: \<open>_ \<Rightarrow> _ \<Rightarrow> 'v multiset\<close> where
  \<open>all_init_atms N NUE = atm_of `# all_init_lits N NUE\<close>

declare all_init_atms_def[symmetric, simp]

lemma all_init_atms_alt_def:
  \<open>set_mset (all_init_atms N NE) = atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE\<close>
  unfolding all_init_atms_def all_init_lits_def
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff
      all_lits_of_mm_def atms_of_ms_def image_UN
      atms_of_def
    dest!: multi_member_split[of \<open>(_, _)\<close> \<open>ran_m N\<close>]
    dest: multi_member_split atm_of_lit_in_atms_of
    simp del: set_image_mset)

abbreviation all_init_atms_st :: \<open>'v twl_st_wl \<Rightarrow> 'v multiset\<close> where
  \<open>all_init_atms_st S \<equiv> atm_of `# all_init_lits_st S\<close>

definition blits_in_\<L>\<^sub>i\<^sub>n' :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>blits_in_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S). \<forall>(i, K, b) \<in> set (watched_by S L). K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S))\<close>

definition literals_are_\<L>\<^sub>i\<^sub>n' :: \<open>nat multiset \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' \<A> S \<equiv>
     is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm ((\<lambda>C. mset (fst C)) `# init_clss_l (get_clauses_wl S)
        + get_unit_init_clss_wl S)) \<and>
     blits_in_\<L>\<^sub>i\<^sub>n' S\<close>

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<B>)\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def \<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma literals_are_\<L>\<^sub>i\<^sub>n'_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n' \<A> S = literals_are_\<L>\<^sub>i\<^sub>n' \<B> S\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma literals_are_\<L>\<^sub>i\<^sub>n_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> S = literals_are_\<L>\<^sub>i\<^sub>n \<B> S\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff:
  assumes
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs xa\<close>
  shows
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' \<A> S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> (is ?A)
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> (is ?B)
    \<open>set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close> (is ?C)
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
  have all_init_lits_alt_def: \<open>all_lits_of_mm
       ({#mset (fst C). C \<in># init_clss_l (get_clauses_wl S)#} +
        get_unit_init_clss_wl S) = all_init_lits_st S\<close>
    by (auto simp: all_init_lits_def)

  have H: \<open>set_mset
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
  show A: \<open>literals_are_\<L>\<^sub>i\<^sub>n' \<A> S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for \<A>
  proof -
    have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A>
       (all_lits_of_mm
	 ({#mset C. C \<in># init_clss_lf (get_clauses_wl S)#} +
	  get_unit_init_clss_wl S)) \<longleftrightarrow>
      is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A>
       (all_lits_of_mm
	 ({#mset (fst C). C \<in># ran_m (get_clauses_wl S)#} +
	  get_unit_clauses_wl S))\<close>
      using H unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
    moreover have \<open>set_mset \<A>' = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> if \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<A>'\<close> for \<A>'
      unfolding that[unfolded is_\<L>\<^sub>a\<^sub>l\<^sub>l_def]
      by auto
    moreover have \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> if \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_st S)\<close>
      for \<A> S
      unfolding that[unfolded is_\<L>\<^sub>a\<^sub>l\<^sub>l_def]
      using \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) = set_mset (all_lits_st S)\<close> is_\<L>\<^sub>a\<^sub>l\<^sub>l_all_lits_st_\<L>\<^sub>a\<^sub>l\<^sub>l(1) that by blast
    moreover have \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
      if \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_init_lits_st S)\<close> for \<A> S
      unfolding that[unfolded is_\<L>\<^sub>a\<^sub>l\<^sub>l_def]
      by (metis \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) = set_mset (all_init_lits_st S)\<close> all_init_lits_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_\<L>\<^sub>a\<^sub>l\<^sub>l_rewrite that)
    ultimately show ?thesis
      using Sx x_xa unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_\<L>\<^sub>i\<^sub>n'_def
	literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def
	all_init_lits_def[symmetric] all_lits_def[symmetric] all_init_lits_alt_def
      by (auto 5 5 dest: multi_member_split)
  qed
  show C: ?C
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_\<L>\<^sub>i\<^sub>n'_def
      literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_atms_def all_init_atms_def
      all_init_lits_def all_lits_def all_init_lits_alt_def
    by (auto simp: H)

  show ?B
    by (subst A)
     (rule literals_are_\<L>\<^sub>i\<^sub>n_cong[OF C])
qed

lemma cdcl_twl_restart_is_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    ST: \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close> and
    struct_invs_S: \<open>twl_struct_invs S\<close> and
    L: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (clauses (get_clauses S) + unit_clss S))\<close>
  shows  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (clauses (get_clauses T) + unit_clss T))\<close>
proof -
  have \<open>twl_struct_invs T\<close>
    using rtranclp_cdcl_twl_restart_twl_struct_invs[OF ST struct_invs_S] .
  then have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>?thesis \<longleftrightarrow> is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (get_all_init_clss T))\<close>
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
    then have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (get_all_init_clss S))\<close>
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
    L: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (get_all_init_clss S))\<close>
  shows  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (get_all_init_clss T))\<close>
proof -
  have \<open>twl_struct_invs T\<close>
    using rtranclp_cdcl_twl_restart_twl_struct_invs[OF ST struct_invs_S] .
  then have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>?thesis \<longleftrightarrow> is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm (get_all_init_clss T))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
    by (cases T)
      (auto simp: cdcl\<^sub>W_restart_mset_state)
  moreover have \<open>get_all_init_clss T = get_all_init_clss S\<close>
    using rtranclp_cdcl_twl_restart_get_all_init_clss[OF ST] .
  then show ?thesis
    using L
    by argo
qed

definition remove_all_annot_true_clause_imp_wl_D_inv
  :: \<open>nat twl_st_wl \<Rightarrow> _ \<Rightarrow> nat \<times> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_inv S xs = (\<lambda>(i, T).
     remove_all_annot_true_clause_imp_wl_inv S xs (i, T) \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T \<and>
     all_init_atms_st S = all_init_atms_st T)\<close>

definition remove_all_annot_true_clause_imp_wl_D_pre
  :: \<open>nat multiset \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_pre \<A> L S \<longleftrightarrow> (L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> literals_are_\<L>\<^sub>i\<^sub>n' \<A> S)\<close>

definition remove_all_annot_true_clause_imp_wl_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl_D = (\<lambda>L S. do {
    ASSERT(remove_all_annot_true_clause_imp_wl_D_pre (all_init_atms_st S)
      L S);
    let xs = get_watched_wl S L;
    (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, T).
        remove_all_annot_true_clause_imp_wl_D_inv S xs
          (i, T)\<^esup>
      (\<lambda>(i, T). i < length xs)
      (\<lambda>(i, T). do {
        ASSERT(i < length xs);
        let (C, _ , _) = xs ! i;
        if C \<in># dom_m (get_clauses_wl T) \<and> length ((get_clauses_wl T) \<propto> C) \<noteq> 2
        then do {
          T \<leftarrow> remove_all_annot_true_clause_one_imp_wl (C, T);
          RETURN (i+1, T)
        }
        else
          RETURN (i+1, T)
      })
      (0, S);
    RETURN T
  })\<close>

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_init_itself[iff]:
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms x1h x2h) (all_init_lits x1h x2h)\<close>
  unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by (auto simp: all_init_lits_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
    in_all_lits_of_mm_ain_atms_of_iff all_init_atms_def)

lemma literals_are_\<L>\<^sub>i\<^sub>n'_alt_def: \<open>literals_are_\<L>\<^sub>i\<^sub>n' \<A> S \<longleftrightarrow>
     is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_init_lits (get_clauses_wl S) (get_unit_init_clss_wl S)) \<and>
     blits_in_\<L>\<^sub>i\<^sub>n' S\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def
  by auto

lemma remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp:
  \<open>(uncurry remove_all_annot_true_clause_imp_wl_D, uncurry remove_all_annot_true_clause_imp_wl) \<in>
   {(L, L'). L = L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>} \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' \<A> S \<and>
      \<A> = all_init_atms_st S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' \<A> S}\<rangle>nres_rel\<close>
   (is \<open>_ \<in> _ \<rightarrow>\<^sub>f \<langle>?R\<rangle>nres_rel\<close>)
proof -
  have [refine0]:
    \<open>remove_all_annot_true_clause_one_imp_wl (C, S) \<le>
       \<Down> {(S', T). (S', T) \<in> ?R \<and> all_init_atms_st S' = all_init_atms_st S}
        (remove_all_annot_true_clause_one_imp_wl (C', S'))\<close>
    if \<open>(S, S') \<in> ?R\<close> and \<open>(C, C') \<in> Id\<close>
    for S S' C C'
    using that unfolding remove_all_annot_true_clause_one_imp_def
    by (cases S)
      (fastforce simp: init_clss_l_fmdrop_irrelev init_clss_l_fmdrop
         image_mset_remove1_mset_if all_init_lits_def
	 remove_all_annot_true_clause_one_imp_wl_def
	 drop_clause_add_move_init_def
	 literals_are_\<L>\<^sub>i\<^sub>n'_def
	 blits_in_\<L>\<^sub>i\<^sub>n'_def drop_clause_def
         all_init_atms_def
        dest!: multi_member_split[of _ \<open>\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>])

  show ?thesis
    supply [[goals_limit=1]]
    unfolding uncurry_def remove_all_annot_true_clause_imp_wl_D_def
      remove_all_annot_true_clause_imp_wl_def
    apply (intro frefI nres_relI)
    subgoal for x y
      apply (refine_vcg
          WHILEIT_refine[where R = \<open>{((i, S), (i', S')). i = i' \<and> (S, S') \<in> Id \<and>
            literals_are_\<L>\<^sub>i\<^sub>n' \<A> S' \<and> all_init_atms_st (snd x) = all_init_atms_st S}\<close>])
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_pre_def
        by (auto simp flip: all_init_atms_def)
      subgoal by auto
      subgoal
        unfolding remove_all_annot_true_clause_imp_wl_D_inv_def all_init_atms_def
	by (auto simp flip: all_atms_def simp: literals_are_\<L>\<^sub>i\<^sub>n'_alt_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_inv_def literals_are_\<L>\<^sub>i\<^sub>n'_alt_def
        blits_in_\<L>\<^sub>i\<^sub>n_def
	by (auto simp flip: all_atms_def simp: blits_in_\<L>\<^sub>i\<^sub>n'_def)
      subgoal by auto
      subgoal by auto
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_pre_def by auto
      done
    done
qed

definition remove_one_annot_true_clause_one_imp_wl_D_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_D_pre i T \<longleftrightarrow>
     remove_one_annot_true_clause_one_imp_wl_pre i T \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T\<close>

definition remove_one_annot_true_clause_one_imp_wl_D
  :: \<open>nat \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl_D = (\<lambda>i S. do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_D_pre i S);
      ASSERT(is_proped (rev (get_trail_wl S) ! i));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev (get_trail_wl S))!i = Propagated L C);
      ASSERT(Propagated L C \<in> set (get_trail_wl S));
      ASSERT(atm_of L \<in># all_init_atms_st S);
      if C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<in># dom_m (get_clauses_wl S));
	T \<leftarrow> replace_annot_l L C S;
	ASSERT(get_clauses_wl S = get_clauses_wl T);
	T \<leftarrow> remove_and_add_cls_l C T;
        \<comment> \<open>\<^text>\<open>S \<leftarrow> remove_all_annot_true_clause_imp_wl L S;\<close>\<close>
        RETURN (i+1, T)
      }
  })\<close>

lemma remove_one_annot_true_clause_one_imp_wl_pre_in_trail_in_all_init_atms_st:
  assumes
    inv: \<open>remove_one_annot_true_clause_one_imp_wl_D_pre K S\<close> and
    LC_tr: \<open>Propagated L C \<in> set (get_trail_wl S)\<close>
  shows \<open>atm_of L \<in># all_init_atms_st S\<close>
proof -
  obtain x xa where
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    \<open>correct_watching'' S\<close> and
    \<open>twl_list_invs x\<close> and
    \<open>K < length (get_trail_l x)\<close> and
    \<open>twl_list_invs x\<close> and
    \<open>get_conflict_l x = None\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs xa\<close>
    using inv
    unfolding remove_one_annot_true_clause_one_imp_wl_pre_def
      remove_one_annot_true_clause_one_imp_pre_def
      remove_one_annot_true_clause_one_imp_wl_D_pre_def
    by blast
  have \<open>L \<in> lits_of_l (trail (state\<^sub>W_of xa))\<close>
    using LC_tr Sx x_xa
    by (force simp: twl_st twl_st_l twl_st_wl lits_of_def)
  moreover have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of xa)\<close>
    using struct unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  ultimately have \<open>atm_of L \<in> atms_of_mm (init_clss (state\<^sub>W_of xa))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: twl_st twl_st_l twl_st_wl)
  then have \<open>atm_of L \<in> atms_of_mm (mset `# (init_clss_lf (get_clauses_wl S)) +
      get_unit_init_clss_wl S)\<close>
    using Sx x_xa
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: twl_st twl_st_l twl_st_wl)
  then show ?thesis
    by (auto simp: all_init_atms_alt_def)
qed


lemma remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl:
  \<open>(uncurry remove_one_annot_true_clause_one_imp_wl_D,
    uncurry remove_one_annot_true_clause_one_imp_wl) \<in>
   nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> _ \<times>\<^sub>f ?A \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>replace_annot_l L C S \<le>
     \<Down> {(S', T'). (S', T') \<in> ?A \<and> get_clauses_wl S' = get_clauses_wl S} (replace_annot_l L' C' T')\<close>
    if \<open>(L, L') \<in> Id\<close> and \<open>(S, T') \<in> ?A\<close> and \<open>(C, C') \<in> Id\<close> for L L' S T' C C'
    using that
    by (cases S; cases T')
      (fastforce simp: replace_annot_l_def state_wl_l_def
          literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def
        intro: RES_refine)
  have [simp]: \<open>all_init_atms (fmdrop C' x1a) (add_mset (mset (x1a \<propto> C')) x1c) =
     all_init_atms x1a x1c\<close>
     if \<open>irred x1a C'\<close> and \<open>C' \<in># dom_m x1a\<close>
     for C' x1a x1c
    using that
    by (auto simp: all_init_atms_def all_init_lits_def
       image_mset_remove1_mset_if)
  have [simp]: \<open>all_init_atms (fmdrop C' x1a) x1c =
     all_init_atms x1a x1c\<close>
     if \<open>\<not>irred x1a C'\<close>
     for C' x1a x1c
    using that
    by (auto simp: all_init_atms_def all_init_lits_def
       image_mset_remove1_mset_if)
  have [refine0]: \<open>remove_and_add_cls_l C S \<le>\<Down> ?A (remove_and_add_cls_l C' S')\<close>
    if \<open>(C, C') \<in> Id\<close> and \<open>(S, S') \<in> ?A\<close> and
      \<open>C \<in># dom_m (get_clauses_wl S)\<close>
      for C C' S S'
    using that unfolding remove_and_add_cls_l_def
    by refine_rcg
      (auto intro!: RES_refine simp: state_wl_l_def init_clss_l_fmdrop
          literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if
	  init_clss_l_fmdrop_irrelev)
  show ?thesis
    supply [[goals_limit=1]]
    unfolding uncurry_def remove_one_annot_true_clause_one_imp_wl_def
      remove_one_annot_true_clause_one_imp_wl_D_def
    apply (intro frefI nres_relI)
    subgoal for x y
      apply (refine_vcg
        remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp[
	  of \<open>all_init_atms_st (snd x)\<close>,
	  THEN fref_to_Down_curry])
      subgoal unfolding remove_one_annot_true_clause_one_imp_wl_D_pre_def by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal for K S K' S' LC LC' L C L' C'
        by (rule remove_one_annot_true_clause_one_imp_wl_pre_in_trail_in_all_init_atms_st)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
    done
qed

definition remove_one_annot_true_clause_imp_wl_D_inv where
  \<open>remove_one_annot_true_clause_imp_wl_D_inv S = (\<lambda>(i, T).
     remove_one_annot_true_clause_imp_wl_inv S (i, T) \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T)\<close>

definition remove_one_annot_true_clause_imp_wl_D :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl_D = (\<lambda>S. do {
    k \<leftarrow> SPEC(\<lambda>k. (\<exists>M1 M2 K. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_wl S)) \<and>
        count_decided M1 = 0 \<and> k = length M1)
      \<or> (count_decided (get_trail_wl S) = 0 \<and> k = length (get_trail_wl S)));
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_D_inv S\<^esup>
      (\<lambda>(i, S). i < k)
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl_D i S)
      (0, S);
    RETURN S
  })\<close>


lemma remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl:
  \<open>(remove_one_annot_true_clause_imp_wl_D, remove_one_annot_true_clause_imp_wl) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding uncurry_def remove_one_annot_true_clause_imp_wl_D_def
      remove_one_annot_true_clause_imp_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where R=\<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl[THEN fref_to_Down_curry])
    subgoal by auto
    subgoal by auto
    subgoal for S S' k k' T T'
      by (cases T') (auto simp: remove_one_annot_true_clause_imp_wl_D_inv_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition mark_to_delete_clauses_wl_D_pre where
  \<open>mark_to_delete_clauses_wl_D_pre S \<longleftrightarrow>
    mark_to_delete_clauses_wl_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S\<close>

definition mark_to_delete_clauses_wl_D_inv where
  \<open>mark_to_delete_clauses_wl_D_inv = (\<lambda>S xs0 (i, T, xs).
       mark_to_delete_clauses_wl_inv S xs0 (i, T, xs) \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T)\<close>

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
          ASSERT(get_clauses_wl T\<propto>(xs!i)!0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
             (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
              \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T\<propto>(xs!i)) \<noteq> 2);
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
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S \<le> \<Down> Id (collect_valid_indices_wl T)\<close>
    if \<open>(S, T) \<in> Id\<close> for S T
    using that by auto
  have [iff]: \<open>(\<forall>(x::bool) xa. P x xa) \<longleftrightarrow> (\<forall>xa.( P True xa \<and> P False xa))\<close> for P
    by metis
  have in_Lit: \<open>get_clauses_wl T' \<propto> (xs ! j) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T')\<close>
    if
      \<open>(l, l') \<in> nat_rel\<close> and
      rel: \<open>(st, st') \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<times>\<^sub>r
         Id\<close> and
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

    have lits_T': \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T') T'\<close>
      using inv_x unfolding mark_to_delete_clauses_wl_D_inv_def prod.simps st
      by fast
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_init_atms_st T) T\<close>
    proof -
      obtain x xa xb where
        lits_T': \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T') T'\<close> and
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

      have \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_init_atms_st T') T'\<close>
        by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(1)[THEN iffD1,
          OF Ta_y Ta_y' struct' lits_T'])
      then show ?thesis
        using rel by (auto simp: st)
    qed
    then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_init_atms_st T') (mset (get_clauses_wl T' \<propto> (xs ! j)))\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of \<open>xs!i\<close> \<open>T\<close>] rel dom
      by (auto simp: st)
    then show ?thesis
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l) (use le assert rel dom in \<open>auto simp: st\<close>)
  qed
  have final_rel_del:
    \<open>((j, mark_garbage_wl (xs ! j) T', delete_index_and_swap xs j),
         i, mark_garbage_wl (xs' ! i) T, delete_index_and_swap xs' i)
        \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<times>\<^sub>r Id\<close>
    if
      rel: \<open>(st, st') \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) S} \<times>\<^sub>r
        Id\<close> and
      \<open>case st of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>case st' of (i, S, xs') \<Rightarrow> i < length xs'\<close> and
      inv: \<open>mark_to_delete_clauses_wl_D_inv S ys st\<close> and
      \<open>mark_to_delete_clauses_wl_inv S' ys' st'\<close> and
      st: \<open>st' = (i, sT)\<close> \<open>sT = (T, xs)\<close> \<open>st = (j, sT')\<close> \<open>sT' = (T', xs')\<close> and
      dom: \<open>\<not> xs ! j \<notin># dom_m (get_clauses_wl T')\<close> and
      \<open>\<not> xs' ! i \<notin># dom_m (get_clauses_wl T)\<close> and
      le: \<open>0 < length (get_clauses_wl T \<propto> (xs' ! i))\<close> and
      \<open>0 < length (get_clauses_wl T' \<propto> (xs ! j))\<close> and
      \<open>get_clauses_wl T' \<propto> (xs ! j) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T')\<close> and
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
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st (mark_garbage_wl (xs' ! i) T)) (mark_garbage_wl (xs' ! i) T)\<close>
      using can_del inv rel unfolding mark_to_delete_clauses_wl_D_inv_def st mark_garbage_wl_def
      by (cases T)
       (auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_def init_clss_l_fmdrop_irrelev mset_take_mset_drop_mset'
         blits_in_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def)
    then show ?thesis
      using inv rel unfolding st
      by auto
  qed

  show ?thesis
    unfolding uncurry_def mark_to_delete_clauses_wl_D_def mark_to_delete_clauses_wl_def
      collect_valid_indices_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<times>\<^sub>r Id\<close>])
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
    subgoal by auto
    subgoal for S S' xs xs' l l' st st' i T j T' can_del can_del'
      by (rule final_rel_del; assumption?) auto
    subgoal by auto
    subgoal by auto
    done
qed

definition mark_to_delete_clauses_wl_D_post where
  \<open>mark_to_delete_clauses_wl_D_post S T \<longleftrightarrow>
     (mark_to_delete_clauses_wl_post S T \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S)\<close>

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
    \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre S\<close> and
    \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<close> and
    post: \<open>mark_to_delete_clauses_wl_post Sa Ta\<close> and
    \<open>mark_to_delete_clauses_wl_post S T\<close>
  shows \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<close>
proof -
  have lits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st Ta) Ta\<close> and T: \<open>T = Ta\<close>
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

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st Ta) Ta\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(2)[THEN iffD1,
       OF Ta_x Ta_y struct lits_T])
  then show ?thesis
    using lits_T T by auto
qed

lemma mark_to_delete_clauses_wl_pre_lits':
  \<open>(S, T) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<Longrightarrow>
    mark_to_delete_clauses_wl_pre T \<Longrightarrow> mark_to_delete_clauses_wl_D_pre S\<close>
  unfolding mark_to_delete_clauses_wl_D_pre_def mark_to_delete_clauses_wl_pre_def
  apply normalize_goal+
  apply (intro conjI)
  subgoal for U
    by (rule exI[of _ U]) auto
  subgoal for U
    unfolding mark_to_delete_clauses_l_pre_def
    apply normalize_goal+
    by (subst literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(2)[of _ U]) auto
  done

lemma cdcl_twl_full_restart_wl_prog_D_cdcl_twl_restart_wl_prog:
  \<open>(cdcl_twl_full_restart_wl_prog_D, cdcl_twl_full_restart_wl_prog) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding uncurry_def cdcl_twl_full_restart_wl_prog_D_def cdcl_twl_full_restart_wl_prog_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl[THEN fref_to_Down])
    subgoal for S T
      by (rule mark_to_delete_clauses_wl_pre_lits')
    subgoal for S T
      unfolding mark_to_delete_clauses_wl_D_pre_def by blast
    subgoal by auto
    subgoal for x y S Sa
      by (rule cdcl_twl_full_restart_wl_prog_D_final_rel)
    done
qed

definition restart_abs_wl_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_D_pre S brk \<longleftrightarrow>
    (restart_abs_wl_pre S brk \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S)\<close>

definition cdcl_twl_local_restart_wl_D_spec
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
    \<in> [\<lambda>S. restart_abs_wl_D_pre S False]\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<rightarrow>
      \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_D_spec_def cdcl_twl_local_restart_wl_spec_def
      rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def
      literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def all_atms_def[symmetric])
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
    \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<close>
  shows \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<close>
proof -
  have lits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> and T: \<open>S = Sa\<close>
    using assms by auto
  obtain x xa where
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S\<close> and
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

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(2)[THEN iffD2,
       OF S_x x_xa struct lits_T])
  then show ?thesis
    using T by auto
qed

lemma cdcl_twl_restart_wl_D_prog_cdcl_twl_restart_wl_prog:
  \<open>(cdcl_twl_restart_wl_D_prog, cdcl_twl_restart_wl_prog)
    \<in> [\<lambda>S. restart_abs_wl_D_pre S False]\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<rightarrow>
      \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_D_prog_def cdcl_twl_restart_wl_prog_def
    rewatch_clauses_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      cdcl_twl_local_restart_wl_D_spec_cdcl_twl_local_restart_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_D_cdcl_twl_restart_wl_prog[THEN fref_to_Down])
  subgoal by (auto simp: state_wl_l_def)
  subgoal for x y b b'
    by auto
  done

context twl_restart_ops
begin

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
     {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>restart_required_wl x1c x2b \<le> \<Down> Id (restart_required_wl x1a x2)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close> \<open>(x2b, x2) \<in> Id\<close>
    for x1c x1a x2b x2
    using that by auto
  have restart_abs_wl_D_pre: \<open>restart_abs_wl_D_pre x1c x2c\<close>
    if
      \<open>(x, y) \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      pre: \<open>restart_abs_wl_pre x1a x2a\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c
  proof -
    have \<open>restart_abs_wl_pre x1a x2c\<close> and lits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st x1a) x1a\<close>
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
      using pre that literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(1,2)[THEN iffD2,
       OF S_x x_xa struct lits_T]
      unfolding restart_abs_wl_D_pre_def
      by auto
  qed

  show ?thesis
    unfolding uncurry_def restart_prog_wl_D_def restart_prog_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
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

definition cdcl_twl_stgy_restart_abs_wl_D_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_D_inv S0 brk T n \<longleftrightarrow>
    cdcl_twl_stgy_restart_abs_wl_inv S0 brk T n \<and>
    literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T\<close>

definition cdcl_twl_stgy_restart_prog_wl_D
  :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres"
where
  \<open>cdcl_twl_stgy_restart_prog_wl_D S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_D_inv S\<^sub>0 brk T n\<^esup>
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

(*TODO Move and replace*)
theorem cdcl_twl_o_prog_wl_D_spec':
  \<open>(cdcl_twl_o_prog_wl_D, cdcl_twl_o_prog_wl) \<in>
    {(S,S'). (S,S') \<in> Id \<and>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T}\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (rule order_trans)
    apply (rule cdcl_twl_o_prog_wl_D_spec[of "all_atms_st x" x])
     apply (auto simp: prod_rel_def intro: conc_fun_R_mono)
    done
  done

lemma unit_propagation_outer_loop_wl_D_spec':
  shows \<open>(unit_propagation_outer_loop_wl_D, unit_propagation_outer_loop_wl) \<in>
    {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T} \<rightarrow>\<^sub>f
     \<langle>{(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (rule order_trans)
    apply (rule unit_propagation_outer_loop_wl_D_spec[of "all_atms_st x" x])
     apply (auto simp: prod_rel_def intro: conc_fun_R_mono)
    done
  done

lemma cdcl_twl_stgy_restart_prog_wl_D_cdcl_twl_stgy_restart_prog_wl:
  \<open>(cdcl_twl_stgy_restart_prog_wl_D, cdcl_twl_stgy_restart_prog_wl) \<in>
     {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<rangle>nres_rel\<close>
  unfolding uncurry_def cdcl_twl_stgy_restart_prog_wl_D_def
    cdcl_twl_stgy_restart_prog_wl_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      restart_prog_wl_D_restart_prog_wl[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_D_spec'[THEN fref_to_Down]
      unit_propagation_outer_loop_wl_D_spec'[THEN fref_to_Down]
      WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<times>\<^sub>r nat_rel\<close>])
  subgoal by auto
  subgoal unfolding cdcl_twl_stgy_restart_abs_wl_D_inv_def by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done



definition cdcl_twl_stgy_restart_prog_early_wl_D
  :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres"
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl_D S\<^sub>0 = do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, brk, T, n). cdcl_twl_stgy_restart_abs_wl_D_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl_D S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
        (T, n) \<leftarrow> restart_prog_wl_D T n brk;
        ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0::nat twl_st_wl, 0);
    if \<not>brk then do {
      (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_D_inv S\<^sub>0 brk T n\<^esup>
	(\<lambda>(brk, _). \<not>brk)
	(\<lambda>(brk, S, n).
	do {
	  T \<leftarrow> unit_propagation_outer_loop_wl_D S;
	  (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
	  (T, n) \<leftarrow> restart_prog_wl_D T n brk;
	  RETURN (brk, T, n)
	})
	(False, T::nat twl_st_wl, n);
      RETURN T
    }
    else RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_wl_D_cdcl_twl_stgy_restart_prog_early_wl:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl_D, cdcl_twl_stgy_restart_prog_early_wl) \<in>
     {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S}\<rangle>nres_rel\<close>
  unfolding uncurry_def cdcl_twl_stgy_restart_prog_early_wl_D_def
    cdcl_twl_stgy_restart_prog_early_wl_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      restart_prog_wl_D_restart_prog_wl[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_D_spec'[THEN fref_to_Down]
      unit_propagation_outer_loop_wl_D_spec'[THEN fref_to_Down]
      WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and>
         literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<times>\<^sub>r nat_rel\<close>]
      WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and>
        literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S} \<times>\<^sub>r nat_rel\<close>])
  subgoal by auto
  subgoal unfolding  cdcl_twl_stgy_restart_abs_wl_D_inv_def by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal unfolding  cdcl_twl_stgy_restart_abs_wl_D_inv_def by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done


definition cdcl_GC_clauses_pre_wl_D :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_GC_clauses_pre_wl_D S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S \<and>
    cdcl_GC_clauses_pre_wl T
  )\<close>

definition cdcl_GC_clauses_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>cdcl_GC_clauses_wl_D = (\<lambda>(M, N, D, NE, UE, WS, Q). do {
  ASSERT(cdcl_GC_clauses_pre_wl_D (M, N, D, NE, UE, WS, Q));
  let b = True;
  if b then do {
    (N', _) \<leftarrow> SPEC (\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N'') \<and>
      0 \<notin># dom_m N'');
    Q \<leftarrow> SPEC(\<lambda>Q. correct_watching' (M, N', D, NE, UE, WS, Q) \<and>
      blits_in_\<L>\<^sub>i\<^sub>n' (M, N', D, NE, UE, WS, Q));
    RETURN (M, N', D, NE, UE, WS, Q)
  }
  else RETURN (M, N, D, NE, UE, WS, Q)})\<close>

lemma cdcl_GC_clauses_wl_D_cdcl_GC_clauses_wl:
  \<open>(cdcl_GC_clauses_wl_D, cdcl_GC_clauses_wl) \<in> {(S::nat twl_st_wl, S').
       (S, S') \<in> Id \<and>  literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<rightarrow>\<^sub>f \<langle>{(S::nat twl_st_wl, S').
       (S, S') \<in> Id \<and>  literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<rangle>nres_rel\<close>
  unfolding cdcl_GC_clauses_wl_D_def cdcl_GC_clauses_wl_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  subgoal unfolding cdcl_GC_clauses_pre_wl_D_def by blast
  subgoal by (auto simp: state_wl_l_def)
  subgoal by (auto simp: state_wl_l_def)
  subgoal by auto
  subgoal by (auto simp: state_wl_l_def)
  subgoal by (auto simp: state_wl_l_def literals_are_\<L>\<^sub>i\<^sub>n'_def  is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    all_init_atms_def all_init_lits_def
    dest: rtranclp_GC_remap_init_clss_l_old_new)
  subgoal by (auto simp: state_wl_l_def)
  done

definition cdcl_twl_full_restart_wl_D_GC_prog_post :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_D_GC_prog_post S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> Id \<and> (T, T') \<in> Id \<and>
    cdcl_twl_full_restart_wl_GC_prog_post S' T')\<close>

definition mark_to_delete_clauses_wl2_D_inv where
  \<open>mark_to_delete_clauses_wl2_D_inv = (\<lambda>S xs0 (i, T, xs).
       mark_to_delete_clauses_wl2_inv S xs0 (i, T, xs) \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T)\<close>

definition mark_to_delete_clauses_wl2_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl2_D  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_D_pre S);
    xs \<leftarrow> collect_valid_indices_wl S;
    l \<leftarrow> SPEC(\<lambda>_::nat. True);
    (_, S, xs) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl2_D_inv S xs\<^esup>
      (\<lambda>(i, _, xs). i < length xs)
      (\<lambda>(i, T, xs). do {
        if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
          ASSERT(get_clauses_wl T\<propto>(xs!i)!0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
             (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
              \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T\<propto>(xs!i)) \<noteq> 2);
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

lemma mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl2:
  \<open>(mark_to_delete_clauses_wl2_D, mark_to_delete_clauses_wl2) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S \<le> \<Down> Id (collect_valid_indices_wl T)\<close>
    if \<open>(S, T) \<in> Id\<close> for S T
    using that by auto
  have [iff]: \<open>(\<forall>(x::bool) xa. P x xa) \<longleftrightarrow> (\<forall>xa.( P True xa \<and> P False xa))\<close> for P
    by metis
  have in_Lit: \<open>get_clauses_wl T' \<propto> (xs ! j) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T')\<close>
    if
      \<open>(l, l') \<in> nat_rel\<close> and
      rel: \<open>(st, st') \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<times>\<^sub>r
         Id\<close> and
      inv_x: \<open>mark_to_delete_clauses_wl2_D_inv S ys st\<close> and
      \<open>mark_to_delete_clauses_wl2_inv S' ys' st'\<close> and
      dom: \<open>\<not> xs ! j \<notin># dom_m (get_clauses_wl T')\<close> and
      \<open>\<not> xs' ! i \<notin># dom_m (get_clauses_wl T)\<close> and
      assert: \<open>0 < length (get_clauses_wl T \<propto> (xs' ! i))\<close> and
      st: \<open>st' = (i, sT)\<close> \<open>sT = (T, xs)\<close> \<open>st = (j, sT')\<close> \<open>sT' = (T', xs')\<close> and
      le: \<open>case st of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>case st' of (i, S, xs') \<Rightarrow> i < length xs'\<close> and
      \<open>0 < length (get_clauses_wl T' \<propto> (xs ! j))\<close>
    for S S' xs' l l' st st' i T j T' sT xs sT' ys ys'
  proof -

    have lits_T': \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T') T'\<close>
      using inv_x unfolding mark_to_delete_clauses_wl2_D_inv_def prod.simps st
      by fast
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_init_atms_st T) T\<close>
    proof -
      obtain x xa xb where
        lits_T': \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T') T'\<close> and
        Ta_x: \<open>(S, x) \<in> state_wl_l None\<close> and
        Ta_y: \<open>(T', xa) \<in> state_wl_l None\<close> and
        \<open>correct_watching'' S\<close> and
        rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* x xa\<close> and
        list: \<open>twl_list_invs x\<close> and
        x_xb: \<open>(x, xb) \<in> twl_st_l None\<close> and
        struct: \<open>twl_struct_invs xb\<close> and
        confl: \<open>get_conflict_l x = None\<close> and
        upd: \<open>clauses_to_update_l x = {#}\<close>
        using inv_x unfolding mark_to_delete_clauses_wl2_D_inv_def st prod.case
          mark_to_delete_clauses_wl2_inv_def mark_to_delete_clauses_l_inv_def
        by blast


      obtain y where
        Ta_y': \<open>(xa, y) \<in> twl_st_l None\<close>  and
        struct': \<open>twl_struct_invs y\<close>
        using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list confl upd x_xb
          struct] by blast

      have \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_init_atms_st T') T'\<close>
        by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(1)[THEN iffD1,
          OF Ta_y Ta_y' struct' lits_T'])
      then show ?thesis
        using rel by (auto simp: st)
    qed
    then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_init_atms_st T') (mset (get_clauses_wl T' \<propto> (xs ! j)))\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of \<open>xs!i\<close> \<open>T\<close>] rel dom
      by (auto simp: st)
    then show ?thesis
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l) (use le assert rel dom in \<open>auto simp: st\<close>)
  qed
  have final_rel_del:
    \<open>((j, mark_garbage_wl (xs ! j) T', delete_index_and_swap xs j),
         i, mark_garbage_wl (xs' ! i) T, delete_index_and_swap xs' i)
        \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<times>\<^sub>r Id\<close>
    if
      rel: \<open>(st, st') \<in> nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) S} \<times>\<^sub>r
        Id\<close> and
      \<open>case st of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>case st' of (i, S, xs') \<Rightarrow> i < length xs'\<close> and
      inv: \<open>mark_to_delete_clauses_wl2_D_inv S ys st\<close> and
      \<open>mark_to_delete_clauses_wl2_inv S' ys' st'\<close> and
      st: \<open>st' = (i, sT)\<close> \<open>sT = (T, xs)\<close> \<open>st = (j, sT')\<close> \<open>sT' = (T', xs')\<close> and
      dom: \<open>\<not> xs ! j \<notin># dom_m (get_clauses_wl T')\<close> and
      \<open>\<not> xs' ! i \<notin># dom_m (get_clauses_wl T)\<close> and
      le: \<open>0 < length (get_clauses_wl T \<propto> (xs' ! i))\<close> and
      \<open>0 < length (get_clauses_wl T' \<propto> (xs ! j))\<close> and
      \<open>get_clauses_wl T' \<propto> (xs ! j) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T')\<close> and
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
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st (mark_garbage_wl (xs' ! i) T)) (mark_garbage_wl (xs' ! i) T)\<close>
      using can_del inv rel unfolding mark_to_delete_clauses_wl2_D_inv_def st mark_garbage_wl_def
      by (cases T)
       (auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_def init_clss_l_fmdrop_irrelev mset_take_mset_drop_mset'
         blits_in_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def)
    then show ?thesis
      using inv rel unfolding st
      by auto
  qed

  show ?thesis
    unfolding uncurry_def mark_to_delete_clauses_wl2_D_def mark_to_delete_clauses_wl2_def
      collect_valid_indices_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<times>\<^sub>r Id\<close>])
    subgoal
      unfolding mark_to_delete_clauses_wl_D_pre_def by auto
    subgoal by auto
    subgoal for x y xs xsa l la xa x'
      unfolding mark_to_delete_clauses_wl2_D_inv_def by (cases x') auto
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
    subgoal by auto
    subgoal for S S' xs xs' l l' st st' i T j T' can_del can_del'
      by (rule final_rel_del; assumption?) auto
    subgoal by auto
    subgoal by auto
    done
qed

definition cdcl_twl_full_restart_wl_D_GC_prog where
\<open>cdcl_twl_full_restart_wl_D_GC_prog S = do {
    S' \<leftarrow> cdcl_twl_local_restart_wl_spec0 S;
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D S';
    ASSERT(mark_to_delete_clauses_wl_D_pre T);
    U \<leftarrow> mark_to_delete_clauses_wl2_D T;
    V \<leftarrow> cdcl_GC_clauses_wl_D U;
    ASSERT(cdcl_twl_full_restart_wl_D_GC_prog_post S V);
    RETURN V
  }\<close>


lemma cdcl_twl_full_restart_wl_D_GC_prog:
  \<open>(cdcl_twl_full_restart_wl_D_GC_prog, cdcl_twl_full_restart_wl_GC_prog) \<in>
    {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S} \<rightarrow>\<^sub>f
    \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st S) S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>cdcl_twl_local_restart_wl_spec0 x
          \<le> \<Down> ?R (cdcl_twl_local_restart_wl_spec0 y)\<close>
    if \<open>(x, y) \<in> ?R\<close>
    for x y
    using that apply (case_tac x; case_tac y)
    by (auto 5 1 simp: cdcl_twl_local_restart_wl_spec0_def image_iff
         RES_RES_RETURN_RES2 intro!: RES_refine)
      (auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def)
  show ?thesis
    unfolding cdcl_twl_full_restart_wl_D_GC_prog_def cdcl_twl_full_restart_wl_GC_prog_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
      mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl2[THEN fref_to_Down]
      cdcl_GC_clauses_wl_D_cdcl_GC_clauses_wl[THEN fref_to_Down])
    subgoal unfolding mark_to_delete_clauses_wl_D_pre_def by fast
    subgoal unfolding cdcl_twl_full_restart_wl_D_GC_prog_post_def by fast
    done
qed


definition cdcl_GC_clauses_prog_copy_wl_entry
  :: \<open>'v clauses_l \<Rightarrow> 'v watched \<Rightarrow> 'v literal \<Rightarrow>
         'v clauses_l \<Rightarrow> ('v clauses_l \<times> 'v clauses_l) nres\<close>
where
\<open>cdcl_GC_clauses_prog_copy_wl_entry = (\<lambda>N W A N'. do {
    let le = length W;
    (i, N, N') \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, N'). i < le)
      (\<lambda>(i, N, N'). do {
        ASSERT(i < length W);
        let C = fst (W ! i);
        if C \<in># dom_m N then do {
          D \<leftarrow> SPEC(\<lambda>D. D \<notin># dom_m N');
	  RETURN (i+1, fmdrop C N, fmupd D (N \<propto> C, irred N C) N')
        } else RETURN (i+1, N, N')
      }) (0, N, N');
    RETURN (N, N')
  })\<close>

lemma cdcl_GC_clauses_prog_copy_wl_entry:
  assumes \<open>\<exists>m. GC_remap\<^sup>*\<^sup>* (a, b, c) (N0, m, N0') \<and>
	  ran m \<subseteq> set_mset (dom_m N0') \<and>
	  dom m = set_mset (dom_m a) - set_mset (dom_m N0)\<close>
  shows
    \<open>cdcl_GC_clauses_prog_copy_wl_entry N0 W A N0' \<le>
      SPEC(\<lambda>(N, N'). \<exists>m. GC_remap\<^sup>*\<^sup>* (a, b, c) (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  dom m = set_mset (dom_m a) - set_mset (dom_m N))\<close>
proof -
  have [simp]:
    \<open>x \<in># remove1_mset a (dom_m aaa) \<longleftrightarrow> x \<noteq> a \<and> x \<in># dom_m aaa\<close> for x a aaa
    using distinct_mset_dom[of aaa]
    by (cases \<open>a \<in># dom_m aaa\<close>)
      (auto dest!: multi_member_split simp: add_mset_eq_add_mset)

  show ?thesis
    unfolding cdcl_GC_clauses_prog_copy_wl_entry_def
    apply (refine_vcg
      WHILET_rule[where I = \<open>\<lambda>(i, N, N'). \<exists>m. GC_remap\<^sup>*\<^sup>* (a, b, c) (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  dom m = set_mset (dom_m a) - set_mset (dom_m N)\<close> and
	R = \<open>measure (\<lambda>(i, N, N'). length W -i)\<close>])
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal for s aa ba aaa baa x x1 x2 x1a x2a
      apply clarify
      apply (subgoal_tac \<open>\<exists>m'. GC_remap (aaa, m, baa) (fmdrop (fst (W ! aa)) aaa, m',
		fmupd x (the (fmlookup aaa (fst (W ! aa)))) baa) \<and>
	  ran m' \<subseteq> set_mset (dom_m (fmupd x (the (fmlookup aaa (fst (W ! aa)))) baa)) \<and>
	  dom m' = set_mset (dom_m a) - set_mset (dom_m (fmdrop (fst (W ! aa)) aaa))\<close>)
      apply (auto intro: rtranclp.rtrancl_into_rtrancl)
      apply (auto simp: GC_remap.simps)
      apply (rule_tac x= \<open>m(fst (W ! aa) \<mapsto> x)\<close> in exI)
      apply (intro conjI)
      apply (rule_tac x=x in exI)
      apply (rule_tac x= \<open>fst (W ! aa)\<close> in exI)
      apply (force dest: rtranclp_GC_remap_ran_m_no_lost)+
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition cdcl_GC_clauses_prog_single_wl
  :: \<open>'v clauses_l \<Rightarrow> ('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v \<Rightarrow>
         'v clauses_l \<Rightarrow> ('v clauses_l \<times> 'v clauses_l \<times> ('v literal \<Rightarrow> 'v watched)) nres\<close>
where
\<open>cdcl_GC_clauses_prog_single_wl = (\<lambda>N WS A N'. do {
    L \<leftarrow> RES {Pos A, Neg A};
    (N, N') \<leftarrow> cdcl_GC_clauses_prog_copy_wl_entry N (WS L) L N';
    let WS = WS(L := []);
    (N, N') \<leftarrow> cdcl_GC_clauses_prog_copy_wl_entry N (WS (-L)) L N';
    let WS = WS(-L := []);
    RETURN (N, N', WS)
  })\<close>


lemma cdcl_GC_clauses_prog_single_wl:
  assumes \<open>\<exists>m. GC_remap\<^sup>*\<^sup>* (a, b, c) (N0, m, N0') \<and>
	  ran m \<subseteq> set_mset (dom_m N0') \<and>
	  dom m = set_mset (dom_m a) - set_mset (dom_m N0)\<close>
  shows
    \<open>cdcl_GC_clauses_prog_single_wl N0 W A N0' \<le>
      SPEC(\<lambda>(N, N', WS'). \<exists>m. GC_remap\<^sup>*\<^sup>* (a, b, c) (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  dom m = set_mset (dom_m a) - set_mset (dom_m N) \<and>
	  WS' (Pos A) = [] \<and> WS' (Neg A) = [] \<and>
	  (\<forall>L. L \<noteq> Pos A \<longrightarrow> L \<noteq> Neg A \<longrightarrow> W L = WS' L)
	  )\<close>
proof -
  show ?thesis
    unfolding cdcl_GC_clauses_prog_single_wl_def
    apply (refine_vcg
      cdcl_GC_clauses_prog_copy_wl_entry)
    apply(solves \<open>use assms in auto\<close>)
    apply(solves \<open>auto\<close>)
    apply(solves \<open>auto\<close>)
    done
qed


definition cdcl_GC_clauses_prog_wl_inv
  :: \<open>'v multiset \<Rightarrow> 'v clauses_l \<Rightarrow>
    'v multiset \<times> ('v clauses_l \<times> 'v clauses_l \<times> ('v literal \<Rightarrow> 'v watched)) \<Rightarrow> bool\<close>
where
\<open>cdcl_GC_clauses_prog_wl_inv \<A> N0 = (\<lambda>(\<B>, (N, N', WS)). \<B> \<subseteq># \<A> \<and>
  (\<forall>A \<in> set_mset \<A> - set_mset \<B>. (WS (Pos A) = []) \<and> WS (Neg A) = []) \<and>
  (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (N, m, N')\<and>
      ran m \<subseteq> set_mset (dom_m N') \<and>
      dom m = set_mset (dom_m N0) - set_mset (dom_m N)))\<close>

definition cdcl_GC_clauses_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_GC_clauses_prog_wl = (\<lambda>(M, N0, D, NE, UE, Q, WS). do {
    ASSERT(cdcl_GC_clauses_pre_wl (M, N0, D, NE, UE, Q, WS));
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset (all_atms N0 (NE + UE)));
    (_, (N, N', WS)) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_GC_clauses_prog_wl_inv \<A> N0\<^esup>
      (\<lambda>(\<B>, _). \<B> \<noteq> {#})
      (\<lambda>(\<B>, (N, N', WS)). do {
        ASSERT(\<B> \<noteq> {#});
	A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
	(N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_single_wl N WS A N';
	RETURN (remove1_mset A \<B>, (N, N', WS))
      })
      (\<A>, (N0, fmempty, WS));
    RETURN (M, N, D, NE, UE, Q, WS)
  })\<close>


lemma cdcl_GC_clauses_prog_single_wl:
  assumes \<open>((M, N0, D, NE, UE, Q, WS), S) \<in> state_wl_l None \<and>
    correct_watching'' (M, N0, D, NE, UE, Q, WS) \<and> cdcl_GC_clauses_pre S\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N0, D, NE, UE, Q, WS) \<le>
      SPEC(\<lambda>(M, N, D, NE, UE, Q, WS).
         \<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (fmempty, m, N)
	  )\<close>
proof -
  show ?thesis
    supply[[goals_limit=1]]
    unfolding cdcl_GC_clauses_prog_wl_def
    apply (refine_vcg
      WHILEIT_rule[where R = \<open>measure (\<lambda>(\<A>::'v multiset, (_::'v clauses_l, _ ::'v clauses_l,
          _:: 'v literal \<Rightarrow> 'v watched)). size \<A>)\<close>]
      cdcl_GC_clauses_prog_single_wl[of N0 \<open>\<lambda>_. None\<close> fmempty])
    subgoal
      using assms
      unfolding cdcl_GC_clauses_pre_wl_def
      by blast
    subgoal by auto
    subgoal unfolding cdcl_GC_clauses_prog_wl_inv_def by auto
    subgoal by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal for a b aa ba ab bb ac bc ad bd ae be
        x s af bf ag bg ah bh xa xb ai bi aj bj
      using in_remove1_msetI[of _ xa af]
      unfolding cdcl_GC_clauses_prog_wl_inv_def prod.case
      apply (intro conjI ballI)
      prefer 2
      apply (case_tac \<open>A = xa\<close>)
      prefer 2
      apply (case_tac \<open>A = xa\<close>)
      apply auto
       by (metis Diff_iff in_remove1_msetI)
    subgoal
      by (auto dest!: multi_member_split)
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      apply auto
  oops

end

end