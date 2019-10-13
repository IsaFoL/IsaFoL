theory Watched_Literals_Watch_List_Restart
  imports Watched_Literals_List_Restart Watched_Literals_Watch_List
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

text \<open>To ease the proof, we introduce the following ``alternative'' definitions, that only considers
  variables that are present in the initial clauses (which are never deleted from the set of
  clauses, but only moved to another component).
\<close>
fun correct_watching' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching' (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm (mset `# init_clss_lf N + NE).
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             b \<longrightarrow> i \<in># dom_m N) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

fun correct_watching'' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching'' (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm (mset `# init_clss_lf N + NE).
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

lemma correct_watching'_correct_watching'': \<open>correct_watching' S \<Longrightarrow> correct_watching'' S\<close>
  by (cases S) auto

declare correct_watching'.simps[simp del] correct_watching''.simps[simp del]

definition blits_in_\<L>\<^sub>i\<^sub>n' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>blits_in_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow>
    (\<forall>L \<in># all_init_lits_st S.
      \<forall>(i, K, b) \<in> set (watched_by S L). K \<in># all_init_lits_st S)\<close>

definition literals_are_\<L>\<^sub>i\<^sub>n' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<equiv>
    set_mset (all_lits_of_mm (mset `# learned_clss_lf (get_clauses_wl S) + get_unit_learned_clss_wl S)) \<subseteq>
      set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)) \<and>
     blits_in_\<L>\<^sub>i\<^sub>n' S\<close>

abbreviation all_init_atms_st :: \<open>'v twl_st_wl \<Rightarrow> 'v multiset\<close> where
  \<open>all_init_atms_st S \<equiv> all_init_atms (get_clauses_wl S) (get_unit_init_clss_wl S)\<close>

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NU)) = set_mset (all_init_lits N NU)\<close>
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S)) = set_mset (all_init_lits_st S)\<close>
  by (simp_all add: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_init_atms_def all_init_lits_def)

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
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> (is ?A)
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> (is ?B)
    \<open>set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close> (is ?C) and
    \<open>set_mset (all_init_lits_st S) = set_mset (all_lits_st S)\<close> (is ?D)
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
    by (auto simp : in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def
      twl_st twl_st_l twl_st_wl get_learned_clss_wl_def)

  show A: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> for \<A>
  proof -
    have sub: \<open>set_mset
      (all_lits_of_mm
        (mset `# learned_clss_lf (get_clauses_wl S) +
         get_unit_learned_clss_wl S))
     \<subseteq> set_mset (all_init_lits_st S) \<longleftrightarrow>
     is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S) (all_lits_st S)\<close>
     unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_def all_lits_def
     apply (subst (2) all_clss_l_ran_m[symmetric])
     unfolding image_mset_union get_unit_clauses_wl_alt_def  \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms
     by (auto simp: all_lits_of_mm_union all_init_lits_def)

    have 1: \<open>set_mset (all_init_lits_st S) = set_mset (all_lits_st S)\<close>
      by (metis H all_init_lits_alt_def all_lits_def)
    then show ?thesis
      unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def
	literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def sub
	all_init_lits_def[symmetric] all_lits_def[symmetric]
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_def[symmetric] all_init_atms_def[symmetric]
      by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
   qed

  show C: ?C
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_\<L>\<^sub>i\<^sub>n'_def
      literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_atms_def all_init_atms_def
      all_init_lits_def all_lits_def all_init_lits_alt_def
    by (auto simp: H)

  show ?B
    apply (subst A)
    ..
  show ?D
    by (metis H all_init_lits_alt_def all_lits_def)
qed


lemma GC_remap_all_init_atmsD:
  \<open>GC_remap (N, x, m) (N', x', m') \<Longrightarrow> all_init_atms N NE + all_init_atms m NE  = all_init_atms N' NE  + all_init_atms m' NE\<close>
  by (induction rule: GC_remap.induct[split_format(complete)])
    (auto simp: all_init_atms_def all_init_lits_def init_clss_l_fmdrop_if
       init_clss_l_fmupd_if image_mset_remove1_mset_if
    simp del: all_init_atms_def[symmetric]
    simp flip: image_mset_union all_lits_of_mm_add_mset all_lits_of_mm_union)

lemma rtranclp_GC_remap_all_init_atmsD:
  \<open>GC_remap\<^sup>*\<^sup>* (N, x, m) (N', x', m') \<Longrightarrow> all_init_atms N NE + all_init_atms m NE  = all_init_atms N' NE  + all_init_atms m' NE\<close>
  by (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
    (auto dest: GC_remap_all_init_atmsD)

lemma rtranclp_GC_remap_all_init_atms:
  \<open>GC_remap\<^sup>*\<^sup>* (x1a, Map.empty, fmempty) (fmempty, m, x1ad) \<Longrightarrow> all_init_atms x1ad NE = all_init_atms x1a NE\<close>
  by (auto dest!: rtranclp_GC_remap_all_init_atmsD[of _ _ _ _ _ _ NE])

lemma GC_remap_all_init_lits:
  \<open>GC_remap (N, m, new) (N', m', new') \<Longrightarrow> all_init_lits N NE + all_init_lits new NE = all_init_lits N' NE + all_init_lits new' NE\<close>
  by (induction rule: GC_remap.induct[split_format(complete)])
    (case_tac \<open>irred N C\<close> ; auto simp: all_init_lits_def init_clss_l_fmupd_if image_mset_remove1_mset_if
    simp flip: all_lits_of_mm_union)

lemma rtranclp_GC_remap_all_init_lits:
  \<open>GC_remap\<^sup>*\<^sup>* (N, m, new) (N', m', new') \<Longrightarrow> all_init_lits N NE + all_init_lits new NE = all_init_lits N' NE + all_init_lits new' NE\<close>
  by (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
    (auto dest: GC_remap_all_init_lits)

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

definition remove_all_annot_true_clause_imp_wl_inv
  :: \<open>'v twl_st_wl \<Rightarrow> _ \<Rightarrow> nat \<times> 'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_inv S xs = (\<lambda>(i, T).
     correct_watching'' S \<and> correct_watching'' T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' T \<and>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
        remove_all_annot_true_clause_imp_inv S' xs (i, T')))\<close>

definition remove_all_annot_true_clause_one_imp_wl
where
\<open>remove_all_annot_true_clause_one_imp_wl = (\<lambda>(C, S). do {
      if C \<in># dom_m (get_clauses_wl S) then
        if irred (get_clauses_wl S) C
        then RETURN (drop_clause_add_move_init S C)
        else RETURN (drop_clause S C)
      else do {
        RETURN S
      }
  })\<close>

definition remove_all_annot_true_clause_imp_wl
  :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl = (\<lambda>L S. do {
    let xs = get_watched_wl S L;
    (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, T). remove_all_annot_true_clause_imp_wl_inv S xs (i, T)\<^esup>
      (\<lambda>(i, T). i < length xs)
      (\<lambda>(i, T). do {
        ASSERT(i < length xs);
        let (C, _, _) = xs!i;
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



lemma reduce_dom_clauses_fmdrop:
  \<open>reduce_dom_clauses N0 N \<Longrightarrow> reduce_dom_clauses N0 (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def distinct_mset_remove1_All)


lemma correct_watching_fmdrop:
  assumes
    irred: \<open>\<not> irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching' (M', N, D, NE, UE, Q, W)\<close> and
    C2: \<open>length (N \<propto> C) \<noteq> 2\<close> and
    blit: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching' (M, fmdrop C N, D, NE, UE, Q, W)\<close> and
     \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, Q, W)\<close>
proof -
  have
    Hdist: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
         correctly_marked_as_binary N (i, K, b)\<close> and
    H1': \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> b \<Longrightarrow>  i \<in># dom_m N\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching'.simps clause_to_update_def
    by fast+
  have 1: \<open>{#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (fmdrop C N \<propto> Ca))#} =
    {#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule filter_mset_cong2)
      using distinct_mset_dom[of N] C irred
    by (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond dest: all_lits_of_mm_diffD
        dest: multi_member_split)
  have 2: \<open>remove1_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#} =
     removeAll_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule distinct_mset_remove1_All)
    using distinct_mset_dom[of N]
    by (auto intro: distinct_mset_filter)
  have [simp]: \<open>filter_mset (\<lambda>i. i \<in># remove1_mset C (dom_m N)) A  =
    removeAll_mset C (filter_mset (\<lambda>i. i \<in># dom_m N) A)\<close> for A
    by (induction A)
      (auto simp: distinct_mset_remove1_All distinct_mset_dom)
  show  \<open>correct_watching' (M, fmdrop C N, D, NE, UE, Q, W)\<close>
    unfolding correct_watching'.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L using Hdist[of L] distinct_mset_dom[of N]
        H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
	H1'[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>]
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
        H1'[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>]
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L iK
       using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
        H1'[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C2
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L
      using C irred apply -
      unfolding get_clauses_l.simps
      apply (subst 1)
      apply (subst (asm) init_clss_lf_fmdrop_irrelev, assumption)
      by (auto 5 1  simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
        distinct_mset_remove1_All filter_mset_neq_cond 2 H2 dest: all_lits_of_mm_diffD
        dest: multi_member_split)
    done
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, Q, W)\<close>
     using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def
       dest: multi_member_split all_lits_of_mm_diffD)
qed

lemma correct_watching''_fmdrop:
  assumes
    irred: \<open>\<not> irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'' (M', N, D, NE, UE, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching'' (M, fmdrop C N, D, NE, UE, Q, W)\<close>and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, Q, W)\<close>
proof -
  have
    Hdist: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching''.simps clause_to_update_def
    by fast+
  have 1: \<open>{#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (fmdrop C N \<propto> Ca))#} =
    {#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule filter_mset_cong2)
      using distinct_mset_dom[of N] C irred
    by (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond dest: all_lits_of_mm_diffD
        dest: multi_member_split)
  have 2: \<open>remove1_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#} =
     removeAll_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule distinct_mset_remove1_All)
    using distinct_mset_dom[of N]
    by (auto intro: distinct_mset_filter)
  have [simp]: \<open>filter_mset (\<lambda>i. i \<in># remove1_mset C (dom_m N)) A  =
    removeAll_mset C (filter_mset (\<lambda>i. i \<in># dom_m N) A)\<close> for A
    by (induction A)
      (auto simp: distinct_mset_remove1_All distinct_mset_dom)
  show  \<open>correct_watching'' (M, fmdrop C N, D, NE, UE, Q, W)\<close>
    unfolding correct_watching''.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L using Hdist[of L] distinct_mset_dom[of N]
        H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L
      using C irred apply -
      unfolding get_clauses_l.simps
      apply (subst 1)
      apply (subst (asm) init_clss_lf_fmdrop_irrelev, assumption)
      by (auto 5 1  simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
        distinct_mset_remove1_All filter_mset_neq_cond 2 H2 dest: all_lits_of_mm_diffD
        dest: multi_member_split)
    done
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, Q, W)\<close>
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def
       dest: multi_member_split all_lits_of_mm_diffD)
qed

lemma correct_watching''_fmdrop':
  assumes
    irred: \<open>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'' (M', N, D, NE, UE, Q, W)\<close>and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching'' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, Q, W)\<close>
proof -
  have
    Hdist: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow>
          K \<in> set (N \<propto> i) \<and> K \<noteq> L\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching''.simps clause_to_update_def
    by blast+
  have 1: \<open>{#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (fmdrop C N \<propto> Ca))#} =
    {#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule filter_mset_cong2)
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>snd iK\<close>] C irred
    by (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond dest: all_lits_of_mm_diffD
        dest: multi_member_split)
  have 2: \<open>remove1_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#} =
     removeAll_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule distinct_mset_remove1_All)
    using distinct_mset_dom[of N]
    by (auto intro: distinct_mset_filter)
  have [simp]: \<open>filter_mset (\<lambda>i. i \<in># remove1_mset C (dom_m N)) A  =
    removeAll_mset C (filter_mset (\<lambda>i. i \<in># dom_m N) A)\<close> for A
    by (induction A)
      (auto simp: distinct_mset_remove1_All distinct_mset_dom)
  show \<open>correct_watching'' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, Q, W)\<close>
    unfolding correct_watching''.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
        Hdist[of L]
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L
      using C irred apply -
      unfolding get_clauses_l.simps
      apply (subst 1)
      by (auto 5 1  simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
        distinct_mset_remove1_All filter_mset_neq_cond 2 H2 dest: all_lits_of_mm_diffD
        dest: multi_member_split)
    done
  have \<open>(N \<propto> C, irred N C) \<in># (init_clss_l N)\<close>
    using assms by (auto simp: ran_m_def dest!: multi_member_split) (metis prod.collapse)
  from multi_member_split[OF this] show \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, Q, W)\<close>
    using distinct_mset_dom[of N]
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if all_lits_of_mm_add_mset
          all_lits_of_mm_union literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def
       dest: multi_member_split all_lits_of_mm_diffD)
qed


lemma correct_watching''_fmdrop'':
  assumes
    irred: \<open>\<not>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'' (M', N, D, NE, UE, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching'' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, Q, W)\<close>
proof -
  have
    Hdist: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and>
          K \<noteq> L\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching''.simps clause_to_update_def
    by blast+
  have 1: \<open>{#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (fmdrop C N \<propto> Ca))#} =
    {#Ca \<in># dom_m (fmdrop C N). L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule filter_mset_cong2)
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>snd iK\<close>] C irred
    by (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond dest: all_lits_of_mm_diffD
        dest: multi_member_split)
  have 2: \<open>remove1_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#} =
     removeAll_mset C {#Ca \<in># dom_m N. L \<in> set (watched_l (N \<propto> Ca))#}\<close> for L
    apply (rule distinct_mset_remove1_All)
    using distinct_mset_dom[of N]
    by (auto intro: distinct_mset_filter)
  have [simp]: \<open>filter_mset (\<lambda>i. i \<in># remove1_mset C (dom_m N)) A  =
    removeAll_mset C (filter_mset (\<lambda>i. i \<in># dom_m N) A)\<close> for A
    by (induction A)
      (auto simp: distinct_mset_remove1_All distinct_mset_dom)
  show  \<open>correct_watching'' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, Q, W)\<close>
    unfolding correct_watching''.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
        Hdist[of L]
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond correctly_marked_as_binary.simps dest: all_lits_of_mm_diffD
        dest: multi_member_split)
      done
    subgoal for L
      using C irred apply -
      unfolding get_clauses_l.simps
      apply (subst 1)
      by (auto 5 1  simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
        distinct_mset_remove1_All filter_mset_neq_cond 2 H2 dest: all_lits_of_mm_diffD
        dest: multi_member_split)
    done

  have \<open>(N \<propto> C, irred N C) \<in># (learned_clss_l N)\<close>
    using assms by (auto simp: ran_m_def dest!: multi_member_split) (metis prod.collapse)
  from multi_member_split[OF this] show \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, Q, W)\<close>
    using distinct_mset_dom[of N]
    using assms by (fastforce simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if all_lits_of_mm_add_mset
          all_lits_of_mm_union literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def
       dest: multi_member_split all_lits_of_mm_diffD)
qed

definition remove_one_annot_true_clause_one_imp_wl_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_pre i T \<longleftrightarrow>
     (\<exists>T'. (T, T') \<in> state_wl_l None \<and>
       remove_one_annot_true_clause_one_imp_pre i T' \<and>
       correct_watching'' T \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

definition replace_annot_wl_pre :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>replace_annot_wl_pre L C S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> L \<in># all_init_lits_st S \<and>
    replace_annot_l_pre L C S' \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    correct_watching'' S)\<close>

definition replace_annot_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>replace_annot_wl L C =
    (\<lambda>(M, N, D, NE, UE, Q, W). do {
      ASSERT(replace_annot_wl_pre L C (M, N, D, NE, UE, Q, W));
      RES {(M', N, D, NE, UE, Q, W)| M'.
       (\<exists>M2 M1 C. M = M2 @ Propagated L C # M1 \<and> M' = M2 @ Propagated L 0 # M1)}
   })\<close>

lemma replace_annot_l_pre_replace_annot_wl_pre: \<open>(((L, C), S), (L', C'), S')
    \<in> Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
      {(S, T).
       (S, T) \<in> state_wl_l None \<and>
       correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<Longrightarrow>
    replace_annot_l_pre L' C' S' \<Longrightarrow>
    replace_annot_wl_pre L C S\<close>
    unfolding replace_annot_wl_pre_def replace_annot_l_pre_alt_def
    unfolding replace_annot_l_pre_def[symmetric]
    by (rule exI[of _ \<open>S'\<close>])
      (auto simp add: all_init_lits_def)

lemma replace_annot_wl_replace_annot_l:
  \<open>(uncurry2 replace_annot_wl, uncurry2 replace_annot_l) \<in>
    Id \<times>\<^sub>f nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
    \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
    unfolding replace_annot_wl_def replace_annot_l_def uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply refine_rcg
    subgoal for a b aa ab ac ad ae af ba ag bb ah ai aj ak al am bc
      by (force intro!: replace_annot_l_pre_replace_annot_wl_pre)
    subgoal
      by (rule RES_refine)
        (fastforce simp: state_wl_l_def literals_are_\<L>\<^sub>i\<^sub>n'_def
          correct_watching''.simps clause_to_update_def blits_in_\<L>\<^sub>i\<^sub>n'_def)
    done

definition remove_one_annot_true_clause_one_imp_wl
  :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i S. do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_pre i S);
      ASSERT(is_proped (rev (get_trail_wl S) ! i));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev (get_trail_wl S))!i = Propagated L C);
      ASSERT(Propagated L C \<in> set (get_trail_wl S));
      ASSERT(L \<in># all_init_lits_st S);
      if C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<in># dom_m (get_clauses_wl S));
	S \<leftarrow> replace_annot_wl L C S;
	S \<leftarrow> remove_and_add_cls_l C S;
        \<comment> \<open>\<^text>\<open>S \<leftarrow> remove_all_annot_true_clause_imp_wl L S;\<close>\<close>
        RETURN (i+1, S)
      }
  })\<close>

lemma
  assumes
      x2_T: \<open>(x2, T) \<in> state_wl_l b\<close> and
      struct: \<open>twl_struct_invs U\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l b'\<close>
  shows
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail_init:
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_init_atms_st x2) (get_trail_wl x2)\<close>
     (is \<open>?trail\<close>)
proof -
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of U)\<close> and
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of U)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close>
   using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
   by fast+

  show lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_init_atms_st x2) (get_trail_wl x2)\<close>
    using alien x2_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def all_atms_def
    by
     (auto 5 2
        simp del: all_clss_l_ran_m union_filter_mset_complement
        simp: twl_st twl_st_l twl_st_wl all_lits_of_mm_union lits_of_def
        convert_lits_l_def image_image in_all_lits_of_mm_ain_atms_of_iff
        get_unit_clauses_wl_alt_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms all_init_lits_def)
qed

lemma remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp:
    \<open>(uncurry remove_one_annot_true_clause_one_imp_wl, uncurry remove_one_annot_true_clause_one_imp)
    \<in> nat_rel \<times>\<^sub>f  {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> _ \<times>\<^sub>f ?A \<rightarrow>\<^sub>f _\<close>)
proof -

  have [refine0]: \<open>remove_and_add_cls_l C S \<le>\<Down> ?A (remove_and_add_cls_l C' S')\<close>
    if \<open>(C, C') \<in> Id\<close> and \<open>(S, S') \<in> ?A\<close>
      for C C' S S'
    using that unfolding remove_and_add_cls_l_def
    by refine_rcg
      (auto intro!: RES_refine simp: state_wl_l_def
       intro: correct_watching''_fmdrop correct_watching''_fmdrop''
          correct_watching''_fmdrop')
  show ?thesis
    unfolding remove_one_annot_true_clause_one_imp_wl_def remove_one_annot_true_clause_one_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg replace_annot_wl_replace_annot_l[THEN fref_to_Down_curry2])
    subgoal for x y unfolding remove_one_annot_true_clause_one_imp_wl_pre_def
      by (rule exI[of _ \<open>snd y\<close>]) auto
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal for x y x1 x2 x1a x2a xa x' x1b x2b x1c x2c
      unfolding remove_one_annot_true_clause_one_imp_wl_pre_def
       remove_one_annot_true_clause_one_imp_pre_def
      apply normalize_goal+

      subgoal for U S T
        using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail_init[of x2a U None T None]
        by (auto simp add: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def image_image
          \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms)
       done
    subgoal by simp
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by simp
    subgoal by (simp add: state_wl_l_def)
    done
qed

definition remove_one_annot_true_clause_imp_wl_inv where
  \<open>remove_one_annot_true_clause_imp_wl_inv S = (\<lambda>(i, T).
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
       correct_watching'' S \<and> correct_watching'' T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
       literals_are_\<L>\<^sub>i\<^sub>n' T \<and>
       remove_one_annot_true_clause_imp_inv S' (i, T')))\<close>

definition remove_one_annot_true_clause_imp_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl = (\<lambda>S. do {
    k \<leftarrow> SPEC(\<lambda>k. (\<exists>M1 M2 K. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_wl S)) \<and>
        count_decided M1 = 0 \<and> k = length M1)
      \<or> (count_decided (get_trail_wl S) = 0 \<and> k = length (get_trail_wl S)));
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_inv S\<^esup>
      (\<lambda>(i, S). i < k)
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl i S)
      (0, S);
    RETURN S
  })\<close>

lemma remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp:
  \<open>(remove_one_annot_true_clause_imp_wl, remove_one_annot_true_clause_imp)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding remove_one_annot_true_clause_imp_wl_def remove_one_annot_true_clause_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>f {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal by force
    subgoal by auto
    subgoal for x y k ka xa x'
      unfolding remove_one_annot_true_clause_imp_wl_inv_def
      apply (subst case_prod_beta)
      apply (rule_tac x=\<open>y\<close> in exI)
      apply (rule_tac x=\<open>snd x'\<close> in exI)
      apply (subst (asm)(18) surjective_pairing)
      apply (subst (asm)(23) surjective_pairing)
      unfolding prod_rel_iff by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition collect_valid_indices_wl :: \<open>'v twl_st_wl \<Rightarrow> nat list nres\<close> where
  \<open>collect_valid_indices_wl S = SPEC (\<lambda>N. True)\<close>

definition mark_to_delete_clauses_wl_inv
  :: \<open>'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> 'v twl_st_wl\<times> nat list  \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_wl_inv = (\<lambda>S xs0 (i, T, xs).
     \<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
      mark_to_delete_clauses_l_inv S' xs0 (i, T', xs) \<and>
      correct_watching' S\<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

definition mark_to_delete_clauses_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_wl_pre S \<longleftrightarrow>
   (\<exists>T. (S, T) \<in> state_wl_l None \<and> mark_to_delete_clauses_l_pre T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition mark_garbage_wl:: \<open>nat \<Rightarrow>  'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>mark_garbage_wl = (\<lambda>C (M, N0, D, NE, UE, WS, Q). (M, fmdrop C N0, D, NE, UE, WS, Q))\<close>

definition mark_to_delete_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_pre S);
    xs \<leftarrow> collect_valid_indices_wl S;
    l \<leftarrow> SPEC(\<lambda>_:: nat. True);
    (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_inv S xs\<^esup>
      (\<lambda>(i, S, xs). i < length xs)
      (\<lambda>(i, T, xs). do {
        if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	  ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
             (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
              \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2);
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

lemma mark_to_delete_clauses_wl_invD1:
  assumes \<open>mark_to_delete_clauses_wl_inv S xs (i, T, ys)\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>0 < length (get_clauses_wl T \<propto> C)\<close>
  shows
    \<open>get_clauses_wl T \<propto> C ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)\<close>
proof -
  have \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
    using assms unfolding mark_to_delete_clauses_wl_inv_def by blast
  then have \<open>get_clauses_wl T \<propto> C ! 0 \<in># all_init_lits_st T\<close>
    using assms(2,3) by (auto dest!: multi_member_split
      simp: ran_m_def all_init_lits_def all_lits_of_mm_add_mset
        in_clause_in_all_lits_of_m literals_are_\<L>\<^sub>i\<^sub>n'_def
        in_clause_in_all_lits_of_m subsetD)
  then show \<open>?thesis\<close>
    by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(1))
qed

lemma mark_to_delete_clauses_wl_mark_to_delete_clauses_l:
  \<open>(mark_to_delete_clauses_wl, mark_to_delete_clauses_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S  \<le> \<Down> Id  (collect_valid_indices S')\<close>
    if \<open>(S, S') \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and>
           mark_to_delete_clauses_wl_pre S}\<close>
    for S S'
    using that by (auto simp: collect_valid_indices_wl_def collect_valid_indices_def)
  have if_inv: \<open>(if A then RETURN P else RETURN Q) = RETURN (if A then P else Q)\<close> for A P Q
    by auto
  have Ball_range[simp]: \<open>(\<forall>x\<in>range f \<union> range g. P x)\<longleftrightarrow>(\<forall>x. P (f x) \<and> P (g x))\<close> for P f g
    by auto
  show ?thesis
    unfolding mark_to_delete_clauses_wl_def mark_to_delete_clauses_l_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>{((i, S, xs), (j, T, ys)). i = j \<and> (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and>
             xs = ys \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal unfolding mark_to_delete_clauses_wl_pre_def by blast
    subgoal by auto
    subgoal by (auto simp: state_wl_l_def)
    subgoal unfolding mark_to_delete_clauses_wl_inv_def by fast
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal for x y xs xsa l to_keep xa x' x1 x2 x1a x2a x1b x2b x1c x2c
      by (auto simp: mark_to_delete_clauses_wl_invD1)
    subgoal by (auto simp: state_wl_l_def can_delete_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal
      by (auto simp: state_wl_l_def correct_watching_fmdrop mark_garbage_wl_def
          mark_garbage_l_def
        split: prod.splits)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by auto
    done
qed

text \<open>
  This is only a specification and must be implemented. There are two ways to do so:
  \<^enum> clean the watch lists and then iterate over all clauses to rebuild them.
  \<^enum> iterate over the watch list and check whether the clause index is in the domain or not.

  It is not clear which is faster (but option 1 requires only 1 memory access per clause instead of
  two). The first option is implemented in SPASS-SAT. The latter version (partly) in cadical.
\<close>
definition rewatch_clauses :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>rewatch_clauses = (\<lambda>(M, N, D, NE, UE, Q, W). SPEC(\<lambda>(M', N', D', NE', UE', Q', W').
     (M, N, D, NE, UE, Q) = (M', N', D', NE', UE', Q') \<and>
    correct_watching (M, N', D, NE, UE, Q, W')))\<close>

definition mark_to_delete_clauses_wl_post where
  \<open>mark_to_delete_clauses_wl_post S T \<longleftrightarrow>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and> blits_in_\<L>\<^sub>i\<^sub>n S \<and>
       mark_to_delete_clauses_l_post S' T' \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n T \<and>
       correct_watching T)\<close>

definition cdcl_twl_full_restart_wl_prog :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_twl_full_restart_wl_prog S = do {
    \<comment> \<open> \<^term>\<open>remove_one_annot_true_clause_imp_wl S\<close>\<close>
    ASSERT(mark_to_delete_clauses_wl_pre S);
    T \<leftarrow> mark_to_delete_clauses_wl S;
    ASSERT(mark_to_delete_clauses_wl_post S T);
    RETURN T
  }\<close>


lemma correct_watching_correct_watching: \<open>correct_watching S \<Longrightarrow> correct_watching' S\<close>
  apply (cases S, simp only: correct_watching.simps correct_watching'.simps)
  apply (subst (asm) all_clss_lf_ran_m[symmetric])
  unfolding image_mset_union all_lits_of_mm_union
  by auto

lemma (in -) [twl_st_l, simp]:
 \<open>(Sa, x) \<in> twl_st_l None \<Longrightarrow> get_all_learned_clss x =  mset `# (get_learned_clss_l Sa) + get_unit_learned_clss_l Sa\<close>
  by (cases Sa; cases x) (auto simp: twl_st_l_def get_learned_clss_l_def mset_take_mset_drop_mset')

lemma cdcl_twl_full_restart_wl_prog_final_rel:
  assumes
    S_Sa: \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close> and
    pre_Sa: \<open>mark_to_delete_clauses_l_pre Sa\<close> and
    pre_S: \<open>mark_to_delete_clauses_wl_pre S\<close> and
    T_Ta: \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close> and
    pre_l: \<open>mark_to_delete_clauses_l_post Sa Ta\<close>
  shows \<open>mark_to_delete_clauses_wl_post S T\<close>
proof -
  obtain x where
    Sa_x: \<open>(Sa, x) \<in> twl_st_l None\<close> and
    st: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* Sa Ta\<close> and
    list_invs: \<open>twl_list_invs Sa\<close> and
    struct: \<open>twl_struct_invs x\<close> and
    confl: \<open>get_conflict_l Sa = None\<close> and
    upd: \<open>clauses_to_update_l Sa = {#}\<close>
    using pre_l
    unfolding mark_to_delete_clauses_l_post_def by blast

  have corr_S: \<open>correct_watching' S\<close> and corr_T: \<open>correct_watching' T\<close> and
    blits_S: \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    blits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close> and
    S_Sa: \<open>(S, Sa) \<in> state_wl_l None\<close> and
    T_Ta: \<open>(T, Ta) \<in> state_wl_l None\<close>
    using S_Sa T_Ta by auto

  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  then have \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    using Sa_x S_Sa
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)

  then have corr_S': \<open>correct_watching S\<close>
    using corr_S
    by (cases S; simp only: correct_watching'.simps correct_watching.simps)
      simp
  obtain y where
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* Sa Ta\<close> and
    Ta_y: \<open>(Ta, y) \<in> twl_st_l None\<close>  and
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* x y\<close> and
    struct: \<open>twl_struct_invs y\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF st list_invs confl upd Sa_x
      struct]
    by blast

  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of y)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  then have eq: \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T) + get_unit_init_clss_wl T)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    using T_Ta Ta_y
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)

  then have corr_T': \<open>correct_watching T\<close>
    using corr_T
    by (cases T; simp only: correct_watching'.simps correct_watching.simps)
      simp

  have \<open>blits_in_\<L>\<^sub>i\<^sub>n T\<close>
    using blits_T eq
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
       all_init_lits_def
    by (auto dest: multi_member_split)
  then show ?thesis
    using S_Sa T_Ta corr_T' corr_S' pre_l blits_S
    unfolding mark_to_delete_clauses_wl_post_def
    by blast
qed

lemma cdcl_twl_full_restart_wl_prog_final_rel':
  assumes
    S_Sa: \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close> and
    pre_Sa: \<open>mark_to_delete_clauses_l_pre Sa\<close> and
    pre_S: \<open>mark_to_delete_clauses_wl_pre S\<close> and
    T_Ta: \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close> and
    pre_l: \<open>mark_to_delete_clauses_l_post Sa Ta\<close>
  shows \<open>mark_to_delete_clauses_wl_post S T\<close>
proof -
  obtain x where
    Sa_x: \<open>(Sa, x) \<in> twl_st_l None\<close> and
    st: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* Sa Ta\<close> and
    list_invs: \<open>twl_list_invs Sa\<close> and
    struct: \<open>twl_struct_invs x\<close> and
    confl: \<open>get_conflict_l Sa = None\<close> and
    upd: \<open>clauses_to_update_l Sa = {#}\<close>
    using pre_l
    unfolding mark_to_delete_clauses_l_post_def by blast

  have corr_S: \<open>correct_watching S\<close> and corr_T: \<open>correct_watching' T\<close> and
    blits_T: \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close> and
    blits_S: \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    S_Sa: \<open>(S, Sa) \<in> state_wl_l None\<close> and
    T_Ta: \<open>(T, Ta) \<in> state_wl_l None\<close>
    using S_Sa T_Ta by auto
  have corr_S: \<open>correct_watching' S\<close>
    using correct_watching_correct_watching[OF corr_S] .
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  then have \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    using Sa_x S_Sa
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)

  then have corr_S': \<open>correct_watching S\<close>
    using corr_S
    by (cases S; simp only: correct_watching'.simps correct_watching.simps)
      simp
  obtain y where
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* Sa Ta\<close> and
    Ta_y: \<open>(Ta, y) \<in> twl_st_l None\<close>  and
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* x y\<close> and
    struct: \<open>twl_struct_invs y\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF st list_invs confl upd Sa_x
      struct]
    by blast

  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of y)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  then have eq: \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T) + get_unit_init_clss_wl T)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    using T_Ta Ta_y
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)

  then have corr_T': \<open>correct_watching T\<close>
    using corr_T
    by (cases T; simp only: correct_watching'.simps correct_watching.simps)
      simp

  have \<open>blits_in_\<L>\<^sub>i\<^sub>n T\<close>
    using blits_T eq
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def
    by (auto dest: multi_member_split)
  then show ?thesis
    using S_Sa T_Ta corr_T' corr_S' pre_l blits_S
    unfolding mark_to_delete_clauses_wl_post_def
    by blast
qed


lemma mark_to_delete_clauses_l_pre_blits_in_\<L>\<^sub>i\<^sub>n':
  assumes
    S_Sa: \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close> and
    pre_Sa: \<open>mark_to_delete_clauses_l_pre Sa\<close>
  shows \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
proof -
  obtain x where
    Sa_x: \<open>(Sa, x) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs Sa\<close> and
    struct: \<open>twl_struct_invs x\<close>
    using pre_Sa
    unfolding mark_to_delete_clauses_l_pre_def by blast

  have corr_S: \<open>correct_watching S\<close> and
    blits_S: \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    S_Sa: \<open>(S, Sa) \<in> state_wl_l None\<close>
    using S_Sa by auto
  have corr_S: \<open>correct_watching' S\<close>
    using correct_watching_correct_watching[OF corr_S] .
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  then have \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    using Sa_x S_Sa
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)

  then have corr_S': \<open>correct_watching S\<close>
    using corr_S
    by (cases S; simp only: correct_watching'.simps correct_watching.simps)
      simp
 
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  then have eq: \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    using Sa_x S_Sa
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)
  moreover have eq: \<open>set_mset (all_lits_of_mm (mset `# learned_clss_lf (get_clauses_wl S) + get_unit_learned_clss_wl S)) \<subseteq>
    set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S))\<close>
    using Sa_x S_Sa alien
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)
  ultimately have \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
    using blits_S eq
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
      all_init_lits_def
    by (auto dest: multi_member_split)
  then show ?thesis
    using S_Sa corr_S' blits_S
    unfolding mark_to_delete_clauses_wl_post_def
    by blast
qed

lemma cdcl_twl_full_restart_wl_prog_cdcl_full_twl_restart_l_prog:
  \<open>(cdcl_twl_full_restart_wl_prog, cdcl_twl_full_restart_l_prog)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_prog_def cdcl_twl_full_restart_l_prog_def
    rewatch_clauses_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
     mark_to_delete_clauses_wl_mark_to_delete_clauses_l[THEN fref_to_Down]
     remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp[THEN fref_to_Down])
  subgoal unfolding mark_to_delete_clauses_wl_pre_def
   by (blast intro: correct_watching_correct_watching mark_to_delete_clauses_l_pre_blits_in_\<L>\<^sub>i\<^sub>n')
  subgoal unfolding mark_to_delete_clauses_wl_pre_def by (blast intro: correct_watching_correct_watching)
  subgoal
    by (rule cdcl_twl_full_restart_wl_prog_final_rel')
  subgoal by (auto simp: state_wl_l_def mark_to_delete_clauses_wl_post_def)
  done

definition (in -) restart_abs_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_pre S brk \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_abs_l_pre S' brk
      \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>

definition (in -) cdcl_twl_local_restart_wl_spec :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_local_restart_wl_spec = (\<lambda>(M, N, D, NE, UE, Q, W). do {
      ASSERT(restart_abs_wl_pre (M, N, D, NE, UE, Q, W) False);
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#}) \<or> (M' = M \<and> Q' = Q));
      RETURN (M, N, D, NE, UE, Q, W)
   })\<close>

lemma cdcl_twl_local_restart_wl_spec_cdcl_twl_local_restart_l_spec:
  \<open>(cdcl_twl_local_restart_wl_spec, cdcl_twl_local_restart_l_spec)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  have [refine0]:
    \<open>\<And>x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k.
        (x, y) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<Longrightarrow>
        x2d = (x1e, x2e) \<Longrightarrow>
        x2c = (x1d, x2d) \<Longrightarrow>
        x2b = (x1c, x2c) \<Longrightarrow>
        x2a = (x1b, x2b) \<Longrightarrow>
        x2 = (x1a, x2a) \<Longrightarrow>
        y = (x1, x2) \<Longrightarrow>
        x2j = (x1k, x2k) \<Longrightarrow>
        x2i = (x1j, x2j) \<Longrightarrow>
        x2h = (x1i, x2i) \<Longrightarrow>
        x2g = (x1h, x2h) \<Longrightarrow>
        x2f = (x1g, x2g) \<Longrightarrow>
        x = (x1f, x2f) \<Longrightarrow>
        SPEC (\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition x1f) \<and>
           Q' = {#}) \<or> M' = x1f \<and> Q' = x1k)
        \<le> \<Down>Id (SPEC (\<lambda>(M', Q') .(\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition x1) \<and>
           Q' = {#}) \<or> M' = x1 \<and> Q' = x2e))\<close>
    by (auto simp: state_wl_l_def)
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_spec_def cdcl_twl_local_restart_l_spec_def
      rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal unfolding restart_abs_wl_pre_def by fast
    apply assumption+
    subgoal by (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def
      blits_in_\<L>\<^sub>i\<^sub>n_def)
    done
qed

definition cdcl_twl_restart_wl_prog where
\<open>cdcl_twl_restart_wl_prog S = do {
   b \<leftarrow> SPEC(\<lambda>_. True);
   if b then cdcl_twl_local_restart_wl_spec S else cdcl_twl_full_restart_wl_prog S
  }\<close>

lemma cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(cdcl_twl_restart_wl_prog, cdcl_twl_restart_l_prog)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_prog_def cdcl_twl_restart_l_prog_def
    rewatch_clauses_def
  apply (intro frefI nres_relI)
  apply (refine_vcg cdcl_twl_local_restart_wl_spec_cdcl_twl_local_restart_l_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_full_twl_restart_l_prog[THEN fref_to_Down])
  subgoal by auto
  done


datatype restart_type =
  NO_RESTART |
  GC |
  RESTART

context twl_restart_ops
begin

definition (in twl_restart_ops) restart_required_wl  :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> restart_type nres\<close> where
\<open>restart_required_wl S n = SPEC (\<lambda>b. b \<noteq> NO_RESTART \<longrightarrow> f n < size (get_learned_clss_wl S))\<close>

definition (in twl_restart_ops) cdcl_twl_stgy_restart_abs_wl_inv
   :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0' brk T' n \<and>
       correct_watching T)\<close>
end


context twl_restart_ops
begin

definition cdcl_GC_clauses_pre_wl :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_GC_clauses_pre_wl S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> state_wl_l None \<and>
    correct_watching'' S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    cdcl_GC_clauses_pre T
  )\<close>

definition cdcl_GC_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_GC_clauses_wl = (\<lambda>(M, N, D, NE, UE, WS, Q). do {
  ASSERT(cdcl_GC_clauses_pre_wl (M, N, D, NE, UE, WS, Q));
  let b = True;
  if b then do {
    (N', _) \<leftarrow> SPEC (\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N'') \<and>
      0 \<notin># dom_m N'');
    Q \<leftarrow> SPEC(\<lambda>Q. correct_watching' (M, N', D, NE, UE, WS, Q)\<and> literals_are_\<L>\<^sub>i\<^sub>n' (M, N', D, NE, UE, WS, Q));
    RETURN (M, N', D, NE, UE, WS, Q)
  }
  else RETURN (M, N, D, NE, UE, WS, Q)})\<close>

lemma cdcl_GC_clauses_wl_cdcl_GC_clauses:
  \<open>(cdcl_GC_clauses_wl, cdcl_GC_clauses) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f \<langle>{(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
  unfolding cdcl_GC_clauses_wl_def cdcl_GC_clauses_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  subgoal unfolding cdcl_GC_clauses_pre_wl_def by blast
  subgoal by (auto simp: state_wl_l_def)
  subgoal by (auto simp: state_wl_l_def)
  subgoal by auto
  subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h
       x2h x1i x2i x1j x2j x1k x2k b xa x' x1l x2l x1m x2m Q
    by (auto simp: state_wl_l_def blits_in_\<L>\<^sub>i\<^sub>n'_def dest: multi_member_split)
  subgoal by auto
  done

definition cdcl_twl_full_restart_wl_GC_prog_post :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_GC_prog_post S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
    cdcl_twl_full_restart_l_GC_prog_pre S' \<and>
    cdcl_twl_restart_l S' T' \<and> correct_watching' T \<and>
    set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T)+ get_unit_init_clss_wl T)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T)+ get_unit_clauses_wl T)))\<close>

definition (in -) restart_abs_wl_pre2 :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_pre2 S brk \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_abs_l_pre S' brk
      \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition (in -) cdcl_twl_local_restart_wl_spec0 :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_local_restart_wl_spec0 = (\<lambda>(M, N, D, NE, UE, Q, W). do {
      ASSERT(restart_abs_wl_pre2 (M, N, D, NE, UE, Q, W) False);
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#} \<and> count_decided M' = 0) \<or> (M' = M \<and> Q' = Q \<and> count_decided M' = 0));
      RETURN (M, N, D, NE, UE, Q, W)
   })\<close>


definition mark_to_delete_clauses_wl2_inv
  :: \<open>'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> 'v twl_st_wl\<times> nat list  \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_wl2_inv = (\<lambda>S xs0 (i, T, xs).
     \<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
      mark_to_delete_clauses_l_inv S' xs0 (i, T', xs) \<and>
      correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>


(*TODO What is exactly the difference with mark_to_delete_clauses_wl?*)
definition mark_to_delete_clauses_wl2 :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl2  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_pre S);
    xs \<leftarrow> collect_valid_indices_wl S;
    l \<leftarrow> SPEC(\<lambda>_:: nat. True);
    (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl2_inv S xs\<^esup>
      (\<lambda>(i, S, xs). i < length xs)
      (\<lambda>(i, T, xs). do {
        if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	  ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
             (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
              \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2);
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

lemma mark_to_delete_clauses_wl2_invD1:
  assumes \<open>mark_to_delete_clauses_wl2_inv S xs (i, T, ys)\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>0 < length (get_clauses_wl T \<propto> C)\<close>
  shows
    \<open>get_clauses_wl T \<propto> C ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)\<close>
proof -
  have \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
    using assms unfolding mark_to_delete_clauses_wl2_inv_def by blast
  then have \<open>get_clauses_wl T \<propto> C ! 0 \<in># all_init_lits_st T\<close>
    using assms(2,3) by (auto dest!: multi_member_split
      simp: ran_m_def all_init_lits_def all_lits_of_mm_add_mset
        in_clause_in_all_lits_of_m literals_are_\<L>\<^sub>i\<^sub>n'_def
        in_clause_in_all_lits_of_m subsetD)
  then show \<open>?thesis\<close>
    by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(1))
qed

lemma mark_to_delete_clauses_wl_mark_to_delete_clauses_l2:
  \<open>(mark_to_delete_clauses_wl2, mark_to_delete_clauses_l)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S  \<le> \<Down> Id (collect_valid_indices S')\<close>
    if \<open>(S, S') \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and>
           mark_to_delete_clauses_wl_pre S}\<close>
    for S S'
    using that by (auto simp: collect_valid_indices_wl_def collect_valid_indices_def)
  have if_inv: \<open>(if A then RETURN P else RETURN Q) = RETURN (if A then P else Q)\<close> for A P Q
    by auto
  have Ball_range[simp]: \<open>(\<forall>x\<in>range f \<union> range g. P x)\<longleftrightarrow>(\<forall>x. P (f x) \<and> P (g x))\<close> for P f g
    by auto
  show ?thesis
    unfolding mark_to_delete_clauses_wl2_def mark_to_delete_clauses_l_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>{((i, S, xs), (j, T, ys)). i = j \<and> (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and>
             xs = ys \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal unfolding mark_to_delete_clauses_wl_pre_def by blast
    subgoal by auto
    subgoal by (auto simp: state_wl_l_def)
    subgoal unfolding mark_to_delete_clauses_wl2_inv_def by fast
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal for x y xs xsa l to_keep xa x' x1 x2 x1a x2a x1b x2b x1c x2c
      by (auto simp: mark_to_delete_clauses_wl2_invD1)
    subgoal by (auto simp: state_wl_l_def can_delete_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal
      by (auto simp: state_wl_l_def correct_watching_fmdrop mark_garbage_wl_def
          mark_garbage_l_def correct_watching''_fmdrop
        split: prod.splits)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by auto
    done
qed

definition cdcl_twl_full_restart_wl_GC_prog_pre
  :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>cdcl_twl_full_restart_wl_GC_prog_pre S \<longleftrightarrow>
   (\<exists>T. (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> cdcl_twl_full_restart_l_GC_prog_pre T)\<close>

definition cdcl_twl_full_restart_wl_GC_prog where
\<open>cdcl_twl_full_restart_wl_GC_prog S = do {
    ASSERT(cdcl_twl_full_restart_wl_GC_prog_pre S);
    S' \<leftarrow> cdcl_twl_local_restart_wl_spec0 S;
    T \<leftarrow> remove_one_annot_true_clause_imp_wl S';
    ASSERT(mark_to_delete_clauses_wl_pre T);
    U \<leftarrow> mark_to_delete_clauses_wl2 T;
    V \<leftarrow> cdcl_GC_clauses_wl U;
    ASSERT(cdcl_twl_full_restart_wl_GC_prog_post S V);
    RETURN V
  }\<close>

lemma blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' (a, b, c, d, e, f', g) \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n' (ah, b, c, d, e, {#}, g)\<close>
  by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def)

lemma cdcl_twl_local_restart_wl_spec0_cdcl_twl_local_restart_l_spec0:
  \<open>(x, y) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<Longrightarrow>
          cdcl_twl_local_restart_wl_spec0 x
          \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}
	    (cdcl_twl_local_restart_l_spec0 y)\<close>
  unfolding cdcl_twl_local_restart_wl_spec0_def cdcl_twl_local_restart_l_spec0_def curry_def
  apply refine_vcg
  subgoal unfolding restart_abs_wl_pre2_def by (rule exI[of _ y]) fast
  by (auto simp:
      state_wl_l_def image_iff correct_watching''.simps clause_to_update_def
      conc_fun_RES RES_RETURN_RES2 blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0)

lemma cdcl_twl_full_restart_wl_GC_prog_post_correct_watching:
  assumes
    pre: \<open>cdcl_twl_full_restart_l_GC_prog_pre y\<close> and
    y_Va: \<open>cdcl_twl_restart_l y Va\<close>
    \<open>(V, Va) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
  shows \<open>(V, Va) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close> and
    \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl V)+ get_unit_init_clss_wl V)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl V)+ get_unit_clauses_wl V))\<close>
proof -
  obtain x where
    y_x: \<open>(y, x) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs x\<close> and
    list_invs: \<open>twl_list_invs y\<close>
    using pre unfolding cdcl_twl_full_restart_l_GC_prog_pre_def by blast
  obtain V' where \<open>cdcl_twl_restart x V'\<close> and Va_V': \<open>(Va, V') \<in> twl_st_l None\<close>
    using cdcl_twl_restart_l_cdcl_twl_restart[OF y_x list_invs struct_invs] y_Va
    unfolding conc_fun_RES by auto
  then have \<open>twl_struct_invs V'\<close>
    using struct_invs by (blast dest: cdcl_twl_restart_twl_struct_invs)
  then have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of V')\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by blast
  then show eq: \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl V)+ get_unit_init_clss_wl V)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl V)+ get_unit_clauses_wl V))\<close>
    using assms(3) Va_V'
    apply (cases V; cases V')
    apply (auto simp: state_wl_l_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      twl_st_l_def cdcl\<^sub>W_restart_mset_state image_image mset_take_mset_drop_mset'
      in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def atms_of_def atm_of_eq_atm_of
      conj_disj_distribR Collect_disj_eq ex_disj_distrib
      split: if_splits
      dest!: multi_member_split[of _ \<open>ran_m _\<close>])
      apply (auto dest!: split_list
        dest!: multi_member_split)
    done
  then have \<open>correct_watching' V \<Longrightarrow>  correct_watching V\<close>
    by (cases V) (auto simp: correct_watching.simps correct_watching'.simps)
  moreover
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n' V \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n V\<close>
    using eq by (cases V)
      (clarsimp simp: blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def)
  ultimately show \<open>(V, Va) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close>
    using assms by (auto simp: cdcl_twl_full_restart_wl_GC_prog_post_def)
qed

lemma cdcl_twl_full_restart_wl_GC_prog:
  \<open>(cdcl_twl_full_restart_wl_GC_prog, cdcl_twl_full_restart_l_GC_prog) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f \<langle>{(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_GC_prog_def cdcl_twl_full_restart_l_GC_prog_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp[THEN fref_to_Down]
    mark_to_delete_clauses_wl_mark_to_delete_clauses_l2[THEN fref_to_Down]
    cdcl_GC_clauses_wl_cdcl_GC_clauses[THEN fref_to_Down]
    cdcl_twl_local_restart_wl_spec0_cdcl_twl_local_restart_l_spec0)
  subgoal unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def by blast
  subgoal by (auto dest: correct_watching'_correct_watching'')
  subgoal unfolding mark_to_delete_clauses_wl_pre_def by fast
  subgoal for x y S S' T Ta U Ua V Va
    using cdcl_twl_full_restart_wl_GC_prog_post_correct_watching[of y Va V]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
    by fast
  subgoal for x y S' S'a T Ta U Ua V Va
    by (rule cdcl_twl_full_restart_wl_GC_prog_post_correct_watching)
  done


definition (in twl_restart_ops) restart_prog_wl
  :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_wl \<times> nat) nres"
where
  \<open>restart_prog_wl S n brk = do {
     ASSERT(restart_abs_wl_pre S brk);
     b \<leftarrow> restart_required_wl S n;
     if b = GC \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_full_restart_wl_GC_prog S;
       RETURN (T, n + 1)
     }
     else if b = RESTART \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog S;
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>

lemma restart_prog_wl_alt_def:
 \<open>restart_prog_wl S n brk = do {
     ASSERT(restart_abs_wl_pre S brk);
     b \<leftarrow> restart_required_wl S n;
     let _ = (b = GC);
     if b = GC \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_full_restart_wl_GC_prog S;
       RETURN (T, n + 1)
     }
     else if b = RESTART \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog S;
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>
  unfolding restart_prog_wl_def
  by auto

lemma restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n:
  assumes pre: \<open>restart_abs_wl_pre x1c b\<close> and
    \<open>blits_in_\<L>\<^sub>i\<^sub>n x1c\<close>
  shows \<open>literals_are_\<L>\<^sub>i\<^sub>n' x1c\<close>
proof -

  obtain y x where
    y_x: \<open>(y, x) \<in> twl_st_l None\<close> and
    x1c_y: \<open>(x1c, y) \<in> state_wl_l None\<close> and
    struct_invs: \<open>twl_struct_invs x\<close> and
    list_invs: \<open>twl_list_invs y\<close>
    using pre unfolding restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def apply - apply normalize_goal+
    by blast
  then have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x)\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by blast
  then have eq: \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl x1c)+ get_unit_init_clss_wl x1c)) =
    set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl x1c)+ get_unit_clauses_wl x1c))\<close>
    using y_x x1c_y
    apply (cases x1c; cases y; cases x)
    apply (auto simp: state_wl_l_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      twl_st_l_def cdcl\<^sub>W_restart_mset_state image_image mset_take_mset_drop_mset'
      in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def atms_of_def atm_of_eq_atm_of
      conj_disj_distribR Collect_disj_eq ex_disj_distrib
      split: if_splits
      dest!: multi_member_split[of _ \<open>ran_m _\<close>])
      apply (auto dest!: split_list
        dest!: multi_member_split)
    done
  moreover have eq: \<open>set_mset (all_lits_of_mm (mset `# learned_clss_lf (get_clauses_wl x1c) + get_unit_learned_clss_wl x1c)) \<subseteq>
    set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl x1c) + get_unit_init_clss_wl x1c))\<close>
    using y_x x1c_y alien
    unfolding image_mset_union cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_mm_union
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff get_learned_clss_l_def
      twl_st get_unit_clauses_wl_alt_def)
  ultimately show \<open>literals_are_\<L>\<^sub>i\<^sub>n' x1c\<close>
    using eq assms by (cases x1c)
      (clarsimp simp: blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def)
qed

lemma cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(uncurry2 restart_prog_wl, uncurry2 restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<times>\<^sub>f _ \<times>\<^sub>f _ \<rightarrow>\<^sub>f \<langle>?R'\<rangle>nres_rel\<close>)
proof -
  have [refine0]: \<open>restart_required_wl a b \<le> \<Down> {(b, b'). b' \<longleftrightarrow> (b \<noteq> NO_RESTART)} (restart_required_l a' b')\<close>
    if \<open>(a, a') \<in> ?R\<close> and \<open>(b, b') \<in> nat_rel\<close> for a a' b b'
    using that unfolding restart_required_wl_def restart_required_l_def apply -
    by (rule RES_refine, rule_tac x= \<open>s \<noteq> NO_RESTART\<close> in bexI)
      (auto simp: twl_st_l)
  show ?thesis
    unfolding uncurry_def restart_prog_wl_alt_def restart_prog_l_def rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_GC_prog[THEN fref_to_Down])
    subgoal unfolding restart_abs_wl_pre_def
       by (fastforce simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c b ba b2 by (cases b; auto)
    subgoal
      by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_wl
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_wl (S\<^sub>0::'v twl_st_wl) =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, n) \<leftarrow> restart_prog_wl T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0::'v twl_st_wl, 0);
    RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  have [refine0]:
    \<open>(x, y) \<in> ?R \<Longrightarrow> ((False, x, 0), False, y, 0) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close> for x y
    by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where
      R=\<open>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    done
qed


definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_early_wl
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl (S\<^sub>0::'v twl_st_wl) = do {
    ebrk \<leftarrow> RES UNIV;
    (_, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, n) \<leftarrow> restart_prog_wl T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0::'v twl_st_wl, 0);
    if \<not> brk then do {
      (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S, n).
          do {
            T \<leftarrow> unit_propagation_outer_loop_wl S;
            (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
            (T, n) \<leftarrow> restart_prog_wl T n brk;
            RETURN (brk, T, n)
          })
         (False, T::'v twl_st_wl, n);
      RETURN T
    }
    else RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_wl_cdcl_twl_stgy_restart_prog_early_l:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl, cdcl_twl_stgy_restart_prog_early_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_wl_def cdcl_twl_stgy_restart_prog_early_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>]
        WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by fastforce
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


theorem cdcl_twl_stgy_restart_prog_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l[where 'a='v]
  unfolding fref_param1 apply -
  apply (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?)
  by (metis (no_types, lifting) in_pair_collect_simp nres_rel_mono subrelI)

theorem cdcl_twl_stgy_restart_prog_early_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl, cdcl_twl_stgy_restart_prog_early_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_early_wl_cdcl_twl_stgy_restart_prog_early_l[where 'a='v]
  unfolding fref_param1 apply -
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?; match_fun_rel?)
    auto

definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_bounded_wl
  :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl (S\<^sub>0::'v twl_st_wl) = do {
    ebrk \<leftarrow> RES UNIV;
    (_, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, n) \<leftarrow> restart_prog_wl T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0::'v twl_st_wl, 0);
    RETURN (brk, T)
  }\<close>


lemma cdcl_twl_stgy_restart_prog_bounded_wl_cdcl_twl_stgy_restart_prog_bounded_l:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_wl, cdcl_twl_stgy_restart_prog_bounded_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>bool_rel \<times>\<^sub>r {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_def cdcl_twl_stgy_restart_prog_bounded_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by fastforce
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

theorem cdcl_twl_stgy_restart_prog_bounded_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_wl, cdcl_twl_stgy_restart_prog_bounded_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>bool_rel \<times>\<^sub>r state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_bounded_wl_cdcl_twl_stgy_restart_prog_bounded_l[where 'a='v]
  unfolding fref_param1 apply -
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?; match_fun_rel?)
    auto

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
          D \<leftarrow> SPEC(\<lambda>D. D \<notin># dom_m N' \<and> D \<noteq> 0);
	  RETURN (i+1, fmdrop C N, fmupd D (N \<propto> C, irred N C) N')
        } else RETURN (i+1, N, N')
      }) (0, N, N');
    RETURN (N, N')
  })\<close>

definition clauses_pointed_to :: \<open>'v literal set \<Rightarrow> ('v literal \<Rightarrow> 'v watched) \<Rightarrow> nat set\<close>
where
  \<open>clauses_pointed_to \<A> W \<equiv> \<Union>(((`) fst) ` set ` W ` \<A>)\<close>

lemma clauses_pointed_to_insert[simp]:
  \<open>clauses_pointed_to (insert A \<A>) W =
    fst ` set (W A) \<union>
    clauses_pointed_to \<A> W\<close> and
  clauses_pointed_to_empty[simp]:
    \<open>clauses_pointed_to {} W = {}\<close>
  by (auto simp: clauses_pointed_to_def)

lemma cdcl_GC_clauses_prog_copy_wl_entry:
  fixes A :: \<open>'v literal\<close> and WS :: \<open>'v literal \<Rightarrow> 'v watched\<close>
  defines [simp]: \<open>W \<equiv> WS A\<close>
  assumes \<open>
	  ran m0 \<subseteq> set_mset (dom_m N0') \<and>
	  (\<forall>L\<in>dom m0. L \<notin># (dom_m N0)) \<and>
	  set_mset (dom_m N0) \<subseteq> clauses_pointed_to (set_mset \<A>) WS \<and>
          0 \<notin># dom_m N0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_copy_wl_entry N0 W A N0' \<le>
      SPEC(\<lambda>(N, N'). (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, m0, N0') (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  (\<forall>L\<in>dom m. L \<notin># (dom_m N)) \<and>
	  set_mset (dom_m N) \<subseteq> clauses_pointed_to (set_mset (remove1_mset A \<A>)) WS) \<and>
	  (\<forall>L \<in> set W. fst L \<notin># dom_m N) \<and>
          0 \<notin># dom_m N')\<close>
proof -
  have [simp]:
    \<open>x \<in># remove1_mset a (dom_m aaa) \<longleftrightarrow> x \<noteq> a \<and> x \<in># dom_m aaa\<close> for x a aaa
    using distinct_mset_dom[of aaa]
    by (cases \<open>a \<in># dom_m aaa\<close>)
      (auto dest!: multi_member_split simp: add_mset_eq_add_mset)

  show ?thesis
    unfolding cdcl_GC_clauses_prog_copy_wl_entry_def
    apply (refine_vcg
      WHILET_rule[where I = \<open>\<lambda>(i, N, N'). \<exists>m. GC_remap\<^sup>*\<^sup>* (N0, m0, N0') (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  (\<forall>L\<in>dom m. L \<notin># (dom_m N)) \<and>
	  set_mset (dom_m N) \<subseteq> clauses_pointed_to (set_mset (remove1_mset A \<A>)) WS \<union>
	    (fst) ` set (drop i W) \<and>
	  (\<forall>L \<in> set (take i W). fst L \<notin># dom_m N) \<and>
          0 \<notin># dom_m N'\<close> and
	R = \<open>measure (\<lambda>(i, N, N'). length W -i)\<close>])
    subgoal by auto
    subgoal
      using assms
      by (cases \<open>A \<in># \<A>\<close>) (auto dest!: multi_member_split)
    subgoal by auto
    subgoal for s aa ba aaa baa x x1 x2 x1a x2a
      apply clarify
      apply (subgoal_tac \<open>(\<exists>m'. GC_remap (aaa, m, baa) (fmdrop (fst (W ! aa)) aaa, m',
		fmupd x (the (fmlookup aaa (fst (W ! aa)))) baa) \<and>
	  ran m' \<subseteq> set_mset (dom_m (fmupd x (the (fmlookup aaa (fst (W ! aa)))) baa)) \<and>
    (\<forall>L\<in>dom m'. L \<notin># (dom_m (fmdrop (fst (W ! aa)) aaa)))) \<and>
	  set_mset (dom_m (fmdrop (fst (W ! aa)) aaa)) \<subseteq>
	    clauses_pointed_to (set_mset (remove1_mset A \<A>)) WS \<union>
	     fst ` set (drop (Suc aa) W) \<and>
	  (\<forall>L \<in> set (take (Suc aa) W). fst L \<notin># dom_m (fmdrop (fst (W ! aa)) aaa))\<close>)
      apply (auto intro: rtranclp.rtrancl_into_rtrancl)[]
      apply (auto simp: GC_remap.simps Cons_nth_drop_Suc[symmetric]
          take_Suc_conv_app_nth
        dest: multi_member_split)
      apply (rule_tac x= \<open>m(fst (W ! aa) \<mapsto> x)\<close> in exI)
      apply (intro conjI)
      apply (rule_tac x=x in exI)
        apply (rule_tac x= \<open>fst (W ! aa)\<close> in exI)
        apply (force dest: rtranclp_GC_remap_ran_m_no_lost)
       apply auto
      by (smt basic_trans_rules(31) fun_upd_apply mem_Collect_eq option.simps(1) ran_def)
    subgoal by auto
    subgoal by (auto 5 5 simp: GC_remap.simps Cons_nth_drop_Suc[symmetric]
          take_Suc_conv_app_nth
        dest: multi_member_split)
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
    (N, N') \<leftarrow> cdcl_GC_clauses_prog_copy_wl_entry N (WS (-L)) (-L) N';
    let WS = WS(-L := []);
    RETURN (N, N', WS)
  })\<close>

lemma clauses_pointed_to_remove1_if:
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow> xa \<in># dom_m aa \<Longrightarrow>
    xa \<in> clauses_pointed_to (set_mset (remove1_mset L \<A>))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    xa \<in> clauses_pointed_to (set_mset (remove1_mset L \<A>)) W\<close>
  by (cases \<open>L \<in># \<A>\<close>)
    (fastforce simp: clauses_pointed_to_def
    dest!: multi_member_split)+

lemma clauses_pointed_to_remove1_if2:
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow> xa \<in># dom_m aa \<Longrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L, L'#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L, L'#})) W\<close>
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow> xa \<in># dom_m aa \<Longrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L', L#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L', L#})) W\<close>
  by (cases \<open>L \<in># \<A>\<close>; fastforce simp: clauses_pointed_to_def
    dest!: multi_member_split)+

lemma clauses_pointed_to_remove1_if2_eq:
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow>
    set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L, L'#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L, L'#})) W\<close>
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow>
     set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L', L#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
     set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L', L#})) W\<close>
  by (auto simp: clauses_pointed_to_remove1_if2)

lemma negs_remove_Neg: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Neg A, Pos A#} =
   negs \<A> + poss \<A>\<close>
  by (induction \<A>) auto
lemma poss_remove_Pos: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Pos A, Neg A#} =
   negs \<A> + poss \<A>\<close>
  by (induction \<A>)  auto

lemma cdcl_GC_clauses_prog_single_wl_removed:
  \<open>\<forall>L\<in>set (W (Pos A)). fst L \<notin># dom_m aaa \<Longrightarrow>
       \<forall>L\<in>set (W (Neg A)). fst L \<notin># dom_m a \<Longrightarrow>
       GC_remap\<^sup>*\<^sup>* (aaa, ma, baa) (a, mb, b) \<Longrightarrow>
       set_mset (dom_m a) \<subseteq> clauses_pointed_to (set_mset (negs \<A> + poss \<A> - {#Neg A, Pos A#})) W \<Longrightarrow>
       xa \<in># dom_m a \<Longrightarrow>
       xa \<in> clauses_pointed_to (Neg ` set_mset (remove1_mset A \<A>) \<union> Pos ` set_mset (remove1_mset A \<A>))
              (W(Pos A := [], Neg A := []))\<close>
  \<open>\<forall>L\<in>set (W (Neg A)). fst L \<notin># dom_m aaa \<Longrightarrow>
       \<forall>L\<in>set (W (Pos A)). fst L \<notin># dom_m a \<Longrightarrow>
       GC_remap\<^sup>*\<^sup>* (aaa, ma, baa) (a, mb, b) \<Longrightarrow>
       set_mset (dom_m a) \<subseteq> clauses_pointed_to (set_mset (negs \<A> + poss \<A> - {#Pos A, Neg A#})) W \<Longrightarrow>
       xa \<in># dom_m a \<Longrightarrow>
       xa \<in> clauses_pointed_to
              (Neg ` set_mset (remove1_mset A \<A>) \<union> Pos ` set_mset (remove1_mset A \<A>))
              (W(Neg A := [], Pos A := []))\<close>
  supply poss_remove_Pos[simp] negs_remove_Neg[simp]
  by (case_tac [!] \<open>A \<in># \<A>\<close>)
    (fastforce simp: clauses_pointed_to_def
      dest!: multi_member_split
      dest: rtranclp_GC_remap_ran_m_no_lost)+

lemma cdcl_GC_clauses_prog_single_wl:
  fixes A :: \<open>'v\<close> and WS :: \<open>'v literal \<Rightarrow> 'v watched\<close> and
    N0 :: \<open>'v clauses_l\<close>
  assumes \<open>ran m \<subseteq> set_mset (dom_m N0') \<and>
	  (\<forall>L\<in>dom m. L \<notin># (dom_m N0)) \<and>
	  set_mset (dom_m N0) \<subseteq>
	    clauses_pointed_to (set_mset (negs \<A> + poss \<A>)) W \<and>
          0 \<notin># dom_m N0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_single_wl N0 W A N0' \<le>
      SPEC(\<lambda>(N, N', WS'). \<exists>m'. GC_remap\<^sup>*\<^sup>* (N0, m, N0') (N, m', N') \<and>
	  ran m' \<subseteq> set_mset (dom_m N') \<and>
	  (\<forall>L\<in>dom m'. L \<notin># dom_m N) \<and>
	  WS' (Pos A) = [] \<and> WS' (Neg A) = [] \<and>
	  (\<forall>L. L \<noteq> Pos A \<longrightarrow> L \<noteq> Neg A \<longrightarrow> W L = WS' L) \<and>
	  set_mset (dom_m N) \<subseteq>
	    clauses_pointed_to
	      (set_mset (negs (remove1_mset A \<A>) + poss (remove1_mset A \<A>))) WS' \<and>
          0 \<notin># dom_m N'
	  )\<close>
proof -
  have [simp]: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Neg A, Pos A#} =
   negs \<A> + poss \<A>\<close>
    by (induction \<A>) auto
  have [simp]: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Pos A, Neg A#} =
   negs \<A> + poss \<A>\<close>
    by (induction \<A>)  auto
  show ?thesis
    unfolding cdcl_GC_clauses_prog_single_wl_def
    apply (refine_vcg)
    subgoal for x (*TODO proof*)
      apply (rule order_trans, rule cdcl_GC_clauses_prog_copy_wl_entry[of _ _ _
            \<open>negs \<A> + poss \<A>\<close>])
       apply(solves \<open>use assms in auto\<close>)
      apply (rule RES_rule)
      apply (refine_vcg)
      apply clarify
      subgoal for aa ba aaa baa ma
        apply (rule order_trans,
            rule cdcl_GC_clauses_prog_copy_wl_entry[of ma _ _
              \<open>remove1_mset x (negs \<A> + poss \<A>)\<close>])
         apply (solves \<open>auto simp: clauses_pointed_to_remove1_if\<close>)[]
        unfolding Let_def
        apply (rule RES_rule)
        apply clarsimp
        apply (simp add: eq_commute[of \<open>Neg _\<close>]
            uminus_lit_swap clauses_pointed_to_remove1_if)
        apply auto
         apply (rule_tac x=mb in exI)
         apply (auto dest!:
            simp: clauses_pointed_to_remove1_if
            clauses_pointed_to_remove1_if2
            clauses_pointed_to_remove1_if2_eq)
         apply (subst (asm) clauses_pointed_to_remove1_if2_eq)
          apply (force dest: rtranclp_GC_remap_ran_m_no_lost)
         apply (auto intro!: cdcl_GC_clauses_prog_single_wl_removed)[]
         apply (rule_tac x=mb in exI)
         apply (auto dest: multi_member_split[of A]
            simp: clauses_pointed_to_remove1_if
            clauses_pointed_to_remove1_if2
            clauses_pointed_to_remove1_if2_eq)
         apply (subst (asm) clauses_pointed_to_remove1_if2_eq)
          apply (force dest: rtranclp_GC_remap_ran_m_no_lost)
        apply (auto intro!: cdcl_GC_clauses_prog_single_wl_removed)[]
        done
    done
    done
qed


definition cdcl_GC_clauses_prog_wl_inv
  :: \<open>'v multiset \<Rightarrow> 'v clauses_l \<Rightarrow>
    'v multiset \<times> ('v clauses_l \<times> 'v clauses_l \<times> ('v literal \<Rightarrow> 'v watched)) \<Rightarrow> bool\<close>
where
\<open>cdcl_GC_clauses_prog_wl_inv \<A> N0 = (\<lambda>(\<B>, (N, N', WS)). \<B> \<subseteq># \<A> \<and>
  (\<forall>A \<in> set_mset \<A> - set_mset \<B>. (WS (Pos A) = []) \<and> WS (Neg A) = []) \<and>
  0 \<notin># dom_m N' \<and>
  (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (N, m, N')\<and>
      ran m \<subseteq> set_mset (dom_m N') \<and>
      (\<forall>L\<in>dom m. L \<notin># dom_m N) \<and>
      set_mset (dom_m N) \<subseteq> clauses_pointed_to (Neg ` set_mset \<B> \<union> Pos ` set_mset \<B>) WS))\<close>

definition cdcl_GC_clauses_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_GC_clauses_prog_wl = (\<lambda>(M, N0, D, NE, UE, Q, WS). do {
    ASSERT(cdcl_GC_clauses_pre_wl (M, N0, D, NE, UE, Q, WS));
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset (all_init_atms N0 NE));
    (_, (N, N', WS)) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_GC_clauses_prog_wl_inv \<A> N0\<^esup>
      (\<lambda>(\<B>, _). \<B> \<noteq> {#})
      (\<lambda>(\<B>, (N, N', WS)). do {
        ASSERT(\<B> \<noteq> {#});
        A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
        (N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_single_wl N WS A N';
        RETURN (remove1_mset A \<B>, (N, N', WS))
      })
      (\<A>, (N0, fmempty, WS));
    RETURN (M, N', D, NE, UE, Q, WS)
  })\<close>


lemma cdcl_GC_clauses_prog_wl:
  assumes \<open>((M, N0, D, NE, UE, Q, WS), S) \<in> state_wl_l None \<and>
    correct_watching'' (M, N0, D, NE, UE, Q, WS) \<and> cdcl_GC_clauses_pre S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' (M, N0, D, NE, UE, Q, WS) \<and> 
   set_mset (dom_m N0) \<subseteq> clauses_pointed_to
      (Neg ` set_mset (all_init_atms N0 NE) \<union> Pos ` set_mset (all_init_atms N0 NE)) WS\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N0, D, NE, UE, Q, WS) \<le>
      (SPEC(\<lambda>(M', N', D', NE', UE', Q', WS'). (M', D', NE', UE', Q') = (M, D, NE, UE, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N' \<and> (\<forall>L \<in># all_init_lits N0 NE. WS' L = [])))\<close>
proof -
  show ?thesis
    supply[[goals_limit=1]]
    unfolding cdcl_GC_clauses_prog_wl_def
    apply (refine_vcg
      WHILEIT_rule[where R = \<open>measure (\<lambda>(\<A>::'v multiset, (_::'v clauses_l, _ ::'v clauses_l,
          _:: 'v literal \<Rightarrow> 'v watched)). size \<A>)\<close>])
    subgoal
      using assms
      unfolding cdcl_GC_clauses_pre_wl_def
      by blast
    subgoal by auto
    subgoal using assms unfolding cdcl_GC_clauses_prog_wl_inv_def by auto
    subgoal by auto
    subgoal for a b aa ba ab bb ac bc ad bd ae be x s af bf ag bg ah bh xa
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      apply clarify
      apply (rule order_trans,
         rule_tac m=m and \<A>=af in cdcl_GC_clauses_prog_single_wl)
      subgoal by auto
      subgoal
        apply (rule RES_rule)
        apply clarify
        apply (rule RETURN_rule)
        apply clarify
        apply (intro conjI)
             apply (solves auto)
            apply (solves \<open>auto dest!: multi_member_split\<close>)
           apply (solves auto)
          apply (rule_tac x=m' in exI)
          apply (solves auto)[]
         apply (simp_all add: size_Diff1_less)[]
        done
      done
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by (intro ballI, rename_tac L, case_tac L)
        (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_init_atms_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split)
  done
qed



(* TODO Move *)

lemma all_init_atms_fmdrop_add_mset_unit:
  \<open>C \<in># dom_m baa \<Longrightarrow> irred baa C \<Longrightarrow>
    all_init_atms (fmdrop C baa) (add_mset (mset (baa \<propto> C)) da) =
   all_init_atms baa da\<close>
  \<open>C \<in># dom_m baa \<Longrightarrow> \<not>irred baa C \<Longrightarrow>
    all_init_atms (fmdrop C baa) da =
   all_init_atms baa da\<close>
  by (auto simp del: all_init_atms_def[symmetric]
    simp: all_init_atms_def all_init_lits_def
      init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if)

lemma cdcl_GC_clauses_prog_wl2:
  assumes \<open>((M, N0, D, NE, UE, Q, WS), S) \<in> state_wl_l None \<and>
    correct_watching'' (M, N0, D, NE, UE, Q, WS) \<and> cdcl_GC_clauses_pre S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' (M, N0, D, NE, UE, Q, WS) \<and>
   set_mset (dom_m N0) \<subseteq> clauses_pointed_to
      (Neg ` set_mset (all_init_atms N0 NE) \<union> Pos ` set_mset (all_init_atms N0 NE)) WS\<close> and
    \<open>N0 = N0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N0, D, NE, UE, Q, WS) \<le>
       \<Down> {((M', N'', D', NE', UE', Q', WS'), (N, N')). (M', D', NE', UE', Q') = (M, D, NE, UE, Q) \<and>
             N'' = N \<and> (\<forall>L\<in>#all_init_lits N0 NE. WS' L = [])\<and>
           all_init_lits N0 NE = all_init_lits N NE' \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (fmempty, m, N))}
      (SPEC(\<lambda>(N'::(nat, 'a literal list \<times> bool) fmap, m).
         GC_remap\<^sup>*\<^sup>* (N0', (\<lambda>_. None), fmempty) (fmempty, m, N') \<and>
	  0 \<notin># dom_m N'))\<close>
proof -
  show ?thesis
    unfolding \<open>N0 = N0'\<close>[symmetric]
    apply (rule order_trans[OF cdcl_GC_clauses_prog_wl[OF assms(1)]])
    apply (rule RES_refine)
    apply (fastforce dest: rtranclp_GC_remap_all_init_lits)
    done
qed

definition cdcl_twl_stgy_restart_abs_wl_D_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_D_inv S0 brk T n \<longleftrightarrow>
    cdcl_twl_stgy_restart_abs_wl_inv S0 brk T n \<and>
    literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T\<close>

definition cdcl_GC_clauses_pre_wl_D :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_GC_clauses_pre_wl_D S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    cdcl_GC_clauses_pre_wl T
  )\<close>


end


end
