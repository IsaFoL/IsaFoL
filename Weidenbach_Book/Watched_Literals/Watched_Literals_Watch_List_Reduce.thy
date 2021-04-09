theory Watched_Literals_Watch_List_Reduce
  imports Watched_Literals_List_Simp Watched_Literals_List_Reduce Watched_Literals_Watch_List
    Watched_Literals_Watch_List_Inprocessing
    Watched_Literals_Watch_List_Restart
begin
no_notation funcset (infixr "\<rightarrow>" 60)

lemma GC_remap_all_init_atmsD:
  \<open>GC_remap (N, x, m) (N', x', m') \<Longrightarrow>
    all_init_atms N NE + all_init_atms m NE  = all_init_atms N' NE  + all_init_atms m' NE\<close>
  by (induction rule: GC_remap.induct[split_format(complete)])
    (auto simp: all_init_atms_def all_init_lits_def init_clss_l_fmdrop_if
       init_clss_l_fmupd_if image_mset_remove1_mset_if
    simp del: all_init_atms_def[symmetric]
    simp flip: image_mset_union all_lits_of_mm_add_mset all_lits_of_mm_union)

lemma rtranclp_GC_remap_all_init_atmsD:
  \<open>GC_remap\<^sup>*\<^sup>* (N, x, m) (N', x', m') \<Longrightarrow>
    all_init_atms N NE + all_init_atms m NE  = all_init_atms N' NE  + all_init_atms m' NE\<close>
  by (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
    (auto dest: GC_remap_all_init_atmsD)

lemma rtranclp_GC_remap_all_init_atms:
  \<open>GC_remap\<^sup>*\<^sup>* (x1a, Map.empty, fmempty) (fmempty, m, x1ad) \<Longrightarrow>
    all_init_atms x1ad NE = all_init_atms x1a NE\<close>
  by (auto dest!: rtranclp_GC_remap_all_init_atmsD[of _ _ _ _ _ _ NE])

lemma GC_remap_all_init_lits:
  \<open>GC_remap (N, m, new) (N', m', new') \<Longrightarrow>
    all_init_lits N NE + all_init_lits new NE = all_init_lits N' NE + all_init_lits new' NE\<close>
  by (induction rule: GC_remap.induct[split_format(complete)])
    (case_tac \<open>irred N C\<close> ; auto simp: all_init_lits_def init_clss_l_fmupd_if image_mset_remove1_mset_if
    simp flip: all_lits_of_mm_union)

lemma rtranclp_GC_remap_all_init_lits:
  \<open>GC_remap\<^sup>*\<^sup>* (N, m, new) (N', m', new') \<Longrightarrow>
  all_init_lits N NE + all_init_lits new NE = all_init_lits N' NE + all_init_lits new' NE\<close>
  by (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
    (auto dest: GC_remap_all_init_lits)

lemma subsumed_clauses_alt_def:
  \<open>subsumed_clauses S = subsumed_init_clauses S + subsumed_learned_clauses S\<close>
  by (cases S) auto

definition remove_all_annot_true_clause_imp_wl_inv
  :: \<open>'v twl_st_wl \<Rightarrow> _ \<Rightarrow> nat \<times> 'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_inv S xs = (\<lambda>(i, T).
     correct_watching'' S \<and> correct_watching'' T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' T \<and>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
        remove_all_annot_true_clause_imp_inv S' xs (i, T')))\<close>

definition drop_clause_add_move_init_wl :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>drop_clause_add_move_init_wl = (\<lambda>(M, N, D, NE0, UE, NS, US, N0, U0, Q, W) C.
     (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE0, UE, NS, {#}, N0, U0, Q, W))\<close>

definition drop_clause_wl :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>drop_clause_wl = (\<lambda>(M, N, D, NE0, UE, NS, US, N0, U0, Q, W) C.
     (M, fmdrop C N, D, NE0, UE, NS, {#}, N0, U0, Q, W))\<close>

definition remove_all_annot_true_clause_one_imp_wl
  :: \<open>nat \<times> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
\<open>remove_all_annot_true_clause_one_imp_wl = (\<lambda>(C, S). do {
      if C \<in># dom_m (get_clauses_wl S) then
        if irred (get_clauses_wl S) C
        then RETURN (drop_clause_add_move_init_wl S C)
        else RETURN (drop_clause_wl S C)
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
    \<open>correct_watching' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> and
    C2: \<open>length (N \<propto> C) \<noteq> 2\<close> and
    blit: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching' (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close> and
     \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  have
    Hdist: \<open>\<And>L i K b. L\<in>#all_init_lits_of_wl ?S \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#all_init_lits_of_wl ?S \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
         correctly_marked_as_binary N (i, K, b)\<close> and
    H1': \<open>\<And>L i K b. L\<in>#all_init_lits_of_wl ?S \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> b \<Longrightarrow>  i \<in># dom_m N\<close> and
    H2: \<open>\<And>L. L\<in># all_init_lits_of_wl ?S \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
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
  show  \<open>correct_watching' (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>
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
      by (auto 5 1  simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
        distinct_mset_remove1_All filter_mset_neq_cond 2 H2 dest: all_lits_of_mm_diffD
        dest: multi_member_split)
    done
  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
    x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> for x
    using assms(1,2)
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def all_lits_of_mm_union
      image_mset_remove1_mset_if)

  show \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>
     using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def all_lits_of_mm_union
       dest: multi_member_split all_lits_of_mm_diffD)
qed

lemma correct_watching''_fmdrop:
  assumes
    irred: \<open>\<not> irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching'' (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  let ?\<L> = \<open>all_init_lits_of_wl ?S\<close>
  have
    Hdist: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L\<close> and
    H2: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NS, US,N0, U0,  {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
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
  show  \<open>correct_watching'' (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>
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
      by (auto 5 1  simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
        distinct_mset_remove1_All filter_mset_neq_cond 2 H2 dest: all_lits_of_mm_diffD
        dest: multi_member_split)
    done
  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
           x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> for x
    using assms
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def
      all_lits_of_mm_union image_mset_remove1_mset_if)
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, Q, W)\<close>
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def all_lits_of_mm_union
       dest: multi_member_split all_lits_of_mm_diffD)
qed

lemma correct_watching''_fmdrop':
  assumes
    irred: \<open>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching'' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, NS, {#}, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, NS, {#}, N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  let ?\<L> = \<open>all_init_lits_of_wl ?S\<close>
  have
    Hdist: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow>
          K \<in> set (N \<propto> i) \<and> K \<noteq> L\<close> and
    H2: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
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
  show \<open>correct_watching'' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, NS, {#}, N0, U0, Q, W)\<close>
    unfolding correct_watching''.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
        Hdist[of L] irred C
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
  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
           x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> for x
    using assms
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def
      all_lits_of_mm_union image_mset_remove1_mset_if)
  have \<open>(N \<propto> C, irred N C) \<in># (init_clss_l N)\<close>
    using assms by (auto simp: ran_m_def dest!: multi_member_split) (metis prod.collapse)
  from multi_member_split[OF this]
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, NS, {#}, N0, U0, Q, W)\<close>
    using distinct_mset_dom[of N]
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if all_lits_of_mm_add_mset
          all_lits_of_mm_union literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def
       dest: multi_member_split all_lits_of_mm_diffD)
qed


lemma correct_watching''_fmdrop'':
  assumes
    irred: \<open>\<not>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching'' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, NS, {#}, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, NS, {#},  N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NS, US, N0, U0, Q, W)\<close>
  let ?\<L> = \<open>all_init_lits_of_wl ?S\<close>
  have
    Hdist: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and>
          K \<noteq> L\<close> and
    H2: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
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
  show  \<open>correct_watching'' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, NS, {#}, N0, U0, Q, W)\<close>
    unfolding correct_watching''.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
        Hdist[of L] assms
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

  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
           x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NS, US, N0, U0, Q, W)\<close> for x
    using assms
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def
      all_lits_of_mm_union image_mset_remove1_mset_if)
  have \<open>(N \<propto> C, irred N C) \<in># (learned_clss_l N)\<close>
    using assms by (auto simp: ran_m_def dest!: multi_member_split) (metis prod.collapse)
  from multi_member_split[OF this]
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, NS, {#}, N0, U0, Q, W)\<close>
    using distinct_mset_dom[of N]
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if all_lits_of_mm_add_mset
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
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> L \<in># all_init_lits_of_wl S \<and>
    replace_annot_l_pre L C S' \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    correct_watching'' S)\<close>

definition replace_annot_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>replace_annot_wl L C =
    (\<lambda>(M, N, D, NE, UE, NS, US, N0, U0, Q, W). do {
      ASSERT(replace_annot_wl_pre L C (M, N, D, NE, UE, NS, US, N0, U0, Q, W));
      RES {(M', N, D, NE, UE, NS, {#}, N0, U0, Q, W)| M'.
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
      (auto simp add: ac_simps all_init_lits_of_wl_def)

lemma all_learned_lits_of_wl_all_init_lits_of_wlD[intro]:
  \<open>set_mset (all_learned_lits_of_wl (M, ab, ac, ad, ae, af, ag, ah, ai, aj, ba))
       \<subseteq> set_mset (all_init_lits_of_wl (M, ab, ac, ad, ae, af, {#}, ah, ai, aj, ba)) \<Longrightarrow>
       x \<in># all_learned_lits_of_wl (M, ab, ac, ad, ae, af, {#}, ah, ai, aj, ba) \<Longrightarrow>
       x \<in># all_init_lits_of_wl (M, ab, ac, ad, ae, af, {#}, ah, ai, aj, ba)\<close>
  by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_wl_def
    all_lits_of_mm_union)

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
        (force simp: state_wl_l_def literals_are_\<L>\<^sub>i\<^sub>n'_def ac_simps
          all_lits_of_mm_union
          correct_watching''.simps clause_to_update_def blits_in_\<L>\<^sub>i\<^sub>n'_def)
    done

definition remove_and_add_cls_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>remove_and_add_cls_wl C =
    (\<lambda>(M, N, D, NE, UE, NS, US, Q, W). do {
       ASSERT(C \<in># dom_m N);
        RETURN (M, fmdrop C N, D,
         (if irred N C then add_mset (mset (N\<propto>C)) else id) NE,
	 (if \<not>irred N C then add_mset (mset (N\<propto>C)) else id) UE, NS, {#}, Q, W)
    })\<close>

definition remove_one_annot_true_clause_one_imp_wl
  :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i S. do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_pre i S);
      ASSERT(is_proped (rev (get_trail_wl S) ! i));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev (get_trail_wl S))!i = Propagated L C);
      ASSERT(Propagated L C \<in> set (get_trail_wl S));
      ASSERT(L \<in># all_init_lits_of_wl S);
      if C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<in># dom_m (get_clauses_wl S));
	S \<leftarrow> replace_annot_wl L C S;
	S \<leftarrow> remove_and_add_cls_wl C S;
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
        pcdcl_all_struct_invs_def state\<^sub>W_of_def
   by fast+

  show lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_init_atms_st x2) (get_trail_wl x2)\<close>
    using alien x2_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      literals_are_\<L>\<^sub>i\<^sub>n_def all_init_lits_of_wl_def all_atms_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms
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

  have [refine0]: \<open>remove_and_add_cls_wl C S \<le>\<Down> ?A (remove_and_add_cls_l C' S')\<close>
    if \<open>(C, C') \<in> Id\<close> and \<open>(S, S') \<in> ?A\<close>
      for C C' S S'
    using that unfolding remove_and_add_cls_l_def remove_and_add_cls_wl_def
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

definition remove_all_learned_subsumed_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close> where
\<open>remove_all_learned_subsumed_clauses_wl = (\<lambda>(M, N, D, NE, UE, NS, US, N0, U0, Q, W).
   RETURN (M, N, D, NE, UE, NS, {#}, N0, U0, Q, W))\<close>

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
    remove_all_learned_subsumed_clauses_wl S
  })\<close>

lemma remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses:
  \<open>(remove_all_learned_subsumed_clauses_wl, remove_all_learned_subsumed_clauses)
   \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
  by (force intro!: frefI nres_relI
    simp: remove_all_learned_subsumed_clauses_wl_def remove_all_learned_subsumed_clauses_def
      literals_are_\<L>\<^sub>i\<^sub>n'_def correct_watching''.simps state_wl_l_def
      clause_to_update_def all_lits_of_mm_union blits_in_\<L>\<^sub>i\<^sub>n'_def)

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
         R = \<open>nat_rel \<times>\<^sub>f {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and>
            literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN
        fref_to_Down_curry]
      remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses[THEN
        fref_to_Down])
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

definition mark_garbage_wl:: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>mark_garbage_wl = (\<lambda>C (M, N, D, NE, UE, NS, US, N0, U0, WS, Q).
    (M, fmdrop C N, D, NE, UE, NS, {#}, N0, U0, WS, Q))\<close>

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
    remove_all_learned_subsumed_clauses_wl S
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
  then have \<open>get_clauses_wl T \<propto> C ! 0 \<in># all_init_lits_of_wl T\<close>
    using nth_in_all_lits_stI[of C T 0]
    using assms(2,3) by (auto simp del: nth_in_all_lits_stI
      simp: all_lits_st_init_learned  literals_are_\<L>\<^sub>i\<^sub>n'_def)
  then show \<open>?thesis\<close>
    by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms)
qed

lemma remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses2:
  \<open>(remove_all_learned_subsumed_clauses_wl, remove_all_learned_subsumed_clauses)
   \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
  by (force intro!: frefI nres_relI
    simp: remove_all_learned_subsumed_clauses_wl_def remove_all_learned_subsumed_clauses_def
      literals_are_\<L>\<^sub>i\<^sub>n'_def correct_watching'.simps state_wl_l_def
      clause_to_update_def all_lits_of_mm_union blits_in_\<L>\<^sub>i\<^sub>n'_def)

lemma mark_to_delete_clauses_wl_mark_to_delete_clauses_l:
  \<open>(mark_to_delete_clauses_wl, mark_to_delete_clauses_l)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
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
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN
        fref_to_Down_curry]
      remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses2[THEN
        fref_to_Down])
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
          mark_garbage_l_def ac_simps
        split: prod.splits)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
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
  \<open>rewatch_clauses = (\<lambda>(M, N, D, NE, UE, NS, US, N0, U0, Q, W).
  SPEC(\<lambda>(M', N', D', NE', UE', NS', US', N0', U0', Q', W').
     (M, N, D, NE, UE, NS, US, N0, U0, Q) = (M', N', D', NE', UE', NS', US', N0', U0', Q') \<and>
    correct_watching (M, N', D, NE, UE, NS', US', N0', U0', Q, W')))\<close>

definition mark_to_delete_clauses_wl_post where
  \<open>mark_to_delete_clauses_wl_post S T \<longleftrightarrow>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and> blits_in_\<L>\<^sub>i\<^sub>n S \<and>
       mark_to_delete_clauses_l_post S' T' \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n T \<and>
       correct_watching T)\<close>

definition cdcl_twl_full_restart_wl_prog :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_twl_full_restart_wl_prog S = do {
    ASSERT(mark_to_delete_clauses_wl_pre S);
    T \<leftarrow> mark_to_delete_clauses_wl S;
    ASSERT(mark_to_delete_clauses_wl_post S T);
    RETURN T
  }\<close>


lemma correct_watching_correct_watching: \<open>correct_watching S \<Longrightarrow> correct_watching' S\<close>
  by (cases S, auto simp only: correct_watching.simps correct_watching'.simps all_lits_st_init_learned
    image_mset_union)

lemma (in -) [twl_st_l, simp]:
 \<open>(Sa, x) \<in> twl_st_l None \<Longrightarrow> get_all_learned_clss x =  mset `# (get_learned_clss_l Sa) + get_unit_learned_clss_l Sa + get_subsumed_learned_clauses_l Sa + get_learned_clauses0_l Sa\<close>
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

  have \<open>set_mset (all_init_lits_of_wl S) = set_mset (all_lits_st S)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF S_Sa Sa_x struct] .

  then have corr_S': \<open>correct_watching S\<close>
    using corr_S
    by (cases S; simp only: correct_watching'.simps correct_watching.simps)
  obtain y where
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* Sa Ta\<close> and
    Ta_y: \<open>(Ta, y) \<in> twl_st_l None\<close>  and
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* x y\<close> and
    struct: \<open>twl_struct_invs y\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF st list_invs confl upd Sa_x
      struct]
    by blast

  have eq: \<open>set_mset (all_init_lits_of_wl T) = set_mset (all_lits_st T)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF T_Ta Ta_y struct] .

  then have corr_T': \<open>correct_watching T\<close>
    using corr_T
    by (cases T; simp only: correct_watching'.simps correct_watching.simps)

  have \<open>blits_in_\<L>\<^sub>i\<^sub>n T\<close>
    using blits_T eq
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
       all_init_lits_def
    by (auto dest: multi_member_split simp: ac_simps)
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
  have \<open>set_mset (all_init_lits_of_wl S) = set_mset (all_lits_st S)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF S_Sa Sa_x struct] .
  then have corr_S': \<open>correct_watching S\<close>
    using corr_S
    by (cases S; simp only: correct_watching'.simps correct_watching.simps)
  obtain y where
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* Sa Ta\<close> and
    Ta_y: \<open>(Ta, y) \<in> twl_st_l None\<close>  and
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* x y\<close> and
    struct: \<open>twl_struct_invs y\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF st list_invs confl upd Sa_x
      struct]
    by blast


  have eq: \<open>set_mset (all_init_lits_of_wl T) = set_mset (all_lits_st T)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF T_Ta Ta_y struct] .

  then have corr_T': \<open>correct_watching T\<close>
    using corr_T
    by (cases T; simp only: correct_watching'.simps correct_watching.simps)

  have \<open>blits_in_\<L>\<^sub>i\<^sub>n T\<close>
    using blits_T eq
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def
    by (auto dest: multi_member_split simp: ac_simps)
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
  have eq: \<open>set_mset (all_init_lits_of_wl S) = set_mset (all_lits_st S)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF S_Sa Sa_x struct] .

  then have corr_S': \<open>correct_watching S\<close>
    using corr_S
    by (cases S; simp only: correct_watching'.simps correct_watching.simps)

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
    using blits_S eq
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
      all_init_lits_def all_lits_st_init_learned[of S] by auto
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


datatype restart_type =
  NO_RESTART |
  GC |
  RESTART

context twl_restart_ops
begin

definition (in twl_restart_ops) restart_required_wl  :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> restart_type nres\<close> where
\<open>restart_required_wl S last_GC last_Restart n =  do {
  ASSERT(size (get_all_learned_clss_wl S) \<ge> last_GC);
  ASSERT(size (get_all_learned_clss_wl S) \<ge> last_Restart);
  SPEC (\<lambda>b.
  (b = GC \<longrightarrow> f n < size (get_all_learned_clss_wl S) - last_GC) \<and>
  (b = RESTART \<longrightarrow> last_Restart < size (get_all_learned_clss_wl S)))}\<close>

definition (in twl_restart_ops) cdcl_twl_stgy_restart_abs_wl_inv
   :: \<open>'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl \<times> nat \<times> nat \<times> nat \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 = (\<lambda>(brk, T, last_GC, last_Restart, n).
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0' (brk, T', last_GC, last_Restart, n) \<and>
       correct_watching T))\<close>
end


definition (in -) cdcl_GC_clauses_pre_wl :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_GC_clauses_pre_wl S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> state_wl_l None \<and>
    correct_watching'' S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    cdcl_GC_clauses_pre T
  )\<close>

definition cdcl_GC_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_GC_clauses_wl = (\<lambda>(M, N, D, NE, UE, NS, US, N0, U0, WS, Q). do {
  ASSERT(cdcl_GC_clauses_pre_wl (M, N, D, NE, UE, NS, US, N0, U0, WS, Q));
  let b = True;
  if b then do {
    (N', _) \<leftarrow> SPEC (\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N'') \<and>
      0 \<notin># dom_m N'');
    Q \<leftarrow> SPEC(\<lambda>Q. correct_watching' (M, N', D, NE, UE, NS, US, N0, U0, WS, Q)\<and> literals_are_\<L>\<^sub>i\<^sub>n' (M, N', D, NE, UE, NS, US, N0, U0, WS, Q));
    RETURN (M, N', D, NE, UE, NS, {#}, N0, U0, WS, Q)
  }
  else RETURN (M, N, D, NE, UE, NS, {#}, N0, U0, WS, Q)})\<close>

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
    by (auto simp: state_wl_l_def blits_in_\<L>\<^sub>i\<^sub>n'_def literals_are_\<L>\<^sub>i\<^sub>n'_empty
      dest: multi_member_split)
  subgoal by auto
  done


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
    remove_all_learned_subsumed_clauses_wl S
  })\<close>

lemma mark_to_delete_clauses_wl2_invD1:
  assumes \<open>mark_to_delete_clauses_wl2_inv S xs (i, T, ys)\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>0 < length (get_clauses_wl T \<propto> C)\<close>
  shows
    \<open>get_clauses_wl T \<propto> C ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)\<close>
proof -
  have \<open>get_clauses_wl T \<propto> C ! 0 \<in># all_lits_st T\<close>
    using assms(2,3) by auto
  moreover have \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
    using assms unfolding mark_to_delete_clauses_wl2_inv_def by blast
  ultimately show \<open>?thesis\<close>
    unfolding all_lits_st_init_learned \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms literals_are_\<L>\<^sub>i\<^sub>n'_def
    by auto
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
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry]
      remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses[THEN fref_to_Down])
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
    subgoal by (auto simp: ac_simps)
    done
qed


end
