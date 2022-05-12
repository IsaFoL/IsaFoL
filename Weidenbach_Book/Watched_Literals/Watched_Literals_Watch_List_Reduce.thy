theory Watched_Literals_Watch_List_Reduce
  imports Watched_Literals_List_Simp Watched_Literals_List_Reduce Watched_Literals_Watch_List
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

definition drop_clause_add_move_init_wl :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>drop_clause_add_move_init_wl = (\<lambda>(M, N, D, NE0, UE, NEk, UEk, NS, US, N0, U0, Q, W) C.
     (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE0, UE, NEk, UEk, NS, {#}, N0, U0, Q, W))\<close>

definition drop_clause_wl :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>drop_clause_wl = (\<lambda>(M, N, D, NE0, UE, NS, US, N0, U0, Q, W) C.
     (M, fmdrop C N, D, NE0, UE, NS, {#}, N0, U0, Q, W))\<close>

lemma reduce_dom_clauses_fmdrop:
  \<open>reduce_dom_clauses N0 N \<Longrightarrow> reduce_dom_clauses N0 (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def distinct_mset_remove1_All)

lemma correct_watching_fmdrop:
  assumes
    irred: \<open>\<not> irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching' (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    C2: \<open>length (N \<propto> C) \<noteq> 2\<close> and
    blit: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching' (M, fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W)\<close> and
     \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
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
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
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
  show  \<open>correct_watching' (M, fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W)\<close>
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
  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W) \<Longrightarrow>
    x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> for x
    using assms(1,2)
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def all_lits_of_mm_union
      image_mset_remove1_mset_if)

  show \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W)\<close>
     using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def all_lits_of_mm_union
       dest: multi_member_split all_lits_of_mm_diffD)
qed

lemma correct_watching'_fmdrop:
  assumes
    irred: \<open>\<not> irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching' (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching'_nobin (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  let ?\<L> = \<open>all_init_lits_of_wl ?S\<close>
  have
    Hdist: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)\<close> and
    H2: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US,N0, U0,  {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
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
  show  \<open>correct_watching'_nobin (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
    unfolding correct_watching'_nobin.simps clause_to_update_def
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
  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], fmdrop C N, D, NE, UE, NEk, UEk, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
           x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> for x
    using assms
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def
      all_lits_of_mm_union image_mset_remove1_mset_if)
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def all_lits_of_mm_union
       dest: multi_member_split all_lits_of_mm_diffD)
qed

lemma all_init_lits_of_wl_fmdrop_addNEk[simp]:
  \<open>irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
  (all_init_lits_of_wl (M, fmdrop C N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, US, N0, U0, Q, W)) =
  (all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))\<close>
  using distinct_mset_dom[of N]
  by (auto simp: all_init_lits_of_wl_def ran_m_def dest!: multi_member_split
    intro!: arg_cong[of _ _ all_lits_of_mm]
    intro!: filter_mset_cong2 image_mset_cong2)

lemma correct_watching'_fmdrop':
  assumes
    irred: \<open>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'_nobin (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
  shows \<open>correct_watching'_nobin (M, fmdrop C N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, {#}, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  let ?\<L> = \<open>all_init_lits_of_wl ?S\<close>
  have
    Hdist: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow>
          K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)\<close> and
    H2: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching'_nobin.simps clause_to_update_def
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
  show \<open>correct_watching'_nobin (M, fmdrop C N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
    unfolding correct_watching'_nobin.simps clause_to_update_def
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
  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
           x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> for x
    using assms
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def
      all_lits_of_mm_union image_mset_remove1_mset_if)
  have \<open>(N \<propto> C, irred N C) \<in># (init_clss_l N)\<close>
    using assms by (auto simp: ran_m_def dest!: multi_member_split) (metis prod.collapse)
  from multi_member_split[OF this]
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
    using distinct_mset_dom[of N]
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if all_lits_of_mm_add_mset
          all_lits_of_mm_union literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def
       dest: multi_member_split all_lits_of_mm_diffD)
qed


lemma correct_watching'_fmdrop'':
  assumes
    irred: \<open>\<not>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching'_nobin (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  shows \<open>correct_watching'_nobin (M, fmdrop C N, D, NE, UE, NEk, add_mset (mset (N \<propto> C)) UEk, NS, {#}, N0, U0, Q, W)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, UE, NEk, add_mset (mset (N \<propto> C)) UEk, NS, {#},  N0, U0, Q, W)\<close>
proof -
  let ?S = \<open>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  let ?\<L> = \<open>all_init_lits_of_wl ?S\<close>
  have
    Hdist: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       distinct_watched (W L)\<close> and
    H1: \<open>\<And>L i K b. L\<in>#?\<L> \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)\<close> and
    H2: \<open>\<And>L. L\<in>#?\<L> \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching'_nobin.simps clause_to_update_def
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
  show  \<open>correct_watching'_nobin (M, fmdrop C N, D, NE, UE, NEk, add_mset (mset (N \<propto> C)) UEk, NS, {#}, N0, U0, Q, W)\<close>
    unfolding correct_watching'_nobin.simps clause_to_update_def
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

  have [dest!]: \<open>x \<in># all_learned_lits_of_wl ([], fmdrop C N, D, NE, UE, NEk, add_mset (mset (N \<propto> C)) UEk, NS, {#}, N0, U0, Q, W) \<Longrightarrow>
           x \<in># all_learned_lits_of_wl ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> for x
    using assms
    by (auto dest: all_lits_of_mm_diffD simp: all_learned_lits_of_wl_def
      all_lits_of_mm_union image_mset_remove1_mset_if)
  have \<open>(N \<propto> C, irred N C) \<in># (learned_clss_l N)\<close>
    using assms by (auto simp: ran_m_def dest!: multi_member_split) (metis prod.collapse)
  from multi_member_split[OF this]
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n' (M, fmdrop C N, D, NE, UE, NEk, add_mset (mset (N \<propto> C)) UEk, NS, {#}, N0, U0, Q, W)\<close>
    using distinct_mset_dom[of N]
    using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def image_mset_remove1_mset_if all_lits_of_mm_add_mset
          all_lits_of_mm_union literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def
      dest: multi_member_split all_lits_of_mm_diffD)
qed

definition remove_one_annot_true_clause_one_imp_wl_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_pre i T \<longleftrightarrow>
     (\<exists>T'. (T, T') \<in> state_wl_l None \<and>
       remove_one_annot_true_clause_one_imp_pre i T' \<and>
       correct_watching'_nobin T \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

definition replace_annot_wl_pre :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>replace_annot_wl_pre L C S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> L \<in># all_init_lits_of_wl S \<and>
    replace_annot_l_pre L C S' \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    correct_watching'_nobin S)\<close>

definition replace_annot_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>replace_annot_wl L C =
    (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(replace_annot_wl_pre L C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
      RES {(M', N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W)| M'.
       (\<exists>M2 M1 C. M = M2 @ Propagated L C # M1 \<and> M' = M2 @ Propagated L 0 # M1)}
   })\<close>

lemma replace_annot_l_pre_replace_annot_wl_pre: \<open>(((L, C), S), (L', C'), S')
    \<in> Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
      {(S, T).
       (S, T) \<in> state_wl_l None \<and>
       correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<Longrightarrow>
    replace_annot_l_pre L' C' S' \<Longrightarrow>
    replace_annot_wl_pre L C S\<close>
    unfolding replace_annot_wl_pre_def replace_annot_l_pre_alt_def
    unfolding replace_annot_l_pre_def[symmetric]
    by (rule exI[of _ \<open>S'\<close>])
      (auto simp add: ac_simps all_init_lits_of_wl_def)

lemma all_learned_lits_of_wl_all_init_lits_of_wlD[intro]:
  \<open>set_mset (all_learned_lits_of_wl (M, ab, ac, ad, ae, NEk, UEk, af, ag, ah, ai, aj, ba))
       \<subseteq> set_mset (all_init_lits_of_wl (M, ab, ac, ad, {#}, NEk, {#}, af, {#}, ah, {#}, aj, ba)) \<Longrightarrow>
       x \<in># all_learned_lits_of_wl (M, ab, ac, ad, {#}, NEk, UEk, af, {#}, ah, {#}, aj, ba) \<Longrightarrow>
       x \<in># all_init_lits_of_wl (M, ab, ac, ad, {#}, NEk, {#}, af, {#}, ah, {#}, aj, ba)\<close>
  by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_wl_def
    all_lits_of_mm_union)

lemma replace_annot_wl_replace_annot_l:
  \<open>(uncurry2 replace_annot_wl, uncurry2 replace_annot_l) \<in>
    Id \<times>\<^sub>f nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and>
        literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
    \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and>
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
        correct_watching'_nobin.simps clause_to_update_def blits_in_\<L>\<^sub>i\<^sub>n'_def)
    done

definition remove_and_add_cls_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>remove_and_add_cls_wl C =
    (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, Q, W). do {
       ASSERT(C \<in># dom_m N);
        RETURN (M, fmdrop C N, D, NE, UE,
         (if irred N C then add_mset (mset (N\<propto>C)) else id) NEk,
	 (if \<not>irred N C then add_mset (mset (N\<propto>C)) else id) UEk, NS, {#}, Q, W)
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
    \<in> nat_rel \<times>\<^sub>f  {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> _ \<times>\<^sub>f ?A \<rightarrow>\<^sub>f _\<close>)
proof -

  have [refine0]: \<open>remove_and_add_cls_wl C S \<le>\<Down> ?A (remove_and_add_cls_l C' S')\<close>
    if \<open>(C, C') \<in> Id\<close> and \<open>(S, S') \<in> ?A\<close>
      for C C' S S'
    using that unfolding remove_and_add_cls_l_def remove_and_add_cls_wl_def
    by refine_rcg
     (auto intro!: RES_refine simp: state_wl_l_def
       intro: correct_watching'_fmdrop correct_watching'_fmdrop''
          correct_watching'_fmdrop')

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
       correct_watching'_nobin S \<and> correct_watching'_nobin T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
       literals_are_\<L>\<^sub>i\<^sub>n' T \<and>
       remove_one_annot_true_clause_imp_inv S' (i, T')))\<close>

definition remove_all_learned_subsumed_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close> where
\<open>remove_all_learned_subsumed_clauses_wl = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
   RETURN (M, N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W))\<close>

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
   \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
  apply (auto intro!: frefI nres_relI
    simp: remove_all_learned_subsumed_clauses_wl_def remove_all_learned_subsumed_clauses_def
      literals_are_\<L>\<^sub>i\<^sub>n'_def correct_watching'_nobin.simps state_wl_l_def all_init_learned_lits_simps_Q
    clause_to_update_def all_lits_of_mm_union blits_in_\<L>\<^sub>i\<^sub>n'_def)
  by (meson basic_trans_rules(31) in_all_learned_lits_of_wl_addUS)

lemma remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp:
  \<open>(remove_one_annot_true_clause_imp_wl, remove_one_annot_true_clause_imp)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding remove_one_annot_true_clause_imp_wl_def remove_one_annot_true_clause_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>f {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching'_nobin S \<and>
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
  \<open>mark_garbage_wl = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q).
    (M, fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, WS, Q))\<close>

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
  by (auto intro!: frefI nres_relI
    simp: remove_all_learned_subsumed_clauses_wl_def remove_all_learned_subsumed_clauses_def
      literals_are_\<L>\<^sub>i\<^sub>n'_def correct_watching'.simps state_wl_l_def all_init_learned_lits_simps_Q
    clause_to_update_def all_lits_of_mm_union blits_in_\<L>\<^sub>i\<^sub>n'_def)
    (meson basic_trans_rules(31) in_all_learned_lits_of_wl_addUS)

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
  \<open>rewatch_clauses = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
  SPEC(\<lambda>(M', N', D', NE', UE',  NEk', UEk', NS', US', N0', U0', Q', W').
     (M, N, D, NE, UE,  NEk, UEk, NS, US, N0, U0, Q) = (M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q') \<and>
    correct_watching (M, N', D, NE, UE, NEk', UEk', NS', US', N0', U0', Q, W')))\<close>

definition mark_to_delete_clauses_wl_post where
  \<open>mark_to_delete_clauses_wl_post S T \<longleftrightarrow>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and> blits_in_\<L>\<^sub>i\<^sub>n S \<and>
       mark_to_delete_clauses_l_post S' T' \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n T \<and>
       correct_watching T \<and> get_unkept_learned_clss_wl T = {#} \<and> 
       get_subsumed_learned_clauses_wl T = {#} \<and> get_learned_clauses0_wl T = {#})\<close>

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
    upd: \<open>clauses_to_update_l Sa = {#}\<close> and
    empty:
       \<open>get_unkept_learned_clss_l Ta = {#}\<close>
      \<open>get_subsumed_learned_clauses_l Ta = {#}\<close>
      \<open>get_learned_clauses0_l Ta = {#}\<close>
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
  moreover have \<open>get_unkept_learned_clss_wl T = {#} \<and>
    get_subsumed_learned_clauses_wl T = {#} \<and>
    get_learned_clauses0_wl T = {#}\<close>
    using empty T_Ta by simp
   ultimately show ?thesis
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
    upd: \<open>clauses_to_update_l Sa = {#}\<close> and
    empty:
       \<open>get_unkept_learned_clss_l Ta = {#}\<close>
      \<open>get_subsumed_learned_clauses_l Ta = {#}\<close>
      \<open>get_learned_clauses0_l Ta = {#}\<close>
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
  moreover have \<open>get_unkept_learned_clss_wl T = {#} \<and>
    get_subsumed_learned_clauses_wl T = {#} \<and>
    get_learned_clauses0_wl T = {#}\<close>
    using empty T_Ta by simp
  ultimately show ?thesis
    using S_Sa T_Ta corr_T' corr_S' pre_l blits_S
    unfolding mark_to_delete_clauses_wl_post_def apply -
    apply (rule exI[of _ Sa])
    apply (rule exI[of _ Ta])
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
  RESTART |
  INPROCESS

context twl_restart_ops
begin

definition (in twl_restart_ops) restart_required_wl  :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> restart_type nres\<close> where
\<open>restart_required_wl S last_GC last_Restart n =  do {
  ASSERT(size (get_all_learned_clss_wl S) \<ge> last_GC);
  ASSERT(size (get_all_learned_clss_wl S) \<ge> last_Restart);
  SPEC (\<lambda>b.
  (b = GC \<longrightarrow> f n < size (get_all_learned_clss_wl S) - last_GC) \<and>
  (b = INPROCESS \<longrightarrow> f n < size (get_all_learned_clss_wl S) - last_GC) \<and>
  (b = RESTART \<longrightarrow> last_Restart < size (get_all_learned_clss_wl S)))}\<close>

definition (in twl_restart_ops) cdcl_twl_stgy_restart_abs_wl_inv
   :: \<open>'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl \<times> nat \<times> nat \<times> nat \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 = (\<lambda>(brk, T, last_GC, last_Restart, n).
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0' (brk, T', last_GC, last_Restart, n) \<and>
       (\<not>brk \<longrightarrow> correct_watching T)))\<close>
end


definition (in -) cdcl_GC_clauses_pre_wl :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_GC_clauses_pre_wl S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    cdcl_GC_clauses_pre T
  )\<close>

definition cdcl_GC_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_GC_clauses_wl = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
  ASSERT(cdcl_GC_clauses_pre_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
  let b = True;
  if b then do {
    (N', _) \<leftarrow> SPEC (\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N'') \<and>
      0 \<notin># dom_m N'');
    Q \<leftarrow> SPEC(\<lambda>Q. correct_watching' (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)\<and> literals_are_\<L>\<^sub>i\<^sub>n' (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
    RETURN (M, N', D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, WS, Q)
  }
  else RETURN (M, N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, WS, Q)})\<close>

lemma cdcl_GC_clauses_wl_cdcl_GC_clauses:
  \<open>(cdcl_GC_clauses_wl, cdcl_GC_clauses) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f \<langle>{(S::'v twl_st_wl, S').
  (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    get_unkept_learned_clss_wl S = {#} \<and>
    get_subsumed_learned_clauses_wl S = {#} \<and>
    get_learned_clauses0_wl S = {#}}\<rangle>nres_rel\<close>
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
      dest: literals_are_\<L>\<^sub>i\<^sub>n'_empty(6-))
  subgoal by auto
  done

definition mark_to_delete_clauses_GC_wl_inv
  :: \<open>'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> 'v twl_st_wl\<times> nat list  \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_GC_wl_inv = (\<lambda>S xs0 (i, T, xs).
     \<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
      mark_to_delete_clauses_l_inv S' xs0 (i, T', xs) \<and>
      no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

lemma mark_to_delete_clauses_GC_wl_inv_alt_def:
  \<open>mark_to_delete_clauses_GC_wl_inv = (\<lambda>S xs0 (i, T, xs).
     \<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
     mark_to_delete_clauses_l_inv S' xs0 (i, T', xs) \<and>
     set (get_all_mark_of_propagated (get_trail_wl T)) \<subseteq> set (get_all_mark_of_propagated (get_trail_wl S)) \<union> {0} \<and> 
      no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>
   unfolding mark_to_delete_clauses_GC_wl_inv_def case_prod_beta
   apply (intro  impI iffI allI ext; normalize_goal+)
   subgoal for S xs0 p x xa
     by (rule_tac x=x in exI, rule_tac x=xa in exI)
      (auto simp: mark_to_delete_clauses_l_inv_def
       dest!: rtranclp_remove_one_annot_true_clause_get_all_mark_of_propagated)
   subgoal for S xs0 p x xa
     by (rule_tac x=x in exI, rule_tac x=xa in exI) auto
   done

definition mark_to_delete_clauses_GC_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>
  where
  \<open>mark_to_delete_clauses_GC_wl_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> mark_to_delete_clauses_l_GC_pre T \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

lemma mark_to_delete_clause_GC_wl_pre_alt_def:
  \<open>mark_to_delete_clauses_GC_wl_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> mark_to_delete_clauses_l_GC_pre T \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S \<and>  set (get_all_mark_of_propagated (get_trail_wl S)) \<subseteq> {0})\<close>
  unfolding mark_to_delete_clauses_GC_wl_pre_def
  apply (rule iffI impI conjI; normalize_goal+)
  subgoal for T
    by (rule exI[of _ T]) (auto simp: mark_to_delete_clauses_l_GC_pre_def)
  subgoal for T
    by (rule exI[of _ T]) (auto simp: mark_to_delete_clauses_l_GC_pre_def)
  done

text \<open>
  Unlike the @{thm[source] mark_to_delete_clauses_wl_def}, this version is only used for garbage
  collection. Hence, there are a few differences.
\<close>
definition mark_to_delete_clauses_GC_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_GC_wl = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_GC_wl_pre S);
    xs \<leftarrow> collect_valid_indices_wl S;
    l \<leftarrow> SPEC(\<lambda>_:: nat. True);
    (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_GC_wl_inv S xs\<^esup>
      (\<lambda>(i, S, xs). i < length xs)
      (\<lambda>(i, T, xs). do {
        if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	  ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
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

lemma mark_to_delete_clauses_GC_wl_invD1:
  assumes \<open>mark_to_delete_clauses_GC_wl_inv S xs (i, T, ys)\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>0 < length (get_clauses_wl T \<propto> C)\<close>
  shows
    \<open>get_clauses_wl T \<propto> C ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)\<close>
proof -
  have \<open>get_clauses_wl T \<propto> C ! 0 \<in># all_lits_st T\<close>
    using assms(2,3) by auto
  moreover have \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
    using assms unfolding mark_to_delete_clauses_GC_wl_inv_def by blast
  ultimately show \<open>?thesis\<close>
    unfolding all_lits_st_init_learned \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms literals_are_\<L>\<^sub>i\<^sub>n'_def
    by auto
qed

lemma no_lost_clause_in_WL_drop_irrel[simp]:
  \<open>\<not>irred a C \<Longrightarrow>
  no_lost_clause_in_WL (x1d, a, aa, ab, ac, NEk, UEk, ad, US, af, ag, ah, b) \<Longrightarrow>
  no_lost_clause_in_WL (x1d, fmdrop C a, aa, ab, {#}, NEk, UEk, ad, {#}, af, {#}, ah, b)\<close>
  by (auto simp: no_lost_clause_in_WL_def all_init_lits_of_wl_def
    dest: in_diffD)

lemma literals_are_\<L>\<^sub>i\<^sub>n'_drop_irrel:
  assumes
    irred: \<open>\<not> irred N C\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  shows
    \<open>literals_are_\<L>\<^sub>i\<^sub>n'  (M, fmdrop C N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W)\<close>
  using assms
  by (cases \<open>C \<in># dom_m N\<close>)
    (auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def
      all_learned_lits_of_wl_def image_mset_remove1_mset_if all_lits_of_mm_union
      all_init_lits_of_wl_def learned_clss_l_l_fmdrop ran_m_fmdrop_notin
      split: if_splits
      dest!: all_lits_of_mm_diffD)

lemma remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses3:
  \<open>(remove_all_learned_subsumed_clauses_wl, remove_all_learned_subsumed_clauses)
  \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
  \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI
    simp: remove_all_learned_subsumed_clauses_wl_def remove_all_learned_subsumed_clauses_def
    literals_are_\<L>\<^sub>i\<^sub>n'_def correct_watching'.simps state_wl_l_def
    all_init_lits_of_wl_def all_learned_lits_of_wl_def
    no_lost_clause_in_WL_def
    clause_to_update_def all_lits_of_mm_union blits_in_\<L>\<^sub>i\<^sub>n'_def)

lemma mark_to_delete_clauses_wl_mark_to_delete_clauses_l2:
  \<open>(mark_to_delete_clauses_GC_wl, mark_to_delete_clauses_l)
  \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
    set (get_all_mark_of_propagated (get_trail_wl S)) \<subseteq> {0}} \<rightarrow>\<^sub>f
  \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S  \<le> \<Down> Id (collect_valid_indices S')\<close>
    if \<open>(S, S') \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and>
           mark_to_delete_clauses_GC_wl_pre S}\<close>
    for S S'
    using that by (auto simp: collect_valid_indices_wl_def collect_valid_indices_def)
  have if_inv: \<open>(if A then RETURN P else RETURN Q) = RETURN (if A then P else Q)\<close> for A P Q
    by auto
  have Ball_range[simp]: \<open>(\<forall>x\<in>range f \<union> range g. P x)\<longleftrightarrow>(\<forall>x. P (f x) \<and> P (g x))\<close> for P f g
    by auto
  show ?thesis
    unfolding mark_to_delete_clauses_GC_wl_def mark_to_delete_clauses_l_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
      R = \<open>{((i, S, xs), (j, T, ys)). i = j \<and> (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and>
             xs = ys \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry]
      remove_all_learned_subsumed_clauses_wl_remove_all_learned_subsumed_clauses3[THEN fref_to_Down])
    subgoal for x y
      unfolding mark_to_delete_clauses_GC_wl_pre_def mark_to_delete_clauses_l_GC_pre_def
        mark_to_delete_clauses_l_pre_def
      apply normalize_goal+
      apply (rule_tac x=y in exI)
      by fastforce
    subgoal by auto
    subgoal by (auto simp: state_wl_l_def)
    subgoal unfolding mark_to_delete_clauses_GC_wl_inv_def by fast
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal for x y xs xsa l to_keep xa x' x1 x2 x1a x2a x1b x2b x1c x2c
      by (auto simp: mark_to_delete_clauses_GC_wl_invD1)
    subgoal by (auto simp: state_wl_l_def can_delete_def
      mark_to_delete_clauses_GC_wl_inv_alt_def
      dest!: split_list)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal
      by (auto simp: state_wl_l_def correct_watching_fmdrop mark_garbage_wl_def
          mark_garbage_l_def
        literals_are_\<L>\<^sub>i\<^sub>n'_drop_irrel
        split: prod.splits)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: ac_simps)
    done
qed

lemma correct_watching'_nobin_clauses_pointed_to:
  assumes
    xa_xb: \<open>(xa, xb) \<in> state_wl_l None\<close> and
    corr: \<open>correct_watching'_nobin xa\<close> and
    pre: \<open>cdcl_GC_clauses_pre xb\<close> and
    L: \<open>literals_are_\<L>\<^sub>i\<^sub>n' xa\<close>
  shows \<open>set_mset (dom_m (get_clauses_wl xa))
         \<subseteq> clauses_pointed_to
            (Neg ` set_mset (all_init_atms_st xa) \<union>
             Pos ` set_mset (all_init_atms_st xa))
            (get_watched_wl xa)\<close>
        (is ?G1 is \<open>_ \<subseteq> ?A\<close>) and
    \<open>no_lost_clause_in_WL xa\<close> (is ?G2)
proof -
  let ?\<A> = \<open>all_init_atms (get_clauses_wl xa) (get_unit_init_clss_wl xa)\<close>
  show ?G1
  proof
    fix C
    assume C: \<open>C \<in># dom_m (get_clauses_wl xa)\<close>
    obtain M N D NE UE NEk UEk NS US N0 U0 Q W where
      xa: \<open>xa = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
      by (cases xa)
    obtain x where
      xb_x: \<open>(xb, x) \<in> twl_st_l None\<close> and
      \<open>twl_list_invs xb\<close> and
      struct_invs: \<open>twl_struct_invs x\<close> and
      \<open>get_conflict_l xb = None\<close> and
      \<open>clauses_to_update_l xb = {#}\<close> and
      \<open>count_decided (get_trail_l xb) = 0\<close> and
      \<open>\<forall>L\<in>set (get_trail_l xb). mark_of L = 0\<close>
      using pre unfolding cdcl_GC_clauses_pre_def by fast
    have \<open>twl_st_inv x\<close>
      using xb_x C struct_invs
      by (auto simp: twl_struct_invs_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
    then have le0: \<open>get_clauses_wl xa \<propto> C \<noteq> []\<close>
      using xb_x C xa_xb
      by (cases x; cases \<open>irred N C\<close>)
        (auto simp: twl_struct_invs_def twl_st_inv.simps
          twl_st_l_def state_wl_l_def xa ran_m_def conj_disj_distribR
          Collect_disj_eq Collect_conv_if
        dest!: multi_member_split)
    then have le: \<open>N \<propto> C ! 0 \<in> set (watched_l (N \<propto> C))\<close>
      by (cases \<open>N \<propto> C\<close>) (auto simp: xa)
    have eq: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NE)) =
          set_mset (all_lits_of_mm (mset `# init_clss_lf N + NE))\<close>
       by (auto simp del: all_init_atms_def[symmetric]
          simp: all_init_atms_def xa \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm[symmetric]
            all_init_lits_def)

    have H: \<open>get_clauses_wl xa \<propto> C ! 0 \<in># all_init_lits_of_wl xa\<close>
      using L C le0 apply -
      unfolding all_init_atms_def[symmetric] all_init_lits_def[symmetric]
      apply (subst literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF xa_xb xb_x struct_invs])
      apply (cases \<open>N \<propto> C\<close>; auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def ran_m_def eq
            all_lits_of_mm_add_mset is_\<L>\<^sub>a\<^sub>l\<^sub>l_def xa all_lits_of_m_add_mset
            \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits all_lits_st_def
          dest!: multi_member_split)
      done
    moreover {
      have \<open>{#i \<in># fst `# mset (W (N \<propto> C ! 0)). i \<in># dom_m N#} =
             add_mset C {#Ca \<in># remove1_mset C (dom_m N). N \<propto> C ! 0 \<in> set (watched_l (N \<propto> Ca))#}\<close>
        using corr H C le unfolding xa
        by (auto simp: clauses_pointed_to_def correct_watching'_nobin.simps xa
          simp flip: all_init_atms_def all_init_lits_def all_init_atms_alt_def
            all_init_lits_alt_def
          simp: clause_to_update_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split)
      from arg_cong[OF this, of set_mset] have \<open>C \<in> fst ` set (W (N \<propto> C ! 0))\<close>
        using corr H C le unfolding xa
        by (auto simp: clauses_pointed_to_def correct_watching'.simps xa
          simp: all_init_atms_def all_init_lits_def clause_to_update_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split) }
    ultimately show \<open>C \<in> ?A\<close>
      by (cases \<open>N \<propto> C ! 0\<close>)
        (auto simp: clauses_pointed_to_def correct_watching'.simps xa
          simp flip: all_init_lits_def all_init_atms_alt_def
            all_init_lits_alt_def 
          simp: clause_to_update_def all_init_atms_st_def all_init_lits_of_wl_def all_init_atms_def
          simp del: all_init_atms_def[symmetric]
        dest!: multi_member_split)
  qed
  moreover have \<open>set_mset (all_init_lits_of_wl xa) =
    Neg ` set_mset (all_init_atms_st xa) \<union> Pos ` set_mset (all_init_atms_st xa)\<close>
    unfolding all_init_lits_of_wl_def
      all_lits_of_mm_def all_init_atms_st_def all_init_atms_def
    by (auto simp: all_init_atms_def all_init_lits_def all_lits_of_mm_def image_image
      image_Un
      simp del: all_init_atms_def[symmetric])
  moreover have \<open>distinct_watched (watched_by xa (Pos L))\<close>
    \<open>distinct_watched (watched_by xa (Neg L))\<close>
    if \<open>L \<in># all_init_atms_st xa\<close> for L
    using that corr
    by (cases xa;
      auto simp: correct_watching'_nobin.simps all_init_lits_of_wl_def all_init_atms_def
      all_lits_of_mm_union all_init_lits_def all_init_atms_st_def literal.atm_of_def
      in_all_lits_of_mm_uminus_iff[symmetric, of \<open>Pos _\<close>]
      simp del: all_init_atms_def[symmetric]
      split: literal.splits; fail)+
  ultimately show ?G2
    unfolding no_lost_clause_in_WL_def
    by (auto simp del: all_init_atms_def[symmetric]) 
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
           D \<leftarrow> SPEC(\<lambda>D. D \<notin># dom_m N' \<and> D \<noteq> 0);
           RETURN (i+1, fmdrop C N, fmupd D (N \<propto> C, irred N C) N')
        } else RETURN (i+1, N, N')
       }) (0, N, N');
    RETURN (N, N')
   })\<close>
 
lemma cdcl_GC_clauses_prog_copy_wl_entry:
  fixes A :: \<open>'v literal\<close> and WS :: \<open>'v literal \<Rightarrow> 'v watched\<close>
  defines [simp]: \<open>W \<equiv> WS A\<close>
  assumes \<open>ran m0 \<subseteq> set_mset (dom_m N0') \<and>
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


definition (in -)cdcl_GC_clauses_prog_wl_inv
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
  \<open>cdcl_GC_clauses_prog_wl = (\<lambda>(M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS). do {
    ASSERT(cdcl_GC_clauses_pre_wl (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS));
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset (all_init_atms_st (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS)));
    (_, (N, N', WS)) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_GC_clauses_prog_wl_inv \<A> N\<^sub>0\<^esup>
      (\<lambda>(\<B>, _). \<B> \<noteq> {#})
      (\<lambda>(\<B>, (N, N', WS)). do {
        ASSERT(\<B> \<noteq> {#});
        A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
        (N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_single_wl N WS A N';
        RETURN (remove1_mset A \<B>, (N, N', WS))
      })
      (\<A>, (N\<^sub>0, fmempty, WS));
    RETURN (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS)
  })\<close>

lemma no_lost_clause_in_WL_no_lost_clause_in_WL0D:
  \<open>no_lost_clause_in_WL S \<Longrightarrow> no_lost_clause_in_WL0 S\<close>
  by (auto simp: no_lost_clause_in_WL_def no_lost_clause_in_WL0_def)

lemma no_lost_clause_in_WL_alt_def:
  \<open>no_lost_clause_in_WL0 (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS) \<longleftrightarrow>
  set_mset (dom_m N\<^sub>0) \<subseteq> clauses_pointed_to
  (Neg ` set_mset (all_init_atms N\<^sub>0 (NE+NEk+NS+N0)) \<union> Pos ` set_mset (all_init_atms N\<^sub>0 (NE+NEk+NS+N0))) WS\<close>
proof -
  have [simp]: \<open>set_mset (all_init_lits_of_wl ([], N\<^sub>0, D, NE, {#}, NEk, {#}, NS, {#}, N0, {#}, Q, WS)) =
    (Neg ` set_mset (all_init_atms N\<^sub>0 (NE + NEk+ NS + N0)) \<union> Pos ` set_mset (all_init_atms N\<^sub>0 (NE + NEk + NS + N0)))\<close>
    unfolding all_init_lits_of_wl_def all_init_atms_def  image_image
      all_lits_of_mm_def all_init_lits_def set_image_mset image_mset_union
      sum_mset.union image_Un
    by (auto simp add: image_image image_Un)
  show ?thesis
    unfolding no_lost_clause_in_WL0_def
    by auto
qed

lemma cdcl_GC_clauses_prog_wl:
  assumes \<open>((M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS), S) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS) \<and>
    cdcl_GC_clauses_pre S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS)\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS) \<le>
      (SPEC(\<lambda>(M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q', WS').
         (M', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q') = (M, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N\<^sub>0, (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N' \<and> (\<forall>L \<in># all_init_lits N\<^sub>0 (NE+NEk+NS+N0). WS' L = [])))\<close>
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
    subgoal using assms
      no_lost_clause_in_WL_no_lost_clause_in_WL0D[of \<open>(M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS)\<close>, unfolded no_lost_clause_in_WL_alt_def]
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by (auto simp: all_init_atms_st_def)
    subgoal by auto
    subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi aj bj ak bk x s al bl am
        bm an bn xa
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      apply clarify
      apply (rule order_trans,
         rule_tac m=m and \<A>=al in cdcl_GC_clauses_prog_single_wl)
      subgoal by (auto simp: all_init_atms_st_def)
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
          apply (solves \<open>auto\<close>)[]
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
       (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_init_atms_def all_init_atms_st_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split)
  done
qed


lemma cdcl_GC_clauses_prog_wl2:
  assumes \<open>((M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS), S) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS) \<and>
    cdcl_GC_clauses_pre S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS)\<close>
  \<open>N\<^sub>0 = N\<^sub>0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS) \<le> \<Down> Id
      (SPEC(\<lambda>(M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q', WS').
         (M', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q') = (M, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N\<^sub>0', (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N' \<and> (\<forall>L \<in># all_init_lits N\<^sub>0 (NE+NEk+NS+N0). WS' L = [])))\<close>
proof -
  show ?thesis
    unfolding \<open>N\<^sub>0 = N\<^sub>0'\<close>[symmetric]
    apply (rule order_trans[OF cdcl_GC_clauses_prog_wl[OF assms(1)]])
    apply (rule RES_refine)
    apply (fastforce dest: rtranclp_GC_remap_all_init_lits)
    done
qed

end
