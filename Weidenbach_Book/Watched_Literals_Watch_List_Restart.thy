theory Watched_Literals_Watch_List_Restart
  imports Watched_Literals_List_Restart Watched_Literals.Watched_Literals_Watch_List "../lib/Explorer"
begin

text \<open>To ease the proof, we introduce the following ``alternative'' definitions, that only considers
  variables that are present in the initial clauses (which are never deleted from the set of
  clauses, but only moved to another component).
\<close>
fun correct_watching' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching' (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm (mset `# init_clss_lf N + NE).
       (\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> is_binary N (i, K, b)) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

declare correct_watching'.simps[simp del]

definition remove_all_annot_true_clause_imp_wl_inv
  :: \<open>'v twl_st_wl \<Rightarrow> _ \<Rightarrow> nat \<times> 'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_inv S xs = (\<lambda>(i, T).
     correct_watching' S \<and> correct_watching' T \<and>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
        remove_all_annot_true_clause_imp_inv S' xs (i, T')))\<close>

definition remove_all_annot_true_clause_imp_wl
  :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl = (\<lambda>L (M, N0, D, NE0, UE, Q, W). do {
    let xs = W L;
    (_, N, NE) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N, NE).
        remove_all_annot_true_clause_imp_wl_inv (M, N0, D, NE0, UE, Q, W) xs
          (i, M, N, D, NE, UE, Q, W)\<^esup>
      (\<lambda>(i, N, NE). i < length xs)
      (\<lambda>(i, N, NE). do {
        ASSERT(i < length xs);
        let (C, _, _) = xs!i;
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



lemma reduce_dom_clauses_fmdrop:
  \<open>reduce_dom_clauses N0 N \<Longrightarrow> reduce_dom_clauses N0 (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def distinct_mset_remove1_All)

lemma image_filter_replicate_mset:
  \<open>{#Ca \<in># replicate_mset m C. P Ca#} = (if P C then replicate_mset m C else {#})\<close>
  by (induction m) auto


lemma ran_m_lf_fmdrop:
  \<open>C \<in># dom_m N \<Longrightarrow> ran_m (fmdrop C N) = remove1_mset (the (fmlookup N C)) (ran_m N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>] dest!: multi_member_split
    intro!: image_mset_cong)


text \<open>change definition to all blits in \<^term>\<open>\<L>\<^sub>a\<^sub>l\<^sub>l\<close>?\<close>
lemma correct_watching_fmdrop:
  assumes 
    irred: \<open>\<not> irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching' (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching' (M, fmdrop C N, D, NE, UE, Q, W)\<close>
proof -
  have
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> is_binary N (i, K, b)\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching'.simps clause_to_update_def
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
  show ?thesis
    unfolding correct_watching'.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond is_binary.simps dest: all_lits_of_mm_diffD
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
qed

lemma correct_watching_fmdrop':
  assumes 
    irred: \<open>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching' (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching' (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, Q, W)\<close>
proof -
  have
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> is_binary N (i, K, b)\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching'.simps clause_to_update_def
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
  show ?thesis
    unfolding correct_watching'.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond is_binary.simps dest: all_lits_of_mm_diffD
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
qed


lemma correct_watching_fmdrop'':
  assumes 
    irred: \<open>\<not>irred N C\<close> and
    C: \<open>C \<in># dom_m N\<close> and
    \<open>correct_watching' (M', N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching' (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, Q, W)\<close>
proof -
  have
    H1: \<open>\<And>L i K b. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       (i, K, b)\<in>#mset (W L) \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> is_binary N (i, K, b)\<close> and
    H2: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# init_clss_lf N + NE) \<Longrightarrow>
       {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
       {#C \<in># dom_m (get_clauses_l (M', N, D, NE, UE, {#}, {#})).
        L \<in> set (watched_l (get_clauses_l (M', N, D, NE, UE, {#}, {#}) \<propto> C))#}\<close>
    using assms
    unfolding correct_watching'.simps clause_to_update_def
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
  show ?thesis
    unfolding correct_watching'.simps clause_to_update_def
    apply (intro conjI impI ballI)
    subgoal for L iK
      using distinct_mset_dom[of N] H1[of L \<open>fst iK\<close> \<open>fst (snd iK)\<close> \<open>snd (snd iK)\<close>] C irred
      apply (auto simp: image_mset_remove1_mset_if clause_to_update_def image_filter_replicate_mset
      distinct_mset_remove1_All filter_mset_neq_cond is_binary.simps dest: all_lits_of_mm_diffD
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
qed

context
  fixes LS :: \<open>'v literal \<times> 'v twl_st_wl\<close> and LT :: \<open>'v literal \<times> 'v twl_st_l\<close> 
  assumes
   LS_LT:  \<open>(LS, LT) \<in> Id \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<close>
begin

context
  fixes x1 :: \<open>'v literal\<close> and
    x2 :: \<open>('v literal, 'v literal, nat) annotated_lit list \<times>
                                      (nat, 'v literal list \<times> bool) fmap \<times>
                                      'v literal multiset option \<times>
                                      'v literal multiset multiset \<times>
                                      'v literal multiset multiset \<times>
                                      nat multiset \<times>
                                      'v literal multiset\<close> and
    x1a :: \<open>('v literal, 'v literal, nat) annotated_lit list\<close> and
    x2a :: \<open>(nat, 'v literal list \<times> bool) fmap \<times>
                             'v literal multiset option \<times>
                             'v literal multiset multiset \<times>
                             'v literal multiset multiset \<times>
                             nat multiset \<times>
                             'v literal multiset\<close> and x1b :: \<open>(nat,
                       'v literal list \<times>
                       bool) fmap\<close> and x2b :: \<open>'v literal multiset option \<times>
       'v literal multiset multiset \<times>
       'v literal multiset multiset \<times>
       nat multiset \<times>
       'v literal multiset\<close> and x1c :: \<open>'v literal multiset option\<close> and x2c :: \<open>'v literal multiset multiset \<times>
'v literal multiset multiset \<times>
nat multiset \<times>
'v literal multiset\<close> and x1d :: \<open>'v literal multiset multiset\<close> and x2d :: \<open>'v literal multiset multiset \<times>
                                   nat multiset \<times>
                                   'v literal multiset\<close> and x1e :: \<open>'v literal multiset multiset\<close> and x2e :: \<open>nat multiset \<times>
                              'v literal multiset\<close> and x1f :: \<open>nat multiset\<close> and x2f :: \<open>'v literal multiset\<close> and x1g :: \<open>'v literal\<close> and x2g :: \<open>('v literal,
                           'v literal, nat) annotated_lit list \<times>
                          (nat, 'v literal list \<times> bool) fmap \<times>
                          'v literal multiset option \<times>
                          'v literal multiset multiset \<times>
                          'v literal multiset multiset \<times>
                          'v literal multiset \<times>
                          ('v literal
                           \<Rightarrow> (nat \<times> 'v literal \<times> bool) list)\<close> and x1h :: \<open>('v literal,
                      'v literal,
                      nat) annotated_lit list\<close> and x2h :: \<open>(nat,
                    'v literal list \<times> bool) fmap \<times>
                   'v literal multiset option \<times>
                   'v literal multiset multiset \<times>
                   'v literal multiset multiset \<times>
                   'v literal multiset \<times>
                   ('v literal
                    \<Rightarrow> (nat \<times> 'v literal \<times> bool) list)\<close> and x1i :: \<open>(nat,
               'v literal list \<times>
               bool) fmap\<close> and x2i :: \<open>'v literal multiset option \<times>
                                       'v literal multiset multiset \<times>
                                       'v literal multiset multiset \<times>
                                       'v literal multiset \<times>
                                       ('v literal
\<Rightarrow> (nat \<times>
   'v literal \<times> bool) list)\<close> and x1j :: \<open>'v literal multiset option\<close> and x2j :: \<open>'v literal multiset multiset \<times>
                                  'v literal multiset multiset \<times>
                                  'v literal multiset \<times>
                                  ('v literal
                                   \<Rightarrow> (nat \<times> 'v literal \<times> bool) list)\<close> and x1k :: \<open>'v literal multiset multiset\<close> and
    x2k :: \<open>'v literal multiset multiset \<times>
                               'v literal multiset \<times>
                               ('v literal \<Rightarrow> (nat \<times> 'v literal \<times> bool) list)\<close> and
    x1l :: \<open>'v literal multiset multiset\<close> and x2l :: \<open>'v literal multiset \<times>
                            ('v literal \<Rightarrow> (nat \<times> 'v literal \<times> bool) list)\<close> and x1m :: \<open>'v literal multiset\<close> and
    x2m :: \<open>'v literal \<Rightarrow> (nat \<times> 'v literal \<times> bool) list\<close>
  assumes 
    st:
      \<open>x2e = (x1f, x2f)\<close>
      \<open>x2d = (x1e, x2e)\<close>
      \<open>x2c = (x1d, x2d)\<close>
      \<open>x2b = (x1c, x2c)\<close>
      \<open>x2a = (x1b, x2b)\<close>
      \<open>x2 = (x1a, x2a)\<close>
      \<open>LT = (x1, x2)\<close>
      \<open>x2l = (x1m, x2m)\<close>
      \<open>x2k = (x1l, x2l)\<close>
      \<open>x2j = (x1k, x2k)\<close>
      \<open>x2i = (x1j, x2j)\<close>
      \<open>x2h = (x1i, x2i)\<close>
      \<open>x2g = (x1h, x2h)\<close>
      \<open>LS = (x1g, x2g)\<close> and
    inv_pre: \<open>remove_all_annot_true_clause_imp_pre x1 (x1a, x1b, x1c, x1d, x1e, x1f, x2f)\<close>
begin

private lemma
  st':
    \<open>x2e = (x1f, x2f)\<close>
    \<open>x2d = (x1e, x1f, x2f)\<close>
    \<open>x2c = (x1d, x1e, x1f, x2f)\<close>
    \<open>x2b = (x1c, x1d, x1e, x1f, x2f)\<close>
    \<open>x2a = (x1b, x1c, x1d, x1e, x1f, x2f)\<close>
    \<open>x2 = (x1a, x1b, x1c, x1d, x1e, x1f, x2f)\<close>
    \<open>LT = (x1, x1a, x1b, x1c, x1d, x1e, x1f, x2f)\<close>
    \<open>x2l = (x1m, x2m)\<close>
    \<open>x2k = (x1l, x1m, x2m)\<close>
    \<open>x2j = (x1k, x1l, x1m, x2m)\<close>
    \<open>x2i = (x1j, x1k, x1l, x1m, x2m)\<close>
    \<open>x2h = (x1i, x1j, x1k, x1l, x1m, x2m)\<close>
    \<open>x2g = (x1h, x1i, x1j, x1k, x1l, x1m, x2m)\<close>
    \<open>LS = (x1, x1h, x1i, x1j, x1k, x1l, x1m, x2m)\<close>
    \<open>x1g = x1\<close>
    \<open>x1i = x1b\<close>
    \<open>x1d = x1k\<close>
     and
  rel:
    \<open>((x1h, x1i, x1j, x1k, x1l, x1m, x2m), x1a, x1b, x1c, x1d, x1e, x1f, x2f)
     \<in> state_wl_l None\<close> and
  corr:
    \<open>correct_watching' (x1h, x1i, x1j, x1k, x1l, x1m, x2m)\<close>
    using LS_LT st by (auto simp: state_wl_l_def)


private lemma x1k_in_all: \<open>x1 \<in># all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l x1i#} + x1k)\<close>
proof -
  let ?S = \<open>(x1a, x1b, x1c, x1d, x1e, x1f, x2f)\<close>
  obtain x' where
    \<open>twl_list_invs ?S\<close> and
    \<open>twl_list_invs ?S\<close> and
    \<open>get_conflict_l ?S = None\<close> and
    Sx: \<open>(?S, x') \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs x'\<close> and
    \<open>clauses_to_update_l ?S = {#}\<close> and
    L': \<open>x1 \<in> lits_of_l (get_trail_l ?S)\<close>
    using inv_pre unfolding remove_all_annot_true_clause_imp_pre_def by blast
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x')\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>\<And>L. L \<in> atm_of ` lits_of_l (get_trail_l ?S) \<Longrightarrow> L \<in> atms_of_ms
      ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m (get_clauses_l ?S) \<and> snd a}) \<union>
      atms_of_mm (get_unit_init_clauses_l ?S)\<close> and
    alien_learned: \<open>atms_of_mm (learned_clss (state\<^sub>W_of x'))
      \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of x'))\<close>
    using Sx unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp add: twl_st twl_st_l)
  from this(1)[of \<open>atm_of x1\<close>] have \<open>x1 \<in># all_lits_of_mm (mset `# ran_mf x1b + (x1d + x1e))\<close>
    using L' by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
      dest!: multi_member_split)

  then show ?thesis
    using alien_learned Sx unfolding all_clss_lf_ran_m[symmetric] image_mset_union
    by (auto simp: cdcl\<^sub>W_restart_mset_state in_all_lits_of_mm_ain_atms_of_iff st st' twl_st_l_def
      twl_st mset_take_mset_drop_mset')
qed

lemma literal_in_watch_list:
  shows \<open>RETURN (x2m x1g)
         \<le> \<Down>  {(xs, xs'). map fst xs = xs'}
            (SPEC (\<lambda>xs. \<forall>x\<in>set xs. x \<in># dom_m x1b \<longrightarrow> x1 \<in> set (x1b \<propto> x)))\<close>
proof -
  let ?S = \<open>(x1a, x1b, x1c, x1d, x1e, x1f, x2f)\<close>
  have \<open>{#i \<in># fst `# mset (x2m x1). i \<in># dom_m x1b#} =
      {#C \<in># dom_m x1b. x1 \<in> set (watched_l (x1b \<propto> C))#}\<close>
    using corr x1k_in_all by (auto simp: st st' correct_watching'.simps clause_to_update_def
      intro!: RETURN_SPEC_refine dest: multi_member_split)
  moreover have \<open>a \<in># (filter_mset (\<lambda>i. (i \<in># (dom_m x1b))) (fst `# (mset (x2m x1))))\<close>
    if \<open>(a, b) \<in> set (x2m x1)\<close> \<open>a \<in># dom_m x1b\<close> for a b
    using that by auto
  ultimately have \<open>x1 \<in> set (x1b \<propto> a)\<close>
    if \<open>(a, b) \<in> set (x2m x1)\<close> \<open>a \<in># dom_m x1b\<close> for a b
    using that by (cases b) (auto dest!: in_set_takeD)
  then show ?thesis
    using corr by (auto simp: st st' correct_watching'.simps
      intro!: RETURN_SPEC_refine)
qed


context
  notes _[simp] = st st'
  fixes xs :: \<open>nat list\<close>
  assumes xs: \<open>(x2m x1g, xs)
           \<in>  {(xs, xs'). map fst xs = xs'}\<close>
begin

lemma remove_all_initialisation:
  assumes \<open>case (0, x1b, x1d) of
           (i, N, NE) \<Rightarrow>
             remove_all_annot_true_clause_imp_inv
              (x1a, x1b, x1c, x1d, x1e, x1f, x2f) xs
              (i, x1a, N, x1c, NE, x1e, x1f, x2f)\<close>
  shows \<open>((0, x1i, x1k), 0, x1b, x1d)
         \<in> {((i, N, NE), i', N', NE').
            i = i' \<and>
            N = N' \<and>
            NE = NE' \<and>
            correct_watching'
             (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
              get_unit_learned_clss_wl (snd LS), literals_to_update_wl (snd LS),
              get_watched_wl (snd LS))}\<close>
  using corr by (auto simp: st st' state_wl_l_def)


context
  fixes x :: \<open>nat \<times>
              (nat, 'v literal list \<times> bool) fmap \<times>
              'v literal multiset multiset\<close> and x' :: \<open>nat \<times>
               (nat, 'v literal list \<times> bool) fmap \<times>
               'v literal multiset multiset\<close>
  assumes xx': \<open>(x, x')
           \<in> {((i, N, NE), i', N', NE').
              i = i' \<and>
              N = N' \<and>
              NE = NE' \<and>
              correct_watching'
               (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
                get_unit_learned_clss_wl (snd LS),
                literals_to_update_wl (snd LS), get_watched_wl (snd LS))}\<close>
begin

context
  assumes x': \<open>case x' of
           (i, N, NE) \<Rightarrow>
             remove_all_annot_true_clause_imp_inv
              (x1a, x1b, x1c, x1d, x1e, x1f, x2f) xs
              (i, x1a, N, x1c, NE, x1e, x1f, x2f)\<close>
begin

lemma remove_all_annot_true_clause_imp_inv_same_lengthI:
  \<open>remove_all_annot_true_clause_imp_inv S xs T \<Longrightarrow> length xs = length xs' \<Longrightarrow>
  remove_all_annot_true_clause_imp_inv S xs' T\<close>
  unfolding remove_all_annot_true_clause_imp_inv_def
  by auto

lemma remove_all_annot_true_clause_imp_wl_inv_in_loop:
  fixes x1n :: \<open>nat\<close> and x2n :: \<open>(nat, 'v literal list \<times> bool) fmap \<times>
                                 'v literal multiset multiset\<close> and x1o :: \<open>(nat,
                                    'v literal list \<times>
                                    bool) fmap\<close> and x2o :: \<open>'v literal multiset multiset\<close>
  assumes 
    \<open>x2n = (x1o, x2o)\<close> and
    \<open>x = (x1n, x2n)\<close>
  shows \<open>remove_all_annot_true_clause_imp_wl_inv
          (x1h, x1i, x1j, x1k, x1l, x1m, x2m) (x2m x1g)
          (x1n, x1h, x1o, x1j, x2o, x1l, x1m, x2m)\<close>
proof -
  show ?thesis
    using assms xx' x' corr 
    unfolding remove_all_annot_true_clause_imp_wl_inv_def prod.case apply -
    apply (intro conjI)
    subgoal by auto
    subgoal by auto
    subgoal
      apply (rule exI[of _ \<open>(x1h, x1b, x1j, x1d, x1l, {#}, x1m)\<close>])
      using rel xs
      by (auto simp: state_wl_l_def intro: remove_all_annot_true_clause_imp_inv_same_lengthI)
    done
qed
end


context
  assumes 
    \<open>case x of
     (i, N, NE) \<Rightarrow>
       remove_all_annot_true_clause_imp_wl_inv
        (x1h, x1i, x1j, x1k, x1l, x1m, x2m) (x2m x1g)
        (i, x1h, N, x1j, NE, x1l, x1m, x2m)\<close> and
    \<open>case x' of
     (i, N, NE) \<Rightarrow>
       remove_all_annot_true_clause_imp_inv (x1a, x1b, x1c, x1d, x1e, x1f, x2f)
        xs (i, x1a, N, x1c, NE, x1e, x1f, x2f)\<close>
begin
lemma
  fixes x1n :: \<open>nat\<close> and x2n :: \<open>(nat, 'v literal list \<times> bool) fmap \<times>
                                 'v literal multiset multiset\<close> and x1o :: \<open>(nat,
                                    'v literal list \<times>
                                    bool) fmap\<close> and x2o :: \<open>'v literal multiset multiset\<close> and x1p :: \<open>nat\<close> and x2p :: \<open>(nat,
'v literal list \<times> bool) fmap \<times>
                                       'v literal multiset multiset\<close> and x1q :: \<open>(nat,
  'v literal list \<times> bool) fmap\<close> and x2q :: \<open>'v literal multiset multiset\<close>
  assumes 
    \<open>x2n = (x1o, x2o)\<close> and
    \<open>x = (x1n, x2n)\<close> and
    \<open>x2p = (x1q, x2q)\<close> and
    \<open>x' = (x1p, x2p)\<close>
  shows \<open>(x1n < length (x2m x1g)) = (x1p < length xs)\<close>
proof -
  show ?thesis
    using assms xs xx' by auto
qed
end


context
  assumes 
    \<open>case x of (i, N, NE) \<Rightarrow> i < length (x2m x1g)\<close> and
    \<open>case x' of (i, N, NE) \<Rightarrow> i < length xs\<close> and
    x_inv: \<open>case x of
     (i, N, NE) \<Rightarrow>
       remove_all_annot_true_clause_imp_wl_inv
        (x1h, x1i, x1j, x1k, x1l, x1m, x2m) (x2m x1g)
        (i, x1h, N, x1j, NE, x1l, x1m, x2m)\<close> and
    x'_inv: \<open>case x' of
     (i, N, NE) \<Rightarrow>
       remove_all_annot_true_clause_imp_inv (x1a, x1b, x1c, x1d, x1e, x1f, x2f)
        xs (i, x1a, N, x1c, NE, x1e, x1f, x2f)\<close>
begin


context
  fixes x1n :: \<open>nat\<close> and x2n :: \<open>(nat, 'v literal list \<times> bool) fmap \<times>
                                 'v literal multiset multiset\<close> and x1o :: \<open>(nat,
                                    'v literal list \<times>
                                    bool) fmap\<close> and x2o :: \<open>'v literal multiset multiset\<close> and x1p :: \<open>nat\<close> and x2p :: \<open>(nat,
'v literal list \<times> bool) fmap \<times>
                                       'v literal multiset multiset\<close> and x1q :: \<open>(nat,
  'v literal list \<times> bool) fmap\<close> and x2q :: \<open>'v literal multiset multiset\<close>
  assumes 
    xx'_eq:
      \<open>x2n = (x1o, x2o)\<close>
      \<open>x' = (x1n, x2n)\<close>
      \<open>x2p = (x1q, x2q)\<close>
      \<open>x = (x1p, x2p)\<close> and
    x1n_le: \<open>x1n < length xs\<close>
begin


private lemma xx'_eq':
    \<open>x2n = (x1o, x2o)\<close>
    \<open>x' = (x1n, x1o, x2o)\<close>
    \<open>x2p = (x1o, x2o)\<close>
    \<open>x = (x1n, x1o, x2o)\<close>
    \<open>x1p = x1n\<close>
    \<open>x1q = x1o\<close>
    \<open>x2q = x2o\<close>
    \<open>xs = map fst (x2m x1)\<close>
  using xx' xx'_eq xs
  by auto

lemma x1p_le_length:
  shows \<open>x1p < length (x2m x1g)\<close>
proof -
  show ?thesis using x1n_le by (auto simp: xx'_eq')
qed

private lemma corr_w': \<open>correct_watching' (x1h, x1o, x1j, x2o, x1l, x1m, x2m)\<close>
  using x_inv
  unfolding remove_all_annot_true_clause_imp_wl_inv_def xx'_eq'
  by auto

context
  notes _[simp] = xx'_eq'
  fixes x1r :: \<open>nat\<close> and x2r :: \<open>'v literal\<close> and x2r' and x2s' :: bool
  assumes x2m: \<open>x2m x1g ! x1p = (x1r, x2r')\<close> \<open>x2r' = (x2r, x2s')\<close>
begin

lemma
  shows \<open>(x1r \<in># dom_m x1q) = (xs ! x1n \<in># dom_m x1o)\<close>
proof -
  show ?thesis
    using x2m x1n_le by auto
qed

private lemma x2m': \<open>x2m x1 ! x1n = (x1r, x2r, x2s')\<close>
  using x2m
  by auto

context
  notes _[simp] = x2m'
  assumes 
    x1r_dom: \<open>x1r \<in># dom_m x1q\<close> and
    xs_x1n_dom: \<open>xs ! x1n \<in># dom_m x1o\<close>
begin

private lemma x1r_xo: \<open>x1r \<in># dom_m x1o\<close>
  using xs_x1n_dom x1r_dom
  by auto


lemma remove_all_annot_true_clause_one_imp_le:
  shows \<open>remove_all_annot_true_clause_one_imp (x1r, x1q, x2q)
         \<le> \<Down> {((N, NE), (N', NE')). N = N' \<and> NE = NE' \<and>
            correct_watching' (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
               get_unit_learned_clss_wl (snd LS), literals_to_update_wl(snd LS), get_watched_wl (snd LS))}
            (remove_all_annot_true_clause_one_imp (xs ! x1n, x1o, x2o))\<close>
proof -
  show ?thesis
    using x1n_le corr_w' x1r_xo
    by (auto simp: remove_all_annot_true_clause_one_imp_def map_nth
      intro: correct_watching_fmdrop intro: correct_watching_fmdrop')
qed


context
  fixes xa :: \<open>(nat, 'v literal list \<times> bool) fmap \<times>
               'v literal multiset multiset\<close> and x'a :: \<open>(nat,
                  'v literal list \<times> bool) fmap \<times>
                 'v literal multiset multiset\<close> and x1s :: \<open>(nat,
                    'v literal list \<times>
                    bool) fmap\<close> and x2s :: \<open>'v literal multiset multiset\<close> and x1t :: \<open>(nat,
       'v literal list \<times> bool) fmap\<close> and x2t :: \<open>'v literal multiset multiset\<close>
  assumes 
    xa_x'a: \<open>(xa, x'a)
     \<in> {((N, NE), (N', NE')). N = N' \<and> NE = NE' \<and>
            correct_watching' (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
               get_unit_learned_clss_wl (snd LS), literals_to_update_wl(snd LS), get_watched_wl (snd LS))}\<close> and
    x'a: \<open>x'a = (x1s, x2s)\<close> and
    xa: \<open>xa = (x1t, x2t)\<close> and
    rem_inv: \<open>remove_all_annot_true_clause_imp_inv (x1a, x1b, x1c, x1d, x1e, x1f, x2f) xs
      (x1n, (x1a, x1s, x1c, x2s, x1e, x1f, x2f))\<close>
begin

private lemma xa:
    \<open>x'a = (x1s, x2s)\<close>
    \<open>xa = (x1s, x2s)\<close>
    \<open>x1t = x1s\<close>
    \<open>x2t = x2s\<close>
  using x'a xa xa_x'a by auto

private lemma add_eq: \<open>x1c = x1j\<close> \<open>x1a = x1h\<close> \<open>x1l = x1e\<close>
  using rel
  apply (auto simp: state_wl_l_def)
  done
(* lemma
  shows \<open>remove_all_annot_true_clause_imp_wl_inv
          (x1h, x1i, x1j, x1k, x1l, x1m, x2m) (x2m x1g)
          (x1p, x1h, x1t, x1j, x2t, x1l, x1m, x2m)\<close>
proof -

  obtain a aa ab ac ad ae b af ag ah ai aj ak ba where
    S: \<open>((x1h, x1b, x1j, x1k, x1l, x1m, x2m), a, aa, ab, ac, ad, ae, b)
     \<in> state_wl_l None\<close> and
    T: \<open>((x1h, x1o, x1j, x2o, x1l, x1m, x2m), af, ag, ah, ai, aj, ak, ba)
     \<in> state_wl_l None\<close> and
    rem: \<open>remove_all_annot_true_clause_imp_inv (a, aa, ab, ac, ad, ae, b) (x2m x1)
      (x1n, af, ag, ah, ai, aj, ak, ba)\<close>
    using x_inv unfolding remove_all_annot_true_clause_imp_wl_inv_def
    by auto
  have g
    using rem rem_inv S T apply (auto simp: xa add_eq state_wl_l_def)
    sorry
    (* 
    \<open>((x1h, x1b, x1j, x1k, x1l, x1m, x2m), a, aa, ab, ac, ad, ae, b)
     \<in> state_wl_l None\<close> and
    \<open>((x1h, x1o, x1j, x2o, x1l, x1m, x2m), af, ag, ah, ai, aj, ak, ba)
     \<in> state_wl_l None\<close> and
    \<open>remove_all_annot_true_clause_imp_inv (a, aa, ab, ac, ad, ae, b) (x2m x1)
      (x1n, af, ag, ah, ai, aj, ak, ba)\<close>
       *)
  let ?S = \<open>(a, aa, ab, ac, ad, ae, b)\<close>
  let ?T = \<open>(af, ag, ah, ai, aj, ak, ba)\<close>
  let ?U = \<open> (af, x1s, ah, x2s, aj, ak, ba)\<close>
  have S': \<open>((x1h, x1b, x1j, x1k, x1l, x1m, x2m), ?S)
    \<in> state_wl_l None\<close>
    using S by auto
  have T': \<open>((x1h, x1s, x1j, x2s, x1l, x1m, x2m), ?U)
    \<in> state_wl_l None\<close>
    using T xa_x'a S
    by (auto simp: state_wl_l_def)
  have \<open>remove_all_annot_true_clause_imp_inv ?T (x2m x1) (x1n, ?U)\<close>
    unfolding remove_all_annot_true_clause_imp_inv_def
    sorry
  have \<open>remove_all_annot_true_clause_imp_inv ?S (x2m x1) (x1n, ?U)\<close>
    using rem rem_inv S' T T'
    apply (auto simp: state_wl_l_def xa)
    sorry
  show ?thesis
    apply (auto simp: xa)
    unfolding remove_all_annot_true_clause_imp_wl_inv_def prod.case
    apply (intro conjI)
    subgoal
      using corr by auto
    subgoal
      using xa_x'a by (auto simp: xa)
    subgoal
      apply (rule exI[of _ \<open>?S\<close>])
      apply (rule exI[of _ \<open>?T\<close>])
      using S' T' apply auto

    sorry
    find_theorems x1h
qed *)

lemma
  shows \<open>((x1p + 1, x1t, x2t), x1n + 1, x1s, x2s)
         \<in> {((i, N, NE), i', N', NE').
            i = i' \<and>
            N = N' \<and>
            NE = NE' \<and>
            correct_watching'
             (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
              get_unit_learned_clss_wl (snd LS), literals_to_update_wl (snd LS),
              get_watched_wl (snd LS))}\<close>
proof -
  show ?thesis
    using xa_x'a
    by (auto simp: xa)
qed
end
end


lemma
  assumes 
    \<open>x1r \<notin># dom_m x1q\<close> and
    \<open>xs ! x1n \<notin># dom_m x1o\<close>
  shows \<open>((x1p + 1, x1q, x2q), x1n + 1, x1o, x2o)
         \<in> {((i, N, NE), i', N', NE').
            i = i' \<and>
            N = N' \<and>
            NE = NE' \<and>
            correct_watching'
             (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
              get_unit_learned_clss_wl (snd LS), literals_to_update_wl (snd LS),
              get_watched_wl (snd LS))}\<close>
proof -
  show ?thesis
    using corr_w'
    by auto
qed

end
end
end


lemma
  fixes x1n :: \<open>nat\<close> and x2n :: \<open>(nat, 'v literal list \<times> bool) fmap \<times>
                                 'v literal multiset multiset\<close> and x1o :: \<open>(nat,
                                    'v literal list \<times>
                                    bool) fmap\<close> and x2o :: \<open>'v literal multiset multiset\<close> and x1p :: \<open>nat\<close> and x2p :: \<open>(nat,
'v literal list \<times> bool) fmap \<times>
                                       'v literal multiset multiset\<close> and x1q :: \<open>(nat,
  'v literal list \<times> bool) fmap\<close> and x2q :: \<open>'v literal multiset multiset\<close>
  assumes 
    \<open>x2n = (x1o, x2o)\<close> and
    \<open>x' = (x1n, x2n)\<close> and
    \<open>x2p = (x1q, x2q)\<close> and
    \<open>x = (x1p, x2p)\<close>
  shows \<open>((x1h, x1q, x1j, x2q, x1l, x1m, x2m), x1a, x1o, x1c, x2o, x1e, x1f,
          x2f)
         \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<close>
proof -
  show ?thesis
    using assms xx' rel by (auto simp: state_wl_l_def)
qed

end

end

end

end


lemma remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp:
  \<open>(uncurry remove_all_annot_true_clause_imp_wl, uncurry remove_all_annot_true_clause_imp) \<in>
   Id \<times>\<^sub>f {(S::'v twl_st_wl, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<rangle>nres_rel\<close>
proof -
  have H: \<open>((0, x1i, x1k), 0, x1b, x1d) \<in> nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    if \<open>(x1i, x1b) \<in> Id\<close> and  \<open>(x1k, x1d) \<in> Id\<close>
    for x1i x1k x1b x1d
    using that by auto
  have L'_in_clause: \<open>L' \<in> set (N0 \<propto> C)\<close>
    if
      pre: \<open>remove_all_annot_true_clause_imp_pre L' (M, N0, D, NE, UE, {#}, Q)\<close> and
      x_W: \<open>x \<in> set (W L')\<close> and
      part: \<open>correct_watching (M, N0, D, NE, UE, Q, W)\<close> and
      x: \<open>x = (C, i)\<close> and 
      dom:  \<open>C \<in># dom_m N0\<close>
    for L' :: \<open>'v literal\<close> and M :: \<open>('v, nat) ann_lits\<close> and N0 D NE UE Q W x and C i
  proof -
    define S :: \<open>'v twl_st_l\<close> where \<open>S \<equiv> (M, N0, D, NE, UE, {#}, Q)\<close>
    obtain x' where
      \<open>twl_list_invs S\<close> and
      \<open>twl_list_invs S\<close> and
      \<open>get_conflict_l S = None\<close> and
      Sx: \<open>(S, x') \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs x'\<close> and
      \<open>clauses_to_update_l S = {#}\<close> and
      L': \<open>L' \<in> lits_of_l (get_trail_l S)\<close>
      using pre unfolding remove_all_annot_true_clause_imp_pre_def S_def[symmetric] by blast
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x')\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then have \<open>\<And>L. L \<in> atm_of ` lits_of_l (get_trail_l S) \<Longrightarrow> L \<in> atms_of_ms
       ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m (get_clauses_l S) \<and> snd a}) \<union>
      atms_of_mm (get_unit_init_clauses_l S)\<close>
      using Sx unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp add: twl_st twl_st_l)
    from this[of \<open>atm_of L'\<close>] have \<open>L' \<in># all_lits_of_mm (mset `# ran_mf N0 + (NE + UE))\<close>
      using L' by (auto simp: S_def in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
        dest!: multi_member_split)
    moreover have \<open>C \<in># {#i \<in># fst `# mset (W L'). i \<in># dom_m N0#}\<close>
      using x_W dom unfolding x by auto
    ultimately show ?thesis
      using part dom x x_W unfolding correct_watching.simps
      by (auto dest!: multi_member_split[of L'] simp: clause_to_update_def
        dest: in_set_takeD)
  qed
  have \<open>remove_all_annot_true_clause_one_imp (C, N0, NE0) \<le>
        \<Down> {((N, NE), (N', NE')). N = N' \<and> NE = NE' \<and>
            (C \<in># dom_m N0 \<longrightarrow> N = fmdrop C N0 \<and> (irred N0 C' \<longrightarrow> NE' = add_mset (mset (N0\<propto>C)) NE0)
              \<and> (\<not>irred N0 C' \<longrightarrow> NE' = NE0)) \<and>
            (C \<notin># dom_m N0 \<longrightarrow> N = N0 \<and>  NE' = NE0)}
          (remove_all_annot_true_clause_one_imp (C', N', NE'))\<close>
      (is \<open>_ \<le> \<Down> ?remove_all_one _\<close>)
    if \<open>(C, C') \<in> Id\<close> and \<open>(N0, N') \<in> Id\<close> and \<open>(NE0, NE') \<in> Id\<close>
    for C C' N' NE0 NE' N0
    using that distinct_mset_dom[of N0]
    unfolding remove_all_annot_true_clause_one_imp_def by (auto simp: distinct_mset_remove1_All)

  show ?thesis
    supply [[goals_limit=1]]
    apply (intro frefI nres_relI)
    unfolding uncurry_def remove_all_annot_true_clause_imp_wl_def
      remove_all_annot_true_clause_imp_def
    subgoal for LS LT
      apply (refine_rcg H literal_in_watch_list remove_all_annot_true_clause_one_imp_le
        WHILEIT_refine[where R=\<open>{((i, N, NE), (i', N', NE')). i = i' \<and> N = N' \<and> NE = NE' \<and>
            correct_watching' (get_trail_wl (snd LS), N, get_conflict_wl (snd LS), NE,
               get_unit_learned_clss_wl (snd LS), literals_to_update_wl(snd LS), get_watched_wl (snd LS))}\<close>])
      apply assumption+
      subgoal by (rule remove_all_initialisation)
      subgoal by (rule remove_all_annot_true_clause_imp_wl_inv_in_loop)
      subgoal by (auto simp: state_wl_l_def remove_all_annot_true_clause_imp_wl_inv_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      apply assumption+
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      done
    done
qed

definition remove_one_annot_true_clause_one_imp_wl_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_pre i T \<longleftrightarrow>
     (\<exists>T'. (T, T') \<in> state_wl_l None \<and>
       remove_one_annot_true_clause_one_imp_pre i T' \<and>
       correct_watching' T)\<close>

definition remove_one_annot_true_clause_one_imp_wl
  :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i (M, N, D, NE, UE, Q, W). do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_pre i (M, N, D, NE, UE, Q, W));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev M)!i = Propagated L C);
      if C = 0 then RETURN (i+1, M, N, D, NE, UE, Q, W)
      else do {
        ASSERT(C \<in># dom_m N);
        M \<leftarrow> replace_annot_in_trail_spec M L;
        (N', C, b) \<leftarrow> extract_and_remove N C;
        let S = (if b then (M, N', D, add_mset (mset C) NE, UE, Q, W)
                      else (M, N', D, NE, add_mset (mset C) UE, Q, W));
        S \<leftarrow> remove_all_annot_true_clause_imp_wl L S;
        RETURN (i+1, S)
      }
  })\<close>

lemma remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp:
    \<open>(uncurry remove_one_annot_true_clause_one_imp_wl, uncurry remove_one_annot_true_clause_one_imp)
    \<in> nat_rel \<times>\<^sub>f  {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S} \<rightarrow>\<^sub>f
      \<langle>nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>replace_annot_in_trail_spec L S \<le> \<Down> Id (replace_annot_in_trail_spec L' T')\<close>
    if \<open>(L, L') \<in> Id\<close> and \<open>(S, T') \<in> Id\<close> for L L' S T'
    using that by auto
  have [refine0]: \<open>extract_and_remove N j \<le>
         \<Down> {((N', C' :: 'a clause_l, b'), (N'', C'', b'')). N' = N'' \<and> C' = C'' \<and> b' = b'' \<and>
               N' = fmdrop j N \<and> C' = N\<propto>j \<and> b' = irred N j} (extract_and_remove N' j')\<close>
    if \<open>(j, j') \<in> Id\<close> and \<open>(N, N') \<in> Id\<close> for j j' N N'
    using that unfolding extract_and_remove_def
    by refine_rcg (auto intro!: RES_refine)

  show ?thesis
    unfolding remove_one_annot_true_clause_one_imp_wl_def remove_one_annot_true_clause_one_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp[THEN fref_to_Down_curry])
    subgoal unfolding remove_one_annot_true_clause_one_imp_wl_pre_def by force
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by simp
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by simp
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by (auto simp add: state_wl_l_def intro: correct_watching_fmdrop
      correct_watching_fmdrop' correct_watching_fmdrop'')
    subgoal by (auto simp add: state_wl_l_def intro: correct_watching_fmdrop
      correct_watching_fmdrop')
    done
qed

definition remove_one_annot_true_clause_imp_wl_inv where
  \<open>remove_one_annot_true_clause_imp_wl_inv S = (\<lambda>(i, T).
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
       correct_watching' S \<and> correct_watching' T \<and>
       remove_one_annot_true_clause_imp_inv S' (i, T')))\<close>

definition remove_one_annot_true_clause_imp_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl = (\<lambda>S. do {
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_inv S\<^esup>
      (\<lambda>(i, S). i < length (get_trail_wl S) \<and> \<not>is_decided (get_trail_wl S!i))
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl i S)
      (0, S);
    RETURN S
  })\<close>

lemma remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp:
  \<open>(remove_one_annot_true_clause_imp_wl, remove_one_annot_true_clause_imp)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding remove_one_annot_true_clause_imp_wl_def remove_one_annot_true_clause_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>f {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal by auto
    subgoal for x y xa x'
      unfolding remove_one_annot_true_clause_imp_wl_inv_def
      apply (subst case_prod_beta)
      apply (rule_tac x=\<open>y\<close> in exI)
      apply (rule_tac x=\<open>snd x'\<close> in exI)
      apply (subst (asm)(8) surjective_pairing)
      apply (subst (asm)(13) surjective_pairing)
      unfolding prod_rel_iff by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition collect_valid_indices_wl where
  \<open>collect_valid_indices_wl S = SPEC (\<lambda>N. distinct N)\<close>

definition mark_to_delete_clauses_wl_inv
  :: \<open>'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> bool \<times> nat \<times> 'v clauses_l \<times> nat list \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_wl_inv = (\<lambda>S xs0 (brk, i, N, xs).
     \<exists>T. (S, T) \<in> state_wl_l None \<and> mark_to_delete_clauses_l_inv T xs0 (brk, i, N, xs) \<and>
      correct_watching' S)\<close>

definition mark_to_delete_clauses_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_wl_pre S \<longleftrightarrow>
   (\<exists>T. (S, T) \<in> state_wl_l None \<and> mark_to_delete_clauses_l_pre T)\<close>

definition mark_to_delete_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl  = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    ASSERT(mark_to_delete_clauses_wl_pre (M, N, D, NE, UE, Q, W));
    xs0 \<leftarrow> collect_valid_indices_wl (M, N, D, NE, UE, Q, W);
    (_, _, N, xs) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_inv (M, N, D, NE, UE, Q, W) xs0\<^esup>
      (\<lambda>(brk, i, N, xs). \<not>brk \<and> i < length xs)
      (\<lambda>(brk, i, N, xs). do {
        if(xs!i \<notin># dom_m N) then RETURN (brk, i, N, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (N\<propto>(xs!i)));
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


lemma mark_to_delete_clauses_wl_mark_to_delete_clauses_l:
  \<open>(mark_to_delete_clauses_wl, mark_to_delete_clauses_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<rangle>nres_rel\<close>
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
    subgoal for x y
    apply (cases x; cases y)
    subgoal for M N D NE UE Q W M' N' D' NE' UE' WS' Q'
    apply (refine_vcg
      WHILEIT_refine_with_post[where
         R = \<open>{((brk' :: bool, i' :: nat, N', xs), (brk'', i'', N'', xs')).
             brk' = brk'' \<and> i' = i'' \<and> N' = N'' \<and> xs = xs' \<and>
             ((M, N', D, NE, UE, Q, W), (M, N'', D, NE, UE, WS', Q')) \<in> state_wl_l None \<and>
             correct_watching' (M, N', D, NE, UE, Q, W)}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal unfolding mark_to_delete_clauses_wl_pre_def by blast
    subgoal by auto
    subgoal by (auto simp: state_wl_l_def)
    subgoal unfolding mark_to_delete_clauses_wl_inv_def by fast
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def correct_watching_fmdrop)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    done
  done
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
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
       mark_to_delete_clauses_l_post S' T' \<and> correct_watching S  \<and>
       correct_watching T)\<close>

definition cdcl_twl_full_restart_wl_prog :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_twl_full_restart_wl_prog S = do {
    S \<leftarrow> remove_one_annot_true_clause_imp_wl S;
    ASSERT(mark_to_delete_clauses_wl_pre S);
    T \<leftarrow> mark_to_delete_clauses_wl S;
    ASSERT(mark_to_delete_clauses_wl_post S T);
    RETURN T
  }\<close>

lemma cdcl_twl_full_restart_wl_prog_alt_def:
  \<open>cdcl_twl_full_restart_wl_prog S = do {
    S \<leftarrow> remove_one_annot_true_clause_imp_wl S;
    ASSERT(mark_to_delete_clauses_wl_pre S);
    T \<leftarrow> mark_to_delete_clauses_wl S;
    ASSERT(mark_to_delete_clauses_wl_post S T);
    RETURN T
  }\<close>
  unfolding cdcl_twl_full_restart_wl_prog_def by auto

lemma cdcl_twl_full_restart_l_prog_alt_def: \<open>cdcl_twl_full_restart_l_prog S = do {
    S \<leftarrow> remove_one_annot_true_clause_imp S;
    ASSERT(mark_to_delete_clauses_l_pre S);
    T \<leftarrow> mark_to_delete_clauses_l S;
    ASSERT (mark_to_delete_clauses_l_post S T);
    RETURN T
  }\<close>
  unfolding cdcl_twl_full_restart_l_prog_def
  by auto

lemma correct_watching_correct_watching: \<open>correct_watching S \<Longrightarrow> correct_watching' S\<close>
  apply (cases S, simp only: correct_watching.simps correct_watching'.simps)
  apply (subst (asm) all_clss_lf_ran_m[symmetric])
  unfolding image_mset_union all_lits_of_mm_union
  by auto

lemma (in -) [twl_st_l, simp]:
 \<open>(Sa, x) \<in> twl_st_l None \<Longrightarrow> get_all_learned_clss x =  mset `# (get_learned_clss_l Sa) + get_unit_learned_clauses_l Sa\<close>
  by (cases Sa; cases x) (auto simp: twl_st_l_def get_learned_clss_l_def mset_take_mset_drop_mset')

lemma cdcl_twl_full_restart_wl_prog_final_rel:
  assumes 
    \<open>(x, y) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S}\<close> and
    S_Sa: \<open>(S, Sa) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<close> and
    pre_Sa: \<open>mark_to_delete_clauses_l_pre Sa\<close> and
    pre_S: \<open>mark_to_delete_clauses_wl_pre S\<close> and
    T_Ta: \<open>(T, Ta) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching' S}\<close> and
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
  then have \<open>set_mset (all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T) + get_unit_init_clss_wl T)) =
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

  show ?thesis
    using S_Sa T_Ta corr_T' corr_S' pre_l
    unfolding mark_to_delete_clauses_wl_post_def
    by blast
qed


lemma cdcl_twl_full_restart_wl_prog_cdcl_full_twl_restart_l_prog:
  \<open>(cdcl_twl_full_restart_wl_prog, cdcl_twl_full_restart_l_prog)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_prog_alt_def cdcl_twl_full_restart_l_prog_def
    rewatch_clauses_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
     mark_to_delete_clauses_wl_mark_to_delete_clauses_l[THEN fref_to_Down]
     remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp[THEN fref_to_Down])
  subgoal unfolding mark_to_delete_clauses_wl_pre_def
    
   by (blast intro: correct_watching_correct_watching)
  subgoal unfolding mark_to_delete_clauses_wl_pre_def by (blast intro: correct_watching_correct_watching)
  subgoal for x y S Sa T Ta
    by (rule cdcl_twl_full_restart_wl_prog_final_rel)
  subgoal by (auto simp: state_wl_l_def mark_to_delete_clauses_wl_post_def)
  done

definition (in -) cdcl_twl_local_restart_wl_spec :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_local_restart_wl_spec = (\<lambda>(M, N, D, NE, UE, Q, W). do {
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#}) \<or> (M' = M \<and> Q' = Q));
      RETURN (M, N, D, NE, UE, Q, W)
   })\<close>

lemma cdcl_twl_local_restart_wl_spec_cdcl_twl_local_restart_l_spec:
  \<open>(cdcl_twl_local_restart_wl_spec, cdcl_twl_local_restart_l_spec)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
proof -
  have [refine0]:
    \<open>\<And>x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k.
        (x, y) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S} \<Longrightarrow>
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
    apply assumption+
    subgoal by (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def)
    done
qed

definition cdcl_twl_restart_wl_prog where
\<open>cdcl_twl_restart_wl_prog S = do {
   b \<leftarrow> SPEC(\<lambda>_. True);
   if b then cdcl_twl_local_restart_wl_spec S else cdcl_twl_full_restart_wl_prog S
  }\<close>

lemma cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(cdcl_twl_restart_wl_prog, cdcl_twl_restart_l_prog)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_prog_def cdcl_twl_restart_l_prog_def
    rewatch_clauses_def
  apply (intro frefI nres_relI)
  apply (refine_vcg cdcl_twl_local_restart_wl_spec_cdcl_twl_local_restart_l_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_full_twl_restart_l_prog[THEN fref_to_Down])
  subgoal by auto
  done

definition (in -) restart_abs_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_pre S brk \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_abs_l_pre S' brk
      \<and> correct_watching S)\<close>

(* 

definition empty_WL :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> ('v literal \<Rightarrow> 'v watched)\<close>  where
  \<open>empty_WL W = (\<lambda>_. [])\<close>

definition rewatch_clause
  :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> ('v literal \<Rightarrow> 'v watched) \<Rightarrow> ('v literal \<Rightarrow> 'v watched) nres\<close>
where
  \<open>rewatch_clause N C W = do {
    ASSERT(length (N \<propto> C) > 1);
    let L = N \<propto> C ! 0;
    let L' = N \<propto> C ! 1;
    RETURN (W(L := W L @ [(C, L')], L' := W L' @ [(C, L)]))
  }\<close>

fun correct_watching_on :: \<open>nat set \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>correct_watching_on xs (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + NE + UE).
       mset (W L) = clause_to_update L (M, fmrestrict_set xs N, D, NE, UE, {#}, {#}))\<close>

lemma fmrestrict_set_dom_m_full:
  assumes
    incl: \<open>set_mset (dom_m N) \<subseteq> xs\<close>
  shows \<open>fmrestrict_set xs N = N\<close>
  apply (rule fmlookup_inject[THEN iffD1], subst eq_commute)
  using assms by (auto intro!: ext dest!: dom_mI)

lemma correct_watching_on_correct_watching:
  assumes
    \<open>correct_watching_on xs (M, N, D, NE, UE, Q, W)\<close> and
    incl: \<open>set_mset (dom_m N) \<subseteq> xs\<close>
  shows \<open>correct_watching (M, N, D, NE, UE, Q, W)\<close>
proof -
  have \<open>xs \<inter> set_mset (dom_m N) = set_mset (dom_m N)\<close>
    using incl by (auto simp: dom_m_fmrestrict_set')
  then have 1: \<open>dom_m (fmrestrict_set xs N) = dom_m N\<close>
    using incl distinct_mset_dom[of N]
    by (auto simp: dom_m_fmrestrict_set' remdups_mset_def[symmetric] distinct_mset_remdups_mset_id)
  then show ?thesis
    using assms
    unfolding correct_watching_on.simps correct_watching.simps
      clause_to_update_def get_clauses_l.simps 1
    by (auto simp: fmrestrict_set_dom_m_full)
qed

definition rewatch_clauses_prog_inv where
  \<open>rewatch_clauses_prog_inv = (\<lambda>(M, N, D, NE, UE, Q, W) xs (i, W).
    i \<le> length xs \<and>
      correct_watching_on (set (take i xs)) (M, N, D, NE, UE, Q, W))\<close>

definition rewatch_clauses_prog_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>rewatch_clauses_prog_pre S \<longleftrightarrow>
     (\<exists>T U.
        (S, T) \<in> state_wl_l None \<and>
        (T, U) \<in> twl_st_l None \<and>
        twl_struct_invs U \<and>
        correct_watching S)\<close>

definition rewatch_clauses_prog :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>rewatch_clauses_prog = (\<lambda>(M, N, D, NE, UE, Q, W0). do {
  ASSERT(rewatch_clauses_prog_pre (M, N, D, NE, UE, Q, W0));
  let W0 = empty_WL W0;
  xs \<leftarrow> SPEC(\<lambda>xs. dom_m N \<subseteq># mset xs \<and> distinct xs);
  (_, W) \<leftarrow> WHILE\<^sub>T\<^bsup>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, W0) xs\<^esup>
    (\<lambda>(i, W). i < length xs)
    (\<lambda>(i, W). do {
      ASSERT(i < length xs);
      if xs!i \<in># dom_m N then do {
        W \<leftarrow> rewatch_clause N (xs!i) W;
        RETURN(i+1, W)
      } else RETURN(i+1, W)
    })
    (0, W0);
  RETURN (M, N, D, NE, UE, Q, W)
})\<close>

lemma rewatch_clauses_prog_rewatch_clauses:
  assumes
    ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    TU: \<open>(T, U) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs U\<close> and
    \<open>twl_list_invs T\<close>
    \<open>correct_watching S\<close>
  shows
    \<open>rewatch_clauses_prog S \<le> rewatch_clauses S\<close>
proof -
  have pre: \<open>rewatch_clauses_prog_pre S\<close>
    using assms unfolding rewatch_clauses_prog_pre_def by blast
  have size_ge2: \<open>1 < length (N \<propto> (xs ! a))\<close>
    if
      N: \<open>N = get_clauses_wl S\<close> and
      dom: \<open>xs ! a \<in># dom_m N\<close>
    for N xs a
  proof -
    have \<open>twl_st_inv U\<close>
      using struct_invs unfolding twl_struct_invs_def by fast+
    then have \<open>Multiset.Ball (get_clauses U) struct_wf_twl_cls\<close>
      unfolding twl_st_inv_alt_def by fast
    moreover have \<open>mset (N \<propto> (xs ! a)) \<in># clauses (get_clauses U)\<close>
      using ST TU N dom by (auto simp: mset_take_mset_drop_mset')
    ultimately show ?thesis
      apply (auto dest!: multi_member_split simp del: size_mset
        simp: size_mset[symmetric])
      apply (case_tac x)
      apply auto
      done
  qed
  have inv_Suc: \<open>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, \<lambda>_. []) xs
        (i + 1, W2
          (N \<propto> (xs ! i) ! 0 := W2 (N \<propto> (xs ! i) ! 0) @ [xs ! i],
          N \<propto> (xs ! i) ! 1 := W2 (N \<propto> (xs ! i) ! 1) @ [xs ! i]))\<close>
    if
      \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
      \<open>rewatch_clauses_prog_pre (M, N, D, NE, UE, Q, W)\<close> and
      \<open>xs \<in> {xs. dom_m N \<subseteq># mset xs \<and> distinct xs}\<close> and
      inv: \<open>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, \<lambda>_. []) xs s\<close> and
      cond: \<open>case s of (i, W) \<Rightarrow> i < length xs\<close> and
      s: \<open>s = (i, W2)\<close> and
      [simp]: \<open>i < length xs\<close> \<open>xs ! i \<in># dom_m N\<close> and
      le: \<open>1 < length (N \<propto> (xs ! i))\<close>
    for M N D NE UE Q W xs i W2 s
  proof -
    define N0 where \<open>N0 \<equiv> fmrestrict_set (set (take i xs)) N\<close>
    define C where \<open>C \<equiv> xs ! i\<close>
    define D' where \<open>D' \<equiv> the (fmlookup N C)\<close>
    define N' where \<open>N' \<equiv> fmdrop C N\<close>
    have D': \<open>D' = (N \<propto> C, irred N C)\<close>
      unfolding D'_def
      by auto
    have N': \<open>N = fmupd C D' N'\<close>
      unfolding N'_def C_def D'_def
      by (smt fmap_ext fmlookup_drop fmupd_lookup in_dom_m_lookup_iff option.collapse that(8))
    have [simp]: \<open>xs ! i \<notin> set (take i xs)\<close>
      by (metis (no_types, lifting) in_set_conv_iff less_not_refl3 mem_Collect_eq
         nth_eq_iff_index_eq that(3) that(7))
    have [simp]: \<open>xs ! i \<notin># dom_m N'\<close>
      using distinct_mset_dom[of N] unfolding N'_def by (auto simp: distinct_mset_remove1_All C_def)
    then have [simp]: \<open>fmlookup N' (xs ! i) = None\<close>
      by (simp_all add: C_def N'_def)
    have \<open>fmfilter (\<lambda>a. a = xs ! i \<or> a \<in> set (take i xs)) N' =
      fmfilter (\<lambda>a. a \<in> set (take i xs)) N'\<close>
      by (rule fmfilter_cong) auto
    then have N1: \<open>fmrestrict_set (set (take (i + 1) xs)) N = fmupd C (N \<propto> C, irred N C) N0\<close>
      by (auto simp: take_Suc_conv_app_nth N0_def C_def fmfilter_alt_defs N')
    have [simp]: \<open>C \<notin># dom_m N0\<close>
      unfolding N0_def
      by (auto simp: dom_m_fmrestrict_set C_def)
    have H: \<open>{#Ca \<in># dom_m N0. (C = Ca \<longrightarrow> P Ca) \<and> (C \<noteq> Ca \<longrightarrow> P' Ca)#} =
       {#Ca \<in># dom_m N0. P' Ca#}\<close> for P P'
      by (rule filter_mset_cong2) auto
    have [simp]: \<open>N \<propto> C ! Suc 0 \<in> set (watched_l (N \<propto> C))\<close>  \<open>N \<propto> C ! 0 \<in> set (watched_l (N \<propto> C))\<close>
      using le by (auto simp: in_set_take_conv_nth C_def intro: exI[of _ \<open>Suc 0\<close>] exI[of _ \<open>0\<close>])
    have [dest]: \<open>L \<noteq> N \<propto> C ! 0 \<Longrightarrow> L \<noteq> N \<propto> C ! Suc 0 \<Longrightarrow> L \<in> set (watched_l (N \<propto> C)) \<Longrightarrow> False\<close>
      for L
      using le by (auto simp: take_2_if hd_conv_nth split: if_splits)
    have \<open>correct_watching_on (set (take i xs)) (M, N, D, NE, UE, Q, W2)\<close>
      using inv
      unfolding s rewatch_clauses_prog_inv_def prod.case
      by fast
    then have \<open>correct_watching_on (set (take (i + 1) xs))
     (M, N, D, NE, UE, Q, W2
      (N \<propto> (xs ! i) ! 0 := W2 (N \<propto> (xs ! i) ! 0) @ [xs ! i],
       N \<propto> (xs ! i) ! 1 := W2 (N \<propto> (xs ! i) ! 1) @ [xs ! i]))\<close>
      using le
      unfolding N1 N0_def[symmetric] D'[symmetric] C_def[symmetric]
         correct_watching_on.simps clause_to_update_def get_clauses_l.simps
      by (auto simp: correct_watching.simps clause_to_update_def H
        correct_watching_on.simps N0_def[symmetric] D' C_def[symmetric])
    then show ?thesis
      using cond unfolding rewatch_clauses_prog_inv_def prod.case s
      by linarith
  qed
  have inv_Suc_notin: \<open>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, \<lambda>_. []) xs
        (i + 1, W2)\<close>
    if
      \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
      \<open>rewatch_clauses_prog_pre (M, N, D, NE, UE, Q, W)\<close> and
      \<open>xs \<in> {xs. dom_m N \<subseteq># mset xs \<and> distinct xs}\<close> and
      inv: \<open>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, \<lambda>_. []) xs s\<close> and
      cond: \<open>case s of (i, W) \<Rightarrow> i < length xs\<close> and
      s: \<open>s = (i, W2)\<close> and
      [simp]: \<open>i < length xs\<close> \<open>xs ! i \<notin># dom_m N\<close>
    for M N D NE UE Q W xs i W2 s
  proof -
    define N0 where \<open>N0 \<equiv> fmrestrict_set (set (take i xs)) N\<close>
    have \<open>fmfilter (\<lambda>a. a = xs ! i \<or> a \<in> set (take i xs)) N =
      fmfilter (\<lambda>a. a \<in> set (take i xs)) N\<close>
      by (rule fmfilter_cong) (auto dest: dom_mI)
    then have N1: \<open>fmrestrict_set (set (take (Suc i) xs)) N =  N0\<close>
      by (auto simp: take_Suc_conv_app_nth N0_def fmfilter_alt_defs N0_def)

    have \<open>correct_watching_on (set (take i xs)) (M, N, D, NE, UE, Q, W2)\<close>
      using inv
      unfolding s rewatch_clauses_prog_inv_def prod.case
      by fast
    then have \<open>correct_watching_on (set (take (i + 1) xs))
     (M, N, D, NE, UE, Q, W2)\<close>
      using N1
      unfolding N0_def[symmetric]
         correct_watching_on.simps clause_to_update_def get_clauses_l.simps
      by (auto simp: correct_watching.simps clause_to_update_def H
        correct_watching_on.simps N0_def[symmetric])
    then show ?thesis
      using cond unfolding rewatch_clauses_prog_inv_def prod.case s
      by linarith
  qed
  show ?thesis
    unfolding rewatch_clauses_prog_def rewatch_clauses_def Let_def empty_WL_def rewatch_clause_def
    apply (cases S)
    apply clarify
    apply (intro ASSERT_leI)
    subgoal using pre by fast
    subgoal for M N D NE UE Q W
      unfolding intro_spec_iff
      apply (intro ballI)
      subgoal for xs
        apply (refine_vcg
          WHILEIT_rule[where R= \<open>measure (\<lambda>(i::nat, W::_ literal \<Rightarrow> watched). length xs -i)\<close>])
        subgoal by auto
        subgoal by (auto simp: rewatch_clauses_prog_inv_def correct_watching_on.simps
              clause_to_update_def)
        subgoal by auto
        subgoal by (rule size_ge2) auto
        subgoal by (rule inv_Suc)
        subgoal by auto
        subgoal by (rule inv_Suc_notin)
        subgoal unfolding rewatch_clauses_prog_inv_def by auto
        subgoal by auto
        subgoal unfolding rewatch_clauses_prog_inv_def
          by (auto dest!: correct_watching_on_correct_watching)
        done
      done
    done
qed *)


context twl_restart_ops
begin

definition (in twl_restart_ops) restart_required_wl  :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
\<open>restart_required_wl S n = SPEC (\<lambda>b. b \<longrightarrow> f n < size (get_learned_clss_wl S))\<close>

definition (in twl_restart_ops) restart_prog_wl
  :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_wl \<times> nat) nres"
where
  \<open>restart_prog_wl S n brk = do {
     ASSERT(restart_abs_wl_pre S brk);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog S;
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>

lemma cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(uncurry2 restart_prog_wl, uncurry2 restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S} \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<times>\<^sub>f _ \<times>\<^sub>f _ \<rightarrow>\<^sub>f \<langle>?R'\<rangle>nres_rel\<close>)
proof -
  have [refine0]: \<open>restart_required_wl a b \<le> \<Down> Id (restart_required_l a' b')\<close>
    if \<open>(a, a') \<in> ?R\<close> and \<open>(b, b') \<in> nat_rel\<close> for a a' b b'
    using that unfolding restart_required_wl_def restart_required_l_def
    by (auto simp: twl_st_l)
  show ?thesis
    unfolding uncurry_def restart_prog_wl_def restart_prog_l_def rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down])
    subgoal unfolding restart_abs_wl_pre_def
       by (fastforce simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal
      unfolding RES_RETURN_RES less_eq_nres.simps(2)
      by (auto simp: correct_watching_correct_watching
        state_wl_l_def)
    subgoal by auto
    done
qed

definition (in twl_restart_ops) cdcl_twl_stgy_restart_abs_wl_inv
   :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0' brk T' n \<and>
       correct_watching T)\<close>


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
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  have [refine0]:
    \<open>(x, y) \<in> ?R \<Longrightarrow> ((False, x, 0), False, y, 0) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close> for x y
    by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where
      R=\<open>{(S, T).  (S, T) \<in> state_wl_l None \<and>  correct_watching S}\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    done
qed

end


context twl_restart_ops
begin

theorem cdcl_twl_stgy_restart_prog_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow> \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S', 0), False, S, 0) \<in> {((brk', T', n'), (brk, T, n)). (T', T) \<in> state_wl_l None \<and> brk' = brk \<and>
       correct_watching T' \<and> n = n'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto

  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end

end
