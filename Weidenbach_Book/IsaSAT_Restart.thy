theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart  IsaSAT_Setup
begin


subsubsection \<open>Handle true clauses from the trail\<close>

text \<open>
  Once of the first thing we do, is removing clauses we know to be true. We do in two ways:
    \<^item> along the trail (at level 0);
    \<^item> along the watch list.

  This is obviously not complete but is fast by avoiding iterating over all clauses.
\<close>
lemma get_all_ann_decomposition_change_annotation_exists:
  assumes 
    \<open>(Decided K # M', M2') \<in> set (get_all_ann_decomposition M2)\<close> and
    \<open>map lit_of M1 = map lit_of M2\<close> and
    \<open>map is_decided M1 = map is_decided M2\<close>
  shows \<open>\<exists>M'' M2'. (Decided K # M'', M2') \<in> set (get_all_ann_decomposition M1) \<and> 
    map lit_of M'' = map lit_of M' \<and>  map is_decided M'' = map is_decided M'\<close>
  using assms
proof (induction M1 arbitrary: M2 M2' rule: ann_lit_list_induct)
  case Nil
  then show ?case by auto
next
  case (Decided L xs M2)
  then show ?case
    by (cases M2; cases \<open>hd M2\<close>) fastforce+
next
  case (Propagated L m xs M2) note IH = this(1) and prems = this(2-)
  show ?case
    using IH[of _ \<open>tl M2\<close>] prems get_all_ann_decomposition_decomp[of xs]
      get_all_ann_decomposition_decomp[of M2 \<open>Decided K # M'\<close>]
    by (cases M2; cases \<open>hd M2\<close>; cases \<open>(get_all_ann_decomposition (tl M2))\<close>;
        cases \<open>hd (get_all_ann_decomposition xs)\<close>; cases \<open>get_all_ann_decomposition xs\<close>)
      fastforce+
qed

lemma valid_trail_reduction_trans:
  assumes
    M1_M2: \<open>valid_trail_reduction M1 M2\<close> and
    M2_M3: \<open>valid_trail_reduction M2 M3\<close>
  shows \<open>valid_trail_reduction M1 M3\<close>
proof -
  consider
    (same) \<open>map lit_of M2 = map lit_of M3\<close> and
       \<open>map is_decided M2 = map is_decided M3\<close> \<open>length M2 = length M3\<close> |
    (decomp_M1) K M'' M2' where
      \<open>(Decided K # M'', M2') \<in> set (get_all_ann_decomposition M2)\<close> and
      \<open>map lit_of M'' = map lit_of M3\<close> and 
      \<open>map is_decided M'' = map is_decided M3\<close> and
      \<open>length M3 = length M''\<close>
    using M2_M3 unfolding valid_trail_reduction_simps
    by auto
  note decomp_M2 = this
  consider
    (same) \<open>map lit_of M1 = map lit_of M2\<close> and
       \<open>map is_decided M1 = map is_decided M2\<close> \<open>length M1 = length M2\<close> |
    (decomp_M1) K M'' M2' where
      \<open>(Decided K # M'', M2') \<in> set (get_all_ann_decomposition M1)\<close> and
      \<open>map lit_of M'' = map lit_of M2\<close> and 
      \<open>map is_decided M'' = map is_decided M2\<close> and
      \<open>length M2 = length M''\<close>
    using M1_M2 unfolding valid_trail_reduction_simps
    by auto
  then show ?thesis
  proof cases
    case same
    from decomp_M2
    show ?thesis
    proof cases
      case same': same
      then show ?thesis
        using same by (auto simp: valid_trail_reduction_simps)
    next
      case decomp_M1 note decomp = this(1) and eq = this(2,3) and [simp] = this(4)
      obtain M4 M5 where
         decomp45: \<open>(Decided K # M4, M5) \<in> set (get_all_ann_decomposition M1)\<close> and
         M4_lit: \<open>map lit_of M4 = map lit_of M''\<close> and
         M4_dec: \<open>map is_decided M4 = map is_decided M''\<close>
        using get_all_ann_decomposition_change_annotation_exists[OF decomp, of M1] eq same
        by (auto simp: valid_trail_reduction_simps)
      show ?thesis
        by (rule valid_trail_reduction.backtrack_red[OF decomp45])
          (use M4_lit M4_dec eq same in auto)
    qed
  next
    case decomp_M1 note decomp = this(1) and eq = this(2,3) and [simp] = this(4)
    from decomp_M2
    show ?thesis
    proof cases
      case same
      obtain M4 M5 where
         decomp45: \<open>(Decided K # M4, M5) \<in> set (get_all_ann_decomposition M1)\<close> and
         M4_lit: \<open>map lit_of M4 = map lit_of M''\<close> and
         M4_dec: \<open>map is_decided M4 = map is_decided M''\<close>
        using get_all_ann_decomposition_change_annotation_exists[OF decomp, of M1] eq same
        by (auto simp: valid_trail_reduction_simps)
      show ?thesis
        by (rule valid_trail_reduction.backtrack_red[OF decomp45])
          (use M4_lit M4_dec eq same in auto)
    next
      case (decomp_M1 K' M''' M2''') note decomp' = this(1) and eq' = this(2,3) and [simp] = this(4)
      obtain M4 M5 where
         decomp45: \<open>(Decided K' # M4, M5) \<in> set (get_all_ann_decomposition M'')\<close> and
         M4_lit: \<open>map lit_of M4 = map lit_of M'''\<close> and
         M4_dec: \<open>map is_decided M4 = map is_decided M'''\<close>
        using get_all_ann_decomposition_change_annotation_exists[OF decomp', of M''] eq 
        by (auto simp: valid_trail_reduction_simps)
      obtain M6 where
        decomp45: \<open>(Decided K' # M4, M6) \<in> set (get_all_ann_decomposition M1)\<close>
        using get_all_ann_decomposition_exists_prepend[OF decomp45]
          get_all_ann_decomposition_exists_prepend[OF decomp]
          get_all_ann_decomposition_ex[of K' M4 \<open>_ @ M2' @ Decided K # _ @ M5\<close>]
        by (auto simp: valid_trail_reduction_simps)
      show ?thesis
        by (rule valid_trail_reduction.backtrack_red[OF decomp45])
          (use M4_lit M4_dec eq decomp_M1 in auto)
    qed
  qed
qed

lemma valid_trail_reduction_length_leD: \<open>valid_trail_reduction M M' \<Longrightarrow> length M' \<le> length M\<close>
  by (auto simp: valid_trail_reduction_simps)

lemma valid_trail_reduction_level0_iff:
  assumes valid:  \<open>valid_trail_reduction M M'\<close> and n_d: \<open>no_dup M\<close>
  shows \<open>(L \<in> lits_of_l M \<and> get_level M L = 0) \<longleftrightarrow> (L \<in> lits_of_l M' \<and> get_level M' L = 0)\<close>
proof -
  have H[intro]: \<open>map lit_of M = map lit_of M' \<Longrightarrow> L \<in> lits_of_l M \<Longrightarrow> L \<in>  lits_of_l M'\<close> for M M'
    by (metis lits_of_def set_map)
  have [dest]: \<open>undefined_lit c L \<Longrightarrow> L \<in> lits_of_l c \<Longrightarrow> False\<close> for c
    by (auto dest: in_lits_of_l_defined_litD)

  show ?thesis
    using valid
  proof cases
    case keep_red
    then show ?thesis
      by (metis H trail_renumber_get_level)
  next
    case (backtrack_red K M'' M2) note decomp = this(1) and eq = this(2,3)
    obtain M3 where M: \<open>M = M3 @ Decided K # M''\<close>
      using decomp by auto
    have \<open>(L \<in> lits_of_l M \<and> get_level M L = 0) \<longleftrightarrow>
      (L \<in> lits_of_l M'' \<and> get_level M'' L = 0)\<close>
      using n_d unfolding M
      by (auto 4 4 simp: valid_trail_reduction_simps get_level_append_if get_level_cons_if
          atm_of_eq_atm_of
      dest: in_lits_of_l_defined_litD cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin 
      split: if_splits)
    also have \<open>... \<longleftrightarrow> (L \<in> lits_of_l M' \<and> get_level M' L = 0)\<close>
      using eq by (metis local.H trail_renumber_get_level)
    finally show ?thesis
      by blast
  qed
qed

lemma cdcl_twl_restart_wl_cdcl_twl_restart_wl_is_cdcl_twl_restart_wl:
  assumes
    ST: \<open>cdcl_twl_restart_wl S T\<close> and TU: \<open>cdcl_twl_restart_wl T U\<close> and
    n_d: \<open>no_dup (get_trail_wl S)\<close>
  shows \<open>cdcl_twl_restart_wl S U\<close>
  using assms
proof -
  obtain M M' N N' NE' UE' NE UE Q Q' W' W where
    S: \<open>S = (M, N, None, NE, UE, Q, W)\<close> and
    T: \<open>T = (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close> and
    tr_red: \<open>valid_trail_reduction M M'\<close> and
    init: \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    learned: \<open>learned_clss_lf N' + UE' \<subseteq># learned_clss_lf N\<close> and
    NUE: \<open>\<forall>E\<in>#NE' + UE'. \<exists>L\<in>set E. L \<in> lits_of_l M \<and> get_level M L = 0\<close> and
    ge0: \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> 0 < E \<longrightarrow> 0 < E' \<longrightarrow>
        E \<in># dom_m N' \<and> N' \<propto> E = N \<propto> E'\<close> and
    new0: \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow>
        E' \<noteq> 0 \<longrightarrow> mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> and
    still0: \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow>
        E' = 0 \<longrightarrow> E = 0\<close> and
    dom0: \<open>0 \<notin># dom_m N'\<close> and
    QQ': \<open>if length M = length M' then Q = Q' else Q' = {#}\<close> and
    \<open>correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
    using ST unfolding cdcl_twl_restart_wl.simps
    apply -
    apply normalize_goal+
    by blast
  obtain M'' N'' NE'' UE'' Q'' W'' where
    U: \<open>U = (M'', N'', None, NE + mset `# NE' + mset `# NE'', UE + mset `# UE' + mset `# UE'', Q'',
      W'')\<close> and
    tr_red': \<open>valid_trail_reduction M' M''\<close> and
    init': \<open>init_clss_lf N' = init_clss_lf N'' + NE''\<close> and
    learned': \<open>learned_clss_lf N'' + UE'' \<subseteq># learned_clss_lf N'\<close> and
    NUE': \<open>\<forall>E\<in>#NE'' + UE''.
        \<exists>L\<in>set E.
           L \<in> lits_of_l M' \<and>
           get_level M' L = 0\<close> and
    ge0': \<open>\<forall>L E E'.
        Propagated L E \<in> set M'' \<longrightarrow>
        Propagated L E' \<in> set M' \<longrightarrow>
        0 < E \<longrightarrow>
        0 < E' \<longrightarrow>
        E \<in># dom_m N'' \<and> N'' \<propto> E = N' \<propto> E'\<close> and
    new0': \<open>\<forall>L E E'.
        Propagated L E \<in> set M'' \<longrightarrow>
        Propagated L E' \<in> set M' \<longrightarrow>
        E = 0 \<longrightarrow>
        E' \<noteq> 0 \<longrightarrow>
        mset (N' \<propto> E')
        \<in># NE + mset `# NE' + mset `# NE'' +
            (UE + mset `# UE') +
            mset `# UE''\<close> and
    still0': \<open>\<forall>L E E'.
        Propagated L E \<in> set M'' \<longrightarrow>
        Propagated L E' \<in> set M' \<longrightarrow>
        E' = 0 \<longrightarrow> E = 0\<close> and
    dom0': \<open>0 \<notin># dom_m N''\<close> and
    Q'Q'': \<open>if length M' = length M'' then Q' = Q'' else Q'' = {#}\<close> and
    corr: \<open>correct_watching (M'', N'', None, NE + mset `# NE' + mset `# NE'',
        UE + mset `# UE' + mset `# UE'', Q'',
       W'')\<close>
    using TU unfolding cdcl_twl_restart_wl.simps T apply -
    apply normalize_goal+
    by blast
  have U': \<open>U = (M'', N'', None, NE + mset `# (NE' + NE''), UE + mset `# (UE' + UE''), Q'',
      W'')\<close>
    unfolding U by simp
  show ?thesis
    unfolding S U'
    apply (rule cdcl_twl_restart_wl.restart_trail)
    subgoal using valid_trail_reduction_trans[OF tr_red tr_red'] .
    subgoal using init init' by auto
    subgoal using learned learned' subset_mset.dual_order.trans by fastforce
    subgoal using NUE NUE' valid_trail_reduction_level0_iff[OF tr_red] n_d unfolding S by auto
    subgoal using ge0 ge0' tr_red' init learned NUE ge0  still0' (* TODO tune proof *)
      apply (auto dest: valid_trail_reduction_Propagated_inD)
       apply (metis neq0_conv still0' valid_trail_reduction_Propagated_inD)+
      done
    subgoal using new0 new0' tr_red' init learned NUE ge0  (* TODO tune proof *)
      apply (auto dest: valid_trail_reduction_Propagated_inD)
      by (smt neq0_conv valid_trail_reduction_Propagated_inD)
    subgoal using still0 still0' tr_red' by (fastforce dest: valid_trail_reduction_Propagated_inD)
    subgoal using dom0' .
    subgoal using QQ' Q'Q'' valid_trail_reduction_length_leD[OF tr_red]
        valid_trail_reduction_length_leD[OF tr_red']
      by (auto split: if_splits)
    subgoal using corr by (simp add: ac_simps)
    done
qed

lemma map_lit_of_eq_defined_litD: \<open>map lit_of M = map lit_of M' \<Longrightarrow> defined_lit M = defined_lit M'\<close>
  apply (induction M arbitrary: M')
  subgoal by auto
  subgoal for L M M'
    by (cases M'; cases L; cases "hd M'")
      (auto simp: defined_lit_cons)
  done
   

lemma map_lit_of_eq_no_dupD: \<open>map lit_of M = map lit_of M' \<Longrightarrow> no_dup M = no_dup M'\<close>
  apply (induction M arbitrary: M')
  subgoal by auto
  subgoal for L M M'
    by (cases M'; cases L; cases "hd M'")
      (auto dest: map_lit_of_eq_defined_litD)
  done

lemma tranclp_cdcl_twl_restart_wl_no_dup:
  assumes
    ST: \<open>cdcl_twl_restart_wl\<^sup>*\<^sup>* S T\<close> and
    n_d: \<open>no_dup (get_trail_wl S)\<close>
  shows \<open>no_dup (get_trail_wl T)\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal 
    by (auto simp: cdcl_twl_restart_wl.simps valid_trail_reduction_simps
      dest: map_lit_of_eq_no_dupD dest!: no_dup_appendD get_all_ann_decomposition_exists_prepend)
  done

lemma rtranclp_cdcl_twl_restart_wl_cdcl_is_cdcl_twl_restart_wl:
  assumes
    ST: \<open>cdcl_twl_restart_wl\<^sup>+\<^sup>+ S T\<close> and
    n_d: \<open>no_dup (get_trail_wl S)\<close>
  shows \<open>cdcl_twl_restart_wl S T\<close>
  using assms
  apply (induction rule: tranclp_induct)
  subgoal by auto
  subgoal 
    using cdcl_twl_restart_wl_cdcl_twl_restart_wl_is_cdcl_twl_restart_wl
    tranclp_cdcl_twl_restart_wl_no_dup by blast
  done

paragraph \<open>Specification\<close>

inductive remove_one_watched_true_clause where
remove_irred: 
  \<open>remove_one_watched_true_clause L (M, N, D, NE, UE, Q, W)
     (M, N, D, add_mset (mset (N\<propto>C))NE, UE, Q, W)\<close>
if
  \<open>L \<in> lits_of_l M\<close> and
  \<open>get_level M L = 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>L \<in> set (watched_l (N\<propto>C))\<close> and
  \<open>irred N C\<close> |
remove_red: 
  \<open>remove_one_watched_true_clause L (M, N, D, NE, UE, Q, W)
     (M, N, D, NE, add_mset (mset (N\<propto>C)) UE, Q, W)\<close>
if
  \<open>L \<in> lits_of_l M\<close> and
  \<open>get_level M L = 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>L \<in> set (watched_l (N\<propto>C))\<close> and
  \<open>\<not>irred N C\<close>

inductive remove_all_watched_true_clause where
  \<open>remove_all_watched_true_clause (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L 0 # M', N', D', NE', UE', Q', W')\<close>
if \<open>full (remove_one_watched_true_clause L) (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L C # M', N', D', NE', UE', Q', W')\<close>


definition (in -) extract_and_remove
  :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> ('v clauses_l \<times> 'v clause_l \<times> bool) nres\<close>
where
  \<open>extract_and_remove N j = do {
      ASSERT((j :: nat) \<in># dom_m (N :: 'v clauses_l));
      SPEC(\<lambda>(N' :: 'v clauses_l, C' :: 'v clause_l, b :: bool). N' = N(j \<hookrightarrow> []) \<and> C' = N\<propto>j \<and> b = irred N j)
    }\<close>

fun (in -) partial_correct_watching where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
     (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE).
       (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (watched_l (N\<propto>i))))\<close>

lemma (in -) in_set_mset_eq_in:
  \<open>i \<in> set A \<Longrightarrow> mset A = B \<Longrightarrow> i \<in># B\<close>
  by fastforce

lemma (in -) \<open>correct_watching S \<Longrightarrow> partial_correct_watching S\<close>
  by (cases S)
    (auto simp: correct_watching.simps partial_correct_watching.simps clause_to_update_def
    simp del: set_mset_mset dest: in_set_mset_eq_in)

lemma impI_isabelle_you_are_stupid: "(\<And>M. M = M' \<Longrightarrow> R M) \<Longrightarrow> (R M')"
  
  by blast

lemma remove_one_watched_true_clause_decomp:
  assumes \<open>remove_one_watched_true_clause L S T\<close> and
    \<open>get_level (get_trail_wl S) L = 0\<close> and
     \<open>L \<in> lits_of_l (get_trail_wl S)\<close>
  obtains M N U D NE UE W Q M' N' U' NE' UE' W' Q' where
    \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
    \<open>T = (M', N', D, NE + NE', UE + UE', Q, W)\<close> and
    \<open>\<forall>C\<in># NE'+UE'. \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M\<close> 
    \<open>dom_m N' \<subseteq># dom_m N\<close> and
    \<open>M = M'\<close>
    apply atomize
  using assms
  by (induction) (auto simp: conj_imp_eq_imp_imp dest: in_set_takeD[of _ 2])

lemma rtranclp_remove_one_watched_true_clause_decomp_Ex:
  assumes \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close> and
    \<open>get_level (get_trail_wl S) L = 0\<close> and
     \<open>L \<in> lits_of_l (get_trail_wl S)\<close>
  shows
    \<open>\<exists>M N U D NE UE W Q M' N' U' D' NE' UE' W' Q'. S = (M, N, D, NE, UE, Q, W) \<and>
     T = (M', N', D, NE + NE', UE + UE', Q, W) \<and>
     (\<forall>C\<in># NE'+UE'. \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
     dom_m N' \<subseteq># dom_m N \<and> M = M'\<close>
  using assms
  apply (induction)
  subgoal by (cases S) auto
  subgoal for T U
    by (drule remove_one_watched_true_clause_decomp) (auto simp: dest!: )
  done

lemma
  assumes \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close> and
    \<open>partial_correct_watching S\<close> and
    \<open>get_conflict_wl S = None\<close> and
    \<open>\<forall>L C. Propagated L C \<in> set (get_trail_wl T) \<longrightarrow> C = 0\<close>
  shows \<open>cdcl_twl_restart_wl S T\<close>
  using assms
  oops

definition remove_all_clause_watched_by_inv where
  \<open>remove_all_clause_watched_by_inv = (\<lambda>(M\<^sub>0, N\<^sub>0, D\<^sub>0, NE\<^sub>0, UE\<^sub>0, Q\<^sub>0, W\<^sub>0) (M, N, D, NE, UE, Q, W).
       ran_mf N + NE + UE = ran_mf N\<^sub>0 + NE\<^sub>0 + UE\<^sub>0)\<close>

definition remove_all_clause_watched_by :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close> where
\<open>remove_all_clause_watched_by L = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    (_, N, NE, UE) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N, NE, UE). partial_correct_watching (M, N, D, NE, UE, Q, W)\<^esup>
      (\<lambda>(i, N, NE, UE). i < length (W L))
      (\<lambda>(i, N, NE, UE). do {
          if i \<in># dom_m N
          then do {
            (N', C, b) \<leftarrow> extract_and_remove N (W L!i);
            if b then RETURN (i+1, N', add_mset (mset C) NE, UE)
            else RETURN (i+1, N', NE, add_mset (mset C) UE)
          }
          else (* The clause might have already been deleted *)
            RETURN (i+1, N, NE, UE)
      })
      (0, N, NE, UE);
    RETURN (M, N, D, NE, UE, Q, W(L := []))
  })\<close>

definition remove_trivially_true_clause where
  \<open>remove_trivially_true_clause = (\<lambda>S. do {
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, S). partial_correct_watching S\<^esup>
      (\<lambda>(i, S). i > 0 \<and> \<not>is_decided (get_trail_wl S!i))
      (\<lambda>(i, (M, N, D, NE, UE, Q, W)). do {
         ASSERT(i > 0);
         let L = lit_of (M!i);
         (M, N, D, NE, UE, Q, W) \<leftarrow> remove_all_clause_watched_by L (M, N, D, NE, UE, Q, W);
         let M = M[i := Propagated L 0];
         RETURN(i-1, (M, N, D, NE, UE, Q, W))
      })
      (0, S);
    RETURN S
  })\<close>

definition collect_valid_indices where
  \<open>collect_valid_indices S = SPEC (\<lambda>N. mset N = dom_m (get_clauses_wl S))\<close>

context isasat_restart_bounded
begin



end

end