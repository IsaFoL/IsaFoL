theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart  IsaSAT_Setup
begin


text \<open>
  The idea of the restart works the following:
  \<^enum> We backtrack to level 0. This simplifies further steps. 
  \<^enum> We move all clauses used to justify the remaining propagating at level 0 out of \<^term>\<open>N\<close> and
    move them to \<^term>\<open>NE\<close> or \<^term>\<open>UE\<close>. To do so, we move that are watching the
    corresponding literal to the entailed clauses. This includes the clauses justifying the
    propagation (if it was not already there).
  \<^enum> Now we can safely deleting all learned clauses.
  \<^enum> Once all that is done, we have to recalculate the watch lists (and can on the way GC the set of
    clauses).
\<close>

subsubsection \<open>Handle true clauses from the trail\<close>

fun (in -) partial_correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
     (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE + UE).
       (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (watched_l (N\<propto>i))))\<close>

lemma (in -) in_set_mset_eq_in:
  \<open>i \<in> set A \<Longrightarrow> mset A = B \<Longrightarrow> i \<in># B\<close>
  by fastforce

lemma (in -) \<open>correct_watching S \<Longrightarrow> partial_correct_watching S\<close>
  by (cases S)
    (auto simp: correct_watching.simps partial_correct_watching.simps clause_to_update_def
    simp del: set_mset_mset dest: in_set_mset_eq_in)


text \<open>Our transformation will be chains of a weaker version of restarts, that don't update the
  watch lists and only keep partial correctness.\<close>

inductive cdcl_twl_restart_wl_p :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart_wl_p (M, N, None, NE, UE, Q, W)
       (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
  if
    \<open>valid_trail_reduction M M'\<close> and
    \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    \<open>learned_clss_lf N' + UE' \<subseteq># learned_clss_lf N\<close> and
    \<open>\<forall>E\<in># (NE'+UE'). \<exists>L\<in>set E. L \<in> lits_of_l M \<and> get_level M L = 0\<close> and
    \<open>\<forall>L E E' . Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E \<in># dom_m N \<longrightarrow> E > 0  \<longrightarrow> E' > 0 \<longrightarrow>
        E \<in># dom_m N' \<and> N' \<propto> E = N \<propto> E'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow> E' \<noteq> 0 \<longrightarrow>
       mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E' = 0 \<longrightarrow> E = 0\<close> and
    \<open>0 \<notin># dom_m N'\<close> and
    \<open>if length M = length M' then Q = Q' else Q' = {#}\<close> and
    \<open>partial_correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>

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

lemma cdcl_twl_restart_wl_p_cdcl_twl_restart_wl_p_is_cdcl_twl_restart_wl_p:
  assumes
    ST: \<open>cdcl_twl_restart_wl_p S T\<close> and TU: \<open>cdcl_twl_restart_wl_p T U\<close> and
    n_d: \<open>no_dup (get_trail_wl S)\<close>
  shows \<open>cdcl_twl_restart_wl_p S U\<close>
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
    \<open>partial_correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
    using ST unfolding cdcl_twl_restart_wl_p.simps
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
    corr: \<open>partial_correct_watching (M'', N'', None, NE + mset `# NE' + mset `# NE'',
        UE + mset `# UE' + mset `# UE'', Q'',
       W'')\<close>
    using TU unfolding cdcl_twl_restart_wl_p.simps T apply -
    apply normalize_goal+
    by blast
  have U': \<open>U = (M'', N'', None, NE + mset `# (NE' + NE''), UE + mset `# (UE' + UE''), Q'',
      W'')\<close>
    unfolding U by simp
  show ?thesis
    unfolding S U'
    apply (rule cdcl_twl_restart_wl_p.restart_trail)
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

lemma tranclp_cdcl_twl_restart_wl_p_no_dup:
  assumes
    ST: \<open>cdcl_twl_restart_wl_p\<^sup>*\<^sup>* S T\<close> and
    n_d: \<open>no_dup (get_trail_wl S)\<close>
  shows \<open>no_dup (get_trail_wl T)\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal 
    by (auto simp: cdcl_twl_restart_wl_p.simps valid_trail_reduction_simps
      dest: map_lit_of_eq_no_dupD dest!: no_dup_appendD get_all_ann_decomposition_exists_prepend)
  done

lemma rtranclp_cdcl_twl_restart_wl_p_cdcl_is_cdcl_twl_restart_wl_p:
  assumes
    ST: \<open>cdcl_twl_restart_wl_p\<^sup>+\<^sup>+ S T\<close> and
    n_d: \<open>no_dup (get_trail_wl S)\<close>
  shows \<open>cdcl_twl_restart_wl_p S T\<close>
  using assms
  apply (induction rule: tranclp_induct)
  subgoal by auto
  subgoal 
    using cdcl_twl_restart_wl_p_cdcl_twl_restart_wl_p_is_cdcl_twl_restart_wl_p
    tranclp_cdcl_twl_restart_wl_p_no_dup by blast
  done

paragraph \<open>Specification\<close>

text \<open>
  Once of the first thing we do, is removing clauses we know to be true. We do in two ways:
    \<^item> along the trail (at level 0);
    \<^item> along the watch list.

  This is obviously not complete but is fast by avoiding iterating over all clauses.
\<close>
inductive remove_one_watched_true_clause :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
remove_irred: 
  \<open>remove_one_watched_true_clause L (M, N, D, NE, UE, Q, W)
     (M, fmdrop C N, D, add_mset (mset (N\<propto>C))NE, UE, Q, W)\<close>
if
  \<open>L \<in> lits_of_l M\<close> and
  \<open>get_level M L = 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>L \<in> set (watched_l (N\<propto>C))\<close> and
  \<open>irred N C\<close> |
remove_red: 
  \<open>remove_one_watched_true_clause L (M, N, D, NE, UE, Q, W)
     (M, fmdrop C N, D, NE, add_mset (mset (N\<propto>C)) UE, Q, W)\<close>
if
  \<open>L \<in> lits_of_l M\<close> and
  \<open>get_level M L = 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>L \<in> set (watched_l (N\<propto>C))\<close> and
  \<open>\<not>irred N C\<close>

inductive remove_all_watched_true_clause :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>remove_all_watched_true_clause (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L 0 # M', N', D', NE', UE', Q', W')\<close>
if \<open>full (remove_one_watched_true_clause L) (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L C # M', N', D', NE', UE', Q', W')\<close>

(* TODO Move *)
lemma singleton_eq_image_mset_iff:  \<open>{#a#} = f `# NE' \<longleftrightarrow> (\<exists>b. NE' = {#b#} \<and> f b = a)\<close>
  by (cases NE') auto

lemma image_mset_If_eq_notin:
   \<open>C \<notin># A \<Longrightarrow> {#f (if x = C then a x else b x). x \<in># A#} = {# f(b x). x \<in># A #}\<close>
  by (induction A) auto

lemma init_clss_lf_fmdrop[simp]:
  \<open>irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> init_clss_lf (fmdrop C N) = remove1_mset (N\<propto>C) (init_clss_lf N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)


lemma init_clss_lf_fmdrop_irrelev[simp]:
  \<open>\<not>irred N C \<Longrightarrow> init_clss_lf (fmdrop C N) = init_clss_lf N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma learned_clss_lf_lf_fmdrop[simp]:
  \<open>\<not>irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> learned_clss_lf (fmdrop C N) = remove1_mset (N\<propto>C) (learned_clss_lf N)\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)


lemma learned_clss_lf_lf_fmdrop_irrelev[simp]:
  \<open>irred N C \<Longrightarrow> learned_clss_lf (fmdrop C N) = learned_clss_lf N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma ran_mf_lf_fmdrop[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow>  ran_mf (fmdrop C N) = remove1_mset (N\<propto>C) (ran_mf N)\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>] dest!: multi_member_split)

(* End Move *)

lemma remove_one_watched_true_clause_partial_correct_watching:
 assumes \<open>remove_one_watched_true_clause L S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>]
  by (induction) 
    (auto simp: partial_correct_watching.simps image_mset_remove1_mset_if
  dest: multi_member_split)

lemma rtranclp_remove_one_watched_true_clause_partial_correct_watching:
 assumes \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>]
  by (induction) 
    (auto simp: remove_one_watched_true_clause_partial_correct_watching)

inductive different_annot_all_killed where
propa_changed:
  \<open>different_annot_all_killed N NUE (Propagated L C) (Propagated L C')\<close>
    if \<open>C \<noteq> C'\<close> and \<open>C' = 0\<close> and
       \<open>C \<in># dom_m N \<Longrightarrow> mset (N\<propto>C) \<in># NUE\<close> |
propa_not_changed:
  \<open>different_annot_all_killed N NUE (Propagated L C) (Propagated L C)\<close> |
decided_not_changed:
  \<open>different_annot_all_killed N NUE (Decided L) (Decided L)\<close>

lemma different_annot_all_killed_refl[iff]:
  \<open>different_annot_all_killed N NUE z z \<longleftrightarrow> is_proped z \<or> is_decided z\<close>
  by (cases z) (auto simp: different_annot_all_killed.simps)

abbreviation different_annots_all_killed where
  \<open>different_annots_all_killed N NUE \<equiv> list_all2 (different_annot_all_killed N NUE)\<close>

lemma different_annots_all_killed_refl:
  \<open>count_decided M = 0 \<Longrightarrow> different_annots_all_killed N NUE M M\<close>
  by (auto intro!: list.rel_refl_strong simp: count_decided_0_iff is_decided_no_proped_iff)

lemma remove_one_watched_true_clause_different_annots_all_killed:
  assumes
    \<open>remove_one_watched_true_clause L S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close>
  shows \<open>different_annots_all_killed (get_clauses_wl S) (get_unit_clauses_wl S)(get_trail_wl S) (get_trail_wl T)\<close>
  using assms by (induction) (auto simp: different_annots_all_killed_refl)

lemma remove_one_watched_true_clause_trail:
  assumes
    \<open>remove_one_watched_true_clause L S T\<close> a
  shows \<open>get_trail_wl S =  get_trail_wl T\<close>
  using assms by (induction) (auto simp: different_annots_all_killed_refl)

lemma rtranclp_remove_one_watched_true_clause_trail:
  assumes
    \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close> a
  shows \<open>get_trail_wl S = get_trail_wl T\<close>
  using assms by (induction) (auto simp: remove_one_watched_true_clause_trail)

definition reduce_dom_clauses where
  \<open>reduce_dom_clauses N N' \<longleftrightarrow>
     (\<forall>C. C \<in># dom_m N' \<longrightarrow> C \<in># dom_m N \<and> N\<propto>C = N'\<propto>C)\<close>

lemma reduce_dom_clauses_fdrop[simp]: \<open>reduce_dom_clauses N (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def dest: in_diffD multi_member_split
    distinct_mem_diff_mset)

lemma reduce_dom_clauses_refl[simp]: \<open>reduce_dom_clauses N N\<close>
  by (auto simp: reduce_dom_clauses_def)

lemma reduce_dom_clauses_trans:
  \<open>reduce_dom_clauses N N' \<Longrightarrow> reduce_dom_clauses N' N'a \<Longrightarrow> reduce_dom_clauses N N'a\<close>
  by (auto simp: reduce_dom_clauses_def)

lemma remove_one_watched_true_clause_decomp:
  assumes
    \<open>remove_one_watched_true_clause L S T\<close>
  obtains M N U D NE UE W Q M' N' U' NE' UE' W' Q' where
    \<open>\<exists>M N D NE UE W Q M' N' NE' UE'. S = (M, N, D, NE, UE, Q, W) \<and>
    T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<and>
    (\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
    dom_m N' \<subseteq># dom_m N \<and>
    M = M' \<and>
    init_clss_lf N = init_clss_lf N' + NE' \<and>
    learned_clss_lf N = learned_clss_lf N' + UE' \<and>
    reduce_dom_clauses N N'\<close>
  using assms
  by (induction) 
    (fastforce simp: conj_imp_eq_imp_imp singleton_eq_image_mset_iff
    dest: in_set_takeD[of _ 2])+

lemma rtranclp_remove_one_watched_true_clause_decomp_Ex:
  assumes \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close>
  shows
    \<open>\<exists>M N D NE UE W Q M' N' NE' UE'. S = (M, N, D, NE, UE, Q, W) \<and>
     T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<and>
     (\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
     dom_m N' \<subseteq># dom_m N \<and> M = M' \<and>
    init_clss_lf N = init_clss_lf N' + NE' \<and>
    learned_clss_lf N = learned_clss_lf N' + UE' \<and>
    reduce_dom_clauses N N'\<close>
  using assms
  apply (induction)
  subgoal by (cases S) auto
  subgoal for T U
    by (drule remove_one_watched_true_clause_decomp)
      (auto simp: image_mset_union[symmetric] ac_simps simp del: image_mset_union
        intro: reduce_dom_clauses_trans)
  done

lemma reduce_dom_clauses_different_annots_all_killed:
  \<open>reduce_dom_clauses N N' \<Longrightarrow> different_annots_all_killed N NUE M M' \<Longrightarrow>
    different_annots_all_killed N' NUE M M'\<close>
  apply (rule list_all2_mono)
   apply assumption
  by (auto simp: different_annot_all_killed.simps reduce_dom_clauses_def all_conj_distrib
    dest!: multi_member_split)

lemma rtranclp_remove_one_watched_true_clause_decomp:
  assumes
    \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close>
  shows \<open>different_annots_all_killed (get_clauses_wl S) (get_unit_clauses_wl S) 
     (get_trail_wl S) (get_trail_wl T)\<close>
  using assms apply (induction)
  subgoal by (auto simp: remove_one_watched_true_clause_decomp different_annots_all_killed_refl)
  subgoal for T U
    apply (elim remove_one_watched_true_clause_decomp[of L T U])
    using remove_one_watched_true_clause_different_annots_all_killed[of L T U]
    by auto
  done

lemma remove_all_watched_true_clause_partial_correct_watching:
 assumes \<open>remove_all_watched_true_clause S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>]
  apply (induction) 
  by (auto dest!: rtranclp_remove_one_watched_true_clause_partial_correct_watching
    simp: full_def)
    (auto simp: partial_correct_watching.simps)

definition reasons_invs_wl where
  \<open>reasons_invs_wl S \<longleftrightarrow>
    (* distinct_mset (mark_of `# filter_mset is_proped (mset (get_trail_wl S))) \<and> *)
    (\<forall>L C M1 M2 . M2 @ Propagated L C # M1 = get_trail_wl S \<longrightarrow> C > 0 \<longrightarrow> 
      C \<in># dom_m (get_clauses_wl S) \<longrightarrow> (L = get_clauses_wl S \<propto> C ! 0 \<and>
       L \<in> set (watched_l (get_clauses_wl S \<propto> C))
        (* \<and>
        M1 \<Turnstile>as CNot (remove1_mset L (mset (get_clauses_wl S \<propto> C))) *)
    ))\<close>

lemma no_step_remove_one_watched_true_clause_different_annot_all_killed:
  fixes S :: \<open>'v twl_st_wl\<close>
  assumes
    \<open>no_step (remove_one_watched_true_clause L) S\<close> and
    count_dec: \<open>count_decided (get_trail_wl S) = 0\<close> and
    L: \<open>Propagated L C \<in> set (get_trail_wl S)\<close> and
    \<open>reasons_invs_wl S\<close>
  shows \<open>different_annot_all_killed (get_clauses_wl S) (get_unit_clauses_wl S) 
     (Propagated L C) (Propagated L (0 :: nat))\<close>
  using assms count_decided_ge_get_level[of \<open>get_trail_wl S\<close> L]
  by (cases S)
   (auto 5 5 simp: different_annot_all_killed.simps remove_one_watched_true_clause.simps
    all_conj_distrib reasons_invs_wl_def
    dest!: multi_member_split split_list[of \<open>Propagated L C\<close>])

lemma remove_one_watched_true_clause_reasons_invs_wl:
  \<open>remove_one_watched_true_clause L S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>] apply -
  by (induction rule: remove_one_watched_true_clause.induct)
    (auto simp: reasons_invs_wl_def dest: multi_member_split)

lemma rtranclp_remove_one_watched_true_clause_reasons_invs_wl:
  \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>] apply -
  by (induction rule: rtranclp_induct)
    (auto simp: remove_one_watched_true_clause_reasons_invs_wl)

lemma reasons_invs_wl_change_annot:
  \<open>reasons_invs_wl (M @ Propagated L C # M', N', D', NE', UE', Q', W') \<Longrightarrow>
       reasons_invs_wl (M @ Propagated L 0 # M', N', D', NE', UE', Q', W')\<close>
  apply (auto 5 5 simp: reasons_invs_wl_def
    simp del: append_assoc append_Cons
    simp: append_assoc[symmetric] append_Cons[symmetric]
    elim!: list_match_lel_lel)
  apply (auto 5 5 simp: reasons_invs_wl_def
    elim!: list_match_lel_lel)
  done

lemma remove_all_watched_true_clause_reasons_invs_wl:
  \<open>remove_all_watched_true_clause S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>] apply -
  by (induction rule: remove_all_watched_true_clause.induct)
    (auto simp: full_def
        dest!: rtranclp_remove_one_watched_true_clause_reasons_invs_wl
       dest: multi_member_split reasons_invs_wl_change_annot)

lemma rtranclp_remove_all_watched_true_clause_reasons_invs_wl:
  \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>] apply -
  by (induction rule: rtranclp_induct)
    (auto simp: remove_all_watched_true_clause_reasons_invs_wl)

lemma reduce_dom_clauses_ran_mf_subset: \<open>reduce_dom_clauses N N' \<Longrightarrow> ran_mf N' \<subseteq># ran_mf N\<close>
  apply (auto simp: reduce_dom_clauses_def ran_m_def)
  apply (induction \<open>dom_m N\<close> arbitrary: N N')
  subgoal by auto
  subgoal premises p for C A N N'
   using p(1)[of \<open>fmdrop C N\<close>] p(2-)
   by auto
  done


lemma remove_all_watched_true_clause_different_annots_all_killed:
  assumes
    \<open>remove_all_watched_true_clause S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close> and
    reasons: \<open>reasons_invs_wl S\<close>
  shows \<open>different_annots_all_killed (get_clauses_wl S) (get_unit_clauses_wl T) (get_trail_wl S)
      (get_trail_wl T)\<close>
  using assms
proof (induction)
  case (1 L M C M' N D NE UE Q W N' D' TNE' TUE' Q' W') note rem = this(1) and count_dec = this(2)
    and reasons = this(3)
  let ?M = \<open>M @ Propagated L C # M'\<close>
  let ?S = \<open>(M @ Propagated L C # M', N, D, NE, UE, Q, W)\<close>
  let ?T = \<open>(M @ Propagated L C # M', N', D', TNE', TUE', Q', W')\<close>
  have nss: \<open>no_step (remove_one_watched_true_clause L) ?T\<close> and
    st: \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* ?S ?T\<close>
    using rem unfolding full_def
    by fast+
  have \<open>reasons_invs_wl (M @ Propagated L C # M', N', D', TNE', TUE', Q', W')\<close>
    using reasons 1
    by (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
        full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
     intro!: list.rel_refl_strong)
  with no_step_remove_one_watched_true_clause_different_annot_all_killed[OF nss, of C]
  have annot_L_N: \<open>different_annot_all_killed N' (TNE' + TUE') (Propagated L C) (Propagated L 0)\<close>
    using count_dec reasons by auto
  
  then have annot: \<open>different_annots_all_killed N' (TNE' + TUE') (M @ Propagated L C # M')
     (M @ Propagated L 0 # M')\<close>
    by (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
        full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
     intro!: list.rel_refl_strong)

  from rtranclp_remove_one_watched_true_clause_decomp_Ex[OF st]
  obtain M'' NE' UE' where
    \<open>?S = (?M, N, D, NE, UE, Q, W)\<close> and 
    \<open>?T = (M'', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<close> and 
    \<open>\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level ?M L = 0 \<and> L \<in> lits_of_l ?M\<close> and 
    dom_m_NN': \<open>dom_m N' \<subseteq># dom_m N\<close> and 
    \<open>?M = M''\<close> and 
    init: \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and 
    learned: \<open>learned_clss_lf N = learned_clss_lf N' + UE'\<close> and 
    red_NN: \<open>reduce_dom_clauses N N'\<close> and
    \<open>TNE' = NE + mset `# NE'\<close> and
    \<open>TUE' = UE + mset `# UE'\<close>
    by blast
  have N_N':  \<open>ran_mf N = ran_mf N' + NE' + UE'\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    unfolding init learned
    by (auto simp: ac_simps all_clss_lf_ran_m) 
  have notin: \<open>C \<notin># dom_m N'\<close>
  if 
    \<open>0 < C\<close> and
    \<open>C \<in># dom_m N\<close>
  proof (rule ccontr)
    assume J: \<open>\<not> ?thesis\<close>
    then have \<open>mset (N\<propto>C) = mset (N'\<propto>C)\<close>
      using red_NN unfolding reduce_dom_clauses_def by auto
    have \<open>L = N\<propto>C!0\<close> and \<open>L \<in> set (watched_l (N\<propto>C))\<close>
      using reasons that by (auto simp: reasons_invs_wl_def)
    moreover have \<open>get_level (M @ Propagated L C # M') K = 0\<close> for K
      using count_decided_ge_get_level[of \<open>M @ Propagated L C # M'\<close> K] count_dec
      by auto
    ultimately show False
      using that nss J red_NN apply (auto 5 5 simp: remove_one_watched_true_clause.simps
        reduce_dom_clauses_def)
      by metis 
  qed
  have \<open>mset (N\<propto>C) \<in># mset `# (NE' + UE')\<close>
  if 
    \<open>0 < C\<close> and
    \<open>C \<in># dom_m N\<close>
  proof -
    have \<open>C \<notin># dom_m N'\<close>
       using notin[OF that] .
    (* have \<open>N\<propto>C \<in># ran_mf N\<close>
      using that by (auto simp: ran_m_def) *)
    then have \<open>N\<propto>C \<in># ran_mf N - ran_mf N'\<close>
      using dom_m_NN'
      using multi_member_split[OF that(2)]
       apply (auto simp: ran_m_def dest!: )
    sorry
    then show ?thesis
      unfolding N_N' apply auto
      sorry
  have \<open>different_annots_all_killed N (NE + mset `# NE' + UE + mset `# UE') (M @ Propagated L C # M')
     (M @ Propagated L 0 # M')\<close>
    using annot annot_L_N
    apply (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
        full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
        different_annot_all_killed.simps
     intro!: list.rel_refl_strong)
     
    sorry
  show ?case apply simp sorry
  unfolding full_def apply clarify
  
  apply (drule no_step_remove_one_watched_true_clause_different_annot_all_killed)
  apply (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
        full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
     intro!: list.rel_refl_strong)

lemma rtranclp_remove_all_watched_true_clause_partial_correct_watching:
 assumes \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_wl S\<close>]
  by (induction) 
    (auto simp: remove_all_watched_true_clause_partial_correct_watching)

lemma remove_all_watched_true_clause_decomp_Ex:
  assumes \<open>remove_all_watched_true_clause S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close>
  shows
    \<open>\<exists>M N D NE UE W Q M' N' NE' UE'. 
     S = (M, N, D, NE, UE, Q, W) \<and>
     T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<and>
     (\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
     dom_m N' \<subseteq># dom_m N \<and> map lit_of M = map lit_of M' \<and>
     count_decided M' = 0 \<and>
     init_clss_lf N = init_clss_lf N' + NE' \<and>
     learned_clss_lf N = learned_clss_lf N' + UE' \<and>
     reduce_dom_clauses N N'\<close>
  using assms
  apply (induction)
  subgoal for L M C M' N D NE UE Q W N' D' NE' UE' Q' W'
    using count_decided_ge_get_level[of \<open>M @ Propagated L C # M'\<close> L] unfolding full_def
    apply -
    apply normalize_goal+
    by (drule rtranclp_remove_one_watched_true_clause_decomp_Ex) auto
  done

lemma rtranclp_remove_all_watched_true_clause_decomp_Ex:
  assumes \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close>
  shows
    \<open>\<exists>M N D NE UE W Q M' N' NE' UE'. 
     S = (M, N, D, NE, UE, Q, W) \<and>
     T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<and>
     (\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
     dom_m N' \<subseteq># dom_m N \<and> map lit_of M = map lit_of M' \<and>
     count_decided M' = 0 \<and>
     init_clss_lf N = init_clss_lf N' + NE' \<and>
     learned_clss_lf N = learned_clss_lf N' + UE' \<and>
     reduce_dom_clauses N N'\<close>
proof -
  have H[simp]: \<open>count_decided M'a = 0 \<Longrightarrow>  get_level M'a L = 0\<close> for M'a L
    using count_decided_ge_get_level[of M'a]
    by (auto intro!: ext)
  have H: \<open>map lit_of M = map lit_of M' \<Longrightarrow> lits_of_l M = lits_of_l M'\<close> for M M'
    by (metis lits_of_def set_map)
  show ?thesis
    using assms
    apply (induction)
    subgoal by (cases S) auto
    subgoal for T U 
      apply (drule remove_all_watched_true_clause_decomp_Ex)
      subgoal by auto
      subgoal
        supply image_mset_union[simp del] image_mset_union[symmetric, simp]
        by (fastforce dest: H simp: ac_simps intro: reduce_dom_clauses_trans)
      done
    done
qed

lemma different_annot_all_killed_trans:
  assumes
    \<open>different_annot_all_killed N NUE L L'\<close> and
    \<open>different_annot_all_killed N' NUE' L' L''\<close>
    \<open>set_mset NUE \<subseteq> set_mset NUE'\<close> and
    \<open>reduce_dom_clauses N N'\<close> 
  shows
    \<open>different_annot_all_killed N' NUE' L L''\<close>
proof -
  show ?thesis
  using assms by (auto 5 5 simp: different_annot_all_killed.simps reduce_dom_clauses_def)
qed

lemma different_annots_all_killed_trans:
  assumes
    MM': \<open>different_annots_all_killed N NUE M M'\<close> and
    M'M'': \<open>different_annots_all_killed N' NUE' M' M''\<close> and
    \<open>set_mset NUE \<subseteq> set_mset NUE'\<close> and
    \<open>reduce_dom_clauses N N'\<close>
  shows
    \<open>different_annots_all_killed N' NUE' M M''\<close>
proof -
  have [simp]: \<open>length M = length M'\<close> \<open>length M' = length M''\<close>
    using MM' M'M'' by (auto simp: list_all2_conv_all_nth)
  show ?thesis
    apply (rule list_all2_all_nthI)
    subgoal using MM' M'M'' by (auto simp: list_all2_conv_all_nth)
    subgoal for n
      using list_all2_nthD[OF MM', of n]
      using list_all2_nthD[OF M'M'', of n]
      using different_annot_all_killed_trans[of N NUE \<open>M!n\<close> \<open>M'!n\<close> N' NUE' \<open>M''!n\<close>] assms(3-4)
      by auto
    done
qed

lemma rtranclp_remove_all_watched_true_clause_different_annots_all_killed:
  assumes
    \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (get_trail_wl S) = 0\<close> and
    reasons_inv: \<open>reasons_invs_wl S\<close>
  shows \<open>different_annots_all_killed (get_clauses_wl S) (get_unit_clauses_wl T) (get_trail_wl S)
      (get_trail_wl T)\<close>
  using assms
proof (induction)
  case base
  then show ?case by (auto intro: different_annots_all_killed_refl)
next
  case (step T U) note st = this(1) and TU = this(2) and IH = this(3-) and
    lev0 = this(4) and reasons = this(5)

  obtain M N D NE UE W Q M' N' NE' UE' where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
    T: \<open>T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W)\<close>
    \<open>\<forall>C\<in>#mset `# (NE' + UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M\<close> and
    \<open>dom_m N' \<subseteq># dom_m N\<close> and
    \<open>map lit_of M = map lit_of M'\<close> and
    count_dec': \<open>count_decided M' = 0\<close> and
    init: \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    learned: \<open>learned_clss_lf N = learned_clss_lf N' + UE' \<and> reduce_dom_clauses N N'\<close>
    using rtranclp_remove_all_watched_true_clause_decomp_Ex[OF st lev0] by force
  have count_dec_T: \<open>count_decided (get_trail_wl T) = 0\<close>
    using count_dec' unfolding T by auto
  obtain TW' TQ' M'' N'' NE'' UE'' where
    T': \<open>T = (M', N', D, NE + mset `# NE', UE + mset `# UE', TQ', TW')\<close> and
    U: \<open>U = (M'', N'', D, NE + mset `# NE' + mset `# NE'', UE + mset `# UE' + mset `# UE'', TQ', TW')\<close> and
    \<open>\<forall>C\<in>#mset `# (NE'' + UE''). \<exists>L\<in>#C. get_level M' L = 0 \<and> L \<in> lits_of_l M'\<close> and
    \<open>dom_m N'' \<subseteq># dom_m N'\<close> and
    \<open>map lit_of M' = map lit_of M''\<close> and
    \<open>count_decided M'' = 0\<close> and
    init': \<open>init_clss_lf N' = init_clss_lf N'' + NE''\<close> and
    learned': \<open>learned_clss_lf N' = learned_clss_lf N'' + UE''\<close> and
    red: \<open>reduce_dom_clauses N' N''\<close>
    using remove_all_watched_true_clause_decomp_Ex[OF TU count_dec_T] unfolding T
    by (auto simp: T)

  have \<open>ran_mf N = init_clss_lf N'' + learned_clss_lf N'' + NE' + NE'' + UE' + UE''\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    unfolding init init'  unfolding learned  learned'
    apply (subst learned learned')+
    by auto
  have IH': \<open>different_annots_all_killed (get_clauses_wl S) (get_unit_clauses_wl T)
    (get_trail_wl S) (get_trail_wl T)\<close>
    using IH by auto
  moreover have \<open>different_annots_all_killed (get_clauses_wl U) (get_unit_clauses_wl U)
    (get_trail_wl T) (get_trail_wl U)\<close>
    apply (rule remove_all_watched_true_clause_different_annots_all_killed[OF TU])
    subgoal using count_dec' by (auto simp: T count_decided_0_iff)
    subgoal using st IH
      by (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
             full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
           intro: rtranclp_remove_one_watched_true_clause_reasons_invs_wl
             rtranclp_remove_all_watched_true_clause_reasons_invs_wl)
    done
  ultimately show ?case
    using red
    apply -
    apply (rule different_annots_all_killed_trans)
      apply assumption+
    by (auto simp: S T U
      intro: different_annots_all_killed_trans)
qed

lemma count_decided0_map_is_decided:
  \<open>count_decided M = 0 \<Longrightarrow> map is_decided M = replicate (length M) False\<close>
  by (induction M rule: ann_lit_list_induct)
    auto

lemma different_annots_all_killed_map_lit_of:
  \<open>different_annots_all_killed N' NUE M M' \<Longrightarrow> map lit_of M = map lit_of M'\<close>
  by (induction rule: list_all2_induct)
    (auto simp: different_annot_all_killed.simps)


lemma different_annots_all_killed_length:
  \<open>different_annots_all_killed N' NUE M M' \<Longrightarrow> length M = length M'\<close>
  by (rule list_all2_lengthD)

lemma different_annots_all_killed_in_annot_in_unit:
  assumes 
    annot: \<open>different_annots_all_killed N' NUE M M'\<close> and
    n_d: \<open>no_dup M\<close> and
    LE': \<open>Propagated L E' \<in> set M\<close> and
    L0: \<open>Propagated L 0 \<in> set M'\<close> and
    \<open>E' \<in># dom_m N'\<close> and
    \<open>0 < E'\<close>
  shows \<open>mset (N' \<propto> E') \<in># NUE\<close>
proof -
  obtain M1 M2 where M: \<open>M = M2 @ Propagated L E' # M1\<close>
    using LE'
    by (auto dest!: split_list
        simp: list_all2_append1 list_all2_Cons1 different_annot_all_killed.simps)
  define M2' where \<open>M2' \<equiv> take (length M2) M'\<close>
  define M1' where \<open>M1' \<equiv> drop (Suc (length M2)) M'\<close>
  have n_d': \<open>no_dup M'\<close>
    using different_annots_all_killed_map_lit_of[OF annot] n_d
    by (blast dest: map_lit_of_eq_no_dupD)

  have M': \<open>M' =M2' @ Propagated L 0 # M1'\<close>
    using n_d' split_list[OF L0] annot unfolding M2'_def M1'_def
    by (auto simp: M list_all2_append1 list_all2_Cons1 different_annot_all_killed.simps
        elim!: list_match_lel_lel)
  have [simp]: \<open>length M1' = length M1\<close> \<open>length M2' = length M2\<close>
    using different_annots_all_killed_length[OF annot]
    unfolding M1'_def M2'_def M
    by auto
  show ?thesis
    using annot  \<open>0 < E'\<close> \<open>E' \<in># dom_m N'\<close>
    apply (subst (asm) M)
    apply (subst (asm) M')
    by (auto simp: list_all2_append different_annot_all_killed.simps)
qed

(* lemma *)
   (* \<open>different_annots_all_killed N' NUE M M' \<Longrightarrow> set_mset (dom_m N') \<subseteq> set_mset (dom_m N) \<Longrightarrow>
      different_annots_all_killed N NUE M M'\<close>
  apply (induction rule: list_all2_induct)
  subgoal by auto
  subgoal for L L' M M'
    apply (auto simp: different_annot_all_killed.simps[of _ _ L L'])

thm different_annot_all_killed.simps[of _ _ L L'] *)
lemma
  assumes
    remove: \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and
    lev0: \<open>count_decided (get_trail_wl S) = 0\<close> and
    partial: \<open>partial_correct_watching S\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    all0: \<open>\<forall>L C. Propagated L C \<in> set (get_trail_wl T) \<longrightarrow> C = 0\<close> and 
    dom0: \<open>0 \<notin># dom_m (get_clauses_wl S)\<close> and
    reason: \<open>reasons_invs_wl S\<close>
  shows \<open>cdcl_twl_restart_wl_p S T\<close>
proof -
  from rtranclp_remove_all_watched_true_clause_decomp_Ex[OF remove lev0]
  obtain M N D NE UE W Q M' N' NE' UE' where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
    T: \<open>T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W)\<close> and
    NUE: \<open>\<forall>C\<in>#mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M\<close> and
    dom_mono: \<open>dom_m N' \<subseteq># dom_m N\<close> and
    lit_of_MM': \<open>map lit_of M = map lit_of M'\<close> and
    \<open>count_decided M' = 0\<close> and 
    init: \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and 
    learned: \<open>learned_clss_lf N = learned_clss_lf N' + UE'\<close> and
    lev0': \<open>count_decided M' = 0\<close> and
    red_NN': \<open>reduce_dom_clauses N N'\<close>
    by metis
  from rtranclp_remove_all_watched_true_clause_different_annots_all_killed[OF remove lev0 reason]
  have annot: \<open>different_annots_all_killed (get_clauses_wl T) (get_unit_clauses_wl T)
   (get_trail_wl S) (get_trail_wl T)\<close>
    .
  have [simp]: \<open>length M = length M'\<close>
    using arg_cong[OF lit_of_MM', of length] by auto
  have D: \<open>D = None\<close>
    using confl unfolding S by auto
  have red: \<open>valid_trail_reduction M M'\<close>
    apply (rule valid_trail_reduction.intros(2))
    using lit_of_MM' lev0 lev0' by (auto simp: count_decided0_map_is_decided S)

  show ?thesis
    unfolding S T D
    apply (rule cdcl_twl_restart_wl_p.intros)
    subgoal using red .
    subgoal using init .
    subgoal using learned by auto
    subgoal using NUE by (auto dest!: multi_member_split)
    subgoal using all0 unfolding T by auto
    subgoal using all0 annot red_NN' unfolding T
      apply (intro conjI impI allI)
     apply (auto simp: S) sorry
    subgoal using all0 unfolding T by auto
    subgoal using dom0 dom_mono by (auto simp: S)
    subgoal by auto
    subgoal using rtranclp_remove_all_watched_true_clause_partial_correct_watching[OF remove
      partial] unfolding T D .
    done
qed


definition (in -) extract_and_remove
  :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> ('v clauses_l \<times> 'v clause_l \<times> bool) nres\<close>
where
  \<open>extract_and_remove N j = do {
      ASSERT((j :: nat) \<in># dom_m (N :: 'v clauses_l));
      SPEC(\<lambda>(N' :: 'v clauses_l, C' :: 'v clause_l, b :: bool). N' = N(j \<hookrightarrow> []) \<and> C' = N\<propto>j \<and> b = irred N j)
    }\<close>

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