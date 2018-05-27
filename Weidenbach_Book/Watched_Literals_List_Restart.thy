theory Watched_Literals_List_Restart
  imports Watched_Literals_List Watched_Literals_Algorithm_Restart
begin

text \<open>
  Unlike most other refinements steps we have done, we don't try to produce here to refine our
  specification to our code:
  \<^item> It is not clear how to get closer to code we would like to have
  \<^item> Without reasonable idea on the code, there are too many paths to produce a useful refinement
    step (for example, if the we want to restart without changing the level, we probably don't
    want to restart. This is can be expressed more easily later).
\<close>

text \<open>
  This invariant abstract over the restart operation on the trail. There can be a backtracking on
  the trail and there can be a renumbering of the indexes.
\<close>
inductive valid_trail_reduction for M M' :: \<open>('v ,'c) ann_lits\<close> where
backtrack_red:
  \<open>valid_trail_reduction M M'\<close>
  if
    \<open>(Decided K # M'', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>map lit_of M'' = map lit_of M'\<close> and
    \<open>map is_decided M'' = map is_decided M'\<close> |
keep_red:
  \<open>valid_trail_reduction M M'\<close>
  if
    \<open>map lit_of M = map lit_of M'\<close> and
    \<open>map is_decided M = map is_decided M'\<close>

lemma valid_trail_reduction_simps: \<open>valid_trail_reduction M M' \<longleftrightarrow>
  ((\<exists>K M'' M2. (Decided K # M'', M2) \<in> set (get_all_ann_decomposition M) \<and>
     map lit_of M'' = map lit_of M' \<and> map is_decided M'' = map is_decided M' \<and>
    length M' = length M'') \<or>
   map lit_of M = map lit_of M' \<and> map is_decided M = map is_decided M' \<and> length M = length M')\<close>
 apply (auto simp: valid_trail_reduction.simps dest: arg_cong[of \<open>map lit_of _\<close> _ length])
 apply (force dest: arg_cong[of \<open>map lit_of _\<close> _ length])+
 done

lemma trail_changes_same_decomp:
  assumes
    M'_lit: \<open>map lit_of M' = map lit_of ysa @ L # map lit_of zsa\<close> and
    M'_dec: \<open>map is_decided M' = map is_decided ysa @ False # map is_decided zsa\<close>
  obtains C' M2 M1 where \<open>M' = M2 @ Propagated L C' # M1\<close> and
    \<open>map lit_of M2 = map lit_of ysa\<close>and
    \<open>map is_decided M2 = map is_decided ysa\<close> and
    \<open>map lit_of M1 = map lit_of zsa\<close> and
    \<open>map is_decided M1 = map is_decided zsa\<close>
proof -
  define M1 M2 K where \<open>M1 \<equiv> drop (Suc (length ysa)) M'\<close> and \<open>M2 \<equiv> take (length ysa) M'\<close> and
    \<open>K \<equiv> hd (drop (length ysa) M')\<close>
  have
    M': \<open>M' = M2 @ K # M1\<close>
    using arg_cong[OF M'_lit, of length] unfolding M1_def M2_def K_def
    by (simp add: Cons_nth_drop_Suc hd_drop_conv_nth)
  have [simp]:
    \<open>length M2 = length ysa\<close>
    \<open>length M1 = length zsa\<close>
    using arg_cong[OF M'_lit, of length] unfolding M1_def M2_def K_def by auto

  obtain C' where
    [simp]: \<open>K = Propagated L C'\<close>
    using M'_lit M'_dec unfolding M'
    by (cases K) auto

  show ?thesis
    using that[of M2 C' M1] M'_lit M'_dec unfolding M'
    by auto
qed

lemma
  assumes
    \<open>map lit_of M = map lit_of M'\<close> and
    \<open>map is_decided M = map is_decided M'\<close>
  shows
    trail_renumber_count_dec:
      \<open>count_decided M = count_decided M'\<close> and
    trail_renumber_get_level:
      \<open>get_level M L = get_level M' L\<close>
proof -
  have [dest]: \<open>count_decided M = count_decided M'\<close>
    if \<open>map is_decided M = map is_decided M'\<close> for M M'
    using that
    apply (induction M arbitrary: M' rule: ann_lit_list_induct)
    subgoal by auto
    subgoal for L M M'
      by (cases M')
        (auto simp: get_level_cons_if)
    subgoal for L C M M'
      by (cases M')
        (auto simp: get_level_cons_if)
    done
  then show \<open>count_decided M = count_decided M'\<close> using assms by blast
  show  \<open>get_level M L = get_level M' L\<close>
    using assms
    apply (induction M arbitrary: M' rule: ann_lit_list_induct)
    subgoal by auto
    subgoal for L M M'
      by (cases M'; cases \<open>hd M'\<close>)
        (auto simp: get_level_cons_if)
    subgoal for L C M M'
      by (cases M')
        (auto simp: get_level_cons_if)
    done
qed


lemma valid_trail_reduction_Propagated_inD:
  \<open>valid_trail_reduction M M' \<Longrightarrow> Propagated L C \<in> set M' \<Longrightarrow> \<exists>C'. Propagated L C' \<in> set M\<close>
  by (induction rule: valid_trail_reduction.induct)
    (force dest!: get_all_ann_decomposition_exists_prepend
      dest!: split_list[of \<open>Propagated L C\<close>] elim!: trail_changes_same_decomp)+

lemma valid_trail_reduction_Propagated_inD2:
  \<open>valid_trail_reduction M M' \<Longrightarrow> length M = length M' \<Longrightarrow> Propagated L C \<in> set M \<Longrightarrow> 
     \<exists>C'. Propagated L C' \<in> set M'\<close>
  apply (induction rule: valid_trail_reduction.induct)
  apply (auto dest!: get_all_ann_decomposition_exists_prepend
      dest!: split_list[of \<open>Propagated L C\<close>] elim!: trail_changes_same_decomp)+
    apply (metis add_Suc_right le_add2 length_Cons length_append length_map not_less_eq_eq)
  by (metis (no_types, lifting) in_set_conv_decomp trail_changes_same_decomp)

text \<open>
  Remarks about the predicate:
  \<^item> The cases \<^term>\<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow>
    E' \<noteq> 0 \<longrightarrow> P\<close> are already covered by the invariants (where \<^term>\<open>P\<close> means that there is
    clause which was already present before).
\<close>
inductive cdcl_twl_restart_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart_l (M, N, None, NE, UE, {#}, Q)
       (M', N', None, NE + mset `# NE', UE + mset `# UE', {#}, Q')\<close>
  if
    \<open>valid_trail_reduction M M'\<close> and
    \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    \<open>learned_clss_lf N' + UE' \<subseteq># learned_clss_lf N\<close> and
    \<open>\<forall>E\<in># (NE'+UE'). \<exists>L\<in>set E. L \<in> lits_of_l M \<and> get_level M L = 0\<close> and
    \<open>\<forall>L E E' . Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E > 0  \<longrightarrow> E' > 0 \<longrightarrow>
        E \<in># dom_m N' \<and> N' \<propto> E = N \<propto> E'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow> E' \<noteq> 0 \<longrightarrow>
       mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E' = 0 \<longrightarrow> E = 0\<close> and
    \<open>0 \<notin># dom_m N'\<close> and
    \<open>if length M = length M' then Q = Q' else Q' = {#}\<close>


context twl_restart
begin

lemma cdcl_twl_restart_l_list_invs:
  assumes
    \<open>cdcl_twl_restart_l S T\<close> and
    \<open>twl_list_invs S\<close>
  shows
    \<open>twl_list_invs T\<close>
  using assms
proof (induction rule: cdcl_twl_restart_l.induct)
  case (restart_trail M M' N N' NE' UE' NE UE Q Q') note red = this(1) and init = this(2) and
    learned = this(3) and NUE = this(4) and tr_ge0 = this(5) and tr_new0 = this(6) and
    tr_still0 = this(7) and dom0 = this(8) and QQ' = this(9) and list_invs = this(10)
  let ?S = \<open>(M, N, None, NE, UE, {#}, Q)\<close>
  let ?T = \<open>(M', N', None, NE + mset `# NE', UE + mset `# UE', {#}, Q')\<close>
  show ?case
    unfolding twl_list_invs_def
  proof (intro conjI impI allI ballI)
    fix C
    assume \<open>C \<in># clauses_to_update_l ?T\<close>
    then show \<open>C \<in># dom_m (get_clauses_l ?T)\<close>
      by simp
  next
    show \<open>0 \<notin># dom_m (get_clauses_l ?T)\<close>
      using dom0 by simp
  next
    fix L C
    assume LC: \<open>Propagated L C \<in> set (get_trail_l ?T)\<close> and C0: \<open>0 < C\<close>
    then obtain C' where LC': \<open>Propagated L C' \<in> set (get_trail_l ?S)\<close>
      using red by (auto dest!: valid_trail_reduction_Propagated_inD)
    moreover have C'0: \<open>C' \<noteq> 0\<close>
      apply (rule ccontr)
      using C0 tr_still0 LC LC'
      by (auto simp: twl_list_invs_def
        dest!: valid_trail_reduction_Propagated_inD)
    ultimately have C_dom: \<open>C \<in># dom_m (get_clauses_l ?T)\<close> and NCC': \<open>N' \<propto> C = N \<propto> C'\<close>
      using tr_ge0 C0 LC by auto
    show \<open>C \<in># dom_m (get_clauses_l ?T)\<close>
      using C_dom .

    have
      L_watched: \<open>L \<in> set (watched_l (get_clauses_l ?S \<propto> C'))\<close> and
      L_C'0: \<open>L = get_clauses_l ?S \<propto> C' ! 0\<close>
      using list_invs C'0 LC' unfolding twl_list_invs_def
      by auto
    show \<open>L \<in> set (watched_l (get_clauses_l ?T \<propto> C))\<close>
      using L_watched NCC' by simp

    show \<open>L = get_clauses_l ?T \<propto> C ! 0\<close>
      using L_C'0 NCC' by simp
  next
    show \<open>distinct_mset (clauses_to_update_l ?T)\<close>
      by auto
  qed
qed

lemma cdcl_twl_restart_l_cdcl_twl_restart:
  assumes ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close>
  shows \<open>SPEC (cdcl_twl_restart_l S) \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
         clauses_to_update_l S = {#}}
     (SPEC (cdcl_twl_restart T))\<close>
proof -
  have [simp]:  \<open>set (watched_l x) \<union> set (unwatched_l x) = set x\<close> for x
    by (metis append_take_drop_id set_append)
  have \<open>\<exists>T'. cdcl_twl_restart T T' \<and> (S', T') \<in> twl_st_l None\<close>
    if \<open>cdcl_twl_restart_l S S'\<close> for S'
    using that ST struct_invs
  proof (induction rule: cdcl_twl_restart_l.induct)
    case (restart_trail M M' N N' NE' UE' NE UE Q Q') note red = this(1) and init = this(2) and
      learned = this(3) and NUE = this(4) and tr_ge0 = this(5) and tr_new0 = this(6) and
      tr_still0 = this(7) and dom0 = this(8) and QQ' = this(9) and ST = this(10) and
      struct_invs = this(11)
    let ?T' = \<open>(drop (length M - length M') (get_trail T), twl_clause_of `# init_clss_lf N',
          twl_clause_of `# learned_clss_lf N', None, NE+mset `# NE', UE+mset `# UE', {#}, Q')\<close>
    have [intro]: \<open>Q \<noteq> Q' \<Longrightarrow> Q' = {#}\<close>
      using QQ' by (auto split: if_splits)
    obtain TM where
        T: \<open>T = (TM, twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N, None,
        NE, UE, {#}, Q)\<close> and
      M_TM: \<open>(M, TM) \<in> convert_lits_l N (NE+UE)\<close>
      using ST
      by (cases T) (auto simp: twl_st_l_def)
    have \<open>no_dup TM\<close>
      using struct_invs unfolding T twl_struct_invs_def
          local.cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (simp add: trail.simps)
    then have n_d: \<open>no_dup M\<close>
      using M_TM by auto
    have \<open>cdcl_twl_restart T ?T'\<close>
      using red
    proof (induction)
      case keep_red
      from arg_cong[OF this(1), of length] have [simp]: \<open>length M = length M'\<close> by simp
      have [simp]: \<open>Q = Q'\<close>
        using QQ' by simp
      have annot_in_clauses: \<open>\<forall>L E. Propagated L E \<in> set TM \<longrightarrow>
        E \<in># clauses
              (twl_clause_of `# init_clss_lf N +
                twl_clause_of `# learned_clss_lf N') +
              NE +
              UE +
              clauses (twl_clause_of `# UE')\<close>
      proof (intro allI impI conjI)
        fix L E
        assume \<open>Propagated L E \<in> set TM\<close>
        then obtain E' where LE'_M: \<open>Propagated L E' \<in> set M\<close> and
          E_E': \<open>convert_lit N (NE+UE) (Propagated L E') (Propagated L E)\<close>
          using in_convert_lits_lD[OF _ M_TM, of \<open>Propagated L E\<close>]
          by (auto simp: convert_lit.simps)
        then obtain E'' where LE''_M: \<open>Propagated L E'' \<in> set M'\<close>
          using valid_trail_reduction_Propagated_inD2[OF red, of L E'] by auto

        consider
          \<open>E' = 0\<close> and \<open>E'' = 0\<close> |
          \<open>E' > 0\<close> and \<open>E'' = 0\<close> and \<open>mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> |
          \<open>E' > 0\<close> and \<open>E'' > 0\<close> and \<open>E'' \<in># dom_m N'\<close> and \<open>N \<propto> E' = N' \<propto> E''\<close>
          using tr_ge0 tr_new0 tr_still0 LE'_M LE''_M E_E'
          by (cases \<open>E''>0\<close>; cases \<open>E' > 0\<close>) auto
        then show \<open>E \<in># clauses
              (twl_clause_of `# init_clss_lf N +
                twl_clause_of `# learned_clss_lf N') +
              NE +
              UE +
              clauses (twl_clause_of `# UE')\<close>
          apply cases
          subgoal
            using E_E'
            by (auto simp: mset_take_mset_drop_mset' convert_lit.simps)
          subgoal
            using E_E' init
            by (auto simp: mset_take_mset_drop_mset' convert_lit.simps)
          subgoal
            using E_E' init
            by (auto simp: mset_take_mset_drop_mset' convert_lit.simps)
          done
      qed
      have \<open>cdcl_twl_restart
        (TM, twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N, None,
          NE, UE, {#}, Q)
        (TM, twl_clause_of `# init_clss_lf N', twl_clause_of `# learned_clss_lf N', None,
          NE + clauses (twl_clause_of `# NE'), UE + clauses (twl_clause_of `# UE'), {#},
          Q)\<close> (is \<open>cdcl_twl_restart ?A ?B\<close>)
        apply (rule cdcl_twl_restart.restart_clauses)
        subgoal
          using learned by (auto dest: image_mset_subseteq_mono)
        subgoal unfolding init image_mset_union by auto
        subgoal using NUE M_TM by auto
        subgoal by (rule annot_in_clauses)
        done
      moreover have \<open>?A = T\<close>
        unfolding T by simp
      moreover have \<open>?B = ?T'\<close>
        by (auto simp: T mset_take_mset_drop_mset')
      ultimately show ?case
        by argo
    next
      case (backtrack_red K M2 M'') note decomp = this(1)
      have [simp]: \<open>length M2 = length M'\<close>
        using arg_cong[OF backtrack_red(2), of length] by simp
      have M_TM: \<open>(drop (length M - length M') M, drop (length M - length M') TM) \<in>
          convert_lits_l N (NE+UE)\<close>
        using M_TM unfolding convert_lits_l_def list_rel_def by auto
      have red: \<open>valid_trail_reduction (drop (length M - length M') M) M'\<close>
        using red backtrack_red by (auto simp: valid_trail_reduction.simps)
      have annot_in_clauses: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M - length M') TM) \<longrightarrow>
        E \<in># clauses
              (twl_clause_of `# init_clss_lf N +
                twl_clause_of `# learned_clss_lf N') +
              NE +
              UE +
              clauses (twl_clause_of `# UE')\<close>
      proof (intro allI impI conjI)
        fix L E
        assume \<open>Propagated L E \<in> set (drop (length M - length M') TM)\<close>
        then obtain E' where LE'_M: \<open>Propagated L E' \<in> set (drop (length M - length M') M)\<close> and
          E_E': \<open>convert_lit N (NE+UE) (Propagated L E') (Propagated L E)\<close>
          using in_convert_lits_lD[OF _ M_TM, of \<open>Propagated L E\<close>]
          by (auto simp: convert_lit.simps)
        then have \<open>Propagated L E' \<in> set M2\<close>
          using decomp by (auto dest!: get_all_ann_decomposition_exists_prepend)
        then obtain E'' where LE''_M: \<open>Propagated L E'' \<in> set M'\<close>
          using valid_trail_reduction_Propagated_inD2[OF red, of L E'] decomp
          by (auto dest!: get_all_ann_decomposition_exists_prepend)
        consider
          \<open>E' = 0\<close> and \<open>E'' = 0\<close> |
          \<open>E' > 0\<close> and \<open>E'' = 0\<close> and \<open>mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> |
          \<open>E' > 0\<close> and \<open>E'' > 0\<close> and \<open>E'' \<in># dom_m N'\<close> and \<open>N \<propto> E' = N' \<propto> E''\<close>
          using tr_ge0 tr_new0 tr_still0 LE'_M LE''_M E_E' decomp
          by (cases \<open>E''>0\<close>; cases \<open>E' > 0\<close>)
            (auto 5 5 dest!: get_all_ann_decomposition_exists_prepend
            simp: convert_lit.simps)
        then show \<open>E \<in># clauses
              (twl_clause_of `# init_clss_lf N +
                twl_clause_of `# learned_clss_lf N') +
              NE +
              UE +
              clauses (twl_clause_of `# UE')\<close>
          apply cases
          subgoal
            using E_E'
            by (auto simp: mset_take_mset_drop_mset' convert_lit.simps)
          subgoal
            using E_E' init
            by (auto simp: mset_take_mset_drop_mset' convert_lit.simps)
          subgoal
            using E_E' init
            by (auto simp: mset_take_mset_drop_mset' convert_lit.simps)
          done
      qed
      have lits_of_M2_M': \<open>lits_of_l M2 = lits_of_l M'\<close>
        using arg_cong[OF backtrack_red(2), of set] by (auto simp: lits_of_def)
      have lev_M2_M': \<open>get_level M2 L = get_level M' L\<close> for L
        using trail_renumber_get_level[OF backtrack_red(2-3)] by (auto simp: )
      have drop_M_M2: \<open>drop (length M - length M') M = M2\<close>
        using  backtrack_red(1) by auto
      have H: \<open>L \<in> lits_of_l (drop (length M - length M') TM) \<and>
          get_level (drop (length M - length M') TM) L = 0\<close>
        if \<open>L \<in> lits_of_l M \<and> get_level M L = 0\<close> for L
      proof -
        have \<open>L \<in> lits_of_l M2 \<and> get_level M2 L = 0\<close>
          using decomp that n_d
          by (auto dest!: get_all_ann_decomposition_exists_prepend
            dest: in_lits_of_l_defined_litD
            simp: get_level_append_if get_level_cons_if  split: if_splits)
        then show ?thesis
          using M_TM
          by (auto dest!: simp: drop_M_M2)
      qed

      have
        \<open>\<exists>M2. (Decided K # drop (length M - length M') TM, M2) \<in> set (get_all_ann_decomposition TM)\<close>
        using convert_lits_l_decomp_ex[OF decomp \<open>(M, TM) \<in> convert_lits_l N (NE + UE)\<close>]
          \<open>(M, TM) \<in> convert_lits_l N (NE + UE)\<close>
        by (simp add: convert_lits_l_imp_same_length)
      then obtain TM2 where decomp_TM:
          \<open>(Decided K # drop (length M - length M') TM, TM2) \<in> set (get_all_ann_decomposition TM)\<close>
          by blast
      have \<open>cdcl_twl_restart
        (TM, twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N, None,
          NE, UE, {#}, Q)
        (drop (length M - length M') TM, twl_clause_of `# init_clss_lf N',
          twl_clause_of `# learned_clss_lf N', None,
          NE + clauses (twl_clause_of `# NE'), UE + clauses (twl_clause_of `# UE'), {#},
          {#})\<close> (is \<open>cdcl_twl_restart ?A ?B\<close>)
        apply (rule cdcl_twl_restart.restart_trail)
        apply (rule decomp_TM)
        subgoal
          using learned by (auto dest: image_mset_subseteq_mono)
        subgoal unfolding init image_mset_union by auto
        subgoal using NUE M_TM H by fastforce
        subgoal by (rule annot_in_clauses)
        done
      moreover have \<open>?A = T\<close>
        unfolding T by auto
      moreover have \<open>?B = ?T'\<close>
        using QQ' decomp unfolding T by (auto simp: mset_take_mset_drop_mset')
      ultimately show ?case
        by argo
    qed
    moreover {
      have \<open>(M', drop (length M - length M') TM) \<in> convert_lits_l N' (NE + mset `# NE' + (UE + mset `# UE'))\<close>
      proof (rule convert_lits_lI)
        show \<open>length M' = length (drop (length M - length M') TM)\<close>
          using M_TM red by (auto simp: valid_trail_reduction.simps T
            dest: convert_lits_l_imp_same_length
            dest!: arg_cong[of \<open>map lit_of _\<close> _ length] get_all_ann_decomposition_exists_prepend)
        fix i
        assume i_M': \<open>i < length M'\<close>
        then have MM'_IM: \<open>length M - length M' + i < length M\<close>  \<open>length M - length M' + i < length TM\<close>
          using M_TM red by (auto simp: valid_trail_reduction.simps T
            dest: convert_lits_l_imp_same_length
            dest!: arg_cong[of \<open>map lit_of _\<close> _ length] get_all_ann_decomposition_exists_prepend)
        then have \<open>convert_lit N (NE + UE) (drop (length M - length M') M ! i)
            (drop (length M - length M') TM ! i)\<close>
          using M_TM list_all2_nthD[of \<open>convert_lit N (NE + UE)\<close> M TM \<open>length M - length M' + i\<close>] i_M'
          unfolding convert_lits_l_def list_rel_def p2rel_def
          by auto
        moreover
          have \<open>lit_of (drop (length M - length M') M!i) = lit_of (M'!i)\<close> and
            \<open>is_decided (drop (length M - length M') M!i) = is_decided (M'!i)\<close>
          using red i_M' MM'_IM
          by (auto 5 5 simp:valid_trail_reduction_simps nth_append
            dest: map_eq_nth_eq[of _ _ _ i]
            dest!: get_all_ann_decomposition_exists_prepend)
        moreover have \<open>M'!i \<in> set M'\<close>
          using i_M' by auto
        moreover have \<open>drop (length M - length M') M!i \<in> set M\<close>
          using MM'_IM by auto
        ultimately show \<open>convert_lit N' (NE + mset `# NE' + (UE + mset `# UE')) (M' ! i)
            (drop (length M - length M') TM ! i)\<close>
          using tr_new0 tr_still0 tr_ge0
          by (cases \<open>M'!i\<close>) (fastforce simp: convert_lit.simps)+
      qed
      then have \<open>((M', N', None, NE + mset `# NE', UE + mset `# UE', {#}, Q'), ?T')
        \<in> twl_st_l None\<close>
        using M_TM by (auto simp: twl_st_l_def T)
    }
    ultimately show ?case
      by fast
  qed
  moreover have \<open>cdcl_twl_restart_l S S' \<Longrightarrow> twl_list_invs S'\<close> for S'
    by (rule cdcl_twl_restart_l_list_invs) (use list_invs in fast)+
  moreover have \<open>cdcl_twl_restart_l S S' \<Longrightarrow> clauses_to_update_l S' = {#}\<close> for S'
    by (auto simp: cdcl_twl_restart_l.simps)
  ultimately show ?thesis
    by (blast intro!: RES_refine)
qed


definition (in -) get_learned_clss_l where
  \<open>get_learned_clss_l S = learned_clss_lf (get_clauses_l S)\<close>

definition restart_required_l :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_l S n = SPEC (\<lambda>b. b \<longrightarrow> size (get_learned_clss_l S) > f n)\<close>

definition restart_prog_l_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>restart_prog_l_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and> restart_prog_pre S'
      \<and> twl_list_invs S)\<close>

definition restart_prog_l :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_l \<times> nat) nres" where
  \<open>restart_prog_l S n brk = do {
     ASSERT(restart_prog_l_pre S);
     b \<leftarrow> restart_required_l S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_l S T);
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>

lemma (in -)[twl_st_l]:
  \<open>(S, S') \<in> twl_st_l None \<Longrightarrow> get_learned_clss S' = twl_clause_of `# (get_learned_clss_l S)\<close>
  by (auto simp: get_learned_clss_l_def twl_st_l_def)

lemma restart_required_l_restart_required:
  \<open>(uncurry restart_required_l, uncurry restart_required) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S} \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f
    \<langle>bool_rel\<rangle> nres_rel\<close>
  unfolding restart_required_l_def restart_required_def uncurry_def
  by (intro frefI nres_relI) (auto simp: twl_st_l_def get_learned_clss_l_def)


lemma restart_prog_l_restart_prog:
  \<open>(uncurry2 restart_prog_l, uncurry2 restart_prog) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}
        \<times>\<^sub>f  nat_rel  \<times>\<^sub>f  bool_rel \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}
        \<times>\<^sub>f nat_rel\<rangle> nres_rel\<close>
    unfolding restart_prog_l_def restart_prog_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      restart_required_l_restart_required[THEN fref_to_Down_curry]
      cdcl_twl_restart_l_cdcl_twl_restart)
    subgoal for Snb Snb'
     unfolding restart_prog_l_pre_def
     by (rule exI[of _ \<open>fst (fst (Snb'))\<close>]) simp
    subgoal by simp
    subgoal by simp -- \<open>If condition\<close>
    subgoal by simp
    subgoal by simp
    subgoal unfolding restart_prog_pre_def by meson
    subgoal by auto
    subgoal by auto
    done


definition cdcl_twl_stgy_restart_prog_l_inv where
  \<open>cdcl_twl_stgy_restart_prog_l_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> twl_st_l None \<and>
       (T, T') \<in> twl_st_l None \<and>
       cdcl_twl_stgy_restart_prog_inv S\<^sub>0' brk T' n \<and>
       clauses_to_update_l T  = {#} \<and>
       twl_list_invs T)\<close>

definition cdcl_twl_stgy_restart_prog_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_prog_l S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_prog_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_prog_l T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0, 0);
    RETURN T
  }\<close>

lemma cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_l, cdcl_twl_stgy_restart_prog) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_prog_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
      (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> brk = brk' \<and> n = n' \<and>
        clauses_to_update_l S = {#}}\<close>]
      unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
      restart_prog_l_restart_prog[THEN fref_to_Down_curry2])
  subgoal by simp
  subgoal for x y xa x' x1 x2 x1a x2a
    unfolding cdcl_twl_stgy_restart_prog_l_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd x')\<close> in exI)
    by auto
  subgoal by fast
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_inv_def
      cdcl_twl_stgy_restart_prog_l_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st)
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end


text \<open>
  The idea of the restart works the following:
  \<^enum> We backtrack to level 0. This simplifies further steps.
  \<^enum> We first move all clause annotating a literal to  \<^term>\<open>NE\<close> or \<^term>\<open>UE\<close>.
  \<^enum> Then, we move remaining clauses that are watching the some literal at level 0.
  \<^enum> Now we can safely deleting any remaining learned clauses.
  \<^enum> Once all that is done, we have to recalculate the watch lists (and can on the way GC the set of
    clauses).
\<close>

subsubsection \<open>Handle true clauses from the trail\<close>
watched_l (N\<propto>i))))\<close>

lemma (in -) in_set_mset_eq_in:
  \<open>i \<in> set A \<Longrightarrow> mset A = B \<Longrightarrow> i \<in># B\<close>
  by fastforce


text \<open>Our transformation will be chains of a weaker version of restarts, that don't update the
  watch lists and only keep partial correctness of it.
\<close>
inductive cdcl_twl_restart_l_p :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart_l_p (M, N, None, NE, UE, W, Q)
       (M', N', None, NE + mset `# NE', UE + mset `# UE', W', Q')\<close>
  if
    \<open>valid_trail_reduction M M'\<close> and
    \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    \<open>learned_clss_lf N' + UE' \<subseteq># learned_clss_lf N\<close> and
    \<open>\<forall>E\<in># (NE'+UE'). \<exists>L\<in>set E. L \<in> lits_of_l M \<and> get_level M L = 0\<close> and
    \<open>\<forall>L E E' . Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E > 0  \<longrightarrow> E' > 0 \<longrightarrow>
        E \<in># dom_m N' \<and> N' \<propto> E = N \<propto> E'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow> E' \<noteq> 0 \<longrightarrow>
       mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E' = 0 \<longrightarrow> E = 0\<close> and
    \<open>0 \<notin># dom_m N'\<close> and
    \<open>if length M = length M' then Q = Q' else Q' = {#}\<close>

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

lemma cdcl_twl_restart_l_p_cdcl_twl_restart_l_p_is_cdcl_twl_restart_l_p:
  assumes
    ST: \<open>cdcl_twl_restart_l_p S T\<close> and TU: \<open>cdcl_twl_restart_l_p T U\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>cdcl_twl_restart_l_p S U\<close>
  using assms
proof -
  obtain M M' N N' NE' UE' NE UE Q Q' W' W where
    S: \<open>S = (M, N, None, NE, UE, W, Q)\<close> and
    T: \<open>T = (M', N', None, NE + mset `# NE', UE + mset `# UE', W', Q')\<close> and
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
    QQ': \<open>if length M = length M' then Q = Q' else Q' = {#}\<close>
    using ST unfolding cdcl_twl_restart_l_p.simps
    apply -
    apply normalize_goal+
    by blast
  obtain M'' N'' NE'' UE'' Q'' W'' where
    U: \<open>U = (M'', N'', None, NE + mset `# NE' + mset `# NE'', UE + mset `# UE' + mset `# UE'', W'',
      Q'')\<close> and
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
    Q'Q'': \<open>if length M' = length M'' then Q' = Q'' else Q'' = {#}\<close>
    using TU unfolding cdcl_twl_restart_l_p.simps T apply -
    apply normalize_goal+
    by blast
  have U': \<open>U = (M'', N'', None, NE + mset `# (NE' + NE''), UE + mset `# (UE' + UE''), W'',
      Q'')\<close>
    unfolding U by simp
  show ?thesis
    unfolding S U'
    apply (rule cdcl_twl_restart_l_p.restart_trail)
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

lemma tranclp_cdcl_twl_restart_l_p_no_dup:
  assumes
    ST: \<open>cdcl_twl_restart_l_p\<^sup>*\<^sup>* S T\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>no_dup (get_trail_l T)\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal
    by (auto simp: cdcl_twl_restart_l_p.simps valid_trail_reduction_simps
      dest: map_lit_of_eq_no_dupD dest!: no_dup_appendD get_all_ann_decomposition_exists_prepend)
  done

lemma rtranclp_cdcl_twl_restart_l_p_cdcl_is_cdcl_twl_restart_l_p:
  assumes
    ST: \<open>cdcl_twl_restart_l_p\<^sup>+\<^sup>+ S T\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>cdcl_twl_restart_l_p S T\<close>
  using assms
  apply (induction rule: tranclp_induct)
  subgoal by auto
  subgoal
    using cdcl_twl_restart_l_p_cdcl_twl_restart_l_p_is_cdcl_twl_restart_l_p
    tranclp_cdcl_twl_restart_l_p_no_dup by blast
  done

paragraph \<open>Auxilary definition\<close>
text \<open>This definition states that the domain of the clauses is reduced, but the remaining clauses
  are not changed.
\<close>
definition reduce_dom_clauses where
  \<open>reduce_dom_clauses N N' \<longleftrightarrow>
     (\<forall>C. C \<in># dom_m N' \<longrightarrow> C \<in># dom_m N \<and> fmlookup N C = fmlookup N' C)\<close>

lemma reduce_dom_clauses_fdrop[simp]: \<open>reduce_dom_clauses N (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def dest: in_diffD multi_member_split
    distinct_mem_diff_mset)

lemma reduce_dom_clauses_refl[simp]: \<open>reduce_dom_clauses N N\<close>
  by (auto simp: reduce_dom_clauses_def)

lemma reduce_dom_clauses_trans:
  \<open>reduce_dom_clauses N N' \<Longrightarrow> reduce_dom_clauses N' N'a \<Longrightarrow> reduce_dom_clauses N N'a\<close>
  by (auto simp: reduce_dom_clauses_def)

definition valid_trail_reduction_eq where
  \<open>valid_trail_reduction_eq M M' \<longleftrightarrow> valid_trail_reduction M M' \<and> length M = length M'\<close>

lemma valid_trail_reduction_eq_alt_def:
  \<open>valid_trail_reduction_eq M M' \<longleftrightarrow> map lit_of M = map lit_of M' \<and>
      map is_decided M = map is_decided M'\<close>
    by (auto simp: valid_trail_reduction_eq_def valid_trail_reduction.simps
      dest!: get_all_ann_decomposition_exists_prepend
      dest: map_eq_imp_length_eq trail_renumber_get_level)

lemma valid_trail_reduction_change_annot:
   \<open>valid_trail_reduction (M @ Propagated L C # M')
              (M @ Propagated L 0 # M')\<close>
    by (auto simp: valid_trail_reduction_eq_def valid_trail_reduction.simps)

lemma valid_trail_reduction_eq_change_annot:
   \<open>valid_trail_reduction_eq (M @ Propagated L C # M')
              (M @ Propagated L 0 # M')\<close>
    by (auto simp: valid_trail_reduction_eq_def valid_trail_reduction.simps)

lemma valid_trail_reduction_refl: \<open>valid_trail_reduction M M\<close>
  by (auto simp: valid_trail_reduction.simps)

lemma valid_trail_reduction_eq_refl: \<open>valid_trail_reduction_eq M M\<close>
  by (auto simp: valid_trail_reduction_eq_def valid_trail_reduction_refl)

lemma valid_trail_reduction_eq_get_level:
  \<open>valid_trail_reduction_eq M M' \<Longrightarrow> get_level M = get_level M'\<close>
  by (intro ext)
    (auto simp: valid_trail_reduction_eq_def valid_trail_reduction.simps
      dest!: get_all_ann_decomposition_exists_prepend
      dest: map_eq_imp_length_eq trail_renumber_get_level)

lemma valid_trail_reduction_eq_lits_of_l:
  \<open>valid_trail_reduction_eq M M' \<Longrightarrow> lits_of_l M = lits_of_l M'\<close>
  apply (auto simp: valid_trail_reduction_eq_def valid_trail_reduction.simps
      dest!: get_all_ann_decomposition_exists_prepend
      dest: map_eq_imp_length_eq trail_renumber_get_level)
  apply (metis image_set lits_of_def)+
  done

lemma valid_trail_reduction_eq_trans:
  \<open>valid_trail_reduction_eq M M' \<Longrightarrow> valid_trail_reduction_eq M' M'' \<Longrightarrow>
    valid_trail_reduction_eq M M''\<close>
  unfolding valid_trail_reduction_eq_alt_def
  by auto

definition no_dup_reasons_invs_wl where
  \<open>no_dup_reasons_invs_wl S \<longleftrightarrow>
    (distinct_mset (mark_of `# filter_mset (\<lambda>C. is_proped C \<and> mark_of C > 0) (mset (get_trail_l S))))\<close>

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
  \<open>different_annots_all_killed N NUE M M\<close>
  by (auto intro!: list.rel_refl_strong simp: count_decided_0_iff is_decided_no_proped_iff)


paragraph \<open>Specification\<close>

text \<open>
  Once of the first thing we do, is removing clauses we know to be true. We do in two ways:
    \<^item> along the trail (at level 0); this makes sure that annotations are kept;
    \<^item> then along the watch list.

  This is obviously not complete but is fast by avoiding iterating over all clauses.
\<close>
inductive remove_one_annot_true_clause :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
remove_irred:
  \<open>remove_one_annot_true_clause (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L 0 # M', fmdrop C N, D, add_mset (mset (N\<propto>C)) NE, UE, Q, W)\<close>
if
  \<open>get_level (M @ Propagated L C # M') L = 0\<close> and
  \<open>C > 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>irred N C\<close> |
remove_red:
  \<open>remove_one_annot_true_clause (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L 0 # M', fmdrop C N, D, NE, add_mset (mset (N\<propto>C)) UE, Q, W)\<close>
if
  \<open>get_level (M @ Propagated L C # M') L = 0\<close> and
  \<open>C > 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>\<not>irred N C\<close>

lemma Ex_ex_eq_Ex: \<open>(\<exists>NE'. (\<exists>b. NE' = {#b#} \<and> P b NE') \<and> Q NE') \<longleftrightarrow>
   (\<exists>b. P b {#b#} \<and> Q {#b#})\<close>
   by auto

lemma remove_one_annot_true_clause_decomp:
  assumes
    \<open>remove_one_annot_true_clause S T\<close>
  obtains M N U D NE UE W Q M' N' U' NE' UE' W' Q' where
    \<open>\<exists>M N D NE UE W Q M' N' NE' UE'.
     S = (M, N, D, NE, UE, Q, W) \<and>
     T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<and>
    (\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
    dom_m N' \<subseteq># dom_m N \<and>
    valid_trail_reduction_eq M M' \<and>
    init_clss_lf N = init_clss_lf N' + NE' \<and>
    learned_clss_lf N = learned_clss_lf N' + UE' \<and>
    reduce_dom_clauses N N'\<close>
  using assms
  by (induction)
    (fastforce simp: conj_imp_eq_imp_imp singleton_eq_image_mset_iff
    valid_trail_reduction_eq_change_annot
     Ex_ex_eq_Ex
    dest: in_set_takeD[of _ 2])+

lemma remove_one_annot_true_clause_reduce_dom_clauses:
  assumes
    \<open>remove_one_annot_true_clause S T\<close>
  shows \<open>reduce_dom_clauses (get_clauses_l S) (get_clauses_l T)\<close>
  using assms
  by (induction)
    (fastforce simp: conj_imp_eq_imp_imp singleton_eq_image_mset_iff
    valid_trail_reduction_eq_change_annot
     Ex_ex_eq_Ex reasons_invs_wl_def
    dest: in_set_takeD[of _ 2])+

lemma rtranclp_remove_one_annot_true_clause_reduce_dom_clauses:
  assumes
    \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close>
  shows \<open>reduce_dom_clauses (get_clauses_l S) (get_clauses_l T)\<close>
  using assms
  apply (induction)
  subgoal by (auto simp: )
  subgoal by (auto intro: reduce_dom_clauses_trans remove_one_annot_true_clause_reduce_dom_clauses)
  done

lemma remove_one_annot_true_clause_different_annots_all_killed:
  assumes \<open>remove_one_annot_true_clause S T\<close>
  shows \<open>different_annots_all_killed (get_clauses_l S) (get_unit_clauses_wl T)
          (get_trail_l S) (get_trail_l T)\<close>
proof -
  have [simp]: \<open>different_annot_all_killed N (add_mset (mset (N \<propto> C)) NE)
        (Propagated L C) (Propagated L 0)\<close> for N C L NE
    by (auto simp: different_annot_all_killed.simps)
  show ?thesis
    using assms
    by (induction rule: remove_one_annot_true_clause.induct)
      (auto simp: list_all2_append different_annots_all_killed_refl)
qed

lemma different_annot_all_killed_proped:
  \<open>different_annot_all_killed N NE z (Propagated L C) \<longleftrightarrow>
     (\<exists>C'.  z = Propagated L C' \<and> (C = C' \<or> (C' > 0 \<and> C = 0 \<and> (C' \<in># dom_m N \<longrightarrow>  mset (N\<propto>C') \<in># NE))))\<close>
  by (auto simp: different_annot_all_killed.simps)

lemma different_annots_all_killed_append_cons_decomp:
  \<open>different_annots_all_killed N NUE M (M2 @ Propagated L C # M1) \<longleftrightarrow>
     (\<exists>M2' M1' C'. different_annots_all_killed N (NUE) M2' M2 \<and>
      different_annots_all_killed N NUE M1' M1 \<and>
      different_annot_all_killed N NUE (Propagated L C') (Propagated L C) \<and>
      M = M2' @ Propagated L C' # M1' \<and>
     length M2' = length M2 \<and>
     length M1' = length M1)\<close>
  apply (auto simp: list_all2_append different_annots_all_killed_refl
      list_all2_Cons1 list_all2_Cons2 list_all2_append1 list_all2_append2)
   apply (rule_tac x=us in exI)
   apply auto
   apply (rule_tac x=zs in exI)
   apply (auto simp: different_annot_all_killed_proped)
     apply (rule_tac x=M2' in exI)
     apply (rule_tac x=\<open>Propagated L C # M1'\<close> in exI)
     apply (auto simp: )
    apply (rule_tac x=M2' in exI)
    apply (rule_tac x=\<open>Propagated L C' # M1'\<close> in exI)
    apply (auto simp: )
   apply (rule_tac x=M2' in exI)
   apply (rule_tac x=\<open>Propagated L C' # M1'\<close> in exI)
   apply (auto simp: )
  done

lemma different_annots_all_killed_add_mset_mono2:
  \<open>different_annots_all_killed N NE M M' \<Longrightarrow> different_annots_all_killed N (add_mset C NE) M M'\<close>
  by (induction rule: list_all2_induct)
    (auto simp: different_annot_all_killed.simps)

lemma remove_one_annot_true_clause_different_annots_all_killed2:
  assumes \<open>remove_one_annot_true_clause S T\<close> and
      \<open>different_annots_all_killed N (get_unit_clauses_wl S) M (get_trail_l S)\<close> and
      \<open>reduce_dom_clauses N (get_clauses_l S)\<close>
  shows \<open>different_annots_all_killed N (get_unit_clauses_wl T)
          M (get_trail_l T)\<close>
proof -
  have [simp]: \<open>different_annot_all_killed N (add_mset (mset (N \<propto> C)) NE)
        (Propagated L C) (Propagated L 0)\<close> for N C L NE
    by (auto simp: different_annot_all_killed.simps)
  show ?thesis
    using assms
    apply (induction rule: remove_one_annot_true_clause.induct)
     apply (auto simp: list_all2_append different_annots_all_killed_refl
        different_annots_all_killed_append_cons_decomp)
     apply (subst (asm) different_annots_all_killed_append_cons_decomp)
     apply (auto simp: list_all2_append different_annot_all_killed.simps
      different_annots_all_killed_add_mset_mono2
      reduce_dom_clauses_def)[]
     apply (subst (asm) different_annots_all_killed_append_cons_decomp)
     apply (auto simp: list_all2_append different_annot_all_killed.simps
      different_annots_all_killed_add_mset_mono2
      reduce_dom_clauses_def)[]
    done
qed

lemma rtranclp_remove_one_annot_true_clause_different_annots_all_killed:
  assumes \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close> and
      \<open>different_annots_all_killed N (get_unit_clauses_wl S) M (get_trail_l S)\<close> and
      \<open>reduce_dom_clauses N (get_clauses_l S)\<close>
  shows \<open>different_annots_all_killed N (get_unit_clauses_wl T)
          M (get_trail_l T)\<close>
  using assms
  apply induction
  subgoal by auto
  subgoal premises p for T U
    using p p(2) apply -
    by (drule remove_one_annot_true_clause_different_annots_all_killed2)
      (auto simp: different_annots_all_killed_refl
        rtranclp_remove_one_annot_true_clause_reduce_dom_clauses
      intro: remove_one_annot_true_clause_different_annots_all_killed2
      reduce_dom_clauses_trans[of _ \<open>get_clauses_l S\<close>])
  done

lemma  no_dup_reasons_invs_wl_repetition:
 \<open>C > 0 \<Longrightarrow>
  \<not>no_dup_reasons_invs_wl (M @ Propagated L C # c21' @ Propagated La C # M1, N, D, NE, UE, Q, W)\<close>
  unfolding no_dup_reasons_invs_wl_def
  by force

lemma  no_dup_reasons_invs_wl_repetition_delone:
 \<open>no_dup_reasons_invs_wl (M @ Propagated L C # c21' @ Propagated La C' # M1, N, D, NE, UE, Q, W) \<Longrightarrow>
  no_dup_reasons_invs_wl (M @ Propagated L 0 # c21' @ Propagated La C' # M1, N', D', NE', UE', Q', W')\<close>
  unfolding no_dup_reasons_invs_wl_def
  by (auto split: if_splits)

lemma  no_dup_reasons_invs_wl_repetition_delone':
 \<open>no_dup_reasons_invs_wl (M @ Propagated L C # c21' @ Propagated La C' # M1, N, D, NE, UE, Q, W) \<Longrightarrow>
  no_dup_reasons_invs_wl (M @ Propagated L C # c21' @ Propagated La 0 # M1, N', D', NE', UE', Q', W')\<close>
  unfolding no_dup_reasons_invs_wl_def
  by (auto split: if_splits)


lemma remove_one_annot_true_clause_reasons_invs_wl:
  \<open>remove_one_annot_true_clause S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  apply (induction rule: remove_one_annot_true_clause.induct)
  subgoal for M L C M' N D NE UE Q W
   apply (auto 5 5 simp: cdcl_twl_restart_l_p.simps singleton_eq_image_mset_iff
     distinct_mset_remove1_All reasons_invs_wl_def no_dup_reasons_invs_wl_repetition
     no_dup_reasons_invs_wl_repetition_delone
    elim!: list_match_lel_lel)
    apply (metis append_Cons append_assoc)
    apply (metis append_Cons append_assoc)
    apply (metis append_Cons append_assoc)
    apply (rule no_dup_reasons_invs_wl_repetition_delone'[of _ _ _ _ _ C _ N D NE UE Q W])
    using append_Cons append_assoc apply blast
    done
  subgoal for M L C M' N D NE UE Q W
   apply (auto 5 5 simp: cdcl_twl_restart_l_p.simps singleton_eq_image_mset_iff
     distinct_mset_remove1_All reasons_invs_wl_def no_dup_reasons_invs_wl_repetition
     no_dup_reasons_invs_wl_repetition_delone
    elim!: list_match_lel_lel)
    apply (metis append_Cons append_assoc)
    apply (metis append_Cons append_assoc)
    apply (metis append_Cons append_assoc)
    apply (rule no_dup_reasons_invs_wl_repetition_delone'[of _ _ _ _ _ C _ N D NE UE Q W])
    using append_Cons append_assoc apply blast
    done
  done

lemma rtranclp_remove_one_annot_true_clause_reasons_invs_wl:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal by (auto intro: remove_one_annot_true_clause_reasons_invs_wl)
  done

lemma rtranclp_remove_one_annot_true_clause_decomp_Ex:
  assumes \<open>(remove_one_annot_true_clause)\<^sup>*\<^sup>* S T\<close> and
    \<open>reasons_invs_wl S\<close>
  shows
    \<open>\<exists>M N D NE UE W Q M' N' NE' UE'. S = (M, N, D, NE, UE, Q, W) \<and>
     T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W) \<and>
     (\<forall>C\<in># mset `# (NE'+UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
     dom_m N' \<subseteq># dom_m N \<and> valid_trail_reduction_eq M M'  \<and>
    init_clss_lf N = init_clss_lf N' + NE' \<and>
    learned_clss_lf N = learned_clss_lf N' + UE' \<and>
    reduce_dom_clauses N N'\<close>
  using assms
  apply (induction)
  subgoal
    by (cases S) (auto simp: singleton_eq_image_mset_iff valid_trail_reduction_eq_refl)
  subgoal for T U
    by (drule remove_one_annot_true_clause_decomp)
      (auto simp: image_mset_union[symmetric] ac_simps simp del: image_mset_union
        simp: rtranclp_remove_one_annot_true_clause_reasons_invs_wl
        valid_trail_reduction_eq_get_level valid_trail_reduction_eq_lits_of_l
        intro: reduce_dom_clauses_trans valid_trail_reduction_eq_trans
        dest: multi_member_split)
  done

lemma valid_trail_reduction_eqD:
  \<open>valid_trail_reduction_eq M M' \<Longrightarrow> valid_trail_reduction M M'\<close>
  by (auto simp: valid_trail_reduction_eq_def)

lemma different_annots_all_killed_inD:
  \<open>different_annots_all_killed N NUE M M' \<Longrightarrow> no_dup M \<Longrightarrow>
           Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow>
     different_annot_all_killed N NUE (Propagated L E) (Propagated L E')\<close>
  by (auto dest!: split_list[of _ M']
      simp: list_all2_append2 list_all2_Cons2 different_annot_all_killed_proped
      defined_lit_def)

lemma remove_one_annot_true_clause_partial_correct_watching:
  assumes
    rem: \<open>remove_one_annot_true_clause S T\<close> and
    \<open>partial_correct_watching S\<close>
  shows \<open>partial_correct_watching T\<close>
proof -
  have H: \<open>set_mset (all_lits_of_mm (add_mset (mset C) (mset `# remove1_mset C (ran_mf N) + NE + UE)))
     = set_mset (all_lits_of_mm (mset `# (ran_mf N) + NE + UE))\<close>
    if C: \<open>C \<in># ran_mf N\<close> for C N NE UE
  proof -
    obtain A where A: \<open>ran_mf N =add_mset C A\<close>
      using multi_member_split[OF C] by blast
    show ?thesis
      unfolding A by (auto dest!:  simp: all_lits_of_mm_add_mset)
  qed
  have H': \<open>C \<in># dom_m N \<Longrightarrow> N \<propto> C \<in># ran_mf N\<close> for N C
    by (auto dest: multi_member_split simp: ran_m_def)
  show ?thesis
    using assms
    apply (induction)
    subgoal for M L C M' N D NE UE Q W
      using distinct_mset_dom[of \<open>N\<close>]
      by (auto simp: partial_correct_watching.simps distinct_mset_remove1_All
          H[OF H'])
    subgoal for M L C M' N D NE UE Q W
      using distinct_mset_dom[of \<open>N\<close>]
      by (auto simp: partial_correct_watching.simps distinct_mset_remove1_All
          H[OF H'])
    done
qed

lemma rtranclp_remove_one_annot_true_clause_partial_correct_watching:
  assumes
    rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close> and
    \<open>partial_correct_watching S\<close>
  shows \<open>partial_correct_watching T\<close>
  using assms
  by (induction) (auto intro: remove_one_annot_true_clause_partial_correct_watching)

lemma remove_one_annot_true_clause_cdcl_twl_restart_l_p:
  assumes
    rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close> and
    reasons: \<open>reasons_invs_wl S\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    all0: \<open>\<forall>L C. Propagated L C \<in> set (get_trail_l T) \<longrightarrow> C = 0\<close> and
    before_valid: \<open>\<forall>L C. Propagated L C \<in> set (get_trail_l S) \<longrightarrow>
           0 < C \<longrightarrow> C \<in># dom_m (get_clauses_l S)\<close> and
    dom0: \<open>0 \<notin># dom_m (get_clauses_l S)\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close> and
    part: \<open>partial_correct_watching S\<close>
  shows \<open>cdcl_twl_restart_l_p S T\<close>
proof -
  obtain M N D NE UE W Q M' N' NE' UE' where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
    T: \<open>T = (M', N', D, NE + mset `# NE', UE + mset `# UE', Q, W)\<close> and
    NUE: \<open>\<forall>C\<in>#mset `# (NE' + UE'). \<exists>L\<in>#C. get_level M L = 0 \<and> L \<in> lits_of_l M\<close> and
    dom_m: \<open>dom_m N' \<subseteq># dom_m N\<close> and
    valid: \<open>valid_trail_reduction_eq M M'\<close> and
    init: \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    learned: \<open>learned_clss_lf N = learned_clss_lf N' + UE'\<close> and
    \<open>reduce_dom_clauses N N'\<close>
    using rtranclp_remove_one_annot_true_clause_decomp_Ex[OF rem reasons] by metis+
  have D: \<open>D = None\<close>
    using confl unfolding S by auto
  from rtranclp_remove_one_annot_true_clause_different_annots_all_killed[OF rem
      different_annots_all_killed_refl]
  have annots: \<open>different_annots_all_killed N (NE + mset `# NE' + UE + mset `# UE') M M'\<close>
    unfolding S T by (simp add: ac_simps)
  have part_T: \<open>partial_correct_watching T\<close>
    using rtranclp_remove_one_annot_true_clause_partial_correct_watching[OF rem] part .
  show ?thesis
    unfolding S T D
    apply (rule cdcl_twl_restart_l_p.intros)
    subgoal using valid_trail_reduction_eqD[OF valid] .
    subgoal using init .
    subgoal using learned by simp
    subgoal using NUE by (auto dest!: multi_member_split)
    subgoal using all0 by (auto simp: T)
    subgoal using n_d before_valid
      by (auto simp: S dest!: different_annots_all_killed_inD[OF annots]
          simp: different_annot_all_killed.simps reasons_invs_wl_def
          dest: split_list)
    subgoal using annots n_d
      by (auto simp: S dest!: different_annots_all_killed_inD
          simp: different_annot_all_killed.simps)
    subgoal using dom_m dom0 unfolding S by auto
    subgoal using valid unfolding valid_trail_reduction_eq_def by simp
    subgoal using part_T unfolding T D .
    done
qed

inductive remove_one_watched_true_clause :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
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

inductive remove_all_watched_true_clause :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>remove_all_watched_true_clause (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L C # M', N', D', NE', UE', Q', W')\<close>
if \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* (M @ Propagated L C # M', N, D, NE, UE, Q, W)
     (M @ Propagated L C # M', N', D', NE', UE', Q', W')\<close>

lemma remove_one_watched_true_clause_partial_correct_watching:
 assumes \<open>remove_one_watched_true_clause L S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>]
  by (induction)
    (auto simp: partial_correct_watching.simps image_mset_remove1_mset_if
  dest: multi_member_split)

lemma rtranclp_remove_one_watched_true_clause_partial_correct_watching:
 assumes \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>]
  by (induction)
    (auto simp: remove_one_watched_true_clause_partial_correct_watching)

lemma remove_one_watched_true_clause_different_annots_all_killed:
  assumes
    \<open>remove_one_watched_true_clause L S T\<close> and
    \<open>count_decided (get_trail_l S) = 0\<close>
  shows \<open>different_annots_all_killed (get_clauses_l S) (get_unit_clauses_wl S)(get_trail_l S) (get_trail_l T)\<close>
  using assms by (induction) (auto simp: different_annots_all_killed_refl)

lemma remove_one_watched_true_clause_trail:
  assumes
    \<open>remove_one_watched_true_clause L S T\<close> a
  shows \<open>get_trail_l S =  get_trail_l T\<close>
  using assms by (induction) (auto simp: different_annots_all_killed_refl)

lemma rtranclp_remove_one_watched_true_clause_trail:
  assumes
    \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T\<close> a
  shows \<open>get_trail_l S = get_trail_l T\<close>
  using assms by (induction) (auto simp: remove_one_watched_true_clause_trail)

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
    \<open>count_decided (get_trail_l S) = 0\<close>
  shows \<open>different_annots_all_killed (get_clauses_l S) (get_unit_clauses_wl S)
     (get_trail_l S) (get_trail_l T)\<close>
  using assms apply (induction)
  subgoal by (auto simp: remove_one_watched_true_clause_decomp different_annots_all_killed_refl)
  subgoal for T U
    apply (elim remove_one_watched_true_clause_decomp[of L T U])
    using remove_one_watched_true_clause_different_annots_all_killed[of L T U]
    by auto
  done


definition (in -) extract_and_remove
  :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> ('v clauses_l \<times> 'v clause_l \<times> bool) nres\<close>
where
  \<open>extract_and_remove N j = do {
      ASSERT((j :: nat) \<in># dom_m (N :: 'v clauses_l));
      SPEC(\<lambda>(N' :: 'v clauses_l, C' :: 'v clause_l, b :: bool). N' = fmdrop j N \<and> C' = N\<propto>j \<and> b = irred N j)
    }\<close>

definition (in -) replace_annot_in_trail_spec :: \<open>('v, nat) ann_lits \<Rightarrow> 'v literal \<Rightarrow>
    (('v, nat) ann_lits) nres\<close>
where
  \<open>replace_annot_in_trail_spec M L = do {
      ASSERT(L \<in> lits_of_l M);
      SPEC(\<lambda>M'. \<exists>M2 M1 C. M = M2 @ Propagated L C # M1 \<and> M' = M2 @ Propagated L 0 # M1)
    }\<close>


definition remove_one_annot_true_clause_one_imp
where
\<open>remove_one_annot_true_clause_one_imp = (\<lambda>(i, M, N, NE, UE). do {
      ASSERT(i < length M);
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). M!i = Propagated L C);
      if C = 0 then RETURN (i+1, M, N, NE, UE)
      else do {
        ASSERT(C \<in># dom_m N);
        M \<leftarrow> replace_annot_in_trail_spec M L;
        (N', C, b) \<leftarrow> extract_and_remove N C;
        if b then RETURN (i+1, M, N', add_mset (mset C) NE, UE)
        else RETURN (i+1, M, N', NE, add_mset (mset C) UE)
      }
  })\<close>


definition remove_one_annot_true_clause_imp
  :: \<open>nat twl_st_l \<Rightarrow> (nat twl_st_l) nres\<close>
where
\<open>remove_one_annot_true_clause_imp = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    (_, M, N, NE, UE) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, M, N, NE, UE). i < length M)
      (\<lambda>(i, M, N, NE, UE). remove_one_annot_true_clause_one_imp (i, M, N, NE, UE))
      (0, M, N, NE, UE);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

lemma remove_one_annot_true_clause_no_dup:
  \<open>remove_one_annot_true_clause S T \<Longrightarrow> no_dup (get_trail_l S) \<longleftrightarrow> no_dup (get_trail_l T)\<close>
  by (induction rule: remove_one_annot_true_clause.induct) auto
lemma rtranclp_remove_one_annot_true_clause_no_dup:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> no_dup (get_trail_l S) \<longleftrightarrow> no_dup (get_trail_l T)\<close>
  by (induction rule: rtranclp_induct) (auto simp: remove_one_annot_true_clause_no_dup)

lemma remove_one_annot_true_clause_count_decided:
  \<open>remove_one_annot_true_clause S T \<Longrightarrow> count_decided (get_trail_l S) = count_decided (get_trail_l T)\<close>
  by (induction rule: remove_one_annot_true_clause.induct) auto
lemma rtranclp_remove_one_annot_true_clause_count_decided:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> count_decided (get_trail_l S) = count_decided (get_trail_l T)\<close>
  by (induction rule: rtranclp_induct) (auto simp: remove_one_annot_true_clause_count_decided)

lemma
  assumes
    n_d: \<open>no_dup (get_trail_l S)\<close> and
    reasons: \<open>reasons_invs_wl S\<close> and
    count_dec: \<open>count_decided (get_trail_l S) = 0\<close>
  shows
    \<open>remove_one_annot_true_clause_imp S \<le> \<Down> Id (SPEC(\<lambda>T. remove_one_annot_true_clause\<^sup>*\<^sup>* S T))\<close>
proof -
  obtain M N D NE UE Q W where S:\<open>S = (M, N, D, NE, UE, Q, W)\<close>
    by (cases S) auto
  define I where
    \<open>I \<equiv> \<lambda>(i, M', N', NE', UE').
      remove_one_annot_true_clause\<^sup>*\<^sup>* (M, N, D, NE, UE, Q, W) (M', N', D, NE', UE', Q, W) \<and>
      length M = length M' \<and> i \<le> length M \<and>
        (\<forall>j < i. mark_of (M'!j) = 0) \<and>
        reasons_invs_wl (M', N', D, NE', UE', Q, W)\<close>
  have I0: \<open>I (0, M, N, NE, UE)\<close>
    using reasons unfolding I_def S by auto
  have \<open>remove_one_annot_true_clause_one_imp (i, M'', NE'', UE'', sUE)
      \<le> SPEC (\<lambda>s'. I s' \<and> (s', s) \<in> measure (\<lambda>(i, _). length M - i))\<close>
    if 
      \<open>(M, N, D, NE, UE, Q, W) = (M', SM)\<close> and
      \<open>SM = (N', SN')\<close> and
      \<open>SN' = (D', SD)\<close> and
      \<open>SD = (NE', SNE)\<close> and
      \<open>SNE = (UE', SUE)\<close> and
      \<open>SUE = (Q', W')\<close> and
      I: \<open>I s\<close> and
      i_le: \<open>case s of (i, M, N, NE, UE) \<Rightarrow> i < length M\<close> and
      s: \<open>s = (i, si)\<close> \<open>si = (M'', sm)\<close> \<open>sm = (NE'', sNE)\<close> \<open>sNE = (UE'', sUE)\<close>
    for M' SM N' SN' D' SD NE' SNE UE' SUE Q' W' s i si M'' sm NE'' sNE UE'' sUE
  proof -
    have \<open>i < length M''\<close>
      using i_le unfolding s by auto
    have
      reasons: \<open>reasons_invs_wl (M'', NE'', D, UE'', sUE, Q, W)\<close> and
      [simp]: \<open>length M = length M''\<close> and
      rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* (M, N, D, NE, UE, Q, W)
         (M'', NE'', D, UE'', sUE, Q, W)\<close> and
      all0: \<open>\<And>j. j<i \<Longrightarrow> mark_of (M'' ! j) = 0\<close> and
      reasons': \<open>reasons_invs_wl (M'', NE'', D, UE'', sUE, Q, W)\<close>
      using I unfolding s I_def prod.simps by fast+
    have I_next0: \<open> I (Suc i, M'', NE'', UE'', sUE)\<close> if \<open>M'' ! i = Propagated L 0\<close> for L
      using I that  \<open>i < length M''\<close> unfolding I_def s by (auto simp: less_Suc_eq)
    have C_dom: \<open>C \<in># dom_m NE''\<close> and
      L_lits: \<open>L \<in> lits_of_l M''\<close>
      if \<open>M'' ! i = Propagated L C \<close> and C0: \<open>C > 0\<close> for L C
    proof -
      have LC: \<open>Propagated L C \<in> set M''\<close>
        using that(1)[symmetric]  \<open>i < length M''\<close> by auto
      then show \<open>C \<in># dom_m NE''\<close>
        using reasons C0 unfolding reasons_invs_wl_def
        by (auto dest!: split_list)
      show \<open>L \<in> lits_of_l M''\<close>
        using LC
        by (auto dest!: split_list)
    qed
    have \<open>I (i + 1, M', N', add_mset (mset C') UE'', sUE)\<close>
      if 
        \<open>i < length M''\<close> and
        LC_i: \<open>case LC of (L, C) \<Rightarrow> M'' ! i = Propagated L C\<close> and
        LC: \<open>LC = (L, C)\<close> and
        \<open>C \<noteq> 0\<close> and
        \<open>C \<in># dom_m NE''\<close> and
        \<open>L \<in> lits_of_l M''\<close> and
        renum: \<open>\<exists>M2 M1 C.
            M'' = M2 @ Propagated L C # M1 \<and> M' = M2 @ Propagated L 0 # M1\<close> and
        NCb': \<open>case NCb of (N', C', b) \<Rightarrow> N' = fmdrop C NE'' \<and> C' = NE'' \<propto> C \<and> b = irred NE'' C\<close> and
        NCb: \<open>NCb = (N', sCb)\<close> \<open>sCb = (C', b')\<close> and
        \<open>b'\<close>
      for LC L C M' NCb N' sCb C' b'
    proof -
      obtain M2 M1 E where
        M'': \<open>M'' = M2 @ Propagated L E # M1\<close> and
        M': \<open>M' = M2 @ Propagated L 0 # M1\<close>
        using renum by blast
      have n_d'': \<open>no_dup M''\<close>
        using rtranclp_remove_one_annot_true_clause_no_dup[OF rem] n_d unfolding S by auto
      moreover have LC_M'': \<open>Propagated L C \<in> set M''\<close>
        using LC_i nth_mem[of i \<open>M''\<close>] \<open>i < length M''\<close>
        unfolding LC 
        by auto
      ultimately have E: \<open>E = C\<close>
        using LC_i \<open>i < length M''\<close> unfolding LC S M' M''
        by (auto dest!: split_list simp: nth_append simp del: \<open>i < length M''\<close>
          split: if_splits)
      have i: \<open>i = length M2\<close>
        using LC_i n_d'' \<open>i < length M''\<close> unfolding LC prod.case M'' S E
        apply (auto simp: nth_append nth_Cons split: if_splits)
        using defined_lit_def nth_mem apply fastforce 
        by (metis E M'' all0 annotated_lit.sel(3) linorder_neqE_nat nth_append_length that(4))
      have
        N': \<open>N' = fmdrop C NE''\<close> and
        C': \<open>C' = NE'' \<propto> C\<close> and
        irred: \<open>irred NE'' C\<close>
        using NCb' \<open>b'\<close> unfolding NCb prod.case
        by simp_all
      have count_dec': \<open>count_decided M'' = 0\<close>
        using rtranclp_remove_one_annot_true_clause_count_decided[OF rem]
        count_dec unfolding S by simp
      have all0': \<open>j<i + 1 \<Longrightarrow> mark_of ((M2 @ Propagated L 0 # M1) ! j) = 0\<close> for j
         using all0[of j]  \<open>i < length M''\<close> i
         by (auto simp: nth_append M'' less_Suc_eq split: if_splits)
      have \<open>reasons_invs_wl (M2 @ Propagated L 0 # M1, N', D, add_mset (mset C') UE'', sUE, Q, W)\<close>
        using reasons' apply (auto 5 5 simp: reasons_invs_wl_def M'' E N'
          no_dup_reasons_invs_wl_def
          elim!: list_match_lel_lel)
        unfolding  append_Cons[symmetric] append_assoc[symmetric]
        supply append_Cons[simp del] append_assoc[simp del]
        apply blast
        apply blast
        apply blast
        sorry
      have \<open>remove_one_annot_true_clause (M'', NE'', D, UE'', sUE, Q, W)
        (M2 @ Propagated L 0 # M1, N', D, add_mset (mset C') UE'', sUE, Q, W)\<close>
        unfolding M'' C' N' E
        apply (rule remove_one_annot_true_clause.intros(1))
        subgoal using count_decided_ge_get_level[of M'' L] count_dec' unfolding M''  E by simp
        subgoal using \<open>C \<noteq> 0\<close> by simp
        subgoal using  \<open>C \<in># dom_m NE''\<close> .
        subgoal using irred .
        done
      then have rem': \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* (M, N, D, NE, UE, Q, W)
          (M2 @ Propagated L 0 # M1, N', D, add_mset (mset C') UE'', sUE, Q, W)\<close> 
        using rem unfolding M'' E by simp
      show ?thesis
        using rem' all0' \<open>i < length M''\<close>
        unfolding I_def NCb M' M'' prod.case
        apply (intro conjI)
        apply (auto simp: M'' )
       sorry
    qed
    show ?thesis
      unfolding remove_one_annot_true_clause_one_imp_def replace_annot_in_trail_spec_def
      extract_and_remove_def s prod.case
      apply (refine_vcg)
      subgoal by simp
      subgoal for LC L C by (auto intro: I_next0)
      subgoal by (auto simp: diff_less_mono2)
      subgoal by (auto intro: C_dom)
      subgoal by (auto intro: L_lits)
      subgoal for LC L C'' M' NCb N' sCb C' b'
        explore_have
       apply auto
       sorry
      subgoal by (auto simp: diff_less_mono2)
      subgoal for LC L C
      
       apply auto
       sorry
      subgoal by (auto simp: diff_less_mono2)
      done
  qed
  show ?thesis
    unfolding S remove_one_annot_true_clause_imp_def
    apply (refine_vcg
      WHILET_rule[where I = I and R=\<open>measure(\<lambda>(i, _). length M - i)\<close>])
    subgoal by auto
    subgoal using I0 by auto
    subgoal for M' SM N' SN' D' SD NE' SNE UE' SUE Q' W' s i si M'' sm NE'' sNE UE'' sUE
      unfolding remove_one_annot_true_clause_one_imp_def replace_annot_in_trail_spec_def
      extract_and_remove_def
      apply (auto simp: assert_bind_spec_conv intro_spec_iff)
    by auto
    subgoal unfolding I_def by fast
  oops

  find_theorems " RES _ >>= (\<lambda>_.  _) <= _"
lemma remove_all_watched_true_clause_partial_correct_watching:
 assumes \<open>remove_all_watched_true_clause S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>]
  apply (induction)
  by (auto dest!: rtranclp_remove_one_watched_true_clause_partial_correct_watching
    simp: full_def)
    (auto simp: partial_correct_watching.simps)


lemma no_step_remove_one_watched_true_clause_different_annot_all_killed:
  fixes S :: \<open>'v twl_st_l\<close>
  assumes
    \<open>no_step (remove_one_watched_true_clause L) S\<close> and
    count_dec: \<open>count_decided (get_trail_l S) = 0\<close> and
    L: \<open>Propagated L C \<in> set (get_trail_l S)\<close> and
    \<open>reasons_invs_wl S\<close>
  shows \<open>different_annot_all_killed (get_clauses_l S) (get_unit_clauses_wl S)
     (Propagated L C) (Propagated L (0 :: nat))\<close>
  using assms count_decided_ge_get_level[of \<open>get_trail_l S\<close> L]
  by (cases S)
   (auto 5 5 simp: different_annot_all_killed.simps remove_one_watched_true_clause.simps
    all_conj_distrib reasons_invs_wl_def
    dest!: multi_member_split split_list[of \<open>Propagated L C\<close>])

lemma remove_one_watched_true_clause_reasons_invs_wl:
  \<open>remove_one_watched_true_clause L S T \<Longrightarrow> reasons_invs_wl_p L S \<Longrightarrow> reasons_invs_wl_p L T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  by (induction rule: remove_one_watched_true_clause.induct)
    (auto simp: reasons_invs_wl_p_def dest: multi_member_split)

lemma rtranclp_remove_one_watched_true_clause_reasons_invs_wl:
  \<open>(remove_one_watched_true_clause L)\<^sup>*\<^sup>* S T \<Longrightarrow> reasons_invs_wl_p L S \<Longrightarrow> reasons_invs_wl_p L T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  by (induction rule: rtranclp_induct)
    (auto simp: remove_one_watched_true_clause_reasons_invs_wl)

lemma reasons_invs_wl_change_annot:
  \<open>no_dup (M @ Propagated L C # M') \<Longrightarrow>
     reasons_invs_wl_p L (M @ Propagated L C # M', N', D', NE', UE', Q', W') \<Longrightarrow>
       reasons_invs_wl (M @ Propagated L 0 # M', N', D', NE', UE', Q', W')\<close>
  apply (auto 5 5 simp: reasons_invs_wl_def
    simp del: append_assoc append_Cons
    simp: append_assoc[symmetric] append_Cons[symmetric] reasons_invs_wl_p_def
    elim!: list_match_lel_lel)
  apply (auto 5 5 simp: reasons_invs_wl_def
    elim!: list_match_lel_lel)
  done

lemma remove_all_watched_true_clause_reasons_invs_wl:
  \<open>remove_all_watched_true_clause S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  by (induction rule: remove_all_watched_true_clause.induct)
    (auto simp: full_def
        dest!: rtranclp_remove_one_watched_true_clause_reasons_invs_wl
       dest: multi_member_split reasons_invs_wl_change_annot)

lemma rtranclp_remove_all_watched_true_clause_reasons_invs_wl:
  \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> reasons_invs_wl S \<Longrightarrow> reasons_invs_wl T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  by (induction rule: rtranclp_induct)
    (auto simp: remove_all_watched_true_clause_reasons_invs_wl)

lemma dom_m_empty_iff: \<open>dom_m N' = {#} \<longleftrightarrow> N' = fmempty\<close>
  by (cases N') auto

lemma reduce_dom_clauses_empty_left: \<open>reduce_dom_clauses fmempty N' \<longleftrightarrow> N' = fmempty\<close>
  by (auto simp: reduce_dom_clauses_def dom_m_empty_iff)

lemma reduce_dom_clauses_empty_right[simp]: \<open>reduce_dom_clauses N' fmempty\<close>
  by (auto simp: reduce_dom_clauses_def)

lemma reduce_dom_clauses_fmupd_notin:
  \<open>x \<notin># dom_m N' \<Longrightarrow> reduce_dom_clauses N (fmupd x C N') \<longleftrightarrow>
   reduce_dom_clauses N N' \<and> x \<in># dom_m N \<and> fmlookup N x = Some C\<close>
  by (auto simp: reduce_dom_clauses_def)

lemma reduce_dom_clauses_fmdrop_notin:
   \<open>reduce_dom_clauses N' N \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> reduce_dom_clauses (fmdrop i N') N\<close>
  by (auto simp: reduce_dom_clauses_def)

lemma setset_mset_add_msetD: \<open>a \<subseteq># b \<Longrightarrow> add_mset x a \<subseteq># add_mset x b\<close>
  by (auto simp: ac_simps)

lemma reduce_dom_clauses_ran_mf_subset: \<open>reduce_dom_clauses N N' \<Longrightarrow> ran_mf N' \<subseteq># ran_mf N\<close>
  apply (induction N' arbitrary: N)
  subgoal by auto
  subgoal premises p for i C N N'
    using p(1)[of \<open>fmdrop i N'\<close>] p(2-)
     setset_mset_add_msetD[of \<open>ran_mf N\<close> \<open>remove1_mset (fst C) (ran_mf N')\<close> \<open>fst C\<close>,
      unfolded add_mset_remove_trivial_If]
    apply (auto simp: reduce_dom_clauses_empty_left ran_m_mapsto_upd_notin
      reduce_dom_clauses_fmupd_notin reduce_dom_clauses_fmdrop_notin split: if_splits)
    apply (auto simp: ran_m_def dest: multi_member_split)
    done
  done

lemma remove_all_watched_true_clause_different_annots_all_killed:
  assumes
    \<open>remove_all_watched_true_clause S T\<close> and
    \<open>count_decided (get_trail_l S) = 0\<close> and
    reasons: \<open>reasons_invs_wl S\<close>
  shows \<open>different_annots_all_killed (get_clauses_l S) (get_unit_clauses_wl T) (get_trail_l S)
      (get_trail_l T)\<close>
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
    TNE': \<open>TNE' = NE + mset `# NE'\<close> and
    TUE': \<open>TUE' = UE + mset `# UE'\<close>
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
    have [simp]: \<open>op \<propto> N `# dom_m N' = op \<propto> N' `# dom_m N'\<close>
      apply (rule image_mset_cong)
      using red_NN
      by (auto simp: reduce_dom_clauses_def)
    have \<open>C \<notin># dom_m N'\<close>
       using notin[OF that] .
    (* have \<open>N\<propto>C \<in># ran_mf N\<close>
      using that by (auto simp: ran_m_def) *)
    then have \<open>N\<propto>C \<in># ran_mf N - ran_mf N'\<close>
      using dom_m_NN' subset_add_mset_notin_subset_mset[of \<open>dom_m N'\<close> C \<open>dom_m (fmdrop C N)\<close>]
      using that(2) reduce_dom_clauses_ran_mf_subset[OF red_NN]
       apply (auto simp:  ran_m_def  dest!: multi_member_split)
       apply (subst (asm)(2) mset_subset_eq_exists_conv)
       apply auto
       done
    then show ?thesis
      unfolding N_N' by auto
  qed
  then have \<open>different_annots_all_killed N (NE + mset `# NE' + UE + mset `# UE') (M @ Propagated L C # M')
     (M @ Propagated L 0 # M')\<close>
    using annot annot_L_N
    by (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
        full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
        different_annot_all_killed.simps
     intro!: list.rel_refl_strong)
  then show ?case by (simp add: TNE' TUE' ac_simps)
qed

lemma rtranclp_remove_all_watched_true_clause_partial_correct_watching:
 assumes \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and \<open>partial_correct_watching S\<close>
 shows \<open>partial_correct_watching T\<close>
  using assms
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>]
  by (induction)
    (auto simp: remove_all_watched_true_clause_partial_correct_watching)

lemma remove_all_watched_true_clause_decomp_Ex:
  assumes \<open>remove_all_watched_true_clause S T\<close> and
    \<open>count_decided (get_trail_l S) = 0\<close>
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
    \<open>count_decided (get_trail_l S) = 0\<close>
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
    red: \<open>reduce_dom_clauses N N'\<close> and
    L': \<open>is_proped L' \<Longrightarrow> mark_of L'  > 0 \<Longrightarrow> mark_of L' \<in># dom_m N'\<close>
  shows
    \<open>different_annot_all_killed N NUE' L L''\<close>
proof -
  have [dest]: \<open>Ca \<in># dom_m N' \<Longrightarrow> mset (N' \<propto> Ca) = mset (N \<propto> Ca)\<close> for Ca
    using red by (auto simp: reduce_dom_clauses_def)
  show ?thesis
    using assms L' by (auto simp: different_annot_all_killed.simps reduce_dom_clauses_def)
qed

lemma different_annots_all_killed_trans:
  assumes
    MM': \<open>different_annots_all_killed N NUE M M'\<close> and
    M'M'': \<open>different_annots_all_killed N' NUE' M' M''\<close> and
    \<open>set_mset NUE \<subseteq> set_mset NUE'\<close> and
    \<open>reduce_dom_clauses N N'\<close> and
    L': \<open>\<forall>L'\<in>set M'. is_proped L' \<longrightarrow> mark_of L' > 0 \<longrightarrow> mark_of L' \<in># dom_m N'\<close>
  shows
    \<open>different_annots_all_killed N NUE' M M''\<close>
proof -
  have [simp]: \<open>length M = length M'\<close> \<open>length M' = length M''\<close>
    using MM' M'M'' by (auto simp: list_all2_conv_all_nth)
  show ?thesis
    apply (rule list_all2_all_nthI)
    subgoal using MM' M'M'' by (auto simp: list_all2_conv_all_nth)
    subgoal for n
      using list_all2_nthD[OF MM', of n]
      using list_all2_nthD[OF M'M'', of n] L'
      using different_annot_all_killed_trans[of N NUE \<open>M!n\<close> \<open>M'!n\<close> N' NUE' \<open>M''!n\<close>] assms(3-4)
      by auto
    done
qed

lemma rtranclp_remove_all_watched_true_clause_different_annots_all_killed:
  assumes
    \<open>remove_all_watched_true_clause\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (get_trail_l S) = 0\<close> and
    reasons_inv: \<open>reasons_invs_wl S\<close>
  shows \<open>different_annots_all_killed (get_clauses_l S) (get_unit_clauses_wl T) (get_trail_l S)
      (get_trail_l T)\<close>
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
    learned: \<open>learned_clss_lf N = learned_clss_lf N' + UE' \<and> reduce_dom_clauses N N'\<close> and
    red: \<open>reduce_dom_clauses N N'\<close>
    using rtranclp_remove_all_watched_true_clause_decomp_Ex[OF st lev0] by force
  have count_dec_T: \<open>count_decided (get_trail_l T) = 0\<close>
    using count_dec' unfolding T by auto
  obtain TW' TQ' M'' N'' NE'' UE'' where
    T': \<open>T = (M', N', D, NE + mset `# NE', UE + mset `# UE', TQ', TW')\<close> and
    U: \<open>U = (M'', N'', D, NE + mset `# NE' + mset `# NE'', UE + mset `# UE' + mset `# UE'', TQ',
       TW')\<close> and
    \<open>\<forall>C\<in>#mset `# (NE'' + UE''). \<exists>L\<in>#C. get_level M' L = 0 \<and> L \<in> lits_of_l M'\<close> and
    \<open>dom_m N'' \<subseteq># dom_m N'\<close> and
    \<open>map lit_of M' = map lit_of M''\<close> and
    \<open>count_decided M'' = 0\<close> and
    init': \<open>init_clss_lf N' = init_clss_lf N'' + NE''\<close> and
    learned': \<open>learned_clss_lf N' = learned_clss_lf N'' + UE''\<close> and
    red': \<open>reduce_dom_clauses N' N''\<close>
    using remove_all_watched_true_clause_decomp_Ex[OF TU count_dec_T] unfolding T
    by (auto simp: T)
  have reasons_T: \<open>reasons_invs_wl T\<close>
    using reasons_inv rtranclp_remove_all_watched_true_clause_reasons_invs_wl st by blast
  have \<open>ran_mf N = init_clss_lf N'' + learned_clss_lf N'' + NE' + NE'' + UE' + UE''\<close>
    apply (subst all_clss_lf_ran_m[symmetric])
    unfolding init init'  unfolding learned  learned'
    apply (subst learned learned')+
    by auto
  have IH': \<open>different_annots_all_killed (get_clauses_l S) (get_unit_clauses_wl T)
    (get_trail_l S) (get_trail_l T)\<close>
    using IH by auto
  moreover have \<open>different_annots_all_killed (get_clauses_l T) (get_unit_clauses_wl U)
    (get_trail_l T) (get_trail_l U)\<close>
    apply (rule remove_all_watched_true_clause_different_annots_all_killed[OF TU])
    subgoal using count_dec' by (auto simp: T count_decided_0_iff)
    subgoal using st IH
      by (auto simp: list_all2_append count_decided_0_iff is_decided_no_proped_iff
             full_def rtranclp_remove_one_watched_true_clause_reasons_invs_wl
           intro: rtranclp_remove_one_watched_true_clause_reasons_invs_wl
             rtranclp_remove_all_watched_true_clause_reasons_invs_wl)
    done
  ultimately show ?case
    using red red' reasons_T
    apply -
    apply (rule different_annots_all_killed_trans)
      apply assumption+
    apply (auto simp: S T U reasons_invs_wl_def
      intro: different_annots_all_killed_trans
      dest: split_list)
    apply (case_tac L')
    apply (auto dest!: split_list)

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
    lev0: \<open>count_decided (get_trail_l S) = 0\<close> and
    partial: \<open>partial_correct_watching S\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    all0: \<open>\<forall>L C. Propagated L C \<in> set (get_trail_l T) \<longrightarrow> C = 0\<close> and
    dom0: \<open>0 \<notin># dom_m (get_clauses_l S)\<close> and
    reason: \<open>reasons_invs_wl S\<close>
  shows \<open>cdcl_twl_restart_l_p S T\<close>
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
  have annot: \<open>different_annots_all_killed (get_clauses_l T) (get_unit_clauses_wl T)
   (get_trail_l S) (get_trail_l T)\<close>
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
    apply (rule cdcl_twl_restart_l_p.intros)
    subgoal using red .
    subgoal using init .
    subgoal using learned by auto
    subgoal using NUE by (auto dest!: multi_member_split)
    subgoal using all0 unfolding T by auto
    subgoal using all0 annot red_NN' unfolding T
      apply (intro conjI impI allI)
     apply (auto simp: S)
    subgoal using all0 unfolding T by auto
    subgoal using dom0 dom_mono by (auto simp: S)
    subgoal by auto
    subgoal using rtranclp_remove_all_watched_true_clause_partial_correct_watching[OF remove
      partial] unfolding T D .
    done
qed


definition remove_all_clause_watched_by_inv where
  \<open>remove_all_clause_watched_by_inv = (\<lambda>(M\<^sub>0, N\<^sub>0, D\<^sub>0, NE\<^sub>0, UE\<^sub>0, Q\<^sub>0, W\<^sub>0) (M, N, D, NE, UE, Q, W).
       ran_mf N + NE + UE = ran_mf N\<^sub>0 + NE\<^sub>0 + UE\<^sub>0)\<close>

definition remove_all_clause_watched_by
  :: \<open>nat literal \<Rightarrow> nat twl_st_l \<Rightarrow> (nat twl_st_l) nres\<close>
where
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
      (\<lambda>(i, S). i > 0 \<and> \<not>is_decided (get_trail_l S!i))
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
  \<open>collect_valid_indices S = SPEC (\<lambda>N. mset N = dom_m (get_clauses_l S))\<close>

end