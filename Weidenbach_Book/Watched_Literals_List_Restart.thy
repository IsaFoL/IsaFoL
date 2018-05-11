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
  Remark about the predicate:
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

lemma (in -) in_convert_lits_lD:
  \<open>K \<in> set TM \<Longrightarrow>
    (M, TM) \<in> convert_lits_l N NE \<Longrightarrow>
      \<exists>K'. K' \<in> set M \<and> convert_lit N NE K' K\<close>
  by (auto 5 5 simp: convert_lits_l_def list_rel_append2 dest!: split_list  p2relD
    elim!: list_relE)

lemma (in -) get_level_append_if:
  \<open>get_level (M @ M') L = (if defined_lit M L then get_level M L + count_decided M'
            else get_level M' L)\<close>
  by (auto)

lemma convert_lits_lI:
  \<open>length M = length M' \<Longrightarrow> (\<And>i. i < length M \<Longrightarrow> convert_lit N NE (M!i) (M'!i)) \<Longrightarrow>
     (M, M') \<in> convert_lits_l N NE\<close>
  by (auto simp: convert_lits_l_def list_rel_def p2rel_def list_all2_conv_all_nth)

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

end