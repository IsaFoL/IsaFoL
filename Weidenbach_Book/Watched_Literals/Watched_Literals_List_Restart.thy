theory Watched_Literals_List_Restart
  imports Watched_Literals_List Watched_Literals_Algorithm_Restart
    Weidenbach_Book_Base.Explorer
begin

text \<open>
  Unlike most other refinements steps we have done, we don't try to refine our
  specification to our code directly: We first introduce an intermediate transition system which
  is closer to what we want to implement. Then we refine it to code.
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

lemma valid_trail_reduction_refl[simp]:
  \<open>valid_trail_reduction M M\<close>
  by (rule valid_trail_reduction.keep_red)
    auto

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
      dest: in_lits_of_l_defined_litD no_dup_append_in_atm_notin
      split: if_splits)
    also have \<open>... \<longleftrightarrow> (L \<in> lits_of_l M' \<and> get_level M' L = 0)\<close>
      using eq by (metis local.H trail_renumber_get_level)
    finally show ?thesis
      by blast
  qed
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

text \<open>
  Remarks about the predicate:
  \<^item> The cases \<^term>\<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow>
    E' \<noteq> 0 \<longrightarrow> P\<close> are already covered by the invariants (where \<^term>\<open>P\<close> means that there is
    clause which was already present before).
\<close>
inductive cdcl_twl_restart_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart_l (M, N, None, NE, UE, NS, US, {#}, Q)
       (M', N', None, NE + mset `# NE', UE + mset `# UE', NS, US', {#}, Q')\<close>
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
    \<open>if length M = length M' then Q = Q' else Q' = {#}\<close>and
    \<open>US' = {#}\<close>

lemma cdcl_twl_restart_l_list_invs:
  assumes
    \<open>cdcl_twl_restart_l S T\<close> and
    \<open>twl_list_invs S\<close>
  shows
    \<open>twl_list_invs T\<close>
  using assms
proof (induction rule: cdcl_twl_restart_l.induct)
  case (restart_trail M M' N N' NE' UE' NE UE Q Q' US' NS US) note red = this(1) and init = this(2) and
    learned = this(3) and NUE = this(4) and tr_ge0 = this(5) and tr_new0 = this(6) and
    tr_still0 = this(7) and dom0 = this(8) and QQ' = this(9) and US = this(10) and list_invs = this(11)
  let ?S = \<open>(M, N, None, NE, UE, NS, US, {#}, Q)\<close>
  let ?T = \<open>(M', N', None, NE + mset `# NE', UE + mset `# UE', NS, US', {#}, Q')\<close>
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
      L_C'0: \<open>length (get_clauses_l ?S \<propto> C') > 2 \<Longrightarrow> L = get_clauses_l ?S \<propto> C' ! 0\<close>
      using list_invs C'0 LC' unfolding twl_list_invs_def
      by auto
    show \<open>L \<in> set (watched_l (get_clauses_l ?T \<propto> C))\<close>
      using L_watched NCC' by simp

    show \<open>length (get_clauses_l ?T \<propto> C) > 2 \<Longrightarrow> L = get_clauses_l ?T \<propto> C ! 0\<close>
      using L_C'0 NCC' by simp
  next
    show \<open>distinct_mset (clauses_to_update_l ?T)\<close>
      by auto
  qed
qed


lemma rtranclp_cdcl_twl_restart_l_list_invs:
  assumes
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_list_invs S\<close>
  shows
    \<open>twl_list_invs T\<close>
  using assms by induction (auto intro: cdcl_twl_restart_l_list_invs)

lemma cdcl_twl_restart_l_cdcl_twl_restart:
  assumes ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close>
  shows \<open>SPEC (cdcl_twl_restart_l S) \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
         clauses_to_update_l S = {#}}
     (SPEC (cdcl_twl_restart T))\<close>
proof -
  have [simp]: \<open>set (watched_l x) \<union> set (unwatched_l x) = set x\<close> for x
    by (metis append_take_drop_id set_append)
  have \<open>\<exists>T'. cdcl_twl_restart T T' \<and> (S', T') \<in> twl_st_l None\<close>
    if \<open>cdcl_twl_restart_l S S'\<close> for S'
    using that ST struct_invs
  proof (induction rule: cdcl_twl_restart_l.induct)
    case (restart_trail M M' N N' NE' UE' NE UE Q Q' US' NS US) note red = this(1) and init = this(2) and
      learned = this(3) and NUE = this(4) and tr_ge0 = this(5) and tr_new0 = this(6) and
      tr_still0 = this(7) and dom0 = this(8) and QQ' = this(9) and US = this(10) and ST = this(11) and
      struct_invs = this(12)
    let ?T' = \<open>(drop (length M - length M') (get_trail T), twl_clause_of `# init_clss_lf N',
          twl_clause_of `# learned_clss_lf N', None, NE+mset `# NE', UE+mset `# UE', NS, US', {#}, Q')\<close>
    have [intro]: \<open>Q \<noteq> Q' \<Longrightarrow> Q' = {#}\<close>
      using QQ' by (auto split: if_splits)
    obtain TM where
        T: \<open>T = (TM, twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N, None,
        NE, UE, NS, US, {#}, Q)\<close> and
      M_TM: \<open>(M, TM) \<in> convert_lits_l N (NE+UE)\<close>
      using ST
      by (cases T) (auto simp: twl_st_l_def)
    have \<open>no_dup TM\<close>
      using struct_invs unfolding T twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
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
          NE, UE, NS, US, {#}, Q)
        (TM, twl_clause_of `# init_clss_lf N', twl_clause_of `# learned_clss_lf N', None,
          NE + clauses (twl_clause_of `# NE'), UE + clauses (twl_clause_of `# UE'),
          NS, {#}, {#}, Q)\<close> (is \<open>cdcl_twl_restart ?A ?B\<close>)
        apply (rule cdcl_twl_restart.restart_clauses)
        subgoal
          using learned by (auto dest: image_mset_subseteq_mono)
        subgoal unfolding init image_mset_union by auto
        subgoal using NUE M_TM by auto
        subgoal by (rule annot_in_clauses)
        subgoal using US by (auto split: if_splits)
        done
      moreover have \<open>?A = T\<close>
        unfolding T by simp
      moreover have \<open>?B = ?T'\<close>
        using US
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
        using backtrack_red(1) by auto
      have H: \<open>L \<in> lits_of_l (drop (length M - length M') TM) \<and>
          get_level (drop (length M - length M') TM) L = 0\<close>
        if \<open>L \<in> lits_of_l M \<and> get_level M L = 0\<close> for L
      proof -
        have \<open>L \<in> lits_of_l M2 \<and> get_level M2 L = 0\<close>
          using decomp that n_d
          by (auto dest!: get_all_ann_decomposition_exists_prepend
            dest: in_lits_of_l_defined_litD
            simp: get_level_append_if get_level_cons_if split: if_splits)
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
          NE, UE, NS, US, {#}, Q)
        (drop (length M - length M') TM, twl_clause_of `# init_clss_lf N',
          twl_clause_of `# learned_clss_lf N', None,
          NE + clauses (twl_clause_of `# NE'), UE + clauses (twl_clause_of `# UE'), NS, {#}, {#},
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
        using QQ' decomp US unfolding T by (auto simp: mset_take_mset_drop_mset')
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
      then have \<open>((M', N', None, NE + mset `# NE', UE + mset `# UE', NS, US', {#}, Q'), ?T')
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


definition (in -) restart_abs_l_pre :: \<open>'v twl_st_l \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_l_pre S brk \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and> restart_prog_pre S' brk
      \<and> twl_list_invs S \<and> clauses_to_update_l S = {#})\<close>

context twl_restart_ops
begin

definition restart_required_l :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_l S n = SPEC (\<lambda>b. b \<longrightarrow> size (get_learned_clss_l S) > f n)\<close>

definition restart_abs_l
  :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_l \<times> nat) nres"
where
  \<open>restart_abs_l S n brk = do {
     ASSERT(restart_abs_l_pre S brk);
     b \<leftarrow> restart_required_l S n;
     b2 \<leftarrow> SPEC (\<lambda>(_ ::bool). True);
     if b \<and> b2 \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_l S T);
       RETURN (T, n + 1)
     }
     else
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


lemma restart_abs_l_restart_prog:
  \<open>(uncurry2 restart_abs_l, uncurry2 restart_prog) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}
        \<times>\<^sub>f nat_rel  \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}
        \<times>\<^sub>f nat_rel\<rangle> nres_rel\<close>
    unfolding restart_abs_l_def restart_prog_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      restart_required_l_restart_required[THEN fref_to_Down_curry]
      cdcl_twl_restart_l_cdcl_twl_restart)
    subgoal for Snb Snb'
     unfolding restart_abs_l_pre_def
     by (rule exI[of _ \<open>fst (fst (Snb'))\<close>]) simp
    subgoal by simp
    subgoal by auto  \<comment> \<open>If condition\<close>
    subgoal by simp
    subgoal by simp
    subgoal unfolding restart_prog_pre_def by meson
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding restart_prog_pre_def by meson
    subgoal by auto
    subgoal by auto
    done


definition cdcl_twl_stgy_restart_abs_l_inv where
  \<open>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> twl_st_l None \<and>
       (T, T') \<in> twl_st_l None \<and>
       cdcl_twl_stgy_restart_prog_inv S\<^sub>0' brk T' n \<and>
       clauses_to_update_l T  = {#} \<and>
       twl_list_invs T)\<close>

definition cdcl_twl_stgy_restart_abs_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_abs_l S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_abs_l T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0, 0);
    RETURN T
  }\<close>

lemma cdcl_twl_stgy_restart_abs_l_cdcl_twl_stgy_restart_abs_l:
  \<open>(cdcl_twl_stgy_restart_abs_l, cdcl_twl_stgy_restart_prog) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_abs_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
      (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> brk = brk' \<and> n = n' \<and>
        clauses_to_update_l S = {#}}\<close>]
      unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
      restart_abs_l_restart_prog[THEN fref_to_Down_curry2])
  subgoal by simp
  subgoal for x y xa x' x1 x2 x1a x2a
    unfolding cdcl_twl_stgy_restart_abs_l_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd x')\<close> in exI)
    by auto
  subgoal by fast
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_inv_def
      cdcl_twl_stgy_restart_abs_l_inv_def
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
  We here start the refinement towards an executable version of the restarts. The idea of the
  restart is the following:
  \<^enum> We backtrack to level 0. This simplifies further steps.
  \<^enum> We first move all clause annotating a literal to \<^term>\<open>NE\<close> or \<^term>\<open>UE\<close>.
  \<^enum> Then, we move remaining clauses that are watching the some literal at level 0.
  \<^enum> Now we can safely deleting any remaining learned clauses.
  \<^enum> Once all that is done, we have to recalculate the watch lists (and can on the way GC the set of
    clauses).
\<close>

subsubsection \<open>Handle true clauses from the trail\<close>

lemma in_set_mset_eq_in:
  \<open>i \<in> set A \<Longrightarrow> mset A = B \<Longrightarrow> i \<in># B\<close>
  by fastforce


text \<open>Our transformation will be chains of a weaker version of restarts, that don't update the
  watch lists and only keep partial correctness of it.
\<close>

lemma cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l:
  assumes
    ST: \<open>cdcl_twl_restart_l S T\<close> and TU: \<open>cdcl_twl_restart_l T U\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>cdcl_twl_restart_l S U\<close>
  using assms
proof -
  obtain M M' N N' NE' UE' NE UE NS US Q Q' W' W where
    S: \<open>S = (M, N, None, NE, UE, NS, US, W, Q)\<close> and
    T: \<open>T = (M', N', None, NE + mset `# NE', UE + mset `# UE', NS, {#}, W', Q')\<close> and
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
    W: \<open>W = {#}\<close>
    using ST unfolding cdcl_twl_restart_l.simps
    apply -
    apply normalize_goal+
    by blast
  obtain M'' N'' NE'' UE'' Q'' W'' where
    U: \<open>U = (M'', N'', None, NE + mset `# NE' + mset `# NE'', UE + mset `# UE' + mset `# UE'', NS,
      {#}, W'', Q'')\<close> and
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
    W': \<open>W' = {#}\<close> and
    W'': \<open>W'' = {#}\<close>
    using TU unfolding cdcl_twl_restart_l.simps T apply -
    apply normalize_goal+
    by blast
  have U': \<open>U = (M'', N'', None, NE + mset `# (NE' + NE''), UE + mset `# (UE' + UE''), NS, {#}, W'',
      Q'')\<close>
    unfolding U by simp
  show ?thesis
    unfolding S U' W W' W''
    apply (rule cdcl_twl_restart_l.restart_trail)
    subgoal using valid_trail_reduction_trans[OF tr_red tr_red'] .
    subgoal using init init' by auto
    subgoal using learned learned' subset_mset.dual_order.trans by fastforce
    subgoal using NUE NUE' valid_trail_reduction_level0_iff[OF tr_red] n_d unfolding S by auto
    subgoal using ge0 ge0' tr_red' init learned NUE ge0  still0' (* TODO tune proof *)
      apply (auto dest: valid_trail_reduction_Propagated_inD)
      apply (blast dest: valid_trail_reduction_Propagated_inD)+
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
    subgoal by auto
    done
qed

lemma rtranclp_cdcl_twl_restart_l_no_dup:
  assumes
    ST: \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S T\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>no_dup (get_trail_l T)\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal
    by (auto simp: cdcl_twl_restart_l.simps valid_trail_reduction_simps
      dest: map_lit_of_eq_no_dupD dest!: no_dup_appendD get_all_ann_decomposition_exists_prepend)
  done

lemma tranclp_cdcl_twl_restart_l_cdcl_is_cdcl_twl_restart_l:
  assumes
    ST: \<open>cdcl_twl_restart_l\<^sup>+\<^sup>+ S T\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>cdcl_twl_restart_l S T\<close>
  using assms
  apply (induction rule: tranclp_induct)
  subgoal by auto
  subgoal
    using cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
    rtranclp_cdcl_twl_restart_l_no_dup by blast
  done


paragraph \<open>Auxilary definition\<close>
text \<open>
  This definition states that the domain of the clauses is reduced, but the remaining clauses
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


paragraph \<open>Refinement towards code\<close>

text \<open>
  Once of the first thing we do, is removing clauses we know to be true. We do in two ways:
    \<^item> along the trail (at level 0); this makes sure that annotations are kept;
    \<^item> then along the watch list.

  This is (obviously) not complete but is faster by avoiding iterating over all clauses. Here are
  the rules we want to apply for our very limited inprocessing:
\<close>
inductive remove_one_annot_true_clause :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
remove_irred_trail:
  \<open>remove_one_annot_true_clause (M @ Propagated L C # M', N, D, NE, UE, NS, US, W, Q)
     (M @ Propagated L 0 # M', fmdrop C N, D, add_mset (mset (N\<propto>C)) NE, UE, NS, {#}, W, Q)\<close>
if
  \<open>get_level (M @ Propagated L C # M') L = 0\<close> and
  \<open>C > 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>irred N C\<close> |
remove_red_trail:
  \<open>remove_one_annot_true_clause (M @ Propagated L C # M', N, D, NE, UE, NS, US, W, Q)
     (M @ Propagated L 0 # M', fmdrop C N, D, NE, add_mset (mset (N\<propto>C)) UE, NS, {#}, W, Q)\<close>
if
  \<open>get_level (M @ Propagated L C # M') L = 0\<close> and
  \<open>C > 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>\<not>irred N C\<close> |
remove_irred:
  \<open>remove_one_annot_true_clause (M, N, D, NE, UE, NS, US, W, Q)
     (M, fmdrop C N, D, add_mset (mset (N\<propto>C))NE, UE, NS, {#}, W, Q)\<close>
if
  \<open>L \<in> lits_of_l M\<close> and
  \<open>get_level M L = 0\<close> and
  \<open>C \<in># dom_m N\<close> and
  \<open>L \<in> set (N\<propto>C)\<close> and
  \<open>irred N C\<close> and
  \<open>\<forall>L. Propagated L C \<notin> set M\<close> |
delete:
  \<open>remove_one_annot_true_clause (M, N, D, NE, UE, NS, US, W, Q)
     (M, fmdrop C N, D, NE, UE, NS, {#}, W, Q)\<close>
if
  \<open>C \<in># dom_m N\<close> and
  \<open>\<not>irred N C\<close> and
  \<open>\<forall>L. Propagated L C \<notin> set M\<close> |
delete_subsumed:
  \<open>remove_one_annot_true_clause (M, N, D, NE, UE, NS, US, W, Q)
     (M, N, D, NE, UE, NS, {#}, W, Q)\<close>

text \<open>Remarks:
  \<^enum> \<^term>\<open>\<forall>L. Propagated L C \<notin> set M\<close> is overkill. However, I am currently unsure how I want to
  handle it (either as \<^term>\<open>Propagated (N\<propto>C!0) C \<notin> set M\<close> or as ``the trail contains only zero
  anyway'').\<close>

lemma Ex_ex_eq_Ex: \<open>(\<exists>NE'. (\<exists>b. NE' = {#b#} \<and> P b NE') \<and> Q NE') \<longleftrightarrow>
   (\<exists>b. P b {#b#} \<and> Q {#b#})\<close>
   by auto

lemma in_set_definedD:
  \<open>Propagated L' C \<in> set M' \<Longrightarrow> defined_lit M' L'\<close>
  \<open>Decided L' \<in> set M' \<Longrightarrow> defined_lit M' L'\<close>
  by (auto simp: defined_lit_def)

lemma (in conflict_driven_clause_learning\<^sub>W) trail_no_annotation_reuse:
  assumes
    struct_invs: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    LC: \<open>Propagated L C \<in> set (trail S)\<close> and
    LC': \<open>Propagated L' C \<in> set (trail S)\<close>
  shows "L = L'"
proof -
  have
    confl: \<open>cdcl\<^sub>W_conflicting S\<close> and
    n_d: \<open>no_dup (trail S)\<close>
    using struct_invs unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by fast+
    find_theorems "_ @ _#_ = _ @ _ # _"
  have H: \<open>L = L'\<close> if \<open>trail S = ysa @ Propagated L' C # c21 @ Propagated L C # zs\<close>
    for ysa xsa c21 zs L L'
  proof -
    have 1: \<open>c21 @ Propagated L C # zs \<Turnstile>as CNot (remove1_mset L' C) \<and> L' \<in># C\<close>
      using confl unfolding cdcl\<^sub>W_conflicting_def that
      by (auto)
    have that': \<open>trail S = (ysa @ Propagated L' C # c21) @ Propagated L C # zs\<close>
      unfolding that by auto
    have 2: \<open>zs \<Turnstile>as CNot (remove1_mset L C) \<and> L \<in># C\<close>
      using confl unfolding cdcl\<^sub>W_conflicting_def that'
      by blast
    show \<open>L = L'\<close>
      using 1 2 n_d unfolding that
      by (auto dest!: multi_member_split
        simp: true_annots_true_cls_def_iff_negation_in_model add_mset_eq_add_mset
        Decided_Propagated_in_iff_in_lits_of_l)
  qed
  show ?thesis
    using H[of _ L _ L']  H[of _  L' _ L]
    using split_list[OF LC] split_list[OF LC']
    by (force elim!: list_match_lel_lel)
qed


lemma
  assumes \<open>no_dup M\<close>
  shows
    no_dup_same_annotD:
        \<open>Propagated L C \<in> set M \<Longrightarrow> Propagated L C' \<in> set M \<Longrightarrow> C = C'\<close> and
     no_dup_no_propa_and_dec:
       \<open>Propagated L C \<in> set M \<Longrightarrow> Decided L \<in> set M \<Longrightarrow> False\<close>
  using assms
  by (auto dest!: split_list elim: list_match_lel_lel)

lemma remove_one_annot_true_clause_cdcl_twl_restart_l:
  assumes
    rem: \<open>remove_one_annot_true_clause S T\<close> and
    lst_invs: \<open>twl_list_invs S\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    n_d: \<open>no_dup (get_trail_l S)\<close>
  shows \<open>cdcl_twl_restart_l S T\<close>
  using assms
proof -
  have dist_N: \<open>distinct_mset (dom_m (get_clauses_l S))\<close>
    by (rule distinct_mset_dom)
  then have C_notin_rem: \<open>C \<notin># remove1_mset C (dom_m (get_clauses_l S))\<close> for C
    by (simp add: distinct_mset_remove1_All)
   have
    \<open>\<forall>C\<in>#clauses_to_update_l S. C \<in># dom_m (get_clauses_l S)\<close> and
    dom0: \<open>0 \<notin># dom_m (get_clauses_l S)\<close> and
    annot: \<open>\<And>L C. Propagated L C \<in> set (get_trail_l S) \<Longrightarrow>
           0 < C \<Longrightarrow>
             (C \<in># dom_m (get_clauses_l S) \<and>
            L \<in> set (watched_l (get_clauses_l S \<propto> C)) \<and>
            (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow> L = get_clauses_l S \<propto> C ! 0))\<close> and
    \<open>distinct_mset (clauses_to_update_l S)\<close>
    using lst_invs unfolding twl_list_invs_def apply -
    by fast+

  have struct_S': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S')\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  show ?thesis
    using rem
  proof (cases rule: remove_one_annot_true_clause.cases)
    case (remove_irred_trail M L C M' N D NE UE NS US W Q) note S = this(1) and T = this(2) and
      lev_L = this(3) and C0 = this(4) and C_dom = this(5) and irred = this(6)
    have D: \<open>D = None\<close> and W: \<open>W = {#}\<close>
      using confl upd unfolding S by auto
    have NE: \<open>add_mset (mset (N \<propto> C)) NE = NE + mset `# {#N\<propto>C#}\<close>
      by simp
    have UE: \<open>UE = UE + mset `# {#}\<close>
      by simp
    have new_NUE: \<open>\<forall>E\<in>#{#N \<propto> C#} + {#}.
       \<exists>La\<in>set E.
          La \<in> lits_of_l (M @ Propagated L C # M') \<and>
          get_level (M @ Propagated L C # M') La = 0\<close>
      apply (intro ballI impI)
      apply (rule_tac x=L in bexI)
      using lev_L annot[of L _] C0 by (auto simp: S dest: in_set_takeD[of _ 2])
    have [simp]: \<open>Propagated L E' \<notin> set M'\<close> \<open>Propagated L E' \<notin> set M\<close> for E'
      using n_d lst_invs
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E'\<close> M]
           split_list[of \<open>Propagated L E'\<close> M'])
    have [simp]:  \<open>Propagated L' C \<notin> set M'\<close> \<open>Propagated L' C \<notin> set M\<close> for L'
      using SS' n_d C0 struct_S'
      cdcl\<^sub>W_restart_mset.trail_no_annotation_reuse[of \<open>state\<^sub>W_of S'\<close> L \<open>(mset (N \<propto> C))\<close> L']
      apply (auto simp: S twl_st_l_def convert_lits_l_imp_same_length trail.simps
        )
      apply (auto simp: list_rel_append1 list_rel_split_right_iff convert_lits_l_def
        p2rel_def)
      apply (case_tac y)
      apply (auto simp: list_rel_append1 list_rel_split_right_iff defined_lit_convert_lits_l
        simp flip: p2rel_def convert_lits_l_def dest: in_set_definedD(1)[of _ _ M'])
      apply (auto simp: list_rel_append1 list_rel_split_right_iff convert_lits_l_def
        p2rel_def convert_lit.simps
        dest!: split_list[of \<open>Propagated L' C\<close> M']
           split_list[of \<open>Propagated L' C\<close> M])
      done
    have propa_MM: \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M \<Longrightarrow> E=E'\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M]
           split_list[of \<open>Propagated L E'\<close> M]
           elim!: list_match_lel_lel)
    have propa_M'M': \<open>Propagated L E \<in> set M' \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow> E=E'\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M']
           split_list[of \<open>Propagated L E'\<close> M']
           elim!: list_match_lel_lel)
    have propa_MM': \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow> False\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M]
           split_list[of \<open>Propagated L E'\<close> M']
           elim!: list_match_lel_lel)
    have propa_M'_nC_dom: \<open>Propagated La E \<in> set M' \<Longrightarrow> E \<noteq> C \<and> (E > 0 \<longrightarrow> E \<in># dom_m N)\<close> for La E
      using annot[of La E] unfolding S by auto
    have propa_M_nC_dom:  \<open>Propagated La E \<in> set M \<Longrightarrow> E \<noteq> C \<and> (E > 0 \<longrightarrow> E \<in># dom_m N)\<close> for La E
      using annot[of La E] unfolding S by auto
    show ?thesis
      unfolding S T D W NE
      apply (subst (2) UE)
      apply (rule cdcl_twl_restart_l.intros)
      subgoal by (auto simp: valid_trail_reduction_change_annot)
      subgoal using C_dom irred by auto
      subgoal using irred by auto
      subgoal using new_NUE .
      subgoal
        apply (intro conjI allI impI)
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E]
          unfolding S by auto
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E] propa_MM'[of La E' E] propa_M'M'[of La E' E]
          unfolding S by auto
        done
      subgoal
        apply (intro allI impI)
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E] propa_MM'[of La E' E] propa_M'M'[of La E' E]
          by auto
        done
      subgoal
        apply (intro allI impI)
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E] propa_MM'[of La E' E] propa_M'M'[of La E' E]
          by auto
        done
      subgoal using dom0 unfolding S by (auto dest: in_diffD)
      subgoal by auto
      subgoal by auto
      done
  next
    case (remove_red_trail M L C M' N D NE UE NS US W Q) note S =this(1) and T = this(2) and
      lev_L = this(3) and C0 = this(4) and C_dom = this(5) and irred = this(6)
    have D: \<open>D = None\<close> and W: \<open>W = {#}\<close>
      using confl upd unfolding S by auto
    have UE: \<open>add_mset (mset (N \<propto> C)) UE = UE + mset `# {#N\<propto>C#}\<close>
      by simp
    have NE: \<open>NE = NE + mset `# {#}\<close>
      by simp
    have new_NUE: \<open>\<forall>E\<in>#{#} + {#N \<propto> C#}.
       \<exists>La\<in>set E.
          La \<in> lits_of_l (M @ Propagated L C # M') \<and>
          get_level (M @ Propagated L C # M') La = 0\<close>
      apply (intro ballI impI)
      apply (rule_tac x=L in bexI)
      using lev_L annot[of L _] C0 by (auto simp: S dest: in_set_takeD[of _ 2])
    have [simp]: \<open>Propagated L E' \<notin> set M'\<close> \<open>Propagated L E' \<notin> set M\<close> for E'
      using n_d lst_invs
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E'\<close> M]
           split_list[of \<open>Propagated L E'\<close> M'])
    have [simp]:  \<open>Propagated L' C \<notin> set M'\<close> \<open>Propagated L' C \<notin> set M\<close> for L'
      using SS' n_d C0 struct_S'
      cdcl\<^sub>W_restart_mset.trail_no_annotation_reuse[of \<open>state\<^sub>W_of S'\<close> L \<open>(mset (N \<propto> C))\<close> L']
      apply (auto simp: S twl_st_l_def convert_lits_l_imp_same_length trail.simps
        )
      apply (auto simp: list_rel_append1 list_rel_split_right_iff convert_lits_l_def
        p2rel_def)
      apply (case_tac y)
      apply (auto simp: list_rel_append1 list_rel_split_right_iff defined_lit_convert_lits_l
        simp flip: p2rel_def convert_lits_l_def dest: in_set_definedD(1)[of _ _ M'])
      apply (auto simp: list_rel_append1 list_rel_split_right_iff convert_lits_l_def
        p2rel_def convert_lit.simps
        dest!: split_list[of \<open>Propagated L' C\<close> M']
           split_list[of \<open>Propagated L' C\<close> M])
      done
    have propa_MM: \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M \<Longrightarrow> E=E'\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M]
           split_list[of \<open>Propagated L E'\<close> M]
           elim!: list_match_lel_lel)
    have propa_M'M': \<open>Propagated L E \<in> set M' \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow> E=E'\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M']
           split_list[of \<open>Propagated L E'\<close> M']
           elim!: list_match_lel_lel)
    have propa_MM': \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow> False\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M]
           split_list[of \<open>Propagated L E'\<close> M']
           elim!: list_match_lel_lel)
    have propa_M'_nC_dom:  \<open>Propagated La E \<in> set M' \<Longrightarrow> E \<noteq> C \<and> (E > 0 \<longrightarrow> E \<in># dom_m N)\<close> for La E
      using annot[of La E] unfolding S by auto
    have propa_M_nC_dom:  \<open>Propagated La E \<in> set M \<Longrightarrow> E \<noteq> C \<and> (E > 0 \<longrightarrow> E \<in># dom_m N)\<close> for La E
      using annot[of La E] unfolding S by auto
    show ?thesis
      unfolding S T D W UE
      apply (subst (2) NE)
      apply (rule cdcl_twl_restart_l.intros)
      subgoal by (auto simp: valid_trail_reduction_change_annot)
      subgoal using C_dom irred by auto
      subgoal using C_dom irred by auto
      subgoal using new_NUE .
      subgoal
        apply (intro conjI allI impI)
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E]
          unfolding S by auto
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E] propa_MM'[of La E' E] propa_M'M'[of La E' E]
          unfolding S by auto
        done
      subgoal
        apply (intro allI impI)
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E] propa_MM'[of La E' E] propa_M'M'[of La E' E]
          by auto
        done
      subgoal
        apply (intro allI impI)
        subgoal for La E E'
          using C_notin_rem propa_MM[of La E E'] propa_MM'[of La E E'] propa_M'_nC_dom[of La E]
            propa_M_nC_dom[of La E] propa_MM'[of La E' E] propa_M'M'[of La E' E]
          by auto
        done
      subgoal using dom0 unfolding S by (auto dest: in_diffD)
      subgoal by auto
      subgoal by auto
      done
  next
    case (remove_irred L M C N D NE UE NS US W Q) note S =this(1) and T = this(2) and
      L_M = this(3) and lev_L = this(4) and C_dom = this(5) and watched_L = this(6) and
      irred = this(7) and L_notin_M = this(8)
    have NE: \<open>add_mset (mset (N \<propto> C)) NE = NE + mset `# {#N\<propto>C#}\<close>
      by simp
    have UE: \<open>UE = UE + mset `# {#}\<close>
      by simp
    have D: \<open>D = None\<close> and W: \<open>W = {#}\<close>
      using confl upd unfolding S by auto
    have new_NUE: \<open>\<forall>E\<in>#{#N \<propto> C#} + {#}.
       \<exists>La\<in>set E.
          La \<in> lits_of_l M \<and>
          get_level M La = 0\<close>
      apply (intro ballI impI)
      apply (rule_tac x=L in bexI)
      using lev_L annot[of L _] L_M watched_L by (auto simp: S dest: in_set_takeD[of _ 2])
    have C0: \<open>C > 0\<close>
      using dom0 C_dom unfolding S by (auto dest!: multi_member_split)
    have [simp]: \<open>Propagated La C \<notin> set M\<close> for La
      using annot[of La C] dom0 n_d L_notin_M C0 unfolding S
      by auto
    have propa_MM: \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M \<Longrightarrow> E=E'\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M]
           split_list[of \<open>Propagated L E'\<close> M]
           elim!: list_match_lel_lel)
    show ?thesis
      unfolding S T D W NE
      apply (subst (2) UE)
      apply (rule cdcl_twl_restart_l.intros)
      subgoal by (auto simp: valid_trail_reduction_refl)
      subgoal using C_dom irred by auto
      subgoal using C_dom irred by auto
      subgoal using new_NUE .
      subgoal
        using n_d L_notin_M C_notin_rem annot propa_MM unfolding S by force
      subgoal
        using propa_MM by auto
      subgoal
        using propa_MM by auto
      subgoal using dom0 C_dom unfolding S by (auto dest: in_diffD)
      subgoal by auto
      subgoal by auto
      done
  next
    case (delete C N M D NE UE NS US W Q) note S = this(1) and T = this(2) and C_dom = this(3) and
       irred = this(4) and L_notin_M = this(5)
    have D: \<open>D = None\<close> and W: \<open>W = {#}\<close>
      using confl upd unfolding S by auto
    have UE: \<open>UE = UE + mset `# {#}\<close>
      by simp
    have NE: \<open>NE = NE + mset `# {#}\<close>
      by simp
    have propa_MM: \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M \<Longrightarrow> E=E'\<close> for L E E'
      using n_d
      by (auto simp: S twl_list_invs_def
        dest!: split_list[of \<open>Propagated L E\<close> M]
           split_list[of \<open>Propagated L E'\<close> M]
           elim!: list_match_lel_lel)
    show ?thesis
      unfolding S T D W
      apply (subst (2) NE)
      apply (subst (2) UE)
      apply (rule cdcl_twl_restart_l.intros)
      subgoal by (auto simp: valid_trail_reduction_refl)
      subgoal using C_dom irred by auto
      subgoal using C_dom irred by auto
      subgoal by simp
      subgoal
        apply (intro conjI impI allI)
        subgoal for L E E'
          using n_d L_notin_M C_notin_rem annot propa_MM[of L E E'] unfolding S
          by (metis dom_m_fmdrop get_clauses_l.simps get_trail_l.simps in_remove1_msetI)
        subgoal for L E E'
          using n_d L_notin_M C_notin_rem annot propa_MM[of L E E'] unfolding S
          by auto
        done
      subgoal
        using propa_MM by auto
      subgoal
        using propa_MM by auto
      subgoal using dom0 C_dom unfolding S by (auto dest: in_diffD)
      subgoal by auto
      subgoal by auto
      done
  next
    case (delete_subsumed M N D NE UE NS US W Q)
    have \<open>cdcl_twl_restart_l (M, N, None, NE, UE, NS, US, {#}, Q)
       (M, N, None, NE + mset `# {#}, UE + mset `# {#}, NS, {#}, {#}, Q)\<close>
      by (rule cdcl_twl_restart_l.intros)
        (use lst_invs n_d in \<open>auto dest: no_dup_same_annotD simp: delete_subsumed twl_list_invs_def\<close>)
    then show ?thesis
      using assms
      unfolding delete_subsumed
      by simp
  qed
qed


lemma is_annot_iff_annotates_first:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    C0: \<open>C > 0\<close>
  shows
    \<open>(\<exists>L. Propagated L C \<in> set (get_trail_l S)) \<longleftrightarrow>
       ((length (get_clauses_l S \<propto> C) > 2 \<longrightarrow>
          Propagated (get_clauses_l S \<propto> C ! 0) C \<in> set (get_trail_l S)) \<and>
        ((length (get_clauses_l S \<propto> C) \<le> 2 \<longrightarrow>
	   Propagated (get_clauses_l S \<propto> C ! 0) C \<in> set (get_trail_l S) \<or>
	   Propagated (get_clauses_l S \<propto> C ! 1) C \<in> set (get_trail_l S))))\<close>
    (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof (rule iffI)
  assume ?B
  then show ?A by auto
next
  assume ?A
  then obtain L where
    LC: \<open>Propagated L C \<in> set (get_trail_l S)\<close>
    by blast
  then have
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close> and
    L_w: \<open>L \<in> set (watched_l (get_clauses_l S \<propto> C))\<close> and
    L: \<open>length (get_clauses_l S \<propto> C) > 2 \<Longrightarrow> L = get_clauses_l S \<propto> C ! 0\<close>
    using list_invs C0 unfolding twl_list_invs_def by blast+
  have \<open>twl_st_inv T\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  then have le2: \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
    using C ST multi_member_split[OF C] unfolding twl_struct_invs_def
    by (cases S; cases T)
      (auto simp: twl_st_inv.simps twl_st_l_def
        image_Un[symmetric])
  show ?B
  proof (cases \<open>length (get_clauses_l S \<propto> C) > 2\<close>)
    case True
    show ?thesis
      using L True LC by auto
  next
    case False
    then show ?thesis
      using LC le2 L_w
      by (cases \<open>get_clauses_l S \<propto> C\<close>;
           cases \<open>tl (get_clauses_l S \<propto> C)\<close>)
        auto
  qed
qed

lemma trail_length_ge2:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    LaC: \<open>Propagated L C \<in> set (get_trail_l S)\<close> and
    C0: \<open>C > 0\<close>
  shows
    \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
proof -
  have conv:
   \<open>(get_trail_l S, get_trail T) \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
   using ST unfolding twl_st_l_def by auto

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of T)\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+

  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using ST lev_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st_l twl_st)
  have
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close>
    using list_invs C0 LaC by (auto simp: twl_list_invs_def all_conj_distrib)
  have \<open>twl_st_inv T\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  then show le2: \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
    using C ST multi_member_split[OF C] unfolding twl_struct_invs_def
    by (cases S; cases T)
      (auto simp: twl_st_inv.simps twl_st_l_def
        image_Un[symmetric])
qed

lemma is_annot_no_other_true_lit:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    C0: \<open>C > 0\<close> and
    LaC: \<open>Propagated La C \<in> set (get_trail_l S)\<close> and
    LC: \<open>L \<in> set (get_clauses_l S \<propto> C)\<close> and
    L: \<open>L \<in> lits_of_l (get_trail_l S)\<close>
  shows
    \<open>La = L\<close> and
    \<open>length (get_clauses_l S \<propto> C) > 2 \<Longrightarrow> L = get_clauses_l S \<propto> C ! 0\<close>
proof -
  have conv:
   \<open>(get_trail_l S, get_trail T) \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
   using ST unfolding twl_st_l_def by auto

  obtain M2 M1 where
    tr_S: \<open>get_trail_l S = M2 @ Propagated La C # M1\<close>
    using split_list[OF LaC] by blast
  then obtain M2' M1' where
    tr_T: \<open>get_trail T = M2' @ Propagated La (mset (get_clauses_l S \<propto> C)) # M1'\<close> and
    M2: \<open>(M2, M2') \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close> and
    M1: \<open>(M1, M1') \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
   using conv C0 by (auto simp: list_all2_append1 list_all2_append2 list_all2_Cons1 list_all2_Cons2
    convert_lits_l_def list_rel_def convert_lit.simps dest!: p2relD)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of T)\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>La \<in># mset (get_clauses_l S \<propto> C)\<close> and
    \<open>M1' \<Turnstile>as CNot (remove1_mset La (mset (get_clauses_l S \<propto> C)))\<close>
    using tr_T
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto 5 5 simp: twl_st twl_st_l)
  then have
    \<open>M1 \<Turnstile>as CNot (remove1_mset La (mset (get_clauses_l S \<propto> C)))\<close>
    using M1 convert_lits_l_true_clss_clss by blast
  then have all_false: \<open>-K \<in> lits_of_l (get_trail_l S)\<close>
    if \<open>K \<in># remove1_mset La (mset (get_clauses_l S \<propto> C))\<close>
    for K
    using that tr_S unfolding true_annots_true_cls_def_iff_negation_in_model
    by (auto dest!: multi_member_split)
  have La0: \<open>length (get_clauses_l S \<propto> C) > 2 \<Longrightarrow> La = get_clauses_l S \<propto> C ! 0\<close> and
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close> and
    \<open>La \<in> set (watched_l (get_clauses_l S \<propto> C))\<close>
    using list_invs tr_S C0 by (auto simp: twl_list_invs_def all_conj_distrib)
  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using ST lev_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st_l twl_st)
  show \<open>La = L\<close>
  proof (rule ccontr)
    assume \<open>\<not>?thesis\<close>
    then have \<open>L \<in># remove1_mset La (mset (get_clauses_l S \<propto> C))\<close>
      using LC by auto
    from all_false[OF this] show False
      using L n_d by (auto dest: no_dup_consistentD)
  qed
  then show \<open>length (get_clauses_l S \<propto> C) > 2 \<Longrightarrow> L = get_clauses_l S \<propto> C ! 0\<close>
    using La0 by simp
qed

lemma remove_one_annot_true_clause_cdcl_twl_restart_l2:
  assumes
    rem: \<open>remove_one_annot_true_clause S T\<close> and
    lst_invs: \<open>twl_list_invs S\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    n_d: \<open>(S, T') \<in> twl_st_l None\<close> \<open>twl_struct_invs T'\<close>
  shows \<open>cdcl_twl_restart_l S T\<close>
proof -
  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using n_d unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st twl_st_l)

  show ?thesis
    apply (rule remove_one_annot_true_clause_cdcl_twl_restart_l[OF _ _ \<open>(S, T') \<in> twl_st_l None\<close>])
    subgoal using rem .
    subgoal using lst_invs .
    subgoal using \<open>twl_struct_invs T'\<close> .
    subgoal using confl .
    subgoal using upd .
    subgoal using n_d .
    done
qed

lemma remove_one_annot_true_clause_get_conflict_l:
  \<open>remove_one_annot_true_clause S T \<Longrightarrow> get_conflict_l T = get_conflict_l S\<close>
  by (auto simp: remove_one_annot_true_clause.simps)

lemma rtranclp_remove_one_annot_true_clause_get_conflict_l:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> get_conflict_l T = get_conflict_l S\<close>
  by (induction rule: rtranclp_induct) (auto simp: remove_one_annot_true_clause_get_conflict_l)

lemma remove_one_annot_true_clause_clauses_to_update_l:
  \<open>remove_one_annot_true_clause S T \<Longrightarrow> clauses_to_update_l T = clauses_to_update_l S\<close>
  by (auto simp: remove_one_annot_true_clause.simps)

lemma rtranclp_remove_one_annot_true_clause_clauses_to_update_l:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> clauses_to_update_l T = clauses_to_update_l S\<close>
  by (induction rule: rtranclp_induct) (auto simp: remove_one_annot_true_clause_clauses_to_update_l)

lemma cdcl_twl_restart_l_invs:
  assumes ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and \<open>cdcl_twl_restart_l S S'\<close>
  shows \<open>\<exists>T'. (S', T') \<in> twl_st_l None \<and> twl_list_invs S' \<and>
         clauses_to_update_l S' = {#} \<and> cdcl_twl_restart T T' \<and> twl_struct_invs T'\<close>
  using cdcl_twl_restart_l_cdcl_twl_restart[OF ST list_invs struct_invs]
  cdcl_twl_restart_twl_struct_invs[OF _ struct_invs]
  by (smt RETURN_ref_SPECD RETURN_rule assms(4) in_pair_collect_simp order_trans)


lemma rtranclp_cdcl_twl_restart_l_invs:
  assumes
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S S'\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>\<exists>T'. (S', T') \<in> twl_st_l None \<and> twl_list_invs S' \<and>
         clauses_to_update_l S' = {#} \<and> cdcl_twl_restart\<^sup>*\<^sup>* T T' \<and> twl_struct_invs T'\<close>
  using assms(1)
  apply (induction rule: rtranclp_induct)
  subgoal
    using assms(2-) apply - by (rule exI[of _ T]) auto
  subgoal for T U
    using cdcl_twl_restart_l_invs[of T _ U] assms
    by (meson rtranclp.rtrancl_into_rtrancl)
  done


lemma rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2:
  assumes
    rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close> and
    lst_invs: \<open>twl_list_invs S\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    n_d: \<open>(S, S') \<in> twl_st_l None\<close> \<open>twl_struct_invs S'\<close>
  shows \<open>\<exists>T'. cdcl_twl_restart_l\<^sup>*\<^sup>* S T \<and> (T, T') \<in> twl_st_l None \<and> cdcl_twl_restart\<^sup>*\<^sup>* S' T' \<and>
    twl_struct_invs T'\<close>
  using rem
proof (induction)
  case base
  then show ?case
    using assms apply - by (rule_tac x=S' in exI) auto
next
  case (step U V) note st = this(1) and step = this(2) and IH = this(3)
  obtain U' where
    IH: \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S U\<close> and
    UT': \<open>(U, U') \<in> twl_st_l None\<close> and
    S'U': \<open>cdcl_twl_restart\<^sup>*\<^sup>* S' U'\<close>
    using IH by blast
  have \<open>twl_list_invs U\<close>
    using rtranclp_cdcl_twl_restart_l_list_invs[OF IH lst_invs] .
  have \<open>get_conflict_l U = None\<close>
    using rtranclp_remove_one_annot_true_clause_get_conflict_l[OF st] confl
    by auto
  have \<open>clauses_to_update_l U = {#}\<close>
    using rtranclp_remove_one_annot_true_clause_clauses_to_update_l[OF st] upd
    by auto
  have \<open>twl_struct_invs U'\<close>
      by (metis (no_types, hide_lams) \<open>cdcl_twl_restart\<^sup>*\<^sup>* S' U'\<close>
          cdcl_twl_restart_twl_struct_invs n_d(2) rtranclp_induct)
  have \<open>cdcl_twl_restart_l U V\<close>
    apply (rule remove_one_annot_true_clause_cdcl_twl_restart_l2[of _ _ U'])
    subgoal using step .
    subgoal using \<open>twl_list_invs U\<close> .
    subgoal using \<open>get_conflict_l U = None\<close> .
    subgoal using \<open>clauses_to_update_l U = {#}\<close> .
    subgoal using UT' .
    subgoal using \<open>twl_struct_invs U'\<close> .
    done
  moreover obtain V' where
    UT': \<open>(V, V') \<in> twl_st_l None\<close> and
    \<open>cdcl_twl_restart U' V'\<close> and
    \<open>twl_struct_invs V'\<close>
    using cdcl_twl_restart_l_invs[OF UT' _ _  \<open>cdcl_twl_restart_l U V\<close>] \<open>twl_list_invs U\<close>
      \<open>twl_struct_invs U'\<close>
    by blast
  ultimately show ?case
    using S'U' IH by fastforce
qed

definition drop_clause_add_move_init where
  \<open>drop_clause_add_move_init = (\<lambda>(M, N0, D, NE0, UE, NS, US, Q, W) C.
     (M, fmdrop C N0, D, add_mset (mset (N0 \<propto> C)) NE0, UE, NS, {#}, Q, W))\<close>

lemma [simp]:
  \<open>get_trail_l (drop_clause_add_move_init V C) = get_trail_l V\<close>
  by (cases V) (auto simp: drop_clause_add_move_init_def)

definition drop_clause where
  \<open>drop_clause = (\<lambda>(M, N0, D, NE0, UE, NS, US, Q, W) C.
     (M, fmdrop C N0, D, NE0, UE, NS, {#}, Q, W))\<close>

lemma [simp]:
  \<open>get_trail_l (drop_clause V C) = get_trail_l V\<close>
  by (cases V) (auto simp: drop_clause_def)

definition remove_all_annot_true_clause_one_imp
where
\<open>remove_all_annot_true_clause_one_imp = (\<lambda>(C, S). do {
      if C \<in># dom_m (get_clauses_l S) then
        if irred (get_clauses_l S) C
        then RETURN (drop_clause_add_move_init S C)
        else RETURN (drop_clause S C)
      else do {
        RETURN S
      }
  })\<close>

definition remove_one_annot_true_clause_imp_inv where
  \<open>remove_one_annot_true_clause_imp_inv S =
    (\<lambda>(i, T). remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<and> twl_list_invs S \<and> i \<le> length (get_trail_l S) \<and>
      twl_list_invs S \<and>
      clauses_to_update_l S = clauses_to_update_l T \<and>
      literals_to_update_l S = literals_to_update_l T \<and>
      get_conflict_l T = None \<and>
      (\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S') \<and>
      get_conflict_l S = None \<and> clauses_to_update_l S = {#} \<and>
      length (get_trail_l S) = length (get_trail_l T) \<and>
      (\<forall>j<i. is_proped (rev (get_trail_l T) ! j) \<and> mark_of (rev (get_trail_l T) ! j) = 0))\<close>


definition remove_all_annot_true_clause_imp_inv where
  \<open>remove_all_annot_true_clause_imp_inv S xs =
    (\<lambda>(i, T). remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<and> twl_list_invs S \<and> i \<le> length xs \<and>
           twl_list_invs S \<and> get_trail_l S = get_trail_l T \<and>
           (\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S') \<and>
           get_conflict_l S = None \<and> clauses_to_update_l S = {#})\<close>

definition remove_all_annot_true_clause_imp_pre where
  \<open>remove_all_annot_true_clause_imp_pre L S \<longleftrightarrow>
    (twl_list_invs S \<and> twl_list_invs S \<and>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S') \<and>
    get_conflict_l S = None \<and> clauses_to_update_l S = {#} \<and> L \<in> lits_of_l (get_trail_l S))\<close>

definition remove_all_annot_true_clause_imp
  :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> ('v twl_st_l) nres\<close>
where
\<open>remove_all_annot_true_clause_imp = (\<lambda>L S. do {
    ASSERT(remove_all_annot_true_clause_imp_pre L S);
    xs \<leftarrow> SPEC(\<lambda>xs.
       (\<forall>x\<in>set xs. x \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set ((get_clauses_l S)\<propto>x)));
    (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, T). remove_all_annot_true_clause_imp_inv S xs (i, T)\<^esup>
      (\<lambda>(i, T). i < length xs)
      (\<lambda>(i, T). do {
          ASSERT(i < length xs);
          if xs!i \<in># dom_m (get_clauses_l T) \<and> length ((get_clauses_l T) \<propto> (xs!i)) \<noteq> 2
          then do {
            T \<leftarrow> remove_all_annot_true_clause_one_imp (xs!i, T);
            ASSERT(remove_all_annot_true_clause_imp_inv S xs (i, T));
            RETURN (i+1, T)
          }
          else
            RETURN (i+1, T)
      })
      (0, S);
    RETURN T
  })\<close>

definition remove_one_annot_true_clause_one_imp_pre where
  \<open>remove_one_annot_true_clause_one_imp_pre i T \<longleftrightarrow>
    (twl_list_invs T \<and> i < length (get_trail_l T) \<and>
           twl_list_invs T \<and>
           (\<exists>S'. (T, S') \<in> twl_st_l None \<and> twl_struct_invs S') \<and>
           get_conflict_l T = None \<and> clauses_to_update_l T = {#})\<close>

definition replace_annot_l_pre :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>replace_annot_l_pre L C S \<longleftrightarrow>
   Propagated L C \<in> set (get_trail_l S) \<and> C > 0 \<and>
   (\<exists>i. remove_one_annot_true_clause_one_imp_pre i S)\<close>

lemma replace_annot_l_pre_alt_def:
  \<open>replace_annot_l_pre L C S \<longleftrightarrow>
   (Propagated L C \<in> set (get_trail_l S) \<and> C > 0 \<and>
   (\<exists>i. remove_one_annot_true_clause_one_imp_pre i S)) \<and>
   L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S +
       get_subsumed_init_clauses_l S)\<close>
   (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S +
       get_subsumed_init_clauses_l S)\<close>
    if pre: \<open>replace_annot_l_pre L C S\<close> and LC: \<open>Propagated L C \<in> set (get_trail_l S)\<close>
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct: \<open>twl_struct_invs T\<close> and
      \<open>get_conflict_l S = None\<close>
      using pre unfolding replace_annot_l_pre_def
        remove_one_annot_true_clause_one_imp_pre_def
      by fast
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close>
      using struct unfolding twl_struct_invs_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then show \<open>?thesis\<close>
      using ST LC unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: twl_st twl_st_l in_all_lits_of_mm_ain_atms_of_iff
         lits_of_def image_image)
  qed
  then show \<open>?thesis\<close>
    by (auto simp: replace_annot_l_pre_def)
qed

definition replace_annot_l where
  \<open>replace_annot_l L C =
    (\<lambda>(M, N, D, NE, UE, NS, US, Q, W). do {
      ASSERT(replace_annot_l_pre L C (M, N, D, NE, UE, NS, US, Q, W));
      RES {(M', N, D, NE, UE, NS, {#}, Q, W)| M'.
       (\<exists>M2 M1 C. M = M2 @ Propagated L C # M1 \<and> M' = M2 @ Propagated L 0 # M1)}
   })\<close>

definition remove_and_add_cls_l :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>remove_and_add_cls_l C =
    (\<lambda>(M, N, D, NE, UE, NS, US, Q, W). do {
       ASSERT(C \<in># dom_m N);
        RETURN (M, fmdrop C N, D,
         (if irred N C then add_mset (mset (N\<propto>C)) else id) NE,
	 (if \<not>irred N C then add_mset (mset (N\<propto>C)) else id) UE, NS, {#}, Q, W)
    })\<close>

text \<open>The following progrom removes all clauses that are annotations. However, this is not compatible
with special handling of binary clauses, since we want to make sure that they should not been deleted.
\<close>
definition remove_one_annot_true_clause_one_imp :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> (nat \<times> 'v twl_st_l) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp = (\<lambda>i S. do {
      ASSERT(remove_one_annot_true_clause_one_imp_pre i S);
      ASSERT(is_proped ((rev (get_trail_l S))!i));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev (get_trail_l S))!i = Propagated L C);
      ASSERT(Propagated L C \<in> set (get_trail_l S));
      if C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<in># dom_m (get_clauses_l S));
	S \<leftarrow> replace_annot_l L C S;
	S \<leftarrow> remove_and_add_cls_l C S;
        \<^cancel>\<open>S \<leftarrow> remove_all_annot_true_clause_imp L S;\<close>
        RETURN (i+1, S)
      }
  })\<close>

definition remove_all_learned_subsumed_clauses :: \<open>'v twl_st_l \<Rightarrow> ('v twl_st_l) nres\<close> where
\<open>remove_all_learned_subsumed_clauses = (\<lambda>(M, N, D, NE, UE, NS, US, Q, W).
   RETURN (M, N, D, NE, UE, NS, {#}, Q, W))\<close>


lemma decomp_nth_eq_lit_eq:
  assumes
    \<open>M = M2 @ Propagated L C' # M1\<close> and
    \<open>rev M ! i = Propagated L C\<close> and
    \<open>no_dup M\<close> and
    \<open>i < length M\<close>
  shows \<open>length M1 = i\<close> and \<open>C = C'\<close>
proof -
  have [simp]: \<open>defined_lit M1 (lit_of (M1 ! i))\<close> if \<open>i < length M1\<close> for i
    using that by (simp add: in_lits_of_l_defined_litD lits_of_def)
  have[simp]: \<open>undefined_lit M2 L \<Longrightarrow>
       k < length M2 \<Longrightarrow>
       M2 ! k \<noteq> Propagated L C\<close> for k
    using defined_lit_def nth_mem by fastforce
  have[simp]: \<open>undefined_lit M1 L \<Longrightarrow>
       k < length M1 \<Longrightarrow>
       M1 ! k \<noteq> Propagated L C\<close> for k
    using defined_lit_def nth_mem by fastforce
  have \<open>M ! (length M - Suc i) \<in> set M\<close>
    apply (rule nth_mem)
    using assms by auto
  from split_list[OF this] show \<open>length M1 = i\<close> and \<open>C = C'\<close>
    using assms
    by (auto simp: nth_append nth_Cons nth_rev split: if_splits nat.splits
      elim!: list_match_lel_lel)
qed

lemma
  assumes \<open>remove_one_annot_true_clause_imp_inv S s\<close> and
    s[simp]: \<open>s = (i, U)\<close>
  shows
    remove_all_learned_subsumed_clauses_cdcl_twl_restart_l:
      \<open>remove_all_learned_subsumed_clauses U \<le> SPEC(\<lambda>U'. cdcl_twl_restart_l U U' \<and>
        get_trail_l U = get_trail_l U')\<close> (is ?A) and
    remove_one_annot_true_clause_imp_inv_no_dupD:
      \<open>no_dup (get_trail_l U)\<close> and
    remove_one_annot_true_clause_imp_inv_no_dupD2:
      \<open>no_dup (get_trail_l S)\<close>
proof -
  obtain x where
    SU: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    \<open>i \<le> length (get_trail_l S)\<close> and
    \<open>twl_list_invs S\<close> and
    clss_upd_U: \<open>clauses_to_update_l S = clauses_to_update_l U\<close> and
    \<open>literals_to_update_l S = literals_to_update_l U\<close> and
    conflU: \<open>get_conflict_l U = None\<close> and
    conflS: \<open>get_conflict_l S = None\<close> and
    Sx: \<open>(S, x) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs x\<close> and
    clss_upd_S:  \<open>clauses_to_update_l S = {#}\<close> and
    \<open>length (get_trail_l S) = length (get_trail_l U)\<close> and
    \<open>\<forall>j<i. is_proped (rev (get_trail_l U) ! j) \<and>
              mark_of (rev (get_trail_l U) ! j) = 0\<close>
    using assms
    unfolding remove_all_learned_subsumed_clauses_def
      remove_one_annot_true_clause_imp_inv_def prod.case
    by blast
  obtain T' where
    list_invs_U: \<open>twl_list_invs U\<close> and
    UT': \<open>(U, T') \<in> twl_st_l None\<close> and
    xT': \<open>cdcl_twl_restart\<^sup>*\<^sup>* x T'\<close>
    using rtranclp_cdcl_twl_restart_l_list_invs[of S U, OF _ list_invs]
      rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF SU list_invs
        conflS clss_upd_S Sx struct_invs]
    by auto
  have 1: \<open>Propagated L E \<in> set (get_trail_l U) \<Longrightarrow> 0 < E \<Longrightarrow> E \<in># dom_m (get_clauses_l U)\<close>
    \<open>0 \<notin># dom_m (get_clauses_l U)\<close> for E L
    using list_invs_U
    unfolding twl_list_invs_def
    by auto
  have \<open>twl_struct_invs T'\<close>
    using rtranclp_cdcl_twl_restart_twl_struct_invs struct_invs xT' by blast
  then show \<open>no_dup (get_trail_l U)\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    using UT' by (simp add: twl_st)
  from no_dup_same_annotD[OF this]
  show ?A
    using clss_upd_U conflU 1 unfolding clss_upd_S
    unfolding remove_all_learned_subsumed_clauses_def
    by (refine_rcg)
      (auto simp: cdcl_twl_restart_l.simps)
   show \<open>no_dup (get_trail_l S)\<close>
     using Sx struct_invs
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: twl_st)
qed


definition remove_one_annot_true_clause_imp :: \<open>'v twl_st_l \<Rightarrow> ('v twl_st_l) nres\<close>
where
\<open>remove_one_annot_true_clause_imp = (\<lambda>S. do {
    k \<leftarrow> SPEC(\<lambda>k. (\<exists>M1 M2 K. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S)) \<and>
        count_decided M1 = 0 \<and> k = length M1)
      \<or> (count_decided (get_trail_l S) = 0 \<and> k = length (get_trail_l S)));
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_inv S\<^esup>
      (\<lambda>(i, S). i < k)
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp i S)
      (0, S);
    remove_all_learned_subsumed_clauses S
  })\<close>


lemma remove_one_annot_true_clause_imp_same_length:
   \<open>remove_one_annot_true_clause S T \<Longrightarrow> length (get_trail_l S) = length (get_trail_l T)\<close>
  by (induction rule: remove_one_annot_true_clause.induct) (auto simp: )

lemma rtranclp_remove_one_annot_true_clause_imp_same_length:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<Longrightarrow> length (get_trail_l S) = length (get_trail_l T)\<close>
  by (induction rule: rtranclp_induct) (auto simp: remove_one_annot_true_clause_imp_same_length)

lemma remove_one_annot_true_clause_map_is_decided_trail:
  \<open>remove_one_annot_true_clause S U \<Longrightarrow>
   map is_decided (get_trail_l S) = map is_decided (get_trail_l U)\<close>
  by (induction rule: remove_one_annot_true_clause.induct)
    auto

lemma remove_one_annot_true_clause_map_mark_of_same_or_0:
  \<open>remove_one_annot_true_clause S U \<Longrightarrow>
   mark_of (get_trail_l S ! i) = mark_of (get_trail_l U ! i) \<or> mark_of (get_trail_l U ! i) = 0\<close>
  by (induction rule: remove_one_annot_true_clause.induct)
    (auto simp: nth_append nth_Cons split: nat.split)

lemma remove_one_annot_true_clause_imp_inv_trans:
 \<open>remove_one_annot_true_clause_imp_inv S (i, T) \<Longrightarrow> remove_one_annot_true_clause_imp_inv T U \<Longrightarrow>
  remove_one_annot_true_clause_imp_inv S U\<close>
  using rtranclp_remove_one_annot_true_clause_imp_same_length[of S T]
  by (auto simp: remove_one_annot_true_clause_imp_inv_def)

lemma rtranclp_remove_one_annot_true_clause_map_is_decided_trail:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U \<Longrightarrow>
   map is_decided (get_trail_l S) = map is_decided (get_trail_l U)\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: remove_one_annot_true_clause_map_is_decided_trail)

lemma rtranclp_remove_one_annot_true_clause_map_mark_of_same_or_0:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U \<Longrightarrow>
   mark_of (get_trail_l S ! i) = mark_of (get_trail_l U ! i) \<or> mark_of (get_trail_l U ! i) = 0\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: remove_one_annot_true_clause_map_mark_of_same_or_0)

lemma remove_one_annot_true_clause_map_lit_of_trail:
  \<open>remove_one_annot_true_clause S U \<Longrightarrow>
   map lit_of (get_trail_l S) = map lit_of (get_trail_l U)\<close>
  by (induction rule: remove_one_annot_true_clause.induct)
    auto

lemma rtranclp_remove_one_annot_true_clause_map_lit_of_trail:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U \<Longrightarrow>
   map lit_of (get_trail_l S) = map lit_of (get_trail_l U)\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: remove_one_annot_true_clause_map_lit_of_trail)

lemma remove_one_annot_true_clause_reduce_dom_clauses:
  \<open>remove_one_annot_true_clause S U \<Longrightarrow>
   reduce_dom_clauses (get_clauses_l S) (get_clauses_l U)\<close>
  by (induction rule: remove_one_annot_true_clause.induct)
    auto

lemma rtranclp_remove_one_annot_true_clause_reduce_dom_clauses:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U \<Longrightarrow>
   reduce_dom_clauses (get_clauses_l S) (get_clauses_l U)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: remove_one_annot_true_clause_reduce_dom_clauses intro: reduce_dom_clauses_trans)

lemma remove_one_annot_true_clause_imp_inv_spec:
  assumes
    annot: \<open>remove_one_annot_true_clause_imp_inv S (i+1, U)\<close> and
    i_le: \<open>i < length (get_trail_l S)\<close> and
    L: \<open>L \<in> lits_of_l (get_trail_l S)\<close> and
    lev0: \<open>get_level (get_trail_l S) L = 0\<close> and
    LC: \<open>Propagated L 0 \<in> set (get_trail_l U)\<close>
  shows \<open>remove_all_annot_true_clause_imp L U
    \<le> SPEC (\<lambda>Sa. RETURN (i + 1, Sa)
                 \<le> SPEC (\<lambda>s'. remove_one_annot_true_clause_imp_inv S s' \<and>
                              (s', (i, T))
                              \<in> measure
                                 (\<lambda>(i, _). length (get_trail_l S) - i)))\<close>
proof -

  obtain M N D NE UE WS NS US Q where
    U: \<open>U = (M, N, D, NE, UE, NS, US, WS, Q)\<close>
    by (cases U)
  obtain x where
    SU: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S (M, N, D, NE, UE, NS, US, WS, Q)\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>i + 1 \<le> length (get_trail_l S)\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>get_conflict_l S = None\<close> and
    \<open>(S, x) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs x\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    level0: \<open>\<forall>j<i + 1. is_proped (rev (get_trail_l (M, N, D, NE, UE, NS, US, WS, Q)) ! j)\<close>and
    mark0: \<open>\<forall>j<i + 1. mark_of (rev (get_trail_l (M, N, D, NE, UE, NS, US, WS, Q)) ! j) = 0\<close>
    using annot unfolding U prod.case remove_one_annot_true_clause_imp_inv_def
    by blast
  obtain U' where
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S U\<close> and
    U'V': \<open>(U, U') \<in> twl_st_l None\<close> and
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* x U'\<close> and
    struvt_invs_V': \<open>twl_struct_invs U'\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF SU \<open>twl_list_invs S\<close>
        \<open>get_conflict_l S = None\<close> \<open>clauses_to_update_l S = {#}\<close> \<open>(S, x) \<in> twl_st_l None\<close>
          \<open>twl_struct_invs x\<close>] unfolding U
    by auto
  moreover have \<open>twl_list_invs U\<close>
    using \<open>twl_list_invs S\<close> calculation(1) rtranclp_cdcl_twl_restart_l_list_invs by blast
  ultimately have rem_U_U: \<open>remove_one_annot_true_clause_imp_inv U (i + 1, U)\<close>
    using level0 rtranclp_remove_one_annot_true_clause_clauses_to_update_l[OF SU]
      rtranclp_remove_one_annot_true_clause_get_conflict_l[OF SU] mark0
      \<open>clauses_to_update_l S = {#}\<close> \<open>get_conflict_l S = None\<close> i_le
      arg_cong[OF rtranclp_remove_one_annot_true_clause_map_lit_of_trail[OF SU], of length]
    unfolding remove_one_annot_true_clause_imp_inv_def unfolding U
    by (cases U') fastforce
  then have rem_true_U_U: \<open>remove_all_annot_true_clause_imp_inv U xs (0, U)\<close> for xs
    using level0 rtranclp_remove_one_annot_true_clause_clauses_to_update_l[OF SU]
      rtranclp_remove_one_annot_true_clause_get_conflict_l[OF SU]  \<open>twl_list_invs U\<close>
      \<open>clauses_to_update_l S = {#}\<close> \<open>get_conflict_l S = None\<close> i_le
      arg_cong[OF rtranclp_remove_one_annot_true_clause_map_lit_of_trail[OF SU], of length]
    unfolding U remove_all_annot_true_clause_imp_inv_def remove_one_annot_true_clause_imp_inv_def
    by (cases U') blast
  moreover have L_M: \<open>L \<in> lits_of_l M\<close>
      using L arg_cong[OF rtranclp_remove_one_annot_true_clause_map_lit_of_trail[OF SU], of set]
      by (simp add: lits_of_def)
  ultimately have pre: \<open>remove_all_annot_true_clause_imp_pre L U\<close>
    unfolding remove_all_annot_true_clause_imp_pre_def remove_all_annot_true_clause_imp_inv_def
      prod.case U by force

  have remove_all_annot_true_clause_one_imp:
    \<open>remove_all_annot_true_clause_one_imp (xs ! k, V)
	\<le> SPEC
	   (\<lambda>T. do {
		  _ \<leftarrow> ASSERT (remove_all_annot_true_clause_imp_inv U xs (k, T));
		  RETURN (k + 1, T)
		} \<le> SPEC
		     (\<lambda>s'. (case s' of
			    (i, T) \<Rightarrow>
			      remove_all_annot_true_clause_imp_inv U xs (i, T)) \<and>
			   (case s' of
			    (uu_, W) \<Rightarrow>
			      remove_one_annot_true_clause_imp_inv U (i + 1, W)) \<and>
			   (s', s) \<in> measure (\<lambda>(i, _). length xs - i)))\<close>
    if
      xs: \<open>xs \<in> {xs.
	     \<forall>x\<in>set xs.
		x \<in># dom_m (get_clauses_l U) \<longrightarrow> L \<in> set (get_clauses_l U \<propto> x)}\<close> and
      I': \<open>case s of (i, T) \<Rightarrow> remove_all_annot_true_clause_imp_inv U xs (i, T)\<close> and
      I: \<open>case s of (uu_, W) \<Rightarrow> remove_one_annot_true_clause_imp_inv U (i + 1, W)\<close> and
      cond: \<open>case s of (i, T) \<Rightarrow> i < length xs\<close> and
      s: \<open>s = (k, V)\<close> and
      k_le: \<open>k < length xs\<close> and
      dom: \<open>xs ! k \<in># dom_m (get_clauses_l V) \<and>
       length (get_clauses_l V \<propto> (xs ! k)) \<noteq> 2\<close>
      for s k V xs
  proof -
    obtain x where
      UU': \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* U V\<close> and
      i_le: \<open>i + 1 \<le> length (get_trail_l U)\<close> and
      list_invs: \<open>twl_list_invs U\<close> and
      confl: \<open>get_conflict_l U = None\<close> and
      Ux: \<open>(U, x) \<in> twl_st_l None\<close> and
      struct_x: \<open>twl_struct_invs x\<close> and
      upd: \<open>clauses_to_update_l U = {#}\<close> and
      all_level0: \<open>\<forall>j<i + 1. is_proped (rev (get_trail_l V) ! j)\<close> and
      all_mark0: \<open>\<forall>j<i + 1. mark_of (rev (get_trail_l V) ! j) = 0\<close> and
      lits_upd: \<open>literals_to_update_l U = literals_to_update_l V\<close> and
      clss_upd: \<open>clauses_to_update_l U = clauses_to_update_l V\<close> and
      confl_V: \<open>get_conflict_l V = None\<close> and
      tr: \<open>get_trail_l U = get_trail_l V\<close>
      using I' I unfolding s prod.case remove_one_annot_true_clause_imp_inv_def
        remove_all_annot_true_clause_imp_inv_def
      by blast
    have n_d: \<open>no_dup (get_trail_l U)\<close>
      using Ux struct_x unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        by (auto simp: twl_st twl_st_l)
    have SU': \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S V\<close>
      using SU UU' unfolding U by simp
    have \<open>get_level M L = 0\<close>
      using lev0 rtranclp_remove_one_annot_true_clause_map_is_decided_trail[OF SU]
        rtranclp_remove_one_annot_true_clause_map_lit_of_trail[OF SU]
        U trail_renumber_get_level[of \<open>get_trail_l S\<close> \<open>get_trail_l U\<close> L]
	by force
    have red: \<open>reduce_dom_clauses (get_clauses_l U) (get_clauses_l V)\<close>
      using rtranclp_remove_one_annot_true_clause_reduce_dom_clauses[OF UU'] unfolding U
      by simp
    then have [simp]: \<open>N \<propto> (xs ! k) = get_clauses_l V \<propto> (xs ! k)\<close> and
      dom_VU: \<open>\<And>C. C \<in># dom_m (get_clauses_l V) \<longrightarrow> C \<in># dom_m (get_clauses_l U)\<close>
      using dom unfolding reduce_dom_clauses_def U by simp_all
    obtain V' where
      \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* U V\<close> and
      U'V': \<open>(V, V') \<in> twl_st_l None\<close> and
      \<open>cdcl_twl_restart\<^sup>*\<^sup>* x V'\<close> and
      struvt_invs_V': \<open>twl_struct_invs V'\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF UU' \<open>twl_list_invs U\<close>
          \<open>get_conflict_l U = None\<close> \<open>clauses_to_update_l U = {#}\<close> \<open>(U, x) \<in> twl_st_l None\<close>
           \<open>twl_struct_invs x\<close>]
      by auto
    have list_invs_U': \<open>twl_list_invs V\<close>
      using \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* U V\<close> \<open>twl_list_invs U\<close>
        rtranclp_cdcl_twl_restart_l_list_invs by blast

    have dom_N: \<open>xs ! k \<in># dom_m (get_clauses_l V)\<close>
      using dom red unfolding s
      by (auto simp del: nth_mem simp: reduce_dom_clauses_def)

    have xs_k_0: \<open>0 < xs ! k\<close>
      apply (rule ccontr)
      using dom list_invs_U' by (auto simp: twl_list_invs_def)
    have L_set: \<open>L \<in> set (get_clauses_l V \<propto> (xs!k))\<close>
      using xs cond nth_mem[of k xs] dom_N dom_VU[of \<open>xs!k\<close>] unfolding s U
      by (auto simp del: nth_mem)
    have \<open>no_dup M\<close>
      using n_d unfolding U by simp
    then have no_already_annot: \<open>Propagated Laa (xs ! k) \<in> set (get_trail_l V) \<Longrightarrow> False\<close> for Laa
      using is_annot_iff_annotates_first[OF U'V' list_invs_U' struvt_invs_V' xs_k_0] LC
      is_annot_no_other_true_lit[OF U'V' list_invs_U' struvt_invs_V' xs_k_0, of Laa L]
        L_set L_M xs_k_0 tr unfolding U
      by (auto dest: no_dup_same_annotD)
    let ?U' = \<open>(M, N, D, NE, UE, NS, US, WS, Q)\<close>
    have V: \<open>V = (M, get_clauses_l V, D, get_unit_init_clauses_l V,
      get_unit_learned_clss_l V, get_subsumed_init_clauses_l V,
      get_subsumed_learned_clauses_l V, WS, Q)\<close>
      using confl upd lits_upd tr clss_upd confl_V unfolding U
      by (cases V) auto
    let ?V = \<open>(M, N, D, NE, UE, NS, US, WS, Q)\<close>
    let ?Vt = \<open>drop_clause_add_move_init V (xs!k)\<close>
    let ?Vf = \<open>drop_clause V (xs!k)\<close>
    have \<open>remove_one_annot_true_clause V ?Vt\<close>
      if \<open>irred (get_clauses_l V) (xs ! k)\<close>
      apply (subst (2) V)
      apply (subst V)
      unfolding drop_clause_add_move_init_def prod.case
      apply (rule remove_one_annot_true_clause.remove_irred[of L])
      subgoal using \<open>L \<in> lits_of_l M\<close> .
      subgoal using \<open>get_level M L = 0\<close> .
      subgoal using dom by simp
      subgoal using L_set by auto
      subgoal using that .
      subgoal using no_already_annot tr unfolding U by auto
      done
    then have UV_irred: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* U ?Vt\<close>
      if \<open>irred (get_clauses_l V) (xs ! k)\<close>
      using UU' that by simp
    have \<open>remove_one_annot_true_clause V ?Vf\<close>
      if \<open>\<not>irred (get_clauses_l V) (xs ! k)\<close>
      apply (subst (2) V)
      apply (subst V)
      unfolding drop_clause_def prod.case
      apply (rule remove_one_annot_true_clause.delete)
      subgoal using dom by simp
      subgoal using that .
      subgoal using no_already_annot tr unfolding U by auto
      done
    then have UV_red: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* U ?Vf\<close>
      if \<open>\<not>irred (get_clauses_l V) (xs ! k)\<close>
      using UU' that by simp
    have i_le: \<open>Suc i \<le> length M\<close>
      using annot assms(2) unfolding U remove_one_annot_true_clause_imp_inv_def
      by auto
    have 1: \<open>remove_one_annot_true_clause_imp_inv U (Suc i, ?Vt)\<close>
      if \<open>irred (get_clauses_l V) (xs ! k)\<close>
      using UV_irred that \<open>twl_list_invs U\<close> i_le all_level0 all_mark0
          \<open>get_conflict_l U = None\<close> \<open>clauses_to_update_l U = {#}\<close> \<open>(U, x) \<in> twl_st_l None\<close>
           \<open>twl_struct_invs x\<close> unfolding U
      unfolding remove_one_annot_true_clause_imp_inv_def prod.case
      apply (intro conjI)
      subgoal by auto
      subgoal by auto
      subgoal using i_le by auto
      subgoal using tr by (cases V) (auto simp: drop_clause_add_move_init_def U)
      subgoal using clss_upd by (cases V) (auto simp: drop_clause_add_move_init_def U)
      subgoal using lits_upd by (cases V) (auto simp: drop_clause_add_move_init_def U)
      subgoal using confl_V by (cases V) (auto simp: drop_clause_add_move_init_def U)
      subgoal by blast
      subgoal by auto
      subgoal by auto
      subgoal using tr by (cases V) (auto simp: drop_clause_add_move_init_def U)
      subgoal using tr by (cases V) (auto simp: drop_clause_add_move_init_def U)
      done
    have 2: \<open>remove_one_annot_true_clause_imp_inv U (Suc i, ?Vf)\<close>
      if \<open>\<not>irred (get_clauses_l V) (xs ! k)\<close>
      using UV_red that  \<open>twl_list_invs U\<close> i_le all_level0 all_mark0
          \<open>get_conflict_l U = None\<close> \<open>clauses_to_update_l U = {#}\<close> \<open>(U, x) \<in> twl_st_l None\<close>
           \<open>twl_struct_invs x\<close> unfolding U
      unfolding remove_one_annot_true_clause_imp_inv_def prod.case
      apply (intro conjI)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal using tr by (cases V) (auto simp: drop_clause_def U)
      subgoal using clss_upd by (cases V) (auto simp: drop_clause_def U)
      subgoal using lits_upd by (cases V) (auto simp: drop_clause_def U)
      subgoal using confl_V by (cases V) (auto simp: drop_clause_def U)
      subgoal by blast
      subgoal by auto
      subgoal by auto
      subgoal using tr by (cases V) (auto simp: drop_clause_def U)
      subgoal using tr by (cases V) (auto simp: drop_clause_def U)
      done
    have \<open>remove_all_annot_true_clause_imp_inv U xs
             (k, ?Vt)\<close>
      if \<open>irred (get_clauses_l V) (xs ! k)\<close>
    proof -
      have "\<exists>p. (U, p) \<in> twl_st_l None \<and> twl_struct_invs p"
	using Ux struct_x
	by meson
      then show ?thesis
	using that Ux struct_x list_invs i_le confl upd UV_irred cond tr
	unfolding remove_all_annot_true_clause_imp_inv_def prod.case s
	by (simp add: less_imp_le_nat)
    qed
    moreover have \<open>remove_all_annot_true_clause_imp_inv U xs
             (k, ?Vf)\<close>
      if \<open>\<not>irred (get_clauses_l V) (xs ! k)\<close>
    proof -
      have "\<exists>p. (U, p) \<in> twl_st_l None \<and> twl_struct_invs p"
	using Ux struct_x
	by meson
      then show ?thesis
	using that Ux struct_x list_invs i_le confl upd  UV_red cond tr
	unfolding remove_all_annot_true_clause_imp_inv_def prod.case
	by (simp add: less_imp_le_nat s)
    qed
    ultimately show ?thesis
      using dom 1 2 cond
      unfolding remove_all_annot_true_clause_one_imp_def s
      by (auto simp:
        Suc_le_eq remove_all_annot_true_clause_imp_inv_def)
  qed
  have remove_all_annot_true_clause_imp_inv_Suc:
    \<open>remove_all_annot_true_clause_imp_inv S xs (Suc i, T)\<close>
    if \<open>remove_all_annot_true_clause_imp_inv S xs (i, T)\<close> and
      \<open>i < length xs\<close>
      for xs
    using that
    by (auto simp: remove_all_annot_true_clause_imp_inv_def)
  have one_all: \<open>remove_one_annot_true_clause_imp_inv S  (Suc i, T) \<Longrightarrow>
    remove_all_annot_true_clause_imp_inv S xs (a, T) \<Longrightarrow>
    Suc a \<le> length xs \<Longrightarrow>
    remove_all_annot_true_clause_imp_inv S xs (Suc a, T)\<close> for S T a xs
    unfolding remove_one_annot_true_clause_imp_inv_def remove_all_annot_true_clause_imp_inv_def
    by auto

  show ?thesis
    unfolding remove_all_annot_true_clause_imp_def prod.case assert_bind_spec_conv
    apply (subst intro_spec_refine_iff[of _ _ Id, simplified])
    apply (intro ballI conjI)
    subgoal using pre unfolding U .
    subgoal for xs
      apply (refine_vcg
        WHILEIT_rule_stronger_inv[where
          R = \<open>measure (\<lambda>(i, _). length xs - i)\<close> and
          I' = \<open>\<lambda>(_, W). remove_one_annot_true_clause_imp_inv U (i+1, W)\<close>])
      subgoal by auto
      subgoal using rem_true_U_U unfolding U by auto
      subgoal using rem_U_U unfolding U by auto
      subgoal by simp
      apply (rule remove_all_annot_true_clause_one_imp; assumption)
      subgoal by (auto simp: remove_all_annot_true_clause_imp_inv_Suc U one_all)
      subgoal by (auto simp: remove_all_annot_true_clause_imp_inv_Suc U one_all)
      subgoal by (auto simp: remove_all_annot_true_clause_imp_inv_Suc U one_all)
      subgoal
        apply (rule remove_one_annot_true_clause_imp_inv_trans[OF annot])
        apply auto
        done
      subgoal using i_le by auto
      done
    done
qed

lemma RETURN_le_RES_no_return:
  \<open>f \<le> SPEC (\<lambda>S. g S \<in> \<Phi>) \<Longrightarrow> do {S \<leftarrow> f; RETURN (g S)} \<le> RES \<Phi>\<close>
  by (cases f) (auto simp: RES_RETURN_RES)

lemma remove_one_annot_true_clause_one_imp_spec:
  assumes
    I: \<open>remove_one_annot_true_clause_imp_inv S iT\<close> and
    cond: \<open>case iT of (i, S) \<Rightarrow> i < length (get_trail_l S)\<close> and
    iT: \<open>iT = (i, T)\<close> and
    proped: \<open>is_proped (rev (get_trail_l S) ! i)\<close>
  shows \<open>remove_one_annot_true_clause_one_imp i T
         \<le> SPEC  (\<lambda>s'. remove_one_annot_true_clause_imp_inv S s' \<and>
                (s', iT) \<in> measure (\<lambda>(i, _). length (get_trail_l S) - i))\<close>
proof -
  obtain M N D NE UE NS US WS Q where T: \<open>T = (M, N, D, NE, UE, NS, US, WS, Q)\<close>
    by (cases T)

  obtain x where
    ST: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>i \<le> length (get_trail_l S)\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>(S, x) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs x\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    level0: \<open>\<forall>j<i. is_proped (rev (get_trail_l T) ! j)\<close> and
    mark0: \<open>\<forall>j<i. mark_of (rev (get_trail_l T) ! j) = 0\<close> and
    le: \<open>length (get_trail_l S) = length (get_trail_l T)\<close> and
    clss_upd: \<open>clauses_to_update_l S = clauses_to_update_l T\<close> and
    lits_upd: \<open>literals_to_update_l S = literals_to_update_l T\<close>
    using I unfolding remove_one_annot_true_clause_imp_inv_def iT prod.case by blast
  then have list_invs_T: \<open>twl_list_invs T\<close>
    by (meson rtranclp_cdcl_twl_restart_l_list_invs
        rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2)
  obtain x' where
    Tx': \<open>(T, x') \<in> twl_st_l None\<close> and
    struct_invs_T: \<open>twl_struct_invs x'\<close>
    using \<open>(S, x) \<in> twl_st_l None\<close> \<open>twl_list_invs S\<close> \<open>twl_struct_invs x\<close> confl
     rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2 ST upd by blast
  then have n_d: \<open>no_dup (get_trail_l T)\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st twl_st_l)

  have D: \<open>D = None\<close> and WS: \<open>WS = {#}\<close>
    using confl upd rtranclp_remove_one_annot_true_clause_clauses_to_update_l[OF ST]
    using rtranclp_remove_one_annot_true_clause_get_conflict_l[OF ST] unfolding T by auto
  have lits_of_ST: \<open>lits_of_l (get_trail_l S) = lits_of_l (get_trail_l T)\<close>
    using arg_cong[OF rtranclp_remove_one_annot_true_clause_map_lit_of_trail[OF ST], of set]
    by (simp add: lits_of_def)

  have rem_one_annot_i_T: \<open>remove_one_annot_true_clause_one_imp_pre i T\<close>
    using Tx' struct_invs_T level0 cond list_invs_T D WS
    unfolding remove_one_annot_true_clause_one_imp_pre_def iT T prod.case
    by fastforce
  have
    annot_in_dom: \<open>C \<in># dom_m (get_clauses_l T)\<close> (is ?annot)
    if
      \<open>case LC of (L, C) \<Rightarrow> rev (get_trail_l T) ! i = Propagated L C\<close> and
      \<open>LC = (L, C)\<close> and
      \<open>\<not>(C = 0)\<close>
    for LC L C
  proof -
    have \<open>rev (get_trail_l T)!i \<in> set (get_trail_l T)\<close>
      using list_invs_T assms le unfolding T
     by (auto simp: twl_list_invs_def rev_nth)
    then show ?annot
      using list_invs_T that le unfolding T
      by (auto simp: twl_list_invs_def simp del: nth_mem)
  qed
  have replace_annot_l:
    \<open>replace_annot_l L C T
	\<le> SPEC
	   (\<lambda>Sa. do {
		   S \<leftarrow> remove_and_add_cls_l C Sa;
		   RETURN (i + 1, S)
		 } \<le> SPEC
		      (\<lambda>s'. remove_one_annot_true_clause_imp_inv S s' \<and>
			    (s', iT)
			    \<in> measure (\<lambda>(i, _). length (get_trail_l S) - i)))\<close>
    if
      rem_one: \<open>remove_one_annot_true_clause_one_imp_pre i T\<close> and
      \<open>is_proped (rev (get_trail_l T) ! i)\<close> and
      LC_d: \<open>case LC of (L, C) \<Rightarrow> rev (get_trail_l T) ! i = Propagated L C\<close> and
      LC: \<open>LC = (L, C)\<close> and
      LC_T: \<open>Propagated L C \<in> set (get_trail_l T)\<close> and
      \<open>C \<noteq> 0\<close> and
      dom: \<open>C \<in># dom_m (get_clauses_l T)\<close>
    for LC C L
  proof -
    have \<open>i < length M\<close>
      using rem_one unfolding remove_one_annot_true_clause_one_imp_pre_def T by auto

    {
      fix M2 Ca M1
      assume M: \<open>M = M2 @ Propagated L Ca # M1\<close> and \<open>irred N Ca\<close>
      have n_d: \<open>no_dup M\<close>
        using n_d unfolding T by auto
      then have [simp]: \<open>Ca = C\<close>
        using LC_T
        by (auto simp: T M dest!: in_set_definedD)
      have \<open>Ca > 0\<close>
        using that(6) by auto
      let ?U = \<open>(M2 @ Propagated L 0 # M1, fmdrop Ca N, D, add_mset (mset (N \<propto> Ca)) NE, UE,
         NS, {#}, WS, Q)\<close>

      have lev: \<open>get_level (M2 @ Propagated L C # M1) L = 0\<close> and
        M1: \<open>length M1 = i\<close>
        using n_d level0 LC_d decomp_nth_eq_lit_eq(1)[OF M
	   LC_d[unfolded T get_trail_l.simps LC prod.case]
	   n_d \<open>i < length M\<close>]
	unfolding M T
      apply (auto simp: count_decided_0_iff nth_append nth_Cons is_decided_no_proped_iff
        in_set_conv_nth rev_nth
       split: if_splits)
       by (metis diff_less gr_implies_not0 linorder_neqE_nat nth_rev_alt rev_nth zero_less_Suc)

      have TU: \<open>remove_one_annot_true_clause T ?U\<close>
        unfolding T M
	apply (rule remove_one_annot_true_clause.remove_irred_trail)
	using \<open>irred N Ca\<close> \<open>Ca > 0\<close> dom lev
	by (auto simp: T M)
      moreover {
	have \<open>length (get_trail_l ?U) = length (get_trail_l T)\<close>
	  using TU by (auto simp: remove_one_annot_true_clause.simps T M)
	then have \<open>j<i \<Longrightarrow> is_proped (rev (get_trail_l ?U) ! j)\<close> for j
	  using arg_cong[OF remove_one_annot_true_clause_map_is_decided_trail[OF TU],
	   of \<open>\<lambda>xs. xs ! (length (get_trail_l ?U) - Suc j)\<close>] level0  \<open>i < length M\<close>
	  by (auto simp: rev_nth T is_decided_no_proped_iff M
	    nth_append nth_Cons split: nat.splits)
      }
      moreover {
	have \<open>length (get_trail_l ?U) = length (get_trail_l T)\<close>
	  using TU by (auto simp: remove_one_annot_true_clause.simps T M)
	then have \<open>j<i \<Longrightarrow> mark_of (rev (get_trail_l ?U) ! j) = 0\<close> for j
	  using remove_one_annot_true_clause_map_mark_of_same_or_0[OF TU,
	    of \<open>(length (get_trail_l ?U) - Suc j)\<close>] mark0  \<open>i < length M\<close>
	  by (auto simp: rev_nth T is_decided_no_proped_iff M
	    nth_append nth_Cons split: nat.splits)
      }
      moreover have \<open>length (get_trail_l S) = length (get_trail_l ?U)\<close>
	using le TU by (auto simp: T M split: if_splits)
      moreover have \<open>\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S'\<close>
        by (rule exI[of _ x])
	  (use \<open>(S, x) \<in> twl_st_l None\<close> \<open>twl_struct_invs x\<close> in blast)
      ultimately have 1: \<open>remove_one_annot_true_clause_imp_inv S (Suc i, ?U)\<close>
	using \<open>twl_list_invs S\<close> \<open>i \<le> length (get_trail_l S)\<close>
	\<open>(S, x) \<in> twl_st_l None\<close> and
	\<open>twl_struct_invs x\<close> and
	\<open>get_conflict_l S = None\<close> and
	\<open>clauses_to_update_l S = {#}\<close> and
	\<open>\<forall>j<i. is_proped (rev (get_trail_l T) ! j)\<close> and
	\<open>\<forall>j<i. mark_of (rev (get_trail_l T) ! j) = 0\<close> and
	le T clss_upd lits_upd ST TU D M1 \<open>i < length M\<close>
	unfolding remove_one_annot_true_clause_imp_inv_def prod.case
	by (auto simp: less_Suc_eq nth_append)
      have 2: \<open>length (get_trail_l S) - Suc i < length (get_trail_l S) - i\<close>
        by (simp add: T \<open>i < length M\<close> diff_less_mono2 le)
      note 1 2
    }
    moreover {
      fix M2 Ca M1
      assume M: \<open>M = M2 @ Propagated L Ca # M1\<close> and \<open>\<not>irred N Ca\<close>
      have n_d: \<open>no_dup M\<close>
        using n_d unfolding T by auto
      then have [simp]: \<open>Ca = C\<close>
        using LC_T
        by (auto simp: T M dest!: in_set_definedD)
      have \<open>Ca > 0\<close>
        using that(6) by auto
      let ?U = \<open>(M2 @ Propagated L 0 # M1, fmdrop Ca N, D, NE,
        add_mset (mset (N \<propto> Ca)) UE, NS, {#}, WS, Q)\<close>

      have lev: \<open>get_level (M2 @ Propagated L C # M1) L = 0\<close> and
        M1: \<open>length M1 = i\<close>
        using n_d level0 LC_d decomp_nth_eq_lit_eq(1)[OF M
	   LC_d[unfolded T get_trail_l.simps LC prod.case]
	   n_d \<open>i < length M\<close>]
	unfolding M T
      apply (auto simp: count_decided_0_iff nth_append nth_Cons is_decided_no_proped_iff
        in_set_conv_nth rev_nth
       split: if_splits)
       by (metis diff_less gr_implies_not0 linorder_neqE_nat nth_rev_alt rev_nth zero_less_Suc)

      have TU: \<open>remove_one_annot_true_clause T ?U\<close>
        unfolding T M
	apply (rule remove_one_annot_true_clause.remove_red_trail)
	using \<open>\<not>irred N Ca\<close> \<open>Ca > 0\<close> dom lev
	by (auto simp: T M)
      moreover {
	have \<open>length (get_trail_l ?U) = length (get_trail_l T)\<close>
	  using TU by (auto simp: remove_one_annot_true_clause.simps T M)
	then have \<open>j<i \<Longrightarrow> is_proped (rev (get_trail_l ?U) ! j)\<close> for j
	  using arg_cong[OF remove_one_annot_true_clause_map_is_decided_trail[OF TU],
	   of \<open>\<lambda>xs. xs ! (length (get_trail_l ?U) - Suc j)\<close>] level0  \<open>i < length M\<close>
	  by (auto simp: rev_nth T is_decided_no_proped_iff M
	    nth_append nth_Cons split: nat.splits)
      }
      moreover {
	have \<open>length (get_trail_l ?U) = length (get_trail_l T)\<close>
	  using TU by (auto simp: remove_one_annot_true_clause.simps T M)
	then have \<open>j<i \<Longrightarrow> mark_of (rev (get_trail_l ?U) ! j) = 0\<close> for j
	  using remove_one_annot_true_clause_map_mark_of_same_or_0[OF TU,
	    of \<open>(length (get_trail_l ?U) - Suc j)\<close>] mark0  \<open>i < length M\<close>
	  by (auto simp: rev_nth T is_decided_no_proped_iff M
	    nth_append nth_Cons split: nat.splits)
      }
      moreover have \<open>length (get_trail_l S) = length (get_trail_l ?U)\<close>
	using le TU by (auto simp: T M split: if_splits)
      moreover have \<open>\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S'\<close>
        by (rule exI[of _ x])
	  (use \<open>(S, x) \<in> twl_st_l None\<close> \<open>twl_struct_invs x\<close> in blast)
      ultimately have 1: \<open>remove_one_annot_true_clause_imp_inv S (Suc i, ?U)\<close>
	using \<open>twl_list_invs S\<close> \<open>i \<le> length (get_trail_l S)\<close>
	\<open>(S, x) \<in> twl_st_l None\<close> and
	\<open>twl_struct_invs x\<close> and
	\<open>get_conflict_l S = None\<close> and
	\<open>clauses_to_update_l S = {#}\<close> and
	\<open>\<forall>j<i. is_proped (rev (get_trail_l T) ! j)\<close> and
	\<open>\<forall>j<i. mark_of (rev (get_trail_l T) ! j) = 0\<close> and
	le T clss_upd lits_upd ST TU D cond \<open>i < length M\<close> M1
	unfolding remove_one_annot_true_clause_imp_inv_def prod.case
	by (auto simp: less_Suc_eq nth_append)
      have 2: \<open>length (get_trail_l S) - Suc i < length (get_trail_l S) - i\<close>
        by (simp add: T \<open>i < length M\<close> diff_less_mono2 le)
      note 1 2
    }
    moreover have \<open>C = Ca\<close> if \<open>M = M2 @ Propagated L Ca # M1\<close> for M1 M2 Ca
      using LC_T n_d
      by (auto simp: T that dest!: in_set_definedD)
    moreover have \<open>replace_annot_l_pre L C (M, N, D, NE, UE, NS, US, WS, Q)\<close>
      using LC_T that unfolding replace_annot_l_pre_def
      by (auto simp: T)
    ultimately show ?thesis
      using dom cond
      by (auto simp: remove_and_add_cls_l_def
        replace_annot_l_def T iT
	intro!: RETURN_le_RES_no_return ASSERT_leI)
  qed

  have rev_set: \<open>rev (get_trail_l T) ! i \<in> set (get_trail_l T)\<close>
    using assms
    by (metis length_rev nth_mem rem_one_annot_i_T
      remove_one_annot_true_clause_one_imp_pre_def set_rev)
  show ?thesis
    unfolding remove_one_annot_true_clause_one_imp_def
    apply refine_vcg
    subgoal using rem_one_annot_i_T unfolding iT T by simp
    subgoal using proped I le
      rtranclp_remove_one_annot_true_clause_map_is_decided_trail[of S T,
        THEN arg_cong, of \<open>\<lambda>xs. (rev xs) ! i\<close>]
      unfolding iT T remove_one_annot_true_clause_imp_inv_def
        remove_one_annot_true_clause_one_imp_pre_def
      by (auto simp add: All_less_Suc rev_map is_decided_no_proped_iff)
    subgoal
      using rev_set unfolding T
      by auto
    subgoal using I le unfolding iT T remove_one_annot_true_clause_imp_inv_def
      remove_one_annot_true_clause_one_imp_pre_def
      by (auto simp add: All_less_Suc)
    subgoal using cond le unfolding iT T remove_one_annot_true_clause_one_imp_pre_def by auto
    subgoal by (rule annot_in_dom)
    subgoal for LC L C
      by (rule replace_annot_l)
    done

qed


lemma remove_one_annot_true_clause_count_dec: \<open>remove_one_annot_true_clause S b \<Longrightarrow>
   count_decided (get_trail_l S) = count_decided (get_trail_l b)\<close>
  by (auto simp: remove_one_annot_true_clause.simps)

lemma rtranclp_remove_one_annot_true_clause_count_dec:
  \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S b \<Longrightarrow>
    count_decided (get_trail_l S) = count_decided (get_trail_l b)\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: remove_one_annot_true_clause_count_dec)

lemma rtranclp_valid_trail_reduction_count_dec_ge:
  \<open>valid_trail_reduction M M' \<Longrightarrow>
    count_decided M' \<le> count_decided M\<close>
  apply (induction rule: valid_trail_reduction.induct)
  by (auto simp: dest!: get_all_ann_decomposition_exists_prepend
    dest: trail_renumber_count_dec)

lemma rtranclp_cdcl_twl_restart_l_count_dec:
  \<open>cdcl_twl_restart_l S b \<Longrightarrow>
    count_decided (get_trail_l S) \<ge> count_decided (get_trail_l b)\<close>
  by (induction rule: cdcl_twl_restart_l.induct)
    (auto simp: remove_one_annot_true_clause_count_dec
    dest: rtranclp_valid_trail_reduction_count_dec_ge)

lemma remove_one_annot_true_clause_imp_spec:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    \<open>get_conflict_l S = None\<close> and
    \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>remove_one_annot_true_clause_imp S \<le> SPEC(\<lambda>T. cdcl_twl_restart_l S T)\<close>
  unfolding remove_one_annot_true_clause_imp_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(i, _). length (get_trail_l S) - i)\<close> and
      I=\<open>remove_one_annot_true_clause_imp_inv S\<close>]
    remove_one_annot_true_clause_imp_inv_spec
    remove_all_learned_subsumed_clauses_cdcl_twl_restart_l[THEN order_trans])
  subgoal by auto
  subgoal using assms unfolding remove_one_annot_true_clause_imp_inv_def by blast
  apply (rule remove_one_annot_true_clause_one_imp_spec[of _ _ ])
  subgoal unfolding remove_one_annot_true_clause_imp_inv_def by auto
  subgoal unfolding remove_one_annot_true_clause_imp_inv_def by auto
  subgoal
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: count_decided_0_iff rev_nth is_decided_no_proped_iff)
  subgoal
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: count_decided_0_iff rev_nth is_decided_no_proped_iff)
  apply assumption
  apply assumption
  subgoal for x s a b xa
    using tranclp_cdcl_twl_restart_l_cdcl_is_cdcl_twl_restart_l[of S xa]
      rtranclp_into_tranclp1[of cdcl_twl_restart_l S b xa]
      remove_one_annot_true_clause_imp_inv_no_dupD2[of S s \<open>fst s\<close> \<open>snd s\<close>]
    by (auto simp: remove_one_annot_true_clause_imp_inv_def
       dest!: rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2)
  done

lemma remove_one_annot_true_clause_imp_spec_lev0:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    \<open>get_conflict_l S = None\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    \<open>count_decided (get_trail_l S) = 0\<close>
  shows \<open>remove_one_annot_true_clause_imp S \<le> SPEC(\<lambda>T. cdcl_twl_restart_l S T \<and>
     count_decided (get_trail_l T) = 0 \<and> (\<forall>L \<in> set (get_trail_l T). mark_of L = 0) \<and>
     length (get_trail_l S) = length (get_trail_l T)) \<close>
proof -
  have H: \<open>\<forall>j<a. is_proped (rev (get_trail_l b) ! j) \<and>
          mark_of (rev (get_trail_l b) ! j) = 0 \<Longrightarrow>  \<not> a < length (get_trail_l b) \<Longrightarrow>
      \<forall>x \<in> set (get_trail_l b). is_proped x \<and> mark_of x = 0\<close> for a b
    apply (rule ballI)
    apply (subst (asm) set_rev[symmetric])
    apply (subst (asm) in_set_conv_nth)
    apply auto
    done
   have K: \<open>a < length (get_trail_l b) \<Longrightarrow> is_decided (get_trail_l b ! a) \<Longrightarrow>
     count_decided (get_trail_l b) \<noteq> 0\<close> for a b
    using count_decided_0_iff nth_mem by blast
  show ?thesis
    apply (rule SPEC_rule_conjI)
    apply (rule remove_one_annot_true_clause_imp_spec[OF assms(1-5)])
    unfolding remove_one_annot_true_clause_imp_def
    apply (refine_vcg WHILEIT_rule[where
        R=\<open>measure (\<lambda>(i, _::'a twl_st_l). length (get_trail_l S) - i)\<close> and
        I=\<open>remove_one_annot_true_clause_imp_inv S\<close>]
      remove_one_annot_true_clause_one_imp_spec
      remove_all_learned_subsumed_clauses_cdcl_twl_restart_l[THEN order_trans])
    subgoal by auto
    subgoal using assms unfolding remove_one_annot_true_clause_imp_inv_def by blast
    subgoal using assms unfolding remove_one_annot_true_clause_imp_inv_def by auto
    subgoal using assms by (auto simp: count_decided_0_iff is_decided_no_proped_iff
      rev_nth)
    apply assumption
    apply assumption
    subgoal using assms unfolding remove_one_annot_true_clause_imp_inv_def
      apply (auto simp: rtranclp_remove_one_annot_true_clause_count_dec
        dest: rtranclp_cdcl_twl_restart_l_count_dec)
      done
    subgoal
      using assms(6) unfolding remove_one_annot_true_clause_imp_inv_def
      by (auto dest: H K)
    subgoal
      using assms(6) unfolding remove_one_annot_true_clause_imp_inv_def
      by (auto dest: H K)
  done
qed


definition collect_valid_indices :: \<open>_ \<Rightarrow> nat list nres\<close> where
  \<open>collect_valid_indices S = SPEC (\<lambda>N. True)\<close>

definition mark_to_delete_clauses_l_inv
  :: \<open>'v twl_st_l \<Rightarrow> nat list \<Rightarrow> nat \<times> 'v twl_st_l \<times> nat list \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_l_inv = (\<lambda>S xs0 (i, T, xs).
      remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<and>
      get_trail_l S = get_trail_l T \<and>
      (\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S') \<and>
      twl_list_invs S \<and>
      get_conflict_l S = None \<and>
      clauses_to_update_l S = {#})\<close>

definition mark_to_delete_clauses_l_pre
  :: \<open>'v twl_st_l \<Rightarrow> bool\<close>
where
  \<open>mark_to_delete_clauses_l_pre S \<longleftrightarrow>
   (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and> twl_list_invs S)\<close>

definition mark_garbage_l:: \<open>nat \<Rightarrow>  'v twl_st_l \<Rightarrow> 'v twl_st_l\<close>  where
  \<open>mark_garbage_l = (\<lambda>C (M, N0, D, NE, UE, NS, US, WS, Q). (M, fmdrop C N0, D, NE, UE, NS, {#}, WS, Q))\<close>

definition can_delete where
  \<open>can_delete S C b = (b \<longrightarrow>
    (length (get_clauses_l S \<propto> C) = 2 \<longrightarrow>
      (Propagated (get_clauses_l S \<propto> C ! 0) C \<notin> set (get_trail_l S)) \<and>
      (Propagated (get_clauses_l S \<propto> C ! 1) C \<notin> set (get_trail_l S))) \<and>
    (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow>
      (Propagated (get_clauses_l S \<propto> C ! 0) C \<notin> set (get_trail_l S))) \<and>
    \<not>irred (get_clauses_l S) C)\<close>

definition mark_to_delete_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>mark_to_delete_clauses_l  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_l_pre S);
    xs \<leftarrow> collect_valid_indices S;
    to_keep \<leftarrow> SPEC(\<lambda>_::nat. True); \<comment> \<open>the minimum number of clauses that should be kept.\<close>
    (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_l_inv S xs\<^esup>
      (\<lambda>(i, S, xs). i < length xs)
      (\<lambda>(i, S, xs). do {
        if(xs!i \<notin># dom_m (get_clauses_l S)) then RETURN (i, S, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (get_clauses_l S\<propto>(xs!i)));
          can_del \<leftarrow> SPEC (can_delete S (xs!i));
          ASSERT(i < length xs);
          if can_del
          then
            RETURN (i, mark_garbage_l (xs!i) S, delete_index_and_swap xs i)
          else
            RETURN (i+1, S, xs)
       }
      })
      (to_keep, S, xs);
    remove_all_learned_subsumed_clauses S
  })\<close>


definition mark_to_delete_clauses_l_post where
  \<open>mark_to_delete_clauses_l_post S T \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_l None \<and> remove_one_annot_true_clause\<^sup>*\<^sup>* S T \<and>
       twl_list_invs S \<and> twl_struct_invs S' \<and> get_conflict_l S = None \<and>
       clauses_to_update_l S = {#})\<close>

lemma mark_to_delete_clauses_l_spec:
  assumes
    ST: \<open>(S, S') \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>mark_to_delete_clauses_l S \<le> \<Down> Id (SPEC(\<lambda>T. remove_one_annot_true_clause\<^sup>+\<^sup>+ S T \<and>
    get_trail_l S = get_trail_l T))\<close>
proof -

  define I where
    \<open>I (xs :: nat list) \<equiv> (\<lambda>(i :: nat, T, xs :: nat list). remove_one_annot_true_clause\<^sup>*\<^sup>* S T)\<close> for xs

  have mark0: \<open>mark_to_delete_clauses_l_pre S\<close>
    using ST list_invs struct_invs unfolding mark_to_delete_clauses_l_pre_def
    by blast
  have I0: \<open>I xs (l, S, xs')\<close>
    for xs xs' :: \<open>nat list\<close> and l :: nat
  proof -
    show ?thesis
      unfolding I_def
      by auto
  qed
  have mark_to_delete_clauses_l_inv_notin:
    \<open>mark_to_delete_clauses_l_inv S xs0 (a, aa, delete_index_and_swap xs' a)\<close>
    if
      \<open>mark_to_delete_clauses_l_pre S\<close> and
      \<open>xs0 \<in> {N. True}\<close> and
      \<open>mark_to_delete_clauses_l_inv S xs0 s\<close> and
      \<open>I xs0 s\<close> and
      \<open>case s of (i, S, xs) \<Rightarrow> i < length xs\<close> and
      \<open>aa' = (aa, xs')\<close> and
      \<open>s = (a, aa')\<close> and
      \<open>ba ! a \<notin># dom_m (get_clauses_l aa)\<close>
    for s a aa ba xs0 aa' xs'
  proof -
    show ?thesis
      using that
      unfolding mark_to_delete_clauses_l_inv_def
      by auto
  qed
  have I_notin: \<open>I xs0 (a, aa, delete_index_and_swap xs' a)\<close>
    if
      \<open>mark_to_delete_clauses_l_pre S\<close> and
      \<open>xs0 \<in> {N. True}\<close> and
      \<open>mark_to_delete_clauses_l_inv S xs0 s\<close> and
      \<open>I xs0 s\<close> and
      \<open>case s of (i, S, xs) \<Rightarrow> i < length xs\<close> and
      \<open>aa' = (aa, xs')\<close> and
      \<open>s = (a, aa')\<close> and
      \<open>ba ! a \<notin># dom_m (get_clauses_l aa)\<close>
    for s a aa ba xs0 aa' xs'
  proof -
    show ?thesis
      using that
      unfolding I_def
      by auto
  qed

  have length_ge0: \<open>0 < length (get_clauses_l aa \<propto> (xs ! a))\<close>
    if
      inv: \<open>mark_to_delete_clauses_l_inv S xs0 s\<close> and
      I: \<open>I xs0 s\<close> and
      cond: \<open>case s of (i, S, xs0) \<Rightarrow> i < length xs0\<close> and
      st:
        \<open>aa' = (aa, xs)\<close>
        \<open>s = (a, aa')\<close> and
      xs: \<open>\<not> xs ! a \<notin># dom_m (get_clauses_l aa)\<close>
    for s a b aa xs0 aa' xs
  proof -
    have
      rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S aa\<close>
      using I unfolding I_def st prod.case by blast+
    then obtain T' where
      T': \<open>(aa, T') \<in> twl_st_l None\<close> and
      \<open>twl_struct_invs T'\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list_invs confl upd
       ST struct_invs] by blast
    then have \<open>Multiset.Ball (get_clauses T') struct_wf_twl_cls\<close>
      unfolding twl_struct_invs_def twl_st_inv_alt_def
      by fast
    then have \<open>\<forall>x\<in>#ran_m (get_clauses_l aa). 2 \<le> length (fst x)\<close>
      using xs T' by (auto simp: twl_st_l)
    then show ?thesis
      using xs by (auto simp: ran_m_def)
  qed

  have mark_to_delete_clauses_l_inv_del:
      \<open>mark_to_delete_clauses_l_inv S xs0 (i, mark_garbage_l (xs ! i) T, delete_index_and_swap xs i)\<close> and
    I_del: \<open>I xs0 (i, mark_garbage_l (xs ! i) T, delete_index_and_swap xs i)\<close>
    if
      \<open>mark_to_delete_clauses_l_pre S\<close> and
      \<open>xs0 \<in> {N. True}\<close> and
      inv: \<open>mark_to_delete_clauses_l_inv S xs0 s\<close> and
      I: \<open>I xs0 s\<close> and
      i_le: \<open>case s of (i, S, xs) \<Rightarrow> i < length xs\<close> and
      st: \<open>sT = (T, xs)\<close>
         \<open>s = (i, sT)\<close> and
      in_dom: \<open>\<not> xs ! i \<notin># dom_m (get_clauses_l T)\<close> and
      \<open>0 < length (get_clauses_l T \<propto> (xs ! i))\<close> and
      can_del: \<open>can_delete T (xs ! i) b\<close> and
      \<open>i < length xs\<close> and
      [simp]: \<open>b\<close>
     for x s i T b xs0 sT xs
  proof -
    obtain M N D NE UE NS US WS Q where S: \<open>S = (M, N, D, NE, UE, NS, US, WS, Q)\<close>
      by (cases S)
    obtain M' N' D' NE' UE' NS' US' WS' Q' where T: \<open>T = (M', N', D', NE', UE', NS', US', WS', Q')\<close>
      by (cases T)
    have
      rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S T\<close>
      using I unfolding I_def st prod.case by blast+

    obtain V where
      SU: \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S T\<close> and
      UV: \<open>(T, V) \<in> twl_st_l None\<close> and
      TV: \<open>cdcl_twl_restart\<^sup>*\<^sup>* S' V\<close> and
      struct_invs_V: \<open>twl_struct_invs V\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list_invs confl upd
        ST struct_invs]
      by auto
    have list_invs_U': \<open>twl_list_invs T\<close>
      using SU list_invs rtranclp_cdcl_twl_restart_l_list_invs by blast

    have \<open>xs ! i > 0\<close>
      apply (rule ccontr)
      using in_dom list_invs_U' unfolding twl_list_invs_def by (auto dest: multi_member_split)
    have \<open>N' \<propto> (xs ! i) ! 0 \<in> lits_of_l M'\<close>
       if \<open>Propagated (N' \<propto> (xs ! i) ! 0) (xs0 ! i) \<in> set M'\<close>
      using that by (auto dest!: split_list)
    then have not_annot: \<open>Propagated Laa (xs ! i) \<in> set M' \<Longrightarrow> False\<close> for Laa
      using is_annot_iff_annotates_first[OF UV list_invs_U' struct_invs_V \<open>xs ! i > 0\<close>]
      is_annot_no_other_true_lit[OF UV list_invs_U' struct_invs_V \<open>xs ! i > 0\<close>, of Laa \<open>
         N' \<propto> (xs !i) ! 0\<close>] can_del
      trail_length_ge2[OF UV list_invs_U' struct_invs_V _ \<open>xs ! i > 0\<close>, of Laa]
      unfolding S T can_delete_def
      by (auto dest: no_dup_same_annotD)

    have star: \<open>remove_one_annot_true_clause T (mark_garbage_l (xs ! i) T)\<close>
      unfolding st T mark_garbage_l_def prod.simps
      apply (rule remove_one_annot_true_clause.delete)
      subgoal using in_dom i_le unfolding st prod.case T by auto
      subgoal using can_del unfolding T can_delete_def by auto
      subgoal using not_annot unfolding T by auto
      done
    moreover have \<open>get_trail_l (mark_garbage_l (xs ! i) T) = get_trail_l T\<close>
      by (cases T) (auto simp: mark_garbage_l_def)
    ultimately show \<open>mark_to_delete_clauses_l_inv S xs0
        (i, mark_garbage_l (xs ! i) T, delete_index_and_swap xs i)\<close>
      using inv
      unfolding mark_to_delete_clauses_l_inv_def prod.simps st
      by force

    show \<open>I xs0 (i, mark_garbage_l (xs ! i) T, delete_index_and_swap xs i)\<close>
      using rem star unfolding st I_def by simp
  qed
  have
    mark_to_delete_clauses_l_inv_keep:
      \<open>mark_to_delete_clauses_l_inv S xs0 (i + 1, T, xs)\<close> and
    I_keep: \<open>I xs0 (i + 1, T, xs)\<close>
    if
      \<open>mark_to_delete_clauses_l_pre S\<close> and
      inv: \<open>mark_to_delete_clauses_l_inv S xs0 s\<close> and
      I: \<open>I xs0 s\<close> and
      cond: \<open>case s of (i, S, xs) \<Rightarrow> i < length xs\<close> and
      st: \<open>sT = (T, xs)\<close>
         \<open>s = (i, sT)\<close> and
      dom: \<open>\<not> xs ! i \<notin># dom_m (get_clauses_l T)\<close> and
      \<open>0 < length (get_clauses_l T \<propto> (xs ! i))\<close> and
      \<open>can_delete T (xs ! i) b\<close> and
      \<open>i < length xs\<close> and
      \<open>\<not> b\<close>
    for x s i T b xs0 sT xs
  proof -
    show \<open>mark_to_delete_clauses_l_inv S xs0 (i + 1, T, xs)\<close>
      using inv
      unfolding mark_to_delete_clauses_l_inv_def prod.simps st
      by fast
    show  \<open>I xs0 (i + 1, T, xs)\<close>
      using I unfolding I_def st prod.simps .
  qed
  have remove_all_learned_subsumed_clauses: \<open>remove_all_learned_subsumed_clauses aa
        \<le> SPEC
           (\<lambda>T. remove_one_annot_true_clause\<^sup>+\<^sup>+ S T \<and>
                get_trail_l S = get_trail_l T)\<close>
    if
      \<open>mark_to_delete_clauses_l_pre S\<close> and
      \<open>xs0 \<in> {N. True}\<close> and
      \<open>True\<close> and
      \<open>mark_to_delete_clauses_l_inv S xs0 s\<close> and
      \<open>I xs0 s\<close> and
      \<open>\<not> (case s of (i, S, xs) \<Rightarrow> i < length xs)\<close> and
      \<open>s = (a, b)\<close> and
      \<open>b = (aa, ba)\<close>
    for x s a b aa ba xs0
  proof -
    have 1: \<open>remove_all_learned_subsumed_clauses aa
        \<le> SPEC
           (\<lambda>T. remove_one_annot_true_clause aa T \<and>
                get_trail_l aa = get_trail_l T)\<close>
      unfolding remove_all_learned_subsumed_clauses_def
      by refine_rcg
        (auto intro!: remove_one_annot_true_clause.delete_subsumed)
    show ?thesis
      by (rule 1[THEN order_trans])
        (use that in \<open>auto simp: mark_to_delete_clauses_l_inv_def\<close>)
  qed


  show ?thesis
    unfolding mark_to_delete_clauses_l_def collect_valid_indices_def
    apply (rule ASSERT_refine_left)
     apply (rule mark0)
    apply (subst intro_spec_iff)
    apply (intro ballI)
    subgoal for xs0
      apply (refine_vcg
        WHILEIT_rule_stronger_inv[where I'=\<open>I xs0\<close> and
          R= \<open>measure (\<lambda>(i :: nat, N, xs0). Suc (length xs0) - i)\<close>])
      subgoal by auto
      subgoal using list_invs confl upd ST struct_invs unfolding mark_to_delete_clauses_l_inv_def
          by (cases S') force
      subgoal by (rule I0)
      subgoal
        by (rule mark_to_delete_clauses_l_inv_notin)
      subgoal
        by (rule I_notin)
      subgoal
        by auto
      subgoal
        by (rule length_ge0)
      subgoal
        by auto
      subgoal \<comment> \<open>delete clause\<close>
        by (rule mark_to_delete_clauses_l_inv_del)
      subgoal
        by (rule I_del)
      subgoal
        by auto
      subgoal \<comment> \<open>Keep clause\<close>
        by (rule mark_to_delete_clauses_l_inv_keep)
      subgoal
        by (rule I_keep)
      subgoal
        by auto
      subgoal for x s a b aa ba
        by (rule remove_all_learned_subsumed_clauses)
      done
    done
qed

definition GC_clauses :: \<open>nat clauses_l \<Rightarrow> nat clauses_l \<Rightarrow> (nat clauses_l \<times> (nat \<Rightarrow> nat option)) nres\<close> where
\<open>GC_clauses N N' = do {
  xs \<leftarrow> SPEC(\<lambda>xs. set_mset (dom_m N) \<subseteq> set xs);
  (N, N', m) \<leftarrow> nfoldli
    xs
    (\<lambda>(N, N', m). True)
    (\<lambda>C (N, N', m).
       if C \<in># dom_m N
       then do {
         C' \<leftarrow> SPEC(\<lambda>i. i \<notin># dom_m N' \<and> i \<noteq> 0);
	 RETURN (fmdrop C N, fmupd C' (N \<propto> C, irred N C) N', m(C \<mapsto> C'))
       }
       else
         RETURN (N, N', m))
    (N, N', (\<lambda>_. None));
  RETURN (N', m)
}\<close>


inductive GC_remap
  :: \<open>('a, 'b) fmap \<times> ('a \<Rightarrow> 'c option) \<times> ('c, 'b) fmap \<Rightarrow>  ('a, 'b) fmap \<times> ('a \<Rightarrow> 'c option) \<times> ('c, 'b) fmap \<Rightarrow> bool\<close>
where
remap_cons:
  \<open>GC_remap (N, m, new) (fmdrop C N, m(C \<mapsto> C'), fmupd C' (the (fmlookup N C)) new)\<close>
   if \<open>C' \<notin># dom_m new\<close> and
      \<open>C \<in># dom_m N\<close> and
      \<open>C \<notin> dom m\<close> and
      \<open>C' \<notin> ran m\<close>

lemma GC_remap_ran_m_old_new:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> ran_m old + ran_m new = ran_m old' + ran_m new'\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin)

lemma GC_remap_init_clss_l_old_new:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow>
    init_clss_l old + init_clss_l new = init_clss_l old' + init_clss_l new'\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin split: if_splits)

lemma GC_remap_learned_clss_l_old_new:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow>
    learned_clss_l old + learned_clss_l new = learned_clss_l old' + learned_clss_l new'\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin split: if_splits)

lemma GC_remap_ran_m_remap:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> C \<in># dom_m old \<Longrightarrow> C \<notin># dom_m old' \<Longrightarrow>
         m' C \<noteq> None \<and>
         fmlookup new' (the (m' C)) = fmlookup old C\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin)

lemma GC_remap_ran_m_no_rewrite_map:
  \<open>GC_remap (old, m, new) (old', m', new') \<Longrightarrow> C \<notin># dom_m old \<Longrightarrow> m' C = m C\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin split: if_splits)


lemma GC_remap_ran_m_no_rewrite_fmap:
  \<open>GC_remap (old, m, new) (old', m', new') \<Longrightarrow> C \<in># dom_m new \<Longrightarrow>
    C \<in># dom_m new' \<and> fmlookup new C = fmlookup new' C\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin)


lemma rtranclp_GC_remap_init_clss_l_old_new:
  \<open>GC_remap\<^sup>*\<^sup>* S S' \<Longrightarrow>
    init_clss_l (fst S) + init_clss_l (snd (snd S)) = init_clss_l (fst S') + init_clss_l (snd (snd S'))\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin split: if_splits
      dest: GC_remap_init_clss_l_old_new)

lemma rtranclp_GC_remap_learned_clss_l_old_new:
  \<open>GC_remap\<^sup>*\<^sup>* S S' \<Longrightarrow>
    learned_clss_l (fst S) + learned_clss_l (snd (snd S)) =
      learned_clss_l (fst S') + learned_clss_l (snd (snd S'))\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin split: if_splits
      dest: GC_remap_learned_clss_l_old_new)

lemma rtranclp_GC_remap_ran_m_no_rewrite_fmap:
  \<open>GC_remap\<^sup>*\<^sup>* S S' \<Longrightarrow> C \<in># dom_m (snd (snd S)) \<Longrightarrow>
    C \<in># dom_m (snd (snd S')) \<and> fmlookup (snd (snd S)) C = fmlookup (snd (snd S')) C\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_no_rewrite_fmap)

lemma GC_remap_ran_m_no_rewrite:
  \<open>GC_remap S S' \<Longrightarrow> C \<in># dom_m (fst S) \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow>
         fmlookup (fst S) C = fmlookup (fst S') C\<close>
  by (induction rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin distinct_mset_dom
        distinct_mset_set_mset_remove1_mset
      dest: GC_remap_ran_m_remap)

lemma GC_remap_ran_m_lookup_kept:
  assumes
    \<open>GC_remap\<^sup>*\<^sup>* S y\<close> and
    \<open>GC_remap y z\<close> and
    \<open>C \<in># dom_m (fst S)\<close> and
    \<open>C \<in># dom_m (fst z)\<close> and
    \<open>C \<notin># dom_m (fst y)\<close>
  shows \<open>fmlookup (fst S) C = fmlookup (fst z) C\<close>
  using assms by (smt GC_remap.cases fmlookup_drop fst_conv in_dom_m_lookup_iff)

lemma rtranclp_GC_remap_ran_m_no_rewrite:
  \<open>GC_remap\<^sup>*\<^sup>*  S S' \<Longrightarrow> C \<in># dom_m (fst S) \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow>
    fmlookup (fst S) C = fmlookup (fst S') C\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (cases \<open>C \<in># dom_m (fst y)\<close>)
      (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept)
  done

lemma GC_remap_ran_m_no_lost:
  \<open>GC_remap S S' \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow> C \<in># dom_m (fst S)\<close>
  by (induction rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin distinct_mset_dom distinct_mset_set_mset_remove1_mset
      dest: GC_remap_ran_m_remap)

lemma rtranclp_GC_remap_ran_m_no_lost:
  \<open>GC_remap\<^sup>*\<^sup>* S S' \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow> C \<in># dom_m (fst S)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (cases \<open>C \<in># dom_m (fst y)\<close>)
      (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin
        dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost)
  done


lemma GC_remap_ran_m_no_new_lost:
  \<open>GC_remap S S' \<Longrightarrow> dom (fst (snd S)) \<subseteq> set_mset (dom_m (fst S)) \<Longrightarrow>
    dom (fst (snd S')) \<subseteq> set_mset (dom_m (fst S))\<close>
  by (induction rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin distinct_mset_dom
        distinct_mset_set_mset_remove1_mset
      dest: GC_remap_ran_m_remap)

lemma rtranclp_GC_remap_ran_m_no_new_lost:
  \<open>GC_remap\<^sup>*\<^sup>* S S' \<Longrightarrow> dom (fst (snd S)) \<subseteq> set_mset (dom_m (fst S)) \<Longrightarrow>
    dom (fst (snd S')) \<subseteq> set_mset (dom_m (fst S))\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    apply (cases \<open>C \<in># dom_m (fst y)\<close>)
    apply (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin
        dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost)
    apply (smt GC_remap_ran_m_no_rewrite_map contra_subsetD domI prod.collapse rtranclp_GC_remap_ran_m_no_lost)
    apply (smt GC_remap_ran_m_no_rewrite_map contra_subsetD domI prod.collapse rtranclp_GC_remap_ran_m_no_lost)
    done
  done


lemma rtranclp_GC_remap_map_ran:
  assumes
    \<open>GC_remap\<^sup>*\<^sup>* S S'\<close> and
    \<open>(the \<circ>\<circ> fst) (snd S) `# mset_set (dom (fst (snd S))) = dom_m (snd (snd S))\<close> and
    \<open>finite (dom (fst (snd S)))\<close>
  shows \<open>finite (dom (fst (snd S'))) \<and>
         (the \<circ>\<circ> fst) (snd S') `# mset_set (dom (fst (snd S'))) = dom_m (snd (snd S'))\<close>
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z) note star = this(1) and st = this(2) and IH = this(3) and H = this(4-)
  from st
  show ?case
  proof cases
    case (remap_cons C' new C N m)
    have \<open>C \<notin> dom m\<close>
      using step remap_cons by auto
   then have [simp]: \<open>{#the (if x = C then Some C' else m x). x \<in># mset_set (dom m)#} =
     {#the (m x). x \<in># mset_set (dom m)#}\<close>
    apply (auto intro!: image_mset_cong split: if_splits)
    by (metis empty_iff finite_set_mset_mset_set local.remap_cons(5) mset_set.infinite set_mset_empty)

    show ?thesis
      using step remap_cons
      by (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin
        dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost dest: )
  qed
qed


lemma rtranclp_GC_remap_ran_m_no_new_map:
  \<open>GC_remap\<^sup>*\<^sup>*  S S'  \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow> C \<in># dom_m (fst S)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (cases \<open>C \<in># dom_m (fst y)\<close>)
      (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost)
  done

lemma rtranclp_GC_remap_learned_clss_lD:
  \<open>GC_remap\<^sup>*\<^sup>* (N, x, m) (N', x', m') \<Longrightarrow> learned_clss_l N + learned_clss_l m  = learned_clss_l N'  + learned_clss_l m'\<close>
  by (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
    (auto dest: GC_remap_learned_clss_l_old_new)

lemma rtranclp_GC_remap_learned_clss_l:
  \<open>GC_remap\<^sup>*\<^sup>* (x1a, Map.empty, fmempty) (fmempty, m, x1ad) \<Longrightarrow> learned_clss_l x1ad = learned_clss_l x1a\<close>
  by (auto dest!: rtranclp_GC_remap_learned_clss_lD[of _ _ _ _ _ _])

lemma remap_cons2:
  assumes
      \<open>C' \<notin># dom_m new\<close> and
      \<open>C \<in># dom_m N\<close> and
      \<open>(the \<circ>\<circ> fst) (snd (N, m, new)) `# mset_set (dom (fst (snd (N, m, new)))) =
        dom_m (snd (snd (N, m, new)))\<close> and
      \<open>\<And>x. x \<in># dom_m (fst (N, m, new)) \<Longrightarrow> x \<notin> dom (fst (snd (N, m, new)))\<close> and
      \<open>finite (dom m)\<close>
  shows
    \<open>GC_remap (N, m, new) (fmdrop C N, m(C \<mapsto> C'), fmupd C' (the (fmlookup N C)) new)\<close>
proof -
  have 3: \<open>C \<in> dom m \<Longrightarrow> False\<close>
    apply (drule mk_disjoint_insert)
    using assms
    apply (auto 5 5 simp: ran_def)
    done

  have 4: \<open>False\<close> if C': \<open>C' \<in> ran m\<close>
  proof -
    obtain a where a: \<open>a \<in> dom m\<close> and [simp]: \<open>m a = Some C'\<close>
      using that C' unfolding ran_def
      by auto
    show False
      using mk_disjoint_insert[OF a] assms by (auto simp: union_single_eq_member)
  qed

  show ?thesis
    apply (rule remap_cons)
    apply (rule assms(1))
    apply (rule assms(2))
    apply (use 3 in fast)
    apply (use 4 in fast)
    done
qed


inductive_cases GC_remapE: \<open>GC_remap S T\<close>

lemma rtranclp_GC_remap_finite_map:
  \<open>GC_remap\<^sup>*\<^sup>*  S S'  \<Longrightarrow> finite (dom (fst (snd S))) \<Longrightarrow> finite (dom (fst (snd S')))\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (auto elim: GC_remapE)
  done


lemma rtranclp_GC_remap_old_dom_map:
  \<open>GC_remap\<^sup>*\<^sup>*  R S  \<Longrightarrow> (\<And>x. x \<in># dom_m (fst R) \<Longrightarrow> x \<notin> dom (fst (snd R))) \<Longrightarrow>
       (\<And>x. x \<in># dom_m (fst S) \<Longrightarrow> x \<notin> dom (fst (snd S)))\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z x
    by (fastforce elim!: GC_remapE simp: distinct_mset_dom distinct_mset_set_mset_remove1_mset)
  done

lemma remap_cons2_rtranclp:
  assumes
      \<open>(the \<circ>\<circ> fst) (snd R) `# mset_set (dom (fst (snd R))) = dom_m (snd (snd R))\<close> and
      \<open>\<And>x. x \<in># dom_m (fst R) \<Longrightarrow> x \<notin> dom (fst (snd R))\<close> and
      \<open>finite (dom (fst (snd R)))\<close> and
      st: \<open>GC_remap\<^sup>*\<^sup>* R S\<close> and
      C': \<open>C' \<notin># dom_m (snd (snd S))\<close> and
      C: \<open>C \<in># dom_m (fst S)\<close>
  shows
    \<open>GC_remap\<^sup>*\<^sup>* R (fmdrop C (fst S), (fst (snd S))(C \<mapsto> C'), fmupd C' (the (fmlookup (fst S) C)) (snd (snd S)))\<close>
proof -
  have
    1: \<open>(the \<circ>\<circ> fst) (snd S) `# mset_set (dom (fst (snd S))) = dom_m (snd (snd S))\<close> and
    2: \<open>\<And>x. x \<in># dom_m (fst S) \<Longrightarrow> x \<notin> dom (fst (snd S))\<close> and
    3: \<open>finite (dom (fst (snd S)))\<close>
      using assms(1) assms(3) assms(4) rtranclp_GC_remap_map_ran apply blast
     apply (meson assms(2) assms(4) rtranclp_GC_remap_old_dom_map)
    using assms(3) assms(4) rtranclp_GC_remap_finite_map by blast
  have 5: \<open>GC_remap S
     (fmdrop C (fst S), (fst (snd S))(C \<mapsto> C'), fmupd C' (the (fmlookup (fst S) C)) (snd (snd S)))\<close>
    using remap_cons2[OF C' C, of \<open>(fst (snd S))\<close>] 1 2 3 by (cases S) auto
  show ?thesis
    using 5 st by simp
qed

lemma (in -) fmdom_fmrestrict_set: \<open>fmdrop xa (fmrestrict_set s N) = fmrestrict_set (s - {xa}) N\<close>
  by (rule fmap_ext_fmdom)
   (auto simp: fset_fmdom_fmrestrict_set fmember.rep_eq notin_fset)

lemma (in -) GC_clauses_GC_remap:
  \<open>GC_clauses N fmempty \<le> SPEC(\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N'') \<and>
    0 \<notin># dom_m N'')\<close>
proof -
  let ?remap = \<open>(GC_remap)\<^sup>*\<^sup>*  (N, \<lambda>_. None, fmempty)\<close>
  note remap = remap_cons2_rtranclp[of \<open>(N, \<lambda>_. None, fmempty)\<close>, of \<open>(a, b, c)\<close> for a b c, simplified]
  define I where
    \<open>I a b \<equiv> (\<lambda>(old :: nat clauses_l, new :: nat clauses_l, m :: nat \<Rightarrow> nat option).
      ?remap (old, m, new) \<and> 0 \<notin># dom_m new \<and>
      set_mset (dom_m old) \<subseteq> set b)\<close>
      for a b :: \<open>nat list\<close>
  have I0: \<open>set_mset (dom_m N) \<subseteq> set x \<Longrightarrow> I [] x (N, fmempty, \<lambda>_. None)\<close> for x
    unfolding I_def
    by (auto intro!: fmap_ext_fmdom simp: fset_fmdom_fmrestrict_set fmember.rep_eq
      notin_fset dom_m_def)

  have I_drop: \<open>I (l1 @ [xa]) l2
       (fmdrop xa a, fmupd xb (a \<propto> xa, irred a xa) aa, ba(xa \<mapsto> xb))\<close>
  if
    \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
    \<open>x = l1 @ xa # l2\<close> and
    \<open>I l1 (xa # l2) \<sigma>\<close> and
    \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
    \<open>\<sigma> = (a, b)\<close> and
    \<open>b = (aa, ba)\<close> and
    \<open>xa \<in># dom_m a\<close> and
    \<open>xb \<notin># dom_m aa \<and> xb \<noteq> 0\<close>
    for x xa l1 l2 \<sigma> a b aa ba xb
  proof -
    have \<open>insert xa (set l2) - set l1 - {xa} = set l2 - insert xa (set l1)\<close>
      by auto
    have \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty)
        (fmdrop xa a, ba(xa \<mapsto> xb), fmupd xb (the (fmlookup a xa)) aa)\<close>
      by (rule remap)
        (use that in \<open>auto simp: I_def\<close>)
    then show ?thesis
      using that distinct_mset_dom[of a] distinct_mset_dom[of aa] unfolding I_def prod.simps
      apply (auto dest!: mset_le_subtract[of \<open>dom_m _\<close> _ \<open>{#xa#}\<close>] simp: mset_set.insert_remove)
      by (metis Diff_empty Diff_insert0 add_mset_remove_trivial finite_set_mset
        finite_set_mset_mset_set insert_subset_eq_iff mset_set.remove set_mset_mset subseteq_remove1)
  qed

  have I_notin: \<open>I (l1 @ [xa]) l2 (a, aa, ba)\<close>
    if
      \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
      \<open>x = l1 @ xa # l2\<close> and
      \<open>I l1 (xa # l2) \<sigma>\<close> and
      \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
      \<open>\<sigma> = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>xa \<notin># dom_m a\<close>
      for x xa l1 l2 \<sigma> a b aa ba
  proof -
    show ?thesis
      using that unfolding I_def
      by (auto dest!: multi_member_split)
  qed
  have early_break: \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
     if
       \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
       \<open>x = l1 @ l2\<close> and
       \<open>I l1 l2 \<sigma>\<close> and
       \<open>\<not> (case \<sigma> of (N, N', m) \<Rightarrow> True)\<close> and
       \<open>\<sigma> = (a, b)\<close> and
       \<open>b = (aa, ba)\<close> and
       \<open>(aa, ba) = (x1, x2)\<close>
      for x l1 l2 \<sigma> a b aa ba x1 x2
   proof -
     show ?thesis using that by auto
   qed

  have final_rel: \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
  if
    \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
    \<open>I x [] \<sigma>\<close> and
    \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
    \<open>\<sigma> = (a, b)\<close> and
    \<open>b = (aa, ba)\<close> and
    \<open>(aa, ba) = (x1, x2)\<close>
  proof -
    show \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
      using that
      by (auto simp: I_def)
  qed
  have final_rel: \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close> \<open>0 \<notin># dom_m x1\<close>
    if
      \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
      \<open>I x [] \<sigma>\<close> and
      \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
      \<open>\<sigma> = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>(aa, ba) = (x1, x2)\<close>
    for x \<sigma> a b aa ba x1 x2
    using that
    by (auto simp: I_def)
  show ?thesis
    unfolding GC_clauses_def
    apply (refine_vcg nfoldli_rule[where I = I])
    subgoal by (rule I0)
    subgoal by (rule I_drop)
    subgoal by (rule I_notin)
    \<comment> \<open>Final properties:\<close>
    subgoal for x l1 l2 \<sigma> a b aa ba x1 x2
      by (rule early_break)
    subgoal
      by (auto simp: I_def)
    subgoal
      by (rule final_rel) assumption+
    subgoal
      by (rule final_rel) assumption+
    done
qed


definition cdcl_twl_full_restart_l_prog where
\<open>cdcl_twl_full_restart_l_prog S = do {
   \<comment> \<open> \<^term>\<open>remove_one_annot_true_clause_imp S\<close>\<close>
    ASSERT(mark_to_delete_clauses_l_pre S);
    T \<leftarrow> mark_to_delete_clauses_l S;
    ASSERT (mark_to_delete_clauses_l_post S T);
    RETURN T
  }\<close>


definition cdcl_GC_clauses_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
\<open>cdcl_GC_clauses_pre S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> twl_st_l None \<and>
    twl_list_invs S \<and> twl_struct_invs T \<and>
    get_conflict_l S = None \<and> clauses_to_update_l S = {#} \<and>
    count_decided (get_trail_l S) = 0 \<and> (\<forall>L\<in>set (get_trail_l S). mark_of L = 0)
  ) \<close>

definition cdcl_GC_clauses :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>cdcl_GC_clauses = (\<lambda>(M, N, D, NE, UE, NS, US, WS, Q). do {
  ASSERT(cdcl_GC_clauses_pre (M, N, D, NE, UE, NS, US, WS, Q));
  b \<leftarrow> SPEC(\<lambda>b. True);
  if b then do {
    (N', _) \<leftarrow> SPEC (\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N'') \<and>
      0 \<notin># dom_m N'');
    RETURN (M, N', D, NE, UE, NS, {#}, WS, Q)
  }
  else RETURN (M, N, D, NE, UE, NS, {#}, WS, Q)})\<close>

lemma cdcl_GC_clauses_cdcl_twl_restart_l:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    count_dec: \<open>count_decided (get_trail_l S) = 0\<close> and
    mark: \<open>\<forall>L\<in>set (get_trail_l S). mark_of L = 0\<close>
  shows \<open>cdcl_GC_clauses S \<le> SPEC (\<lambda>T. cdcl_twl_restart_l S T \<and>
      get_trail_l S = get_trail_l T)\<close>
proof -
  show ?thesis
    unfolding cdcl_GC_clauses_def
    apply refine_vcg
    subgoal using assms unfolding cdcl_GC_clauses_pre_def by blast
    subgoal using confl upd count_dec mark by (auto simp: cdcl_twl_restart_l.simps
        valid_trail_reduction_refl
      dest: rtranclp_GC_remap_init_clss_l_old_new rtranclp_GC_remap_learned_clss_l_old_new)
    subgoal by simp
    subgoal using confl upd count_dec mark by (auto simp: cdcl_twl_restart_l.simps
        valid_trail_reduction_refl cdcl_GC_clauses_pre_def twl_list_invs_def)
    subgoal by simp
    done
qed

lemma remove_one_annot_true_clause_cdcl_twl_restart_l_spec:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>SPEC(remove_one_annot_true_clause\<^sup>+\<^sup>+ S) \<le> SPEC(\<lambda>T. cdcl_twl_restart_l S T)\<close>
proof -
  have \<open>cdcl_twl_restart_l S U'\<close>
    if rem: \<open>remove_one_annot_true_clause\<^sup>+\<^sup>+ S U'\<close> for U'
  proof -
    have n_d: \<open>no_dup (get_trail_l S)\<close>
      using ST struct_invs unfolding twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (simp add: twl_st twl_st_l)
    have subs_U': \<open>get_subsumed_learned_clauses_l U' = {#}\<close>
      using rem unfolding tranclp_unfold_end
      by (cases U'; auto simp: remove_one_annot_true_clause.simps)
    have SU': \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S U'\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[of S U' T, OF
        tranclp_into_rtranclp[OF rem] list_invs
        confl upd ST struct_invs]
      apply -
      apply normalize_goal+
      by auto
    moreover have \<open>cdcl_twl_restart_l S U'\<close> if \<open>S = U'\<close>
      using confl upd rem rtranclp_cdcl_twl_restart_l_no_dup[OF SU'] list_invs
       n_d subs_U'
      unfolding that[symmetric]
      by (cases S)
        (auto simp: cdcl_twl_restart_l.simps twl_list_invs_def
         dest: no_dup_same_annotD)
    ultimately show \<open>cdcl_twl_restart_l S U'\<close>
      using tranclp_cdcl_twl_restart_l_cdcl_is_cdcl_twl_restart_l[of S U', OF _ n_d]
      by (meson rtranclpD)
  qed
  then show ?thesis
    by force
qed

definition (in -) cdcl_twl_local_restart_l_spec :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>cdcl_twl_local_restart_l_spec = (\<lambda>(M, N, D, NE, UE, NS, US, W, Q). do {
      ASSERT(restart_abs_l_pre (M, N, D, NE, UE, NS, US, W, Q) False);
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#}) \<or> (M' = M \<and> Q' = Q));
      RETURN (M, N, D, NE, UE, NS, {#}, W, Q)
   })\<close>

definition cdcl_twl_restart_l_prog where
\<open>cdcl_twl_restart_l_prog S = do {
   b \<leftarrow> SPEC(\<lambda>_. True);
   if b then cdcl_twl_local_restart_l_spec S else cdcl_twl_full_restart_l_prog S
  }\<close>


lemma cdcl_twl_local_restart_l_spec_cdcl_twl_restart_l:
  assumes inv: \<open>restart_abs_l_pre S False\<close>
  shows \<open>cdcl_twl_local_restart_l_spec S \<le> SPEC (cdcl_twl_restart_l S)\<close>
proof -
  obtain T where
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    stgy_invs: \<open>twl_stgy_invs T\<close> and
    confl: \<open>get_conflict_l S = None\<close>
    using inv unfolding restart_abs_l_pre_def restart_prog_pre_def
    apply - apply normalize_goal+
    by (auto simp: twl_st_l twl_st)
  have S: \<open>S = (get_trail_l S, snd S)\<close>
    by (cases S) auto

  obtain M N D NE UE NS US W Q where
    S: \<open>S = (M, N, D, NE, UE, NS, US, W, Q)\<close>
    by (cases S)
  have restart: \<open>cdcl_twl_restart_l S (M', N, D, NE, UE, NS, {#}, W, Q')\<close>
    if decomp': \<open>(\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#}) \<or> (M' = M \<and> Q' = Q)\<close>
    for M' K M2 Q'
  proof -
    consider
      (nope) \<open>M = M'\<close> and \<open>Q' = Q\<close> |
      (decomp) K M2 where \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
        \<open>Q' = {#}\<close>
      using decomp' by auto
    then show ?thesis
    proof cases
      case [simp]: nope
      have valid: \<open>valid_trail_reduction M M'\<close>
        by (use valid_trail_reduction.keep_red[of M'] in \<open>auto simp: S\<close>)
      have
        S1: \<open>S = (M, N, None, NE, UE, NS, US, {#}, Q)\<close> and
        S2 : \<open>(M', N, D, NE, UE, NS, {#}, W, Q') =
          (M', N, None, NE + mset `# {#}, UE + mset `# {#}, NS, {#}, {#}, Q)\<close>
        using confl upd unfolding S
        by auto
      have
        \<open>\<forall>C\<in>#clauses_to_update_l S. C \<in># dom_m (get_clauses_l S)\<close> and
        dom0: \<open>0 \<notin># dom_m (get_clauses_l S)\<close> and
        annot: \<open>\<And>L C. Propagated L C \<in> set (get_trail_l S) \<Longrightarrow>
           0 < C \<Longrightarrow>
             (C \<in># dom_m (get_clauses_l S) \<and>
            L \<in> set (watched_l (get_clauses_l S \<propto> C)) \<and>
            (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow> L = get_clauses_l S \<propto> C ! 0))\<close> and
        \<open>distinct_mset (clauses_to_update_l S)\<close>
        using list_invs unfolding twl_list_invs_def S[symmetric] by auto
      have n_d: \<open>no_dup M\<close>
        using struct_invs ST unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: twl_st_l twl_st S)
      have propa_MM: \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow> E=E'\<close> for L E E'
        using n_d
        by (auto simp: S twl_list_invs_def
            dest!: split_list[of \<open>Propagated L E\<close> M]
            split_list[of \<open>Propagated L E'\<close> M]
            dest: no_dup_same_annotD
            elim!: list_match_lel_lel)

      show ?thesis
        unfolding S[symmetric] S1 S2
        apply (rule cdcl_twl_restart_l.intros)
        subgoal by (rule valid)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal using propa_MM annot unfolding S by fastforce
        subgoal using propa_MM annot unfolding S by fastforce
        subgoal using propa_MM annot unfolding S by fastforce
        subgoal using dom0 unfolding S by auto
        subgoal by auto
        subgoal by auto
        done
    next
      case decomp note decomp = this(1) and Q = this(2)
      have valid: \<open>valid_trail_reduction M M'\<close>
        by (use valid_trail_reduction.backtrack_red[OF decomp, of M'] in \<open>auto simp: S\<close>)
      have
        \<open>\<forall>C\<in>#clauses_to_update_l S. C \<in># dom_m (get_clauses_l S)\<close> and
        dom0: \<open>0 \<notin># dom_m (get_clauses_l S)\<close> and
        annot: \<open>\<And>L C. Propagated L C \<in> set (get_trail_l S) \<Longrightarrow>
           0 < C \<Longrightarrow>
             (C \<in># dom_m (get_clauses_l S) \<and>
            L \<in> set (watched_l (get_clauses_l S \<propto> C)) \<and>
            (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow> L = get_clauses_l S \<propto> C ! 0))\<close> and
        \<open>distinct_mset (clauses_to_update_l S)\<close>
        using list_invs unfolding twl_list_invs_def S[symmetric] by auto
      obtain M3 where M: \<open>M = M3 @ Decided K # M'\<close>
        using decomp by auto
      have n_d: \<open>no_dup M\<close>
        using struct_invs ST unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: twl_st_l twl_st S)
      have
        S1: \<open>S = (M, N, None, NE, UE, NS, US, {#}, Q)\<close> and
        S2 : \<open>(M', N, D, NE, UE, NS, {#}, W, Q') = (M', N, None, NE + mset `# {#}, UE + mset `# {#},
          NS, {#}, {#}, {#})\<close>
        using confl upd unfolding S Q
        by auto
      have propa_MM: \<open>Propagated L E \<in> set M \<Longrightarrow> Propagated L E' \<in> set M' \<Longrightarrow> E=E'\<close> for L E E'
        using n_d unfolding M
        by (auto simp: S twl_list_invs_def
            dest!: split_list[of \<open>Propagated L E\<close> M]
            split_list[of \<open>Propagated L E'\<close> M]
            dest: no_dup_same_annotD
            elim!: list_match_lel_lel)

      show ?thesis
        unfolding S[symmetric] S1 S2
        apply (rule cdcl_twl_restart_l.intros)
        subgoal by (rule valid)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal using propa_MM annot unfolding S by fastforce
        subgoal using propa_MM annot unfolding S by fastforce
        subgoal using propa_MM annot unfolding S by fastforce
        subgoal using dom0 unfolding S by auto
        subgoal using decomp unfolding S by auto
        subgoal by auto
        done
    qed
  qed
  show ?thesis
    apply (subst S)
    unfolding cdcl_twl_local_restart_l_spec_def prod.case RES_RETURN_RES2 less_eq_nres.simps
      uncurry_def
    apply (rule ASSERT_leI)
    using assms[unfolded S] apply assumption
    apply clarsimp
    apply (rule restart)
    apply simp
    done
qed

definition (in -) cdcl_twl_local_restart_l_spec0 :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>cdcl_twl_local_restart_l_spec0 = (\<lambda>(M, N, D, NE, UE, NS, US, W, Q). do {
      ASSERT(restart_abs_l_pre (M, N, D, NE, UE, NS, US, W, Q) False);
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#} \<and> count_decided M' = 0) \<or> (M' = M \<and> Q' = Q \<and> count_decided M' = 0));
      RETURN (M, N, D, NE, UE, NS, {#}, W, Q)
   })\<close>

lemma cdcl_twl_local_restart_l_spec0_cdcl_twl_local_restart_l_spec:
  \<open>cdcl_twl_local_restart_l_spec0 S \<le> \<Down>{(S, S'). S = S' \<and> count_decided (get_trail_l S) = 0}
    (cdcl_twl_local_restart_l_spec S)\<close>
  unfolding cdcl_twl_local_restart_l_spec0_def
    cdcl_twl_local_restart_l_spec_def
    by refine_vcg (auto simp: RES_RETURN_RES2)


definition cdcl_twl_full_restart_l_GC_prog_pre
  :: \<open>'v twl_st_l \<Rightarrow> bool\<close>
where
  \<open>cdcl_twl_full_restart_l_GC_prog_pre S \<longleftrightarrow>
   (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and> twl_list_invs S \<and>
      get_conflict T = None)\<close>

definition cdcl_twl_full_restart_l_GC_prog where
\<open>cdcl_twl_full_restart_l_GC_prog S = do {
   ASSERT(cdcl_twl_full_restart_l_GC_prog_pre S);
    S' \<leftarrow> cdcl_twl_local_restart_l_spec0 S;
    T \<leftarrow> remove_one_annot_true_clause_imp S';
    ASSERT(mark_to_delete_clauses_l_pre T);
    U \<leftarrow> mark_to_delete_clauses_l T;
    V \<leftarrow> cdcl_GC_clauses U;
    ASSERT(cdcl_twl_restart_l S V);
    RETURN V
  }\<close>

lemma cdcl_twl_full_restart_l_prog_spec:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>cdcl_twl_full_restart_l_prog S \<le> \<Down> Id (SPEC(remove_one_annot_true_clause\<^sup>+\<^sup>+ S))\<close>
proof -
  have mark_to_delete_clauses_l:
    \<open>mark_to_delete_clauses_l x \<le> SPEC (\<lambda>T. ASSERT (mark_to_delete_clauses_l_post U T) \<bind>
             (\<lambda>_. RETURN T)
             \<le> SPEC (remove_one_annot_true_clause\<^sup>+\<^sup>+ U))\<close>
    if
      Ux: \<open>(x, U) \<in> Id\<close> and
      U: \<open>U \<in> Collect (remove_one_annot_true_clause\<^sup>*\<^sup>* S)\<close>
      for x U
  proof -
    from U have SU: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U\<close> by simp
    have x: \<open>x = U\<close>
      using Ux by auto
    obtain V where
      SU': \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S U\<close> and
      UV: \<open>(U, V) \<in> twl_st_l None\<close> and
      TV: \<open>cdcl_twl_restart\<^sup>*\<^sup>* T V\<close> and
      struct_invs_V: \<open>twl_struct_invs V\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF SU list_invs
        confl upd ST struct_invs]
      by auto
    have
      confl_U: \<open>get_conflict_l U = None\<close> and
      upd_U: \<open>clauses_to_update_l U = {#}\<close>
      using rtranclp_remove_one_annot_true_clause_get_conflict_l[OF SU]
         rtranclp_remove_one_annot_true_clause_clauses_to_update_l[OF SU] confl upd
      by auto
    have list_U: \<open>twl_list_invs U\<close>
      using SU' list_invs rtranclp_cdcl_twl_restart_l_list_invs by blast
     have [simp]:
      \<open>remove_one_annot_true_clause\<^sup>+\<^sup>+ U V' \<Longrightarrow>  mark_to_delete_clauses_l_post U V'\<close> for V'
      unfolding mark_to_delete_clauses_l_post_def
      using UV struct_invs_V list_U confl_U upd_U
      by (blast dest: tranclp_into_rtranclp)
    show ?thesis
      unfolding x
      by (rule mark_to_delete_clauses_l_spec[OF UV list_U struct_invs_V confl_U upd_U,
         THEN order_trans])
       (auto intro: RES_refine)
  qed
  have 1: \<open>SPEC (remove_one_annot_true_clause\<^sup>*\<^sup>* S) = do {
       T \<leftarrow> SPEC (remove_one_annot_true_clause\<^sup>*\<^sup>* S);
       SPEC (remove_one_annot_true_clause\<^sup>*\<^sup>* T)
    }\<close>
  by (auto simp: RES_RES_RETURN_RES)
  have H: \<open>mark_to_delete_clauses_l_pre T\<close>
    if
      \<open>(T, U) \<in> Id\<close> and
      \<open>U \<in> Collect (remove_one_annot_true_clause\<^sup>*\<^sup>* S)\<close>
    for T U
  proof -
    show ?thesis
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[of S U,
          OF _ list_invs confl upd ST struct_invs] that list_invs
      unfolding mark_to_delete_clauses_l_pre_def
      by (force intro: rtranclp_cdcl_twl_restart_l_list_invs)
  qed
  show ?thesis
    unfolding cdcl_twl_full_restart_l_prog_def
    apply (refine_vcg mark_to_delete_clauses_l)
    subgoal
      using assms
      unfolding mark_to_delete_clauses_l_pre_def
      by blast
    subgoal by auto
    subgoal by (auto simp: assert_bind_spec_conv)
    done
qed

lemma valid_trail_reduction_count_dec_ge:
  \<open>valid_trail_reduction M M' \<Longrightarrow> count_decided M \<ge> count_decided M'\<close>
  apply (induction rule: valid_trail_reduction.induct)
  subgoal for K M M'
    using trail_renumber_count_dec
    by (fastforce simp: dest!: get_all_ann_decomposition_exists_prepend)
  subgoal by (auto dest: trail_renumber_count_dec)
  done

lemma cdcl_twl_restart_l_count_dec_ge:
  \<open>cdcl_twl_restart_l S T \<Longrightarrow> count_decided (get_trail_l S) \<ge> count_decided (get_trail_l T)\<close>
  by (induction rule: cdcl_twl_restart_l.induct)
    (auto dest!: valid_trail_reduction_count_dec_ge)

lemma valid_trail_reduction_lit_of_nth:
  \<open>valid_trail_reduction M M' \<Longrightarrow> length M = length M' \<Longrightarrow> i < length M \<Longrightarrow>
    lit_of (M ! i) = lit_of (M' ! i)\<close>
  apply (induction rule: valid_trail_reduction.induct)
  subgoal premises p for K M'' M2
    using arg_cong[OF p(2), of length] p(1) arg_cong[OF p(2), of \<open>\<lambda>xs. xs ! i\<close>] p(4)
    by (auto simp: nth_map nth_append nth_Cons split: if_splits
      dest!: get_all_ann_decomposition_exists_prepend)
  subgoal premises p
    using arg_cong[OF p(1), of length] p(3) arg_cong[OF p(1), of \<open>\<lambda>xs. xs ! i\<close>] p(4)
    by (auto simp: nth_map nth_append nth_Cons split: if_splits
      dest!: get_all_ann_decomposition_exists_prepend)
  done

lemma cdcl_twl_restart_l_lit_of_nth:
  \<open>cdcl_twl_restart_l S U \<Longrightarrow> i < length (get_trail_l U) \<Longrightarrow> is_proped (get_trail_l U ! i) \<Longrightarrow>
    length (get_trail_l S) = length (get_trail_l U) \<Longrightarrow>
    lit_of (get_trail_l S ! i) = lit_of (get_trail_l U ! i)\<close>
  apply (induction rule: cdcl_twl_restart_l.induct)
  subgoal for M M' N N' NE' UE' NE UE Q Q'
    using valid_trail_reduction_length_leD[of M M']
    valid_trail_reduction_lit_of_nth[of M M' i]
    by auto
  done

lemma valid_trail_reduction_is_decided_nth:
  \<open>valid_trail_reduction M M' \<Longrightarrow> length M = length M' \<Longrightarrow> i < length M \<Longrightarrow>
    is_decided (M ! i) = is_decided (M' ! i)\<close>
  apply (induction rule: valid_trail_reduction.induct)
  subgoal premises p for K M'' M2
    using arg_cong[OF p(2), of length] p(1) arg_cong[OF p(3), of \<open>\<lambda>xs. xs ! i\<close>] p(4)
    by (auto simp: nth_map nth_append nth_Cons split: if_splits
      dest!: get_all_ann_decomposition_exists_prepend)
  subgoal premises p
    using arg_cong[OF p(1), of length] p(3) arg_cong[OF p(2), of \<open>\<lambda>xs. xs ! i\<close>] p(4)
    by (auto simp: nth_map nth_append nth_Cons split: if_splits
      dest!: get_all_ann_decomposition_exists_prepend)
  done

lemma cdcl_twl_restart_l_mark_of_same_or_0:
  \<open>cdcl_twl_restart_l S U \<Longrightarrow> i < length (get_trail_l U) \<Longrightarrow> is_proped (get_trail_l U ! i) \<Longrightarrow>
    length (get_trail_l S) = length (get_trail_l U) \<Longrightarrow>
     (mark_of (get_trail_l U ! i) > 0 \<Longrightarrow> mark_of (get_trail_l S ! i) > 0 \<Longrightarrow>
        mset (get_clauses_l S \<propto> mark_of (get_trail_l S ! i))
	 = mset (get_clauses_l U \<propto> mark_of (get_trail_l U ! i)) \<Longrightarrow> P) \<Longrightarrow>
    (mark_of (get_trail_l U ! i) = 0 \<Longrightarrow> P) \<Longrightarrow> P\<close>
  apply (induction rule: cdcl_twl_restart_l.induct)
  subgoal for M M' N N' NE' UE' NE UE Q Q'
    using valid_trail_reduction_length_leD[of M M']
    valid_trail_reduction_lit_of_nth[of M M' i]
    valid_trail_reduction_is_decided_nth[of M M' i]
    split_list[of \<open>M ! i\<close> M, OF nth_mem] split_list[of \<open>M' ! i\<close> M', OF nth_mem]
    by (cases \<open>M ! i\<close>; cases \<open>M' ! i\<close>)
      (force simp: all_conj_distrib)+
  done


lemma cdcl_twl_full_restart_l_GC_prog_cdcl_twl_restart_l:
  assumes
    ST: \<open>(S, S') \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    stgy_invs: \<open>twl_stgy_invs S'\<close>
  shows \<open>cdcl_twl_full_restart_l_GC_prog S \<le> \<Down> Id (SPEC (\<lambda>T. cdcl_twl_restart_l S T))\<close>
proof -
  let ?f = \<open>(\<lambda>S T. cdcl_twl_restart_l S T)\<close>
  let ?f1 = \<open>\<lambda>S S'. (?f S S' \<or> S = S') \<and> count_decided (get_trail_l S') = 0\<close>
  let ?f1' = \<open>\<lambda>S S'. (?f S S') \<and> count_decided (get_trail_l S') = 0\<close>
  let ?f2 = \<open>\<lambda>S S'. ?f S S' \<and> (\<forall>L \<in> set (get_trail_l S'). mark_of L = 0) \<and>
    length (get_trail_l S) = length (get_trail_l S')\<close>
  let ?f3 = \<open>\<lambda>S S'. ?f1 S S' \<and> (\<forall>L \<in> set (get_trail_l S'). mark_of L = 0) \<and>
    length (get_trail_l S) = length (get_trail_l S')\<close>
  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using struct_invs ST unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: twl_st)
  then have alt_def: \<open>SPEC (\<lambda>T. cdcl_twl_restart_l S T) \<ge> do {
    S' \<leftarrow> SPEC (\<lambda>S'. ?f1 S S');
    T \<leftarrow> SPEC (?f2 S');
    U \<leftarrow> SPEC (?f3 T);
    V \<leftarrow> SPEC (\<lambda>V. ?f3 U V);
    RETURN V
    }\<close>
    unfolding RETURN_def RES_RES_RETURN_RES apply -
    apply (rule RES_rule)
    unfolding UN_iff
    apply (elim bexE)+
    unfolding mem_Collect_eq
    by (metis (full_types) cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l singletonD)

  have 1: \<open>remove_one_annot_true_clause_imp T \<le> SPEC (\<lambda>V. ?f2 U V)\<close>
    if
      \<open>(T, U) \<in> Id\<close> and
      \<open>U \<in> Collect (\<lambda>S'. ?f1 S S')\<close>
    for T U
  proof -
    have \<open>T = U\<close> and \<open>?f S T \<or> S = T\<close> and count_0: \<open>count_decided (get_trail_l T) = 0\<close>
      using that by auto
    have confl: \<open>get_conflict_l T = None\<close>
      using \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain T' where
      TT': \<open>(T, T') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs T\<close> and
      struct_invs: \<open>twl_struct_invs T'\<close> and
      clss_upd: \<open>clauses_to_update_l T = {#}\<close> and
      \<open>cdcl_twl_restart S' T' \<or> S' = T'\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of T] assms
        \<open>?f S T \<or> S = T\<close>
      by blast
    show ?thesis
      unfolding \<open>T = U\<close>[symmetric]
      by (rule remove_one_annot_true_clause_imp_spec_lev0[OF TT' list_invs struct_invs confl
          clss_upd, THEN order_trans])
       (use count_0 remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF TT' list_invs struct_invs
           confl clss_upd] n_d \<open>?f S T \<or> S = T\<close>
	   remove_one_annot_true_clause_map_mark_of_same_or_0[of T] in
         \<open>auto dest: cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
	   simp: rtranclp_remove_one_annot_true_clause_count_dec\<close>)
  qed

  have mark_to_delete_clauses_l_pre: \<open>mark_to_delete_clauses_l_pre U\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>U' \<in> Collect (?f2 T')\<close>
    for T T' U U'
  proof -
    have \<open>T = T'\<close> \<open>U = U'\<close> and \<open>?f T U\<close> and \<open>?f S T \<or> S = T\<close>
      using that by auto
    then have \<open>?f S U \<or> S = U\<close>
      using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
      by blast
    have confl: \<open>get_conflict_l U = None\<close>
      using \<open>?f T U\<close> \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain U' where
      TT': \<open>(U, U') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs U\<close> and
      struct_invs: \<open>twl_struct_invs U'\<close> and
      clss_upd: \<open>clauses_to_update_l U = {#}\<close> and
      \<open>cdcl_twl_restart S' U' \<or> S' = U'\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of U] \<open>?f S U \<or> S = U\<close> assms that[of S']
      by blast
    then show ?thesis
      unfolding mark_to_delete_clauses_l_pre_def
      by blast
  qed
  have 2: \<open>mark_to_delete_clauses_l U \<le> SPEC (\<lambda>V. ?f3 U' V)\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      UU': \<open>(U, U') \<in> Id\<close> and
      U: \<open>U' \<in> Collect (?f2 T')\<close> and
      pre: \<open>mark_to_delete_clauses_l_pre U\<close>
    for T T' U U'
  proof -
    have \<open>T = T'\<close> \<open>U = U'\<close> and \<open>?f T U\<close> and \<open>?f S T \<or> S = T\<close>
      using that by auto
    then have SU: \<open>?f S U\<close>
      using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
      by blast

    obtain V where
      TV: \<open>(U, V) \<in> twl_st_l None\<close> and
      struct: \<open>twl_struct_invs V\<close> and
      list_invs: \<open>twl_list_invs U\<close>
      using pre unfolding mark_to_delete_clauses_l_pre_def
      by auto
    have confl: \<open>get_conflict_l U = None\<close> and upd: \<open>clauses_to_update_l U = {#}\<close> and UU[simp]: \<open>U' = U\<close>
      using U UU' \<open>?f T U\<close> confl  \<open>?f S T \<or> S = T\<close> assms
      by (auto simp: cdcl_twl_restart_l.simps)
    show ?thesis
      by (rule mark_to_delete_clauses_l_spec[OF TV list_invs struct confl upd, THEN order_trans],
         subst Down_id_eq)
       (use remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF TV list_invs struct confl upd]
          cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[OF _ _ n_d, of T] that
          ST in \<open>auto dest!: rtranclp_cdcl_twl_restart_l_count_dec\<close>)
  qed
  have 3: \<open>cdcl_GC_clauses V \<le> SPEC (?f3 V')\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>U' \<in> Collect (?f2 T')\<close> and
      \<open>mark_to_delete_clauses_l_pre U\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>V' \<in> Collect (?f3 U')\<close>
    for T T' U U' V V'
  proof -
    have eq: \<open>U' = U\<close>
      using that by auto
    have st: \<open>T = T'\<close> \<open>U = U'\<close> \<open>V = V'\<close> and \<open>?f S T \<or> S = T\<close> and \<open>?f T U\<close> and
       \<open>?f U V \<or> U = V\<close> and
      le_UV: \<open>length (get_trail_l U) = length (get_trail_l V)\<close> and
      mark0: \<open>\<forall>L\<in>set (get_trail_l V'). mark_of L = 0\<close> and
      count_dec: \<open>count_decided (get_trail_l V') = 0\<close>
      using that by (auto dest!: rtranclp_cdcl_twl_restart_l_count_dec)
    then have \<open>?f S V\<close>
      using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
      by blast
    have mark: \<open>mark_of (get_trail_l V ! i) = 0\<close> if \<open>i < length (get_trail_l V)\<close> for i
      using that
      by (use st that le_UV count_dec mark0 in
        \<open>auto simp: count_decided_0_iff is_decided_no_proped_iff\<close>)
    then have count_dec: \<open>count_decided (get_trail_l V') = 0\<close> and
      mark: \<open>\<And>L. L \<in> set (get_trail_l V') \<Longrightarrow> mark_of L = 0\<close>
      using cdcl_twl_restart_l_count_dec_ge[of U V] that \<open>?f U V \<or> U = V\<close>
      by (auto dest!: rtranclp_cdcl_twl_restart_l_count_dec
        rtranclp_cdcl_twl_restart_l_count_dec)
    obtain W where
      UV: \<open>(V, W) \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs V\<close> and
      clss: \<open>clauses_to_update_l V = {#}\<close> and
      \<open>cdcl_twl_restart S' W\<close> and
      struct: \<open>twl_struct_invs W\<close>
      using cdcl_twl_restart_l_invs[OF assms(1,2,3) \<open>?f S V\<close>] unfolding eq by blast
    have confl: \<open>get_conflict_l V = None\<close>
      using \<open>?f S V\<close> unfolding eq
      by (auto simp: cdcl_twl_restart_l.simps)
    show ?thesis
      unfolding eq
      by (rule cdcl_GC_clauses_cdcl_twl_restart_l[OF UV list_invs struct confl clss, THEN order_trans])
       (use count_dec cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[OF _ _ n_d, of U']
         \<open>?f S V\<close> eq mark in \<open>auto simp: \<open>V = V'\<close>\<close>)
  qed
  have cdcl_twl_restart_l: \<open>cdcl_twl_restart_l S W\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>U' \<in> Collect (?f2 T')\<close> and
      \<open>mark_to_delete_clauses_l_pre U\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>V' \<in> Collect (?f3 U')\<close> and
      \<open>(W, W') \<in> Id\<close> and
      \<open>W' \<in> Collect (?f3 V')\<close>
    for T T' U U' V V' W W'
    using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[of S T U]
      cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[of S U V]
      cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[of S V W] that
    by fast

  show ?thesis
    unfolding cdcl_twl_full_restart_l_GC_prog_def
    apply (rule order_trans)
    prefer 2 apply (rule ref_two_step')
    apply (rule alt_def)
    apply refine_rcg
    subgoal
      using assms unfolding cdcl_twl_full_restart_l_GC_prog_pre_def
      by fastforce
    subgoal
      by (rule cdcl_twl_local_restart_l_spec0_cdcl_twl_local_restart_l_spec[THEN order_trans],
        subst (3) Down_id_eq[symmetric],
	rule order_trans,
        rule ref_two_step',
        rule cdcl_twl_local_restart_l_spec_cdcl_twl_restart_l,
        unfold restart_abs_l_pre_def, rule exI[of _ S'])
       (use assms in \<open>auto simp: restart_prog_pre_def conc_fun_RES\<close>)
    subgoal
      by (rule 1)
    subgoal for  T T' U U'
      by (rule mark_to_delete_clauses_l_pre)
    subgoal for T T' U U'
      by (rule 2)
    subgoal for T T' U U' V V'
      by (rule 3)
    subgoal for T T' U U' V V' W W'
      by (rule cdcl_twl_restart_l)
    done
qed


context twl_restart_ops
begin

definition restart_prog_l
  :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_l \<times> nat) nres"
where
  \<open>restart_prog_l S n brk = do {
     ASSERT(restart_abs_l_pre S brk);
     b \<leftarrow> restart_required_l S n;
     b2 \<leftarrow> SPEC(\<lambda>_. True);
     if b2 \<and> b \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_full_restart_l_GC_prog S;
       RETURN (T, n + 1)
     }
     else if b \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_l_prog S;
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>


lemma restart_prog_l_restart_abs_l:
  \<open>(uncurry2 restart_prog_l, uncurry2 restart_abs_l) \<in> Id \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_full_restart_l_prog:
    \<open>cdcl_twl_full_restart_l_prog S \<le> SPEC (\<lambda>T. cdcl_twl_restart_l S T)\<close>
    if
      inv: \<open>restart_abs_l_pre S brk\<close> and
      \<open>(b, ba) \<in> bool_rel\<close> and
      \<open>b \<in> {b. b \<longrightarrow> f n < size ( S)}\<close> and
      \<open>ba \<in> {b. b \<longrightarrow> f n < size ( S)}\<close> and
      brk: \<open>\<not>brk\<close>
    for b ba S brk n
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      list_invs: \<open>twl_list_invs S\<close> and
      upd: \<open>clauses_to_update_l S = {#}\<close> and
      stgy_invs: \<open>twl_stgy_invs T\<close> and
      confl: \<open>get_conflict_l S = None\<close>
      using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
      apply - apply normalize_goal+
      by (auto simp: twl_st)
    show ?thesis
      using cdcl_twl_full_restart_l_prog_spec[OF ST list_invs struct_invs
         confl upd]
        remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF ST list_invs struct_invs
         confl upd]
      by (rule conc_trans_additional)
  qed
  have cdcl_twl_full_restart_l_GC_prog:
    \<open>cdcl_twl_full_restart_l_GC_prog S \<le> SPEC (cdcl_twl_restart_l S)\<close>
    if
      inv: \<open>restart_abs_l_pre S brk\<close> and
      brk: \<open>ba \<and> b2a \<and> \<not> brk\<close>
    for ba b2a brk S
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      list_invs: \<open>twl_list_invs S\<close> and
      upd: \<open>clauses_to_update_l S = {#}\<close> and
      stgy_invs: \<open>twl_stgy_invs T\<close> and
      confl: \<open>get_conflict_l S = None\<close>
      using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
      apply - apply normalize_goal+
      by (auto simp: twl_st)
    show ?thesis
      by (rule cdcl_twl_full_restart_l_GC_prog_cdcl_twl_restart_l[unfolded Down_id_eq, OF ST list_invs
        struct_invs confl upd stgy_invs])
  qed

  have \<open>restart_prog_l S n brk \<le> \<Down> Id (restart_abs_l S n brk)\<close> for S n brk
    unfolding restart_prog_l_def restart_abs_l_def restart_required_l_def cdcl_twl_restart_l_prog_def
    apply (refine_vcg)
    subgoal by auto
    subgoal by (rule cdcl_twl_full_restart_l_GC_prog)
    subgoal by auto
    subgoal by auto
    subgoal by (rule cdcl_twl_local_restart_l_spec_cdcl_twl_restart_l) auto
    subgoal by (rule cdcl_twl_full_restart_l_prog) auto
    subgoal by auto
    done
  then show ?thesis
    apply -
    unfolding uncurry_def
    apply (intro frefI nres_relI)
    by force
qed

definition cdcl_twl_stgy_restart_abs_early_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_abs_early_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (_, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_abs_l T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0, 0);
    if \<not>brk then do {
      (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_abs_l T n brk;
        RETURN (brk, T, n)
      })
      (False, T, n);
      RETURN T
    } else RETURN T
  }\<close>

definition cdcl_twl_stgy_restart_abs_bounded_l :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>cdcl_twl_stgy_restart_abs_bounded_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (_, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_abs_l T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0, 0);
    RETURN (brk, T)
  }\<close>

definition cdcl_twl_stgy_restart_prog_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_prog_l S\<^sub>0 =
  do {
    (brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
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


definition cdcl_twl_stgy_restart_prog_early_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_prog_early_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_prog_l T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0, 0);
    if \<not>brk then do {
      (brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
	(\<lambda>(brk, _). \<not>brk)
	(\<lambda>(brk, S, n).
	do {
	  T \<leftarrow> unit_propagation_outer_loop_l S;
	  (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
	  (T, n) \<leftarrow> restart_prog_l T n brk;
	  RETURN (brk, T, n)
	})
	(False, T, n);
      RETURN T
    }
    else RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_l_cdcl_twl_stgy_restart_abs_early_l:
  \<open>(cdcl_twl_stgy_restart_prog_early_l, cdcl_twl_stgy_restart_abs_early_l) \<in> {(S, S').
   (S, S') \<in> Id \<and>  twl_list_invs S \<and>  clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
   (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>((False, S, 0), (False, T , 0)) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>
    if \<open>(S, T) \<in> ?R\<close>
    for S T
    using that by auto
  have [refine0]: \<open>unit_propagation_outer_loop_l x1c  \<le> \<Down> Id (unit_propagation_outer_loop_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  have [refine0]: \<open>cdcl_twl_o_prog_l x1c  \<le> \<Down> Id (cdcl_twl_o_prog_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
      cdcl_twl_stgy_restart_abs_early_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
        (S, S') \<in> Id \<and> brk = brk' \<and> n = n'}\<close>]
	WHILEIT_refine[where R = \<open>{((ebrk :: bool, brk :: bool, S, n :: nat), (ebrk', brk', S', n')).
        (S, S') \<in> Id \<and> brk = brk' \<and> n = n' \<and> ebrk = ebrk'}\<close> ]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        restart_abs_l_restart_prog[THEN fref_to_Down_curry2]
        restart_prog_l_restart_abs_l[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal for x y xa x' x1 x2 x1a x2a
      by fastforce
    subgoal by auto
    subgoal
      by (simp add: twl_st)
    subgoal by (auto simp: twl_st)
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    subgoal by auto
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma cdcl_twl_stgy_restart_abs_early_l_cdcl_twl_stgy_restart_abs_early_l:
  \<open>(cdcl_twl_stgy_restart_abs_early_l, cdcl_twl_stgy_restart_prog_early) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_abs_early_l_def cdcl_twl_stgy_restart_prog_early_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
      (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> brk = brk' \<and> n = n' \<and>
        clauses_to_update_l S = {#}}\<close>]
	WHILEIT_refine[where R = \<open>{((ebrk :: bool, brk :: bool, S, n :: nat), (ebrk' :: bool, brk', S', n')).
      (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> brk = brk' \<and> n = n' \<and> ebrk = ebrk' \<and>
        clauses_to_update_l S = {#}}\<close>]
      unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
      restart_abs_l_restart_prog[THEN fref_to_Down_curry2])
  subgoal by simp
  subgoal for x y _ _ xa x' x1 x2 x1a x2a
    unfolding cdcl_twl_stgy_restart_abs_l_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd (snd x'))\<close> in exI)
    by auto
  subgoal by fast
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_inv_def
      cdcl_twl_stgy_restart_abs_l_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st)
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x y _ _ xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e xb x'a x1f x2f x1g
    unfolding cdcl_twl_stgy_restart_abs_l_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd x'a)\<close> in exI)
    by auto
  subgoal by auto
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_inv_def
      cdcl_twl_stgy_restart_abs_l_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done


lemma (in twl_restart) cdcl_twl_stgy_restart_prog_early_l_cdcl_twl_stgy_restart_prog_early:
  \<open>(cdcl_twl_stgy_restart_prog_early_l, cdcl_twl_stgy_restart_prog_early)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule order_trans)
  defer
  apply (rule cdcl_twl_stgy_restart_abs_early_l_cdcl_twl_stgy_restart_abs_early_l[THEN fref_to_Down])
    apply fast
    apply assumption
  apply (rule cdcl_twl_stgy_restart_prog_early_l_cdcl_twl_stgy_restart_abs_early_l[THEN fref_to_Down,
    simplified])
  apply simp
  done

lemma cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_abs_l:
  \<open>(cdcl_twl_stgy_restart_prog_l, cdcl_twl_stgy_restart_abs_l) \<in> {(S, S').
   (S, S') \<in> Id \<and>  twl_list_invs S \<and>  clauses_to_update_l S =  {#}} \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
   (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>((False, S, 0), (False, T , 0)) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>
    if \<open>(S, T) \<in> ?R\<close>
    for S T
    using that by auto
  have [refine0]: \<open>unit_propagation_outer_loop_l x1c  \<le> \<Down> Id (unit_propagation_outer_loop_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  have [refine0]: \<open>cdcl_twl_o_prog_l x1c  \<le> \<Down> Id (cdcl_twl_o_prog_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
      cdcl_twl_stgy_restart_abs_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
        (S, S') \<in> Id \<and> brk = brk' \<and> n = n'}\<close>]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        restart_abs_l_restart_prog[THEN fref_to_Down_curry2]
        restart_prog_l_restart_abs_l[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal for x y xa x' x1 x2 x1a x2a
      by fastforce
    subgoal by auto
    subgoal
      by (simp add: twl_st)
    subgoal by (auto simp: twl_st)
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    subgoal by auto
    done
qed

lemma (in twl_restart) cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_prog:
  \<open>(cdcl_twl_stgy_restart_prog_l, cdcl_twl_stgy_restart_prog)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule order_trans)
  defer
  apply (rule cdcl_twl_stgy_restart_abs_l_cdcl_twl_stgy_restart_abs_l[THEN fref_to_Down])
    apply fast
    apply assumption
  apply (rule cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_abs_l[THEN fref_to_Down,
    simplified])
  apply simp
  done


definition cdcl_twl_stgy_restart_prog_bounded_l :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>cdcl_twl_stgy_restart_prog_bounded_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_prog_l T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0, 0);
    RETURN (brk, T)
  }\<close>


lemma cdcl_twl_stgy_restart_abs_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l:
  \<open>(cdcl_twl_stgy_restart_abs_bounded_l, cdcl_twl_stgy_restart_prog_bounded) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f
      \<langle>bool_rel \<times>\<^sub>r {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_abs_bounded_l_def cdcl_twl_stgy_restart_prog_bounded_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
	WHILEIT_refine[where R = \<open>{((ebrk :: bool, brk :: bool, S, n :: nat), (ebrk' :: bool, brk', S', n')).
      (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> brk = brk' \<and> n = n' \<and> ebrk = ebrk' \<and>
        clauses_to_update_l S = {#}}\<close>]
      unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
      restart_abs_l_restart_prog[THEN fref_to_Down_curry2])
  subgoal by simp
  subgoal for x y _ _ xa x' x1 x2 x1a x2a
    unfolding cdcl_twl_stgy_restart_abs_l_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd (snd x'))\<close> in exI)
    by auto
  subgoal by fast
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_inv_def
      cdcl_twl_stgy_restart_abs_l_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st)
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma cdcl_twl_stgy_restart_prog_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_l, cdcl_twl_stgy_restart_abs_bounded_l) \<in> {(S, S').
   (S, S') \<in> Id \<and>  twl_list_invs S \<and>  clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
   (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>((False, S, 0), (False, T , 0)) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>
    if \<open>(S, T) \<in> ?R\<close>
    for S T
    using that by auto
  have [refine0]: \<open>unit_propagation_outer_loop_l x1c  \<le> \<Down> Id (unit_propagation_outer_loop_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  have [refine0]: \<open>cdcl_twl_o_prog_l x1c  \<le> \<Down> Id (cdcl_twl_o_prog_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_bounded_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
      cdcl_twl_stgy_restart_abs_bounded_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
        (S, S') \<in> Id \<and> brk = brk' \<and> n = n'}\<close>]
	WHILEIT_refine[where R = \<open>{((ebrk :: bool, brk :: bool, S, n :: nat), (ebrk', brk', S', n')).
        (S, S') \<in> Id \<and> brk = brk' \<and> n = n' \<and> ebrk = ebrk'}\<close> ]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        restart_abs_l_restart_prog[THEN fref_to_Down_curry2]
        restart_prog_l_restart_abs_l[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal for x y xa x' x1 x2 x1a x2a
      by fastforce
    subgoal by auto
    subgoal
      by (simp add: twl_st)
    subgoal by (auto simp: twl_st)
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    subgoal by auto
    done
qed



lemma (in twl_restart) cdcl_twl_stgy_restart_prog_bounded_l_cdcl_twl_stgy_restart_prog_bounded:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_l, cdcl_twl_stgy_restart_prog_bounded)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
      \<langle>bool_rel \<times>\<^sub>r {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule order_trans)
  defer
  apply (rule cdcl_twl_stgy_restart_abs_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l[THEN fref_to_Down])
    apply fast
    apply assumption
  apply (rule cdcl_twl_stgy_restart_prog_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l[THEN fref_to_Down,
    simplified])
  apply simp
  done

end

end