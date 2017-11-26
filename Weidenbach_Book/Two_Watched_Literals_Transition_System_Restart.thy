theory Two_Watched_Literals_Transition_System_Restart
  imports Two_Watched_Literals_Transition_System CDCL.CDCL_W_Restart
begin


text \<open>
  Unlike the basic CDCL, it does not make any sense to fully restart the trail:
  the part propagated at level 0 (only the part due to unit clauses) have to be kept.
  Therefore, we allow fast restarts (i.e. a restart where part of the trail is reused).
\<close>
inductive cdcl_twl_restart :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" where
  \<open>cdcl_twl_restart (M, N, U, None, NP, UP, {#}, Q) (M', N, U', None, NP, UP, {#}, {#})\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>U' \<subseteq># U\<close> and

    \<open>\<forall>L E. Propagated L E \<in> set M' \<longrightarrow> E \<in># clause `# (N + U') + NP + UP\<close>

inductive_cases cdcl_twl_restartE: \<open>cdcl_twl_restart S T\<close>


locale twl_restart =
  fixes
    f :: \<open>nat \<Rightarrow> nat\<close>
  assumes
    f: \<open>unbounded f\<close>
begin

text \<open>This should be moved to @{file CDCL_W_Abstract_State.thy}\<close>
sublocale cdcl\<^sub>W_restart_mset: cdcl\<^sub>W_restart_restart where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  f = f
  by unfold_locales (rule f)



inductive cdcl_twl_stgy_restart :: \<open>'v twl_st \<times> nat \<Rightarrow> 'v twl_st \<times> nat \<Rightarrow> bool\<close> where
restart_step:
  \<open>cdcl_twl_stgy_restart (S, n) (U, Suc n)\<close>
  if
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>size (get_all_learned_clss T) - size (get_all_learned_clss S) > f n\<close> and
    \<open>cdcl_twl_restart T U\<close> |
restart_full:
 \<open>cdcl_twl_stgy_restart (S, n) (T, Suc n)\<close>
 if
    \<open>full1 cdcl_twl_stgy S T\<close>

lemma cdcl_twl_cp_all_learned_diff_learned:
  assumes \<open>cdcl_twl_cp S T\<close>
  shows
    \<open>clause `# get_learned_clss S = clause `# get_learned_clss T \<and>
     get_init_learned_clss S = get_init_learned_clss T \<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  apply (use assms in \<open>induction rule: cdcl_twl_cp.induct\<close>)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for D
    by (cases D)
      (auto simp: update_clauses.simps size_Suc_Diff1 dest!: multi_member_split)
  done

lemma cdcl_twl_o_all_learned_diff_learned:
  assumes \<open>cdcl_twl_o S T\<close>
  shows
    \<open>clause `# get_learned_clss S \<subseteq># clause `# get_learned_clss T \<and>
     get_init_learned_clss S \<subseteq># get_init_learned_clss T\<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  by (use assms in \<open>induction rule: cdcl_twl_o.induct\<close>)
   (auto simp: update_clauses.simps size_Suc_Diff1)

lemma cdcl_twl_stgy_all_learned_diff_learned:
  assumes \<open>cdcl_twl_stgy S T\<close>
  shows
    \<open>clause `# get_learned_clss S \<subseteq># clause `# get_learned_clss T \<and>
     get_init_learned_clss S \<subseteq># get_init_learned_clss T\<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  by (use assms in \<open>induction rule: cdcl_twl_stgy.induct\<close>)
    (auto simp: cdcl_twl_cp_all_learned_diff_learned cdcl_twl_o_all_learned_diff_learned)

lemma rtranclp_cdcl_twl_stgy_all_learned_diff_learned:
  assumes \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
  shows
    \<open>clause `# get_learned_clss S \<subseteq># clause `# get_learned_clss T \<and>
     get_init_learned_clss S \<subseteq># get_init_learned_clss T \<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  by (use assms in \<open>induction rule: rtranclp_induct\<close>)
   (auto dest: cdcl_twl_stgy_all_learned_diff_learned)

lemma rtranclp_cdcl_twl_stgy_all_learned_diff_learned_size:
  assumes \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
  shows
    \<open>size (get_all_learned_clss T) - size (get_all_learned_clss S) \<ge>
         size (get_learned_clss T) - size (get_learned_clss S)\<close>
  using rtranclp_cdcl_twl_stgy_all_learned_diff_learned[OF assms]
  apply (cases S, cases T)
  using size_mset_mono by force+

lemma cdcl_twl_stgy_restart_init_clss:
  assumes \<open>cdcl_twl_stgy_restart S T\<close>
  shows
    \<open>get_all_init_clss (fst S) = get_all_init_clss (fst T)\<close>
  by (use assms in \<open>induction rule: cdcl_twl_stgy_restart.induct\<close>)
     (auto simp: full1_def cdcl_twl_restart.simps
     dest: rtranclp_cdcl_twl_stgy_all_learned_diff_learned tranclp_into_rtranclp)

lemma rtranclp_cdcl_twl_stgy_restart_init_clss:
  assumes \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close>
  shows
    \<open>get_all_init_clss (fst S) = get_all_init_clss (fst T)\<close>
  by (use assms in \<open>induction rule: rtranclp_induct\<close>)
   (auto simp: full1_def dest: cdcl_twl_stgy_restart_init_clss)

lemma cdcl_twl_restart_cdcl\<^sub>W_stgy:
  assumes
    \<open>cdcl_twl_restart S V\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>twl_stgy_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T (state\<^sub>W_of V) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of V)\<close>
  using assms
proof (induction rule: cdcl_twl_restart.induct)
  case (1 K M' M2 M U' U N NP UP Q)
  note decomp = this(1) and learned = this(2) and kept = this(3) and inv = this(4) and
    stgy_invs = this(5)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, Q)\<close>
  let ?T = \<open>([], clause `# N + NP, clause `# U' + UP, None)\<close>
  let ?V = \<open>(M', N, U', None, NP, UP, {#}, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        image_mset_subseteq_mono)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>  and
    smaller_propa:
      \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>
    using inv unfolding twl_struct_invs_def  by fast+
  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], clause `# N + NP, clause `# U' + UP, None)
      (drop (length M - length M') M, clause `# N + NP, clause `# U' + UP, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>clause `# N + NP\<close> \<open>clause `# U+UP\<close> _
          \<open>clause `# U' + UP\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs unfolding twl_stgy_invs_def by simp
    subgoal using smaller_propa by simp
    subgoal using kept unfolding drop_M_M' by (auto simp add: ac_simps)
    subgoal using learned by (auto simp: image_mset_subseteq_mono)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state\<^sub>W_of ?V)\<close>
    unfolding drop_M_M' by simp
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of ?S) (state\<^sub>W_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart by fast
qed

lemma cdcl_twl_restart_cdcl\<^sub>W:
  assumes
    \<open>cdcl_twl_restart S V\<close> and
    \<open>twl_struct_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T (state\<^sub>W_of V)\<close>
  using assms
proof (induction rule: cdcl_twl_restart.induct)
  case (1 K M' M2 M U' U N NP UP Q)
  note decomp = this(1) and learned = this(2) and kept = this(3) and inv = this(4)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, Q)\<close>
  let ?T = \<open>([], clause `# N + NP, clause `# U' + UP, None)\<close>
  let ?V = \<open>(M', N, U', None, NP, UP, {#}, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        image_mset_subseteq_mono)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>  and
    smaller_propa:
      \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>
    using inv unfolding twl_struct_invs_def  by fast+
  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], clause `# N + NP, clause `# U' + UP, None)
      (drop (length M - length M') M, clause `# N + NP, clause `# U' + UP, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M \<open>clause `# N + NP\<close> \<open>clause `# U+UP\<close> _
          \<open>clause `# U' + UP\<close>])
    subgoal using struct_invs by simp
    subgoal using kept unfolding drop_M_M' by (auto simp add: ac_simps)
    subgoal using learned by (auto simp: image_mset_subseteq_mono)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state\<^sub>W_of ?V)\<close>
    unfolding drop_M_M' by simp
  then show ?case
    using restart by fast
qed

lemma cdcl_twl_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_restart S T\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using assms
proof (induction rule: cdcl_twl_restart.induct)
  case (1 K M' M2 M U' U N NP UP Q) note decomp = this(1) and learned = this(2) and kept = this(3)
    and invs = this(4) and stgy_invs = this(5)
  then have
    twl_st_inv: \<open>twl_st_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    \<open>valid_annotation (M, N, U, None, NP, UP, {#}, Q)\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
      (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa
      (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close> and
    \<open>twl_st_exception_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    no_dup_q: \<open>no_duplicate_queued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    dist: \<open>distinct_queued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    \<open>confl_cands_enqueued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    \<open>propa_cands_enqueued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    \<open>get_conflict (M, N, U, None, NP, UP, {#}, Q) \<noteq> None \<longrightarrow>
     clauses_to_update (M, N, U, None, NP, UP, {#}, Q) = {#} \<and>
     literals_to_update (M, N, U, None, NP, UP, {#}, Q) = {#}\<close> and
    unit: \<open>unit_clss_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    to_upd: \<open>clauses_to_update_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    past: \<open>past_invs (M, N, U, None, NP, UP, {#}, Q)\<close>
    unfolding twl_struct_invs_def by clarify+
  have
    ex: \<open>(\<forall>C\<in>#N + U. twl_lazy_update M' C \<and>
           twl_inv M' C \<and>
           watched_literals_false_of_max_level M' C \<and>
           twl_exception_inv (M', N, U, None, NP, UP, {#}, {#}) C)\<close> and
     conf_cands: \<open>confl_cands_enqueued (M', N, U, None, NP, UP, {#}, {#})\<close> and
     propa_cands: \<open>propa_cands_enqueued (M', N, U, None, NP, UP, {#}, {#})\<close> and
     clss_to_upd: \<open>clauses_to_update_inv (M', N, U, None, NP, UP, {#}, {#})\<close>
     using past get_all_ann_decomposition_exists_prepend[OF decomp] unfolding past_invs.simps
     by force+

   have excp_inv: \<open>twl_st_exception_inv (M', N, U, None, NP, UP, {#}, {#})\<close>
     using ex unfolding twl_st_exception_inv.simps by blast+
   have twl_st_inv': \<open>twl_st_inv (M', N, U, None, NP, UP, {#}, {#})\<close>
     using ex learned twl_st_inv
     unfolding twl_st_exception_inv.simps twl_st_inv.simps
     by auto
   have n_d: \<open>no_dup M\<close>
     using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
   obtain M3 where
     M: \<open>M = M3 @ M2 @ Decided K # M'\<close>
     using decomp by blast
   define M3' where \<open>M3' = M3 @ M2\<close>
   then have M3': \<open>M = M3' @ Decided K # M'\<close>
     unfolding M by auto
   have unit_clss_inv: \<open>unit_clss_inv (M', N, U', None, NP, UP, {#}, {#})\<close>
     unfolding unit_clss_inv.simps
   proof
     fix C
     assume \<open>C \<in># NP + UP\<close>
     then obtain L where
       lev_L: \<open>get_level M L = 0\<close>
       \<open>L \<in> lits_of_l M\<close> and
       C: \<open>C = {#L#}\<close>
       using unit by auto
     then have \<open>L \<in> lits_of_l M'\<close>
       apply (cases \<open>defined_lit M3' L\<close>)
       using n_d unfolding M3' by (auto simp: get_level_cons_if split: if_splits
           dest: in_lits_of_l_defined_litD)
     moreover have \<open>get_level M' L = 0\<close>
       apply (cases \<open>defined_lit M3' L\<close>)
       using n_d lev_L unfolding M3' by (auto simp: get_level_cons_if split: if_splits
           dest: in_lits_of_l_defined_litD)
     ultimately show \<open>\<exists>L. C = {#L#} \<and>
             (None = None \<or> 0 < count_decided M' \<longrightarrow>
              get_level M' L = 0 \<and> L \<in> lits_of_l M')\<close>
       using C by blast
   qed
   have past_invs: \<open>past_invs (M', N, U', None, NP, UP, {#}, {#})\<close>
     unfolding past_invs.simps
   proof (intro conjI impI allI)
     fix M1 M2 K'
     assume \<open>M' = M2 @ Decided K' # M1\<close>
     then have \<open>M = (M3' @ Decided K # M2) @ Decided K' # M1\<close>
       using M3' by simp
     then have
       1: \<open>\<forall>C\<in>#N + U.
           twl_lazy_update M1 C \<and>
           twl_inv M1 C \<and>
           watched_literals_false_of_max_level M1 C \<and>
           twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close> and
       2: \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
       3: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
       4: \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
       using past unfolding past_invs.simps by blast+
     show \<open>\<forall>C\<in>#N + U'.
          twl_lazy_update M1 C \<and>
          twl_inv M1 C \<and>
          watched_literals_false_of_max_level M1 C \<and>
          twl_exception_inv (M1, N, U', None, NP, UP, {#}, {#}) C\<close>
       using 1 learned twl_st_exception_inv_mono[OF learned, of M1 N None NP UP \<open>{#}\<close> \<open>{#}\<close>]
       by auto
     show \<open>confl_cands_enqueued (M1, N, U', None, NP, UP, {#}, {#})\<close>
       using confl_cands_enqueued_mono[OF learned 2] .
     show \<open>propa_cands_enqueued (M1, N, U', None, NP, UP, {#}, {#})\<close>
       using propa_cands_enqueued_mono[OF learned 3] .
     show \<open>clauses_to_update_inv (M1, N, U', None, NP, UP, {#}, {#})\<close>
       using 4 learned by (auto simp add: filter_mset_empty_conv)
   qed
   have clss_to_upd: \<open>clauses_to_update_inv (M', N, U', None, NP, UP, {#}, {#})\<close>
     using clss_to_upd learned by (auto simp add: filter_mset_empty_conv)
   have step':
     \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q)) T \<and>
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close> and
    step: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>*
       (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q)) (state\<^sub>W_of
         (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using cdcl_twl_restart_cdcl\<^sub>W_stgy[OF cdcl_twl_restart.intros[OF 1(1-3)] invs stgy_invs]
     by fast+
   then have struct_inv':
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using struct_inv
     by (auto intro: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
   obtain T' where
     res: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q)) T'\<close> and
     res': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T' (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using step' by fast
   have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa T'\<close>
     using res
     by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset.restart.simps
         state_def)
   moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv T'\<close>
     using res struct_inv
     by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
         cdcl\<^sub>W_restart_mset.rf cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv)
   ultimately have smaller':
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using res'
     by (auto intro: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa)

   show ?case
    unfolding twl_struct_invs_def
    apply (intro conjI)
    subgoal using twl_st_inv_mono[OF learned twl_st_inv'] .
    subgoal by simp
    subgoal by (rule struct_inv')
    subgoal by (rule smaller')
    subgoal using twl_st_exception_inv_mono[OF learned excp_inv] .
    subgoal using no_dup_q by auto
    subgoal using dist by auto
    subgoal using confl_cands_enqueued_mono[OF learned conf_cands] .
    subgoal using propa_cands_enqueued_mono[OF learned propa_cands] .
    subgoal by simp
    subgoal by (rule unit_clss_inv)
    subgoal by (rule clss_to_upd)
    subgoal by (rule past_invs)
    done
qed


lemma cdcl_twl_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_restart S T\<close> and \<open>twl_stgy_invs S\<close>
  shows \<open>twl_stgy_invs T\<close>
  using assms
  by (induction rule: cdcl_twl_restart.induct)
   (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      conflicting.simps cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def trail.simps
      dest!: get_all_ann_decomposition_exists_prepend)

lemma cdcl_twl_stgy_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst S)\<close>
  shows \<open>twl_struct_invs (fst T)\<close>
  using assms
  by (induction rule: cdcl_twl_stgy_restart.induct)
     (auto simp add: full1_def intro: rtranclp_cdcl_twl_stgy_twl_struct_invs tranclp_into_rtranclp
      cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs)

lemma cdcl_twl_stgy_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst S)\<close>
  shows \<open>twl_stgy_invs (fst T)\<close>
  using assms
  by (induction rule: cdcl_twl_stgy_restart.induct)
    (auto simp add: full1_def  dest!: tranclp_into_rtranclp
      intro: cdcl_twl_restart_twl_stgy_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs )

lemma (in -) cdcl_twl_stgy_cdcl\<^sub>W_stgy3:
  assumes \<open>cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close> and
    \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  using cdcl_twl_stgy_cdcl\<^sub>W_stgy2[OF assms(1,2)] assms(3-)
  by (auto simp: lexn2_conv)

lemma (in -) tranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy:
  assumes ST: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close> and
    twl: \<open>twl_struct_invs S\<close> and
    \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
proof -
  obtain S' where
    SS': \<open>cdcl_twl_stgy S S'\<close> and
    S'T: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' T\<close>
    using ST unfolding tranclp_unfold_begin by blast

  have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of S')\<close>
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy3[OF SS' assms(2-4)]
    by blast
  have struct_S': \<open>twl_struct_invs S'\<close>
    using twl SS' by (blast intro: cdcl_twl_stgy_twl_struct_invs)
  have 2: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S') (state\<^sub>W_of T)\<close>
    apply (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy)
     apply (rule S'T)
    by (rule struct_S')
  show ?thesis
    using 1 2 by auto
qed


lemma no_step_cdcl_twl_stgy_restart_cdcl_twl_stgy:
  assumes
    ns: \<open>no_step cdcl_twl_stgy_restart S\<close> and
    \<open>twl_struct_invs (fst S)\<close>
  shows
    \<open>no_step cdcl_twl_stgy (fst S)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain T where T: \<open>cdcl_twl_stgy (fst S) T\<close> by blast
  then have \<open>twl_struct_invs T\<close>
    using assms(2) cdcl_twl_stgy_twl_struct_invs by blast
  obtain U where U: \<open>full (\<lambda>S T. twl_struct_invs S \<and> cdcl_twl_stgy S T) T U\<close>
   using wf_exists_normal_form_full[OF wf_cdcl_twl_stgy] by blast
  have \<open>full cdcl_twl_stgy T U\<close>
  proof -
    have
      st: \<open>(\<lambda>S T. twl_struct_invs S \<and> cdcl_twl_stgy S T)\<^sup>*\<^sup>* T U\<close> and
      ns: \<open>no_step (\<lambda>U V. twl_struct_invs U \<and> cdcl_twl_stgy U V) U\<close>
      using U unfolding full_def by blast+
    have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
      using st by (induction rule: rtranclp_induct) auto
    moreover have \<open>no_step cdcl_twl_stgy U\<close>
      using ns \<open>twl_struct_invs T\<close> calculation rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
    ultimately show ?thesis
      unfolding full_def by blast
  qed
  then have \<open>full1 cdcl_twl_stgy (fst S) U\<close>
    using T by (auto intro: full_fullI)
  then show False
    using ns cdcl_twl_stgy_restart.intros(2)[of \<open>fst S\<close> U \<open>snd S\<close>]
    by fastforce
qed

lemma (in -) substract_left_le: \<open>(a :: nat) + b < c ==> a <= c - b\<close>
  by auto


thm cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new
theorem
  \<open>wf {(T, S :: 'v twl_st \<times> nat). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
    then obtain g :: \<open>nat \<Rightarrow> 'v twl_st \<times> nat\<close> where
    g: \<open>\<And>i. cdcl_twl_stgy_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. twl_struct_invs (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast
  have init_g: \<open>get_all_init_clss (fst (g i)) = get_all_init_clss (fst (g 0))\<close> for i
    apply (induction i)
    subgoal by simp
    subgoal for i using g[of i] inv by (auto dest!: cdcl_twl_stgy_restart_init_clss)
    done
  let ?U0 = \<open>get_all_learned_clss (fst (g 0))\<close>
  let ?Ui = \<open>\<lambda>i. get_all_learned_clss (fst (g i)) - ?U0\<close>

  let ?S = \<open>g 0\<close>
  have \<open>finite (atms_of_mm (get_all_init_clss (fst ?S)))\<close>
    using inv by auto
  have snd_g: \<open>snd (g i) = i + snd (g 0)\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal for i
      using g[of i] by (auto simp: cdcl_twl_stgy_restart.simps)
    done
  then have snd_g_0: \<open>\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)\<close>
    by blast
  have unbounded_f_g: \<open>unbounded (\<lambda>i. f (snd (g i)))\<close>
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  define j where
    \<open>j \<equiv> (\<lambda>i. case g (i + 1) of ((M, N, U, D, NP, UP, WS, Q), n) \<Rightarrow>
           (state\<^sub>W_of (M, N, U, D, NP, UP, WS, Q)))\<close>

  have H: False if \<open>no_step cdcl_twl_stgy (fst (g i))\<close> for i
     using g[of i] that
  proof (induction rule: cdcl_twl_stgy_restart.induct)
     case (restart_step S T n) note H = this(1) and c = this(2) and n_s = this(4)
    obtain S' where \<open>cdcl_twl_stgy S S'\<close>
      using H c  by (subst (asm) rtranclp_unfold) (auto dest!: tranclpD)
    then show False using n_s by fastforce
  next
     case (restart_full S T)
     then show False unfolding full1_def by (auto dest: tranclpD)
   qed
   have
      \<open>\<exists>h. cdcl_twl_stgy\<^sup>*\<^sup>* (fst (g i)) (h) \<and>
         size (get_all_learned_clss (h)) - size (get_all_learned_clss (fst (g i))) > f (snd (g i)) \<and>
         cdcl_twl_restart (h) (fst (g (i+1)))\<close>
       for i
     using g[of i] H[of \<open>Suc i\<close>]
     unfolding cdcl_twl_stgy_restart.simps full1_def Suc_eq_plus1[symmetric]
     by force
   then obtain h :: \<open>nat \<Rightarrow> 'v twl_st\<close> where
      \<open>cdcl_twl_stgy\<^sup>*\<^sup>* (fst (g i)) (h i)\<close> and
      \<open>size (get_all_learned_clss (h i)) - size (get_all_learned_clss (fst (g i))) > f (snd (g i))\<close>
        and
      \<open>cdcl_twl_restart (h i) (fst (g (i+1)))\<close> for i
     by metis

   have \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W S T}\<close>
     by (rule cdcl\<^sub>W_restart_mset.wf_cdcl\<^sub>W)
   then have
     \<open>\<nexists>j. \<forall>i. cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (j i) \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (j i) (j (Suc i))\<close>
     unfolding wf_iff_no_infinite_down_chain by auto

   then show False
   proof auto
     sorry
     subgoal premises p
       apply (rule that)
         using g[of ] H[of \<open>Suc _\<close>]
         unfolding cdcl_twl_stgy_restart.simps full1_def Suc_eq_plus1[symmetric]
         
         apply auto
         try0

     using g[of ]
     unfolding cdcl_twl_stgy_restart.simps full1_def
     apply blast
     apply (simp)
 
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (j i) (j (Suc i))\<close> for i :: nat
  proof -
    
    have 1: \<open>cdcl_twl_stgy_restart (g (i)) (g (i + 1))\<close>
      using g[of i] by simp
    then obtain T where
      \<open>\<close>
    have 2: \<open>cdcl_twl_stgy_restart (g (i + 1)) (g (i + 2))\<close>
      using g[of \<open>i+1\<close>] by simp

  qed
  obtain k where
    f_g_k: \<open>f (snd (g k)) > card (simple_clss (atms_of_mm (get_all_init_clss (fst ?S)))) + size ?U0\<close> and
    k_ge: \<open>k > card (simple_clss (atms_of_mm (get_all_init_clss (fst ?S)))) + size ?U0\<close>
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>


  obtain m T where
    m: \<open>m = size (get_all_learned_clss T) - size (get_all_learned_clss (fst (g k)))\<close> and
    \<open>m > f (snd (g k))\<close> and
    \<open>cdcl_twl_restart T (fst (g (k+1)))\<close> and
    cdcl\<^sub>W_stgy: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close>
    using g[of k] H[of \<open>Suc k\<close>] by (force simp: cdcl_twl_stgy_restart.simps full1_def)
  have \<open>twl_struct_invs T\<close>
    using inv[of k] cdcl\<^sub>W_stgy rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
  moreover {
    have [simp]: \<open>get_all_init_clss (fst (g k)) = get_all_init_clss T\<close>
      using cdcl\<^sub>W_stgy rtranclp_cdcl_twl_stgy_all_learned_diff_learned by blast
    then have [simp]: \<open>get_all_init_clss (fst ?S) = get_all_init_clss T\<close>
      using init_g[of k] by auto
  }
  moreover {
    have 3:\<open>size (get_all_learned_clss T) - size (get_all_learned_clss (fst (g k)))
      > card (simple_clss (atms_of_mm (get_all_init_clss (fst ?S)))) + size ?U0\<close>
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have  \<open>size (get_all_learned_clss T)
      > card (simple_clss (atms_of_mm (get_all_init_clss (fst ?S)))) + size ?U0\<close>
      by linarith
    have \<open>size (get_all_learned_clss T - ?U0) > card (simple_clss (atms_of_mm (get_all_init_clss (fst ?S))))\<close>
      apply (rule order.strict_trans2)
      defer
      apply (rule diff_size_le_size_Diff)
      using 3 by auto
  }

  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed


lemma
  assumes \<open>cdcl_twl_stgy_restart S U\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>distinct_mset (get_all_learned_clss (fst S))\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_with_restart (state\<^sub>W_of (fst S), snd S)
           (state\<^sub>W_of (fst T), snd T) \<and>
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of (fst T)) (state\<^sub>W_of (fst U)) \<or>
    no_step cdcl_twl_stgy (fst U)\<close>
proof (use assms in \<open>induction rule: cdcl_twl_stgy_restart.induct\<close>)
  case (restart_step S T n U) note st = this(1) and f = this(2) and restart = this(3) and
    struct = this(4) and dist = this(5)
  have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
    using st struct
    sorry

  have \<open>distinct_mset (get_all_learned_clss T)\<close>
    sorry
  then have \<open>card (set_mset (learned_clss (state\<^sub>W_of T))) = size (get_all_learned_clss T)\<close>
    by (cases T) (auto simp: learned_clss.simps dest!: distinct_mset_size_eq_card)
  moreover have \<open>size (get_all_init_clss S) \<ge> card (set_mset (learned_clss (state\<^sub>W_of S)))\<close>
    apply (cases S)
    apply (auto simp: learned_clss.simps intro: card_Un_le order.trans)
    sorry
  ultimately have
    2: \<open>f n < card (set_mset (learned_clss (state\<^sub>W_of T))) - card (set_mset (learned_clss (state\<^sub>W_of S)))\<close>
    using f by linarith

  have 3: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of T) (state\<^sub>W_of U)\<close>
    using st restart apply (auto simp: cdcl\<^sub>W_restart_mset.restart.simps cdcl_twl_restart.simps
        cdcl\<^sub>W_restart_mset_state state_def)
    sorry
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_with_restart (state\<^sub>W_of S, n) (state\<^sub>W_of U, Suc n)\<close>
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_with_restart.intros(1))
      apply (rule 1)
     apply (rule 2)
    sorry

    show ?case

    sorry
  oops

term cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_with_restart
lemma
  assumes \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close>
  shows \<open>(cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_with_restart\<^sup>+\<^sup>+ (state\<^sub>W_of (fst S), snd S) (state\<^sub>W_of (fst T), snd T)) \<or>
     (cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_with_restart\<^sup>*\<^sup>* (state\<^sub>W_of (fst S), snd S) (state\<^sub>W_of (fst T), snd T)) \<and>
       no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart (state\<^sub>W_of (fst S))\<close>
proof (use assms in \<open>induction rule: cdcl_twl_stgy_restart.induct\<close>)
  case (restart_step S T n U)
  then show ?case sorry
next
  case (restart_full S T n)
  then have
    st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close>  and
    ns: \<open>no_step cdcl_twl_stgy T\<close> and
    struct: \<open>twl_struct_invs S\<close>
    by (auto simp: full1_def)
  have struct_T: \<open>twl_struct_invs T\<close>
    by (meson rtranclp_cdcl_twl_stgy_twl_struct_invs rtranclp_unfold st struct)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of (fst (S, n))) (state\<^sub>W_of (fst (T, Suc n)))\<close>
    using st struct no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy[of T]
      rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[of S T]
    unfolding full1_def
    apply simp(* TODO Proof *)
    by (meson cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart rtranclp_unfold)
  moreover have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of T)\<close>
    apply (rule no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy)
    using restart_full unfolding full1_def apply blast
    using struct_T .
  then have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart (state\<^sub>W_of T)\<close>
    apply (auto
        dest!: cdcl\<^sub>W_restart_mset.tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart)

    sorry
  ultimately show ?case
    apply simp
    apply (auto dest: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
        rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy simp: rtranclp_unfold
        dest!: cdcl\<^sub>W_restart_mset.tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart)

    sorry
qed

lemma tranclp_wf_cdcl_twl_stgy:
  \<open>wf {(T, S). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart S T}\<close>
  (is \<open>wf ?S\<close>)
proof -
  let ?CDCL = \<open>{(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>+\<^sup>+ (state\<^sub>W_of S) (state\<^sub>W_of T)}\<close>
  have \<open>?S \<subseteq> {(T, S). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart\<^sup>+\<^sup>+ S T}\<close>
  proof
    fix TS
    assume H: \<open>TS \<in> {(T, S). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart S T}\<close>
    obtain S T where
      \<open>TS = (T, S)\<close> by (cases TS)
    with H have
      \<open>twl_struct_invs (fst S)\<close> and
      \<open>cdcl_twl_stgy_restart S T\<close>
      by simp_all

    have \<open>cdcl_twl_stgy_restart\<^sup>+\<^sup>+ S T\<close>





    show \<open>ST \<in> {(T, S). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart\<^sup>+\<^sup>+ S T}\<close>
      sorry



end

end