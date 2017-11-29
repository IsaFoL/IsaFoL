theory Two_Watched_Literals_Transition_System_Restart
  imports Two_Watched_Literals_Transition_System
begin


text \<open>
  Unlike the basic CDCL, it does not make any sense to fully restart the trail:
  the part propagated at level 0 (only the part due to unit clauses) have to be kept.
  Therefore, we allow fast restarts (i.e. a restart where part of the trail is reused).

  There are two cases:
    \<^item> either the trail is strictly decreasing;
    \<^item> or it is kept and the number of clauses is strictly decreasing.

  This ensures that \<^emph>\<open>something\<close> changes to prove termination.
\<close>
inductive cdcl_twl_restart :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" where
restart_trail:
   \<open>cdcl_twl_restart (M, N, U, None, NP, UP, {#}, Q) (M', N, U', None, NP, UP, {#}, {#})\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>U' \<subseteq># U\<close> and

    \<open>\<forall>L E. Propagated L E \<in> set M' \<longrightarrow> E \<in># clause `# (N + U') + NP + UP\<close> |
restart_clauses:
   \<open>cdcl_twl_restart (M, N, U, None, NP, UP, {#}, Q) (M, N, U', None, NP, UP, {#}, Q)\<close>
  if
    \<open>U' \<subset># U\<close> and
    \<open>\<forall>L E. Propagated L E \<in> set M \<longrightarrow> E \<in># clause `# (N + U') + NP + UP\<close>

inductive_cases cdcl_twl_restartE: \<open>cdcl_twl_restart S T\<close>

lemma wf_cdcl_twl_restart:
  \<open>wf {(T, S). cdcl_twl_restart S T}\<close>
proof -
  have [simp]: \<open>U' \<subseteq># U \<Longrightarrow> \<not> U \<subseteq># U' \<Longrightarrow> size U' < size U\<close> for U U'
    using mset_subset_size subset_mset_def by blast
  have \<open>wf {(x, y). cdcl_twl_restart y x \<and> True}\<close>
    by (rule wfP_if_measure2[of \<open>\<lambda>T S. cdcl_twl_restart S T\<close> \<open>\<lambda>_ _. True\<close>
          \<open>\<lambda>S. length (get_trail S) + size (get_clauses S)\<close>])
      (auto simp: cdcl_twl_restart.simps ac_simps
      dest!: get_all_ann_decomposition_exists_prepend dest: size_mset_mono)
  then show ?thesis by simp
qed

context twl_restart
begin

inductive cdcl_twl_stgy_restart :: \<open>'v twl_st \<times> nat \<Rightarrow> 'v twl_st \<times> nat \<Rightarrow> bool\<close> where
restart_step:
  \<open>cdcl_twl_stgy_restart (S, n) (U, Suc n)\<close>
  if
    \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (get_learned_clss T) > f n\<close> and
    \<open>cdcl_twl_restart T U\<close> |
restart_full:
 \<open>cdcl_twl_stgy_restart (S, n) (T, Suc n)\<close>
 if
    \<open>full1 cdcl_twl_stgy S T\<close>

lemma cdcl_twl_stgy_restart_init_clss:
  assumes \<open>cdcl_twl_stgy_restart S T\<close>
  shows
    \<open>get_all_init_clss (fst S) = get_all_init_clss (fst T)\<close>
  by (use assms in \<open>induction rule: cdcl_twl_stgy_restart.induct\<close>)
     (auto simp: full1_def cdcl_twl_restart.simps
     dest: rtranclp_cdcl_twl_stgy_all_learned_diff_learned dest!: tranclp_into_rtranclp)

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
  case (restart_trail K M' M2 M U' U N NP UP Q)
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
next
  case (restart_clauses U' U M N NP UP Q)
  note learned = this(1) and kept = this(2) and inv = this(3) and stgy_invs = this(4)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, Q)\<close>
  let ?T = \<open>([], clause `# N + NP, clause `# U' + UP, None)\<close>
  let ?V = \<open>(M, N, U', None, NP, UP, {#}, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        image_mset_subseteq_mono)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>  and
    smaller_propa:
      \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>
    using inv unfolding twl_struct_invs_def  by fast+

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], clause `# N + NP, clause `# U' + UP, None)
      (drop (length M - length M) M, clause `# N + NP, clause `# U' + UP, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>clause `# N + NP\<close> \<open>clause `# U+UP\<close> _
          \<open>clause `# U' + UP\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs unfolding twl_stgy_invs_def by simp
    subgoal using smaller_propa by simp
    subgoal using kept by (auto simp add: ac_simps)
    subgoal using learned by (auto simp: image_mset_subseteq_mono)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state\<^sub>W_of ?V)\<close>
    by simp
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of ?S) (state\<^sub>W_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart by auto
qed

lemma cdcl_twl_restart_cdcl\<^sub>W:
  assumes
    \<open>cdcl_twl_restart S V\<close> and
    \<open>twl_struct_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T (state\<^sub>W_of V)\<close>
  using assms
proof (induction rule: cdcl_twl_restart.induct)
  case (restart_trail K M' M2 M U' U N NP UP Q)
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
next
  case (restart_clauses U' U M N NP UP Q)
  note learned = this(1) and kept = this(2) and inv = this(3)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, Q)\<close>
  let ?T = \<open>([], clause `# N + NP, clause `# U' + UP, None)\<close>
  let ?V = \<open>(M, N, U', None, NP, UP, {#}, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        image_mset_subseteq_mono)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>  and
    smaller_propa:
      \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close>
    using inv unfolding twl_struct_invs_def  by fast+
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], clause `# N + NP, clause `# U' + UP, None)
      (drop (length M - length M) M, clause `# N + NP, clause `# U' + UP, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M \<open>clause `# N + NP\<close> \<open>clause `# U+UP\<close> _
          \<open>clause `# U' + UP\<close>])
    subgoal using struct_invs by simp
    subgoal using kept  by (auto simp add: ac_simps)
    subgoal using learned by (auto simp: image_mset_subseteq_mono)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state\<^sub>W_of ?V)\<close>
    by simp
  then show ?case
    using restart by auto
qed

lemma cdcl_twl_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_restart S T\<close> and
    \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using assms
proof (induction rule: cdcl_twl_restart.induct)
  case (restart_trail K M' M2 M U' U N NP UP Q) note decomp = this(1) and learned = this(2) and
    kept = this(3) and invs = this(4)
  then have
    twl_st_inv: \<open>twl_st_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    \<open>valid_annotation (M, N, U, None, NP, UP, {#}, Q)\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
      (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa
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

   have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W \<le> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<close>
     using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart  by blast

   obtain T' where
     res: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q)) T'\<close> and
     res': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T' (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using cdcl_twl_restart_cdcl\<^sub>W[OF cdcl_twl_restart.restart_trail[OF restart_trail(1-3)] invs]
     by fast
   then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))
       (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using rtranclp_mono[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart]
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart
     by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros)
   from cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF this struct_inv]
   have struct_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     .
   have smaller':
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M', N, U', None, NP, UP, {#}, {#}))\<close>
     using smaller mset_subset_eqD[OF learned]
     apply (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def M3' cdcl\<^sub>W_restart_mset_state
         clauses_def) (* TODO Proof *)
     by (metis Cons_eq_appendI append_assoc image_eqI)

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
next
  case (restart_clauses U' U M N NP UP Q) note learned = this(1) and
    kept = this(2) and invs = this(3)
  then have
    twl_st_inv: \<open>twl_st_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    valid: \<open>valid_annotation (M, N, U, None, NP, UP, {#}, Q)\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
      (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa
      (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))\<close> and
    excp_inv: \<open>twl_st_exception_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    no_dup_q: \<open>no_duplicate_queued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    dist: \<open>distinct_queued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    confl_cands: \<open>confl_cands_enqueued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    propa_cands: \<open>propa_cands_enqueued (M, N, U, None, NP, UP, {#}, Q)\<close> and
    \<open>get_conflict (M, N, U, None, NP, UP, {#}, Q) \<noteq> None \<longrightarrow>
     clauses_to_update (M, N, U, None, NP, UP, {#}, Q) = {#} \<and>
     literals_to_update (M, N, U, None, NP, UP, {#}, Q) = {#}\<close> and
    unit: \<open>unit_clss_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    to_upd: \<open>clauses_to_update_inv (M, N, U, None, NP, UP, {#}, Q)\<close> and
    past: \<open>past_invs (M, N, U, None, NP, UP, {#}, Q)\<close>
    unfolding twl_struct_invs_def by clarify+
   have learned: \<open>U' \<subseteq># U\<close>
    using learned by auto
   have n_d: \<open>no_dup M\<close>
     using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
   have valid': \<open>valid_annotation (M, N, U', None, NP, UP, {#}, Q)\<close>
     using valid by auto
   have unit_clss_inv: \<open>unit_clss_inv (M, N, U', None, NP, UP, {#}, Q)\<close>
     unfolding unit_clss_inv.simps
   proof
     fix C
     assume \<open>C \<in># NP + UP\<close>
     then obtain L where
       lev_L: \<open>get_level M L = 0\<close>
       \<open>L \<in> lits_of_l M\<close> and
       C: \<open>C = {#L#}\<close>
       using unit by auto
     then show \<open>\<exists>L. C = {#L#} \<and>
             (None = None \<or> 0 < count_decided M \<longrightarrow>
              get_level M L = 0 \<and> L \<in> lits_of_l M)\<close>
       using C by blast
   qed
   have past_invs: \<open>past_invs (M, N, U', None, NP, UP, {#}, Q)\<close>
     using past unfolding past_invs.simps
   proof (intro conjI impI allI)
     fix M1 M2 K'
     assume \<open>M = M2 @ Decided K' # M1\<close>
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

   have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W \<le> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<close>
     using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart  by blast

   have clss_to_upd: \<open>clauses_to_update_inv (M, N, U', None, NP, UP, {#}, Q)\<close>
     using to_upd learned by (auto simp add: filter_mset_empty_conv)
      obtain T' where
     res: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q)) T'\<close> and
     res': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T' (state\<^sub>W_of (M, N, U', None, NP, UP, {#}, Q))\<close>
     using cdcl_twl_restart_cdcl\<^sub>W[OF cdcl_twl_restart.restart_clauses[OF restart_clauses(1-2)] invs]
     by fast
   then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, Q))
       (state\<^sub>W_of (M, N, U', None, NP, UP, {#}, Q))\<close>
     using rtranclp_mono[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart]
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart
     by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros)
   from cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF this struct_inv]
   have struct_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M, N, U', None, NP, UP, {#}, Q))\<close>
     .

    have smaller':
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M, N, U', None, NP, UP, {#}, Q))\<close>
     using smaller mset_subset_eqD[OF learned]
     by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
         clauses_def)

   show ?case
    unfolding twl_struct_invs_def
    apply (intro conjI)
    subgoal using twl_st_inv_mono[OF learned twl_st_inv] .
    subgoal by (rule valid')
    subgoal by (rule struct_inv')
    subgoal by (rule smaller')
    subgoal using twl_st_exception_inv_mono[OF learned excp_inv] .
    subgoal using no_dup_q by auto
    subgoal using dist by auto
    subgoal using confl_cands_enqueued_mono[OF learned confl_cands] .
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
    \<open>twl_struct_invs (fst S)\<close>
  shows \<open>twl_struct_invs (fst T)\<close>
  using assms
  by (induction rule: cdcl_twl_stgy_restart.induct)
     (auto simp add: full1_def intro: rtranclp_cdcl_twl_stgy_twl_struct_invs tranclp_into_rtranclp
      cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs)

lemma rtranclp_cdcl_twl_stgy_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs (fst S)\<close>
  shows \<open>twl_struct_invs (fst T)\<close>
  using assms
  by (induction)
     (auto intro: cdcl_twl_stgy_restart_twl_struct_invs)

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

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_stgy_new_learned_in_all_simple_clss:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    invR: "cdcl\<^sub>W_all_struct_inv R"
  shows \<open>set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (init_clss S))\<close>
proof
  fix C
  assume C: \<open>C \<in># learned_clss S\<close>
  have invS: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
    using rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv[OF st invR] .
  then have dist: \<open>distinct_cdcl\<^sub>W_state S\<close> and alien: \<open>no_strange_atm S\<close>
    unfolding cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>atms_of C \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien C unfolding no_strange_atm_def
    by (auto dest!: multi_member_split)
  moreover have \<open>distinct_mset C\<close>
    using dist C unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by (auto dest: in_diffD)
  moreover have \<open>\<not> tautology C\<close>
    using invS C unfolding cdcl\<^sub>W_all_struct_inv_def
    by (auto dest: in_diffD)
  ultimately show \<open>C \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    unfolding simple_clss_def
    by clarify
qed

lemma (in -) learned_clss_get_all_learned_clss[simp]:
   \<open>learned_clss (state\<^sub>W_of S) = get_all_learned_clss S\<close>
  by (cases S) (auto simp: learned_clss.simps)

lemma cdcl_twl_stgy_restart_new_learned_in_all_simple_clss:
  assumes
    st: "cdcl_twl_stgy_restart\<^sup>*\<^sup>* R S" and
    invR: "twl_struct_invs (fst R)"
  shows \<open>set_mset (clauses (get_learned_clss (fst S))) \<subseteq>
     simple_clss (atms_of_mm (get_all_init_clss (fst S)))\<close>
proof
  fix C
  assume C: \<open>C \<in># clauses (get_learned_clss (fst S))\<close>
  have invS: \<open>twl_struct_invs (fst S)\<close>
    using invR rtranclp_cdcl_twl_stgy_restart_twl_struct_invs st by blast
  then have dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (fst S))\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (fst S))\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>atms_of C \<subseteq> atms_of_mm (get_all_init_clss (fst S))\<close>
    using alien C unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases S) (auto dest!: multi_member_split simp: cdcl\<^sub>W_restart_mset_state)
  moreover have \<open>distinct_mset C\<close>
    using dist C unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by (cases S) (auto dest: in_diffD simp: cdcl\<^sub>W_restart_mset_state)
  moreover have \<open>\<not> tautology C\<close>
    using invS C unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_struct_invs_def
    by (cases S) (auto dest: in_diffD)
  ultimately show \<open>C \<in> simple_clss (atms_of_mm (get_all_init_clss (fst S)))\<close>
    unfolding simple_clss_def
    by clarify
qed

lemma cdcl_twl_stgy_restart_new:
  assumes
   \<open>cdcl_twl_stgy_restart S T\<close> and
   \<open>twl_struct_invs (fst S)\<close> and
   \<open>distinct_mset (get_all_learned_clss (fst S) - A)\<close>
 shows \<open>distinct_mset (get_all_learned_clss (fst T) - A)\<close>
  using assms
proof induction
  case (restart_step S T n U) note st = this(1) and res = this(3) and invs = this(4) and
    dist = this(5)
  have st: \<open> cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
    using st by auto
  have \<open>get_all_learned_clss U \<subseteq># get_all_learned_clss T\<close>
    using res by (auto simp: cdcl_twl_restart.simps image_mset_subseteq_mono)
  then have \<open>get_all_learned_clss U - A \<subseteq>#
          learned_clss (state\<^sub>W_of T) - A\<close>
    using mset_le_subtract by (cases S; cases T; cases U)
       (auto simp: learned_clss.simps ac_simps
        intro!: distinct_mset_mono[of \<open>get_all_learned_clss U - get_all_learned_clss S\<close>
          \<open>learned_clss (state\<^sub>W_of T) - learned_clss (state\<^sub>W_of S)\<close>])
  moreover {
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
      by (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[OF st]) (use invs in simp)
    then have \<open>distinct_mset (learned_clss (state\<^sub>W_of T) - A)\<close>
      apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
      subgoal using invs unfolding twl_struct_invs_def fst_conv by fast
      subgoal using invs unfolding twl_struct_invs_def fst_conv by fast
      subgoal using dist by simp
      done
  }
  ultimately show ?case
    unfolding fst_conv
    by (rule distinct_mset_mono)
next
  case (restart_full S T n) note st = this(1) and invs = this(2) and dist = this(3)
  have st: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
    using st unfolding full1_def by fastforce
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
    by (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[OF st]) (use invs in simp)
  then have \<open>distinct_mset (learned_clss (state\<^sub>W_of T) - A)\<close>
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
    subgoal using invs unfolding twl_struct_invs_def fst_conv by fast
    subgoal using invs unfolding twl_struct_invs_def fst_conv by fast
    subgoal using dist by simp
    done
  then show ?case
    by (cases S; cases T) (auto simp: learned_clss.simps)
qed

lemma rtranclp_cdcl_twl_stgy_restart_new_abs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>distinct_mset (get_all_learned_clss (fst S) - A)\<close>
  shows \<open>distinct_mset (get_all_learned_clss (fst T) - A)\<close>
  using assms apply (induction)
  subgoal by auto
  subgoal by (auto intro: cdcl_twl_stgy_restart_new rtranclp_cdcl_twl_stgy_restart_twl_struct_invs)
  done

lemma cdcl_twl_stgy_restart_get_init_learned_clss_mono:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close>
  shows \<open>get_init_learned_clss (fst S) \<subseteq># get_init_learned_clss (fst T)\<close>
  using assms
  by (induction) (auto dest!: rtranclp_cdcl_twl_stgy_get_init_learned_clss_mono
      tranclp_into_rtranclp
      simp: cdcl_twl_restart.simps full1_def)

lemma rtranclp_cdcl_twl_stgy_restart_get_init_learned_clss_mono:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close>
  shows \<open>get_init_learned_clss (fst S) \<subseteq># get_init_learned_clss (fst T)\<close>
  using assms
  by induction (auto dest!: tranclp_into_rtranclp cdcl_twl_stgy_restart_get_init_learned_clss_mono)

lemma rtranclp_cdcl_twl_stgy_restart_get_learned_clss_abs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>distinct_mset (clauses (get_learned_clss (fst S)) - A)\<close>
  shows \<open>distinct_mset (clauses (get_learned_clss (fst T)) - A)\<close>
  using rtranclp_cdcl_twl_stgy_restart_new_abs[OF assms(1,2), of
     \<open>A + get_init_learned_clss (fst T)\<close>] assms(3)
   rtranclp_cdcl_twl_stgy_restart_get_init_learned_clss_mono[OF assms(1)]
   distinct_mset_minus
  apply (cases S; cases T)
  apply (auto intro: distinct_mset_mono)
  apply (rule distinct_mset_mono[of _ \<open>get_all_learned_clss (fst T) -
      (A + get_init_learned_clss (fst T))\<close>])
  by (fastforce simp: mset_subset_eq_exists_conv)+


theorem wf_cdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v twl_st \<times> nat). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v twl_st \<times> nat\<close> where
    g: \<open>\<And>i. cdcl_twl_stgy_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. twl_struct_invs (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast

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

  have H: False if \<open>no_step cdcl_twl_stgy (fst (g i))\<close> for i
    using g[of i] that
    unfolding cdcl_twl_stgy_restart.simps
    by (auto simp: full1_def tranclp_unfold_begin)

  have \<open>\<exists>h. cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (h) \<and>
         size (get_learned_clss (h)) > f (snd (g i)) \<and>
         cdcl_twl_restart (h) (fst (g (i+1)))\<close>
    for i
    using g[of i] H[of \<open>Suc i\<close>]
    unfolding cdcl_twl_stgy_restart.simps full1_def Suc_eq_plus1[symmetric]
    by force
  then obtain h :: \<open>nat \<Rightarrow> 'v twl_st\<close> where
    cdcl_twl: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (h i)\<close> and
    size_h_g: \<open>size (get_learned_clss (h i)) > f (snd (g i))\<close> and
    res: \<open>cdcl_twl_restart (h i) (fst (g (i+1)))\<close> for i
    by metis

  obtain k where
    f_g_k: \<open>f (snd (g k)) >
       card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h 0))))) +
           size (clauses (get_learned_clss (fst (g 0))))\<close>
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  have cdcl_twl: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* (fst (g i)) (h i)\<close> for i
    using cdcl_twl[of i] by auto
  have W_g_h: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of (fst (g i))) (state\<^sub>W_of (h i))\<close> for i
    by (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[OF cdcl_twl]) (rule inv)
  have tranclp_g: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (g 0) (g i)\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal for i using g[of i] by auto
    done

  have dist_all_g:
    \<open>distinct_mset (get_all_learned_clss (fst (g i)) - get_all_learned_clss (fst (g 0)))\<close>
    for i
    apply (rule rtranclp_cdcl_twl_stgy_restart_new_abs[OF tranclp_g])
    subgoal using inv .
    subgoal by simp
    done

  have dist_h: \<open>distinct_mset (get_all_learned_clss (h i) - get_all_learned_clss (fst (g 0)))\<close>
    (is \<open>distinct_mset (?U i)\<close>)
    for i
    unfolding learned_clss_get_all_learned_clss[symmetric]
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs[OF W_g_h])
    subgoal using inv[of i] unfolding twl_struct_invs_def by fast
    subgoal using inv[of i] unfolding twl_struct_invs_def by fast
    subgoal using dist_all_g[of i] distinct_mset_minus
        rtranclp_cdcl_twl_stgy_restart_get_init_learned_clss_mono[OF tranclp_g, of i]
      unfolding learned_clss_get_all_learned_clss by auto
    done
  have dist_diff: \<open>distinct_mset (c + (Ca + C) - ai) \<Longrightarrow>
       distinct_mset (c - ai)\<close> for c Ca C ai
    by (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute
        distinct_mset_minus)
  have dist_h:
    \<open>distinct_mset (clauses (get_learned_clss (h i)) - clauses (get_learned_clss (fst (g 0))))\<close>
    (is \<open>distinct_mset (?U i)\<close>)
    for i
    using dist_h[of i]
      rtranclp_cdcl_twl_stgy_get_init_learned_clss_mono[OF cdcl_twl, of i]
      rtranclp_cdcl_twl_stgy_restart_get_init_learned_clss_mono[OF tranclp_g, of i]
    by (cases \<open>g i\<close>; cases \<open>h i\<close>; cases \<open>g 0\<close>)
      (auto simp: mset_subset_eq_exists_conv dest: dist_diff
        intro: distinct_mset_mono)

  have \<open>get_learned_clss (fst (g (Suc i))) \<subseteq># get_learned_clss (h i)\<close> for i
    using res[of i] by (auto simp: cdcl_twl_restart.simps image_mset_subseteq_mono)

  have h_g: \<open>init_clss (state\<^sub>W_of (h i)) = init_clss (state\<^sub>W_of (fst (g i)))\<close> for i
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss[OF W_g_h[of i]] ..

  have h_g_Suc: \<open>init_clss (state\<^sub>W_of (h i)) = init_clss (state\<^sub>W_of (fst (g (Suc i))))\<close> for i
    using res[of i] by (auto simp: cdcl_twl_restart.simps init_clss.simps)
  have init_g_0: \<open>init_clss (state\<^sub>W_of (fst (g i))) = init_clss (state\<^sub>W_of (fst (g 0)))\<close> for i
    apply (induction i)
    subgoal ..
    subgoal for j
      using h_g[of j] h_g_Suc[of j] by simp
    done
  then have K: \<open>init_clss (state\<^sub>W_of (h i)) = init_clss (state\<^sub>W_of (fst (g 0)))\<close> for i
    using h_g[of i] by simp

  have incl: \<open>set_mset (get_all_learned_clss (h i)) \<subseteq>
         simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close> for i
    unfolding learned_clss_get_all_learned_clss[symmetric]
    supply [[unify_trace_failure]]
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_new_learned_in_all_simple_clss[of \<open>state\<^sub>W_of (fst (g i))\<close>])
    subgoal by (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[OF cdcl_twl]) (rule inv)
    subgoal using inv[of i]  unfolding twl_struct_invs_def by fast
    done
  have incl: \<open>set_mset (clauses (get_learned_clss (h i))) \<subseteq>
         simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close>  (is \<open>set_mset (?V i) \<subseteq> _\<close>) for i
    using incl[of i] by (cases \<open>h i\<close>) (auto dest: in_diffD)

  have incl_init: \<open>set_mset (?U i) \<subseteq> simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close> for i
    using incl[of i] by (auto dest: in_diffD)
  have size_U_atms: \<open>size (?U i) \<le> card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i)))))\<close> for i
    apply (subst distinct_mset_size_eq_card[OF dist_h])
    apply (rule card_mono[OF _ incl_init])
    by (auto simp: simple_clss_finite)
  have S:
    \<open>size (?V i) - size (clauses (get_learned_clss (fst (g 0)))) \<le>
      card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i)))))\<close> for i
    apply (rule order.trans)
     apply (rule diff_size_le_size_Diff)
    apply (rule size_U_atms)
    done
  have S:
    \<open>size (?V i) \<le>
      card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))) +
       size (clauses (get_learned_clss (fst (g 0))))\<close> for i
    using S[of i] by auto

  have H: \<open>card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h k))))) +
         size (clauses (get_learned_clss (fst (g 0)))) > f (k + snd (g 0))\<close> for k
    using S[of k] size_h_g[of k] unfolding snd_g[symmetric]
    by force

  show False
    using H[of k] f_g_k unfolding snd_g[symmetric]
    unfolding K
    by linarith
qed

end

end