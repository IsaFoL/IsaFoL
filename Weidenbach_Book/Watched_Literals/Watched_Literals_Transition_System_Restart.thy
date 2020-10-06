theory Watched_Literals_Transition_System_Restart
imports CDCL.Pragmatic_CDCL_Restart Watched_Literals_Transition_System
  Watched_Literals_Transition_System_Inprocessing
begin


text \<open>
  Unlike the basic CDCL, it does not make any sense to fully restart the trail:
  the part propagated at level 0 (only the part due to unit clauses) has to be kept.
  Therefore, we allow fast restarts (i.e. a restart where part of the trail is reused).

  There are two cases:
    \<^item> either the trail is strictly decreasing;
    \<^item> or it is kept and the number of clauses is strictly decreasing.

  This ensures that \<^emph>\<open>something\<close> changes to prove termination.

  In practice, there are two types of restarts that are done:
    \<^item> First, a restart can be done to enforce that the SAT solver goes more into the direction
      expected by the decision heuristics.
    \<^item> Second, a full restart can be done to simplify inprocessing and garbage collection of the memory:
      instead of properly updating the trail, we restart the search. This is not necessary (i.e.,
      glucose and minisat do not do it), but it simplifies the proofs by allowing to move clauses
      without taking care of updating references in the trail. Moreover, as this happens ``rarely''
      (around once every few thousand conflicts), it should not matter too much.

  Restarts are the ``local search'' part of all modern SAT solvers.
\<close>

inductive cdcl_twl_restart :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart (M, N, U, None, NE, UE, NS, US, {#}, Q)
        (M', N', U', None, NE + clauses NE', UE + clauses UE', NS, {#},
           {#}, {#})\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#clause E. L \<in> lits_of_l M' \<and> get_level M' L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M' \<longrightarrow> E \<in># clause `# (N + U') + NE + UE + clauses UE'\<close> |
restart_clauses:
   \<open>cdcl_twl_restart (M, N, U, None, NE, UE, NS, US, {#}, Q)
      (M, N', U', None, NE + clauses NE', UE + clauses UE', NS, US',
        {#}, Q)\<close>
  if
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#clause E. L \<in> lits_of_l M \<and> get_level M L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M \<longrightarrow> E \<in># clause `# (N + U') + NE + UE + clauses UE'\<close>
    \<open>US' = {#}\<close>

inductive_cases cdcl_twl_restartE: \<open>cdcl_twl_restart S T\<close>


inductive cdcl_twl_restart_only :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
restart_trail:
  \<open>cdcl_twl_restart_only (M, N, U, None, NE, UE, NS, US, {#}, Q)
  (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> |
norestart_trail:
  \<open>cdcl_twl_restart_only (M, N, U, None, NE, UE, NS, US, {#}, Q)
    (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>



lemma cdcl_twl_restart_pcdcl: \<open>cdcl_twl_restart S T \<Longrightarrow> pcdcl_restart (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  by (induction rule: cdcl_twl_restart.induct)
    (auto simp add: pcdcl_restart.simps dest: image_mset_subseteq_mono) 

lemma cdcl_twl_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_restart S T\<close> and
    \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using assms cdcl_twl_restart_pcdcl[OF assms(1)]
proof (induction rule: cdcl_twl_restart.induct)
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US Q)
  note decomp = this(1) and learned' = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6) and st' = this(7)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  let ?S' = \<open>(M', N', U', None, NE+ clauses NE', UE + clauses UE', NS, {#}, {#}, {#})\<close>
  have learned: \<open>U' \<subseteq># U\<close>
    using learned' by (rule mset_le_decr_left1)
  have
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    \<open>valid_enqueued ?S\<close> and
    struct_inv: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of ?S)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close> and
    \<open>twl_st_exception_inv ?S\<close> and
    no_dup_q: \<open>no_duplicate_queued ?S\<close> and
    dist: \<open>distinct_queued ?S\<close> and
    \<open>confl_cands_enqueued ?S\<close> and
    \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow>
     clauses_to_update ?S = {#} \<and>
     literals_to_update ?S = {#}\<close> and
    to_upd: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using inv unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by clarsimp+
  have
    ex: \<open>(\<forall>C\<in>#N + U. twl_lazy_update M' C \<and>
           watched_literals_false_of_max_level M' C \<and>
           twl_exception_inv (M', N, U, None, NE, UE, NS, US, {#}, {#}) C)\<close> and
     conf_cands: \<open>confl_cands_enqueued (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close> and
     propa_cands: \<open>propa_cands_enqueued (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close> and
     clss_to_upd: \<open>clauses_to_update_inv (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     using past get_all_ann_decomposition_exists_prepend[OF decomp] unfolding past_invs.simps
     by force+

   have excp_inv: \<open>twl_st_exception_inv (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     using ex unfolding twl_st_exception_inv.simps by blast+
   have twl_st_inv': \<open>twl_st_inv (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     using ex learned twl_st_inv
     unfolding twl_st_exception_inv.simps twl_st_inv.simps
     by auto
   have n_d: \<open>no_dup M\<close>
     using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
     by (auto simp: trail.simps)
   obtain M3 where
     M: \<open>M = M3 @ M2 @ Decided K # M'\<close>
     using decomp by blast
   define M3' where \<open>M3' = M3 @ M2\<close>
   then have M3': \<open>M = M3' @ Decided K # M'\<close>
     unfolding M by auto
   have a: \<open>N \<subseteq># N\<close> and NN': \<open>N' \<subseteq># N\<close> using N by auto
   have past_invs: \<open>past_invs ?S'\<close>
     unfolding past_invs.simps
   proof (intro conjI impI allI)
     fix M1 M2 K'
     assume H:\<open>M' = M2 @ Decided K' # M1\<close>
     let ?U = \<open>(M1, N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     let ?U' = \<open>(M1, N', U', None, NE+clauses NE', UE+clauses UE', NS, {#}, {#}, {#})\<close>
     have \<open>M = (M3' @ Decided K # M2) @ Decided K' # M1\<close>
       using H M3' by simp
     then have
       1: \<open>\<forall>C\<in>#N + U.
           twl_lazy_update M1 C \<and>
           watched_literals_false_of_max_level M1 C \<and>
           twl_exception_inv ?U C\<close> and
       2: \<open>confl_cands_enqueued ?U\<close> and
       3: \<open>propa_cands_enqueued ?U\<close> and
       4: \<open>clauses_to_update_inv ?U\<close>
       using past unfolding past_invs.simps by blast+
     show \<open>\<forall>C\<in>#N' + U'.
          twl_lazy_update M1 C \<and>
          watched_literals_false_of_max_level M1 C \<and>
          twl_exception_inv ?U' C\<close>
       using 1 learned twl_st_exception_inv_mono[OF learned NN', of M1 None NE \<open>UE\<close>
           NS US \<open>{#}\<close> \<open>{#}\<close> \<open>NE+clauses NE'\<close> \<open>UE+clauses UE'\<close>] N
         twl_st_exception_inv_subsumed_mono[of  \<open>{#}\<close> US M1 N' U' None \<open>NE+clauses NE'\<close>
           \<open>UE + clauses UE'\<close> NS \<open>{#}\<close> \<open>{#}\<close>]
        by auto

     show \<open>confl_cands_enqueued ?U'\<close>
       by (rule confl_cands_enqueued_subsumed_mono[OF _ confl_cands_enqueued_mono[OF learned NN' 2]])
         auto
     show \<open>propa_cands_enqueued ?U'\<close>
       by (rule propa_cands_enqueued_subsumed_mono[OF _ propa_cands_enqueued_mono[OF learned NN' 3]])
         auto
     show \<open>clauses_to_update_inv ?U'\<close>
       using 4 learned by (auto simp add: filter_mset_empty_conv N)
   qed
   have clss_to_upd: \<open>clauses_to_update_inv ?S'\<close>
     using clss_to_upd learned by (auto simp add: filter_mset_empty_conv N)

   have struct_inv': \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of ?S')\<close>
     using pcdcl_restart_pcdcl_all_struct_invs[OF st' struct_inv] by simp
   have smaller': \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S')\<close>
     using pcdcl_restart_no_smaller_propa'[OF st'] smaller by simp
   show ?case
     unfolding twl_struct_invs_def
     apply (intro conjI)
     subgoal
       using twl_st_inv_subsumed_mono[OF _ twl_st_inv_mono[OF learned NN' twl_st_inv']]
       by (auto simp: ac_simps N)
     subgoal by simp
     subgoal by (rule struct_inv')
     subgoal by (rule smaller')
     subgoal by (rule twl_st_exception_inv_subsumed_mono[OF _ twl_st_exception_inv_mono[OF learned NN' excp_inv]])
       auto
     subgoal using no_dup_q by auto
     subgoal using dist by auto
     subgoal by (rule confl_cands_enqueued_subsumed_mono[OF _ confl_cands_enqueued_mono[OF learned NN' conf_cands]])
       auto
     subgoal by (rule propa_cands_enqueued_subsumed_mono[OF _ propa_cands_enqueued_mono[OF learned NN' propa_cands]])
       auto
     subgoal by simp
     subgoal by (rule clss_to_upd)
     subgoal by (rule past_invs)
     done
next
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US Q)
  note learned' = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and invs = this(6) and st' = this(7)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  let ?T = \<open>(M, N', U', None, NE+clauses NE', UE +clauses UE', NS, US', {#}, Q)\<close>
  have learned: \<open>U' \<subseteq># U\<close>
    using learned' by (rule mset_le_decr_left1)
  have
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    valid: \<open>valid_enqueued ?S\<close> and
    struct_inv: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of ?S)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close> and
    excp_inv: \<open>twl_st_exception_inv ?S\<close> and
    no_dup_q: \<open>no_duplicate_queued ?S\<close> and
    dist: \<open>distinct_queued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close> and
    propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow>
     clauses_to_update ?S = {#} \<and>
     literals_to_update ?S = {#}\<close> and
    to_upd: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using invs unfolding twl_struct_invs_def by clarify+
   have n_d: \<open>no_dup M\<close>
     using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def by (auto simp: trail.simps)
   have valid': \<open>valid_enqueued ?T\<close>
     using valid by auto

   have NN': \<open>N' \<subseteq># N\<close> unfolding N by auto
   have past_invs: \<open>past_invs ?T\<close>
     using past unfolding past_invs.simps
   proof (intro conjI impI allI)
     fix M1 M2 K'
     assume H:\<open>M = M2 @ Decided K' # M1\<close>
     let ?U = \<open>(M1, N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     let ?U' = \<open>(M1, N', U', None, NE+clauses NE', UE + clauses UE', NS, US', {#}, {#})\<close>
     have
       1: \<open>\<forall>C\<in>#N + U.
           twl_lazy_update M1 C \<and>
           watched_literals_false_of_max_level M1 C \<and>
           twl_exception_inv ?U C\<close> and
       2: \<open>confl_cands_enqueued ?U\<close> and
       3: \<open>propa_cands_enqueued ?U\<close> and
       4: \<open>clauses_to_update_inv ?U\<close>
       using H past unfolding past_invs.simps by blast+
     show \<open>\<forall>C\<in>#N' + U'.
          twl_lazy_update M1 C \<and>
          watched_literals_false_of_max_level M1 C \<and>
          twl_exception_inv ?U' C\<close>
       using 1 learned twl_st_exception_inv_subsumed_mono[OF _
              twl_st_exception_inv_mono[OF learned NN', of M1 None NE UE NS US \<open>{#}\<close> \<open>{#}\<close>
              \<open>NE + clauses NE'\<close> \<open>UE + clauses UE'\<close>], of \<open>US'\<close>] N US
       by (auto split: if_splits)
     show \<open>confl_cands_enqueued ?U'\<close>
       by (rule confl_cands_enqueued_subsumed_mono[OF _ confl_cands_enqueued_mono[OF learned NN' 2]])
         (use US in \<open>auto split: if_splits\<close>)
     show \<open>propa_cands_enqueued ?U'\<close>
       by (rule propa_cands_enqueued_subsumed_mono[OF _ propa_cands_enqueued_mono[OF learned NN' 3]])
         (use US in \<open>auto split: if_splits\<close>)
     show \<open>clauses_to_update_inv ?U'\<close>
       using 4 learned by (auto simp add: filter_mset_empty_conv N)
   qed

   let ?S' = \<open>(M, N', U', None, NE + clauses NE', UE + clauses UE', NS, US', {#}, Q)\<close>
   have struct_inv': \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of ?S')\<close>
     using pcdcl_restart_pcdcl_all_struct_invs[OF st' struct_inv] by simp
   have smaller': \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S')\<close>
     using pcdcl_restart_no_smaller_propa'[OF st'] smaller by simp

   have clss_to_upd: \<open>clauses_to_update_inv ?T\<close>
     using to_upd learned by (auto simp add: filter_mset_empty_conv N ac_simps)


   show ?case
    unfolding twl_struct_invs_def
    apply (intro conjI)
    subgoal using twl_st_inv_subsumed_mono[OF _ twl_st_inv_mono[OF learned NN' twl_st_inv]] US
      by (auto simp: ac_simps N split: if_splits)
    subgoal by (rule valid')
    subgoal by (rule struct_inv')
    subgoal by (rule smaller')
    subgoal by (rule twl_st_exception_inv_subsumed_mono[OF _ twl_st_exception_inv_mono[OF learned NN' excp_inv]])
      (use US in \<open>auto split: if_splits\<close>)
    subgoal using no_dup_q by auto
    subgoal using dist by auto
    subgoal by (rule confl_cands_enqueued_subsumed_mono[OF _ confl_cands_enqueued_mono[OF learned NN' confl_cands]])
      (use US in \<open>auto split: if_splits\<close>)
    subgoal by (rule propa_cands_enqueued_subsumed_mono[OF _ propa_cands_enqueued_mono[OF learned NN' propa_cands]])
      (use US in \<open>auto split: if_splits\<close>)
    subgoal by simp
    subgoal by (rule clss_to_upd)
    subgoal by (rule past_invs)
    done
qed


lemma rtranclp_cdcl_twl_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using assms by (induction rule: rtranclp_induct) (auto simp: cdcl_twl_restart_twl_struct_invs)

lemma cdcl_twl_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_restart S T\<close> and \<open>twl_stgy_invs S\<close>
  shows \<open>twl_stgy_invs T\<close>
  using assms
  by (induction rule: cdcl_twl_restart.induct)
   (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
        conflicting.simps cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def trail.simps
      dest!: get_all_ann_decomposition_exists_prepend
      split: if_splits)

lemma rtranclp_cdcl_twl_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>twl_stgy_invs T\<close>
  using assms by (induction rule: rtranclp_induct) (auto simp: cdcl_twl_restart_twl_stgy_invs)

lemma cdcl_twl_restart_only_cdcl: \<open>cdcl_twl_restart_only T U \<Longrightarrow>
  pcdcl_restart_only (pstate\<^sub>W_of T) (pstate\<^sub>W_of U)\<close>
  by (auto 5 3 simp: cdcl_twl_restart_only.simps pcdcl_restart_only.simps)

lemma cdcl_twl_restart_only_twl_struct_invs:
  assumes
    \<open>cdcl_twl_restart_only S T\<close> and
    \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using assms cdcl_twl_restart_only_cdcl[OF assms(1)]
proof (induction rule: cdcl_twl_restart_only.induct)
  case (norestart_trail M N U NE UE NS US Q)
  note invs = this(1) and st' = this(2)
  then show ?case
    by simp
next
  case (restart_trail K M' M2 M N U NE UE NS US Q)
  note decomp = this(1) and inv = this(2) and st' = this(3)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  let ?T = \<open>(M', N, U, None, NE, UE, NS, US, {#}, {#})\<close>
  have
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    \<open>valid_enqueued ?S\<close> and
    struct_inv: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of ?S)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    no_dup_q: \<open>no_duplicate_queued ?S\<close> and
    dist: \<open>distinct_queued ?S\<close> and
    confl: \<open>confl_cands_enqueued ?S\<close> and
    propa: \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow>
     clauses_to_update ?S = {#} \<and>
     literals_to_update ?S = {#}\<close> and
    to_upd: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using inv unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by clarsimp+
  have
    ex: \<open>(\<forall>C\<in>#N + U. twl_lazy_update M' C \<and>
           watched_literals_false_of_max_level M' C \<and>
           twl_exception_inv (M', N, U, None, NE, UE, NS, US, {#}, {#}) C)\<close> and
     conf_cands: \<open>confl_cands_enqueued (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close> and
     propa_cands: \<open>propa_cands_enqueued (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close> and
     clss_to_upd: \<open>clauses_to_update_inv (M', N, U, None, NE, UE, NS, US, {#}, {#})\<close>
    using past get_all_ann_decomposition_exists_prepend[OF decomp]
      confl propa to_upd excep
    unfolding past_invs.simps
    by force+

   have excp_inv: \<open>twl_st_exception_inv ?T\<close>
     using ex unfolding twl_st_exception_inv.simps by blast+
   have twl_st_inv': \<open>twl_st_inv ?T\<close>
     using ex twl_st_inv
     unfolding twl_st_exception_inv.simps twl_st_inv.simps
     by auto
   have n_d: \<open>no_dup M\<close>
     using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
     by (auto simp: trail.simps)
   obtain M3 where
     M: \<open>M = M3 @ M2 @ Decided K # M'\<close>
     using decomp by blast
   define M3' where \<open>M3' = M3 @ M2\<close>
   then have M3': \<open>M = M3' @ Decided K # M'\<close>
     unfolding M by auto
   have past_invs: \<open>past_invs ?T\<close>
     unfolding past_invs.simps
   proof (intro conjI impI allI)
     fix M1 M2 K'
     assume H:\<open>M' = M2 @ Decided K' # M1\<close>
     let ?U = \<open>(M1, N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     let ?U' = \<open>(M1, N, U, None, NE, UE, NS, US, {#}, {#})\<close>
     have \<open>M = (M3' @ Decided K # M2) @ Decided K' # M1\<close>
       using H M3' by simp
     then show 
       1: \<open>\<forall>C\<in>#N + U.
           twl_lazy_update M1 C \<and>
           watched_literals_false_of_max_level M1 C \<and>
           twl_exception_inv ?U C\<close> and
       2: \<open>confl_cands_enqueued ?U\<close> and
       3: \<open>propa_cands_enqueued ?U\<close> and
       4: \<open>clauses_to_update_inv ?U\<close>
       using past unfolding past_invs.simps by blast+
   qed
   have clss_to_upd: \<open>clauses_to_update_inv ?T\<close>
     using clss_to_upd by (auto simp add: filter_mset_empty_conv)

   have struct_inv': \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of ?T)\<close>
     using pcdcl_restart_only_pcdcl_all_struct_invs st' struct_inv by fastforce
   have smaller': \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?T)\<close>
     using pcdcl_restart_only_no_smaller_propa smaller st' state\<^sub>W_of_def struct_inv by force
   show ?case
     unfolding twl_struct_invs_def
     apply (intro conjI)
     subgoal
       using twl_st_inv' by (auto simp: ac_simps)
     subgoal by simp
     subgoal by (rule struct_inv')
     subgoal by (rule smaller')
     subgoal using excp_inv by auto
     subgoal using no_dup_q by auto
     subgoal using dist by auto
     subgoal using conf_cands by auto

     subgoal using propa_cands by auto
     subgoal by simp
     subgoal by (rule clss_to_upd)
     subgoal by (rule past_invs)
     done
qed

definition pcdcl_twl_final_state :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>pcdcl_twl_final_state S \<longleftrightarrow> no_step cdcl_twl_stgy S \<or>
  (count_decided (get_trail S) = 0 \<and> get_conflict S \<noteq> None)\<close>


context twl_restart_ops
begin
text \<open>
  This is en essence the calculus with restarts we are now using. Compared to the version in my
  thesis, the major difference is that we don't restrict restarts anymore, by requiring only that
  at least one clause has been learned since.

  However, this has a major drawback: The transition do not depend only on the current state, but
  also on the path that was taken. This is annoying for refinement, because the main loop does not
  do one transition anymore, but only a part of transitions. The difference is very small on the
  practical side, but that makes the termination more involved.

  We allow inprocessing, but restrict it a lot. We could allow anything such that the invariants
  are still fulfilled afterwards, but we currently restrict to be some CDCL steps (TODO: generalise
  to also include restarts) and add requirements on the output.
\<close>
type_synonym 'v twl_st_restart = \<open>'v twl_st \<times> 'v twl_st \<times> 'v twl_st \<times> nat \<times> nat \<times> bool\<close>
inductive cdcl_twl_stgy_restart :: \<open>'v twl_st_restart \<Rightarrow> 'v twl_st_restart  \<Rightarrow> bool\<close> where
step:
 \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (R, S, U, m, n, True)\<close>
 if
   \<open>cdcl_twl_stgy T U\<close> |
restart_step:
  \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (W, W, W, m, Suc n, True)\<close>
  if
    \<open>size (get_all_learned_clss T) - size (get_all_learned_clss R) > f n\<close> and
    \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* T U\<close> and
    \<open>count_decided (get_trail U) = 0\<close>
    \<open>cdcl_twl_restart U V\<close> and
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close>
    \<open>clauses_to_update W = {#}\<close>
    \<open>get_conflict W \<noteq> None \<longrightarrow> count_decided (get_trail W) = 0\<close> |
restart_noGC:
  \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (R, U, U, Suc m, n, True)\<close>
  if
    \<open>size (get_all_learned_clss T) > size (get_all_learned_clss S)\<close> and
    \<open>cdcl_twl_restart_only T U\<close> |
restart_full:
 \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (R, S, T, m, n, False)\<close>
 if
   \<open>pcdcl_twl_final_state T\<close>

lemma cdcl_twl_stgy_restart_induct[consumes 1, case_names restart_step restart_noGC full]:
  assumes
    \<open>cdcl_twl_stgy_restart (R, S, T, m, n, b) (R', S', T', m', n', b')\<close> and
    \<open>\<And>R S T U. cdcl_twl_stgy T U \<Longrightarrow> m' = m \<Longrightarrow> n' = n \<Longrightarrow> b \<Longrightarrow> b' \<Longrightarrow>  P R S T m n True R S U m n True\<close> and
    \<open>\<And>R S T U V W.
      f n < size (get_all_learned_clss T) - size (get_all_learned_clss R) \<Longrightarrow> cdcl_twl_subsumption_inp\<^sup>*\<^sup>* T U \<Longrightarrow>
      cdcl_twl_restart U V \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V W \<Longrightarrow>
     clauses_to_update W = {#} \<Longrightarrow> (get_conflict W \<noteq> None \<Longrightarrow> count_decided (get_trail W) = 0) \<Longrightarrow>
     count_decided (get_trail U) = 0 \<Longrightarrow> 
      m' = m \<Longrightarrow> n' = Suc n \<Longrightarrow>
      P R S T m n True W W W m (Suc n) True\<close>and
    \<open>\<And>R S T U.
      size (get_all_learned_clss T) > size (get_all_learned_clss S) \<Longrightarrow>
      cdcl_twl_restart_only T U \<Longrightarrow> m' = Suc m \<Longrightarrow> n' = n \<Longrightarrow>
    P R S T m n True R U U (Suc m) n True\<close>
    \<open>pcdcl_twl_final_state T \<Longrightarrow> R' = R \<Longrightarrow> S' = S \<Longrightarrow> T' = T \<Longrightarrow> P R S T m n True R S T m n False\<close>
  shows \<open>P R S T m n b R' S' T' m' n' b'\<close>
  using assms(1)
  apply (cases rule: cdcl_twl_stgy_restart.cases)
  subgoal
    using assms(2)[of T T' R S]
    by simp
  subgoal for U
    using assms(3)[of ]
    by simp
  subgoal
    using assms(4)[of ]
    by simp
  subgoal
    using assms(5)[of ]
    by simp
  done


lemma tranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy2:
  \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T \<Longrightarrow>
  twl_struct_invs S \<Longrightarrow> (pstate\<^sub>W_of S) \<noteq> (pstate\<^sub>W_of T) \<Longrightarrow>
  pcdcl_tcore_stgy\<^sup>+\<^sup>+ (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[of S T] unfolding rtranclp_unfold
  by auto

lemma tranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy3:
  \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T \<Longrightarrow>
  size (get_all_learned_clss T) > size (get_all_learned_clss S) \<Longrightarrow>
  twl_struct_invs S \<Longrightarrow>
  pcdcl_tcore_stgy\<^sup>+\<^sup>+ (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[of S T] unfolding rtranclp_unfold
  apply auto
  apply (cases T; cases S)
  apply (auto simp: clauses_def dest!: arg_cong[of \<open>clauses _\<close> _ size])
  done

lemma [twl_st, simp]:
  \<open>pget_all_learned_clss (pstate\<^sub>W_of T) = get_all_learned_clss T\<close>
  \<open>pget_conflict (pstate\<^sub>W_of T) = get_conflict T\<close>
  by (cases T; auto; fail)+

lemma pcdcl_twl_final_state_pcdcl:
  \<open>pcdcl_twl_final_state S \<Longrightarrow>
  twl_struct_invs S \<Longrightarrow> pcdcl_final_state (pstate\<^sub>W_of S)\<close>
  using no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy[of S]
  unfolding pcdcl_twl_final_state_def pcdcl_final_state_def
  by (auto simp add: no_step_pcdcl_core_stgy_pcdcl_coreD)

lemma pcdcl_stgy_restart_stepI:
  \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* T T' \<Longrightarrow> pcdcl_stgy_restart\<^sup>*\<^sup>* (R, S, T, m, n, True) (R, S, T', m, n, True)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for V W
    by (auto dest!: pcdcl_stgy_restart.intros(1)[of _ _ R S m n])
  done

lemma rtranclp_cdcl_twl_subsumption_inp_pcdcl_inprocessing:
  \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  pcdcl_inprocessing\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  apply (drule rtranclp_cdcl_twl_subsumption_inp_pcdcl; assumption?)
  by (metis mono_rtranclp pcdcl_inprocessing.intros(1))

lemma cdcl_twl_stgy_restart_pcdcl:
  \<open>cdcl_twl_stgy_restart (R, S :: 'v twl_st, T, m, n, g) (R', S', T', m', n', h) \<Longrightarrow>
  twl_struct_invs R \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_struct_invs T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<Longrightarrow>
  pcdcl_stgy_restart\<^sup>*\<^sup>* (pstate\<^sub>W_of R, pstate\<^sub>W_of S, pstate\<^sub>W_of T, m, n, g)
      (pstate\<^sub>W_of R', pstate\<^sub>W_of S', pstate\<^sub>W_of T', m', n', h)\<close>
  apply (induction rule: cdcl_twl_stgy_restart_induct)
  subgoal for R S T U
    by (drule cdcl_twl_stgy_cdcl\<^sub>W_stgy)
      (simp add: pcdcl_stgy_restart_stepI)+
  subgoal
    apply (rule r_into_rtranclp)
    apply (rule pcdcl_stgy_restart.intros(2))
    apply simp
    apply (rule rtranclp_cdcl_twl_subsumption_inp_pcdcl_inprocessing; assumption)
    apply (simp; fail)
    apply (rule cdcl_twl_restart_pcdcl, assumption)
    using cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_tcore_stgy_pcdcl_stgy'
    by (simp add: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs)
  subgoal
    apply (rule r_into_rtranclp)
    apply (rule pcdcl_stgy_restart.intros(3))
    apply simp
    apply (rule cdcl_twl_restart_only_cdcl, assumption)
    done
  subgoal
    apply (rule r_into_rtranclp)
    apply (rule pcdcl_stgy_restart.intros(4))
    by (simp add: twl_restart_ops.pcdcl_twl_final_state_pcdcl)
  done


lemma cdcl_twl_stgy_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_struct_invs (fst (snd S))\<close> and
    \<open>twl_struct_invs (fst (snd (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of  (fst (snd (snd S))))\<close>
  shows \<open>twl_struct_invs (fst T) \<and> twl_struct_invs (fst (snd T)) \<and> twl_struct_invs (fst (snd (snd T)))\<close>
  using assms
  by (induction rule: cdcl_twl_stgy_restart.induct)
  (auto simp add: full1_def intro: rtranclp_cdcl_twl_stgy_twl_struct_invs
      dest: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs
      rtranclp_cdcl_twl_stgy_twl_struct_invs
   cdcl_twl_restart_only_twl_struct_invs
   simp:
     cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
     rtranclp_cdcl_twl_stgy_twl_struct_invs rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
   dest!: tranclp_into_rtranclp intro: rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs)

lemma pcdcl_restart_entailed_by_init:
  assumes \<open>pcdcl_restart S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl_restart.induct)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      subset_mset.le_iff_add ac_simps)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      subset_mset.le_iff_add ac_simps)
  done

lemma pcdcl_restart_only_entailed_by_init:
  assumes \<open>pcdcl_restart_only S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl_restart_only.induct)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      subset_mset.le_iff_add ac_simps)
  done


lemma cdcl_twl_stgy_restart_entailed_by_init:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_struct_invs (fst (snd S))\<close> and
    \<open>twl_struct_invs (fst (snd (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd S))))\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst T)) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd T))) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd T))))\<close>
  using assms
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal apply simp
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_entailed_by_init rtranclp_pcdcl_stgy_pcdcl
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' twl_struct_invs_def by blast
    subgoal apply simp
      by (smt cdcl_twl_restart_pcdcl cdcl_twl_restart_twl_struct_invs
        rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_cdcl_twl_subsumption_inp_pcdcl
        rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs rtranclp_pcdcl_entailed_by_init
        rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' state\<^sub>W_of_def
        pcdcl_restart_entailed_by_init twl_struct_invs_def)
    subgoal apply simp
      using cdcl_twl_restart_only_cdcl twl_restart_ops.pcdcl_restart_only_entailed_by_init
        twl_struct_invs_def by blast
    subgoal
      by simp
    done

lemma rtranclp_cdcl_twl_stgy_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_struct_invs (fst (snd S))\<close> and
    \<open>twl_struct_invs (fst (snd (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd S))))\<close>
  shows \<open>twl_struct_invs (fst T) \<and> twl_struct_invs (fst (snd T)) \<and> twl_struct_invs (fst (snd (snd T))) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst T)) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd T))) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd T))))\<close>
  using assms
  apply (induction)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_entailed_by_init[of T U] cdcl_twl_stgy_restart_twl_struct_invs[of T U]
    by simp
  done


lemma rtranclp_cdcl_twl_stgy_restart_pcdcl:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (R, S :: 'v twl_st, T, m, n, g) (R', S', T', m', n', h) \<Longrightarrow>
  twl_struct_invs R \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_struct_invs T \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of R) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<Longrightarrow>
  pcdcl_stgy_restart\<^sup>*\<^sup>* (pstate\<^sub>W_of R, pstate\<^sub>W_of S, pstate\<^sub>W_of T, m, n, g)
      (pstate\<^sub>W_of R', pstate\<^sub>W_of S', pstate\<^sub>W_of T', m', n', h)\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _, _, _, _)\<close> \<open>(_, _, _, _, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for R' S' T' m' n' g' R'' S'' T'' m'' n'' g''
    using rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of \<open>(R, S, T, m, n, g)\<close> \<open>(R', S', T', m', n', g')\<close>]
    by (auto dest: cdcl_twl_stgy_restart_pcdcl)
  done

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2:
  assumes \<open>cdcl_twl_stgy_restart (S, T, U, m, n, g) (S', T', U', m', n', g')\<close>
    and twl: \<open>twl_struct_invs U\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
  shows \<open>pcdcl_stgy_restart (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g)
       (pstate\<^sub>W_of S', pstate\<^sub>W_of T', pstate\<^sub>W_of U', m', n', g') \<or>
    (S = S' \<and> T = T' \<and> m = m' \<and> n = n' \<and> g = g' \<and>
      pstate\<^sub>W_of U = pstate\<^sub>W_of U' \<and> (literals_to_update_measure U', literals_to_update_measure U)
    \<in> lexn less_than 2)\<close>
  using assms(1,2,3)
  apply (induction rule: cdcl_twl_stgy_restart_induct)
  subgoal for R S T U
    by (drule  cdcl_twl_stgy_cdcl\<^sub>W_stgy2)
      (auto simp add: pcdcl_stgy_restart.step)
  subgoal
    apply (rule disjI1)
    apply (rule pcdcl_stgy_restart.intros(2))
    apply simp
    apply (rule rtranclp_cdcl_twl_subsumption_inp_pcdcl_inprocessing)
    apply assumption+
    apply (simp; fail)
    apply (rule cdcl_twl_restart_pcdcl, assumption)
    using cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_tcore_stgy_pcdcl_stgy'
    by (simp add: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs)
  subgoal
    apply (rule disjI1)
    apply (rule pcdcl_stgy_restart.intros(3))
    apply simp
    apply (rule cdcl_twl_restart_only_cdcl, assumption)
    done
  subgoal
    apply (rule disjI1)
    apply (rule pcdcl_stgy_restart.intros(4))
    by (simp add: twl_restart_ops.pcdcl_twl_final_state_pcdcl)
  done

abbreviation state\<^sub>W_of_restart where
  \<open>state\<^sub>W_of_restart \<equiv> (\<lambda>(S, T, U, n, b). (state\<^sub>W_of S, state\<^sub>W_of T, state\<^sub>W_of U, n))\<close>

definition twl_restart_inv :: \<open>'v twl_st_restart \<Rightarrow> bool\<close> where
  \<open>twl_restart_inv = (\<lambda>(Q, R, S, m, n). twl_struct_invs Q \<and> twl_struct_invs R \<and> twl_struct_invs S \<and>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of Q) \<and>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of R) \<and>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
   pcdcl_stgy_restart_inv (pstate\<^sub>W_of Q, pstate\<^sub>W_of R, pstate\<^sub>W_of S, m, n))\<close>
lemma cdcl_twl_stgy_entailed_by_init:
  \<open>cdcl_twl_stgy S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  apply (induction rule: cdcl_twl_stgy.induct)
  apply (metis cdcl_twl_stgy_cdcl\<^sub>W_stgy cp rtranclp_pcdcl_entailed_by_init rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' state\<^sub>W_of_def twl_struct_invs_def)
  by (metis cdcl_twl_o_cdcl\<^sub>W_o_stgy pcdcl_tcore_pcdcl pcdcl_tcore_stgy_pcdcl_tcoreD rtranclp_pcdcl_entailed_by_init state\<^sub>W_of_def twl_struct_invs_def)

lemma rtranclp_cdcl_twl_stgy_entailed_by_init:
  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  apply (induction rule: rtranclp_induct)
  apply auto[]
  using rtranclp_cdcl_twl_stgy_twl_struct_invs twl_restart_ops.cdcl_twl_stgy_entailed_by_init by blast

lemma cdcl_twl_stgy_restart_twl_restart_inv:
  \<open>cdcl_twl_stgy_restart S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_restart_inv T\<close>
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal for T U R S m n
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2[of R S T m n True R S U m n True]
    unfolding twl_restart_inv_def
    apply (auto intro: cdcl_twl_stgy_twl_struct_invs
      simp: pcdcl_stgy_restart_pcdcl_stgy_restart_inv cdcl_twl_stgy_restart.intros)
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_entailed_by_init rtranclp_pcdcl_stgy_pcdcl
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' unfolding twl_struct_invs_def by blast
  subgoal for T R n U V W S m
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2[of R S T m n True W W W m \<open>Suc n\<close> True]
    unfolding twl_restart_inv_def
    apply (auto intro: cdcl_twl_stgy_twl_struct_invs
      simp: pcdcl_stgy_restart_pcdcl_stgy_restart_inv cdcl_twl_stgy_restart.intros
      cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_struct_invs
      rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs rtranclp_pcdcl_all_struct_invs
      rtranclp_pcdcl_entailed_by_init pcdcl_restart_entailed_by_init
      intro: pcdcl_restart_entailed_by_init rtranclp_pcdcl_entailed_by_init
      dest: rtranclp_cdcl_twl_subsumption_inp_pcdcl cdcl_twl_restart_pcdcl)
      apply (smt cdcl_twl_restart_pcdcl cdcl_twl_restart_twl_struct_invs
        rtranclp_cdcl_twl_subsumption_inp_pcdcl rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
        rtranclp_pcdcl_entailed_by_init state\<^sub>W_of_def twl_restart_ops.pcdcl_restart_entailed_by_init
        twl_restart_ops.rtranclp_cdcl_twl_stgy_entailed_by_init twl_struct_invs_def)+
      done
  subgoal for T S U R m n
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2[of R S T m n True R U U \<open>Suc m\<close> n True]
    unfolding twl_restart_inv_def
    apply (auto intro: cdcl_twl_stgy_twl_struct_invs
      simp: pcdcl_stgy_restart_pcdcl_stgy_restart_inv cdcl_twl_stgy_restart.intros
      cdcl_twl_restart_only_twl_struct_invs)
      using cdcl_twl_restart_only_cdcl twl_restart_ops.pcdcl_restart_only_entailed_by_init twl_struct_invs_def by blast
  subgoal
    unfolding twl_restart_inv_def pcdcl_stgy_restart_inv_def prod.simps by blast
  done

lemma rtranclp_cdcl_twl_stgy_restart_twl_restart_inv:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_restart_inv T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: cdcl_twl_stgy_restart_twl_restart_inv)

definition twl_stgy_restart_inv :: \<open>'v twl_st_restart \<Rightarrow> bool\<close> where
  \<open>twl_stgy_restart_inv = (\<lambda>(Q, R, S, m, n). twl_stgy_invs Q \<and> twl_stgy_invs R \<and> twl_stgy_invs S)\<close>
lemma cdcl_twl_restart_only_twl_stgy_invs:
  \<open>cdcl_twl_restart_only S T \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  by (auto simp: cdcl_twl_restart_only.simps twl_stgy_invs_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
    dest!: get_all_ann_decomposition_exists_prepend)

lemma cdcl_twl_stgy_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_restart_inv S\<close> and
    \<open>twl_stgy_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst (snd S))\<close> and
    \<open>twl_stgy_invs (fst (snd (snd S)))\<close>and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd S))))\<close>
  shows \<open>twl_stgy_invs (fst T) \<and> twl_stgy_invs (fst (snd T)) \<and> twl_stgy_invs (fst (snd (snd T)))\<close>
  using assms
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal for T U R S m n
    using rtranclp_cdcl_twl_stgy_twl_stgy_invs[of T U]
    by (auto simp: twl_restart_inv_def)
  subgoal for T R n U V W S m
    using cdcl_twl_restart_twl_stgy_invs[of U V]
    by (auto simp: twl_restart_inv_def rtranclp_cdcl_twl_subsumption_inp_twl_stgy_invs
        cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs
        rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
      intro: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs)
  subgoal for T S U R m n
    using cdcl_twl_restart_only_twl_stgy_invs[of T U]
    by (auto simp: twl_restart_inv_def)
  subgoal
    by auto
  done

lemma rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_restart_inv S\<close> and
    \<open>twl_stgy_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst (snd S))\<close> and
    \<open>twl_stgy_invs (fst (snd (snd S)))\<close>
  shows \<open>twl_stgy_invs (fst T) \<and> twl_stgy_invs (fst (snd T)) \<and> twl_stgy_invs (fst (snd (snd T)))\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_twl_stgy_invs[of T U]
      rtranclp_cdcl_twl_stgy_restart_twl_restart_inv[of S T]
    by (auto dest!: simp: twl_restart_inv_def)
  done

lemma cdcl_twl_stgy_restart_twl_stgy_restart_inv:
  \<open>cdcl_twl_stgy_restart S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_stgy_restart_inv S \<Longrightarrow>
  twl_stgy_restart_inv T\<close>
  using cdcl_twl_stgy_restart_twl_stgy_invs[of S T] unfolding twl_stgy_restart_inv_def twl_restart_inv_def
  by auto

lemma rtranclp_cdcl_twl_stgy_restart_twl_stgy_restart_inv:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_stgy_restart_inv S \<Longrightarrow>
  twl_stgy_restart_inv T\<close>
  using rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S T] unfolding twl_stgy_restart_inv_def
  by auto

end


context twl_restart
begin

theorem wf_cdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v twl_st_restart). twl_restart_inv S \<and> cdcl_twl_stgy_restart S T}\<close> (is \<open>wf ?S\<close>)
proof -
  have \<open>?S \<subseteq>
    {((S', T', U', m', n', g'), (S, T, U, m, n, g)).
        pcdcl_stgy_restart_inv (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g) \<and>
        pcdcl_stgy_restart (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g)
           (pstate\<^sub>W_of S', pstate\<^sub>W_of T', pstate\<^sub>W_of U', m', n', g')} \<union>
    {((S', T', U', m', n', g'), (S, T, U, m, n, g)).
        pcdcl_stgy_restart_inv (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g) \<and>
        S = S' \<and> T = T' \<and> m = m' \<and> n = n' \<and> g = g' \<and>
      pstate\<^sub>W_of U = pstate\<^sub>W_of U' \<and> (literals_to_update_measure U', literals_to_update_measure U)
      \<in> lexn less_than 2}\<close> (is \<open>_ \<subseteq> ?A \<union> ?B\<close>)
    by (auto dest!: cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2 simp: twl_restart_inv_def)
  moreover have \<open>wf (?A \<union> ?B)\<close>
    apply (rule wf_union_compatible)
    subgoal
      by (rule wf_subset[OF wf_if_measure_f[OF wf_pcdcl_twl_stgy_restart],
        of _ \<open>\<lambda>(S, T, U, m, g). (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, g)\<close>]) auto
    subgoal
      by (rule wf_subset[OF wf_if_measure_f[OF ],
        of \<open>(lexn less_than 2)\<close>  _ \<open>\<lambda>(S, T, U, m, g). literals_to_update_measure (U)\<close>])
        (auto intro!: wf_lexn)
    subgoal
      by auto
    done
  ultimately show ?thesis
    by (blast intro: wf_subset)
qed

end


context twl_restart_ops
begin

lemma cdcl_twl_stgy_size_get_all_learned:
  \<open>cdcl_twl_stgy S T \<Longrightarrow> size (get_all_learned_clss S) \<le> size (get_all_learned_clss T)\<close>
  by (induction rule: cdcl_twl_stgy.induct)
   (auto simp: cdcl_twl_cp.simps cdcl_twl_o.simps update_clauses.simps
    dest: multi_member_split)

lemma rtranclp_cdcl_twl_stgy_size_get_all_learned:
  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> size (get_all_learned_clss S) \<le> size (get_all_learned_clss T)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: cdcl_twl_stgy_size_get_all_learned)

(*TODO Move*)
lemma (in -) wf_trancl_iff: \<open>wf (r\<^sup>+) \<longleftrightarrow> wf r\<close>
  by (auto intro!: wf_subset[of \<open>r\<^sup>+\<close> r] simp: wf_trancl)

lemma (in -) tranclp_inv_tranclp:
  assumes \<open>\<And>S T. R S T \<Longrightarrow> P S \<Longrightarrow> P T\<close>
  shows
    \<open>{(T, S). R S T \<and> P S}\<^sup>+ = {(T, S). R\<^sup>+\<^sup>+ S T \<and> P S}\<close>
proof -
  have H: \<open>R\<^sup>+\<^sup>+ S T \<Longrightarrow> P S \<Longrightarrow> P T\<close> for S T
    by (induction rule: tranclp_induct)
      (auto dest: assms)
  show ?thesis
    apply (rule; rule; clarify)
    unfolding mem_Collect_eq in_pair_collect_simp
    subgoal for a b
      by (induction rule: trancl_induct) auto
    subgoal for b x
      apply (induction rule: tranclp_induct)
      subgoal for b
        by auto
      subgoal for e f
        by (rule trancl_into_trancl2[of f e])
          (use H[of x e] in auto)
      done
    done
qed

lemma (in -) cdcl_twl_stgy_restart_only_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_restart_only S T\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>twl_stgy_invs T\<close>
  using assms cdcl_twl_restart_only_cdcl[OF assms(1)]
  by (induction rule: cdcl_twl_restart_only.induct)
    (auto simp: twl_stgy_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      cdcl\<^sub>W_restart_mset.no_smaller_confl_def
      clauses_def
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
      dest!: get_all_ann_decomposition_exists_prepend)

definition partial_conclusive_TWL_run :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>partial_conclusive_TWL_run S = SPEC(\<lambda>(b, T). \<exists>R1 R2 m m\<^sub>0 n\<^sub>0.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, S, S, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> (\<not>b \<longrightarrow> final_twl_state T))\<close>

definition partial_conclusive_TWL_run2
  :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close>
where
  \<open>partial_conclusive_TWL_run2  m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 = SPEC(\<lambda>(b, T). \<exists>R1 R2 m.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> (\<not>b \<longrightarrow> final_twl_state T))\<close>

definition conclusive_TWL_run :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_run S = SPEC(\<lambda>T. (\<exists>R1 R2 m m\<^sub>0 n\<^sub>0.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, S, S, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> final_twl_state T))\<close>

definition conclusive_TWL_run2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_run2 m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 = SPEC(\<lambda>T. (\<exists>R1 R2 m.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> final_twl_state T))\<close>
end


end
