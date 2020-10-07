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

end
