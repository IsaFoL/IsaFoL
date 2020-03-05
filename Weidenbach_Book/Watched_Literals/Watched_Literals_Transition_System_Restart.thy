theory Watched_Literals_Transition_System_Restart
  imports Watched_Literals_Transition_System
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


lemma cdcl_twl_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_restart S T\<close> and
    \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using assms
proof (induction rule: cdcl_twl_restart.induct)
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US Q)
  note decomp = this(1) and learned' = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  let ?S' = \<open>(M', N', U', None, NE+ clauses NE', UE + clauses UE', NS, {#}, {#}, {#})\<close>
  have learned: \<open>U' \<subseteq># U\<close>
    using learned' by (rule mset_le_decr_left1)
  have
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    \<open>valid_enqueued ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
      (state\<^sub>W_of ?S)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa
      (state\<^sub>W_of ?S)\<close> and
    \<open>twl_st_exception_inv ?S\<close> and
    no_dup_q: \<open>no_duplicate_queued ?S\<close> and
    dist: \<open>distinct_queued ?S\<close> and
    \<open>confl_cands_enqueued ?S\<close> and
    \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow>
     clauses_to_update ?S = {#} \<and>
     literals_to_update ?S = {#}\<close> and
    unit: \<open>entailed_clss_inv ?S\<close> and
    to_upd: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close> and
    subs: \<open>subsumed_clauses_inv ?S\<close>
    using inv unfolding twl_struct_invs_def by clarify+
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
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
   obtain M3 where
     M: \<open>M = M3 @ M2 @ Decided K # M'\<close>
     using decomp by blast
   define M3' where \<open>M3' = M3 @ M2\<close>
   then have M3': \<open>M = M3' @ Decided K # M'\<close>
     unfolding M by auto
   have entailed_clss_inv: \<open>entailed_clss_inv ?S'\<close>
     unfolding entailed_clss_inv.simps
   proof
     fix C
     assume \<open>C \<in># NE + clauses NE' + (UE + clauses UE')\<close>
     moreover have \<open>L \<in> lits_of_l M \<and> get_level M L = 0 \<Longrightarrow>L \<in> lits_of_l M' \<and> get_level M' L = 0\<close>
       for L
       using n_d
       by (cases \<open>undefined_lit M3' L\<close>)
         (auto simp: M3' atm_of_eq_atm_of get_level_cons_if
           dest: in_lits_of_l_defined_litD split: if_splits)
     ultimately obtain L where
       lev_L: \<open>get_level M' L = 0\<close>
       \<open>L \<in> lits_of_l M'\<close> and
       C: \<open>L \<in># C\<close>
       using unit has_true by auto blast+
     then have \<open>L \<in> lits_of_l M'\<close>
       apply (cases \<open>defined_lit M3' L\<close>)
       using n_d unfolding M3' by (auto simp: get_level_cons_if split: if_splits
           dest: in_lits_of_l_defined_litD)
     moreover have \<open>get_level M' L = 0\<close>
       apply (cases \<open>defined_lit M3' L\<close>)
       using n_d lev_L unfolding M3' by (auto simp: get_level_cons_if split: if_splits
           dest: in_lits_of_l_defined_litD)
     ultimately show \<open>\<exists>L. L \<in># C \<and>
             (None = None \<or> 0 < count_decided M' \<longrightarrow>
              get_level M' L = 0 \<and> L \<in> lits_of_l M')\<close>
       using C by blast
   qed
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

   have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W \<le> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<close>
     using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart by blast

   obtain T' where
     res: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of ?S) T'\<close> and
     res': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T' (state\<^sub>W_of ?S')\<close>
     using cdcl_twl_restart_cdcl\<^sub>W[OF cdcl_twl_restart.restart_trail[OF restart_trail(1-5)] inv]
     by (auto simp: ac_simps N)
   then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of ?S)
       (state\<^sub>W_of ?S')\<close>
     using rtranclp_mono[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart]
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart
     by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros)
   from cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF this struct_inv]
   have struct_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (M', N', U', None, NE+ clauses NE',
         UE+ clauses UE', NS, {#}, {#}, {#}))\<close>
     by (auto simp: ac_simps N)
   have smaller':
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M', N', U', None, NE+ clauses NE',
       UE+ clauses UE', NS, {#}, {#}, {#}))\<close>
     using smaller mset_subset_eqD[OF learned']
     apply (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def M3' cdcl\<^sub>W_restart_mset_state
         clauses_def ac_simps N) (* TODO Proof *)
     apply (metis Cons_eq_appendI append_assoc image_eqI)
     apply (metis Cons_eq_appendI append_assoc image_eqI)
     done
  have subsumed: \<open>subsumed_clauses_inv
     (M', N', U', None, NE + clauses NE', UE + clauses UE', NS, {#}, {#},
      {#})\<close>
    using subs N by (auto dest!: multi_member_split)

   show ?case
    unfolding twl_struct_invs_def
    apply (intro conjI)
    subgoal using twl_st_inv_subsumed_mono[OF _ twl_st_inv_mono[OF learned NN' twl_st_inv']]
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
    subgoal by (rule entailed_clss_inv)
    subgoal by (rule clss_to_upd)
    subgoal by (rule past_invs)
    subgoal by (rule subsumed)
    done
next
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US Q)
  note learned' = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and invs = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  let ?T = \<open>(M, N', U', None, NE+clauses NE', UE +clauses UE', NS, US', {#}, Q)\<close>
  have learned: \<open>U' \<subseteq># U\<close>
    using learned' by (rule mset_le_decr_left1)
  have
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    valid: \<open>valid_enqueued ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
      (state\<^sub>W_of ?S)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa
      (state\<^sub>W_of ?S)\<close> and
    excp_inv: \<open>twl_st_exception_inv ?S\<close> and
    no_dup_q: \<open>no_duplicate_queued ?S\<close> and
    dist: \<open>distinct_queued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close> and
    propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow>
     clauses_to_update ?S = {#} \<and>
     literals_to_update ?S = {#}\<close> and
    unit: \<open>entailed_clss_inv ?S\<close> and
    to_upd: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close> and
    subs: \<open>subsumed_clauses_inv ?S\<close>
    using invs unfolding twl_struct_invs_def by clarify+
   have learned: \<open>U' \<subseteq># U\<close>
    using learned by auto
   have n_d: \<open>no_dup M\<close>
     using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
   have valid': \<open>valid_enqueued ?T\<close>
     using valid by auto
   have entailed_clss_inv: \<open>entailed_clss_inv ?T\<close>
     unfolding entailed_clss_inv.simps
   proof
     fix C
     assume \<open>C \<in># NE + clauses NE' + (UE + clauses UE')\<close>
     then obtain L where
       lev_L: \<open>get_level M L = 0\<close>
       \<open>L \<in> lits_of_l M\<close> and
       C: \<open>L \<in># C\<close>
       using unit has_true by auto
     then show \<open>\<exists>L. L \<in># C \<and>
             (None = None \<or> 0 < count_decided M \<longrightarrow>
              get_level M L = 0 \<and> L \<in> lits_of_l M)\<close>
       using C by blast
   qed
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

   have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W \<le> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<close>
     using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart by blast

   have clss_to_upd: \<open>clauses_to_update_inv ?T\<close>
     using to_upd learned by (auto simp add: filter_mset_empty_conv N ac_simps)
   obtain T' where
     res: \<open>cdcl\<^sub>W_restart_mset.restart (state\<^sub>W_of ?S) T'\<close> and
     res': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T' (state\<^sub>W_of ?T)\<close>
     using cdcl_twl_restart_cdcl\<^sub>W[OF cdcl_twl_restart.restart_clauses[OF restart_clauses(1-4)] invs,
       of US'] US
     by (auto simp: ac_simps N)
   then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state\<^sub>W_of ?S)
       (state\<^sub>W_of ?T)\<close>
     using rtranclp_mono[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart]
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart
     by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros)
   from cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF this struct_inv]
   have struct_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
     .

   have smaller':
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?T)\<close>
     using smaller mset_subset_eqD[OF learned'] US
     by (auto 7 5 simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
         clauses_def N ac_simps split: if_splits)

   have subsumed: \<open>subsumed_clauses_inv ?T\<close>
    using subs US N by (auto dest!: multi_member_split split: if_splits)

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
    subgoal by (rule entailed_clss_inv)
    subgoal by (rule clss_to_upd)
    subgoal by (rule past_invs)
    subgoal by (rule subsumed)
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


context twl_restart_ops
begin

inductive cdcl_twl_stgy_restart :: \<open>'v twl_st \<times> nat \<Rightarrow> 'v twl_st \<times> nat \<Rightarrow> bool\<close> where
restart_step:
  \<open>cdcl_twl_stgy_restart (S, n) (U, Suc n)\<close>
  if
    \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (get_learned_clss T) > f n\<close> and
    \<open>cdcl_twl_restart T U\<close> |
restart_full:
 \<open>cdcl_twl_stgy_restart (S, n) (T, n)\<close>
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
    (auto simp add: full1_def dest!: tranclp_into_rtranclp
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

lemma (in -) learned_clss_get_all_learned_clss[simp]:
   \<open>learned_clss (state\<^sub>W_of S) = get_all_learned_clss S\<close>
  by (cases S) (auto simp: learned_clss.simps)

lemma cdcl_twl_stgy_restart_new_learned_in_all_simple_clss:
  assumes
    st: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* R S\<close> and
    invR: \<open>twl_struct_invs (fst R)\<close>
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
    using res by (auto simp: cdcl_twl_restart.simps
        dest!: image_mset_subseteq_mono[of _ _ clause]
        intro: mset_le_incr_right1
        split: if_splits)
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

end


context twl_restart
begin

theorem wf_cdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v twl_st \<times> nat). twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v twl_st \<times> nat\<close> where
    g: \<open>\<And>i. cdcl_twl_stgy_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. twl_struct_invs (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast

  have H: False if \<open>no_step cdcl_twl_stgy (fst (g i))\<close> for i
    using g[of i] that
    unfolding cdcl_twl_stgy_restart.simps
    by (auto simp: full1_def tranclp_unfold_begin)

  have snd_g: \<open>snd (g i) = i + snd (g 0)\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal for i
      using g[of i] H[of \<open>Suc i\<close>] by (auto simp: cdcl_twl_stgy_restart.simps full1_def)
    done
  then have snd_g_0: \<open>\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)\<close>
    by blast
  have unbounded_f_g: \<open>unbounded (\<lambda>i. f (snd (g i)))\<close>
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
        not_bounded_nat_exists_larger not_le le_iff_add)

  have \<open>\<exists>h. cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (h) \<and>
         size (get_all_learned_clss (h)) > f (snd (g i)) \<and>
         cdcl_twl_restart (h) (fst (g (i+1)))\<close>
    for i
    using g[of i] H[of \<open>Suc i\<close>]
    unfolding cdcl_twl_stgy_restart.simps full1_def Suc_eq_plus1[symmetric]
    by force
  then obtain h :: \<open>nat \<Rightarrow> 'v twl_st\<close> where
    cdcl_twl: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (h i)\<close> and
    size_h_g: \<open>size (get_all_learned_clss (h i)) > f (snd (g i))\<close> and
    res: \<open>cdcl_twl_restart (h i) (fst (g (i+1)))\<close> for i
    by metis

  obtain k where
    f_g_k: \<open>f (snd (g k)) >
       card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h 0))))) +
           size (get_all_learned_clss (fst (g 0)))\<close>
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
      unfolding learned_clss_get_all_learned_clss by auto
    done
  have dist_diff: \<open>distinct_mset (c + (Ca + C) - ai) \<Longrightarrow>
       distinct_mset (c - ai)\<close> for c Ca C ai
    by (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute
        distinct_mset_minus)

  have \<open>get_all_learned_clss (fst (g (Suc i))) \<subseteq># get_all_learned_clss (h i)\<close> for i
    using res[of i] by (auto simp: cdcl_twl_restart.simps
        dest!: image_mset_subseteq_mono[of _ _ clause]
        intro: mset_le_incr_right1
        split: if_splits)

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
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_new_learned_in_all_simple_clss[of \<open>state\<^sub>W_of (fst (g i))\<close>])
    subgoal by (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[OF cdcl_twl]) (rule inv)
    subgoal using inv[of i]  unfolding twl_struct_invs_def by fast
    done
  have incl: \<open>set_mset (get_all_learned_clss (h i)) \<subseteq>
         simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close>  (is \<open>set_mset (?V i) \<subseteq> _\<close>) for i
    using incl[of i] by (cases \<open>h i\<close>) (auto dest: in_diffD)

  have incl_init: \<open>set_mset (?U i) \<subseteq> simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close> for i
    using incl[of i] by (auto dest: in_diffD)
  have size_U_atms: \<open>size (?U i) \<le> card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i)))))\<close> for i
    apply (subst distinct_mset_size_eq_card[OF dist_h])
    apply (rule card_mono[OF _ incl_init])
    by (auto simp: simple_clss_finite)
  have S:
    \<open>size (?V i) - size (get_all_learned_clss (fst (g 0))) \<le>
      card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i)))))\<close> for i
    apply (rule order.trans)
     apply (rule diff_size_le_size_Diff)
    apply (rule size_U_atms)
    done
  have S:
    \<open>size (?V i) \<le>
      card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))) +
       size (get_all_learned_clss (fst (g 0)))\<close> for i
    using S[of i] by auto

  have H: \<open>card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h k))))) +
         size (get_all_learned_clss (fst (g 0))) > f (k + snd (g 0))\<close> for k
    using S[of k] size_h_g[of k] unfolding snd_g[symmetric]
    by force

  show False
    using H[of k] f_g_k unfolding snd_g[symmetric]
    unfolding K
    by linarith
qed

end

abbreviation state\<^sub>W_of_restart where
  \<open>state\<^sub>W_of_restart \<equiv> (\<lambda>(S, n). (state\<^sub>W_of S, n))\<close>

context twl_restart_ops
begin

lemma rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S, n) (state\<^sub>W_of T, n)\<close>
  using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[of S T]
  by (auto dest: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart
     cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy)

lemma cdcl_twl_stgy_restart_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl_twl_stgy_restart S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>  twl_stgy_invs (fst S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of_restart S) (state\<^sub>W_of_restart T)\<close>
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal for S T n U
    using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_restart_stgy[of S T n]
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy.intros [of \<open>state\<^sub>W_of_restart(T, n)\<close>
        \<open>(_, Suc n)\<close>]
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy[of \<open>_\<close>
        \<open>state\<^sub>W_of U\<close> \<open>Suc n\<close>]
       cdcl_twl_restart_cdcl\<^sub>W_stgy[of T U]
       rtranclp_cdcl_twl_stgy_twl_struct_invs[of S T]
       rtranclp_cdcl_twl_stgy_twl_stgy_invs[of S T]
    apply (auto dest!: tranclp_into_rtranclp)
    by (meson r_into_rtranclp rtranclp_trans)
  subgoal for S T n
    using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_restart_stgy[of S T n]
       rtranclp_cdcl_twl_stgy_twl_struct_invs[of S T]
       rtranclp_cdcl_twl_stgy_twl_stgy_invs[of S T]
    by (auto dest!: tranclp_into_rtranclp simp: full1_def)
  done

lemma rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst S)\<close>
  shows \<open>twl_stgy_invs (fst T)\<close>
  using assms
  by (induction rule: rtranclp_induct)
    (auto intro: cdcl_twl_stgy_restart_twl_stgy_invs
        rtranclp_cdcl_twl_stgy_restart_twl_struct_invs)

lemma rtranclp_cdcl_twl_stgy_restart_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>  twl_stgy_invs (fst S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of_restart S) (state\<^sub>W_of_restart T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of S T]
       rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S T]
       cdcl_twl_stgy_restart_cdcl\<^sub>W_restart_stgy[of T U]
    by (auto dest!: tranclp_into_rtranclp)
  done



definition (in twl_restart_ops) cdcl_twl_stgy_restart_with_leftovers where
  \<open>cdcl_twl_stgy_restart_with_leftovers S U \<longleftrightarrow>
     (\<exists>T. cdcl_twl_stgy_restart\<^sup>*\<^sup>* S (T, snd U) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* T (fst U))\<close>

lemma cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart:
  \<open>cdcl_twl_stgy_restart (T, m) (V, Suc m) \<Longrightarrow>
       cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_twl_stgy_restart (S, m) (V, Suc m)\<close>
  by (subst (asm) cdcl_twl_stgy_restart.simps)
   (auto simp: intro: cdcl_twl_stgy_restart.intros
      dest: rtranclp_tranclp_tranclp)

lemma cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2:
  \<open>cdcl_twl_stgy_restart (T, m) (V, m) \<Longrightarrow>
       cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_twl_stgy_restart (S, m) (V, m)\<close>
  by (subst (asm) cdcl_twl_stgy_restart.simps)
    (auto simp: intro: cdcl_twl_stgy_restart.intros
      dest: rtranclp_tranclp_tranclp rtranclp_full1I)


definition cdcl_twl_stgy_restart_with_leftovers1 where
  \<open>cdcl_twl_stgy_restart_with_leftovers1 S U \<longleftrightarrow>
     cdcl_twl_stgy_restart S U \<or>
     (cdcl_twl_stgy\<^sup>+\<^sup>+ (fst S) (fst U) \<and> snd S = snd U)\<close>

lemma (in twl_restart) wf_cdcl_twl_stgy_restart_with_leftovers1:
  \<open>wf {(T :: 'v twl_st \<times> nat, S).
        twl_struct_invs (fst S) \<and> cdcl_twl_stgy_restart_with_leftovers1 S T}\<close>
  (is \<open>wf ?S\<close>)
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v twl_st \<times> nat\<close> where
    g: \<open>\<And>i. cdcl_twl_stgy_restart_with_leftovers1 (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. twl_struct_invs (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast
  have ns: \<open>\<not>no_step cdcl_twl_stgy (fst (g i))\<close> for i
    using g[of i]
    by (fastforce simp: cdcl_twl_stgy_restart_with_leftovers1_def
        cdcl_twl_stgy_restart.simps full1_def tranclp_unfold_begin)

  define h where
    \<open>h \<equiv> rec_nat (g 0) (\<lambda>i Si. g (SOME k. cdcl_twl_stgy_restart Si (g k)))\<close>
  have [simp]: \<open>h 0 = g 0\<close>
    unfolding h_def by auto

  have L: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (fst (g (Suc (i + k)))) \<and>
         cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g (i + k))) (fst (g (Suc (i + k)))) \<and>
         snd (g (Suc (i + k))) = snd (g i)\<close>
    if \<open>k < j\<close> and
      H: \<open>\<And>k. k \<le> j \<Longrightarrow> \<not>cdcl_twl_stgy_restart (g i) (g (Suc i + k))\<close>
    for k i j
    using that
  proof (induction j arbitrary: k)
    case 0
    then show ?case by auto
  next
    case (Suc j k)
    then have
      IH: \<open>\<And>k. k < j \<Longrightarrow>
         cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (fst (g (Suc (i + k)))) \<and>
         cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g (i + k))) (fst (g (Suc (i + k)))) \<and>
         snd (g (Suc (i + k))) = snd (g i)\<close> and
      \<open>k < Suc j\<close> and
      H: \<open>\<And>k. k \<le> Suc j \<Longrightarrow> \<not> cdcl_twl_stgy_restart (g i) (g (Suc i + k))\<close>
      by auto
    show ?case
    proof (cases \<open>k = j\<close>)
      case False
      then show ?thesis
        using IH[of k] \<open>k < Suc j\<close> by simp
    next
      case [simp]: True
      consider
        (res) \<open>cdcl_twl_stgy_restart (g ( (i+k))) (g ((Suc (i+k))))\<close> |
        (stgy) \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g ((i+k)))) (fst (g ((Suc (i+k)))))\<close> and
        \<open>snd (g (Suc (i + k))) = snd (g (i + k))\<close>
        using g[of \<open>i+k\<close>] unfolding cdcl_twl_stgy_restart_with_leftovers1_def
        by auto
      then show ?thesis
      proof cases
        case stgy
        then show ?thesis
          using IH[of \<open>k - 1\<close>]
          by (cases \<open>0 < j\<close>) auto
      next
        case res
        have Sucg: \<open>Suc (snd (g ((i + k)))) = snd (g (Suc ((i + k))))\<close>
          using res
            ns[of \<open>Suc ((i + k))\<close>]
          by (auto simp: cdcl_twl_stgy_restart.simps full1_def)

        have \<open>cdcl_twl_stgy_restart (g i) (g (Suc (i + k)))\<close>
          using IH[of \<open>k - 1\<close>]
            res cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart[ of \<open>fst (g ((i + k)))\<close>
              \<open>snd (g ((i + k)))\<close> \<open>fst (g (Suc ((i + k))))\<close> \<open>fst (g i)\<close>]
          unfolding Sucg prod.collapse
          by (cases \<open>0 < j\<close>) (auto intro!: cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart
              dest!: tranclp_into_rtranclp)
        then show ?thesis
          using H[of k] \<open>k < Suc j\<close>
          by auto
      qed
    qed
  qed
  have Ex_cdcl_twl_stgy_restart: \<open>\<exists>k > i. cdcl_twl_stgy_restart (g i) (g k)\<close> for i
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have H: \<open>\<And>k. k > i \<Longrightarrow> \<not>cdcl_twl_stgy_restart (g i) (g k)\<close>
      by fast

    define g' where
      \<open>g' = (\<lambda>k. fst (g (k + i)))\<close>
    have L: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g i)) (fst (g (Suc (i + k)))) \<and>
         cdcl_twl_stgy\<^sup>+\<^sup>+ (fst (g (i + k))) (fst (g (Suc (i + k)))) \<and>
         snd (g (Suc (i + k))) = snd (g i)\<close>
      for k
      using L[of k \<open>k+1\<close> i] H[of \<open>Suc i+_\<close>]
      by auto
    have \<open>(g' (Suc k), g' k) \<in> {(T, S). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T}\<close> for k
      using L[of k] inv
      unfolding g'_def
      by (auto simp: ac_simps)
    then show False
      using tranclp_wf_cdcl_twl_stgy
      unfolding wf_iff_no_infinite_down_chain
      by fast
  qed
  have h_Suc: \<open>h (Suc i) = g (SOME j. cdcl_twl_stgy_restart (h i) (g j))\<close> for i
    unfolding h_def by auto
  have h_g: \<open>\<exists>j. h i = g j\<close> for i
  proof (induction i)
    case 0
    then show ?case by auto
  next
    case (Suc i)
    then obtain i' where
      i': \<open>h i = g i'\<close>
      by blast
    define j where \<open>j \<equiv> SOME j. cdcl_twl_stgy_restart (h i) (g j)\<close>
    obtain k where
      k: \<open>k > i'\<close> and
      i_k: \<open>cdcl_twl_stgy_restart (g i') (g k)\<close>
      using Ex_cdcl_twl_stgy_restart[of i'] by blast
    have \<open>cdcl_twl_stgy_restart (h i) (g j)\<close>
      unfolding j_def
      apply (rule someI[of \<open>\<lambda>S. cdcl_twl_stgy_restart (h i) (g S)\<close>])
      using k i_k unfolding i' by fast
    then show ?case
      unfolding h_Suc by auto
  qed

  have \<open>cdcl_twl_stgy_restart (h i) (h (Suc i))\<close> for i
  proof -
    obtain i' where
       h_g_i: \<open>h i = g i'\<close>
      using h_g by fast
    define j where \<open>j \<equiv> SOME j. cdcl_twl_stgy_restart (h i) (g j)\<close>
    obtain k where
      k: \<open>k > i'\<close> and
      i_k: \<open>cdcl_twl_stgy_restart (g i') (g k)\<close>
      using Ex_cdcl_twl_stgy_restart[of i'] by blast
    have \<open>cdcl_twl_stgy_restart (h i) (g j)\<close>
      unfolding j_def
      apply (rule someI[of _ k])
      using k i_k unfolding h_g_i by fast
    then show ?thesis
      unfolding h_Suc j_def[symmetric] .
  qed
  moreover have \<open>\<And>i. twl_struct_invs (fst (h i))\<close>
    using inv h_g by metis
  ultimately show False
    using wf_cdcl_twl_stgy_restart
    unfolding wf_iff_no_infinite_down_chain by fast
qed


lemma (in twl_restart) wf_cdcl_twl_stgy_restart_measure:
   \<open>wf ({((brkT, T, n), brkS, S, m).
         twl_struct_invs S \<and> cdcl_twl_stgy_restart_with_leftovers1 (S, m) (T, n)} \<union>
        {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS})\<close>
  (is \<open>wf (?TWL \<union> ?BOOL)\<close>)
proof (rule wf_union_compatible)
  show \<open>wf ?TWL\<close>
    apply (rule wf_subset)
     apply (rule wf_snd_wf_pair[OF wf_cdcl_twl_stgy_restart_with_leftovers1])
    by auto
  show \<open>?TWL O ?BOOL \<subseteq> ?TWL\<close>
    by auto

  show \<open>wf ?BOOL\<close>
    unfolding wf_iff_no_infinite_down_chain
  proof clarify
    fix f :: \<open>nat \<Rightarrow> bool \<times> 'b\<close>
    assume H: \<open>\<forall>i. (f (Suc i), f i) \<in> {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>
    then have \<open>(f (Suc 0), f 0) \<in> {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close> and
      \<open>(f (Suc 1), f 1) \<in> {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>
      by presburger+
    then show False
      by auto
  qed
qed

lemma (in twl_restart) wf_cdcl_twl_stgy_restart_measure_early:
   \<open>wf ({((ebrk, brkT, T, n), ebrk, brkS, S, m).
         twl_struct_invs S \<and> cdcl_twl_stgy_restart_with_leftovers1 (S, m) (T, n)} \<union>
        {((ebrkT, brkT, T), (ebrkS, brkS, S)). S = T \<and> (ebrkT \<or> brkT) \<and> (\<not>brkS \<and> \<not>ebrkS)})\<close>
  (is \<open>wf (?TWL \<union> ?BOOL)\<close>)
proof (rule wf_union_compatible)
  show \<open>wf ?TWL\<close>
    apply (rule wf_subset)
    apply (rule wf_snd_wf_pair)
     apply (rule wf_snd_wf_pair[OF wf_cdcl_twl_stgy_restart_with_leftovers1])
    by auto
  show \<open>?TWL O ?BOOL \<subseteq> ?TWL\<close>
    by auto

  show \<open>wf ?BOOL\<close>
    unfolding wf_iff_no_infinite_down_chain
  proof clarify
    fix f :: \<open>nat \<Rightarrow> bool \<times> bool \<times> _\<close>
    assume H: \<open>\<forall>i. (f (Suc i), f i) \<in> ?BOOL\<close>
    then have \<open>(f (Suc 0), f 0) \<in> ?BOOL\<close> and
      \<open>(f (Suc 1), f 1) \<in> ?BOOL\<close>
      by presburger+
    then show False
      by auto
  qed
qed


lemma cdcl_twl_stgy_restart_with_leftovers_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl_twl_stgy_restart_with_leftovers S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>  twl_stgy_invs (fst S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of_restart S) (state\<^sub>W_of_restart T)\<close>
  unfolding cdcl_twl_stgy_restart_with_leftovers_def
  apply (rule exE)
   apply assumption
  subgoal for S'
    using
      rtranclp_cdcl_twl_stgy_restart_cdcl\<^sub>W_restart_stgy[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_restart_stgy[of S' \<open>fst T\<close> \<open>snd T\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S \<open>(S', snd T)\<close>]
      by (cases T) auto
  done

lemma cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs:
  \<open>cdcl_twl_stgy_restart_with_leftovers S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>
    twl_struct_invs (fst T)\<close>
  unfolding cdcl_twl_stgy_restart_with_leftovers_def
  apply (rule exE)
   apply assumption
  subgoal for S'
    using
      rtranclp_cdcl_twl_stgy_twl_struct_invs[of \<open>S'\<close> \<open>(fst T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_cdcl\<^sub>W_restart_stgy[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_restart_stgy[of S' \<open>fst T\<close> \<open>snd T\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S \<open>(S', snd T)\<close>]
    by auto
  done

lemma rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs:
  \<open>cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>
    twl_struct_invs (fst T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs[of T U]
    by auto
  done

lemma cdcl_twl_stgy_restart_with_leftovers_twl_stgy_invs:
  \<open>cdcl_twl_stgy_restart_with_leftovers S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>
    twl_stgy_invs (fst S) \<Longrightarrow> twl_stgy_invs (fst T)\<close>
  unfolding cdcl_twl_stgy_restart_with_leftovers_def
  apply (rule exE)
  apply assumption
  subgoal for S'
    using
      rtranclp_cdcl_twl_stgy_twl_struct_invs[of \<open>S'\<close> \<open>(fst T)\<close>]
      rtranclp_cdcl_twl_stgy_twl_stgy_invs[of \<open>S'\<close> \<open>(fst T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_cdcl\<^sub>W_restart_stgy[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_restart_stgy[of S' \<open>fst T\<close> \<open>snd T\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of S \<open>(S', snd T)\<close>]
      rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S \<open>(S', snd T)\<close>]
    by auto
  done

lemma rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_stgy_invs:
  \<open>cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow>
    twl_stgy_invs (fst S) \<Longrightarrow> twl_stgy_invs (fst T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_with_leftovers_twl_stgy_invs[of T U]
      rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs[of S T]
    by auto
  done

lemma rtranclp_cdcl_twl_stgy_restart_with_leftovers_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs (fst S) \<Longrightarrow> twl_stgy_invs (fst S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of_restart S) (state\<^sub>W_of_restart T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_with_leftovers_cdcl\<^sub>W_restart_stgy[of T U]
    rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs[of S T]
    rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_stgy_invs[of S T]
    by auto
  done

end

end
