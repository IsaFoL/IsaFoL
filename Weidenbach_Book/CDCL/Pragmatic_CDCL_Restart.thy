theory Pragmatic_CDCL_Restart
imports Pragmatic_CDCL
begin

section \<open>Restarts\<close>
text \<open>

  While refactoring the code (or more precisely, creating the PCDCL version with restarts), I
  realised that the restarts as specified in my thesis are not exactly as I want to have them and
  not how they are implemented in SAT solvers. The problem is that I introduced both restart and
  garbage collection at the same time, but they have a different termination criterion:

    \<^item> Restarts are always applicable as long you have learned at least one clause since the last
    restart.
    \<^item> GC must be applied after longer and longer time intervals.


  In the version from the thesis, I use the second criterion to justify termination for both
  criteria. Due to the implementation, it did not really make a difference for small number of
  conflicts, but limited the ability to restart after many conflicts have been generated. I don't
  know if performance will change, as I already observed that changing the restart heuristic can
  have dramatic effects, but fixing it is always better, because it only gives more freedom to
  the implementation (including to not change anything).

  The first criterion does not allow deleting clauses (including the useless US component as I did
  previously). The termination in both cases comes from non-relearning of clauses.

  The proofs changed dramatically (and become much more messy) but that was expected, because the
  base calculus has changed a lot (new clauses can be learned).

  Another difference is that after restarting, I allow anything following a CDCL run to
  happen. Proving that this terminates is delayed to the concrete implementation (e.g., vivification
  or HBR) and does not matter of the overall termination proof (but is obviously important in
  when generating code!).

\<close>
inductive pcdcl_restart :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
restart_trail:
   \<open>pcdcl_restart (M, N, U, None, NE, UE, NS, US)
        (M', N', U', None, NE + NE', UE + UE', NS, {#})\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#E. L \<in> lits_of_l M' \<and> get_level M' L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M' \<longrightarrow> E \<in># (N + U') + NE + UE + UE'\<close> |
restart_clauses:
   \<open>pcdcl_restart (M, N, U, None, NE, UE, NS, US)
      (M, N', U', None, NE + NE', UE + UE', NS, US')\<close>
  if
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#E. L \<in> lits_of_l M \<and> get_level M L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M \<longrightarrow> E \<in># (N + U') + NE + UE + UE'\<close>
    \<open>US' = {#}\<close>


inductive pcdcl_restart_only :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
restart_trail:
   \<open>pcdcl_restart_only (M, N, U, None, NE, UE, NS, US)
        (M', N, U, None, NE, UE, NS, US)\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<or> M = M'\<close>


(*TODO Taken from Misc*)
lemma mset_le_incr_right1: "a\<subseteq>#(b::'a multiset) \<Longrightarrow> a\<subseteq>#b+c" using mset_subset_eq_mono_add[of a b "{#}" c, simplified] .

lemma pcdcl_restart_cdcl\<^sub>W_stgy:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T (state_of V) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of S) (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart.induct)
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US)
  note decomp = this(1) and learned = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6) and stgy_invs = this(7) and
    smaller_propa = this(8)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS,  U' + UE + UE', None)\<close>
  let ?V = \<open>(M', N, U', None, NE, UE + UE', NS, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def
          intro: mset_le_incr_right1)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding  pcdcl_all_struct_invs_def by auto

  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M, N + NE + NS,
        U' + UE + UE', None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE + NS\<close>
          \<open>U+UE+US\<close> _
          \<open>U' + UE + UE'\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs by simp
    subgoal using smaller_propa by simp
    subgoal using kept unfolding drop_M_M' by (auto simp add: ac_simps)
    subgoal using learned by (auto intro: mset_le_incr_right1)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of ?S) (state_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart unfolding N state_of.simps image_mset_union add.assoc state_of.simps
      add.commute[of \<open>NE'\<close>]
    by fast
next
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US)
  note learned = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and inv = this(6) and stgy_invs = this(7) and  smaller_propa = this(8)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US) :: 'v prag_st\<close>
  let ?T = \<open>([], N + NE + NS, U' + UE + UE' + US', None)\<close>
  let ?V = \<open>(M, N, U', None, NE, UE + UE', NS, US') :: 'v prag_st\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned US
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1
        split: if_splits)

  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding pcdcl_all_struct_invs_def by auto

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M) M, N + NE+NS,
        U' + UE+ UE'+US', None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE+NS\<close>
           \<open>U+UE+US\<close> _
          \<open>U' + UE + UE'+US'\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs by simp
    subgoal using smaller_propa by simp
    subgoal using kept by (auto simp add: ac_simps)
    subgoal using learned US
      by (auto
        intro: mset_le_incr_right1
        split: if_splits)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    by (simp add: ac_simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of ?S) (state_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart unfolding N state_of.simps image_mset_union add.assoc add.commute[of \<open>NE'\<close>]
    by fast
qed

lemma pcdcl_restart_cdcl\<^sub>W:
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart.induct)
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US)
  note decomp = this(1) and learned = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS, U' + UE + UE', None)\<close>
  let ?V = \<open>(M', N, U', None, NE, UE + UE', NS, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by auto
  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M,  N + NE + NS,
          U' + UE+ UE', None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
      \<open>N + NE + NS\<close> \<open>U+UE+US\<close> _
          \<open>U' + UE + UE'\<close>])
    subgoal using struct_invs by simp
    subgoal using kept unfolding drop_M_M' by (auto simp add: ac_simps)
    subgoal using learned
      by (auto
        intro: mset_le_incr_right1)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  then show ?case
    using restart by (auto simp: ac_simps N)
next
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US)
  note learned = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE,NS, US)\<close>
  let ?T = \<open>([], N + NE + NS, U' + UE + UE' + US', None)\<close>
  let ?V = \<open>(M, N, U', None, NE, UE + UE', NS, US')\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned US
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1 split: if_splits)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by fast+
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M) M, N + NE + NS,
          U' + UE+ UE' + US', None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
          \<open>N + NE + NS\<close> \<open>U+ UE + US\<close> _
          \<open>U' + UE+ UE' + US'\<close>])
    subgoal using struct_invs by simp
    subgoal using kept by (auto simp add: ac_simps)
    subgoal
     using learned US by (auto
        intro: mset_le_incr_right1 split: if_splits)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    by (simp add: ac_simps)
  then show ?case
    using restart by (auto simp: ac_simps N)
qed

lemma (in -) pcdcl_restart_pcdcl_all_struct_invs:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows 
    \<open>pcdcl_all_struct_invs V\<close>
  using assms pcdcl_restart_cdcl\<^sub>W[OF assms(1,2)] apply -
  apply normalize_goal+
  subgoal for T
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of \<open>state_of S\<close> \<open>state_of V\<close>]
        cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart[of T \<open>state_of V\<close>]
        cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart
       converse_rtranclp_into_rtranclp[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart \<open>state_of S\<close> T \<open>state_of V\<close>] apply -
    apply (cases rule: pcdcl_restart.cases, assumption)
    subgoal
      using get_all_ann_decomposition_lvl0_still[of _ _ _ \<open>pget_trail S\<close>]
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def dest!: multi_member_split)
    subgoal
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def dest!: multi_member_split)
    done
  done
lemma (in conflict_driven_clause_learning_with_adding_init_clause\<^sub>W) restart_no_smaller_propa:
  \<open>restart S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  by (induction rule: restart.induct)
   (auto simp: restart.simps no_smaller_propa_def state_prop)

text \<open>The next theorem does not use the existence of the decomposition to prove
a much stronger version.\<close>
lemma (in -) pcdcl_restart_no_smaller_propa:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows 
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of V)\<close>
  using assms pcdcl_restart_cdcl\<^sub>W_stgy[OF assms(1,2,3,4)]
    pcdcl_restart_pcdcl_all_struct_invs[OF assms(1,2)] apply -
  apply normalize_goal+
	subgoal for T
    using cdcl\<^sub>W_restart_mset.restart_no_smaller_propa[of \<open>state_of S\<close> T]
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa[of T \<open>state_of V\<close>]
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv[of \<open>state_of S\<close> T,
      OF cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.rf,
      OF cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart]
    by (auto simp: pcdcl_all_struct_invs_def)
  done



lemma pcdcl_restart_no_smaller_propa':
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows 
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of V)\<close>
  using assms
  by (induction rule: pcdcl_restart.induct)
   (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
      dest!: get_all_ann_decomposition_exists_prepend)

lemma pcdcl_restart_only_cdcl\<^sub>W_stgy:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart_only S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T (state_of V) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of S) (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart_only.induct)
  case (restart_trail K M' M2 M N U NE UE NS US)
  note decomp = this(1) and inv = this(2) and stgy_invs = this(3) and
    smaller_propa = this(4)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS,  U + UE + US, None)\<close>
  let ?V = \<open>(M', N, U, None, NE, UE, NS, US)\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have reas: \<open>cdcl\<^sub>W_restart_mset.reasons_in_clauses (state_of ?S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def pcdcl_all_struct_invs_def
      by auto
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding  pcdcl_all_struct_invs_def by auto

  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M, N + NE + NS, U + UE + US, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE + NS\<close>
          \<open>U+UE+US\<close> _
          \<open>U+UE+US\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs by simp
    subgoal using smaller_propa by simp
    subgoal using reas unfolding cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
      by (auto simp: clauses_def get_all_mark_of_propagated_alt_def dest!: in_set_dropD)
    subgoal by auto
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of ?S) (state_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart unfolding state_of.simps image_mset_union add.assoc state_of.simps
      add.commute[of \<open>NE'\<close>]
    by fast
qed

lemma pcdcl_restart_only_cdcl\<^sub>W:
  assumes
    \<open>pcdcl_restart_only S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart_only.induct)
  case (restart_trail K M' M2 M N U NE UE NS US)
  note decomp = this(1) and inv = this(2)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS, U + UE + US, None)\<close>
  let ?V = \<open>(M', N, U, None, NE, UE + US, NS, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by auto
  then have reas: \<open>cdcl\<^sub>W_restart_mset.reasons_in_clauses (state_of ?S)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      by auto
  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M,  N + NE + NS,
          U + UE+ US, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
      \<open>N + NE + NS\<close> \<open>U+UE+US\<close> _
          \<open>U + UE + US\<close>])
    subgoal using struct_invs by simp
    subgoal using reas unfolding cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
      by (auto simp: clauses_def get_all_mark_of_propagated_alt_def dest!: in_set_dropD)
    subgoal by (auto intro: mset_le_incr_right1)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  then show ?case
    using restart by (auto simp: ac_simps)
qed

lemma pcdcl_restart_only_pcdcl_all_struct_invs:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart_only S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows 
    \<open>pcdcl_all_struct_invs V\<close>
  using assms pcdcl_restart_only_cdcl\<^sub>W[OF assms] apply -
  apply normalize_goal+
  subgoal for T
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of \<open>state_of S\<close> \<open>state_of V\<close>]
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart[of T \<open>state_of V\<close>]
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart
      converse_rtranclp_into_rtranclp[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart \<open>state_of S\<close> T \<open>state_of V\<close>] apply -
    apply (cases rule: pcdcl_restart_only.cases, assumption)
    subgoal
      using get_all_ann_decomposition_lvl0_still[of _ _ _ \<open>pget_trail S\<close>]
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def dest!: multi_member_split)
    done
  done

definition pcdcl_final_state :: \<open>'v prag_st \<Rightarrow> bool\<close> where
  \<open>pcdcl_final_state S \<longleftrightarrow> no_step pcdcl_core S \<or>
     (count_decided (pget_trail S) = 0 \<and> pget_conflict S \<noteq> None)\<close>

context twl_restart_ops
begin
text \<open>
  The following definition diverges from our previous attempt... mostly because we barely used it
  anyway. The problem was that we need to stop in final states which was not covered in the previous
  form.

  The main issue is the termination of the calculus. Between two restarts we
  allow very abstract inprocessing that makes it possible to add clauses.
  However, this means that we can add the same clause over and over and that
  have reached the bound (or subsume these clauses).

  TODO: add a forget rule in \<^term>\<open>pcdcl_stgy\<close> instead of having it in restart.

  The state is defined as an accumulator: The first component is the state we had after the last
  full restart (or the beginning of the search). We tried to make do without it, but the problem
  is managing to express the condition
  \<^term>\<open>size (pget_all_learned_clss T) - size (pget_all_learned_clss R) > f n\<close> without it. In a fast
  attempt, we completely oversaw that issue and had (in the current notations)
  \<^term>\<open>size (pget_all_learned_clss T) - size (pget_all_learned_clss S) > f n\<close>. This has, however,
   a very different semantics and allows much fewer restarts.


  One minor drawback is that we compare the number of clauses to the number of clauses after
  inprocessing instead of before inprocessing. The problem is that inprocessing could add the
  clause several times. I am not certain how to avoid that problem. An obvious solution is to
  ensure that no already-present clause is added (or at least that all duplicates have been removed)
  but it is not clear how to implement that inprocessing is not done until fixpoint.
 \<close>
type_synonym 'v prag_st_restart = \<open>'v prag_st \<times> 'v prag_st \<times> nat \<times> bool\<close>

abbreviation current_state :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st\<close> where
  \<open>current_state S \<equiv> fst (snd S)\<close>

abbreviation current_number :: \<open>'v prag_st_restart \<Rightarrow> nat\<close> where
  \<open>current_number S \<equiv> fst (snd (snd S))\<close>

abbreviation last_restart_state :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st\<close> where
  \<open>last_restart_state S \<equiv> fst S\<close>

inductive pcdcl_stgy_restart
  :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st_restart \<Rightarrow> bool\<close>
where
restart_step:
  \<open>pcdcl_stgy_restart (R, S, n, True)  (V, V, Suc n, True)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (pget_all_learned_clss T) - size (pget_all_learned_clss R) > f n\<close> and
    \<open>pcdcl_restart T U\<close> and
    \<open>pcdcl_stgy\<^sup>*\<^sup>* U V\<close> |
restart_noGC_step:
  \<open>pcdcl_stgy_restart (R, S, n, True)  (R, U, n, True)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (pget_all_learned_clss T) > size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart_only T U\<close> |
restart_full:
 \<open>pcdcl_stgy_restart (R, S, n, True)  (R, T, n, False)\<close>
 if
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>pcdcl_final_state T\<close>

end


lemma (in -) pcdcl_tcore_conflict_final_state_still:
  assumes
    \<open>pcdcl_tcore S T\<close> and
    \<open>count_decided (pget_trail S) = 0 \<and> pget_conflict S \<noteq> None\<close>
    shows \<open>count_decided (pget_trail T) = 0 \<and> pget_conflict T \<noteq> None \<and>
       pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms
  by (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
    cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
    cdcl_backtrack_unit.simps cdcl_flush_unit.simps)


lemma (in -) rtranclp_pcdcl_tcore_conflict_final_state_still:
  assumes
    \<open>pcdcl_tcore\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (pget_trail S) = 0 \<and> pget_conflict S \<noteq> None\<close>
  shows
    \<open>count_decided (pget_trail T) = 0 \<and> pget_conflict T \<noteq> None \<and>
    pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto simp: pcdcl_tcore_conflict_final_state_still)

lemma pcdcl_tcore_no_core_no_learned:
  assumes \<open>pcdcl_tcore S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms
  by (cases T)
    (auto simp: pcdcl_tcore.simps cdcl_subsumed.simps cdcl_flush_unit.simps pcdcl_core.simps
      dest: pcdcl_core.intros(6) elim!:  cdcl_backtrack_unit_is_backtrack[of S])

lemma (in -) pcdcl_tcore_no_step_final_state_still:
  assumes
    \<open>pcdcl_tcore S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>no_step pcdcl_core T\<close>
proof -
  have \<open>cdcl_subsumed S T \<or> cdcl_backtrack_unit S T \<or> cdcl_flush_unit S T\<close>
    using assms unfolding pcdcl_tcore.simps by fast
  then have dist: \<open>cdcl_subsumed S T \<or> cdcl_flush_unit S T\<close>
    using assms(2) cdcl_backtrack_unit_is_backtrack pcdcl_core.intros(6) by blast
  then have \<open>\<exists>U. cdcl_resolve T U \<Longrightarrow> \<exists>T. cdcl_resolve S T\<close>
    by (metis cdcl_flush_unit_unchanged cdcl_resolve_is_resolve resolve_is_cdcl_resolve
      state_of_cdcl_subsumed)
  moreover have \<open>\<exists>U. cdcl_skip T U \<Longrightarrow> \<exists>T. cdcl_skip S T\<close>
    using dist
    by (metis cdcl_flush_unit_unchanged cdcl_skip_is_skip skip_is_cdcl_skip
      state_of_cdcl_subsumed)
   moreover have \<open>\<exists>U. cdcl_backtrack T U \<Longrightarrow> \<exists>T. cdcl_backtrack S T\<close>
    using dist
    by (metis backtrack_is_cdcl_backtrack cdcl_backtrack_is_backtrack cdcl_flush_unit_unchanged
      state_of_cdcl_subsumed)
   moreover have \<open>\<exists>U. cdcl_conflict T U \<Longrightarrow> \<exists>T. cdcl_conflict S T\<close>
    using dist
    by (cases S)
     (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
        cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
        cdcl_backtrack_unit.simps cdcl_flush_unit.simps)
   moreover have \<open>\<exists>U. cdcl_propagate T U \<Longrightarrow> \<exists>T. cdcl_propagate S T\<close>
    using dist
    by (cases S)
      (auto 5 3 simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
        cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
        cdcl_backtrack_unit.simps cdcl_flush_unit.simps)
   moreover have \<open>\<exists>U. cdcl_decide T U \<Longrightarrow> \<exists>T. cdcl_decide S T\<close>
    using dist
    by (cases S)
      (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
        cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
        cdcl_backtrack_unit.simps cdcl_flush_unit.simps)
   ultimately have \<open>pcdcl_core T S' \<Longrightarrow> False\<close> for S'
     using assms(2) unfolding pcdcl_core.simps
     by (elim disjE) metis+
   then show ?thesis
     by blast
qed

lemma (in -) rtranclp_pcdcl_tcore_no_step_final_state_still:
  assumes
    \<open>pcdcl_tcore\<^sup>*\<^sup>* S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>no_step pcdcl_core T\<close>
  using assms by (induction rule: rtranclp_induct) (blast dest!: pcdcl_tcore_no_step_final_state_still)+

lemma rtranclp_pcdcl_tcore_no_core_no_learned:
  assumes \<open>pcdcl_tcore\<^sup>*\<^sup>* S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms rtranclp_pcdcl_tcore_no_step_final_state_still[OF assms]
  by (induction rule: rtranclp_induct)
    (simp_all add: pcdcl_tcore_no_core_no_learned rtranclp_pcdcl_tcore_no_step_final_state_still)


lemma no_step_pcdcl_core_stgy_pcdcl_coreD:
   \<open>no_step pcdcl_core_stgy S \<Longrightarrow> no_step pcdcl_core S\<close>
  using pcdcl_core.simps pcdcl_core_stgy.simps by blast

lemma rtranclp_pcdcl_tcore_stgy_no_core_no_learned:
  assumes \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using rtranclp_pcdcl_tcore_stgy_pcdcl_tcoreD[OF assms(1)] assms(2)
  by (blast intro: rtranclp_pcdcl_tcore_no_core_no_learned)

inductive pcdcl_stgy_only_restart for S where
 restart_noGC_step:
  \<open>pcdcl_stgy_only_restart (S) (U)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (pget_all_learned_clss T) > size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart_only T U\<close>

lemma pcdcl_tcore_stgy_step_or_unchanged:
   \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_core_stgy\<^sup>*\<^sup>* S T \<or> state_of S = state_of T \<or>
   (\<exists>T'. cdcl_backtrack S T' \<and> state_of T' = state_of T)\<close>
  apply (induction rule: pcdcl_tcore_stgy.induct)
  apply (auto simp: state_of_cdcl_subsumed cdcl_flush_unit_unchanged)[3]
  using cdcl_backtrack_unit_is_backtrack cdcl_flush_unit_unchanged by blast

lemma pcdcl_tcore_stgy_cdcl\<^sub>W_stgy:
   \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  using rtranclp_pcdcl_core_stgy_is_cdcl_stgy[of S T]
  apply (auto dest!: pcdcl_tcore_stgy_step_or_unchanged simp: pcdcl_all_struct_invs_def)
  by (metis pcdcl_core_stgy.intros(6) pcdcl_core_stgy_is_cdcl_stgy r_into_rtranclp
    state_of.simps)

lemma rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy:
   \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    by (smt pcdcl_tcore_pcdcl_all_struct_invs pcdcl_tcore_stgy_cdcl\<^sub>W_stgy
      pcdcl_tcore_stgy_pcdcl_tcoreD rtranclp.rtrancl_into_rtrancl rtranclp_induct)
  done

lemma [simp]: \<open>learned_clss (state_of S) = pget_all_learned_clss S\<close>
  by (cases S) auto

lemma
  pcdcl_tcore_stgy_init_learned:
    \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  pcdcl_tcore_stgy_psubsumed_learned_clauses:
    \<open>pcdcl_tcore_stgy S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>
  by (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma
  rtranclp_pcdcl_tcore_stgy_init_learned:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  rtranclp_pcdcl_tcore_stgy_psubsumed_learned_clauses:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: pcdcl_tcore_stgy_init_learned pcdcl_tcore_stgy_psubsumed_learned_clauses)

lemma
  pcdcl_stgy_only_restart_init_learned:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  pcdcl_stgy_only_restart_psubsumed_learned_clauses:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>
  by (auto simp: pcdcl_stgy_only_restart.simps pcdcl_restart_only.simps
    dest!: tranclp_into_rtranclp dest: rtranclp_pcdcl_tcore_stgy_init_learned
    rtranclp_pcdcl_tcore_stgy_psubsumed_learned_clauses)


lemma cdcl_twl_stgy_restart_new:
  assumes
    \<open>pcdcl_stgy_only_restart S U\<close> and
    invs: \<open>pcdcl_all_struct_invs S\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close> and
    dist: \<open>distinct_mset (pget_learned_clss S - A)\<close>
 shows \<open>distinct_mset (pget_learned_clss U - A)\<close>
  using assms(1)
proof cases
  case (restart_noGC_step T) note st = this(1) and res = this(3)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
    using rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy[of S T] invs st
    unfolding pcdcl_all_struct_invs_def
    by (auto dest!: tranclp_into_rtranclp)

 then have dist: \<open>distinct_mset (learned_clss (state_of T) - (A + pget_init_learned_clss S + psubsumed_learned_clauses S))\<close>
   apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
   subgoal using invs unfolding pcdcl_all_struct_invs_def by fast
   subgoal using propa unfolding pcdcl_all_struct_invs_def by fast
   subgoal using dist by (cases S) simp
   done
 have [simp]: \<open>pget_all_learned_clss U = pget_all_learned_clss T\<close>
   by (use res in \<open>auto simp: pcdcl_restart_only.simps\<close>)
 have \<open>distinct_mset (learned_clss (state_of U) - (A + pget_init_learned_clss U + psubsumed_learned_clauses U))\<close>
   apply (rule distinct_mset_mono[OF _ dist])
   by (simp add: assms(1) diff_le_mono2_mset pcdcl_stgy_only_restart_init_learned
     pcdcl_stgy_only_restart_psubsumed_learned_clauses subset_mset.add_mono)
 then show \<open>?thesis\<close>
   using res by (auto simp add: pcdcl_restart_only.simps)
qed


lemma cdcl_twl_stgy_restart_new':
  assumes
    \<open>pcdcl_stgy_only_restart S U\<close> and
    invs: \<open>pcdcl_all_struct_invs S\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close> and
    dist: \<open>distinct_mset (pget_all_learned_clss S - A)\<close>
 shows \<open>distinct_mset (pget_all_learned_clss U - A)\<close>
  using assms(1)
proof cases
  case (restart_noGC_step T) note st = this(1) and res = this(3)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
    using rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy[of S T] invs st
    unfolding pcdcl_all_struct_invs_def
    by (auto dest!: tranclp_into_rtranclp)

  then have dist: \<open>distinct_mset (learned_clss (state_of T) - (A))\<close>
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
    subgoal using invs unfolding pcdcl_all_struct_invs_def by fast
    subgoal using propa unfolding pcdcl_all_struct_invs_def by fast
    subgoal using dist by (cases S) simp
    done
  have [simp]: \<open>pget_all_learned_clss U = pget_all_learned_clss T\<close>
    by (use res in \<open>auto simp: pcdcl_restart_only.simps\<close>)
  have \<open>distinct_mset (learned_clss (state_of U) - A)\<close>
    apply (rule distinct_mset_mono[OF _ dist])
    by (simp add: assms(1) diff_le_mono2_mset pcdcl_stgy_only_restart_init_learned
      pcdcl_stgy_only_restart_psubsumed_learned_clauses subset_mset.add_mono)
  then show \<open>?thesis\<close>
    using res by (auto simp add: pcdcl_restart_only.simps)
qed


lemma pcdcl_stgy_only_restart_all_struct_invs:
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  using pcdcl_restart_only_pcdcl_all_struct_invs[of S]
  apply (auto simp: pcdcl_stgy_only_restart.simps dest!: tranclp_into_rtranclp)
  by (metis pcdcl_restart_only_pcdcl_all_struct_invs rtranclp_pcdcl_all_struct_invs
    rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy')


lemma rtranclp_pcdcl_stgy_only_restart_all_struct_invs:
  \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_stgy_only_restart_all_struct_invs)

lemma pcdcl_tcore_stgy_all_struct_invs:
  \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  using pcdcl_tcore_pcdcl_all_struct_invs pcdcl_tcore_stgy_pcdcl_tcoreD by blast

lemma rtranclp_pcdcl_tcore_stgy_all_struct_invs:
  \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  by (simp add: pcdcl_tcore_stgy_all_struct_invs rtranclp_induct)

lemma pcdcl_restart_only_no_smaller_propa:
  \<open>pcdcl_restart_only S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  by (fastforce simp: pcdcl_restart_only.simps cdcl\<^sub>W_restart_mset.no_smaller_propa_def
    clauses_def)

lemma pcdcl_stgy_only_restart_no_smaller_propa:
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  using pcdcl_restart_only_pcdcl_all_struct_invs[of _ T]
    rtranclp_pcdcl_tcore_stgy_no_smaller_propa[of S]
    rtranclp_pcdcl_tcore_stgy_all_struct_invs[of S]
    pcdcl_restart_only_no_smaller_propa[of _ T]
  by (auto simp: pcdcl_stgy_only_restart.simps dest!: tranclp_into_rtranclp)

lemma rtranclp_pcdcl_stgy_only_restart_no_smaller_propa:
  \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  apply (induction rule: rtranclp_induct)
   apply auto[]
  using pcdcl_stgy_only_restart_no_smaller_propa rtranclp_pcdcl_stgy_only_restart_all_struct_invs
  by blast

lemma rtranclp_cdcl_twl_stgy_restart_new_abs:
  assumes
    \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T\<close> and
    invs: \<open>pcdcl_all_struct_invs S\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close> and
    dist: \<open>distinct_mset (pget_learned_clss S - A)\<close>
  shows \<open>distinct_mset (pget_learned_clss T - A)\<close>
  using assms apply (induction)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_new[of T U A] rtranclp_pcdcl_stgy_only_restart_all_struct_invs[of S T]
    by (auto dest: rtranclp_pcdcl_stgy_only_restart_no_smaller_propa)
  done

lemma rtranclp_cdcl_twl_stgy_restart_new_abs':
  assumes
    \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T\<close> and
    invs: \<open>pcdcl_all_struct_invs S\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close> and
    dist: \<open>distinct_mset (pget_all_learned_clss S - A)\<close>
  shows \<open>distinct_mset (pget_all_learned_clss T - A)\<close>
  using assms apply (induction)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_new'[of T U A] rtranclp_pcdcl_stgy_only_restart_all_struct_invs[of S T]
    by (auto dest: rtranclp_pcdcl_stgy_only_restart_no_smaller_propa)
  done

lemma pcdcl_tcore_stgy_pget_all_learned_clss_mono:
  \<open>pcdcl_tcore_stgy S T \<Longrightarrow> size (pget_all_learned_clss S) \<le> size (pget_all_learned_clss T)\<close>
  by (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma rtranclp_pcdcl_tcore_stgy_pget_all_learned_clss_mono:
  \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> size (pget_all_learned_clss S) \<le> size (pget_all_learned_clss T)\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_tcore_stgy_pget_all_learned_clss_mono)

lemma pcdcl_stgy_only_restart_pget_all_learned_clss_mono:
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> size (pget_all_learned_clss S) \<le> size (pget_all_learned_clss T)\<close>
  by (induction rule: pcdcl_stgy_only_restart.induct)
   (auto dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_learned_clss_mono
    simp: pcdcl_restart_only.simps)

lemma [simp]: \<open>init_clss (state_of S) = pget_all_init_clss S\<close>
  by (cases S) auto

lemma pcdcl_tcore_stgy_pget_all_init_clss:
  \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma rtranclp_pcdcl_tcore_stgy_pget_all_init_clss:
  \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_tcore_stgy_pget_all_init_clss)

text \<open>TODO: Move\<close>
lemma card_simple_clss_with_tautology:
  assumes \<open>finite N\<close>
  shows \<open>finite {C. atms_of C \<subseteq> N \<and> distinct_mset C}\<close> and
    \<open>card {C. atms_of C \<subseteq> N \<and> distinct_mset C} \<le> 4 ^ card N\<close>
proof -
  have [simp]: \<open>finite x\<close> if \<open>atm_of ` x \<subseteq> N\<close> for x
  proof -
    have \<open>x \<subseteq> Pos ` N \<union> Neg ` N\<close>
      using that by (smt in_set_image_subsetD literal.exhaust_sel subsetI sup_ge1 sup_ge2)
    then show \<open>?thesis\<close>
      using assms by (meson finite_UnI finite_imageI finite_subset)
  qed

  have eq: \<open>card {C. atms_of C \<subseteq> N \<and> distinct_mset C} = card (set_mset ` {C. atms_of C \<subseteq> N \<and> distinct_mset C})\<close>
    (is \<open>card ?A = card ?B\<close>)
    if [simp]: \<open>finite {C. atms_of C \<subseteq> N \<and> distinct_mset C}\<close>
    apply (subst eq_sym_conv)
    apply (subst inj_on_iff_eq_card[symmetric])
    apply (auto simp: inj_on_def distinct_set_mset_eq_iff)
    done
  moreover have eq'[symmetric]: \<open>?B = {C. atm_of ` C \<subseteq> N}\<close> (is \<open>_  = ?C\<close>)
    apply (auto simp: atms_of_def image_iff distinct_mset_mset_set intro: exI[of _ \<open>mset_set _\<close>])
    apply (rule_tac x = \<open>mset_set x\<close> in exI)
    by (auto simp: distinct_mset_mset_set)

  moreover {
    have subst: \<open>?C \<subseteq> (\<lambda>(a,b). a \<union> b) ` (Pow (Pos ` N) \<times> Pow (Neg ` N))\<close>
      apply (rule, subst image_iff)
        apply (rule_tac x = \<open>({L. L \<in> x \<and> is_pos L}, {L. L \<in> x \<and> is_neg L})\<close> in bexI)
        apply (auto simp: is_pos_def)
      by (metis image_iff image_subset_iff literal.exhaust_sel)

    then have \<open>finite ?C\<close>
      by (rule finite_subset)
        (auto intro!: finite_imageI finite_cartesian_product simp: assms)
     note _ = this and subst
  } note H = this(1,2)
  ultimately show [iff]: \<open>finite {C. atms_of C \<subseteq> N \<and> distinct_mset C}\<close>
    apply simp
    by (metis (no_types, lifting) distinct_set_mset_eq_iff finite_imageD inj_on_def mem_Collect_eq)

  have H''[simp]: \<open>card ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> insert a ` B)) =
    card ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> B))\<close>
    if \<open>finite A\<close> \<open>finite B\<close> \<open>a \<notin> \<Union>A\<close> \<open>a \<notin> \<Union>B\<close> for A B a
  proof -
    have 1: \<open>((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> insert a ` B)) =
      insert a `  ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> B))\<close>
      by (rule; rule; clarsimp simp: image_iff)
    show \<open>card ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> insert a ` B)) =
      card  ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> B))\<close> 
      unfolding 1
      by (subst inj_on_iff_eq_card[symmetric])
        (use that in \<open>auto simp: inj_on_def\<close>)
  qed

  have H'[simp]: \<open>card ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (insert a ` A \<times> B)) =
    card ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> B))\<close>
    if \<open>finite A\<close> \<open>finite B\<close> \<open>a \<notin> \<Union>A\<close> \<open>a \<notin> \<Union>B\<close> for A B a
  proof -
    have 1: \<open>((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (insert a ` A \<times> B)) =
      insert a `  ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> B))\<close>
      by (rule; rule; clarsimp simp: image_iff)
    show \<open>card ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (insert a ` A \<times> B)) =
      card  ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<union> xa) ` (A \<times> B))\<close> 
      unfolding 1
      by (subst inj_on_iff_eq_card[symmetric])
        (use that in \<open>auto simp: inj_on_def\<close>)
  qed
  have \<open>card {C. atms_of C \<subseteq> N \<and> distinct_mset C} \<le> card ((\<lambda>(a,b). a \<union> b) ` (Pow (Pos ` N) \<times> Pow (Neg ` N)))\<close>
    apply (subst eq)
    apply (auto simp flip: eq')
    apply (rule card_mono[OF _ H(2)])
    by (auto intro!: finite_imageI finite_cartesian_product simp: assms)
  also have \<open>... \<le> 4 ^ card N\<close>
    using assms
    apply (induction N rule: finite_induct)
    apply (auto simp: Pow_insert insert_Times_insert Sigma_Un_distrib1 Sigma_Un_distrib2
      image_Un card_Un_disjoint)
    apply (subst card_Un_disjoint)
    apply auto
    apply (subst card_Un_disjoint)
    apply auto
    apply (subst card_Un_disjoint)
    apply auto
    apply (subst H')
    apply auto
    apply (subst H')
    apply auto
    apply (subst H'')
    apply auto
    apply (subst H'')
    apply auto
    done
  finally show \<open>card {C. atms_of C \<subseteq> N \<and> distinct_mset C} \<le> 4 ^ card N\<close>
    .
qed


lemma pcdcl_stgy_only_restart_pget_all_init_clss:
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (induction rule: pcdcl_stgy_only_restart.induct)
   (auto dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_init_clss
    simp: pcdcl_restart_only.simps)

lemma rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss:
  \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (induction rule: rtranclp_induct)
   (auto dest: pcdcl_stgy_only_restart_pget_all_init_clss)

lemma
  assumes \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows
    rtranclp_pcdcl_stgy_only_restart_distinct_mset:
      \<open>distinct_mset (pget_all_learned_clss T - pget_all_learned_clss S)\<close> and
    rtranclp_pcdcl_stgy_only_restart_bound:
      \<open>card (set_mset (pget_all_learned_clss T - pget_all_learned_clss S))
      \<le> 4 ^ (card (atms_of_mm (pget_all_init_clss S)))\<close> and
    rtranclp_pcdcl_stgy_only_restart_bound_size:
      \<open>size (pget_all_learned_clss T - pget_all_learned_clss S)
      \<le> 4 ^ (card (atms_of_mm (pget_all_init_clss S)))\<close>
proof -
  from assms(1) show dist: \<open>distinct_mset (pget_all_learned_clss T - pget_all_learned_clss S)\<close>
    by (rule rtranclp_cdcl_twl_stgy_restart_new_abs'[of \<open>S\<close> \<open>T\<close> \<open>pget_all_learned_clss S\<close>])
      (auto simp: assms)

  let ?N = \<open>atms_of_mm (pget_all_init_clss S)\<close>
  have fin_N: \<open>finite ?N\<close>
    by auto
  have \<open>pcdcl_all_struct_invs T\<close>
    using assms(1) assms(2) rtranclp_pcdcl_stgy_only_restart_all_struct_invs by blast
  then have \<open>set_mset (pget_all_learned_clss T) \<subseteq> {C. atms_of C \<subseteq> ?N \<and> distinct_mset C}\<close>
    by (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      simple_clss_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def
      rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss[OF assms(1)]
      dest!: multi_member_split)
  from card_mono[OF _ this] have \<open>card (set_mset (pget_all_learned_clss T)) \<le> 4 ^ (card ?N)\<close>
    using card_simple_clss_with_tautology[OF fin_N] by simp
  then show \<open>card (set_mset (pget_all_learned_clss T - pget_all_learned_clss S)) \<le> 4 ^ (card ?N)\<close>
    by (meson card_mono finite_set_mset in_diffD le_trans subsetI)
  then show \<open>size (pget_all_learned_clss T - pget_all_learned_clss S)
      \<le> 4 ^ (card (atms_of_mm (pget_all_init_clss S)))\<close>
    by (subst (asm) distinct_mset_size_eq_card[symmetric])
      (auto simp: dist)
qed

lemma wf_pcdcl_stgy_only_restart:
  \<open>wf {(T, S :: 'v prag_st). pcdcl_all_struct_invs S \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<and> pcdcl_stgy_only_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v prag_st\<close> where
    g: \<open>\<And>i. pcdcl_stgy_only_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. pcdcl_all_struct_invs (g i)\<close>and
    inv': \<open>\<And>i. cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast
  have \<open>pget_all_init_clss (g (Suc i)) = pget_all_init_clss (g i)\<close> for i
    using pcdcl_stgy_only_restart_pget_all_init_clss[OF g[of i]] by auto
  then have [simp]: \<open>NO_MATCH 0 i \<Longrightarrow> pget_all_init_clss (g i) = pget_all_init_clss (g 0)\<close> for i
    by (induction i) auto
  have star: \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* (g 0) (g i)\<close> for i
    by (induction i)
      (use g in \<open>auto intro: rtranclp.intros\<close>)

  let ?U = \<open>pget_all_learned_clss (g 0)\<close>
  define i j where
    \<open>i \<equiv> 4 ^ (card (atms_of_mm (pget_all_init_clss (g 0)))) + size (pget_all_learned_clss (g 0)) + 1\<close> and
    \<open>j \<equiv> i + size (pget_all_learned_clss (g 0))\<close>
  have \<open>size (pget_all_learned_clss (g (Suc i))) > size (pget_all_learned_clss (g i))\<close> for i
    using g[of i] by (auto simp: pcdcl_stgy_only_restart.simps pcdcl_restart_only.simps
      dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_learned_clss_mono)
  then have \<open>size (pget_all_learned_clss (g i)) \<ge> i\<close> for i
    by (induction i) (auto simp add: Suc_leI le_less_trans)
  from this[of j] have \<open>size (pget_all_learned_clss (g j) - pget_all_learned_clss (g 0)) \<ge> i\<close>
    unfolding i_def j_def
    by (meson add_le_imp_le_diff diff_size_le_size_Diff le_trans)
  moreover have \<open>size (pget_all_learned_clss (g j) - pget_all_learned_clss (g 0))
    \<le> i - 1\<close> for j
    using rtranclp_pcdcl_stgy_only_restart_bound_size[OF star[of j] inv inv'] by (auto simp: i_def)
  ultimately show False
    using not_less_eq_eq by (metis Suc_eq_plus1 add_diff_cancel_right' i_def)
qed


lemma pcdcl_core_stgy_pget_all_init_clss:
  \<open>pcdcl_core_stgy S T \<Longrightarrow> atms_of_mm (pget_all_init_clss S) =
    atms_of_mm (pget_all_init_clss T)\<close>
  by (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma pcdcl_stgy_pget_all_init_clss:
  \<open>pcdcl_stgy S T \<Longrightarrow> atms_of_mm (pget_all_init_clss S) =
    atms_of_mm (pget_all_init_clss T)\<close>
  by (induction rule: pcdcl_stgy.induct)
    (auto dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_init_clss
      simp: pcdcl_restart.simps pcdcl_core_stgy_pget_all_init_clss
        cdcl_learn_clause.simps cdcl_resolution.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma rtranclp_pcdcl_stgy_pget_all_init_clss:
  \<open>pcdcl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> atms_of_mm (pget_all_init_clss S) =
    atms_of_mm (pget_all_init_clss T)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: pcdcl_stgy_pget_all_init_clss)

context twl_restart
begin

lemma pcdcl_stgy_restart_pget_all_init_clss:
  \<open>pcdcl_stgy_restart S T \<Longrightarrow>
    atms_of_mm (pget_all_init_clss (fst S)) = atms_of_mm (pget_all_init_clss (fst (snd S))) \<Longrightarrow>
    atms_of_mm (pget_all_init_clss (fst S)) =
    atms_of_mm (pget_all_init_clss (fst T))\<close>
  by (induction rule: pcdcl_stgy_restart.induct)
   (auto dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_init_clss
      rtranclp_pcdcl_stgy_pget_all_init_clss
    simp: pcdcl_restart.simps pcdcl_restart_only.simps)

lemma pcdcl_stgy_restart_pget_all_init_clss2:
  \<open>pcdcl_stgy_restart S T \<Longrightarrow>
    atms_of_mm (pget_all_init_clss (fst S)) = atms_of_mm (pget_all_init_clss (fst (snd S))) \<Longrightarrow>
    atms_of_mm (pget_all_init_clss (fst T)) =
    atms_of_mm (pget_all_init_clss (fst (snd T)))\<close>
  by (induction rule: pcdcl_stgy_restart.induct)
    (clarsimp dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_init_clss
      rtranclp_pcdcl_stgy_pget_all_init_clss
    simp: pcdcl_restart.simps pcdcl_restart_only.simps)+

definition pcdcl_stgy_restart_inv :: \<open>'v prag_st_restart \<Rightarrow> bool\<close> where
  \<open>pcdcl_stgy_restart_inv = (\<lambda>(R, S, m, n). pcdcl_all_struct_invs R \<and>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of R) \<and>
  ((pcdcl_stgy_only_restart\<^sup>*\<^sup>* R S \<and>  n) \<or>
  (\<exists> R'. pcdcl_stgy_only_restart\<^sup>*\<^sup>* R R' \<and> pcdcl_tcore_stgy\<^sup>*\<^sup>* R' S \<and> pcdcl_final_state S \<and> \<not>n)))\<close>

lemma pcdcl_stgy_restart_inv_alt_def:
  \<open>pcdcl_stgy_restart_inv = (\<lambda>(R, S, m, n). pcdcl_all_struct_invs R \<and>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of R) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<and>
  ((pcdcl_stgy_only_restart\<^sup>*\<^sup>* R S \<and> n) \<or>
  (\<exists> R'. pcdcl_stgy_only_restart\<^sup>*\<^sup>* R R' \<and> pcdcl_tcore_stgy\<^sup>*\<^sup>* R' S \<and> pcdcl_final_state S \<and> \<not>n)) \<and>
  pcdcl_all_struct_invs S)\<close>
proof -
  have pcdcl_stgy_restart_inv_alt_def:
    \<open>pcdcl_stgy_restart_inv (R, S, m, n) \<longleftrightarrow> pcdcl_all_struct_invs R \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of R) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<and>
    ((pcdcl_stgy_only_restart\<^sup>*\<^sup>* R S \<and> n) \<or>
    (\<exists> R'. pcdcl_stgy_only_restart\<^sup>*\<^sup>* R R' \<and> pcdcl_tcore_stgy\<^sup>*\<^sup>* R' S \<and> pcdcl_final_state S \<and> \<not>n)) \<and>
    pcdcl_all_struct_invs S\<close> for R S m n
    unfolding pcdcl_stgy_restart_inv_def
    by (auto simp add: rtranclp_pcdcl_stgy_only_restart_all_struct_invs
      rtranclp_pcdcl_stgy_only_restart_all_struct_invs rtranclp_pcdcl_tcore_stgy_all_struct_invs
      dest: rtranclp_pcdcl_stgy_only_restart_no_smaller_propa rtranclp_pcdcl_tcore_stgy_no_smaller_propa)
  then show ?thesis
    by blast
qed

lemma pcdcl_stgy_restart_pcdcl_stgy_restart_inv:
  assumes \<open>pcdcl_stgy_restart S T\<close>\<open>pcdcl_stgy_restart_inv S\<close>
  shows \<open>pcdcl_stgy_restart_inv T\<close>
  using assms apply -
  apply (induction rule: pcdcl_stgy_restart.induct)
  subgoal
    by (auto simp add: pcdcl_stgy_restart_inv_def dest!: tranclp_into_rtranclp
    dest: pcdcl_restart_only_pcdcl_all_struct_invs rtranclp_pcdcl_tcore_stgy_all_struct_invs
    rtranclp_pcdcl_stgy_pcdcl pcdcl_restart_pcdcl_all_struct_invs rtranclp_pcdcl_all_struct_invs
      rtranclp_pcdcl_stgy_only_restart_all_struct_invs rtranclp_pcdcl_tcore_stgy_no_smaller_propa
      rtranclp_pcdcl_stgy_only_restart_no_smaller_propa pcdcl_restart_no_smaller_propa'
      rtranclp_pcdcl_stgy_no_smaller_propa)
  subgoal for S T U R n
    using pcdcl_stgy_only_restart.intros[of S T U] apply -
    unfolding pcdcl_stgy_restart_inv_def prod.case
    apply normalize_goal+
    apply (rule conjI)
    apply simp
    apply (rule conjI)
    apply simp
    apply (rule disjI1)
    by auto
  subgoal for S T R n
    unfolding pcdcl_stgy_restart_inv_def prod.case
    apply normalize_goal+
    apply (rule conjI)
    apply simp
    apply (rule conjI)
    apply simp
    apply (rule disjI2)
    by (meson rtranclp_trans)
  done

lemma rtranclp_pcdcl_stgy_restart_pcdcl_stgy_restart_inv:
  \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_stgy_restart_inv S \<Longrightarrow> pcdcl_stgy_restart_inv T\<close>
  by (induction rule: rtranclp_induct)
   (auto intro: pcdcl_stgy_restart_pcdcl_stgy_restart_inv)

theorem wf_cdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v prag_st \<times> 'v prag_st \<times> nat \<times> bool). pcdcl_stgy_restart_inv S \<and>
    pcdcl_stgy_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v prag_st \<times>'v prag_st \<times> nat \<times> bool\<close> where
    g: \<open>\<And>i. pcdcl_stgy_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. pcdcl_stgy_restart_inv (g i)\<close>
    unfolding wf_iff_no_infinite_down_chain
    by fast
  then have
    inv: \<open>\<And>i. pcdcl_all_struct_invs (last_restart_state (g i))\<close> and
    inv_c: \<open>\<And>i. pcdcl_all_struct_invs (current_state (g i))\<close> and
    inv': \<open>\<And>i. cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (last_restart_state (g i)))\<close> and
    inv'_c: \<open>\<And>i. cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (current_state (g i)))\<close> and
    rest_decomp: \<open>\<And>i. (pcdcl_stgy_only_restart\<^sup>*\<^sup>* (last_restart_state (g i)) (current_state (g i)) \<and> snd (snd (snd (g i))) \<or>
    (\<exists>R'. pcdcl_stgy_only_restart\<^sup>*\<^sup>* (last_restart_state (g i)) R' \<and>
    pcdcl_tcore_stgy\<^sup>*\<^sup>* R' (current_state (g i)) \<and> pcdcl_final_state (current_state (g i)) \<and>
    \<not>snd (snd (snd (g i)))))\<close>
    unfolding pcdcl_stgy_restart_inv_alt_def
    by (simp_all add: prod.case_eq_if)

  have [simp]: \<open>atms_of_mm (pget_all_init_clss (current_state (g i))) =
    atms_of_mm (pget_all_init_clss (last_restart_state (g i)))\<close> for i
    using rest_decomp[of i] apply -
    apply(elim disjE)
    apply (auto dest: rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss)[]
    apply normalize_goal+
    by (simp add: rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss rtranclp_pcdcl_tcore_stgy_pget_all_init_clss)

  have [simp]: \<open>NO_MATCH True c \<Longrightarrow> g i = (a, a', b, c) \<longleftrightarrow> g i = (a, a', b, True) \<and> c = True\<close> for i a b c a'
    using g[of i]
    by (auto simp: pcdcl_stgy_restart.simps)
  have H: \<open>snd (snd (snd (g i))) = True\<close> for i
    by (cases \<open>g i\<close>) auto
  have step_last_current: \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* (last_restart_state (g i)) (current_state (g i))\<close> for i
    using rest_decomp[of i] by (simp add: H)
  have n_mono: \<open>current_number (g (Suc i)) = Suc (current_number (g i)) \<or>
    current_number (g (Suc i)) = current_number (g i)\<close> for i
    using g[of i] by (auto simp: pcdcl_stgy_restart.simps)
  have will_eventually_GC: \<open>\<exists>i>j. current_number (g (Suc i)) = Suc (current_number (g i))\<close> for j
  proof (rule ccontr)
    assume mono: \<open>\<not> ?thesis\<close>
    have neq: \<open>current_number (g (Suc i)) = current_number (g (Suc j))\<close> if \<open>i \<ge> Suc j\<close> for i
      using that
      apply (induction rule:nat_induct_at_least)
      using le_Suc_eq mono n_mono apply auto[1]
      by (metis Suc_leD le_imp_less_Suc le_SucI mono n_mono)

    define f where \<open>f i = current_state (g (Suc i + j))\<close> for i
    have
      g: \<open>pcdcl_stgy_only_restart (f i) (f (Suc i))\<close> and
      inv: \<open>pcdcl_all_struct_invs (f i)\<close> and
      inv': \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (f i))\<close> for i
      defer
      using g[of \<open>Suc (i+j)\<close>] inv[of \<open>Suc (i+j)\<close>] inv'[of \<open>Suc (i+j)\<close>] neq[of \<open>i+j\<close>]
        neq[of \<open>Suc (i+j)\<close>] H[of \<open>i+j+1\<close>] inv_c[of \<open>Suc (i+j)\<close>] inv'_c[of \<open>Suc (i+j)\<close>]
      apply (auto simp: f_def pcdcl_stgy_restart.simps
        pcdcl_stgy_only_restart.simps Suc_le_eq pcdcl_stgy_restart.cases)[2]
      using g[of \<open>Suc (i+j)\<close>] inv[of \<open>Suc (i+j)\<close>] inv'[of \<open>Suc (i+j)\<close>] neq[of \<open>i+j\<close>]
        neq[of \<open>Suc (i+j)\<close>] H[of \<open>i+j+1\<close>]
      apply (cases rule: pcdcl_stgy_restart.cases)
      apply (force simp: f_def pcdcl_stgy_only_restart.restart_noGC_step
        pcdcl_stgy_restart.simps pcdcl_stgy_only_restart.simps Suc_le_eq)+
      done
    then show False
      using wf_pcdcl_stgy_only_restart unfolding wf_iff_no_infinite_down_chain by blast
  qed

  define f' where \<open>f' \<equiv> rec_nat 0 (\<lambda>_ n. LEAST i. i > n \<and> current_number (g (Suc i)) = Suc (current_number (g i)))\<close>
  then have [simp]: \<open>f' 0 = 0\<close> and f_Suc: \<open>f' (Suc n) = (LEAST i. i > f' n \<and> current_number (g (Suc i)) =
      Suc (current_number (g i)))\<close> for n
    by auto
  let ?f' = \<open>\<lambda>i. g (f' i)\<close>
  have
    f': \<open>current_number (g (Suc (f' (Suc i)))) = Suc (current_number (g (f' (Suc i))))\<close>
      \<open>f' i < f' (Suc i)\<close> for i
    using will_eventually_GC[of \<open>f' i\<close>]
      wellorder_class.LeastI_ex[of \<open>\<lambda>j. j > f' i \<and> current_number (g (Suc j)) = Suc (current_number (g j))\<close>]
    unfolding f_Suc[symmetric, of i]
    by (auto)

  have H: \<open>f' (Suc i) + k < f' (Suc (Suc i)) \<Longrightarrow> k > 0 \<Longrightarrow>
    current_number (g (Suc (f' (Suc i) + k))) =  current_number (g (f' (Suc i) + k))\<close> for k i
    using not_less_Least[of \<open>f' (Suc i) + k\<close>
      \<open>\<lambda>j. j > f' ((Suc i)) \<and> current_number (g (Suc j)) = Suc (current_number (g j))\<close>]
      g[of \<open>f' (Suc i) + k\<close>] unfolding f_Suc[symmetric]
    by (auto simp: pcdcl_stgy_restart.simps)

  have in_between: \<open>k \<ge> 1 \<Longrightarrow> f' (Suc i) + k < f' (Suc (Suc i)) \<Longrightarrow>
    current_number (g (Suc (f' (Suc i) + k))) =  current_number (g (Suc (f' (Suc i))))\<close> for k i
    apply (induction rule:nat_induct_at_least)
    subgoal
      using H[of i 1] by auto
    subgoal for k
      using H[of i \<open>Suc k\<close>]
      by auto
    done
  have f'_steps: \<open>current_number (g ((f' (Suc (Suc i))))) =  1 + current_number (g ((f' (Suc i))))\<close> for i
    using f'[of \<open>Suc i\<close>] f'[of \<open>i\<close>] in_between[of \<open>f' (Suc (Suc i)) - f' (Suc i) - 1\<close> \<open>i\<close>]
    apply (cases \<open>f' (Suc (Suc i)) - Suc (f' (Suc i)) = 0\<close>)
    apply auto
    by (metis Suc_lessI f'(1) f'(2) leD)
  have snd_f'_0: \<open>current_number (g ((f' (Suc (Suc i))))) =  Suc i + current_number (g ((f' (Suc 0))))\<close> for i
    apply (induction i)
    subgoal
      using f'_steps[of 0] by auto
    subgoal for i
      using f'_steps[of \<open>Suc i\<close>]
      by auto
    done

  let ?N = \<open>atms_of_mm (pget_all_init_clss (fst (g (f' (Suc 0)))))\<close>
  have \<open>unbounded (\<lambda>n. f (Suc ((n + current_number (g (f' (Suc 0)))))))\<close>
    unfolding bounded_def
    apply clarsimp
    subgoal for b
      using not_bounded_nat_exists_larger[OF f, of b \<open>((current_number (g (f' (Suc 0)))))\<close>]
      apply (auto simp: less_iff_Suc_add ac_simps)
      by (metis less_add_Suc2 not_less)
    done
  then obtain n where
    f: \<open>f ((Suc (n+ current_number (g (f' (Suc 0)))))) > 4 ^ (card ?N)\<close> (is \<open>f ?n > _\<close>)
    using not_less unfolding bounded_def by blast

  obtain Tn where
    Tn: \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ (current_state (?f' (Suc (Suc n)))) Tn\<close> and
    bound: \<open>f (?n) + size (pget_all_learned_clss (last_restart_state (?f' (Suc (Suc n)))))
       < size (pget_all_learned_clss Tn)\<close>
    using g[of \<open>f' (Suc (Suc n))\<close>] f'(1)[of \<open>Suc n\<close>] snd_f'_0[of n]
    by (auto elim: pcdcl_stgy_restart.cases)

  have \<open>atms_of_mm (pget_all_init_clss (fst (g (Suc i)))) = atms_of_mm (pget_all_init_clss (fst (g i)))\<close> for i
    using pcdcl_stgy_restart_pget_all_init_clss[OF g[of i]] by simp
  then have [simp]: \<open>NO_MATCH 0 i \<Longrightarrow>
      atms_of_mm (pget_all_init_clss (fst (g i))) = atms_of_mm (pget_all_init_clss (fst (g 0)))\<close> for i
    by (induction i) auto

  have inv_Tn: \<open>pcdcl_all_struct_invs Tn\<close>
    by (meson Tn inv_c rtranclp_pcdcl_tcore_stgy_all_struct_invs tranclp_into_rtranclp)

  have dist: \<open>distinct_mset
     (pget_all_learned_clss (current_state (g (f' (Suc (Suc n))))) -
     pget_all_learned_clss (last_restart_state (g (f' (Suc (Suc n))))))\<close>
    by (rule rtranclp_cdcl_twl_stgy_restart_new_abs'[of \<open>(fst (g (f' (Suc (Suc n)))))\<close>])
      (auto simp: inv inv' step_last_current)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of (current_state (?f' (Suc (Suc n))))) (state_of Tn)\<close>
    using rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy[of \<open>(current_state (?f' (Suc (Suc n))))\<close> Tn] Tn inv_Tn inv
    unfolding pcdcl_all_struct_invs_def
    by (auto dest!: tranclp_into_rtranclp simp: inv_c dest: rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy)

 then have dist: \<open>distinct_mset (learned_clss (state_of Tn) - (learned_clss (state_of (fst (?f' (Suc (Suc n)))))))\<close>
   apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
   subgoal using inv_c unfolding pcdcl_all_struct_invs_def by fast
   subgoal using inv'_c unfolding pcdcl_all_struct_invs_def by fast
   subgoal using dist by simp
   done


  have fin_N: \<open>finite ?N\<close>
    by auto
  have \<open>pget_all_init_clss Tn = pget_all_init_clss (fst (g (f' (Suc (Suc n)))))\<close>
    by (metis Tn rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss
      rtranclp_pcdcl_tcore_stgy_pget_all_init_clss step_last_current tranclp_into_rtranclp)
  then have \<open>set_mset (pget_all_learned_clss Tn) \<subseteq> {C. atms_of C \<subseteq> ?N \<and> distinct_mset C}\<close>
    using inv_Tn by (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        simple_clss_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def
      dest!: multi_member_split)
  from card_mono[OF _ this] have \<open>card (set_mset (pget_all_learned_clss Tn)) \<le> 4 ^ (card ?N)\<close>
    using card_simple_clss_with_tautology[OF fin_N] by simp
  then have \<open>card (set_mset (pget_all_learned_clss Tn
        - pget_all_learned_clss (fst (?f' (Suc (Suc n)))))) \<le> 4 ^ (card ?N)\<close>
    by (meson card_mono finite_set_mset in_diffD le_trans subsetI)
  then have \<open>size (pget_all_learned_clss Tn - pget_all_learned_clss (fst (g (f' (Suc (Suc n))))))
     \<le> 4 ^ (card ?N)\<close>
    using dist by (subst (asm) distinct_mset_size_eq_card[symmetric]) auto
  then show False
    using f bound by (meson diff_size_le_size_Diff leD le_less_trans less_diff_conv less_imp_le_nat)
qed

end

end