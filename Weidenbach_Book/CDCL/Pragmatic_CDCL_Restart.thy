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
   \<open>pcdcl_restart (M, N, U, None, NE, UE, NS, US, N0, U0)
        (M', N', U', None, NE + NE', UE + UE', NS, {#}, N0, U0)\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#E. L \<in> lits_of_l M' \<and> get_level M' L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M' \<longrightarrow> E \<in># (N + U') + NE + UE + UE'\<close> |
restart_clauses:
   \<open>pcdcl_restart (M, N, U, None, NE, UE, NS, US, N0, U0)
      (M, N', U', None, NE + NE', UE + UE', NS, US', N0, U0)\<close>
  if
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#E. L \<in> lits_of_l M \<and> get_level M L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M \<longrightarrow> E \<in># (N + U') + NE + UE + UE'\<close>
    \<open>US' = {#}\<close>


inductive pcdcl_restart_only :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
restart_trail:
   \<open>pcdcl_restart_only (M, N, U, None, NE, UE, NS, US, N0, U0)
        (M', N, U, None, NE, UE, NS, US, N0, U0)\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<or> M = M'\<close>


(*TODO Taken from Misc*)
lemma mset_le_incr_right1:
  "a\<subseteq>#(b::'a multiset) \<Longrightarrow> a\<subseteq>#b+c" using mset_subset_eq_mono_add[of a b "{#}" c, simplified] .

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
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US N0 U0)
  note decomp = this(1) and learned = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6) and stgy_invs = this(7) and
    smaller_propa = this(8)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0)\<close>
  let ?T = \<open>([], N + NE + NS + N0,  U' + UE + UE' + U0, None)\<close>
  let ?V = \<open>(M', N, U', None, NE, UE + UE', NS, {#}, N0, U0)\<close>
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
      (drop (length M - length M') M, N + NE + NS + N0,
        U' + UE + UE' + U0, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE + NS + N0\<close>
          \<open>U+UE+US+U0\<close> _
          \<open>U' + UE + UE'+U0\<close>])
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
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US N0 U0)
  note learned = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and inv = this(6) and stgy_invs = this(7) and  smaller_propa = this(8)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0) :: 'v prag_st\<close>
  let ?T = \<open>([], N + NE + NS + N0, U' + UE + UE' + US' + U0, None)\<close>
  let ?V = \<open>(M, N, U', None, NE, UE + UE', NS, US', N0, U0) :: 'v prag_st\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned US
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1
        split: if_splits)

  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding pcdcl_all_struct_invs_def by auto

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M) M, N + NE+NS+N0,
        U' + UE+ UE'+US'+U0, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE+NS+N0\<close>
           \<open>U+UE+US+U0\<close> _
          \<open>U' + UE + UE'+US'+U0\<close>])
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
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US N0 U0)
  note decomp = this(1) and learned = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0)\<close>
  let ?T = \<open>([], N + NE + NS + N0, U' + UE + UE' + U0, None)\<close>
  let ?V = \<open>(M', N, U', None, NE, UE + UE', NS, {#}, N0, U0)\<close>
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
      (drop (length M - length M') M,  N + NE + NS + N0,
          U' + UE+ UE' + U0, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
      \<open>N + NE + NS+N0\<close> \<open>U+UE+US+U0\<close> _
          \<open>U' + UE + UE'+U0\<close>])
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
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US N0 U0)
  note learned = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE,NS, US, N0, U0)\<close>
  let ?T = \<open>([], N + NE + NS+N0, U' + UE + UE' + US' + U0, None)\<close>
  let ?V = \<open>(M, N, U', None, NE, UE + UE', NS, US', N0, U0)\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned US
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1 split: if_splits)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by fast+
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M) M, N + NE + NS+N0,
          U' + UE+ UE' + US'+U0, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
          \<open>N + NE + NS+N0\<close> \<open>U+ UE + US+U0\<close> _
          \<open>U' + UE+ UE' + US'+U0\<close>])
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
      by (auto 7 3 simp: entailed_clss_inv_def clauses0_inv_def psubsumed_invs_def
        dest!: multi_member_split)
    subgoal
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def clauses0_inv_def
        dest!: multi_member_split)
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
  case (restart_trail K M' M2 M N U NE UE NS US N0 U0)
  note decomp = this(1) and inv = this(2) and stgy_invs = this(3) and
    smaller_propa = this(4)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0)\<close>
  let ?T = \<open>([], N + NE + NS + N0,  U + UE + US + U0, None)\<close>
  let ?V = \<open>(M', N, U, None, NE, UE, NS, US, N0, U0)\<close>
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
      (drop (length M - length M') M, N + NE + NS + N0, U + UE + US + U0, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE + NS + N0\<close>
          \<open>U+UE+US+U0\<close> _
          \<open>U+UE+US+U0\<close>])
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
  case (restart_trail K M' M2 M N U NE UE NS US N0 U0)
  note decomp = this(1) and inv = this(2)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0)\<close>
  let ?T = \<open>([], N + NE + NS+N0, U + UE + US+U0, None)\<close>
  let ?V = \<open>(M', N, U, None, NE, UE + US, NS, {#}, N0, U0)\<close>
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
      (drop (length M - length M') M,  N + NE + NS+N0,
          U + UE+ US+U0, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
      \<open>N + NE + NS+N0\<close> \<open>U+UE+US+U0\<close> _
          \<open>U + UE + US+U0\<close>])
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
      by (auto 7 3 simp: entailed_clss_inv_def clauses0_inv_def psubsumed_invs_def
        dest!: multi_member_split)
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
type_synonym (in -)'v prag_st_restart = \<open>'v prag_st \<times> 'v prag_st \<times> 'v prag_st \<times> nat \<times> nat \<times> bool\<close>

abbreviation (in -)current_state :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st\<close> where
  \<open>current_state S \<equiv> fst (snd (snd S))\<close>

abbreviation (in -)current_number :: \<open>'v prag_st_restart \<Rightarrow> nat\<close> where
  \<open>current_number S \<equiv> fst (snd (snd (snd (snd S))))\<close>

abbreviation (in -)current_restart_count :: \<open>'v prag_st_restart \<Rightarrow> nat\<close> where
  \<open>current_restart_count S \<equiv> fst (snd (snd (snd S)))\<close>

abbreviation (in -)last_GC_state :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st\<close> where
  \<open>last_GC_state S \<equiv> fst S\<close>

abbreviation (in -)last_restart_state :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st\<close> where
  \<open>last_restart_state S \<equiv> fst (snd S)\<close>

abbreviation (in -)restart_continue :: \<open>'v prag_st_restart \<Rightarrow> bool\<close> where
  \<open>restart_continue S \<equiv> snd (snd (snd (snd (snd S))))\<close>

text \<open>As inprocessing, we allow a slightly different set of rules, including restart. Remember that
the termination below takes the inprocessing as a granted (terminated) process. And without 
restrictions, the inprocessing does not terminate (it can restart).

On limitation of the following system is that \<^term>\<open>pcdcl_inprocessing\<close> is not allowed to derive the
empty clause. We tried to lift this limitation, but finally decided against it. The main problem is
that the regularity and the termination gets lost due to that rule.

The right place to handle the special case is later when reaching the final state in our or wherever
the predicate is used.

\<close>

inductive (in -)pcdcl_inprocessing :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close>
where
  \<open>pcdcl S T \<Longrightarrow> pcdcl_inprocessing S T\<close> |
  \<open>pcdcl_restart S T \<Longrightarrow> pcdcl_inprocessing S T\<close>

inductive pcdcl_stgy_restart
  :: \<open>'v prag_st_restart \<Rightarrow> 'v prag_st_restart \<Rightarrow> bool\<close>
where
step:
  \<open>pcdcl_stgy_restart (R, S, T, m, n, True)  (R, S, T', m, n, True)\<close>
  if
    \<open>pcdcl_tcore_stgy T T'\<close> |
restart_step:
  \<open>pcdcl_stgy_restart (R, S, T, m, n, True)  (W, W, W, m, Suc n, True)\<close>
  if
    \<open>size (pget_all_learned_clss T) - size (pget_all_learned_clss R) > f n\<close> and
    \<open>pcdcl_inprocessing\<^sup>*\<^sup>* T U\<close>
    \<open>pcdcl_restart U V\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of V)\<close> and
    \<open>pcdcl_stgy\<^sup>*\<^sup>* V W\<close> |
restart_noGC_step:
  \<open>pcdcl_stgy_restart (R, S, T, m, n, True)  (R, U, U, Suc m, n, True)\<close>
  if
    \<open>size (pget_all_learned_clss T) > size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart_only T U\<close> |
restart_full:
 \<open>pcdcl_stgy_restart (R, S, T, m, n, True)  (R, S, T, m, n, False)\<close>
 if
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

lemma restart_noGC_stepI:
  \<open>pcdcl_stgy_only_restart (S) (U)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>size (pget_all_learned_clss T) > size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart_only T U\<close>
  using restart_noGC_step[of S T U]
  by (metis not_less_iff_gr_or_eq restart_noGC_step rtranclpD that(1) that(2) that(3))

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
    \<open>pcdcl_tcore_stgy S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>and
  pcdcl_tcore_stgy_plearned_clauses0:
    \<open>pcdcl_tcore_stgy S T \<Longrightarrow> plearned_clauses0 S \<subseteq># plearned_clauses0 T\<close>
  by (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma
  rtranclp_pcdcl_tcore_stgy_init_learned:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  rtranclp_pcdcl_tcore_stgy_psubsumed_learned_clauses:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close> and
  rtranclp_pcdcl_tcore_stgy_plearned_clauses0:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> plearned_clauses0 S \<subseteq># plearned_clauses0 T\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: pcdcl_tcore_stgy_init_learned pcdcl_tcore_stgy_psubsumed_learned_clauses
      pcdcl_tcore_stgy_plearned_clauses0)

lemma
  pcdcl_stgy_only_restart_init_learned:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  pcdcl_stgy_only_restart_psubsumed_learned_clauses:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close> and
  pcdcl_stgy_only_restart_plearned_clauses0:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> plearned_clauses0 S \<subseteq># plearned_clauses0 T\<close>
  by (auto simp: pcdcl_stgy_only_restart.simps pcdcl_restart_only.simps
    dest!: tranclp_into_rtranclp dest: rtranclp_pcdcl_tcore_stgy_init_learned
    rtranclp_pcdcl_tcore_stgy_psubsumed_learned_clauses rtranclp_pcdcl_tcore_stgy_plearned_clauses0)


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

  then have dist: \<open>distinct_mset (learned_clss (state_of T) - (A + pget_init_learned_clss S +
      psubsumed_learned_clauses S + plearned_clauses0 S))\<close>
   apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
   subgoal using invs unfolding pcdcl_all_struct_invs_def by fast
   subgoal using propa unfolding pcdcl_all_struct_invs_def by fast
   subgoal using dist by (cases S) simp
   done
 have [simp]: \<open>pget_all_learned_clss U = pget_all_learned_clss T\<close>
   by (use res in \<open>auto simp: pcdcl_restart_only.simps\<close>)
 have \<open>distinct_mset (learned_clss (state_of U) - (A + pget_init_learned_clss U +
    psubsumed_learned_clauses U + plearned_clauses0 U))\<close>
   apply (rule distinct_mset_mono[OF _ dist])
   by (simp add: assms(1) diff_le_mono2_mset pcdcl_stgy_only_restart_init_learned
     pcdcl_stgy_only_restart_psubsumed_learned_clauses subset_mset.add_mono
     pcdcl_stgy_only_restart_plearned_clauses0)
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

lemma cdcl_unitres_true_all_init_clss:
  \<open>cdcl_unitres_true S T \<Longrightarrow> (pget_all_init_clss S) = (pget_all_init_clss T)\<close>
  by (induction rule: cdcl_unitres_true.induct) auto

lemma pcdcl_stgy_pget_all_init_clss:
  \<open>pcdcl_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> atms_of_mm (pget_all_init_clss S) =
    atms_of_mm (pget_all_init_clss T)\<close>
  by (induction rule: pcdcl_stgy.induct)
    (auto dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_stgy_pget_all_init_clss
    simp: pcdcl_restart.simps pcdcl_core_stgy_pget_all_init_clss cdcl_inp_propagate.simps
    cdcl_inp_conflict.simps pcdcl_all_struct_invs_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.no_strange_atm_def
    cdcl_learn_clause.simps cdcl_resolution.simps cdcl_subsumed.simps cdcl_flush_unit.simps
    cdcl_unitres_true_all_init_clss)

lemma rtranclp_pcdcl_stgy_pget_all_init_clss:
  \<open>pcdcl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
  atms_of_mm (pget_all_init_clss S) = atms_of_mm (pget_all_init_clss T)\<close>
  by (induction rule: rtranclp_induct)
   (auto dest: pcdcl_stgy_pget_all_init_clss rtranclp_pcdcl_all_struct_invs
    dest!: rtranclp_pcdcl_stgy_pcdcl)

lemma pcdcl_tcore_pget_all_init_clss:
  \<open>pcdcl_tcore S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma rtranclp_pcdcl_tcore_pget_all_init_clss:
  \<open>pcdcl_tcore\<^sup>*\<^sup>* S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_tcore_pget_all_init_clss)

lemma pcdcl_core_pget_all_init_clss:
  \<open>pcdcl_core S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (auto simp: pcdcl_core.simps pcdcl_core.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma rtranclp_pcdcl_core_pget_all_init_clss:
  \<open>pcdcl_core\<^sup>*\<^sup>* S T \<Longrightarrow> pget_all_init_clss S = pget_all_init_clss T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_core_pget_all_init_clss)

lemma pcdcl_pget_all_init_clss:
  \<open>pcdcl S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>  atms_of_mm (pget_all_init_clss S) =
    atms_of_mm (pget_all_init_clss T)\<close>
  by (induction rule: pcdcl.induct)
   (auto dest!: tranclp_into_rtranclp rtranclp_pcdcl_tcore_pget_all_init_clss
      pcdcl_core_pget_all_init_clss
    simp: pcdcl_restart.simps pcdcl_core_stgy_pget_all_init_clss cdcl_inp_propagate.simps
        cdcl_inp_conflict.simps
    cdcl_learn_clause.simps cdcl_resolution.simps cdcl_subsumed.simps cdcl_flush_unit.simps
    cdcl_unitres_true_all_init_clss
    cdcl_inp_conflict.simps pcdcl_all_struct_invs_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_promote_false.simps
    cdcl\<^sub>W_restart_mset.no_strange_atm_def)

lemma rtranclp_pcdcl_pget_all_init_clss:
  \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>  atms_of_mm (pget_all_init_clss S) =
  atms_of_mm (pget_all_init_clss T)\<close>
  by (induction rule: rtranclp_induct)
   (auto dest!: pcdcl_pget_all_init_clss rtranclp_pcdcl_all_struct_invs)


lemma pcdcl_inprocessing_pget_all_init_clss:
  \<open>pcdcl_inprocessing S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
    atms_of_mm (pget_all_init_clss T) = atms_of_mm (pget_all_init_clss S)\<close>
  by (induction rule: pcdcl_inprocessing.induct)
   (auto dest!: rtranclp_pcdcl_stgy_pget_all_init_clss rtranclp_pcdcl_pget_all_init_clss pcdcl_pget_all_init_clss
    simp: pcdcl_restart.simps pcdcl_restart_only.simps)

lemma pcdcl_inprocessing_pcdcl_all_struct_invs:
  \<open>pcdcl_inprocessing S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  by (cases rule: pcdcl_inprocessing.cases, assumption)
    (blast dest: pcdcl_all_struct_invs pcdcl_restart_pcdcl_all_struct_invs)+

lemma rtranclp_pcdcl_inprocessing_pcdcl_all_struct_invs:
  \<open>pcdcl_inprocessing\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  by (induction rule: rtranclp_induct)
    (blast dest: pcdcl_inprocessing_pcdcl_all_struct_invs)+

lemma rtranclp_pcdcl_inprocessing_pget_all_init_clss:
  \<open>pcdcl_inprocessing\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>atms_of_mm (pget_all_init_clss T) = atms_of_mm (pget_all_init_clss S)\<close>
  by (induction rule: rtranclp_induct)
   (auto dest!: pcdcl_inprocessing_pget_all_init_clss
    dest: pcdcl_inprocessing_pget_all_init_clss rtranclp_pcdcl_inprocessing_pcdcl_all_struct_invs)

context twl_restart_ops
begin
lemma pcdcl_stgy_restart_pget_all_init_clss:
  \<open>pcdcl_stgy_restart S T \<Longrightarrow> pcdcl_all_struct_invs (current_state S) \<Longrightarrow>
    atms_of_mm (pget_all_init_clss (last_restart_state S)) = atms_of_mm (pget_all_init_clss (current_state S)) \<Longrightarrow>
    atms_of_mm (pget_all_init_clss (last_GC_state S)) = atms_of_mm (pget_all_init_clss (current_state S)) \<Longrightarrow>
  atms_of_mm (pget_all_init_clss (current_state T)) = atms_of_mm (pget_all_init_clss (current_state S)) \<and>
  atms_of_mm (pget_all_init_clss (last_restart_state T)) = atms_of_mm (pget_all_init_clss (current_state S)) \<and>
  atms_of_mm (pget_all_init_clss (last_GC_state T)) = atms_of_mm (pget_all_init_clss (current_state S))\<close>
  apply (induction rule: pcdcl_stgy_restart.induct)
  apply (simp add: pcdcl_tcore_stgy_pget_all_init_clss)
  apply simp
  apply (metis (full_types) pcdcl_inprocessing.intros(2) pcdcl_inprocessing_pcdcl_all_struct_invs
    pcdcl_inprocessing_pget_all_init_clss rtranclp_pcdcl_inprocessing_pcdcl_all_struct_invs
    rtranclp_pcdcl_inprocessing_pget_all_init_clss rtranclp_pcdcl_stgy_pget_all_init_clss)
  apply simp
  apply (smt pcdcl_restart_only.cases pget_all_init_clss.simps)
  apply simp
  done

definition pcdcl_stgy_restart_inv :: \<open>'v prag_st_restart \<Rightarrow> bool\<close> where
  \<open>pcdcl_stgy_restart_inv = (\<lambda>(Q, R, S, m, n). pcdcl_all_struct_invs Q \<and>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of Q) \<and>
  pcdcl_stgy_only_restart\<^sup>*\<^sup>* Q R \<and> pcdcl_tcore_stgy\<^sup>*\<^sup>* R S)\<close>

lemma pcdcl_stgy_restart_inv_alt_def:
  \<open>pcdcl_stgy_restart_inv = (\<lambda>(Q, R, S, m, n). pcdcl_all_struct_invs Q \<and>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of Q) \<and> pcdcl_all_struct_invs R \<and>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of R) \<and>  pcdcl_all_struct_invs S \<and>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<and>
  pcdcl_stgy_only_restart\<^sup>*\<^sup>* Q R \<and> pcdcl_tcore_stgy\<^sup>*\<^sup>* R S)\<close>
  (is \<open>_ = ?P\<close>)
proof -
  have pcdcl_stgy_restart_inv_alt_def:
    \<open>pcdcl_stgy_restart_inv (Q, R, S, m, n) \<longleftrightarrow> ?P (Q, R, S, m, n)\<close> for Q R S m n
    unfolding pcdcl_stgy_restart_inv_def
    by (auto simp add: rtranclp_pcdcl_stgy_only_restart_all_struct_invs
      rtranclp_pcdcl_stgy_only_restart_all_struct_invs rtranclp_pcdcl_tcore_stgy_all_struct_invs
      dest: rtranclp_pcdcl_stgy_only_restart_no_smaller_propa rtranclp_pcdcl_tcore_stgy_no_smaller_propa)
  then show ?thesis
    by blast
qed

lemma no_smaller_propa_lvl0:
  \<open>count_decided (pget_trail U) = 0 \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of U)\<close>
  by (auto simp add: cdcl\<^sub>W_restart_mset.no_smaller_propa_def)

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
  subgoal for T R n U V W S m
    using pcdcl_stgy_only_restart.intros[of S T U] apply -
    apply (subst (asm) pcdcl_stgy_restart_inv_alt_def)
    unfolding pcdcl_stgy_restart_inv_def prod.case
    apply normalize_goal+
    apply (rule conjI)
    using pcdcl_restart_pcdcl_all_struct_invs rtranclp_pcdcl_all_struct_invs rtranclp_pcdcl_inprocessing_pcdcl_all_struct_invs
      rtranclp_pcdcl_stgy_pcdcl apply blast
    apply simp
    using pcdcl_restart_no_smaller_propa' pcdcl_restart_pcdcl_all_struct_invs rtranclp_pcdcl_stgy_no_smaller_propa
      rtranclp_pcdcl_inprocessing_pcdcl_all_struct_invs
    by blast
  subgoal for T S U R n
    apply (subst (asm) pcdcl_stgy_restart_inv_alt_def)
    unfolding pcdcl_stgy_restart_inv_def prod.case
    apply normalize_goal+
    apply (rule conjI)
    apply simp
    apply (rule conjI)
    apply simp
    apply (rule conjI)
    apply (metis (no_types, lifting) Nitpick.rtranclp_unfold nat_neq_iff
      pcdcl_stgy_only_restart.restart_noGC_step rtranclp.simps)
    apply blast
    done
  subgoal for T R S n
    unfolding pcdcl_stgy_restart_inv_def prod.case
    by auto
  done


lemma rtranclp_pcdcl_stgy_restart_pcdcl_stgy_restart_inv:
  assumes \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* S T\<close>\<open>pcdcl_stgy_restart_inv S\<close>
  shows \<open>pcdcl_stgy_restart_inv T\<close>
  using assms
  by (induction rule: rtranclp_induct)
    (auto dest!: pcdcl_stgy_restart_pcdcl_stgy_restart_inv)

lemma pcdcl_stgy_restart_current_number:
  \<open>pcdcl_stgy_restart S T \<Longrightarrow> current_number S \<le> current_number T\<close>
  by (induction rule: pcdcl_stgy_restart.induct) auto

lemma rtranclp_pcdcl_stgy_restart_current_number:
  \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> current_number S \<le> current_number T\<close>
  by (induction rule: rtranclp_induct) (auto dest: pcdcl_stgy_restart_current_number)

lemma pcdcl_stgy_restart_no_GC_either:
  \<open>pcdcl_stgy_restart S T \<Longrightarrow> pcdcl_stgy_restart_inv S \<Longrightarrow>
  current_number T = current_number S \<Longrightarrow>
  (last_restart_state T = current_state T \<and> pcdcl_stgy_only_restart (last_restart_state S) (current_state T)) \<or>
  (last_restart_state S = last_restart_state T \<and> pcdcl_tcore_stgy (current_state S) (current_state T)) \<or>
  (last_restart_state S = last_restart_state T \<and> (current_state S) = (current_state T)  \<and> \<not>restart_continue T)\<close>
  using pcdcl_stgy_restart_pcdcl_stgy_restart_inv[of S T]
  apply simp
  apply (induction rule: pcdcl_stgy_restart.induct)
  subgoal
    by (simp add: pcdcl_stgy_restart_inv_def case_prod_beta)
  subgoal
    by (simp add: pcdcl_stgy_restart_inv_def case_prod_beta)
  subgoal for T S U R m n
    using restart_noGC_stepI[of S T U]
    by (auto simp add: pcdcl_stgy_restart_inv_def)
  subgoal for T R S m n
    using restart_noGC_stepI[of S T U]
    by (auto simp add: pcdcl_stgy_restart_inv_def)
  done

lemma rtranclp_pcdcl_stgy_restart_decomp:
  \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_stgy_restart_inv S \<Longrightarrow>
  current_number T = current_number S \<Longrightarrow> pcdcl_stgy_only_restart\<^sup>*\<^sup>* (current_state S) (last_restart_state S) \<Longrightarrow>
  pcdcl_stgy_only_restart\<^sup>*\<^sup>* (current_state S) (last_restart_state T) \<and> pcdcl_tcore_stgy\<^sup>*\<^sup>* (last_restart_state T) (current_state T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal
    by (simp add: pcdcl_stgy_restart_inv_def case_prod_beta)
  subgoal for T U
    using rtranclp_pcdcl_stgy_restart_current_number[of S T] pcdcl_stgy_restart_current_number[of T U]
      pcdcl_stgy_restart_no_GC_either[of T U] rtranclp_pcdcl_stgy_restart_pcdcl_stgy_restart_inv[of S T]
    by (auto)
  done

lemma
  assumes \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>pcdcl_stgy_restart_inv S\<close> and
    \<open>current_number T = current_number S\<close> and
    \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* (current_state S) (last_restart_state S)\<close> and
    \<open>distinct_mset (pget_all_learned_clss (current_state S) - A)\<close>
  shows
    rtranclp_pcdcl_stgy_restart_distinct_mset:
    \<open>distinct_mset (pget_all_learned_clss (current_state T) - A)\<close> (is ?dist) and
    rtranclp_pcdcl_stgyrestart_bound:
      \<open>card (set_mset (pget_all_learned_clss (current_state T) - A))
      \<le> 4 ^ (card (atms_of_mm (pget_all_init_clss (current_state S))))\<close> (is ?A) and
    rtranclp_pcdcl_stgy_restart_bound_size:
      \<open>size (pget_all_learned_clss (current_state T) - A)
      \<le> 4 ^ (card (atms_of_mm (pget_all_init_clss (current_state S))))\<close> (is ?B)
proof -
  let ?S = \<open>current_state S\<close>
  let ?T = \<open>last_restart_state T\<close>
  let ?U = \<open>current_state T\<close>
  have ST: \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* ?S ?T\<close> and
    TU: \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* ?T ?U\<close>
    using rtranclp_pcdcl_stgy_restart_decomp[OF assms(1-4)] by fast+

  have inv_T: \<open>pcdcl_stgy_restart_inv T\<close>
    using assms(1) inv rtranclp_pcdcl_stgy_restart_pcdcl_stgy_restart_inv by blast
  have dist: \<open>distinct_mset (pget_all_learned_clss ?T - A)\<close>
    by (rule rtranclp_cdcl_twl_stgy_restart_new_abs'[OF ST])
     (use inv in \<open>auto simp: pcdcl_stgy_restart_inv_def assms(5)
       rtranclp_pcdcl_tcore_stgy_all_struct_invs
      dest: rtranclp_pcdcl_stgy_only_restart_all_struct_invs
      rtranclp_pcdcl_stgy_only_restart_no_smaller_propa rtranclp_pcdcl_tcore_stgy_no_smaller_propa\<close>)

  have inv_T': \<open>pcdcl_all_struct_invs ?T\<close>
    by (smt ST inv pcdcl_stgy_restart_inv_alt_def rtranclp_pcdcl_stgy_only_restart_all_struct_invs
      split_beta)
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of ?T) (state_of ?U)\<close>
    using rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy[OF TU]
    unfolding pcdcl_all_struct_invs_def
    by (auto dest!: tranclp_into_rtranclp)

  then have dist: \<open>distinct_mset (learned_clss (state_of ?U) - (A))\<close>
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
    subgoal using inv_T' unfolding pcdcl_all_struct_invs_def by fast
    subgoal using inv_T unfolding pcdcl_stgy_restart_inv_alt_def by auto
    subgoal using dist by (cases S) simp
    done
  then show \<open>?dist\<close>
    by auto

  have SU: \<open>pget_all_init_clss ?U = pget_all_init_clss ?S\<close>
    by (metis ST TU rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss rtranclp_pcdcl_tcore_stgy_pget_all_init_clss)
  let ?N = \<open>atms_of_mm (pget_all_init_clss ?U)\<close>
  have fin_N: \<open>finite ?N\<close>
    by auto
  have inv_U: \<open>pcdcl_all_struct_invs ?U\<close>
    using TU inv_T' rtranclp_pcdcl_tcore_stgy_all_struct_invs by blast
  then have \<open>set_mset (pget_all_learned_clss ?U) \<subseteq> {C. atms_of C \<subseteq> ?N \<and> distinct_mset C}\<close>
    by (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      simple_clss_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def
      dest!: multi_member_split)
  from card_mono[OF _ this] have \<open>card (set_mset (pget_all_learned_clss ?U)) \<le> 4 ^ (card ?N)\<close>
    using card_simple_clss_with_tautology[OF fin_N] by simp
  then show ?A
    unfolding SU
    by (meson card_mono finite_set_mset in_diffD le_trans subsetI)
  then show ?B
    unfolding SU
    by (subst (asm) distinct_mset_size_eq_card[symmetric])
      (use dist in auto)
qed

lemma pcdcl_stgy_restart_mono:
  \<open>pcdcl_stgy_restart S T \<Longrightarrow> current_number S = current_number T \<Longrightarrow>
  pget_all_learned_clss (current_state S) \<subseteq># pget_all_learned_clss (current_state T)\<close>
  by (induction rule: pcdcl_stgy_restart.induct)
   (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps
    cdcl_conflict.simps cdcl_propagate.simps cdcl_decide.simps
    cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps
    cdcl_subsumed.simps cdcl_flush_unit.simps cdcl_backtrack_unit.simps
    pcdcl_restart_only.simps)

lemma rtranclp_pcdcl_stgy_restart_mono:
  \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow>current_number S = current_number T \<Longrightarrow>
  pget_all_learned_clss (current_state S) \<subseteq># pget_all_learned_clss (current_state T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using pcdcl_stgy_restart_mono[of T U]
      rtranclp_pcdcl_stgy_restart_current_number[of S T] pcdcl_stgy_restart_current_number[of T U]
    by auto
  done

end



text \<open>

The termination proof contains the usual boilerplate that hide the real argument. The idea of the
proof is to consider an infinite chain of \<^term>\<open>pcdcl_stgy_restart\<close>. From it:

   \<^item> We know that have eventually to do a restart, as \<^term>\<open>pcdcl_tcore_stgy\<close> terminates.

   \<^item> Then, if there are no GC, as we will eventually restart we can extract a sequence of
   \<^term>\<open>pcdcl_stgy_only_restart\<close>. That terminates, so we have to eventually GC.

  \<^item> Finally, as \<^term>\<open>f\<close> is unbounded, at some we have learned more clauses that admissible.

The proof is make more complicated by the extraction of the subsequences: we derive the subsequence
of indices \<^term>\<open>f'\<close>, then by induction we prove properties on the subsequence.

\<close>
context twl_restart
begin

theorem wf_pcdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v prag_st_restart). pcdcl_stgy_restart_inv S \<and> pcdcl_stgy_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v prag_st_restart\<close> where
    g: \<open>\<And>i. pcdcl_stgy_restart (g i) (g (Suc i))\<close> and
    restart_inv: \<open>\<And>i. pcdcl_stgy_restart_inv (g i)\<close>
    unfolding wf_iff_no_infinite_down_chain
    by fast
  then have
    inv: \<open>\<And>i. pcdcl_all_struct_invs (last_restart_state (g i))\<close> and
    inv_c: \<open>\<And>i. pcdcl_all_struct_invs (current_state (g i))\<close> and
    inv': \<open>\<And>i. cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (last_restart_state (g i)))\<close> and
    inv'_c: \<open>\<And>i. cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (current_state (g i)))\<close> and
    rest_decomp: \<open>\<And>i. pcdcl_tcore_stgy\<^sup>*\<^sup>* (last_restart_state (g i)) (current_state (g i))\<close> and
    rest_decomp2: \<open>\<And>i. pcdcl_stgy_only_restart\<^sup>*\<^sup>* (last_GC_state (g i)) (last_restart_state (g i))\<close>
    unfolding pcdcl_stgy_restart_inv_alt_def
    by (simp_all add: prod.case_eq_if)


  have [simp]: \<open>NO_MATCH True c \<Longrightarrow> g i = (a, a', a'', b, b', c) \<longleftrightarrow> g i = (a, a', a'', b, b', True) \<and> c = True\<close>
    for i a b c a' a'' b'
    using g[of i]
    by (auto simp: pcdcl_stgy_restart.simps)
  have H: \<open>restart_continue (g i) = True\<close> for i
    by (cases \<open>g i\<close>) auto

  have n_mono: \<open>current_number (g (Suc i)) = Suc (current_number (g i)) \<or>
    current_number (g (Suc i)) = current_number (g i)\<close> for i
    using g[of i] by (auto simp: pcdcl_stgy_restart.simps)
  have n_mono': \<open>current_restart_count (g (Suc i)) = Suc (current_restart_count (g i)) \<or>
    current_restart_count (g (Suc i)) = current_restart_count (g i)\<close> for i
    using g[of i] by (auto simp: pcdcl_stgy_restart.simps)
  have will_eventually_Restart: \<open>\<exists>i>j. current_restart_count (g (Suc i)) \<noteq> current_restart_count (g i)\<close>
    if no_GC: \<open>\<And>i. i > j \<Longrightarrow> current_number (g (Suc i)) = (current_number (g i))\<close>
    for j
  proof (rule ccontr)
    assume mono: \<open>\<not> ?thesis\<close>
    have neq: \<open>current_restart_count (g (Suc i)) = current_restart_count (g (Suc j))\<close> if \<open>i \<ge> j\<close> for i
      using that
      apply (induction rule:nat_induct_at_least)
      using le_Suc_eq mono n_mono apply auto[1]
      by (metis Suc_leD le_imp_less_Suc le_SucI mono n_mono)

    define f where \<open>f i = current_state (g (Suc i + j))\<close> for i
    have
      g: \<open>pcdcl_tcore_stgy (f i) (f (Suc i))\<close> and
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
      subgoal for T T' R S n
        by (auto simp: f_def pcdcl_stgy_only_restart.restart_noGC_step
          pcdcl_stgy_restart.simps pcdcl_stgy_only_restart.simps Suc_le_eq)
      subgoal for T R n U V S
        using no_GC[of \<open>Suc (i + j)\<close>]
        by (auto simp: f_def pcdcl_stgy_only_restart.restart_noGC_step
          pcdcl_stgy_restart.simps pcdcl_stgy_only_restart.simps Suc_le_eq)
      subgoal for T R n U V S
        by (auto simp: f_def pcdcl_stgy_only_restart.restart_noGC_step
          pcdcl_stgy_restart.simps pcdcl_stgy_only_restart.simps Suc_le_eq)
      subgoal
        by simp
      done
    then show False
      using wf_pcdcl_tcore_stgy unfolding wf_iff_no_infinite_down_chain by blast
  qed
  have will_eventually_GC: \<open>\<exists>i>j. current_number (g (Suc i)) = Suc (current_number (g i))\<close> for j
  proof (rule ccontr)
    assume mono: \<open>\<not> ?thesis\<close>
    have neq: \<open>current_number (g (Suc i)) = current_number (g (Suc j))\<close> if \<open>i \<ge> Suc j\<close> for i
      using that
      apply (induction rule:nat_induct_at_least)
      using le_Suc_eq mono n_mono apply auto[1]
      by (metis Suc_leD le_imp_less_Suc le_SucI mono n_mono)

    define f' where
      \<open>f' \<equiv> rec_nat (Suc j)
         (\<lambda>_ n. LEAST i. i > n \<and> current_restart_count (g (Suc i)) = Suc (current_restart_count (g i)))\<close>
    then have [simp]: \<open>f' 0 = Suc j\<close> and f_Suc: \<open>f' (Suc n) = (LEAST i. i > f' n \<and> current_restart_count (g (Suc i)) =
        Suc (current_restart_count (g i)))\<close> for n
      by auto
    let ?f' = \<open>\<lambda>i. g (f' i)\<close>
    have will_eventually_Restart:
      \<open>j' > j \<Longrightarrow> \<exists>ia>j'. current_restart_count (g (Suc ia)) \<noteq> (current_restart_count (g ia))\<close> for j'
      by (rule will_eventually_Restart)
       (use less_trans mono n_mono in blast)
    have will_eventually_Restart:
      \<open>\<exists>ia>j'. current_restart_count (g (Suc ia)) = Suc (current_restart_count (g ia))\<close> if \<open>j' > j\<close> for j'
      using will_eventually_Restart[of j', OF that] apply - apply normalize_goal+
      subgoal for x
        apply (rule_tac x=x in exI)
        using n_mono'[of x] mono[of ] that
        by auto
      done
    have
      f': \<open>current_restart_count (g (Suc (f' (Suc i)))) = Suc (current_restart_count (g (f' (Suc i)))) \<and>
        f' i < f' (Suc i) \<and> f' i > j\<close> for i
      apply (induction i)
      subgoal
        using will_eventually_Restart[of \<open>Suc j\<close>]
          wellorder_class.LeastI_ex[of \<open>\<lambda>j'. j' > Suc j \<and> current_restart_count (g (Suc j')) = Suc (current_restart_count (g j'))\<close>]
        unfolding f_Suc[symmetric]  \<open>f' 0 = Suc j\<close>[symmetric]
        by (auto)
      subgoal for i
        using will_eventually_Restart[of \<open>f' (Suc i)\<close>]
          wellorder_class.LeastI_ex[of \<open>\<lambda>j. j > f' (Suc i) \<and> current_restart_count (g (Suc j)) = Suc (current_restart_count (g j))\<close>]
        unfolding f_Suc[symmetric, of ]
        by (auto)
      done
    then have
      f': \<open>current_restart_count (g (Suc (f' (Suc i)))) = Suc (current_restart_count (g (f' (Suc i))))\<close> and
      fii: \<open>f' i < f' (Suc i)\<close> and
      fj: \<open>f' i > j\<close> for i
      by fast+

    have same_res: \<open>k < f' (Suc i) \<Longrightarrow> k > f' i \<Longrightarrow> last_restart_state (g (Suc (k))) = last_restart_state (g (k))\<close> for i k
      using wellorder_class.not_less_Least[of \<open>k\<close> \<open>\<lambda>j. j > f' (i) \<and> current_restart_count (g (Suc j)) = Suc (current_restart_count (g j))\<close>]
        g[of k] neq[of k] fj[of i] neq[of k] neq[of \<open>k - 1\<close>] unfolding f_Suc[symmetric]
      by (cases \<open>Suc j \<le> k - Suc 0\<close>) (auto elim!: pcdcl_stgy_restart.cases)
    have f'_less_diff[iff]: \<open>\<not> f' i < f' (Suc i) - Suc 0 \<longleftrightarrow> f' i = f' (Suc i) - Suc 0\<close> for i
      using fii[of i] by auto
    have same_res': \<open>k < f' (Suc i) \<Longrightarrow> k > f' i \<Longrightarrow> last_restart_state (g (Suc (k))) = last_restart_state (g (Suc (f' i)))\<close> for i k
      apply (induction "k - f' i" arbitrary: k)
      subgoal by auto
      subgoal premises p for x k
        using p(1)[of \<open>k - 1\<close>] p(2-)
        by (cases k; cases \<open>f' i < k\<close>)
          (auto simp: same_res less_Suc_eq_le Suc_diff_le order_class.order.order_iff_strict)
      done

    have tcore_stgy: \<open>k < f' (Suc i) \<Longrightarrow> k > f' i \<Longrightarrow> pcdcl_tcore_stgy (current_state (g k)) (current_state (g (Suc k)))\<close> for i k
      using same_res[of k i] neq[of \<open>k\<close>] fj[of i] g[of \<open>k\<close>] mono neq[of \<open>k - 1\<close>]
      by (subgoal_tac \<open>Suc j \<le> k - Suc 0\<close>)
        (auto simp: pcdcl_stgy_restart.simps elim: pcdcl_restart_only.cases)

    have tcore_stgy: \<open>k \<le> f' (Suc i) \<Longrightarrow> k \<ge> Suc (f' i) \<Longrightarrow> pcdcl_tcore_stgy\<^sup>*\<^sup>* (current_state (g (Suc (f' i)))) (current_state (g k))\<close> for i k
      apply (induction "k - Suc (f' i)" arbitrary: k)
      subgoal by auto
      subgoal premises p for x k
        using p(1)[of \<open>k-1\<close>] p(2-) tcore_stgy[of \<open>k-1\<close> i]
        by (cases k; cases \<open>f' i < k\<close>)
          (force simp: same_res less_Suc_eq_le Suc_diff_le order_class.order.order_iff_strict)+
      done
    have fii0: \<open>(f' i) \<le> f' (Suc i) - Suc 0\<close> for i
      using fii[of i] fj[of i] by auto
    have curr_last: \<open>current_state (g (Suc (f' (Suc i)))) = last_restart_state (g (Suc (f' (Suc i))))\<close> for i
      using f'[of i] g[of \<open>f' (Suc i)\<close>]
      by (auto elim!: pcdcl_stgy_restart.cases)
    have tcore_stgy': \<open>Suc (f' i) \<le> f' (Suc i) - Suc 0 \<Longrightarrow>pcdcl_tcore_stgy\<^sup>*\<^sup>* (current_state (g (Suc (f' i)))) (current_state (g (f' (Suc i) - 1)))\<close> for i
      using tcore_stgy[of \<open>f' (Suc i) - 1\<close> i] fii[of i] fii0[of i]
      by (auto)
    have [iff]: \<open>f' (Suc i) < f' (Suc i) - Suc 0 \<longleftrightarrow> False \<close> for i
      using fii[of i] by (cases \<open>f' (Suc i)\<close>) auto
    have tcore_stgy: \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* (current_state (g (Suc (f' i)))) (current_state (g (f' (Suc i))))\<close> for i
      using tcore_stgy[of \<open>f' (Suc i)\<close> i] fii[of i] fii0[of i]
      by (auto)
    moreover have
      \<open>size (pget_all_learned_clss (current_state (g (Suc (f' (Suc i)))))) < size (pget_all_learned_clss (current_state (g (f' (Suc (Suc i))))))\<close> and
      \<open>pcdcl_restart_only (current_state (g (f' (Suc (Suc i))))) (current_state (g (Suc (f' (Suc (Suc i))))))\<close> for i
      defer
      subgoal SS
        using f'[of \<open>Suc i\<close>] g[of \<open>f' (Suc (Suc i))\<close>] curr_last[of i, symmetric]
          same_res'[of \<open>f' (Suc i)\<close> \<open>Suc i\<close>]
          rtranclp_pcdcl_tcore_stgy_pget_all_learned_clss_mono[OF tcore_stgy[of \<open>Suc i\<close>]]
        apply (auto elim!: pcdcl_stgy_restart.cases simp: )
        done
      subgoal
        using f'[of \<open>Suc i\<close>] g[of \<open>f' (Suc (Suc i))\<close>] curr_last[of i, symmetric]
          same_res'[of \<open>f' (Suc (Suc i)) - 1\<close> \<open>Suc (i)\<close>] fii[of \<open>Suc i\<close>]
          rtranclp_pcdcl_tcore_stgy_pget_all_learned_clss_mono[OF tcore_stgy[of \<open>Suc i\<close>]]
        by (cases \<open>f' (Suc i) < f' (Suc (Suc i)) - Suc 0\<close>)
          (auto elim!: pcdcl_stgy_restart.cases simp: pcdcl_restart_only.simps)
      done
    ultimately have \<open>pcdcl_stgy_only_restart (current_state (g (Suc (f' (Suc i))))) (current_state (g (Suc (f' (Suc (Suc i))))))\<close> for i
      by (rule restart_noGC_stepI)
    moreover have \<open>pcdcl_all_struct_invs (current_state (g (Suc (f' (Suc i))))) \<and>
      cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of (current_state (g (Suc (f' (Suc i))))))\<close> for i
      using inv'_c inv_c by auto
    ultimately show False
      using wf_pcdcl_stgy_only_restart unfolding wf_iff_no_infinite_down_chain
      by fast
  qed


  define f' where \<open>f' \<equiv> rec_nat 0 (\<lambda>_ n. LEAST i. i > n \<and> current_number (g (Suc i)) = Suc (current_number (g i)))\<close>
  then have [simp]: \<open>f' 0 = 0\<close> and f_Suc: \<open>f' (Suc n) = (LEAST i. i > f' n \<and> current_number (g (Suc i)) =
      Suc (current_number (g i)))\<close> for n
    by auto
  let ?f' = \<open>\<lambda>i. g (f' i)\<close>
  have
    f': \<open>current_number (g (Suc (f' (Suc i)))) = Suc (current_number (g (f' (Suc i))))\<close> and
    fii: \<open>f' i < f' (Suc i)\<close> for i
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

  have in_between: \<open>f' (Suc i) + k < f' (Suc (Suc i)) \<Longrightarrow>
    current_number (g (Suc (f' (Suc i) + k))) =  current_number (g (Suc (f' (Suc i))))\<close> for k i
    apply (induction k)
    subgoal
      using H[of i 1] by auto
    subgoal for k
      using H[of i \<open>Suc k\<close>]
      by auto
    done

  have Hc: \<open>f' (Suc i) + Suc k \<le> f' (Suc (Suc i)) \<Longrightarrow>
    last_GC_state (g (Suc (f' (Suc i) + k))) = last_restart_state (g (Suc (f' (Suc i))))\<close> for k i
    apply (induction k)
    subgoal using f'[of i] g[of \<open>f' (Suc i)\<close>]
      by (auto simp: pcdcl_stgy_restart.simps)
    subgoal for k
      using H[of i \<open>Suc k\<close>] g[of \<open>f' (Suc i) + Suc k\<close>] unfolding f_Suc[symmetric]
      by (auto simp: pcdcl_stgy_restart.simps)
    done

  have [simp]: \<open>f' (Suc (Suc i)) \<ge> Suc (Suc 0)\<close> for i
    by (metis (full_types) antisym_conv fii not_le not_less_eq_eq zero_less_Suc)

  have in_between_last_GC_state: \<open>
    last_GC_state (g ((f' (Suc (Suc i))))) =  last_restart_state (g (Suc (f' (Suc i))))\<close> for i
    apply (cases \<open>f' (Suc (Suc i)) \<ge> Suc (Suc (f' (Suc i)))\<close>)
    using Hc[of i \<open>f' (Suc (Suc i)) - f' (Suc i) - Suc (0)\<close>] fii[of \<open>Suc i\<close>] fii[of i]
    by (auto simp: Suc_diff_Suc antisym_conv not_less_eq_eq)

  have f'_steps: \<open>current_number (g ((f' (Suc (Suc i))))) = 1 + current_number (g ((f' (Suc i))))\<close> for i
    using f'[of \<open>Suc i\<close>] f'[of \<open>i\<close>] in_between[of i \<open>f' (Suc (Suc i)) - f' (Suc i) - 1\<close>]
    apply (cases \<open>f' (Suc (Suc i)) - Suc (f' (Suc i)) = 0\<close>)
    apply auto
    by (metis Suc_lessI f' fii leD)
  have snd_f'_0: \<open>current_number (g ((f' (Suc (Suc i))))) =  Suc i + current_number (g ((f' (Suc 0))))\<close> for i
    apply (induction i)
    subgoal
      using f'_steps[of 0] by auto
    subgoal for i
      using f'_steps[of \<open>Suc i\<close>]
      by auto
    done
  have gstar: \<open>j \<ge> i \<Longrightarrow> pcdcl_stgy_restart\<^sup>*\<^sup>* (g i) (g j)\<close> for i j
    apply (induction "j - i" arbitrary: i j)
    subgoal by auto
    subgoal
      by (metis (no_types, lifting) Suc_diff_Suc Suc_leI diff_Suc_1 g r_into_rtranclp
        rtranclp.rtrancl_into_rtrancl rtranclp_idemp zero_less_Suc zero_less_diff)
    done
  have f'star: \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* (g (f' i + 1)) (?f' (Suc i))\<close> for i
    by (rule gstar)
     (use fii in \<open>auto simp: Suc_leI\<close>)

  have curr_last[simp]: \<open>(current_state (g (Suc (f' (Suc i))))) = (last_restart_state (g (Suc (f' (Suc i)))))\<close> for i
    using g[of \<open>f' (Suc i)\<close>] f'[of i]
      by (auto simp: pcdcl_stgy_restart.simps)
  have size_clss:
     \<open>size (pget_all_learned_clss (current_state (g (f' (Suc (Suc i))))) - pget_all_learned_clss (current_state (g (Suc (f' (Suc i))))))
    \<le> 4 ^ card (atms_of_mm (pget_all_init_clss (current_state (g (f' (Suc i) + 1)))))\<close> for i
    by (rule rtranclp_pcdcl_stgy_restart_bound_size[OF f'star])
      (auto simp: restart_inv f' f'_steps)

  have \<open>atms_of_mm (pget_all_init_clss (fst (g (Suc i)))) = atms_of_mm (pget_all_init_clss (fst (g i)))\<close> for i
    using pcdcl_stgy_restart_pget_all_init_clss[OF g[of i]]
    by (metis inv_c rest_decomp rest_decomp2 rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss
      rtranclp_pcdcl_tcore_stgy_pget_all_init_clss)
  then have atms_init[simp]: \<open>NO_MATCH 0 i \<Longrightarrow>
      atms_of_mm (pget_all_init_clss (fst (g i))) = atms_of_mm (pget_all_init_clss (fst (g 0)))\<close> for i
    by (induction i) auto
  {
     fix i
    have
      bound: \<open>f (current_number (?f' (Suc (Suc i)))) + size (pget_all_learned_clss (last_GC_state (?f' (Suc (Suc i)))))
         < size (pget_all_learned_clss (current_state (?f' (Suc (Suc i)))))\<close>
      using g[of \<open>f' (Suc (Suc i))\<close>] f'(1)[of \<open>Suc i\<close>]
      by (auto elim!: pcdcl_stgy_restart.cases)
    then have \<open>f (current_number (?f' (Suc (Suc i)))) < size (pget_all_learned_clss (current_state (?f' (Suc (Suc i))))) - size (pget_all_learned_clss (last_GC_state (?f' (Suc (Suc i)))))\<close>
      by linarith
    also have \<open>... \<le> size (pget_all_learned_clss (current_state (?f' (Suc (Suc i)))) - pget_all_learned_clss (last_GC_state (?f' (Suc (Suc i)))))\<close>
      using diff_size_le_size_Diff by blast
    also have \<open>... \<le> 4 ^ card (atms_of_mm (pget_all_init_clss (current_state (g (f' (Suc i) + 1)))))\<close>
      using size_clss[of i]
      by (auto simp: f'_steps f' in_between_last_GC_state)

  finally have
    bound: \<open>f (current_number (?f' (Suc (Suc i)))) < 4 ^ card (atms_of_mm (pget_all_init_clss (current_state (g 0))))\<close>
    apply auto
    by (metis NO_MATCH_def atms_init rest_decomp rest_decomp2
      rtranclp_pcdcl_stgy_only_restart_pget_all_init_clss rtranclp_pcdcl_tcore_stgy_pget_all_init_clss)
  } note bound = this[]
  moreover have \<open>unbounded (\<lambda>n. f (current_number (g (f' (Suc (Suc n))))))\<close>
    unfolding bounded_def
    apply clarsimp
    subgoal for b
      using not_bounded_nat_exists_larger[OF f, of b \<open>((current_number (g (f' (Suc (Suc 0))))))\<close>] apply -
      apply normalize_goal+
      apply (rename_tac n, rule_tac x = \<open>n - (Suc (current_number (g (f' ((Suc 0))))))\<close> in exI)
      by (auto simp: snd_f'_0 intro: exI[of _ \<open>_ - (Suc (current_number (g (f' ((Suc 0))))))\<close>])
    done
  ultimately show False
    using le_eq_less_or_eq unfolding bounded_def by blast
qed

end

end