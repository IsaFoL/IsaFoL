theory Pragmatic_CDCL_MR
  imports Pragmatic_CDCL Model_Reconstruction.Inprocessing_Rules
begin

text \<open>In this function lies an interesting design choice (that we might change in the future).
We use the support set of all possible variables only as set for variable unlike the CDCL case
where we actually also used it to generate a big tautology.

This avoids the problem of wondering whether we need to resolve with the tautology. But we have to
be careful because the two calculi have a different opinion on what the state is. The other consequence
is that we probably do not need to have a tautology on all literals, one would be enough. But I 
have realized that only when starting the proofs here.
\<close>
fun to_mr_state :: \<open>'v prag_st \<times> 'v stackWit \<Rightarrow> 'v clauses \<times> 'v clauses \<times> 'v stackWit \<times> 'v set\<close> where
  \<open>to_mr_state ((M, N, U, D, NE, UE, N0, U0, \<A>), S) = (N + NE + N0, U + UE + U0, S, set_mset \<A> \<union> atms_of_ms (wit_clause ` set S))\<close>

lemma to_mr_state_alt_def:
  \<open>to_mr_state ( (S,T)) = (pget_all_init_clss_strict S, pget_all_learned_clss S, T,
  set_mset (pget_support_set S) \<union> atms_of_ms (wit_clause ` set T))\<close>
  by (cases S) auto

lemma pcdcl_all_struct_invs_proper_support_set_all:
  assumes \<open>pcdcl_all_struct_invs S\<close>
  shows \<open>atms_of_mm (pget_all_init_clss S + pget_all_learned_clss S) = set_mset (pget_support_set S)\<close>
proof -
  have proper: \<open>proper_support_set S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state_of S)\<close>
    using assms(1) unfolding pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>atms_of_mm (pget_all_learned_clss S) \<subseteq> atms_of_mm (pget_all_init_clss S)\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases S) auto
  then show ?thesis
    using proper unfolding proper_support_set_def by auto
qed
 
lemma cdcl_backtrack_inp_mr:
  assumes \<open>cdcl_backtrack V W\<close> and \<open>pcdcl_all_struct_invs V\<close>
  shows \<open>inp_mr (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  using assms
proof (cases rule: cdcl_backtrack.cases)
  case (1 K M1 M2 M L D' i D \<A> N U NE UE N0 U0)
  moreover have \<open>insert (atm_of L) (atms_of D' \<union>
    (set_mset \<A> \<union> (atms_of_mm N0 \<union> (atms_of_mm NE \<union> (atms_of_mm N \<union> (atms_of_mm U0 \<union>
    (atms_of_mm UE \<union> (atms_of_mm U \<union> atms_of_ms (wit_clause ` set S))))))))) =  set_mset \<A> \<union> atms_of_ms (wit_clause ` set S)\<close>
  proof -
    have \<open>pcdcl_all_struct_invs W\<close>
      using assms(1) assms(2) pcdcl.intros(1) pcdcl_all_struct_invs pcdcl_core.intros(6) by blast
    from pcdcl_all_struct_invs_proper_support_set_all[OF this] show ?thesis
      unfolding 1 by auto
  qed
  moreover have \<open>L \<notin># D'\<close>
    using assms(2) 1(8) unfolding 1
    by (auto simp: cdcl_backtrack.simps ac_simps pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.clauses_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      intro: learn_minus dest!: multi_member_split)
  moreover have \<open>set_mset N0 \<union> (set_mset NE \<union> (set_mset N \<union> (set_mset U0 \<union> (set_mset UE \<union> set_mset U)))) \<Turnstile>p
    add_mset L D'\<close>
    by (smt (verit, del_insts) ab_semigroup_add_class.add_ac(1) add.commute add.left_commute
      calculation(9) make_big_tautology_true_clss_cls_iff_mset set_mset_union)
  ultimately show ?thesis
    using learn_minus[of "pget_all_init_clss_strict V" "pget_all_learned_clss V" "add_mset L D'" S "set_mset \<A>"] 1
      distinct_mset_mono[of D' D] assms(2)
    by (auto simp: cdcl_backtrack.simps ac_simps pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.clauses_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      intro: learn_minus dest!: multi_member_split)
qed


lemma pcdcl_core_inp_mr:
  \<open>pcdcl_core V W \<Longrightarrow> pcdcl_all_struct_invs V \<Longrightarrow> inp_mr\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  apply (cases rule: pcdcl_core.cases, assumption)
  subgoal
    by (auto simp: cdcl_conflict.simps ac_simps pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      intro: learn_minus dest!: multi_member_split)
  subgoal
    by (auto simp: cdcl_propagate.simps)
  subgoal
    by (auto simp: cdcl_decide.simps)
  subgoal
    by (auto simp: cdcl_skip.simps)
  subgoal
    by (auto simp: cdcl_resolve.simps)
  subgoal
    using cdcl_backtrack_inp_mr[of V W S] by auto
  done

lemma cdcl_resolution_inp_mr: 
  assumes \<open>cdcl_resolution V W\<close>
    \<open>pcdcl_all_struct_invs V\<close>
  shows \<open>inp_mr\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
proof -
  have inv_W: \<open>pcdcl_all_struct_invs W\<close>
    using assms(1) assms(2) pcdcl.intros(3) pcdcl_all_struct_invs by blast
  show ?thesis
    using assms
  proof (cases rule: cdcl_resolution.cases)
    case (resolution_LL M C C' N U L D NE UE N0 U0 \<A>) note V = this(1) and W = this(2) and _ = this(3)
    have \<open>insert (add_mset L C)
      (insert (add_mset (- L) C')
      (set_mset N \<union> set_mset NE \<union> set_mset N0 \<union>
      (set_mset U \<union> set_mset UE \<union> set_mset U0))) \<Turnstile>p
      C' + C\<close>
      using resolution_LL true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss_strict V + pget_all_learned_clss V)\<close> L C' C]
      by auto
    then have R: \<open>inp_mr (pget_all_init_clss_strict V, pget_all_learned_clss V, S, set_mset (pget_support_set V) \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
      atms_of_mm (pget_all_learned_clss V) \<union>
      atms_of_mm (wit_clause `# mset S))
      (pget_all_init_clss_strict V, add_mset (remdups_mset (C + C')) (pget_all_learned_clss V), S, set_mset (pget_support_set V) \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
      atms_of_mm (pget_all_learned_clss V) \<union>
      atms_of_mm (wit_clause `# mset S))\<close>
      using learn_minus[of \<open>pget_all_init_clss_strict V\<close> \<open>pget_all_learned_clss V\<close> \<open>remdups_mset (C+C')\<close> S \<open>set_mset (pget_support_set V)\<close>]
      by (auto simp: V W ac_simps)
    have \<open>inp_mr (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
      apply (rule arg_cong2[where f = inp_mr, THEN iffD2, OF _ _ R])
      subgoal using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: W V)
      subgoal using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: W V)
      done
    then show ?thesis by blast
  next
    case (resolution_II M N L C C' U D NE UE N0 U0 \<A>) note V = this(1) and W = this(2) and _ = this(3)
    have \<A>1: \<open>insert (atm_of L) (atms_of C' \<union> (atms_of C \<union> (set_mset \<A> \<union> (atms_of_mm N0 \<union> (atms_of_mm NE \<union> (atms_of_mm N \<union> (atms_of_mm U0 \<union> (atms_of_mm UE \<union> (atms_of_mm U \<union> atms_of_ms (wit_clause ` set S)))))))))) = set_mset \<A>  \<union> atms_of_ms (wit_clause ` set S)\<close> and
      \<A>2: \<open>insert (atm_of L)
      (atms_of C' \<union>
      (atms_of C \<union>
      (set_mset \<A> \<union>
      (atms_of_mm N0 \<union> (atms_of_mm NE \<union> (atms_of_mm N \<union> (atms_of_mm U0 \<union> (atms_of_mm UE \<union> (atms_of_mm U \<union> atms_of_ms (wit_clause ` set S)))))))))) = set_mset \<A>  \<union> atms_of_ms (wit_clause ` set S)\<close>
      using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: W V)
    have \<open>insert (add_mset L C) (insert (add_mset (- L) C') (set_mset N0 \<union> (set_mset NE \<union>
      (set_mset N \<union> (set_mset U0 \<union> (set_mset UE \<union> set_mset U)))))) \<Turnstile>p C' + C\<close>
      using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss_strict V + pget_all_learned_clss V)\<close> L C' C]
      by (auto simp: V ac_simps)
    then have \<open>insert (add_mset L C) (insert (add_mset (- L) C') (set_mset N0 \<union> (set_mset NE \<union>
      (set_mset N \<union> (set_mset U0 \<union> (set_mset UE \<union> set_mset U)))))) \<Turnstile>p
      C' + C\<close>
      using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss V + pget_all_learned_clss V)\<close> L C' C]
      by auto
    then have R: \<open>inp_mr (to_mr_state (V, S))
      (pget_all_init_clss_strict V, add_mset (remdups_mset (C + C')) (pget_all_learned_clss V), S, set_mset \<A> \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss_strict V) \<union>
      atms_of_mm (pget_all_learned_clss V) \<union>
      atms_of_mm (wit_clause `# mset S))\<close> (is \<open>inp_mr ?A ?B\<close>)
      using learn_minus[of \<open>pget_all_init_clss_strict V\<close> \<open>pget_all_learned_clss V\<close> \<open>remdups_mset (C+C')\<close> S \<open>set_mset \<A>\<close>] \<A>1
      by (auto simp: V W ac_simps)
    moreover have R: \<open>inp_mr ?B
      ( add_mset (remdups_mset (C + C')) (pget_all_init_clss_strict V),(pget_all_learned_clss V), S, set_mset \<A> \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss_strict V) \<union>
      atms_of_mm (pget_all_learned_clss V) \<union>
      atms_of_mm (wit_clause `# mset S))\<close> (is \<open>inp_mr _ ?C\<close>)
      using strenghten[of \<open>pget_all_init_clss_strict V\<close>  \<open>remdups_mset (C+C')\<close>  \<open>pget_all_learned_clss V\<close> S \<open>set_mset \<A>\<close>] \<A>2
      by (auto simp: V W ac_simps)
    moreover have \<open> ?C = (to_mr_state (W, S))\<close>
      using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: V W ac_simps)
    ultimately show \<open>inp_mr\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
      by auto
  next
    case (resolution_IL M C C' N L U D NE UE N0 U0 \<A>) note V = this(1) and W = this(2) and _ = this(3)
    have \<A>1: \<open>insert (atm_of L)
      (atms_of C' \<union>
      (atms_of C \<union>
      (set_mset \<A> \<union>
      (atms_of_mm N0 \<union> (atms_of_mm NE \<union> (atms_of_mm N \<union> (atms_of_mm U0 \<union> (atms_of_mm UE \<union> (atms_of_mm U \<union> atms_of_ms (wit_clause ` set S)))))))))) = set_mset \<A> \<union> atms_of_ms (wit_clause ` set S)\<close>
      using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: W V)
    have \<open>insert (add_mset (-L) C')
      (insert (add_mset L C)
      (set_mset N \<union> set_mset NE \<union> set_mset N0 \<union>
      (set_mset U \<union> set_mset UE \<union> set_mset U0))) \<Turnstile>p
      C' + C\<close>
      using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss V + pget_all_learned_clss V)\<close> L C' C] resolution_IL
      by (meson insertCI true_clss_cls_in true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or)
    then have R: \<open>inp_mr (pget_all_init_clss_strict V, pget_all_learned_clss V, S, set_mset \<A> \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss_strict V) \<union>
      atms_of_mm (pget_all_learned_clss V) \<union>
      atms_of_mm (wit_clause `# mset S))
      (pget_all_init_clss_strict V, add_mset (remdups_mset (C + C')) (pget_all_learned_clss V), S, set_mset \<A> \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss_strict V) \<union>
      atms_of_mm (pget_all_learned_clss V) \<union>
      atms_of_mm (wit_clause `# mset S))\<close>
      using learn_minus[of \<open>pget_all_init_clss_strict V\<close> \<open>pget_all_learned_clss V\<close> \<open>remdups_mset (C+C')\<close> S \<open>set_mset \<A>\<close>]
        \<A>1
      by (auto simp: V W ac_simps)
    have \<open>inp_mr (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
      apply (rule arg_cong2[where f = inp_mr, THEN iffD2, OF _ _ R])
      subgoal using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: V W)
      subgoal using pcdcl_all_struct_invs_proper_support_set_all[OF inv_W] by (auto simp: W V)
      done
    then show ?thesis by blast
  qed
qed

lemma consistent_interp_diffI: "consistent_interp I \<Longrightarrow> consistent_interp (I - A)"
  by (metis Diff_iff consistent_interp_def)


text \<open>
Learning a pure literal as we did in the CADE'29 paper is sadly not compatible with our
transition system. In essence, we could force it to make it compatible by enforcing that in
every step \<^term>\<open>N  \<Turnstile>psm U\<close>, but this would not be compatible with the invariants. Only the invariant
\<^term>\<open>(N + wit_clause `# mset S) \<Turnstile>psm U\<close> holds\<dots> but if we do that, we also need to check for conflicts
in the witness.

The counter-example is easy: Learn the clause \<^term>\<open>L\<close> where  \<^term>\<open>L\<close> is a fresh literal, put  \<^term>\<open>L\<close> in the
set of learned clauses. Then put  \<^term>\<open>L\<close> to the reconstruction stack\<dots> and you can learn  \<^term>\<open>-L\<close> again.
\<close>
instance nat :: numeral

  term "3 :: nat"
ML \<open>@{term \<open>3::int\<close>}\<close>
term numeral
thm pred_numeral_Suc
lemma "a - b - 2 \<le> 0" for a b :: nat
  supply [[smt_nat_as_int,smt_trace]]
    apply smt
lemma
  assumes \<open>cdcl_pure_literal_remove V W\<close> \<open>pcdcl_all_struct_invs V\<close>
  shows \<open>inp_mr (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  using assms(1)
proof (cases)
  case (cdcl_pure_literal_remove L N \<A> NE N0 M U UE U0) note S = this(1) and T = this(2) and
    L = this(3,4) and undef = this(5) and lev0 = this(6)
  have
    ent: \<open>entailed_clss_inv V\<close> and
    clss0: \<open>clauses0_inv V\<close> and
    struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of V)\<close>
    using assms(2) unfolding pcdcl_all_struct_invs_def by fast+
      
  have \<open>satisfiable (insert {#L#} (set_mset (pget_all_init_clss V) \<union> set_mset (pget_all_learned_clss V)))\<close>
    if sat: \<open>satisfiable (set_mset (pget_all_init_clss V) \<union> set_mset (pget_all_learned_clss V))\<close>
  proof -
    obtain I where
      cons: \<open>consistent_interp I\<close> and
      IS: \<open>I \<Turnstile>sm pget_all_init_clss V + pget_all_learned_clss V\<close> and
      tot: \<open>total_over_m I (set_mset (pget_all_init_clss V) \<union> set_mset (pget_all_learned_clss V))\<close>
      using sat unfolding satisfiable_def by blast
    let ?J = \<open>insert L (I - {-L})\<close>
    have cons2: \<open>consistent_interp ?J\<close>
      using cons
      by (metis Diff_empty Diff_iff Diff_insert0 consistent_interp_insert_iff insert_Diff singletonI)

    have \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state_of V))
      (get_all_ann_decomposition (trail (state_of V)))\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state_of V)\<close>
      using struct_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>set_mset (pget_all_init_clss V + pget_all_learned_clss V) \<Turnstile>ps unmark_l M\<close>
      using tot lev0 by (auto simp: S clauses_def count_decided_0_iff
        no_decision_get_all_ann_decomposition)
    moreover have \<open>total_over_m I (unmark_l M)\<close>
      using alien tot by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def S
        total_over_m_def total_over_set_def)
    ultimately have \<open>I \<Turnstile>s unmark_l M\<close>
      using IS tot cons by (auto simp: S true_clss_clss_def)
    then have \<open>lits_of_l M \<subseteq> I\<close>
      by (auto simp: true_clss_def lits_of_def)
    have IN: \<open>I \<Turnstile>m N\<close> and \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m NE\<close>
      using IS by (auto simp: S)
    have totJ: \<open>total_over_m ?J (set_mset (pget_all_init_clss W)\<union> set_mset (pget_all_learned_clss W))\<close>
      using tot apply (auto simp: total_over_m_def S T total_over_set_alt_def
        uminus_lit_swap)
      apply (metis atm_of_uminus literal.sel)+
      done
    have \<open>?J \<Turnstile>m N\<close>
      using IN L by (clarsimp simp: true_cls_mset_def add_mset_eq_add_mset true_cls_def
        dest!: multi_member_split)
    moreover have \<open>?J \<Turnstile>m NE\<close>
      using ent \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m NE\<close> totJ L(1) undef \<open>lits_of_l M \<subseteq> I\<close>
      apply (auto simp: entailed_clss_inv_def S true_cls_mset_def T Decided_Propagated_in_iff_in_lits_of_l
        dest!: multi_member_split[of \<open>_ :: _ clause\<close>])
      unfolding true_cls_def[of ]
      apply clarsimp
      apply (rule_tac x=La in bexI)
      by auto
    moreover have \<open>?J \<Turnstile>m N0\<close>
      using ent \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m NE\<close> totJ L undef clss0
      by (auto simp: entailed_clss_inv_def S true_cls_mset_def T Decided_Propagated_in_iff_in_lits_of_l
        clauses0_inv_def
        dest!: multi_member_split)
    moreover have \<open>?J \<Turnstile>m U\<close>
      using IS apply auto
      sorry
    moreover have \<open>?J \<Turnstile>m UE\<close> \<open>?J \<Turnstile>m U0\<close>
      sledgehammer
      sorry
    ultimately have \<open>?J \<Turnstile>sm pget_all_init_clss W + pget_all_learned_clss W\<close>
      using ent by (auto simp: S T)

    then show ?thesis
      using cons2 unfolding S T  by auto
  qed
  moreover have \<open>insert (atm_of L)
          (atms_of_mm N \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0 \<union>
        (atms_of_mm U \<union> atms_of_mm UE \<union> atms_of_mm US \<union> atms_of_mm U0) \<union>
        atms_of_ms (wit_clause ` set S)) = 
          (atms_of_mm N \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0 \<union>
        (atms_of_mm U \<union> atms_of_mm UE \<union> atms_of_mm US \<union> atms_of_mm U0) \<union>
        atms_of_ms (wit_clause ` set S))\<close>
    using L by auto
  ultimately show \<open>?thesis\<close>
    using inp_mr.learn_plus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> \<open>{#L#}\<close> S \<open>{}\<close>]
    by (auto intro: consistent_interp_diffI simp: S T to_mr_state_alt_def)
qed


lemma pcdcl_inp_mr:
  \<open>pcdcl V W \<Longrightarrow> pcdcl_all_struct_invs V \<Longrightarrow> inp_mr\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  apply (cases rule: pcdcl.cases, assumption)
  subgoal by (rule pcdcl_core_inp_mr)
  subgoal
    apply (cases rule: cdcl_learn_clause.cases, assumption)
    subgoal for C N NE NS N0 M U D UE US U0
      apply (rule r_into_rtranclp)
      using learn_minus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> C S \<open>{}\<close>]
      apply (auto simp: )
      by (smt (verit, del_insts) Un_absorb1 Un_assoc atms_of_ms_union learn_plus multiset.set_map sat set_mset_mset set_mset_union union_mset_add_mset_right)
    subgoal for C N NE NS N0 M U D UE US U0
      apply (rule r_into_rtranclp)
      using learn_minus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> C S \<open>{}\<close>]
      apply (auto simp: )
      by (smt (verit, del_insts) Un_absorb1 Un_assoc atms_of_ms_union learn_plus multiset.set_map sat set_mset_mset set_mset_union union_mset_add_mset_right)
    subgoal for C M N U D NE UE NS US N0 U0
      apply (rule r_into_rtranclp)
      using strenghten[of \<open>pget_all_init_clss V\<close> C \<open>pget_all_learned_clss V - {#C#}\<close> S \<open>{}\<close>]
      by (auto simp: pcdcl_all_struct_invs_def ac_simps pcdcl_all_struct_invs_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset.no_strange_atm_def)
    done
  subgoal by (rule cdcl_resolution_inp_mr)
  subgoal by (auto simp: cdcl_subsumed.simps Un_left_commute add_mset_commute)
  subgoal by (auto simp: cdcl_flush_unit.simps)
  subgoal by (auto simp: cdcl_inp_propagate.simps)
  subgoal by (auto simp: cdcl_inp_conflict.simps)
  subgoal by (auto simp: cdcl_unitres_true.simps)
  subgoal by (auto simp: cdcl_promote_false.simps)
  subgoal
    
    sorry
(*does not hold without the Ns \<Turnstile> Us which we do not really want to add as assumptiom*)
    oops

text \<open>
This is an attempt to create a rule derived from our inprocessing inp_mr back to our cdcl:

  \<^item> \<^term>\<open>add_mset (add_mset (-L) C)\<close> is on purpose a tautology to make sure that we do not lose variables. Although

\<close>
inductive cdcl_weaken :: \<open>'v prag_st \<times> 'v stackWit  \<Rightarrow> 'v prag_st \<times> 'v stackWit \<Rightarrow> bool\<close> where
weaken:
  \<open>cdcl_weaken ((M, add_mset C N, U, None, NE, UE, NS, US, N0, U0), S)
    ((M, N, U, None, add_mset (add_mset (-L) C) NE, UE, NS, US, N0, U0), S @ [Witness I C])\<close>
  if
    "I \<Turnstile> C"  and "redundancy (N+NE+NS+N0) C I (N+NE+NS+N0)" and "consistent_interp I " and
    "atm_of ` I \<subseteq> atms_of_mm (add_mset C N+NE+NS+N0) \<union> atms_of_mm (U+UE+US+U0) \<union> atms_of_mm (wit_clause `# mset S)" and
    \<open>L \<in># C\<close>and
    \<open>-L \<notin># C\<close>

lemma
  assumes \<open>cdcl_weaken (V, S) (W, T)\<close> \<open>pcdcl_all_struct_invs V\<close>
  shows
    \<open>pcdcl_all_struct_invs W\<close> and
    \<open>inp_mr\<^sup>*\<^sup>*  (to_mr_state (V, S)) (to_mr_state (W, T))\<close>
  using assms
proof (induct rule: cdcl_weaken.cases)
  case (weaken I C N NE NS N0 U UE US U0 S' L M)
  have
    V: \<open>V = (M, add_mset C N, U, None, NE, UE, NS, US, N0, U0)\<close> and
    S': \<open>S' = S\<close> and
    W: \<open>W = (M, N, U, None, add_mset (add_mset (-L) C) NE, UE, NS, US, N0, U0)\<close> and
    T: \<open>T = S @ [Witness I C]\<close> and
    LC: \<open>L \<in># C\<close> \<open>-L \<notin># C\<close>
    using weaken by auto
  let ?D = \<open>add_mset (-L) C\<close>
  have tauto_D: \<open>tautology ?D\<close>
    using weaken by (auto dest!: multi_member_split[of L C] simp: tautology_add_mset)
  have dist: \<open>distinct_mset C\<close>
    sorry
  case 1
  then show ?case using weaken apply auto sorry

  case 2
  let ?T = \<open>(M, add_mset C N, U, None, NE, add_mset (add_mset (-L) C) UE, NS, US, N0, U0)\<close>
  have \<open>set_mset N \<union> set_mset NE \<union> set_mset NS \<union> set_mset N0 \<union> (set_mset U \<union> set_mset UE \<union> set_mset US \<union> set_mset U0) \<Turnstile>p add_mset (- L) C\<close>
    by (meson consistent_CNot_not_tautology tauto_D total_not_CNot total_over_m_union true_clss_cls_def)
  moreover have [simp]: \<open>insert (atm_of L) (atms_of C \<union> \<V>) =
    (atms_of C \<union> \<V>)\<close> for \<V>
    using LC by (auto dest!: multi_member_split)
  ultimately have 1: \<open>inp_mr (to_mr_state (V, S)) (to_mr_state (?T, S))\<close>
    using tauto_D learn_minus[of \<open>(add_mset C N+NE+NS+N0)\<close> \<open>U+UE+US+U0\<close> \<open>add_mset (-L) C\<close> S \<open>{}\<close>] LC dist
    by (auto simp: V T add_mset_commute ac_simps)

  let ?U = \<open>(M, add_mset C N, U, None, add_mset (add_mset (-L) C) NE, UE, NS, US, N0, U0)\<close>
  have 2: \<open>inp_mr (to_mr_state (?T, S)) (to_mr_state (?U, S))\<close>
    using strenghten[of \<open>(add_mset C N+NE+NS+N0)\<close>  \<open>add_mset (-L) C\<close>  \<open>U+UE+US+U0\<close>  S \<open>{}\<close>]
    by (auto simp: inp_mr.simps)

  have \<open>redundancy (add_mset (add_mset (-L) C) N+NE+NS+N0) C I (add_mset (add_mset (-L) C) N+NE+NS+N0)\<close>
    using weaken apply auto unfolding redundancy_def apply auto
    sorry
  then have H: \<open>inp_mr
  (add_mset C (add_mset (add_mset (- L) C) N + NE + NS + N0), U + UE + US + U0, S,
   {} \<union> atms_of C \<union> atms_of_mm (add_mset (add_mset (- L) C) N + NE + NS + N0) \<union> atms_of_mm (U + UE + US + U0) \<union>
   atms_of_mm (wit_clause `# mset S))
  (add_mset (add_mset (- L) C) N + NE + NS + N0, U + UE + US + U0, S @ [Witness I C],
   {} \<union> atms_of C \<union> atms_of_mm (add_mset (add_mset (- L) C) N + NE + NS + N0) \<union> atms_of_mm (U + UE + US + U0) \<union>
    atms_of_mm (wit_clause `# mset S))\<close>
   apply -
   apply (rule inp_mr.weakenp[of I C  \<open>(add_mset (add_mset (-L) C) N+NE+NS+N0)\<close> \<open>{}\<close> \<open>U+UE+US+U0\<close> S])
   using weaken by auto
  have 3: \<open>inp_mr (to_mr_state (?U, S)) (to_mr_state (W, T))\<close>
    by (rule arg_cong2[of _ _ _ _ inp_mr, THEN iffD1, OF _ _ H])
      (auto simp: V S' W T ac_simps)
    
  then show ?case
    using weaken apply auto 
    sorry
qed
  oops
(*this will get tricky here*)
end
