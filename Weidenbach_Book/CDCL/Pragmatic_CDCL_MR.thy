theory Pragmatic_CDCL_MR
  imports Pragmatic_CDCL Model_Reconstruction.Inprocessing_Rules
begin

fun to_mr_state :: \<open>'v prag_st \<times> 'v stackWit \<Rightarrow> 'v clauses \<times> 'v clauses \<times> 'v stackWit \<times> 'v set\<close> where
  \<open>to_mr_state ((M, N, U, D, NE, UE, NS, US, N0, U0), S) = (N + NE + NS + N0, U + UE + US + U0, S, atms_of_mm (N + NE + NS + N0 + U + UE + US + U0) \<union> atms_of_ms (wit_clause ` set S))\<close>

lemma to_mr_state_alt_def:
  \<open>to_mr_state ( (S,T)) = (pget_all_init_clss S, pget_all_learned_clss S, T,
  atms_of_mm (pget_all_init_clss S) \<union>  atms_of_mm (pget_all_learned_clss S) \<union> atms_of_ms (wit_clause ` set T))\<close>
  by (cases S) auto

lemma cdcl_backtrack_rules:
  assumes \<open>cdcl_backtrack V W\<close> and \<open>pcdcl_all_struct_invs V\<close>
  shows \<open>rules (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  using assms
proof (cases rule: cdcl_backtrack.cases)
  case (1 K M1 M2 M L D' i D N U NE UE NS US N0 U0)
  moreover have \<open>insert (atm_of L)
     (atms_of D' \<union>
      (atms_of_mm N0 \<union>
    (atms_of_mm NE \<union>
     (atms_of_mm NS \<union>
      (atms_of_mm N \<union>
       (atms_of_mm U0 \<union>
    (atms_of_mm UE \<union> (atms_of_mm US \<union> (atms_of_mm U \<union> atms_of_ms (wit_clause ` set S)))))))))) =
      (atms_of_mm N0 \<union>
    (atms_of_mm NE \<union>
     (atms_of_mm NS \<union>
      (atms_of_mm N \<union>
       (atms_of_mm U0 \<union>
    (atms_of_mm UE \<union> (atms_of_mm US \<union> (atms_of_mm U \<union> atms_of_ms (wit_clause ` set S)))))))))\<close>
    using assms(2) 1 distinct_mset_mono[of D' D] distinct_subseteq_iff[of D' D, THEN iffD2]
    by (auto simp: cdcl_backtrack.simps ac_simps pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      intro: learn_minus dest!: multi_member_split)
      (metis (no_types, lifting) UnE distinct_subseteq_iff lits_subseteq_imp_atms_subseteq subsetD)+
  moreover have \<open>L \<notin># D'\<close>
    using assms(2) 1(8) unfolding 1
    by (auto simp: cdcl_backtrack.simps ac_simps pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.clauses_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      intro: learn_minus dest!: multi_member_split)
  ultimately show ?thesis
    using learn_minus[of "pget_all_init_clss V" "pget_all_learned_clss V" "add_mset L D'" S "{}"] 1
      distinct_mset_mono[of D' D] assms(2)
    by (auto simp: cdcl_backtrack.simps ac_simps pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.clauses_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      intro: learn_minus dest!: multi_member_split)
qed


lemma pcdcl_core_rules:
  \<open>pcdcl_core V W \<Longrightarrow> pcdcl_all_struct_invs V \<Longrightarrow> rules\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
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
    using cdcl_backtrack_rules[of V W S] by auto
  done

lemma cdcl_resolution_rules: 
  assumes \<open>cdcl_resolution V W\<close>
    \<open>pcdcl_all_struct_invs V\<close>
  shows \<open>rules\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  using assms
proof (cases rule: cdcl_resolution.cases)
  case (resolution_LL M C C' N U L D NE UE NS US N0 U0) note V = this(1) and W = this(2) and _ = this(3)
  then have \<open>insert (add_mset L C)
   (insert (add_mset (- L) C')
     (set_mset N \<union> set_mset NE \<union> set_mset NS \<union> set_mset N0 \<union>
      (set_mset U \<union> set_mset UE \<union> set_mset US \<union> set_mset U0))) \<Turnstile>p
    C' + C\<close>
    using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss V + pget_all_learned_clss V)\<close> L C' C]
    by auto
  then have R: \<open>rules (pget_all_init_clss V, pget_all_learned_clss V, S, {} \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
    atms_of_mm (pget_all_learned_clss V) \<union>
    atms_of_mm (wit_clause `# mset S))
    (pget_all_init_clss V, add_mset (remdups_mset (C + C')) (pget_all_learned_clss V), S, {} \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
    atms_of_mm (pget_all_learned_clss V) \<union>
    atms_of_mm (wit_clause `# mset S))\<close>
    using learn_minus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> \<open>remdups_mset (C+C')\<close> S \<open>{}\<close>]
    by (auto simp: V W ac_simps)
  have \<open>rules (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
    apply (rule arg_cong2[where f = rules, THEN iffD2, OF _ _ R])
    subgoal by (auto simp: V)
    subgoal by (auto simp: W V)
    done
  then show ?thesis by blast
next
  case (resolution_II M N L C C' U D NE UE NS US N0 U0) note V = this(1) and W = this(2) and _ = this(3)
  then have \<open>insert (add_mset L C)
   (insert (add_mset (- L) C')
     (set_mset N \<union> set_mset NE \<union> set_mset NS \<union> set_mset N0 \<union>
      (set_mset U \<union> set_mset UE \<union> set_mset US \<union> set_mset U0))) \<Turnstile>p
    C' + C\<close>
    using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss V + pget_all_learned_clss V)\<close> L C' C]
    by auto
  then have R: \<open>rules (to_mr_state (V, S))
    (pget_all_init_clss V, add_mset (remdups_mset (C + C')) (pget_all_learned_clss V), S, {} \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
    atms_of_mm (pget_all_learned_clss V) \<union>
    atms_of_mm (wit_clause `# mset S))\<close> (is \<open>rules ?A ?B\<close>)
    using learn_minus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> \<open>remdups_mset (C+C')\<close> S \<open>{}\<close>]
    by (auto simp: V W ac_simps)
  moreover have R: \<open>rules ?B
    ( add_mset (remdups_mset (C + C')) (pget_all_init_clss V),(pget_all_learned_clss V), S, {} \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
    atms_of_mm (pget_all_learned_clss V) \<union>
    atms_of_mm (wit_clause `# mset S))\<close> (is \<open>rules _ ?C\<close>)
    using strenghten[of \<open>pget_all_init_clss V\<close>  \<open>remdups_mset (C+C')\<close>  \<open>pget_all_learned_clss V\<close> S \<open>{}\<close>]
    by (auto simp: V W ac_simps)
  moreover have \<open> ?C = (to_mr_state (W, S))\<close>
    by (auto simp: V W ac_simps)
  ultimately show \<open>rules\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
    by auto
next
  case (resolution_IL M C C' N L U D NE UE NS US N0 U0) note V = this(1) and W = this(2) and _ = this(3)
  then have \<open>insert (add_mset (-L) C')
   (insert (add_mset L C)
     (set_mset N \<union> set_mset NE \<union> set_mset NS \<union> set_mset N0 \<union>
      (set_mset U \<union> set_mset UE \<union> set_mset US \<union> set_mset U0))) \<Turnstile>p
    C' + C\<close>
    using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>set_mset (pget_all_init_clss V + pget_all_learned_clss V)\<close> L C' C]
    by auto
  then have R: \<open>rules (pget_all_init_clss V, pget_all_learned_clss V, S, {} \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
    atms_of_mm (pget_all_learned_clss V) \<union>
    atms_of_mm (wit_clause `# mset S))
    (pget_all_init_clss V, add_mset (remdups_mset (C + C')) (pget_all_learned_clss V), S, {} \<union> atms_of (remdups_mset (C + C')) \<union> atms_of_mm (pget_all_init_clss V) \<union>
    atms_of_mm (pget_all_learned_clss V) \<union>
    atms_of_mm (wit_clause `# mset S))\<close>
    using learn_minus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> \<open>remdups_mset (C+C')\<close> S \<open>{}\<close>]
    by (auto simp: V W ac_simps)
  have \<open>rules (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
    apply (rule arg_cong2[where f = rules, THEN iffD2, OF _ _ R])
    subgoal by (auto simp: V)
    subgoal by (auto simp: W V)
    done
  then show ?thesis by blast
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
set of learned clauses. Then put  \<^term>\<open>L\<close> to the reconstruction stack\<dots> and you can learn  \<^term>\<open>-L\<close> again.>&
\<close>
lemma
  assumes \<open>cdcl_pure_literal_remove V W\<close> \<open>pcdcl_all_struct_invs V\<close>
  shows \<open>rules (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  using assms(1)
proof (cases)
  case (cdcl_pure_literal_remove L N NE NS N0 M U UE US U0) note S = this(1) and T = this(2) and
    L = this(3,4) and undef = this(5) and lev0 = this(6)
  have
    ent: \<open>entailed_clss_inv V\<close> and
    sub: \<open>psubsumed_invs V\<close> and
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
    have IN: \<open>I \<Turnstile>m N\<close> and \<open>I \<Turnstile>m NS\<close> \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m NE\<close>
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
      using \<open>I \<Turnstile>m NS\<close> ent \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m NE\<close> totJ L(1) undef \<open>lits_of_l M \<subseteq> I\<close>
      apply (auto simp: entailed_clss_inv_def S true_cls_mset_def T Decided_Propagated_in_iff_in_lits_of_l
        dest!: multi_member_split[of \<open>_ :: _ clause\<close>])
      unfolding true_cls_def[of ]
      apply clarsimp
      apply (rule_tac x=La in bexI)
      by auto
    moreover have \<open>?J \<Turnstile>m N0\<close>
      using \<open>I \<Turnstile>m NS\<close> ent \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m NE\<close> totJ L undef clss0
      by (auto simp: entailed_clss_inv_def S true_cls_mset_def T Decided_Propagated_in_iff_in_lits_of_l
        clauses0_inv_def
        dest!: multi_member_split)
    moreover have \<open>?J \<Turnstile>m NS\<close>
      using \<open>I \<Turnstile>m NS\<close> sub \<open>I \<Turnstile>m N0\<close> \<open>I \<Turnstile>m N\<close> totJ calculation
      apply (auto simp: psubsumed_invs_def S true_cls_mset_def T
        dest!: multi_member_split dest: true_cls_mono_leD)
      apply (simp add: tautology_def)
      apply (metis calculation true_cls_mono_leD true_cls_mset_add_mset)+
      done
    moreover have \<open>?J \<Turnstile>m U\<close>
      using IS apply auto
      sorry
    moreover have \<open>?J \<Turnstile>m UE\<close> \<open>?J \<Turnstile>m US\<close> \<open>?J \<Turnstile>m U0\<close>
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
    using rules.learn_plus[of \<open>pget_all_init_clss V\<close> \<open>pget_all_learned_clss V\<close> \<open>{#L#}\<close> S \<open>{}\<close>]
    by (auto intro: consistent_interp_diffI simp: S T to_mr_state_alt_def)
qed


lemma pcdcl_rules:
  \<open>pcdcl V W \<Longrightarrow> pcdcl_all_struct_invs V \<Longrightarrow> rules\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  apply (cases rule: pcdcl.cases, assumption)
  subgoal by (rule pcdcl_core_rules)
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
  subgoal by (rule cdcl_resolution_rules)
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
This is an attempt to create a rule derived from our inprocessing rules back to our cdcl:

  \<^item> \<^term>\<open>add_mset (add_mset (-L) C)\<close> is on purpose a tautology to make sure that we do not lose variables. Although

\<close>
inductive cdcl_weaken :: \<open>'v prag_st \<times> 'v stackWit  \<Rightarrow> 'v prag_st \<times> 'v stackWit \<Rightarrow> bool\<close> where
weaken:
  \<open>cdcl_weaken ((M, add_mset C N, U, None, NE, UE, NS, US, N0, U0), S)
    ((M, N, U, None, add_mset (add_mset (-L) C) NE, UE, NS, US, N0, U0), S @ [Witness I C])\<close>
  if
    "I \<Turnstile> C"  and "redundancy N C I N" and "consistent_interp I " and
    "atm_of ` I \<subseteq> atms_of_mm (N+NE+NS+N0) \<union> atms_of_mm (wit_clause `# mset S)" and
    \<open>L \<in># C\<close>

lemma
  assumes \<open>cdcl_weaken (V, S) (W, T)\<close> \<open>pcdcl_all_struct_invs V\<close>
  shows
    \<open>pcdcl_all_struct_invs W\<close> and
    \<open>rules\<^sup>*\<^sup>*  (to_mr_state (V, S)) (to_mr_state (W, T))\<close>
oops
(*this will get tricky here*)
end
