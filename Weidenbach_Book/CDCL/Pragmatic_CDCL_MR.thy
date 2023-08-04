theory Pragmatic_CDCL_MR
  imports Pragmatic_CDCL Model_Reconstruction.Inprocessing_Rules
begin

fun to_mr_state :: \<open>'v prag_st \<times> 'v stackWit \<Rightarrow> 'v clauses \<times> 'v clauses \<times> 'v stackWit \<times> 'v set\<close> where
  \<open>to_mr_state ((M, N, U, D, NE, UE, NS, US, N0, U0), S) = (N + NE + NS + N0, U + UE + US + U0, S, atms_of_mm (N + NE + NS + N0 + U + UE + US + U0) \<union> atms_of_ms (wit_clause ` set S))\<close>

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
