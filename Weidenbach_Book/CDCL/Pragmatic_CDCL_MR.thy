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
  subgoal apply (auto simp: cdcl_resolution.simps)
    sorry
  subgoal by (auto simp: cdcl_subsumed.simps Un_left_commute add_mset_commute)
  subgoal by (auto simp: cdcl_flush_unit.simps)
  subgoal by (auto simp: cdcl_inp_propagate.simps)
  subgoal by (auto simp: cdcl_inp_conflict.simps)
  subgoal by (auto simp: cdcl_unitres_true.simps)
  subgoal by (auto simp: cdcl_promote_false.simps)

    oops



end
