theory Watched_Literals_Transition_System_Inprocessing
  imports Watched_Literals_Transition_System Weidenbach_Book_Base.Explorer
begin


chapter \<open>Inprocessing\<close>

section \<open>Subsumption\<close>


section \<open>Subsumption resolution\<close>
text \<open>
  The lifting from \<^term>\<open>cdcl_subresolution\<close> is a lot more complicated due to the handling of
  unit and nonunit clauses. Basically, we have to split every rule in two. Hence we don't have a
  one-to-one mapping anymore, but need to use \<^term>\<open>cdcl_flush_unit\<close> or rule of that kind.

  We don't support (yet) generation of the empty clause. This is very tricky because we entirely
  leave the CDCL calculus.


  To maintain compatibility with the TWL scheme we require the condition
  ⬣\<open>\<forall>L \<in># clause E. undefined_lit M L\<close>. This is stronger than what we really need (we could only
  assume that no literal is watched that is false). However, this goes against the whole idea of
  inprocessing, where we want to get rid of such clauses (if we do a round of inprocessing, we
  do it entirely).
\<close>
inductive cdcl_twl_subresolution :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
twl_subresolution_II_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, DD, NE, UE, NS, US, {#}, {#})
    (M, N + {#C, E#}, U, DD, NE, UE, add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>clause E = remdups_mset D'\<close> \<open>size (watched E) = 2\<close>  \<open>\<forall>L \<in># D+D'. undefined_lit M L\<close>
   \<open>undefined_lit M L\<close>|
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, DD, add_mset {#K#} NE, UE,
        add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_LL_nonunit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, DD, NE, UE, NS, US, {#}, Q)
    (M, N, U + {#C, E#}, DD, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>size (watched E) = 2\<close>
   \<open>clause E = remdups_mset D'\<close> \<open>\<not>tautology (D + D')\<close>  \<open>\<forall>L \<in># D+D'. undefined_lit M L\<close>
   \<open>undefined_lit M L\<close>|
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, DD, NE, add_mset {#K#} UE, NS,
       add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>undefined_lit M K\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>\<not>tautology (D + D')\<close> |

twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, DD, NE, UE, NS, US, {#}, Q)
    (M, N + {#C#}, U + {#E#}, DD, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>size (watched E) = 2\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close>  \<open>\<forall>L \<in># D+D'. undefined_lit M L\<close>
   \<open>undefined_lit M L\<close>|
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, DD, NE, add_mset {#K#} UE, NS,
      add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>undefined_lit M K\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> |

twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, {#})
    (M, N + {#E#}, U + {#C#}, DD, NE, UE, add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>size (watched E) = 2\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close>  \<open>\<forall>L \<in># D+D'. undefined_lit M L\<close>
   \<open>undefined_lit M L\<close>|
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, DD, add_mset {#K#} NE, UE,
       add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset (-L) D\<close>
   \<open>clause C' = add_mset (L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>undefined_lit M K\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close>

lemma no_blit_propagatedD: \<open>undefined_lit M K \<Longrightarrow> \<not>has_blit (Propagated K D # M) C L \<Longrightarrow>
   \<not>has_blit (M) C L\<close>
  apply (auto simp: has_blit_def get_level_cons_if intro: exI[of _ \<open>-K\<close>]
    split: if_split dest!: multi_member_split cong: if_cong)
    apply (smt count_decided_ge_get_level defined_lit_map get_level_cons_if in_lits_of_l_defined_litD lit_of.simps(2))+
  done

lemma has_blitI:
  \<open>K \<in># C \<Longrightarrow> get_level M K = count_decided M \<Longrightarrow> get_level M K' = count_decided M \<Longrightarrow> K \<in> lits_of_l M \<Longrightarrow> has_blit (M) C K'\<close>
  unfolding has_blit_def
  by (rule exI[of _ K]) (auto simp: atm_of_eq_atm_of)

lemma struct_wf_twl_cls_alt_def:
  \<open>struct_wf_twl_cls E \<longleftrightarrow> distinct_mset (clause E) \<and> size (watched E) = 2\<close>
  by (cases E) auto

lemma has_blit_lvl0_iff: \<open>count_decided M = 0 \<Longrightarrow>
  has_blit (Propagated K {#K#} # M) C (- K) \<longleftrightarrow> K \<in># C \<or> has_blit (M) C (- K)\<close>
  using count_decided_ge_get_level[of M]
  unfolding has_blit_def
  by (auto simp: get_level_cons_if split: if_splits)

lemma not_has_blit_lvl0_iff: \<open>count_decided M = 0 \<Longrightarrow>
  \<not>has_blit M C K \<longleftrightarrow> (\<forall>L \<in># C. L \<notin> lits_of_l M)\<close>
  using count_decided_ge_get_level[of M]
  unfolding has_blit_def
  by (auto simp: get_level_cons_if split: if_splits)

lemma has_blit_already_in: \<open>L \<in># C \<Longrightarrow> L \<in> lits_of_l M \<Longrightarrow> has_blit M C L\<close>
  by (auto simp: has_blit_def)

lemma cdcl_twl_subresolution_twl_st_inv:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> no_dup (get_trail S) \<Longrightarrow> twl_st_inv S \<Longrightarrow> twl_st_inv T\<close>
proof (induction rule: cdcl_twl_subresolution.induct)
  case (twl_subresolution_II_nonunit C L D C' D' M E N U DD NE UE NS US)
  moreover have \<open>twl_lazy_update M E\<close>
    using twl_subresolution_II_nonunit
    by (cases E;
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  moreover have \<open>watched_literals_false_of_max_level M E\<close> if \<open>watched_literals_false_of_max_level M C'\<close>
    using twl_subresolution_II_nonunit(1-7) that count_decided_ge_get_level[of M]
    by (cases E; cases C';
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def)
next
  case (twl_subresolution_II_unit C L D C' D' M K N U DD NE UE NS US Q)
  moreover have \<open>twl_is_an_exception C (add_mset K Q) WS\<close> if \<open>twl_is_an_exception C Q WS\<close> for WS
    using that
    by (auto simp: twl_is_an_exception_add_mset_to_queue)
  moreover have [simp]: \<open>watched_literals_false_of_max_level (Propagated K D # M) C\<close> for C D
    using count_decided_ge_get_level[of M] twl_subresolution_II_unit
    by (cases C) (auto simp: get_level_cons_if)
  moreover have \<open>twl_lazy_update (Propagated K {#K#} # M) Ca\<close>
    if
      \<open>\<forall>C\<in>set_mset N \<union> set_mset U. \<not> twl_is_an_exception C Q {#} \<longrightarrow> twl_lazy_update M C\<close> and
      \<open>\<not> twl_is_an_exception Ca Q {#}\<close> and
      \<open>- K \<notin># watched Ca\<close> and
      \<open>\<not> twl_is_an_exception C Q {#} \<Longrightarrow> twl_lazy_update M C\<close> and
      \<open>Ca \<in>#  (N+U) \<or> Ca = C\<close>
      for Ca
      using that twl_subresolution_II_unit count_decided_ge_get_level[of M]
      apply (cases Ca)
      apply (auto 5 3 simp: get_level_cons_if uminus_lit_swap twl_is_an_exception_def
        twl_st_inv.simps
        dest!: multi_member_split[of _ N] multi_member_split[of _ U])
      done
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps twl_is_an_exception_add_mset_to_queue)
next
  case (twl_subresolution_LL_nonunit C L D C' D' M E N U DD NE UE NS US Q)
  moreover have \<open>twl_lazy_update M E\<close>
    using twl_subresolution_LL_nonunit
    by (cases E;
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  moreover have \<open>watched_literals_false_of_max_level M E\<close> if \<open>watched_literals_false_of_max_level M C'\<close>
    using twl_subresolution_LL_nonunit(1-7) that count_decided_ge_get_level[of M]
    by (cases E; cases C';
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def)
next
  case (twl_subresolution_LL_unit C L D C' D' M K N U DD NE UE NS US Q)
  moreover have \<open>twl_is_an_exception C (add_mset K Q) WS\<close> if \<open>twl_is_an_exception C Q WS\<close> for WS
    using that
    by (auto simp: twl_is_an_exception_add_mset_to_queue)
  moreover have [simp]: \<open>watched_literals_false_of_max_level (Propagated K D # M) C\<close> for C D
    using count_decided_ge_get_level[of M] twl_subresolution_LL_unit
    by (cases C) (auto simp: get_level_cons_if)
  moreover have \<open>twl_lazy_update (Propagated K {#K#} # M) Ca\<close>
    if
      \<open>\<forall>C\<in>set_mset N \<union> set_mset U. \<not> twl_is_an_exception C Q {#} \<longrightarrow> twl_lazy_update M C\<close> and
      \<open>\<not> twl_is_an_exception Ca Q {#}\<close> and
      \<open>- K \<notin># watched Ca\<close> and
      \<open>\<not> twl_is_an_exception C Q {#} \<Longrightarrow> twl_lazy_update M C\<close> and
      \<open>Ca \<in>#  (N+U) \<or> Ca = C\<close>
      for Ca
      using that twl_subresolution_LL_unit count_decided_ge_get_level[of M]
      apply (cases Ca)
      apply (auto 5 3 simp: get_level_cons_if uminus_lit_swap twl_is_an_exception_def
        twl_st_inv.simps
        dest!: multi_member_split[of _ N] multi_member_split[of _ U])
      done
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps twl_is_an_exception_add_mset_to_queue)
next
  case (twl_subresolution_LI_nonunit C L D C' D' M E N U DD NE UE NS US Q)
  moreover have \<open>twl_lazy_update M E\<close>
    using twl_subresolution_LI_nonunit
    by (cases E;
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  moreover have \<open>watched_literals_false_of_max_level M E\<close> if \<open>watched_literals_false_of_max_level M C'\<close>
    using twl_subresolution_LI_nonunit(1-7) that count_decided_ge_get_level[of M]
    by (cases E; cases C';
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def)
next
  case (twl_subresolution_LI_unit C L D C' D' M K N U DD NE UE NS US Q)
  moreover have \<open>twl_is_an_exception C (add_mset K Q) WS\<close> if \<open>twl_is_an_exception C Q WS\<close> for WS
    using that
    by (auto simp: twl_is_an_exception_add_mset_to_queue)
  moreover have [simp]: \<open>watched_literals_false_of_max_level (Propagated K D # M) C\<close> for C D
    using count_decided_ge_get_level[of M] twl_subresolution_LI_unit
    by (cases C) (auto simp: get_level_cons_if)
  moreover have \<open>twl_lazy_update (Propagated K {#K#} # M) Ca\<close>
    if
      \<open>\<forall>C\<in>set_mset N \<union> set_mset U. \<not> twl_is_an_exception C Q {#} \<longrightarrow> twl_lazy_update M C\<close> and
      \<open>\<not> twl_is_an_exception Ca Q {#}\<close> and
      \<open>- K \<notin># watched Ca\<close> and
      \<open>\<not> twl_is_an_exception C Q {#} \<Longrightarrow> twl_lazy_update M C\<close> and
      \<open>Ca \<in>#  (N+U) \<or> Ca = C\<close>
      for Ca
      using that twl_subresolution_LI_unit count_decided_ge_get_level[of M]
      apply (cases Ca)
      apply (auto 5 3 simp: get_level_cons_if uminus_lit_swap twl_is_an_exception_def
        twl_st_inv.simps
        dest!: multi_member_split[of _ N] multi_member_split[of _ U])
      done
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps twl_is_an_exception_add_mset_to_queue)
next
  case (twl_subresolution_IL_nonunit C L D C' D' M E N U DD NE UE NS US)
  moreover have \<open>twl_lazy_update M E\<close>
    using twl_subresolution_IL_nonunit
    by (cases E;
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  moreover have \<open>watched_literals_false_of_max_level M E\<close> if \<open>watched_literals_false_of_max_level M C'\<close>
    using twl_subresolution_IL_nonunit(1-7) that count_decided_ge_get_level[of M]
    by (cases E; cases C';
      auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def distinct_mset_remdups_mset_id
      dest!: multi_member_split dest: uminus_lits_of_l_definedD)
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps struct_wf_twl_cls_alt_def)
next
  case (twl_subresolution_IL_unit C L D C' D' M K N U DD NE UE NS US Q)
  moreover have \<open>twl_is_an_exception C (add_mset K Q) WS\<close> if \<open>twl_is_an_exception C Q WS\<close> for WS
    using that
    by (auto simp: twl_is_an_exception_add_mset_to_queue)
  moreover have [simp]: \<open>watched_literals_false_of_max_level (Propagated K D # M) C\<close> for C D
    using count_decided_ge_get_level[of M] twl_subresolution_IL_unit
    by (cases C) (auto simp: get_level_cons_if)
  moreover have \<open>twl_lazy_update (Propagated K {#K#} # M) Ca\<close>
    if
      \<open>\<forall>C\<in>set_mset N \<union> set_mset U. \<not> twl_is_an_exception C Q {#} \<longrightarrow> twl_lazy_update M C\<close> and
      \<open>\<not> twl_is_an_exception Ca Q {#}\<close> and
      \<open>- K \<notin># watched Ca\<close> and
      \<open>\<not> twl_is_an_exception C Q {#} \<Longrightarrow> twl_lazy_update M C\<close> and
      \<open>Ca \<in>#  (N+U) \<or> Ca = C\<close>
      for Ca
      using that twl_subresolution_IL_unit count_decided_ge_get_level[of M]
      apply (cases Ca)
      apply (auto 5 3 simp: get_level_cons_if uminus_lit_swap twl_is_an_exception_def
        twl_st_inv.simps
        dest!: multi_member_split[of _ N] multi_member_split[of _ U])
      done
  ultimately show ?case
    using count_decided_ge_get_level[of M]
    by (auto simp: twl_st_inv.simps twl_is_an_exception_add_mset_to_queue)
qed

lemma cdcl_twl_subresolution_twl_stgy_invs:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  using count_decided_ge_get_level[of \<open>get_trail S\<close>] apply -
  apply (induction rule: cdcl_twl_subresolution.induct)
  apply (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
    conflict_non_zero_unless_level_0_lvl0 get_level_cons_if
    dest!: multi_member_split)
  done

lemma cdcl_twl_subresolution_cdcl:
  assumes \<open>cdcl_twl_subresolution S W\<close> and \<open>get_conflict S = None\<close>
  obtains T U where
    \<open>cdcl_subresolution (pstate\<^sub>W_of S) T\<close> and
    \<open>cdcl_propagate\<^sup>*\<^sup>* T U\<close>and
    \<open>cdcl_flush_unit\<^sup>*\<^sup>* U (pstate\<^sub>W_of W)\<close>
proof -
  show ?thesis
  using assms(1,2)
  apply (cases rule: cdcl_twl_subresolution.cases)
  subgoal for C L D C' D' M E N Ua DD NE UE NS US
    by (rule that[of \<open>(pstate\<^sub>W_of W)\<close> \<open>(pstate\<^sub>W_of W)\<close>]) (auto simp: cdcl_subresolution.simps)
  subgoal for C L D C' D' M K N Ua DD NE UE NS US Q
    apply (rule that[of \<open>(M,  (clause `# N) + {# {#K#}, clause C#}, clause `# Ua, DD, NE, UE, add_mset (clause C') NS, US)\<close>
                        \<open>(Propagated K {#K#} # M,  (clause `# N) + {# {#K#}, clause C#}, clause `# Ua, DD, NE, UE, add_mset (clause C') NS, US)\<close>])
    subgoal
      by (auto simp: cdcl_subresolution.simps)
    subgoal
      by (rule r_into_rtranclp) (auto simp: cdcl_propagate.simps)
    subgoal
      by (auto simp: cdcl_flush_unit.simps)
    done
  subgoal for C L D C' D' M E N U DD NE UE NS US Q
    by (rule that[of \<open>(pstate\<^sub>W_of W)\<close> \<open>(pstate\<^sub>W_of W)\<close>]) (auto simp: cdcl_subresolution.simps)
  subgoal for C L D C' D' M K N U DD NE UE NS US Q
    apply (rule that[of \<open>(M,  (clause `# N), clause `# U + {# {#K#}, clause C#}, DD, NE, UE, NS, add_mset (clause C') US)\<close>
                        \<open>(Propagated K {#K#} # M,  (clause `# N), clause `# U + {# {#K#}, clause C#}, DD, NE, UE, NS, add_mset (clause C') US)\<close>])
    subgoal
      by (fastforce simp: cdcl_subresolution.simps)
    subgoal
      by (rule r_into_rtranclp) (auto simp: cdcl_propagate.simps)
    subgoal
      by (auto simp: cdcl_flush_unit.simps)
    done
  subgoal for C L D C' D' M E N U DD NE UE NS US Q
    apply (rule that[of \<open>(pstate\<^sub>W_of W)\<close> \<open>(pstate\<^sub>W_of W)\<close>])
    apply (auto simp: cdcl_subresolution.simps)
    by fast
  subgoal for C L D C' D' M K N U DD NE UE NS US Q
    apply (rule that[of \<open>(M, add_mset (clause C) (clause `# N), clause `# U + {# {#K#}#}, DD, NE, UE, NS, add_mset (clause C') US)\<close>
                        \<open>(Propagated K {#K#} # M, add_mset (clause C) (clause `# N), clause `# U + {# {#K#}#}, DD, NE, UE, NS, add_mset (clause C') US)\<close>])
    subgoal
      by (fastforce simp: cdcl_subresolution.simps)
    subgoal
      by (rule r_into_rtranclp) (auto simp: cdcl_propagate.simps)
    subgoal
      apply  (rule r_into_rtranclp)
      by (auto simp: cdcl_flush_unit.simps)
    done
  subgoal for C L D C' D' M E N U DD NE UE NS US
    by (rule that[of \<open>(pstate\<^sub>W_of W)\<close> \<open>(pstate\<^sub>W_of W)\<close>])
      (fastforce simp: cdcl_subresolution.simps ac_simps)+
  subgoal for C L D C' D' M K N U DD NE UE NS US Q
    apply (rule that[of \<open>(M, add_mset ({#K#}) (clause `# N), clause `# U + {# clause C#}, DD, NE, UE, add_mset (clause C') NS, US)\<close>
                        \<open>(Propagated K {#K#} # M, add_mset {#K#} (clause `# N), clause `# U + {#clause C#}, DD, NE, UE, add_mset (clause C') NS, US)\<close>])
    subgoal
      by (fastforce simp: cdcl_subresolution.simps ac_simps)
    subgoal
      by (rule r_into_rtranclp) (auto simp: cdcl_propagate.simps)
    subgoal
      apply  (rule r_into_rtranclp)
      by (auto simp: cdcl_flush_unit.simps)
    done
  done
qed

(*TODO Move*)
lemma cdcl_subresolution:
  assumes \<open>cdcl_subresolution S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows \<open>pcdcl\<^sup>*\<^sup>* S T\<close>
  using assms
proof  (induction rule: cdcl_subresolution.induct)
  case (subresolution_II M C C' N L U D NE UE NS US)
  then show ?case
    apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_II, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(1)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M
      \<open>N + {#add_mset L C#}\<close> U D NE UE NS US]
    apply (auto simp add: dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_LL M C C' N U L D NE UE NS US)
  then show ?case apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_LL, assumption, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(2)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M N
      \<open>U + {#add_mset L C#}\<close> D NE UE NS US]
    apply (auto dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_LI M C C' N L U D NE UE NS US)
  then show ?case apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_IL, assumption, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(2)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M
      \<open>N  + {#add_mset L C#}\<close> \<open>U\<close> D NE UE NS US]
    apply (auto simp add: dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_IL M C C' N L U D NE UE NS US)
  have 1: \<open>cdcl_resolution
     (M, N + {#add_mset L C#}, U + {#add_mset (- L) C'#}, D, NE, UE, NS, US)
     (M, N + {#add_mset L C, remdups_mset (C + C')#},
        U + {#add_mset (- L) C'#}, D, NE, UE, NS, US)\<close>
      (is \<open>cdcl_resolution ?A ?B\<close>)
      using subresolution_IL apply -
      by (rule cdcl_resolution.resolution_LI, assumption, assumption)
  have \<open>pcdcl_all_struct_invs ?B\<close>
    using 1 pcdcl.intros(3) pcdcl_all_struct_invs subresolution_IL.prems by blast
  have 3: \<open>cdcl_subsumed ?B
     (M, add_mset (remdups_mset C) N, (add_mset (add_mset (- L) C') U), D,
    NE, UE, add_mset (add_mset L C) NS, US)\<close> (is \<open>cdcl_subsumed _ ?C\<close>)
    if \<open>C' \<subseteq># C\<close>
    using cdcl_subsumed.intros(1)[of \<open>remdups_mset (C)\<close> \<open>add_mset L C\<close> M \<open>N\<close>
      \<open>(add_mset (add_mset (- L) C') U)\<close> D NE UE NS US] that
    by (auto simp add: dest!: remdups_mset_sum_subset(2)
      simp: remdups_mset_subset_add_mset add_mset_commute)[]
  have 4: \<open>cdcl_subsumed (M, add_mset (remdups_mset C) N, add_mset (remdups_mset C) (add_mset (add_mset (- L) C') U), D,
    NE, UE, add_mset (add_mset L C) NS, US)
    (M, N + {#remdups_mset C#}, U + {#add_mset (- L) C'#}, D, NE, UE, add_mset (add_mset L C) NS,
      add_mset (remdups_mset C) US)\<close>
    by (auto simp: cdcl_subsumed.simps)
  show ?case using subresolution_IL apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3)[OF 1])
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(4))
    apply (rule 3)
    apply assumption
    apply auto
    done
qed

lemma clause_alt_def:
  \<open>clause E =  watched E + unwatched E\<close>
  by (cases E) auto

lemma cdcl_twl_subresolution_twl_struct_invs:
  assumes \<open>cdcl_twl_subresolution S T\<close>
    \<open>twl_struct_invs S\<close> and
    confl_S: \<open>get_conflict S = None\<close>
  shows \<open>twl_struct_invs T\<close>
proof -
  have st_inv: \<open>twl_st_inv S\<close> and
    enq: \<open>valid_enqueued S\<close> and
    struct_invs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of S)\<close> and
    excep: \<open>twl_st_exception_inv S\<close> and
    dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close> and
    confl: \<open>confl_cands_enqueued S\<close> and
    propa: \<open>propa_cands_enqueued S\<close> and
    confl2: \<open>get_conflict S \<noteq> None \<longrightarrow> clauses_to_update S = {#} \<and> literals_to_update S = {#}\<close> and
    clss: \<open>clauses_to_update_inv S\<close> and
    upd: \<open>past_invs S\<close> and
    early_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of S)\<close>
    using assms(2) unfolding twl_struct_invs_def
    by blast+
  have nd: \<open>no_dup (get_trail S)\<close>
    using struct_invs unfolding pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
  have struct_inv: \<open>(\<forall>C \<in># get_clauses S. struct_wf_twl_cls C)\<close>
    using st_inv by (cases S) (auto simp: twl_st_inv.simps)
  obtain Ta U where
    STa: \<open>cdcl_subresolution (pstate\<^sub>W_of S) Ta\<close>
    \<open>cdcl_propagate\<^sup>*\<^sup>* Ta U\<close>
    \<open>cdcl_flush_unit\<^sup>*\<^sup>* U (pstate\<^sub>W_of T)\<close>
    by (rule cdcl_twl_subresolution_cdcl[OF assms(1) confl_S]) blast
  have
    STa: \<open>pcdcl\<^sup>*\<^sup>* (pstate\<^sub>W_of S) Ta\<close> and
    TaU: \<open>pcdcl\<^sup>*\<^sup>* Ta U\<close> and
    UT: \<open>pcdcl\<^sup>*\<^sup>* U (pstate\<^sub>W_of T)\<close>
      apply (rule cdcl_subresolution[OF STa(1) struct_invs])
     apply (metis \<open>cdcl_propagate\<^sup>*\<^sup>* Ta U\<close> mono_rtranclp pcdcl.intros(1) pcdcl_core.intros(2))
    by (metis \<open>cdcl_flush_unit\<^sup>*\<^sup>* U (pstate\<^sub>W_of T)\<close> mono_rtranclp pcdcl.intros(5))

  have neg_iff: \<open>Propagated K {#K#} # M \<Turnstile>as CNot (Ca) \<longleftrightarrow> (-K \<notin># Ca \<and> M \<Turnstile>as CNot (Ca)) \<or>
    (-K \<in># Ca \<and> M \<Turnstile>as CNot (remove1_mset (-K) Ca))\<close>
    if \<open>distinct_mset Ca\<close> \<open>undefined_lit M K\<close>
    for K Ca M
    using that
    by (cases \<open>-K \<in># Ca\<close>)
     (auto dest!: multi_member_split simp: Decided_Propagated_in_iff_in_lits_of_l
      add_mset_eq_add_mset true_annots_true_cls_def_iff_negation_in_model
      dest: true_annots_CNot_lit_of_notin_skip)
  have remdups_mset_set_msetD: \<open>remdups_mset D = A \<Longrightarrow> set_mset D = set_mset A\<close> for A D
    by auto

  have \<open>twl_st_inv T\<close>
    using cdcl_twl_subresolution_twl_st_inv[of S T, OF assms(1) nd st_inv] .
  moreover have \<open>valid_enqueued T\<close>
    using assms(1) enq count_decided_ge_get_level[of \<open>get_trail S\<close>]
    by (induction rule: cdcl_twl_subresolution.induct) (auto simp: get_level_cons_if)
  moreover have \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of T)\<close>
    using struct_invs assms(1) TaU UT STa
      cdcl_subsumed_pcdcl_all_struct_invs[of \<open>pstate\<^sub>W_of S\<close>  \<open>pstate\<^sub>W_of T\<close>] apply -
    by (auto dest!: rtranclp_pcdcl_all_struct_invs)
  moreover have \<open>twl_st_exception_inv T\<close>
    using assms(1) excep confl_S nd
    apply (induction rule: cdcl_twl_subresolution.induct)
    subgoal
      by (auto simp: twl_exception_inv.simps eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>] 
          clause_alt_def uminus_lits_of_l_definedD
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
          multi_member_split[of _ \<open>unwatched _\<close>])
    subgoal
      apply (auto simp: twl_exception_inv.simps
          eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>]
          clause_alt_def uminus_lits_of_l_definedD uminus_lit_swap
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
        multi_member_split[of _ \<open>unwatched _\<close>])
      apply (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left union_mset_add_mset_right union_single_eq_member)
      by (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left union_mset_add_mset_right union_single_eq_member)
    subgoal
      by (auto simp: twl_exception_inv.simps eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>] 
          clause_alt_def uminus_lits_of_l_definedD
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
          multi_member_split[of _ \<open>unwatched _\<close>])
    subgoal
      apply (auto simp: twl_exception_inv.simps
          eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>]
          clause_alt_def uminus_lits_of_l_definedD uminus_lit_swap
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
        multi_member_split[of _ \<open>unwatched _\<close>])
      apply (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left union_mset_add_mset_right union_single_eq_member)
      by (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left union_mset_add_mset_right union_single_eq_member)
    subgoal
      by (auto simp: twl_exception_inv.simps eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>] 
          clause_alt_def uminus_lits_of_l_definedD
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
          multi_member_split[of _ \<open>unwatched _\<close>])
    subgoal
      apply (auto simp: twl_exception_inv.simps
          eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>]
          clause_alt_def uminus_lits_of_l_definedD uminus_lit_swap
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
        multi_member_split[of _ \<open>unwatched _\<close>])
      apply (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left
        union_mset_add_mset_right union_single_eq_member)
      by (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left
        union_mset_add_mset_right union_single_eq_member)
    subgoal
      by (auto simp: twl_exception_inv.simps eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>] 
          clause_alt_def uminus_lits_of_l_definedD
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
          multi_member_split[of _ \<open>unwatched _\<close>])
    subgoal
      apply (auto simp: twl_exception_inv.simps
          eq_commute[of \<open>watched _ + unwatched _\<close> \<open>remdups_mset _\<close>]
          clause_alt_def uminus_lits_of_l_definedD uminus_lit_swap
        dest!: remdups_mset_set_msetD dest!: multi_member_split[of _ \<open>watched _\<close>]
        multi_member_split[of _ \<open>unwatched _\<close>])
      apply (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left union_mset_add_mset_right union_single_eq_member)
      by (metis (no_types, lifting) Un_iff no_blit_propagatedD union_mset_add_mset_left union_mset_add_mset_right union_single_eq_member)
    done
  moreover have dup_T: \<open>no_duplicate_queued T\<close>
    using assms(1) dup
    by (induction rule: cdcl_twl_subresolution.induct) auto
  moreover have \<open>distinct_queued T\<close>
    using assms(1) dist dup
    apply (induction rule: cdcl_twl_subresolution.induct)
    subgoal
      by (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
    subgoal
      apply (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
      apply (drule mset_le_add_mset_decr_left2)
      apply clarsimp
      using undefined_notin by blast
    subgoal
      by (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
    subgoal
      apply (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
      apply (drule mset_le_add_mset_decr_left2)
      by (auto dest: undefined_notin mset_le_add_mset_decr_left2)
    subgoal
      by (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
    subgoal
      apply (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
      apply (drule mset_le_add_mset_decr_left2)
      by (auto dest: undefined_notin mset_le_add_mset_decr_left2)
    subgoal
      by (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
    subgoal
      apply (clarsimp_all simp: dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
      apply (drule mset_le_add_mset_decr_left2)
      by (auto dest: undefined_notin mset_le_add_mset_decr_left2)
    done
  moreover {
    have H: \<open>-K \<in># Ca \<and> M \<Turnstile>as CNot (remove1_mset (-K) Ca)\<close>
      if \<open>Propagated K {#K#} # M \<Turnstile>as CNot (Ca)\<close> \<open>\<not>M \<Turnstile>as CNot (Ca)\<close>
        \<open>no_dup (Propagated K {#K#} # M)\<close>
        \<open>distinct_mset Ca\<close>
      for K Ca M
      using that
      by (cases \<open>-K \<in># Ca\<close>)
       (fastforce dest: true_annots_lit_of_notin_skip multi_member_split)+
    have one_unset_is_propa: \<open>(\<exists>L'. L' \<in># watched Ca \<and> L' \<in># literals_to_update S)\<close>
      if \<open>K \<in># clause Ca\<close> and
        \<open>Ca \<in># get_clauses S\<close>
        \<open>undefined_lit (get_trail S) K\<close>
        \<open>K \<in># clause Ca\<close>
        \<open>clauses_to_update S = {#}\<close>
        \<open>get_trail S \<Turnstile>as CNot (remove1_mset K (clause Ca))\<close>
      for K Ca
      using propa that confl_S
      apply (cases S)
      by (auto dest!: multi_member_split simp: all_conj_distrib eq_commute[of _ \<open>clause _\<close>])

    have confl_unit_learned:
      \<open>confl_cands_enqueued (Propagated K {#K#} # M, N + {#C#}, U, None, add_mset {#K#} NE, UE,
        add_mset (clause C') NS, US, {#}, add_mset (- K) Q)\<close>
    if 
      \<open>confl_cands_enqueued S\<close> and
      \<open>get_conflict S = None\<close> and
      \<open>no_dup (get_trail S)\<close> and
      \<open>clause C = add_mset L D\<close> and
      \<open>clause C' = add_mset (- L) D'\<close> and
      \<open>count_decided M = 0\<close> and
      \<open>D \<subseteq># D'\<close> and
      \<open>\<not> tautology (D + D')\<close> and
      \<open>remdups_mset D' = {#K#}\<close> and
      \<open>undefined_lit M K\<close> and
      \<open>get_trail S = M\<close> and
      \<open>get_clauses S = N + {#C, C'#} + U\<close> and
      \<open>literals_to_update S = Q\<close> and
      \<open>clauses_to_update S = {#}\<close>
    for C L D C' D' M K N U DD NE UE NS US Q
        using that struct_inv one_unset_is_propa[of \<open>-K\<close>]
        apply (cases S; cases C; cases C')
        apply (clarsimp_all simp: distinct_mset_remdups_mset_id uminus_lit_swap
          dest!: multi_member_split[of _ \<open>_ :: _ clause twl_clause multiset\<close>])
        apply (intro conjI impI allI ballI)
        apply (metis in_multiset_nempty insert_iff lit_of.simps(2) no_dup_cons no_dup_consistentD
          set_mset_add_mset_insert subset_eq_mset_single_iff true_annots_lit_of_notin_skip
          true_annots_true_cls_def_iff_negation_in_model)
        apply (clarsimp simp add: neg_iff)
        apply (rule disjE)
        apply assumption
        apply (drule multi_member_split)
        apply (clarsimp simp: struct_wf_twl_cls_alt_def)
        apply (subst (asm) neg_iff)
        apply clarsimp_all
        apply (rule disjE)
        apply assumption
        apply clarsimp_all
        apply blast
        apply blast
        apply (drule multi_member_split)
        apply (clarsimp simp: struct_wf_twl_cls_alt_def)
        apply (subst (asm) neg_iff)
        apply clarsimp_all
        apply (rule disjE)
        apply assumption
        apply auto[]
        apply metis
        done

    have \<open>confl_cands_enqueued T\<close>
      using assms(1) confl confl_S nd
      apply (cases rule: cdcl_twl_subresolution.cases)
      subgoal H1 for C L D C' D' M E N U DD NE UE NS US
        using propa
        by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      subgoal for C L D C' D' M K N U DD NE UE NS US Q
        using confl_unit_learned
        by auto
      subgoal for C L D C' D' M E N U DD NE UE NS US Q
        using propa
        apply (cases D')
        apply (clarsimp_all simp: true_annots_true_cls_def_iff_negation_in_model
            all_conj_distrib clause_alt_def
          dest!: uminus_lits_of_l_definedD remdups_mset_set_msetD)
        by (metis mset_left_cancel_union remdups_mset_set_msetD uminus_lits_of_l_definedD
          union_single_eq_member)
      subgoal for C L D C' D' M K N U DD NE UE NS US Q
        using confl_unit_learned
        by auto
      subgoal for C L D C' D' M E N U DD NE UE NS US Q
        using propa
        apply (cases D')
        apply (clarsimp_all simp: true_annots_true_cls_def_iff_negation_in_model
            all_conj_distrib clause_alt_def
          dest!: uminus_lits_of_l_definedD remdups_mset_set_msetD)
        by (metis mset_left_cancel_union remdups_mset_set_msetD uminus_lits_of_l_definedD
          union_single_eq_member)
      subgoal for C L D C' D' M K N U DD NE UE NS US Q
        using confl_unit_learned
        by auto
      subgoal for C L D C' D' M E N U DD NE UE NS US
        using propa
        by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      subgoal for C L D C' D' M K N U DD NE UE NS US Q
        using confl_unit_learned
        by auto
      done
  }
  moreover {
    have [simp]: \<open>undefined_lit M K \<Longrightarrow> -K \<notin> lits_of_l M\<close> \<open>undefined_lit M K \<Longrightarrow> K \<notin> lits_of_l M\<close> and
     [dest]:
       \<open>- ab \<in> lits_of_l M \<Longrightarrow> defined_lit M ab\<close> \<open>ab \<in> lits_of_l M \<Longrightarrow> defined_lit M ab\<close> for ab K M
      by (auto simp add: Decided_Propagated_in_iff_in_lits_of_l)
    have [simp]:
      \<open>no_dup M \<Longrightarrow> count_decided M = 0 \<Longrightarrow> has_blit M K L \<longleftrightarrow> (\<exists>L'\<in>#K. L' \<in> lits_of_l M)\<close> for M K L
      using count_decided_ge_get_level[of M]
      by (auto simp: has_blit_def)
    have confl_unit_learned:
      \<open>propa_cands_enqueued (Propagated K {#K#} # M, N + {#C#}, U, None, add_mset {#K#} NE, UE,
        add_mset (clause C') NS, US, {#}, add_mset (- K) Q)\<close>
    if 
      \<open>propa_cands_enqueued S\<close> and
      \<open>get_conflict S = None\<close> and
      \<open>no_dup (get_trail S)\<close> and
      \<open>clause C = add_mset L D\<close> and
      \<open>clause C' = add_mset (- L) D'\<close> and
      \<open>count_decided M = 0\<close> and
      \<open>D \<subseteq># D'\<close> and
      \<open>\<not> tautology (D + D')\<close> and
      \<open>remdups_mset D' = {#K#}\<close> and
      \<open>undefined_lit M K\<close> and
      \<open>get_trail S = M\<close> and
      \<open>get_clauses S = N + {#C, C'#} + U\<close> and
      \<open>literals_to_update S = Q\<close> and
      \<open>clauses_to_update S = {#}\<close> and
      \<open>count_decided M = 0\<close>
    for C L D C' D' M K N U DD NE UE NS US Q
      using that struct_inv st_inv
      apply (cases S; cases C; cases C')
      apply (clarsimp_all simp: distinct_mset_remdups_mset_id uminus_lit_swap atm_of_eq_atm_of
          all_conj_distrib
          dest!: multi_member_split[of _ \<open>_ :: _ clause twl_clause multiset\<close>])
      apply (intro conjI impI allI ballI)
      subgoal
        apply (subst (asm) neg_iff)
          apply clarsimp_all
        apply (elim disjE)
         apply clarsimp_all
         apply blast
        apply (drule multi_member_split)
        apply (clarsimp simp: struct_wf_twl_cls_alt_def)
        done
      subgoal
        apply (subst (asm) neg_iff)
          apply clarsimp_all
        apply (elim disjE)
         apply (auto ; fail)[]
        apply (simp add: in_multiset_nempty subset_eq_mset_single_iff)
        done
      subgoal for b c e f g h x1 x2 x1a x2a La Ca
        apply (subst (asm) neg_iff)
          apply (simp add: struct_wf_twl_cls_alt_def; fail)
         apply (clarsimp; fail)
        apply (elim disjE)
         apply blast
        apply (simp add: in_multiset_nempty subset_eq_mset_single_iff tautology_add_mset
            twl_st_inv.simps uminus_lit_swap)
        apply normalize_goal+
        apply (drule multi_member_split)
        apply (case_tac Ca)
        apply (clarsimp simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap all_conj_distrib)
        apply (rule disjE[of _ \<open>_ \<or> _\<close>])
        apply assumption
        apply (clarsimp_all simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap)
        apply (rule disjE[of _ \<open>_ \<in># _\<close>])
        apply assumption
        apply (clarsimp_all simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap)
          apply (metis )
        apply (drule multi_member_split)
        apply (clarsimp_all simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap add_mset_eq_add_mset)
        apply (elim disjE)
        apply (clarsimp_all simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap add_mset_eq_add_mset)
            apply (rule ccontr)
        apply (clarsimp_all simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap add_mset_eq_add_mset all_conj_distrib)
        apply (metis in_CNot_implies_uminus(2) no_dup_consistentD)
        apply (metis in_CNot_implies_uminus(2) no_dup_consistentD)
        apply (metis in_CNot_implies_uminus(2) no_dup_consistentD)
        apply (metis in_CNot_implies_uminus(2) no_dup_consistentD)
            apply (rule ccontr)
        apply (elim disjE[of \<open>_ = _\<close> \<open>_ \<in># _\<close>])
        apply (clarsimp_all simp: struct_wf_twl_cls_alt_def twl_is_an_exception_def size_2_iff
            uminus_lit_swap add_mset_eq_add_mset)
        try0
        supply[[smt_trace]]
        apply (smt \<open>\<And>ab M. - ab \<in> lits_of_l M \<Longrightarrow> defined_lit M ab\<close>  insert_iff no_dup_consistentD set_mset_add_mset_insert true_annots_true_cls_def_iff_negation_in_model uminus_of_uminus_id)
        oops
        find_theorems \<open>undefined_lit\<close> lits_of_l
        apply (metis in_multiset_nempty insert_iff lit_of.simps(2) no_dup_cons no_dup_consistentD
          set_mset_add_mset_insert subset_eq_mset_single_iff true_annots_lit_of_notin_skip
          true_annots_true_cls_def_iff_negation_in_model)
        apply (clarsimp simp add: neg_iff)
        apply (rule disjE)
        apply assumption
        apply (drule multi_member_split)
        apply (clarsimp simp: struct_wf_twl_cls_alt_def)
        apply (subst (asm) neg_iff)
        apply clarsimp_all
        apply (rule disjE)
        apply assumption
        apply clarsimp_all
        apply blast
        apply blast
        apply (drule multi_member_split)
        apply (clarsimp simp: struct_wf_twl_cls_alt_def)
        apply (subst (asm) neg_iff)
        apply clarsimp_all
        apply (rule disjE)
        apply assumption
        apply auto[]
        apply metis
        done
    have \<open>propa_cands_enqueued T\<close>
    using assms(1) propa
    by (induction rule: cdcl_twl_subresolution.induct)
      (case_tac D; auto)+}
  moreover have \<open>get_conflict T \<noteq> None \<longrightarrow> clauses_to_update T = {#} \<and> literals_to_update T = {#}\<close>
    using assms(1) confl2 confl_S
    by (induction rule: cdcl_twl_subresolution.induct) auto
  moreover have \<open>clauses_to_update_inv T\<close>
    using assms(1) clss
    by (induction rule: cdcl_twl_subresolution.induct)
      (auto simp: clauses_to_update_prop.simps filter_mset_empty_conv)+
  moreover have \<open>past_invs T\<close>
  proof -
    let ?f = \<open>(\<lambda>(M, N, U, D, NE, UE, NS, US, WS, Q).
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (\<forall>C \<in># N + U. twl_lazy_update M1 C)))\<close>
    let ?g = \<open>(\<lambda>(M, N, U, D, NE, UE, NS, US, WS, Q).
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (\<forall>C \<in># N + U. watched_literals_false_of_max_level M1 C)))\<close>
    let ?h = \<open>(\<lambda>(M, N, U, D, NE, UE, NS, US, WS, Q).
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (
      (\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NE, UE, NS, US, {#}, {#}) C))))\<close>
    let ?i = \<open>(\<lambda>(M, N, U, D, NE, UE, NS, US, WS, Q).
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (
      confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, {#}, {#}))))\<close>
    let ?j = \<open>(\<lambda>(M, N, U, D, NE, UE, NS, US, WS, Q).
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (
      propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, {#}, {#}))))\<close>
    let ?k = \<open>(\<lambda>(M, N, U, D, NE, UE, NS, US, WS, Q).
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (
      clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, {#}, {#}))))\<close>
    have \<open>?f T\<close> if \<open>?f S\<close>
      using assms(1) that
      by (induction rule: cdcl_twl_subsumed.induct) auto
    moreover have \<open>?g T\<close> if \<open>?g S\<close>
      using assms(1) that
      by (induction rule: cdcl_twl_subsumed.induct) auto
    moreover have \<open>?h T\<close> if \<open>?h S\<close>
      using assms(1) that
      by (induction rule: cdcl_twl_subsumed.induct)
        (case_tac C; auto simp: twl_exception_inv.simps)+
    moreover have \<open>?i T\<close> if \<open>?i S\<close>
      using assms(1) that
      by (induction rule: cdcl_twl_subsumed.induct) auto
    moreover have \<open>?j T\<close> if \<open>?j S\<close>
      using assms(1) that
      by (induction rule: cdcl_twl_subsumed.induct) auto
    moreover have \<open>?k T\<close> if \<open>?k S\<close>
      using assms(1) that
      by (induction rule: cdcl_twl_subsumed.induct) (auto simp: clauses_to_update_prop.simps
        filter_mset_empty_conv)
    ultimately show \<open>past_invs T\<close>
      using upd by (cases S; cases T)
       (simp only: prod.case past_invs.simps imp_conjR all_conj_distrib
          ball_conj_distrib, fast)
  qed
  moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of T)\<close>
    using assms(1) early_propa
    by (induction rule: cdcl_twl_subsumed.induct)
      (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def)
  ultimately show ?thesis
    using cdcl_twl_subsumed_twl_st_inv[of S T] cdcl_twl_subsumed_cdcl_subsumed[of S T]
      cdcl_subsumed_pcdcl_all_struct_invs[of \<open>pstate\<^sub>W_of S\<close>  \<open>pstate\<^sub>W_of T\<close>]
    by (simp add: twl_struct_invs_def)
qed


end