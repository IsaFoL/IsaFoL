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
   \<open>clause E = remdups_mset D'\<close> \<open>size (watched E) = 2\<close>  \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
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
   \<open>clause E = remdups_mset D'\<close> \<open>\<not>tautology (D + D')\<close>  \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
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
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close>  \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
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
    (M, N + {#E#}, U + {#C, E#}, DD, NE, UE, add_mset (clause C') NS, US, {#}, {#})\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> \<open>size (watched E) = 2\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close>  \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, DD, add_mset {#K#} NE, UE,
       add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
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

(* find_theorems \<open>twl_lazy_update (_ # _)\<close>
 * lemma \<open>twl_lazy_update M C \<Longrightarrow> undefined_lit M K \<Longrightarrow> twl_lazy_update (Propagated K D # M) C\<close>
 *   using no_blit_propagatedD[of M K D \<open>clause C\<close>]
 *   apply (cases C)
 *   apply (auto simp: get_level_cons_if atm_of_eq_atm_of uminus_lit_swap
 *     count_decided_ge_get_level Decided_Propagated_in_iff_in_lits_of_l
 *     dest: no_blit_propagatedD)
 *   apply (auto simp add: has_blit_def)[]
 * defer
 *   apply force
 *   subgoal for x1 x2 Ka
 *     apply (drule_tac x = Ka in spec)
 *       apply auto
 *   apply (subst (asm)(4) has_blitI[of \<open>-K\<close>])
 *   apply (auto; fail)+
 *     defer
 *     apply auto[]
 * try0 intro: has_blitI
 *   apply auto
 * apply (auto simp add: has_blitI)
 * apply (auto simp add: has_blit_def dest!: multi_member_split)[]
 *   sledgehammer
 * 
 *     sorry
 * apply (metis get_level_uminus has_blit_def is_blit_Cons order_mono_setup.refl union_iff)
 * using count_decided_ge_get_level le_SucI apply blast
 * sledgehammer
 * find_theorems has_blit \<open>_ # _\<close>
 * find_theorems twl_lazy_update Cons *)

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

end