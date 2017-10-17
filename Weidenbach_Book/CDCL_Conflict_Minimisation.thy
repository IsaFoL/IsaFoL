theory CDCL_Conflict_Minimisation
  imports CDCL.CDCL_W_Abstract_State "../lib/Explorer"
begin

declare cdcl\<^sub>W_restart_mset_state[simp]

context
  fixes M :: \<open>('v, 'v clause) ann_lits\<close>
begin

inductive_set minimize_conflict_tree:: \<open>'v literal \<Rightarrow> 'v literal set\<close> for L :: \<open>'v literal\<close> where
\<open>L \<in> minimize_conflict_tree L\<close> |
\<open>Propagated L C \<in> set M \<Longrightarrow> K \<in># C \<Longrightarrow> L \<in> minimize_conflict_tree L\<close>


inductive resolution_chain :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close> where
  \<open>Propagated (-L) C \<in> set M \<Longrightarrow> resolution_chain (add_mset L E) (remdups_mset (E + (C - {#-L#})))\<close>

inductive conflict_minimization :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close> where
  \<open>resolution_chain C D \<Longrightarrow> D \<subseteq># C \<Longrightarrow> conflict_minimization C D\<close>


inductive minimize_conflict where
resolve_propa: \<open>Propagated L E \<in> set M \<Longrightarrow> minimize_conflict (add_mset (-L) C) (C + remove1_mset L E)\<close> |
remdups: \<open>L \<in># C \<Longrightarrow> minimize_conflict (add_mset (-L) C) C\<close>

definition minimize_conflict_mes :: \<open>'v clause \<Rightarrow> nat list\<close> where
\<open>minimize_conflict_mes C = map (\<lambda>L. count C (-(lit_of L))) M\<close>

end


context
  fixes M :: \<open>('v, 'v clause) ann_lits\<close> and N U :: \<open>'v clauses\<close> and
    D :: \<open>'v clause\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, Some D)\<close>
begin

private lemma
   no_dup: \<open>no_dup M\<close> and
   consistent: \<open>consistent_interp (lits_of_l M)\<close>
  using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
  by simp_all

lemma resolution_chain_resolve:
  assumes \<open>resolution_chain M C E\<close> and  \<open>set_mset N \<union> set_mset U \<Turnstile>p C\<close>
  shows \<open>set_mset N \<union> set_mset U \<Turnstile>p E\<close>
  using assms
proof (induction)
  case (1 L C) note in_trail = this(1) and entailed = this(2)
  have \<open>a @ Propagated L mark # b = trail (M, N, U, Some D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have [simp]: \<open>-L \<in># C\<close>
    by (metis in_trail split_list trail.simps)

  have \<open>set (get_all_mark_of_propagated (trail (M, N, U, Some D)))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N, U, Some D))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  then have \<open>C \<in># N + U\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of C M]
    by (auto simp: clauses_def)
  then have NU_C: \<open>N + U \<Turnstile>pm add_mset (- L) (remove1_mset (-L) C)\<close>
    by auto
  show ?case
    unfolding true_clss_cls_remdups_mset
    apply (rule true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of _ \<open>-L\<close>])
    using  entailed NU_C by simp_all
qed

lemma rtranclp_resolution_chain_resolve:
  assumes \<open>(resolution_chain M)\<^sup>*\<^sup>* C E\<close> and  \<open>N + U \<Turnstile>pm C\<close>
  shows \<open>N + U \<Turnstile>pm E\<close>
  using assms by (induction) (auto dest!: resolution_chain_resolve)


lemma minimize_conflict_entailed_trail:
  assumes \<open>minimize_conflict M C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms
proof (induction rule: minimize_conflict.induct)
  case (resolve_propa L E C) note in_trail = this(1) and M_C = this(2)
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated L E # M1\<close>
    using split_list[OF in_trail] by metis
  have \<open>a @ Propagated L mark # b = trail (M, N, U, Some D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have L_E: \<open>L \<in># E\<close> and M_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L E)\<close>
    unfolding M by force+
  then have M_E: \<open>M \<Turnstile>as CNot (remove1_mset L E)\<close>
    unfolding M by (simp add: true_annots_append_l)
  show ?case
    using M_E M_C L_E by (auto dest!: multi_member_split)
next
  case (remdups L C)
  then show ?case
    by auto
qed

lemma minimize_conflict_mes:
  assumes \<open>minimize_conflict M C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>(minimize_conflict_mes M E, minimize_conflict_mes M C) \<in> lexn less_than (length M)\<close>
  using assms
proof (induction rule: minimize_conflict.induct)
  case (resolve_propa L E C) note in_trail = this(1) and M_C = this(2)
    obtain M2 M1 where
    M: \<open>M = M2 @ Propagated L E # M1\<close>
    using split_list[OF in_trail] by metis
  have \<open>a @ Propagated L mark # b = trail (M, N, U, Some D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have L_E: \<open>L \<in># E\<close> and M_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L E)\<close>
    unfolding M by force+
  then have [simp]: \<open>count E (- L) = 0\<close> and uL_E: \<open>-L \<notin># E\<close>
    using no_dup by (auto simp: count_eq_zero_iff add_mset_eq_add_mset M
       true_annots_true_cls_def_iff_negation_in_model Decided_Propagated_in_iff_in_lits_of_l
      dest!: multi_member_split)
  have [simp]: \<open>count E L = Suc 0\<close>
    using L_E M_E no_dup
    by (auto dest!: multi_member_split simp: count_eq_zero_iff M
      true_annots_true_cls_def_iff_negation_in_model Decided_Propagated_in_iff_in_lits_of_l)
  have [dest]: \<open>x \<in> set M2 \<Longrightarrow> lit_of x \<notin> lits_of_l M2 \<Longrightarrow> - lit_of x \<notin> lits_of_l M2 \<Longrightarrow> False\<close> for x
    using lits_of_def by fastforce
  have tauto_E: \<open>\<not>tautology E\<close>
    using consistent consistent_CNot_not_tautology[of \<open>lits_of_l M1\<close> \<open>remove1_mset L E\<close>] M_E L_E uL_E
    unfolding M  by (auto dest!: consistent_interp_unionD multi_member_split
       simp: consistent_interp_insert_iff true_annots_true_cls tautology_add_mset)
  have H: \<open>count E (- lit_of x) = 0\<close>
    if
      x: \<open>x \<in> set M2\<close> and
      \<open>lit_of x \<noteq> - L\<close> and
      \<open>L \<noteq> lit_of x\<close> for x
    unfolding count_eq_zero_iff
  proof
    assume \<open>- lit_of x \<in># E\<close>
    then have \<open>-lit_of x \<in># remove1_mset L E\<close>
      using that by (auto simp: uminus_lit_swap)
    then have \<open>lit_of x \<in> lits_of_l M1\<close>
      using M_E unfolding true_annots_true_cls_def_iff_negation_in_model
      by (auto dest: in_diffD)
    then show False
      using x no_dup apply (auto simp: M)
      using M_E cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin[of M1 M2 \<open>lit_of x\<close>]
      unfolding true_annots_true_cls_def_iff_negation_in_model
      by (auto dest: in_diffD simp: lits_of_def no_dup_def)
  qed
  have 1: \<open>map (\<lambda>L'. count (C + remove1_mset L E) (- lit_of L')) M2 = map (\<lambda>L'. count (add_mset (-L) C) (- lit_of L')) M2\<close>
    apply (rule map_cong)
    apply (rule refl)
    using no_dup M_E unfolding M true_annots_true_cls_def_iff_negation_in_model
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l eq_commute[of L \<open>- lit_of _\<close>] uminus_lit_swap
      H)
  have [simp]: \<open>length M - length M2 = Suc (length M1)\<close>
    unfolding M by auto
  show ?case
    unfolding minimize_conflict_mes_def
    apply (subst M)
    apply (subst M)
    unfolding map_append list.map(2) 1
    apply (subst prepend_same_lexn)
    apply auto[]
    apply (simp del: lexn.simps)
    apply (subst lexn_Suc)
    apply (intro conjI)
    subgoal by simp
    subgoal by simp
    subgoal by (rule disjI1) simp
    done
next
  case (remdups L C) note LC = this(1) and MC = this(2)
  have \<open>L \<in> lits_of_l M\<close>
    using MC LC unfolding true_annots_true_cls_def_iff_negation_in_model
    by auto
  then obtain M1 K M2 where
     M: \<open>M = M2 @ K # M1\<close> and
     [simp]: \<open>lit_of K = L\<close>
    using split_list by (metis (no_types, lifting) imageE lits_of_def)
  have 1: \<open>map (\<lambda>La. count (add_mset (- L) C) (- lit_of La)) M2 = map (\<lambda>La. count C (- lit_of La)) M2\<close>
    apply (rule map_cong)
    apply (rule refl)
    using no_dup LC MC by (fastforce dest: no_dup_consistentD multi_member_split)
  have 2: \<open>map (\<lambda>La. count (add_mset (- L) C) (- lit_of La)) M1 = map (\<lambda>La. count C (- lit_of La)) M1\<close>
    apply (rule map_cong)
    apply (rule refl)
    using no_dup LC MC by (fastforce dest: no_dup_consistentD multi_member_split)
  have [simp]: \<open>length M - length M2 = Suc (length M1)\<close>
    unfolding M by auto

  show ?case
    unfolding minimize_conflict_mes_def
    apply (subst M)
    apply (subst M)
    unfolding map_append list.map(2) 1 2
    by (auto simp: uminus_lit_swap prepend_same_lexn lexn_Suc simp del: lexn.simps)
qed

definition cut_conflict_at  :: \<open>'v literal \<Rightarrow> 'v clause \<Rightarrow> 'v clause\<close> where
\<open>cut_conflict_at L E = filter_mset (\<lambda>K. -K \<in> lit_of ` set (takeWhile (\<lambda>K. lit_of K \<noteq> L) M)) E\<close>

end

end