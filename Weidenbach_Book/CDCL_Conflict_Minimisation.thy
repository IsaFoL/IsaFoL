theory CDCL_Conflict_Minimisation
  imports
    Watched_Literals_Watch_List
    WB_More_Refinement
    WB_More_Refinement_List "List-Index.List_Index"
begin


text \<open>We implement the conflict minimisation as presented by Sörensson and Biere
(``Minimizing Learned Clauses''').

We refer to the paper for further details, but the general idea is to produce a series of resolution
steps such that eventually (i.e., after enough resolution steps) no new literals has been introduced
in the conflict clause.

The resolution steps are only done with the reasons of the of literals
appearing in the trail. Hence these steps are terminating: we are ``shortening'' the trail we have
to consider with each resolution step. Remark that the shortening refers to the length of the trail
we have to consider, not the levels.

The concrete proof was harder than we initially expected. Our first proof try was to certify the
resolution steps. While this worked out, adding caching on top of that turned to be rather hard,
since it is not obvious how to add resolution steps in the middle of the current proof if the
literal has already been removed (basically we would have to prove termination and confluence of the
rewriting system).
Therefore, we worked instead directly on the entailment of the literals of the conflict clause
(up to the point in the trail we currently considering, which is also the termination measure).
The previous try is still present in our formalisation (see \<^term>\<open>minimize_conflict_support\<close>, which
we however only use for the termination proof).

The algorithm presented above does not distinguish between literals propagated at the same level:
we cannot reuse information about failures to cut branches. There is a variant of the algorithm
presented above that is able to do so (Van Gelder, ``Improved Conflict-Clause Minimization
Leads to Improved Propositional Proof Traces''). The algorithm is however more complicated and has
only be implemented in very few solvers (at least lingeling and cadical) and is especially not part
of glucose nor cryptominisat. Therefore, we have decided to not implement it: It is probably not
worth it and requires some additional data structures.
\<close>
declare cdcl\<^sub>W_restart_mset_state[simp]

type_synonym out_learned = \<open>nat clause_l\<close>


text \<open>The data structure contains the (unique) literal of highest at position one. This is useful
since this is what we want to have at the end (propagation clause) and we can skip the first
literal when minimising the clause.
\<close>
definition out_learned :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> out_learned \<Rightarrow> bool\<close> where
  \<open>out_learned M D out \<longleftrightarrow>
     out \<noteq> [] \<and>
     (D = None \<longrightarrow> length out = 1) \<and>
     (D \<noteq> None \<longrightarrow> mset (tl out) = filter_mset (\<lambda>L. get_level M L < count_decided M) (the D))\<close>

definition out_learned_confl :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> out_learned \<Rightarrow> bool\<close> where
  \<open>out_learned_confl M D out \<longleftrightarrow>
     out \<noteq> [] \<and> (D \<noteq> None \<and> mset out = the D)\<close>

lemma out_learned_Cons_None[simp]:
  \<open>out_learned (L # aa) None ao \<longleftrightarrow> out_learned aa None ao\<close>
  by (auto simp: out_learned_def)

lemma out_learned_tl_None[simp]:
  \<open>out_learned (tl aa) None ao \<longleftrightarrow> out_learned aa None ao\<close>
  by (auto simp: out_learned_def)

definition index_in_trail :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v literal \<Rightarrow> nat\<close> where
  \<open>index_in_trail M L = index (map (atm_of o lit_of) (rev M)) (atm_of L)\<close>

lemma Propagated_in_trail_entailed:
  assumes
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, D)\<close> and
    in_trail: \<open>Propagated L C \<in> set M\<close>
  shows
    \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close> and \<open>N + U \<Turnstile>pm C\<close> and
    \<open>K \<in># remove1_mset L C \<Longrightarrow> index_in_trail M K < index_in_trail M L\<close> and
    \<open>\<not>tautology C\<close> and \<open>distinct_mset C\<close>
proof -
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated L C # M1\<close>
    using split_list[OF in_trail] by metis
  have \<open>a @ Propagated L mark # b = trail (M, N, U, D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (M, N, U, D)\<close>
    for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast+
  then have L_E: \<open>L \<in># C\<close> and M1_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L C)\<close>
    unfolding M by force+
  then have M_E: \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close>
    unfolding M by (simp add: true_annots_append_l)
  show \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close>
    using L_E M_E by fast+
  have \<open>set (get_all_mark_of_propagated (trail (M, N, U, D)))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N, U, D))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
    by fast
  then have \<open>C \<in># N + U\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of C M]
    by (auto simp: clauses_def)
  then show \<open>N + U \<Turnstile>pm C\<close> by auto

  have n_d: \<open>no_dup M\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  show \<open>index_in_trail M K < index_in_trail M L\<close> if K_C: \<open>K \<in># remove1_mset L C\<close>
  proof -
    have
      KL: \<open>atm_of K \<noteq> atm_of L\<close> and
      uK_M1: \<open>-K \<in> lits_of_l M1\<close> and
      L: \<open>L \<notin> lit_of ` (set M2 \<union> set M1)\<close> \<open>-L \<notin> lit_of ` (set M2 \<union> set M1)\<close>
      using M1_E K_C n_d unfolding M true_annots_true_cls_def_iff_negation_in_model
      by (auto dest!: multi_member_split simp: atm_of_eq_atm_of lits_of_def uminus_lit_swap
          Decided_Propagated_in_iff_in_lits_of_l)
    have L_M1: \<open>atm_of L \<notin> (atm_of \<circ> lit_of) ` set M1\<close>
      using L by (auto simp: image_Un atm_of_eq_atm_of)
    have K_M1: \<open>atm_of K \<in> (atm_of \<circ> lit_of) ` set M1\<close>
      using uK_M1 by (auto simp: lits_of_def image_image comp_def uminus_lit_swap)
    show ?thesis
      using KL L_M1 K_M1 unfolding index_in_trail_def M by (auto simp: index_append)
  qed
  have \<open>\<not>tautology(remove1_mset L C)\<close>
    by (rule consistent_CNot_not_tautology[of \<open>lits_of_l M1\<close>])
     (use n_d M1_E in \<open>auto dest: distinct_consistent_interp no_dup_appendD
       simp: true_annots_true_cls M\<close>)
  then show \<open>\<not>tautology C\<close>
    using multi_member_split[OF L_E] M1_E n_d
    by (auto simp: tautology_add_mset true_annots_true_cls_def_iff_negation_in_model M
        dest!: multi_member_split in_lits_of_l_defined_litD)
  show \<open>distinct_mset (C)\<close>
    using dist \<open>C \<in># N + U\<close> unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto dest: multi_member_split)
qed

text \<open>This predicate corresponds to one resolution step.\<close>
inductive minimize_conflict_support :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close>
  for M where
resolve_propa:
  \<open>minimize_conflict_support M (add_mset (-L) C) (C + remove1_mset L E)\<close>
  if \<open>Propagated L E \<in> set M\<close> |
remdups: \<open>minimize_conflict_support M (add_mset L C) C\<close>


lemma index_in_trail_uminus[simp]: \<open>index_in_trail M (-L) = index_in_trail M L\<close>
  by (auto simp: index_in_trail_def)

text \<open>This is the termination argument of the conflict minimisation: the multiset of the levels
decreases (for the multiset ordering).\<close>
definition minimize_conflict_support_mes :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clause \<Rightarrow> nat multiset\<close>
where
  \<open>minimize_conflict_support_mes M C = index_in_trail M `# C\<close>

context
  fixes M :: \<open>('v, 'v clause) ann_lits\<close> and N U :: \<open>'v clauses\<close> and
    D :: \<open>'v clause option\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, D)\<close>
begin

private lemma
   no_dup: \<open>no_dup M\<close> and
   consistent: \<open>consistent_interp (lits_of_l M)\<close>
  using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
  by simp_all

lemma minimize_conflict_support_entailed_trail:
  assumes \<open>minimize_conflict_support M C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms
proof (induction rule: minimize_conflict_support.induct)
  case (resolve_propa L E C) note in_trail = this(1) and M_C = this(2)
  then show ?case
    using Propagated_in_trail_entailed[OF invs in_trail] by (auto dest!: multi_member_split)
next
  case (remdups L C)
  then show ?case
    by auto
qed

lemma rtranclp_minimize_conflict_support_entailed_trail:
  assumes \<open>(minimize_conflict_support M)\<^sup>*\<^sup>* C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by fast
  subgoal using minimize_conflict_support_entailed_trail by fast
  done

lemma minimize_conflict_support_mes:
  assumes \<open>minimize_conflict_support M C E\<close>
  shows \<open>minimize_conflict_support_mes M E < minimize_conflict_support_mes M C\<close>
  using assms unfolding minimize_conflict_support_mes_def
proof (induction rule: minimize_conflict_support.induct)
  case (resolve_propa L E C) note in_trail = this
  let ?f = \<open>\<lambda>xa. index (map (\<lambda>a. atm_of (lit_of a)) (rev M)) xa\<close>
  have \<open>?f (atm_of x) < ?f (atm_of L)\<close> if x: \<open>x \<in># remove1_mset L E\<close> for x
  proof -
    obtain M2 M1 where
      M: \<open>M = M2 @ Propagated L E # M1\<close>
      using split_list[OF in_trail] by metis
    have \<open>a @ Propagated L mark # b = trail (M, N, U, D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using invs
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by fast
    then have L_E: \<open>L \<in># E\<close> and M_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L E)\<close>
      unfolding M by force+
    then have \<open>-x \<in> lits_of_l M1\<close>
      using x unfolding true_annots_true_cls_def_iff_negation_in_model by auto
    then have \<open>?f (atm_of x) < length M1\<close>
      using no_dup
      by (auto simp: M lits_of_def index_append Decided_Propagated_in_iff_in_lits_of_l
          uminus_lit_swap)
    moreover have \<open>?f (atm_of L) = length M1\<close>
      using no_dup unfolding M by (auto simp: index_append Decided_Propagated_in_iff_in_lits_of_l
          atm_of_eq_atm_of lits_of_def)
    ultimately show ?thesis by auto
  qed

  then show ?case by (auto simp: comp_def index_in_trail_def)
next
  case (remdups L C)
  then show ?case by auto
qed

lemma wf_minimize_conflict_support:
  shows \<open>wf {(C', C). minimize_conflict_support M C C'}\<close>
  apply (rule wf_if_measure_in_wf[of \<open>{(C', C). C' < C}\<close> _ \<open>minimize_conflict_support_mes M\<close>])
  subgoal using wf .
  subgoal using minimize_conflict_support_mes by auto
  done
end

lemma conflict_minimize_step:
  assumes
    \<open>NU \<Turnstile>p add_mset L C\<close> and
    \<open>NU \<Turnstile>p add_mset (-L) D\<close> and
    \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') D\<close>
  shows \<open>NU \<Turnstile>p D\<close>
proof -
  have \<open>NU \<Turnstile>p D + C\<close>
    using assms(1,2) true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or by blast
  then show ?thesis
    using assms(3)
  proof (induction C)
    case empty
    then show ?case
      using true_clss_cls_in true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or by fastforce
  next
    case (add x C) note IH =this(1) and NU_DC = this(2) and entailed = this(3)
    have \<open>NU \<Turnstile>p D + C + D\<close>
      using entailed[of x] NU_DC
        true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of NU \<open>-x\<close> \<open>D + C\<close> D]
      by auto
    then have \<open>NU \<Turnstile>p D + C\<close>
      by (metis add.comm_neutral diff_add_zero sup_subset_mset_def true_clss_cls_sup_iff_add)
    from IH[OF this] entailed show ?case by auto
  qed
qed

text \<open>This function filters the clause by the levels up the level of the given literal. This is
the part the conflict clause that is considered when testing if the given literal is redundant.\<close>
definition filter_to_poslev where
  \<open>filter_to_poslev M L D = filter_mset (\<lambda>K. index_in_trail M K < index_in_trail M L) D\<close>

lemma filter_to_poslev_uminus[simp]:
  \<open>filter_to_poslev M (-L) D = filter_to_poslev M L D\<close>
  by (auto simp: filter_to_poslev_def)

lemma filter_to_poslev_empty[simp]:
  \<open>filter_to_poslev M L {#} = {#}\<close>
  by (auto simp: filter_to_poslev_def)

lemma filter_to_poslev_mono:
  \<open>index_in_trail M K' \<le> index_in_trail M L \<Longrightarrow>
   filter_to_poslev M K' D \<subseteq># filter_to_poslev M L D\<close>
  unfolding filter_to_poslev_def
  by (auto simp: multiset_filter_mono2)

lemma filter_to_poslev_mono_entailement:
  \<open>index_in_trail M K' \<le> index_in_trail M L \<Longrightarrow>
   NU \<Turnstile>p filter_to_poslev M K' D \<Longrightarrow> NU \<Turnstile>p filter_to_poslev M L D\<close>
  by (metis (full_types) filter_to_poslev_mono subset_mset.le_iff_add true_clss_cls_mono_r)

lemma filter_to_poslev_mono_entailement_add_mset:
  \<open>index_in_trail M K' \<le> index_in_trail M L \<Longrightarrow>
   NU \<Turnstile>p add_mset J (filter_to_poslev M K' D) \<Longrightarrow> NU \<Turnstile>p add_mset J (filter_to_poslev M L D)\<close>
  by (metis filter_to_poslev_mono mset_subset_eq_add_mset_cancel subset_mset.le_iff_add
      true_clss_cls_mono_r)

lemma conflict_minimize_intermediate_step:
  assumes
    \<open>NU \<Turnstile>p add_mset L C\<close> and
    K'_C: \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') D \<or> K' \<in># D\<close>
  shows \<open>NU \<Turnstile>p add_mset L D\<close>
proof -
  have \<open>NU \<Turnstile>p add_mset L C + D\<close>
    using assms(1) true_clss_cls_mono_r by blast
  then show ?thesis
    using assms(2)
  proof (induction C)
    case empty
    then show ?case
      using true_clss_cls_in true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or by fastforce
  next
    case (add x C) note IH =this(1) and NU_DC = this(2) and entailed = this(3)

    have 1: \<open>NU \<Turnstile>p add_mset x (add_mset L (D + C))\<close>
      using NU_DC by (auto simp: add_mset_commute ac_simps)
    moreover have 2: \<open>remdups_mset (add_mset L (D + C + D)) = remdups_mset (add_mset L (C + D))\<close>
      by (auto simp: remdups_mset_def)
    moreover have 3: \<open>remdups_mset (D + C + D) = remdups_mset (D + C)\<close>
      by (auto simp: remdups_mset_def)
    moreover have \<open>x \<in># D \<Longrightarrow> NU \<Turnstile>p add_mset L (D + C + D)\<close>
      using 1
      apply (subst (asm) true_clss_cls_remdups_mset[symmetric])
      apply (subst true_clss_cls_remdups_mset[symmetric])
      by (auto simp: 2 3)
    ultimately have \<open>NU \<Turnstile>p add_mset L (D + C + D)\<close>
      using entailed[of x] NU_DC
        true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of NU \<open>-x\<close> \<open>add_mset L D + C\<close> D]
      by auto
    moreover have \<open>remdups_mset (D + (C + D)) = remdups_mset (D + C)\<close>
      by (auto simp: remdups_mset_def)
    ultimately have \<open>NU \<Turnstile>p add_mset L C + D\<close>
      apply (subst true_clss_cls_remdups_mset[symmetric])
      apply (subst (asm) true_clss_cls_remdups_mset[symmetric])
      by (auto simp add: 3 2 add.commute simp del: true_clss_cls_remdups_mset)
    from IH[OF this] entailed show ?case by auto
  qed
qed

lemma conflict_minimize_intermediate_step_filter_to_poslev:
  assumes
    lev_K_L: \<open>\<And>K'. K' \<in># C \<Longrightarrow> index_in_trail M K' < index_in_trail M L\<close> and
    NU_LC: \<open>NU \<Turnstile>p add_mset L C\<close> and
    K'_C: \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') (filter_to_poslev M L D) \<or>
     K' \<in># filter_to_poslev M L D\<close>
  shows \<open>NU \<Turnstile>p add_mset L (filter_to_poslev M L D)\<close>
proof -
  have C_entailed: \<open>K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') (filter_to_poslev M L D) \<or>
   K' \<in># filter_to_poslev M L D\<close> for K'
    using filter_to_poslev_mono[of M K' L D] lev_K_L[of K'] K'_C[of K']
      true_clss_cls_mono_r[of _ \<open> add_mset (- K') (filter_to_poslev M K' D)\<close> ]
    by (auto simp: mset_subset_eq_exists_conv)
  show ?thesis
    using conflict_minimize_intermediate_step[OF NU_LC C_entailed]  by fast
qed

datatype minimize_status = SEEN_FAILED | SEEN_REMOVABLE | SEEN_UNKNOWN

instantiation minimize_status :: default
begin
  definition default_minimize_status where
    \<open>default_minimize_status = SEEN_UNKNOWN\<close>

instance by standard
end

type_synonym 'v conflict_min_analyse = \<open>('v literal \<times> 'v clause) list\<close>
type_synonym 'v conflict_min_cach = \<open>'v \<Rightarrow> minimize_status\<close>

definition get_literal_and_remove_of_analyse
   :: \<open>'v conflict_min_analyse \<Rightarrow> ('v literal \<times> 'v conflict_min_analyse) nres\<close> where
  \<open>get_literal_and_remove_of_analyse analyse =
    SPEC(\<lambda>(L, ana). L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and> ana \<noteq> [] \<and>
         hd ana = (fst (hd analyse), snd (hd (analyse)) - {#L#}))\<close>

definition mark_failed_lits
  :: \<open>_ \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> 'v conflict_min_cach \<Rightarrow> 'v conflict_min_cach nres\<close>
where
  \<open>mark_failed_lits NU analyse cach = SPEC(\<lambda>cach'.
     (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>


definition conflict_min_analysis_inv
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v conflict_min_cach \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_inv M cach NU D \<longleftrightarrow>
    (\<forall>L. -L \<in> lits_of_l M \<longrightarrow> cach (atm_of L) = SEEN_REMOVABLE \<longrightarrow>
      set_mset NU \<Turnstile>p add_mset (-L) (filter_to_poslev M L D))\<close>

lemma conflict_min_analysis_inv_update_removable:
  \<open>no_dup M \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow>
      conflict_min_analysis_inv M (cach(atm_of L := SEEN_REMOVABLE)) NU D \<longleftrightarrow>
      conflict_min_analysis_inv M cach NU D \<and> set_mset NU \<Turnstile>p add_mset (-L) (filter_to_poslev M L D)\<close>
  by (auto simp: conflict_min_analysis_inv_def atm_of_eq_atm_of dest: no_dup_consistentD)


lemma conflict_min_analysis_inv_update_failed:
  \<open>conflict_min_analysis_inv M cach NU D \<Longrightarrow>
   conflict_min_analysis_inv M (cach(L := SEEN_FAILED)) NU D\<close>
  by (auto simp: conflict_min_analysis_inv_def)

fun conflict_min_analysis_stack
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_stack M NU D [] \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack M NU D ((L, E) # []) \<longleftrightarrow> -L \<in> lits_of_l M\<close> |
  \<open>conflict_min_analysis_stack M NU D ((L, E) # (L', E') # analyse) \<longleftrightarrow>
     (\<exists>C. set_mset NU \<Turnstile>p add_mset (-L') C \<and>
       (\<forall>K\<in>#C-add_mset L E'. set_mset NU \<Turnstile>p (filter_to_poslev M L' D) + {#-K#} \<or>
           K \<in># filter_to_poslev M L' D) \<and>
       (\<forall>K\<in>#C. index_in_trail M K < index_in_trail M L') \<and>
       E' \<subseteq># C) \<and>
     -L' \<in> lits_of_l M \<and>
     -L \<in> lits_of_l M \<and>
     index_in_trail M L < index_in_trail M L' \<and>
     conflict_min_analysis_stack M NU D ((L', E') # analyse)\<close>

lemma conflict_min_analysis_stack_change_hd:
  \<open>conflict_min_analysis_stack M NU D ((L, E) # ana) \<Longrightarrow>
     conflict_min_analysis_stack M NU D ((L, E') # ana)\<close>
  by (cases ana, auto)

lemma conflict_min_analysis_stack_sorted:
  \<open>conflict_min_analysis_stack M NU D analyse \<Longrightarrow>
    sorted (map (index_in_trail M o fst) analyse)\<close>
  by (induction rule: conflict_min_analysis_stack.induct)
    auto
lemma conflict_min_analysis_stack_sorted_and_distinct:
  \<open>conflict_min_analysis_stack M NU D analyse \<Longrightarrow>
    sorted (map (index_in_trail M o fst) analyse) \<and>
     distinct (map (index_in_trail M o fst) analyse)\<close>
  by (induction rule: conflict_min_analysis_stack.induct)
    auto

lemma conflict_min_analysis_stack_distinct_fst:
  assumes \<open>conflict_min_analysis_stack M NU D analyse\<close>
  shows \<open>distinct (map fst analyse)\<close> and  \<open>distinct (map (atm_of o fst) analyse)\<close>
proof -
  have dist: \<open>distinct (map (index_in_trail M \<circ> fst) analyse)\<close>
    using conflict_min_analysis_stack_sorted_and_distinct[of M NU D analyse, OF assms]
    by auto
  then show \<open>distinct (map fst analyse)\<close>
    by (auto simp: intro!: distinct_mapI[of \<open>(index_in_trail M)\<close>])
  show \<open>distinct (map (atm_of o fst) analyse)\<close>
  proof (rule ccontr)
    assume \<open>\<not>?thesis\<close>
    from not_distinct_decomp[OF this]
    obtain xs L ys zs where \<open>map (atm_of o fst) analyse = xs @ L # ys @ L # zs\<close>
      by auto
   then show False
     using dist
     by (auto simp: map_eq_append_conv atm_of_eq_atm_of Int_Un_distrib image_Un)
  qed
qed

lemma conflict_min_analysis_stack_neg:
  \<open>conflict_min_analysis_stack M NU D analyse \<Longrightarrow>
    M \<Turnstile>as CNot (fst `# mset analyse)\<close>
  by (induction M NU D analyse rule: conflict_min_analysis_stack.induct)
    auto


fun conflict_min_analysis_stack_hd
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_stack_hd M NU D [] \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack_hd M NU D ((L, E) # _) \<longleftrightarrow>
     (\<exists>C. set_mset NU \<Turnstile>p add_mset (-L) C \<and>
     (\<forall>K\<in>#C. index_in_trail M K < index_in_trail M L) \<and> E \<subseteq># C \<and> -L \<in> lits_of_l M \<and>
     (\<forall>K\<in>#C-E. set_mset NU \<Turnstile>p (filter_to_poslev M L D) + {#-K#} \<or> K \<in># filter_to_poslev M L D))\<close>
lemma conflict_min_analysis_stack_tl:
  \<open>conflict_min_analysis_stack M NU D analyse \<Longrightarrow> conflict_min_analysis_stack M NU D (tl analyse)\<close>
  by (cases \<open>(M, NU, D, analyse)\<close> rule: conflict_min_analysis_stack.cases) auto

definition lit_redundant_inv
  :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow>
        'v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool \<Rightarrow> bool\<close> where
  \<open>lit_redundant_inv M NU D init_analyse = (\<lambda>(cach, analyse, b).
           conflict_min_analysis_inv M cach NU D \<and>
           (analyse \<noteq> [] \<longrightarrow> fst (hd init_analyse) = fst (last analyse)) \<and>
           (analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analyse))) = SEEN_REMOVABLE) \<and>
           conflict_min_analysis_stack M NU D analyse \<and>
           conflict_min_analysis_stack_hd M NU D analyse)\<close>

definition lit_redundant_rec_loop_inv :: \<open>('v, 'v clause) ann_lits \<Rightarrow>
    'v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool \<Rightarrow> bool\<close> where
\<open>lit_redundant_rec_loop_inv M = (\<lambda>(cach, analyse, b).
    (uminus o fst) `# mset analyse \<subseteq># lit_of `# mset M \<and>
    (\<forall>L \<in> set analyse. cach (atm_of (fst L)) = SEEN_UNKNOWN))\<close>

definition lit_redundant_rec :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow>
     'v conflict_min_cach \<Rightarrow> 'v conflict_min_analyse \<Rightarrow>
      ('v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec M NU D cach analysis =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_loop_inv M  \<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(length analyse \<le> length M);
            ASSERT(-fst (hd analyse) \<in> lits_of_l M);
            if snd (hd analyse) = {#}
            then
              RETURN(cach (atm_of (fst (hd analyse)) := SEEN_REMOVABLE), tl analyse, True)
            else do {
              (L, analyse) \<leftarrow> get_literal_and_remove_of_analyse analyse;
              ASSERT(-L \<in> lits_of_l M);
              b \<leftarrow> RES UNIV;
              if (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)
              then RETURN (cach, analyse, False)
              else if b \<or> cach (atm_of L) = SEEN_FAILED
              then do {
                 cach \<leftarrow> mark_failed_lits NU analyse cach;
                 RETURN (cach, [], False)
              }
              else do {
                 ASSERT(cach (atm_of L) = SEEN_UNKNOWN);
                 C \<leftarrow> get_propagation_reason M (-L);
                 case C of
                   Some C \<Rightarrow> do {
		     ASSERT (distinct_mset C \<and> \<not>tautology C);
		     RETURN (cach, (L, C - {#-L#}) # analyse, False)}
                 | None \<Rightarrow> do {
                     cach \<leftarrow> mark_failed_lits NU analyse cach;
                     RETURN (cach, [], False)
                 }
            }
          }
        })
        (cach, analysis, False)\<close>

definition lit_redundant_rec_spec where
  \<open>lit_redundant_rec_spec M NU D L =
    SPEC(\<lambda>(cach, analysis, b). (b \<longrightarrow> NU \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)) \<and>
     conflict_min_analysis_inv M cach NU D)\<close>

lemma WHILEIT_rule_stronger_inv_keepI':
  assumes
    \<open>wf R\<close> and
    \<open>I s\<close> and
    \<open>I' s\<close> and
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I' s')\<close> and
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I' s' \<longrightarrow>  (I s' \<and> (s', s) \<in> R))\<close> and
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> \<not> b s \<Longrightarrow> \<Phi> s\<close>
 shows \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> SPEC \<Phi>\<close>
proof -
  have A[iff]: \<open>f s \<le> SPEC (\<lambda>v. I' v \<and> I v \<and> (v, s) \<in> R) \<longleftrightarrow> f s \<le>  SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> for s
    by (rule cong[of \<open> \<lambda>n. f s \<le> n\<close>]) auto
  then have H: \<open>I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> for s
   using SPEC_rule_conjI [OF assms(4,5)[of s]] by auto
  have \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s\<close>
    by (metis (mono_tags, lifting) WHILEIT_weaken)

  also have \<open>WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s \<le> SPEC \<Phi>\<close>
    by (rule WHILEIT_rule) (use assms H in \<open>auto simp: \<close>)
  finally show ?thesis .
qed

lemma lit_redundant_rec_spec:
  fixes L :: \<open>'v literal\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N + NE, U + UE, D')\<close>
  assumes
    init_analysis: \<open>init_analysis = [(L, C)]\<close> and
    in_trail: \<open>Propagated (-L) (add_mset (-L) C) \<in> set M\<close> and
    \<open>conflict_min_analysis_inv M cach (N + NE + U + UE) D\<close> and
    L_D: \<open>L \<in># D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    unknown: \<open>cach (atm_of L) = SEEN_UNKNOWN\<close>
  shows
    \<open>lit_redundant_rec M (N + U) D cach init_analysis \<le>
      lit_redundant_rec_spec M (N + U + NE + UE) D L\<close>
proof -
  let ?N = \<open>N + NE + U + UE\<close>
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated (- L) (add_mset (- L) C) # M1\<close>
    using split_list[OF in_trail] by (auto 5 5)
  have \<open>a @ Propagated L mark # b = trail (M, N + NE, U + UE, D') \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have \<open>M1 \<Turnstile>as CNot C\<close>
    by (force simp: M)
  then have M_C: \<open>M \<Turnstile>as CNot C\<close>
    unfolding M by (simp add: true_annots_append_l)
  have \<open>set (get_all_mark_of_propagated (trail (M, N + NE, U + UE, D')))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N + NE, U + UE, D'))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
    by fast
  then have \<open>add_mset (-L) C \<in># ?N\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of \<open>add_mset (-L) C\<close> M]
    by (auto simp: clauses_def)
  then have NU_C: \<open>?N \<Turnstile>pm add_mset (- L) C\<close>
    by auto
  have n_d: \<open>no_dup M\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto

  let ?f = \<open>\<lambda>analysis. fold_mset (+) D (snd `# mset analysis)\<close>
  define I' where
    \<open>I' = (\<lambda>(cach :: 'v conflict_min_cach, analysis :: 'v conflict_min_analyse, b::bool).
        lit_redundant_inv M ?N D init_analysis (cach, analysis, b) \<and> M \<Turnstile>as CNot (?f analysis) \<and>
        distinct (map (atm_of o fst) analysis))\<close>
  define R where
    \<open>R = {((cach :: 'v conflict_min_cach, analysis :: 'v conflict_min_analyse, b::bool),
           (cach' :: 'v conflict_min_cach, analysis' :: 'v conflict_min_analyse, b' :: bool)).
           (analysis' \<noteq> [] \<and> (minimize_conflict_support M) (?f analysis') (?f analysis)) \<or>
           (analysis' \<noteq> [] \<and> analysis = tl analysis' \<and> snd (hd analysis') = {#}) \<or>
           (analysis' \<noteq> [] \<and> analysis = [])}\<close>
  have wf_R: \<open>wf R\<close>
  proof -
    have R: \<open>R =
              {((cach, analysis, b), (cach', analysis', b')).
                 analysis' \<noteq> [] \<and>analysis = []} \<union>
              ({((cach, analysis, b), (cach', analysis', b')).
                  analysis' \<noteq> [] \<and> (minimize_conflict_support M) (?f analysis') (?f analysis)} \<union>
              {((cach, analysis, b), (cach', analysis', b')).
                  analysis' \<noteq> [] \<and> analysis = tl analysis' \<and> snd (hd analysis') = {#}})\<close>
      (is \<open>_ = ?end \<union> (?Min \<union> ?ana)\<close>)
      unfolding R_def by auto
    have 1: \<open>wf {((cach:: 'v conflict_min_cach, analysis:: 'v conflict_min_analyse, b::bool),
         (cach':: 'v conflict_min_cach, analysis':: 'v conflict_min_analyse, b'::bool)).
       length analysis < length analysis'}\<close>
      using wf_if_measure_f[of \<open>measure length\<close>, of \<open>\<lambda>(_, xs, _). xs\<close>] apply auto
      apply (rule subst[of _ _ wf])
       prefer 2 apply assumption
      apply auto
      done

    have 2: \<open>wf {(C', C).minimize_conflict_support M C C'}\<close>
      by (rule wf_minimize_conflict_support[OF invs])
    from wf_if_measure_f[OF this, of ?f]
    have 2: \<open>wf {(C', C). minimize_conflict_support M (?f C) (?f C')}\<close>
      by auto
    from wf_fst_wf_pair[OF this, where 'b = bool]
    have \<open>wf {((analysis':: 'v conflict_min_analyse, _ :: bool),
               (analysis:: 'v conflict_min_analyse,  _:: bool)).
            (minimize_conflict_support M) (?f analysis) (?f analysis')}\<close>
      by blast
    from wf_snd_wf_pair[OF this, where 'b = \<open>'v conflict_min_cach\<close>]
    have \<open>wf {((M' :: 'v conflict_min_cach, N'), Ma, N).
      (case N' of
       (analysis' :: 'v conflict_min_analyse, _ :: bool) \<Rightarrow>
         \<lambda>(analysis, _).
            minimize_conflict_support M (fold_mset (+) D (snd `# mset analysis))
              (fold_mset (+) D (snd `# mset analysis'))) N}\<close>
      by blast
    then have wf_Min: \<open>wf ?Min\<close>
      apply (rule wf_subset)
      by auto
    have wf_ana: \<open>wf ?ana\<close>
      by (rule wf_subset[OF 1])  auto
    have wf: \<open>wf (?Min \<union> ?ana)\<close>
      apply (rule wf_union_compatible)
      subgoal by (rule wf_Min)
      subgoal by (rule wf_ana)
      subgoal by (auto elim!: neq_NilE)
      done
    have wf_end: \<open>wf ?end\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain f where f: \<open>(f (Suc i), f i) \<in> ?end\<close> for i
        unfolding wf_iff_no_infinite_down_chain by auto
      have \<open>fst (snd (f (Suc 0))) = []\<close>
        using f[of 0] by auto
      moreover have \<open>fst (snd (f (Suc 0))) \<noteq> []\<close>
        using f[of 1] by auto
      ultimately show False by blast
    qed
    show ?thesis
      unfolding R
      apply (rule wf_Un)
      subgoal by (rule wf_end)
      subgoal by (rule wf)
      subgoal by auto
      done
  qed
  have uL_M: \<open>- L \<in> lits_of_l M\<close>
    using in_trail by (force simp: lits_of_def)
  then have init_I: \<open>lit_redundant_inv M ?N D init_analysis (cach, init_analysis, False)\<close>
    using assms NU_C Propagated_in_trail_entailed[OF invs in_trail]
    unfolding lit_redundant_inv_def
    by (auto simp: ac_simps)

  have \<open>(minimize_conflict_support M) D (remove1_mset L (C + D))\<close>
    using minimize_conflict_support.resolve_propa[OF in_trail, of \<open>remove1_mset L D\<close>] L_D
    by (auto simp: ac_simps)

  then have init_I': \<open>I' (cach, init_analysis, False)\<close>
    using M_D L_D M_C init_I unfolding I'_def by (auto simp: init_analysis)

  have hd_M: \<open>- fst (hd analyse) \<in> lits_of_l M\<close>
    if
      inv_I': \<open>I' s\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, ba)\<close> and
      nempty: \<open>analyse \<noteq> []\<close>
    for analyse s s' ba cach
  proof -
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> ba \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    show ?thesis
      using stack_hd nempty by (cases analyse) auto
  qed

  have all_removed: \<open>lit_redundant_inv M ?N D init_analysis
       (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE), tl analysis, True)\<close> (is ?I) and
     all_removed_I': \<open>I' (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE), tl analysis, True)\<close>
       (is ?I') and
     all_removed_J: \<open>lit_redundant_rec_loop_inv M (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE), tl analysis, True)\<close> (is ?J)
    if
      inv_I': \<open>I' s\<close> and inv_J: \<open>lit_redundant_rec_loop_inv M s\<close>
      \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close>
         \<open>s' = (analysis, b)\<close> and
      nemtpy_stack: \<open>analysis \<noteq> []\<close> and
      finished: \<open>snd (hd analysis) = {#}\<close>
    for s cach s' analysis b
  proof -
    obtain L ana' where analysis: \<open>analysis = (L, {#}) # ana'\<close>
      using nemtpy_stack finished by (cases analysis)  auto
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analysis\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analysis\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analysis\<close> and
      last_analysis: \<open>analysis \<noteq> [] \<longrightarrow> fst (last analysis) = fst (hd init_analysis)\<close> and
      b: \<open>analysis = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close> and
      dist: \<open>distinct (map (atm_of o fst) analysis)\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    obtain C where
       NU_C: \<open>?N \<Turnstile>pm add_mset (-L) C\<close> and
       IH: \<open>\<And>K. K \<in># C \<Longrightarrow> ?N \<Turnstile>pm add_mset (-K) (filter_to_poslev M L D) \<or>
         K \<in># filter_to_poslev M L D\<close> and
       index_K: \<open>K\<in>#C \<Longrightarrow> index_in_trail M K < index_in_trail M L\<close> and
       L_M: \<open>-L \<in> lits_of_l M\<close> for K
      using stack_hd unfolding analysis by auto

    have NU_D: \<open>?N \<Turnstile>pm add_mset (- fst (hd analysis)) (filter_to_poslev M (fst (hd analysis)) D)\<close>
      using conflict_minimize_intermediate_step_filter_to_poslev[OF _ NU_C, simplified, OF index_K]
        IH
      unfolding analysis by auto
    have ana': \<open>conflict_min_analysis_stack M ?N D (tl analysis)\<close>
      using ana by (auto simp: conflict_min_analysis_stack_tl)
    have \<open>-fst (hd analysis) \<in> lits_of_l M\<close>
      using L_M by (auto simp: analysis I'_def s ana)
    then have cach':
      \<open>conflict_min_analysis_inv M (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE)) ?N D\<close>
      using NU_D n_d by (auto simp: conflict_min_analysis_inv_update_removable cach)
    have stack_hd': \<open>conflict_min_analysis_stack_hd M ?N D ana'\<close>
    proof (cases \<open>ana' = []\<close>)
      case True
      then show ?thesis by auto
    next
      case False
      then obtain L' C' ana'' where ana'': \<open>ana' = (L', C') # ana''\<close>
        by (cases ana'; cases \<open>hd ana'\<close>) auto
      then obtain E' where
         NU_E': \<open>?N \<Turnstile>pm add_mset (- L') E'\<close> and
         \<open>\<forall>K\<in>#E' - add_mset L C'. ?N \<Turnstile>pm add_mset (- K) (filter_to_poslev M L' D) \<or>
           K \<in># filter_to_poslev M L' D\<close> and
         index_C': \<open>\<forall>K\<in>#E'. index_in_trail M K < index_in_trail M L'\<close> and
         index_L'_L: \<open>index_in_trail M L < index_in_trail M L'\<close> and
         C'_E': \<open>C' \<subseteq># E'\<close> and
         uL'_M: \<open>- L' \<in> lits_of_l M\<close>
         using stack by (auto simp: analysis ana'')
       moreover have \<open>?N \<Turnstile>pm add_mset (- L) (filter_to_poslev M L D)\<close>
         using NU_D analysis by auto
       moreover have \<open>K \<in># E' - C' \<Longrightarrow> K \<in># E' - add_mset L C' \<or> K = L\<close> for K
         by (cases \<open>L \<in># E'\<close>)
           (fastforce simp: minus_notin_trivial dest!: multi_member_split[of L]
             dest: in_remove1_msetI)+
       moreover have \<open>K \<in># E' - C' \<Longrightarrow> index_in_trail M K \<le> index_in_trail M L'\<close> for K
         by (meson in_diffD index_C' less_or_eq_imp_le)
       ultimately have \<open>K \<in># E' - C' \<Longrightarrow> ?N \<Turnstile>pm add_mset (- K) (filter_to_poslev M L' D) \<or>
             K \<in># filter_to_poslev M L' D\<close> for K
         using filter_to_poslev_mono_entailement_add_mset[of M K L']
           filter_to_poslev_mono[of M L L']
         by fastforce
       then show ?thesis
         using NU_E' uL'_M index_C' C'_E' unfolding ana'' by (auto intro!: exI[of _ E'])
    qed

    have \<open>fst (hd init_analysis) = fst (last (tl analysis))\<close> if \<open>tl analysis \<noteq> []\<close>
      using last_analysis tl_last[symmetric, OF that] that unfolding ana' by auto
    then show ?I
      using ana' cach' last_analysis stack_hd' dist unfolding lit_redundant_inv_def
      by (cases ana'; auto simp: analysis atm_of_eq_atm_of split: if_splits)
    then show I': ?I'
      using inv_I' unfolding I'_def s by (auto simp: analysis)
    have \<open>distinct (map (\<lambda>x. - fst x) (tl analysis))\<close>
      using dist distinct_mapI[of \<open>atm_of o uminus\<close> \<open>map (uminus o fst) (tl analysis)\<close>]
       conflict_min_analysis_stack_neg[OF ana'] by (auto simp: comp_def map_tl
       simp flip: distinct_mset_image_mset)
    then show ?J
      using inv_J unfolding lit_redundant_rec_loop_inv_def prod.case s
      apply (subst distinct_subseteq_iff[symmetric])
      using conflict_min_analysis_stack_neg[OF ana']  no_dup_distinct[OF n_d] dist
      by (force simp: comp_def entails_CNot_negate_ann_lits negate_ann_lits_def
        analysis ana'
       simp flip: distinct_mset_image_mset)+
  qed
  have all_removed_R:
      \<open>((cach(atm_of (fst (hd analyse)) := SEEN_REMOVABLE), tl analyse, True), s) \<in> R\<close>
    if
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> and
      nempty: \<open>analyse \<noteq> []\<close> and
      finished: \<open>snd (hd analyse) = {#}\<close>
    for s cach s' analyse b
    using nempty finished unfolding R_def s by auto
  have
    seen_removable_inv: \<open>lit_redundant_inv M ?N D init_analysis (cach, ana, False)\<close> (is ?I) and
    seen_removable_I': \<open>I' (cach, ana, False)\<close> (is ?I') and
    seen_removable_R: \<open>((cach, ana, False), s) \<in> R\<close> (is ?R) and
    seen_removable_J: \<open>lit_redundant_rec_loop_inv M (cach, ana, False)\<close> (is ?J)
    if
      inv_I': \<open>I' s\<close> and inv_J: \<open>lit_redundant_rec_loop_inv M s\<close> and
      cond: \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> \<open>x = (L, ana)\<close> and
      nemtpy_stack: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      next_lit: \<open>case x of
        (L, ana) \<Rightarrow> L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and> ana \<noteq> [] \<and>
          hd ana = (fst (hd analyse), remove1_mset L (snd (hd analyse)))\<close> and
      lev0_removable: \<open>get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D\<close>
    for s cach s' analyse b x L ana
  proof -
    obtain K C ana' where analysis: \<open>analyse = (K, C) # ana'\<close>
      using nemtpy_stack by (cases analyse) auto
    have ana': \<open>ana = (K, remove1_mset L C) # ana'\<close> and L_C: \<open>L \<in># C\<close>
      using next_lit unfolding s by (cases ana; auto simp: analysis)+
    have
      cach: \<open>conflict_min_analysis_inv M cach (?N) D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close> and
      dist: \<open>distinct (map (atm_of \<circ> fst) analyse)\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def prod.case by auto

    have last_analysis': \<open>ana \<noteq> [] \<Longrightarrow> fst (hd init_analysis) = fst (last ana)\<close>
      using last_analysis next_lit unfolding analysis s
      by (cases ana) (auto split: if_splits)
    have uL_M: \<open>-L \<in> lits_of_l M\<close>
      using inv_I' L_C unfolding analysis ana s I'_def
      by (auto dest!: multi_member_split)
    have uK_M: \<open>- K \<in> lits_of_l M\<close>
      using stack_hd unfolding analysis by auto
    consider
      (lev0) \<open>get_level M L = 0\<close> |
      (Removable) \<open>cach (atm_of L) = SEEN_REMOVABLE\<close> |
      (in_D) \<open>L \<in># D\<close>
      using lev0_removable by fast
    then have H: \<open>\<exists>CK. ?N \<Turnstile>pm add_mset (- K) CK \<and>
           (\<forall>Ka\<in>#CK - remove1_mset L C. ?N \<Turnstile>pm  (filter_to_poslev M K D) + {#- Ka#} \<or>
             Ka \<in># filter_to_poslev M K D) \<and>
           (\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K) \<and>
           remove1_mset L C \<subseteq># CK\<close>
      (is \<open>\<exists>C. ?P C\<close>)
    proof cases
      case Removable
      then have L: \<open>?N \<Turnstile>pm add_mset (- L) (filter_to_poslev M L D)\<close>
        using cach uL_M unfolding conflict_min_analysis_inv_def by auto
      obtain CK where
        \<open>?N \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>K'\<in>#CK - C. ?N \<Turnstile>pm (filter_to_poslev M K D) + {#- K'#} \<or> K' \<in># filter_to_poslev M K D\<close> and
        index_CK: \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K\<close> and
        C_CK: \<open>C \<subseteq># CK\<close>
        using stack_hd unfolding analysis by auto
      moreover have \<open>remove1_mset L C \<subseteq># CK\<close>
        using C_CK by (meson diff_subset_eq_self subset_mset.dual_order.trans)
      moreover have \<open>index_in_trail M L < index_in_trail M K\<close>
        using index_CK C_CK L_C unfolding analysis ana' by auto
      moreover have index_CK': \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka \<le> index_in_trail M K\<close>
        using index_CK by auto
      ultimately have \<open>?P CK\<close>
         using filter_to_poslev_mono_entailement_add_mset[of M _ _]
           filter_to_poslev_mono[of M K L]
         using L L_C C_CK by (auto simp: minus_remove1_mset_if)
      then show ?thesis by blast
    next
      assume lev0: \<open>get_level M L = 0\<close>
      have \<open>M \<Turnstile>as CNot (?f analyse)\<close>
        using inv_I' unfolding I'_def s by auto
      then have \<open>-L \<in> lits_of_l M\<close>
        using next_lit unfolding analysis s by (auto dest: multi_member_split)
      then have \<open>?N \<Turnstile>pm {#-L#}\<close>
        using lev0 cdcl\<^sub>W_restart_mset.literals_of_level0_entailed[OF invs, of \<open>-L\<close>]
        by (auto simp: clauses_def ac_simps)
      moreover obtain CK where
        \<open>?N \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>K'\<in>#CK - C. ?N \<Turnstile>pm (filter_to_poslev M K D) + {#- K'#} \<or> K' \<in># filter_to_poslev M K D\<close> and
        \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K\<close> and
        C_CK: \<open>C \<subseteq># CK\<close>
        using stack_hd unfolding analysis by auto
      moreover have \<open>remove1_mset L C \<subseteq># CK\<close>
        using C_CK by (meson diff_subset_eq_self subset_mset.order_trans)
      ultimately have \<open>?P CK\<close>
        by (auto simp: minus_remove1_mset_if intro: conflict_minimize_intermediate_step)
      then show ?thesis by blast
    next
      case in_D
      obtain CK where
        \<open>?N \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>Ka\<in>#CK - C. ?N \<Turnstile>pm (filter_to_poslev M K D) + {#- Ka#} \<or> Ka \<in># filter_to_poslev M K D\<close> and
        index_CK: \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K\<close> and
        C_CK: \<open>C \<subseteq># CK\<close>
        using stack_hd unfolding analysis by auto
      moreover have \<open>remove1_mset L C \<subseteq># CK\<close>
        using C_CK by (meson diff_subset_eq_self subset_mset.order_trans)
      moreover have \<open>L \<in># filter_to_poslev M K D\<close>
        using in_D L_C index_CK C_CK by (fastforce simp: filter_to_poslev_def)

      ultimately have \<open>?P CK\<close>
        using in_D
         using filter_to_poslev_mono_entailement_add_mset[of M L K]
         by (auto simp: minus_remove1_mset_if dest!:
             intro: conflict_minimize_intermediate_step)
      then show ?thesis by blast
    qed note H = this
    have stack': \<open>conflict_min_analysis_stack M ?N D ana\<close>
      using stack unfolding ana' analysis by (cases ana') auto
    have stack_hd': \<open>conflict_min_analysis_stack_hd M ?N D ana\<close>
      using H uL_M uK_M unfolding ana' by auto

    show ?I
      using last_analysis' cach stack' stack_hd' unfolding lit_redundant_inv_def s
      by auto
    have \<open>M \<Turnstile>as CNot (?f ana)\<close>
      using inv_I' unfolding I'_def s ana analysis ana'
      by (cases \<open>L \<in># C\<close>) (auto dest!: multi_member_split)
    then show ?I'
      using inv_I' \<open>?I\<close> unfolding I'_def s by (auto simp: analysis ana')

    show ?R
      using next_lit
      unfolding R_def s by (auto simp: ana' analysis dest!: multi_member_split
          intro: minimize_conflict_support.intros)
    have \<open>distinct (map (\<lambda>x. - fst x) ana)\<close>
      using dist distinct_mapI[of \<open>atm_of o uminus\<close> \<open>map (uminus o fst) (tl analyse)\<close>]
       conflict_min_analysis_stack_neg[OF stack'] by (auto simp: comp_def map_tl
          analysis ana'
       simp flip: distinct_mset_image_mset)
    then show ?J
      using inv_J unfolding lit_redundant_rec_loop_inv_def prod.case s
      apply (subst distinct_subseteq_iff[symmetric])
      using conflict_min_analysis_stack_neg[OF stack'] no_dup_distinct[OF n_d]
      apply (auto simp: comp_def entails_CNot_negate_ann_lits negate_ann_lits_def
       simp flip: distinct_mset_image_mset)
     apply (force simp add: analysis ana ana')
     done

  qed
  have
    failed_I: \<open>lit_redundant_inv M ?N D init_analysis
       (cach', [], False)\<close> (is ?I) and
    failed_I': \<open>I' (cach', [], False)\<close> (is ?I') and
    failed_R: \<open>((cach', [], False), s) \<in> R\<close> (is ?R) and
    failed_J: \<open>lit_redundant_rec_loop_inv M (cach', [], False)\<close> (is ?J)
    if
      inv_I': \<open>I' s\<close> and inv_J: \<open>lit_redundant_rec_loop_inv M s\<close> and
      cond: \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> and
      nempty: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      \<open>case x of (L, ana) \<Rightarrow> L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and>
        ana \<noteq> [] \<and> hd ana = (fst (hd analyse), remove1_mset L (snd (hd analyse)))\<close> and
      \<open>x = (L, ana)\<close> and
      \<open>\<not> (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)\<close> and
      cach_update: \<open>\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE\<close>
    for s cach s' analyse b x L ana E cach'
  proof -
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    have \<open>conflict_min_analysis_inv M cach' ?N D\<close>
      using cach cach_update by (auto simp: conflict_min_analysis_inv_def)
    moreover have \<open>conflict_min_analysis_stack M ?N D []\<close>
      by simp
    ultimately show ?I
      unfolding lit_redundant_inv_def by simp
    then show ?I'
      using M_D unfolding I'_def by auto
    show ?R
      using nempty unfolding R_def s by auto
    show ?J
      by (auto simp: lit_redundant_rec_loop_inv_def)
  qed
  have is_propagation_inv: \<open>lit_redundant_inv M ?N D init_analysis
       (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?I) and
    is_propagation_I': \<open>I' (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?I') and
    is_propagation_R: \<open>((cach, (L, remove1_mset (-L) E') # ana, False), s) \<in> R\<close> (is ?R) and
    is_propagation_dist: \<open>distinct_mset E'\<close> (is ?dist) and
    is_propagation_tauto: \<open>\<not>tautology E'\<close> (is ?tauto) and
    is_propagation_J': \<open>lit_redundant_rec_loop_inv M (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?J)
    if
      inv_I': \<open>I' s\<close> and inv_J: \<open>lit_redundant_rec_loop_inv M s\<close> and
      \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> \<open>x = (L, ana)\<close> and
      nemtpy_stack: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      next_lit: \<open>case x of (L, ana) \<Rightarrow>
       L \<in># snd (hd analyse) \<and>
       tl ana = tl analyse \<and>
       ana \<noteq> [] \<and>
       hd ana =
       (fst (hd analyse),
        remove1_mset L (snd (hd analyse)))\<close> and
      \<open>\<not> (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)\<close> and
      E: \<open>E \<noteq> None \<longrightarrow> Propagated (- L) (the E) \<in> set M\<close> \<open>E = Some E'\<close> and
      st: \<open>cach (atm_of L) = SEEN_UNKNOWN\<close>
    for s cach s' analyse b x L ana E E'
  proof -
    obtain K C ana' where analysis: \<open>analyse = (K, C) # ana'\<close>
      using nemtpy_stack by (cases analyse) auto
    have ana': \<open>ana = (K, remove1_mset L C) # ana'\<close>
      using next_lit unfolding s by (cases ana) (auto simp: analysis)
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close> and
      dist_ana: \<open>distinct (map (atm_of \<circ> fst) analyse)\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    have
      NU_E: \<open>?N \<Turnstile>pm add_mset (- L) (remove1_mset (-L) E')\<close> and
      uL_E: \<open>-L \<in># E'\<close> and
      M_E': \<open>M \<Turnstile>as CNot (remove1_mset (- L) E')\<close> and
      tauto: \<open>\<not> tautology E'\<close> and
      dist: \<open>distinct_mset E'\<close> and
      lev_E': \<open>K \<in># remove1_mset (- L) E' \<Longrightarrow> index_in_trail M K < index_in_trail M (- L)\<close> for K
      using Propagated_in_trail_entailed[OF invs, of \<open>-L\<close> E'] E by (auto simp: ac_simps)
    have uL_M: \<open>- L \<in> lits_of_l M\<close>
      using next_lit inv_I' unfolding s analysis I'_def by (auto dest!: multi_member_split)
    obtain C' where
      \<open>?N \<Turnstile>pm add_mset (- K) C'\<close> and
      \<open>\<forall>Ka\<in>#C'. index_in_trail M Ka < index_in_trail M K\<close> and
      \<open>C \<subseteq># C'\<close> and
      \<open>\<forall>Ka\<in>#C' - C.
        ?N \<Turnstile>pm add_mset (- Ka) (filter_to_poslev M K D) \<or>
        Ka \<in># filter_to_poslev M K D\<close> and
      uK_M: \<open>- K \<in> lits_of_l M\<close>
      using stack_hd
      unfolding s ana'[symmetric]
      by (auto simp: analysis ana' conflict_min_analysis_stack_change_hd)

    then have cmas: \<open>conflict_min_analysis_stack M ?N D ((L, remove1_mset (-L) E') # ana)\<close>
      using stack E next_lit NU_E uL_E uL_M
        filter_to_poslev_mono_entailement_add_mset[of M _ _ \<open>set_mset ?N\<close> _ D]
        filter_to_poslev_mono[of M ] uK_M
      unfolding s ana'[symmetric] prod.case
      by (auto simp: analysis ana' conflict_min_analysis_stack_change_hd)
    moreover have \<open>conflict_min_analysis_stack_hd M ?N D ((L, remove1_mset (- L) E') # ana)\<close>
      using NU_E lev_E' uL_M by (auto intro!:exI[of _ \<open>remove1_mset (- L) E'\<close>])
    moreover have \<open>fst (hd init_analysis) = fst (last ((L, remove1_mset (- L) E') # ana))\<close>
      using last_analysis unfolding analysis ana' by auto
    ultimately show ?I
      using cach b unfolding lit_redundant_inv_def analysis by auto
    moreover have \<open>L \<noteq> K\<close>
       using cmas
       unfolding ana' conflict_min_analysis_stack.simps(3) by blast
    moreover have \<open>L \<noteq> -K\<close>
       using cmas
       unfolding ana' conflict_min_analysis_stack.simps(3) by auto
    ultimately show ?I'
      using M_E' inv_I' conflict_min_analysis_stack_distinct_fst[OF cmas]
      unfolding I'_def s ana analysis ana'
      by (auto simp: true_annot_CNot_diff atm_of_eq_atm_of uminus_lit_swap)

    have \<open>L \<in># C\<close> and in_trail: \<open>Propagated (- L) (the E) \<in> set M\<close> and EE': \<open>the E = E'\<close>
      using next_lit E by (auto simp: analysis ana' s)
    then obtain E'' C' where
      E': \<open>E' = add_mset (-L) E''\<close> and
      C: \<open>C = add_mset L C'\<close>
      using uL_E by (blast dest: multi_member_split)

    have \<open>minimize_conflict_support M (C + fold_mset (+) D (snd `# mset ana'))
           (remove1_mset (- L) E' + (remove1_mset L C + fold_mset (+) D (snd `# mset ana')))\<close>
      using minimize_conflict_support.resolve_propa[OF in_trail,
        of \<open>C' + fold_mset (+) D (snd `# mset ana')\<close>]
      unfolding C E' EE'
      by (auto simp: ac_simps)

    then show ?R
      using nemtpy_stack unfolding s analysis ana' by (auto simp: R_def
          intro: resolve_propa)
    have \<open>distinct (map (\<lambda>x. - fst x) analyse)\<close>
      using dist_ana distinct_mapI[of \<open>atm_of o uminus\<close> \<open>map (uminus o fst) analyse\<close>]
       conflict_min_analysis_stack_neg[OF cmas] unfolding analysis ana'
       by (auto simp: comp_def map_tl
          simp flip: distinct_mset_image_mset)
    then show ?J
      using inv_J st unfolding lit_redundant_rec_loop_inv_def prod.case s
      apply (intro conjI)
      apply (subst distinct_subseteq_iff[symmetric])
      using conflict_min_analysis_stack_neg[OF cmas] no_dup_distinct[OF n_d] uL_M
        \<open>L \<noteq> -K\<close> \<open>L \<noteq> K\<close>  conflict_min_analysis_stack_distinct_fst[OF cmas]
      apply (auto simp: comp_def entails_CNot_negate_ann_lits
        negate_ann_lits_def lits_of_def uminus_lit_swap
       simp flip: distinct_mset_image_mset)[3]
     apply (clarsimp_all simp add: analysis ana')[]
    using that by (clarsimp_all simp add: analysis ana')[]

    show ?tauto
      using tauto .
    show ?dist
      using dist .
  qed
  have length_aa_le: \<open>length aa \<le> length M\<close>
    if
      \<open>I' s\<close> and
      \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>s = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>aa \<noteq> []\<close> for s a b aa ba
  proof -
    have \<open>M \<Turnstile>as CNot (fst `# mset aa)\<close> and \<open>distinct (map (atm_of o fst) aa)\<close> and
       \<open>distinct (map fst aa)\<close> and
      \<open>conflict_min_analysis_stack M (N + NE + U + UE) D aa\<close>
      using distinct_mapI[of \<open>atm_of\<close> \<open>map fst aa\<close>]
      using that by (auto simp: I'_def lit_redundant_inv_def
        dest: conflict_min_analysis_stack_neg)

    then have \<open>set (map fst aa) \<subseteq> uminus ` lits_of_l M\<close>
      by (auto simp: true_annots_true_cls_def_iff_negation_in_model lits_of_def image_image
          uminus_lit_swap
         dest!: multi_member_split)
    from card_mono[OF _ this] have \<open>length (map fst aa) \<le> length M\<close>
      using \<open>distinct (map (fst) aa)\<close> distinct_card[of \<open>map fst aa\<close>] n_d
     by (auto simp: card_image[OF lit_of_inj_on_no_dup[OF n_d]] lits_of_def image_image
        distinct_card[OF no_dup_imp_distinct])
    then show \<open>?thesis\<close> by auto
  qed

  show ?thesis
    unfolding lit_redundant_rec_def lit_redundant_rec_spec_def mark_failed_lits_def
      get_literal_and_remove_of_analyse_def get_propagation_reason_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = R and I' = I'])
      \<comment> \<open>Well-foundness\<close>
    subgoal by (rule wf_R)
    subgoal using assms by (auto simp: lit_redundant_rec_loop_inv_def lits_of_def
       dest!: multi_member_split)
    subgoal by (rule init_I')
    subgoal by auto
    subgoal by (rule length_aa_le)
      \<comment> \<open>Assertion:\<close>
    subgoal by (rule hd_M)
        \<comment> \<open>We finished one stage:\<close>
    subgoal by (rule all_removed_J) 
    subgoal by (rule all_removed_I') 
    subgoal by (rule all_removed_R)
      \<comment> \<open>Assertion:\<close>
    subgoal for s cach s' analyse ba
      by (cases \<open>analyse\<close>) (auto simp: I'_def dest!: multi_member_split)

        \<comment> \<open>Cached or level 0:\<close>
    subgoal by (rule seen_removable_J)
    subgoal by (rule seen_removable_I')
    subgoal by (rule seen_removable_R)
        \<comment> \<open>Failed:\<close>
    subgoal by (rule failed_J)
    subgoal by (rule failed_I')
    subgoal by (rule failed_R)
    subgoal for s a b aa ba x ab bb xa by (cases \<open>a (atm_of ab)\<close>) auto
    subgoal by (rule failed_J)
    subgoal by (rule failed_I')
    subgoal by (rule failed_R)
        \<comment> \<open>The literal was propagated:\<close>
    subgoal by (rule is_propagation_dist)
    subgoal by (rule is_propagation_tauto)
    subgoal by (rule is_propagation_J')
    subgoal by (rule is_propagation_I')
    subgoal by (rule is_propagation_R)
        \<comment> \<open>End of Loop invariant:\<close>
    subgoal
      using uL_M by (auto simp: lit_redundant_inv_def conflict_min_analysis_inv_def init_analysis
          I'_def ac_simps)
    subgoal by (auto simp: lit_redundant_inv_def conflict_min_analysis_inv_def init_analysis
          I'_def ac_simps)
    done
qed

definition literal_redundant_spec where
  \<open>literal_redundant_spec M NU D L =
    SPEC(\<lambda>(cach, analysis, b). (b \<longrightarrow> NU \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)) \<and>
     conflict_min_analysis_inv M cach NU D)\<close>

definition literal_redundant where
  \<open>literal_redundant M NU D cach L = do {
     ASSERT(-L \<in> lits_of_l M);
     if get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       C \<leftarrow> get_propagation_reason M (-L);
       case C of
         Some C \<Rightarrow> do{
	   ASSERT(distinct_mset C \<and> \<not>tautology C);
	   lit_redundant_rec M NU D cach [(L, C - {#-L#})]}
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
     }
    }
  }\<close>

lemma true_clss_cls_add_self: \<open>NU \<Turnstile>p D' + D' \<longleftrightarrow> NU \<Turnstile>p D'\<close>
  by (metis subset_mset.sup_idem true_clss_cls_sup_iff_add)

lemma true_clss_cls_add_add_mset_self: \<open>NU \<Turnstile>p add_mset L (D' + D') \<longleftrightarrow> NU \<Turnstile>p add_mset L D'\<close>
  using true_clss_cls_add_self true_clss_cls_mono_r by fastforce


lemma filter_to_poslev_remove1:
  \<open>filter_to_poslev M L (remove1_mset K D) =
      (if index_in_trail M K \<le> index_in_trail M L then remove1_mset K (filter_to_poslev M L D)
   else filter_to_poslev M L D)\<close>
  unfolding filter_to_poslev_def
  by (auto simp: multiset_filter_mono2)


lemma filter_to_poslev_add_mset:
  \<open>filter_to_poslev M L (add_mset K D) =
      (if index_in_trail M K < index_in_trail M L then add_mset K (filter_to_poslev M L D)
   else filter_to_poslev M L D)\<close>
  unfolding filter_to_poslev_def
  by (auto simp: multiset_filter_mono2)

lemma filter_to_poslev_conflict_min_analysis_inv:
  assumes
    L_D: \<open>L \<in># D\<close> and
    NU_uLD: \<open>N+U \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)\<close> and
    inv: \<open>conflict_min_analysis_inv M cach (N + U) D\<close>
  shows \<open>conflict_min_analysis_inv M cach (N + U) (remove1_mset L D)\<close>
  unfolding conflict_min_analysis_inv_def
proof (intro allI impI)
  fix K
  assume \<open>-K \<in> lits_of_l M\<close> and \<open>cach (atm_of K) = SEEN_REMOVABLE\<close>
  then have K: \<open>N + U \<Turnstile>pm add_mset (- K) (filter_to_poslev M K D)\<close>
    using inv unfolding conflict_min_analysis_inv_def by blast
  obtain D' where D: \<open>D = add_mset L D'\<close>
    using multi_member_split[OF L_D] by blast
  have \<open>N + U \<Turnstile>pm add_mset (- K) (filter_to_poslev M K D')\<close>
  proof (cases \<open>index_in_trail M L < index_in_trail M K\<close>)
    case True
    then have \<open>N + U \<Turnstile>pm add_mset (- K) (add_mset L (filter_to_poslev M K D'))\<close>
      using K by (auto simp: filter_to_poslev_add_mset D)
    then have 1: \<open>N + U \<Turnstile>pm add_mset L (add_mset (-K) (filter_to_poslev M K D'))\<close>
      by (simp add: add_mset_commute)
    have H: \<open>index_in_trail M L \<le> index_in_trail M K\<close>
      using True by simp
    have 2: \<open>N+U \<Turnstile>pm add_mset (-L) (filter_to_poslev M K D')\<close>
      using filter_to_poslev_mono_entailement_add_mset[OF H] NU_uLD
      by (metis (no_types, hide_lams) D NU_uLD filter_to_poslev_add_mset
          order_less_irrefl)
    show ?thesis
      using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF 2 1]
      by (auto simp: true_clss_cls_add_add_mset_self)
  next
    case False
    then show ?thesis using K by (auto simp: filter_to_poslev_add_mset D split: if_splits)
  qed
  then show \<open>N + U \<Turnstile>pm add_mset (- K) (filter_to_poslev M K (remove1_mset L D))\<close>
    by (simp add: D)
qed

lemma can_filter_to_poslev_can_remove:
  assumes
    L_D: \<open>L \<in># D\<close> and
    \<open>M \<Turnstile>as CNot D\<close> and
    NU_D: \<open>NU \<Turnstile>pm D\<close> and
    NU_uLD: \<open>NU \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)\<close>
  shows \<open>NU \<Turnstile>pm remove1_mset L D\<close>
proof -
  obtain D' where
    D: \<open>D = add_mset L D'\<close>
    using multi_member_split[OF L_D] by blast
  then have \<open>filter_to_poslev M L D \<subseteq># D'\<close>
    by (auto simp: filter_to_poslev_def)
  then have \<open>NU \<Turnstile>pm add_mset (-L) D'\<close>
    using NU_uLD true_clss_cls_mono_r[of _ \<open> add_mset (- L) (filter_to_poslev M (-L) D)\<close> ]
    by (auto simp: mset_subset_eq_exists_conv)
  from true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF this, of D']
  show \<open>NU \<Turnstile>pm remove1_mset L D\<close>
    using NU_D by (auto simp: D true_clss_cls_add_self)
qed

lemma literal_redundant_spec:
  fixes L :: \<open>'v literal\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N + NE, U + UE, D')\<close>
  assumes
    inv: \<open>conflict_min_analysis_inv M cach (N + NE + U + UE) D\<close> and
    L_D: \<open>L \<in># D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close>
  shows
    \<open>literal_redundant M (N + U) D cach L \<le> literal_redundant_spec M (N + U + NE + UE) D L\<close>
proof -
  have lit_redundant_rec: \<open>lit_redundant_rec M (N + U) D cach [(L, remove1_mset (- L) E')]
      \<le> literal_redundant_spec M (N + U + NE + UE) D L\<close>
    if
      E: \<open>E \<noteq> None \<longrightarrow> Propagated (- L) (the E) \<in> set M\<close> and
      E': \<open>E = Some E'\<close> and
      failed: \<open>\<not> (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE)\<close>
        \<open>cach (atm_of L) \<noteq> SEEN_FAILED\<close>
    for E E'
  proof -
    have
      [simp]: \<open>-L \<in># E'\<close> and
      in_trail: \<open>Propagated (- L) (add_mset (-L) (remove1_mset (-L) E')) \<in> set M\<close>
      using Propagated_in_trail_entailed[OF invs, of \<open>-L\<close> E'] E E'
      by auto
    have H: \<open>lit_redundant_rec_spec M (N + U + NE + UE) D L \<le>
       literal_redundant_spec M (N + U + NE + UE) D L\<close>
      by (auto simp: lit_redundant_rec_spec_def literal_redundant_spec_def ac_simps)
    show ?thesis
      apply (rule order.trans)
       apply (rule lit_redundant_rec_spec[OF invs _ in_trail])
      subgoal ..
      subgoal by (rule inv)
      subgoal using assms by fast
      subgoal by (rule M_D)
      subgoal using failed by (cases \<open>cach (atm_of L)\<close>) auto
      subgoal unfolding literal_redundant_spec_def[symmetric] by (rule H)
      done
  qed

  have
    L_dist: \<open>distinct_mset (C)\<close> and
    L_tauto: \<open>\<not>tautology C\<close>
  if
    in_trail: \<open>Propagated (- L) C \<in> set M\<close>
    for C
    using that
    Propagated_in_trail_entailed[of M \<open>N+NE\<close> \<open>U+UE\<close> \<open>D'\<close> \<open>-L\<close> \<open>C\<close>] invs
    by (auto simp: )
  have uL_M: \<open>-L \<in> lits_of_l M\<close>
    using L_D M_D by (auto dest!: multi_member_split)
  show ?thesis
    unfolding literal_redundant_def get_propagation_reason_def literal_redundant_spec_def
    apply (refine_vcg)
    subgoal using uL_M .
    subgoal
      using inv uL_M cdcl\<^sub>W_restart_mset.literals_of_level0_entailed[OF invs, of \<open>-L\<close>]
        true_clss_cls_mono_r'
      by (fastforce simp: mark_failed_lits_def conflict_min_analysis_inv_def
          clauses_def ac_simps)
    subgoal using inv by (auto simp: ac_simps)
    subgoal by auto
    subgoal using inv by (auto simp: ac_simps)
    subgoal using inv by (auto simp: mark_failed_lits_def conflict_min_analysis_inv_def)
    subgoal using inv by (auto simp: mark_failed_lits_def conflict_min_analysis_inv_def ac_simps)
    subgoal using L_dist by simp
    subgoal using L_tauto by simp
    subgoal for E E'
      unfolding literal_redundant_spec_def[symmetric]
      by (rule lit_redundant_rec)
    done
qed

definition set_all_to_list where
  \<open>set_all_to_list e ys = do {
     S \<leftarrow> WHILE\<^bsup>\<lambda>(i, xs). i \<le> length xs \<and> (\<forall>x \<in> set (take i xs). x = e) \<and> length xs = length ys\<^esup>
       (\<lambda>(i, xs). i < length xs)
       (\<lambda>(i, xs). do {
         ASSERT(i < length xs);
         RETURN(i+1, xs[i := e])
        })
       (0, ys);
    RETURN (snd S)
    }\<close>

lemma
  \<open>set_all_to_list e ys \<le> SPEC(\<lambda>xs. length xs = length ys \<and> (\<forall>x \<in> set xs. x = e))\<close>
  unfolding set_all_to_list_def
  apply (refine_vcg)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: take_Suc_conv_app_nth list_update_append)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition get_literal_and_remove_of_analyse_wl
   :: \<open>'v clause_l \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> 'v literal \<times> (nat \<times> nat \<times> nat \<times> nat) list\<close> where
  \<open>get_literal_and_remove_of_analyse_wl C analyse =
    (let (i, k, j, ln) = last analyse in
     (C ! j, analyse[length analyse - 1 := (i, k, j + 1, ln)]))\<close>


definition mark_failed_lits_wl
where
  \<open>mark_failed_lits_wl NU analyse cach = SPEC(\<lambda>cach'.
     (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>


definition lit_redundant_rec_wl_ref where
  \<open>lit_redundant_rec_wl_ref NU analyse \<longleftrightarrow>
    (\<forall>(i, k, j, ln) \<in> set analyse. j \<le> ln \<and> i \<in># dom_m NU \<and> i > 0 \<and>
      ln \<le> length (NU \<propto> i) \<and> k < length (NU \<propto> i) \<and>
    distinct (NU \<propto> i) \<and>
    \<not>tautology (mset (NU \<propto> i))) \<and>
    (\<forall>(i, k, j, ln) \<in> set (butlast analyse). j > 0)\<close>

definition lit_redundant_rec_wl_inv where
  \<open>lit_redundant_rec_wl_inv M NU D = (\<lambda>(cach, analyse, b). lit_redundant_rec_wl_ref NU analyse)\<close>

definition lit_redundant_reason_stack
  :: \<open>'v literal \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)\<close> where
\<open>lit_redundant_reason_stack L NU C' =
  (if length (NU \<propto> C') > 2 then (C', 0, 1, length (NU \<propto> C'))
  else if NU \<propto> C' ! 0 = L then (C', 0, 1, length (NU \<propto> C'))
  else (C', 1, 0, 1))\<close>

definition lit_redundant_rec_wl :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clause \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
      (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec_wl M NU D cach analysis _ =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(length analyse \<le> length M);
	    let (C, k, i, ln) = last analyse;
            ASSERT(C \<in># dom_m NU);
            ASSERT(length (NU \<propto> C) > k);
            ASSERT(NU \<propto> C!k \<in> lits_of_l M);
            let C = NU \<propto> C;
            if i \<ge> ln
            then
              RETURN(cach (atm_of (C ! k) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
	      let (L, analyse) = get_literal_and_remove_of_analyse_wl C analyse;
              ASSERT(fst(snd(snd (last analyse))) \<noteq> 0);
	      ASSERT(-L \<in> lits_of_l M);
	      b \<leftarrow> RES (UNIV);
	      if (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)
	      	     then RETURN (cach, analyse, False)
	      else if b \<or> cach (atm_of L) = SEEN_FAILED
	      then do {
		cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
		RETURN (cach, [], False)
	      }
	      else do {
                ASSERT(cach (atm_of L) = SEEN_UNKNOWN);
		C' \<leftarrow> get_propagation_reason M (-L);
		case C' of
		  Some C' \<Rightarrow> do {
		    ASSERT(C' \<in># dom_m NU);
		    ASSERT(length (NU \<propto> C') \<ge> 2);
		    ASSERT (distinct (NU \<propto> C') \<and> \<not>tautology (mset (NU \<propto> C')));
		    ASSERT(C' > 0);
		    RETURN (cach, analyse @ [lit_redundant_reason_stack (-L) NU C'], False)
		  }
		| None \<Rightarrow> do {
		    cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
		    RETURN (cach, [], False)
		}
	     }
           }
        })
       (cach, analysis, False)\<close>

fun convert_analysis_l where
  \<open>convert_analysis_l NU (i, k, j, le) = (-NU \<propto> i ! k, mset (Misc.slice j le (NU \<propto> i)))\<close>

definition convert_analysis_list where
  \<open>convert_analysis_list NU analyse = map (convert_analysis_l NU) (rev analyse)\<close>

lemma convert_analysis_list_empty[simp]:
  \<open>convert_analysis_list NU [] = []\<close>
  \<open>convert_analysis_list NU a = [] \<longleftrightarrow> a = []\<close>
  by (auto simp: convert_analysis_list_def)


lemma trail_length_ge2:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    LaC: \<open>Propagated L C \<in> set (get_trail_l S)\<close> and
    C0: \<open>C > 0\<close>
  shows
    \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
proof -
  have conv:
   \<open>(get_trail_l S, get_trail T) \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
   using ST unfolding twl_st_l_def by auto

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of T)\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+

  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using ST lev_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st_l twl_st)
  have
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close>
    using list_invs C0 LaC by (auto simp: twl_list_invs_def all_conj_distrib)
  have \<open>twl_st_inv T\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  then show le2: \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
    using C ST multi_member_split[OF C] unfolding twl_struct_invs_def
    by (cases S; cases T)
      (auto simp: twl_st_inv.simps twl_st_l_def
        image_Un[symmetric])
qed

lemma clauses_length_ge2:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close>
  shows
    \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
proof -
  have \<open>twl_st_inv T\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  then show le2: \<open>length (get_clauses_l S \<propto> C) \<ge> 2\<close>
    using C ST multi_member_split[OF C] unfolding twl_struct_invs_def
    by (cases S; cases T)
      (auto simp: twl_st_inv.simps twl_st_l_def
        image_Un[symmetric])
qed

lemma lit_redundant_rec_wl:
  fixes S :: \<open>nat twl_st_wl\<close> and S' :: \<open>nat twl_st_l\<close> and S'' :: \<open>nat twl_st\<close> and NU M analyse
  defines
    [simp]: \<open>S''' \<equiv> state\<^sub>W_of S''\<close>
  defines
    \<open>M \<equiv> get_trail_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU': \<open>NU' \<equiv> mset `# ran_mf NU\<close> and
    \<open>analyse' \<equiv> convert_analysis_list NU analyse\<close>
  assumes
    S_S': \<open>(S, S') \<in> state_wl_l None\<close> and
    S'_S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
    bounds_init: \<open>lit_redundant_rec_wl_ref NU analyse\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close>
  shows
    \<open>lit_redundant_rec_wl M NU D cach analyse lbd \<le> \<Down>
       (Id \<times>\<^sub>r {(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          lit_redundant_rec_wl_ref NU analyse} \<times>\<^sub>r bool_rel)
       (lit_redundant_rec M' NU' D cach analyse')\<close>
   (is \<open>_ \<le> \<Down> (_ \<times>\<^sub>r ?A \<times>\<^sub>r _) _\<close> is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  obtain D' NE UE Q W NS US where
    S: \<open>S = (M, NU, D', NE, UE, NS, US, Q, W)\<close>
    using M_def NU by (cases S) auto
  have M'_def: \<open>(M, M') \<in> convert_lits_l NU (NE + UE)\<close>
    using NU S_S' S'_S'' unfolding M' by (auto simp: S state_wl_l_def twl_st_l_def)
  then have [simp]: \<open>lits_of_l M' = lits_of_l M\<close>
    by auto
  have [simp]: \<open>fst (convert_analysis_l NU x) = -NU \<propto> (fst x) ! (fst (snd x))\<close> for x
    by (cases x) auto
  have [simp]: \<open>snd (convert_analysis_l NU x) =
    mset (Misc.slice (fst (snd (snd x))) (snd (snd (snd x))) (NU \<propto> fst x))\<close> for x
    by (cases x) auto

  have
    no_smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa S'''\<close> and
    struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S'''\<close>
    using struct_invs unfolding twl_struct_invs_def S'''_def[symmetric]
    by fast+
  have annots: \<open>set (get_all_mark_of_propagated (trail S''')) \<subseteq>
     set_mset (cdcl\<^sub>W_restart_mset.clauses S''')\<close>
    using struct_invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
    by fast
  have \<open>no_dup (get_trail_wl S)\<close>
    using struct_invs S_S' S'_S'' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st_wl twl_st_l twl_st)
  then have n_d: \<open>no_dup M\<close>
    by (auto simp: S)
  then have n_d': \<open>no_dup M'\<close>
    using M'_def by (auto simp: S)
  let ?B = \<open>{(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          lit_redundant_rec_wl_ref NU analyse \<and> fst (snd (snd (last analyse))) > 0}\<close>
  have get_literal_and_remove_of_analyse_wl:
    \<open>RETURN (get_literal_and_remove_of_analyse_wl (NU \<propto> x1d) x1c)
	\<le> \<Down> (Id \<times>\<^sub>r ?B)
	   (get_literal_and_remove_of_analyse x1a)\<close>
    if
      xx': \<open>(x, x')  \<in> ?R\<close> and
      \<open>case x of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>lit_redundant_rec_wl_inv M NU D x\<close> and
      s: \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2d = (x1f, x2e)\<close>
        \<open>x2c = (x1e, x2d)\<close>
        \<open>(fst (last x1c), fst (snd (last x1c)), fst (snd (snd (last x1c))),
	snd (snd (snd (last x1c)))) =
         (x1d, x2c)\<close>
        \<open>x2b = (x1c, x2f)\<close>
        \<open>x = (x1b, x2b)\<close> and
      \<open>x1a \<noteq> []\<close> and
      \<open>- fst (hd x1a) \<in> lits_of_l M'\<close> and
      x1c: \<open>x1c \<noteq> []\<close> and
      \<open>x1d \<in># dom_m NU\<close> and
      \<open>x1e < length (NU \<propto> x1d)\<close> and
      \<open>NU \<propto> x1d ! x1e \<in> lits_of_l M\<close> and
      length: \<open>\<not> x2e \<le> x1f\<close> and
      \<open>snd (hd x1a) \<noteq> {#}\<close>
    for x x' x1 x2 x1a x2a x1b x2b x1c x1d x2c x1e x2d x1f x2e x2f
  proof -
    have x1d: \<open>x1d = fst (last x1c)\<close>
      using s by auto
    have \<open>last x1c = (a, b, c, d) \<Longrightarrow> d \<le> length (NU \<propto> a)\<close>
      \<open>last x1c = (a, b, c, d) \<Longrightarrow> c \<le> d\<close> for aa ba list a b c d
      using xx' x1c length unfolding s convert_analysis_list_def
        lit_redundant_rec_wl_ref_def
      by (cases x1c rule: rev_cases; auto; fail)+
    then show ?thesis
      supply convert_analysis_list_def[simp] hd_rev[simp] last_map[simp] rev_map[symmetric, simp]
      using x1c xx' length s
      using Cons_nth_drop_Suc[of \<open>snd (snd (snd (last x1c)))\<close> \<open>NU \<propto> fst (last x1c)\<close>, symmetric]
      unfolding lit_redundant_rec_wl_ref_def x1d
      by (cases x1c; cases \<open>last x1c\<close>)
        (auto simp: get_literal_and_remove_of_analyse_wl_def nth_in_sliceI mset_tl
          get_literal_and_remove_of_analyse_def convert_analysis_list_def slice_Suc
	  slice_head
          intro!: RETURN_SPEC_refine elim!: neq_Nil_revE split: if_splits)
  qed

  have get_propagation_reason: \<open>get_propagation_reason M (- x1h)
	\<le> \<Down> (\<langle>{(C', C). C = mset (NU \<propto> C') \<and> C' \<noteq> 0 \<and>
	      Propagated (- x1g) (mset (NU\<propto>C')) \<in> set M'
		  \<and> Propagated (- x1g) C' \<in> set M \<and> C' \<in># dom_m NU \<and>
		  length (NU \<propto> C') \<ge> 2}\<rangle>
		option_rel)
	   (get_propagation_reason M' (- x1g))\<close>
      (is \<open>_ \<le> \<Down> (\<langle>?get_propagation_reason\<rangle>option_rel) _\<close>)
    if
      \<open>(x, x')  \<in> ?R\<close> and
      \<open>case x of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>lit_redundant_rec_wl_inv M NU D x\<close> and
      st:
	\<open>x2 = (x1a, x2a)\<close>
	\<open>x' = (x1, x2)\<close>
	\<open>x2d = (x1f, x2e)\<close>
	\<open>x2c = (x1e, x2d)\<close>
	\<open>(fst (last x1c), fst (snd (last x1c)), fst (snd (snd (last x1c))),
	  snd (snd (snd (last x1c)))) =
	 (x1d, x2c)\<close>
	\<open>x2b = (x1c, x2f)\<close>
	\<open>x = (x1b, x2b)\<close>
        \<open>x'a = (x1g, x2g)\<close> and
      \<open>x1a \<noteq> []\<close> and
      \<open>- fst (hd x1a) \<in> lits_of_l M'\<close> and
      \<open>x1c \<noteq> []\<close> and
      x1d: \<open>x1d \<in># dom_m NU\<close> and
      \<open>x1e < length (NU \<propto> x1d)\<close> and
      \<open>NU \<propto> x1d ! x1e \<in> lits_of_l M\<close> and
      \<open>\<not> x2e \<le> x1f\<close> and
      \<open>snd (hd x1a) \<noteq> {#}\<close> and
      H: \<open>(get_literal_and_remove_of_analyse_wl (NU \<propto> x1d) x1c, x'a)
            \<in> Id \<times>\<^sub>f ?B\<close>
        \<open>get_literal_and_remove_of_analyse_wl (NU \<propto> x1d) x1c = (x1h, x2h)\<close> and
      \<open>- x1g \<in> lits_of_l M'\<close> and
      \<open>- x1h \<in> lits_of_l M\<close> and
      \<open>(b, ba) \<in> bool_rel\<close> and
      \<open>b \<in> UNIV\<close> and
      \<open>ba \<in> UNIV\<close> and
      \<open>\<not> (get_level M x1h = 0 \<or> x1b (atm_of x1h) = SEEN_REMOVABLE \<or> x1h \<in># D)\<close> and
      cond: \<open>\<not> (get_level M' x1g = 0 \<or> x1 (atm_of x1g) = SEEN_REMOVABLE \<or> x1g \<in># D)\<close> and
      \<open>\<not> (b \<or> x1b (atm_of x1h) = SEEN_FAILED)\<close> and
      \<open>\<not> (ba \<or> x1 (atm_of x1g) = SEEN_FAILED)\<close>
   for x x' x1 x2 x1a x2a x1b x2b x1c x1d x2c x1e x2d x1f x2e x2f x'a x1g x2g x1h
	 x2h b ba
  proof -
    have [simp]: \<open>x1h = x1g\<close>
      using st H by auto
    have le2: \<open>length (NU \<propto> x1d) \<ge> 2\<close>
      using clauses_length_ge2[OF S'_S'' add_inv assms(10), of x1d] x1d st S_S'
      by (auto simp: S)
    have
      \<open>Propagated (- x1g) (mset (NU \<propto> a)) \<in> set M'\<close> (is ?propa) and
      \<open>a \<noteq> 0\<close> (is ?a) and
      \<open>a \<in># dom_m NU\<close> (is ?L) and
      \<open>length (NU \<propto> a) \<ge> 2\<close> (is ?len)
      if x1e_M: \<open>Propagated (- x1g) a \<in> set M\<close>
      for a
    proof -
      have [simp]: \<open>a \<noteq> 0\<close>
      proof
        assume [simp]: \<open>a = 0\<close>
        obtain E' where
           x1d_M': \<open>Propagated (- x1g) E' \<in> set M'\<close> and
           \<open>E' \<in># NE + UE\<close>
          using x1e_M M'_def by (auto dest: split_list simp: convert_lits_l_def p2rel_def
              convert_lit.simps
              elim!: list_rel_in_find_correspondanceE split: if_splits)
        moreover have \<open>unit_clss S'' = NE + UE\<close>
          using S_S' S'_S'' x1d_M' by (auto simp: S)
        moreover have \<open>Propagated (- x1g) E' \<in> set (get_trail S'')\<close>
          using S_S' S'_S'' x1d_M' by (auto simp: S state_wl_l_def twl_st_l_def M')
        moreover have \<open>0 < count_decided (get_trail S'')\<close>
          using cond S_S' S'_S'' count_decided_ge_get_level[of M \<open>x1g\<close>]
          by (auto simp: S M' twl_st)
        ultimately show False
          using clauses_in_unit_clss_have_level0(1)[of S'' E' \<open>- x1g\<close>] cond \<open>twl_struct_invs S''\<close>
          S_S' S'_S''  M'_def
          by (auto simp: S)
      qed
      show ?propa and ?a
        using that M'_def by (auto simp: convert_lits_l_def p2rel_def convert_lit.simps
              elim!: list_rel_in_find_correspondanceE split: if_splits)
      then show ?L
        using that add_inv S_S' S'_S'' S unfolding twl_list_invs_def
        by (auto 5 5 simp: state_wl_l_def twl_st_l_def)
      show ?len
        using trail_length_ge2[OF S'_S'' add_inv assms(10), of \<open>- x1g\<close> a] that S_S'
	by (force simp: S)
    qed
    then show ?thesis
      apply (auto simp: get_propagation_reason_def refine_rel_defs intro!: RES_refine)
      apply (case_tac s)
      by auto
  qed
  have resolve: \<open>((x1b, x2h @ [lit_redundant_reason_stack (- x1h) NU xb], False), x1,
	 (x1g, remove1_mset (- x1g) x'c) # x2g, False)
	\<in> Id \<times>\<^sub>f
	  ({(analyse, analyse').
	    analyse' = convert_analysis_list NU analyse \<and>
	    lit_redundant_rec_wl_ref NU analyse} \<times>\<^sub>f
	   bool_rel)\<close>
    if
      xx': \<open>(x, x') \<in> Id \<times>\<^sub>r ?A \<times>\<^sub>r bool_rel\<close> and
      \<open>case x of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>lit_redundant_rec_wl_inv M NU D x\<close> and
      s:
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2d = (x1f, x2e)\<close>
        \<open>x2c = (x1e, x2d)\<close>
        \<open>(fst (last x1c), fst (snd (last x1c)), fst (snd (snd (last x1c))),
         	snd (snd (snd (last x1c)))) =
         (x1d, x2c)\<close>
        \<open>x2b = (x1c, x2f)\<close>
        \<open>x = (x1b, x2b)\<close>
	\<open>x'a = (x1g, x2g)\<close>  and
      [simp]: \<open>x1a \<noteq> []\<close> and
      \<open>- fst (hd x1a) \<in> lits_of_l M'\<close> and
      [simp]: \<open>x1c \<noteq> []\<close> and
      \<open>x1d \<in># dom_m NU\<close> and
      \<open>x1e < length (NU \<propto> x1d)\<close> and
      \<open>NU \<propto> x1d ! x1e \<in> lits_of_l M\<close> and
      \<open>\<not> x2e \<le> x1f\<close> and
      \<open>snd (hd x1a) \<noteq> {#}\<close> and
      get_literal_and_remove_of_analyse_wl:
        \<open>(get_literal_and_remove_of_analyse_wl (NU \<propto> x1d) x1c, x'a)
       \<in> Id \<times>\<^sub>f
	 {(analyse, analyse').
	  analyse' = convert_analysis_list NU analyse \<and>
	  lit_redundant_rec_wl_ref NU analyse \<and>
	  0 < fst (snd (snd (last analyse)))}\<close> and
      get_lit: \<open>get_literal_and_remove_of_analyse_wl (NU \<propto> x1d) x1c = (x1h, x2h)\<close> and
      \<open>- x1g \<in> lits_of_l M'\<close> and
      \<open>fst (snd (snd (last x2h))) \<noteq> 0\<close> and
      \<open>- x1h \<in> lits_of_l M\<close> and
      bba: \<open>(b, ba) \<in> bool_rel\<close> and
      \<open>\<not> (get_level M x1h = 0 \<or> x1b (atm_of x1h) = SEEN_REMOVABLE \<or> x1h \<in># D)\<close> and
      \<open>\<not> (get_level M' x1g = 0 \<or> x1 (atm_of x1g) = SEEN_REMOVABLE \<or> x1g \<in># D)\<close> and
      \<open>\<not> (b \<or> x1b (atm_of x1h) = SEEN_FAILED)\<close> and
      \<open>\<not> (ba \<or> x1 (atm_of x1g) = SEEN_FAILED)\<close> and
      xb_x'c: \<open>(xa, x'b)
       \<in> \<langle>?get_propagation_reason x1g\<rangle>option_rel\<close> and
      xa: \<open>xa = Some xb\<close> \<open>x'b = Some x'c\<close> and
      \<open>(xb, x'c)
       \<in> (?get_propagation_reason x1g)\<close> and
      dist_tauto: \<open>distinct_mset x'c \<and> \<not> tautology x'c\<close> and
      \<open>xb \<in># dom_m NU\<close> and
      \<open>2 \<le> length (NU \<propto> xb)\<close>
     for x x' x1 x2 x1a x2a x1b x2b x1c x1d x2c x1e x2d x1f x2e x2f x'a x1g x2g x1h
       x2h b ba xa x'b xb x'c
  proof -
    have [simp]: \<open>mset (tl C) = remove1_mset (C!0) (mset C)\<close> for C
      by (cases C) auto
    have [simp]:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x1a, x2a)\<close>
      \<open>x2d = (x1f, x2e)\<close>
      \<open>x2c = (x1e, x1f, x2e)\<close>
      \<open>last x1c = (x1d, x1e, x1f, x2e)\<close>
      \<open>x2b = (x1c, x2f)\<close>
      \<open>x = (x1b, x1c, x2f)\<close>
      \<open>xa = Some xb\<close>
      \<open>x'b = Some x'c\<close>
      \<open>x'c = mset (NU \<propto> xb)\<close>
      using s get_literal_and_remove_of_analyse_wl xa xb_x'c
      unfolding get_lit convert_analysis_list_def
      by auto
    then have x1d0: \<open>length (NU \<propto> xb) > 2 \<Longrightarrow> x1g = -NU \<propto> xb ! 0\<close> \<open>NU \<propto> xb \<noteq> []\<close> and
      x1d: \<open>-x1g \<in> set (watched_l (NU \<propto> xb))\<close>
      using add_inv xb_x'c S_S' S'_S'' S unfolding twl_list_invs_def
      by (auto 5 5 simp: state_wl_l_def twl_st_l_def)

    have le2: \<open>length (NU \<propto> xb) \<ge> 2\<close>
      using clauses_length_ge2[OF S'_S'' add_inv assms(10)] xb_x'c S_S'
      by (auto simp: S)
    have 0: \<open>case lit_redundant_reason_stack (-x1g) NU xb of (i, k, j, ln) \<Rightarrow>
            j \<le> ln \<and> i \<in># dom_m NU \<and> 0 \<le> j \<and> 0 < i \<and> ln \<le> length (NU \<propto> i) \<and>
	      k < length (NU \<propto> i) \<and> distinct (NU \<propto> i) \<and> \<not> tautology (mset (NU \<propto> i))\<close>
      for i j ln k
      using s xx' get_literal_and_remove_of_analyse_wl xb_x'c x1d le2 dist_tauto
      unfolding get_lit convert_analysis_list_def lit_redundant_rec_wl_ref_def
      lit_redundant_reason_stack_def
      by (auto split: if_splits)

    have \<open>(x1g, remove1_mset (- x1g) (mset (NU \<propto> xb))) =
      convert_analysis_l NU (lit_redundant_reason_stack (- x1g) NU xb)\<close>
      using s xx' get_literal_and_remove_of_analyse_wl xb_x'c x1d le2
      unfolding get_lit convert_analysis_list_def lit_redundant_rec_wl_ref_def
        lit_redundant_reason_stack_def
      by (auto split: simp: Misc.slice_def drop_Suc simp: x1d0(1)
        dest!: list_decomp_2)
    then show ?thesis
      using s xx' get_literal_and_remove_of_analyse_wl xb_x'c x1d 0
      unfolding get_lit convert_analysis_list_def lit_redundant_rec_wl_ref_def
      by (cases x2h rule: rev_cases)
        (auto simp: drop_Suc uminus_lit_swap butlast_append
        dest: list_decomp_2)
  qed
  have mark_failed_lits_wl: \<open>mark_failed_lits_wl NU x2e x1b \<le> \<Down> Id (mark_failed_lits NU' x2d x1)\<close>
    if
      \<open>(x, x') \<in> ?R\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x = (x1b, x2b)\<close>
    for x x' x2e x1b x1 x2 x2b x2d
    using that unfolding mark_failed_lits_wl_def mark_failed_lits_def by auto

  have ana: \<open>last analyse = (fst (last analyse), fst (snd (last analyse)),
    fst (snd (snd (last analyse))), snd (snd (snd (last analyse))))\<close> for analyse
      by (cases \<open>last analyse\<close>) auto

  show ?thesis
    supply convert_analysis_list_def[simp] hd_rev[simp] last_map[simp] rev_map[symmetric, simp]
    unfolding lit_redundant_rec_wl_def lit_redundant_rec_def
    apply (rewrite at \<open>let _ = _ \<propto> _ in _\<close> Let_def)
    apply (rewrite in \<open>let _ = _ in _\<close> ana)
    apply (rewrite at \<open>let _ = (_, _, _) in _\<close> Let_def)
    apply refine_rcg
    subgoal using bounds_init unfolding analyse'_def by auto
    subgoal for x x'
      by (cases x, cases x')
         (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def)
    subgoal by auto
    subgoal by auto
    subgoal using M'_def by (auto dest: convert_lits_l_imp_same_length)
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
       elim!: neq_Nil_revE)
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
       elim!: neq_Nil_revE)
    subgoal by (auto simp: map_butlast rev_butlast_is_tl_rev lit_redundant_rec_wl_ref_def
          dest: in_set_butlastD)
    subgoal by (auto simp: map_butlast rev_butlast_is_tl_rev lit_redundant_rec_wl_ref_def
            Misc.slice_def
          dest: in_set_butlastD
          elim!: neq_Nil_revE)
    subgoal by (auto simp: map_butlast rev_butlast_is_tl_rev lit_redundant_rec_wl_ref_def
            Misc.slice_def
          dest: in_set_butlastD
          elim!: neq_Nil_revE)
    apply (rule get_literal_and_remove_of_analyse_wl; assumption)
    subgoal by auto
    subgoal by auto
    subgoal using M'_def by auto
    subgoal by auto
    subgoal by auto
    apply (rule mark_failed_lits_wl; assumption)
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
    subgoal by auto
    apply (rule get_propagation_reason; assumption)
    apply assumption
    apply (rule mark_failed_lits_wl; assumption)
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x1d x2c x1e x2d x1f x2e x2f x'a x1g x2g x1h
       x2h b ba xa x'b xb x'c
      by (rule resolve)
    done
qed


definition literal_redundant_wl where
  \<open>literal_redundant_wl M NU D cach L lbd = do {
     ASSERT(-L \<in> lits_of_l M);
     if get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       C \<leftarrow> get_propagation_reason M (-L);
       case C of
         Some C \<Rightarrow> do{
	   ASSERT(C \<in># dom_m NU);
	   ASSERT(length (NU \<propto> C) \<ge> 2);
	   ASSERT(distinct (NU \<propto> C) \<and>  \<not>tautology (mset (NU \<propto> C)));
	   lit_redundant_rec_wl M NU D cach [lit_redundant_reason_stack (-L) NU C] lbd
	 }
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma literal_redundant_wl_literal_redundant:
  fixes S :: \<open>nat twl_st_wl\<close> and S' :: \<open>nat twl_st_l\<close> and S'' :: \<open>nat twl_st\<close> and NU M
  defines
    [simp]: \<open>S''' \<equiv> state\<^sub>W_of S''\<close>
  defines
    \<open>M \<equiv> get_trail_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU': \<open>NU' \<equiv> mset `# ran_mf NU\<close>
  assumes
    S_S': \<open>(S, S') \<in> state_wl_l None\<close> and
    S'_S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
    \<open>M \<equiv> get_trail_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU': \<open>NU' \<equiv> mset `# ran_mf NU\<close>
  assumes
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close> and
    L_D: \<open>L \<in># D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close>
  shows
    \<open>literal_redundant_wl M NU D cach L lbd \<le> \<Down>
       (Id \<times>\<^sub>r {(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          lit_redundant_rec_wl_ref NU analyse} \<times>\<^sub>r bool_rel)
       (literal_redundant M' NU' D cach L)\<close>
   (is \<open>_ \<le> \<Down> (_ \<times>\<^sub>r ?A \<times>\<^sub>r _) _\<close> is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  obtain D' NE UE Q W NS US where
    S: \<open>S = (M, NU, D', NE, UE, NS, US, Q, W)\<close>
    using M_def NU by (cases S) auto
  have M'_def: \<open>(M, M') \<in> convert_lits_l NU (NE+UE)\<close>
    using NU S_S' S'_S'' S M' by (auto simp: twl_st_l_def state_wl_l_def)
  have [simp]: \<open>lits_of_l M' = lits_of_l M\<close>
    using M'_def by auto
  have
    no_smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa S'''\<close> and
    struct_invs': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S'''\<close>
    using struct_invs unfolding twl_struct_invs_def S'''_def[symmetric]
    by fast+
  have annots: \<open>set (get_all_mark_of_propagated (trail S''')) \<subseteq>
     set_mset (cdcl\<^sub>W_restart_mset.clauses S''')\<close>
    using struct_invs'
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
    by fast
  have n_d: \<open>no_dup (get_trail_wl S)\<close>
    using struct_invs' S_S' S'_S'' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st_wl twl_st_l twl_st)
  then have n_d: \<open>no_dup M\<close>
    by (auto simp: S)
  then have n_d': \<open>no_dup M'\<close>
    using M'_def by (auto simp: S)
  have uL_M: \<open>-L \<in> lits_of_l M\<close>
    using L_D M_D by (auto dest!: multi_member_split)
  have H: \<open>lit_redundant_rec_wl M NU D cach analyse lbd
      \<le> \<Down> ?R (lit_redundant_rec M' NU' D cach analyse')\<close>
    if \<open>analyse' = convert_analysis_list NU analyse\<close> and
       \<open>lit_redundant_rec_wl_ref NU analyse\<close>
     for analyse analyse'
    using lit_redundant_rec_wl[of S S' S'' analyse D cach lbd, unfolded S'''_def[symmetric],
      unfolded
      M_def[symmetric] M'[symmetric] NU[symmetric] NU'[symmetric],
      OF S_S' S'_S'' _ struct_invs add_inv]
    that by (auto simp: )
  have get_propagation_reason: \<open>get_propagation_reason M (-L)
      \<le> \<Down> (\<langle>{(C', C).  C = mset (NU \<propto> C') \<and> C' \<noteq> 0 \<and> Propagated (-L) (mset (NU\<propto>C')) \<in> set M'
                \<and> Propagated (-L) C' \<in> set M \<and> length (NU\<propto>C') \<ge> 2}\<rangle>
              option_rel)
          (get_propagation_reason M' (-L))\<close>
      (is \<open>_ \<le> \<Down> (\<langle>?get_propagation_reason\<rangle>option_rel) _\<close> is ?G1) and
    propagated_L:
       \<open>Propagated (-L) a \<in> set M \<Longrightarrow> a \<noteq> 0 \<and> Propagated (- L) (mset (NU \<propto> a)) \<in> set M'\<close>
       (is \<open>?H2 \<Longrightarrow> ?G2\<close>)
    if
      lev0_rem: \<open>\<not> (get_level M' L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE)\<close> and
      ux1e_M: \<open>- L \<in> lits_of_l M\<close>
    for a
    proof -
      have \<open>Propagated (- L) (mset (NU \<propto> a)) \<in> set M'\<close> (is ?propa) and
        \<open>a \<noteq> 0\<close> (is ?a) and
	\<open>length (NU \<propto> a) \<ge> 2\<close> (is ?len)
        if L_M: \<open>Propagated (-L) a \<in> set M\<close>
        for a
      proof -
        have [simp]: \<open>a \<noteq> 0\<close>
        proof
          assume [simp]: \<open>a = 0\<close>
          obtain E' where
            x1d_M': \<open>Propagated (- L) E' \<in> set M'\<close> and
            \<open>E' \<in># NE + UE\<close>
            using L_M M'_def by (auto dest: split_list simp: convert_lits_l_def p2rel_def
                convert_lit.simps
                elim!: list_rel_in_find_correspondanceE split: if_splits)
          moreover have \<open>unit_clss S'' = NE + UE\<close>
            using S_S' S'_S'' x1d_M' by (auto simp: S)
          moreover have \<open>Propagated (- L) E' \<in> set (get_trail S'')\<close>
            using S_S' S'_S'' x1d_M' by (auto simp: S state_wl_l_def twl_st_l_def M')
          moreover have \<open>0 < count_decided (get_trail S'')\<close>
            using lev0_rem S_S' S'_S'' count_decided_ge_get_level[of M L]
            by (auto simp: S M' twl_st)
          ultimately show False
            using clauses_in_unit_clss_have_level0(1)[of S'' E' \<open>- L\<close>] lev0_rem \<open>twl_struct_invs S''\<close>
              S_S' S'_S''  M'_def
            by (auto simp: S)
        qed

        show ?propa and ?a
          using that M'_def by (auto simp: convert_lits_l_def p2rel_def convert_lit.simps
              elim!: list_rel_in_find_correspondanceE split: if_splits)
	show ?len
	  using trail_length_ge2[OF S'_S'' add_inv struct_invs, of \<open>- L\<close> a] that S_S'
	  by (force simp: S)
      qed note H = this
     show \<open>?H2 \<Longrightarrow> ?G2\<close>
       using H by auto
     show ?G1
       using H
       apply (auto simp: get_propagation_reason_def refine_rel_defs
           get_propagation_reason_def intro!: RES_refine)
       apply (case_tac s)
       by auto
    qed
  have S''': \<open>S''' = (get_trail S'', get_all_init_clss S'', get_all_learned_clss S'',
      get_conflict S'')\<close>
    by (cases S'') (auto simp: S'''_def)
  have [simp]: \<open>mset (tl C) = remove1_mset (C!0) (mset C)\<close> for C
    by (cases C) auto
  have S''_M': \<open>(get_trail S'') = M'\<close>
    using M' S''' by auto

  have [simp]: \<open>length (NU \<propto> C) > 2 \<Longrightarrow> NU \<propto> C ! 0 = -L\<close> and
    L_watched: \<open>-L \<in> set (watched_l (NU \<propto> C))\<close> and
    L_dist: \<open>distinct (NU \<propto> C)\<close> and
    L_tauto: \<open>\<not>tautology (mset (NU \<propto> C))\<close>
  if
    in_trail: \<open>Propagated (- L) C \<in> set M\<close> and
    lev: \<open>\<not> (get_level M' L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE)\<close>
    for C
    using add_inv that propagated_L[OF lev _ in_trail] uL_M S_S' S'_S''
    Propagated_in_trail_entailed[of \<open>get_trail S''\<close> \<open>get_all_init_clss S''\<close> \<open>get_all_learned_clss S''\<close>
      \<open>get_conflict S''\<close> \<open>-L\<close> \<open>mset (NU \<propto> C)\<close>] struct_invs' unfolding S'''[symmetric]
    by (auto simp: S twl_list_invs_def S''_M'; fail)+

  have [dest]: \<open>C \<noteq> {#}\<close> if \<open>Propagated (- L) C \<in> set M'\<close> for C
  proof -
    have \<open>a @ Propagated L mark # b = trail S''' \<Longrightarrow> b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
      for L mark a b
      using struct_invs' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by fast
    then show ?thesis
      using that S_S' S'_S'' M'_def M'
      by (fastforce simp: S state_wl_l_def
          twl_st_l_def convert_lits_l_def convert_lit.simps
          list_rel_append2 list_rel_append1
          elim!: list_relE3 list_relE4
          elim: list_rel_in_find_correspondanceE split: if_splits
          dest!: split_list p2relD)
  qed
  have le2: \<open>Propagated (- L) C \<in> set M \<Longrightarrow> C > 0 \<Longrightarrow> length (NU \<propto> C) \<ge> 2\<close> for C
    using trail_length_ge2[OF S'_S'' add_inv struct_invs, of _ C] S_S'
    by (auto simp: S)
  have [simp]: \<open>Propagated (- L) C \<in> set M \<Longrightarrow> C > 0 \<Longrightarrow> C \<in># dom_m NU\<close> for C
    using add_inv S_S' S'_S'' propagated_L[of C]
    by (auto simp: S twl_list_invs_def state_wl_l_def
        twl_st_l_def)
  show ?thesis
    unfolding literal_redundant_wl_def literal_redundant_def
    apply (refine_rcg H get_propagation_reason)
    subgoal by simp
    subgoal using M'_def by simp
    subgoal using M'_def by (auto simp: lit_redundant_rec_wl_ref_def)
    subgoal by simp
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
    apply (assumption)
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
    subgoal by simp
    subgoal by simp
    subgoal for x x' C x'a
      using le2[of C] L_watched[of C] L_dist[of C] L_tauto[of C]
      by (auto simp: convert_analysis_list_def drop_Suc slice_0
          lit_redundant_reason_stack_def slice_Suc slice_head slice_end
        dest!: list_decomp_2)
    subgoal for x x' C x'a
      using le2[of C] L_watched[of C] L_dist[of C] L_tauto[of C]
      by (auto simp: convert_analysis_list_def drop_Suc slice_0
          lit_redundant_reason_stack_def slice_Suc slice_head slice_end
        dest!: list_decomp_2)
    subgoal for x x' C x'a
      using le2[of C] L_watched[of C] L_dist[of C] L_tauto[of C]
      by (auto simp: convert_analysis_list_def drop_Suc slice_0
          lit_redundant_reason_stack_def slice_Suc slice_head slice_end
        dest!: list_decomp_2)
    subgoal for x x' C x'a
      using le2[of C] L_watched[of C] L_dist[of C] L_tauto[of C]
      by (auto simp: lit_redundant_reason_stack_def lit_redundant_rec_wl_ref_def)
    done
qed

definition mark_failed_lits_stack_inv where
  \<open>mark_failed_lits_stack_inv NU analyse = (\<lambda>cach.
       (\<forall>(i, k, j, len) \<in> set analyse. j \<le> len \<and> len \<le> length (NU \<propto> i) \<and> i \<in># dom_m NU \<and>
          k < length (NU \<propto> i) \<and> j > 0))\<close>

text \<open>We mark all the literals from the current literal stack as failed, since every minimisation
call will find the same minimisation problem.\<close>
definition mark_failed_lits_stack where
  \<open>mark_failed_lits_stack \<A>\<^sub>i\<^sub>n NU analyse cach = do {
    ( _, cach) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, cach). mark_failed_lits_stack_inv NU analyse cach\<^esup>
      (\<lambda>(i, cach). i < length analyse)
      (\<lambda>(i, cach). do {
        ASSERT(i < length analyse);
        let (cls_idx, _, idx, _) = analyse ! i;
        ASSERT(atm_of (NU \<propto> cls_idx ! (idx - 1)) \<in># \<A>\<^sub>i\<^sub>n);
        RETURN (i+1, cach (atm_of (NU \<propto> cls_idx ! (idx - 1)) := SEEN_FAILED))
      })
      (0, cach);
    RETURN cach
   }\<close>

lemma mark_failed_lits_stack_mark_failed_lits_wl:
  shows
    \<open>(uncurry2 (mark_failed_lits_stack \<A>), uncurry2 mark_failed_lits_wl) \<in>
       [\<lambda>((NU, analyse), cach). literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf NU) \<and>
          mark_failed_lits_stack_inv NU analyse cach]\<^sub>f
       Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have \<open>mark_failed_lits_stack \<A> NU analyse cach \<le> (mark_failed_lits_wl NU analyse cach)\<close>
    if
      NU_\<L>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf NU)\<close> and
      init: \<open>mark_failed_lits_stack_inv NU analyse cach\<close>
    for NU analyse cach
  proof -
    define I where
      \<open>I = (\<lambda>(i :: nat, cach'). (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>
    have valid_atm: \<open>atm_of (NU \<propto> cls_idx ! (idx - 1)) \<in># \<A>\<close>
      if
        \<open>I s\<close> and
        \<open>case s of (i, cach) \<Rightarrow> i < length analyse\<close> and
        \<open>case s of (i, cach) \<Rightarrow> mark_failed_lits_stack_inv NU analyse cach\<close> and
        \<open>s = (i, cach)\<close> and
        i: \<open>i < length analyse\<close> and
        \<open>analyse ! i = (cls_idx, k)\<close> \<open>k = (k0, k')\<close> \<open>k' = (idx, len)\<close>
      for s i cach cls_idx idx k len k' k'' k0
    proof -
      have [iff]: \<open>(\<forall>a b. (a, b) \<notin> set analyse) \<longleftrightarrow> False\<close>
        using i by (cases analyse) auto
      show ?thesis
        unfolding in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric]
        apply (subst atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[symmetric])
        unfolding atms_of_def
        apply (rule imageI)
        apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
        using NU_\<L>\<^sub>i\<^sub>n that nth_mem[of i analyse]
        by (auto simp: mark_failed_lits_stack_inv_def I_def)
    qed
    show ?thesis
      unfolding mark_failed_lits_stack_def mark_failed_lits_wl_def
      apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length analyse -i)\<close>
         and I' = I])
      subgoal by auto
      subgoal using init by simp
      subgoal unfolding I_def by auto
      subgoal by auto
      subgoal for s i cach cls_idx idx
        by (rule valid_atm)
      subgoal unfolding mark_failed_lits_stack_inv_def by auto
      subgoal unfolding I_def by auto
      subgoal by auto
      subgoal unfolding I_def by auto
      done
  qed
  then show ?thesis
    by (intro frefI nres_relI) auto
qed

end
