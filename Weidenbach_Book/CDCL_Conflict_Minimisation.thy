theory CDCL_Conflict_Minimisation
  imports CDCL.CDCL_W_Abstract_State "../lib/Explorer" WB_More_Refinement
begin

no_notation Ref.update ("_ := _" 62)

declare cdcl\<^sub>W_restart_mset_state[simp]


lemma Propagated_in_trail_entailed:
  assumes
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, Some D)\<close> and
    in_trail: \<open>Propagated L C \<in> set M\<close>
  shows \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close> and \<open>N + U \<Turnstile>pm C\<close>
proof -
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated L C # M1\<close>
    using split_list[OF in_trail] by metis
  have \<open>a @ Propagated L mark # b = trail (M, N, U, Some D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have L_E: \<open>L \<in># C\<close> and M_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L C)\<close>
    unfolding M by force+
  then have M_E: \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close>
    unfolding M by (simp add: true_annots_append_l)
  show \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close>
    using L_E M_E by fast+
  have \<open>set (get_all_mark_of_propagated (trail (M, N, U, Some D)))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N, U, Some D))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  then have \<open>C \<in># N + U\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of C M]
    by (auto simp: clauses_def)
  then show \<open>N + U \<Turnstile>pm C\<close> by auto
qed

inductive minimize_conflict :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close> for M where
resolve_propa: \<open>Propagated L E \<in> set M \<Longrightarrow> minimize_conflict M (add_mset (-L) C) (C + remove1_mset L E)\<close> |
remdups: \<open>minimize_conflict M (add_mset L C) C\<close>


definition minimize_conflict_mes :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clause \<Rightarrow> nat multiset\<close> where
\<open>minimize_conflict_mes M C = index (map (atm_of o lit_of) (rev M)) `# atm_of `# C\<close>

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

lemma minimize_conflict_entailed_trail:
  assumes \<open>minimize_conflict M C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms
proof (induction rule: minimize_conflict.induct)
  case (resolve_propa L E C) note in_trail = this(1) and M_C = this(2)
  then show ?case
    using Propagated_in_trail_entailed[OF invs in_trail] by (auto dest!: multi_member_split)
next
  case (remdups L C)
  then show ?case
    by auto
qed

lemma rtranclp_minimize_conflict_entailed_trail:
  assumes \<open>(minimize_conflict M)\<^sup>*\<^sup>* C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by fast
  subgoal using minimize_conflict_entailed_trail by fast
  done

lemma minimize_conflict_mes:
  assumes \<open>minimize_conflict M C E\<close>
  shows \<open>minimize_conflict_mes M E < minimize_conflict_mes M C\<close>
  using assms unfolding minimize_conflict_mes_def
proof (induction rule: minimize_conflict.induct)
  case (resolve_propa L E C) note in_trail = this
  let ?f = \<open>\<lambda>xa. index (map (\<lambda>a. atm_of (lit_of a)) (rev M)) xa\<close>
  have \<open>?f (atm_of x) < ?f (atm_of L)\<close> if x: \<open>x \<in># remove1_mset L E\<close> for x
  proof -
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

  then show ?case by (auto simp: comp_def)
next
  case (remdups L C)
  then show ?case by auto
qed

lemma wf_minimize_conflict:
  shows \<open>wf {(C', C). minimize_conflict M C C'}\<close>
  apply (rule wf_if_measure_in_wf[of \<open>{(C', C). C' < C}\<close> _ \<open>minimize_conflict_mes M\<close>])
  subgoal using wf .
  subgoal using minimize_conflict_mes by auto
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

lemma conflict_minimize_intermediate_step:
  assumes
    \<open>NU \<Turnstile>p add_mset L C\<close> and
    \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') D\<close>
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
    have \<open>NU \<Turnstile>p add_mset x (add_mset L (D + C))\<close>
      using NU_DC by (auto simp: add_mset_commute ac_simps)
    then have \<open>NU \<Turnstile>p add_mset L (D + C + D)\<close>
      using entailed[of x] NU_DC
        true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of NU \<open>-x\<close> \<open>add_mset L D + C\<close> D]
      by auto
    moreover have \<open>remdups_mset (add_mset L (D + C + D)) = remdups_mset (add_mset L (C + D))\<close>
      by (auto simp: remdups_mset_def)
    ultimately have \<open>NU \<Turnstile>p add_mset L C + D\<close>
      apply (subst  true_clss_cls_remdups_mset[symmetric])
      apply (subst (asm) true_clss_cls_remdups_mset[symmetric])
      by simp
    from IH[OF this] entailed show ?case by auto
  qed
qed

datatype minimizer = SEEN_FAILED | SEEN_REMOVABLE | SEEN_UNKNOWN

type_synonym 'v conflict_min_analyse = \<open>('v literal \<times> 'v clause) list\<close>
type_synonym 'v conflict_min_cach = \<open>'v literal \<Rightarrow> minimizer\<close>

definition get_literal_and_remove_of_analyse
   :: \<open>'v conflict_min_analyse \<Rightarrow> ('v literal \<times> 'v conflict_min_analyse) nres\<close> where
  \<open>get_literal_and_remove_of_analyse analyse =
    SPEC(\<lambda>(L, ana). L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and> ana \<noteq> [] \<and>
         hd ana = (fst (hd analyse), snd (hd (analyse)) - {#L#}))\<close>

definition get_propagation_reason where
  \<open>get_propagation_reason M L = SPEC(\<lambda>C. C \<noteq> None \<longrightarrow> Propagated (-L) (the C) \<in> set M)\<close>

definition mark_failed_lits
  :: \<open>'v conflict_min_analyse \<Rightarrow> 'v conflict_min_cach \<Rightarrow> 'v conflict_min_cach nres\<close>
where
  \<open>mark_failed_lits analyse cach = SPEC(\<lambda>cach'. (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>

definition conflict_min_analysis_inv
  :: \<open>'v conflict_min_cach \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_inv cach NU D \<longleftrightarrow>
    (\<forall>L. cach L = SEEN_REMOVABLE \<longrightarrow> set_mset NU \<Turnstile>p add_mset (-L) D)\<close>

lemma conflict_min_analysis_inv_update_removable:
  \<open>conflict_min_analysis_inv (cach(L := SEEN_REMOVABLE)) NU D \<longleftrightarrow>
       conflict_min_analysis_inv cach NU D \<and> set_mset NU \<Turnstile>p add_mset (-L) D\<close>
  by (auto simp: conflict_min_analysis_inv_def)

lemma conflict_min_analysis_inv_update_failed:
  \<open>conflict_min_analysis_inv cach NU D \<Longrightarrow> conflict_min_analysis_inv (cach(L := SEEN_FAILED)) NU D\<close>
  by (auto simp: conflict_min_analysis_inv_def)

fun conflict_min_analysis_stack
  :: \<open>'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_stack NU D [] \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack NU D ((L, E) # []) \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack NU D ((L, E) # (L', E') # analyse) \<longleftrightarrow>
     (\<exists>C. set_mset NU \<Turnstile>p add_mset (-L') C \<and> (\<forall>K\<in>#C-add_mset L E'. set_mset NU \<Turnstile>p D + {#-K#})) \<and>
      conflict_min_analysis_stack NU D ((L', E') # analyse)\<close>

lemma conflict_min_analysis_stack_change_hd:
  \<open>conflict_min_analysis_stack NU D ((L, E) # ana) \<Longrightarrow> conflict_min_analysis_stack NU D ((L, E') # ana)\<close>
  by (cases ana, auto)

fun conflict_min_analysis_stack_hd
  :: \<open>'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_stack_hd NU D [] \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack_hd NU D ((L, E) # _) \<longleftrightarrow>
     (\<exists>C. set_mset NU \<Turnstile>p add_mset (-L) C \<and> (\<forall>K\<in>#C-E. set_mset NU \<Turnstile>p D + {#-K#}))\<close>

lemma conflict_min_analysis_stack_tl:
  \<open>conflict_min_analysis_stack NU D analyse \<Longrightarrow> conflict_min_analysis_stack NU D (tl analyse)\<close>
  by (cases \<open>(NU, D, analyse)\<close> rule: conflict_min_analysis_stack.cases) auto

definition lit_redundant_inv
  :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> 
        'v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool \<Rightarrow> bool\<close> where
  \<open>lit_redundant_inv M NU D init_analyse = (\<lambda>(cach, analyse, b).
           conflict_min_analysis_inv cach NU D \<and>
           (analyse \<noteq> [] \<longrightarrow> fst (hd init_analyse) = fst (last analyse)) \<and>
           (analyse = [] \<longrightarrow> b \<longrightarrow> cach (fst (hd init_analyse)) = SEEN_REMOVABLE) \<and>
           conflict_min_analysis_stack NU D analyse \<and>
           conflict_min_analysis_stack_hd NU D analyse)\<close>

definition lit_redundant_rec :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow>
     'v conflict_min_cach \<Rightarrow> 'v conflict_min_analyse \<Rightarrow>
      ('v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec M NU D cach analysis =
      WHILE\<^sub>T\<^bsup>lit_redundant_inv M NU D analysis\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            if snd (hd analyse) = {#}
            then
               RETURN(cach ((fst (hd analyse)) := SEEN_REMOVABLE), tl analyse, True)
            else do {
               (L, analyse) \<leftarrow> get_literal_and_remove_of_analyse analyse;
               if (get_level M L = 0 \<or> cach L = SEEN_REMOVABLE)
               then RETURN (cach, analyse, False)
               else do {
                  C \<leftarrow> get_propagation_reason M L;
                  case C of
                    Some C \<Rightarrow> RETURN (cach, (L, C - {#-L#}) # analyse, False)
                  | None \<Rightarrow> do {
                      cach \<leftarrow> mark_failed_lits analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>

definition lit_redundant_rec_spec where
  \<open>lit_redundant_rec_spec NU D L =
    SPEC(\<lambda>(cach, analysis, b). (b \<longrightarrow> set_mset NU \<Turnstile>p add_mset (-L) D) \<and>
     conflict_min_analysis_inv cach NU D)\<close>

(* TODO Move *)
context conflict_driven_clause_learning\<^sub>W
begin

lemma in_unmark_l_in_lits_of_l_iff: \<open>{#L#} \<in> unmark_l M \<longleftrightarrow> L \<in> lits_of_l M\<close>
  by (induction M) auto

lemma literals_of_level0_entailed:
  assumes
    struct_invs: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    in_trail: \<open>L \<in> lits_of_l (trail S)\<close> and
    lev: \<open>get_level (trail S) L = 0\<close>
  shows
    \<open>clauses S \<Turnstile>pm {#L#}\<close>
proof -
  have decomp: \<open>all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))\<close>
    using struct_invs unfolding cdcl\<^sub>W_all_struct_inv_def
    by fast
  have L_trail: \<open>{#L#} \<in> unmark_l (trail S)\<close>
    using in_trail by (auto simp: in_unmark_l_in_lits_of_l_iff)
  have n_d: \<open>no_dup (trail S)\<close>
    using struct_invs unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by fast

  show ?thesis
  proof (cases \<open>count_decided (trail S) = 0\<close>)
    case True
    have \<open>get_all_ann_decomposition (trail S) = [([], trail S)]\<close>
      apply (rule no_decision_get_all_ann_decomposition)
      using True by (auto simp: count_decided_0_iff)
    then show ?thesis
      using decomp L_trail
      unfolding all_decomposition_implies_def
      by (auto intro: true_clss_clss_in_imp_true_clss_cls)
  next
    case False
    then obtain K M1 M2 M3 where
      decomp': \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
      lev_K: \<open>get_level (trail S) K = Suc 0\<close> and
      M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
      using struct_invs backtrack_ex_decomp[of S 0] unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    then have dec_M1: \<open>count_decided M1 = 0\<close>
      using n_d by auto
    define M2' where \<open>M2' = M3 @ M2\<close>
    then have M3: \<open>trail S = M2' @ Decided K # M1\<close> using M3 by auto
    have \<open>get_all_ann_decomposition M1 = [([], M1)]\<close>
      apply (rule no_decision_get_all_ann_decomposition)
      using dec_M1 by (auto simp: count_decided_0_iff)
    then have \<open>([], M1) \<in> set (get_all_ann_decomposition (trail S))\<close>
      using hd_get_all_ann_decomposition_skip_some[of Nil M1 M1 \<open>_ @ _\<close>] decomp'
      by auto
    then have \<open>set_mset (clauses S) \<Turnstile>ps unmark_l M1\<close>
      using decomp
      unfolding all_decomposition_implies_def by auto
    moreover {
      have \<open>L \<in> lits_of_l M1\<close>
        using n_d lev M3 in_trail
        by (cases \<open>undefined_lit (M2' @ Decided K # []) L\<close>) (auto dest: in_lits_of_l_defined_litD)
      then have \<open>{#L#} \<in> unmark_l M1\<close>
        using in_trail by (auto simp: in_unmark_l_in_lits_of_l_iff) 
    }
    ultimately show ?thesis
      unfolding all_decomposition_implies_def
      by (auto intro: true_clss_clss_in_imp_true_clss_cls)
  qed
qed
end


lemma
  fixes L :: \<open>'v literal\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, Some D)\<close>
  assumes 
    init_analysis: \<open>init_analysis = [(L, C)]\<close> and
    in_trail: \<open>Propagated (-L) (add_mset (-L) C) \<in> set M\<close> and
    \<open>conflict_min_analysis_inv cach (N + U) D\<close> and
    L_D: \<open>L \<in># D\<close>
  shows
    \<open>lit_redundant_rec M (N + U) D cach init_analysis \<le> lit_redundant_rec_spec (N + U) D L\<close>
proof -
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated (- L) (add_mset (- L) C) # M1\<close>
    using split_list[OF in_trail] by (auto 5 5)
  have \<open>a @ Propagated L mark # b = trail (M, N, U, Some D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have \<open>M1 \<Turnstile>as CNot C\<close>
    by (force simp: M)
  then have M_C: \<open>M \<Turnstile>as CNot C\<close>
    unfolding M by (simp add: true_annots_append_l)
  have \<open>set (get_all_mark_of_propagated (trail (M, N, U, Some D)))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N, U, Some D))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  then have \<open>add_mset (-L) C \<in># N + U\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of \<open>add_mset (-L) C\<close> M]
    by (auto simp: clauses_def)
  then have NU_C: \<open>N + U \<Turnstile>pm add_mset (- L) C\<close>
    by auto
  have M_D: \<open>M \<Turnstile>as CNot D\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by auto

  let ?f = \<open>\<lambda>analysis. fold_mset (op +) D (snd `# mset analysis)\<close>
  define I' where
    \<open>I' = (\<lambda>(cach :: 'v conflict_min_cach, analysis :: 'v conflict_min_analyse, b::bool).
        M \<Turnstile>as CNot (?f analysis))\<close>
  define R where
    \<open>R = {((cach :: 'v conflict_min_cach, analysis :: 'v conflict_min_analyse, b::bool),
           (cach' :: 'v conflict_min_cach, analysis' :: 'v conflict_min_analyse, b' :: bool)).
           (analysis' \<noteq> [] \<and> (minimize_conflict M) (?f analysis') (?f analysis)) \<or>
           (analysis' \<noteq> [] \<and> analysis = tl analysis' \<and> snd (hd analysis') = {#}) \<or>
           (analysis' \<noteq> [] \<and>analysis = [])}\<close>
  have wf_R: \<open>wf R\<close>
  proof -
    have R: \<open>R = 
              {((cach, analysis, b), (cach', analysis', b')).
                 analysis' \<noteq> [] \<and>analysis = []} \<union>
              ({((cach, analysis, b), (cach', analysis', b')).
                  analysis' \<noteq> [] \<and> (minimize_conflict M) (?f analysis') (?f analysis)} \<union>
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

    have 2: \<open>wf {(C', C).minimize_conflict M C C'}\<close>
      by (rule wf_minimize_conflict[OF invs])
    from wf_if_measure_f[OF this, of ?f] 
    have 2: \<open>wf {(C', C). minimize_conflict M (?f C) (?f C')}\<close>
      by auto
    from wf_fst_wf_pair[OF this, where 'b = bool]
    have \<open>wf {((analysis':: 'v conflict_min_analyse, _ :: bool), (analysis:: 'v conflict_min_analyse,  _:: bool)).
            (minimize_conflict M) (?f analysis) (?f analysis')}\<close>
      by blast
    from wf_snd_wf_pair[OF this, where 'b = \<open>'v conflict_min_cach\<close>]
    have \<open>wf {((M' :: 'v conflict_min_cach, N'), Ma, N).
      (case N' of
       (analysis' :: 'v conflict_min_analyse, _ :: bool) \<Rightarrow>
         \<lambda>(analysis, _).
            minimize_conflict M (fold_mset op + D (snd `# mset analysis))
              (fold_mset op + D (snd `# mset analysis'))) N}\<close>
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
  have init_I: \<open>lit_redundant_inv M (N + U) D init_analysis (cach, init_analysis, False)\<close>
    using assms NU_C unfolding lit_redundant_inv_def
    by auto
  have \<open>(minimize_conflict M) D (remove1_mset L (C + D))\<close>
    using minimize_conflict.resolve_propa[OF in_trail, of \<open>remove1_mset L D\<close>] L_D
    by (auto simp: ac_simps)

  then have init_I': \<open>I' (cach, init_analysis, False)\<close>
    using M_D L_D M_C unfolding I'_def by (auto simp: init_analysis)
  have all_removed: \<open>lit_redundant_inv M (N + U) D init_analysis
       (cach(fst (hd analysis) := SEEN_REMOVABLE), tl analysis, True)\<close> (is ?I) and
     all_removed_I': \<open>I' (cach(fst (hd analysis) := SEEN_REMOVABLE), tl analysis, True)\<close> (is ?I')
    if
      inv: \<open>lit_redundant_inv M (N + U) D init_analysis s\<close> and
      inv_I': \<open>I' s\<close>
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
      cach: \<open>conflict_min_analysis_inv cach (N + U) D\<close> and
      ana: \<open>conflict_min_analysis_stack (N + U) D analysis\<close> and
      stack: \<open>conflict_min_analysis_stack (N + U) D analysis\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd (N + U) D analysis\<close> and
      last_analysis: \<open>analysis \<noteq> [] \<longrightarrow> fst (last analysis) = fst (hd init_analysis)\<close> and
      b: \<open>analysis = [] \<longrightarrow> b \<longrightarrow> cach (fst (hd init_analysis)) = SEEN_REMOVABLE\<close>
      using inv unfolding lit_redundant_inv_def s by auto
    obtain C where
       NU_C: \<open>N + U \<Turnstile>pm add_mset (-L) C\<close> and
       IH: \<open>\<And>K. K \<in># C \<Longrightarrow> N + U \<Turnstile>pm add_mset (-K) D\<close>
      using stack_hd unfolding analysis by auto

    have NU_D: \<open>N + U \<Turnstile>pm add_mset (- fst (hd analysis)) D\<close>
      using conflict_minimize_intermediate_step[OF NU_C IH] unfolding analysis by auto
    have ana': \<open>conflict_min_analysis_stack (N + U) D (tl analysis)\<close>
      using ana by (auto simp: conflict_min_analysis_stack_tl)
    have cach': \<open>conflict_min_analysis_inv (cach(fst (hd analysis) := SEEN_REMOVABLE)) (N + U) D\<close>
      using NU_D by (auto simp: conflict_min_analysis_inv_update_removable cach)
    have stack_hd': \<open>conflict_min_analysis_stack_hd (N + U) D ana'\<close>
    proof (cases \<open>ana' = []\<close>)
      case True
      then show ?thesis by auto
    next
      case False
      then obtain L' C' ana'' where ana'': \<open>ana' = (L', C') # ana''\<close> by (cases ana'; cases \<open>hd ana'\<close>) auto
      then obtain E' where
         NU_E': \<open>N+U \<Turnstile>pm add_mset (- L') E'\<close> and
         \<open>\<forall>K\<in>#E' - add_mset L C'. N+U \<Turnstile>pm add_mset (- K) D\<close>
         using stack
         by (auto simp: analysis ana'')
       moreover have \<open>N+U \<Turnstile>pm add_mset (- L) D\<close>
         using NU_D analysis by auto
       moreover have \<open>K \<in># E' - C' \<Longrightarrow> K \<in># E' - add_mset L C' \<or> K = L\<close> for K
         by (cases \<open>L \<in># E'\<close>)
           (fastforce simp: minus_notin_trivial dest!: multi_member_split[of L] dest: in_remove1_msetI)+
       ultimately have \<open>K \<in># E' - C' \<Longrightarrow> set_mset N \<union> set_mset U \<Turnstile>p add_mset (- K) D\<close> for K
         by auto
       then show ?thesis using NU_E'
         unfolding ana'' by auto
    qed

    have \<open>fst (hd init_analysis) = fst (last (tl analysis))\<close> if \<open>tl analysis \<noteq> []\<close>
      using last_analysis tl_last[symmetric, OF that] that unfolding ana' by auto
    then show ?I
      using ana' cach' last_analysis stack_hd' unfolding lit_redundant_inv_def
      by (auto simp: analysis)
    show ?I'
      using inv_I' unfolding I'_def s by (auto simp: analysis)
  qed
  have all_removed_R: \<open>((cach(fst (hd analyse) := SEEN_REMOVABLE), tl analyse, True), s) \<in> R\<close>
    if
      \<open>lit_redundant_inv M (N + U) D init_analysis s\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> and
      nempty: \<open>analyse \<noteq> []\<close> and
      finished: \<open>snd (hd analyse) = {#}\<close>
    for s cach s' analyse b
    using nempty finished unfolding R_def s by auto
  have 
    seen_removable_inv: \<open>lit_redundant_inv M (N + U) D init_analysis (cach, ana, False)\<close> (is ?I) and
    seen_removable_I': \<open>I' (cach, ana, False)\<close> (is ?I') and
    seen_removable_R: \<open>((cach, ana, False), s) \<in> R\<close> (is ?R)
    if 
      inv: \<open>lit_redundant_inv M (N + U) D init_analysis s\<close> and
      inv_I': \<open>I' s\<close> and
      cond: \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> \<open>x = (L, ana)\<close> and
      nemtpy_stack: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      next_lit: \<open>case x of
        (L, ana) \<Rightarrow> L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and> ana \<noteq> [] \<and>
          hd ana = (fst (hd analyse), remove1_mset L (snd (hd analyse)))\<close> and
      lev0_removable: \<open>get_level M L = 0 \<or> cach L = SEEN_REMOVABLE\<close>
    for s cach s' analyse b x L ana
  proof -
    obtain K C ana' where analysis: \<open>analyse = (K, C) # ana'\<close>
      using nemtpy_stack by (cases analyse) auto
    have ana': \<open>ana = (K, remove1_mset L C) # ana'\<close>
      using next_lit unfolding s by (cases ana) (auto simp: analysis)
    have
      cach: \<open>conflict_min_analysis_inv cach (N + U) D\<close> and
      ana: \<open>conflict_min_analysis_stack (N + U) D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack (N + U) D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd (N + U) D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (fst (hd init_analysis)) = SEEN_REMOVABLE\<close>
      using inv unfolding lit_redundant_inv_def s by auto

    have last_analysis': \<open>ana \<noteq> [] \<Longrightarrow> fst (hd init_analysis) = fst (last ana)\<close>
      using last_analysis next_lit unfolding analysis s 
      by (cases ana) (auto split: if_splits)
    have H: \<open>\<exists>CK. N + U \<Turnstile>pm add_mset (- K) CK \<and> (\<forall>K\<in>#CK - remove1_mset L C. N + U \<Turnstile>pm D + {#- K#})\<close>
      (is \<open>\<exists>C. ?P C\<close>)
      using lev0_removable
    proof
      assume \<open>cach L = SEEN_REMOVABLE\<close>
      then have L: \<open>set_mset N \<union> set_mset U \<Turnstile>p add_mset (- L) D\<close>
        using cach unfolding conflict_min_analysis_inv_def by auto
      obtain CK where
        \<open>N + U \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>K\<in>#CK - C. N + U \<Turnstile>pm D + {#- K#}\<close>
        using stack_hd unfolding analysis by auto
      then have \<open>?P CK\<close>
        using L by (auto simp: minus_remove1_mset_if)
      then show ?thesis by blast
    next
      assume lev0: \<open>get_level M L = 0\<close>
      have \<open>M \<Turnstile>as CNot (?f analyse)\<close>
        using inv_I' unfolding I'_def s by auto
      then have \<open>-L \<in> lits_of_l M\<close>
        using next_lit unfolding analysis s by (auto dest: multi_member_split)
      then have \<open>N + U \<Turnstile>pm {#-L#}\<close>
        using lev0 cdcl\<^sub>W_restart_mset.literals_of_level0_entailed[OF invs, of \<open>-L\<close>]
        by (auto simp: clauses_def)
      moreover obtain CK where
        \<open>N + U \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>K\<in>#CK - C. N + U \<Turnstile>pm D + {#- K#}\<close>
        using stack_hd unfolding analysis by auto
      ultimately have \<open>?P CK\<close>
        by (auto simp: minus_remove1_mset_if intro: conflict_minimize_intermediate_step)
      then show ?thesis by blast
    qed note H = this
    have stack': \<open>conflict_min_analysis_stack (N + U) D ana\<close>
      using stack unfolding ana' analysis by (cases ana') auto
    have stack_hd': \<open>conflict_min_analysis_stack_hd (N + U) D ana\<close>
      using H unfolding ana' by auto

    show ?I
      using last_analysis' cach stack' stack_hd' unfolding lit_redundant_inv_def s
      by auto
    have \<open>M \<Turnstile>as CNot (?f ana)\<close>
      using inv_I' unfolding I'_def s ana analysis ana'
      by (cases \<open>L \<in># C\<close>) (auto dest!: multi_member_split)
    then show ?I'
      using inv_I' unfolding I'_def s by auto

    show ?R
      using next_lit
      unfolding R_def s by (auto simp: ana' analysis dest!: multi_member_split
          intro: minimize_conflict.intros)
  qed
  have
    failed_I: \<open>lit_redundant_inv M (N + U) D init_analysis
       (cach', [], False)\<close> (is ?I) and
    failed_I': \<open>I' (cach', [], False)\<close> (is ?I') and
    failed_R: \<open>((cach', [], False), s) \<in> R\<close> (is ?R)
    if 
      inv: \<open>lit_redundant_inv M (N + U) D init_analysis s\<close> and
      inv_I': \<open>I' s\<close> and
      cond: \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> and
      nempty: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      \<open>case x of (L, ana) \<Rightarrow> L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and>
        ana \<noteq> [] \<and> hd ana = (fst (hd analyse), remove1_mset L (snd (hd analyse)))\<close> and
      \<open>x = (L, ana)\<close> and
      \<open>\<not> (get_level M L = 0 \<or> cach L = SEEN_REMOVABLE)\<close> and
      \<open>E \<noteq> None \<longrightarrow> Propagated (- L) (the E) \<in> set M\<close> and
      \<open>E = None\<close> and
      cach_update: \<open>\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE\<close>
    for s cach s' analyse b x L ana E cach'
  proof -
    have
      cach: \<open>conflict_min_analysis_inv cach (N + U) D\<close> and
      ana: \<open>conflict_min_analysis_stack (N + U) D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack (N + U) D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (fst (hd init_analysis)) = SEEN_REMOVABLE\<close>
      using inv unfolding lit_redundant_inv_def s by auto
    have \<open>conflict_min_analysis_inv cach' (N + U) D\<close>
      using cach cach_update by (auto simp: conflict_min_analysis_inv_def)
    moreover have \<open>conflict_min_analysis_stack (N + U) D []\<close>
      by simp
    ultimately show ?I
      unfolding lit_redundant_inv_def by simp
    show ?I'
      using M_D unfolding I'_def by auto
    show ?R
      using nempty unfolding R_def s by auto
  qed
  have is_propagation_inv: \<open>lit_redundant_inv M (N + U) D init_analysis
       (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?I) and
    is_propagation_I': \<open>I' (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?I') and
    is_propagation_R: \<open>((cach, (L, remove1_mset (-L) E') # ana, False), s) \<in> R\<close> (is ?R)
    if 
      inv: \<open>lit_redundant_inv M (N + U) D init_analysis s\<close> and
      inv_I': \<open>I' s\<close> and
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
      \<open>\<not> (get_level M L = 0 \<or> cach L = SEEN_REMOVABLE)\<close> and
      E: \<open>E \<noteq> None \<longrightarrow> Propagated (- L) (the E) \<in> set M\<close> \<open>E = Some E'\<close>
    for s cach s' analyse b x L ana E E'
  proof -
    obtain K C ana' where analysis: \<open>analyse = (K, C) # ana'\<close>
      using nemtpy_stack by (cases analyse) auto
    have ana': \<open>ana = (K, remove1_mset L C) # ana'\<close>
      using next_lit unfolding s by (cases ana) (auto simp: analysis)
    have
      cach: \<open>conflict_min_analysis_inv cach (N + U) D\<close> and
      ana: \<open>conflict_min_analysis_stack (N + U) D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack (N + U) D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd (N + U) D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (fst (hd init_analysis)) = SEEN_REMOVABLE\<close>
      using inv unfolding lit_redundant_inv_def s by auto
    have NU_E: \<open>N + U \<Turnstile>pm add_mset (- L) (remove1_mset (-L) E')\<close> and uL_E: \<open>-L \<in># E'\<close> and
       M_E': \<open>M \<Turnstile>as CNot (remove1_mset (- L) E')\<close>
      using Propagated_in_trail_entailed[OF invs, of \<open>-L\<close> E'] E by auto
    have \<open>conflict_min_analysis_stack (N + U) D ((L, remove1_mset (-L) E') # ana)\<close>
      using stack E next_lit NU_E uL_E stack_hd unfolding s ana'[symmetric]
      by (auto simp: analysis ana' conflict_min_analysis_stack_change_hd)
    moreover have \<open>conflict_min_analysis_stack_hd (N + U) D ((L, remove1_mset (- L) E') # ana)\<close>
      using NU_E by auto
    moreover have \<open>fst (hd init_analysis) = fst (last ((L, remove1_mset (- L) E') # ana))\<close>
      using last_analysis unfolding analysis ana' by auto
    ultimately show ?I
      using cach b unfolding lit_redundant_inv_def analysis by auto

    show ?I'
      using M_E' inv_I' unfolding I'_def s ana analysis ana' by (auto simp: true_annot_CNot_diff)

    have \<open>L \<in># C\<close> and in_trail: \<open>Propagated (- L) (the E) \<in> set M\<close> and E: \<open>the E = E'\<close>
      using next_lit E by (auto simp: analysis ana' s)
    then obtain E'' C' where 
      E': \<open>E' = add_mset (-L) E''\<close> and
      C: \<open>C = add_mset L C'\<close>
      using uL_E by (blast dest: multi_member_split)

    have \<open>minimize_conflict M (C + fold_mset op + D (snd `# mset ana'))
           (remove1_mset (- L) E' + (remove1_mset L C + fold_mset op + D (snd `# mset ana')))\<close>
      using minimize_conflict.resolve_propa[OF in_trail, of \<open>C' + fold_mset op + D (snd `# mset ana')\<close>]
      unfolding C E' E
      by (auto simp: ac_simps)

    then show ?R
      using nemtpy_stack unfolding s analysis ana' by (auto simp: R_def
          intro: resolve_propa)
  qed
  show ?thesis
    unfolding lit_redundant_rec_def lit_redundant_rec_spec_def mark_failed_lits_def
      get_literal_and_remove_of_analyse_def get_propagation_reason_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = R and I' = I'])
      -- \<open>Well foundedness\<close>
    subgoal by (rule wf_R)
    subgoal by (rule init_I)
    subgoal by (rule init_I')
    subgoal by simp
        -- \<open>We finished one stage:\<close>
    subgoal by (rule all_removed)
    subgoal by (rule all_removed_I')
    subgoal by (rule all_removed_R)
        -- \<open>Cached or level 0:\<close>
    subgoal by (rule seen_removable_inv)
    subgoal by (rule seen_removable_I')
    subgoal by (rule seen_removable_R)
        -- \<open>Failed:\<close>
    subgoal by (rule failed_I)
    subgoal by (rule failed_I')
    subgoal by (rule failed_R)
        -- \<open>The literal was propagated:\<close>
    subgoal by (rule is_propagation_inv)
    subgoal by (rule is_propagation_I')
    subgoal by (rule is_propagation_R)
        -- \<open>End of Loop invariant:\<close>
    subgoal by (auto simp: lit_redundant_inv_def conflict_min_analysis_inv_def init_analysis)
    subgoal by (auto simp: lit_redundant_inv_def conflict_min_analysis_inv_def init_analysis)
    done
qed

end