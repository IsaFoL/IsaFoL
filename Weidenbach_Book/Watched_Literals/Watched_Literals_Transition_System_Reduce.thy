theory Watched_Literals_Transition_System_Reduce
imports Watched_Literals_Transition_System_Restart
begin

inductive cdcl_twl_subsumption_inp :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_subsumed S T \<Longrightarrow> cdcl_twl_subsumption_inp S T\<close> |
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> cdcl_twl_subsumption_inp S T\<close> |
  \<open>cdcl_twl_unitres S T \<Longrightarrow> cdcl_twl_subsumption_inp S T\<close> |
  \<open>cdcl_twl_unitres_true S T \<Longrightarrow> cdcl_twl_subsumption_inp S T\<close> |
  \<open>cdcl_twl_restart S T \<Longrightarrow> cdcl_twl_subsumption_inp S T\<close>

lemma cdcl_twl_restart_entailed_init:
  \<open>cdcl_twl_restart S T \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of (pstate\<^sub>W_of S)) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of (pstate\<^sub>W_of T))\<close>
  by (induction rule: cdcl_twl_restart.induct)
   (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
    subset_mset.le_iff_add Un_left_commute image_Un sup_commute)


lemma cdcl_twl_subsumption_inp_invs:
  assumes \<open>cdcl_twl_subsumption_inp S T\<close>
    \<open>twl_struct_invs S\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    cdcl_twl_subsumption_inp_twl_struct_invs: \<open>twl_struct_invs T\<close> (is ?A) and
    cdcl_twl_subsumption_inp_twl_stgy_invs: \<open>twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close> (is \<open>_ \<Longrightarrow> ?B\<close>) and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close> (is ?C)
proof -
  show ?A
    using assms(1,2,3)
    by (induction rule: cdcl_twl_subsumption_inp.induct)
      (blast dest: cdcl_twl_subsumed_struct_invs cdcl_twl_subresolution_twl_struct_invs
      cdcl_twl_unitres_struct_invs cdcl_twl_unitres_true_twl_struct_invs
      cdcl_twl_restart_twl_struct_invs)+
  show ?C
    using assms(1,2,3)
    apply (induction rule: cdcl_twl_subsumption_inp.induct)
    apply (metis cdcl_subsumed_RI_pcdcl cdcl_subsumed_entailed_by_init cdcl_twl_subsumed_cdcl_subsumed
      rtranclp_pcdcl_entailed_by_init state\<^sub>W_of_def twl_struct_invs_def)
    unfolding state\<^sub>W_of_def
    apply (elim cdcl_twl_subresolution_decompE)
    apply (auto elim!: cdcl_twl_subresolution_decompE
      simp: twl_struct_invs_def struct_wf_twl_cls_alt_def twl_st_inv_alt_def; fail)[]
    apply (rule cdcl_subresolutions_entailed_by_init; assumption)
    apply (metis cdcl_flush_unit_unchanged cdcl_subresolution cdcl_subresolutions_entailed_by_init
      pcdcl.intros(1) pcdcl_core.intros(2) pcdcl_entailed_by_init rtranclp_pcdcl_all_struct_invs
      twl_struct_invs_def)
    apply (drule cdcl_twl_unitres_cdcl_unitres, drule cdcl_unitres_learn_subsume)
    apply assumption+
    using rtranclp_pcdcl_entailed_by_init twl_struct_invs_def apply blast
    apply (drule cdcl_twl_unitres_true_cdcl_unitres_true, drule pcdcl.intros)
    using pcdcl_entailed_by_init twl_struct_invs_def apply blast
    using cdcl_twl_restart_entailed_init by blast
  with assms show ?B if \<open>twl_stgy_invs S\<close>
    using that
    apply (induction rule: cdcl_twl_subsumption_inp.induct)
    apply (metis (no_types, lifting) cdcl_twl_subsumed_stgy_invs)
    using cdcl_twl_subresolution_twl_stgy_invs apply blast
    using cdcl_twl_unitres_twl_stgy_invs apply blast
    apply (metis (no_types, lifting) cdcl_twl_unitres_true_cdcl_unitres_true cdcl_unitres_true_same state\<^sub>W_of_def twl_stgy_invs_def)
    using cdcl_twl_restart_twl_stgy_invs by blast
qed

lemma rtranclp_cdcl_twl_subsumption_inp_invs:
  assumes \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* S T\<close>
    \<open>twl_struct_invs S\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs: \<open>twl_struct_invs T\<close> and
    rtranclp_cdcl_twl_subsumption_inp_twl_stgy_invs: \<open>twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close> and
    rtranclp_cdcl_twl_subsumption_inp_entailed_init:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for T U using cdcl_twl_subsumption_inp_invs[of T U] by auto
  subgoal for T U using cdcl_twl_subsumption_inp_invs[of T U] by auto
  subgoal for T U using cdcl_twl_subsumption_inp_invs[of T U] by auto
  done

lemma cdcl_twl_subsumption_inp_no_new_conflict:
  \<open>cdcl_twl_subsumption_inp S T \<Longrightarrow> get_conflict T = get_conflict S \<or> get_conflict T \<noteq> None \<and> count_decided(get_trail T) = 0\<close>
  by (induction rule: cdcl_twl_subsumption_inp.induct)
   (auto simp: cdcl_twl_subsumed.simps cdcl_twl_subresolution.simps cdcl_twl_unitres.simps
    cdcl_twl_unitres_true.simps cdcl_twl_restart.simps)

lemma rtranclp_pcdcl_restart_inprocessing: \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_inprocessing\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest: pcdcl_inprocessing.intros)
 
lemma cdcl_twl_subsumption_inp_pcdcl:
  \<open>cdcl_twl_subsumption_inp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  pcdcl_inprocessing\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  apply (induction rule: cdcl_twl_subsumption_inp.induct)
  subgoal
    by (meson cdcl_subsumed_RI_pcdcl cdcl_twl_subsumed_cdcl_subsumed pcdcl.intros(4) r_into_rtranclp
      rtranclp_pcdcl_restart_inprocessing)
  subgoal
    apply (rule rtranclp_pcdcl_restart_inprocessing, elim cdcl_twl_subresolution_decompE)
    apply (auto elim!: cdcl_twl_subresolution_decompE
      simp: twl_struct_invs_def struct_wf_twl_cls_alt_def twl_st_inv_alt_def; fail)[]
      apply (drule cdcl_subresolution)
    apply (auto elim!: cdcl_twl_subresolution_decompE
      simp: twl_struct_invs_def struct_wf_twl_cls_alt_def twl_st_inv_alt_def; fail)[]
    by (meson cdcl_subresolution pcdcl.intros(1) pcdcl.intros(5) pcdcl_core.intros(2)
      rtranclp.rtrancl_into_rtrancl)
  subgoal
    by (simp add: cdcl_twl_unitres_cdcl_unitres cdcl_unitres_learn_subsume rtranclp_pcdcl_restart_inprocessing)
  subgoal
    by (simp add: cdcl_twl_unitres_true_cdcl_unitres_true pcdcl.intros(8) r_into_rtranclp
      rtranclp_pcdcl_restart_inprocessing)
  subgoal
    using cdcl_twl_restart_pcdcl pcdcl_inprocessing.intros(2) by blast
  done

lemma rtranclp_cdcl_twl_subsumption_inp_pcdcl:
  \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  pcdcl_inprocessing\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_subsumption_inp_pcdcl[of T U] rtranclp_cdcl_twl_subsumption_inp_invs[of S T]
    by simp
  done



context twl_restart_ops
begin
text \<open>
  This is en essence the calculus with restarts we are now using. Compared to the version in my
  thesis, the major difference is that we don't restrict restarts anymore, by requiring only that
  at least one clause has been learned since.

  However, this has a major drawback: The transition do not depend only on the current state, but
  also on the path that was taken. This is annoying for refinement, because the main loop does not
  do one transition anymore, but only a part of transitions. The difference is very small on the
  practical side, but that makes the termination more involved.

  We allow inprocessing, but restrict it a lot. We could allow anything such that the invariants
  are still fulfilled afterwards, but we currently restrict to be some CDCL steps (TODO: generalise
  to also include restarts) and add requirements on the output.
\<close>
type_synonym 'v twl_st_restart = \<open>'v twl_st \<times> 'v twl_st \<times> 'v twl_st \<times> nat \<times> nat \<times> bool\<close>
inductive cdcl_twl_stgy_restart :: \<open>'v twl_st_restart \<Rightarrow> 'v twl_st_restart  \<Rightarrow> bool\<close> where
step:
 \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (R, S, U, m, n, True)\<close>
 if
   \<open>cdcl_twl_stgy T U\<close> |
restart_step:
  \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (W, W, W, m, Suc n, True)\<close>
  if
    \<open>size (get_all_learned_clss T) - size (get_all_learned_clss R) > f n\<close> and
    \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* T U\<close> and
    (* \<open>get_conflict U \<noteq> None \<longrightarrow> count_decided (get_trail U) = 0\<close> *)
    \<open>cdcl_twl_restart U V\<close> and
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close>
    \<open>clauses_to_update W = {#}\<close>
    \<open>get_conflict W \<noteq> None \<longrightarrow> count_decided (get_trail W) = 0\<close> |
restart_noGC:
  \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (R, U, U, Suc m, n, True)\<close>
  if
    \<open>size (get_all_learned_clss T) > size (get_all_learned_clss S)\<close> and
    \<open>cdcl_twl_restart_only T U\<close> |
restart_full:
 \<open>cdcl_twl_stgy_restart (R, S, T, m, n, True) (R, S, T, m, n, False)\<close>
 if
   \<open>pcdcl_twl_final_state T\<close>

lemma cdcl_twl_stgy_restart_induct[consumes 1, case_names restart_step restart_noGC full]:
  assumes
    \<open>cdcl_twl_stgy_restart (R, S, T, m, n, b) (R', S', T', m', n', b')\<close> and
    \<open>\<And>R S T U. cdcl_twl_stgy T U \<Longrightarrow> m' = m \<Longrightarrow> n' = n \<Longrightarrow> b \<Longrightarrow> b' \<Longrightarrow>  P R S T m n True R S U m n True\<close> and
    \<open>\<And>R S T U V W.
      f n < size (get_all_learned_clss T) - size (get_all_learned_clss R) \<Longrightarrow> cdcl_twl_subsumption_inp\<^sup>*\<^sup>* T U \<Longrightarrow>
      cdcl_twl_restart U V \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V W \<Longrightarrow>
     clauses_to_update W = {#} \<Longrightarrow> (get_conflict W \<noteq> None \<Longrightarrow> count_decided (get_trail W) = 0) \<Longrightarrow>
      m' = m \<Longrightarrow> n' = Suc n \<Longrightarrow>
      P R S T m n True W W W m (Suc n) True\<close>and
    \<open>\<And>R S T U.
      size (get_all_learned_clss T) > size (get_all_learned_clss S) \<Longrightarrow>
      cdcl_twl_restart_only T U \<Longrightarrow> m' = Suc m \<Longrightarrow> n' = n \<Longrightarrow>
    P R S T m n True R U U (Suc m) n True\<close>
    \<open>pcdcl_twl_final_state T \<Longrightarrow> R' = R \<Longrightarrow> S' = S \<Longrightarrow> T' = T \<Longrightarrow> P R S T m n True R S T m n False\<close>
  shows \<open>P R S T m n b R' S' T' m' n' b'\<close>
  using assms(1)
  apply (cases rule: cdcl_twl_stgy_restart.cases)
  subgoal
    using assms(2)[of T T' R S]
    by simp
  subgoal for U
    using assms(3)[of ]
    by simp
  subgoal
    using assms(4)[of ]
    by simp
  subgoal
    using assms(5)[of ]
    by simp
  done


lemma tranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy2:
  \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T \<Longrightarrow>
  twl_struct_invs S \<Longrightarrow> (pstate\<^sub>W_of S) \<noteq> (pstate\<^sub>W_of T) \<Longrightarrow>
  pcdcl_tcore_stgy\<^sup>+\<^sup>+ (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[of S T] unfolding rtranclp_unfold
  by auto

lemma tranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy3:
  \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T \<Longrightarrow>
  size (get_all_learned_clss T) > size (get_all_learned_clss S) \<Longrightarrow>
  twl_struct_invs S \<Longrightarrow>
  pcdcl_tcore_stgy\<^sup>+\<^sup>+ (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy[of S T] unfolding rtranclp_unfold
  apply auto
  apply (cases T; cases S)
  apply (auto simp: clauses_def dest!: arg_cong[of \<open>clauses _\<close> _ size])
  done

lemma [twl_st, simp]:
  \<open>pget_all_learned_clss (pstate\<^sub>W_of T) = get_all_learned_clss T\<close>
  \<open>pget_conflict (pstate\<^sub>W_of T) = get_conflict T\<close>
  by (cases T; auto; fail)+

lemma pcdcl_twl_final_state_pcdcl:
  \<open>pcdcl_twl_final_state S \<Longrightarrow>
  twl_struct_invs S \<Longrightarrow> pcdcl_final_state (pstate\<^sub>W_of S)\<close>
  using no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy[of S]
  unfolding pcdcl_twl_final_state_def pcdcl_final_state_def
  by (auto simp add: no_step_pcdcl_core_stgy_pcdcl_coreD)

lemma pcdcl_stgy_restart_stepI:
  \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* T T' \<Longrightarrow> pcdcl_stgy_restart\<^sup>*\<^sup>* (R, S, T, m, n, True) (R, S, T', m, n, True)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for V W
    by (auto dest!: pcdcl_stgy_restart.intros(1)[of _ _ R S m n])
  done

lemma rtranclp_cdcl_twl_subsumption_inp_pcdcl_inprocessing:
  \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  pcdcl_inprocessing\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  by (drule rtranclp_cdcl_twl_subsumption_inp_pcdcl; assumption?)

lemma cdcl_twl_stgy_restart_pcdcl:
  \<open>cdcl_twl_stgy_restart (R, S :: 'v twl_st, T, m, n, g) (R', S', T', m', n', h) \<Longrightarrow>
  twl_struct_invs R \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_struct_invs T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<Longrightarrow>
  pcdcl_stgy_restart\<^sup>*\<^sup>* (pstate\<^sub>W_of R, pstate\<^sub>W_of S, pstate\<^sub>W_of T, m, n, g)
      (pstate\<^sub>W_of R', pstate\<^sub>W_of S', pstate\<^sub>W_of T', m', n', h)\<close>
  apply (induction rule: cdcl_twl_stgy_restart_induct)
  subgoal for R S T U
    by (drule cdcl_twl_stgy_cdcl\<^sub>W_stgy)
      (simp add: pcdcl_stgy_restart_stepI)+
  subgoal
    apply (rule r_into_rtranclp)
    apply (rule pcdcl_stgy_restart.intros(2))
      term pcdcl_stgy_restart
    apply simp
    apply (rule rtranclp_cdcl_twl_subsumption_inp_pcdcl_inprocessing; assumption)
    apply (rule cdcl_twl_restart_pcdcl, assumption)
    using cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_tcore_stgy_pcdcl_stgy'
    apply (simp_all add: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs)
    apply (smt cdcl_twl_restart_pcdcl pcdcl_restart_no_smaller_propa' rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs state\<^sub>W_of_def twl_struct_invs_def)
    done
  subgoal
    apply (rule r_into_rtranclp)
    apply (rule pcdcl_stgy_restart.intros(3))
    apply simp
    apply (rule cdcl_twl_restart_only_cdcl, assumption)
    done
  subgoal
    apply (rule r_into_rtranclp)
    apply (rule pcdcl_stgy_restart.intros(4))
    by (simp add: twl_restart_ops.pcdcl_twl_final_state_pcdcl)
  done


lemma cdcl_twl_stgy_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_struct_invs (fst (snd S))\<close> and
    \<open>twl_struct_invs (fst (snd (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of  (fst (snd (snd S))))\<close>
  shows \<open>twl_struct_invs (fst T) \<and> twl_struct_invs (fst (snd T)) \<and> twl_struct_invs (fst (snd (snd T)))\<close>
  using assms
  by (induction rule: cdcl_twl_stgy_restart.induct)
  (auto simp add: full1_def intro: rtranclp_cdcl_twl_stgy_twl_struct_invs
      dest: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs
      rtranclp_cdcl_twl_stgy_twl_struct_invs
   cdcl_twl_restart_only_twl_struct_invs
   simp:
     cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
     rtranclp_cdcl_twl_stgy_twl_struct_invs rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
   dest!: tranclp_into_rtranclp intro: rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs)

lemma pcdcl_restart_entailed_by_init:
  assumes \<open>pcdcl_restart S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl_restart.induct)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      subset_mset.le_iff_add ac_simps)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      subset_mset.le_iff_add ac_simps)
  done

lemma pcdcl_restart_only_entailed_by_init:
  assumes \<open>pcdcl_restart_only S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl_restart_only.induct)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      subset_mset.le_iff_add ac_simps)
  done


lemma cdcl_twl_stgy_restart_entailed_by_init:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_struct_invs (fst (snd S))\<close> and
    \<open>twl_struct_invs (fst (snd (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd S))))\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst T)) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd T))) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd T))))\<close>
  using assms
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal apply simp
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_entailed_by_init rtranclp_pcdcl_stgy_pcdcl
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' twl_struct_invs_def by blast
    subgoal apply simp
      by (metis (mono_tags, lifting) cdcl_twl_subsumption_inp.intros(5) rtranclp.rtrancl_into_rtrancl
        rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_cdcl_twl_subsumption_inp_entailed_init
        rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs rtranclp_pcdcl_entailed_by_init
        rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' state\<^sub>W_of_def
        twl_struct_invs_def)
    subgoal apply simp
      using cdcl_twl_restart_only_cdcl twl_restart_ops.pcdcl_restart_only_entailed_by_init
        twl_struct_invs_def by blast
    subgoal
      by simp
    done

lemma rtranclp_cdcl_twl_stgy_restart_twl_struct_invs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs (fst S)\<close> and
    \<open>twl_struct_invs (fst (snd S))\<close> and
    \<open>twl_struct_invs (fst (snd (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd S))))\<close>
  shows \<open>twl_struct_invs (fst T) \<and> twl_struct_invs (fst (snd T)) \<and> twl_struct_invs (fst (snd (snd T))) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst T)) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd T))) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd T))))\<close>
  using assms
  apply (induction)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_entailed_by_init[of T U] cdcl_twl_stgy_restart_twl_struct_invs[of T U]
    by simp
  done

lemma rtranclp_cdcl_twl_stgy_restart_pcdcl:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (R, S :: 'v twl_st, T, m, n, g) (R', S', T', m', n', h) \<Longrightarrow>
  twl_struct_invs R \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_struct_invs T \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of R) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<Longrightarrow>
  pcdcl_stgy_restart\<^sup>*\<^sup>* (pstate\<^sub>W_of R, pstate\<^sub>W_of S, pstate\<^sub>W_of T, m, n, g)
      (pstate\<^sub>W_of R', pstate\<^sub>W_of S', pstate\<^sub>W_of T', m', n', h)\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _, _, _, _)\<close> \<open>(_, _, _, _, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for R' S' T' m' n' g' R'' S'' T'' m'' n'' g''
    using rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of \<open>(R, S, T, m, n, g)\<close> \<open>(R', S', T', m', n', g')\<close>]
    by (auto dest: cdcl_twl_stgy_restart_pcdcl)
  done

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2:
  assumes \<open>cdcl_twl_stgy_restart (S, T, U, m, n, g) (S', T', U', m', n', g')\<close>
    and twl: \<open>twl_struct_invs U\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
  shows \<open>pcdcl_stgy_restart (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g)
       (pstate\<^sub>W_of S', pstate\<^sub>W_of T', pstate\<^sub>W_of U', m', n', g') \<or>
    (S = S' \<and> T = T' \<and> m = m' \<and> n = n' \<and> g = g' \<and>
      pstate\<^sub>W_of U = pstate\<^sub>W_of U' \<and> (literals_to_update_measure U', literals_to_update_measure U)
    \<in> lexn less_than 2)\<close>
  using assms(1,2,3)
  apply (induction rule: cdcl_twl_stgy_restart_induct)
  subgoal for R S T U
    by (drule  cdcl_twl_stgy_cdcl\<^sub>W_stgy2)
      (auto simp add: pcdcl_stgy_restart.step)
  subgoal
    apply (rule disjI1)
    apply (rule pcdcl_stgy_restart.intros(2))
    apply simp
    apply (rule rtranclp_cdcl_twl_subsumption_inp_pcdcl_inprocessing)
    apply assumption+
    apply (rule cdcl_twl_restart_pcdcl, assumption)
    using cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_tcore_stgy_pcdcl_stgy'
    apply (simp_all add: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs)
    by (smt cdcl_twl_restart_pcdcl pcdcl_restart_no_smaller_propa' rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs state\<^sub>W_of_def twl_struct_invs_def)
  subgoal
    apply (rule disjI1)
    apply (rule pcdcl_stgy_restart.intros(3))
    apply simp
    apply (rule cdcl_twl_restart_only_cdcl, assumption)
    done
  subgoal
    apply (rule disjI1)
    apply (rule pcdcl_stgy_restart.intros(4))
    by (simp add: twl_restart_ops.pcdcl_twl_final_state_pcdcl)
  done

abbreviation state\<^sub>W_of_restart where
  \<open>state\<^sub>W_of_restart \<equiv> (\<lambda>(S, T, U, n, b). (state\<^sub>W_of S, state\<^sub>W_of T, state\<^sub>W_of U, n))\<close>

definition twl_restart_inv :: \<open>'v twl_st_restart \<Rightarrow> bool\<close> where
  \<open>twl_restart_inv = (\<lambda>(Q, R, S, m, n). twl_struct_invs Q \<and> twl_struct_invs R \<and> twl_struct_invs S \<and>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of Q) \<and>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of R) \<and>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
   pcdcl_stgy_restart_inv (pstate\<^sub>W_of Q, pstate\<^sub>W_of R, pstate\<^sub>W_of S, m, n))\<close>
lemma cdcl_twl_stgy_entailed_by_init:
  \<open>cdcl_twl_stgy S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  apply (induction rule: cdcl_twl_stgy.induct)
  apply (metis cdcl_twl_stgy_cdcl\<^sub>W_stgy cp rtranclp_pcdcl_entailed_by_init rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' state\<^sub>W_of_def twl_struct_invs_def)
  by (metis cdcl_twl_o_cdcl\<^sub>W_o_stgy pcdcl_tcore_pcdcl pcdcl_tcore_stgy_pcdcl_tcoreD rtranclp_pcdcl_entailed_by_init state\<^sub>W_of_def twl_struct_invs_def)

lemma rtranclp_cdcl_twl_stgy_entailed_by_init:
  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  apply (induction rule: rtranclp_induct)
  apply auto[]
  using rtranclp_cdcl_twl_stgy_twl_struct_invs twl_restart_ops.cdcl_twl_stgy_entailed_by_init by blast

lemma cdcl_twl_stgy_restart_twl_restart_inv:
  \<open>cdcl_twl_stgy_restart S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_restart_inv T\<close>
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal for T U R S m n
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2[of R S T m n True R S U m n True]
    unfolding twl_restart_inv_def
    apply (auto intro: cdcl_twl_stgy_twl_struct_invs
      simp: pcdcl_stgy_restart_pcdcl_stgy_restart_inv cdcl_twl_stgy_restart.intros)
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_entailed_by_init rtranclp_pcdcl_stgy_pcdcl
      rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' unfolding twl_struct_invs_def by blast
  subgoal for T R n U V W S m
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2[of R S T m n True W W W m \<open>Suc n\<close> True]
    unfolding twl_restart_inv_def
    apply (auto intro: cdcl_twl_stgy_twl_struct_invs
      simp: pcdcl_stgy_restart_pcdcl_stgy_restart_inv cdcl_twl_stgy_restart.intros
      cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_struct_invs
      rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs rtranclp_pcdcl_all_struct_invs
      rtranclp_pcdcl_entailed_by_init pcdcl_restart_entailed_by_init
      intro: pcdcl_restart_entailed_by_init rtranclp_pcdcl_entailed_by_init
      dest: rtranclp_cdcl_twl_subsumption_inp_pcdcl cdcl_twl_restart_pcdcl)
    apply (metis cdcl_twl_restart_twl_struct_invs cdcl_twl_subsumption_inp.intros(5)
      cdcl_twl_subsumption_inp_invs(3) rtranclp_cdcl_twl_subsumption_inp_entailed_init
      rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs state\<^sub>W_of_def
      rtranclp_cdcl_twl_stgy_entailed_by_init)
    by (metis cdcl_twl_restart_twl_struct_invs cdcl_twl_subsumption_inp.intros(5)
      cdcl_twl_subsumption_inp_invs(3) rtranclp_cdcl_twl_subsumption_inp_entailed_init
      rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs state\<^sub>W_of_def
      rtranclp_cdcl_twl_stgy_entailed_by_init)
  subgoal for T S U R m n
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2[of R S T m n True R U U \<open>Suc m\<close> n True]
    unfolding twl_restart_inv_def
    apply (auto intro: cdcl_twl_stgy_twl_struct_invs
      simp: pcdcl_stgy_restart_pcdcl_stgy_restart_inv cdcl_twl_stgy_restart.intros
      cdcl_twl_restart_only_twl_struct_invs)
      using cdcl_twl_restart_only_cdcl twl_restart_ops.pcdcl_restart_only_entailed_by_init twl_struct_invs_def by blast
  subgoal
    unfolding twl_restart_inv_def pcdcl_stgy_restart_inv_def prod.simps by blast
  done

lemma rtranclp_cdcl_twl_stgy_restart_twl_restart_inv:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_restart_inv T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: cdcl_twl_stgy_restart_twl_restart_inv)

definition twl_stgy_restart_inv :: \<open>'v twl_st_restart \<Rightarrow> bool\<close> where
  \<open>twl_stgy_restart_inv = (\<lambda>(Q, R, S, m, n). twl_stgy_invs Q \<and> twl_stgy_invs R \<and> twl_stgy_invs S)\<close>
lemma cdcl_twl_restart_only_twl_stgy_invs:
  \<open>cdcl_twl_restart_only S T \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  by (auto simp: cdcl_twl_restart_only.simps twl_stgy_invs_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
    dest!: get_all_ann_decomposition_exists_prepend)

lemma cdcl_twl_stgy_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy_restart S T\<close> and
    \<open>twl_restart_inv S\<close> and
    \<open>twl_stgy_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst (snd S))\<close> and
    \<open>twl_stgy_invs (fst (snd (snd S)))\<close>and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd S)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of (fst (snd (snd S))))\<close>
  shows \<open>twl_stgy_invs (fst T) \<and> twl_stgy_invs (fst (snd T)) \<and> twl_stgy_invs (fst (snd (snd T)))\<close>
  using assms
  apply (induction rule: cdcl_twl_stgy_restart.induct)
  subgoal for T U R S m n
    using rtranclp_cdcl_twl_stgy_twl_stgy_invs[of T U]
    by (auto simp: twl_restart_inv_def)
  subgoal for T R n U V W S m
    using cdcl_twl_restart_twl_stgy_invs[of U V]
    by (auto simp: twl_restart_inv_def rtranclp_cdcl_twl_subsumption_inp_twl_stgy_invs
        cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs
        rtranclp_cdcl_twl_subsumption_inp_twl_struct_invs
      intro: cdcl_twl_restart_twl_struct_invs rtranclp_cdcl_twl_stgy_twl_stgy_invs)
  subgoal for T S U R m n
    using cdcl_twl_restart_only_twl_stgy_invs[of T U]
    by (auto simp: twl_restart_inv_def)
  subgoal
    by auto
  done

lemma rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_restart_inv S\<close> and
    \<open>twl_stgy_invs (fst S)\<close> and
    \<open>twl_stgy_invs (fst (snd S))\<close> and
    \<open>twl_stgy_invs (fst (snd (snd S)))\<close>
  shows \<open>twl_stgy_invs (fst T) \<and> twl_stgy_invs (fst (snd T)) \<and> twl_stgy_invs (fst (snd (snd T)))\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_twl_stgy_invs[of T U]
      rtranclp_cdcl_twl_stgy_restart_twl_restart_inv[of S T]
    by (auto dest!: simp: twl_restart_inv_def)
  done

lemma cdcl_twl_stgy_restart_twl_stgy_restart_inv:
  \<open>cdcl_twl_stgy_restart S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_stgy_restart_inv S \<Longrightarrow>
  twl_stgy_restart_inv T\<close>
  using cdcl_twl_stgy_restart_twl_stgy_invs[of S T] unfolding twl_stgy_restart_inv_def twl_restart_inv_def
  by auto

lemma rtranclp_cdcl_twl_stgy_restart_twl_stgy_restart_inv:
  \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> twl_stgy_restart_inv S \<Longrightarrow>
  twl_stgy_restart_inv T\<close>
  using rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs[of S T] unfolding twl_stgy_restart_inv_def
  by auto

end



end