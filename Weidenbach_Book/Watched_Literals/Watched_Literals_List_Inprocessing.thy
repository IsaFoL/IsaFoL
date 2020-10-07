theory Watched_Literals_List_Inprocessing
imports Watched_Literals_List Watched_Literals_Algorithm_Reduce
begin

inductive cdcl_twl_subsumed_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
subsumed_II:
  \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, WS, Q)
     (M, fmdrop C' N, D, NE, UE, add_mset (mset (N \<propto> C')) NS, US, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>irred N C'\<close>  \<open>irred N C\<close> \<open>C \<noteq> C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subsumed_RR:
  \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, WS, Q)
     (M, fmdrop C' N, D, NE, UE, NS, add_mset (mset (N \<propto> C')) US, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>\<not>irred N C'\<close> \<open>\<not>irred N C\<close>\<open>C \<noteq> C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subsumed_IR:
  \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, WS, Q)
     (M, fmdrop C' N, D, NE, UE, NS, add_mset (mset (N \<propto> C')) US, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>irred N C\<close> \<open>irred N C'\<close> \<open>C \<noteq> C'\<close>\<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>

lemma convert_lits_l_drop:
  \<open>C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  (M, M') \<in> convert_lits_l (fmdrop C N) E \<longleftrightarrow> (M, M') \<in> convert_lits_l N E\<close>
  unfolding convert_lits_l_def list_rel_def in_pair_collect_simp
  apply (rule iffI; (rule list.rel_mono_strong, assumption))
  apply (auto simp: convert_lits_l_def list_rel_def p2rel_def convert_lit.simps
    cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail)
  done

find_theorems \<open>image_mset _ (_ - _)\<close>
lemma
  assumes \<open>cdcl_twl_subsumed_l S T\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_subsumed S' T'\<close>
proof -
  obtain M' N' U' D' NE' UE' NS' US' WS' Q' where
    S': \<open>S' = (M', N', U', D', NE', UE', NS', US', WS', Q')\<close>
    by (cases S')

  show ?thesis
    using assms(1)
  proof (cases rule: cdcl_twl_subsumed_l.cases)
    case (subsumed_II N C C' M D NE UE NS US WS Q)
    define N'' where \<open>N'' = (N' - {#twl_clause_of (N \<propto> C), twl_clause_of (N \<propto> C')#})\<close>
    let ?E = \<open>twl_clause_of (N \<propto> C)\<close>
    let ?E' = \<open>twl_clause_of (N \<propto> C')\<close>
    have \<open>(N \<propto> C, irred N C) \<in># init_clss_l N\<close>  and H: \<open>(N \<propto> C', irred N C') \<in># remove1_mset (N \<propto> C, irred N C)(init_clss_l N)\<close>
      using subsumed_II
      apply (auto dest!: multi_member_split simp: ran_m_def add_mset_eq_add_mset remove1_mset_add_mset_If
        split: if_splits)
      apply (metis prod.collapse)+
      done
    from multi_member_split[OF this(1)] multi_member_split[OF this(2)]
    have \<open>N' = N'' + {#twl_clause_of (N \<propto> C), twl_clause_of (N \<propto> C')#}\<close>
      using subsumed_II SS' unfolding N''_def
      by (auto simp: ran_m_def S' twl_st_l_def add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      using SS' subsumed_II H unfolding S'
      apply (auto simp: add_mset_eq_add_mset image_mset_Diff conj_disj_distribL
        conj_disj_distribR eq_commute[of \<open>twl_clause_of _\<close>] eq_commute[of \<open>remove1_mset _ _\<close>]
        S' convert_lits_l_drop learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev
        simp del: twl_clause_of.simps
        simp flip: twl_clause_of.simps
        dest!: intro!:  exI[of _ \<open>get_trail S'\<close>])
      apply (auto simp: init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
        cdcl_twl_subsumed_II_simp[where C = ?E and C' = ?E'])
      done
          find_theorems \<open>image_mset _(remove1_mset _ _ )\<close>
apply (rule exI[of _ M])
    obtain N'' E E' where
      \<open>N' = N'' + {#E, E'#}\<close>
      \<open>clause E = mset (N \<propto> C)\<close>
      \<open>clause E' = mset (N \<propto> C')\<close>and
      \<open>(M, M') \<in> convert_lits_l N (NE + UE)\<close> and
      \<open>N' = {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x))) . x \<in># init_clss_l N#}\<close> and
      \<open>U' = {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x))) . x \<in># learned_clss_l N#}\<close> and
      \<open>D' = D\<close> and
      \<open>NE' = NE\<close> and
      \<open>UE' = UE\<close> and
      \<open>NS' = NS\<close> and
      \<open>US' = US\<close> and
      \<open>WS' = {#}\<close> and
      \<open>Q' = Q\<close>
      using SS' subsumed_II unfolding S'
      apply (auto simp: twl_st_l_def add_mset_eq_add_mset image_mset_Diff conj_disj_distribL
        conj_disj_distribR eq_commute[of \<open>twl_clause_of _\<close>] eq_commute[of \<open>remove1_mset _ _\<close>]
        simp del: twl_clause_of.simps
        simp flip: twl_clause_of.simps
        dest!: )
        try0

        find_theorems \<open>_ \<and>  (_ \<or> _) \<longleftrightarrow> _ \<or> _\<close>
    then show ?thesis sorry
  next
    case (subsumed_RR N C C' M D NE UE NS US WS Q)
    then show ?thesis sorry
  next
    case (subsumed_IR N C C' M D NE UE NS US WS Q)
    then show ?thesis sorry
  qed
    oops
  apply (induction rule: cdcl_twl_subsumed_l.induct)
  subgoal for N C C' M D NE UE NS US WS Q
    apply (rule_tac x= \<open>(\<lambda>(M,_,U,D,NE,UE,NS,US,WS,Q). (M,_,U,D,NE,UE,add_mset (mset (N \<propto> C')) NS,US,{#},Q)) S'\<close> in exI)
    apply (auto simp: cdcl_twl_subsumed_II_simp twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop)
    apply (force simp:
      cdcl_twl_subsumed_II_simp twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
      cdcl_twl_subsumed.simps twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
      image_mset_remove1_mset_if convert_lits_l_drop mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
      image_mset_remove1_mset_if
      ran_m_def add_mset_eq_add_mset convert_lits_l_drop dest!: multi_member_split
      simp: mset_take_mset_drop_mset'
      intro: exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C)))\<close>]
      exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C')))\<close>])+
    done
  subgoal for N C C' M D NE UE NS US WS Q
    apply (rule_tac x= \<open>(\<lambda>(M,N0,U,D,NE,UE,NS,US,WS,Q). (M, N0,_, D,NE,UE,NS,add_mset (mset (N \<propto> C')) US,{#},Q)) S'\<close> in exI)
    apply (auto simp: cdcl_twl_subsumed_RR_simp twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop init_clss_l_fmdrop
      learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop_irrelev convert_lits_l_drop)
    apply (auto simp:  twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
      cdcl_twl_subsumed.simps twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
      learned_clss_l_l_fmdrop learned_clss_l_l_fmdrop init_clss_l_fmdrop
      learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop_irrelev
      image_mset_remove1_mset_if convert_lits_l_drop mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
      image_mset_remove1_mset_if
      ran_m_def add_mset_eq_add_mset convert_lits_l_drop dest!: multi_member_split
      simp: mset_take_mset_drop_mset' eq_commute [of \<open>TWL_Clause _ _\<close>]
      intro: exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C)))\<close>]
      exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C')))\<close>])
    apply (drule_tac exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C)))\<close>])
    apply (drule_tac exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C')))\<close>])
      apply auto
      apply (drule_tac exI[of _ \<open>TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C)))\<close>])
    done
    


    (*  |
 * subsumed_RR:
 *   \<open>cdcl_twl_subsumed_l (M, N, U + {#C, C'#}, D, NE, UE, NS, US, {#}, Q)
 *      (M, N, add_mset C U, D, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 *   if \<open>clause C \<subseteq># clause C'\<close> |
 * subsumed_IR:
 *   \<open>cdcl_twl_subsumed_l (M, add_mset C N, add_mset C' U, D, NE, UE, NS, US, {#}, Q)
 *      (M, add_mset C N, U, D, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 *   if \<open>clause C \<subseteq># clause C'\<close> *)
thm cdcl_twl_subsumed.intros
end