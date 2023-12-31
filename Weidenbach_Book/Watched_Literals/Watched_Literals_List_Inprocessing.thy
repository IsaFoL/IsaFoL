theory Watched_Literals_List_Inprocessing
imports Watched_Literals_List Watched_Literals_Algorithm_Reduce
begin

definition all_learned_lits_of_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause\<close> where
  \<open>all_learned_lits_of_l S' \<equiv> all_lits_of_mm (mset `# learned_clss_lf (get_clauses_l S') + get_unit_learned_clss_l S' +
  get_subsumed_learned_clauses_l S' + get_learned_clauses0_l S')\<close>
definition all_init_lits_of_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause\<close> where
  \<open>all_init_lits_of_l S' \<equiv> all_lits_of_mm (mset `# get_init_clss_l S' + get_unit_init_clauses_l S' +
  get_subsumed_init_clauses_l S' + get_init_clauses0_l S')\<close>

inductive cdcl_twl_subsumed_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
subsumed_II:
  \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C' N, D, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>irred N C'\<close>  \<open>irred N C\<close> \<open>C \<noteq> C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subsumed_RR:
    \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmdrop C' N, D, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> C')) US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>\<not>irred N C'\<close> \<open>\<not>irred N C\<close>\<open>C \<noteq> C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subsumed_IR:
    \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmdrop C' N, D, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> C')) US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>irred N C\<close> \<open>\<not>irred N C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> |
subsumed_RI:
    \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd C (N \<propto> C, True) (fmdrop C' N), D, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>\<not>irred N C\<close> \<open>irred N C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>
    \<open>\<not>tautology (mset (N \<propto> C))\<close>
    \<open>distinct_mset (mset (N \<propto> C))\<close>

lemma convert_lits_l_drop:
  \<open>C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  (M, M') \<in> convert_lits_l (fmdrop C N) E \<longleftrightarrow> (M, M') \<in> convert_lits_l N E\<close>
  unfolding convert_lits_l_def list_rel_def in_pair_collect_simp
  apply (rule iffI; (rule list.rel_mono_strong, assumption))
  apply (auto simp: convert_lits_l_def list_rel_def p2rel_def convert_lit.simps
    cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail)
  done

lemma convert_lits_l_update_sel:
  \<open>C \<in># dom_m N \<Longrightarrow> C' = N \<propto> C \<Longrightarrow>
  (M, M') \<in> convert_lits_l (fmupd C (C', b) N) E \<longleftrightarrow> (M, M') \<in> convert_lits_l N E\<close>
  unfolding convert_lits_l_def list_rel_def in_pair_collect_simp
  apply (rule iffI; (rule list.rel_mono_strong, assumption))
  apply (auto simp: convert_lits_l_def list_rel_def p2rel_def convert_lit.simps
    cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail)
  done

lemma learned_clss_l_mapsto_upd_in_irrelev: \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
  learned_clss_l (fmupd C  (C', True) N) = remove1_mset (N \<propto> C, irred N C) (learned_clss_l N)\<close>
  by (auto simp: ran_m_mapsto_upd_notin ran_m_mapsto_upd)

lemma init_clss_l_mapsto_upd_irrelev:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
   init_clss_l (fmupd C (C', True) N) = add_mset (C', True) ((init_clss_l N))\<close>
  by (auto simp: ran_m_mapsto_upd)

lemma cdcl_twl_subsumed_l_cdcl_twl_subsumed:
  assumes \<open>cdcl_twl_subsumed_l S T\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_subsumed S' T'\<close>
proof -
  obtain M' N' U' D' NE' UE' NS' US' WS' N0' U0' Q'  where
    S': \<open>S' = (M', N', U', D', NE', UE',NS', US', N0', U0', WS', Q')\<close>
    by (cases S')

  show ?thesis
    using assms(1)
  proof (cases rule: cdcl_twl_subsumed_l.cases)
    case (subsumed_II N C C' M D NE UE NEk UEk NS US N0 U0 Q)
    define N'' where \<open>N'' = (N' - {#twl_clause_of (N \<propto> C), twl_clause_of (N \<propto> C')#})\<close>
    let ?E = \<open>twl_clause_of (N \<propto> C)\<close>
    let ?E' = \<open>twl_clause_of (N \<propto> C')\<close>
    have \<open>(N \<propto> C, irred N C) \<in># init_clss_l N\<close>  and
      H: \<open>(N \<propto> C', irred N C') \<in># remove1_mset (N \<propto> C, irred N C)(init_clss_l N)\<close>
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
        intro!: cdcl_twl_subsumed_II_simp[where C = ?E and C' = ?E'])
      done
  next
    case (subsumed_RR N C C' M D NE UE NEk UEk NS US N0 U0 Q)
    define U'' where \<open>U'' = (U' - {#twl_clause_of (N \<propto> C), twl_clause_of (N \<propto> C')#})\<close>
    let ?E = \<open>twl_clause_of (N \<propto> C)\<close>
    let ?E' = \<open>twl_clause_of (N \<propto> C')\<close>
    have \<open>(N \<propto> C, irred N C) \<in># learned_clss_l N\<close>  and
      H: \<open>(N \<propto> C', irred N C') \<in># remove1_mset (N \<propto> C, irred N C)(learned_clss_l N)\<close>
      using subsumed_RR
      apply (auto dest!: multi_member_split simp: ran_m_def add_mset_eq_add_mset remove1_mset_add_mset_If
        split: if_splits)
      apply (metis prod.collapse)+
      done
    from multi_member_split[OF this(1)] multi_member_split[OF this(2)]
    have \<open>U' = U'' + {#twl_clause_of (N \<propto> C), twl_clause_of (N \<propto> C')#}\<close>
      using subsumed_RR SS' unfolding U''_def
      by (auto simp: ran_m_def S' twl_st_l_def add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      using SS' subsumed_RR H unfolding S'
      apply (auto simp: add_mset_eq_add_mset image_mset_Diff conj_disj_distribL
        conj_disj_distribR eq_commute[of \<open>twl_clause_of _\<close>] eq_commute[of \<open>remove1_mset _ _\<close>]
        S' convert_lits_l_drop learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset'
        simp del: twl_clause_of.simps
        simp flip: twl_clause_of.simps
        dest!: intro!:  exI[of _ \<open>get_trail S'\<close>])
      apply (auto simp: init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
        learned_clss_l_l_fmdrop
        cdcl_twl_subsumed_RR_simp[where C = ?E and C' = ?E'])
      done
  next
    case (subsumed_IR N C C' M D NE UE NEk UEk NS US N0 U0 Q)
    define U'' where \<open>U'' = (U' - {#twl_clause_of (N \<propto> C')#})\<close>
    define N'' where \<open>N'' = (N' - {#twl_clause_of (N \<propto> C)#})\<close>
    let ?E = \<open>twl_clause_of (N \<propto> C)\<close>
    let ?E' = \<open>twl_clause_of (N \<propto> C')\<close>
    have \<open>(N \<propto> C, irred N C) \<in># init_clss_l N\<close>  and
      H: \<open>(N \<propto> C', irred N C') \<in># (learned_clss_l N)\<close>
      using subsumed_IR
      apply (auto dest!: multi_member_split simp: ran_m_def add_mset_eq_add_mset remove1_mset_add_mset_If
        split: if_splits)
      apply (metis prod.collapse)+
      done
    from multi_member_split[OF this(1)] multi_member_split[OF this(2)]
    have \<open>U' = U'' + {#twl_clause_of (N \<propto> C')#}\<close> \<open>N' = N'' + {#twl_clause_of (N \<propto> C)#}\<close>
      using subsumed_IR SS' unfolding U''_def N''_def
      by (auto simp: ran_m_def S' twl_st_l_def add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      using SS' subsumed_IR H unfolding S'
      apply (auto simp: add_mset_eq_add_mset image_mset_Diff conj_disj_distribL
        conj_disj_distribR eq_commute[of \<open>twl_clause_of _\<close>] eq_commute[of \<open>remove1_mset _ _\<close>]
        S' convert_lits_l_drop learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset'
        simp del: twl_clause_of.simps
        simp flip: twl_clause_of.simps
        dest!: intro!:  exI[of _ \<open>get_trail S'\<close>])
      apply (auto simp: init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
        learned_clss_l_l_fmdrop
        cdcl_twl_subsumed_IR_simp[where C = ?E and C' = ?E'])
      done
  next
    case (subsumed_RI N C C' M D NE UE NEk UEk NS US N0 U0 Q)
    define U'' where \<open>U'' = (U' - {#twl_clause_of (N \<propto> C)#})\<close>
    define N'' where \<open>N'' = (N' - {#twl_clause_of (N \<propto> C')#})\<close>
    let ?E = \<open>twl_clause_of (N \<propto> C)\<close>
    let ?E' = \<open>twl_clause_of (N \<propto> C')\<close>
    have \<open>(N \<propto> C', irred N C') \<in># init_clss_l N\<close>  and
      H: \<open>(N \<propto> C, irred N C) \<in># (learned_clss_l N)\<close> and
      [simp,iff]: \<open>C \<in># remove1_mset C' (dom_m N)\<close> \<open>\<not> irred (fmdrop C' N) C\<close> \<open>C \<noteq> C'\<close>
      \<open>(N \<propto> C, False) \<in># learned_clss_l N\<close>
      using subsumed_RI
      apply (auto dest!: multi_member_split simp: ran_m_def add_mset_eq_add_mset remove1_mset_add_mset_If
        split: if_splits)
      apply (metis prod.collapse)+
      done
    from multi_member_split[OF this(1)] multi_member_split[OF this(2)]
    have \<open>U' = U'' + {#twl_clause_of (N \<propto> C)#}\<close> \<open>N' = N'' + {#twl_clause_of (N \<propto> C')#}\<close>
      using subsumed_RI SS' unfolding U''_def N''_def
      by (auto simp: ran_m_def S' twl_st_l_def add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      using SS' subsumed_RI H unfolding S'
      apply (auto simp: add_mset_eq_add_mset image_mset_Diff conj_disj_distribL
        conj_disj_distribR eq_commute[of \<open>twl_clause_of _\<close>] eq_commute[of \<open>remove1_mset _ _\<close>]
        S' convert_lits_l_drop learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>] convert_lits_l_update_sel
        twl_st_l_def mset_take_mset_drop_mset'
        simp del: twl_clause_of.simps
        simp flip: twl_clause_of.simps
        dest!: intro!:  exI[of _ \<open>get_trail S'\<close>])
      apply (auto simp: init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if
        eq_commute[of \<open>add_mset _ (add_mset _ _)\<close> \<open>image_mset _ _\<close>]
        twl_st_l_def mset_take_mset_drop_mset' learned_clss_l_l_fmdrop_irrelev init_clss_l_fmdrop
        learned_clss_l_l_fmdrop convert_lits_l_drop learned_clss_l_mapsto_upd_in_irrelev
        init_clss_l_mapsto_upd init_clss_l_mapsto_upd_irrelev
        intro!: cdcl_twl_subsumed_RI_simp[where C = ?E and C' = ?E'])
      done
  qed
qed

lemma cdcl_twl_subsumed_l_list_invs:
  \<open>cdcl_twl_subsumed_l S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  apply (induction rule: cdcl_twl_subsumed_l.induct)
 apply (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
   ran_m_mapsto_upd distinct_mset_remove1_All distinct_mset_dom
   ran_m_lf_fmdrop
   dest: in_diffD)
 apply (subst (asm) ran_m_mapsto_upd)
 apply (auto dest!: in_diffD simp: distinct_mset_remove1_All distinct_mset_dom
   ran_m_lf_fmdrop)
 done

inductive cdcl_twl_subresolution_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
twl_subresolution_II_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, True) N, None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close> 
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>irred N C'\<close> |
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop C' N, None, NE, UE, add_mset {#K#} NEk, UEk, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>irred N C'\<close> |
twl_subresolution_LL_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, False) N, None, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> C'))  US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
   (Propagated K 0 # M, fmdrop C' N, None, NE, UE, NEk, add_mset {#K#} UEk, NS,  add_mset (mset (N \<propto> C')) US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, False) N, None, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> C'))  US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
   (Propagated K 0 # M, fmdrop C' N, None, NE, UE, NEk, add_mset {#K#} UEk,  NS,  add_mset (mset (N \<propto> C')) US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, True) N, None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>irred N C'\<close> |
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop C' N, None, NE, UE, add_mset {#K#} NEk, UEk, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>irred N C'\<close>


lemma convert_lits_l_update_sel2:
  \<open>C \<in># dom_m N \<Longrightarrow> C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> 
  (M, M') \<in> convert_lits_l (fmupd C (C', b) N) E \<longleftrightarrow> (M, M') \<in> convert_lits_l N E\<close>
  unfolding convert_lits_l_def list_rel_def in_pair_collect_simp
  apply (rule iffI; (rule list.rel_mono_strong, assumption))
  apply (auto simp: convert_lits_l_def list_rel_def p2rel_def convert_lit.simps
    cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail)
  done

lemma twl_subresolution_II_nonunit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, add_mset E (remove1_mset C' N), U, None, NE, UE, add_mset (clause C') NS, US, N0, U0, {#}, Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>clause E = remdups_mset D'\<close> \<open>size (watched E) = 2\<close> \<open>struct_wf_twl_cls E\<close>
    \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>
    \<open>C \<in># N\<close>
    \<open>C' \<in># N\<close>
  using cdcl_twl_subresolution.twl_subresolution_II_nonunit[of C L D C' D' M E \<open>N - {#C, C'#}\<close> U] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_II_unit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, (remove1_mset C' N), U, None, add_mset {#K#} NE, UE, add_mset (clause C') NS, US,  N0, U0, {#}, add_mset (-K) Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C \<in># N\<close>
    \<open>C' \<in># N\<close>
  using cdcl_twl_subresolution.twl_subresolution_II_unit[of C L D C' D' M K \<open>N - {#C, C'#}\<close> U] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_LL_nonunit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, N, add_mset E (remove1_mset C' U), None, NE, UE, NS, add_mset (clause C') US, N0, U0, {#}, Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>clause E = remdups_mset D'\<close> \<open>size (watched E) = 2\<close> \<open>struct_wf_twl_cls E\<close>
    \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>
    \<open>C \<in># U\<close>
    \<open>C' \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_LL_nonunit[of C L D C' D' M E N \<open>U - {#C, C'#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_LL_unit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, (N), remove1_mset C' U, None, NE, add_mset {#K#} UE,
    NS, add_mset (clause C') US, N0, U0, {#}, add_mset (-K) Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C \<in># U\<close>
    \<open>C' \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_LL_unit[of C L D C' D' M K N \<open>U - {#C, C'#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_LI_nonunit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, N, add_mset E (remove1_mset C' U), None, NE, UE, NS, add_mset (clause C') US, N0, U0, {#}, Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>clause E = remdups_mset D'\<close> \<open>size (watched E) = 2\<close> \<open>struct_wf_twl_cls E\<close>
    \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>
    \<open>C \<in># N\<close>
    \<open>C' \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_LI_nonunit[of C L D C' D' M E \<open>N - {#C#}\<close> \<open>U - {#C'#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_LI_unit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, (N), remove1_mset C' U, None, NE, add_mset {#K#} UE,
    NS, add_mset (clause C') US, N0, U0, {#}, add_mset (-K) Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C \<in># N\<close>
    \<open>C' \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_LI_unit[of C L D C' D' M K \<open>N - {#C#}\<close> \<open>U - {#C'#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_IL_nonunit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, add_mset E (remove1_mset C' N), U, None, NE, UE, add_mset (clause C') NS, US, N0, U0, {#}, Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>clause E = remdups_mset D'\<close> \<open>size (watched E) = 2\<close> \<open>struct_wf_twl_cls E\<close>
    \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>
    \<open>C' \<in># N\<close>
    \<open>C \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_IL_nonunit[of C L D C' D' M E \<open>N - {#C'#}\<close> \<open>U - {#C#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma twl_subresolution_IL_unit_simps:
  \<open>cdcl_twl_subresolution S T\<close>
  if
    \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, remove1_mset C' N,  U, None, add_mset {#K#} NE, UE,
    add_mset (clause C') NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<in># N\<close>
    \<open>C \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_IL_unit[of C L D C' D' M K \<open>N - {#C'#}\<close> \<open>U - {#C#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma cdcl_twl_subresolution_l_cdcl_twl_subresolution:
  assumes \<open>cdcl_twl_subresolution_l S T\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_subresolution S' T'\<close>
proof -
  have tauto: \<open>\<forall>C\<in>#dom_m (get_clauses_l S). \<not>tautology (mset (get_clauses_l S \<propto> C))\<close>
    using list_invs unfolding twl_list_invs_def
    by (auto simp: dest!: multi_member_split)
  have H1: \<open>C \<in># dom_m N \<Longrightarrow>
    C' \<in># dom_m N \<Longrightarrow>
    mset (N \<propto> C) = add_mset L D \<Longrightarrow>
    mset (N \<propto> C') = add_mset (- L) D' \<Longrightarrow>
    D \<subseteq># D' \<Longrightarrow>
    \<forall>C\<in>#dom_m N. \<not> tautology (mset (N \<propto> C)) \<Longrightarrow> tautology (D + D') \<Longrightarrow> False\<close> for C C' L D N D'
   by (metis mset_subset_eqD tautology_add_mset tautology_minus tautology_union)
  from assms tauto show ?thesis
    apply -
    supply [simp] = convert_lits_l_update_sel2
    apply (induction rule: cdcl_twl_subresolution_l.induct)
    subgoal for C N C' L D D' M E NE UE NEk UEk NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = x in exI)
      apply auto
      apply (rule twl_subresolution_II_nonunit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>])
      apply (auto simp: init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        )
      done
    subgoal for C N C' L D D' M K NE UE NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>Propagated K {#K#} # x\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset)
      apply (rule twl_subresolution_II_unit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
          C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>])
      apply (auto simp: init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev; fail
        )+
      done
    subgoal for C N C' L D D' M E NE UE NS US N0 U0 Q
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>x\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
        intro!: twl_subresolution_LL_nonunit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
          init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
          init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
          learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev; fail
          )+
      done
    subgoal for C N C' L D D' M K NE UE NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>Propagated K {#K#} # x\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
        intro!: twl_subresolution_LL_unit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
          init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
          init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
          learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
          )
        done
    subgoal for C N C' L D D' M E NE UE NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>get_trail S'\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
        intro!: twl_subresolution_LI_nonunit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
          init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
          init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
          learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev; fail
          )+
        done
    subgoal for C N C' L D D' M K NE UE NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>Propagated K {#K#} # x\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
        intro!: twl_subresolution_LI_unit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
          init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
          init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
          learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
          )
        done
    subgoal for C N C' L D D' M E NE UE NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>get_trail S'\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
        intro!: twl_subresolution_IL_nonunit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
          init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
          init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
          learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev; fail
        )+
        done
    subgoal for C N C' L D D' M K NE UE NS US N0 U0 Q
      using H1[of C N C' L D D']
      apply (auto simp: twl_st_l_def)
      apply (rule_tac x = \<open>Propagated K {#K#} # x\<close> in exI)
      apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
        intro!: twl_subresolution_IL_unit_simps[where
          C' = \<open>(TWL_Clause (mset (watched_l (N \<propto> C'))) (mset (unwatched_l (N \<propto> C'))))\<close> and
        C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
          init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
          init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
          learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
          )
        done
      done
qed

inductive cdcl_twl_unitres_true_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_unitres_true_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C N, None, add_mset (mset (N \<propto> C)) NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)\<close>
  if \<open>L \<in># mset (N \<propto> C)\<close> \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close>
    \<open>C \<in># dom_m N\<close> \<open>irred N C\<close>
    \<open>C \<notin> set (get_all_mark_of_propagated M)\<close> |
  \<open>cdcl_twl_unitres_true_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmdrop C N, None, NE, add_mset (mset (N \<propto> C)) UE, NEk, UEk, NS, US, N0, U0, {#}, Q)\<close>
  if \<open>L \<in># mset (N \<propto> C)\<close> \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close>
    \<open>C \<in># dom_m N\<close> \<open>\<not>irred N C\<close>
    \<open>C \<notin> set (get_all_mark_of_propagated M)\<close>

lemma cdcl_twl_unitres_true_intro1:
  \<open>cdcl_twl_unitres_true S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, remove1_mset C N, U, None, add_mset (clause C) NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>L \<in># clause C\<close> \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close> \<open>C \<in># N\<close>
  using cdcl_twl_unitres_true.intros(1)[of L C M \<open>N - {#C#}\<close> U] that
  by auto

lemma cdcl_twl_unitres_true_intro2:
  \<open>cdcl_twl_unitres_true S T\<close>
  if  \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, N, remove1_mset C U, None, NE, add_mset (clause C) UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>L \<in># clause C\<close> \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close> \<open>C \<in># U\<close>
  using cdcl_twl_unitres_true.intros(2)[of L C M N \<open>U - {#C#}\<close>] that
  by auto

lemma cdcl_twl_unitres_true_l_cdcl_twl_unitres_true:
  assumes \<open>cdcl_twl_unitres_true_l S T\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_unitres_true S' T'\<close>
  using assms
  apply (induction rule: cdcl_twl_unitres_true_l.induct)
  subgoal for L N C M NE UE NS US Q
    apply (auto simp: twl_st_l_def)
    apply (rule_tac x=x in exI)
    apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
      intro!: cdcl_twl_unitres_true_intro1[where
      C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
      )
    done
  subgoal for L N C M NE UE NS US N0 U0 Q
    apply (auto simp: twl_st_l_def)
    apply (rule_tac x=x in exI)
    apply (auto simp: convert_lit.simps convert_lits_l_drop convert_lits_l_add_mset
      intro!: cdcl_twl_unitres_true_intro2[where
      C = \<open>(TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C))))\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
      )
    done
  done

lemma cdcl_twl_subresolution_l_list_invs:
  \<open>cdcl_twl_subresolution_l S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  by (induction rule: cdcl_twl_subresolution_l.induct)
   (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
     ran_m_mapsto_upd ran_m_def add_mset_eq_add_mset tautology_add_mset
    dest: in_diffD dest!: multi_member_split)

lemma cdcl_twl_unitres_True_l_list_invs:
  \<open>cdcl_twl_unitres_true_l S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  by (induction rule: cdcl_twl_unitres_true_l.induct)
   (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
    dest: in_diffD)

inductive cdcl_twl_unitres_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd D (E, irred N D) N, None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> D)) NS, US, N0, U0, {#}, Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = C +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NEk + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close>
    \<open>struct_wf_twl_cls (twl_clause_of E)\<close>
    \<open>Multiset.Ball (mset E) (undefined_lit M)\<close>
    \<open>mset E = C\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N D\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop D N, None, NE, UE, add_mset {#K#} NEk, UEk, add_mset (mset (N \<propto> D)) NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = {#K#} +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NEk + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N D\<close>
    \<open>undefined_lit M K\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmupd D (E, irred N D) N, None, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = C +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NEk + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close>
    \<open>struct_wf_twl_cls (twl_clause_of E)\<close>
    \<open>Multiset.Ball (mset E) (undefined_lit M)\<close>
    \<open>mset E = C\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N D\<close>
    \<open>atms_of (mset E) \<subseteq> atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE \<union> atms_of_mm NEk \<union>
       atms_of_mm NS \<union> atms_of_mm N0\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop D N, None, NE, UE, NEk, add_mset {#K#} UEk, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = {#K#} +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NEk + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N D\<close>
    \<open>undefined_lit M K\<close>
    \<open>atm_of K \<in> atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE \<union> atms_of_mm NEk \<union>
       atms_of_mm NS \<union> atms_of_mm N0\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmdrop D N, Some {#}, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> D)) US, N0, add_mset {#} U0, {#}, {#})\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>(mset `# init_clss_lf N + NE + NEk + NS + N0) \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
    \<open>\<not>irred N D\<close>
    \<open>count_decided M = 0\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmdrop D N, Some {#}, NE, UE, NEk, UEk, add_mset (mset (N \<propto> D)) NS, US, add_mset {#} N0, U0, {#}, {#})\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>(mset `# init_clss_lf N + NE + NEk + NS + N0) \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
    \<open>irred N D\<close>
    \<open>count_decided M = 0\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close>

lemma cdcl_twl_unitres_I1:
  \<open>cdcl_twl_unitres S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, add_mset E (remove1_mset D N), U, None, NE, UE, add_mset (clause D)  NS, US, N0, U0, {#}, Q)\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<in># N\<close>
    \<open>clause D = C+C'\<close>
    \<open>(clauses N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close>
    \<open>struct_wf_twl_cls E\<close>
    \<open>Multiset.Ball (clause E) (undefined_lit M)\<close>
    \<open>clause E = C\<close>
  using that cdcl_twl_unitres.intros(1)[of M D C C' \<open>N - {#D#}\<close> NE NS N0 E U UE US U0 Q]
  by (auto dest!: multi_member_split)

lemma cdcl_twl_unitres_I2:
  \<open>cdcl_twl_unitres S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, (remove1_mset D N), U, None, add_mset {#K#} NE, UE, add_mset (clause D)  NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<in># N\<close>
    \<open>clause D = {#K#}+C'\<close>
    \<open>(clauses N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>undefined_lit M K\<close>
  using that cdcl_twl_unitres.intros(2)[of M D \<open>{#K#}\<close> C' \<open>N - {#D#}\<close> NE NS N0 K U UE US U0 Q]
  by (auto dest!: multi_member_split)

lemma cdcl_twl_unitres_I3:
  \<open>cdcl_twl_unitres S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, N, add_mset E (remove1_mset D U), None, NE, UE, NS, add_mset (clause D) US, N0, U0, {#}, Q)\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<in># U\<close>
    \<open>clause D = C+C'\<close>
    \<open>(clauses N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close>
    \<open>struct_wf_twl_cls E\<close>
    \<open>Multiset.Ball (clause E) (undefined_lit M)\<close>
    \<open>clause E = C\<close>
    \<open>atms_of C \<subseteq> atms_of_ms (clause ` set_mset N) \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0\<close>
  using that cdcl_twl_unitres.intros(3)[of M D C C' N NE NS N0 E \<open>U - {#D#}\<close> UE US U0 Q]
  by (auto dest!: multi_member_split)

lemma cdcl_twl_unitres_I4:
  \<open>cdcl_twl_unitres S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, N, remove1_mset D U, None, NE, add_mset {#K#} UE, NS, add_mset (clause D) US, N0, U0, {#}, add_mset (-K) Q)\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<in># U\<close>
    \<open>clause D = {#K#}+C'\<close>
    \<open>(clauses N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>undefined_lit M K\<close>
    \<open>atm_of K \<in> atms_of_ms (clause ` set_mset N) \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0\<close>
  using that cdcl_twl_unitres.intros(4)[of M D \<open>{#K#}\<close> C' N NE NS N0 K \<open>U - {#D#}\<close> UE US U0 Q]
  by (auto dest!: multi_member_split)

lemma cdcl_twl_unitres_I5:
  \<open>cdcl_twl_unitres S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, N, remove1_mset D U, Some {#}, NE, UE, NS, add_mset (clause D) US, N0, add_mset {#} U0, {#}, {#})\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<in># U\<close>
    \<open>(clauses N + NE + NS + N0) \<Turnstile>psm mset_set (CNot (clause D))\<close>
  using that cdcl_twl_unitres.intros(5)[of M N NE NS N0 D \<open>remove1_mset D U\<close> UE US U0 Q]
  by (auto dest!: multi_member_split)

lemma cdcl_twl_unitres_I6:
  \<open>cdcl_twl_unitres S T\<close>
  if \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    \<open>T = (M, remove1_mset D N, U, Some {#}, NE, UE, add_mset (clause D) NS, US, add_mset {#} N0, U0, {#}, {#})\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<in># N\<close>
    \<open>(clauses (add_mset D N) + NE + NS + N0) \<Turnstile>psm mset_set (CNot (clause D))\<close>
  using that cdcl_twl_unitres.intros(6)[of M D \<open>remove1_mset D N\<close> NE NS N0 U UE US U0 Q]
  by (auto dest!: multi_member_split)

lemma cdcl_twl_unitres_l_cdcl_twl_unitres:
  assumes \<open>cdcl_twl_unitres_l S T\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_unitres S' T'\<close>
  using assms
  apply (induction rule: cdcl_twl_unitres_l.induct)
  subgoal for D N M C C' NE NEk NS N0 E UE UEk US U0 Q
    apply (auto simp: twl_st_l_def)[]
    apply (rule_tac x=x in exI)
    apply (auto simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I1[where E= \<open>twl_clause_of E\<close> and D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev Un_assoc
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)[]
    done
  subgoal for D N M K C' NE NS N0 UE US U0 Q
    apply (auto simp: twl_st_l_def)[]
    apply (rule_tac x= \<open>Propagated K {#K#} # x\<close> in exI)
    apply (auto simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I2[where K=K and D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev Un_assoc
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel convert_lits_l_add_mset
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd convert_lit.intros(3)
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)[]
    done
  subgoal for D N M C C' NE NEk NS N0 E UE UEk US U0 Q
    apply (auto simp: twl_st_l_def)[]
    apply (rule_tac x=x in exI)
    apply (auto 5 3 simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I3[where E= \<open>twl_clause_of E\<close> and D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev Un_assoc
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd image_image
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)[]
    done
  subgoal for D N M K C' NE NS N0 UE US U0 Q
    apply (auto simp: twl_st_l_def; rule_tac x= \<open>Propagated K {#K#} # x\<close> in exI)
    apply (auto simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I4[where K=K and D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev image_image
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop Un_assoc
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel convert_lits_l_add_mset
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd convert_lit.intros(3)
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)
    done
  subgoal for D N NE NS N0 M UE US U0 Q
    by (auto simp: twl_st_l_def; rule_tac x= \<open>x\<close> in exI)
     (auto simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I5[where D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev image_image
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop Un_assoc
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel convert_lits_l_add_mset
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd convert_lit.intros(3)
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)
    subgoal for D N NE NS N0 M UE US U0 Q
      by (auto simp: twl_st_l_def; rule_tac x= \<open>x\<close> in exI)
       (auto simp: twl_st_l_def
        intro!: cdcl_twl_unitres_I6[where D = \<open>twl_clause_of (N \<propto> D)\<close>]
        simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
        learned_clss_l_mapsto_upd_irrel
        mset_take_mset_drop_mset'
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev image_image
        learned_clss_l_mapsto_upd_irrel convert_lits_l_drop Un_assoc
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
        init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel convert_lits_l_add_mset
        learned_clss_l_fmupd_if learned_clss_l_mapsto_upd convert_lit.intros(3)
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)
  done

definition simplify_clause_with_unit :: \<open>nat \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> (bool \<times> bool \<times> 'v clauses_l) nres\<close> where
  \<open>simplify_clause_with_unit = (\<lambda>C M N. do {
  SPEC(\<lambda>(unc, b, N'). fmdrop C N = fmdrop C N' \<and> mset (N' \<propto> C) \<subseteq># mset (N \<propto> C) \<and> C \<in># dom_m N' \<and>
     (\<not>b \<longrightarrow> (\<forall>L \<in># mset (N' \<propto> C). undefined_lit M L)) \<and>
     (\<forall>L \<in># mset (N \<propto> C) - mset (N' \<propto> C). defined_lit M L) \<and>
     (irred N C = irred N' C) \<and>
     (b \<longleftrightarrow> (\<exists>L. L \<in># mset (N \<propto> C) \<and> L \<in> lits_of_l M)) \<and>
     (unc \<longrightarrow> (N = N' \<and> \<not>b)))
  })\<close>

definition simplify_clause_with_unit_st_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>simplify_clause_with_unit_st_pre = (\<lambda>C S.
  C \<in># dom_m (get_clauses_l S) \<and> count_decided (get_trail_l S) = 0 \<and> get_conflict_l S = None \<and> clauses_to_update_l S = {#} \<and>
  twl_list_invs S \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
  (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T)))
)\<close>

definition simplify_clause_with_unit_st :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>simplify_clause_with_unit_st = (\<lambda>C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
    ASSERT(simplify_clause_with_unit_st_pre C  (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None \<and> WS = {#} \<and> no_dup M \<and> C \<noteq> 0);
    let S = (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q);
    if False
    then RETURN (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
    else do {
      let E = mset (N\<^sub>0 \<propto> C);
      let irr = irred N\<^sub>0 C;
      (unc, b, N) \<leftarrow> simplify_clause_with_unit C M N\<^sub>0;
      ASSERT(fmdrop C N = fmdrop C N\<^sub>0 \<and> irred N C = irred N\<^sub>0 C \<and> mset (N \<propto> C) \<subseteq># mset (N\<^sub>0 \<propto> C) \<and>
        C \<in># dom_m N);
      if unc then do {
        ASSERT (N = N\<^sub>0);
        RETURN (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
      }
      else if b then do {
        let T = (M, fmdrop C N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NEk, UEk, NS, US, N0, U0, WS, Q);
          ASSERT (set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S));
          ASSERT (set_mset (all_learned_lits_of_l T) = set_mset (all_learned_lits_of_l S));
        RETURN T
      }
      else if size (N \<propto> C) = 1
      then do {
        let L = ((N \<propto> C) ! 0);
        let T = (Propagated L 0 # M, fmdrop C N, D, NE, UE, (if irr then add_mset {#L#} else id) NEk,
            (if \<not>irr then add_mset {#L#} else id)UEk, (if irr then add_mset E else id) NS,
            (if \<not>irr then add_mset E else id)US, N0, U0, WS, add_mset (-L) Q);
          ASSERT (set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S));
          ASSERT (set_mset (all_learned_lits_of_l T) = set_mset (all_learned_lits_of_l S));
          ASSERT (undefined_lit M L \<and> L \<in># all_init_lits_of_l S);
        RETURN T}
      else if size (N \<propto> C) = 0
      then do {
          let T = (M, fmdrop C N, Some {#}, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, WS, {#});
          ASSERT (set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S));
          ASSERT (set_mset (all_learned_lits_of_l T) = set_mset (all_learned_lits_of_l S));
          RETURN T
      }
      else do {
          let T = (M, N, D, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, WS, Q);
            ASSERT (set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S));
            ASSERT (set_mset (all_learned_lits_of_l T) = set_mset (all_learned_lits_of_l S));
            RETURN T
      }
    }
  })\<close>

(*TODO Move*)
lemma true_clss_clss_def_more_atms:
  \<open>N \<Turnstile>ps N' \<longleftrightarrow> (\<forall>I. total_over_m I (N \<union> N' \<union> N'') \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile>s N')\<close>
  (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof (rule iffI)
  assume ?A
  then show ?B
    by (simp add: true_clss_clss_def)
next
  assume ?B
  show ?A
    unfolding true_clss_clss_def
  proof (intro allI impI)
    fix I
    assume tot: \<open>total_over_m I (N \<union> N')\<close> and
      cons: \<open>consistent_interp I\<close> and
      IN: \<open>I \<Turnstile>s N\<close>
    let ?I = \<open>I \<union> Pos ` {A. A \<in> atms_of_ms N'' \<and> A \<notin> atm_of ` I}\<close>
    have \<open>total_over_m ?I (N \<union> N' \<union> N'')\<close>
      using tot atms_of_s_def by (fastforce simp: total_over_m_def total_over_set_def)
    moreover have \<open>consistent_interp ?I\<close>
      using cons unfolding consistent_interp_def
      by (force simp: uminus_lit_swap)
    moreover have \<open>?I \<Turnstile>s N\<close>
      using IN by auto
    ultimately have \<open>?I \<Turnstile>s N'\<close>
      using \<open>?B\<close> by blast
    then show \<open>I \<Turnstile>s N'\<close>
      by (smt atms_of_ms_mono atms_of_s_def imageE literal.sel(1) mem_Collect_eq
        notin_vars_union_true_clss_true_clss subsetD sup_ge2 tot total_over_m_alt_def)
  qed
qed

(*TODO Move*)
lemma true_clss_clss_def_iff_negation_in_model:
  \<open>A \<Turnstile>ps CNot C' \<longleftrightarrow> (\<forall>L \<in># C'. A \<Turnstile>ps {{#-L#}})\<close>
  apply (rule iffI)
  subgoal
    by (simp add: true_clss_clss_in_imp_true_clss_cls)
  subgoal
    apply (subst (asm)true_clss_clss_def_more_atms[of _ _ \<open>{C'}\<close>])
    apply (auto simp: true_clss_clss_def true_clss_def_iff_negation_in_model
      dest!: multi_member_split)
    done
  done

lemma
  fixes M :: \<open>('v, nat) ann_lit list\<close> and N NE UE NS US N0 U0 Q NEk UEk
  defines \<open>S \<equiv> (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)\<close>
  assumes
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close> and
    dec: \<open>count_decided (get_trail_l S) = 0\<close> and
    false: \<open>\<forall>L \<in># C'. \<not>undefined_lit (get_trail_l S) L\<close>
      \<open>\<forall>L \<in># C'. L \<notin> lits_of_l (get_trail_l S)\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  shows cdcl_twl_unitres_l_intros2':
      \<open>irred N D \<Longrightarrow> undefined_lit M K \<Longrightarrow> mset (N \<propto> D) = {#K#} +C' \<Longrightarrow>
    cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
       (Propagated K 0 # M, fmdrop D N, None, NE, UE, add_mset {#K#} NEk, UEk,  add_mset (mset (N \<propto> D))  NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
       (is \<open>?A \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?B\<close>) and
    cdcl_twl_unitres_l_intros4':
    \<open>\<not>irred N D \<Longrightarrow> undefined_lit M K \<Longrightarrow> mset (N \<propto> D) = {#K#} +C' \<Longrightarrow> 
    cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop D N, None, NE, UE, NEk, add_mset {#K#} UEk, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, add_mset (-K) Q)\<close>
    (is \<open>?A' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?B'\<close>) and
    cdcl_twl_unitres_false_entailed:
       \<open>(mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S + get_subsumed_init_clauses_l S + get_init_clauses0_l S) \<Turnstile>psm mset_set (CNot C')\<close> and
    cdcl_twl_unitres_l_intros5':
      \<open>\<not>irred N D \<Longrightarrow> mset (N \<propto> D) = C' \<Longrightarrow>
      cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
         (M, fmdrop D N, Some {#}, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> D)) US, N0,
           add_mset {#} U0, {#}, {#})\<close>
       (is \<open>?E \<Longrightarrow> _ \<Longrightarrow> ?F\<close>)  and
  cdcl_twl_unitres_l_intros6':
    \<open>irred N D \<Longrightarrow> mset (N \<propto> D) = C' \<Longrightarrow>
    cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, fmdrop D N, Some {#}, NE, UE, NEk, UEk, add_mset (mset (N \<propto> D)) NS, US, add_mset {#} N0,
    U0, {#}, {#})\<close>
    (is \<open>?E' \<Longrightarrow> _ \<Longrightarrow> ?F'\<close>) and
  cdcl_twl_unitres_l_intros1':
    \<open>irred N D \<Longrightarrow> mset (N \<propto> D) = mset C +C' \<Longrightarrow> length C \<ge> 2 \<Longrightarrow> \<not>tautology (mset (N \<propto> D)) \<Longrightarrow>
    \<forall>L\<in>set C. undefined_lit M L \<Longrightarrow> N' = fmupd D (C, irred N D) N \<Longrightarrow>
      cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
        (M, N', None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> D)) NS, US, N0, U0, {#}, Q)\<close>
    (is \<open>?G \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _  \<Longrightarrow> _ \<Longrightarrow> ?H\<close>) and
  cdcl_twl_unitres_l_intros3':
    \<open>\<not>irred N D \<Longrightarrow> mset (N \<propto> D) = mset C +C' \<Longrightarrow> length C \<ge> 2 \<Longrightarrow> \<not>tautology (mset (N \<propto> D)) \<Longrightarrow>
    \<forall>L\<in>set C. undefined_lit M L \<Longrightarrow> N' = fmupd D (C, irred N D) N \<Longrightarrow>
    cdcl_twl_unitres_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (M, N', None, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, Q)\<close>
    (is \<open>?G' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?H'\<close>)
proof -
  have \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ((state\<^sub>W_of T)))
    (get_all_ann_decomposition (trail ((state\<^sub>W_of T))))\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of T)\<close> and
    tauto: \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of T). \<not> tautology s\<close> and
    nd: \<open>no_dup (trail (state_of (pstate\<^sub>W_of T)))\<close>
    using st_invs unfolding twl_struct_invs_def unfolding pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def state\<^sub>W_of_def pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by fast+
  moreover have H: \<open>(\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m b \<and> snd a} \<union> (set_mset d \<union> set_mset d') \<union> f \<union> h \<union> U\<Turnstile>ps
       unmark_l aa \<Longrightarrow>
       (a, aa) \<in> convert_lits_l b (d' + e) \<Longrightarrow>
    (\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m b \<and> snd a} \<union> (set_mset d \<union> set_mset d') \<union> f \<union> h \<Turnstile>ps U \<Longrightarrow>
       - L \<in> lits_of_l a \<Longrightarrow>
    (\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m b \<and> snd a} \<union> (set_mset d \<union> set_mset d') \<union> f \<union> h \<Turnstile>p {#- L#}\<close>
    for aa :: \<open>('v, 'v clause) ann_lits\<close> and a :: \<open>('v, nat) ann_lit list\<close> and b d e f L U h d'
    by (smt in_unmark_l_in_lits_of_l_iff list_of_l_convert_lits_l
      true_clss_clss_in_imp_true_clss_cls true_clss_clss_left_right
      true_clss_clss_union_and)
  moreover have false: \<open>\<forall>L \<in># C'. -L \<in> lits_of_l (get_trail_l S)\<close>
    using false nd by (auto dest!: multi_member_split
      simp: Decided_Propagated_in_iff_in_lits_of_l)
  ultimately show ent2: \<open>(mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S + get_subsumed_init_clauses_l S + get_init_clauses0_l S) \<Turnstile>psm mset_set (CNot C')\<close>
    using dec ST false ent
    by (cases S; cases T)
     (auto simp: twl_st_l_def all_decomposition_implies_def clauses_def
      get_all_ann_decomposition_count_decided0 image_image mset_take_mset_drop_mset'
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def true_clss_clss_def_iff_negation_in_model
      dest!: multi_member_split)
  moreover {
    have \<open>N \<propto> D \<in># init_clss_lf N \<or> N \<propto> D \<in># learned_clss_lf N\<close>
      using assms(1,2) by (auto simp: ran_m_def)
    then have \<open>atms_of (mset (N \<propto> D)) \<subseteq> atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE \<union> atms_of_mm NEk \<union> atms_of_mm NS \<union> atms_of_mm N0\<close>
      using alien assms(1) ST
      by (fastforce simp: twl_st_l_def clauses_def mset_take_mset_drop_mset' image_image
        cdcl\<^sub>W_restart_mset.no_strange_atm_def conj_disj_distribR Collect_disj_eq Collect_conv_if
        dest!: multi_member_split[of _ \<open>ran_m N\<close>])
   } note H = this
   ultimately show \<open>?A \<Longrightarrow>  ?B\<close> \<open>?A' \<Longrightarrow> undefined_lit M K \<Longrightarrow> ?B'\<close>
      if \<open>mset (N \<propto> D) = {#K#} + C'\<close> \<open>undefined_lit M K\<close>
    using assms cdcl_twl_unitres_l.intros(2)[of D N M K C' NE NEk NS N0 UE UEk US U0 Q]
      cdcl_twl_unitres_l.intros(4)[of D N M K C' NE NEk NS N0 UE UEk US U0 Q] that
    by (auto simp: Un_assoc)

  show ?F if \<open>?E\<close> \<open>mset (N \<propto> D) = C'\<close>
  proof -
    have \<open>mset `# init_clss_lf N + NE + NEk + NS + N0 \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
      using ent2 that assms by (auto simp: Un_assoc)
    then show ?thesis
      using cdcl_twl_unitres_l.intros(5)[of D N NE NEk NS N0 M UE UEk US U0 Q] assms that
      by (auto simp: Un_assoc)
  qed

  show ?F' if \<open>?E'\<close> \<open>mset (N \<propto> D) = C'\<close>
  proof -
    have \<open>mset `# init_clss_lf N + NE + NEk + NS + N0 \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
      using ent2 that assms by (auto simp: Un_assoc)
    then show ?thesis
      using cdcl_twl_unitres_l.intros(6)[of D N NE NEk NS N0 M UE UEk US U0 Q] assms that
      by auto
  qed
  show ?H if ?G \<open>mset (N \<propto> D) = mset C +C'\<close> \<open>length C \<ge> 2\<close> \<open>\<forall>L\<in>set C. undefined_lit M L\<close>
    \<open>\<not>tautology (mset (N \<propto> D))\<close> \<open>N' = fmupd D (C, irred N D) N\<close>
  proof -
    have dist_C: \<open>distinct_mset (mset (N \<propto> D))\<close>
      using that dist ST assms(2)
      by (auto simp: twl_st_l_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def ran_m_def
          S_def mset_take_mset_drop_mset'
        dest!: multi_member_split)
    moreover have \<open>struct_wf_twl_cls (twl_clause_of C)\<close> \<open>distinct C\<close>
      using that distinct_mset_mono[of \<open>mset C\<close> \<open>mset (N \<propto> D)\<close>] dist_C
      by (auto simp: twl_st_l_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        mset_take_mset_drop_mset')
    moreover have \<open>\<not>tautology (mset C)\<close>
      using not_tautology_mono[of \<open>mset C\<close> \<open>mset C + C'\<close>] that assms by auto
    ultimately show ?thesis
      using cdcl_twl_unitres_l.intros(1)[of D N M \<open>mset C\<close> C' NE NEk NS N0 C UE UEk US U0] assms that ent2
      by (auto simp: Un_assoc)
  qed
  show ?H' if ?G' \<open>mset (N \<propto> D) = mset C +C'\<close> \<open>length C \<ge> 2\<close> \<open>\<forall>L\<in>set C. undefined_lit M L\<close>
    \<open>\<not>tautology (mset (N \<propto> D))\<close> \<open>N' = fmupd D (C, irred N D) N\<close>
  proof -
    have dist_C: \<open>distinct_mset (mset (N \<propto> D))\<close>
      using that dist ST assms(2)
      by (auto simp: twl_st_l_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def ran_m_def
          S_def mset_take_mset_drop_mset'
        dest!: multi_member_split)
    moreover have \<open>struct_wf_twl_cls (twl_clause_of C)\<close> \<open>distinct C\<close>
      using that distinct_mset_mono[of \<open>mset C\<close> \<open>mset (N \<propto> D)\<close>] dist_C
      by (auto simp: twl_st_l_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        mset_take_mset_drop_mset')
    moreover have \<open>\<not>tautology (mset C)\<close>
      using not_tautology_mono[of \<open>mset C\<close> \<open>mset C + C'\<close>] that assms by auto
    ultimately show ?thesis
      using cdcl_twl_unitres_l.intros(3)[of D N M \<open>mset C\<close> C' NE NEk NS N0 C UE UEk US U0] assms that ent2 H
      by (auto simp: Un_assoc)
  qed
qed


lemma fmdrop_eq_update_eq: \<open>fmdrop C aa = fmdrop C bh \<Longrightarrow> C \<in># dom_m bh \<Longrightarrow>
  bh = fmupd C (bh \<propto> C, irred bh C) aa\<close>
  apply (subst (asm) fmlookup_inject[symmetric])
  apply (subst fmlookup_inject[symmetric])
  apply (intro ext)
  apply auto[]
  by (metis fmlookup_drop)

lemma fmdrop_eq_update_eq2: \<open>fmdrop C aa = fmdrop C bh \<Longrightarrow> C \<in># dom_m bh \<Longrightarrow> b = irred bh C \<Longrightarrow>
  bh = fmupd C (bh \<propto> C, b) aa\<close>
  using fmdrop_eq_update_eq by fast

lemma twl_st_l_struct_invs_distinct:
  assumes 
    ST: \<open>(S, T) \<in> twl_st_l b\<close> and
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close> and
    invs: \<open>twl_struct_invs T\<close>
  shows \<open>distinct (get_clauses_l S \<propto> C)\<close>
proof -
  have \<open>(\<forall>C \<in># get_clauses T. struct_wf_twl_cls C)\<close>
    using invs unfolding twl_struct_invs_def by (cases T) (auto simp: twl_st_inv.simps)
  moreover have \<open>twl_clause_of (get_clauses_l S \<propto> C) \<in># (get_clauses T)\<close>
    using ST C by (cases S; cases T) (auto simp: twl_st_l_def)
  ultimately show ?thesis
    by (auto dest!: multi_member_split simp: mset_take_mset_drop_mset')
qed

lemma list_length_2_isabelle_come_on:
  \<open>length C \<noteq> Suc 0 \<Longrightarrow> C \<noteq> [] \<Longrightarrow> length C \<ge> 2\<close>
  by (cases C; cases \<open>tl C\<close>) auto

lemma in_all_lits_of_mm_init_clss_l_single_out:
  \<open>xa \<in># all_lits_of_m (mset (aa \<propto> C)) \<Longrightarrow>
  C \<in># dom_m aa \<Longrightarrow> irred aa C \<Longrightarrow> xa \<in># all_lits_of_mm {#mset (fst x). x \<in># init_clss_l aa#}\<close> and
  in_all_lits_of_mm_learned_clss_l_single_out:
  \<open>xa \<in># all_lits_of_m (mset (aa \<propto> C)) \<Longrightarrow>
  C \<in># dom_m aa \<Longrightarrow> \<not>irred aa C \<Longrightarrow> xa \<in># all_lits_of_mm {#mset (fst x). x \<in># learned_clss_l aa#}\<close>
  by (auto simp: ran_m_def all_lits_of_mm_add_mset dest!: multi_member_split)

(*TODO simp: twl_st_l*)
lemma pget_all_learned_clss_get_all_learned_clss_l:
 \<open>(S, x) \<in> twl_st_l b \<Longrightarrow>
  pget_all_learned_clss (pstate\<^sub>W_of x) = get_all_learned_clss_l S\<close>
  by (cases x; cases S)
   (auto simp: get_learned_clss_l_def twl_st_l_def mset_take_mset_drop_mset')
lemma pget_all_init_clss_get_all_init_clss_l:
 \<open>(S, x) \<in> twl_st_l b \<Longrightarrow>
  pget_all_init_clss (pstate\<^sub>W_of x) = get_all_init_clss_l S\<close>
  by (cases x; cases S)
   (auto simp: get_init_clss_l_def twl_st_l_def mset_take_mset_drop_mset')

lemma simplify_clause_with_unit_st_spec:
  assumes \<open>simplify_clause_with_unit_st_pre C S\<close>
  shows \<open>simplify_clause_with_unit_st C S \<le> \<Down>Id (SPEC(\<lambda>T.
      (S = T \<or> cdcl_twl_unitres_l S T \<or> cdcl_twl_unitres_true_l S T) \<and>
    (set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq>
       set (get_all_mark_of_propagated (get_trail_l S)) \<union> {0}) \<and>
      (dom_m (get_clauses_l T) = dom_m (get_clauses_l S) \<or>
           dom_m (get_clauses_l T) = remove1_mset C (dom_m (get_clauses_l S))) \<and>
      (\<forall>C' \<in># dom_m (get_clauses_l T). C \<noteq> C' \<longrightarrow> fmlookup (get_clauses_l S) C' = fmlookup (get_clauses_l T) C') \<and>
      (C \<in># dom_m (get_clauses_l T) \<longrightarrow> (\<forall>L\<in>set (get_clauses_l T \<propto> C). undefined_lit (get_trail_l T) L))))\<close>
proof -
  obtain T where
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close> \<open>count_decided (get_trail_l S) = 0\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    clss: \<open>clauses_to_update_l S = {#}\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T))\<close> and
    annot: \<open>set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0}\<close>
    using assms unfolding simplify_clause_with_unit_st_pre_def
    by auto
  have C0: \<open>C \<noteq> 0\<close> \<open>C \<notin> set (get_all_mark_of_propagated (get_trail_l S))\<close>
    using list_invs C annot
    by (auto simp: twl_list_invs_def)
  have add_new: \<open>L \<in># all_init_lits_of_l S \<longleftrightarrow> L \<in># all_init_lits_of_l S + all_learned_lits_of_l S\<close>
    if \<open>simplify_clause_with_unit_st_pre C S\<close> for L S
    using that unfolding simplify_clause_with_unit_st_pre_def twl_struct_invs_def
      pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def state\<^sub>W_of_def[symmetric] apply -
    by normalize_goal+
      (auto simp add: all_init_lits_of_l_def all_learned_lits_of_l_def
      in_all_lits_of_mm_ain_atms_of_iff pget_all_learned_clss_get_all_learned_clss_l
      pget_all_init_clss_get_all_init_clss_l image_Un get_learned_clss_l_def)

  have [dest]: \<open>fmdrop C aa = fmdrop C bj \<Longrightarrow>
    remove1_mset C (dom_m bj) = remove1_mset C (dom_m aa)\<close> for C ab bj aa
    by (metis dom_m_fmdrop) 
  have n_d:\<open>no_dup (get_trail_l S)\<close>
    using ST st_invs unfolding twl_struct_invs_def pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by simp
  have in_lits:
    \<open>C \<in># dom_m aa \<and> count_decided a = 0 \<and> ab = None \<and> ci = {#} \<and> no_dup a \<and> C \<noteq> 0\<Longrightarrow>
  case x of
    (unc, b, N') \<Rightarrow>
    fmdrop C aa = fmdrop C N' \<and>
    mset (N' \<propto> C) \<subseteq># mset (aa \<propto> C) \<and>
    C \<in># dom_m N' \<and>
    (\<not> b \<longrightarrow> (\<forall>L\<in>#mset (N' \<propto> C). undefined_lit a L)) \<and>
    Multiset.Ball (mset (aa \<propto> C) - mset (N' \<propto> C)) (defined_lit a) \<and>
    irred aa C = irred N' C \<and> b = (\<exists>L. L \<in># mset (aa \<propto> C) \<and> L \<in> lits_of_l a) \<and>
    (unc \<longrightarrow> (aa = N' \<and> \<not>b)) \<Longrightarrow>
    fmdrop C bj = fmdrop C aa \<and> irred bj C = irred aa C \<and> mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<and> C \<in># dom_m bj \<Longrightarrow>
    x = (unc, bj') \<Longrightarrow>
    bj' = (aj, bj) \<Longrightarrow>
    \<not>unc \<Longrightarrow> aj \<Longrightarrow>
    set_mset
    (all_init_lits_of_l
    (a, fmdrop C bj, ab, (if irred aa C then add_mset (mset (aa \<propto> C)) else id) ac,
    (if \<not> irred aa C then add_mset (mset (aa \<propto> C)) else id) ad, ae, af, ag, ah, ai, bi, ci, di)) =
    set_mset (all_init_lits_of_l (a, aa, ab, ac, ad, ae, af, ag, ah, ai, bi, ci, di))
\<close>
    \<open>C \<in># dom_m aa \<and> count_decided a = 0 \<and> ab = None \<and> ci = {#} \<and> no_dup a \<and> C \<noteq> 0 \<Longrightarrow>
  case x of
    (unc, b, N') \<Rightarrow>
    fmdrop C aa = fmdrop C N' \<and>
    mset (N' \<propto> C) \<subseteq># mset (aa \<propto> C) \<and>
    C \<in># dom_m N' \<and>
    (\<not> b \<longrightarrow> (\<forall>L\<in>#mset (N' \<propto> C). undefined_lit a L)) \<and>
    Multiset.Ball (mset (aa \<propto> C) - mset (N' \<propto> C)) (defined_lit a) \<and>
    irred aa C = irred N' C \<and> b = (\<exists>L. L \<in># mset (aa \<propto> C) \<and> L \<in> lits_of_l a) \<and>
    (unc \<longrightarrow> (aa = N' \<and> \<not>b))  \<Longrightarrow>
    fmdrop C bj = fmdrop C aa \<and> irred bj C = irred aa C \<and> mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<and> C \<in># dom_m bj \<Longrightarrow>
    x = (unc, bj') \<Longrightarrow>
    bj' = (aj, bj) \<Longrightarrow>
    \<not>unc \<Longrightarrow> aj \<Longrightarrow>
    set_mset
    (all_learned_lits_of_l
      (a, fmdrop C bj, ab, (if irred aa C then add_mset (mset (aa \<propto> C)) else id) ac,
      (if \<not> irred aa C then add_mset (mset (aa \<propto> C)) else id) ad, ae, af, ag, ah, ai, bi, ci, di)) =
    set_mset (all_learned_lits_of_l (a, aa, ab, ac, ad, ae, af, ag, ah, ai, bi, ci, di)) \<close>
    for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x aj bj unc bj' ci di
    using assms distinct_mset_dom[of bj]  distinct_mset_dom[of aa]
    apply (auto simp: all_init_lits_of_l_def get_init_clss_l_def ran_m_def
      all_lits_of_mm_add_mset all_lits_of_mm_union
      all_learned_lits_of_l_def get_learned_clss_l_def
      dest!: multi_member_split[of _ \<open>dom_m _\<close>]
      cong: )
    apply (smt (verit, best) image_mset_cong2)+
    done
   have in_lits_prop:
     \<open>C \<in># dom_m aa \<and> count_decided a = 0 \<and> ab = None \<and> di = {#} \<and> no_dup a \<and> C \<noteq> 0 \<Longrightarrow>
    case x of
    (unc, b, N') \<Rightarrow>
   fmdrop C aa = fmdrop C N' \<and>
   mset (N' \<propto> C) \<subseteq># mset (aa \<propto> C) \<and>
   C \<in># dom_m N' \<and>
   (\<not> b \<longrightarrow> (\<forall>L\<in>#mset (N' \<propto> C). undefined_lit a L)) \<and>
   Multiset.Ball (mset (aa \<propto> C) - mset (N' \<propto> C)) (defined_lit a) \<and>
   irred aa C = irred N' C \<and> b = (\<exists>L. L \<in># mset (aa \<propto> C) \<and> L \<in> lits_of_l a) \<and>
      (unc \<longrightarrow> (aa = N'\<and> \<not>b)) \<Longrightarrow>
      x = (unc, bj') \<Longrightarrow>
      bj' = (aj, bj) \<Longrightarrow>
      \<not>unc \<Longrightarrow> \<not>aj \<Longrightarrow>
    fmdrop C bj = fmdrop C aa \<and> irred bj C = irred aa C \<and> mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<and> C \<in># dom_m bj \<Longrightarrow>
    length (bj \<propto> C) = 1 \<Longrightarrow>
    set_mset
  (all_init_lits_of_l
    (Propagated (bj \<propto> C ! 0) 0 # a, fmdrop C bj, ab, ah, ai, (if irred aa C then add_mset {#bj \<propto> C ! 0#} else id) ac,
     (if \<not> irred aa C then add_mset {#bj \<propto> C ! 0#} else id) ad, (if irred aa C then add_mset (mset (aa \<propto> C)) else id) ae,
     (if \<not> irred aa C then add_mset (mset (aa \<propto> C)) else id) af, ag, ci, di, add_mset (- bj \<propto> C ! 0) bi)) =
    set_mset (all_init_lits_of_l (a, aa, ab, ah, ai, ac, ad, ae, af, ag, ci, di, bi))
      \<close>
      \<open>C \<in># dom_m aa \<and> count_decided a = 0 \<and> ab = None \<and> di = {#} \<and> no_dup a \<and> C \<noteq> 0 \<Longrightarrow>
    case x of
    (unc, b, N') \<Rightarrow>
   fmdrop C aa = fmdrop C N' \<and>
   mset (N' \<propto> C) \<subseteq># mset (aa \<propto> C) \<and>
   C \<in># dom_m N' \<and>
   (\<not> b \<longrightarrow> (\<forall>L\<in>#mset (N' \<propto> C). undefined_lit a L)) \<and>
   Multiset.Ball (mset (aa \<propto> C) - mset (N' \<propto> C)) (defined_lit a) \<and>
   irred aa C = irred N' C \<and> b = (\<exists>L. L \<in># mset (aa \<propto> C) \<and> L \<in> lits_of_l a) \<and>
    (unc \<longrightarrow> (aa = N'\<and> \<not>b)) \<Longrightarrow>
      x = (unc, bj') \<Longrightarrow>
      bj' = (aj, bj) \<Longrightarrow>
      \<not>unc \<Longrightarrow> \<not>aj \<Longrightarrow>
    fmdrop C bj = fmdrop C aa \<and> irred bj C = irred aa C \<and> mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<and> C \<in># dom_m bj \<Longrightarrow>
    length (bj \<propto> C) = 1 \<Longrightarrow>
    set_mset
  (all_learned_lits_of_l
    (Propagated (bj \<propto> C ! 0) 0 # a, fmdrop C bj, ab, ah, ai, (if irred aa C then add_mset {#bj \<propto> C ! 0#} else id) ac,
     (if \<not> irred aa C then add_mset {#bj \<propto> C ! 0#} else id) ad, (if irred aa C then add_mset (mset (aa \<propto> C)) else id) ae,
     (if \<not> irred aa C then add_mset (mset (aa \<propto> C)) else id) af, ag, ci, di, add_mset (- bj \<propto> C ! 0) bi)) =
    set_mset (all_learned_lits_of_l (a, aa, ab, ah, ai, ac, ad, ae, af, ag, ci, di, bi))
      \<close>
      for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x aj bj bj' unc ci di
      subgoal
        using assms distinct_mset_dom[of bj]  distinct_mset_dom[of aa]
          image_mset_cong2[of \<open>dom_m (fmdrop C aa)\<close>
          \<open>\<lambda>x. the (fmlookup (fmdrop C aa) x)\<close>  \<open>\<lambda>x. the (fmlookup aa x)\<close>  \<open>dom_m (fmdrop C aa)\<close>,
          simplified]
        apply (cases \<open>bj \<propto> C\<close>)
        apply (auto simp: all_init_lits_of_l_def get_init_clss_l_def ran_m_def
          all_lits_of_mm_add_mset all_lits_of_mm_union all_lits_of_m_add_mset
          all_learned_lits_of_l_def get_learned_clss_l_def
          dest!: multi_member_split[of _ \<open>dom_m _\<close>]
          cong: )
        apply (metis in_clause_in_all_lits_of_m set_mset_mset)
        apply (metis all_lits_of_m_add_mset member_add_mset multi_member_split set_mset_mset)
        apply (smt (verit, best) image_mset_cong2)+
        done
      subgoal
        using assms distinct_mset_dom[of bj]  distinct_mset_dom[of aa]
          image_mset_cong2[of \<open>dom_m (fmdrop C aa)\<close>
          \<open>\<lambda>x. the (fmlookup (fmdrop C aa) x)\<close>  \<open>\<lambda>x. the (fmlookup aa x)\<close>  \<open>dom_m (fmdrop C aa)\<close>,
          simplified]
        apply (cases \<open>bj \<propto> C\<close>)
        apply (auto simp: all_init_lits_of_l_def get_init_clss_l_def ran_m_def
          all_lits_of_mm_add_mset all_lits_of_mm_union all_lits_of_m_add_mset
          all_learned_lits_of_l_def get_learned_clss_l_def
          dest!: multi_member_split[of _ \<open>dom_m _\<close>]
          cong: )
        apply (smt (verit, best) image_mset_cong2)+
        apply (metis in_clause_in_all_lits_of_m set_mset_mset)
        apply (metis all_lits_of_m_add_mset member_add_mset multi_member_split set_mset_mset)
        apply (smt (verit, best) image_mset_cong2)+
        done
      done

  have in_lits2: \<open>mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<Longrightarrow>
    C \<in># dom_m bj \<Longrightarrow> C \<in># dom_m aa \<Longrightarrow> length (bj \<propto> C) > 0 \<Longrightarrow>
    irred bj C \<Longrightarrow> irred aa C \<Longrightarrow> bj \<propto> C ! 0 \<in># all_lits_of_mm {#mset (fst x). x \<in># init_clss_l aa#}\<close> \<open>mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<Longrightarrow>
    C \<in># dom_m bj \<Longrightarrow> C \<in># dom_m aa \<Longrightarrow> length (bj \<propto> C) > 0 \<Longrightarrow>
    irred bj C \<Longrightarrow> irred aa C \<Longrightarrow> -bj \<propto> C ! 0 \<in># all_lits_of_mm {#mset (fst x). x \<in># init_clss_l aa#}\<close>
    \<open>mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<Longrightarrow>
    C \<in># dom_m bj \<Longrightarrow> C \<in># dom_m aa \<Longrightarrow> length (bj \<propto> C) > 0 \<Longrightarrow>
    \<not>irred bj C \<Longrightarrow> \<not>irred aa C \<Longrightarrow> bj \<propto> C ! 0 \<in># all_lits_of_mm {#mset (fst x). x \<in># learned_clss_l aa#}\<close> \<open>mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<Longrightarrow>
    C \<in># dom_m bj \<Longrightarrow> C \<in># dom_m aa \<Longrightarrow> length (bj \<propto> C) > 0 \<Longrightarrow>
    \<not>irred bj C \<Longrightarrow> \<not>irred aa C \<Longrightarrow> -bj \<propto> C ! 0 \<in># all_lits_of_mm {#mset (fst x). x \<in># learned_clss_l aa#}\<close>
    \<open>mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<Longrightarrow>
    fmdrop C bj = fmdrop C aa \<Longrightarrow>
    C \<in># dom_m bj \<Longrightarrow> irred bj C \<Longrightarrow> irred aa C \<Longrightarrow> 
    C \<in># dom_m aa \<Longrightarrow>
    xa \<in># all_lits_of_mm {#mset (fst x). x \<in># init_clss_l bj#} \<Longrightarrow> xa \<in># all_lits_of_mm {#mset (fst x). x \<in># init_clss_l aa#}
    \<close>
    \<open>mset (bj \<propto> C) \<subseteq># mset (aa \<propto> C) \<Longrightarrow>
    fmdrop C bj = fmdrop C aa \<Longrightarrow>
    C \<in># dom_m bj \<Longrightarrow> \<not>irred bj C \<Longrightarrow> \<not>irred aa C \<Longrightarrow> 
    C \<in># dom_m aa \<Longrightarrow>
    xa \<in># all_lits_of_mm {#mset (fst x). x \<in>#  learned_clss_l bj#} \<Longrightarrow> xa \<in># all_lits_of_mm {#mset (fst x). x \<in># learned_clss_l aa#}
    \<close>
    for bj C aa xa
    apply (auto 5 3 dest!: multi_member_split[of _ \<open>dom_m _\<close>] simp: ran_m_def all_lits_of_mm_add_mset
      in_all_lits_of_mm_uminus_iff dest: all_lits_of_m_mono)
    apply ((metis (no_types, lifting) in_clause_in_all_lits_of_m length_greater_0_conv mset_subset_eq_exists_conv nth_mem_mset union_iff)+)[4]
    apply (blast dest: all_lits_of_m_mono)
    apply (metis (no_types, lifting) add_mset_remove_trivial distinct_mset_add_mset distinct_mset_dom dom_m_fmdrop fmlookup_drop image_mset_cong2)
    apply (blast dest: all_lits_of_m_mono)
    by (metis (no_types, lifting) add_mset_remove_trivial distinct_mset_add_mset distinct_mset_dom dom_m_fmdrop fmlookup_drop image_mset_cong2)
  have tauto: \<open>\<not>tautology (mset ((get_clauses_l S) \<propto> C))\<close>
    using list_invs C
    by (auto simp: twl_list_invs_def)
  then show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding simplify_clause_with_unit_st_def simplify_clause_with_unit_def Let_def
    apply refine_vcg
    subgoal using assms by blast
    subgoal using C by auto
    subgoal using C by auto
    subgoal using confl by auto
    subgoal using clss by auto
    subgoal using n_d by simp
    subgoal using C list_invs by (auto simp: twl_list_invs_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal 
      by (rule in_lits)
    subgoal 
      by (rule in_lits)
    subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg x ah bh
      supply[[goals_limit=1]]
      using count_decided_ge_get_level[of \<open>get_trail_l S\<close>] C0
      by (auto simp: cdcl_twl_unitres_true_l.simps
        intro!: exI[of _ C])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto (metis dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff)+
    subgoal
      by (rule in_lits_prop)
    subgoal
      by (rule in_lits_prop)
    subgoal by (auto simp: all_init_lits_of_l_def)
    subgoal
      by (subst add_new, subst (asm) eq_commute[of \<open>set_mset (all_init_lits_of_l _)\<close>],
        subst (asm) eq_commute[of \<open>set_mset (all_learned_lits_of_l _)\<close>])
       (auto simp: all_init_lits_of_l_def get_init_clss_l_def
        all_learned_lits_of_l_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset)
    subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x _ _ _ _ _ _ aj bj
      using ST st_invs C0 ent apply -
      apply (rule disjI2, rule disjI1)
      apply (auto simp: length_list_Suc_0
        dest: in_diffD
        intro!: cdcl_twl_unitres_l_intros2' cdcl_twl_unitres_l_intros4'
        intro:  cdcl_twl_unitres_l_intros2'[where C' = \<open>mset (get_clauses_l S \<propto> C) - mset (bj \<propto> C)\<close>
        and T = T]
        cdcl_twl_unitres_l_intros4'[where C' = \<open>mset (get_clauses_l S \<propto> C) - mset (bj \<propto> C)\<close>
        and T = T])
      done
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto (metis dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff)+
    subgoal using assms apply (auto simp: all_init_lits_of_l_def
      all_lits_of_mm_union init_clss_l_fmdrop_if image_mset_remove1_mset_if
      get_init_clss_l_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      dest: all_lits_of_mm_diffD in_lits
      intro: in_all_lits_of_mm_init_clss_l_single_out)
      by (metis all_lits_of_mm_add_mset diff_single_trivial insert_DiffM union_iff)
    subgoal using assms apply (auto simp: all_learned_lits_of_l_def
      all_lits_of_mm_union learned_clss_l_fmdrop_if image_mset_remove1_mset_if
      get_learned_clss_l_def all_lits_of_mm_add_mset all_lits_of_m_add_mset in_lits
      dest: all_lits_of_mm_diffD
      intro: in_all_lits_of_mm_learned_clss_l_single_out)
      by (metis all_lits_of_mm_add_mset diff_single_trivial insert_DiffM union_iff)
    subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x _ _ _ _ _ _ aj bj
      using count_decided_ge_get_level[of \<open>get_trail_l S\<close>] ST st_invs C0 ent
        cdcl_twl_unitres_false_entailed[of C \<open>get_clauses_l S\<close> \<open>get_trail_l S\<close>
         \<open>get_unkept_init_clauses_l S\<close> \<open>get_unkept_learned_clss_l S\<close>
         \<open>get_kept_init_clauses_l S\<close> \<open>get_kept_learned_clss_l S\<close>
        \<open>get_subsumed_init_clauses_l S\<close> \<open>get_subsumed_learned_clauses_l S\<close>
        \<open>get_init_clauses0_l S\<close> \<open>get_learned_clauses0_l S\<close>
        \<open>literals_to_update_l S\<close> T
        \<open>mset (get_clauses_l S \<propto> C) - mset (bj \<propto> C)\<close>]
        twl_st_l_struct_invs_distinct[of S T None C]
      apply (auto simp: cdcl_twl_unitres_true_l.simps cdcl_twl_unitres_l.simps Un_assoc
        dest: distinct_mset_mono[of \<open>mset _\<close> \<open>mset _\<close>, unfolded distinct_mset_mset_distinct]
        intro!: exI[of _ C])
      done
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto (metis dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff)+
    subgoal using assms apply (auto simp: all_init_lits_of_l_def
      all_lits_of_mm_union init_clss_l_fmdrop_if image_mset_remove1_mset_if
      get_init_clss_l_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      dest: all_lits_of_mm_diffD in_lits2
      intro: in_all_lits_of_mm_init_clss_l_single_out)
      apply (smt (z3) Watched_Literals_Clauses.ran_m_mapsto_upd all_lits_of_mm_add_mset filter_mset_add_mset fmupd_same image_mset_add_mset prod.collapse ran_m_lf_fmdrop union_iff)+
      done
    subgoal using assms apply (auto simp: all_init_lits_of_l_def
      all_lits_of_mm_union init_clss_l_fmdrop_if image_mset_remove1_mset_if
      get_init_clss_l_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      get_learned_clss_l_def all_learned_lits_of_l_def
      dest: all_lits_of_mm_diffD in_lits2
      intro: in_all_lits_of_mm_init_clss_l_single_out)
      apply (smt (z3) Watched_Literals_Clauses.ran_m_mapsto_upd all_lits_of_mm_add_mset filter_mset_add_mset fmupd_same image_mset_add_mset prod.collapse ran_m_lf_fmdrop union_iff)+
      done
    subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x _ _ _ _ _ _ aj bj
      using assms
      by (auto  simp: list_length_2_isabelle_come_on twl_list_invs_def simplify_clause_with_unit_st_pre_def
        intro!: cdcl_twl_unitres_l_intros3' cdcl_twl_unitres_l_intros1'
        dest: distinct_mset_mono[of \<open>mset _\<close> \<open>mset _\<close>, unfolded distinct_mset_mset_distinct]
        intro!: exI[of _ C] fmdrop_eq_update_eq2)
    subgoal using assms apply (auto simp: all_init_lits_of_l_def
      all_lits_of_mm_union init_clss_l_fmdrop_if image_mset_remove1_mset_if
      get_init_clss_l_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      dest: all_lits_of_mm_diffD in_lits2
      intro: in_all_lits_of_mm_init_clss_l_single_out)
    done
    subgoal using assms by auto
       (metis dom_m_fmdrop insert_DiffM)+
    subgoal using assms apply auto
      apply (metis fmlookup_drop)+
      done
    subgoal using assms by auto
    done
qed

text \<open>

  We implement forward subsumption (even if it is not a complete algorithm...). We initially tried
  to implement a very limited version similar to Splatz, i.e., putting all clauses in an array
  sorted by length and checking for sub-res in that array. This is more efficient in the sense that
  we know that all previous clauses are smaller... unless you want to strengthen binary clauses too.
  In this case list have to resorted.

  After some time, we decided to implement forward subsumption directly. The implementation works in
  three steps:

  \<^item> the \<open>one-step\<close> version tries to sub-res the clause with a given set of indices. Typically, one
  entry in the watch list.

  \<^item> then the \<open>try_to_forward_subsume\<close> iterates over multiple of whatever. Typically, the iteration
  goes over all watch lists from the literals in the clause (and their negation) to find strengthening
  clauses.

  \<^item> finally, the \<open>all\<close> version goes over all clauses sorted in a set of indices.

After much thinking, we decided to follow the version from CaDiCaL that ignores all clauses that
contain a fixed literal. At first we tried to simplify the clauses, but this means that down in the
real implementation, sorting clauses does not work (because the units are removed).
\<close>

definition forward_subsumption_one_pre :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_pre = (\<lambda>C xs S.
  \<exists>T. C \<noteq> 0 \<and>
  (S, T) \<in> twl_st_l None \<and>
  twl_struct_invs T \<and>
  twl_list_invs S \<and>
  clauses_to_update_l S = {#} \<and>
  get_conflict_l S = None \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and>
  count_decided (get_trail_l S) = 0 \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
  C \<in># dom_m (get_clauses_l S) \<and>
  (\<forall>L \<in># mset (get_clauses_l S \<propto> C). undefined_lit (get_trail_l S) L) \<and>
  length (get_clauses_l S \<propto> C) > 2)\<close>

datatype 'v subsumption =
  is_subsumed: SUBSUMED_BY (subsumed_by: nat) |
  is_strengthened: STRENGTHENED_BY (strengthened_on_lit: \<open>'v literal\<close>)
    (strengthened_by: nat) |
  NONE

definition try_to_subsume :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v clauses_l \<Rightarrow> 'v subsumption \<Rightarrow> bool\<close> where
  \<open>try_to_subsume C C' N s = (case s of
    NONE \<Rightarrow> True
  | SUBSUMED_BY C'' \<Rightarrow> mset (N \<propto> C') \<subseteq># mset (N \<propto> C) \<and> C'' = C'
  | STRENGTHENED_BY L C'' \<Rightarrow> L \<in># mset (N \<propto> C') \<and> -L \<in># mset (N \<propto> C) \<and>
   mset (N \<propto> C') - {#L#} \<subseteq># mset (N \<propto> C) - {#-L#} \<and> C'' = C')\<close>

definition strengthen_clause_pre where
  \<open>strengthen_clause_pre C C' L S \<longleftrightarrow> (C \<noteq> C' \<and> C\<in>#dom_m (get_clauses_l S) \<and> C'\<in>#dom_m (get_clauses_l S))\<close>

definition strengthen_clause :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow>
   'v twl_st_l  \<Rightarrow>  'v twl_st_l nres\<close> where
  \<open>strengthen_clause = (\<lambda>C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
   ASSERT (strengthen_clause_pre C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
  E \<leftarrow> SPEC (\<lambda>E. mset E = mset (remove1 (-L) (N \<propto> C)));
  if length (N \<propto> C) = 2
  then do {
     ASSERT (length (remove1 (-L) (N \<propto> C)) = 1);
     let L = hd E;
     RETURN (Propagated L 0 # M, fmdrop C' (fmdrop C N), D,
       (if irred N C' then add_mset (mset (N \<propto> C')) else id) NE,
       (if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) UE,
        (if irred N C then add_mset {#L#} else id) NEk, (if \<not>irred N C then add_mset {#L#} else id) UEk,
        ((if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
       ((if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US,
       N0, U0, WS, add_mset (-L) Q)
  }
  else if length (N \<propto> C) = length (N \<propto> C')
  then RETURN (M, fmdrop C' (fmupd C (E, irred N C \<or> irred N C') N), D, NE, UE, NEk, UEk,
     ((if irred N C' then add_mset (mset (N \<propto> C')) else id)  o (if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
    ((if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) o (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US,
     N0, U0, WS, Q)
  else RETURN (M, fmupd C (E, irred N C) N, D, NE, UE, NEk, UEk,
    (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
    (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, WS, Q)
  })\<close>

definition subsume_or_strengthen_pre :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>subsume_or_strengthen_pre = (\<lambda>C s S. \<exists>S'.  length (get_clauses_l S \<propto> C) \<ge> 2 \<and> C \<in># dom_m (get_clauses_l S) \<and>
  count_decided (get_trail_l S) = 0 \<and> distinct (get_clauses_l S \<propto> C) \<and> (\<forall>L\<in>set (get_clauses_l S \<propto> C). undefined_lit (get_trail_l S) L) \<and> get_conflict_l S = None \<and>
  C \<notin> set (get_all_mark_of_propagated (get_trail_l S)) \<and> clauses_to_update_l S = {#} \<and>
  twl_list_invs S \<and>
  (S,S')\<in>twl_st_l None \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S') \<and> 
    twl_struct_invs S' \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
   (case s of
    NONE \<Rightarrow> True
  | SUBSUMED_BY C' \<Rightarrow> mset (get_clauses_l S \<propto> C') \<subseteq># mset (get_clauses_l S \<propto> C) \<and> C \<notin> set (get_all_mark_of_propagated (get_trail_l S)) \<and> distinct ((get_clauses_l S) \<propto> C') \<and> C \<noteq> C' \<and> \<not>tautology (mset ((get_clauses_l S) \<propto> C')) \<and> C' \<in># dom_m (get_clauses_l S)
  | STRENGTHENED_BY L C' \<Rightarrow> L \<in># mset ((get_clauses_l S) \<propto> C') \<and> -L \<in># mset ((get_clauses_l S) \<propto> C) \<and> \<not>tautology (mset ((get_clauses_l S) \<propto> C')) \<and> C' \<noteq> 0 \<and>
  mset ((get_clauses_l S) \<propto> C') - {#L#} \<subseteq># mset ((get_clauses_l S) \<propto> C) - {#-L#} \<and> C' \<in># dom_m (get_clauses_l S) \<and> distinct ((get_clauses_l S) \<propto> C')  \<and>
  C' \<notin> set (get_all_mark_of_propagated (get_trail_l S))\<and> 2 \<le> length ((get_clauses_l S) \<propto> C') \<and>
  \<not> tautology (remove1_mset L (mset ((get_clauses_l S) \<propto> C')) + remove1_mset (- L) (mset ((get_clauses_l S) \<propto> C)))))\<close>

definition subsume_or_strengthen :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> 'v twl_st_l \<Rightarrow> _ nres\<close> where
  \<open>subsume_or_strengthen = (\<lambda>C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
   ASSERT(subsume_or_strengthen_pre C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
   (case s of
     NONE \<Rightarrow> RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
   | SUBSUMED_BY C' \<Rightarrow> do { let T= (M, fmdrop C (if \<not>irred N C' \<and> irred N C then fmupd C' (N \<propto> C', True) N else N), D,
          NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
           (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, WS, Q);
       ASSERT (set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l  (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)));
       RETURN T
     }
   | STRENGTHENED_BY L C' \<Rightarrow> strengthen_clause C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q))
  })\<close>

inductive cdcl_twl_pure_remove_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_pure_remove_l (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
    (Propagated L 0 # M, N, None, NE, UE, add_mset {#L#} NEk, UEk, NS, US, N0, U0,
      {#}, add_mset (-L)Q)\<close>
  if
    \<open>undefined_lit M L\<close>
    \<open>-L \<notin> \<Union>(set_mset ` set_mset (mset `# init_clss_lf N))\<close>
    \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf N + NE + NEk + NS + N0)\<close>
    \<open>count_decided M = 0\<close>

lemma cdcl_twl_pure_remove_l_cdcl_twl_pure_remove:
  assumes \<open>cdcl_twl_pure_remove_l S T\<close>
    \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_pure_remove S' T'\<close>
  using assms
  by (auto 5 3 simp: cdcl_twl_pure_remove_l.simps twl_st_l_def
    cdcl_twl_pure_remove.simps image_image in_all_lits_of_mm_ain_atms_of_iff
    intro!: convert_lit.intros(3)
    simp: convert_lits_l_add_mset mset_take_mset_drop_mset'
    dest: in_set_takeD in_set_dropD)

lemma rtranclp_cdcl_twl_pure_remove_l_cdcl_twl_pure_remove:
  assumes \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T\<close>
    \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_pure_remove\<^sup>*\<^sup>* S' T'\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by blast
  subgoal for T U
    using cdcl_twl_pure_remove_l_cdcl_twl_pure_remove[of T U] by fastforce
  done

lemma cdcl_twl_pure_remove_l_twl_list_invs:
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  by (auto simp: cdcl_twl_pure_remove_l.simps
    twl_list_invs_def)

inductive cdcl_twl_inprocessing_l for S T where
  \<open>cdcl_twl_unitres_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close> |
  \<open>cdcl_twl_unitres_true_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close> |
  \<open>cdcl_twl_subsumed_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>|
  \<open>cdcl_twl_subresolution_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>|
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>

lemma subseteq_mset_size_eql_iff: \<open>size Aa = size A \<Longrightarrow> Aa \<subseteq># A \<longleftrightarrow> Aa = A\<close>
  by (auto simp: subseteq_mset_size_eql)

lemma subresolution_strengtheningI:
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  remove1_mset (-L) (mset (N \<propto> C)) \<subseteq># remove1_mset L (mset (N \<propto> C')) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> 3 \<le> length (N \<propto> C') \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C'). undefined_lit M L \<Longrightarrow>
  C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  irred N C' \<Longrightarrow> mset E = mset (remove1 (L) (N \<propto> C')) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmupd C' (E, True) N, None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C')) NS,
  US, N0, U0, {#}, Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  remove1_mset (-L) (mset (N \<propto> C)) \<subseteq># remove1_mset L (mset (N \<propto> C')) \<Longrightarrow>
  \<not> tautology (remove1_mset (-L) (mset (N \<propto> C)) + remove1_mset L (mset (N \<propto> C'))) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> 3 \<le> length (N \<propto> C') \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C'). undefined_lit M L \<Longrightarrow>
  C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  \<not>irred N C' \<Longrightarrow> mset E = mset (remove1 (L) (N \<propto> C')) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmupd C' (E, False) N, None, NE, UE, NEk, UEk, NS, add_mset (mset (N \<propto> C')) US, N0, U0, {#}, Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  remove1_mset (-L) (mset (N \<propto> C)) \<subseteq># remove1_mset L (mset (N \<propto> C')) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> 3 \<le> length (N \<propto> C') \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C'). undefined_lit M L \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> mset E = mset (remove1 (L) (N \<propto> C')) \<Longrightarrow>
  irred N C' \<Longrightarrow> irred N C \<Longrightarrow> length (N \<propto> C') = length (N \<propto> C) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C (fmupd C' (E, True) N), None, NE, UE, NEk, UEk,
  add_mset (mset (N \<propto> C))  (add_mset (mset (N \<propto> C')) NS),
  US, N0, U0, {#}, Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  remove1_mset (-L) (mset (N \<propto> C)) \<subseteq># remove1_mset L (mset (N \<propto> C')) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> 3 \<le> length (N \<propto> C') \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C'). undefined_lit M L \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> mset E = mset (remove1 (L) (N \<propto> C')) \<Longrightarrow>
  \<not> tautology (remove1_mset (- L) (mset (N \<propto> C)) + remove1_mset L (mset (N \<propto> C'))) \<Longrightarrow>
  \<not>irred N C' \<Longrightarrow> \<not>irred N C \<Longrightarrow> length (N \<propto> C') = length (N \<propto> C) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C (fmupd C' (E, False) N), None, NE, UE, NEk, UEk, NS,
  add_mset (mset (N \<propto> C))  (add_mset (mset (N \<propto> C')) US), N0, U0, {#}, Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  remove1_mset (-L) (mset (N \<propto> C)) \<subseteq># remove1_mset L (mset (N \<propto> C')) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> 3 \<le> length (N \<propto> C') \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C'). undefined_lit M L \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  \<not> tautology (remove1_mset (- L) (mset (N \<propto> C)) + remove1_mset L (mset (N \<propto> C'))) \<Longrightarrow>
  \<not>irred N C' \<Longrightarrow> irred N C \<Longrightarrow> length (N \<propto> C') = length (N \<propto> C) \<Longrightarrow> mset E = mset (remove1 (L) (N \<propto> C')) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C (fmupd C' (E, True) N), None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C)) NS,
  (add_mset (mset (N \<propto> C')) US), N0, U0, {#}, Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  remove1_mset (-L) (mset (N \<propto> C)) \<subseteq># remove1_mset L (mset (N \<propto> C')) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> 3 \<le> length (N \<propto> C') \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C'). undefined_lit M L \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> mset E = mset (remove1 (L) (N \<propto> C')) \<Longrightarrow>
  \<not> tautology (remove1_mset (- L) (mset (N \<propto> C)) + remove1_mset L (mset (N \<propto> C'))) \<Longrightarrow>
  irred N C' \<Longrightarrow> \<not>irred N C \<Longrightarrow> length (N \<propto> C') = length (N \<propto> C) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C (fmupd C' (E, True) N), None, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C')) NS,
  (add_mset (mset (N \<propto> C)) US), N0, U0, {#}, Q)\<close>
  and

  subresolution_strengtheningI_binary:
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  length (N \<propto> C) = 2 \<Longrightarrow> remove1_mset (L) (mset (N \<propto> C')) \<subseteq># remove1_mset (-L) (mset (N \<propto> C)) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> length (N \<propto> C') \<ge> 2  \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C). undefined_lit M L \<Longrightarrow>
  irred N C \<Longrightarrow> C' \<noteq> 0 \<Longrightarrow> mset E = mset (remove1 (-L) (N \<propto> C)) \<Longrightarrow>
  irred N C' \<Longrightarrow> C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>*
  (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (Propagated (hd E) 0 # M, fmdrop C' (fmdrop C N), None, add_mset (mset (N \<propto> C')) NE, UE, add_mset {#hd E#} NEk, UEk,
   (add_mset (mset (N \<propto> C)) NS), US, N0, U0, {#}, add_mset (-hd E) Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  length (N \<propto> C) = 2 \<Longrightarrow> remove1_mset (L) (mset (N \<propto> C')) \<subseteq># remove1_mset (-L) (mset (N \<propto> C)) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> length (N \<propto> C') \<ge> 2  \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C). undefined_lit M L \<Longrightarrow>
  \<not>irred N C \<Longrightarrow> \<not>irred N C' \<Longrightarrow> C' \<noteq> 0 \<Longrightarrow> mset E = mset (remove1 (-L) (N \<propto> C)) \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>*
  (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (Propagated (hd E) 0 # M, fmdrop C' (fmdrop C N), None, NE, add_mset (mset (N \<propto> C')) UE, NEk,
   add_mset {#hd E#} UEk, NS, add_mset (mset (N \<propto> C)) US, N0, U0,
   {#}, add_mset (- hd E) Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  length (N \<propto> C) = 2 \<Longrightarrow> remove1_mset (L) (mset (N \<propto> C')) \<subseteq># remove1_mset (-L) (mset (N \<propto> C)) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> length (N \<propto> C') \<ge> 2  \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C). undefined_lit M L \<Longrightarrow>
  \<not>irred N C \<Longrightarrow> irred N C' \<Longrightarrow> C' \<noteq> 0 \<Longrightarrow> mset E = mset (remove1 (-L) (N \<propto> C)) \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>*
  (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (Propagated (hd E) 0 # M, fmdrop C' (fmdrop C N), None, add_mset (mset (N \<propto> C'))  NE, UE, NEk,
   add_mset {#hd E#} UEk, NS, add_mset (mset (N \<propto> C)) US, N0, U0,
   {#}, add_mset (- hd E) Q)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> C' \<in># dom_m N \<Longrightarrow> -L \<in># mset (N \<propto> C) \<Longrightarrow> L \<in># mset (N \<propto> C') \<Longrightarrow> count_decided M = 0 \<Longrightarrow>
  length (N \<propto> C) = 2 \<Longrightarrow> remove1_mset (L) (mset (N \<propto> C')) \<subseteq># remove1_mset (-L) (mset (N \<propto> C)) \<Longrightarrow>
  distinct (N \<propto> C') \<Longrightarrow> length (N \<propto> C') \<ge> 2  \<Longrightarrow>
  \<forall>L\<in> set (N \<propto> C). undefined_lit M L \<Longrightarrow>
  irred N C \<Longrightarrow> \<not>irred N C' \<Longrightarrow> C' \<noteq> 0 \<Longrightarrow> mset E = mset (remove1 (-L) (N \<propto> C)) \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow> C' \<notin> set (get_all_mark_of_propagated M) \<Longrightarrow>
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>*
  (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (Propagated (hd E) 0 # M, fmdrop C' (fmdrop C N), None, NE,
   add_mset (mset (N \<propto> C')) UE, add_mset {#hd E#} NEk, UEk,
   add_mset (mset (N \<propto> C)) NS, US, N0, U0, {#}, add_mset (- hd E) Q)\<close>
  unfolding distinct_mset_mset_distinct[symmetric] set_mset_mset[symmetric]
  supply [simp del] = distinct_mset_mset_distinct set_mset_mset
  supply [simp] = distinct_mset_mset_distinct[symmetric]
  subgoal
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (cases \<open>irred N C\<close>)
    apply (rule cdcl_twl_subresolution_l.intros(1)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset L (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 simp flip: size_mset; fail)+
    apply (rule cdcl_twl_subresolution_l.intros(7)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset L (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 simp flip: size_mset; fail)+
    done
  subgoal
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule r_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (cases \<open>\<not>irred N C\<close>)
    apply (rule cdcl_twl_subresolution_l.intros(3)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset (L) (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 simp flip: size_mset; fail)+
    apply (rule cdcl_twl_subresolution_l.intros(5)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset (L) (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 simp flip: size_mset; fail)+
    done
  subgoal
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (cases \<open>irred N C\<close>)
    apply (rule cdcl_twl_subresolution_l.intros(1)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset L (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 simp flip: size_mset; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(3))
    apply (rule cdcl_twl_subsumed_l.intros(1)[where C=C' and C'=C])
    apply normalize_goal+
    using subseteq_mset_size_eql[of \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>  \<open>remove1_mset L (mset (N \<propto> C'))\<close>]  apply -
    apply ((subst (asm) size_mset[symmetric])+; hypsubst?)
    apply (simp only: add_mset_remove_trivial size_add_mset nat.inject)
    apply (simp; fail)
    apply (auto; fail)+
    done
  subgoal
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(3)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset (L) (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1  simp flip: size_mset; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(3))
    apply (rule cdcl_twl_subsumed_l.intros(2)[where C=C' and C'=C])
    apply normalize_goal+
    using subseteq_mset_size_eql[of \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>  \<open>remove1_mset L (mset (N \<propto> C'))\<close>]  apply -
    apply ((subst (asm) size_mset[symmetric])+; hypsubst?)
    apply (simp only: add_mset_remove_trivial size_add_mset nat.inject)
    apply (simp; fail)
    apply (auto; fail)+
    done
  subgoal
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(5)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset (L) (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1  simp flip: size_mset; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(3))
    apply (rule cdcl_twl_subsumed_l.intros(4)[where C=C' and C'=C])
    apply normalize_goal+
    using subseteq_mset_size_eql[of \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>  \<open>remove1_mset L (mset (N \<propto> C'))\<close>]  apply -
    apply ((subst (asm) size_mset[symmetric])+; hypsubst?)
    apply (simp only: add_mset_remove_trivial size_add_mset nat.inject)
    apply (simp; fail)
    apply (auto simp: tautology_union; fail)+
    apply (auto simp: fmdrop_fmupd)
    done
  subgoal
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(7)[of C N C' \<open>-L\<close> \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>
      \<open>remove1_mset (L) (mset (N \<propto> C'))\<close> _ \<open>E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1  simp flip: size_mset; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(3))
    apply (rule cdcl_twl_subsumed_l.intros(3)[where C=C' and C'=C])
    apply normalize_goal+
    using subseteq_mset_size_eql[of \<open>remove1_mset (-L) (mset (N \<propto> C))\<close>  \<open>remove1_mset L (mset (N \<propto> C'))\<close>]  apply -
    apply ((subst (asm) size_mset[symmetric])+; hypsubst?)
    apply (simp only: add_mset_remove_trivial size_add_mset nat.inject)
    apply (simp; fail)
    apply (auto simp: tautology_union; fail)+
    done
  \<comment> \<open>Now binary:\<close>
  subgoal
    using distinct_mset_dom[of N] apply -
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(2)[of C' N C \<open>L\<close> \<open>remove1_mset (L) (mset (N \<propto> C'))\<close>
      \<open>remove1_mset (-L) (mset (N \<propto> C))\<close> _  \<open>hd E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 length_list_2
      add_mset_eq_add_mset subset_eq_mset_single_iff; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(2))
    apply (rule cdcl_twl_unitres_true_l.intros(1)[where N=\<open>fmdrop C N\<close> and C=C' and
      L = \<open>hd (remove1 (- L) (N \<propto> C))\<close>])
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff)[]
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff
      dest!: multi_member_split[of _ \<open>dom_m N\<close>]
      ; fail)+
    done
  subgoal
    using distinct_mset_dom[of N] apply -
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(4)[of C' N C \<open>L\<close> \<open>remove1_mset (L) (mset (N \<propto> C'))\<close>
      \<open>remove1_mset (-L) (mset (N \<propto> C))\<close> _  \<open>hd (remove1 (-L) (N \<propto> C))\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 length_list_2
      add_mset_eq_add_mset; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(2))
    apply (rule cdcl_twl_unitres_true_l.intros(2)[where N=\<open>fmdrop C N\<close> and C=C' and
      L = \<open>hd (remove1 (- L) (N \<propto> C))\<close>])
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff)[]
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff
      dest!: multi_member_split[of _ \<open>dom_m N\<close>]
      ; fail)+
    done
  subgoal
    using distinct_mset_dom[of N] apply -
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(6)[of C' N C \<open>L\<close> \<open>remove1_mset (L) (mset (N \<propto> C'))\<close>
      \<open>remove1_mset (-L) (mset (N \<propto> C))\<close> _  \<open>hd E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 length_list_2
      add_mset_eq_add_mset subset_eq_mset_single_iff; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(2))
    apply (rule cdcl_twl_unitres_true_l.intros(1)[where N=\<open>fmdrop C N\<close> and C=C' and
      L = \<open>hd E\<close>])
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff)[]
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff
      dest!: multi_member_split[of _ \<open>dom_m N\<close>]
      ; fail)+
    done
  subgoal
    using distinct_mset_dom[of N] apply -
    apply (drule multi_member_split[of L] multi_member_split[of \<open>-L\<close>])+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(4))
    apply (rule cdcl_twl_subresolution_l.intros(8)[of C' N C \<open>L\<close> \<open>remove1_mset (L) (mset (N \<propto> C'))\<close>
      \<open>remove1_mset (-L) (mset (N \<propto> C))\<close> _  \<open>hd E\<close>])
    apply (auto dest!: in_diffD simp: distinct_mset_remdups_mset_id length_remove1 length_list_2
      add_mset_eq_add_mset subset_eq_mset_single_iff; fail)+
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_twl_inprocessing_l.intros(2))
    apply (rule cdcl_twl_unitres_true_l.intros(2)[where N=\<open>fmdrop C N\<close> and C=C' and
      L = \<open>hd E\<close>])
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff)[]
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (metis add_mset_commute set_mset_mset union_single_eq_member)
    apply (auto simp: add_mset_eq_add_mset length_list_2 subset_eq_mset_single_iff
      dest!: multi_member_split[of _ \<open>dom_m N\<close>]
      ; fail)+
    done
  done

lemma cdcl_twl_inprocessing_l_all_init_lits_of_l:
  assumes \<open>cdcl_twl_inprocessing_l S T\<close>
  shows \<open>set_mset (all_init_lits_of_l S) = set_mset (all_init_lits_of_l T)\<close>
proof -
  have [simp]: \<open>D \<notin># A \<Longrightarrow> {#the (if D = x then b else fmlookup N x). x \<in># A#} =
    {#the (fmlookup N x). x \<in># A#}\<close>
    \<open>D \<notin># A \<Longrightarrow> {#the (if x = D then b else fmlookup N x). x \<in># A#} =
    {#the (fmlookup N x). x \<in># A#}\<close> for D E N A b
    by (auto intro!: image_mset_cong)
  have dups_uniq[dest]: \<open>remdups_mset D' = {#K#} \<Longrightarrow> set_mset (all_lits_of_m D') = {-K,K}\<close> for D' K
    by (metis all_lits_of_m_add_mset all_lits_of_m_empty all_lits_of_m_remdups_mset
      insert_commute set_mset_add_mset_insert set_mset_empty)
  have [simp]: \<open>- L \<in># all_lits_of_m a \<longleftrightarrow> L \<in># all_lits_of_m a\<close>
     \<open>- L \<in># all_lits_of_mm b \<longleftrightarrow> L \<in># all_lits_of_mm b\<close>
    \<open>L \<in># xb \<Longrightarrow> L \<in># all_lits_of_m xb\<close> for L a xb b
    by (solves \<open>cases L, auto simp: rev_image_eqI all_lits_of_m_def all_lits_of_mm_def\<close>)+

  have [simp]: \<open>L \<in># all_lits_of_m (mset (N \<propto> xa)) \<longleftrightarrow> L \<in> set (N \<propto> xa) \<or> -L \<in> set (N \<propto> xa)\<close>
    for L N xa xb
    by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_all_lits_of_m_ain_atms_of_iff)

  show ?thesis
    using assms
    using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
    supply [[goals_limit=1]]
    apply (induction rule: cdcl_twl_inprocessing_l.induct)
    by (auto 4 3 simp: cdcl_twl_unitres_l.simps
      cdcl_twl_unitres_true_l.simps
      cdcl_twl_subsumed_l.simps
      cdcl_twl_subresolution_l.simps
      all_init_lits_of_l_def
      add_mset_eq_add_mset removeAll_notin
      get_init_clss_l_def init_clss_l_mapsto_upd_notin
      init_clss_l_mapsto_upd ran_m_def all_lits_of_m_union
      all_lits_of_m_add_mset distinct_mset_remove1_All
      init_clss_l_fmupd_if all_lits_of_mm_add_mset
      all_lits_of_m_remdups_mset
      dest!: multi_member_split[of \<open>_ :: nat\<close> \<open>_\<close>]
      dest: all_lits_of_m_mono)[4]
    (auto simp: cdcl_twl_pure_remove_l.simps
      all_init_lits_of_l_def
      add_mset_eq_add_mset removeAll_notin
      get_init_clss_l_def init_clss_l_mapsto_upd_notin
      init_clss_l_mapsto_upd ran_m_def all_lits_of_m_union
      all_lits_of_m_add_mset distinct_mset_remove1_All
      init_clss_l_fmupd_if all_lits_of_mm_add_mset all_lits_of_mm_union
      all_lits_of_m_remdups_mset
    dest!: multi_member_split[of \<open>_\<close> \<open>_ :: _ clauses\<close>]
        multi_member_split[of \<open>_ :: nat\<close> \<open>_\<close>]
    dest: all_lits_of_m_mono
    intro: in_clause_in_all_lits_of_m)
qed

lemma rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l:
  assumes \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T\<close>
  shows \<open>set_mset (all_init_lits_of_l S) = set_mset (all_init_lits_of_l T)\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto dest: cdcl_twl_inprocessing_l_all_init_lits_of_l)

lemma subsume_or_strengthen:
  assumes \<open>subsume_or_strengthen_pre C s S\<close> \<open>C \<in># dom_m (get_clauses_l S)\<close>
  shows
    \<open>subsume_or_strengthen C s S \<le>\<Down>Id (SPEC(\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and>
      (s = NONE \<longrightarrow> T = S) \<and>
    (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow> get_trail_l S = get_trail_l T) \<and>
     (\<forall>D\<in>#remove1_mset C (dom_m (get_clauses_l T)).
    D \<in># dom_m (get_clauses_l S) \<and> get_clauses_l T \<propto> D = get_clauses_l S \<propto> D) \<and>
    (\<forall>D. D \<noteq> C \<longrightarrow> is_strengthened s \<longrightarrow> D \<noteq> strengthened_by s \<longrightarrow> (D \<in># dom_m (get_clauses_l T)) = (D \<in># dom_m (get_clauses_l S))) \<and>
    (\<forall>D. D \<noteq> C \<longrightarrow> is_subsumed s \<longrightarrow> D \<noteq> subsumed_by s \<longrightarrow> (D \<in># dom_m (get_clauses_l T)) = (D \<in># dom_m (get_clauses_l S)))))\<close>
proof -
  have [iff]: \<open>C \<in># remove1_mset C (dom_m N) \<longleftrightarrow> False\<close>
    \<open>C \<in># dom_m N - {#C, C#} \<longleftrightarrow> False\<close>for N
    using distinct_mset_dom[of N] by (cases \<open>C\<in>#dom_m N\<close>; auto dest: multi_member_split)+
  have [iff]: \<open>C \<in># dom_m N - {#C, x22, C#} \<longleftrightarrow> False\<close>  \<open>C \<in># dom_m N - {#C, x22#} \<longleftrightarrow> False\<close>
    \<open>x22 \<in># dom_m N - {#C, x22, C#} \<longleftrightarrow> False\<close>
    \<open>x22 \<in># dom_m N - {#C, x22#} \<longleftrightarrow> False\<close>
    for N x22
    using distinct_mset_dom[of N] by (cases \<open>C\<in>#dom_m N\<close>;cases \<open>x22\<in>#dom_m N\<close>; cases \<open>C=x22\<close>; auto dest: multi_member_split; fail)+
  have [iff]: \<open>C \<in># add_mset C' (remove1_mset C' (dom_m N)) - {#C, C#} \<longleftrightarrow> False\<close> for C' N
    using distinct_mset_dom[of N] by (cases \<open>C\<in>#dom_m N\<close>;cases \<open>C'\<in>#dom_m N\<close>; cases \<open>C=C'\<close>; auto dest: multi_member_split)
  show ?thesis
  using assms unfolding subsume_or_strengthen_def
  apply refine_vcg+
  subgoal by auto
  subgoal for M b N ba NE bb UE bc NEk bd UEk be NS bf US bg NS0 bh US0 bi WS bj Q occs
    apply (cases s)
    subgoal for C'
      apply (simp only: Let_def subsumption.case(1))
      apply refine_vcg
      subgoal
        apply (subgoal_tac \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>*
          (M, N, NE, UE, NEk, UEk, NS, US, NS0, US0, WS, Q, occs)
          (M, fmdrop C (if \<not> irred N C' \<and> irred N C then fmupd C' (N \<propto> C', True) N else N),
             NE, UE, NEk, UEk, NS,
             (if irred N C then add_mset (mset (N \<propto> C)) else id) US,
             (if \<not> irred N C then add_mset (mset (N \<propto> C)) else id) NS0, US0, WS, Q,  occs)\<close>)
        subgoal
          by (frule rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
           presburger
        subgoal by auto (auto 8 8 simp: subsume_or_strengthen_pre_def cdcl_twl_subsumed_l.simps fmdrop_fmupd
           intro!: cdcl_twl_inprocessing_l.intros(3) r_into_rtranclp dest!: in_diffD)
        done
      subgoal by auto (auto 8 8 simp: subsume_or_strengthen_pre_def cdcl_twl_subsumed_l.simps fmdrop_fmupd
           intro!: cdcl_twl_inprocessing_l.intros(3) r_into_rtranclp dest!: in_diffD)
      subgoal by auto
      subgoal by auto
      subgoal by auto  (auto 8 8 simp: subsume_or_strengthen_pre_def cdcl_twl_subsumed_l.simps fmdrop_fmupd
           intro!: cdcl_twl_inprocessing_l.intros(3) r_into_rtranclp dest!: in_diffD)
      subgoal by auto 
      subgoal by auto
      done
    subgoal
      apply (clarsimp simp only: strengthen_clause_def subsumption.case Let_def
        intro!: ASSERT_leI impI)
      apply (intro ASSERT_leI intro_spec_iff[THEN iffD2]; (split if_splits[of _ \<open>_ = (2::nat)\<close>])?; (intro conjI impI ballI ASSERT_leI)?)
      subgoal by (auto simp: length_remove1 strengthen_clause_pre_def subsume_or_strengthen_pre_def)
      subgoal
        by (auto simp: strengthen_clause_def subsume_or_strengthen_pre_def length_remove1 Let_def
           subresolution_strengtheningI_binary
          intro!: ASSERT_leI
          dest: in_diffD)
      subgoal
        by (auto simp: strengthen_clause_def subsume_or_strengthen_pre_def length_remove1 Let_def
           intro: subresolution_strengtheningI_binary
          intro!: ASSERT_leI
          dest: in_diffD)
      subgoal
        by (auto simp: strengthen_clause_def subsume_or_strengthen_pre_def length_remove1 Let_def
          intro!: subresolution_strengtheningI(1)[of \<open>strengthened_by s\<close>]
          subresolution_strengtheningI(2)[of \<open>strengthened_by s\<close>]
          subresolution_strengtheningI(3-)
          intro!: ASSERT_leI
          dest: in_diffD)
      done
    subgoal
      by (auto dest: in_diffD)
    done
  done
qed

lemma
  assumes \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T\<close>
  shows
    rtranclp_cdcl_twl_inprocessing_l_count_decided:
    \<open>count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close> (is ?A) and
    rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l:
    \<open>clauses_to_update_l T = clauses_to_update_l S\<close> (is ?B) and
    rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated:
    \<open>set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq> set (get_all_mark_of_propagated (get_trail_l S)) \<union> {0}\<close> (is ?C)
proof -
  have [dest]:
    \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close> 
    \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> clauses_to_update_l T = clauses_to_update_l S\<close>
    \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq> set (get_all_mark_of_propagated (get_trail_l S)) \<union> {0}\<close> for S T
    by (auto simp: cdcl_twl_inprocessing_l.simps cdcl_twl_subsumed_l.simps
      cdcl_twl_unitres_l.simps cdcl_twl_subresolution_l.simps cdcl_twl_unitres_true_l.simps
      cdcl_twl_pure_remove_l.simps)
      (*set (get_all_mark_of_propagated (get_trail_l T))*)
  show ?A ?B ?C
    using assms
    by (induction rule: rtranclp_induct; auto; fail)+
qed


lemma cdcl_twl_inprocessing_l_twl_st_l0:
  assumes \<open>cdcl_twl_inprocessing_l S U\<close> and
    \<open>(S, T) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs T\<close> and
    \<open>twl_list_invs S\<close>
 obtains V where
   \<open>(U, V) \<in> twl_st_l None\<close> and
   \<open>cdcl_twl_unitres T V \<or> cdcl_twl_unitres_true T V \<or> cdcl_twl_subsumed T V \<or>
   cdcl_twl_subresolution T V \<or> cdcl_twl_pure_remove T V\<close>
  using assms
  apply (induction rule: cdcl_twl_inprocessing_l.induct)
  using cdcl_twl_unitres_l_cdcl_twl_unitres apply blast
  using cdcl_twl_unitres_true_l_cdcl_twl_unitres_true apply blast
  using cdcl_twl_subsumed_l_cdcl_twl_subsumed apply blast
  using cdcl_twl_subresolution_l_cdcl_twl_subresolution apply blast
  using cdcl_twl_pure_remove_l_cdcl_twl_pure_remove by blast


lemma cdcl_twl_unitres_l_list_invs:
  \<open>cdcl_twl_unitres_l S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  by (induction rule: cdcl_twl_unitres_l.induct)
   (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
    ran_m_mapsto_upd
    dest: in_diffD)


lemma cdcl_twl_inprocessing_l_twl_list_invs:
  assumes \<open>cdcl_twl_inprocessing_l S U\<close> and
    \<open>twl_list_invs S\<close>
  shows
    \<open>twl_list_invs U\<close>
  using assms by (induction rule: cdcl_twl_inprocessing_l.induct)
   (auto simp: cdcl_twl_unitres_True_l_list_invs
    cdcl_twl_unitres_l_list_invs cdcl_twl_subsumed_l_list_invs
    cdcl_twl_subresolution_l_list_invs cdcl_twl_pure_remove_l_twl_list_invs)

lemma rtranclp_cdcl_twl_inprocessing_l_twl_list_invs:
  assumes \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S U\<close> and
    \<open>twl_list_invs S\<close>
  shows
    \<open>twl_list_invs U\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto simp: cdcl_twl_inprocessing_l_twl_list_invs)

lemma cdcl_twl_inprocessing_l_twl_st_l:
  assumes \<open>cdcl_twl_inprocessing_l S U\<close> and
    \<open>(S, T) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs T\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  obtains V where
    \<open>(U, V) \<in> twl_st_l None\<close> and
    \<open>cdcl_twl_unitres T V \<or> cdcl_twl_unitres_true T V \<or> cdcl_twl_subsumed T V \<or>
    cdcl_twl_subresolution T V \<or> cdcl_twl_pure_remove T V\<close> and
    \<open>twl_struct_invs V\<close> and
    \<open>twl_list_invs U\<close>and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of V)\<close>
  apply (rule cdcl_twl_inprocessing_l_twl_st_l0[OF assms(1-4)])
  subgoal premises p for V
    using p(2-) cdcl_twl_inprocessing_l_twl_list_invs[OF assms(1)] apply -
    apply (rule that[of V])
    apply (auto intro: cdcl_twl_unitres_true_twl_struct_invs
      cdcl_twl_unitres_struct_invs assms cdcl_twl_subsumed_struct_invs
      cdcl_twl_subresolution_twl_struct_invs cdcl_twl_unitres_twl_stgy_invs
      cdcl_twl_subresolution_twl_stgy_invs cdcl_twl_unitres_true_twl_stgy_invs
      cdcl_twl_subsumed_twl_stgy_invs
      cdcl_twl_pure_remove_twl_struct_invs)
    apply (metis assms(3) assms(5) cdcl_twl_inp.intros cdcl_twl_inp_invs(3) state\<^sub>W_of_def)+
    done
  done


lemma rtranclp_cdcl_twl_inprocessing_l_twl_st_l:
  assumes \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S U\<close> and
    \<open>(S, T) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs T\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  obtains V where
    \<open>(U, V) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs V\<close> and
    \<open>twl_list_invs U\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of V)\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by blast
  subgoal premises p for X Y
    apply (rule p(3)[OF _ p(5-)])
    apply (rule cdcl_twl_inprocessing_l_twl_st_l[of X Y, OF p(2)]; assumption?)
    apply (rule p(4))
    apply assumption+
    done
  done

text \<open>Forward subsumption is done in two steps. First we work on the binary clauses
(also deduplicationg them), and only then we work on other clauses.

Short version:
  \<^enum> first, we work only on binary clauses ;
  \<^enum> second, we work on all other clauses.


Longer version: We already implement the functions towards how we will need implement it (although
this just slightly more general that what would be needed to implement the Splatz version).

The \<^term>\<open>forward_all\<close> schedules all clauses. This functions leaves the work to subsume one clause to
the function \<^term>\<open>try_to_subsume\<close>. This is the function that is slightly more specialized: it allows
to test subsumption on \<^term>\<open>n\<close> different times (potentially only once). Finally it is the funtion
\<^term>\<open>forward_one\<close> that compares two clauses and checks for subsumption. We assume that no new unit
clause is produced (as only binary clauses can produce new clauses).

The names follow the corresponding functions from CaDiCaL. In newer minimal solvers from Armin (like
satch or Gimsatul), only vivification is implemented.
\<close>

definition clause_remove_duplicate_clause_pre :: \<open>_\<close> where
  \<open>clause_remove_duplicate_clause_pre C S \<longleftrightarrow> (\<exists>C' S'.
  (S,S') \<in> twl_st_l None \<and>
  mset ((get_clauses_l S) \<propto> C) = mset ((get_clauses_l S) \<propto> C') \<and>
  (\<not>irred (get_clauses_l S) C' \<longrightarrow> \<not>irred (get_clauses_l S) C) \<and>
  C' \<notin> set (get_all_mark_of_propagated (get_trail_l S)) \<and>
  C \<in># dom_m (get_clauses_l S) \<and>
  clauses_to_update_l S = {#} \<and>
  C' \<in># dom_m (get_clauses_l S) \<and>
  C \<notin> set (get_all_mark_of_propagated (get_trail_l S)) \<and>
  C \<noteq> C' \<and>
  twl_list_invs S \<and> twl_struct_invs S' \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S'))\<close>

definition clause_remove_duplicate_clause :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>clause_remove_duplicate_clause C = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
   ASSERT (clause_remove_duplicate_clause_pre C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
   RETURN (M, fmdrop C N, D, NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS, (if irred N C then id else add_mset (mset (N \<propto> C))) US, N0, U0, WS, Q)
 })\<close>

definition clause_remove_duplicate_clause_spec where
  \<open>clause_remove_duplicate_clause_spec C S T \<longleftrightarrow> cdcl_twl_inprocessing_l S T \<and>
    get_clauses_l T = fmdrop C (get_clauses_l S) \<and> get_trail_l T = get_trail_l S\<close>

lemma clause_remove_duplicate_clause:
  assumes \<open>clause_remove_duplicate_clause_pre C S\<close>
  shows \<open>clause_remove_duplicate_clause C S \<le> SPEC(clause_remove_duplicate_clause_spec C S)\<close>
  using assms
  unfolding clause_remove_duplicate_clause_def clause_remove_duplicate_clause_pre_def
    clause_remove_duplicate_clause_spec_def apply -
  apply normalize_goal+
  apply (cases S; hypsubst)
  unfolding prod.simps
  apply (intro ASSERT_leI, rule_tac x=x in exI, rule_tac x=xa in exI)
  apply auto []
  apply simp
  apply (intro impI conjI cdcl_twl_inprocessing_l.intros(3))
  using cdcl_twl_subsumed_l.intros[of \<open>get_clauses_l S\<close> _ C \<open>get_trail_l S\<close> \<open>get_conflict_l S\<close>
    \<open>get_unkept_init_clauses_l S\<close> \<open>get_unkept_learned_clss_l S\<close> \<open>get_kept_init_clauses_l S\<close> \<open>get_kept_learned_clss_l S\<close>
      \<open>get_subsumed_init_clauses_l S\<close> \<open>get_subsumed_learned_clauses_l S\<close> \<open>get_init_clauses0_l S\<close> \<open>get_learned_clauses0_l S\<close>
      \<open>literals_to_update_l S\<close>]
  apply (auto simp: )
  done


definition binary_clause_subres_lits_pre :: \<open>_\<close> where
  \<open>binary_clause_subres_lits_pre C L L' S \<longleftrightarrow> (\<exists>C' S'.
  (S,S') \<in> twl_st_l None \<and>
   mset (get_clauses_l S \<propto> C) = {#L, -L'#} \<and> mset (get_clauses_l S \<propto> C')= {#L, L'#} \<and>
  get_conflict_l S = None \<and>
  clauses_to_update_l S = {#} \<and>
  C \<in># dom_m (get_clauses_l S) \<and>
  C' \<in># dom_m (get_clauses_l S) \<and>
  count_decided (get_trail_l S) = 0 \<and>
  undefined_lit (get_trail_l S) L \<and>
  C \<notin> set (get_all_mark_of_propagated (get_trail_l S)) \<and>
  twl_list_invs S \<and>
  twl_struct_invs S' \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S'))\<close>

definition binary_clause_subres :: \<open>nat \<Rightarrow> 'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>binary_clause_subres C L L' = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
   ASSERT (binary_clause_subres_lits_pre C L L' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
   RETURN (Propagated L 0 # M, fmdrop C N, D, NE, UE,
      (if irred N C then add_mset {#L#} else id) NEk, (if irred N C then id else add_mset {#L#}) UEk,
      (if irred N C then add_mset (mset (N \<propto> C)) else id) NS, (if irred N C then id else add_mset (mset (N \<propto> C))) US,
       N0, U0, WS, add_mset (-L) Q)
 })\<close>


lemma binary_clause_subres_binary_clause:
  assumes \<open>binary_clause_subres_lits_pre C L L' S\<close>
  shows \<open>binary_clause_subres C L L' S \<le> SPEC(cdcl_twl_inprocessing_l S)\<close>
  using assms unfolding binary_clause_subres_def binary_clause_subres_lits_pre_def binary_clause_subres_lits_pre_def apply -
  apply normalize_goal+
  subgoal for C' xa
    apply (cases S; hypsubst)
    unfolding prod.simps
    apply (intro ASSERT_leI exI[of _ C'] exI[of _ xa])
    apply auto []
    using cdcl_twl_subresolution_l.intros(2,4,6,8)[of C' \<open>get_clauses_l S\<close> C \<open>L'\<close> \<open>{#L#}\<close>  \<open>{#L#}\<close> \<open>get_trail_l S\<close>
      L \<open>get_unkept_init_clauses_l S\<close> \<open>get_unkept_learned_clss_l S\<close> \<open>get_kept_init_clauses_l S\<close> \<open>get_kept_learned_clss_l S\<close>
      \<open>get_subsumed_init_clauses_l S\<close> \<open>get_subsumed_learned_clauses_l S\<close> \<open>get_init_clauses0_l S\<close> \<open>get_learned_clauses0_l S\<close>
      \<open>literals_to_update_l S\<close>, unfolded assms, simplified]
    apply (cases \<open>irred (get_clauses_l S) C'\<close>)
    apply (auto simp add: add_mset_commute cdcl_twl_inprocessing_l.intros(4))
    done
   done

definition deduplicate_binary_clauses_pre where
  \<open>deduplicate_binary_clauses_pre L S \<longleftrightarrow>
    (\<exists>T. (S,T) \<in> twl_st_l None \<and> set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and> count_decided (get_trail_l S) = 0 \<and>
      clauses_to_update_l S = {#} \<and> twl_list_invs S \<and> twl_struct_invs T \<and> L \<in># all_init_lits_of_l S)\<close>

definition deduplicate_binary_clauses_correctly_marked where
  \<open>deduplicate_binary_clauses_correctly_marked L xs0 xs CS T \<longleftrightarrow>
     (\<forall>C L' b. CS L' = Some (C, b) \<longrightarrow> (C \<in># dom_m (get_clauses_l T) \<and> C\<in># xs0 - xs \<and> mset (get_clauses_l T \<propto> C) = {#L,L'#} \<and> irred (get_clauses_l T) C = b))\<close>

definition deduplicate_binary_clauses_inv
  :: \<open>'v literal \<Rightarrow> _ \<Rightarrow> 'v twl_st_l \<Rightarrow> bool \<times> nat multiset \<times> _ \<times> 'v twl_st_l \<Rightarrow> bool\<close>
where
\<open>deduplicate_binary_clauses_inv L xs0 S = (\<lambda>(abort, xs, CS, T). 
  \<exists>S'. (S,S') \<in> twl_st_l None \<and> twl_struct_invs S' \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
    cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and> xs \<subseteq># xs0 \<and>
    (\<not>abort \<longrightarrow> deduplicate_binary_clauses_correctly_marked L xs0 xs CS T) \<and>
    twl_list_invs S \<and>
    count_decided (get_trail_l S) = 0 \<and>
    clauses_to_update_l S = {#} \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
    (\<not>abort \<longrightarrow> undefined_lit (get_trail_l T) L))\<close>

lemma deduplicate_binary_clauses_inv_alt_def:
\<open>deduplicate_binary_clauses_inv L xs0 S = (\<lambda>(abort, xs, CS, T).
  \<exists>S' T'. (S,S') \<in> twl_st_l None \<and> twl_struct_invs S' \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
     (T,T') \<in> twl_st_l None \<and> twl_struct_invs T' \<and>  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T') \<and>
   cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and> xs \<subseteq># xs0 \<and>
   (\<not>abort \<longrightarrow> deduplicate_binary_clauses_correctly_marked L xs0 xs CS T) \<and>
  twl_list_invs S \<and>
  count_decided (get_trail_l S) = 0 \<and>
  clauses_to_update_l S = {#} \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
  twl_list_invs T \<and>
  count_decided (get_trail_l T) = 0 \<and>
  clauses_to_update_l T = {#} \<and>
  set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq> {0} \<and>
  (\<not>abort \<longrightarrow>undefined_lit (get_trail_l T) L))\<close>
  unfolding deduplicate_binary_clauses_inv_def
  apply (intro ext iffI)
  unfolding case_prod_beta apply normalize_goal+
  apply (rule_tac x=xa in exI)
  apply (frule rtranclp_cdcl_twl_inprocessing_l_twl_st_l; assumption?)
  apply (rule_tac x=V in exI)
  apply (auto 5 3 dest: rtranclp_cdcl_twl_inprocessing_l_count_decided
    rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l rtranclp_cdcl_twl_inprocessing_l_twl_list_invs
    rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated
    elim: rtranclp_cdcl_twl_inprocessing_l_twl_st_l)[]
  unfolding case_prod_beta apply normalize_goal+
  apply (rule_tac x=xa in exI)
  apply (auto 5 3 dest: rtranclp_cdcl_twl_inprocessing_l_count_decided
    rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l rtranclp_cdcl_twl_inprocessing_l_twl_list_invs
    rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated rtranclp_cdcl_twl_inprocessing_l_twl_st_l)[]
  done

lemma deduplicate_binary_clauses_inv_alt_def2:
  \<open> deduplicate_binary_clauses_pre L S \<Longrightarrow>
  deduplicate_binary_clauses_inv L xs0 S = (\<lambda>(abort, xs, CS, T). 
    cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and> xs \<subseteq># xs0 \<and>
    (\<not>abort \<longrightarrow> deduplicate_binary_clauses_correctly_marked L xs0 xs CS T) \<and>
    (\<not>abort \<longrightarrow> undefined_lit (get_trail_l T) L))\<close>
  unfolding deduplicate_binary_clauses_pre_def deduplicate_binary_clauses_inv_def case_prod_beta
  apply (intro ext iffI)
  apply normalize_goal+
  apply simp
  apply normalize_goal+
  apply (rule_tac x=x in exI)
  apply simp
  done


definition deduplicate_binary_clauses :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>deduplicate_binary_clauses L S = do {
    ASSERT (deduplicate_binary_clauses_pre L S);
    let CS = (\<lambda>_. None);
    xs \<leftarrow> SPEC (\<lambda>CS. \<forall>C. (C \<in># CS \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C)) \<and> distinct_mset CS);
    (_, _, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup>deduplicate_binary_clauses_inv L xs S\<^esup> (\<lambda>(abort, xs, CS, S). \<not>abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None)
      (\<lambda>(abort, xs, CS, S).
      do {
         C \<leftarrow> SPEC (\<lambda>C. C \<in># xs);
         if C \<notin># dom_m (get_clauses_l S) \<or> length (get_clauses_l S \<propto> C) \<noteq> 2 then
           RETURN (abort, xs - {#C#}, CS, S)
         else do {
           L' \<leftarrow> SPEC (\<lambda>L'. mset (get_clauses_l S \<propto> C) = {#L, L'#});
           if defined_lit (get_trail_l S) L' then do {
             U \<leftarrow> simplify_clause_with_unit_st C S;
             ASSERT (cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S U);
             RETURN (defined_lit (get_trail_l U) L, xs - {#C#}, CS, U)
           }
           else if CS L' \<noteq> None then do {
             let C' = (if (\<not>snd (the (CS L')) \<longrightarrow> \<not>irred (get_clauses_l S) C) then C else fst (the (CS L')));
             let CS = (if (\<not>snd (the (CS L')) \<longrightarrow> \<not>irred (get_clauses_l S) C) then CS else CS (L' := Some (C, irred (get_clauses_l S) C)));
             S \<leftarrow> clause_remove_duplicate_clause C' S;
             RETURN (abort, xs - {#C#}, CS, S)
           } else if CS (-L') \<noteq> None then do {
             S \<leftarrow> binary_clause_subres C L (-L') S;
             RETURN (True, xs - {#C#}, CS, S)
           } else do {
             RETURN (abort, xs - {#C#}, CS (L' := Some (C, irred (get_clauses_l S) C)), S)
           }
        }
      })
      (defined_lit (get_trail_l S) L, xs, CS, S);
   RETURN S
}\<close>

lemma deduplicate_binary_clauses_correctly_marked_remove1:
  \<open>deduplicate_binary_clauses_correctly_marked L xs0 xs CS T \<Longrightarrow> distinct_mset xs0 \<Longrightarrow> xs \<subseteq># xs0 \<Longrightarrow>
  deduplicate_binary_clauses_correctly_marked L xs0 (remove1_mset C xs) CS T\<close>
  apply (cases \<open>C \<in># xs\<close>)
  apply (auto simp: deduplicate_binary_clauses_correctly_marked_def dest!: multi_member_split)
  apply (metis Multiset.diff_add add_mset_add_single in_diffD)+
  done

lemma fmdrop_eq_dom_m_iff: \<open>C \<in># dom_m N \<Longrightarrow> fmdrop C N = fmdrop C' N \<longleftrightarrow> C = C'\<close>
  by (metis distinct_mset_add_mset distinct_mset_dom dom_m_fmdrop in_remove1_mset_neq insert_DiffM)

lemma deduplicate_binary_clauses_inv_cdcl_twl_unitres_l:
  \<open>cdcl_twl_inprocessing_l bb xc \<Longrightarrow> deduplicate_binary_clauses_pre L S \<Longrightarrow>
  deduplicate_binary_clauses_inv L x S (False, aa, ab, bb) \<Longrightarrow>
  xa \<in># aa \<Longrightarrow>
      xa \<in># dom_m (get_clauses_l xc) \<Longrightarrow>
      defined_lit (get_trail_l bb) xb \<Longrightarrow>
      \<forall>C. C \<in># x \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C) \<Longrightarrow>
      distinct_mset x \<Longrightarrow>
      \<not> a \<Longrightarrow>
      aa \<noteq> {#} \<Longrightarrow>
      get_conflict_l bb = None \<Longrightarrow>
      set (get_all_mark_of_propagated (get_trail_l xc))
      \<subseteq> insert 0 (set (get_all_mark_of_propagated (get_trail_l bb))) \<Longrightarrow>
      \<forall>L\<in>set (get_clauses_l xc \<propto> xa). undefined_lit (get_trail_l xc) L \<Longrightarrow>
     dom_m (get_clauses_l bb) = dom_m (get_clauses_l xc) \<Longrightarrow>
     \<forall>C'\<in>#dom_m (get_clauses_l xc). xa \<noteq> C' \<longrightarrow> fmlookup (get_clauses_l bb) C' = fmlookup (get_clauses_l xc) C' \<Longrightarrow>
      deduplicate_binary_clauses_inv L x S
    (defined_lit (get_trail_l xc) L, remove1_mset xa aa, ab, xc)\<close>

    apply (subst deduplicate_binary_clauses_inv_alt_def2, assumption)
    apply (subst (asm)deduplicate_binary_clauses_inv_alt_def2, assumption)
    unfolding prod.simps deduplicate_binary_clauses_pre_def
    apply normalize_goal+
    apply (auto dest: )[]
    apply (clarsimp simp: deduplicate_binary_clauses_correctly_marked_def)
    apply (intro conjI impI allI)
    apply (auto dest: in_diffD simp: distinct_mset_in_diff)
    apply (metis)+
    done

lemma deduplicate_binary_clauses_inv_deleted:
  \<open>deduplicate_binary_clauses_pre L S \<Longrightarrow>
      deduplicate_binary_clauses_inv L x S (False, aa, ab, bb) \<Longrightarrow>
      s = (False, aa, ab, bb) \<Longrightarrow>
      b = (aa, ab, bb) \<Longrightarrow>
      ba = (ab, bb) \<Longrightarrow>
      xa \<in># aa \<Longrightarrow>
      xa \<in># dom_m (get_clauses_l bb) \<Longrightarrow>
      mset (get_clauses_l bb \<propto> xa) = {#L, xb#} \<Longrightarrow>
      defined_lit (get_trail_l bb) xb \<Longrightarrow>
      \<forall>C. C \<in># x \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C) \<Longrightarrow>
      distinct_mset x \<Longrightarrow>
      \<not> a \<Longrightarrow>
      aa \<noteq> {#} \<Longrightarrow>
      get_conflict_l bb = None \<Longrightarrow>
      set (get_all_mark_of_propagated (get_trail_l xc)) \<subseteq> insert 0 (set (get_all_mark_of_propagated (get_trail_l bb))) \<Longrightarrow>
      \<forall>C'\<in>#dom_m (get_clauses_l xc). xa \<noteq> C' \<longrightarrow> fmlookup (get_clauses_l bb) C' = fmlookup (get_clauses_l xc) C' \<Longrightarrow>
      xa \<in># dom_m (get_clauses_l xc) \<longrightarrow> (\<forall>L\<in>set (get_clauses_l xc \<propto> xa). undefined_lit (get_trail_l xc) L) \<Longrightarrow>
      remove1_mset xa (dom_m (get_clauses_l bb)) = dom_m (get_clauses_l xc) \<Longrightarrow>
      cdcl_twl_inprocessing_l bb xc \<Longrightarrow>
      deduplicate_binary_clauses_inv L x S (defined_lit (get_trail_l xc) L, remove1_mset xa aa, ab, xc)\<close>

    apply (subst deduplicate_binary_clauses_inv_alt_def2, assumption)
    apply (subst (asm)deduplicate_binary_clauses_inv_alt_def2, assumption)
    unfolding prod.simps deduplicate_binary_clauses_pre_def
    apply normalize_goal+
    apply (auto dest: )[]
    apply (clarsimp simp: deduplicate_binary_clauses_correctly_marked_def)
    apply (intro conjI impI allI)
    apply (auto dest: in_diffD simp: distinct_mset_in_diff)
    apply (metis in_dom_m_lookup_iff in_remove1_msetI)
    apply (metis in_dom_m_lookup_iff insert_DiffM insert_iff set_mset_add_mset_insert)
    apply (metis in_dom_m_lookup_iff insert_DiffM insert_iff set_mset_add_mset_insert)
    apply (metis in_dom_m_lookup_iff insert_DiffM insert_iff set_mset_add_mset_insert)
    apply (clarsimp simp: deduplicate_binary_clauses_correctly_marked_def)
    apply (intro conjI impI allI)
    apply (auto dest: in_diffD simp: distinct_mset_in_diff)
    apply (metis in_dom_m_lookup_iff in_remove1_msetI)
    apply (metis in_dom_m_lookup_iff insert_DiffM insert_iff set_mset_add_mset_insert)
    apply (metis in_dom_m_lookup_iff insert_DiffM insert_iff set_mset_add_mset_insert)
    apply (metis in_dom_m_lookup_iff insert_DiffM insert_iff set_mset_add_mset_insert)
    done

lemma deduplicate_binary_clauses:
  assumes \<open>deduplicate_binary_clauses_pre L S\<close>
  shows \<open>deduplicate_binary_clauses L S \<le> SPEC(cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S)\<close>
proof -
  have clause_remove_duplicate_clause_pre:
    \<open>clause_remove_duplicate_clause_pre (if \<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa then xa
      else fst (the (ab xb))) bb\<close>
    if
      pre: \<open>deduplicate_binary_clauses_pre L S\<close> and
      x_spec: \<open>\<forall>C. (C \<in># x \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C)) \<and> distinct_mset x\<close> and
      inv: \<open>deduplicate_binary_clauses_inv L x S s\<close> and
      abort: \<open>case s of (abort, xs, CS, S) \<Rightarrow> \<not> abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      st: \<open>s = (a, b)\<close>
      \<open>b = (aa, ba)\<close>
      \<open>ba = (ab, bb)\<close> and
      aa: \<open>xa \<in># aa\<close> and
      xa: \<open>\<not> (xa \<notin># dom_m (get_clauses_l bb) \<or> length (get_clauses_l bb \<propto> xa) \<noteq> 2)\<close> and
      xa_L: \<open>mset (get_clauses_l bb \<propto> xa) = {#L, xb#}\<close> and
      \<open>undefined_lit (get_trail_l bb) xb\<close> and
      ab: \<open>ab xb \<noteq> None\<close>
    for x s a b aa ba ab bb xa xb
  proof -
    let ?C = \<open>(if \<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa then xa
      else fst (the (ab xb)))\<close>
    let ?C' = \<open>(if \<not>(\<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa) then xa
      else fst (the (ab xb)))\<close>
    obtain T' where
      T': \<open>(bb, T') \<in> twl_st_l None \<and> twl_struct_invs T' \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T')\<close>
      \<open>twl_list_invs bb\<close>
      using inv pre xa abort apply -
      unfolding clause_remove_duplicate_clause_pre_def st prod.simps deduplicate_binary_clauses_inv_alt_def
      by blast
    have H: \<open>ab xb = Some (C, b) \<Longrightarrow> C \<noteq> 0 \<and> C \<notin> set (get_all_mark_of_propagated (get_trail_l bb)) \<and>
      C \<in># dom_m (get_clauses_l bb) \<and>
      C \<in># x - aa \<and> mset (get_clauses_l bb \<propto> C) = {#L, xb#} \<and> irred (get_clauses_l bb) C = b\<close>
      \<open>clauses_to_update_l bb = {#}\<close>
      \<open>xa \<notin> set (get_all_mark_of_propagated (get_trail_l bb))\<close> for C b
      using inv pre xa abort T' apply -
      unfolding clause_remove_duplicate_clause_pre_def st prod.simps
      apply (clarsimp_all simp: deduplicate_binary_clauses_inv_alt_def deduplicate_binary_clauses_correctly_marked_def
        twl_list_invs_def)
      apply (intro conjI impI)
      apply (metis neq0_conv)
      apply (metis empty_iff in_mono insert_iff)
      by (metis empty_iff singletonD subset_singletonD)

    show ?thesis
      using pre H ab xa xa_L x_spec aa T' apply -
      unfolding clause_remove_duplicate_clause_pre_def st
      apply (rule exI[of _ \<open>?C'\<close>])
      apply (rule exI[of _ \<open>T'\<close>])
      apply (auto simp: deduplicate_binary_clauses_inv_alt_def deduplicate_binary_clauses_correctly_marked_def)
      apply (meson distinct_mset_in_diff)+
      done
  qed
  have clause_remove_duplicate_clause_post:
    \<open>deduplicate_binary_clauses_inv L x S (a, remove1_mset xa aa, if \<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa then ab
      else ab(xb \<mapsto> (xa, irred (get_clauses_l bb) xa)), xc)\<close>
    if
      \<open>deduplicate_binary_clauses_pre L S\<close> and
      \<open>\<forall>C. (C \<in># x \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C)) \<and> distinct_mset x\<close> and
      \<open>deduplicate_binary_clauses_inv L x S s\<close> and
      \<open>case s of (abort, xs, CS, S) \<Rightarrow> \<not> abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      st: \<open>s = (a, b)\<close>
        \<open>b = (aa, ba)\<close>
        \<open>ba = (ab, bb)\<close> and
      \<open>xa \<in># aa\<close> and
      \<open>\<not> (xa \<notin># dom_m (get_clauses_l bb) \<or> length (get_clauses_l bb \<propto> xa) \<noteq> 2)\<close> and
      \<open>mset (get_clauses_l bb \<propto> xa) = {#L, xb#}\<close> and
      \<open>undefined_lit (get_trail_l bb) xb\<close> and
      \<open>ab xb \<noteq> None\<close> and
      \<open>clause_remove_duplicate_clause_spec (if \<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa then xa
      else fst (the (ab xb))) bb xc\<close>
      for x s a b aa ba ab bb xa xb xc
  proof -
    let ?C = \<open>(if \<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa then xa
      else fst (the (ab xb)))\<close>
    let ?C' = \<open>(if \<not>(\<not> snd (the (ab xb)) \<longrightarrow> \<not> irred (get_clauses_l bb) xa) then xa
      else fst (the (ab xb)))\<close>
    show ?thesis
      using that
      apply (subst deduplicate_binary_clauses_inv_alt_def2)
      apply assumption
      apply (subst (asm)deduplicate_binary_clauses_inv_alt_def)
      unfolding st prod.simps clause_remove_duplicate_clause_spec_def
      apply normalize_goal+
      apply (intro conjI)
      apply (auto simp add: deduplicate_binary_clauses_correctly_marked_def
        distinct_mset_remove1_All distinct_mset_dom distinct_mset_in_diff dest: in_diffD)
      apply (metis in_multiset_nempty member_add_mset)
      by (meson Duplicate_Free_Multiset.distinct_mset_mono distinct_mem_diff_mset union_single_eq_member)
  qed
  have binary_clause_subres_lits_pre: \<open>binary_clause_subres_lits_pre xa L (-xb) bb\<close>
    if
      pre: \<open>deduplicate_binary_clauses_pre L S\<close> and
      \<open>\<forall>C. (C \<in># x \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C)) \<and> distinct_mset x\<close> and
      inv: \<open>deduplicate_binary_clauses_inv L x S s\<close> and
      abort: \<open>case s of (abort, xs, CS, S) \<Rightarrow> \<not> abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      st: \<open>s = (a, b)\<close>
        \<open>b = (aa, ba)\<close>
        \<open>ba = (ab, bb)\<close> and
      \<open>xa \<in># aa\<close> and
      \<open>\<not> (xa \<notin># dom_m (get_clauses_l bb)\<or> length (get_clauses_l bb \<propto> xa) \<noteq> 2)\<close> and
      \<open>mset (get_clauses_l bb \<propto> xa) = {#L, xb#}\<close> and
      \<open>undefined_lit (get_trail_l bb) xb\<close> and
      \<open>\<not> ab xb \<noteq> None\<close> and
      xb: \<open>ab (- xb) \<noteq> None\<close>
    for x s a b aa ba ab bb xa xb
  proof -
    obtain T' where
      T': \<open>(bb, T') \<in> twl_st_l None\<close> \<open>twl_struct_invs T'\<close>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T')\<close>
      using inv pre xb abort apply -
      unfolding clause_remove_duplicate_clause_pre_def st prod.simps deduplicate_binary_clauses_inv_alt_def
      apply normalize_goal+
      by blast
    have H: \<open>ab (- xb) = Some (C, b) \<Longrightarrow> C \<noteq> 0 \<and> C \<notin> set (get_all_mark_of_propagated (get_trail_l bb)) \<and>
      C \<in># dom_m (get_clauses_l bb) \<and>
      C \<in># x - aa \<and> mset (get_clauses_l bb \<propto> C) = {#L, (- xb)#} \<and> irred (get_clauses_l bb) C = b\<close>
      \<open>clauses_to_update_l bb = {#}\<close>
      \<open>xa \<notin> set (get_all_mark_of_propagated (get_trail_l bb))\<close> for C b
      using inv pre xb abort apply -
      unfolding clause_remove_duplicate_clause_pre_def st prod.simps deduplicate_binary_clauses_inv_alt_def
      apply normalize_goal+
      apply (clarsimp_all simp: deduplicate_binary_clauses_inv_alt_def deduplicate_binary_clauses_correctly_marked_def
        twl_list_invs_def)
      apply (intro conjI)
      apply (metis neq0_conv)
      apply (metis empty_iff in_mono insert_iff)
      by (metis in_mono singletonD that(9))
    show ?thesis
      using that H T' apply -
      unfolding binary_clause_subres_lits_pre_def
      by (rule exI[of _ \<open>fst (the (ab (-xb)))\<close>], rule exI[of _ T'])
       (auto simp: deduplicate_binary_clauses_inv_alt_def deduplicate_binary_clauses_correctly_marked_def)
  qed
  have new_lit: \<open>deduplicate_binary_clauses_inv L x S
    (a, remove1_mset xa aa, ab(xb \<mapsto> (xa, irred (get_clauses_l bb) xa)), bb)\<close>
    if
      \<open>deduplicate_binary_clauses_pre L S\<close> and
      \<open>\<forall>C. (C \<in># x \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<longrightarrow> L \<in> set (get_clauses_l S \<propto> C)) \<and> distinct_mset x\<close> and
      \<open>deduplicate_binary_clauses_inv L x S s\<close> and
      \<open>case s of
      (abort, xs, CS, S) \<Rightarrow> \<not> abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      st: \<open>s = (a, b)\<close>
        \<open>b = (aa, ba)\<close>
        \<open>ba = (ab, bb)\<close> and
      \<open>xa \<in># aa\<close> and
      \<open>\<not> (xa \<notin># dom_m (get_clauses_l bb) \<or> length (get_clauses_l bb \<propto> xa) \<noteq> 2)\<close> and
      \<open>mset (get_clauses_l bb \<propto> xa) = {#L, xb#}\<close> and
      \<open>undefined_lit (get_trail_l bb) xb\<close> and
      \<open>\<not> (ab xb \<noteq> None)\<close> and
      \<open>\<not> ab (- xb) \<noteq> None\<close>
      for x s a b aa ba ab bb xa xb
  proof -
    show ?thesis
      using that unfolding prod.simps st apply -
      apply (subst deduplicate_binary_clauses_inv_alt_def2, assumption)
      apply (subst (asm) deduplicate_binary_clauses_inv_alt_def2, assumption)
      apply normalize_goal+
      apply (auto simp: deduplicate_binary_clauses_correctly_marked_def distinct_mset_in_diff
        dest!: multi_member_split dest: distinct_mset_mono)
      apply (meson distinct_mset_add_mset distinct_mset_mono member_add_mset)
      done
  qed
  let ?R = \<open>measure (\<lambda>(abort, xs, CS, S). size xs)\<close>
  show ?thesis
    unfolding deduplicate_binary_clauses_def Let_def
    apply (refine_vcg assms WHILEIT_rule[where R = ?R] simplify_clause_with_unit_st_spec[THEN order_trans]
      clause_remove_duplicate_clause[THEN order_trans] binary_clause_subres_binary_clause[THEN order_trans])
    subgoal
      by auto
    subgoal
      by (fastforce simp: deduplicate_binary_clauses_inv_def deduplicate_binary_clauses_pre_def deduplicate_binary_clauses_correctly_marked_def)
    subgoal
      by (subst deduplicate_binary_clauses_inv_alt_def2, assumption)
       (auto simp: deduplicate_binary_clauses_inv_def deduplicate_binary_clauses_correctly_marked_remove1)
    subgoal
      by (auto dest: multi_member_split)
    subgoal
      unfolding deduplicate_binary_clauses_inv_alt_def simplify_clause_with_unit_st_pre_def
        case_prod_beta ex_simps(2)[symmetric]
      apply normalize_goal+
      by (rule_tac x=xd in exI) simp
    subgoal
      apply simp
      apply standard
      apply simp
      apply normalize_goal+
      apply (intro ASSERT_leI)
      apply (metis cdcl_twl_inprocessing_l.intros(1,2) r_into_rtranclp rtranclp.rtrancl_refl)
      apply simp
      apply (elim disjE; intro conjI; subst (asm) eq_commute[of \<open>dom_m _\<close>])
      apply (subst deduplicate_binary_clauses_inv_alt_def2, assumption)
      apply (subst (asm)deduplicate_binary_clauses_inv_alt_def2, assumption)
      unfolding prod.simps
      apply (intro conjI)
      apply (simp_all add: deduplicate_binary_clauses_correctly_marked_remove1 size_mset_remove1_mset_le_iff)
      apply (force dest: multi_member_split)
      apply (rule deduplicate_binary_clauses_inv_cdcl_twl_unitres_l)
      apply (rule cdcl_twl_inprocessing_l.intros; assumption)
      apply assumption+
      apply (rule deduplicate_binary_clauses_inv_cdcl_twl_unitres_l)
      apply (rule cdcl_twl_inprocessing_l.intros; assumption)
      apply assumption+
      apply (rule deduplicate_binary_clauses_inv_deleted)
      apply assumption+
      apply (rule cdcl_twl_inprocessing_l.intros; assumption)
      apply (rule deduplicate_binary_clauses_inv_deleted)
      apply assumption+
      apply (rule cdcl_twl_inprocessing_l.intros; assumption)
      done
    subgoal by (rule clause_remove_duplicate_clause_pre)
    subgoal by (rule clause_remove_duplicate_clause_post)
    subgoal
      by (auto dest!: multi_member_split)
    subgoal by (rule binary_clause_subres_lits_pre)
    subgoal
      by (subst deduplicate_binary_clauses_inv_alt_def2, assumption,
          subst (asm)deduplicate_binary_clauses_inv_alt_def2, assumption)
      (auto simp: )
    subgoal by (auto dest!: multi_member_split)
    subgoal by (rule new_lit)
    subgoal by (auto dest!: multi_member_split)
    subgoal unfolding deduplicate_binary_clauses_inv_def by fast
    done
qed

definition mark_duplicated_binary_clauses_as_garbage_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_pre = (\<lambda>S. (\<exists>T. (S,T) \<in> twl_st_l None \<and> set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and> 
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and> count_decided (get_trail_l S) = 0 \<and>
      clauses_to_update_l S = {#} \<and> twl_list_invs S \<and> twl_struct_invs T))\<close>

definition mark_duplicated_binary_clauses_as_garbage_inv :: \<open>'v multiset \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l \<times> 'v multiset \<Rightarrow> bool\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_inv = (\<lambda>xs S (U, ys). ys \<subseteq># xs \<and> cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S U)\<close>

lemma mark_duplicated_binary_clauses_as_garbage_inv_alt_def:
  assumes \<open>mark_duplicated_binary_clauses_as_garbage_pre S\<close>
  shows \<open>mark_duplicated_binary_clauses_as_garbage_inv xs S (U, Ls) \<longleftrightarrow> 
    (\<exists>T. (U,T) \<in> twl_st_l None \<and> set (get_all_mark_of_propagated (get_trail_l U)) \<subseteq> {0} \<and> 
      Ls \<subseteq># xs \<and>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and> count_decided (get_trail_l U) = 0 \<and>
      clauses_to_update_l U = {#} \<and> twl_list_invs U \<and> twl_struct_invs T \<and> cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S U)\<close>
  using assms rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated[of S U] rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l[of S U]
    rtranclp_cdcl_twl_inprocessing_l_count_decided[of S U] rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated[of S U]
  unfolding mark_duplicated_binary_clauses_as_garbage_pre_def
    mark_duplicated_binary_clauses_as_garbage_inv_def prod.simps apply -
  apply normalize_goal+
  apply (rule iffI)
  apply normalize_goal+
   apply (rule rtranclp_cdcl_twl_inprocessing_l_twl_st_l; assumption?)
   apply (rename_tac x V; rule_tac x=V in exI)
   apply (solves auto)
  by meson

definition mark_duplicated_binary_clauses_as_garbage :: \<open>_ \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage S = do {
     ASSERT (mark_duplicated_binary_clauses_as_garbage_pre S);
     Ls \<leftarrow> SPEC (\<lambda>Ls:: 'v multiset. \<forall>L\<in>#Ls. L \<in># atm_of `# all_init_lits_of_l S);
     (S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_duplicated_binary_clauses_as_garbage_inv Ls S\<^esup>(\<lambda>(S, Ls). Ls \<noteq> {#} \<and> get_conflict_l S = None)
      (\<lambda>(S, Ls). do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># Ls);
        ASSERT (L \<in># atm_of `# all_init_lits_of_l S);
        skip \<leftarrow> RES (UNIV :: bool set);
        if skip then RETURN (S, remove1_mset L Ls)
        else do {
          S \<leftarrow> deduplicate_binary_clauses (Pos L) S;
          S \<leftarrow> deduplicate_binary_clauses (Neg L) S;
          RETURN (S, remove1_mset L Ls)
        }
     })
     (S, Ls);
    RETURN S
  }\<close>

lemma cdcl_twl_inprocessing_l_all_learned_lits_of_l:
  assumes \<open>cdcl_twl_inprocessing_l S T\<close>
  shows \<open>set_mset (all_learned_lits_of_l T) \<subseteq> set_mset (all_learned_lits_of_l S)\<close>
proof -
  have [simp]: \<open>D \<notin># A \<Longrightarrow> {#the (if D = x then b else fmlookup N x). x \<in># A#} =
    {#the (fmlookup N x). x \<in># A#}\<close>
    \<open>D \<notin># A \<Longrightarrow> {#the (if x = D then b else fmlookup N x). x \<in># A#} =
    {#the (fmlookup N x). x \<in># A#}\<close> for D E N A b
    by (auto intro!: image_mset_cong)
  have dups_uniq[dest]: \<open>remdups_mset D' = {#K#} \<Longrightarrow> set_mset (all_lits_of_m D') = {-K,K}\<close> for D' K
    by (metis all_lits_of_m_add_mset all_lits_of_m_empty all_lits_of_m_remdups_mset
      insert_commute set_mset_add_mset_insert set_mset_empty)
  show ?thesis
    using assms
    using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
    supply [[goals_limit=1]]
    by (induction rule: cdcl_twl_inprocessing_l.induct)
     (auto 4 3 simp: cdcl_twl_unitres_l.simps 
      cdcl_twl_unitres_true_l.simps
      cdcl_twl_subsumed_l.simps
      cdcl_twl_subresolution_l.simps cdcl_twl_pure_remove_l.simps
      all_learned_lits_of_l_def
      add_mset_eq_add_mset removeAll_notin
      get_init_clss_l_def init_clss_l_mapsto_upd_notin
      init_clss_l_mapsto_upd ran_m_def all_lits_of_m_union
      all_lits_of_m_add_mset distinct_mset_remove1_All
      init_clss_l_fmupd_if all_lits_of_mm_add_mset
      all_lits_of_m_remdups_mset
      dest!: multi_member_split[of \<open>_ :: nat\<close> \<open>_\<close>]
      dest: all_lits_of_m_mono)
qed

lemma rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l:
  assumes \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T\<close>
  shows \<open>set_mset (all_learned_lits_of_l T) \<subseteq> set_mset (all_learned_lits_of_l S)\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto dest: cdcl_twl_inprocessing_l_all_learned_lits_of_l)

lemma mark_duplicated_binary_clauses_as_garbage:
  fixes S :: \<open>'v twl_st_l\<close>
  assumes pre: \<open>mark_duplicated_binary_clauses_as_garbage_pre S\<close>
  shows \<open>mark_duplicated_binary_clauses_as_garbage S \<le> \<Down> Id (SPEC(cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S))\<close>
proof -
  have deduplicate_binary_clauses_pre: \<open>deduplicate_binary_clauses_pre (Pos xa) xb\<close> (is ?A)
     \<open>deduplicate_binary_clauses_pre (Neg xa) xb\<close> (is ?B)
    if
      \<open>mark_duplicated_binary_clauses_as_garbage_inv xs S s\<close> and
      \<open>case s of (S, Ls) \<Rightarrow> Ls \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      st: \<open>s = (a, b)\<close> and
      \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* a xb\<close> and
      xs: \<open>\<forall>L\<in>#xs. L \<in># atm_of `# all_init_lits_of_l S\<close>
      \<open>xa \<in># b\<close>
      for s a xa xb and xs b :: \<open>'v multiset\<close>
    proof -
      have \<open>mark_duplicated_binary_clauses_as_garbage_inv xs S (xb, b)\<close> \<open>xa \<in># xs\<close>
        using that unfolding mark_duplicated_binary_clauses_as_garbage_inv_def
        by auto
      moreover have \<open>set_mset (all_init_lits_of_l xb) = set_mset (all_init_lits_of_l S)\<close>
        using that by (auto dest!: rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l
          simp: mark_duplicated_binary_clauses_as_garbage_inv_def)
      then have \<open>Pos xa \<in># all_init_lits_of_l xb\<close> \<open>Neg xa \<in># all_init_lits_of_l xb\<close>
        using \<open>xa \<in># xs\<close> xs by (auto dest!: multi_member_split[of xa xs]
          simp: all_init_lits_of_l_def)
         (metis in_all_lits_of_mm_ain_atms_of_iff literal.sel)+
      ultimately show ?A ?B
        using pre unfolding deduplicate_binary_clauses_pre_def st
        by (meson mark_duplicated_binary_clauses_as_garbage_inv_alt_def)+
  qed
  let ?R = \<open>measure (\<lambda>(_, Ls). size Ls)\<close>
  have wf: \<open>wf ?R\<close>
    by auto
  show ?thesis
    unfolding mark_duplicated_binary_clauses_as_garbage_def
    apply (refine_vcg deduplicate_binary_clauses[THEN order_trans] wf assms)
    subgoal by (auto simp: mark_duplicated_binary_clauses_as_garbage_inv_def)
    subgoal by (auto simp: mark_duplicated_binary_clauses_as_garbage_inv_def
      dest!: rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
    subgoal by (auto simp: mark_duplicated_binary_clauses_as_garbage_inv_def)
    subgoal by (auto dest!: multi_member_split)
    subgoal unfolding deduplicate_binary_clauses_pre_def
      by hypsubst
        (metis deduplicate_binary_clauses_pre deduplicate_binary_clauses_pre_def rtranclp.rtrancl_refl)
    subgoal by (rule deduplicate_binary_clauses_pre)
    subgoal by (auto simp: mark_duplicated_binary_clauses_as_garbage_inv_def)
    subgoal by (auto dest!: multi_member_split)
    subgoal by (auto simp: mark_duplicated_binary_clauses_as_garbage_inv_def)
    done
qed

definition forward_subsumption_one_inv :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> nat multiset \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_inv = (\<lambda>C S zs (xs, s).
  (\<exists>S' . (S, S') \<in> twl_st_l None \<and>
      twl_struct_invs S' \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
    C \<notin># xs \<and> C \<in># dom_m (get_clauses_l S) \<and> count_decided (get_trail_l S) = 0 \<and>
    clauses_to_update_l S = {#} \<and> twl_list_invs S \<and> twl_struct_invs S' \<and>
   set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
   (\<forall>C'\<in>#xs. C' \<in># dom_m (get_clauses_l S) \<longrightarrow> length (get_clauses_l S \<propto>  C') \<le> length (get_clauses_l S \<propto> C) )\<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
  subsume_or_strengthen_pre C s S \<and> xs \<subseteq># zs \<and>
    (is_subsumed s \<longrightarrow> subsumed_by s \<in># zs) \<and>
    (is_strengthened s \<longrightarrow> strengthened_by s \<in># zs)))\<close>

definition forward_subsumption_one_select where
  \<open>forward_subsumption_one_select C ys S = (\<lambda>xs. C \<notin># xs \<and> ys \<inter># xs = {#} \<and>
  (\<forall>D\<in>#xs. D \<in># dom_m (get_clauses_l S) \<longrightarrow>
    (\<forall>L\<in> set (get_clauses_l S \<propto> D). undefined_lit (get_trail_l S) L) \<and>
    (length (get_clauses_l S \<propto> D) \<le> length (get_clauses_l S \<propto> C))))\<close>

definition forward_subsumption_one :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_l \<Rightarrow> ('v twl_st_l \<times> bool) nres\<close> where
  \<open>forward_subsumption_one = (\<lambda>C cands S\<^sub>0. do {
    ASSERT(forward_subsumption_one_pre C cands S\<^sub>0);
    xs\<^sub>0 \<leftarrow> SPEC (forward_subsumption_one_select C cands S\<^sub>0);
    (xs, s) \<leftarrow>
      WHILE\<^sub>T\<^bsup> forward_subsumption_one_inv C S\<^sub>0 xs\<^sub>0 \<^esup> (\<lambda>(xs, s). xs \<noteq> {#} \<and> s = NONE)
      (\<lambda>(xs, s). do {
        C' \<leftarrow> SPEC(\<lambda>C'. C' \<in># xs);
        if C' \<notin># dom_m (get_clauses_l S\<^sub>0)
        then RETURN (remove1_mset C' xs, s)
        else do {
          s \<leftarrow> SPEC(try_to_subsume C C' (get_clauses_l S\<^sub>0));
          RETURN (remove1_mset C' xs, s)
        }
      })
      (xs\<^sub>0, NONE);
    ASSERT (forward_subsumption_one_inv C S\<^sub>0 xs\<^sub>0 (xs, s));
    S \<leftarrow> subsume_or_strengthen C s S\<^sub>0;
    ASSERT (set_mset (all_learned_lits_of_l S) \<subseteq> set_mset (all_learned_lits_of_l S\<^sub>0) \<and> set_mset (all_init_lits_of_l S) = set_mset (all_init_lits_of_l S\<^sub>0));
    RETURN (S, s \<noteq> NONE)
  }
)\<close>

lemma forward_subsumption_one:
  assumes \<open>forward_subsumption_one_pre C cands S\<close>
  shows \<open>forward_subsumption_one C cands S \<le> \<Down>{((st, SR), st'). st = st' \<and> (\<not>SR \<longrightarrow> st = S)}
    (SPEC(\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and> get_trail_l T = get_trail_l S \<and>
      (\<forall>D\<in>#cands. D \<noteq> C \<longrightarrow> (D \<in># dom_m (get_clauses_l T)) = (D \<in># dom_m (get_clauses_l S))) \<and>
      (\<forall>D\<in>#remove1_mset C (dom_m (get_clauses_l T)).
       D \<in># dom_m (get_clauses_l S) \<and> get_clauses_l T \<propto> D = get_clauses_l S \<propto> D)))\<close>
proof -
  obtain x where
    Sx: \<open>(S, x) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs x\<close> and
    st_inv: \<open>twl_st_inv x\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    C: \<open>C \<in># dom_m (get_clauses_l S)\<close> and
    all_struct_x: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of x)\<close> and
    clss: \<open>clauses_to_update_l S = {#}\<close> \<open>get_conflict_l S = None\<close> and
    no_annot: \<open>set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0}\<close> and
    init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of x)\<close> and
    dec: \<open>count_decided (get_trail_l S) = 0\<close> and
    undef_C: \<open>\<forall>L\<in>#mset (get_clauses_l S \<propto> C). undefined_lit (get_trail_l S) L\<close> and
    le_C: \<open>2 < length (get_clauses_l S \<propto> C)\<close>
    using assms unfolding forward_subsumption_one_pre_def twl_struct_invs_def
      pcdcl_all_struct_invs_def state\<^sub>W_of_def
    apply -
    by normalize_goal+ blast  have \<open>C \<noteq> 0\<close>
    using list_invs C by (auto simp: twl_list_invs_def)
  then have C_annot: \<open>C \<notin> set (get_all_mark_of_propagated (get_trail_l S))\<close>
    using no_annot by blast

  have [refine0]: \<open>wf (measure (\<lambda>(d, _). size d))\<close>
    by auto
  have H: \<open>length (get_clauses_l S \<propto> D) \<ge>2\<close> \<open>distinct (get_clauses_l S \<propto> D)\<close>  \<open>D \<noteq> 0\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated (get_trail_l S))\<close>
    \<open>\<not>tautology (mset (get_clauses_l S \<propto> D))\<close>
    if \<open>D \<in># dom_m (get_clauses_l S)\<close>for D
    using st_inv that Sx list_invs no_annot unfolding twl_struct_invs_def twl_list_invs_def apply -
    by (auto simp: twl_struct_invs_def twl_st_l_def ran_m_def conj_disj_distribR
      twl_st_inv.simps Collect_disj_eq image_image image_Un Collect_conv_if mset_take_mset_drop_mset'
      dest!: multi_member_split split: if_splits
      simp flip: insert_compr)

  have H2: \<open>\<not>tautology (mset (get_clauses_l S \<propto> D))\<close> if \<open>D \<in># dom_m (get_clauses_l S)\<close> for D
    using list_invs that by (auto simp: twl_list_invs_def ran_m_def)

  have forward_subsumption_one_inv: \<open>forward_subsumption_one_inv C S xs\<^sub>0 (remove1_mset xa aa, xb)\<close>
    if
      select: \<open>forward_subsumption_one_select C cands S xs\<close> and
      inv: \<open>forward_subsumption_one_inv C S xs\<^sub>0 s\<close> and
      \<open>case s of (xs, s) \<Rightarrow> xs \<noteq> {#} \<and> s = NONE\<close> and
      st[simp]: \<open>s = (aa, ba)\<close> and
      xa_aa: \<open>xa \<in># aa\<close> and
      xa: \<open>\<not> xa \<notin># dom_m (get_clauses_l S)\<close> and
      subs: \<open>try_to_subsume C xa (get_clauses_l S) xb\<close>
    for xs s b aa ba xa xb xs\<^sub>0
  proof -
    have [simp]: \<open>C \<noteq> xa\<close>
      using xa_aa select inv unfolding forward_subsumption_one_select_def forward_subsumption_one_inv_def
      by auto

    have [intro]: \<open>x21 \<in> set (get_clauses_l S \<propto> xa) \<Longrightarrow>
    - x21 \<in> set (get_clauses_l S \<propto> C) \<Longrightarrow>
    remove1_mset x21 (mset (get_clauses_l S \<propto> xa)) \<subseteq># remove1_mset (- x21) (mset (get_clauses_l S \<propto> C)) \<Longrightarrow>
    tautology (mset (get_clauses_l S \<propto> xa) + mset (get_clauses_l S \<propto> C) - {#- x21, x21#}) \<Longrightarrow> False\<close> for a x21
      using multi_member_split[of x21 \<open>mset (get_clauses_l S \<propto> xa)\<close>]
        multi_member_split[of \<open>-x21\<close> \<open>mset (get_clauses_l S \<propto> C)\<close>] H[of C] C
      by (auto simp: tautology_add_subset tautology_add_mset)

    have \<open>subsume_or_strengthen_pre C xb S\<close>
      using undef_C le_C dec clss C_annot subs H xa C Sx struct init all_struct_x st_inv list_invs 
        H[of C] unfolding subsume_or_strengthen_pre_def
      apply -
      apply (rule exI[of _ x])
      by (auto simp: try_to_subsume_def split: subsumption.splits intro!: exI[of _ x])
    then show ?thesis
      using inv
      unfolding forward_subsumption_one_inv_def prod.simps st apply -
      apply normalize_goal+
      apply (rule exI[of _ x])
      apply (use Sx struct st_inv init dec subs xa_aa in \<open>auto dest!: in_diffD\<close>)
        using subs xa_aa
      apply (case_tac xb; auto simp: try_to_subsume_def; fail)+
      done
  qed
  show ?thesis
    unfolding forward_subsumption_one_def conc_fun_RES
    apply (rewrite at \<open>_ \<le> \<hole>\<close> RES_SPEC_conv)
    apply (refine_vcg subsume_or_strengthen[unfolded Down_id_eq] if_rule)
    subgoal using assms by auto
    subgoal for ax
      unfolding forward_subsumption_one_inv_def prod.simps forward_subsumption_one_select_def
        subsume_or_strengthen_pre_def ex_simps[symmetric]
      apply (rule_tac x=x in exI)+
      using all_struct_x Sx H struct st_inv C init by (auto simp add: subsume_or_strengthen_pre_def forward_subsumption_one_pre_def )
   subgoal for xs
     unfolding simplify_clause_with_unit_st_pre_def forward_subsumption_one_inv_def case_prod_beta
     apply normalize_goal+
     by (rule_tac x=x in exI)
      (auto dest: in_diffD)
   subgoal
     unfolding simplify_clause_with_unit_st_pre_def forward_subsumption_one_inv_def case_prod_beta
     apply normalize_goal+
     by  (auto dest: multi_member_split)
   subgoal by (rule forward_subsumption_one_inv)
   subgoal by (auto dest!: multi_member_split)
   subgoal by auto
   subgoal
     unfolding forward_subsumption_one_inv_def
     by fast
   subgoal using C by auto
   subgoal by (simp add: rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
   subgoal by (auto dest:  rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
   subgoal premises p for x s a b xa
     using p(1-7) le_C unfolding forward_subsumption_one_inv_def prod.simps p(5) apply -
     apply normalize_goal+
     apply standard
     apply (auto simp add: forward_subsumption_one_inv_def)[]
     apply simp
     apply (intro ballI)
     subgoal for xx D
     apply (subgoal_tac \<open>(is_strengthened (b) \<longrightarrow> D \<noteq> strengthened_by (b)) \<and>
       (is_subsumed (b) \<longrightarrow> D \<noteq> subsumed_by (b))\<close>)
     apply (cases b)
     apply (simp add:)
     apply (simp add:)
     apply blast
     apply (cases b)
     apply (intro conjI)
     apply (auto simp add: forward_subsumption_one_select_def dest!: multi_member_split[of D])[3]
     apply (simp only: subsumption.disc simp_thms)
     done
   done
   done
qed


definition simplify_clauses_with_unit_st_pre where
  \<open>simplify_clauses_with_unit_st_pre S \<longleftrightarrow> (\<exists>T.
  (S, T) \<in> twl_st_l None \<and>
  twl_struct_invs T \<and>
  twl_list_invs S \<and>
  clauses_to_update_l S = {#} \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and>
  count_decided (get_trail_l S) = 0 \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0})\<close>

definition simplify_clauses_with_unit_st_inv :: \<open>'v twl_st_l \<Rightarrow> nat set \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>simplify_clauses_with_unit_st_inv S\<^sub>0 it S \<longleftrightarrow> (
    cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S\<^sub>0 S \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq>
    set (get_all_mark_of_propagated (get_trail_l S\<^sub>0)) \<union> {0})\<close>

text \<open>Hard-coding the invariants was a lot faster than the alternative way, namely proving that
  the loop invariants still holds at the end of the loop. No this makes not sense, I know.\<close>
definition simplify_clauses_with_unit_st :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close>  where
  \<open>simplify_clauses_with_unit_st S =
  do {
  ASSERT(simplify_clauses_with_unit_st_pre S);
  xs \<leftarrow> SPEC(\<lambda>xs. finite xs);
  T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_inv S it T)
  (xs)
  (\<lambda>S. get_conflict_l S = None)
  (\<lambda>i S. if i \<in># dom_m (get_clauses_l S) then simplify_clause_with_unit_st i S else RETURN S)
  S;
  ASSERT(set_mset (all_learned_lits_of_l T) \<subseteq> set_mset (all_learned_lits_of_l S));
  ASSERT(set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S));
  RETURN T
  }\<close>

lemma simplify_clauses_with_unit_st_inv_simplify_clauses_with_unit_st_preD:
  assumes
    inv: \<open>simplify_clauses_with_unit_st_inv S\<^sub>0 it T\<close> and
    pre: \<open>simplify_clauses_with_unit_st_pre S\<^sub>0\<close>
  shows \<open>simplify_clauses_with_unit_st_pre T\<close>
proof -
  have st: \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S\<^sub>0 T\<close>
    using inv unfolding simplify_clauses_with_unit_st_inv_def
    by blast
  obtain S where
    S\<^sub>0S: \<open>(S\<^sub>0, S) \<in> twl_st_l None\<close> and
    struct_S: \<open>twl_struct_invs S\<close> and
    list_S: \<open>twl_list_invs S\<^sub>0\<close> and
    clss_upd_S: \<open>clauses_to_update_l S\<^sub>0 = {#}\<close> and
    ent_S: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close> and
    lvl_S: \<open>count_decided (get_trail_l S\<^sub>0) = 0\<close> and
    empty: \<open>set (get_all_mark_of_propagated (get_trail_l S\<^sub>0)) \<subseteq> {0}\<close>
    using pre unfolding simplify_clauses_with_unit_st_pre_def
    by blast

  obtain U where
    TU: \<open>(T, U) \<in> twl_st_l None\<close> and
    struct_T: \<open>twl_struct_invs U\<close> and
    list_T: \<open>twl_list_invs T\<close> and
    ent_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
    using rtranclp_cdcl_twl_inprocessing_l_twl_st_l[OF st S\<^sub>0S struct_S list_S ent_S]
    by blast
  have
    clss_upd_T: \<open>clauses_to_update_l T = {#}\<close> and
    lvl_S: \<open>count_decided (get_trail_l T) = 0\<close>
    subgoal
      using st apply (subst (asm) rtranclp_unfold)
       apply (elim disjE)
      subgoal using clss_upd_S by auto
      subgoal
        by (subst (asm) tranclp_unfold_end)
         (auto simp: cdcl_twl_inprocessing_l.simps cdcl_twl_pure_remove_l.simps
          cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
          cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
      done
    subgoal
      using st apply (induction rule: rtranclp_induct)
      subgoal using lvl_S by auto
      subgoal
        by (auto simp: cdcl_twl_inprocessing_l.simps cdcl_twl_pure_remove_l.simps
          cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
          cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
      done
    done
  have empty: \<open>set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq> {0}\<close>
    using st apply (induction rule: rtranclp_induct)
    subgoal using empty by auto
    subgoal by (auto simp: cdcl_twl_inprocessing_l.simps
      cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps cdcl_twl_pure_remove_l.simps
      cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
    done
  show ?thesis
    unfolding simplify_clauses_with_unit_st_pre_def
    by (rule exI[of _ U])
     (use TU struct_T list_T ent_T clss_upd_T lvl_S empty in auto)
qed

lemma simplify_clauses_with_unit_st_spec:
  assumes \<open>count_decided (get_trail_l S) = 0\<close>
    \<open>get_conflict_l S = None\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    empty: \<open>set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0}\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T))\<close> 
  shows \<open>simplify_clauses_with_unit_st S \<le> \<Down>Id (SPEC(\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and>
    simplify_clauses_with_unit_st_inv S {} T))\<close>
proof -
  show ?thesis
    unfolding simplify_clauses_with_unit_st_def
    apply (refine_vcg)
    subgoal using assms apply -
      unfolding simplify_clauses_with_unit_st_pre_def
      by (rule exI[of _ T]) auto
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
        simplify_clauses_with_unit_st_pre_def
      by blast
    subgoal  for x xa it \<sigma>
      apply (frule simplify_clauses_with_unit_st_inv_simplify_clauses_with_unit_st_preD,
        assumption)
       apply (unfold simplify_clauses_with_unit_st_pre_def)
       apply normalize_goal+
      apply (rule simplify_clause_with_unit_st_spec[THEN order_trans])
      subgoal
        unfolding simplify_clauses_with_unit_st_inv_def simplify_clause_with_unit_st_pre_def
        by normalize_goal+ fast
      subgoal
        using empty
        by (auto 5 3 simp: simplify_clauses_with_unit_st_inv_def distinct_mset_dom
          rtranclp.rtrancl_into_rtrancl[of _ S] distinct_mset_remove1_All
          dest!: cdcl_twl_inprocessing_l.intros)
      done
    subgoal for x \<sigma>
      unfolding simplify_clauses_with_unit_st_inv_def
      by (auto dest: rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by (auto dest: rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by (auto dest: rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by auto
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by (auto dest: rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by (auto dest: rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by auto
    subgoal
      unfolding simplify_clauses_with_unit_st_inv_def
      by auto
    done
qed

definition simplify_clauses_with_units_st_pre where
  \<open>simplify_clauses_with_units_st_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and> twl_list_invs S \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T)) \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
    clauses_to_update_l S = {#} \<and>
    count_decided (get_trail_l S) = 0)\<close>

definition simplify_clauses_with_units_st where
  \<open>simplify_clauses_with_units_st S = do {
    ASSERT(simplify_clauses_with_units_st_pre S);
    new_units \<leftarrow> SPEC (\<lambda>b. b \<longrightarrow> get_conflict_l S = None);
    if new_units
    then simplify_clauses_with_unit_st S
    else RETURN S}\<close>


lemma simplify_clauses_with_units_st_spec:
  assumes \<open>count_decided (get_trail_l S) = 0\<close>
    \<open>clauses_to_update_l S = {#}\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T))\<close> and
    \<open>set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0}\<close>
  shows \<open>simplify_clauses_with_units_st S \<le> \<Down>Id (SPEC(\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and>
    simplify_clauses_with_unit_st_inv S {} T))\<close>
  using assms unfolding simplify_clauses_with_units_st_def
  apply (refine_vcg simplify_clauses_with_unit_st_spec[THEN order_trans])
  subgoal unfolding simplify_clauses_with_units_st_pre_def by blast
  subgoal by auto
  apply assumption+
  subgoal by auto
  subgoal by auto
  subgoal unfolding simplify_clauses_with_unit_st_inv_def by auto
  done

definition try_to_forward_subsume_inv :: \<open>'v twl_st_l \<Rightarrow> nat multiset \<Rightarrow> nat \<Rightarrow> nat \<times> bool \<times> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>try_to_forward_subsume_inv S0 = (\<lambda>cands C (i,brk,S).
  (cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S0 S \<and>
  clauses_to_update_l S = {#} \<and>
  count_decided (get_trail_l S) = 0 \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
  (\<not>brk \<longrightarrow> (get_conflict_l S = None \<and> C \<in># dom_m (get_clauses_l S) \<and>
  (\<forall>L \<in># mset (get_clauses_l S \<propto> C). undefined_lit (get_trail_l S) L) \<and>
  length (get_clauses_l S \<propto> C) > 2)) \<and>
  (get_trail_l S = get_trail_l S0) \<and>
  (\<forall>D\<in>#remove1_mset C (dom_m (get_clauses_l S)).
  D \<in># dom_m (get_clauses_l S0) \<and> get_clauses_l S \<propto> D = get_clauses_l S0 \<propto> D) \<and>
  (\<forall>D\<in>#cands. D \<noteq> C \<longrightarrow> (D \<in># dom_m (get_clauses_l S0)) = (D \<in># dom_m (get_clauses_l S)))))\<close>

definition try_to_forward_subsume_pre :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>try_to_forward_subsume_pre = (\<lambda>C xs S.
  \<exists>T. C \<noteq> 0 \<and>
  (S, T) \<in> twl_st_l None \<and>
  twl_struct_invs T \<and>
  twl_list_invs S \<and>
  clauses_to_update_l S = {#} \<and>
  get_conflict_l S = None \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and>
  count_decided (get_trail_l S) = 0 \<and>
  set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
  C \<in># dom_m (get_clauses_l S) \<and>
  (\<forall>L \<in># mset (get_clauses_l S \<propto> C). undefined_lit (get_trail_l S) L) \<and>
  length (get_clauses_l S \<propto> C) > 2)\<close>

definition try_to_forward_subsume :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>try_to_forward_subsume C xs S\<^sub>0 = do {
  ASSERT (try_to_forward_subsume_pre C xs S\<^sub>0);
  n \<leftarrow> RES {_::nat. True};
  ebreak \<leftarrow> RES {_::bool. True};
  (_, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup> try_to_forward_subsume_inv S\<^sub>0 xs C\<^esup>
    (\<lambda>(i, break, S). \<not>break \<and> i < n)
    (\<lambda>(i, break, S). do {
      (S, subs) \<leftarrow> forward_subsumption_one C xs S;
      ebreak \<leftarrow> RES {_::bool. True};
      RETURN (i+1, subs \<or> ebreak, S)
    })
  (0, ebreak, S\<^sub>0);
  RETURN S
  }
  \<close>

lemma try_to_forward_forward_subsumption_one_pre:
  \<open>try_to_forward_subsume_pre C xs S \<Longrightarrow>
  try_to_forward_subsume_inv S xs C (a, False, ba) \<Longrightarrow> forward_subsumption_one_pre C xs ba\<close>
  unfolding try_to_forward_subsume_inv_def forward_subsumption_one_pre_def case_prod_beta
    try_to_forward_subsume_pre_def
  apply normalize_goal+
  apply (elim rtranclp_cdcl_twl_inprocessing_l_twl_st_l)
  apply assumption+
  apply (rule_tac x=V in exI)
  apply simp
  done

lemma in_remove1_mset_dom_m_iff[simp]: \<open>a \<in># remove1_mset C (dom_m N) \<longleftrightarrow> a \<noteq> C \<and> a \<in># dom_m N\<close>
  using distinct_mset_dom[of N]
  by (cases \<open>C \<in># dom_m N\<close>; auto dest: multi_member_split)

lemma try_to_forward_subsume:
  assumes \<open>try_to_forward_subsume_pre C cands S\<close>
  shows \<open>try_to_forward_subsume C cands S \<le> \<Down>Id (SPEC(\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and>
      (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow> get_trail_l T = get_trail_l S) \<and>
     (\<forall>D\<in>#cands. D \<noteq> C \<longrightarrow>((D \<in># dom_m (get_clauses_l T)) = (D \<in># dom_m (get_clauses_l S)))) \<and>
     (\<forall>D\<in>#remove1_mset C (dom_m (get_clauses_l T)).
       D \<in># dom_m (get_clauses_l S) \<and> get_clauses_l T \<propto> D = get_clauses_l S \<propto> D)))\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(i, _, _). Suc n - i))\<close> for n
    by auto
  show ?thesis
    unfolding try_to_forward_subsume_def
    apply (refine_vcg forward_subsumption_one[THEN order_trans])
    subgoal using assms by auto
    apply (rule_tac n1=x in wf)
    subgoal unfolding try_to_forward_subsume_inv_def try_to_forward_subsume_pre_def prod.simps
      by (auto dest: in_diffD)
    subgoal for x s a b aa ba
      by (auto intro!: try_to_forward_forward_subsumption_one_pre)
    subgoal
      unfolding conc_fun_RES RES_RETURN_RES
      apply (rule RES_rule, unfold Image_iff)
      apply (elim bexE, unfold mem_Collect_eq)
      apply (case_tac xa, hypsubst, unfold prod.simps)
      apply (rule RES_rule)
      apply (simp add: try_to_forward_subsume_inv_def)
      apply (intro conjI impI)
      apply  (auto simp: conc_fun_RES RES_RETURN_RES
        try_to_forward_subsume_inv_def dest: in_diffD
        dest: rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l
          rtranclp_cdcl_twl_inprocessing_l_count_decided rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated)
      done
    subgoal by (auto simp: try_to_forward_subsume_inv_def)
    subgoal by (auto simp: try_to_forward_subsume_inv_def)
    subgoal by (auto simp: try_to_forward_subsume_inv_def)
    subgoal by (auto simp: try_to_forward_subsume_inv_def)
    done
qed

definition forward_subsumption_all_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_pre = (\<lambda>S.
  \<exists>T.
    (S, T) \<in> twl_st_l None \<and>
    twl_struct_invs T \<and>
    twl_list_invs S \<and>
    clauses_to_update_l S = {#} \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T) \<and>
    count_decided (get_trail_l S) = 0 \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0})\<close>


definition forward_subsumption_all_inv :: \<open>'v twl_st_l \<Rightarrow> nat multiset \<times> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_inv S = (\<lambda>(xs, T). \<exists>S'. (S,S')\<in> twl_st_l None \<and>  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and> xs \<subseteq># dom_m (get_clauses_l S) \<and>
    twl_struct_invs S' \<and>
    twl_list_invs S \<and>
    clauses_to_update_l S = {#} \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
    count_decided (get_trail_l S) = 0 \<and>
    get_trail_l T = get_trail_l S \<and> (\<forall>C\<in>#xs. get_clauses_l T \<propto> C = get_clauses_l S \<propto> C) \<and> xs \<subseteq># dom_m (get_clauses_l T))\<close>

definition forward_subsumption_all_cands where
  \<open>forward_subsumption_all_cands S xs \<longleftrightarrow> xs \<subseteq># dom_m (get_clauses_l S) \<and>
  (\<forall>C\<in>#xs. (\<forall>L\<in>set (get_clauses_l S \<propto> C). undefined_lit (get_trail_l S) L) \<and>
  length (get_clauses_l S \<propto> C) > 2)\<close>

definition forward_subsumption_all :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>forward_subsumption_all = (\<lambda>S. do {
  ASSERT (forward_subsumption_all_pre S);
  xs \<leftarrow> SPEC (forward_subsumption_all_cands S);
  (xs, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_all_inv S \<^esup> (\<lambda>(xs, S). xs \<noteq> {#} \<and> get_conflict_l S = None)
    (\<lambda>(xs, S). do {
       C \<leftarrow> SPEC(\<lambda>C'. C' \<in># xs);
       T \<leftarrow> try_to_forward_subsume C xs S;
       ASSERT (\<forall>D\<in>#remove1_mset C xs. get_clauses_l T \<propto> D = get_clauses_l S \<propto> D);
       RETURN (remove1_mset C xs, T)
    })
    (xs, S);
  RETURN S
  }
)\<close>


lemma forward_subsumption_all:
  assumes \<open>forward_subsumption_all_pre S\<close>
  shows \<open>forward_subsumption_all S \<le> \<Down>Id (SPEC(cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S))\<close>
proof -
  let ?R = \<open>measure (\<lambda>(xs, _). size xs)\<close>
  have simplify_clause_with_unit_st_pre: \<open>simplify_clause_with_unit_st_pre D T\<close>
    if
      \<open>forward_subsumption_all_pre S\<close> and
      \<open>C \<subseteq># dom_m (get_clauses_l S)\<close> and
      \<open>forward_subsumption_all_inv S xsS\<close> and
      \<open>case xsS of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      st: \<open>xsS = (Cs, T)\<close> and
      \<open>D \<in># Cs\<close> and
      \<open>\<not> D \<notin># dom_m (get_clauses_l T)\<close>
    for C xsS Cs T D
  proof -
    have \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T\<close>
      using that unfolding simplify_clause_with_unit_st_pre_def forward_subsumption_all_inv_def st prod.simps
      apply - apply normalize_goal+
      by auto
  show ?thesis
      using rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated[of S T] rtranclp_cdcl_twl_inprocessing_l_twl_st_l[of S T]
      using that unfolding simplify_clause_with_unit_st_pre_def forward_subsumption_all_inv_def st prod.simps
        forward_subsumption_all_pre_def
      apply - apply normalize_goal+
      apply (auto dest: rtranclp_cdcl_twl_inprocessing_l_count_decided
        rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l
        rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated)
      apply (meson rtranclp_cdcl_twl_inprocessing_l_twl_list_invs)
      by metis
  qed
  have 0: \<open>\<Down>Id  (do {
  ASSERT (forward_subsumption_all_pre S);
  xs \<leftarrow> SPEC (\<lambda>xs. xs \<subseteq># (dom_m (get_clauses_l S)));
  (xs, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> \<lambda>(xs, T). cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<and> xs \<subseteq># dom_m (get_clauses_l S) \<^esup> (\<lambda>(xs, S). xs \<noteq> {#} \<and> get_conflict_l S = None)
    (\<lambda>(xs, S'). do {
       C \<leftarrow> SPEC(\<lambda>C'. C' \<in># xs);
       S \<leftarrow> SPEC(\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S' T \<and> get_trail_l T = get_trail_l S \<and> length (get_clauses_l S \<propto> C) > 2 \<and>
          remove1_mset C xs \<subseteq># dom_m (get_clauses_l T) \<and>
          (\<forall>D\<in>#remove1_mset C (dom_m (get_clauses_l T)). D \<in># dom_m (get_clauses_l S') \<and> get_clauses_l T \<propto> D = get_clauses_l S' \<propto> D));
        RETURN (remove1_mset C xs, S)
    })
    (xs, S);
  RETURN S
           }) \<le> \<Down>Id (SPEC(cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S))\<close>
    apply (subst (1) Down_id_eq)
    apply (refine_vcg WHILEIT_rule[where R= ?R] forward_subsumption_one[THEN order_trans]
      simplify_clause_with_unit_st_spec[THEN order_trans])
    subgoal using assms by auto
    subgoal by auto
    subgoal by (auto simp: forward_subsumption_all_inv_def)
    subgoal by (auto simp: forward_subsumption_all_inv_def)
    subgoal by (auto simp: size_mset_remove1_mset_le_iff)
    subgoal by (auto simp: forward_subsumption_all_inv_def)
    subgoal by (auto simp: size_mset_remove1_mset_le_iff)
    subgoal by (auto simp: forward_subsumption_all_inv_def)
    done
  let ?R = \<open>\<lambda>xs\<^sub>0. {((xs, U), (ys,V)). (xs,ys)\<in>Id \<and> xs \<subseteq># xs\<^sub>0 \<and> distinct_mset xs \<and> (U, V) \<in> Id \<and> get_trail_l U = get_trail_l S \<and>
      (\<forall>C\<in># xs. C \<in>#dom_m (get_clauses_l U) \<and> get_clauses_l U \<propto> C = get_clauses_l S \<propto> C) \<and> xs \<subseteq># dom_m (get_clauses_l U)}\<close>
  have try_to_forward_subsume_pre: \<open>try_to_forward_subsume_pre C x1a x2a\<close>
    if
     pre: \<open>forward_subsumption_all_pre S\<close> and
      \<open>(xs, xsa) \<in> Id\<close> and
      cands: \<open>xs \<in> Collect (forward_subsumption_all_cands S)\<close> and
      \<open>xsa \<in> {xs. xs \<subseteq># dom_m (get_clauses_l S)}\<close> and
      xx': \<open>(x, x') \<in> ?R xsa\<close> and
      break: \<open>case x of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      \<open>case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      inv: \<open>forward_subsumption_all_inv S x\<close> and
      st: \<open>x' = (x1, x2)\<close> \<open>x = (x1a, x2a)\<close> and
      CCa: \<open>(C, Ca) \<in> nat_rel\<close> and
       \<open>C \<in> {C'. C' \<in># x1a}\<close> and
      \<open>Ca \<in> {C'. C' \<in># x1}\<close> 
    for xs xsa x x' x1 x2 x1a x2a C Ca T U
  proof -
    have TU: \<open>x2 = x2a\<close> and
      Sx2a: \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S x2\<close> and
      st': \<open>x1 = x1a\<close> \<open>x2 = x2a\<close> \<open>C=Ca\<close> and
      C:  \<open>C \<in># dom_m (get_clauses_l x2a)\<close>  and
      undef: \<open>\<forall>L\<in>set (get_clauses_l x2 \<propto> C). undefined_lit (get_trail_l x2a) L\<close> and
      [intro]: \<open>2 < length (get_clauses_l x2a \<propto> Ca)\<close> and
      confl: \<open>get_conflict_l x2a = None\<close>
      using inv xx' CCa cands break
      unfolding forward_subsumption_all_inv_def st forward_subsumption_all_cands_def
      by (auto dest!: multi_member_split simp: ball_conj_distrib)
       (metis mem_Collect_eq pair_in_Id_conv subset_mset.le_iff_add that(13) that(2) union_iff)+
    obtain x where
      Sx: \<open>(S, x) \<in> twl_st_l None\<close> and
      struct_S: \<open>twl_struct_invs x\<close> and
      list_S: \<open>twl_list_invs S\<close> and
      [simp]: \<open>clauses_to_update_l S = {#}\<close> and
      ent_S: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of x)\<close> and
      [simp]: \<open>count_decided (get_trail_l S) = 0\<close> and
      marks: \<open>set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0}\<close>
      using pre unfolding forward_subsumption_all_pre_def by fast
    have [intro]: \<open>2 < length (get_clauses_l x2a \<propto> Ca)\<close>
        using CCa by auto

    show ?thesis
      using undef C confl apply -
      apply (rule rtranclp_cdcl_twl_inprocessing_l_twl_st_l[OF Sx2a Sx struct_S list_S ent_S])
      subgoal for V
      unfolding st' TU
      unfolding try_to_forward_subsume_pre_def TU
      apply (rule_tac x=V in exI)
      using rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l[OF Sx2a]
        rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated[OF Sx2a]
        rtranclp_cdcl_twl_inprocessing_l_count_decided[OF Sx2a]
        rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated[OF Sx2a]
        marks
      by (auto simp add: twl_list_invs_def TU)
      done
  qed
  have [refine]: \<open>(xs,xsa)\<in>Id \<Longrightarrow>xsa \<subseteq># dom_m (get_clauses_l S)\<Longrightarrow>((xs, S), xsa, S) \<in> ?R xsa\<close> for xs xsa
    by (auto simp add: Duplicate_Free_Multiset.distinct_mset_mono distinct_mset_dom)
  show ?thesis
    apply (rule order_trans)
    prefer 2
    apply (rule 0)
    unfolding forward_subsumption_all_def
    apply (refine_vcg WHILEIT_refine[where R=\<open>?R xs\<close> for xs]
      try_to_forward_subsume
      forward_subsumption_one[THEN order_trans])
    subgoal using assms by (auto simp: forward_subsumption_all_cands_def)
    subgoal by auto
    subgoal unfolding forward_subsumption_all_pre_def forward_subsumption_all_inv_def case_prod_beta apply normalize_goal+
      by (rename_tac xa, rule_tac x=xa in exI) (auto simp: forward_subsumption_all_inv_def)
    subgoal by (auto simp: forward_subsumption_all_inv_def)
    subgoal by (auto simp: size_mset_remove1_mset_le_iff)
    apply (rule try_to_forward_subsume[THEN order_trans])
    subgoal by (rule try_to_forward_subsume_pre)
    subgoal unfolding Down_id_eq
      by (rule SPEC_rule) (auto simp: forward_subsumption_all_cands_def Ball_def
        forward_subsumption_all_inv_def distinct_mset_remove1_All 
        intro!: distinct_subseteq_iff[THEN iffD1])
    subgoal
      by (auto dest: in_diffD simp: distinct_mset_remove1_All)
    subgoal
      by (auto dest: in_diffD simp: distinct_mset_remove1_All)
    subgoal by auto
    done
qed


definition forward_subsumption_needed_l :: \<open>_\<close> where
  \<open>forward_subsumption_needed_l S = SPEC (\<lambda>_. True)\<close>

definition forward_subsume_l :: \<open>_\<close> where
  \<open>forward_subsume_l S = do {
     ASSERT (forward_subsumption_all_pre S);
     b \<leftarrow> forward_subsumption_needed_l S;
     if b then forward_subsumption_all S else RETURN S
}\<close>

lemma forward_subsume_l:
  assumes \<open>forward_subsumption_all_pre S\<close>
  shows \<open>forward_subsume_l S \<le> \<Down>Id (SPEC(cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S))\<close>
  unfolding forward_subsume_l_def forward_subsumption_needed_l_def
  by (refine_vcg forward_subsumption_all[unfolded Down_id_eq]) (use assms in auto)

subsection \<open>Pure Literal Deletion\<close>
definition propagate_pure_l_pre:: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>propagate_pure_l_pre L S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> twl_st_l None \<and> L \<in># all_init_lits_of_l S \<and> undefined_lit (get_trail_l S) L \<and>
  clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and>
  count_decided (get_trail_l S) = 0 \<and> -L \<notin> \<Union>(set_mset ` set_mset (mset `# get_init_clss_l S)))\<close>

definition propagate_pure_bt_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>propagate_pure_bt_l = (\<lambda>L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
    ASSERT(propagate_pure_l_pre L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
    M \<leftarrow> cons_trail_propagate_l L 0 M;
    RETURN (M, N, D, NE, UE, add_mset {#L#} NEk, UEk, NS, US, N0, U0, WS, add_mset (-L) Q)})\<close>

lemma in_all_lits_of_mm_Pos_Neg:
  \<open>L \<in># all_lits_of_mm A \<longleftrightarrow> L \<in> \<Union>(set_mset ` set_mset A) \<or>  -L \<in> \<Union>(set_mset ` set_mset A)\<close>
  by (cases L)
   (auto simp: all_lits_of_mm_def image_UN dest!: multi_member_split)

lemma propagate_pure_bt_l_spec:
  assumes
    \<open>propagate_pure_l_pre L S\<close> and
    \<open>undefined_lit (get_trail_l S) L\<close>
  shows \<open>propagate_pure_bt_l L S \<le> SPEC (\<lambda>T. cdcl_twl_pure_remove_l S T)\<close>
proof -
  have [iff]: \<open>\<not>(\<forall>b. \<not> b)\<close> \<open>(\<exists>b. b)\<close>
    by blast+
  show ?thesis
    using assms
    unfolding propagate_pure_bt_l_def cons_trail_propagate_l_def
    apply (cases S)
    apply refine_vcg
    subgoal by simp
    subgoal by auto
    subgoal
      unfolding propagate_pure_l_pre_def
      apply (subst cdcl_twl_pure_remove_l.simps)
      apply simp
      apply (clarsimp simp add: propagate_pure_l_pre_def get_init_clss_l_def
        all_init_lits_of_l_def all_lits_of_mm_union)
      apply metis
      done
    done
qed


lemma in_all_lits_of_mm_direct_inI: \<open>-L \<in> \<Union>(set_mset ` set_mset A) \<Longrightarrow> L \<in># all_lits_of_mm A\<close>
  by (auto simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset
    dest!: multi_member_split)
lemma cdcl_twl_pure_remove_l_same:
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close>
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> clauses_to_update_l T = clauses_to_update_l S\<close>
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_conflict_l T = get_conflict_l S\<close>
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_init_clss_l T = get_init_clss_l S\<close>
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_subsumed_init_clauses_l T = get_subsumed_init_clauses_l S\<close>
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_init_clauses0_l T = get_init_clauses0_l S\<close>
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S)\<close> and
 cdcl_twl_pure_remove_l_same_unit_init_subsetD:
  \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_unit_init_clauses_l S \<subseteq># get_unit_init_clauses_l T\<close>
proof -
  have [iff]: \<open>\<not>(\<forall>b. \<not> b)\<close>
    by blast
  have [simp]: \<open>L \<in># a \<Longrightarrow>-L \<in># all_lits_of_m (a)\<close>\<open>L \<in># a \<Longrightarrow>L \<in># all_lits_of_m (a)\<close> for L a
    by (simp_all add: atm_of_lit_in_atms_of in_all_lits_of_m_ain_atms_of_iff in_clause_in_all_lits_of_m)
  have [simp]: \<open>- L \<in># all_lits_of_mm b \<longleftrightarrow> L \<in># all_lits_of_mm b\<close> for b L
    by (cases L; auto simp: all_lits_of_mm_def)
  show
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> clauses_to_update_l T = clauses_to_update_l S\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_conflict_l T = get_conflict_l S\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_init_clss_l T = get_init_clss_l S\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_subsumed_init_clauses_l T = get_subsumed_init_clauses_l S\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_init_clauses0_l T = get_init_clauses0_l S\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S)\<close>
    \<open>cdcl_twl_pure_remove_l S T \<Longrightarrow> get_unit_init_clauses_l S \<subseteq># get_unit_init_clauses_l T\<close>
    by (solves \<open>auto simp: cdcl_twl_pure_remove_l.simps all_init_lits_of_l_def get_init_clss_l_def
      all_lits_of_mm_add_mset all_lits_of_m_add_mset
      intro: in_all_lits_of_mm_direct_inI
      dest!: multi_member_split[of \<open>_\<close> \<open>ran_m _\<close>]
        multi_member_split[of \<open>_\<close> \<open>_ :: _ clauses\<close>]\<close>)+
     (auto simp: cdcl_twl_pure_remove_l.simps all_init_lits_of_l_def get_init_clss_l_def
      all_lits_of_mm_add_mset all_lits_of_m_add_mset all_lits_of_mm_union
      intro: in_all_lits_of_mm_direct_inI
      dest!: multi_member_split[of \<open>_\<close> \<open>ran_m _\<close>]
        multi_member_split[of \<open>_\<close> \<open>_ :: _ clauses\<close>])
qed

lemma rtranclp_cdcl_twl_pure_remove_l_same:
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close>
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> clauses_to_update_l T = clauses_to_update_l S\<close>
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> get_conflict_l T = get_conflict_l S\<close>
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> get_init_clss_l T = get_init_clss_l S\<close>
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> get_subsumed_init_clauses_l T = get_subsumed_init_clauses_l S\<close>
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> get_init_clauses0_l T = get_init_clauses0_l S\<close>
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S)\<close> and
  rtranclp_cdcl_twl_pure_remove_l_same_unit_init_subsetD:
  \<open>cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<Longrightarrow> get_unit_init_clauses_l S \<subseteq># get_unit_init_clauses_l T\<close>
  by (solves \<open>induction rule: rtranclp_induct; auto simp: cdcl_twl_pure_remove_l_same
    dest: cdcl_twl_pure_remove_l_same_unit_init_subsetD\<close>)+


subsection \<open>Pure Literal deletion\<close>

text \<open>
  Pure literal deletion is not really used nowadays (as it is subsumed by variable elimination),
  but it is the first non-model preserving model we intend to implement and it should be easy to
  implement.

  In the implementation, it would better to simplify also when going over the clauses, instead of 
  either (i) no simplifying anything or (ii) simplify all clauses. However, in the current version,
  I can reuse the other proofs.

  \<close>

definition pure_literal_deletion_pre where
  \<open>pure_literal_deletion_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
  clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
  count_decided (get_trail_l S) = 0 \<and> twl_list_invs S \<and> twl_struct_invs S')\<close>

definition pure_literal_deletion_candidates where
  \<open>pure_literal_deletion_candidates S = SPEC (\<lambda>Ls. set_mset Ls \<subseteq> atms_of_mm (get_all_init_clss_l S))\<close>

definition pure_literal_deletion_l_inv where
  \<open>pure_literal_deletion_l_inv S xs0 = (\<lambda>(T, xs).
     \<exists>S'. (S, S') \<in> twl_st_l None \<and> cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T \<and> xs \<subseteq># xs0)\<close>


definition pure_literal_deletion_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>pure_literal_deletion_l S = do {
    ASSERT (pure_literal_deletion_pre S);
    let As = \<Union>(set_mset ` set_mset (mset `# get_init_clss_l S));
    xs \<leftarrow> pure_literal_deletion_candidates S;
    (S, xs) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_deletion_l_inv S xs\<^esup> (\<lambda>(S, xs). xs \<noteq> {#})
      (\<lambda>(S, xs). do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># xs);
        A \<leftarrow> RES {Pos L, Neg L};
        if -A \<notin> As \<and> undefined_lit (get_trail_l S) A
        then do {S \<leftarrow> propagate_pure_bt_l A S;
          RETURN (S, remove1_mset L xs)}
        else RETURN (S, remove1_mset L xs)
      })
    (S, xs);
  RETURN S
  }\<close>


lemma pure_literal_deletion_l_spec:
  assumes \<open>pure_literal_deletion_pre S\<close>
  shows
    \<open>pure_literal_deletion_l S \<le> SPEC (\<lambda>T. cdcl_twl_pure_remove_l\<^sup>*\<^sup>* S T)\<close>
proof -
  have [simp]: \<open>a - Suc b < a - b \<longleftrightarrow> Suc b \<le> a\<close> for a b
    by auto
  have [refine0]: \<open>wf (measure (\<lambda>(_, x). size x))\<close>
    by auto
  show ?thesis
    unfolding pure_literal_deletion_l_def Let_def pure_literal_deletion_candidates_def
    apply (refine_vcg propagate_pure_bt_l_spec[THEN order_trans])
    subgoal using assms by fast
    subgoal unfolding pure_literal_deletion_l_inv_def pure_literal_deletion_pre_def
      by fast
    subgoal for x s T xs L unfolding propagate_pure_l_pre_def pure_literal_deletion_l_inv_def
       case_prod_beta pure_literal_deletion_pre_def
      apply normalize_goal+
      apply (frule rtranclp_cdcl_twl_pure_remove_l_cdcl_twl_pure_remove)
      apply assumption+
      apply normalize_goal+
      apply (rule_tac x=xd in exI)
      using rtranclp_cdcl_twl_pure_remove_l_same_unit_init_subsetD[of S T]
      unfolding atms_of_ms_def[symmetric]
      apply (auto simp add: rtranclp_cdcl_twl_pure_remove_l_same
        all_init_lits_of_l_def in_all_lits_of_mm_ain_atms_of_iff 
        dest!: multi_member_split[of L xs] multi_member_split[of L x]
        mset_subset_eq_insertD)
      apply (metis UnCI atms_of_ms_union set_mset_union subset_mset.le_iff_add)
      by (metis Un_iff atms_of_ms_union set_mset_union subset_mset.le_iff_add)
    subgoal by simp
    subgoal by (auto dest!: multi_member_split
      simp: pure_literal_deletion_l_inv_def)
    subgoal by (auto dest!: multi_member_split
      simp: pure_literal_deletion_l_inv_def)
    subgoal
      by (simp add: pure_literal_deletion_l_inv_def)
    subgoal
      by (auto dest!: multi_member_split)
    subgoal by (simp add: pure_literal_deletion_l_inv_def)
    done
qed




definition pure_literal_count_occs_l_clause_invs :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow>_\<Rightarrow> nat \<times> ('v literal \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>pure_literal_count_occs_l_clause_invs C S occs = (\<lambda>(i, occs2). i \<le> length (get_clauses_l S \<propto> C) \<and>
     (\<forall>L. occs2 L = (occs L \<or> (L \<in> set (take i (get_clauses_l S \<propto> C))))))\<close>

definition pure_literal_count_occs_l_clause_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>pure_literal_count_occs_l_clause_pre C S occs = (C \<in># dom_m (get_clauses_l S) \<and> irred (get_clauses_l S) C)\<close>

definition pure_literal_count_occs_l_clause :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> _ \<Rightarrow> ('v literal \<Rightarrow> bool) nres\<close> where
  \<open>pure_literal_count_occs_l_clause C S occs = do {
    ASSERT (pure_literal_count_occs_l_clause_pre C S occs);
    (i, occs) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_count_occs_l_clause_invs C S occs\<^esup> (\<lambda>(i, occs). i < length (get_clauses_l S \<propto> C))
      (\<lambda>(i, occs). do {
        let L = get_clauses_l S \<propto> C ! i;
        let occs = occs (L := True);
        RETURN (i+1, occs)
      })
      (0, occs);
   RETURN occs
 }\<close>


lemma pure_literal_count_occs_l_clause_spec:
  assumes \<open>pure_literal_count_occs_l_clause_pre C S occs\<close>
  shows \<open>pure_literal_count_occs_l_clause C S occs \<le> SPEC (\<lambda>occs2.
     (occs2 = (\<lambda>L. if L \<in> set (get_clauses_l S \<propto> C) then True else occs L)))\<close>
proof -
  have [iff]: \<open>(\<forall>j. \<not> j < a) \<longleftrightarrow> a = 0\<close> for a :: nat
    by auto
  have [simp]: \<open>filter_mset P xs - xs = {#}\<close> for P xs
    by (induction xs) auto
  have [refine0]: \<open>wf (measure (\<lambda>(A, _). length (get_clauses_l S \<propto> C) - A))\<close>
    by auto
  show ?thesis
    unfolding pure_literal_count_occs_l_clause_def
    apply (refine_vcg)
    subgoal using assms by fast
    subgoal unfolding pure_literal_count_occs_l_clause_invs_def
      by (auto dest: in_diffD dest: multi_member_split)
    subgoal unfolding pure_literal_count_occs_l_clause_invs_def
      apply simp
      by (metis in_set_conv_iff less_Suc_eq)
    subgoal
      by auto
    subgoal unfolding pure_literal_count_occs_l_clause_invs_def
      by auto
    done
qed

definition pure_literal_count_occs_l_pre :: \<open>_\<close> where
  \<open>pure_literal_count_occs_l_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
    clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S') \<and>
    count_decided (get_trail_l S) = 0 \<and> twl_list_invs S \<and> twl_struct_invs S')\<close>

definition pure_literal_count_occs_l_inv :: \<open>'v twl_st_l \<Rightarrow> nat multiset \<Rightarrow> nat multiset \<times> ('v literal \<Rightarrow> bool) \<times> bool \<Rightarrow> _\<close> where
  \<open>pure_literal_count_occs_l_inv S xs0 = (\<lambda>(A, occs, _). A \<subseteq># xs0 \<and>
    (occs = (\<lambda>L. L\<in>\<Union>(set_mset ` set_mset (mset `# (\<lambda>C. get_clauses_l S \<propto> C) `# ({#C \<in># xs0. (C \<in># dom_m (get_clauses_l S) \<and> irred (get_clauses_l S) C)#} - A))))))\<close>

text \<open>We allow the solver to abort the search (for example if you already know that there are no 
pure literals).\<close>

definition pure_literal_count_occs_l :: \<open>'v twl_st_l \<Rightarrow> _\<close> where
  \<open>pure_literal_count_occs_l S = do {
  ASSERT (pure_literal_count_occs_l_pre S);
  xs \<leftarrow> SPEC (\<lambda>xs. distinct_mset xs \<and> (\<forall>C\<in>#dom_m (get_clauses_l S). irred (get_clauses_l S) C \<longrightarrow> C \<in># xs));
  abort \<leftarrow> RES (UNIV :: bool set);
  let occs = (\<lambda>_. False);
  (_, occs, abort) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_count_occs_l_inv S xs\<^esup>(\<lambda>(A, occs, abort). A \<noteq> {#} \<and> \<not>abort)
      (\<lambda>(A, occs, abort). do {
        ASSERT (A \<noteq> {#});
        C \<leftarrow> SPEC (\<lambda>C. C \<in># A);
        if (C \<in># dom_m (get_clauses_l S) \<and> irred (get_clauses_l S) C) 
        then do {
            occs \<leftarrow> pure_literal_count_occs_l_clause C S occs;
            abort \<leftarrow> RES (UNIV :: bool set);
            RETURN (remove1_mset C A, occs, abort)
        } else RETURN  (remove1_mset C A, occs, abort)
      })
      (xs, occs, abort);
   RETURN (abort, occs)
  }\<close>

(*TODO Move*)
lemma filter_mset_remove_itself [simp]: \<open>filter_mset P xs - xs = {#}\<close> for P xs
  by (induction xs) auto
(*END Move*)

lemma pure_literal_count_occs_l_spec:
  assumes \<open>pure_literal_count_occs_l_pre S\<close>
  shows \<open>pure_literal_count_occs_l S \<le> SPEC (\<lambda>(abort, occs). \<not>abort \<longrightarrow>
     (\<forall>L. occs L = (L \<in> \<Union>(set_mset ` set_mset (mset `# get_init_clss_l S)))))\<close>
proof -
  have H: \<open>y\<notin># A \<Longrightarrow> x \<in># A - remove1_mset y B \<longleftrightarrow> x \<in># A - B \<close> for x y A B
    apply (auto simp: minus_remove1_mset_if)
    done
  have [refine0]: \<open>wf (measure (\<lambda>(A, _). size A))\<close>
    by auto
  show ?thesis
    unfolding pure_literal_count_occs_l_def
    apply (refine_vcg pure_literal_count_occs_l_clause_spec)
    subgoal using assms by fast
    subgoal unfolding pure_literal_count_occs_l_inv_def
      by (auto dest: in_diffD dest: multi_member_split)
    subgoal by auto
    subgoal
      unfolding pure_literal_count_occs_l_clause_pre_def
      by simp
    subgoal for x abort s a b aa ba xa xb xc (*TODO Proof*)
      using distinct_mset_dom[of \<open>get_clauses_l S\<close>]
      apply (auto dest!: multi_member_split[of \<open>_ :: nat\<close> a] multi_member_split[of xa] dest: mset_subset_eq_insertD
        simp add: pure_literal_count_occs_l_inv_def intro!: ext split: if_splits)
      apply (meson in_multiset_minus_notin_snd mset_subset_eqD union_single_eq_member)
      apply (metis (no_types, lifting) add_mset_remove_trivial distinct_mem_diff_mset distinct_mset_filter in_diffD in_multiset_minus_notin_snd)
      by (metis (no_types, lifting) diff_add_mset_swap insert_DiffM insert_noteq_member mset_subset_eqD)
    subgoal
      by (auto dest!: multi_member_split)
    subgoal for x abort s a b aa ba xa
      by (auto simp: pure_literal_count_occs_l_inv_def minus_remove1_mset_if)
    subgoal
      by (auto dest!: multi_member_split)
    subgoal
      by (auto simp: pure_literal_count_occs_l_inv_def get_init_clss_l_def ran_m_def
        eq_commute[of _ \<open>the _\<close>] all_conj_distrib conj_disj_distribR ex_disj_distrib
        dest!: multi_member_split)
    done
qed


definition pure_literal_deletion_l2 :: \<open>_ \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>pure_literal_deletion_l2 occs S = do {
    ASSERT (pure_literal_deletion_pre S);
    let As = \<Union>(set_mset ` set_mset (mset `# get_init_clss_l S));
    xs \<leftarrow> pure_literal_deletion_candidates S;
    (S, xs) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_deletion_l_inv S xs\<^esup> (\<lambda>(S, xs). xs \<noteq> {#})
      (\<lambda>(S, xs). do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># xs);
        let A = (if occs (Pos L) \<and> \<not>occs (Neg L) then Pos L else Neg L);
        if \<not>occs (-A) \<and> undefined_lit (get_trail_l S) A
        then do {S \<leftarrow> propagate_pure_bt_l A S;
          RETURN (S, remove1_mset L xs)}
        else RETURN (S, remove1_mset L xs)
      })
    (S, xs);
  RETURN S
  }\<close>

lemma pure_literal_deletion_l2_pure_literal_deletion_l:
  assumes \<open>(\<forall>L. occs L = (L \<in> \<Union>(set_mset ` set_mset (mset `# get_init_clss_l S))))\<close>
  shows \<open>pure_literal_deletion_l2 occs S \<le> \<Down>Id (pure_literal_deletion_l S)\<close>
proof -
  have 1: \<open>a=b \<Longrightarrow> (a,b) \<in> Id\<close> and 2: \<open>c \<in> \<Phi> \<Longrightarrow> RETURN c \<le>\<Down>Id (RES \<Phi>)\<close> and
    3: \<open>e = f \<Longrightarrow> e \<le>\<Down>Id f\<close> for a b c \<Phi> e f
    by auto
  show ?thesis
    unfolding pure_literal_deletion_l2_def pure_literal_deletion_l_def
    apply (refine_vcg)
    apply (rule 1)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule 2)
    subgoal by auto
    subgoal using assms by (auto split: if_splits)
    apply (rule 3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition pure_literal_elimination_round_pre where
  \<open>pure_literal_elimination_round_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and> twl_list_invs S \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T)) \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
    clauses_to_update_l S = {#} \<and>
    count_decided (get_trail_l S) = 0)\<close>

definition pure_literal_elimination_round where
  \<open>pure_literal_elimination_round S = do {
    ASSERT (pure_literal_elimination_round_pre S);
    S \<leftarrow> simplify_clauses_with_units_st S;
    if get_conflict_l S = None
    then do {
     (abort, occs) \<leftarrow> pure_literal_count_occs_l S;
      if \<not>abort then pure_literal_deletion_l2 occs S
      else RETURN S}
    else RETURN S
}\<close>

lemma pure_literal_elimination_round:
  assumes \<open>pure_literal_elimination_round_pre S\<close>
  shows \<open>pure_literal_elimination_round S \<le> SPEC (\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T)\<close>
proof -
  have pure_literal_deletion_pre: \<open>pure_literal_elimination_round_pre S \<Longrightarrow>
    cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S x \<and> simplify_clauses_with_unit_st_inv S {} x \<Longrightarrow>
    get_conflict_l x = None \<Longrightarrow>
    pure_literal_deletion_pre x\<close> for x
    unfolding pure_literal_deletion_pre_def pure_literal_elimination_round_pre_def apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_twl_st_l; assumption?)
    apply (rule_tac x=V in exI)
    apply (simp add: rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l
      rtranclp_cdcl_twl_inprocessing_l_count_decided)
    done
  have pure_literal_count_occs_l_pre: \<open>pure_literal_elimination_round_pre S \<Longrightarrow>
    cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S x \<and> simplify_clauses_with_unit_st_inv S {} x \<Longrightarrow>
    get_conflict_l x = None \<Longrightarrow>
    pure_literal_count_occs_l_pre x\<close> for x
    unfolding pure_literal_count_occs_l_pre_def pure_literal_elimination_round_pre_def apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_twl_st_l; assumption?)
    apply (rule_tac x=V in exI)
    apply (auto simp add: rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l simplify_clauses_with_unit_st_inv_def
      rtranclp_cdcl_twl_inprocessing_l_count_decided)
    done

  obtain T where
    T: \<open> (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and> twl_list_invs S \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T)) \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
    clauses_to_update_l S = {#} \<and>
    count_decided (get_trail_l S) = 0\<close>
    using assms unfolding pure_literal_elimination_round_pre_def by blast
  show ?thesis
    unfolding pure_literal_elimination_round_def
    apply (refine_vcg
      simplify_clauses_with_units_st_spec[THEN order_trans, of _ T])
    subgoal using assms by auto
    subgoal using T by blast
    subgoal using T by blast
    subgoal using T by blast
    subgoal using T by blast
    subgoal using T by blast
    subgoal using T by blast
    subgoal using T by blast
    apply (subst Down_id_eq)
    apply (refine_vcg pure_literal_count_occs_l_spec
      pure_literal_deletion_l2_pure_literal_deletion_l[THEN order_trans]
      pure_literal_deletion_l_spec[THEN order_trans])
    subgoal by (rule pure_literal_count_occs_l_pre)
    subgoal by auto
    subgoal
      apply (subst Down_id_eq)
      apply (rule pure_literal_deletion_l_spec[THEN order_trans])
      apply (simp_all add: pure_literal_deletion_pre)
      by (smt (verit, best) Collect_mono cdcl_twl_inprocessing_l.intros(5) mono_rtranclp rtranclp_trans)
    subgoal by auto
    subgoal by auto
    done
qed


definition pure_literal_elimination_l_pre where
  \<open>pure_literal_elimination_l_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T \<and> twl_list_invs S \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T)) \<and>
    set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0} \<and>
    clauses_to_update_l S = {#} \<and>
    count_decided (get_trail_l S) = 0)\<close>

definition pure_literal_elimination_l_inv where
  \<open>pure_literal_elimination_l_inv S max_rounds = (\<lambda>(T,n,_). n \<le> max_rounds \<and> cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T)\<close>

definition pure_literal_elimination_l :: \<open>_\<close> where
  \<open>pure_literal_elimination_l S = do {
     ASSERT (pure_literal_elimination_l_pre S);
     max_rounds \<leftarrow> RES (UNIV :: nat set);
    (S, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_elimination_l_inv S max_rounds\<^esup> (\<lambda>(S, m, abort). m < max_rounds \<and> \<not>abort)
     (\<lambda>(S, m, abort). do {
         S \<leftarrow> pure_literal_elimination_round S;
         abort \<leftarrow> RES (UNIV :: bool set);
         RETURN (S, m+1, abort)
       })
    (S, 0, False);
   RETURN S
  }\<close>


lemma pure_literal_elimination_l:
  assumes \<open>pure_literal_elimination_l_pre S\<close>
  shows \<open>pure_literal_elimination_l S \<le> SPEC (\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T)\<close>
proof -
  have [refine0]: \<open>max_rounds \<in> UNIV \<Longrightarrow> wf (measure (\<lambda>(S,n,m). max_rounds - n))\<close> for max_rounds
    by auto
  have H: \<open>pure_literal_elimination_l_pre S \<Longrightarrow>
    x \<in> UNIV \<Longrightarrow>
    pure_literal_elimination_l_inv S x s \<Longrightarrow>
    case s of (S, m, abort) \<Rightarrow> m < x \<and> \<not> abort \<Longrightarrow>
      s = (a, b) \<Longrightarrow> b = (aa, ba) \<Longrightarrow> pure_literal_elimination_round_pre a\<close> for x s a aa ba b S
    apply hypsubst
    unfolding pure_literal_elimination_round_pre_def pure_literal_elimination_l_inv_def
        pure_literal_elimination_l_pre_def prod.simps
    apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_twl_st_l; assumption?)
    apply (rule_tac x=V in exI)
    apply (auto simp add: rtranclp_cdcl_twl_inprocessing_l_clauses_to_update_l simplify_clauses_with_unit_st_inv_def
      rtranclp_cdcl_twl_inprocessing_l_count_decided
      dest: rtranclp_cdcl_twl_inprocessing_l_get_all_mark_of_propagated)
    done
  show ?thesis
    unfolding pure_literal_elimination_l_def
    apply (refine_vcg pure_literal_elimination_round)
    subgoal using assms by auto
    apply assumption
    subgoal unfolding pure_literal_elimination_l_inv_def by auto
    subgoal by (rule H)
    subgoal by (auto simp: pure_literal_elimination_l_inv_def)
    subgoal by auto
    subgoal by (auto simp: pure_literal_elimination_l_inv_def)
    done
qed


definition pure_literal_elimination_l_needed :: \<open>'v twl_st_l \<Rightarrow> bool nres\<close> where
  \<open>pure_literal_elimination_l_needed S = SPEC (\<lambda>_. True)\<close>

definition pure_literal_eliminate_l :: \<open>_\<close> where
  \<open>pure_literal_eliminate_l S = do {
     ASSERT (pure_literal_elimination_l_pre S);
     b \<leftarrow> pure_literal_elimination_l_needed S;
     if b then pure_literal_elimination_l S else RETURN S
  }\<close>


lemma pure_literal_eliminate_l:
  assumes \<open>pure_literal_elimination_l_pre S\<close>
  shows \<open>pure_literal_eliminate_l S \<le> SPEC (\<lambda>T. cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T)\<close>
  unfolding pure_literal_eliminate_l_def pure_literal_elimination_l_needed_def
  by (refine_vcg pure_literal_elimination_l)
   (use assms in auto)

end
