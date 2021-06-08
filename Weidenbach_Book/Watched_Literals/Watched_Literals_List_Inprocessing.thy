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
     (unc \<longrightarrow> N = N'))
  })\<close>

definition simplify_clause_with_unit_st_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>simplify_clause_with_unit_st_pre = (\<lambda>C S.
  C \<in># dom_m (get_clauses_l S) \<and> count_decided (get_trail_l S) = 0 \<and> get_conflict_l S = None \<and> clauses_to_update_l S = {#} \<and>
    twl_list_invs S \<and>
   (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T)
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
  assumes \<open>C \<in># dom_m (get_clauses_l S)\<close> \<open>count_decided (get_trail_l S) = 0\<close>
    \<open>get_conflict_l S = None\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T))\<close> and
    annot: \<open>set (get_all_mark_of_propagated (get_trail_l S)) \<subseteq> {0}\<close>
  shows \<open>simplify_clause_with_unit_st C S \<le> \<Down>Id (SPEC(\<lambda>T.
      (S = T \<or> cdcl_twl_unitres_l S T \<or> cdcl_twl_unitres_true_l S T) \<and>
    (set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq>
       set (get_all_mark_of_propagated (get_trail_l S)) \<union> {0}) \<and>
      (dom_m (get_clauses_l T) = dom_m (get_clauses_l S) \<or>
          dom_m (get_clauses_l T) = remove1_mset C (dom_m (get_clauses_l S)))))\<close>
proof -
  have C0: \<open>C \<noteq> 0\<close> \<open>C \<notin> set (get_all_mark_of_propagated (get_trail_l S))\<close>
    using list_invs assms(1) annot
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
    (unc \<longrightarrow> (aa = N')) \<Longrightarrow>
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
    (unc \<longrightarrow> (aa = N'))  \<Longrightarrow>
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
      (unc \<longrightarrow> aa = N') \<Longrightarrow>
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
    (unc \<longrightarrow> aa = N') \<Longrightarrow>
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
    using list_invs assms(1)
    by (auto simp: twl_list_invs_def)
  then show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding simplify_clause_with_unit_st_def simplify_clause_with_unit_def Let_def
    apply refine_vcg
    subgoal using assms unfolding simplify_clause_with_unit_st_pre_def
      apply (intro conjI)
      apply (simp; fail)+
      apply (rule exI[of _ T], simp)
      done
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using n_d by simp
    subgoal using assms by (auto simp: twl_list_invs_def)
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
      using ST st_invs C0 apply -
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
      using count_decided_ge_get_level[of \<open>get_trail_l S\<close>] ST st_invs C0
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
      by (auto  simp: list_length_2_isabelle_come_on twl_list_invs_def
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
    done
qed


definition forward_subsumption_one_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_pre = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, WS, Q). C \<in># dom_m N \<and>
    (\<forall>L \<in># mset (N \<propto> C). undefined_lit M L))\<close>

datatype 'v subsumption = SUBSUMED nat | STRENGTHEN \<open>'v literal\<close> nat | NONE
definition try_to_subsume :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v clauses_l \<Rightarrow> 'v subsumption \<Rightarrow> bool\<close> where
  \<open>try_to_subsume C C' N s = (case s of
    NONE \<Rightarrow> True
  | SUBSUMED C'' \<Rightarrow> mset (N \<propto> C') \<subseteq># mset (N \<propto> C) \<and> C'' = C'
  | STRENGTHEN L C'' \<Rightarrow> L \<in># mset (N \<propto> C') \<and> -L \<in># mset (N \<propto> C) \<and>
   mset (N \<propto> C) - {#L#} \<subseteq># mset (N \<propto> C') - {#L#} \<and> C'' = C')\<close>

definition strengthen_clause where
  \<open>strengthen_clause = (\<lambda>C C' L (N, NE, UE, NS, US).
  if size C = size C'
  then RETURN (fmupd C (remove1 (-L) (N \<propto> C), irred N C \<or> irred N C') N, NE, UE,
     ((if irred N C' then add_mset (mset (N \<propto> C')) else id)  o (if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
     ((if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) o (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US)
  else RETURN (fmupd C (remove1 (-L) (N \<propto> C), irred N C) N, NE, UE,
    (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
    (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US))\<close>

definition subsume_or_strengthen_pre :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> _ \<Rightarrow> 'v clauses_l \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<Rightarrow> bool\<close> where
  \<open>subsume_or_strengthen_pre = (\<lambda>C s M (N, NE, UE, NS, US). C \<in># dom_m N \<and> length (N \<propto> C) > 2 \<and> 
   (case s of
    NONE \<Rightarrow> True
  | SUBSUMED C' \<Rightarrow> mset (N \<propto> C') \<subseteq># mset (N \<propto> C) \<and> C \<notin> set (get_all_mark_of_propagated M) \<and> distinct (N \<propto> C') \<and> C \<noteq> C' \<and> \<not>tautology (mset (N \<propto> C')) \<and> C' \<in># dom_m N
  | STRENGTHEN L C' \<Rightarrow> L \<in># mset (N \<propto> C') \<and> -L \<in># mset (N \<propto> C) \<and>
   mset (N \<propto> C) - {#L#} \<subseteq># mset (N \<propto> C') - {#L#} \<and> C' \<in># dom_m N))\<close>

definition subsume_or_strengthen :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> _ \<Rightarrow> 'v clauses_l \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<Rightarrow>
   ('v clauses_l \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses) nres\<close> where
  \<open>subsume_or_strengthen = (\<lambda>C s M (N, NE, UE, NS, US). do {
   ASSERT(subsume_or_strengthen_pre C s M (N, NE, UE, NS, US));
   (case s of
     NONE \<Rightarrow> RETURN (N, NE, UE, NS, US)
   | SUBSUMED C' \<Rightarrow> RETURN (fmdrop C (if \<not>irred N C' \<and> irred N C then fmupd C' (N \<propto> C', True) N else N),
          NE, UE, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
      (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US)
   | STRENGTHEN L C' \<Rightarrow> strengthen_clause C C' L (N, NE, UE, NS, US))
  })\<close>

inductive cdcl_twl_inprocessing_l for S T where
  \<open>cdcl_twl_unitres_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close> |
  \<open>cdcl_twl_unitres_true_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close> |
  \<open>cdcl_twl_subsumed_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>|
  \<open>cdcl_twl_subresolution_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>

lemma
  assumes \<open>subsume_or_strengthen_pre C s M (N, NE, UE, NS, US)\<close>
  shows
    \<open>subsume_or_strengthen C s M (N, NE, UE, NS, US) \<le>\<Down>Id (SPEC(\<lambda>(N', NE', UE', NS', US').
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)
  (M, N', None, NE', UE', NEk, UEk, NS', US', N0, U0, {#}, Q)))\<close>
  using assms unfolding subsume_or_strengthen_def
  apply refine_vcg+
  subgoal by auto
  subgoal
    apply (cases s)
    subgoal for C'
      by (auto 8 8 simp: subsume_or_strengthen_pre_def cdcl_twl_subsumed_l.simps fmdrop_fmupd
        intro!: cdcl_twl_inprocessing_l.intros(3) r_into_rtranclp)
    subgoal
      apply (auto simp: eq_commute[of N] eq_commute[of NE] eq_commute[of UE] eq_commute[of NS]
        eq_commute[of US])
      apply (auto simp: strengthen_clause_def)

      oops
definition forward_subsumption_one :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>forward_subsumption_one = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, WS, Q). do {
  ASSERT(forward_subsumption_one_pre C (M, N, D, NE, UE, NEk, UEk, NS, US, WS, Q));
  xs \<leftarrow> SPEC (\<lambda>xs. xs \<subseteq># (dom_m N) - {#C#});
  (xs, s) \<leftarrow>
    WHILE (\<lambda>(xs, s). xs \<noteq> {#} \<and> s = NONE)
    (\<lambda>(xs, _). do {
      C' \<leftarrow> SPEC(\<lambda>C'. C' \<in># dom_m N);
      s \<leftarrow> SPEC(try_to_subsume C C' N);
     RETURN (xs, s)
    })
    (xs, NONE);
  (N, NE, UE, NS, US) \<leftarrow> subsume_or_strengthen C s M (N, NE, UE, NS, US);
  RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, WS, Q)
  }
)\<close>

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

lemma cdcl_twl_inprocessing_l_twl_st_l0:
  assumes \<open>cdcl_twl_inprocessing_l S U\<close> and
    \<open>(S, T) \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs T\<close> and
    \<open>twl_list_invs S\<close>
 obtains V where
   \<open>(U, V) \<in> twl_st_l None\<close> and
   \<open>cdcl_twl_unitres T V \<or> cdcl_twl_unitres_true T V \<or> cdcl_twl_subsumed T V \<or>
   cdcl_twl_subresolution T V\<close>
  using assms
  apply (induction rule: cdcl_twl_inprocessing_l.induct)
  using cdcl_twl_unitres_l_cdcl_twl_unitres apply blast
  using cdcl_twl_unitres_true_l_cdcl_twl_unitres_true apply blast
  using cdcl_twl_subsumed_l_cdcl_twl_subsumed apply blast
  using cdcl_twl_subresolution_l_cdcl_twl_subresolution by blast

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
    cdcl_twl_subresolution_l_list_invs)

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
    cdcl_twl_subresolution T V\<close> and
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
      cdcl_twl_subsumed_twl_stgy_invs)
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
         (auto simp: cdcl_twl_inprocessing_l.simps
          cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
          cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
      done
    subgoal
      using st apply (induction rule: rtranclp_induct)
      subgoal using lvl_S by auto
      subgoal
        by (auto simp: cdcl_twl_inprocessing_l.simps
          cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
          cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
      done
    done
  have empty: \<open>set (get_all_mark_of_propagated (get_trail_l T)) \<subseteq> {0}\<close>
    using st apply (induction rule: rtranclp_induct)
    subgoal using empty by auto
    subgoal by (auto simp: cdcl_twl_inprocessing_l.simps
      cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
      cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
    done
  show ?thesis
    unfolding simplify_clauses_with_unit_st_pre_def
    by (rule exI[of _ U])
     (use TU struct_T list_T ent_T clss_upd_T lvl_S empty in auto)
qed

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
  show ?thesis
    using assms
    using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
    supply [[goals_limit=1]]
    by (induction rule: cdcl_twl_inprocessing_l.induct)
     (auto 4 3 simp: cdcl_twl_unitres_l.simps 
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
      dest: all_lits_of_m_mono)
qed

lemma rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l:
  assumes \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T\<close>
  shows \<open>set_mset (all_init_lits_of_l S) = set_mset (all_init_lits_of_l T)\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto dest: cdcl_twl_inprocessing_l_all_init_lits_of_l)

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
      cdcl_twl_subresolution_l.simps
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
        unfolding simplify_clauses_with_unit_st_inv_def
        by normalize_goal+ auto
      apply assumption+
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
    get_conflict_l S = None \<and>
    count_decided (get_trail_l S) = 0)\<close>

definition simplify_clauses_with_units_st where
  \<open>simplify_clauses_with_units_st S = do {
    ASSERT(simplify_clauses_with_units_st_pre S);
    new_units \<leftarrow> SPEC (\<lambda>_. True);
    if new_units
    then simplify_clauses_with_unit_st S
    else RETURN S}\<close>


lemma simplify_clauses_with_units_st_spec:
  assumes \<open>count_decided (get_trail_l S) = 0\<close>
    \<open>get_conflict_l S = None\<close> and
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
  apply assumption+
  subgoal by auto
  subgoal by auto
  subgoal unfolding simplify_clauses_with_unit_st_inv_def by auto
  done

end
