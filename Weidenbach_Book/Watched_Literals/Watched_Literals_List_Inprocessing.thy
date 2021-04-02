theory Watched_Literals_List_Inprocessing
imports Watched_Literals_List Watched_Literals_Algorithm_Reduce
begin

inductive cdcl_twl_subsumed_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
subsumed_II:
  \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C' N, D, NE, UE, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>irred N C'\<close>  \<open>irred N C\<close> \<open>C \<noteq> C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subsumed_RR:
    \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmdrop C' N, D, NE, UE, NS, add_mset (mset (N \<propto> C')) US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>\<not>irred N C'\<close> \<open>\<not>irred N C\<close>\<open>C \<noteq> C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subsumed_IR:
    \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmdrop C' N, D, NE, UE, NS, add_mset (mset (N \<propto> C')) US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
    \<open>irred N C\<close> \<open>\<not>irred N C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> |
subsumed_RI:
    \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd C (N \<propto> C, True) (fmdrop C' N), D, NE, UE, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if \<open>mset (N \<propto> C) \<subseteq># mset (N \<propto> C')\<close> \<open>C \<in># dom_m N\<close> \<open>C' \<in># dom_m N\<close>
nn    \<open>\<not>irred N C\<close> \<open>irred N C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>
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
  obtain M' N' U' D' NE' UE' NS' US' WS' N0' U0' Q' where
    S': \<open>S' = (M', N', U', D', NE', UE', NS', US', N0', U0', WS', Q')\<close>
    by (cases S')

  show ?thesis
    using assms(1)
  proof (cases rule: cdcl_twl_subsumed_l.cases)
    case (subsumed_II N C C' M D NE UE NS US N0 U0 Q)
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
    case (subsumed_RR N C C' M D NE UE NS US N0 U0 Q)
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
    case (subsumed_IR N C C' M D NE UE NS US N0 U0 Q)
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
    case (subsumed_RI N C C' M D NE UE NS US N0 U0 Q)
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
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, True) N, None, NE, UE, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>irred N C'\<close> |
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop C' N, None, add_mset {#K#} NE, UE, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>irred N C'\<close> |
twl_subresolution_LL_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, False) N, None, NE, UE, NS, add_mset (mset (N \<propto> C'))  US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
   (Propagated K 0 # M, fmdrop C' N, None, NE, add_mset {#K#} UE, NS,  add_mset (mset (N \<propto> C')) US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, False) N, None, NE, UE, NS, add_mset (mset (N \<propto> C'))  US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
   (Propagated K 0 # M, fmdrop C' N, None, NE, add_mset {#K#} UE, NS,  add_mset (mset (N \<propto> C')) US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd C' (E, True) N, None, NE, UE, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>irred N C'\<close> |
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop C' N, None, add_mset {#K#} NE, UE, add_mset (mset (N \<propto> C')) NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
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
    SS': \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_subresolution S' T'\<close>
proof -
  show ?thesis
    using assms
      supply [simp] = convert_lits_l_update_sel2
    apply (induction rule: cdcl_twl_subresolution_l.induct)
    subgoal for C N C' L D D' M E NE UE NS US N0 U0 Q
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
  \<open>cdcl_twl_unitres_true_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
  (M, fmdrop C N, None, add_mset (mset (N \<propto> C)) NE, UE, NS, US, N0, U0, {#}, Q)\<close>
  if \<open>L \<in># mset (N \<propto> C)\<close> \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close>
    \<open>C \<in># dom_m N\<close> \<open>irred N C\<close>
    \<open>C \<notin> set (get_all_mark_of_propagated M)\<close> |
  \<open>cdcl_twl_unitres_true_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmdrop C N, None, NE, add_mset (mset (N \<propto> C)) UE, NS, US, N0, U0, {#}, Q)\<close>
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
  by (induction rule: cdcl_twl_subresolution_l.induct)
   (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
    dest: in_diffD)

lemma cdcl_twl_unitres_True_l_list_invs:
  \<open>cdcl_twl_unitres_true_l S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  by (induction rule: cdcl_twl_unitres_true_l.induct)
   (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
    dest: in_diffD)

inductive cdcl_twl_unitres_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd D (E, irred N D) N, None, NE, UE, add_mset (mset (N \<propto> D)) NS, US, N0, U0, {#}, Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = C +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close>
    \<open>struct_wf_twl_cls (twl_clause_of E)\<close>
    \<open>Multiset.Ball (mset E) (undefined_lit M)\<close>
    \<open>mset E = C\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N D\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop D N, None, add_mset {#K#} NE, UE, add_mset (mset (N \<propto> D))  NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = {#K#} +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N D\<close>
    \<open>undefined_lit M K\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmupd D (E, irred N D) N, None, NE, UE, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = C +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close>
    \<open>struct_wf_twl_cls (twl_clause_of E)\<close>
    \<open>Multiset.Ball (mset E) (undefined_lit M)\<close>
    \<open>mset E = C\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N D\<close>
    \<open>atms_of (mset E) \<subseteq> atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop D N, None, NE, add_mset {#K#} UE, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, add_mset (-K) Q)\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>mset (N \<propto> D) = {#K#} +C'\<close>
    \<open>(mset `# init_clss_lf N + NE + NS + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N D\<close>
    \<open>undefined_lit M K\<close>
    \<open>atm_of K \<in> atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmdrop D N, Some {#}, NE, UE, NS, add_mset (mset (N \<propto> D)) US, N0, add_mset {#} U0, {#}, {#})\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>(mset `# init_clss_lf N + NE + NS + N0) \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
    \<open>\<not>irred N D\<close>
    \<open>count_decided M = 0\<close>
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> |
\<open>cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmdrop D N, Some {#}, NE, UE, add_mset (mset (N \<propto> D)) NS, US, add_mset {#} N0, U0, {#}, {#})\<close>
  if
    \<open>D \<in># dom_m N\<close>
    \<open>(mset `# init_clss_lf N + NE + NS + N0) \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
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
  subgoal for D N M C C' NE NS N0 E UE US U0 Q
    apply (auto simp: twl_st_l_def)[]
    apply (rule_tac x=x in exI)
    apply (auto simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I1[where E= \<open>twl_clause_of E\<close> and D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
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
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
      mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
      init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel convert_lits_l_add_mset
      learned_clss_l_fmupd_if learned_clss_l_mapsto_upd convert_lit.intros(3)
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)[]
    done
  subgoal for D N M C C' NE NS N0 E UE US U0 Q
    apply (auto simp: twl_st_l_def)[]
    apply (rule_tac x=x in exI)
    apply (auto 5 3 simp: twl_st_l_def
      intro!: cdcl_twl_unitres_I3[where E= \<open>twl_clause_of E\<close> and D = \<open>twl_clause_of (N \<propto> D)\<close>]
      simp:  init_clss_l_mapsto_upd image_mset_remove1_mset_if
      learned_clss_l_mapsto_upd_irrel
      mset_take_mset_drop_mset'
      init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev
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
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
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
      learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
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
        learned_clss_l_mapsto_upd_irrel convert_lits_l_drop
        mset_take_mset_drop_mset' init_clss_l_mapsto_upd_irrelev
        init_clss_l_fmdrop_irrelev learned_clss_l_l_fmdrop convert_lits_l_update_sel2
        init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_irrel convert_lits_l_add_mset
        learned_clss_l_fmupd_if learned_clss_l_mapsto_upd convert_lit.intros(3)
        init_clss_l_fmdrop learned_clss_l_l_fmdrop_irrelev)
  done

definition simplify_clause_with_unit :: \<open>nat \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> (bool \<times> 'v clauses_l) nres\<close> where
  \<open>simplify_clause_with_unit = (\<lambda>C M N. do {
  SPEC(\<lambda>(b, N'). fmdrop C N = fmdrop C N' \<and> mset (N' \<propto> C) \<subseteq># mset (N \<propto> C) \<and> C \<in># dom_m N' \<and>
     (\<not>b \<longrightarrow> (\<forall>L \<in># mset (N' \<propto> C). undefined_lit M L)) \<and>
     (\<forall>L \<in># mset (N \<propto> C) - mset (N' \<propto> C). -L \<in> lits_of_l M) \<and>
     (irred N C = irred N' C) \<and>
     (b \<longleftrightarrow> (\<exists>L. L \<in># mset (N \<propto> C) \<and> L \<in> lits_of_l M)))
  })\<close>

definition simplify_clause_with_unit_st_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>simplify_clause_with_unit_st_pre = (\<lambda>C S.
    C \<in># dom_m (get_clauses_l S) \<and> count_decided (get_trail_l S) = 0 \<and> get_conflict_l S = None \<and> clauses_to_update_l S = {#} \<and>
    C \<notin> set (get_all_mark_of_propagated (get_trail_l S)) \<and>
   (\<exists>T. (S, T) \<in> twl_st_l None \<and> twl_struct_invs T)
)\<close>

definition simplify_clause_with_unit_st :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>simplify_clause_with_unit_st = (\<lambda>C (M, N, D, NE, UE, NS, US, N0, U0, WS, Q). do {
    ASSERT (C \<in># dom_m N \<and> count_decided M = 0 \<and> D = None \<and> WS = {#} \<and> C \<notin> set (get_all_mark_of_propagated M));
    let E = mset (N \<propto> C);
    let irr = irred N C;
    (b, N) \<leftarrow> simplify_clause_with_unit C M N;
    if b then
      RETURN (M, fmdrop C N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NS, US, N0, U0, WS, Q)
    else if size (N \<propto> C) = 1
    then do {
      let L = ((N \<propto> C) ! 0);
      RETURN (Propagated L 0 # M, fmdrop C N, D, (if irr then add_mset {#L#} else id) NE, (if \<not>irr then add_mset {#L#} else id)UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, WS, add_mset (-L) Q)}
    else if size (N \<propto> C) = 0
      then RETURN (M, fmdrop C N, Some {#}, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, WS, {#})
    else
        RETURN (M, N, D, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, WS, Q)
  })\<close>

lemma true_clss_clss_def_more_atms:
  "N \<Turnstile>ps N' \<longleftrightarrow> (\<forall>I. total_over_m I (N \<union> N' \<union> N'') \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile>s N')"
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
  fixes M :: \<open>('v, nat) ann_lit list\<close> and N NE UE NS US N0 U0 Q
  defines \<open>S \<equiv> (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
  assumes
    \<open>D \<in># dom_m N\<close>
    \<open>count_decided M = 0\<close> and
    \<open>D \<notin> set (get_all_mark_of_propagated M)\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close> and
    dec: \<open>count_decided (get_trail_l S) = 0\<close> and
    false: \<open>\<forall>L \<in># C'. -L \<in> lits_of_l (get_trail_l S)\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  shows cdcl_twl_unitres_l_intros2':
      \<open>irred N D \<Longrightarrow> undefined_lit M K \<Longrightarrow> mset (N \<propto> D) = {#K#} +C' \<Longrightarrow>
    cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
       (Propagated K 0 # M, fmdrop D N, None, add_mset {#K#} NE, UE, add_mset (mset (N \<propto> D))  NS, US, N0, U0, {#}, add_mset (-K) Q)\<close>
       (is \<open>?A \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?B\<close>) and
    cdcl_twl_unitres_l_intros4':
    \<open>\<not>irred N D \<Longrightarrow> undefined_lit M K \<Longrightarrow> mset (N \<propto> D) = {#K#} +C' \<Longrightarrow> 
    cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (Propagated K 0 # M, fmdrop D N, None, NE, add_mset {#K#} UE, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, add_mset (-K) Q)\<close>
    (is \<open>?A' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?B'\<close>) and
    cdcl_twl_unitres_false_entailed:
       \<open>(mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S + get_subsumed_init_clauses_l S + get_init_clauses0_l S) \<Turnstile>psm mset_set (CNot C')\<close> and
    cdcl_twl_unitres_l_intros5':
      \<open>\<not>irred N D \<Longrightarrow> mset (N \<propto> D) = C' \<Longrightarrow>
      cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
         (M, fmdrop D N, Some {#}, NE, UE, NS, add_mset (mset (N \<propto> D)) US, N0,
           add_mset {#} U0, {#}, {#})\<close>
       (is \<open>?E \<Longrightarrow> _ \<Longrightarrow> ?F\<close>)  and
  cdcl_twl_unitres_l_intros6':
    \<open>irred N D \<Longrightarrow> mset (N \<propto> D) = C' \<Longrightarrow>
    cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, fmdrop D N, Some {#}, NE, UE, add_mset (mset (N \<propto> D)) NS, US, add_mset {#} N0,
    U0, {#}, {#})\<close>
    (is \<open>?E' \<Longrightarrow> _ \<Longrightarrow> ?F'\<close>) and
  cdcl_twl_unitres_l_intros1':
    \<open>irred N D \<Longrightarrow> mset (N \<propto> D) = mset C +C' \<Longrightarrow> length C \<ge> 2 \<Longrightarrow> \<not>tautology (mset (N \<propto> D)) \<Longrightarrow>
    \<forall>L\<in>set C. undefined_lit M L \<Longrightarrow> N' = fmupd D (C, irred N D) N \<Longrightarrow>
      cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
        (M, N', None, NE, UE, add_mset (mset (N \<propto> D)) NS, US, N0, U0, {#}, Q)\<close>
    (is \<open>?G \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _  \<Longrightarrow> _ \<Longrightarrow> ?H\<close>) and
  cdcl_twl_unitres_l_intros3':
    \<open>\<not>irred N D \<Longrightarrow> mset (N \<propto> D) = mset C +C' \<Longrightarrow> length C \<ge> 2 \<Longrightarrow> \<not>tautology (mset (N \<propto> D)) \<Longrightarrow>
    \<forall>L\<in>set C. undefined_lit M L \<Longrightarrow> N' = fmupd D (C, irred N D) N \<Longrightarrow>
    cdcl_twl_unitres_l (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
    (M, N', None, NE, UE, NS, add_mset (mset (N \<propto> D)) US, N0, U0, {#}, Q)\<close>
    (is \<open>?G' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?H'\<close>)
proof -
  have \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ((state\<^sub>W_of T)))
    (get_all_ann_decomposition (trail ((state\<^sub>W_of T))))\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of T)\<close> and
    tauto: \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of T). \<not> tautology s\<close>
    using st_invs unfolding twl_struct_invs_def unfolding pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def state\<^sub>W_of_def
    by fast+
  moreover have \<open>(\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m b \<and> snd a} \<union> set_mset d \<union> f \<union> h \<union> U\<Turnstile>ps
       unmark_l aa \<Longrightarrow>
       (a, aa) \<in> convert_lits_l b (d + e) \<Longrightarrow>
    (\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m b \<and> snd a} \<union> set_mset d \<union> f \<union> h \<Turnstile>ps U \<Longrightarrow>
       - L \<in> lits_of_l a \<Longrightarrow>
    (\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m b \<and> snd a} \<union> set_mset d \<union> f \<union> h \<Turnstile>p {#- L#}\<close>
    for aa :: \<open>('v, 'v clause) ann_lits\<close> and a :: \<open>('v, nat) ann_lit list\<close> and b d e f L U h
    by (smt in_unmark_l_in_lits_of_l_iff list_of_l_convert_lits_l
      true_clss_clss_in_imp_true_clss_cls true_clss_clss_left_right
      true_clss_clss_union_and)
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
    then have \<open>atms_of (mset (N \<propto> D)) \<subseteq> atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE \<union> atms_of_mm NS \<union> atms_of_mm N0\<close>
      using alien assms(1) ST
      by (fastforce simp: twl_st_l_def clauses_def mset_take_mset_drop_mset' image_image
        cdcl\<^sub>W_restart_mset.no_strange_atm_def conj_disj_distribR Collect_disj_eq Collect_conv_if
        dest!: multi_member_split[of _ \<open>ran_m N\<close>])
   } note H = this
   ultimately show \<open>?A \<Longrightarrow>  ?B\<close> \<open>?A' \<Longrightarrow> undefined_lit M K \<Longrightarrow> ?B'\<close>
      if \<open>mset (N \<propto> D) = {#K#} + C'\<close> \<open>undefined_lit M K\<close>
    using assms cdcl_twl_unitres_l.intros(2)[of D N M K C' NE NS N0 UE US U0 Q]
      cdcl_twl_unitres_l.intros(4)[of D N M K C' NE NS N0 UE US U0 Q] that
    by auto

  show ?F if \<open>?E\<close> \<open>mset (N \<propto> D) = C'\<close>
  proof -
    have \<open>mset `# init_clss_lf N + NE + NS + N0 \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
      using ent2 that assms by auto
    then show ?thesis
      using cdcl_twl_unitres_l.intros(5)[of D N NE NS N0 M UE US U0 Q] assms that
      by auto
  qed

  show ?F' if \<open>?E'\<close> \<open>mset (N \<propto> D) = C'\<close>
  proof -
    have \<open>mset `# init_clss_lf N + NE + NS + N0 \<Turnstile>psm mset_set (CNot (mset (N \<propto> D)))\<close>
      using ent2 that assms by auto
    then show ?thesis
      using cdcl_twl_unitres_l.intros(6)[of D N NE NS N0 M UE US U0 Q] assms that
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
      using cdcl_twl_unitres_l.intros(1)[of D N M \<open>mset C\<close> C' NE NS N0 C UE US U0] assms that ent2
      by auto
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
      using cdcl_twl_unitres_l.intros(3)[of D N M \<open>mset C\<close> C' NE NS N0 C UE US U0] assms that ent2 H
      by auto
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

lemma simplify_clause_with_unit_st_spec:
  assumes \<open>C \<in># dom_m (get_clauses_l S)\<close> \<open>count_decided (get_trail_l S) = 0\<close>
    \<open>get_conflict_l S = None\<close> and
    \<open>clauses_to_update_l S = {#}\<close> \<open>C \<notin> set (get_all_mark_of_propagated (get_trail_l S))\<close>
    \<open>no_dup (get_trail_l S)\<close> and
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs T\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ((state\<^sub>W_of T))\<close> and
    tauto: \<open>\<not>tautology (mset ((get_clauses_l S) \<propto> C))\<close>
  shows \<open>simplify_clause_with_unit_st C S \<le> \<Down>Id (SPEC(\<lambda>T. cdcl_twl_unitres_l S T \<or> cdcl_twl_unitres_true_l S T))\<close>
  unfolding simplify_clause_with_unit_st_def simplify_clause_with_unit_def
  apply refine_vcg
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg x ah bh
    using count_decided_ge_get_level[of \<open>get_trail_l S\<close>]
    by (auto simp: cdcl_twl_unitres_true_l.simps
      intro!: exI[of _ C])
  subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x aj bj
    using ST st_invs apply -
    apply (rule disjI1)
    apply (subgoal_tac \<open>fmdrop C bj = fmdrop C aa\<close>)
    apply auto
    apply (auto simp: length_list_Suc_0 cdcl_twl_unitres_l_intros2' cdcl_twl_unitres_l_intros4'
      intro:  cdcl_twl_unitres_l_intros2'[where C' = \<open>mset (get_clauses_l S \<propto> C) - mset (bj \<propto> C)\<close>
      and T = T]
      cdcl_twl_unitres_l_intros4'[where C' = \<open>mset (get_clauses_l S \<propto> C) - mset (bj \<propto> C)\<close>
      and T = T])[2]
    done
  subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x aj bj
    using count_decided_ge_get_level[of \<open>get_trail_l S\<close>] ST st_invs
      cdcl_twl_unitres_false_entailed[of C \<open>get_clauses_l S\<close> \<open>get_trail_l S\<close>
       \<open>get_unit_init_clauses_l S\<close> \<open>get_unit_learned_clss_l S\<close>
      \<open>get_subsumed_init_clauses_l S\<close> \<open>get_subsumed_learned_clauses_l S\<close>
      \<open>get_init_clauses0_l S\<close> \<open>get_learned_clauses0_l S\<close>
      \<open>literals_to_update_l S\<close> T
      \<open>mset (get_clauses_l S \<propto> C) - mset (bj \<propto> C)\<close>]
      twl_st_l_struct_invs_distinct[of S T None C]
    apply (auto simp: cdcl_twl_unitres_true_l.simps cdcl_twl_unitres_l.simps
      dest: distinct_mset_mono[of \<open>mset _\<close> \<open>mset _\<close>, unfolded distinct_mset_mset_distinct]
      intro!: exI[of _ C])
    done
  subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x aj bj
    using assms
    by (auto  simp: list_length_2_isabelle_come_on
      intro!: cdcl_twl_unitres_l_intros3' cdcl_twl_unitres_l_intros1'
      dest: distinct_mset_mono[of \<open>mset _\<close> \<open>mset _\<close>, unfolded distinct_mset_mset_distinct]
      intro!: exI[of _ C] fmdrop_eq_update_eq2)
  done

definition forward_subsumption_one_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_pre = (\<lambda>C (M, N, D, NE, UE, NS, US, WS, Q). C \<in># dom_m N \<and>
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

inductive cdcl_twl_inprocessing_l where
  \<open>cdcl_twl_unitres_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close> |
  \<open>cdcl_twl_unitres_true_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close> |
  \<open>cdcl_twl_subsumed_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>|
  \<open>cdcl_twl_subresolution_l S T \<Longrightarrow> cdcl_twl_inprocessing_l S T\<close>

lemma
  assumes \<open>subsume_or_strengthen_pre C s M (N, NE, UE, NS, US)\<close>
  shows
    \<open>subsume_or_strengthen C s M (N, NE, UE, NS, US) \<le>\<Down>Id (SPEC(\<lambda>(N', NE', UE', NS', US').
  cdcl_twl_inprocessing_l\<^sup>*\<^sup>* (M, N, None, NE, UE, NS, US, N0, U0, {#}, Q)
  (M, N', None, NE', UE', NS', US', N0, U0, {#}, Q)))\<close>
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
  \<open>forward_subsumption_one = (\<lambda>C (M, N, D, NE, UE, NS, US, WS, Q). do {
  ASSERT(forward_subsumption_one_pre C (M, N, D, NE, UE, NS, US, WS, Q));
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
  RETURN (M, N, D, NE, UE, NS, US, WS, Q)
  }
)\<close>

end