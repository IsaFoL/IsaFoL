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
    \<open>irred N C\<close> \<open>\<not>irred N C'\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> |
subsumed_RI:
  \<open>cdcl_twl_subsumed_l (M, N, D, NE, UE, NS, US, WS, Q)
    (M, fmupd C (N \<propto> C, True) (fmdrop C' N), D, NE, UE, add_mset (mset (N \<propto> C')) NS, US, {#}, Q)\<close>
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
        cdcl_twl_subsumed_II_simp[where C = ?E and C' = ?E'])
      done
  next
    case (subsumed_RR N C C' M D NE UE NS US WS Q)
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
    case (subsumed_IR N C C' M D NE UE NS US WS Q)
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
    case (subsumed_RI N C C' M D NE UE NS US WS Q)
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
  by (induction rule: cdcl_twl_subsumed_l.induct)
   (auto simp: twl_list_invs_def cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
    dest: in_diffD)

inductive cdcl_twl_subresolution_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
twl_subresolution_II_nonunit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, {#}, Q)
    (M, fmupd C' (E, True) N, None, NE, UE, add_mset (mset (N \<propto> C')) NS, US, {#}, Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
   \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>irred N C\<close> \<open>irred N C'\<close>
    |
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, {#}, Q)
    (Propagated K 0 # M, fmdrop C' N, None, add_mset {#K#} NE, UE, add_mset (mset (N \<propto> C')) NS, US, {#}, add_mset (-K) Q)\<close>
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
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, {#}, Q)
    (M, fmupd C' (E, False) N, None, NE, UE, NS, add_mset (mset (N \<propto> C'))  US, {#}, Q)\<close>
 if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
   \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>mset E = remdups_mset D'\<close> \<open>length E \<ge> 2\<close> \<open>distinct E\<close> \<open>\<forall>L \<in># mset E. undefined_lit M L\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>\<not>irred N C'\<close> |
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution_l (M, N, None, NE, UE, NS, US, {#}, Q)
    (Propagated K 0 # M, fmdrop C' N, None, NE, add_mset {#K#} UE, NS,  add_mset (mset (N \<propto> C')) US, {#}, add_mset (-K) Q)\<close>
  if
    \<open>C \<in># dom_m N\<close>
    \<open>C' \<in># dom_m N\<close>
    \<open>mset (N \<propto> C) = add_mset L D\<close>
    \<open>mset (N \<propto> C') = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> \<open>\<not>irred N C\<close> \<open>\<not>irred N C'\<close>
(* |
twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, None, NE, UE, NS, US, {#}, Q)
    (M, N + {#C#}, U + {#E#}, None, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>\<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, None, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, None, NE, add_mset {#K#} UE, NS,
      add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, None, NE, UE, NS, US, {#}, Q)
    (M, N + {#E#}, U + {#C#}, None, NE, UE, add_mset (clause C') NS, US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close> \<open>\<forall>L \<in># clause E. undefined_lit M L\<close> |
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, None, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, None, add_mset {#K#} NE, UE,
       add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close> *)

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
    \<open>S = (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
    \<open>T = (M, add_mset E (remove1_mset C' N), U, None, NE, UE, add_mset (clause C') NS, US, {#}, Q)\<close>
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
    \<open>S = (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, (remove1_mset C' N), U, None, add_mset {#K#} NE, UE, add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
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
    \<open>S = (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
    \<open>T = (M, N, add_mset E (remove1_mset C' U), None, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
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
    \<open>S = (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
    \<open>T = (Propagated K {#K#} # M, (N), remove1_mset C' U, None, NE, add_mset {#K#} UE,
      NS, add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
    \<open>clause C = add_mset L D\<close>
    \<open>clause C' = add_mset (-L) D'\<close>
    \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
    \<open>remdups_mset D' = {#K#}\<close>
    \<open>undefined_lit M K\<close>
    \<open>C \<in># U\<close>
    \<open>C' \<in># U\<close>
  using cdcl_twl_subresolution.twl_subresolution_LL_unit[of C L D C' D' M K N \<open>U - {#C, C'#}\<close>] that
  by (auto dest!: multi_member_split simp: add_mset_eq_add_mset add_mset_commute)

lemma cdcl_twl_subresolution_eqD:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> S = S' \<Longrightarrow> T = T' \<Longrightarrow> cdcl_twl_subresolution S' T'\<close>
  by auto
thm cdcl_twl_subresolution_eqD[OF cdcl_twl_subresolution.twl_subresolution_II_nonunit]
  
lemma cdcl_twl_subresolution_l_cdcl_twl_subresolution:
  assumes \<open>cdcl_twl_subresolution_l S T\<close> and
    SS': \<open>(S, S') \<in> twl_st_l None\<close>
  shows \<open>\<exists>T'. (T, T') \<in> twl_st_l None \<and> cdcl_twl_subresolution S' T'\<close>
proof -
  show ?thesis
    using assms
      supply [simp] = convert_lits_l_update_sel2
    apply (induction rule: cdcl_twl_subresolution_l.induct)
    subgoal for C N C' L D D' M E NE UE NS US Q
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
    subgoal for C N C' L D D' M K NE UE NS US Q
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
    subgoal for C N C' L D D' M E NE UE NS US Q
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
    subgoal for C N C' L D D' M K NE UE NS US Q
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
      done
qed
end