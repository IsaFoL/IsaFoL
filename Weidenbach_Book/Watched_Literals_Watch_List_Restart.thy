theory Watched_Literals_Watch_List_Restart
  imports Watched_Literals_List_Restart Watched_Literals_Watch_List
begin

text \<open>We relax the condition on the invariant on the watch list to only have inclusion
  of the literal: This is enough and would allow to reorder clauses\<close>
fun (in -) partial_correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE + UE).
        (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (N\<propto>i)))\<close>

lemma (in -) \<open>correct_watching S \<Longrightarrow> partial_correct_watching S\<close>
  by (cases S)
    (auto simp: correct_watching.simps partial_correct_watching.simps clause_to_update_def
    simp del: set_mset_mset dest: in_set_mset_eq_in dest!: in_set_takeD)

definition remove_all_annot_true_clause_imp_wl_inv where
  \<open>remove_all_annot_true_clause_imp_wl_inv S xs = (\<lambda>(i, T).
     partial_correct_watching S \<and> partial_correct_watching T \<and>
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
        remove_all_annot_true_clause_imp_inv S' xs (i, T')))\<close>

definition remove_all_annot_true_clause_imp_wl
  :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl = (\<lambda>L (M, N0, D, NE0, UE, Q, W). do {
    let xs = W L;
    (_, N, NE) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N, NE).
        remove_all_annot_true_clause_imp_wl_inv (M, N0, D, NE0, UE, Q, W) xs
          (i, M, N, D, NE, UE, Q, W)\<^esup>
      (\<lambda>(i, N, NE). i < length xs)
      (\<lambda>(i, N, NE). do {
        ASSERT(i < length xs);
        if xs!i \<in># dom_m N
        then do {
          (N, NE) \<leftarrow> remove_all_annot_true_clause_one_imp (xs!i, N, NE);
          ASSERT(remove_all_annot_true_clause_imp_wl_inv (M, N0, D, NE0, UE, Q, W) xs
            (i, M, N, D, NE, UE, Q, W));
          RETURN (i+1, N, NE)
        }
        else
          RETURN (i+1, N, NE)
      })
      (0, N0, NE0);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

(* TODO Move *)
lemma all_lits_of_mm_diffD:
  \<open>L \<in># all_lits_of_mm (A - B) \<Longrightarrow> L \<in># all_lits_of_mm A\<close>
  apply (induction A arbitrary: B)
  subgoal by auto
  subgoal for a A' B
    by (cases \<open>a \<in># B\<close>)
      (fastforce dest!: multi_member_split[of a B] simp: all_lits_of_mm_add_mset)+
  done

lemma all_lits_of_mm_mono:
  \<open>set_mset A \<subseteq> set_mset B \<Longrightarrow> set_mset (all_lits_of_mm A) \<subseteq> set_mset (all_lits_of_mm B)\<close>
  by (auto simp: all_lits_of_mm_def)

(* End Move *)

lemma reduce_dom_clauses_fmdrop:
  \<open>reduce_dom_clauses N0 N \<Longrightarrow> reduce_dom_clauses N0 (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def distinct_mset_remove1_All)

lemma partial_correct_watching_fmdrop:
  \<open>partial_correct_watching (M, N, D, NE, UE, Q, W) \<Longrightarrow>
     partial_correct_watching (M, fmdrop C N, D, NE, UE, Q, W)\<close>
  using distinct_mset_dom[of N]
  by (cases \<open>C \<in># dom_m N\<close>)
   (auto simp: partial_correct_watching.simps image_mset_remove1_mset_if
    distinct_mset_remove1_All dest: all_lits_of_mm_diffD)

lemma \<open>remove_one_annot_true_clause S T \<Longrightarrow>
   mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S =
     mset `# init_clss_lf (get_clauses_l T) + get_unit_init_clauses_l T\<close>
  using distinct_mset_dom[of \<open>get_clauses_l S\<close>] apply -
  apply (induction rule: remove_one_annot_true_clause.induct)
  apply (auto simp: ran_m_def dest!: multi_member_split
    intro!: image_mset_cong2)
  apply (auto intro!: filter_mset_cong2)
  apply (auto intro!: image_mset_cong2)
  done

lemma
  assumes
    red: \<open>reduce_dom_clauses SN' N2\<close> and
    \<open>partial_correct_watching (SM', SN', SD', SNE', SUE', SQ', SW')\<close>
  shows \<open>partial_correct_watching (SM', N2, SD', NE2, SUE', SQ', SW')\<close>
proof -
  have \<open>\<forall>C. C \<in># dom_m N2 \<longrightarrow> C \<in># dom_m SN'\<close> and
    \<open>set_mset {#mset (fst x). x \<in># ran_m N2#} \<subseteq> set_mset{#mset (fst x). x \<in># ran_m SN'#}\<close>
    using red unfolding reduce_dom_clauses_def ran_m_def
    by (auto dest!: multi_member_split)
  then show ?thesis
    using assms(2) apply (auto simp: partial_correct_watching.simps reduce_dom_clauses_def)

   sorry
qed
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>
(* TODO Move *)
text \<open>This is the refinement version of @{thm WHILEIT_add_post_condition}.\<close>
lemma WHILEIT_refine_with_post:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF:
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x'; f' x' \<le> SPEC I' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  apply (subst (2) WHILEIT_add_post_condition)
  apply (rule WHILEIT_refine)
  subgoal using R0 by blast
  subgoal using IREF by blast
  subgoal using COND_REF by blast
  subgoal using STEP_REF by auto
  done
(* End Move *)

lemma remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp:
  \<open>(uncurry remove_all_annot_true_clause_imp_wl, uncurry remove_all_annot_true_clause_imp) \<in>
   Id \<times>\<^sub>f {(S::'v twl_st_wl, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
proof -
  have H: \<open>((0, x1i, x1k), 0, x1b, x1d) \<in> nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    if \<open>(x1i, x1b) \<in> Id\<close> and  \<open>(x1k, x1d) \<in> Id\<close>
    for x1i x1k x1b x1d
    using that by auto
  have L'_in_clause: \<open>L' \<in> set (N0 \<propto> x)\<close>
    if
      pre: \<open>remove_all_annot_true_clause_imp_pre L' (M, N0, D, NE, UE, {#}, Q)\<close> and
      x: \<open>x \<in> set (W L')\<close> and
      part: \<open>partial_correct_watching (M, N0, D, NE, UE, Q, W)\<close> and
      dom:  \<open>x \<in># dom_m N0\<close>
    for L' :: \<open>'v literal\<close> and M :: \<open>('v, nat) ann_lits\<close> and N0 D NE UE Q W x
  proof -
    define S :: \<open>'v twl_st_l\<close> where \<open>S \<equiv> (M, N0, D, NE, UE, {#}, Q)\<close>
    obtain x where
      \<open>twl_list_invs S\<close> and
      \<open>twl_list_invs S\<close> and
      \<open>get_conflict_l S = None\<close> and
      Sx: \<open>(S, x) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs x\<close> and
      \<open>clauses_to_update_l S = {#}\<close> and
      L': \<open>L' \<in> lits_of_l (get_trail_l S)\<close>
      using pre unfolding remove_all_annot_true_clause_imp_pre_def S_def[symmetric] by blast
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of x)\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then have \<open>\<And>L. L \<in> atm_of ` lits_of_l (get_trail_l S) \<Longrightarrow> L \<in> atms_of_ms
       ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m (get_clauses_l S) \<and> snd a}) \<union>
      atms_of_mm (get_unit_init_clauses_l S)\<close>
      using Sx unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp add: twl_st twl_st_l)
    from this[of \<open>atm_of L'\<close>] have \<open>L' \<in>#all_lits_of_mm (mset `# ran_mf N0 + NE + UE)\<close>
      using L' by (auto simp: S_def in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
        dest!: multi_member_split)
    then show ?thesis
      using part dom x unfolding partial_correct_watching.simps
      by fast
  qed
  have [refine0]: \<open>remove_all_annot_true_clause_one_imp (C, N0, NE0) \<le>
        \<Down> {((N, NE), (N', NE')). N = N' \<and> NE = NE' \<and>
            (C \<in># dom_m N0 \<longrightarrow> N = fmdrop C N0 \<and> (irred N0 C' \<longrightarrow> NE' = add_mset (mset (N0\<propto>C)) NE0)
              \<and> (\<not>irred N0 C' \<longrightarrow> NE' = NE0)) \<and>
            (C \<notin># dom_m N0 \<longrightarrow> N = N0 \<and>  NE' = NE0)}
          (remove_all_annot_true_clause_one_imp (C', N', NE'))\<close>
      (is \<open>_ \<le> \<Down> ?remove_all_one _\<close>)
    if \<open>(C, C') \<in> Id\<close> and \<open>(N0, N') \<in> Id\<close> and \<open>(NE0, NE') \<in> Id\<close>
    for C C' N' NE0 NE' N0
    using that distinct_mset_dom[of N0]
     unfolding remove_all_annot_true_clause_one_imp_def by (auto simp: distinct_mset_remove1_All)
  have remove_all_annot_true_clause_imp_wl_inv:
     \<open>remove_all_annot_true_clause_imp_wl_inv
        (SM', SN', SD', SNE', SUE', SQ', SW') (SW' SL')
        (j, SM', N2', SD', NE2', SUE', SQ', SW')\<close>
    if
      LST: \<open>(LS, LT) \<in> Id \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<close> and
      NNE: \<open>(NNE2, NNE2') \<in> ?remove_all_one (SW' SL' ! j) (xs ! j') NE1 N1\<close> and
      st:
        \<open>LS = (L, M, N0, D, NE, UE, Q, W)\<close>
        \<open>LT = (L', M', N', D', NE', UE', Q', W')\<close>
        \<open>oTUE' = (TQ', TW')\<close>
        \<open>oTNE' = (TUE', oTUE')\<close>
        \<open>oTD' = (TNE', oTNE')\<close>
        \<open>oTN' = (TD', oTD')\<close>
        \<open>oTM' = (TN', oTN')\<close>
        \<open>oTL' = (TM', oTM')\<close>
        \<open>LT = (TL', oTL')\<close>
        \<open>oSUE' = (SQ', SW')\<close>
        \<open>oSNE' = (SUE', oSUE')\<close>
        \<open>oSD' = (SNE', oSNE')\<close>
        \<open>oSN' = (SD', oSD')\<close>
        \<open>oSM' = (SN', oSN')\<close>
        \<open>oSL' = (SM', oSM')\<close>
        \<open>LS = (SL', oSL')\<close>
        \<open>jNNE' = (j', oNNE1')\<close>
        \<open>jNNE1 = (j, oNNE)\<close>
        \<open>NNE2' = (N2, NE2)\<close>
        \<open>NNE2 = (N2', NE2')\<close>
        \<open>oNNE1' = (N1', NE1')\<close>
        \<open>oNNE = (N1, NE1)\<close> and
      \<open>remove_all_annot_true_clause_imp_pre TL' (TM', TN', TD', TNE', TUE', TQ', TW')\<close> and
      \<open>(SW' SL', xs) \<in> Id\<close> and
      jNNE: \<open>(jNNE1, jNNE') \<in> {((i, N, NE), i', N', NE'). i = i' \<and> N = N' \<and>
          NE = NE' \<and> partial_correct_watching (M, N, D, NE, UE, Q, W)}\<close> and
      \<open>case jNNE1 of (i, N, NE) \<Rightarrow> i < length (SW' SL')\<close> and
      \<open>case jNNE' of (i, N, NE) \<Rightarrow> i < length xs\<close> and
      jNNE: \<open>case jNNE1 of
      (i, N, NE) \<Rightarrow>
        remove_all_annot_true_clause_imp_wl_inv
          (SM', SN', SD', SNE', SUE', SQ', SW') (SW' SL')
          (i, SM', N, SD', NE, SUE', SQ', SW')\<close> and
      jNNE': \<open>case jNNE' of
      (i, N, NE) \<Rightarrow>
        remove_all_annot_true_clause_imp_inv
          (TM', TN', TD', TNE', TUE', TQ', TW') xs
          (i, TM', N, TD', NE, TUE', TQ', TW')\<close> and
      \<open>j' < length xs\<close> and
      \<open>j < length (SW' SL')\<close> and
      dom: \<open>SW' SL' ! j \<in># dom_m N1\<close> and
      \<open>xs ! j' \<in># dom_m N1'\<close> and
      H: \<open>remove_all_annot_true_clause_imp_inv (TM', TN', TD', TNE', TUE', TQ', TW')
        xs (j', TM', N2, TD', NE2, TUE', TQ', TW')\<close>
    for TL' oTL' TM' oTM' TN' oTN' TD' oTD' TNE' oTNE' TUE' oTUE' TQ' TW' SL' oSL' SM' oSM' SN'
       oSN' SD' oSD' SNE' oSNE' SUE' oSUE' SQ' SW' xs jNNE1 jNNE' j' oNNE1' N1' NE1' j oNNE N1
       NE1 NNE2 NNE2' N2 NE2 N2' NE2'
      L M N0 D NE UE Q W L' M' N' D' NE' UE' Q' W' LS LT
  proof -
    have
      inv: \<open>remove_all_annot_true_clause_imp_wl_inv
        (SM', SN', SD', SNE', SUE', SQ', SW') (SW' TL')
        (j', SM', N1', SD', NE1', SUE', SQ', SW')\<close> and
      rem_post: \<open>remove_all_annot_true_clause_imp_inv (TM', TN', TD', TNE', TUE', TQ', TW')
        (SW' TL')
        (j', TM', N2', TD', NE2, TUE', TQ', TW')\<close> and
      part_S: \<open>partial_correct_watching (SM', SN', SD', SNE', SUE', SQ', SW')\<close> and
      st':
        \<open>M' = TM'\<close>
        \<open>M = SM'\<close>
        \<open>N1 = N1'\<close>
        \<open>NE2' = NE2\<close>
        \<open>N' = TN'\<close>
        \<open>N0 = SN'\<close>
        \<open>NE1 = NE1'\<close>
        \<open>D' = TD'\<close>
        \<open>D = SD'\<close>
        \<open>NE' = TNE'\<close>
        \<open>NE = SNE'\<close>
        \<open>UE' = TUE'\<close>
        \<open>UE = SUE'\<close>
        \<open>Q' = TQ'\<close>
        \<open>W' = TW'\<close>
        \<open>Q = SQ'\<close>
        \<open>W = SW'\<close>
        \<open>xs = SW' TL'\<close>
        \<open>SL' = TL'\<close>
        \<open>L' = TL'\<close>
        \<open>L = TL'\<close>
        \<open>j = j'\<close>
      using that unfolding st by auto
    have part_U: \<open>partial_correct_watching (SM', N1', SD', NE1', SUE', SQ', SW')\<close>
      using inv unfolding remove_all_annot_true_clause_imp_wl_inv_def prod.case
      by fast
    have SU: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* (TM', TN', TD', TNE', TUE', TQ', TW')
        (TM', N2, TD', NE2, TUE', TQ', TW')\<close>
      using H unfolding remove_all_annot_true_clause_imp_inv_def prod.case
      by auto
    obtain x xa where
      \<open>partial_correct_watching (SM', SN', SD', SNE', SUE', SQ', SW')\<close> and
      part_V: \<open>partial_correct_watching (SM', N1', SD', NE1', SUE', SQ', SW')\<close> and
      \<open>((SM', SN', SD', SNE', SUE', SQ', SW'), x) \<in> state_wl_l None\<close> and
      \<open>((SM', N1, SD', NE1, SUE', SQ', SW'), xa) \<in> state_wl_l None\<close> and
      \<open>remove_all_annot_true_clause_imp_inv x (SW' SL') (j, xa)\<close>
      using jNNE unfolding remove_all_annot_true_clause_imp_wl_inv_def prod.case st st' by blast

    have \<open>reduce_dom_clauses TN' N2\<close>
      using rtranclp_remove_one_annot_true_clause_reduce_dom_clauses[OF SU] by simp
    then have \<open>partial_correct_watching (SM', SN', SD', SNE', SUE', SQ', SW') \<Longrightarrow>
    SW' TL' ! j' \<in># dom_m N1' \<Longrightarrow>
    partial_correct_watching (SM', N1', SD', NE1', SUE', SQ', SW') \<Longrightarrow>
    N2' = fmdrop (SW' TL' ! j') N1' \<Longrightarrow>
    N2 = fmdrop (SW' TL' ! j') N1' \<Longrightarrow>
    NE2 = add_mset (mset (N1' \<propto> (SW' TL' ! j'))) NE1' \<Longrightarrow>
    \<not> partial_correct_watching
       (SM', N1', SD', add_mset (mset (N1' \<propto> (SW' TL' ! j'))) NE1', SUE', SQ',
        SW') \<Longrightarrow>
    irred N1' (SW' TL' ! j') \<Longrightarrow> False\<close>
      using multi_member_split[of \<open>xs!j'\<close> \<open>dom_m N1'\<close>]
      by (auto simp: partial_correct_watching.simps ran_m_def all_lits_of_mm_add_mset
        st st')
    then have part_V: \<open>partial_correct_watching (SM', N2', SD', NE2', SUE', SQ', SW')\<close>
      using part_S NNE dom part_V
      unfolding st st' remove_all_annot_true_clause_imp_wl_inv_def
      by (auto intro!: partial_correct_watching_fmdrop)
    show ?thesis
      unfolding remove_all_annot_true_clause_imp_wl_inv_def prod.case
      apply (intro conjI)
      subgoal using part_S .
      subgoal using part_V .
      subgoal
       using
        \<open>((SM', SN', SD', SNE', SUE', SQ', SW'), x) \<in> state_wl_l None\<close> and
        \<open>((SM', N1, SD', NE1, SUE', SQ', SW'), xa) \<in> state_wl_l None\<close> and
        \<open>remove_all_annot_true_clause_imp_inv x (SW' SL') (j, xa)\<close>
        using NNE rem_post LST unfolding st st'
        by (auto simp: state_wl_l_def)
      done
  qed
  show ?thesis
    supply [[goals_limit=1]]
    apply (intro frefI nres_relI)
    unfolding uncurry_def remove_all_annot_true_clause_imp_wl_def
      remove_all_annot_true_clause_imp_def
    subgoal for LS LT
      apply (cases LS; cases LT)
      subgoal for L M N0 D NE UE Q W L' M' N' D' NE' UE' Q' W'
      apply (refine_rcg H
        WHILEIT_refine[where R=\<open>{((i, N, NE), (i', N', NE')). i = i' \<and> N = N' \<and> NE = NE' \<and>
            partial_correct_watching (M, N, D, NE, UE, Q, W)}\<close>])
      subgoal by (auto simp: state_wl_l_def L'_in_clause)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def remove_all_annot_true_clause_imp_wl_inv_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def reduce_dom_clauses_fmdrop)
      subgoal
        for TL' oTL' TM' oTM' TN' oTN' TD' oTD' TNE' oTNE' TUE' oTUE' TQ' TW' SL' oSL' SM' oSM' SN'
        oSN' SD' oSD' SNE' oSNE' SUE' oSUE' SQ' SW' xs jNNE1 jNNE' j' oNNE1' N1' NE1' j oNNE N1
        NE1 NNE2 NNE2' N2 NE2 N2' NE2'
        by (rule remove_all_annot_true_clause_imp_wl_inv)
      subgoal by (auto simp: state_wl_l_def remove_all_annot_true_clause_imp_wl_inv_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      done
      done
    done
qed

definition remove_one_annot_true_clause_one_imp_wl
  :: \<open>nat \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i (M, N, D, NE, UE, Q, W). do {
      ASSERT(i < length M);
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev M)!i = Propagated L C);
      if C = 0 then RETURN (i+1, M, N, D, NE, UE, Q, W)
      else do {
        ASSERT(C \<in># dom_m N);
        M \<leftarrow> replace_annot_in_trail_spec M L;
        (N', C, b) \<leftarrow> extract_and_remove N C;
        let S = (if b then (M, N', D, add_mset (mset C) NE, UE, Q, W)
                      else (M, N', D, NE, add_mset (mset C) UE, Q, W));
        S \<leftarrow> remove_all_annot_true_clause_imp_wl L S;
        RETURN (i+1, S)
      }
  })\<close>

definition remove_one_annot_true_clause_imp_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl = (\<lambda>S. do {
    (_, S) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, S). i < length (get_trail_wl S) \<and> \<not>is_decided (get_trail_wl S!i))
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl i S)
      (0, S);
    RETURN S
  })\<close>

definition collect_valid_indices_wl where
  \<open>collect_valid_indices_wl S = SPEC (\<lambda>N. mset N \<subseteq># dom_m (get_clauses_wl S) \<and> distinct N)\<close>

definition mark_to_delete_clauses_wl :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl  = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    xs \<leftarrow> collect_valid_indices_wl (M, N, D, NE, UE, Q, W);
    (_, _, N) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(brk, i, N). \<not>brk \<and> i < length xs)
      (\<lambda>(brk, i, N). do {
        can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> (Propagated (N\<propto>(xs!i)!0) (xs!i) \<notin> set M) \<and> \<not>irred N (xs!i));
        brk \<leftarrow> SPEC(\<lambda>_. True);
        ASSERT(i < length xs);
        if can_del
        then
          RETURN (brk, i+1, fmdrop (xs!i) N)
        else
          RETURN (brk, i+1, N)
      })
      (False, 0, N);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>



lemma \<open>(uncurry remove_all_annot_true_clause_imp_wl, uncurry remove_all_annot_true_clause_imp) \<in>
   Id \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding uncurry_def remove_all_annot_true_clause_imp_wl_def
    remove_all_annot_true_clause_imp_def
  apply (refine_vcg
    WHILET_refine[where R=\<open>bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
       {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<close>])

thm WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
       {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<close>]
  oops

text \<open>Most important point: We assume that the new watch list is correct.\<close>
inductive cdcl_twl_restart_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart_wl (M, N, None, NE, UE, Q, W)
       (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
  if
    \<open>valid_trail_reduction M M'\<close> and
    \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    \<open>learned_clss_lf N' + UE' \<subseteq># learned_clss_lf N\<close> and
    \<open>\<forall>E\<in># (NE'+UE'). \<exists>L\<in>set E. L \<in> lits_of_l M \<and> get_level M L = 0\<close> and
    \<open>\<forall>L E E' . Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E > 0  \<longrightarrow> E' > 0 \<longrightarrow>
        E \<in># dom_m N' \<and> N' \<propto> E = N \<propto> E'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow> E' \<noteq> 0 \<longrightarrow>
       mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E' = 0 \<longrightarrow> E = 0\<close> and
    \<open>0 \<notin># dom_m N'\<close> and
    \<open>if length M = length M' then Q = Q' else Q' = {#}\<close> and
    \<open>correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>

lemma cdcl_twl_restart_wl_cdcl_twl_restart_l_spec:
  assumes
    \<open>cdcl_twl_restart_wl S S'\<close> and
    \<open>(S, T) \<in> state_wl_l None\<close> and
    \<open>correct_watching S\<close>
  shows \<open>\<exists>T'. (S' , T') \<in> state_wl_l None \<and> cdcl_twl_restart_l T T' \<and> correct_watching S'\<close>
  using assms
proof (induction rule: cdcl_twl_restart_wl.induct)
  case (restart_trail M M' N N' NE' UE' NE UE Q Q' W' W)
  let ?T' = \<open>(M', N', None, NE + mset `# NE', UE + mset `# UE', {#}, Q')\<close>
  have \<open>cdcl_twl_restart_l T ?T'\<close>
    using restart_trail
    by (auto simp: cdcl_twl_restart_l.simps state_wl_l_def)
  moreover have \<open>((M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W') , ?T') \<in> state_wl_l None\<close>
    using restart_trail
    by (auto simp: cdcl_twl_restart_l.simps state_wl_l_def)
  moreover have \<open>correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
    using restart_trail
    by fast
  ultimately show ?case
    by blast
qed

lemma restart_prog_wl_restart_prog_l:
  \<open>(\<lambda>S. SPEC (cdcl_twl_restart_wl S), \<lambda>S. SPEC (cdcl_twl_restart_l S)) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule RES_refine)
  using cdcl_twl_restart_wl_cdcl_twl_restart_l_spec by blast

definition (in -) get_learned_clss_wl where
  \<open>get_learned_clss_wl S = learned_clss_lf (get_clauses_wl S)\<close>

context twl_restart
begin

definition restart_required_wl :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_wl S n = SPEC (\<lambda>b. b \<longrightarrow> size (get_learned_clss_wl S) > f n)\<close>

definition restart_prog_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>restart_prog_wl_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_prog_l_pre S'
      \<and> correct_watching S)\<close>

definition restart_prog_wl :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_wl \<times> nat) nres" where
  \<open>restart_prog_wl S n brk = do {
     ASSERT(restart_prog_wl_pre S);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_wl S T);
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>


lemma (in -)[twl_st_l]:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> get_learned_clss_l S' = get_learned_clss_wl S\<close>
  by (auto simp: get_learned_clss_wl_def get_learned_clss_l_def state_wl_l_def)

lemma restart_required_wl_restart_required_l:
  \<open>(uncurry restart_required_wl, uncurry restart_required_l) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None} \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f
    \<langle>bool_rel\<rangle> nres_rel\<close>
  unfolding restart_required_wl_def restart_required_l_def uncurry_def
  by (intro frefI nres_relI)
   (auto simp: state_wl_l_def get_learned_clss_l_def get_learned_clss_wl_def)


lemma restart_prog_wl_restart_prog_l:
  \<open>(uncurry2 restart_prog_wl, uncurry2 restart_prog_l) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}
        \<times>\<^sub>f  nat_rel  \<times>\<^sub>f  bool_rel \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}
        \<times>\<^sub>f nat_rel\<rangle> nres_rel\<close>
    unfolding restart_prog_wl_def restart_prog_l_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      restart_required_wl_restart_required_l[THEN fref_to_Down_curry]
      restart_prog_wl_restart_prog_l[THEN fref_to_Down])
    subgoal for Snb Snb'
     unfolding restart_prog_wl_pre_def
     by (rule exI[of _ \<open>fst (fst (Snb'))\<close>]) simp
    subgoal by simp
    subgoal by simp -- \<open>If condition\<close>
    subgoal by simp
    subgoal by simp
    subgoal by auto
    done


definition cdcl_twl_stgy_restart_prog_wl_inv where
  \<open>cdcl_twl_stgy_restart_prog_wl_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_prog_l_inv S\<^sub>0' brk T' n \<and>
       correct_watching T)\<close>

definition cdcl_twl_stgy_restart_prog_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>cdcl_twl_stgy_restart_prog_wl S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_prog_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, n) \<leftarrow> restart_prog_wl T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0, 0);
    RETURN T
  }\<close>

lemma cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
      (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> brk = brk' \<and> n = n'}\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down]
      restart_prog_wl_restart_prog_l[THEN fref_to_Down_curry2])
  subgoal by simp
  subgoal for x y xa x' x1 x2 x1a x2a
    unfolding cdcl_twl_stgy_restart_prog_wl_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd x')\<close> in exI)
    by auto
  subgoal by fast
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_l_inv_def
      cdcl_twl_stgy_restart_prog_wl_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st twl_st_wl)
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by auto
  subgoal by auto
  done

end

end
