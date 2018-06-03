theory Watched_Literals_Watch_List_Restart
  imports Watched_Literals_List_Restart Watched_Literals_Watch_List
begin

text \<open>We relax the condition on the invariant on the watch list to allow to point to non-existing
  clauses.\<close>
fun (in -) partial_correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE + UE).
        (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (watched_l(N\<propto>i))))\<close>

lemma partial_correct_watching_correct_watching:
  \<open>correct_watching S \<Longrightarrow> partial_correct_watching S\<close>
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
      by (fast dest: in_set_takeD)
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
      using that unfolding st by simp_all
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

definition remove_one_annot_true_clause_one_imp_wl_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_pre i T \<longleftrightarrow>
     (\<exists>T'. (T, T') \<in> state_wl_l None \<and>
       remove_one_annot_true_clause_one_imp_pre i T' \<and>
       partial_correct_watching T)\<close>

definition remove_one_annot_true_clause_one_imp_wl
  :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i (M, N, D, NE, UE, Q, W). do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_pre i (M, N, D, NE, UE, Q, W));
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

lemma remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp:
    \<open>(uncurry remove_one_annot_true_clause_one_imp_wl, uncurry remove_one_annot_true_clause_one_imp)
    \<in> nat_rel \<times>\<^sub>f  {(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S} \<rightarrow>\<^sub>f
      \<langle>nat_rel \<times>\<^sub>f {(S, T).  (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>replace_annot_in_trail_spec L S \<le> \<Down> Id (replace_annot_in_trail_spec L' T')\<close>
    if \<open>(L, L') \<in> Id\<close> and \<open>(S, T') \<in> Id\<close> for L L' S T'
    using that by auto
    thm extract_and_remove_def
  have [refine0]: \<open>extract_and_remove N j \<le>
         \<Down> {((N', C' :: 'a clause_l, b'), (N'', C'', b'')). N' = N'' \<and> C' = C'' \<and> b' = b'' \<and>
               N' = fmdrop j N \<and> C' = N\<propto>j \<and> b' = irred N j} (extract_and_remove N' j')\<close>
    if \<open>(j, j') \<in> Id\<close> and \<open>(N, N') \<in> Id\<close> for j j' N N'
    using that unfolding extract_and_remove_def
    by refine_rcg (auto intro!: RES_refine)
  have partial_correct_watching_drop:
    \<open>partial_correct_watching (x1h, x1i, x1j, x1k, x1l, x1m, x2m) \<Longrightarrow> x2n \<in># dom_m x1i \<Longrightarrow>
    partial_correct_watching
     (Ma, fmdrop x2n x1i, x1j, add_mset (mset (x1i \<propto> x2n)) x1k, x1l,
      x1m, x2m)\<close>
    for x1h x1i x1j x1k x1l x1m x2m Ma x2n
      using distinct_mset_dom[of x1i] ran_m_fmdrop[of x2n x1i]
      by (auto simp: partial_correct_watching.simps image_mset_remove1_mset_if
        dest!: multi_member_split[of x2n] cong: multiset.map_cong0 image_mset_cong2
        simp del: ran_m_fmdrop)
  have partial_correct_watching_drop':
    \<open>partial_correct_watching (x1h, x1i, x1j, x1k, x1l, x1m, x2m) \<Longrightarrow> x2n \<in># dom_m x1i \<Longrightarrow>
    partial_correct_watching
     (Ma, fmdrop x2n x1i, x1j, x1k, add_mset (mset (x1i \<propto> x2n)) x1l,
      x1m, x2m)\<close>
    for x1h x1i x1j x1k x1l x1m x2m Ma x2n
      using distinct_mset_dom[of x1i] ran_m_fmdrop[of x2n x1i]
      by (auto simp: partial_correct_watching.simps image_mset_remove1_mset_if
        dest!: multi_member_split[of x2n] cong: multiset.map_cong0 image_mset_cong2
        simp del: ran_m_fmdrop)

  show ?thesis
    unfolding remove_one_annot_true_clause_one_imp_wl_def remove_one_annot_true_clause_one_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp[THEN fref_to_Down_curry])
    subgoal unfolding remove_one_annot_true_clause_one_imp_wl_pre_def by force
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by simp
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by simp
    subgoal by (simp add: state_wl_l_def)
    subgoal by (simp add: state_wl_l_def)
    subgoal by (auto simp add: state_wl_l_def intro: partial_correct_watching_drop
      partial_correct_watching_drop')
    subgoal by (auto simp add: state_wl_l_def intro: partial_correct_watching_drop
      partial_correct_watching_drop')
    done
qed

definition remove_one_annot_true_clause_imp_wl_inv where
  \<open>remove_one_annot_true_clause_imp_wl_inv S = (\<lambda>(i, T).
     (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
       partial_correct_watching S \<and> partial_correct_watching T \<and>
       remove_one_annot_true_clause_imp_inv S' (i, T')))\<close>

definition remove_one_annot_true_clause_imp_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl = (\<lambda>S. do {
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_inv S\<^esup>
      (\<lambda>(i, S). i < length (get_trail_wl S) \<and> \<not>is_decided (get_trail_wl S!i))
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl i S)
      (0, S);
    RETURN S
  })\<close>

lemma remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp:
  \<open>(remove_one_annot_true_clause_imp_wl, remove_one_annot_true_clause_imp)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding remove_one_annot_true_clause_imp_wl_def remove_one_annot_true_clause_imp_def
      uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where
         R = \<open>nat_rel \<times>\<^sub>f {(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal by auto
    subgoal for x y xa x'
      unfolding remove_one_annot_true_clause_imp_wl_inv_def
      apply (subst case_prod_beta)
      apply (rule_tac x=\<open>y\<close> in exI)
      apply (rule_tac x=\<open>snd x'\<close> in exI)
      apply (subst (asm)(8) surjective_pairing)
      apply (subst (asm)(13) surjective_pairing)
      unfolding prod_rel_iff by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition collect_valid_indices_wl where
  \<open>collect_valid_indices_wl S = SPEC (\<lambda>N. mset N \<subseteq># dom_m (get_clauses_wl S) \<and> distinct N)\<close>

definition mark_to_delete_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
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


lemma mark_to_delete_clauses_wl_mark_to_delete_clauses_l:
  \<open>(mark_to_delete_clauses_wl, mark_to_delete_clauses_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S  \<le> \<Down> Id  (collect_valid_indices S')\<close>
    if \<open>(S, S') \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S}\<close>
    for S S'
    using that by (auto simp: collect_valid_indices_wl_def collect_valid_indices_def)
  show ?thesis
    unfolding mark_to_delete_clauses_wl_def mark_to_delete_clauses_l_def
      uncurry_def
    apply (intro frefI nres_relI)
    subgoal for x y
    apply (cases x; cases y)
    subgoal for M N D NE UE Q W M' N' D' NE' UE' WS' Q'
    apply (refine_vcg
      WHILET_refine[where
         R = \<open>{((brk' :: bool, i' :: nat, N'), (brk'', i'', N'')).
             brk' = brk'' \<and> i' = i'' \<and> N' = N'' \<and>
             ((M, N', D, NE, UE, Q, W), (M, N'', D, NE, UE, WS', Q')) \<in> state_wl_l None \<and>
             partial_correct_watching (M, N', D, NE, UE, Q, W)}\<close>]
      remove_one_annot_true_clause_one_imp_wl_remove_one_annot_true_clause_one_imp[THEN fref_to_Down_curry])
    subgoal by auto
    subgoal by (auto simp: state_wl_l_def)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (force simp: state_wl_l_def partial_correct_watching_fmdrop)
    subgoal by auto
    subgoal by (force simp: state_wl_l_def)
    done
  done
  done
qed


definition cdcl_twl_restart_wl_prog :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_twl_restart_wl_prog S = do {
    S \<leftarrow> remove_one_annot_true_clause_imp_wl S;
    mark_to_delete_clauses_wl S
  }\<close>

lemma cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(cdcl_twl_restart_wl_prog, cdcl_twl_restart_l_prog)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_prog_def cdcl_twl_restart_l_prog_def
  by (intro frefI nres_relI)
    (refine_vcg
     mark_to_delete_clauses_wl_mark_to_delete_clauses_l[THEN fref_to_Down]
     remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp[THEN fref_to_Down])


definition (in -) restart_abs_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_pre S brk \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_abs_l_pre S' brk
      \<and> partial_correct_watching S)\<close>

definition (in -) get_learned_clss_wl where
  \<open>get_learned_clss_wl S = learned_clss_lf (get_clauses_wl S)\<close>

(* TODO move + remove simp flag *)
lemma [twl_st_l, simp]:
  \<open>(a, a') \<in> state_wl_l None \<Longrightarrow>
        get_learned_clss_l a' = get_learned_clss_wl a\<close>
  unfolding state_wl_l_def by (cases a; cases a')
   (auto simp: get_learned_clss_l_def get_learned_clss_wl_def)
(* End Move *)

text \<open>
  This is only a specification and must be implemented. There are two ways to do so:
  \<^enum> clean the watch lists and then iterate over all clauses to rebuild them.
  \<^enum> iterate over the watch list and check whether the clause index is in the domain or not.

  It is not clear which is faster (but option 1 requires only 1 memory access per clause instead of
  two). The first option is implemented in SPASS. The latter version (partly) in cadical.
\<close>
definition rewatch_clauses :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>rewatch_clauses = (\<lambda>(M, N, D, NE, UE, Q, W). SPEC(\<lambda>(M', N', D', NE', UE', Q', W').
     (M, N, D, NE, UE, Q) = (M', N', D', NE', UE', Q') \<and>
    correct_watching (M, N', D, NE, UE, Q, W')))\<close>

definition empty_WL :: \<open>('v literal \<Rightarrow> watched) \<Rightarrow> ('v literal \<Rightarrow> watched)\<close>  where
  \<open>empty_WL W = (\<lambda>_. [])\<close>

definition rewatch_clause 
  :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> ('v literal \<Rightarrow> watched) \<Rightarrow> ('v literal \<Rightarrow> watched) nres\<close>
where
  \<open>rewatch_clause N C W = do {
    ASSERT(length (N \<propto> C) > 1);
    let L = N \<propto> C ! 0;
    let L' = N \<propto> C ! 1;
    RETURN (W(L := W L @ [C], L' := W L' @ [C]))
  }\<close>

definition rewatch_clauses_prog_inv where
  \<open>rewatch_clauses_prog_inv = (\<lambda>(M, N, D, NE, UE, Q, W) xs (i, W).
    i \<le> length xs \<and>
      correct_watching (M, fmrestrict_set (set (take i xs)) N, D, NE, UE, Q, W))\<close>

definition rewatch_clauses_prog_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>rewatch_clauses_prog_pre S \<longleftrightarrow>
     (\<exists>T U.
        (S, T) \<in> state_wl_l None \<and>
        (T, U) \<in> twl_st_l None \<and>
        twl_struct_invs U \<and>
        partial_correct_watching S)\<close>

definition rewatch_clauses_prog :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>rewatch_clauses_prog = (\<lambda>(M, N, D, NE, UE, Q, W0). do {
  ASSERT(rewatch_clauses_prog_pre (M, N, D, NE, UE, Q, W0));
  let W0 = empty_WL W0;
  xs \<leftarrow> SPEC(\<lambda>xs. dom_m N \<subseteq># mset xs \<and> distinct xs);
  (_, W) \<leftarrow> WHILE\<^sub>T\<^bsup>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, W0) xs\<^esup>
    (\<lambda>(i, W). i < length xs)
    (\<lambda>(i, W). do {
      ASSERT(i < length xs);
      if xs!i \<in># dom_m N then do {
        W \<leftarrow> rewatch_clause N (xs!i) W;
        RETURN(i+1, W)
      } else  RETURN(i+1, W)
    })
    (0, W0);
  RETURN (M, N, D, NE, UE, Q, W)
})\<close>

lemma fmrestrict_set_fmupd:
  \<open>a \<in> xs \<Longrightarrow> fmrestrict_set xs (fmupd a C N) = fmupd a C (fmrestrict_set xs N)\<close>
  \<open>a \<notin> xs \<Longrightarrow> fmrestrict_set xs (fmupd a C N) = fmrestrict_set xs N\<close>
  by (auto simp: fmfilter_alt_defs)

lemma fset_fmdom_fmrestrict_set:
  \<open>fset (fmdom (fmrestrict_set xs N)) = fset (fmdom N) \<inter> xs\<close>
  by (auto simp: fmfilter_alt_defs)

lemma finite_mset_set_inter:
  \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set (A \<inter> B) = mset_set A \<inter># mset_set B\<close>
  apply (induction A rule: finite_induct)
  subgoal by auto
  subgoal for a A
    apply (cases \<open>a \<in> B\<close>; cases \<open>a \<in># mset_set B\<close>)
    using multi_member_split[of a \<open>mset_set B\<close>]
    by (auto simp: mset_set.insert_remove)
  done


lemma distinct_mset_inter_remdups_mset:
  assumes dist: \<open>distinct_mset A\<close>
  shows \<open>A \<inter># remdups_mset B = A \<inter># B\<close>
proof -
  have [simp]: \<open>A' \<inter># remove1_mset a (remdups_mset Aa) = A' \<inter># Aa\<close>
    if 
      \<open>A' \<inter># remdups_mset Aa = A' \<inter># Aa\<close> and
      \<open>a \<notin># A'\<close> and
      \<open>a \<in># Aa\<close>
    for A' Aa :: \<open>'a multiset\<close> and a
  by (metis insert_DiffM inter_add_right1 set_mset_remdups_mset that)

  show ?thesis
    using dist
    apply (induction A)
    subgoal by auto
     subgoal for a A'
      apply (cases \<open>a \<in># B\<close>)
      using multi_member_split[of a \<open>B\<close>]  multi_member_split[of a \<open>A\<close>]
      by (auto simp: mset_set.insert_remove)
    done
qed


lemma dom_m_fmresctrict_set: \<open>dom_m (fmrestrict_set (set xs) N) =
  mset xs \<inter># dom_m N\<close>
  using fset_fmdom_fmrestrict_set[of \<open>set xs\<close> N] distinct_mset_dom[of N]
  distinct_mset_inter_remdups_mset[of \<open>mset_fset (fmdom N)\<close> \<open>mset xs\<close>]
  by (auto simp: dom_m_def fset_mset_mset_fset finite_mset_set_inter multiset_inter_commute
    remdups_mset_def)

lemma
  assumes
    ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    TU: \<open>(T, U) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs U\<close> andfir
    \<open>twl_list_invs T\<close>
    \<open>partial_correct_watching S\<close>
  shows
    \<open>rewatch_clauses_prog S \<le> rewatch_clauses S\<close>
proof -
  have pre: \<open>rewatch_clauses_prog_pre S\<close>
    using assms unfolding rewatch_clauses_prog_pre_def by blast
  have size_ge2: \<open>1 < length (N \<propto> (xs ! a))\<close>
    if 
      N: \<open>N = get_clauses_wl S\<close> and
      dom: \<open>xs ! a \<in># dom_m N\<close>
    for N xs a
  proof -
    have \<open>twl_st_inv U\<close>
      using struct_invs unfolding twl_struct_invs_def by fast+
    then have \<open>Multiset.Ball (get_clauses U) struct_wf_twl_cls\<close>
      unfolding twl_st_inv_alt_def by fast
    moreover have \<open>mset (N \<propto> (xs ! a)) \<in># clauses (get_clauses U)\<close>
      using ST TU N dom by (auto simp: mset_take_mset_drop_mset')
    ultimately show ?thesis
      apply (auto dest!: multi_member_split simp del: size_mset
        simp: size_mset[symmetric])
      apply (case_tac x)
      apply auto
      done
  qed
  have \<open>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, \<lambda>_. []) xs
        (i + 1, W2
          (N \<propto> (xs ! i) ! 0 := W2 (N \<propto> (xs ! i) ! 0) @ [xs ! i],
          N \<propto> (xs ! i) ! 1 := W2 (N \<propto> (xs ! i) ! 1) @ [xs ! i]))\<close>
    if 
      \<open>S = (M, N, D, NE, UE, Q, W)\<close> and
      \<open>rewatch_clauses_prog_pre (M, N, D, NE, UE, Q, W)\<close> and
      \<open>xs \<in> {xs. dom_m N \<subseteq># mset xs \<and> distinct xs}\<close> and
      inv: \<open>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, \<lambda>_. []) xs s\<close> and
      \<open>case s of (i, W) \<Rightarrow> i < length xs\<close> and
      s: \<open>s = (i, W2)\<close> and
      [simp]: \<open>i < length xs\<close> \<open>xs ! i \<in># dom_m N\<close> and
      \<open>1 < length (N \<propto> (xs ! i))\<close>
    for M N D NE UE Q W xs i W2 s
  proof -
    define N0 where \<open>N0 \<equiv> fmrestrict_set (set (take i xs)) N\<close>
    define C where \<open>C \<equiv> xs ! i\<close>
    define D' where \<open>D' \<equiv> the (fmlookup N C)\<close>
    define N' where \<open>N' \<equiv> fmdrop C N\<close>
    have D': \<open>D' = (N \<propto> C, irred N C)\<close>
      unfolding D'_def
      by auto
    have N': \<open>N = fmupd C D' N'\<close>
      unfolding N'_def C_def D'_def
      by (smt fmap_ext fmlookup_drop fmupd_lookup in_dom_m_lookup_iff option.collapse that(8)) 
    have [simp]: \<open>xs ! i \<notin> set (take i xs)\<close>
      by (metis (no_types, lifting) in_set_conv_iff less_not_refl3 mem_Collect_eq
         nth_eq_iff_index_eq that(3) that(7))
    have [simp]: \<open>xs ! i \<notin># dom_m N'\<close>
      using distinct_mset_dom[of N] unfolding N'_def by (auto simp: distinct_mset_remove1_All C_def)
    then have [simp]: \<open>fmlookup N' (xs ! i) = None\<close>
      by (simp_all add: C_def N'_def)
    have \<open>fmfilter (\<lambda>a. a = xs ! i \<or> a \<in> set (take i xs)) N' =
      fmfilter (\<lambda>a. a \<in> set (take i xs)) N'\<close>
      by (rule fmfilter_cong) auto
    then have N1: \<open>fmrestrict_set (set (take (i + 1) xs)) N = fmupd C (N \<propto> C, irred N C) N0\<close>
      by (auto simp: take_Suc_conv_app_nth N0_def C_def fmfilter_alt_defs N')
    have [simp]: \<open>C \<notin># dom_m N0\<close>
      unfolding N0_def
      by (auto simp: dom_m_fmresctrict_set C_def)
    have H: \<open>{#Ca \<in># dom_m N0. (C = Ca \<longrightarrow> P Ca) \<and> (C \<noteq> Ca \<longrightarrow> P' Ca)#} =
       {#Ca \<in># dom_m N0. P' Ca#}\<close> for P P'
      by (rule filter_mset_cong2) auto
    have \<open>correct_watching (M, fmrestrict_set (set (take i xs)) N, D, NE, UE, Q, W2)\<close>
      using inv 
      unfolding s rewatch_clauses_prog_inv_def prod.case
      by fast
    then have \<open>correct_watching
     (M, fmrestrict_set (set (take (i + 1) xs)) N, D, NE, UE, Q, W2
      (N \<propto> (xs ! i) ! 0 := W2 (N \<propto> (xs ! i) ! 0) @ [xs ! i],
       N \<propto> (xs ! i) ! 1 := W2 (N \<propto> (xs ! i) ! 1) @ [xs ! i]))\<close>
      unfolding N1 N0_def[symmetric] D'[symmetric] C_def[symmetric]
      apply (auto simp: correct_watching.simps clause_to_update_def H
        )

     sorry
    show ?thesis
      unfolding rewatch_clauses_prog_inv_def prod.case
       
     sorry
  qed

  show ?thesis
    unfolding rewatch_clauses_prog_def rewatch_clauses_def Let_def empty_WL_def rewatch_clause_def
    apply (cases S)
    apply clarify
    apply (intro ASSERT_leI)
    subgoal using pre by fast
    subgoal for M N D NE UE Q W
      unfolding intro_spec_iff
      apply (intro ballI)
      subgoal for xs
        apply (refine_vcg
          WHILEIT_rule[where R= \<open>measure (\<lambda>(i::nat, W::_ literal \<Rightarrow> watched). length xs -i)\<close>])
        subgoal by auto
        subgoal by (auto simp: rewatch_clauses_prog_inv_def correct_watching.simps clause_to_update_def)
        subgoal by auto
        subgoal by (rule size_ge2) auto
        subgoal for s i W2
          explore_have
           apply (auto simp: rewatch_clauses_prog_inv_def correct_watching.simps clause_to_update_def)
           sorry
        subgoal by auto
        subgoal by auto
        subgoal unfolding rewatch_clauses_prog_inv_def by auto
        subgoal by auto
        subgoal unfolding rewatch_clauses_prog_inv_def by auto
term fmrestrict_set

context twl_restart
begin

definition restart_required_wl  :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
\<open>restart_required_wl S n = SPEC (\<lambda>b. b \<longrightarrow> f n < size (get_learned_clss_wl S))\<close>

definition restart_prog_wl :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_wl \<times> nat) nres" where
  \<open>restart_prog_wl S n brk = do {
     ASSERT(restart_abs_wl_pre S brk);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog S;
       U \<leftarrow> rewatch_clauses T;
       RETURN (U, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>


lemma cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(uncurry2 restart_prog_wl, uncurry2 restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S} \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S} \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<times>\<^sub>f _ \<times>\<^sub>f _ \<rightarrow>\<^sub>f \<langle>?R'\<rangle>nres_rel\<close>)
proof -
  have [refine0]: \<open>restart_required_wl a b \<le> \<Down> Id (restart_required_l a' b')\<close>
    if \<open>(a, a') \<in> ?R\<close> and \<open>(b, b') \<in> nat_rel\<close> for a a' b b'
    using that unfolding restart_required_wl_def restart_required_l_def
    by auto
  show ?thesis
    unfolding uncurry_def restart_prog_wl_def restart_prog_l_def rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down])
    subgoal unfolding restart_abs_wl_pre_def
       by (fastforce simp: partial_correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: partial_correct_watching_correct_watching)
    subgoal
      unfolding RES_RETURN_RES less_eq_nres.simps(2)
      by (auto simp: partial_correct_watching_correct_watching
        state_wl_l_def)
    subgoal by auto
    done
qed

definition cdcl_twl_stgy_restart_abs_wl_inv
   :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0' brk T' n \<and>
       correct_watching T)\<close>


definition cdcl_twl_stgy_restart_prog_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>cdcl_twl_stgy_restart_prog_wl (S\<^sub>0::'v twl_st_wl) =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, n) \<leftarrow> restart_prog_wl T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0::'v twl_st_wl, 0);
    RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  have [refine0]:
    \<open>(x, y) \<in> ?R \<Longrightarrow> ((False, x, 0), False, y, 0) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close> for x y
    by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where
      R=\<open>{(S, T).  (S, T) \<in> state_wl_l None \<and>  partial_correct_watching S}\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: partial_correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    done
qed

end

end
