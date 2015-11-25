theory CDCL_CW_NOT
imports CDCL_CW_Termination CDCL_NOT
begin

declare upt.simps(2)[simp del]
sledgehammer_params[verbose]


interpretation cdcl_CW: dpll_state trail "\<lambda>S. clauses S \<union> learned_clauses S"
  "\<lambda> M (_, N, U, k, D). (M, N, U, k, D)" "\<lambda> C (M, N, U, k, D). (M, N, insert C U, k, D)"
  "\<lambda> C (M, N, U, k, D). (M, N - {C}, U - {C}, k, D)"
  by unfold_locales auto

lemma rtranclp_skip_backtrack_backtrack:
  assumes
    "skip\<^sup>*\<^sup>* S T" and
    "backtrack T W" and
    "cdcl_all_inv_mes S"
  shows "backtrack S W"
  using assms
proof (induction)
  case base
  thus ?case by simp
next
  case (step T V) note st = this(1) and skip = this(2) and IH = this(3) and bt = this(4) and
    inv = this(5)
  obtain M N k M1 M2 K i D L U where
    V: "V = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "W = (Propagated L (D + {#L#}) # M1, N, insert (D + {#L#}) U, get_maximum_level D M, C_True)"
  and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    lev_l: "get_level L M = k" and
    lev_l_D: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "i = get_maximum_level D M"
    using bt by auto
  let ?D = "(D + {#L#})"
  obtain L' C' where
    T: "T = (Propagated L' C' # M, N, U, k, C_Clause ?D)" and
    "V = (M, N, U, k, C_Clause ?D)" and
    "-L' \<notin># ?D" and
    "?D \<noteq> {#}"
    using skip unfolding V by fastforce
  let ?M =  "Propagated L' C' # M"
  have inv': "cdcl_all_inv_mes T"
    by (metis (no_types, hide_lams) cdcl_o.bj cdcl_bj.skip inv mono_rtranclp other
      rtranclp_cdcl_all_inv_mes_inv st)
  have M_lev: "cdcl_M_level_inv T" using inv' unfolding cdcl_all_inv_mes_def by auto
  hence n_d': "no_dup ?M"
    unfolding cdcl_M_level_inv_def T by auto

  have "k > 0"
    using decomp M_lev unfolding cdcl_M_level_inv_def T by auto
  hence "atm_of L \<in> atm_of ` lits_of M"
    using lev_l get_rev_level_ge_0_atm_of_in by fastforce
  hence L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' unfolding lits_of_def by auto
  have L'_M: "atm_of L' \<notin> atm_of ` lits_of M"
    using n_d' unfolding lits_of_def by auto
  have "?M \<Turnstile>as CNot ?D"
    using inv' unfolding cdcl_conflicting_def cdcl_all_inv_mes_def T by auto
  hence "L' \<notin># ?D"
    using L_L' L'_M unfolding true_annots_def by (auto simp add: true_annot_def true_cls_def
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set Ball_mset_def
      split: split_if_asm)

  obtain M2' where
    "(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition ?M)"
    using decomp by (cases "hd (get_all_marked_decomposition M)",
      cases "get_all_marked_decomposition M") auto
  moreover
    from L_L'
    have "get_level L ?M = k"
    using lev_l \<open>-L' \<notin># ?D\<close> by (auto split: split_if_asm)
  moreover
    have "atm_of L' \<notin> atms_of D"
      using \<open>L' \<notin># ?D\<close> \<open>-L' \<notin># ?D\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
        atms_of_def)
    hence "get_level L ?M = get_maximum_level (D+{#L#}) ?M"
      using lev_l_D L_L' by simp
  moreover have "i = get_maximum_level D ?M"
    using i \<open>atm_of L' \<notin> atms_of D\<close> by auto
  ultimately show ?thesis using inv
    by (metis (no_types, lifting) T Un_insert_right W backtracking i step.IH sup_bot.comm_neutral)
qed

lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m\<in>set M. \<not>is_marked m)" and
    "T = (trail T, clauses S, learned_clauses S, backtrack_level S, conflicting S)"
  using assms by (induction rule: rtranclp_induct) (cases S;auto)+

lemma fst_get_all_marked_decomposition_prepend_not_marked:
  assumes "\<forall>m\<in>set MS. \<not> is_marked m"
  shows "set (map fst (get_all_marked_decomposition M))
    = set (map fst (get_all_marked_decomposition (MS @ M)))"
    using assms apply (induction MS rule: marked_lit_list_induct)
    apply auto[2]
    by (case_tac "get_all_marked_decomposition (xs @ M)") simp_all

text \<open>See also @{thm rtranclp_skip_backtrack_backtrack}\<close>
lemma rtranclp_skip_backtrack_backtrack_end:
  assumes
    skip: "skip\<^sup>*\<^sup>* S T" and
    bt: "backtrack S W" and
    inv: "cdcl_all_inv_mes S"
  shows "backtrack T W"
  using assms
proof -
  obtain M N k M1 M2 K i D L U where
    S: "S = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "W = (Propagated L (D + {#L#}) # M1, N, insert (D + {#L#}) U, get_maximum_level D M, C_True)"
  and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    lev_l: "get_level L M = k" and
    lev_l_D: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "i = get_maximum_level D M"
    using bt by auto
  let ?D = "(D + {#L#})"

  (* M\<^sub>T is a proxy to allow auto to unfold T*)
  obtain MS M\<^sub>T where M: "M = MS @ M\<^sub>T" and M\<^sub>T: "M\<^sub>T = trail T" and nm: "\<forall>m\<in>set MS. \<not>is_marked m"
    using rtranclp_skip_state_decomp(1)[OF skip] S by auto
  have T: "T = (M\<^sub>T, N, U, k, C_Clause ?D)"
    using M\<^sub>T rtranclp_skip_state_decomp(2) skip S by fast
  have "cdcl_all_inv_mes T"
    by (metis (no_types, hide_lams) bj cdcl_bj.skip inv local.skip mono_rtranclp other
      rtranclp_cdcl_all_inv_mes_inv)
  hence "M\<^sub>T \<Turnstile>as CNot ?D"
    unfolding cdcl_all_inv_mes_def cdcl_conflicting_def unfolding T
    by (auto simp: lits_of_def)
  have "\<forall>L\<in>#?D. atm_of L \<in> atm_of ` lits_of M\<^sub>T"
    proof -
      have f1: "\<And>l. \<not> M\<^sub>T \<Turnstile>a {#- l#} \<or> atm_of l \<in> atm_of ` lits_of M\<^sub>T"
        by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_lit_of_true_annot
          lits_of_def)
      have "\<And>l. l \<notin># D \<or> - l \<in> lits_of M\<^sub>T"
        using \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> multi_member_split by fastforce
      thus ?thesis
        using f1 by (meson \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> ball_msetI true_annots_CNot_all_atms_defined)
    qed
  moreover have "no_dup M"
    using inv unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def S  by auto
  ultimately have "\<forall>L\<in>#?D. atm_of L \<notin> atm_of ` lits_of MS"
    unfolding M unfolding lits_of_def by auto
  hence H: "\<And>L. L\<in>#?D \<Longrightarrow> get_level L M  = get_level L M\<^sub>T"
    unfolding M by (fastforce simp: lits_of_def)
  have [simp]: "get_maximum_level ?D M = get_maximum_level ?D M\<^sub>T"
    by (metis \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close>  M nm ball_msetI true_annots_CNot_all_atms_defined
      get_maximum_level_skip_un_marked_not_present)

  have lev_l': "get_level L M\<^sub>T = k"
    using lev_l by (auto simp: H)

  have lev_l_D': "get_level L M\<^sub>T = get_maximum_level (D+{#L#}) M\<^sub>T"
    using lev_l_D by (auto simp: H)
  have [simp]: "get_maximum_level D M = get_maximum_level D M\<^sub>T"
    by (smt Ball_mset_def M\<^sub>T \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> nm M ab_semigroup_add_class.add_ac(1)
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set get_maximum_level_skip_un_marked_not_present
      in_CNot_implies_uminus(2) multi_member_split multi_member_this union_commute)
  hence i': "i = get_maximum_level D M\<^sub>T"
    using i by auto
  have "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M))"
    using Set.imageI[OF decomp, of fst] by auto
  hence "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M\<^sub>T))"
    using fst_get_all_marked_decomposition_prepend_not_marked[OF nm] unfolding M  by auto
  then obtain M2' where decomp':"(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition M\<^sub>T)"
    by auto
  thus "backtrack T W"
    using backtrack.intros[OF T decomp' lev_l'] lev_l_D' i' unfolding W by force
qed

inductive cdcl_fw :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
fw_propagate: "propagate S S' \<Longrightarrow> cdcl_fw S S'" |
fw_conflict: "conflict S T \<Longrightarrow> full cdcl_bj T U \<Longrightarrow> cdcl_fw S U" |
fw_decided: "decided S S' \<Longrightarrow> cdcl_fw S S'"|
fw_rf: "cdcl_rf S S' \<Longrightarrow> cdcl_fw S S'"

lemma cdcl_fw_cdcl:
  assumes "cdcl_fw S T"
  shows "cdcl\<^sup>*\<^sup>* S T"
  using assms
proof (induction)
  case (fw_conflict S T U) note confl = this(1) and bj = this(2)
  have "cdcl S T" using confl by (simp add: cdcl.intros r_into_rtranclp)
  moreover
    have "cdcl_bj\<^sup>*\<^sup>* T U" using bj unfolding full_def by auto
    hence "cdcl\<^sup>*\<^sup>* T U" by (metis cdcl_o.bj mono_rtranclp other)
  ultimately show ?case by auto
qed (simp_all add: cdcl_o.intros cdcl.intros r_into_rtranclp)

abbreviation skip_or_resolve :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
"skip_or_resolve \<equiv> (\<lambda>S T. skip S T \<or> resolve S T)"

lemma cdcl_bj_decomp_resolve_skip_and_bj:
  assumes "cdcl_bj\<^sup>*\<^sup>* S T"
  shows "(skip_or_resolve\<^sup>*\<^sup>* S T
    \<or> (\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T))"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step T U) note st = this(1) and bj = this(2) and IH = this(3)
  have IH: "skip_or_resolve\<^sup>*\<^sup>* S T"
    proof -
      { assume "(\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T)"
        then obtain V where
          "backtrack V T"
          by blast
        with bj have False by induction fastforce+
      }
      thus ?thesis using IH by blast
    qed
  show ?case
    using bj
    proof (cases rule: cdcl_bj.cases)
      case backtrack
      thus ?thesis using IH by blast
    qed (metis (no_types, lifting) IH rtranclp.simps)+
qed

lemma resolve_skip_deterministic:
  "resolve S T \<Longrightarrow> skip S U \<Longrightarrow> False"
  by fastforce

lemma skip_or_resolve_append:
  assumes
    ST: "skip_or_resolve S T" and
    SV: "skip_or_resolve\<^sup>+\<^sup>+ S V"
  shows "skip_or_resolve\<^sup>*\<^sup>* T V"
proof -
  obtain U where SU: "skip_or_resolve S U" and UV: "skip_or_resolve\<^sup>*\<^sup>* U V"
    by (metis (no_types, lifting) SV tranclpD)
  have "T = U"
    using SU ST by (meson resolve_skip_deterministic resolve_unique skip_unique)
  thus ?thesis using UV by blast
qed

lemma backtrack_unique:
  assumes
    bt_T: "backtrack S T" and
    bt_U: "backtrack S U" and
    inv: "cdcl_all_inv_mes S"
  shows "T = U"
proof -
  obtain M N U' k D L i K M1 M2 where
    S: "S = (M, N, U', k, C_Clause (D + {#L#}))" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    "get_level L M = k" and
    "get_level L M = get_maximum_level (D+{#L#}) M" and
    "get_maximum_level D M = i" and
    T: "T = (Propagated L (D+{#L#}) # M1 , N, U' \<union> {D + {#L#}}, i, C_True)"
    using bt_T by auto

  obtain  D' L' i' K' M1' M2' where
    S': "S = (M, N, U', k, C_Clause (D' + {#L'#}))" and
    decomp': "(Marked K' (i'+1) # M1', M2') \<in> set (get_all_marked_decomposition M)" and
    "get_level L' M = k" and
    "get_level L' M = get_maximum_level (D'+{#L'#}) M" and
    "get_maximum_level D' M = i'" and
    U: "U = (Propagated L' (D'+{#L'#}) # M1', N, U' \<union> {D' + {#L'#}}, i', C_True)"
    using bt_U S by auto
  obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  obtain c' where M': "M = c' @ M2' @ Marked K' (i' + 1) # M1'"
    using decomp' by auto
  have marked: "get_all_levels_of_marked M = rev [1..<1+k]"
    using inv unfolding S cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
  hence "i < k"
    unfolding M
    by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have [simp]: "L = L'"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "L' \<in># D"
        using S unfolding S' by (fastforce simp: multiset_eq_iff split: split_if_asm)
      hence "get_maximum_level D M \<ge> k"
        using \<open>get_level L' M = k\<close> get_maximum_level_ge_get_level by blast
      thus False using \<open>get_maximum_level D M = i\<close> \<open>i < k\<close> by auto
    qed
  hence [simp]: "D = D'"
    using S S' by auto
  have [simp]: "i=i'" using \<open>get_maximum_level D' M = i'\<close> \<open>get_maximum_level D M = i\<close> by auto

  text \<open>Automation in a step later...\<close>
  have H: "\<And>a A B. insert a A = B \<Longrightarrow> a : B"
    by blast
  have "get_all_levels_of_marked (c@M2) = rev [i+2..<1+k]" and
    "get_all_levels_of_marked (c'@M2') = rev [i+2..<1+k]"
    using marked unfolding M
    using marked unfolding M'
    unfolding rev_swap[symmetric] by (auto dest: append_cons_eq_upt_length_i_end)
  from arg_cong[OF this(1), of set] arg_cong[OF this(2), of set]
  have
    "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i) (c @ M2) = []" and
    "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i) (c' @ M2') = []"
      unfolding dropWhile_eq_Nil_conv Ball_def
      by (intro allI; case_tac x; auto dest!: H simp add: in_set_conv_decomp)+

  hence "M1 = M1'"
    using arg_cong[OF M, of "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i)"]
    unfolding M' by auto
  thus ?thesis unfolding T U by auto
qed


lemma if_can_apply_backtrack_no_more_resolve:
  assumes
    skip: "skip\<^sup>*\<^sup>* S U" and
    bt: "backtrack S T" and
    inv: "cdcl_all_inv_mes S"
  shows "\<not>resolve U V"
proof (rule ccontr)
  assume resolve: "\<not>\<not>resolve U V"

  obtain L C M N U' k D where
    U: "U = (Propagated L (C + {#L#}) # M, N, U', k, C_Clause (D + {#-L#}))"and
    "get_maximum_level D (Propagated L (C + {#L#}) # M) = k" and
    "V = (M, N, U', k, C_Clause (remdups_mset (D + C)))"
    using resolve by auto

  have
    S: "clauses S = N"
       "learned_clauses S = U'"
       "backtrack_level S = k"
       "conflicting S = C_Clause (D + {#-L#})"
    using rtranclp_skip_state_decomp(2)[OF skip] unfolding U by auto
  obtain M\<^sub>0 where
    tr_S: "trail S = M\<^sub>0 @ trail U" and
    nm: "\<forall>m\<in>set M\<^sub>0. \<not>is_marked m"
    using rtranclp_skip_state_decomp[OF skip] apply (cases U) by blast

  obtain M' D' L' i K M1 M2 where
    S': "S = (M', N, U', k, C_Clause (D' + {#L'#}))"  and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M')" and
    "get_level L' M' = k" and
    "get_level L' M' = get_maximum_level (D'+{#L'#}) M'" and
    "get_maximum_level D' M' = i" and
    T: "T = (Propagated L' (D'+{#L'#}) # M1 , N, U' \<union> {D' + {#L'#}}, i, C_True)"
    using bt S apply (cases S) by (auto elim!: backtrackE) fastforce
  obtain c where M: "M' = c @ M2 @ Marked K (i + 1) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] by auto
  have marked: "get_all_levels_of_marked M' = rev [1..<1+k]"
    using inv unfolding S' cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
  hence "i < k"
    unfolding M by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have DD': "D' + {#L'#} = D + {#-L#}"
    using S S' by auto
  have [simp]: "L' = -L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "-L \<in># D'"
        using DD' by (metis add_diff_cancel_right' diff_single_trivial diff_union_swap
          multi_self_add_other_not_self)
      moreover
        have "no_dup M'"
           using inv unfolding U S' cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
        have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lits_of M)"
          using \<open>no_dup M'\<close> tr_S unfolding U S' by (auto simp: lits_of_def)
        have "get_all_levels_of_marked M' = rev [1..<1+k]"
          using inv unfolding U S' cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
        hence "get_all_levels_of_marked M = rev [1..<1+k]"
          using nm tr_S unfolding S' U by (simp add: get_all_levels_of_marked_no_marked)
        hence get_lev_L:
          "get_level L (Propagated L (C + {#L#}) # M) = k"
          using get_level_get_rev_level_get_all_levels_of_marked[OF atm_L_notin_M,
            of "[Propagated L (C + {#L#})]"] by simp
        have "atm_of L \<notin> atm_of ` (lits_of (rev M\<^sub>0))"
          using \<open>no_dup M'\<close> tr_S unfolding U S' by (auto simp: lits_of_def)
        hence "get_level L M' = k"
          using get_rev_level_notin_end[of L "rev M\<^sub>0" 0 "rev M @ Propagated L (C + {#L#}) # []"]
          using tr_S get_lev_L unfolding U S' by (simp add:nm lits_of_def)
      ultimately have "get_maximum_level D' M' \<ge> k"
        by (metis get_maximum_level_ge_get_level get_rev_level_uminus)
      thus False
        using \<open>i < k\<close> unfolding \<open>get_maximum_level D' M' = i\<close> by auto
    qed
  have [simp]: "D = D'" using DD' by auto
  have "cdcl_all_inv_mes U"
    by (metis (no_types, hide_lams) bj cdcl_bj.skip inv local.skip mono_rtranclp other
      rtranclp_cdcl_all_inv_mes_inv)
  hence "Propagated L (C + {#L#}) # M \<Turnstile>as CNot (D' + {#L'#})"
    unfolding cdcl_all_inv_mes_def cdcl_conflicting_def U by auto
  hence "\<forall>L'\<in>#D. atm_of L' \<in> atm_of ` lits_of (Propagated L (C + {#L#}) # M)"
    by (metis CNot_plus CNot_singleton Un_insert_right \<open>D = D'\<close> true_annots_insert ball_msetI
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set  in_CNot_implies_uminus(2)
      sup_bot.comm_neutral)
  hence "get_maximum_level D M' = k"
     using tr_S nm
       get_maximum_level_skip_un_marked_not_present[of D "Propagated L (C + {#L#}) # M" M\<^sub>0]
     unfolding  \<open>get_maximum_level D (Propagated L (C + {#L#}) # M) = k\<close> unfolding \<open>D = D'\<close> U S'
     by simp
  show False
    using \<open>get_maximum_level D' M' = i\<close> \<open>get_maximum_level D M' = k\<close> \<open>i < k\<close> by auto
qed

lemma if_can_apply_resolve_no_more_backtrack:
  assumes
    skip: "skip\<^sup>*\<^sup>* S U" and
    resolve: "resolve S T" and
    inv: "cdcl_all_inv_mes S"
  shows "\<not>backtrack U V"
  using assms
  by (meson if_can_apply_backtrack_no_more_resolve rtranclp.rtrancl_refl
    rtranclp_skip_backtrack_backtrack)

lemma if_can_apply_backtrack_skip_or_resolve_is_skip:
  assumes
    bt: "backtrack S T" and
    skip: "skip_or_resolve\<^sup>*\<^sup>* S U" and
    inv: "cdcl_all_inv_mes S"
  shows "skip\<^sup>*\<^sup>* S U"
  using assms(2,3,1)
  by (induction) (simp_all add: if_can_apply_backtrack_no_more_resolve)

lemma cdcl_bj_bj_decomp:
  assumes "cdcl_bj\<^sup>*\<^sup>* S W" and "cdcl_all_inv_mes S"
  shows
    "(\<exists>T U V. (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T
        \<and> (\<lambda>T U. resolve T U \<and> no_step backtrack T) T U
        \<and> skip\<^sup>*\<^sup>* U V  \<and> backtrack V W)
    \<or> (\<exists>T U. (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T
        \<and> (\<lambda>T U. resolve T U \<and> no_step backtrack T) T U \<and> skip\<^sup>*\<^sup>* U W)
    \<or> (\<exists>T. skip\<^sup>*\<^sup>* S T  \<and> backtrack T W)
    \<or> skip\<^sup>*\<^sup>* S W" (is "?RB S W \<or> ?R S W \<or> ?SB S W \<or> ?S S W")
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step W X) note st = this(1) and bj = this(2) and IH = this(3)[OF this(4)] and inv = this(4)
  have "\<not>?RB S W" and "\<not>?SB S W" using bj by (auto simp add: cdcl_bj.simps)
  hence IH: "?R S W \<or> ?S S W" using IH by blast

  have "cdcl\<^sup>*\<^sup>* S W" by (metis cdcl_o.bj mono_rtranclp other st)
  hence inv_W: "cdcl_all_inv_mes W" by (simp add: rtranclp_cdcl_all_inv_mes_inv step.prems)
  consider
      (BT) X' where "backtrack W X'"
    | (skip) "no_step backtrack W" and "skip W X"
    | (resolve) "no_step backtrack W" and "resolve W X"
    using bj cdcl_bj.cases by blast
  thus ?case
    proof cases
      case (BT X')
      hence "backtrack W X \<or> skip W X"
        using bj if_can_apply_backtrack_no_more_resolve[of W W X' X] inv_W cdcl_bj.cases by blast
      show ?thesis
        using IH by (meson \<open>backtrack W X \<or> skip W X\<close> rtranclp.rtrancl_into_rtrancl)
    next
      case skip
      thus ?thesis using IH  by (meson rtranclp.rtrancl_into_rtrancl)
    next
      case resolve note no_bt = this(1) and res = this(2)
      consider
          (RS) T U where
            "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T" and
            "resolve T U" and
            "no_step backtrack T" and
            "skip\<^sup>*\<^sup>* U W"
        | (S)  "skip\<^sup>*\<^sup>* S W"
        using IH by auto
      thus ?thesis
        proof cases
          case (RS T U)
          have "cdcl\<^sup>*\<^sup>* S T"
            by (metis (no_types, lifting) RS(1) cdcl_bj.resolve cdcl_o.bj mono_rtranclp other skip)
          hence "cdcl_all_inv_mes U"
            by (meson RS(2) cdcl_all_inv_mes_inv cdcl_bj.resolve cdcl_o.bj other
              rtranclp_cdcl_all_inv_mes_inv step.prems)
          { fix U'
            assume "skip\<^sup>*\<^sup>* U U'" and "skip\<^sup>*\<^sup>* U' W"
            have "cdcl_all_inv_mes U'"
              by (metis (no_types, hide_lams) \<open>cdcl_all_inv_mes U\<close> \<open>skip\<^sup>*\<^sup>* U U'\<close> cdcl_o.bj
                mono_rtranclp other rtranclp_cdcl_all_inv_mes_inv skip)
            hence "no_step backtrack U'"
              using if_can_apply_backtrack_no_more_resolve[OF \<open>skip\<^sup>*\<^sup>* U' W\<close> ] res by blast
          }
          with \<open>skip\<^sup>*\<^sup>* U W\<close>
          have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U W"
             proof induction
               case base
               thus ?case by simp
             next
               case (step V W) note st = this(1) and skip = this(2) and IH = this(3) and H = this(4)
               have "\<And>U'. skip\<^sup>*\<^sup>* U' V \<Longrightarrow> skip\<^sup>*\<^sup>* U' W"
                 using skip by auto
               hence "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U V"
                 using IH H by blast
               moreover have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* V W"
                 (* adding the \<^sup>*\<^sup>* here makes the ?case easier to find *)
                 by (simp add: local.skip r_into_rtranclp st step.prems)
               ultimately show ?case by simp
             qed
          thus ?thesis
            proof -
              have f1: "\<forall>p pa pb pc. \<not> p (pa::('a, nat, 'a literal multiset) marked_lit list
                \<times> 'a literal multiset set \<times> 'a literal multiset set \<times> nat
                \<times> 'a literal multiset conflicting_clause) pb \<or> \<not> p\<^sup>*\<^sup>* pb pc \<or> p\<^sup>*\<^sup>* pa pc"
                by (meson converse_rtranclp_into_rtranclp)
              have "skip_or_resolve T U \<and> no_step backtrack T"
                using RS(2) RS(3) by force
              hence "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* T W"
                using f1 \<open>(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U W\<close>
                by presburger
              hence "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* S W"
                using RS(1) by force
              thus ?thesis
                using no_bt res by blast
            qed
        next
          case S
          { fix U'
            assume "skip\<^sup>*\<^sup>* S U'" and "skip\<^sup>*\<^sup>* U' W"
            have "cdcl_all_inv_mes U'"
              by (metis (no_types, hide_lams) \<open>cdcl_all_inv_mes S\<close> \<open>skip\<^sup>*\<^sup>* S U'\<close> cdcl_o.bj
                mono_rtranclp other rtranclp_cdcl_all_inv_mes_inv skip)
            hence "no_step backtrack U'"
              using if_can_apply_backtrack_no_more_resolve[OF \<open>skip\<^sup>*\<^sup>* U' W\<close> ] res by blast
          }
          with S
          have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S W"
             proof induction
               case base
               thus ?case by simp
             next
               case (step V W) note st = this(1) and skip = this(2) and IH = this(3) and H = this(4)
               have "\<And>U'. skip\<^sup>*\<^sup>* U' V \<Longrightarrow> skip\<^sup>*\<^sup>* U' W"
                 using skip by auto
               hence "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S V"
                 using IH H by blast
               moreover have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* V W"
                 (* adding the \<^sup>*\<^sup>* here makes the ?case easier to find *)
                 by (simp add: local.skip r_into_rtranclp st step.prems)
               ultimately show ?case by simp
             qed
          thus ?thesis using res no_bt by blast
        qed
    qed
qed

lemma rtranclp_cdcl_bj_resolve_in_the_middle:
  assumes
    "cdcl_bj\<^sup>*\<^sup>* S U" and
    "(\<lambda>S T. resolve S T \<and> no_step backtrack S) S T" and
    "no_step cdcl_bj U"
  shows "cdcl_bj S T \<and> cdcl_bj\<^sup>*\<^sup>* T U"
  using assms
  by (metis cdcl_bj.cases resolve resolve_skip_deterministic resolve_unique rtranclp_unfold
    tranclpD)

lemma cdcl_bj_strongly_confluent:
  assumes
    "cdcl_bj\<^sup>*\<^sup>* S V" and
    "cdcl_bj\<^sup>*\<^sup>* S T" and
    n_s: "no_step cdcl_bj V" and
    inv: "cdcl_all_inv_mes S"
  shows "cdcl_bj\<^sup>*\<^sup>* T V"
  using assms(2)
proof induction
  case base
  thus ?case by (simp add: assms(1))
next
  case (step T U) note st =this(1) and s_o_r = this(2) and IH = this(3)
  obtain U' where
    T_U': "cdcl_bj T U'" and
    "cdcl_bj\<^sup>*\<^sup>* U' V"
    using IH n_s s_o_r by (metis rtranclp_unfold tranclpD)
  have inv_T: "cdcl_all_inv_mes T"
    by (metis (no_types, hide_lams) inv bj mono_rtranclp other rtranclp_cdcl_all_inv_mes_inv st)

  show ?case
    using s_o_r
    proof cases
      case backtrack
      then obtain V0 where "skip\<^sup>*\<^sup>* T V0" and "backtrack V0 V"
        using IH if_can_apply_backtrack_skip_or_resolve_is_skip[OF backtrack _ inv_T]
        rtranclp_skip_backtrack_backtrack[of T V] cdcl_bj_decomp_resolve_skip_and_bj[OF IH]
        by (meson cdcl_bj.backtrack inv_T n_s rtranclp_skip_backtrack_backtrack_end)
      thus ?thesis by (metis backtrack_unique inv_T local.backtrack rtranclp.rtrancl_refl
        rtranclp_skip_backtrack_backtrack)
    next
      case resolve
      thus ?thesis
        by (metis T_U' \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> cdcl_bj.simps if_can_apply_backtrack_no_more_resolve inv_T
          resolve_skip_deterministic resolve_unique rtranclp.simps)
    next
      case skip
      have "cdcl_all_inv_mes T"
        by (metis (no_types, hide_lams) inv bj mono_rtranclp other rtranclp_cdcl_all_inv_mes_inv st)
      consider
          (sk)  "skip T U'"
        | (bt)  "backtrack T U'"
        using T_U' by (meson cdcl_bj.cases local.skip resolve_skip_deterministic)
      thus ?thesis
        proof cases
          case sk
          thus ?thesis using \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> local.skip by blast
        next
          case bt
          have "skip\<^sup>+\<^sup>+ T U"
            using local.skip by blast (* 0.3 ms *)
          thus ?thesis
            using bt by (metis (no_types) \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> backtrack inv_T reflclp_tranclp
              rtranclp_into_tranclp2 rtranclp_skip_backtrack_backtrack_end sup2CI)
        qed
    qed
qed

lemma cdcl_bj_unique_normal_form:
  assumes "cdcl_bj\<^sup>*\<^sup>* S T" and "cdcl_bj\<^sup>*\<^sup>* S U" and
    n_s_U: "no_step cdcl_bj U" and
    n_s_T: "no_step cdcl_bj T" and
    inv: "cdcl_all_inv_mes S"
  shows "T = U"
  using assms by (meson cdcl_bj_strongly_confluent converse_rtranclpE)


lemma
  assumes "cdcl_bj\<^sup>*\<^sup>* S T" and "full cdcl_bj S U" and
    inv: "cdcl_all_inv_mes S"
  shows "cdcl_bj\<^sup>*\<^sup>* T U"
  using assms by (metis cdcl_bj_strongly_confluent full_def tranclp_into_rtranclp)

text \<open>As is, this is wrong because of the conflict that is merged within the other rules\<close>
lemma
  assumes
    inv: "cdcl_all_inv_mes S" and
    "cdcl S U"
  shows "\<exists>T. cdcl_fw S T \<and> cdcl\<^sup>*\<^sup>* U T"
  using assms(2,1)
proof (induction rule: cdcl_all_rules_induct)
  case (conflict S T)
  thus ?case using fw_conflict
oops

subsection \<open>A better version of @{term cdcl_s}\<close>
inductive cdcl_s' :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
conflict': "full cdcl_cp S S' \<Longrightarrow> cdcl_s' S S'" |
decided': "decided S S'  \<Longrightarrow> no_step cdcl_cp S \<Longrightarrow> full0 cdcl_cp S' S'' \<Longrightarrow> cdcl_s' S S''" |
bj': "full cdcl_bj S S'  \<Longrightarrow> no_step cdcl_cp S \<Longrightarrow> full0 cdcl_cp S' S'' \<Longrightarrow> cdcl_s' S S''"

lemma rtranclp_cdcl_bj_full_cdclp_cdcl_s:
  "cdcl_bj\<^sup>*\<^sup>* S S' \<Longrightarrow> full0 cdcl_cp S' S'' \<Longrightarrow> cdcl_s\<^sup>*\<^sup>* S S''"
proof (induction rule: converse_rtranclp_induct)
  case base
  thus ?case by (metis cdcl_s.conflict' full0_unfold rtranclp.simps)
next
  case (step T U) note st =this(2) and bj = this(1) and IH = this(3)[OF this(4)]
  have "no_step cdcl_cp T"
    using bj by (auto simp add: cdcl_bj.simps)
  consider
      (U) "U = S'"
    | (U') U' where "cdcl_bj U U'" and "cdcl_bj\<^sup>*\<^sup>* U' S'"
    using st by (metis converse_rtranclpE)
  thus ?case
    proof cases
      case U
      thus ?thesis using \<open>no_step cdcl_cp T\<close> cdcl_o.bj local.bj other' step.prems by blast
    next
      case U' note U' = this(1)
      have "no_step cdcl_cp U"
        using U' by (fastforce simp: cdcl_cp.simps cdcl_bj.simps)
      hence "full0 cdcl_cp U U"
        by (simp add: full0_unfold)
      hence "cdcl_s T U"
        using \<open>no_step cdcl_cp T\<close> cdcl_s.simps local.bj by blast
      thus ?thesis using IH by auto
    qed
qed

lemma cdcl_s'_is_rtranclp_cdcl_s:
  "cdcl_s' S T \<Longrightarrow> cdcl_s\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl_s'.induct)
    apply (auto intro: cdcl_s.intros)[]
   using decided other' apply blast
  by (metis full_def rtranclp_cdcl_bj_full_cdclp_cdcl_s tranclp_into_rtranclp)

lemma XXX: "cdcl_bj\<^sup>*\<^sup>* S S' \<Longrightarrow> full cdcl_cp S' T' \<Longrightarrow> cdcl_s\<^sup>*\<^sup>* S T'"
  by (simp add: full0_unfold rtranclp_cdcl_bj_full_cdclp_cdcl_s)

lemma cdcl_cp_decreasing_measure:
  assumes "cdcl_cp S T" and "cdcl_all_inv_mes S"
  shows "(\<lambda>S. card (atms_of_m (clauses S)) - length (trail S) + (if conflicting S = C_True then 1 else 0)) S
        > (\<lambda>S. card (atms_of_m (clauses S)) - length (trail S) + (if conflicting S = C_True then 1 else 0)) T"
  using assms
proof -
  have "length (trail T) \<le> card (atms_of_m (clauses T))"
    by (rule length_model_le_vars_all_inv)
     (meson assms(1) assms(2) cdcl_all_inv_mes_inv cdcl_cp.cases conflict propagate)
  with assms
  show ?thesis by (induction) force+
qed

lemma cdcl_cp_wf: "wf {(b,a). cdcl_all_inv_mes a \<and> cdcl_cp a b}"
  apply (rule wf_wf_if_measure'[of less_than _ _
      "(\<lambda>S. card (atms_of_m (clauses S)) - length (trail S)
        + (if conflicting S = C_True then 1 else 0))"])
    apply simp
  using cdcl_cp_decreasing_measure unfolding less_than_iff by blast

lemma rtranclp_cdcl_all_inv_mes_cdcl_cp_iff_rtranclp_cdcl_cp:
  "cdcl_all_inv_mes S \<Longrightarrow> (\<lambda>a b. cdcl_all_inv_mes a \<and> cdcl_cp a b)\<^sup>*\<^sup>* S T \<longleftrightarrow> cdcl_cp\<^sup>*\<^sup>* S T"
  (is "?inv S \<Longrightarrow> ?I S T \<longleftrightarrow> ?C S T")
proof
  assume
    "?I S T"
    "?inv S"
  thus "?C S T" by (induction) auto
next
  assume
    "?C S T"
    "?inv S"
  thus "?I S T"
    apply (induction)
      apply simp
    by (metis (no_types, lifting) \<open>cdcl_all_inv_mes S\<close> inf_sup_aci(5) r_into_rtranclp
      reflclp_tranclp rtranclpD rtranclp_cdcl_all_inv_mes_inv rtranclp_idemp rtranclp_into_tranclp1
      rtranclp_reflclp tranclp_cdcl_cp_tranclp_cdcl)
qed

lemma cdcl_bj_measure:
  assumes "cdcl_bj S T"
  shows "length (trail S) + (if conflicting S = C_True then 0 else 1)
    > length (trail T) +  (if conflicting T = C_True then 0 else 1)"
  using assms apply (induction rule: cdcl_bj.induct)
  by(auto elim!: backtrackE dest!: get_all_marked_decomposition_exists_prepend
    dest:arg_cong[of _ _ length])

lemma cdcl_bj_wf:
  "wf {(b,a). cdcl_bj a b}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) +  (if conflicting T = C_True then 0 else 1)", simplified])
  using cdcl_bj_measure by blast

lemma cdcl_cp_normalized_element:
  assumes inv: "cdcl_all_inv_mes S"
  obtains T where "full0 cdcl_cp S T"
proof -
  obtain T where T: "full0 (\<lambda>a b. cdcl_all_inv_mes a \<and> cdcl_cp a b) S T"
    using cdcl_cp_wf wf_exists_normal_form[of "\<lambda>a b. cdcl_all_inv_mes a \<and> cdcl_cp a b"]
    unfolding full0_def by blast
    hence "cdcl_cp\<^sup>*\<^sup>* S T"
      using rtranclp_cdcl_all_inv_mes_cdcl_cp_iff_rtranclp_cdcl_cp inv unfolding full0_def
      by blast
    moreover
      hence "cdcl_all_inv_mes T"
        by (metis inv rtranclp_cdcl_all_inv_mes_inv rtranclp_unfold tranclp_cdcl_cp_tranclp_cdcl)
      hence "no_step cdcl_cp T"
        using T unfolding full0_def by auto
    ultimately show thesis using that unfolding full0_def by blast
qed

lemma cdcl_cp_cdcl_bj_bissimulation:
  assumes
    "full0 cdcl_cp T U" and
    "cdcl_bj\<^sup>*\<^sup>* T T'" and
    "cdcl_all_inv_mes T" and
    "no_step cdcl_bj T'"
  shows "\<exists>U'. full0 cdcl_cp T' U' \<and> cdcl_s\<^sup>*\<^sup>* U U' \<and> cdcl_s'\<^sup>*\<^sup>* U U'"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl_o.bj local.bj mono_rtranclp other st
      rtranclp.rtrancl_into_rtrancl)
  hence inv_T'': "cdcl_all_inv_mes T''"
    using inv rtranclp_cdcl_all_inv_mes_inv by blast
  have "cdcl_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  hence "T = U"
    proof -
      obtain Z where "cdcl_bj T Z"
          by (meson tranclpD \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close>)
      { assume "cdcl_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl_cp T Z'"
          by (meson tranclpD)
        hence False
          using \<open>cdcl_bj T Z\<close> by (fastforce simp: cdcl_bj.simps cdcl_cp.simps)
      }
      thus ?thesis
        using full unfolding full0_def rtranclp_unfold by blast
    qed
  obtain U' where "full0 cdcl_cp T'' U'"
    using cdcl_cp_normalized_element inv_T'' by blast
  moreover hence "cdcl_s\<^sup>*\<^sup>* U U'"
    by (metis \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl_bj_full_cdclp_cdcl_s rtranclp_unfold)
  moreover have "cdcl_s'\<^sup>*\<^sup>* U U'"
    by (metis (no_types, hide_lams) \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> calculation(1) cdcl_s'.simps full 
      full0_def full_def r_into_rtranclp step.prems(3))
  ultimately show ?case by blast
qed

text \<open>TODO: the connection \<open>cdcl_s\<^sup>*\<^sup>*\<close> should be \<open>cdcl_bj; full cdcl_cp\<close>.\<close>
lemma cdcl_s_cdcl_s'_connected:
  assumes "cdcl_s S U" and "cdcl_all_inv_mes S"
  shows "\<exists>T. cdcl_s' S T \<and> cdcl_s\<^sup>*\<^sup>* U T \<and> cdcl_s'\<^sup>*\<^sup>* U T"
  using assms
proof (induction rule: cdcl_s.induct)
  case (conflict' S T)
  hence "cdcl_s' S T"
    using cdcl_s'.conflict' by blast
  thus ?case
    by blast
next
  case (other' S T U) note o = this(1) and n_s = this(2) and full = this(3) and inv = this(4)
  show ?case
    using o
    proof cases
      case (decided)
      thus ?thesis using cdcl_s'.simps full n_s by blast
    next
      case bj
      obtain T' where T': "full0 cdcl_bj T T'"
        using wf_exists_normal_form cdcl_bj_wf unfolding full0_def by metis
      hence "full0 cdcl_bj S T'"
        by (metis converse_rtranclp_into_rtranclp full0_def local.bj)

      have "cdcl_bj\<^sup>*\<^sup>* T T'"
        using T' unfolding full0_def by simp
      have "cdcl_all_inv_mes T"
        using cdcl_all_inv_mes_inv o other other'.prems by blast
      then obtain U' where "full0 cdcl_cp T' U'" and "cdcl_s\<^sup>*\<^sup>* U U'" and "cdcl_s'\<^sup>*\<^sup>* U U'"
        using cdcl_cp_cdcl_bj_bissimulation[OF full \<open>cdcl_bj\<^sup>*\<^sup>* T T'\<close>] T'
        unfolding full0_def by blast
      have "cdcl_s' S U'"
        by (metis \<open>cdcl_bj\<^sup>\<down> S T'\<close> \<open>cdcl_cp\<^sup>\<down> T' U'\<close> cdcl_s'.simps full0_unfold local.bj n_s)
      then show ?thesis
        using \<open>cdcl_s\<^sup>*\<^sup>* U U'\<close> \<open>cdcl_s'\<^sup>*\<^sup>* U U'\<close> by blast
    qed
qed

lemma cdcl_s_cdcl_s'_no_step:
  assumes "cdcl_s S U" and "cdcl_all_inv_mes S" and "no_step cdcl_bj U"
  shows "cdcl_s' S U"
  using cdcl_s_cdcl_s'_connected[OF assms(1,2)] assms(3) oops

lemma cdcl_s_cdcl_s'_connected:
  assumes "cdcl_s S U" and "cdcl_all_inv_mes S" and "cdcl_s' S V"
  shows "cdcl_s' U V \<or> U = V"
  using assms
proof (induction rule:cdcl_s.induct)
  case (conflict' S T) note full = this(1) and inv = this(2) and s' = this(3)
  consider
    (ST) "cdcl_cp S T" and "full cdcl_cp S T"
  | (SST) S' where "cdcl_cp S S'" and "full cdcl_cp S' T"
  using full unfolding full_def full0_def by (metis converse_tranclpE)
  thus ?case
    proof cases
      case ST
      hence  "T = V"  sorry
    next
      case (SST S')

oops

end