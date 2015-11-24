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
  hence "atm_of L \<in> atm_of ` lit_of `set M"
    using lev_l get_rev_level_ge_0_atm_of_in by fastforce
  hence L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' by auto
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

inductive cdcl_fw :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
fw_propagate: "propagate S S' \<Longrightarrow> cdcl_fw S S'" |
fw_conflict: "conflict S T \<Longrightarrow> full cdcl_bj T U \<Longrightarrow> cdcl_fw S U" |
fw_other: "decided S S' \<Longrightarrow> cdcl_fw S S'"|
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

lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m\<in>set M. \<not>is_marked m)" and
    "T = (trail T, clauses S, learned_clauses S, backtrack_level S, conflicting S)"
  using assms by (induction rule: rtranclp_induct) (cases S;auto)+

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
        have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lit_of ` set M)"
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

lemma
  assumes "cdcl_bj\<^sup>*\<^sup>* S T" and "cdcl_bj\<^sup>*\<^sup>* S U"
  shows "cdcl_bj\<^sup>*\<^sup>* T U \<or> cdcl_bj U T"
  using assms
proof -
  consider
      (RS) "skip_or_resolve\<^sup>*\<^sup>* S T"
    | (RSB) S' where "skip_or_resolve\<^sup>*\<^sup>* S S'" and "backtrack S' T"
    using assms(1) cdcl_bj_decomp_resolve_skip_and_bj by blast
  thus ?thesis
    proof cases
      case RS
      with \<open>cdcl_bj\<^sup>*\<^sup>* S U\<close>
      show ?thesis

        apply (induction)


          oops
lemma
  assumes "cdcl_bj\<^sup>*\<^sup>* S T" and "cdcl_bj\<^sup>*\<^sup>* S U" and
    n_s_U: "no_step cdcl_bj U" and
    n_s_T: "no_step cdcl_bj T"
  shows "T = U"
  using assms
proof -
  consider
      (RS) "skip_or_resolve\<^sup>*\<^sup>* S T"
    | (RSB) S' where "skip_or_resolve\<^sup>*\<^sup>* S S'" and "backtrack S' T"
    using assms(1) cdcl_bj_decomp_resolve_skip_and_bj by blast
  thus ?thesis
    proof cases
      case RS
      with \<open>cdcl_bj\<^sup>*\<^sup>* S U\<close> n_s_U
      show ?thesis
        apply (induction)
          using assms(1) apply (metis converse_rtranclpE)


  (* Idea : cdcl is resolve or skip and first step if st \<Rightarrow> deterministic
     is backtrack \<Rightarrow> st is skip**; backtrack
     *)
oops

lemma
  assumes "cdcl_bj\<^sup>*\<^sup>* S T" and "full cdcl_bj S U"
  shows "cdcl_bj\<^sup>*\<^sup>* T U"
  using assms
proof (induction arbitrary: )
  case base
  thus ?case unfolding full_def by (metis tranclp_into_rtranclp)
next
  case (step T V) note st = this(1) and cdcl = this(2) and IH = this(3)[OF this(4)] and bj = this(4)
  show ?case
  (* Idea : cdcl is resolve or skip and first step if st \<Rightarrow> deterministic
     is backtrack \<Rightarrow> st is skip**; backtrack
     *)
oops


theorem
  "cdcl_bj\<^sup>*\<^sup>* S T \<Longrightarrow> full cdcl_bj S U \<Longrightarrow> cdcl\<^sup>*\<^sup>* T U"
  apply (induction rule: converse_rtranclp_induct)
oops
end