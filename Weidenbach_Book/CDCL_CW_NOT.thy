theory CDCL_CW_NOT
imports CDCL_CW_Termination CDCL_NOT
begin

declare upt.simps(2)[simp del]
sledgehammer_params[verbose]

context cdcl_cw_ops
begin

lemma update_trail_trail_id[simp]:"update_trail (trail S) S = S"
  by (auto simp: st_equal)

lemma cdcl_bj_measure:
  assumes "cdcl_bj S T"
  shows "length (trail S) + (if conflicting S = C_True then 0 else 1)
    > length (trail T) +  (if conflicting T = C_True then 0 else 1)"
  using assms apply (induction rule: cdcl_bj.induct)
  by (auto elim!: backtrackE dest!: get_all_marked_decomposition_exists_prepend
    dest:arg_cong[of _ _ length])

lemma cdcl_bj_wf:
  "wf {(b,a). cdcl_bj a b}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) +  (if conflicting T = C_True then 0 else 1)", simplified])
  using cdcl_bj_measure by blast

lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m\<in>set M. \<not>is_marked m)" and
    "T = update_trail (trail T) S"
  using assms by (induction rule: rtranclp_induct) (auto simp: st_equal)+

lemma rtranclp_skip_backtrack_backtrack:
  assumes
    "skip\<^sup>*\<^sup>* S T" and
    "backtrack T W" and
    "cdcl_all_inv_mes S"
  shows "backtrack S W"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step T V) note st = this(1) and skip = this(2) and IH = this(3) and bt = this(4) and
    inv = this(5)
  obtain M N k M1 M2 K i D L U where
    V: "state V = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "state W = (Propagated L (mark_of_cls (D + {#L#})) # M1, N, insert (D + {#L#}) U,
      get_maximum_level D M, C_True)" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    lev_l: "get_level L M = k" and
    lev_l_D: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "i = get_maximum_level D M"
    using bt by auto
  let ?D = "(D + {#L#})"
  obtain L' C' where
    T: "state T = (Propagated L' C' # M, N, U, k, C_Clause ?D)" and
    "V = update_trail M T" and
    "-L' \<notin># ?D" and
    "?D \<noteq> {#}"
    using skip V by auto

  let ?M =  "Propagated L' C' # M"
  have "cdcl\<^sup>*\<^sup>* S T" using bj cdcl_bj.skip mono_rtranclp[of skip cdcl S T] other st by meson
  hence inv': "cdcl_all_inv_mes T"
    using rtranclp_cdcl_all_inv_mes_inv inv by blast
  have M_lev: "cdcl_M_level_inv T" using inv' unfolding cdcl_all_inv_mes_def by auto
  hence n_d': "no_dup ?M"
    using T unfolding cdcl_M_level_inv_def by auto

  have "k > 0"
    using decomp M_lev T unfolding cdcl_M_level_inv_def by auto
  hence "atm_of L \<in> atm_of ` lits_of M"
    using lev_l get_rev_level_ge_0_atm_of_in by fastforce
  hence L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' unfolding lits_of_def by auto
  have L'_M: "atm_of L' \<notin> atm_of ` lits_of M"
    using n_d' unfolding lits_of_def by auto
  have "?M \<Turnstile>as CNot ?D"
    using inv' T unfolding cdcl_conflicting_def cdcl_all_inv_mes_def by auto
  hence "L' \<notin># ?D"
    using L_L' L'_M unfolding true_annots_def by (auto simp add: true_annot_def true_cls_def
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set Ball_mset_def
      split: split_if_asm)

  have "skip\<^sup>*\<^sup>* S V"
    using st skip by auto
  hence [simp]: "init_clss S = N" and [simp]: "learned_clss S = U"
    using V \<open>V = update_trail M T\<close> \<open>cdcl\<^sup>*\<^sup>* S T\<close> rtranclp_cdcl_init_clss apply auto[1]
    using rtranclp_skip_state_decomp[OF \<open>skip\<^sup>*\<^sup>* S V\<close>] V by auto
  hence W_S: "W = update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
  (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True T)))"
    unfolding st_equal W using i T by simp

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
  moreover

  ultimately have "backtrack T W"
    using T(1) W_S by blast


  thus ?thesis using IH inv by blast
qed

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
    S: "state S = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "state W = (Propagated L (mark_of_cls (D + {#L#})) # M1, N, insert (D + {#L#}) U,
       get_maximum_level D M, C_True)"
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
  have T: "state T = (M\<^sub>T, N, U, k, C_Clause ?D)"
    using M\<^sub>T rtranclp_skip_state_decomp(2) skip S
    by (metis backtrack_lvl_update_trail conflicting_update_trail learned_update_trail prod.inject
      trail_update_clss)
  have "cdcl_all_inv_mes T"
    by (smt bj cdcl_all_inv_mes_inv cdcl_bj.skip inv local.skip other rtranclp_induct)
  hence "M\<^sub>T \<Turnstile>as CNot ?D"
    unfolding cdcl_all_inv_mes_def cdcl_conflicting_def using T by blast
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
    using inv S unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
  ultimately have "\<forall>L\<in>#?D. atm_of L \<notin> atm_of ` lits_of MS"
    unfolding M unfolding lits_of_def by auto
  hence H: "\<And>L. L\<in>#?D \<Longrightarrow> get_level L M  = get_level L M\<^sub>T"
    unfolding M by (fastforce simp: lits_of_def)
  have [simp]: "get_maximum_level ?D M = get_maximum_level ?D M\<^sub>T"
    by (metis \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close>  M nm ball_msetI true_annots_CNot_all_atms_defined
      get_maximum_level_skip_un_marked_not_present)

  have lev_l': "get_level L M\<^sub>T = k"
    using lev_l by (auto simp: H)
  have W: "W = update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
    (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True T)))"
    unfolding st_equal using W T i by simp_all

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
    using backtrack.intros[OF T decomp' lev_l'] lev_l_D' i' W by force
qed


abbreviation skip_or_resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
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
    S: "state S = (M, N, U', k, C_Clause (D + {#L#}))" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    "get_level L M = k" and
    "get_level L M = get_maximum_level (D+{#L#}) M" and
    "get_maximum_level D M = i" and
    T: "state T = (Propagated L (mark_of_cls (D+{#L#})) # M1 , N, U' \<union> {D + {#L#}}, i, C_True)"
    using bt_T by auto

  obtain  D' L' i' K' M1' M2' where
    S': "state S = (M, N, U', k, C_Clause (D' + {#L'#}))" and
    decomp': "(Marked K' (i'+1) # M1', M2') \<in> set (get_all_marked_decomposition M)" and
    "get_level L' M = k" and
    "get_level L' M = get_maximum_level (D'+{#L'#}) M" and
    "get_maximum_level D' M = i'" and
    U: "state U = (Propagated L' (mark_of_cls(D'+{#L'#})) # M1', N, U' \<union> {D' + {#L'#}}, i', C_True)"
    using bt_U S by (auto elim!: backtrackE)
  obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  obtain c' where M': "M = c' @ M2' @ Marked K' (i' + 1) # M1'"
    using decomp' by auto
  have marked: "get_all_levels_of_marked M = rev [1..<1+k]"
    using inv S unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
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
  thus ?thesis using T U by (auto simp: st_equal)
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
    U: "state U = (Propagated L (mark_of_cls (C + {#L#})) # M, N, U', k, C_Clause (D + {#-L#}))"and
    "get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M) = k" and
    "state V = (M, N, U', k, C_Clause (remdups_mset (D + C)))"
    using resolve by auto

  have
    S: "init_clss S = N"
       "learned_clss S = U'"
       "backtrack_lvl S = k"
       "conflicting S = C_Clause (D + {#-L#})"
    using rtranclp_skip_state_decomp(2)[OF skip] U by auto
  obtain M\<^sub>0 where
    tr_S: "trail S = M\<^sub>0 @ trail U" and
    nm: "\<forall>m\<in>set M\<^sub>0. \<not>is_marked m"
    using rtranclp_skip_state_decomp[OF skip] by blast

  obtain M' D' L' i K M1 M2 where
    S': "state S = (M', N, U', k, C_Clause (D' + {#L'#}))"  and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M')" and
    "get_level L' M' = k" and
    "get_level L' M' = get_maximum_level (D'+{#L'#}) M'" and
    "get_maximum_level D' M' = i" and
    T: "state T = (Propagated L' (mark_of_cls (D'+{#L'#})) # M1 , N, U' \<union> {D' + {#L'#}}, i, C_True)"
    using bt S apply (cases S) by auto
  obtain c where M: "M' = c @ M2 @ Marked K (i + 1) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] by auto
  have marked: "get_all_levels_of_marked M' = rev [1..<1+k]"
    using inv S' unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
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
        have M': "M' = M\<^sub>0 @ Propagated L (mark_of_cls (C + {#L#})) # M"
          using tr_S U S S' by (auto simp: lits_of_def)
        have "no_dup M'"
           using inv U S' unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
        have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lits_of M)"
          using \<open>no_dup M'\<close> M' U S S' by (auto simp: lits_of_def)
        have "get_all_levels_of_marked M' = rev [1..<1+k]"
          using inv U S' unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
        hence "get_all_levels_of_marked M = rev [1..<1+k]"
          using nm M' S' U by (simp add: get_all_levels_of_marked_no_marked)
        hence get_lev_L:
          "get_level L (Propagated L (mark_of_cls (C + {#L#})) # M) = k"
          using get_level_get_rev_level_get_all_levels_of_marked[OF atm_L_notin_M,
            of "[Propagated L (mark_of_cls(C + {#L#}))]"] by simp
        have "atm_of L \<notin> atm_of ` (lits_of (rev M\<^sub>0))"
          using \<open>no_dup M'\<close> M' U S' by (auto simp: lits_of_def)
        hence "get_level L M' = k"
          using get_rev_level_notin_end[of L "rev M\<^sub>0" 0
            "rev M @ Propagated L (mark_of_cls (C + {#L#})) # []"]
          using tr_S get_lev_L M' U S' by (simp add:nm lits_of_def)
      ultimately have "get_maximum_level D' M' \<ge> k"
        by (metis get_maximum_level_ge_get_level get_rev_level_uminus)
      thus False
        using \<open>i < k\<close> unfolding \<open>get_maximum_level D' M' = i\<close> by auto
    qed
  have [simp]: "D = D'" using DD' by auto
  have "cdcl\<^sup>*\<^sup>* S U"
    using bj cdcl_bj.skip local.skip mono_rtranclp[of skip cdcl S U] other by meson
  hence "cdcl_all_inv_mes U"
    using inv rtranclp_cdcl_all_inv_mes_inv by blast
  hence "Propagated L (mark_of_cls (C + {#L#})) # M \<Turnstile>as CNot (D' + {#L'#})"
    using cdcl_all_inv_mes_def cdcl_conflicting_def U by auto
  hence "\<forall>L'\<in>#D. atm_of L' \<in> atm_of ` lits_of (Propagated L (mark_of_cls (C + {#L#})) # M)"
    by (metis CNot_plus CNot_singleton Un_insert_right \<open>D = D'\<close> true_annots_insert ball_msetI
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set  in_CNot_implies_uminus(2)
      sup_bot.comm_neutral)
  hence "get_maximum_level D M' = k"
     using tr_S nm U S'
       get_maximum_level_skip_un_marked_not_present[of D "
         Propagated L (mark_of_cls (C + {#L#})) # M" M\<^sub>0]
     unfolding  \<open>get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M) = k\<close>
     unfolding \<open>D = D'\<close>
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
  by induction (simp_all add: if_can_apply_backtrack_no_more_resolve)

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
  have "\<not>?RB S W" and "\<not>?SB S W"
    using bj by (fastforce simp: cdcl_bj.simps elim!: backtrackE skipE resolveE)+
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
            using  RS(1) cdcl_bj.resolve cdcl_o.bj  other skip
            mono_rtranclp[of " (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)" cdcl S T]
            by meson
          hence "cdcl_all_inv_mes U"
            by (meson RS(2) cdcl_all_inv_mes_inv cdcl_bj.resolve cdcl_o.bj other
              rtranclp_cdcl_all_inv_mes_inv step.prems)
          { fix U'
            assume "skip\<^sup>*\<^sup>* U U'" and "skip\<^sup>*\<^sup>* U' W"
            have "cdcl_all_inv_mes U'"
              by (smt \<open>cdcl_all_inv_mes U\<close> \<open>skip\<^sup>*\<^sup>* U U'\<close> cdcl_cw_ops.rtranclp_cdcl_all_inv_mes_inv
                cdcl_cw_ops_axioms cdcl_o.bj mono_rtranclp other skip)
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
              have f1: "\<forall>p pa pb pc. \<not> p (pa) pb \<or> \<not> p\<^sup>*\<^sup>* pb pc \<or> p\<^sup>*\<^sup>* pa pc"
                by (meson converse_rtranclp_into_rtranclp)
              have "skip_or_resolve T U \<and> no_step backtrack T"
                using RS(2) RS(3) by force
              hence "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* T W"
                using f1 \<open>(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U W\<close>
                by (smt RS(2))
              hence "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* S W"
                using RS(1) by force
              thus ?thesis
                using no_bt res by blast
            qed
        next
          case S
          { fix U'
            assume "skip\<^sup>*\<^sup>* S U'" and "skip\<^sup>*\<^sup>* U' W"
            hence "cdcl\<^sup>*\<^sup>* S U'"
              using mono_rtranclp[of skip cdcl S U'] by (simp add: cdcl_o.bj other skip)
            hence "cdcl_all_inv_mes U'"
              by (metis (no_types, hide_lams) \<open>cdcl_all_inv_mes S\<close> other
                rtranclp_cdcl_all_inv_mes_inv)
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
  have " cdcl\<^sup>*\<^sup>* S T"
    by (metis (no_types, hide_lams) bj mono_rtranclp[of cdcl_bj cdcl] other st)
  hence inv_T: "cdcl_all_inv_mes T"
    by (metis (no_types, hide_lams) inv rtranclp_cdcl_all_inv_mes_inv)

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
      consider
          (sk)  "skip T U'"
        | (bt)  "backtrack T U'"
        using T_U' by (meson cdcl_bj.cases local.skip resolve_skip_deterministic)
      thus ?thesis
        proof cases
          case sk
          thus ?thesis using \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> local.skip cdcl_bj.intros(1) skip_unique by blast
        next
          case bt
          have "skip\<^sup>+\<^sup>+ T U"
            using local.skip by blast
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
  using assms by (metis cdcl_bj_strongly_confluent converse_rtranclpE)

lemma full0_cdcl_bj_unique_normal_form:
  assumes "full0 cdcl_bj S T" and "full0 cdcl_bj S U" and
    inv: "cdcl_all_inv_mes S"
  shows "T = U"
  using cdcl_bj_unique_normal_form assms unfolding full0_def by blast

lemma
  assumes "cdcl_bj\<^sup>*\<^sup>* S T" and "full cdcl_bj S U" and
    inv: "cdcl_all_inv_mes S"
  shows "cdcl_bj\<^sup>*\<^sup>* T U"
  using assms by (metis cdcl_bj_strongly_confluent full_def tranclp_into_rtranclp)

subsection \<open>A better version of @{term cdcl_s}\<close>
inductive cdcl_s' :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
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

lemma cdcl_cp_decreasing_measure:
  assumes "cdcl_cp S T" and "cdcl_all_inv_mes S"
  shows "(\<lambda>S. card (atms_of_m (init_clss S)) - length (trail S) + (if conflicting S = C_True then 1 else 0)) S
        > (\<lambda>S. card (atms_of_m (init_clss S)) - length (trail S) + (if conflicting S = C_True then 1 else 0)) T"
  using assms
proof -
  have "length (trail T) \<le> card (atms_of_m (init_clss T))"
    by (rule length_model_le_vars_all_inv)
      (meson assms(1) assms(2) cdcl_all_inv_mes_inv cdcl_cp.cases conflict propagate)
  with assms
  show ?thesis by induction force+
qed

lemma cdcl_cp_wf: "wf {(b,a). cdcl_all_inv_mes a \<and> cdcl_cp a b}"
  apply (rule wf_wf_if_measure'[of less_than _ _
      "(\<lambda>S. card (atms_of_m (init_clss S)) - length (trail S)
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
  thus "?C S T" by induction auto
next
  assume
    "?C S T"
    "?inv S"
  thus "?I S T"
    proof induction
      case base
      thus ?case by simp
    next
      case (step T U) note st = this(1) and cp = this(2) and IH = this(3)[OF this(4)] and
        inv = this(4)
      have "cdcl\<^sup>*\<^sup>* S T"
        by (metis rtranclp_unfold local.step(1) tranclp_cdcl_cp_tranclp_cdcl)
      hence "cdcl_all_inv_mes T"
        by (metis (no_types, lifting) \<open>cdcl_all_inv_mes S\<close> rtranclp_cdcl_all_inv_mes_inv)
      hence " (\<lambda>a b. cdcl_all_inv_mes a \<and> cdcl_cp a b)\<^sup>*\<^sup>* T U"
        using cp by auto
      thus ?case using IH by auto
    qed
qed

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
  shows "full0 cdcl_cp T' U
    \<or> (\<exists>U' U''. full0 cdcl_cp T' U'' \<and> full cdcl_bj U U' \<and> full0 cdcl_cp U' U'' \<and> cdcl_s'\<^sup>*\<^sup>* U U'')"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl_o.bj local.bj mono_rtranclp[of cdcl_bj cdcl T T''] other st
      rtranclp.rtrancl_into_rtrancl)
  hence inv_T'': "cdcl_all_inv_mes T''"
    using inv rtranclp_cdcl_all_inv_mes_inv by blast
  have "cdcl_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full cdcl_bj T T''"
    by (metis \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> full_def step.prems(3))
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
  obtain U'' where "full0 cdcl_cp T'' U''"
    using cdcl_cp_normalized_element inv_T'' by blast
  moreover hence "cdcl_s\<^sup>*\<^sup>* U U''"
    by (metis \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl_bj_full_cdclp_cdcl_s rtranclp_unfold)
  moreover have "cdcl_s'\<^sup>*\<^sup>* U U''"
    proof -
      obtain ss :: "'st \<Rightarrow> 'st" where
        f1: "\<forall>x2. (\<exists>v3. cdcl_cp x2 v3) = cdcl_cp x2 (ss x2)"
        by moura
      have "\<not> cdcl_cp U (ss U)"
        by (meson full full0_def)
      then show ?thesis
        using f1 by (metis (no_types) \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>\<down> T T''\<close> bj' calculation(1) r_into_rtranclp)
    qed
  ultimately show ?case
    using \<open>full cdcl_bj T T''\<close> \<open>full0 cdcl_cp T'' U''\<close> unfolding \<open>T = U\<close> by blast
qed

lemma cdcl_cp_cdcl_bj_bissimulation':
  assumes
    "full0 cdcl_cp T U" and
    "cdcl_bj\<^sup>*\<^sup>* T T'" and
    "cdcl_all_inv_mes T" and
    "no_step cdcl_bj T'"
  shows "full0 cdcl_cp T' U
    \<or> (\<exists>U'. full cdcl_bj U U' \<and> (\<forall>U''. full0 cdcl_cp U' U'' \<longrightarrow> full0 cdcl_cp T' U''
      \<and> cdcl_s'\<^sup>*\<^sup>* U U''))"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl_o.bj local.bj mono_rtranclp[of cdcl_bj cdcl T T''] other st
      rtranclp.rtrancl_into_rtrancl)
  hence inv_T'': "cdcl_all_inv_mes T''"
    using inv rtranclp_cdcl_all_inv_mes_inv by blast
  have "cdcl_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full cdcl_bj T T''"
    by (metis \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> full_def step.prems(3))
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
  { fix U''
    assume "full0 cdcl_cp T'' U''"
    moreover hence "cdcl_s\<^sup>*\<^sup>* U U''"
      by (metis \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl_bj_full_cdclp_cdcl_s rtranclp_unfold)
    moreover have "cdcl_s'\<^sup>*\<^sup>* U U''"
      proof -
        obtain ss :: "'st \<Rightarrow> 'st" where
          f1: "\<forall>x2. (\<exists>v3. cdcl_cp x2 v3) = cdcl_cp x2 (ss x2)"
          by moura
        have "\<not> cdcl_cp U (ss U)"
          by (meson assms(1) full0_def)
        then show ?thesis
          using f1 by (metis (no_types) \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>\<down> T T''\<close> bj' calculation(1) r_into_rtranclp)
      qed
    ultimately have "full cdcl_bj U T''" and " cdcl_s'\<^sup>*\<^sup>* T'' U''"
      using \<open>full cdcl_bj T T''\<close> \<open>full0 cdcl_cp T'' U''\<close> unfolding \<open>T = U\<close>
        apply blast
      by (metis \<open>cdcl_cp\<^sup>\<down> T'' U''\<close> cdcl_s'.simps full0_unfold rtranclp.simps)
    }
  then show ?case
    using \<open>full cdcl_bj T T''\<close> full bj' unfolding \<open>T = U\<close> full0_def by (metis r_into_rtranclp)
qed

lemma
  assumes
    "cdcl_bj S T" and
    "full0 cdcl_cp T U"
  shows
    "(T = U \<and> (\<exists>U'. full cdcl_bj S U' \<and> full0 cdcl_bj U U'))
    \<or> cdcl_s' S U"
    using assms
proof induction
  case (skip S T)
  obtain U' where "full0 cdcl_bj T U'"
    using wf_exists_normal_form_full0[OF cdcl_bj_wf] by blast
  moreover hence "full cdcl_bj S U'"
    proof -
      have f1: "cdcl_bj\<^sup>*\<^sup>* T U' \<and> no_step cdcl_bj U'"
        by (metis (no_types) calculation full0_def)
      have "cdcl_bj S T"
        by (simp add: cdcl_bj.skip skip.hyps)
      then show ?thesis
        using f1 by (simp add: full_def rtranclp_into_tranclp2)
  qed
  moreover
    have "no_step cdcl_cp T"
      using skip(1) by (fastforce simp:cdcl_cp.simps)
    hence "T = U"
      using skip(2) unfolding full0_def rtranclp_unfold by (auto dest: tranclpD)
  ultimately show ?case by blast
next
  case (resolve S T)
  obtain U' where "full0 cdcl_bj T U'"
    using wf_exists_normal_form_full0[OF cdcl_bj_wf] by blast
  moreover hence "full cdcl_bj S U'"
    proof -
      have f1: "cdcl_bj\<^sup>*\<^sup>* T U' \<and> no_step cdcl_bj U'"
        by (metis (no_types) calculation full0_def)
      have "cdcl_bj S T"
        by (simp add: cdcl_bj.resolve resolve.hyps)
      then show ?thesis
        using f1 by (simp add: full_def rtranclp_into_tranclp2)
    qed
  moreover
    have "no_step cdcl_cp T"
      using resolve(1) by (fastforce simp:cdcl_cp.simps)
    hence "T = U"
      using resolve(2) unfolding full0_def rtranclp_unfold by (auto dest: tranclpD)
  ultimately show ?case by blast
next
  case (backtrack S T) note bt = this(1)
  hence "no_step cdcl_bj T"
    by (fastforce simp: cdcl_bj.simps)
  moreover have "cdcl_bj\<^sup>+\<^sup>+ S T"
    using bt by (simp add: cdcl_bj.backtrack tranclp.r_into_trancl)
  ultimately have "full cdcl_bj S T"
    unfolding full0_def full_def by simp
  moreover have "no_step cdcl_cp S"
    using backtrack(1) by (fastforce simp: cdcl_cp.simps)
  ultimately show ?case using backtrack(2) cdcl_s'.bj' by blast
qed

lemma cdcl_s_cdcl_s'_connected:
  assumes "cdcl_s S U" and "cdcl_all_inv_mes S"
  shows "cdcl_s' S U
    \<or> (\<exists>U'. full cdcl_bj U U' \<and> (\<forall>U''. full0 cdcl_cp U' U'' \<longrightarrow> cdcl_s' S U'' ))"
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
      case decided
      thus ?thesis using cdcl_s'.simps full n_s by blast
    next
      case bj
      have inv_T: "cdcl_all_inv_mes T"
        using cdcl_all_inv_mes_inv o other other'.prems by blast
      consider
          (cp) "full0 cdcl_cp T U" and "no_step cdcl_bj T"
        | (fbj) T' where "full cdcl_bj T T'"
        apply (cases "no_step cdcl_bj T")
         using full apply blast
        using wf_exists_normal_form_full0[OF cdcl_bj_wf, of T] by (metis full0_unfold)
      thus ?thesis
        proof cases
          case cp
          thus ?thesis
            proof -
              obtain ss :: "'st \<Rightarrow> 'st" where
                f1: "\<forall>s sa sb. (\<not> full cdcl_bj s sa \<or> cdcl_cp s (ss s) \<or> \<not> full0 cdcl_cp sa sb)
                  \<or> cdcl_s' s sb"
                using bj' by moura
              have "full cdcl_bj S T"
                by (simp add: cp(2) full_def local.bj tranclp.r_into_trancl)
              then show ?thesis
                using f1 full n_s by blast
            qed
        next
          case (fbj U')
          hence "full cdcl_bj S U'"
            using bj unfolding full_def by auto
          moreover have "no_step cdcl_cp S"
            using n_s by blast
          moreover have "T = U"
            using full fbj unfolding full_def full0_def rtranclp_unfold
            by (force dest!: tranclpD simp:cdcl_bj.simps)
          ultimately show ?thesis using cdcl_s'.bj'[of S U'] using fbj by blast
        qed
    qed
qed

lemma cdcl_s_cdcl_s'_connected':
  assumes "cdcl_s S U" and "cdcl_all_inv_mes S"
  shows "cdcl_s' S U
    \<or> (\<exists>U' U''. cdcl_s' S U'' \<and> full cdcl_bj U U' \<and> full0 cdcl_cp U' U'')"
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
      case decided
      thus ?thesis using cdcl_s'.simps full n_s by blast
    next
      case bj
      obtain T' where T': "full0 cdcl_bj T T'"
        using wf_exists_normal_form cdcl_bj_wf unfolding full0_def by metis
      hence "full0 cdcl_bj S T'"
        proof -
          have f1: "cdcl_bj\<^sup>*\<^sup>* T T' \<and> no_step cdcl_bj T'"
            by (metis (no_types) T' full0_def)
          then have "cdcl_bj\<^sup>*\<^sup>* S T'"
            by (meson converse_rtranclp_into_rtranclp local.bj)
          then show ?thesis
            using f1 by (simp add: full0_def)
        qed
      have "cdcl_bj\<^sup>*\<^sup>* T T'"
        using T' unfolding full0_def by simp
      have "cdcl_all_inv_mes T"
        using cdcl_all_inv_mes_inv o other other'.prems by blast
      then consider
          (T'U) "full0 cdcl_cp T' U"
        | (U) U' U'' where
            "full0 cdcl_cp T' U''" and
            "full cdcl_bj U U'" and
            "full0 cdcl_cp U' U''" and
            "cdcl_s'\<^sup>*\<^sup>* U U''"
        using cdcl_cp_cdcl_bj_bissimulation[OF full \<open>cdcl_bj\<^sup>*\<^sup>* T T'\<close>] T' unfolding full0_def
        by blast
      then show ?thesis
        (* a sledgehammer one-liner:
         by (metis \<open>cdcl_bj\<^sup>\<down> S T'\<close> bj' full0_unfold local.bj n_s)*)
        proof cases
          case T'U
          thus ?thesis
            by (metis \<open>cdcl_bj\<^sup>\<down> S T'\<close> cdcl_s'.simps full0_unfold local.bj n_s)
        next
          case (U U' U'')
          have "cdcl_s' S U''"
            by (metis U(1) \<open>cdcl_bj\<^sup>\<down> S T'\<close> cdcl_s'.simps full0_unfold local.bj n_s)
          thus ?thesis using U(2,3) by blast
        qed
    qed
qed

lemma cdcl_s_cdcl_s'_no_step:
  assumes "cdcl_s S U" and "cdcl_all_inv_mes S" and "no_step cdcl_bj U"
  shows "cdcl_s' S U"
  using cdcl_s_cdcl_s'_connected[OF assms(1,2)] assms(3)
  by (metis (no_types, lifting) full_def tranclpD)

lemma cdcl_o_rule_cases[case_names other decided backtrack skip resolve]:
  assumes
    "cdcl_o S T" and
    "decided S T \<Longrightarrow> P" and
    "backtrack S T \<Longrightarrow> P" and
    "skip S T \<Longrightarrow> P" and
    "resolve S T \<Longrightarrow> P"
  shows P
  using assms by (auto simp: cdcl_o.simps cdcl_bj.simps)

lemma backtrack_is_full_cdcl_bj:
  assumes bt: "backtrack S T"
  shows "full cdcl_bj S T"
proof -
  have "no_step cdcl_bj T"
    using bt by (fastforce simp: cdcl_bj.simps)
  moreover have "cdcl_bj\<^sup>+\<^sup>+ S T"
    using bt by auto
  ultimately show ?thesis unfolding full_def by blast
qed

lemma rtranclp_cdcl_s_connected_to_rtranclp_cdcl_s':
  assumes "cdcl_s\<^sup>*\<^sup>* S U"
  shows "cdcl_s'\<^sup>*\<^sup>* S U \<or> (\<exists>T. cdcl_s'\<^sup>*\<^sup>* S T \<and> cdcl_bj\<^sup>+\<^sup>+ T U \<and> conflicting U \<noteq> C_True)"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step T V) note st = this(1) and o = this(2) and IH = this(3)
  from o show ?case
    proof cases
      case conflict'
      then have f2: "cdcl_s' T V"
        using cdcl_s'.conflict' by blast
      obtain ss :: 'st where
        f3: "S = T \<or> cdcl_s\<^sup>*\<^sup>* S ss \<and> cdcl_s ss T"
        by (metis (full_types) rtranclp.simps st)
      obtain ssa :: 'st where
        "cdcl_cp T ssa"
        using conflict' by (metis (no_types) full_def tranclpD)
      then have "S = T"
        using f3 by (metis (no_types) cdcl_s.simps full0_def full_def)
      then show ?thesis
        using f2 by blast
    next
      case (other' U) note o = this(1) and n_s = this(2) and full = this(3)
      thus ?thesis
        proof (cases rule: cdcl_o_rule_cases[OF o])
          case 1
          hence "cdcl_s'\<^sup>*\<^sup>* S T"
            using IH by auto
          thus ?thesis
            by (meson "1" decided' full n_s rtranclp.rtrancl_into_rtrancl)
        next
          case 2
          consider
              (s') "cdcl_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          thus ?thesis
            proof cases
              case s'
              moreover
                have "full cdcl_bj T U"
                   using backtrack_is_full_cdcl_bj 2 by blast
                hence "cdcl_s' T V"
                  using full bj' n_s by blast
              ultimately show ?thesis by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "no_step cdcl_cp S'"
                using bj_T by (fastforce simp: cdcl_cp.simps cdcl_bj.simps dest!: tranclpD)
              moreover
                have "full cdcl_bj T U"
                  using backtrack_is_full_cdcl_bj 2 by blast
                hence "full cdcl_bj S' U"
                  using bj_T unfolding full_def by fastforce
              ultimately have "cdcl_s' S' V" using full by (simp add: bj')
              thus ?thesis using S_S' by auto
            qed
        next
          case 3
          hence [simp]: "U = V"
            using full converse_rtranclpE unfolding full0_def by fastforce

          consider
              (s') "cdcl_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          thus ?thesis
            proof cases
              case s'
              have "cdcl_bj\<^sup>+\<^sup>+ T V"
                using 3  by fastforce
              moreover have "conflicting V \<noteq> C_True"
                using 3 by auto
              ultimately show ?thesis using s' by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl_bj\<^sup>+\<^sup>+ S' V"
                using 3  bj_T by (metis \<open>U = V\<close> skip tranclp.simps)

              moreover have "conflicting V \<noteq> C_True"
                using 3 by auto
              ultimately show ?thesis using S_S' by auto
            qed
        next
          case 4
          hence [simp]: "U = V"
            using full converse_rtranclpE unfolding full0_def by fastforce

          consider
              (s') "cdcl_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          thus ?thesis
            proof cases
              case s'
              have "cdcl_bj\<^sup>+\<^sup>+ T V"
                using 4  by fastforce
              moreover have "conflicting V \<noteq> C_True"
                using 4 by auto
              ultimately show ?thesis using s' by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl_bj\<^sup>+\<^sup>+ S' V"
                using 4  bj_T by (metis \<open>U = V\<close> resolve tranclp.simps)
              moreover have "conflicting V \<noteq> C_True"
                using 4 by auto
              ultimately show ?thesis using S_S' by auto
            qed
        qed
    qed
qed

lemma n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o:
  assumes inv: "cdcl_all_inv_mes S"
  shows "no_step cdcl_s' S \<longleftrightarrow> no_step cdcl_cp S \<and> no_step cdcl_o S" (is "?S' S \<longleftrightarrow> ?C S \<and> ?O S")
proof
  assume "?C S \<and> ?O S"
  thus "?S' S"
    by (metis bj cdcl_s'.cases decided full_def tranclpD)
next
  assume n_s: "?S' S"
  have "?C S"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain S' where "cdcl_cp S S'"
        by auto
      then obtain T where "full cdcl_cp S T"
        using cdcl_cp_normalized_element inv by (metis (no_types, lifting) full0_unfold)
      thus False using n_s cdcl_s'.conflict' by blast
    qed
  moreover have "?O S"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain S' where "cdcl_o S S'"
        by auto
      then obtain T where "full cdcl_cp S' T"
        using cdcl_cp_normalized_element inv
        by (meson cdcl_all_inv_mes_def cdcl_s_cdcl_s'_connected' cdcl_then_exists_cdcl_s_step n_s)
      thus False using n_s by (meson \<open>cdcl_o S S'\<close> cdcl_all_inv_mes_def cdcl_s_cdcl_s'_connected'
        cdcl_then_exists_cdcl_s_step inv)
    qed
  ultimately show "?C S \<and> ?O S" by auto
qed


lemma cdcl_s'_tranclp_cdcl:
   "cdcl_s' S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
  apply (induct rule: cdcl_s'.induct)
    apply (simp add: full_def tranclp_cdcl_cp_tranclp_cdcl)
   using cdcl_s.simps cdcl_s_tranclp_cdcl apply blast
proof -
  fix Sa :: 'st and S'a :: 'st and S'' :: 'st
  assume a1: "cdcl_cp\<^sup>\<down> S'a S''"
  assume a2: "cdcl_bj\<^sup>+\<^sup>\<down> Sa S'a"
  obtain ss :: "'st \<Rightarrow> 'st \<Rightarrow> ('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st" where
    "\<forall>x0 x1 x2. (\<exists>v3. x2 x1 v3 \<and> x2\<^sup>*\<^sup>* v3 x0) = (x2 x1 (ss x0 x1 x2) \<and> x2\<^sup>*\<^sup>* (ss x0 x1 x2) x0)"
    by moura
  then have f3: "\<forall>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ss sa s p) \<and> p\<^sup>*\<^sup>* (ss sa s p) sa"
    by (metis (full_types) tranclpD)
  have "cdcl_bj\<^sup>+\<^sup>+ Sa S'a \<and> no_step cdcl_bj S'a"
    using a2 by (simp add: full_def)
  then have "cdcl_bj Sa (ss S'a Sa cdcl_bj) \<and> cdcl_bj\<^sup>*\<^sup>* (ss S'a Sa cdcl_bj) S'a"
    using f3 by auto
  then show "cdcl\<^sup>+\<^sup>+ Sa S''"
    using a1 by (meson bj other rtranclp_cdcl_bj_full_cdclp_cdcl_s rtranclp_cdcl_s_rtranclp_cdcl
      rtranclp_into_tranclp2)
qed


lemma tranclp_cdcl_s'_tranclp_cdcl:
   "cdcl_s'\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
   using cdcl_s'_tranclp_cdcl apply blast
   by (meson cdcl_s'_tranclp_cdcl tranclp_trans)

lemma rtranclp_cdcl_s'_rtranclp_cdcl:
   "cdcl_s'\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl_s' S S'] tranclp_cdcl_s'_tranclp_cdcl[of S S'] by auto

lemma full0_cdcl_s_iff_full0_cdcl_s':
  assumes inv: "cdcl_all_inv_mes S"
  shows "full0 cdcl_s S T \<longleftrightarrow> full0 cdcl_s' S T" (is "?S \<longleftrightarrow> ?S'")
proof
  assume ?S'
  hence "cdcl\<^sup>*\<^sup>* S T"
    using rtranclp_cdcl_s'_rtranclp_cdcl[of S T] unfolding full0_def by blast
  hence inv': "cdcl_all_inv_mes T"
    using rtranclp_cdcl_all_inv_mes_inv inv by blast
  have "cdcl_s\<^sup>*\<^sup>* S T"
    using \<open>?S'\<close> unfolding full0_def
      by (smt cdcl_s'_is_rtranclp_cdcl_s mono_rtranclp rtranclp_idemp)
  thus ?S
    using \<open>?S'\<close> inv' cdcl_s_cdcl_s'_connected' unfolding full0_def by blast
next
  assume ?S
  hence inv_T:"cdcl_all_inv_mes T"
    by (metis assms full0_def rtranclp_cdcl_all_inv_mes_inv rtranclp_cdcl_s_rtranclp_cdcl)

  consider
      (s')  "cdcl_s'\<^sup>*\<^sup>* S T"
    | (st) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
    using rtranclp_cdcl_s_connected_to_rtranclp_cdcl_s'[of S T] using \<open>?S\<close> unfolding full0_def
    by blast
  thus ?S'
    proof cases
      case s'
      thus ?thesis
        by (metis \<open>cdcl_s\<^sup>\<down> S T\<close> inv_T cdcl_all_inv_mes_def cdcl_s'.simps cdcl_s.conflict'
          cdcl_then_exists_cdcl_s_step full0_def n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o)
    next
      case (st S')
      have "full0 cdcl_cp T T"
        using conflicting_clause_full0_cdcl_cp st(3) by blast
      moreover
        have n_s: "no_step cdcl_bj T"
          by (metis \<open>cdcl_s\<^sup>\<down> S T\<close> bj inv_T cdcl_all_inv_mes_def cdcl_then_exists_cdcl_s_step
            full0_def)
        hence "full cdcl_bj S' T"
          using st(2) unfolding full_def by blast
      moreover have "no_step cdcl_cp S'"
        using st(2) by (fastforce dest!: tranclpD simp: cdcl_cp.simps cdcl_bj.simps)
      ultimately have "cdcl_s' S' T"
        using cdcl_s'.bj'[of S' T T] by blast
      hence "cdcl_s'\<^sup>*\<^sup>* S T"
        using st(1) by auto
      moreover have "no_step cdcl_s' T"
        using inv_T by (metis \<open>cdcl_cp\<^sup>\<down> T T\<close> \<open>cdcl_s\<^sup>\<down> S T\<close> cdcl_all_inv_mes_def
          cdcl_then_exists_cdcl_s_step full0_def n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o)
      ultimately show ?thesis
        unfolding full0_def by blast
    qed
qed

lemma conflicting_not_model_can_do_conflict_or_decide:
  assumes
    confl:"conflicting S = C_True" and
    tr: " \<not> trail S \<Turnstile>as init_clss S" and
    inv: "cdcl_all_inv_mes S"
  shows "\<exists>T. conflict S T \<or> decided S T"
proof -
  obtain M N U k where S: "state S = (M, N, U, k, C_True)" using confl by auto
  obtain C where "\<not>M \<Turnstile>a C" and "C \<in> N"
    using tr S unfolding true_annots_def  clauses_def by auto
  then consider
      (conf) "M \<Turnstile>as CNot C"
    | (dec) y where "y \<in> atms_of C" and "y \<notin> atm_of ` lits_of M"
    using all_variables_defined_not_imply_cnot by force
  thus ?thesis
    proof cases
      case conf
      thus ?thesis using conflict_rule[OF S] \<open>C \<in> N\<close> S unfolding clauses_def by auto
    next
      case (dec L)
      have "atm_of (Pos L) \<in> atms_of_m (init_clss S)"
        using dec  \<open>C \<in> N\<close> S unfolding atms_of_m_def by (fastforce simp add: S atms_of_def)
      moreover have "undefined_lit (Pos L) M"
        using dec by (metis Marked_Propagated_in_iff_in_lits_of literal.sel(1)
          atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
      ultimately show ?thesis using deciding[OF S] S by force
    qed
qed

lemma conflict_step_cdcl_s_step:
  assumes
    "conflict S T"
    "cdcl_all_inv_mes S"
  shows "\<exists>T. cdcl_s S T"
proof -
  obtain U where "full0 cdcl_cp S U"
    using cdcl_cp_normalized_element assms by blast
  then have "full cdcl_cp S U"
    by (metis cdcl_cp.conflict' assms(1) full0_unfold)
  thus ?thesis using cdcl_s.conflict' by blast
qed

lemma decided_step_cdcl_s_step:
  assumes
    "decided S T"
    "cdcl_all_inv_mes S"
  shows "\<exists>T. cdcl_s S T"
proof -
  obtain U where "full0 cdcl_cp T U"
    using cdcl_cp_normalized_element by (meson assms(1) assms(2) cdcl_all_inv_mes_inv
      cdcl_cp_normalized_element decided other)
  thus ?thesis
    by (metis assms cdcl_cp_normalized_element cdcl_s.conflict' decided full0_unfold other')
qed

lemma rtranclp_cdcl_cp_conflicting_C_Clause:
  "cdcl_cp\<^sup>*\<^sup>* S T \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> S = T"
  using rtranclpD tranclpD by fastforce

subsection \<open>cdcl FW\<close>
inductive cdcl_fw :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
fw_propagate: "propagate S S' \<Longrightarrow> cdcl_fw S S'" |
fw_conflict: "conflict S T \<Longrightarrow> full0 cdcl_bj T U \<Longrightarrow> cdcl_fw S U" |
fw_decided: "decided S S' \<Longrightarrow> cdcl_fw S S'"|
fw_rf: "cdcl_rf S S' \<Longrightarrow> cdcl_fw S S'"

lemma cdcl_fw_cdcl:
  assumes "cdcl_fw S T"
  shows "cdcl\<^sup>*\<^sup>* S T"
  using assms
proof induction
  case (fw_conflict S T U) note confl = this(1) and bj = this(2)
  have "cdcl S T" using confl by (simp add: cdcl.intros r_into_rtranclp)
  moreover
    have "cdcl_bj\<^sup>*\<^sup>* T U" using bj unfolding full0_def by auto
    hence "cdcl\<^sup>*\<^sup>* T U" by (metis cdcl_o.bj mono_rtranclp other)
  ultimately show ?case by auto
qed (simp_all add: cdcl_o.intros cdcl.intros r_into_rtranclp)


lemma cdcl_fw_conflicting_true_or_no_step:
  assumes "cdcl_fw S T"
  shows "conflicting T = C_True \<or> no_step cdcl T"
  using assms
proof induction
  case (fw_conflict S T U) note confl = this(1) and n_s = this(2)
  { fix D V
    assume "cdcl U V" and "conflicting U = C_Clause D"
    then have False
      using n_s unfolding full0_def
      by (induction rule: cdcl_all_rules_induct) (auto dest!: cdcl_bj.intros )
  }
  thus ?case by (cases "conflicting U") fastforce+
qed (auto simp add: cdcl_rf.simps)

inductive cdcl_cbj where
cbj_conflict[intro]: "conflict S T \<Longrightarrow> cdcl_cbj S T" |
cbj_bj[intro]: "cdcl_bj S T \<Longrightarrow> cdcl_cbj S T"

lemma rtrancl_cdcl_conflicting_true_cdcl_fw:
  assumes "cdcl\<^sup>*\<^sup>* S V" and "conflicting S = C_True"
  shows "(cdcl_fw\<^sup>*\<^sup>* S V \<and> conflicting V = C_True)
    \<or> (\<exists>T U. cdcl_fw\<^sup>*\<^sup>* S T \<and> conflicting V \<noteq> C_True \<and> conflict T U \<and> cdcl_bj\<^sup>*\<^sup>* U V)"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step U V) note st = this(1) and cdcl = this(2) and IH = this(3) and confl[simp] = this(4)
  from cdcl
  show ?case
    proof (cases)
      case propagate
      moreover hence "conflicting U = C_True"
        by auto
      moreover have "conflicting V = C_True"
        using propagate by auto
      ultimately show ?thesis using IH cdcl_fw.fw_propagate[of U V] by auto
    next
      case conflict
      moreover hence "conflicting U = C_True"
        by auto
      moreover have "conflicting V \<noteq> C_True"
        using conflict by auto
      ultimately show ?thesis using IH by auto
    next
      case other
      thus ?thesis
        proof cases
          case decided
          moreover hence "conflicting U = C_True"
            by auto
          ultimately show ?thesis using IH cdcl_fw.fw_decided[of U V] by auto
        next
          case bj
          moreover {
            assume "skip_or_resolve U V"
            have f1: "cdcl_cbj\<^sup>+\<^sup>+ U V"
              by (simp add: cbj_bj local.bj tranclp.r_into_trancl) (* 5 ms *)
            obtain T T' :: 'st where
              f2: "cdcl_fw\<^sup>*\<^sup>* S U \<or> cdcl_fw\<^sup>*\<^sup>* S T \<and> conflicting U \<noteq> C_True \<and> conflict T T'
                \<and> cdcl_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
            have f0: "\<forall>s sa. \<not> resolve s sa \<or> (\<exists>l m ms ma. sa = update_conflicting
              (C_Clause (remdups_mset (ma + m))) (update_trail ms s)
              \<and> trail s = Propagated l (mark_of_cls (m + {#l#})) # ms
              \<and> backtrack_lvl s = get_maximum_level ma (Propagated l (mark_of_cls (m + {#l#})) # ms)
              \<and> conflicting s = C_Clause (ma + {#- l#}))"
              by blast
            then have ?thesis
              proof -
                obtain Ms :: "('v, nat, 'mark) marked_lit list" and C :: "'v literal multiset" and
                  ll :: "'v literal" and m :: 'mark where
                  "\<not> skip U V
                    \<or> (\<exists>vr60 vr69 vr62 vr61. update_trail vr62 U = V
                        \<and> 0 = count vr61 (- vr60) \<and> {#} \<noteq> vr61
                        \<and> trail U = Propagated vr60 vr69 # vr62 \<and> C_Clause vr61 = conflicting U)
                      \<longrightarrow> \<not> skip U V
                    \<or> V = update_trail Ms U
                      \<and> 0 = count C (- ll)
                      \<and> C \<noteq> {#}
                      \<and> trail U = Propagated ll m # Ms \<and> conflicting U = C_Clause C"
                  by metis
                then have f3: "(\<exists>s sa. skip s sa
                  \<and> (\<forall>l m ms ma. update_trail ms s \<noteq> sa \<or> 0 \<noteq> count ma (- l) \<or> {#} = ma
                       \<or> Propagated l m # ms \<noteq> trail s \<or> C_Clause ma \<noteq> conflicting s))
                     \<or> \<not> skip U V
                     \<or> V = update_trail Ms U \<and> 0 = count C (- ll) \<and> C \<noteq> {#}
                        \<and> trail U = Propagated ll m # Ms \<and> conflicting U = C_Clause C"
                  by (metis (no_types))
                have f5: "(C = {#} \<or> trail U \<noteq> Propagated ll m # Ms
                  \<or> conflicting U \<noteq> C_Clause C)
                  \<or> trail U = Propagated ll m # Ms \<and> conflicting U = C_Clause C"
                  by meson
                have f6: "(trail U \<noteq> Propagated ll m # Ms \<or> conflicting U \<noteq> C_Clause C)
                  \<or> conflicting U = C_Clause C"
                  by blast
                obtain ss :: 'st where
                  "cdcl_fw\<^sup>*\<^sup>* S U \<longrightarrow> S = U \<or> cdcl_fw\<^sup>*\<^sup>* S ss \<and> cdcl_fw ss U"
                  by (metis (full_types) rtranclp.simps)
                then have "\<not> cdcl_fw\<^sup>*\<^sup>* S U"
                  using f6 f5 conflicting_clause.simps(3) f3 f0 by (metis \<open>skip_or_resolve U V\<close>
                    cdcl_fw_conflicting_true_or_no_step conflicting_clause.simps(3) local.step(2)
                    skipE step.prems)
                then show ?thesis
                  using f6 f5 conflicting_clause.simps(3) f3 f0 f2 by (metis (no_types)
                    \<open>skip_or_resolve U V\<close> conflicting_clause.simps(3) conflicting_update_conflicting
                    conflicting_update_trail local.bj rtranclp.simps skipE)
              qed
          }
          moreover {
            assume "backtrack U V"
            hence "conflicting U \<noteq> C_True" by auto
            then obtain T T' where
              "cdcl_fw\<^sup>*\<^sup>* S T" and
              "conflicting U \<noteq> C_True" and
              "conflict T T'" and
              "cdcl_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
            have "conflicting V = C_True"
              using \<open>backtrack U V\<close> by auto
            have "full0 cdcl_bj T' V"
              apply (rule rtranclp_full0I[of cdcl_bj T' U V])
                using \<open>cdcl_bj\<^sup>*\<^sup>* T' U\<close> apply fast
              using \<open>backtrack U V\<close> backtrack_is_full_cdcl_bj unfolding full_def full0_def by blast
            then have ?thesis
              using cdcl_fw.fw_conflict[of T T' V] \<open>conflict T T'\<close> \<open>cdcl_fw\<^sup>*\<^sup>* S T\<close>
              \<open>conflicting V = C_True\<close> by auto
          }
          ultimately show ?thesis by (auto simp: cdcl_bj.simps)
      qed
    next
      case rf
      moreover hence "conflicting U = C_True" and "conflicting V = C_True"
        by (auto simp: cdcl_rf.simps)
      ultimately show ?thesis using IH cdcl_fw.fw_rf[of U V] by auto
    qed
qed

lemma no_step_cdcl_no_step_cdcl_fw: "no_step cdcl S \<Longrightarrow> no_step cdcl_fw S"
  by (auto simp: cdcl.simps cdcl_fw.simps cdcl_o.simps cdcl_bj.simps)

lemma no_step_cdcl_fw_no_step_cdcl:
  "conflicting S = C_True \<Longrightarrow> no_step cdcl_fw S \<Longrightarrow> no_step cdcl S"
  unfolding cdcl.simps cdcl_fw.simps cdcl_o.simps cdcl_bj.simps
  using wf_exists_normal_form_full0[OF cdcl_bj_wf] by force

lemma rtranclp_cdcl_fw_no_step_cdcl_bj:
  assumes
    "cdcl_fw\<^sup>*\<^sup>* S T" and
    "conflicting S = C_True"
  shows "no_step cdcl_bj T"
  using assms
  by (induction rule: rtranclp_induct)
     (fastforce simp: cdcl_bj.simps cdcl_rf.simps cdcl_fw.simps full0_def)+

text \<open>If @{term "conflicting  S \<noteq> C_True"}, we cannot say anything.\<close>
lemma conflicting_true_full0_cdcl_iff_full0_cdcl_fw:
  assumes confl: "conflicting  S = C_True"
  shows "full0 cdcl S V \<longleftrightarrow> full0 cdcl_fw S V"
proof
  assume full: "full0 cdcl_fw S V"
  hence st: "cdcl\<^sup>*\<^sup>* S V"
    using rtranclp_mono[of cdcl_fw "cdcl\<^sup>*\<^sup>*"] cdcl_fw_cdcl unfolding full0_def by auto

  have n_s: "no_step cdcl_fw V"
    using full unfolding full0_def by auto
  have n_s_bj: "no_step cdcl_bj V"
    using rtranclp_cdcl_fw_no_step_cdcl_bj confl full unfolding full0_def by auto

  have "\<And>S'. conflict V S' \<Longrightarrow> False"
    using n_s n_s_bj wf_exists_normal_form_full0[OF cdcl_bj_wf] cdcl_fw.simps by meson
  hence n_s_cdcl: "no_step cdcl V"
    using n_s n_s_bj by (auto simp: cdcl.simps cdcl_o.simps cdcl_fw.simps)
  then show "full0 cdcl S V" using st unfolding full0_def by auto
next
  assume full: "full0 cdcl S V"
  have "no_step cdcl_fw V"
    using full no_step_cdcl_no_step_cdcl_fw unfolding full0_def by blast
  moreover
    consider
        (fw) "cdcl_fw\<^sup>*\<^sup>* S V" and "conflicting V = C_True"
      | (bj) T U where
        "cdcl_fw\<^sup>*\<^sup>* S T" and
        "conflicting V \<noteq> C_True" and
        "conflict T U" and
        "cdcl_bj\<^sup>*\<^sup>* U V"
      using full rtrancl_cdcl_conflicting_true_cdcl_fw confl unfolding full0_def by blast
    then have "cdcl_fw\<^sup>*\<^sup>* S V"
      proof cases
        case fw
        thus ?thesis by fast
      next
        case (bj T U)
        have "no_step cdcl_bj V"
          by (meson cdcl_o.bj full full0_def other)
        hence "full0 cdcl_bj U V"
          using \<open> cdcl_bj\<^sup>*\<^sup>* U V\<close> unfolding full0_def by auto
        hence "cdcl_fw T V" using \<open>conflict T U\<close> cdcl_fw.fw_conflict by blast
        thus ?thesis using \<open>cdcl_fw\<^sup>*\<^sup>* S T\<close> by auto
      qed
  ultimately show "full0 cdcl_fw S V" unfolding full0_def by fast
qed

lemma init_state_true_full0_cdcl_iff_full0_cdcl_fw:
  assumes fin[simp]: "finite N"
  shows "full0 cdcl (init_state N) V \<longleftrightarrow> full0 cdcl_fw (init_state N) V"
  by (rule conflicting_true_full0_cdcl_iff_full0_cdcl_fw) simp

end
end
