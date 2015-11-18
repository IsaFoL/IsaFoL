theory CDCL_CW_NOT
imports CDCL_CW_Termination CDCL_NOT
begin
sledgehammer_params[verbose]

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
    by (metis (no_types, hide_lams) cdcl_o.skip inv mono_rtranclp other 
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

inductive cdcl_s_sr where
"full cdcl_cp S T \<Longrightarrow> cdcl_s_sr S T" |
"decided S T \<Longrightarrow> full cdcl_cp T U \<Longrightarrow> cdcl_s_sr S U" |
"no_step cdcl_cp S \<Longrightarrow> full (\<lambda>S T. skip S T \<or> resolve S T \<or> backtrack S T) S T 
  \<Longrightarrow> full cdcl_cp T U 
  \<Longrightarrow> cdcl_s_sr S U"

lemma 
  "cdcl_s\<^sup>*\<^sup>* S T \<Longrightarrow> no_step cdcl_s T \<Longrightarrow> cdcl_s_sr\<^sup>*\<^sup>* S T"
  apply (induction rule: rtranclp_induct)
  apply simp
  apply simp
oops

interpretation cdcl_CW: dpll_state trail "\<lambda>S. clauses S \<union> learned_clauses S" 
  "\<lambda> M (_, N, U, k, D). (M, N, U, k, D)" "\<lambda> C (M, N, U, k, D). (M, N, insert C U, k, D)" 
  "\<lambda> C (M, N, U, k, D). (M, N - {C}, U - {C}, k, D)"
  by unfold_locales auto
  
end