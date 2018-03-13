theory Watched_Literals_Transition_System_Enumeration
  imports Watched_Literals_Transition_System Model_Enumeration
begin

definition DECO_clause :: \<open>('v, 'a) ann_lits \<Rightarrow>  'v clause\<close>where
  \<open>DECO_clause M = (uminus o lit_of) `# (filter_mset is_decided (mset M))\<close>

lemma distinct_mset_DECO:
  \<open>distinct_mset (DECO_clause M) \<longleftrightarrow> distinct_mset (lit_of `# filter_mset is_decided (mset M))\<close>
  (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have \<open>?A \<longleftrightarrow> distinct_mset (uminus `# lit_of `# (filter_mset is_decided (mset M)))\<close>
    by (auto simp: DECO_clause_def)
  also have \<open>\<dots> \<longleftrightarrow> distinct_mset (lit_of `# (filter_mset is_decided (mset M)))\<close>
    apply (subst distinct_image_mset_inj)
    subgoal by (auto simp: inj_on_def)
    subgoal by auto
    done
  finally show ?thesis
    .
qed

definition TWL_DECO_clause where
  \<open>TWL_DECO_clause M =
       TWL_Clause 
         ((uminus o lit_of) `# mset (take 2 (rev (filter is_decided M))))
         ((uminus o lit_of) `# mset (drop 2 (rev (filter is_decided M))))\<close>

lemma clause_TWL_Deco_clause[simp]: \<open>clause (TWL_DECO_clause M) = DECO_clause M\<close>
  by (auto simp: TWL_DECO_clause_def DECO_clause_def
      simp del: image_mset_union mset_append
      simp add: image_mset_union[symmetric] mset_append[symmetric] mset_filter)

inductive negate_model_and_add :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
bj_unit: 
  \<open>negate_model_and_add (M, N, U, D, NP, UP, WS, Q)
       (Propagated K (DECO_clause M) # M1, add_mset (TWL_DECO_clause M) N, U, None, NP, UP, {#}, {#-K#})\<close>
if
  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
  \<open>get_level M K = count_decided M\<close> and
  \<open>count_decided M = 1\<close> |
bj_nonunit: 
  \<open>negate_model_and_add (M, N, U, D, NP, UP, WS, Q)
       (Propagated K (DECO_clause M) # M1, N, add_mset (TWL_DECO_clause M) U, None, NP, UP, {#}, {#-K#})\<close>
if
  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
  \<open>get_level M K = count_decided M\<close> and
  \<open>count_decided M \<ge> 2\<close> |
restart_nonunit:
  \<open>negate_model_and_add (M, N, U, D, NP, UP, WS, Q)
       (M1, add_mset (TWL_DECO_clause M) N, U, None, NP, UP, {#}, {#})\<close>
if 
  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
  \<open>get_level M K = 1\<close> and
  \<open>count_decided M > 1\<close>

lemma
  assumes
     \<open>negate_model_and_add S T\<close> and
     \<open>twl_struct_invs S\<close>
   shows \<open>twl_struct_invs T\<close>
  using assms
proof (induction rule: negate_model_and_add.induct)
  case (bj_nonunit K M1 M2 M N U D NP UP WS Q) note decomp = this(1) and lev = this(2) and
    count_dec = this(3) and inv = this(4)
  let ?S = \<open>(M, N, U, D, NP, UP, WS, Q)\<close>
  let ?T = \<open>(Propagated K (DECO_clause M) # M1, add_mset (TWL_DECO_clause M) N, U, None,
        NP, UP, {#}, {#- K#})\<close>
  have
    st_invs: \<open>twl_st_inv ?S\<close> and
    \<open>valid_enqueued ?S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close> and
    \<open>twl_st_exception_inv ?S\<close> and
    \<open>no_duplicate_queued ?S\<close> and
    \<open>distinct_queued ?S\<close> and
    \<open>confl_cands_enqueued ?S\<close> and
    \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow> clauses_to_update ?S = {#} \<and> literals_to_update ?S = {#}\<close> and
    \<open>entailed_clss_inv ?S\<close> and
    \<open>clauses_to_update_inv ?S\<close> and
    \<open>past_invs ?S\<close>
    using inv unfolding twl_struct_invs_def 
    by fast+
  obtain L L' C where
    M: \<open>TWL_DECO_clause M = TWL_Clause {#L, L'#} C\<close>
    using count_dec
    by (cases \<open>rev (filter is_decided M)\<close>; cases \<open>tl (rev (filter is_decided M))\<close>)
      (auto simp: TWL_DECO_clause_def count_decided_def)
  have no_dup: \<open>no_dup M\<close>
    sorry
  then have dist: \<open>distinct (map atm_of (map lit_of M))\<close>
    by (auto simp: no_dup_def comp_def)

  have \<open>distinct_mset (lit_of `# filter_mset is_decided (mset M))\<close>
    apply (rule distinct_mset_mono[of _ \<open>lit_of `# mset M\<close>])
    subgoal by (auto intro: image_mset_subseteq_mono)
    subgoal using dist by (auto simp: mset_map[symmetric] simp del: mset_map
          intro: distinct_mapI)
    done
  then have \<open>struct_wf_twl_cls (TWL_DECO_clause M)\<close>
    using clause_TWL_Deco_clause[of M]
    by (auto simp: M distinct_mset_DECO simp del: clause_TWL_Deco_clause)
  moreover have True
    apply (auto simp: M twl_is_an_exception_def uminus_lit_swap)
    sorry
  ultimately have \<open>twl_st_inv ?T\<close>
    using st_invs unfolding twl_st_inv.simps
    apply (auto simp: )
    sorry

  show ?case
    unfolding twl_struct_invs_def 
    apply (intro conjI)
    sorry

next
  case (bj_unit K M1 M2 M N U D NP UP WS Q)
  then show ?case sorry
next
  case (restart_nonunit K M1 M2 M N U D NP UP WS Q)
  then show ?case sorry
qed


end
