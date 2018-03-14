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

(* TODO Merge with the proof from  thm after_fast_restart_replay*)
lemma after_fast_restart_replay:
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    stgy_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (M', N, U, None)\<close> and
    smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close> and
    N'_N: \<open>\<forall>C\<in>#N'. \<forall>M1 K M2. M' = M2 @ Decided K # M1 \<longrightarrow> \<not>M1 \<Turnstile>as CNot C\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], N+N', U', None) (drop (length M' - n) M', N+ N', U', None)\<close>
proof -
  let ?S = \<open>\<lambda>n. (drop (length M' - n) M', N+N', U', None)\<close>
  note cdcl\<^sub>W_restart_mset_state[simp]
  have
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (M', N, U, None)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (M', N, U, None)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (M', N, U, None)\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (M', N, U, None)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+

  have smaller_confl: \<open>cdcl\<^sub>W_restart_mset.no_smaller_confl (M', N, U, None)\<close>
    using stgy_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def by blast
  have n_d: \<open>no_dup M'\<close>
    using M_lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by simp
  let ?L = \<open>\<lambda>m. M' ! (length M' - Suc m)\<close>
  have undef_nth_Suc:
     \<open>undefined_lit (drop (length M' - m) M') (lit_of (?L m))\<close>
     if \<open>m < length M'\<close>
     for m
  proof -
    define k where
      \<open>k = length M' - Suc m\<close>
    then have Sk: \<open>length M' - m = Suc k\<close>
      using that by linarith
    have k_le_M': \<open>k < length M'\<close>
      using that unfolding k_def by linarith
    have n_d': \<open>no_dup (take k M' @ ?L m # drop (Suc k) M')\<close>
      using n_d
      apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc k\<close>])
      apply (subst (asm) take_Suc_conv_app_nth)
       apply (rule k_le_M')
      apply (subst k_def[symmetric])
      by simp

    show ?thesis
      using n_d'
      apply (subst (asm) no_dup_append_cons)
      apply (subst (asm) k_def[symmetric])+
      apply (subst k_def[symmetric])+
      apply (subst Sk)+
      by blast
  qed

  have atm_in:
    \<open>atm_of (lit_of (M' ! m)) \<in> atms_of_mm N\<close>
    if \<open>m < length M'\<close>
    for m
    using alien that
    by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def lits_of_def)
  then have atm_in':
    \<open>atm_of (lit_of (M' ! m)) \<in> atms_of_mm (N + N')\<close>
    if \<open>m < length M'\<close>
    for m
    using alien that
    by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def lits_of_def)

  show ?thesis
    using kept
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc m) note IH = this(1) and kept = this(2)
    consider
      (le) \<open>m < length M'\<close> |
      (ge) \<open>m \<ge> length M'\<close>
      by linarith
    then show ?case
    proof (cases)
      case ge
      then show ?thesis
        using Suc by auto
    next
      case le
      define k where
        \<open>k = length M' - Suc m\<close>
      then have Sk: \<open>length M' - m = Suc k\<close>
        using le by linarith
      have k_le_M': \<open>k < length M'\<close>
        using le unfolding k_def by linarith
      have kept': \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - m) M') \<longrightarrow> E \<in># N + U'\<close>
        using kept k_le_M' unfolding k_def[symmetric] Sk
        by (subst (asm) Cons_nth_drop_Suc[symmetric]) auto
      have M': \<open>M' = take (length M' - Suc m) M' @ ?L m # trail (?S m)\<close>
        apply (subst append_take_drop_id[symmetric, of _ \<open>Suc k\<close>])
        apply (subst take_Suc_conv_app_nth)
         apply (rule k_le_M')
        apply (subst k_def[symmetric])
        unfolding k_def[symmetric] Sk
        by auto

      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (?S m) (?S (Suc m))\<close>
      proof (cases \<open>?L (m)\<close>)
        case (Decided K) note K = this
        have dec: \<open>cdcl\<^sub>W_restart_mset.decide (?S m) (?S (Suc m))\<close>
          apply (rule cdcl\<^sub>W_restart_mset.decide_rule[of _ \<open>lit_of (?L m)\<close>])
          subgoal by simp
          subgoal using undef_nth_Suc[of m] le by simp
          subgoal using le by (auto simp: atm_in)
          subgoal using le k_le_M' K unfolding k_def[symmetric] Sk
            by (auto simp: state_eq_def state_def Cons_nth_drop_Suc[symmetric])
          done
        have Dec: \<open>M' ! k = Decided K\<close>
          using K unfolding k_def[symmetric] Sk .

        have H: \<open>D + {#L#} \<in># N + U \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot D\<close> for D L
          using smaller_propa unfolding cdcl\<^sub>W_restart_mset.no_smaller_propa_def
            trail.simps clauses_def
            cdcl\<^sub>W_restart_mset_state
          apply (subst (asm) M')
          unfolding Dec Sk k_def[symmetric]
          by (auto simp: clauses_def state_eq_def)
        have \<open>D \<in># N \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow> L \<in># D \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot (remove1_mset L D)\<close> and
          \<open>D \<in># U' \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow> L \<in># D \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot (remove1_mset L D)\<close>for D L
          using H[of \<open>remove1_mset L D\<close> L] U'_U by auto
        then have nss: \<open>no_step cdcl\<^sub>W_restart_mset.propagate (?S m)\<close>
          using N'_N
          by (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def
              state_eq_def k_def[symmetric] Sk)

        have H: \<open>D \<in># N + U' \<longrightarrow> \<not> (trail (?S m)) \<Turnstile>as CNot D\<close> for D
          using smaller_confl U'_U unfolding cdcl\<^sub>W_restart_mset.no_smaller_confl_def
            trail.simps clauses_def cdcl\<^sub>W_restart_mset_state
          apply (subst (asm) M')
          unfolding Dec Sk k_def[symmetric]
          by (auto simp: clauses_def state_eq_def)
        then have nsc: \<open>no_step cdcl\<^sub>W_restart_mset.conflict (?S m)\<close>
          using N'_N
          by (auto simp: cdcl\<^sub>W_restart_mset.conflict.simps clauses_def state_eq_def
              k_def[symmetric] Sk)
        show ?thesis
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.other')
            apply (rule nsc)
           apply (rule nss)
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.decide)
          apply (rule dec)
          done
      next
        case K: (Propagated K C)
        have Propa: \<open>M' ! k = Propagated K C\<close>
          using K unfolding k_def[symmetric] Sk .
        have
          M_C: \<open>trail (?S m) \<Turnstile>as CNot (remove1_mset K C)\<close> and
          K_C: \<open>K \<in># C\<close>
          using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def trail.simps
          by (subst (asm)(3) M'; auto simp: k_def[symmetric] Sk Propa)+
        have [simp]: \<open>k - min (length M') k = 0\<close>
          unfolding k_def by auto
        have C_N_U: \<open>C \<in># N + U'\<close>
          using learned kept unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def Sk
            k_def[symmetric]
          apply (subst (asm)(4)M')
          apply (subst (asm)(10)M')
          unfolding K
          by (auto simp: K k_def[symmetric] Sk Propa clauses_def)
        have \<open>cdcl\<^sub>W_restart_mset.propagate (?S m) (?S (Suc m))\<close>
          apply (rule cdcl\<^sub>W_restart_mset.propagate_rule[of _ C K])
          subgoal by simp
          subgoal using C_N_U by (auto simp add: clauses_def)
          subgoal using K_C .
          subgoal using M_C .
          subgoal using undef_nth_Suc[of m] le K by (simp add: k_def[symmetric] Sk)
          subgoal
            using le k_le_M' K unfolding k_def[symmetric] Sk
            by (auto simp: state_eq_def
                state_def Cons_nth_drop_Suc[symmetric])
          done
        then show ?thesis
          by (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
      qed
      then show ?thesis
        using IH[OF kept'] by simp
    qed
  qed
qed

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
