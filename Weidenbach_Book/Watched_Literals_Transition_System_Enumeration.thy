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
         ((uminus o lit_of) `# mset (take 2 (filter is_decided M)))
         ((uminus o lit_of) `# mset (drop 2 (filter is_decided M)))\<close>

lemma clause_TWL_Deco_clause[simp]: \<open>clause (TWL_DECO_clause M) = DECO_clause M\<close>
  by (auto simp: TWL_DECO_clause_def DECO_clause_def
      simp del: image_mset_union mset_append
      simp add: image_mset_union[symmetric] mset_append[symmetric] mset_filter)

inductive negate_model_and_add :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
bj_unit:
  \<open>negate_model_and_add (M, N, U, None, NP, UP, WS, Q)
       (Propagated (-K) (DECO_clause M) # M1, N, U, None, add_mset (DECO_clause M) NP, UP, {#}, {#K#})\<close>
if
  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
  \<open>get_level M K = count_decided M\<close> and
  \<open>count_decided M = 1\<close> |
bj_nonunit:
  \<open>negate_model_and_add (M, N, U, None, NP, UP, WS, Q)
       (Propagated (-K) (DECO_clause M) # M1, add_mset (TWL_DECO_clause M) N, U, None, NP, UP, {#}, {#K#})\<close>
if
  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
  \<open>get_level M K = count_decided M\<close> and
  \<open>count_decided M \<ge> 2\<close> |
restart_nonunit:
  \<open>negate_model_and_add (M, N, U, None, NP, UP, WS, Q)
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
    no_confl: \<open>\<forall>C\<in>#N'. \<forall>M1 K M2. M' = M2 @ Decided K # M1 \<longrightarrow> \<not>M1 \<Turnstile>as CNot C\<close> and
    no_propa: \<open>\<forall>C\<in>#N'. \<forall>M1 K M2 L. M' = M2 @ Decided K # M1 \<longrightarrow> L \<in># C \<longrightarrow>
          \<not>M1 \<Turnstile>as CNot (remove1_mset L C)\<close>
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
        have no_new_propa: \<open>False\<close>
          if
            \<open>drop (Suc k) M' \<Turnstile>as CNot (remove1_mset L E)\<close> and
            \<open>L \<in># E\<close> and
            \<open>undefined_lit (drop (Suc k) M') L\<close> and
            \<open>E \<in># N'\<close> for L E
          using that no_propa
          apply (subst (asm)(3) M')
          apply (subst (asm)(2) M')
          apply (subst (asm) M')
          unfolding k_def[symmetric] Dec
          by (auto simp: k_def dest!: multi_member_split)

        have \<open>D \<in># N \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow> L \<in># D \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot (remove1_mset L D)\<close> and
          \<open>D \<in># U' \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow> L \<in># D \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot (remove1_mset L D)\<close>for D L
          using H[of \<open>remove1_mset L D\<close> L] U'_U by auto
        then have nss: \<open>no_step cdcl\<^sub>W_restart_mset.propagate (?S m)\<close>
          using no_propa no_new_propa
          by (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def
              state_eq_def k_def[symmetric] Sk)
        have no_new_confl: \<open>drop (Suc k) M' \<Turnstile>as CNot D \<Longrightarrow> D \<in># N' \<Longrightarrow> False\<close> for D
          using no_confl
          apply (subst (asm)(2) M')
          apply (subst (asm) M')
          unfolding k_def[symmetric] Dec
          by (auto simp: k_def dest!: multi_member_split)

        have H: \<open>D \<in># N + U' \<longrightarrow> \<not> (trail (?S m)) \<Turnstile>as CNot D\<close> for D
          using smaller_confl U'_U unfolding cdcl\<^sub>W_restart_mset.no_smaller_confl_def
            trail.simps clauses_def cdcl\<^sub>W_restart_mset_state
          apply (subst (asm) M')
          unfolding Dec Sk k_def[symmetric]
          by (auto simp: clauses_def state_eq_def)
        then have nsc: \<open>no_step cdcl\<^sub>W_restart_mset.conflict (?S m)\<close>
          using no_new_confl
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

lemma after_fast_restart_replay':
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    stgy_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (M', N, U, None)\<close> and
    smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close> and
    N_N': \<open>N \<subseteq># N'\<close> and
    no_confl: \<open>\<forall>C\<in>#N'-N. \<forall>M1 K M2. M' = M2 @ Decided K # M1 \<longrightarrow> \<not>M1 \<Turnstile>as CNot C\<close> and
    no_propa: \<open>\<forall>C\<in>#N'-N. \<forall>M1 K M2 L. M' = M2 @ Decided K # M1 \<longrightarrow> L \<in># C \<longrightarrow>
          \<not>M1 \<Turnstile>as CNot (remove1_mset L C)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], N', U', None) (drop (length M' - n) M', N', U', None)\<close>
  using after_fast_restart_replay[OF inv stgy_invs smaller_propa kept U'_U, of \<open>N' - N\<close>]
  no_confl no_propa N_N'
  by auto

lemma after_fast_restart_replay_no_stgy:
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N+N' + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], N+N', U', None) (drop (length M' - n) M', N+N', U', None)\<close>
proof -
  let ?S = \<open>\<lambda>n. (drop (length M' - n) M', N + N', U', None)\<close>
  note cdcl\<^sub>W_restart_mset_state[simp]
  have
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (M', N, U, None)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (M', N, U, None)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (M', N, U, None)\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (M', N, U, None)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+

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
    \<open>atm_of (lit_of (M' ! m)) \<in> atms_of_mm (N+N')\<close>
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
    proof cases
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
      have kept': \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - m) M') \<longrightarrow> E \<in># N+N' + U'\<close>
        using kept k_le_M' unfolding k_def[symmetric] Sk
        by (subst (asm) Cons_nth_drop_Suc[symmetric]) auto
      have M': \<open>M' = take (length M' - Suc m) M' @ ?L m # trail (?S m)\<close>
        apply (subst append_take_drop_id[symmetric, of _ \<open>Suc k\<close>])
        apply (subst take_Suc_conv_app_nth)
         apply (rule k_le_M')
        apply (subst k_def[symmetric])
        unfolding k_def[symmetric] Sk
        by auto

      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (?S m) (?S (Suc m))\<close>
      proof (cases \<open>?L (m)\<close>)
        case (Decided K) note K = this
        have dec: \<open>cdcl\<^sub>W_restart_mset.decide (?S m) (?S (Suc m))\<close>
          apply (rule cdcl\<^sub>W_restart_mset.decide_rule[of _ \<open>lit_of (?L m)\<close>])
          subgoal by simp
          subgoal using undef_nth_Suc[of m] le by simp
          subgoal using le  atm_in by auto
          subgoal using le k_le_M' K unfolding k_def[symmetric] Sk
            by (auto simp: state_eq_def state_def Cons_nth_drop_Suc[symmetric])
          done
        have Dec: \<open>M' ! k = Decided K\<close>
          using K unfolding k_def[symmetric] Sk .

        show ?thesis
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.intros(3))
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
        have C_N_U: \<open>C \<in># N+N' + U'\<close>
          using learned kept unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def Sk
            k_def[symmetric]
          apply (subst (asm)(4)M')
          apply (subst (asm)(10)M')
          unfolding K
          by (auto simp: K k_def[symmetric] Sk Propa clauses_def)
        have \<open>cdcl\<^sub>W_restart_mset.propagate (?S m) (?S (Suc m))\<close>
          apply (rule cdcl\<^sub>W_restart_mset.propagate_rule[of _ C K])
          subgoal by simp
          subgoal using C_N_U by (simp add: clauses_def)
          subgoal using K_C .
          subgoal using M_C .
          subgoal using undef_nth_Suc[of m] le K by (simp add: k_def[symmetric] Sk)
          subgoal
            using le k_le_M' K unfolding k_def[symmetric] Sk
            by (auto simp: state_eq_def
                state_def Cons_nth_drop_Suc[symmetric])
          done
        then show ?thesis
          by (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.intros)
      qed
      then show ?thesis
        using IH[OF kept'] by simp
    qed
  qed
qed

lemma after_fast_restart_replay_no_stgy':
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N' + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close> and
     \<open>N \<subseteq># N'\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], N', U', None) (drop (length M' - n) M', N', U', None)\<close>
  using after_fast_restart_replay_no_stgy[OF inv, of n \<open>N'-N\<close> U'] assms by auto

(* TODO Move *)
lemma (in conflict_driven_clause_learning\<^sub>W) rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart:
  \<open>cdcl\<^sub>W\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl\<^sub>W_cdcl\<^sub>W_restart)
(* End Move *)


lemma cdcl\<^sub>W_all_struct_inv_move_to_init:
  assumes inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U + U', D)\<close>
 shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N + U', U, D)\<close>
  using assms
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state clauses_def
          assms
  apply (intro conjI impI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: ac_simps)
  subgoal by (auto simp: ac_simps)
  subgoal by auto
  done

lemma twl_struct_invs_move_to_init:
  assumes \<open>twl_struct_invs (M, N, U + U', D, NP, UP, WS, Q)\<close>
  shows \<open>twl_struct_invs (M, N + U', U, D, NP, UP, WS, Q)\<close>
proof -
  have H: \<open>N + (U + U') = N + U' + U\<close>
    by simp
  have struct_invs:
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NP, clauses (U + U') + UP, D')\<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses (N + U') + NP, clauses U + UP, D')\<close>
    for D'
    using cdcl\<^sub>W_all_struct_inv_move_to_init[of M \<open>clauses N + NP\<close> \<open>clauses U + UP\<close>
      \<open>clauses U'\<close> D']
    by (auto simp: ac_simps)
  have smaller: \<open>clauses N + NP + (clauses (U + U') + UP) = clauses (N + U') + NP + (clauses U + UP)\<close>
    by auto
  show ?thesis
    using assms
    apply (cases D; clarify)
    unfolding twl_struct_invs_def twl_st_inv.simps valid_enqueued.simps
      twl_st_exception_inv.simps no_duplicate_queued.simps
      confl_cands_enqueued.simps distinct_queued.simps propa_cands_enqueued.simps
      assms entailed_clss_inv.simps past_invs.simps H state\<^sub>W_of.simps
      cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state clauses_def
      twl_exception_inv.simps get_conflict.simps literals_to_update.simps clauses_to_update.simps
      clauses_to_update_inv.simps
     apply (intro conjI)
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (rule struct_invs) fast
    subgoal unfolding smaller by argo
    subgoal by argo
    subgoal by argo
    subgoal by argo
    subgoal by fast
    subgoal by fast
    subgoal by argo
    subgoal by fast
    subgoal by argo
    subgoal by blast
    subgoal by fast
    subgoal by argo
    subgoal by argo
    subgoal by argo
    subgoal by argo
    apply (intro conjI)
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (rule struct_invs) fast
    subgoal unfolding smaller by argo
    subgoal by argo
    subgoal by argo
    subgoal by argo
    subgoal by fast
    subgoal by fast
    subgoal by argo
    subgoal by fast
    subgoal by argo
    subgoal by argo
    subgoal by fast
    subgoal by argo
    subgoal by argo
    done
qed

lemma
  assumes
     \<open>negate_model_and_add S T\<close> and
     \<open>twl_struct_invs S\<close>
   shows \<open>twl_struct_invs T\<close>
  using assms
proof (induction rule: negate_model_and_add.induct)
  case (bj_nonunit K M1 M2 M N U NP UP WS Q) note decomp = this(1) and lev = this(2) and
    count_dec = this(3) and inv = this(4)
  let ?S = \<open>(M, N, U, None, NP, UP, WS, Q)\<close>
  let ?T = \<open>(Propagated K (DECO_clause M) # M1, add_mset (TWL_DECO_clause M) N, U, None,
        NP, UP, {#}, {#- K#})\<close>
  have
    st_invs: \<open>twl_st_inv ?S\<close> and
    \<open>valid_enqueued ?S\<close> and
    struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close> and
    no_smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close> and
    \<open>twl_st_exception_inv ?S\<close> and
    \<open>no_duplicate_queued ?S\<close> and
    \<open>distinct_queued ?S\<close> and
    \<open>confl_cands_enqueued ?S\<close> and
    \<open>propa_cands_enqueued ?S\<close> and
    \<open>get_conflict ?S \<noteq> None \<longrightarrow> clauses_to_update ?S = {#} \<and> literals_to_update ?S = {#}\<close> and
    entailed: \<open>entailed_clss_inv ?S\<close> and
    \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using inv unfolding twl_struct_invs_def
    by fast+
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast
  define M2' where
    \<open>M2' = M3 @ M2\<close>
  then have M': \<open>M = M2' @ Decided K # M1\<close>
    using M by auto
  then have
    st_invs_M1: \<open>\<forall>C\<in>#N + U. twl_lazy_update M1 C \<and> twl_inv M1 C \<and>
         watched_literals_false_of_max_level M1 C \<and>
         twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close> and
    confl_enqueued_M1: \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    propa_enqueued_M1: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    clss_upd: \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    past_M1: \<open>past_invs (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using past
    unfolding past_invs.simps
    by auto
  have no_dup: \<open>no_dup M\<close>
    using struct_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: trail.simps)
  then have [simp]: \<open>filter is_decided M2' = []\<close>
    using count_dec lev unfolding M'
    by (auto simp: TWL_DECO_clause_def count_decided_def add_mset_eq_add_mset M')

  have dist: \<open>distinct (map atm_of (map lit_of M))\<close>
    using no_dup by (auto simp: no_dup_def comp_def)

  have dist_filtered: \<open>distinct_mset (lit_of `# mset (filter is_decided M))\<close>
    apply (rule distinct_mset_mono[of _ \<open>lit_of `# mset M\<close>])
    subgoal by (auto intro!: image_mset_subseteq_mono simp: mset_filter)
    subgoal using dist by (auto simp: mset_map[symmetric] simp del: mset_map
          intro: distinct_mapI)
    done
  then have dist_filtered': \<open>distinct_mset (uminus `# lit_of `# mset (filter is_decided M))\<close>
    apply (subst distinct_image_mset_inj)
    subgoal by (auto simp: inj_on_def)
    subgoal .
    done
  obtain L' C where
(*     M: \<open>TWL_DECO_clause M = TWL_Clause {#-K, L'#} C\<close> and *)
    filter_M: \<open>filter is_decided M = Decided K # Decided L' # C\<close>
    using count_dec lev unfolding M'
    by (cases \<open>filter is_decided M\<close>; cases \<open>tl (filter is_decided M)\<close>;
        cases \<open>hd (filter is_decided M)\<close>; cases \<open>hd (tl (filter is_decided M))\<close>)
      (auto simp: TWL_DECO_clause_def count_decided_def add_mset_eq_add_mset M'
        filter_eq_Cons_iff tl_append)
  then have deco_M: \<open>TWL_DECO_clause M = TWL_Clause {#-K, -L'#} (uminus `# lit_of `# mset C)\<close>
    by (auto simp: TWL_DECO_clause_def)
  have C_M1: \<open>C = tl (filter is_decided M1)\<close>
    using filter_M unfolding M'
    by auto
  then obtain M1'' M1' where
    M1: \<open>M1 = M1'' @ Decided L' # M1'\<close>
    by (metis (no_types, lifting) M' \<open>filter is_decided M2' = []\<close> append_self_conv2
        filter.simps(2) filter_M filter_append filter_eq_Cons_iff list.sel(3))
  then have [simp]: \<open>count_decided M1'' = 0\<close> and filter_M1'': \<open>filter is_decided M1'' = []\<close>
    using filter_M no_dup unfolding C_M1 M1 M'
    by (auto simp: tl_append count_decided_def dest: filter_eq_ConsD split: list.splits)
  have C_in_M1: \<open>lits_of_l C \<subseteq> lits_of_l M1\<close>
    unfolding C_M1 by (auto simp: lits_of_def dest: in_set_tlD)

  let ?S' = \<open>(M1, add_mset (TWL_DECO_clause M) N, U, None, NP, UP, add_mset (-L', (TWL_DECO_clause M)) {#}, {#})\<close>
  let ?T' = \<open>(Propagated (-K) (DECO_clause M) # M1, add_mset (TWL_DECO_clause M) N, U, None,
        NP, UP, {#}, {#- (-K)#})\<close>
  have propa: \<open>cdcl_twl_cp ?S' ?T'\<close>
    unfolding clause_TWL_Deco_clause[symmetric]
    apply (rule cdcl_twl_cp.propagate)
    subgoal by (auto simp: deco_M)
    subgoal using no_dup unfolding M by auto
    subgoal using C_in_M1 unfolding deco_M by (auto simp: lits_of_def)
    done

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], clauses (add_mset (TWL_DECO_clause M) N) + NP,
         clauses U + UP, None)
    (drop (length M - length M1) M, clauses (add_mset (TWL_DECO_clause M) N) + NP, clauses U + UP, None)\<close>
    apply (rule after_fast_restart_replay_no_stgy'[OF struct_invs[unfolded state\<^sub>W_of.simps]])
    subgoal
      apply (intro allI impI conjI)
      subgoal for L E
        by (use M' struct_invs cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of E M]
            in \<open>auto simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
                  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset_state clauses_def\<close>)
      done
    subgoal by simp
    subgoal by simp
    done
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], clauses (add_mset (TWL_DECO_clause M) N) + NP,
         clauses U + UP, None) (state\<^sub>W_of ?S')\<close>
    using M' by simp
  moreover {
    have \<open>distinct_mset (DECO_clause M)\<close>
      using dist_filtered' unfolding DECO_clause_def
      by (simp add: mset_filter)
    then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ([], clauses (add_mset (TWL_DECO_clause M) N) + NP,
         clauses U + UP, None)\<close>
      using struct_invs
      by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state)
  }
  ultimately have struct_invs_S': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S')\<close>
    by (auto intro: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv
        dest!: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart)
  have no_smaller_M1:
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of (M1, N, U, None, NP, UP, WS, Q))\<close>
    using no_smaller by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        cdcl\<^sub>W_restart_mset_state clauses_def M')

  have no_smaller_S': \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S')\<close>
    unfolding  cdcl\<^sub>W_restart_mset.no_smaller_propa_def state\<^sub>W_of.simps
        cdcl\<^sub>W_restart_mset_state clauses_def
  proof (intro conjI impI allI)
    fix M1a M2 K' D L
    assume
      M1a: \<open>M1 = M2 @ Decided K' # M1a\<close> and
      DL: \<open>D + {#L#} \<in># clauses (add_mset (TWL_DECO_clause M) N) + NP + (clauses U + UP)\<close> and
      undef: \<open>undefined_lit M1a L\<close>
    consider
      \<open>D+{#L#} \<in># clauses N + NP + (clauses U + UP)\<close> |
      \<open>D+{#L#} = clause (TWL_DECO_clause M)\<close>
      using DL by auto
    then show \<open>\<not> M1a \<Turnstile>as CNot D\<close>
    proof cases
      case 1
      then show ?thesis
        using DL M1a undef no_smaller_M1
        by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def
            cdcl\<^sub>W_restart_mset_state clauses_def deco_M
            add_mset_eq_add_mset)
    next
      case 2
      moreover have \<open>L' \<notin> lits_of_l M1a\<close>  \<open>-K \<notin> lits_of_l M1a\<close> \<open>K \<notin> lits_of_l M1a\<close>
      using no_dup M1 filter_M1'' unfolding deco_M unfolding M' M1a
      by (auto simp: deco_M add_mset_eq_add_mset
        dest: in_lits_of_l_defined_litD
        simp del: \<open>filter is_decided M2' = []\<close>
        elim!: list_match_lel_lel)
      ultimately  show ?thesis
        using undef by (auto simp: deco_M add_mset_eq_add_mset
            dest!: multi_member_split)
    qed
  qed
  have [simp]: \<open>get_level M1 L' = count_decided M1\<close>
    using no_dup unfolding M' M1 by auto
  have \<open>watched_literals_false_of_max_level M1 (TWL_DECO_clause M)\<close>
    using no_dup apply (subst (asm) M')
    by (auto simp: deco_M add_mset_eq_add_mset dest: in_lits_of_l_defined_litD)
  moreover have \<open>C \<in># N + U \<Longrightarrow> struct_wf_twl_cls C\<close> for C
    using st_invs unfolding twl_st_inv.simps by auto
  moreover have \<open>struct_wf_twl_cls (TWL_DECO_clause M)\<close>
    using dist_filtered' unfolding deco_M filter_M
    by (auto simp: simp del: clause_TWL_Deco_clause)
  ultimately have \<open>twl_st_inv ?S'\<close>
    using st_invs_M1 unfolding twl_st_inv.simps
    by (auto simp: twl_is_an_exception_def)

  moreover have \<open>valid_enqueued ?S'\<close>
    by (auto simp: deco_M) (auto simp: M1)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S')\<close>
    using struct_invs_S' .
  moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S')\<close>
    using no_smaller_S' .
  moreover have \<open>twl_st_exception_inv ?S'\<close>
    using st_invs_M1 C_in_M1
    by (auto simp: twl_exception_inv.simps deco_M add_mset_eq_add_mset)
      (auto simp: lits_of_def)
  moreover have \<open>no_duplicate_queued ?S'\<close>
    by (auto simp: M1)
  moreover have \<open>distinct_queued ?S'\<close>
    by auto
  moreover have \<open>confl_cands_enqueued ?S'\<close>
    using confl_enqueued_M1 by auto
  moreover have \<open>propa_cands_enqueued ?S'\<close>
    using propa_enqueued_M1 by auto
  moreover {
    have \<open>get_level M L = 0 \<Longrightarrow> get_level M1 L = 0\<close> for L
      using no_dup defined_lit_no_dupD(1)[of M1 L M2']
      by (cases \<open>defined_lit M L\<close>)
          (auto simp: M' defined_lit_append defined_lit_cons atm_of_eq_atm_of
          get_level_cons_if split: if_splits)
    moreover have \<open>get_level M L = 0 \<Longrightarrow> L \<in> lits_of_l M \<Longrightarrow> L \<in> lits_of_l M1\<close> for L
      using no_dup defined_lit_no_dupD(1)[of M1 L M2']
      by (cases \<open>defined_lit M L\<close>)
        (auto simp: M' defined_lit_append defined_lit_cons atm_of_eq_atm_of
          get_level_cons_if split: if_splits dest: in_lits_of_l_defined_litD)
    ultimately have \<open>entailed_clss_inv ?S'\<close>
      using entailed unfolding entailed_clss_inv.simps by meson
  }
  moreover have \<open>clauses_to_update_inv ?S'\<close>
    using clss_upd no_dup unfolding deco_M by (auto simp: deco_M add_mset_eq_add_mset M'
        dest: in_lits_of_l_defined_litD)
  moreover have \<open>past_invs ?S'\<close>
    unfolding past_invs.simps
  proof (intro conjI impI allI)
    fix M1a M2 K'
    assume M1a: \<open>M1 = M2 @ Decided K' # M1a\<close>
    let ?SM1a = \<open>(M1a, add_mset (TWL_DECO_clause M) N, U, None, NP, UP, {#}, {#})\<close>
    have
      struct:
      \<open>C\<in>#N + U \<Longrightarrow> twl_lazy_update M1a C \<and> twl_inv M1a C \<and>
          watched_literals_false_of_max_level M1a C \<and>
          twl_exception_inv (M1a, N, U, None, NP, UP, {#}, {#}) C\<close>
      for C
      using past_M1 unfolding past_invs.simps unfolding M1a
      by fast+
    have
      confl: \<open>confl_cands_enqueued (M1a, N, U, None, NP, UP, {#}, {#})\<close> and
      propa: \<open>propa_cands_enqueued (M1a, N, U, None, NP, UP, {#}, {#})\<close> and
      clss_to_upd: \<open>clauses_to_update_inv (M1a, N, U, None, NP, UP, {#}, {#})\<close>
      using past_M1 unfolding past_invs.simps unfolding M1a
      by fast+
    have [iff]: \<open>L' \<notin> lits_of_l M1a\<close> \<open>K \<notin> lits_of_l M1a\<close>
      using no_dup M1 filter_M1'' unfolding deco_M unfolding M' M1a
      by (auto simp: deco_M add_mset_eq_add_mset
        dest: in_lits_of_l_defined_litD
        simp del: \<open>filter is_decided M2' = []\<close>
        elim!: list_match_lel_lel)
    have \<open>twl_lazy_update M1a (TWL_DECO_clause M)\<close>
      using no_dup M1 unfolding deco_M unfolding M' M1a
      by (auto simp: deco_M add_mset_eq_add_mset
        dest: in_lits_of_l_defined_litD)
    moreover have \<open>twl_inv M1a (TWL_DECO_clause M)\<close>
      unfolding deco_M by (auto simp: add_mset_eq_add_mset)
    moreover have \<open>watched_literals_false_of_max_level M1a (TWL_DECO_clause M)\<close>
      unfolding deco_M by (auto simp: add_mset_eq_add_mset)
    moreover have \<open>twl_exception_inv ?SM1a (TWL_DECO_clause M)\<close>
      unfolding deco_M by (auto simp: add_mset_eq_add_mset twl_exception_inv.simps)
    ultimately have \<open>C\<in>#add_mset (TWL_DECO_clause M) N + U \<Longrightarrow> twl_lazy_update M1a C \<and> twl_inv M1a C \<and>
         watched_literals_false_of_max_level M1a C \<and>
         twl_exception_inv ?SM1a C\<close> for C
      using struct[of C]
      by (auto simp: twl_exception_inv.simps)
    then show \<open>\<forall>C\<in>#add_mset (TWL_DECO_clause M) N + U. twl_lazy_update M1a C \<and> twl_inv M1a C \<and>
         watched_literals_false_of_max_level M1a C \<and>
         twl_exception_inv ?SM1a C\<close>
      by blast
    show \<open>confl_cands_enqueued ?SM1a\<close>
      using confl by (auto simp: deco_M)
    show \<open>propa_cands_enqueued ?SM1a\<close>
      using propa by (auto simp: deco_M)
    show \<open>clauses_to_update_inv ?SM1a\<close>
      using clss_to_upd
      by (auto simp: deco_M clauses_to_update_prop.simps add_mset_eq_add_mset)
  qed
  moreover have \<open>get_conflict ?S' = None\<close>
    by simp
  ultimately have \<open>twl_struct_invs ?S'\<close>
    unfolding twl_struct_invs_def
    by meson
  then have \<open>twl_struct_invs ?T'\<close>
    by (rule cdcl_twl_cp_twl_struct_invs[OF propa])
  then show ?case
    by simp
next
  case (bj_unit K M1 M2 M N U NP UP WS Q)
  then show ?case sorry
next
  case (restart_nonunit K M1 M2 M N U NP UP WS Q)
  then show ?case sorry
qed


end
