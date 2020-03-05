theory CDCL_W_Abstract_State
imports CDCL_W_Full CDCL_W_Restart CDCL_W_Incremental

begin

section \<open>Instantiation of Weidenbach's CDCL by Multisets\<close>

text \<open>We first instantiate the locale of Weidenbach's locale. Then we refine it to a 2-WL program.\<close>

type_synonym 'v cdcl\<^sub>W_restart_mset = "('v, 'v clause) ann_lit list \<times>
  'v clauses \<times>
  'v clauses \<times>
  'v clause option"

text \<open>We use definition, otherwise we could not use the simplification theorems we have already
  shown.\<close>
fun trail :: "'v cdcl\<^sub>W_restart_mset \<Rightarrow> ('v, 'v clause) ann_lit list" where
"trail (M, _) = M"

fun init_clss :: "'v cdcl\<^sub>W_restart_mset \<Rightarrow> 'v clauses" where
"init_clss (_, N, _) = N"

fun learned_clss :: "'v cdcl\<^sub>W_restart_mset \<Rightarrow> 'v clauses" where
"learned_clss (_, _, U, _) = U"

fun conflicting :: "'v cdcl\<^sub>W_restart_mset \<Rightarrow> 'v clause option" where
"conflicting (_, _, _, C) = C"

fun cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'v cdcl\<^sub>W_restart_mset \<Rightarrow> 'v cdcl\<^sub>W_restart_mset" where
"cons_trail L (M, R) = (L # M, R)"

fun tl_trail where
"tl_trail (M, R) = (tl M, R)"

fun add_learned_cls where
"add_learned_cls C (M, N, U, R) = (M, N, {#C#} + U, R)"

fun add_init_cls where
"add_init_cls C (M, N, U, R) = (M, {#C#} + N, U, R)"

fun remove_cls where
"remove_cls C (M, N, U, R) = (M, removeAll_mset C N, removeAll_mset C U, R)"

fun update_conflicting where
"update_conflicting D (M, N, U,  _) = (M, N, U, D)"

fun init_state where
"init_state N = ([], N, {#}, None)"

declare trail.simps[simp del] cons_trail.simps[simp del] tl_trail.simps[simp del]
  add_learned_cls.simps[simp del] remove_cls.simps[simp del]
  update_conflicting.simps[simp del] init_clss.simps[simp del] learned_clss.simps[simp del]
  conflicting.simps[simp del] init_state.simps[simp del]

lemmas cdcl\<^sub>W_restart_mset_state = trail.simps cons_trail.simps tl_trail.simps add_learned_cls.simps
    remove_cls.simps update_conflicting.simps init_clss.simps learned_clss.simps
    conflicting.simps init_state.simps

definition state where
\<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, ())\<close>

interpretation cdcl\<^sub>W_restart_mset: state\<^sub>W_ops where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state
  .

definition state_eq :: "'v cdcl\<^sub>W_restart_mset \<Rightarrow> 'v cdcl\<^sub>W_restart_mset \<Rightarrow> bool" (infix "\<sim>m" 50) where
\<open>S \<sim>m T \<longleftrightarrow> state S = state T\<close>

interpretation cdcl\<^sub>W_restart_mset: state\<^sub>W where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and
  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state
  by unfold_locales (auto simp: cdcl\<^sub>W_restart_mset_state state_eq_def state_def)


abbreviation backtrack_lvl :: "'v cdcl\<^sub>W_restart_mset \<Rightarrow> nat" where
"backtrack_lvl \<equiv> cdcl\<^sub>W_restart_mset.backtrack_lvl"

interpretation cdcl\<^sub>W_restart_mset: conflict_driven_clause_learning\<^sub>W where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state
  by unfold_locales

lemma cdcl\<^sub>W_restart_mset_state_eq_eq: "state_eq = (=)"
   apply (intro ext)
   unfolding state_eq_def
   by (auto simp: cdcl\<^sub>W_restart_mset_state state_def)


lemma clauses_def: \<open>cdcl\<^sub>W_restart_mset.clauses (M, N, U, C) = N + U\<close>
  by (subst cdcl\<^sub>W_restart_mset.clauses_def) (simp add: cdcl\<^sub>W_restart_mset_state)

lemma cdcl\<^sub>W_restart_mset_reduce_trail_to:
  "cdcl\<^sub>W_restart_mset.reduce_trail_to F S =
    ((if length (trail S) \<ge> length F
    then drop (length (trail S) - length F) (trail S)
    else []), init_clss S, learned_clss S, conflicting S)"
    (is "?S = _")
proof (induction F S rule: cdcl\<^sub>W_restart_mset.reduce_trail_to.induct)
  case (1 F S) note IH = this
  show ?case
  proof (cases "trail S")
    case Nil
    then show ?thesis using IH by (cases S) (auto simp: cdcl\<^sub>W_restart_mset_state)
  next
    case (Cons L M)
    then show ?thesis
      apply (cases "Suc (length M) > length F")
      subgoal
        apply (subgoal_tac "Suc (length M) - length F = Suc (length M - length F)")
        using cdcl\<^sub>W_restart_mset.reduce_trail_to_length_ne[of S F] IH by auto
      subgoal
        using IH cdcl\<^sub>W_restart_mset.reduce_trail_to_length_ne[of S F]
          apply (cases S)
        by (simp add: cdcl\<^sub>W_restart_mset.trail_reduce_trail_to_drop cdcl\<^sub>W_restart_mset_state)
      done
  qed
qed


interpretation cdcl\<^sub>W_restart_mset: state\<^sub>W_adding_init_clause where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  add_init_cls = add_init_cls
  by unfold_locales (auto simp: state_def cdcl\<^sub>W_restart_mset_state)


interpretation cdcl\<^sub>W_restart_mset: conflict_driven_clause_learning_with_adding_init_clause\<^sub>W where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  add_init_cls = add_init_cls
  by unfold_locales (auto simp: state_def cdcl\<^sub>W_restart_mset_state)

lemma full_cdcl\<^sub>W_init_state:
  \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state {#}) S \<longleftrightarrow> S = init_state {#}\<close>
  unfolding full_def rtranclp_unfold
  by (subst tranclp_unfold_begin)
     (auto simp:  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps
      cdcl\<^sub>W_restart_mset.conflict.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
       cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.decide.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.backtrack.simps
      cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
      cdcl\<^sub>W_restart_mset_state clauses_def)

locale twl_restart_ops =
  fixes
    f :: \<open>nat \<Rightarrow> nat\<close>
begin

interpretation cdcl\<^sub>W_restart_mset: cdcl\<^sub>W_restart_restart_ops where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  f = f
  by unfold_locales

end

locale twl_restart =
  twl_restart_ops f for f :: \<open>nat \<Rightarrow> nat\<close> +
  assumes
    f: \<open>unbounded f\<close>
begin

interpretation cdcl\<^sub>W_restart_mset: cdcl\<^sub>W_restart_restart where
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and

  state_eq = state_eq and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  f = f
  by unfold_locales (rule f)

end

context conflict_driven_clause_learning\<^sub>W
begin

lemma distinct_cdcl\<^sub>W_state_alt_def:
  \<open>distinct_cdcl\<^sub>W_state S =
    ((\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T) \<and>
     distinct_mset_mset (clauses S) \<and>
     (\<forall>L mark. Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark))\<close>
  unfolding distinct_cdcl\<^sub>W_state_def clauses_def
  by auto
end


lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state {#}) S \<longleftrightarrow> False\<close>
  unfolding rtranclp_unfold
  by (auto simp:  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps
      cdcl\<^sub>W_restart_mset.conflict.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
       cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.decide.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.backtrack.simps
      cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
      cdcl\<^sub>W_restart_mset_state clauses_def)

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state {#}) S \<longleftrightarrow> S = init_state {#}\<close>
  unfolding rtranclp_unfold
  by (subst tranclp_unfold_begin)
    (auto simp: cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step)


subsection \<open>Restart with Replay\<close>

text \<open>
  In rather unfortunate move, we named restart with reuse of the trail ``fast restarts''
  due to the name the technique was presented first, before a reviewer pointed out that the ``fast''
  refers to the interval between two successive restarts and not to the idea that restarts are
  faster to do.
  This error is still present in various lemmas throughout the formalization.

  Anyway, the idea is that after a restart, parts of the trail are often reused (at least, for the
  VSIDS heuristic: VMTF moves too fast for that) and, therefore, it is better to not redo the
  propagations. A similar idea exists for backjump, chronological backtracking, but that technique
  is much more complicated to understand and implement properly.

TODO: fix
\<close>
lemma after_fast_restart_replay:
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    stgy_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (M', N, U, None)\<close> and
    smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], N, U', None) (drop (length M' - n) M', N, U', None)\<close>
proof -
  let ?S = \<open>\<lambda>n. (drop (length M' - n) M', N, U', None)\<close>
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
          by (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def
              state_eq_def k_def[symmetric] Sk)

        have H: \<open>D \<in># N + U' \<longrightarrow> \<not> (trail (?S m)) \<Turnstile>as CNot D\<close> for D
          using smaller_confl U'_U unfolding cdcl\<^sub>W_restart_mset.no_smaller_confl_def
            trail.simps clauses_def cdcl\<^sub>W_restart_mset_state
          apply (subst (asm) M')
          unfolding Dec Sk k_def[symmetric]
          by (auto simp: clauses_def state_eq_def)
        then have nsc: \<open>no_step cdcl\<^sub>W_restart_mset.conflict (?S m)\<close>
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
          using learned kept unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def Sk
            k_def[symmetric] cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
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
          by (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
      qed
      then show ?thesis
        using IH[OF kept'] by simp
    qed
  qed
qed

lemma after_fast_restart_replay_no_stgy:
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ([], N, U', None) (drop (length M' - n) M', N, U', None)\<close>
proof -
  let ?S = \<open>\<lambda>n. (drop (length M' - n) M', N, U', None)\<close>
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
    \<open>atm_of (lit_of (M' ! m)) \<in> atms_of_mm N\<close>
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

      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (?S m) (?S (Suc m))\<close>
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
        have C_N_U: \<open>C \<in># N + U'\<close>
          using learned kept unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def Sk
            k_def[symmetric] cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
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

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_stgy_new_learned_in_all_simple_clss:
  assumes
    st: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S\<close> and
    invR: \<open>cdcl\<^sub>W_all_struct_inv R\<close>
  shows \<open>set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (init_clss S))\<close>
proof
  fix C
  assume C: \<open>C \<in># learned_clss S\<close>
  have invS: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
    using rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv[OF st invR] .
  then have dist: \<open>distinct_cdcl\<^sub>W_state S\<close> and alien: \<open>no_strange_atm S\<close>
    unfolding cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>atms_of C \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien C unfolding no_strange_atm_def
    by (auto dest!: multi_member_split)
  moreover have \<open>distinct_mset C\<close>
    using dist C unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by (auto dest: in_diffD)
  moreover have \<open>\<not> tautology C\<close>
    using invS C unfolding cdcl\<^sub>W_all_struct_inv_def
    by (auto dest: in_diffD)
  ultimately show \<open>C \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    unfolding simple_clss_def
    by clarify
qed

end
