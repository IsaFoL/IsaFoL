theory CDCL_W_Abstract_State
imports CDCL_W_Full CDCL_W_Restart

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
     (auto simp: cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step simp del: init_state.simps)

end
