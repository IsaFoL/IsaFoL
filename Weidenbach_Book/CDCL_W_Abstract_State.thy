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


context conflict_driven_clause_learning\<^sub>W
begin

lemma no_step_skip_hd_in_conflicting:
  assumes
    inv_s: \<open>cdcl\<^sub>W_stgy_invariant S\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    ns: \<open>no_step skip S\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> \<open>conflicting S \<noteq> Some {#}\<close>
  shows \<open>-lit_of (hd (trail S)) \<in># the (conflicting S)\<close>
proof -
  let
    ?M = \<open>trail S\<close> and
    ?N = \<open>init_clss S\<close> and
    ?U = \<open>learned_clss S\<close> and
    ?k = \<open>backtrack_lvl S\<close> and
    ?D = \<open>conflicting S\<close>
  obtain D where D: \<open>?D = Some D\<close>
    using confl by (cases ?D) auto
  have M_D: \<open>?M \<Turnstile>as CNot D\<close>
    using inv D unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by auto
  then have tr: \<open>trail S \<noteq> []\<close>
    using confl D by auto
  obtain L M where M: \<open>?M = L # M\<close>
    using tr by (cases \<open>?M\<close>) auto
  have conlf_k: \<open>conflict_is_false_with_level S\<close>
    using inv_s unfolding cdcl\<^sub>W_stgy_invariant_def by simp
  then obtain L_k where
    L_k: \<open>L_k \<in># D\<close> and lev_L_k: \<open>get_level ?M L_k = ?k\<close>
    using confl D by auto
  have dec: \<open>?k = count_decided ?M\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  moreover {
    have \<open>no_dup ?M\<close>
      using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
    then have \<open>-lit_of L \<notin> lits_of_l M\<close>
      unfolding M by (auto simp: defined_lit_map lits_of_def uminus_lit_swap)
    }
  ultimately have L_D: \<open>lit_of L \<notin># D\<close>
    using M_D unfolding M by (auto simp add: true_annots_true_cls_def_iff_negation_in_model
        uminus_lit_swap)
  show ?thesis
  proof (cases L)
    case (Decided L') note L' = this(1)
    moreover have \<open>atm_of L' = atm_of L_k\<close>
      using lev_L_k count_decided_ge_get_level[of M L_k] unfolding M dec L'
      by (auto simp: get_level_cons_if split: if_splits)
    then have \<open>L' = -L_k\<close>
      using L_k L_D L' by (auto simp: atm_of_eq_atm_of)
    then show ?thesis using L_k unfolding D M L' by simp
  next
    case (Propagated L' C)
    then show ?thesis
      using ns confl by (auto simp: skip.simps M D)
  qed
qed

lemma
  fixes S
  assumes
     nss: \<open>no_step skip S\<close> and
     nsr: \<open>no_step resolve S\<close> and
     invs: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
     stgy: \<open>cdcl\<^sub>W_stgy_invariant S\<close> and
     confl: \<open>conflicting S \<noteq> None\<close> and
     confl': \<open>conflicting S \<noteq> Some {#}\<close>
  shows no_skip_no_resolve_single_highest_level:
    \<open>the (conflicting S) =
       add_mset (-(lit_of (hd (trail S)))) {#L \<in># the (conflicting S).
         get_level (trail S) L < local.backtrack_lvl S#}\<close> (is ?A) and
      no_skip_no_resolve_level_lvl_nonzero:
    \<open>0 < backtrack_lvl S\<close> (is ?B) and
      no_skip_no_resolve_level_get_maximum_lvl_le:
    \<open>get_maximum_level (trail S) (remove1_mset (-(lit_of (hd (trail S)))) (the (conflicting S)))
        < backtrack_lvl S\<close> (is ?C)
proof -
  define K where \<open>K \<equiv> lit_of (hd (trail S))\<close>
  have K: \<open>-K \<in># the (conflicting S)\<close>
    using no_step_skip_hd_in_conflicting[OF stgy invs nss confl confl']
    unfolding K_def .
  have
    \<open>no_strange_atm S\<close> and
    lev: \<open>cdcl\<^sub>W_M_level_inv S\<close> and
    \<open>\<forall>s\<in>#learned_clss S. \<not> tautology s\<close> and
    dist: \<open>distinct_cdcl\<^sub>W_state S\<close> and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    \<open>all_decomposition_implies_m (local.clauses S)
      (get_all_ann_decomposition (trail S))\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close>
    using invs unfolding cdcl\<^sub>W_all_struct_inv_def
    by auto

  obtain D where
    D[simp]: \<open>conflicting S = Some (add_mset (-K) D)\<close>
    using confl K by (auto dest: multi_member_split)

  have dist: \<open>distinct_mset (the (conflicting S))\<close>
    using dist confl unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have [iff]: \<open>L \<notin># remove1_mset L (the (conflicting S))\<close> for L
    by (meson distinct_mem_diff_mset union_single_eq_member)
  from this[of K] have [simp]: \<open>-K \<notin># D\<close> using dist by auto

  have nd: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have CNot: \<open>trail S \<Turnstile>as CNot (add_mset (-K) D)\<close>
    using conf unfolding cdcl\<^sub>W_conflicting_def
    by fastforce
  then have tr: \<open>trail S \<noteq> []\<close>
    by auto
  have [simp]: \<open>K \<notin># D\<close>
    using nd K_def tr CNot unfolding true_annots_true_cls_def_iff_negation_in_model
    by (cases \<open>trail S\<close>)
       (auto simp: uminus_lit_swap Decided_Propagated_in_iff_in_lits_of_l dest!: multi_member_split)
  have H1:
    \<open>0 < backtrack_lvl S\<close>
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis by simp
  next
    case proped: False
    have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      by simp
  qed
  show H2: ?C
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis by simp
  next
    case proped: False
    have \<open>get_maximum_level (tl (trail S)) D = get_maximum_level (trail S) D\<close>
      apply (rule get_maximum_level_cong)
      using K_def \<open>- K \<notin># D\<close> \<open>K \<notin># D\<close>
      apply (cases \<open>trail S\<close>)
      by (auto simp: get_level_cons_if atm_of_eq_atm_of)
    moreover have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    ultimately show ?thesis
      by (simp add: K_def)
  qed

  have H:
    \<open>get_level (trail S) L < local.backtrack_lvl S\<close>
    if \<open>L \<in># remove1_mset (-K) (the (conflicting S))\<close>
    for L
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K that proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      using get_maximum_level_ge_get_level[of L D M] that
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  next
    case proped: False
    have L_K: \<open>L \<noteq> - K\<close> \<open>-L \<noteq> K\<close> \<open>L \<noteq> -lit_of (hd (trail S))\<close>
      using that by (auto simp: uminus_lit_swap K_def[symmetric])
    have \<open>L \<noteq> lit_of (hd (trail S))\<close>
      using tr that K_def \<open>K \<notin># D\<close>
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)

    have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K that proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      using get_maximum_level_ge_get_level[of L D \<open>(trail S)\<close>] that tr L_K \<open>L \<noteq> lit_of (hd (trail S))\<close>
        count_decided_ge_get_level[of \<open>tl (trail S)\<close> L] proped
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  qed
  have [simp]: \<open>get_level (trail S) K = local.backtrack_lvl S\<close>
    using tr K_def
    by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
      (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  show ?A
    apply (rule distinct_set_mset_eq)
    subgoal using dist by auto
    subgoal using dist by (auto simp: distinct_mset_filter K_def[symmetric])
    subgoal using H by (auto simp: K_def[symmetric])
    done
  show ?B
    using H1 .
qed

end

end
