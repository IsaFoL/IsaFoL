theory CDCL_W_Bound
  imports CDCL.CDCL_W_Abstract_State
begin

lemma satisfiable_union_entailed:
   \<open>A  \<Turnstile>ps B \<Longrightarrow> satisfiable A \<longleftrightarrow> satisfiable (A \<union> B)\<close>
  by (auto dest: satisfiable_decreasing)
    (metis satisfiable_carac sup.idem true_clss_clss_CNot_true_clss_cls_unsatisfiable true_clss_clss_def true_clss_clss_generalise_true_clss_clss true_clss_clss_insert)

text \<open>
  We here define a very abstract extension of CDCL: It is CDCL with additional conflicts coming
  from an (unspecified component). The idea started when working on the CDCL with branch-and-bounds,
  where the new conflicts are the ``bound'' part.

  The idea is that these additional clauses are entailed for an external reason (that is not
  important for the CDCL calculus). Conflicts arising from this set of clauses are not eagerly
  identified, but must be identified for total models.

\<close>

locale conflict_driven_clause_learning_with_adding_init_clause_bound\<^sub>W_no_state =
  state\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50) and
    state :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'a \<times> 'b\<close> and
    trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    init_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    learned_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    conflicting :: \<open>'st \<Rightarrow> 'v clause option\<close> and

    cons_trail :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    add_learned_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    update_conflicting :: \<open>'v clause option \<Rightarrow> 'st \<Rightarrow> 'st\<close> and

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close> +
  fixes
    conflicting_clauses :: \<open>'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses\<close> and
    weight :: \<open>'st \<Rightarrow> 'a\<close>
begin

definition additional_info' :: \<open>'st \<Rightarrow> 'b\<close> where
\<open>additional_info' S = (\<lambda>(_, _, _, _, _, D). D) (state S)\<close>

definition conflicting_clss :: \<open>'st \<Rightarrow> 'v literal multiset multiset\<close> where
\<open>conflicting_clss S = conflicting_clauses (init_clss S) (weight S)\<close>

text \<open>While it would more be natural to add an sublocale with the extended version clause set,
  this actually causes a loop in the hierarchy structure (although with different parameters).
  Therefore, adding theorems (e.g. defining an inductive predicate) causes a loop.
\<close>
definition abs_state
  :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lit list \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option\<close>
where
  \<open>abs_state S = (trail S, init_clss S + conflicting_clss S, learned_clss S,
    conflicting S)\<close>

end

locale conflict_driven_clause_learning_with_adding_init_clause_bound\<^sub>W_ops =
  conflict_driven_clause_learning_with_adding_init_clause_bound\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
      \<comment> \<open>Adding a clause:\<close>
    conflicting_clauses weight
  for
    state_eq :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>  'v clause option \<times>
      'a \<times> 'b" and
    trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    init_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    learned_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    conflicting :: \<open>'st \<Rightarrow> 'v clause option\<close> and

    cons_trail :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    add_learned_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    update_conflicting :: \<open>'v clause option \<Rightarrow> 'st \<Rightarrow> 'st\<close> and

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close> and
    conflicting_clauses :: \<open>'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses\<close> and
    weight :: \<open>'st \<Rightarrow> 'a\<close> +
  assumes
    state_prop':
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>
    and
    atms_of_conflicting_clss:
      \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close> and
    distinct_mset_mset_conflicting_clss:
      \<open>distinct_mset_mset (conflicting_clss S)\<close>
begin

paragraph \<open>Conversion to CDCL\<close>
sublocale conflict_driven_clause_learning\<^sub>W where
  state_eq = state_eq and
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
  apply unfold_locales
  unfolding additional_info'_def additional_info_def by (auto simp: state_prop')

paragraph \<open>Overall simplification on states\<close>
declare reduce_trail_to_skip_beginning[simp]

lemma state_eq_weight[state_simp, simp]: \<open>S \<sim> T \<Longrightarrow> weight S = weight T\<close>
  apply (drule state_eq_state)
  apply (subst (asm) state_prop')+
  by simp


lemma conflicting_clause_state_eq[state_simp, simp]:
  \<open>S \<sim> T \<Longrightarrow> conflicting_clss S = conflicting_clss T\<close>
  unfolding conflicting_clss_def by simp

lemma
  weight_cons_trail[simp]:
    \<open>weight (cons_trail L S) = weight S\<close> and
  weight_update_conflicting[simp]:
    \<open>weight (update_conflicting C S) = weight S\<close> and
  weight_tl_trail[simp]:
    \<open>weight (tl_trail S) = weight S\<close> and
  weight_add_learned_cls[simp]:
    \<open>weight (add_learned_cls D S) = weight S\<close>
  using cons_trail[of S _ _ L] update_conflicting[of S] tl_trail[of S] add_learned_cls[of S]
  by (auto simp: state_prop')

lemma
  conflicting_clss_cons_trail[simp]: \<open>conflicting_clss (cons_trail K S) = conflicting_clss S\<close> and
  conflicting_clss_tl_trail[simp]: \<open>conflicting_clss (tl_trail S) = conflicting_clss S\<close> and
  conflicting_clss_add_learned_cls[simp]:
    \<open>conflicting_clss (add_learned_cls D S) = conflicting_clss S\<close> and
  conflicting_clss_update_conflicting[simp]:
    \<open>conflicting_clss (update_conflicting E S) = conflicting_clss S\<close>
  unfolding conflicting_clss_def by auto

lemma conflicting_abs_state_conflicting[simp]:
    \<open>CDCL_W_Abstract_State.conflicting (abs_state S) = conflicting S\<close> and
  clauses_abs_state[simp]:
    \<open>cdcl\<^sub>W_restart_mset.clauses (abs_state S) = clauses S + conflicting_clss S\<close> and
  abs_state_tl_trail[simp]:
    \<open>abs_state (tl_trail S) = CDCL_W_Abstract_State.tl_trail (abs_state S)\<close> and
  abs_state_add_learned_cls[simp]:
    \<open>abs_state (add_learned_cls C S) = CDCL_W_Abstract_State.add_learned_cls C (abs_state S)\<close> and
  abs_state_update_conflicting[simp]:
    \<open>abs_state (update_conflicting D S) = CDCL_W_Abstract_State.update_conflicting D (abs_state S)\<close>
  by (auto simp: conflicting.simps abs_state_def cdcl\<^sub>W_restart_mset.clauses_def
    init_clss.simps learned_clss.simps clauses_def tl_trail.simps
    add_learned_cls.simps update_conflicting.simps)

lemma sim_abs_state_simp: \<open>S \<sim> T \<Longrightarrow> abs_state S = abs_state T\<close>
  by (auto simp: abs_state_def)

lemma additional_info_weight_additional_info': \<open>additional_info S = (weight S, additional_info' S)\<close>
  using state_prop[of S] state_prop'[of S] by auto

lemma
  weight_reduce_trail_to[simp]: \<open>weight (reduce_trail_to M S) = weight S\<close> and
  additional_info'_reduce_trail_to[simp]: \<open>additional_info' (reduce_trail_to M S) = additional_info' S\<close>
  using additional_info_reduce_trail_to[of M S] unfolding additional_info_weight_additional_info'
  by auto

lemma conflicting_clss_reduce_trail_to[simp]:
  \<open>conflicting_clss (reduce_trail_to M S) = conflicting_clss S\<close>
  unfolding conflicting_clss_def by auto

lemma trail_trail [simp]:
  \<open>CDCL_W_Abstract_State.trail (abs_state S) = trail S\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma [simp]:
  \<open>CDCL_W_Abstract_State.trail (cdcl\<^sub>W_restart_mset.reduce_trail_to M (abs_state S)) =
     trail (reduce_trail_to M S)\<close>
  by (auto simp: trail_reduce_trail_to_drop
    cdcl\<^sub>W_restart_mset.trail_reduce_trail_to_drop)

lemma abs_state_cons_trail[simp]:
    \<open>abs_state (cons_trail K S) = CDCL_W_Abstract_State.cons_trail K (abs_state S)\<close> and
  abs_state_reduce_trail_to[simp]:
    \<open>abs_state (reduce_trail_to M S) = cdcl\<^sub>W_restart_mset.reduce_trail_to M (abs_state S)\<close>
  subgoal by (auto simp: abs_state_def cons_trail.simps)
  subgoal by (induction rule: reduce_trail_to_induct)
       (auto simp: reduce_trail_to.simps cdcl\<^sub>W_restart_mset.reduce_trail_to.simps)
  done


lemma learned_clss_learned_clss[simp]:
    \<open>CDCL_W_Abstract_State.learned_clss (abs_state S) = learned_clss S\<close>
    \<open>CDCL_W_Abstract_State.init_clss (abs_state S) = init_clss S + conflicting_clss S\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma state_eq_init_clss_abs_state[state_simp, simp]:
  \<open>S \<sim> T \<Longrightarrow> CDCL_W_Abstract_State.init_clss (abs_state S) = CDCL_W_Abstract_State.init_clss (abs_state T)\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma
  init_clss_abs_state_update_conflicting[simp]:
    \<open>CDCL_W_Abstract_State.init_clss (abs_state (update_conflicting (Some D) S)) =
       CDCL_W_Abstract_State.init_clss (abs_state S)\<close> and
  init_clss_abs_state_cons_trail[simp]:
    \<open>CDCL_W_Abstract_State.init_clss (abs_state (cons_trail K S)) =
      CDCL_W_Abstract_State.init_clss (abs_state S)\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)


inductive conflict_opt :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S T :: 'st where
conflict_opt_rule:
  \<open>conflict_opt S T\<close>
  if
    \<open>C \<in># conflicting_clss S\<close>
    \<open>conflicting S = None\<close>
    \<open>trail S \<Turnstile>as CNot C\<close>
    \<open>T \<sim> update_conflicting (Some C) (reduce_trail_wrt_clause C S)\<close>

inductive_cases conflict_optE: \<open>conflict_opt S T\<close>

lemma cut_trail_wrt_clause_simps[simp]:
    \<open>conflicting_clss (cut_trail_wrt_clause C M S) = conflicting_clss S\<close>
  by (induction C M S rule: cut_trail_wrt_clause.induct; auto)

lemma weight_cut_trail_wrt_clause[simp]: \<open>weight (cut_trail_wrt_clause C M S) = weight S\<close>
  by (induction C M S rule: cut_trail_wrt_clause.induct)
    auto

lemma reduce_trail_wrt_clause_simps[simp]:
  \<open>conflicting_clss (reduce_trail_wrt_clause C S) = conflicting_clss S\<close>
  \<open>init_clss (reduce_trail_wrt_clause C S) = init_clss S\<close>
  \<open>learned_clss (reduce_trail_wrt_clause C S) = learned_clss S\<close>
  \<open>clauses (reduce_trail_wrt_clause C S) = clauses S\<close>
  \<open>weight (reduce_trail_wrt_clause C S) = weight S\<close>
  by (auto simp: reduce_trail_wrt_clause_def)

lemma ISABELLE_WTF: \<open>n \<le> n - Suc m \<longleftrightarrow> n = 0\<close>
  by auto
lemma update_conflicting_cut_trail_wrt_clause:
   \<open>CDCL_W_Abstract_State.update_conflicting D
     (cdcl\<^sub>W_restart_mset.cut_trail_wrt_clause C M
       (M, N, U, D')) =
    (CDCL_W_Abstract_State.trail (cdcl\<^sub>W_restart_mset.cut_trail_wrt_clause C M
       (M, N, U, D')), N, U, D)\<close>
   by (induction C M \<open>(M, N, U, D')\<close> rule: cdcl\<^sub>W_restart_mset.cut_trail_wrt_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset_state)

lemma cdcl\<^sub>W_restart_mset_cut_trail_wrt_clause_state_cut_trail_wrt:
    \<open>(cdcl\<^sub>W_restart_mset.cut_trail_wrt_clause C (trail S)
       (trail S, init_clss S + conflicting_clss S, learned_clss S, conflicting S)) =
    abs_state (cut_trail_wrt_clause C (trail S) S)\<close>
  apply (induction C \<open>trail S\<close> \<open>(trail S, init_clss S + conflicting_clss S, learned_clss S, conflicting S)\<close>
    arbitrary: S rule: cdcl\<^sub>W_restart_mset.cut_trail_wrt_clause.induct)
  subgoal by (auto simp: abs_state_def reduce_trail_wrt_clause_def)[]
  subgoal premises p for C L M S
    using p(1)[of \<open>tl_trail S\<close>] p(2-)
    by (auto simp: cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>trail S\<close>] abs_state_def)
  subgoal premises p for C L _ M S
    using p(1)[of \<open>tl_trail S\<close>] p(2-)
    by (auto simp: cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>trail S\<close>] abs_state_def)
  done

lemma cdcl\<^sub>W_restart_mset_reduce_trail_wrt_clause_reduce_trail_wrt_clause:
   \<open>cdcl\<^sub>W_restart_mset.reduce_trail_wrt_clause C
         (trail S, init_clss S + conflicting_clss S, learned_clss S, conflicting S) =
    (trail (reduce_trail_wrt_clause C S),
         init_clss S + conflicting_clss S, learned_clss S, Some C)\<close>
  unfolding cdcl\<^sub>W_restart_mset.reduce_trail_wrt_clause_def cdcl\<^sub>W_restart_mset_state
  by (auto simp: cdcl\<^sub>W_restart_mset_state update_conflicting_cut_trail_wrt_clause
   cdcl\<^sub>W_restart_mset_cut_trail_wrt_clause_state_cut_trail_wrt reduce_trail_wrt_clause_def)
    (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma conflict_opt_cdcl\<^sub>W_OOO_conflict:
   \<open>conflict_opt S T \<Longrightarrow>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_OOO_conflict (abs_state S) (abs_state T)\<close>
   using cdcl\<^sub>W_restart_mset_reduce_trail_wrt_clause_reduce_trail_wrt_clause[of _ S]
  by (auto simp: conflict_opt.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_OOO_conflict.simps)
    (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state_eq_eq
    cdcl\<^sub>W_restart_mset_reduce_trail_wrt_clause_reduce_trail_wrt_clause)

lemma conflict_opt_cdcl\<^sub>W_all_struct_inv:
  assumes \<open>conflict_opt S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using conflict_opt_cdcl\<^sub>W_OOO_conflict[OF assms(1)]
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_OOO_conflict_all_struct_invs inv by blast

lemma conflict_opt_no_smaller_conflict:
  assumes \<open>conflict_opt S T\<close> and  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>conflict_is_false_with_level T\<close>
    using conflict_opt_cdcl\<^sub>W_OOO_conflict[OF assms(1)] assms(2-)
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_OOO_conflict_conflict_is_false_with_level[of \<open>abs_state S\<close>
      \<open>abs_state T\<close>]
   by auto

fun no_confl_prop_impr :: \<open>'st \<Rightarrow> bool\<close> where
  \<open>no_confl_prop_impr S \<longleftrightarrow> no_step propagate S \<and> no_step conflict S\<close>

text \<open>We use a slighlty generalised form of backtrack to make conflict clause minimisation possible.\<close>
inductive obacktrack :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
obacktrack_rule: \<open>
  conflicting S = Some (add_mset L D) \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
  get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
  get_level (trail S) K = i + 1 \<Longrightarrow>
  D' \<subseteq># D \<Longrightarrow>
  clauses S + conflicting_clss S \<Turnstile>pm add_mset L D' \<Longrightarrow>
  T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S))) \<Longrightarrow>
  obacktrack S T\<close>

inductive_cases obacktrackE: \<open>obacktrack S T\<close>

inductive cdcl_bnb_bj :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
skip: \<open>skip S S' \<Longrightarrow> cdcl_bnb_bj S S'\<close> |
resolve: \<open>resolve S S' \<Longrightarrow> cdcl_bnb_bj S S'\<close> |
backtrack: \<open>obacktrack S S' \<Longrightarrow> cdcl_bnb_bj S S'\<close>

inductive_cases cdcl_bnb_bjE: \<open>cdcl_bnb_bj S T\<close>

inductive ocdcl\<^sub>W_o :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
decide: \<open>decide S S' \<Longrightarrow> ocdcl\<^sub>W_o S S'\<close> |
bj: \<open>cdcl_bnb_bj S S' \<Longrightarrow> ocdcl\<^sub>W_o S S'\<close>

inductive cdcl_bnb :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_conflict: \<open>conflict S S' \<Longrightarrow> cdcl_bnb S S'\<close> |
cdcl_propagate: \<open>propagate S S' \<Longrightarrow> cdcl_bnb S S'\<close> |
cdcl_conflict_opt: \<open>conflict_opt S S' \<Longrightarrow> cdcl_bnb S S'\<close> |
cdcl_other': \<open>ocdcl\<^sub>W_o S S' \<Longrightarrow> cdcl_bnb S S'\<close>

inductive cdcl_bnb_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_bnb_conflict: \<open>conflict S S' \<Longrightarrow> cdcl_bnb_stgy S S'\<close> |
cdcl_bnb_propagate: \<open>propagate S S' \<Longrightarrow> cdcl_bnb_stgy S S'\<close> |
cdcl_bnb_conflict_opt: \<open>conflict_opt S S' \<Longrightarrow> cdcl_bnb_stgy S S'\<close> |
cdcl_bnb_other': \<open>ocdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_bnb_stgy S S'\<close>

lemma cdcl_bnb_stgy_cdcl_bnb: \<open>cdcl_bnb_stgy S T \<Longrightarrow> cdcl_bnb S T\<close>
  by (auto simp: cdcl_bnb_stgy.simps cdcl_bnb.simps)

lemma rtranclp_cdcl_bnb_stgy_cdcl_bnb: \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bnb\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_bnb_stgy_cdcl_bnb)

lemma ocdcl\<^sub>W_o_induct[consumes 1, case_names decide skip resolve backtrack]:
  fixes S :: 'st
  assumes cdcl\<^sub>W_restart: \<open>ocdcl\<^sub>W_o S T\<close> and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow> undefined_lit (trail S) L  \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Decided L) S \<Longrightarrow>
      P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      conflicting S = Some E \<Longrightarrow>
      -L \<notin># E \<Longrightarrow> E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L E # M \<Longrightarrow>
      L \<in># E \<Longrightarrow>
      hd_trail S = Propagated L E \<Longrightarrow>
      conflicting S = Some D \<Longrightarrow>
      -L \<in># D \<Longrightarrow>
      get_maximum_level (trail S) ((remove1_mset (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting
        (Some (resolve_cls L D E)) (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>L D K i M1 M2 T D'.
      conflicting S = Some (add_mset L D) \<Longrightarrow>
      (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
      get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
      get_level (trail S) K = i+1 \<Longrightarrow>
      D' \<subseteq># D \<Longrightarrow>
      clauses S + conflicting_clss S \<Turnstile>pm add_mset L D' \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (add_mset L D'))
            (reduce_trail_to M1
              (add_learned_cls (add_mset L D')
                (update_conflicting None S))) \<Longrightarrow>
       P S T"
  shows \<open>P S T\<close>
  using cdcl\<^sub>W_restart apply (induct T rule: ocdcl\<^sub>W_o.induct)
  subgoal using assms(2) by (auto elim: decideE; fail)
  subgoal apply (elim cdcl_bnb_bjE skipE resolveE obacktrackE)
    apply (frule skipH; simp; fail)
    apply (cases \<open>trail S\<close>; auto elim!: resolveE intro!: resolveH; fail)
    apply (frule backtrackH; simp; fail)
    done
  done

lemma obacktrack_backtrackg: \<open>obacktrack S T \<Longrightarrow> backtrackg S T\<close>
  unfolding obacktrack.simps backtrackg.simps
  by blast


subsubsection \<open>Pluging into normal CDCL\<close>

lemma cdcl_bnb_no_more_init_clss:
  \<open>cdcl_bnb S S' \<Longrightarrow> init_clss S = init_clss S'\<close>
  by (induction rule: cdcl_bnb.cases)
    (auto simp: conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps cdcl_bnb_bj.simps
      decide.simps)

lemma rtranclp_cdcl_bnb_no_more_init_clss:
  \<open>cdcl_bnb\<^sup>*\<^sup>* S S' \<Longrightarrow> init_clss S = init_clss S'\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: cdcl_bnb_no_more_init_clss)

lemma cdcl_bnb_no_more_weight:
  \<open>cdcl_bnb S S' \<Longrightarrow> weight S = weight S'\<close>
  by (induction rule: cdcl_bnb.cases)
    (auto simp: conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps cdcl_bnb_bj.simps
      decide.simps)

lemma rtranclp_cdcl_bnb_no_more_weight:
  \<open>cdcl_bnb\<^sup>*\<^sup>* S S' \<Longrightarrow> weight S = weight S'\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: cdcl_bnb_no_more_weight)

lemma conflict_conflict:
  \<open>conflict S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict (abs_state S) (abs_state T)\<close>
  by (induction rule: conflict.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.conflict_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)


lemma propagate_propagate:
  \<open>propagate S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.propagate (abs_state S) (abs_state T)\<close>
  by (induction rule: propagate.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.propagate_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
        true_annots_true_cls_def_iff_negation_in_model abs_state_def
        in_negate_trial_iff)

lemma decide_decide:
  \<open>decide S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.decide (abs_state S) (abs_state T)\<close>
  by (induction rule: decide.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.decide_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
        true_annots_true_cls_def_iff_negation_in_model abs_state_def
        in_negate_trial_iff)

lemma skip_skip:
  \<open>skip S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.skip (abs_state S) (abs_state T)\<close>
  by (induction rule: skip.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.skip_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
        true_annots_true_cls_def_iff_negation_in_model abs_state_def
        in_negate_trial_iff)

lemma resolve_resolve:
  \<open>resolve S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.resolve (abs_state S) (abs_state T)\<close>
  by (induction rule: resolve.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.resolve_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
        true_annots_true_cls_def_iff_negation_in_model abs_state_def
        in_negate_trial_iff)

lemma backtrack_backtrack:
  \<open>obacktrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (abs_state S) (abs_state T)\<close>
proof (induction rule: obacktrack.cases)
  case (obacktrack_rule L D K M1 M2 D' i T)
  have H: \<open>set_mset (init_clss S) \<union> set_mset (learned_clss S)
    \<subseteq> set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S)\<close>
    by auto
  have [simp]: \<open>cdcl\<^sub>W_restart_mset.reduce_trail_to M1
       (trail S, init_clss S + conflicting_clss S, add_mset D (learned_clss S), None) =
    (M1, init_clss S + conflicting_clss S, add_mset D (learned_clss S), None)\<close> for D
    using obacktrack_rule by (auto simp add: cdcl\<^sub>W_restart_mset_reduce_trail_to
        cdcl\<^sub>W_restart_mset_state)
  show ?case
    using obacktrack_rule
    by (auto intro!: cdcl\<^sub>W_restart_mset.backtrack.intros
        simp: cdcl\<^sub>W_restart_mset_state abs_state_def clauses_def cdcl\<^sub>W_restart_mset.clauses_def
          ac_simps)
qed

lemma ocdcl\<^sub>W_o_all_rules_induct[consumes 1, case_names decide backtrack skip resolve]:
  fixes S T :: 'st
  assumes
    \<open>ocdcl\<^sub>W_o S T\<close> and
    \<open>\<And>T. decide S T \<Longrightarrow> P S T\<close> and
    \<open>\<And>T. obacktrack S T \<Longrightarrow> P S T\<close> and
    \<open>\<And>T. skip S T \<Longrightarrow> P S T\<close> and
    \<open>\<And>T. resolve S T \<Longrightarrow> P S T\<close>
  shows \<open>P S T\<close>
  using assms by (induct T rule: ocdcl\<^sub>W_o.induct) (auto simp: cdcl_bnb_bj.simps)

lemma cdcl\<^sub>W_o_cdcl\<^sub>W_o:
  \<open>ocdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (abs_state S) (abs_state S')\<close>
  apply (induction rule: ocdcl\<^sub>W_o_all_rules_induct)
     apply (simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps decide_decide; fail)
    apply (blast dest: backtrack_backtrack)
   apply (blast dest: skip_skip)
  by (blast dest: resolve_resolve)

lemma cdcl_bnb_stgy_all_struct_inv:
  assumes \<open>cdcl_bnb S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms
proof (induction rule: cdcl_bnb.cases)
  case (cdcl_conflict S')
  then show ?case
    by (blast dest: conflict_conflict cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
next
  case (cdcl_propagate S')
  then show ?case
    by (blast dest: propagate_propagate cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
next
  case (cdcl_conflict_opt S')
  then show ?case
    using conflict_opt_cdcl\<^sub>W_all_struct_inv by blast
next
  case (cdcl_other' S')
  then show ?case
    by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other cdcl\<^sub>W_o_cdcl\<^sub>W_o)
qed

lemma rtranclp_cdcl_bnb_stgy_all_struct_inv:
  assumes \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms by induction (auto dest: cdcl_bnb_stgy_all_struct_inv)

definition cdcl_bnb_struct_invs :: \<open>'st \<Rightarrow> bool\<close> where
\<open>cdcl_bnb_struct_invs S \<longleftrightarrow>
   atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close>

lemma cdcl_bnb_cdcl_bnb_struct_invs:
  \<open>cdcl_bnb S T \<Longrightarrow> cdcl_bnb_struct_invs S \<Longrightarrow> cdcl_bnb_struct_invs T\<close>
  by (induction rule: cdcl_bnb.induct)
    (force simp: conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps
      cdcl_bnb_bj.simps decide.simps cdcl_bnb_struct_invs_def)+

lemma rtranclp_cdcl_bnb_cdcl_bnb_struct_invs:
  \<open>cdcl_bnb\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bnb_struct_invs S \<Longrightarrow> cdcl_bnb_struct_invs T\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_bnb_cdcl_bnb_struct_invs)


text \<open>The following does \<^emph>\<open>not\<close> hold, because we cannot guarantee the absence of conflict of
  smaller level after \<^term>\<open>improve\<close> and \<^term>\<open>conflict_opt\<close>.\<close>
lemma cdcl_bnb_all_stgy_inv:
  assumes \<open>cdcl_bnb S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (abs_state T)\<close>
  oops

lemma skip_conflict_is_false_with_level:
  assumes \<open>skip S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv:\<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof induction
  case (skip_rule L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  have conflicting: \<open>cdcl\<^sub>W_conflicting S\<close> and
    lev: \<open>cdcl\<^sub>W_M_level_inv S\<close>
    using struct_inv unfolding cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  obtain La where
    \<open>La \<in># D\<close> and
    \<open>get_level (Propagated L C' # M) La = backtrack_lvl S\<close>
    using skip_rule confl_inv by auto
  moreover {
    have \<open>atm_of La \<noteq> atm_of L\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have La: \<open>La = L\<close> using \<open>La \<in># D\<close> \<open>- L \<notin># D\<close>
        by (auto simp add: atm_of_eq_atm_of)
      have \<open>Propagated L C' # M \<Turnstile>as CNot D\<close>
        using conflicting tr_S D unfolding cdcl\<^sub>W_conflicting_def by auto
      then have \<open>-L \<in> lits_of_l M\<close>
        using \<open>La \<in># D\<close> in_CNot_implies_uminus(2)[of L D \<open>Propagated L C' # M\<close>] unfolding La
        by auto
      then show False using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def consistent_interp_def by auto
    qed
    then have \<open>get_level (Propagated L C' # M) La = get_level M La\<close> by auto
  }
  ultimately show ?case using D tr_S T by auto
qed

lemma propagate_conflict_is_false_with_level:
  assumes \<open>propagate S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv:\<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms by (induction rule: propagate.induct) auto

lemma cdcl\<^sub>W_o_conflict_is_false_with_level:
  assumes \<open>cdcl\<^sub>W_o S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv: \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  apply (rule cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of S T])
  subgoal using assms by auto
  subgoal using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using assms by auto
  subgoal using struct_inv unfolding distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using struct_inv unfolding cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  done

lemma cdcl\<^sub>W_o_no_smaller_confl:
  assumes \<open>cdcl\<^sub>W_o S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv: \<open>no_smaller_confl S\<close> and
    lev: \<open>conflict_is_false_with_level S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close>
  shows \<open>no_smaller_confl T\<close>
  apply (rule cdcl\<^sub>W_o_no_smaller_confl_inv[of S T])
  subgoal using assms by (auto dest!:cdcl\<^sub>W_o_cdcl\<^sub>W_o)[]
  subgoal using n_s by auto
  subgoal using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using lev by fast
  subgoal using confl_inv unfolding distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state clauses_def)
  done

declare cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def [simp del]

declare conflict_is_false_with_level_def[simp del]

lemma cdcl\<^sub>W_M_level_inv_cdcl\<^sub>W_M_level_inv[iff]:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S) = cdcl\<^sub>W_M_level_inv S\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state)

lemma obacktrack_state_eq_compatible:
  assumes
    bt: \<open>obacktrack S T\<close> and
    SS': \<open>S \<sim> S'\<close> and
    TT': \<open>T \<sim> T'\<close>
  shows \<open>obacktrack S' T'\<close>
proof -
  obtain D L K i M1 M2 D' where
    conf: \<open>conflicting S = Some (add_mset L D)\<close> and
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev: \<open>get_level (trail S) L = backtrack_lvl S\<close> and
    max: \<open>get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')\<close> and
    max_D: \<open>get_maximum_level (trail S) D' \<equiv> i\<close> and
    lev_K: \<open>get_level (trail S) K = Suc i\<close> and
    D'_D: \<open>D' \<subseteq># D\<close> and
    NU_DL: \<open>clauses S + conflicting_clss S \<Turnstile>pm add_mset L D'\<close> and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
                (reduce_trail_to M1
                  (add_learned_cls (add_mset L D')
                    (update_conflicting None S)))"
    using bt by (elim obacktrackE) force
  let ?D = \<open>add_mset L D\<close>
  let ?D' = \<open>add_mset L D'\<close>
  have D': \<open>conflicting S' = Some ?D\<close>
    using SS' conf by (cases \<open>conflicting S'\<close>) auto

  have T'_S: "T' \<sim> cons_trail (Propagated L ?D')
     (reduce_trail_to M1 (add_learned_cls ?D'
     (update_conflicting None S)))"
    using T TT' state_eq_sym state_eq_trans by blast
  have T': "T' \<sim> cons_trail (Propagated L ?D')
     (reduce_trail_to M1 (add_learned_cls ?D'
     (update_conflicting None S')))"
    apply (rule state_eq_trans[OF T'_S])
    by (auto simp: cons_trail_state_eq reduce_trail_to_state_eq add_learned_cls_state_eq
        update_conflicting_state_eq SS')
  show ?thesis
    apply (rule obacktrack_rule[of _ L D K M1 M2 D' i])
    subgoal by (rule D')
    subgoal using TT' decomp SS' by auto
    subgoal using lev TT'  SS' by auto
    subgoal using max TT' SS' by auto
    subgoal using max_D TT' SS' by auto
    subgoal using lev_K TT' SS' by auto
    subgoal by (rule D'_D)
    subgoal using NU_DL TT' SS' by auto
    subgoal by (rule T')
    done
qed

lemma ocdcl\<^sub>W_o_no_smaller_confl_inv:
  fixes S S' :: \<open>'st\<close>
  assumes
    \<open>ocdcl\<^sub>W_o S S'\<close> and
    n_s: \<open>no_step conflict S\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    max_lev: \<open>conflict_is_false_with_level S\<close> and
    smaller: \<open>no_smaller_confl S\<close>
  shows \<open>no_smaller_confl S'\<close>
  using assms(1,2) unfolding no_smaller_confl_def
proof (induct rule: ocdcl\<^sub>W_o_induct)
  case (decide L T) note confl = this(1) and undef = this(2) and T = this(4)
  have [simp]: \<open>clauses T = clauses S\<close>
    using T undef by auto
  show ?case
  proof (intro allI impI)
    fix M'' K M' Da
    assume \<open>trail T = M'' @ Decided K # M'\<close> and D: \<open>Da \<in># local.clauses T\<close>
    then have "trail S = tl M'' @ Decided K # M'
        \<or> (M'' = [] \<and> Decided K # M' = Decided L # trail S)"
      using T undef by (cases M'') auto
    moreover {
      assume \<open>trail S = tl M'' @ Decided K # M'\<close>
      then have \<open>\<not>M' \<Turnstile>as CNot Da\<close>
        using D T undef confl smaller unfolding no_smaller_confl_def smaller by fastforce
    }
    moreover {
      assume \<open>Decided K # M' = Decided L # trail S\<close>
      then have \<open>\<not>M' \<Turnstile>as CNot Da\<close> using smaller D confl T n_s by (auto simp: conflict.simps)
    }
    ultimately show \<open>\<not>M' \<Turnstile>as CNot Da\<close> by fast
  qed
next
  case resolve
  then show ?case using smaller max_lev unfolding no_smaller_confl_def by auto
next
  case skip
  then show ?case using smaller max_lev unfolding no_smaller_confl_def by auto
next
  case (backtrack L D K i M1 M2 T D') note confl = this(1) and decomp = this(2) and
    T = this(9)
  obtain c where M: \<open>trail S = c @ M2 @ Decided K # M1\<close>
    using decomp by auto

  show ?case
  proof (intro allI impI)
    fix M ia K' M' Da
    assume \<open>trail T = M' @ Decided K' # M\<close>
    then have \<open>M1 = tl M' @ Decided K' # M\<close>
      using T decomp lev by (cases M') (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
    let ?D' = \<open>add_mset L D'\<close>
    let ?S' = "(cons_trail (Propagated L ?D')
                  (reduce_trail_to M1 (add_learned_cls ?D' (update_conflicting None S))))"
    assume D: \<open>Da \<in># clauses T\<close>
    moreover{
      assume \<open>Da \<in># clauses S\<close>
      then have \<open>\<not>M \<Turnstile>as CNot Da\<close> using \<open>M1 = tl M' @ Decided K' # M\<close> M confl smaller
        unfolding no_smaller_confl_def by auto
    }
    moreover {
      assume Da: \<open>Da = add_mset L D'\<close>
      have \<open>\<not>M \<Turnstile>as CNot Da\<close>
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then have \<open>-L \<in> lits_of_l M\<close>
          unfolding Da by (simp add: in_CNot_implies_uminus(2))
        then have \<open>-L \<in> lits_of_l (Propagated L D # M1)\<close>
          using UnI2 \<open>M1 = tl M' @ Decided K' # M\<close>
          by auto
        moreover {
          have \<open>obacktrack S ?S'\<close>
            using obacktrack_rule[OF backtrack.hyps(1-8) T] obacktrack_state_eq_compatible[of S T S] T
            by force
          then have \<open>cdcl_bnb S ?S'\<close>
            by (auto dest!: cdcl_bnb_bj.intros ocdcl\<^sub>W_o.intros intro: cdcl_bnb.intros)
          then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state ?S')\<close>
            using cdcl_bnb_stgy_all_struct_inv[of S, OF _ lev] by fast
          then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state ?S')\<close>
            by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
          then have \<open>no_dup (Propagated L D # M1)\<close>
            using decomp lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
        }
        ultimately show False
          using Decided_Propagated_in_iff_in_lits_of_l defined_lit_map
          by (auto simp: no_dup_def)
      qed
    }
    ultimately show \<open>\<not>M \<Turnstile>as CNot Da\<close>
      using T decomp lev unfolding cdcl\<^sub>W_M_level_inv_def by fastforce
  qed
qed

lemma trail_cut_trail_wrt_clause_decomp:
   \<open>trail (cut_trail_wrt_clause C (trail S) S) = M' @ Decided K # M \<Longrightarrow>
    \<exists>M'. trail (S) = M' @ Decided K # M\<close>
  apply (induction C \<open>trail S\<close> S arbitrary: S rule: cut_trail_wrt_clause.induct)
  subgoal by auto
  subgoal premises p for C L M S T
    using p(1)[of \<open>tl_trail T\<close>] p(2-)
    by (auto simp: eq_commute[of \<open>_ # _\<close> \<open>trail _\<close>] eq_commute[of \<open>_ @ _ # _\<close> \<open>_ # _\<close>]
      split: if_splits)
  subgoal premises p for C L _ M S T
    using p(1)[of \<open>tl_trail T\<close>] p(2-)
    by (auto simp: eq_commute[of \<open>_ # _\<close> \<open>trail _\<close>] eq_commute[of \<open>_ @ _ # _\<close> \<open>_ # _\<close>]
      split: if_splits)
  done

lemma trail_reduce_trail_wrt_clause_decomp:
    \<open>trail (reduce_trail_wrt_clause C S) = M' @ Decided K # M \<Longrightarrow>
    \<exists>M'. trail (S) = M' @ Decided K # M\<close>
  by (auto simp: reduce_trail_wrt_clause_def dest: trail_cut_trail_wrt_clause_decomp)

lemma cdcl_bnb_stgy_no_smaller_confl:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>no_smaller_confl T\<close>
  using assms
proof (induction rule: cdcl_bnb_stgy.cases)
  case (cdcl_bnb_other' S')
  show ?case
    by (rule ocdcl\<^sub>W_o_no_smaller_confl_inv)
     (use cdcl_bnb_other' in \<open>auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def\<close>)
qed (auto intro: conflict_no_smaller_confl_inv propagate_no_smaller_confl_inv;
  auto simp: no_smaller_confl_def conflict_opt.simps dest!: trail_reduce_trail_wrt_clause_decomp)+

lemma ocdcl\<^sub>W_o_conflict_is_false_with_level_inv:
  assumes
    \<open>ocdcl\<^sub>W_o S S'\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv: \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level S'\<close>
  using assms(1,2)
proof (induct rule: ocdcl\<^sub>W_o_induct)
  case (resolve L C M D T) note tr_S = this(1) and confl = this(4) and LD = this(5) and T = this(7)

  have \<open>resolve S T\<close>
    using resolve.intros[of S L C D T] resolve
    by auto
  then have \<open>cdcl\<^sub>W_restart_mset.resolve (abs_state S) (abs_state T)\<close>
    by (simp add: resolve_resolve)
  moreover have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S)\<close>
    using confl_inv
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  ultimately have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state T)\<close>
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of \<open>abs_state S\<close> \<open>abs_state T\<close>]
    lev confl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)
  then show \<open>?case\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  have \<open>cdcl\<^sub>W_restart_mset.skip (abs_state S) (abs_state T)\<close>
     using skip.intros[of S L C' M D T] skip by (simp add: skip_skip)
  moreover have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S)\<close>
    using confl_inv
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  ultimately have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state T)\<close>
    using  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of \<open>abs_state S\<close> \<open>abs_state T\<close>]
    lev confl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)
  then show \<open>?case\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev conflict_is_false_with_level_def)
qed (auto simp: conflict_is_false_with_level_def)


lemma cdcl_bnb_stgy_conflict_is_false_with_level:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof (induction rule: cdcl_bnb_stgy.cases)
  case (cdcl_bnb_conflict S')
  then show ?case
    using conflict_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_bnb_propagate S')
  then show ?case
    using propagate_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_bnb_conflict_opt S')
  then show ?case
    using conflict_opt_no_smaller_conflict by blast
next
  case (cdcl_bnb_other' S')
  show ?case
    apply (rule ocdcl\<^sub>W_o_conflict_is_false_with_level_inv)
    using cdcl_bnb_other' by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
qed

lemma decided_cons_eq_append_decide_cons: \<open>Decided L # MM = M' @ Decided K # M \<longleftrightarrow>
  (M' \<noteq> [] \<and> hd M' = Decided L \<and> MM = tl M' @ Decided K # M) \<or>
  (M' = [] \<and> L = K \<and> MM = M)\<close>
  by (cases M') auto

lemma either_all_false_or_earliest_decomposition:
  shows \<open>(\<forall>K K'. L = K' @ K \<longrightarrow> \<not>P K) \<or>
      (\<exists>L' L''. L = L'' @ L' \<and> P L' \<and> (\<forall>K K'. L' = K' @ K \<longrightarrow> K' \<noteq> [] \<longrightarrow> \<not>P K))\<close>
  apply (induction L)
  subgoal by auto
  subgoal for a
    by (metis append_Cons append_Nil list.sel(3) tl_append2)
  done

definition cdcl_bnb_stgy_inv :: \<open>'st \<Rightarrow> bool\<close> where
  \<open>cdcl_bnb_stgy_inv S \<longleftrightarrow> conflict_is_false_with_level S \<and> no_smaller_confl S\<close>

lemma cdcl_bnb_stgy_invD:
  shows \<open>cdcl_bnb_stgy_inv S \<longleftrightarrow> cdcl\<^sub>W_stgy_invariant S\<close>
  unfolding cdcl\<^sub>W_stgy_invariant_def cdcl_bnb_stgy_inv_def
  by auto

lemma cdcl_bnb_stgy_stgy_inv:
  \<open>cdcl_bnb_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bnb_stgy_inv S \<Longrightarrow> cdcl_bnb_stgy_inv T\<close>
  using cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant[of S T]
     cdcl_bnb_stgy_conflict_is_false_with_level cdcl_bnb_stgy_no_smaller_confl
  unfolding cdcl_bnb_stgy_inv_def
  by blast

lemma rtranclp_cdcl_bnb_stgy_stgy_inv:
  \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bnb_stgy_inv S \<Longrightarrow> cdcl_bnb_stgy_inv T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_bnb_stgy_stgy_inv rtranclp_cdcl_bnb_stgy_all_struct_inv
      rtranclp_cdcl_bnb_stgy_cdcl_bnb by blast
  done

lemma cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_bnb S T\<close> and
    entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
  using assms(1)
proof (induction rule: cdcl_bnb.cases)
  case (cdcl_conflict S')
  then show ?case
    using entailed
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        elim!: conflictE)
next
  case (cdcl_propagate S')
  then show ?case
    using entailed
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        elim!: propagateE)
next
  case (cdcl_other' S') note T = this(1) and o = this(2)
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed[of \<open>abs_state S\<close>])
    subgoal using o unfolding T by (blast dest: cdcl\<^sub>W_o_cdcl\<^sub>W_o cdcl\<^sub>W_restart_mset.other)
    subgoal using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
    subgoal using entailed by fast
    done
next
  case (cdcl_conflict_opt S')
  then show ?case
    using entailed
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def abs_state_def
         init_clss.simps learned_clss.simps
        elim!: conflict_optE)
qed

lemma rtranclp_cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and
    entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
  using assms by (induction rule: rtranclp_induct)
   (auto intro: cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init
      rtranclp_cdcl_bnb_stgy_all_struct_inv)

lemma atms_of_init_clss_conflicting_clss2[simp]:
  \<open>atms_of_mm (init_clss S) \<union> atms_of_mm (conflicting_clss S) = atms_of_mm (init_clss S)\<close>
  using atms_of_conflicting_clss[of S] by blast

lemma no_strange_atm_no_strange_atm[simp]:
  \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S) = no_strange_atm S\<close>
  using atms_of_conflicting_clss[of S]
  unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def no_strange_atm_def
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma cdcl\<^sub>W_conflicting_cdcl\<^sub>W_conflicting[simp]:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (abs_state S) = cdcl\<^sub>W_conflicting S\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_conflicting_def
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma distinct_cdcl\<^sub>W_state_distinct_cdcl\<^sub>W_state:
  \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (abs_state S) \<Longrightarrow> distinct_cdcl\<^sub>W_state S\<close>
  unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_cdcl\<^sub>W_state_def
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma obacktrack_imp_backtrack:
  \<open>obacktrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (abs_state S) (abs_state T)\<close>
  by (elim obacktrackE, rule_tac D=D and L=L and K=K in cdcl\<^sub>W_restart_mset.backtrack.intros)
    (auto elim!: obacktrackE simp: cdcl\<^sub>W_restart_mset.backtrack.simps sim_abs_state_simp)

lemma backtrack_imp_obacktrack:
  \<open>cdcl\<^sub>W_restart_mset.backtrack (abs_state S) T \<Longrightarrow> Ex (obacktrack S)\<close>
  by (elim cdcl\<^sub>W_restart_mset.backtrackE, rule exI,
       rule_tac D=D and L=L and K=K in obacktrack.intros)
    (auto simp: cdcl\<^sub>W_restart_mset.backtrack.simps obacktrack.simps)

lemma cdcl\<^sub>W_same_weight: \<open>cdcl\<^sub>W S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: cdcl\<^sub>W.induct)
    (auto simp: cdcl\<^sub>W.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
        skip.simps resolve.simps backtrack.simps)

lemma ocdcl\<^sub>W_o_same_weight: \<open>ocdcl\<^sub>W_o S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: ocdcl\<^sub>W_o.induct)
    (auto simp: cdcl\<^sub>W.simps cdcl_bnb_bj.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
        skip.simps resolve.simps obacktrack.simps)

lemma conflict_is_false_with_level_abs_iff:
  \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S) \<longleftrightarrow>
    conflict_is_false_with_level S\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
    conflict_is_false_with_level_def)

lemma decide_abs_state_decide:
  \<open>cdcl\<^sub>W_restart_mset.decide (abs_state S) T \<Longrightarrow> cdcl_bnb_struct_invs S \<Longrightarrow> Ex(decide S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.decide.cases, assumption)
  subgoal for L
    apply (rule exI)
    apply (rule decide.intros[of _ L])
    by (auto simp: cdcl_bnb_struct_invs_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  done

lemma cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W:
  assumes \<open>cdcl_bnb S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) (abs_state T) \<and> conflicting_clss S = {#}\<close>
  using assms
  by (auto simp: cdcl_bnb.simps conflict_opt.simps ocdcl\<^sub>W_o.simps
      cdcl_bnb_bj.simps
    dest: conflict_conflict propagate_propagate decide_decide skip_skip resolve_resolve
      backtrack_backtrack
    intro: cdcl\<^sub>W_restart_mset.W_conflict cdcl\<^sub>W_restart_mset.W_propagate cdcl\<^sub>W_restart_mset.W_other
    elim: conflictE propagateE decideE skipE resolveE obacktrackE)

lemma rtranclp_cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W:
  assumes \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* (abs_state S) (abs_state T) \<and> conflicting_clss S = {#}\<close>
  using assms
  by (induction rule: rtranclp_induct)
     (fastforce dest: cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W)+

lemma conflict_abs_ex_conflict_no_conflicting:
  assumes \<open>cdcl\<^sub>W_restart_mset.conflict (abs_state S) T\<close> and \<open>conflicting_clss S = {#}\<close>
  shows \<open>\<exists>T. conflict S T\<close>
  using assms by (auto simp: conflict.simps cdcl\<^sub>W_restart_mset.conflict.simps abs_state_def
    cdcl\<^sub>W_restart_mset_state clauses_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma propagate_abs_ex_propagate_no_conflicting:
  assumes \<open>cdcl\<^sub>W_restart_mset.propagate (abs_state S) T\<close> and \<open>conflicting_clss S = {#}\<close>
  shows \<open>\<exists>T. propagate S T\<close>
  using assms by (auto simp: propagate.simps cdcl\<^sub>W_restart_mset.propagate.simps abs_state_def
    cdcl\<^sub>W_restart_mset_state clauses_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_bnb_stgy S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S) (abs_state T)\<close>
proof -
  have \<open>conflicting_clss S = {#}\<close>
    using cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W[of S T] assms
    by (auto dest: cdcl_bnb_stgy_cdcl_bnb)
  then show ?thesis
    using assms
    by (auto 7 5 simp: cdcl_bnb_stgy.simps conflict_opt.simps ocdcl\<^sub>W_o.simps
        cdcl_bnb_bj.simps
      dest: conflict_conflict propagate_propagate decide_decide skip_skip resolve_resolve
        backtrack_backtrack
      dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
        conflict_abs_ex_conflict_no_conflicting
        propagate_abs_ex_propagate_no_conflicting
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros(3))
qed

lemma rtranclp_cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (abs_state S) (abs_state T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W[of T U, OF cdcl_bnb_stgy_cdcl_bnb]
    by (auto dest: cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy)
  done


lemma ocdcl\<^sub>W_o_no_smaller_propa:
  assumes \<open>ocdcl\<^sub>W_o S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close>
  shows \<open>no_smaller_propa T\<close>
  using assms(1)
proof cases
  case decide
  show ?thesis
    unfolding no_smaller_propa_def
  proof clarify
    fix M K M' D L
    assume
      tr: \<open>trail T = M' @ Decided K # M\<close> and
      D: \<open>D+{#L#} \<in># clauses T\<close> and
      undef: \<open>undefined_lit M L\<close> and
      M: \<open>M \<Turnstile>as CNot D\<close>
    then have \<open>Ex (propagate S)\<close>
      apply (cases M')
      using propagate_rule[of S \<open>D+{#L#}\<close> L \<open>cons_trail (Propagated L (D + {#L#})) S\<close>]
        smaller_propa decide
      by (auto simp: no_smaller_propa_def elim!: rulesE)
    then show False
      using n_s unfolding no_confl_prop_impr.simps by blast
  qed
next
  case bj
  then show ?thesis
  proof cases
    case skip
    then show ?thesis
      using assms no_smaller_propa_tl[of S T]
      by (auto simp: cdcl_bnb_bj.simps ocdcl\<^sub>W_o.simps obacktrack.simps elim!: rulesE)
  next
    case resolve
    then show ?thesis
      using assms no_smaller_propa_tl[of S T]
      by (auto simp: cdcl_bnb_bj.simps ocdcl\<^sub>W_o.simps obacktrack.simps elim!: rulesE)
  next
    case backtrack
    have inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
      using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv assms(1)
      using cdcl_bnb_stgy_all_struct_inv cdcl_other' by blast
    obtain D D' :: \<open>'v clause\<close> and K L :: \<open>'v literal\<close> and
      M1 M2 :: \<open>('v, 'v clause) ann_lit list\<close> and i :: nat where
      \<open>conflicting S = Some (add_mset L D)\<close> and
      decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
      \<open>get_level (trail S) L = backtrack_lvl S\<close> and
      \<open>get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')\<close> and
      i: \<open>get_maximum_level (trail S) D' \<equiv> i\<close> and
      lev_K: \<open>get_level (trail S) K = i + 1\<close> and
      D_D': \<open>D' \<subseteq># D\<close> and
      T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
          (reduce_trail_to M1
            (add_learned_cls (add_mset L D')
              (update_conflicting None S)))"
      using backtrack by (auto elim!: obacktrackE)
    let ?D' = \<open>add_mset L D'\<close>
    have [simp]: \<open>trail (reduce_trail_to M1 S) = M1\<close>
      using decomp by auto
    obtain M'' c where M'': \<open>trail S = M'' @ tl (trail T)\<close> and c: \<open>M'' = c @ M2 @ [Decided K]\<close>
      using decomp T by auto
    have M1: \<open>M1 = tl (trail T)\<close> and tr_T: \<open>trail T = Propagated L ?D' # M1\<close>
      using decomp T by auto
    have lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
      using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by auto
    then have lev_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state T)\<close>
      using inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by auto
    have n_d: \<open>no_dup (trail S)\<close>
      using lev_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: abs_state_def trail.simps)
    have n_d_T: \<open>no_dup (trail T)\<close>
      using lev_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: abs_state_def trail.simps)

    have i_lvl: \<open>i = backtrack_lvl T\<close>
      using no_dup_append_in_atm_notin[of \<open>c @ M2\<close> \<open>Decided K # tl (trail T)\<close> K]
      n_d lev_K unfolding c M'' by (auto simp: image_Un tr_T)

    from backtrack show ?thesis
      unfolding no_smaller_propa_def
    proof clarify
      fix M K' M' E' L'
      assume
        tr: \<open>trail T = M' @ Decided K' # M\<close> and
        E: \<open>E'+{#L'#} \<in># clauses T\<close> and
        undef: \<open>undefined_lit M L'\<close> and
        M: \<open>M \<Turnstile>as CNot E'\<close>
      have False if D: \<open>add_mset L D' = add_mset L' E'\<close> and M_D: \<open>M \<Turnstile>as CNot E'\<close>
      proof -
        have \<open>i \<noteq> 0\<close>
          using i_lvl tr T by auto
        moreover {
          have \<open>M1 \<Turnstile>as CNot D'\<close>
            using inv_T tr_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
            by (force simp: abs_state_def trail.simps conflicting.simps)
          then have \<open>get_maximum_level M1 D' = i\<close>
            using T i n_d D_D' unfolding M'' tr_T
            by (subst (asm) get_maximum_level_skip_beginning)
              (auto dest: defined_lit_no_dupD dest!: true_annots_CNot_definedD) }
        ultimately obtain L_max where
          L_max_in: \<open>L_max \<in># D'\<close> and
          lev_L_max: \<open>get_level M1 L_max = i\<close>
          using i get_maximum_level_exists_lit_of_max_level[of D' M1]
          by (cases D') auto
        have count_dec_M: \<open>count_decided M < i\<close>
          using T i_lvl unfolding tr by auto
        have \<open>- L_max \<notin> lits_of_l M\<close>
        proof (rule ccontr)
          assume \<open>\<not> ?thesis\<close>
          then have \<open>undefined_lit (M' @ [Decided K']) L_max\<close>
            using n_d_T unfolding tr
            by (auto dest: in_lits_of_l_defined_litD dest: defined_lit_no_dupD simp: atm_of_eq_atm_of)
          then have \<open>get_level (tl M' @ Decided K' # M) L_max < i\<close>
            apply (subst get_level_skip)
             apply (cases M'; auto simp add: atm_of_eq_atm_of lits_of_def; fail)
            using count_dec_M count_decided_ge_get_level[of M L_max] by auto
          then show False
            using lev_L_max tr unfolding tr_T by (auto simp: propagated_cons_eq_append_decide_cons)
        qed
        moreover have \<open>- L \<notin> lits_of_l M\<close>
        proof (rule ccontr)
          define MM where \<open>MM = tl M'\<close>
          assume \<open>\<not> ?thesis\<close>
          then have \<open>- L \<notin> lits_of_l (M' @ [Decided K'])\<close>
            using n_d_T unfolding tr by (auto simp: lits_of_def no_dup_def)
          have \<open>undefined_lit (M' @ [Decided K']) L\<close>
            apply (rule no_dup_uminus_append_in_atm_notin)
            using n_d_T \<open>\<not> - L \<notin> lits_of_l M\<close> unfolding tr by auto
          moreover have \<open>M' = Propagated L ?D' # MM\<close>
            using tr_T MM_def by (metis hd_Cons_tl propagated_cons_eq_append_decide_cons tr)
          ultimately show False
            by simp
        qed
        moreover have \<open>L_max \<in># D' \<or> L \<in># D'\<close>
          using D L_max_in by (auto split: if_splits)
        ultimately show False
          using M_D D by (auto simp: true_annots_true_cls true_clss_def add_mset_eq_add_mset)
      qed
      then show False
        using M'' smaller_propa tr undef M T E
        by (cases M') (auto simp: no_smaller_propa_def trivial_add_mset_remove_iff elim!: rulesE)
    qed
  qed
qed

lemma ocdcl\<^sub>W_no_smaller_propa:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close>
  shows \<open>no_smaller_propa T\<close>
  using assms
  apply (cases)
  subgoal by (auto)
  subgoal by (auto)
  subgoal by (auto elim!: conflict_optE simp: no_smaller_propa_def
     dest!: trail_reduce_trail_wrt_clause_decomp)
  subgoal using ocdcl\<^sub>W_o_no_smaller_propa by fast
  done


text \<open>Unfortunately, we cannot reuse the proof we have alrealy done.\<close>
lemma ocdcl\<^sub>W_no_relearning:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close> and
    dist: \<open>distinct_mset (clauses S)\<close>
  shows \<open>distinct_mset (clauses T)\<close>
  using assms(1)
proof cases
  case cdcl_bnb_conflict
  then show ?thesis using dist by (auto elim: rulesE)
next
  case cdcl_bnb_propagate
  then show ?thesis using dist by (auto elim: rulesE)
next
  case cdcl_bnb_conflict_opt
  then show ?thesis using dist by (auto elim: conflict_optE)
next
  case cdcl_bnb_other'
  then show ?thesis
  proof cases
    case decide
    then show ?thesis using dist by (auto elim: rulesE)
  next
    case bj
    then show ?thesis
    proof cases
      case skip
      then show ?thesis using dist by (auto elim: rulesE)
    next
      case resolve
      then show ?thesis using dist by (auto elim: rulesE)
    next
      case backtrack
      have smaller_propa: \<open>\<And>M K M' D L.
        trail S = M' @ Decided K # M \<Longrightarrow>
        D + {#L#} \<in># clauses S \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
        using smaller_propa unfolding no_smaller_propa_def by fast
      have inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
        using inv
        using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv assms(1)
        using cdcl_bnb_stgy_all_struct_inv cdcl_other' backtrack ocdcl\<^sub>W_o.intros
        cdcl_bnb_bj.intros
        by blast
      then have n_d: \<open>no_dup (trail T)\<close> and
        ent: \<open>\<And>L mark a b.
          a @ Propagated L mark # b = trail T \<Longrightarrow>
           b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
           cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp: abs_state_def trail.simps)
      show ?thesis
      proof (rule ccontr)
        assume H: \<open>\<not>?thesis\<close>
        obtain D D' :: \<open>'v clause\<close> and K L :: \<open>'v literal\<close> and
          M1 M2 :: \<open>('v, 'v clause) ann_lit list\<close> and i :: nat where
          \<open>conflicting S = Some (add_mset L D)\<close> and
          decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
          \<open>get_level (trail S) L = backtrack_lvl S\<close> and
          \<open>get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')\<close> and
          i: \<open>get_maximum_level (trail S) D' \<equiv> i\<close> and
          lev_K: \<open>get_level (trail S) K = i + 1\<close> and
          D_D': \<open>D' \<subseteq># D\<close> and
          T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
              (reduce_trail_to M1
                (add_learned_cls (add_mset L D')
                  (update_conflicting None S)))"
          using backtrack by (auto elim!: obacktrackE)
        from H T dist have LD': \<open>add_mset L D' \<in># clauses S\<close>
          by auto
        have \<open>\<not>M1 \<Turnstile>as CNot D'\<close>
          using get_all_ann_decomposition_exists_prepend[OF decomp] apply (elim exE)
          by (rule smaller_propa[of \<open>_ @ M2\<close> K M1 D' L])
            (use n_d T decomp LD' in auto)
        moreover have \<open>M1 \<Turnstile>as CNot D'\<close>
          using ent[of \<open>[]\<close> L \<open>add_mset L D'\<close> M1] T decomp by auto
        ultimately show False
          ..
      qed
    qed
  qed
qed

lemma get_all_mark_of_propagated_reduce_trail_wrt_clause_subset:
  \<open>set (get_all_mark_of_propagated (trail (reduce_trail_wrt_clause C S))) \<subseteq>
  set (get_all_mark_of_propagated (trail S))\<close>
  apply (induction C \<open>trail S\<close> S arbitrary: S rule: cut_trail_wrt_clause.induct)
  subgoal by (auto simp: reduce_trail_wrt_clause_def)
  subgoal premises p for C L M S T
    using p(1)[of \<open>tl_trail T\<close>] p(2-)
    by (auto simp: eq_commute[of \<open>_ # _\<close> \<open>trail _\<close>] reduce_trail_wrt_clause_def
      split: if_splits)
  subgoal premises p for C L _ M S T
    using p(1)[of \<open>tl_trail T\<close>] p(2-)
    by (auto simp: eq_commute[of \<open>_ # _\<close> \<open>trail _\<close>] reduce_trail_wrt_clause_def
      split: if_splits)
  done

lemma cdcl_bnb_reasons_in_clauses:
  \<open>cdcl_bnb S T \<Longrightarrow> reasons_in_clauses S \<Longrightarrow> reasons_in_clauses T\<close>
  by (auto simp: cdcl_bnb.simps reasons_in_clauses_def ocdcl\<^sub>W_o.simps
        cdcl_bnb_bj.simps get_all_mark_of_propagated_tl_proped
    elim!: rulesE conflict_optE obacktrackE
    dest!: in_set_tlD get_all_ann_decomposition_exists_prepend
      set_mp[OF get_all_mark_of_propagated_reduce_trail_wrt_clause_subset])

lemma no_step_cdcl_bnb_no_stop_cdcl:
  assumes ns: \<open>no_step cdcl_bnb S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows
    \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S)\<close>
proof -
  have nsd: \<open>no_step decide S\<close> and
     nsc: \<open>no_step conflict S\<close> \<open>no_step conflict_opt S\<close> and
     nso: \<open>no_step cdcl_bnb_bj S\<close> and
     nsb: \<open>no_step obacktrack S\<close>
    using ns by (auto simp: cdcl_bnb.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.simps ocdcl\<^sub>W_o.simps
     cdcl\<^sub>W_o.simps cdcl_bnb_bj.simps)
  then have nsd': \<open>\<And>L. conflicting S = None \<Longrightarrow> undefined_lit (trail S) L \<Longrightarrow>
    atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow> False\<close>
    using nsd by (auto simp: decide.simps)
  have nsc': \<open>no_step cdcl\<^sub>W_restart_mset.conflict (abs_state S)\<close>
    using nsc by (fastforce simp: conflict.simps conflict_opt.simps cdcl\<^sub>W_restart_mset.conflict.simps
      clauses_def dest!: multi_member_split)

  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close>
    using assms(2) unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+

  have \<open>atm_of L \<in> atms_of_mm (clauses S) \<Longrightarrow> defined_lit (trail S) (L)\<close>
      \<open>atm_of L \<in> atms_of_mm (conflicting_clss S) \<Longrightarrow> defined_lit (trail S) (L)\<close> 
   if \<open>conflicting S = None\<close> for L
    using nsd'[of \<open>L\<close>, simplified] alien atms_of_conflicting_clss[of S] that apply -
    by (cases \<open>undefined_lit (trail S) (L)\<close>; auto simp:  clauses_def atms_of_ms_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def dest!: multi_member_split;
      smt Un_iff UnionE imageE in_mono)+
  then have nsd':  \<open>no_step cdcl\<^sub>W_restart_mset.decide (abs_state S)\<close> and
     nsp': \<open>no_step cdcl\<^sub>W_restart_mset.propagate (abs_state S)\<close>
    using nsc' by (auto simp: cdcl_bnb.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.simps clauses_def
     cdcl\<^sub>W_restart_mset.decide.simps  cdcl\<^sub>W_restart_mset.propagate.simps dest!: multi_member_split)
  have \<open>no_step cdcl\<^sub>W_restart_mset.backtrack (abs_state S)\<close>
    using nsb by (auto 7 1 simp: cdcl\<^sub>W_restart_mset.backtrack.simps backtrack.simps
    obacktrack.simps)
  then have nso': \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (abs_state S)\<close>
   using nso nsd' by (auto 7 3 simp: cdcl_bnb_bj.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.skip.simps skip.simps
    cdcl\<^sub>W_restart_mset.resolve.simps resolve.simps all_conj_distrib)

  show \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S)\<close>
     using nsc' nso' nsd' nsp'
     by (auto simp: cdcl_bnb.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.simps)
  then have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S)\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.simps)
qed

lemma cdcl\<^sub>W_bnb_final_state_conclusive:
  assumes ns: \<open>no_step cdcl_bnb S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>cdcl_bnb_stgy_inv S\<close>
  shows
     \<open>conflicting S = Some {#} \<and>
      unsatisfiable (set_mset (cdcl\<^sub>W_restart_mset.clauses (abs_state S))) \<or>
      conflicting S = None \<and>
      trail S \<Turnstile>asm cdcl\<^sub>W_restart_mset.clauses (abs_state S)\<close>
proof -
  have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S)\<close>
     using no_step_cdcl_bnb_no_stop_cdcl[OF assms(1,2)] .
  then have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S)\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S)\<close>
    using assms(3) by (auto simp: cdcl_bnb_stgy_inv_def conflict_is_false_with_level_def
     cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def)
  ultimately show \<open>conflicting S = Some {#} \<and>
      unsatisfiable (set_mset (cdcl\<^sub>W_restart_mset.clauses (abs_state S))) \<or>
      conflicting S = None \<and>
      trail S \<Turnstile>asm cdcl\<^sub>W_restart_mset.clauses (abs_state S)\<close>
   using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_final_state_conclusive2[of \<open>abs_state S\<close>]
     assms(2) unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
   by auto
qed


lemma full_cdcl_bnb_inv_normal_form2:
  assumes
    full: "full cdcl_bnb_stgy S T" and
    inv_s: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)" and
    inv: "cdcl_bnb_stgy_inv S"
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (clauses T + conflicting_clss T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm cdcl\<^sub>W_restart_mset.clauses (abs_state T) \<and>
     consistent_interp (lits_of_l (trail T)) \<and>
     satisfiable (set_mset (clauses T + conflicting_clss T))" (is ?T)
proof -
  have \<open>no_step cdcl_bnb T\<close> and st: \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close>
    using full unfolding full_def
    by (auto simp: cdcl_bnb_stgy.simps cdcl_bnb.simps)
  moreover have st': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using st by (meson rtranclp_cdcl_bnb_stgy_all_struct_inv inv_s rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  moreover have \<open>cdcl_bnb_stgy_inv T\<close>
    using st inv inv_s rtranclp_cdcl_bnb_stgy_stgy_inv by blast
  moreover have \<open>consistent_interp (lits_of_l (trail T))\<close>
    using st' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  ultimately show ?thesis
    using cdcl\<^sub>W_bnb_final_state_conclusive[of T]
    by (auto dest: consistent_inter_true_annots_satisfiable)
qed

lemma full_cdcl_bnb_final_state_conclusive:
  assumes
    full: "full cdcl_bnb_stgy S T" and
    inv_s: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)" and
    inv: "cdcl_bnb_stgy_inv S" and
    learned_entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close>
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss S + conflicting_clss S))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss S + conflicting_clss S \<and>
     consistent_interp (lits_of_l (trail T)) \<and>
     satisfiable (set_mset (clauses S + conflicting_clss S))" (is ?T)
proof -
  have st: \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close>
    using rtranclp_cdcl_bnb_stgy_cdcl_bnb[of S T] assms unfolding full_def by auto
  have [simp]: \<open>init_clss T = init_clss S\<close>  \<open>conflicting_clss T = conflicting_clss S\<close>
    using rtranclp_cdcl_bnb_no_more_init_clss[OF st] rtranclp_cdcl_bnb_no_more_weight[OF st]
    by (auto simp: conflicting_clss_def)
  have learned_entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
    using inv_s learned_entailed rtranclp_cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init st by blast
  then have[iff]: \<open>satisfiable (set_mset (clauses T) \<union> set_mset (conflicting_clss S)) \<longleftrightarrow>
        satisfiable (set_mset (init_clss S) \<union> set_mset (conflicting_clss S))\<close>
    using satisfiable_union_entailed[of \<open>set_mset (init_clss S + conflicting_clss T)\<close>
       \<open>set_mset (learned_clss T)\<close>]
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
    by (auto simp: clauses_def ac_simps)

  have[iff]: \<open>satisfiable (set_mset (clauses S) \<union> set_mset (conflicting_clss S)) \<longleftrightarrow>
        satisfiable (set_mset (init_clss S) \<union> set_mset (conflicting_clss S))\<close>
    using satisfiable_union_entailed[of \<open>set_mset (init_clss S + conflicting_clss S)\<close>
       \<open>set_mset (learned_clss S)\<close>] assms
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
    by (auto simp: clauses_def ac_simps)

  consider
    \<open>conflicting T = Some {#}\<close> and \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close> |
    \<open>conflicting T = None\<close> and \<open>trail T \<Turnstile>asm cdcl\<^sub>W_restart_mset.clauses (abs_state T)\<close> and
      \<open>consistent_interp (lits_of_l (trail T))\<close> and \<open>satisfiable (set_mset (clauses T + conflicting_clss T))\<close>
    using full_cdcl_bnb_inv_normal_form2[OF assms(1-3)] by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
    by (auto simp:)
  next
    case 2
    then show ?thesis
      by (auto, auto simp: clauses_def)
  qed
qed
end

end