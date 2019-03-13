theory CDCL_W_Covering_Models
  imports CDCL_W_Optimal_Model
begin

section \<open>Covering Models\<close>

text \<open>I am only interested in the extension of CDCL to find covering mdoels, not in the required
subsequent extraction of the minimal covering models.\<close>

type_synonym 'v cov = \<open>'v literal multiset multiset\<close>

locale covering_models =
  fixes
    \<rho> :: \<open>'v \<Rightarrow> bool\<close>
begin

definition model_is_dominated :: \<open>'v literal multiset \<Rightarrow> 'v literal multiset \<Rightarrow> bool\<close> where
\<open>model_is_dominated M M' \<longleftrightarrow>
  filter_mset (\<lambda>L. is_pos L \<and> \<rho> (atm_of L)) M \<subseteq># filter_mset (\<lambda>L. is_pos L \<and> \<rho> (atm_of L)) M'\<close>

definition is_improving_int :: \<open>('v, 'v clause) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v cov \<Rightarrow> bool\<close> where
\<open>is_improving_int M M' N \<M> \<longleftrightarrow>
  (M = M' \<and> (\<forall>I \<in># \<M>. \<not>model_is_dominated (lit_of `# mset M) I)) \<and>
  total_over_m (lits_of_l M) (set_mset N) \<and>
  lit_of `# mset M \<in> simple_clss (atms_of_mm N) \<and>
  M \<Turnstile>asm N \<and>
  no_dup M\<close>

lemma model_is_dominated_refl: \<open>model_is_dominated I I\<close>
  by (auto simp: model_is_dominated_def)

lemma model_is_dominated_trans:
  \<open>model_is_dominated I J \<Longrightarrow> model_is_dominated J K \<Longrightarrow> model_is_dominated I K\<close>
  by (auto simp: model_is_dominated_def)

text \<open>This criteria is a bit more general than Weidenbach's version.\<close>
definition conflicting_clauses
  :: \<open>'v clauses \<Rightarrow> 'v cov \<Rightarrow> 'v clauses\<close>
where
  \<open>conflicting_clauses N w =
    {#C \<in># mset_set (simple_clss (atms_of_mm N)). pNeg `# w \<Turnstile>pm C#}\<close>

lemma pNeg_simple_clss_iff[simp]:
  \<open>pNeg M \<in> simple_clss N \<longleftrightarrow> M \<in> simple_clss N\<close>
  by (auto simp: simple_clss_def)

lemma conflicting_clauses_insert:
  assumes \<open>M \<in> simple_clss (atms_of_mm N)\<close>
  shows \<open>pNeg M \<in># conflicting_clauses N (add_mset M w)\<close>
  using assms by (auto simp: conflicting_clauses_def simple_clss_finite)

end

locale conflict_driven_clause_learning\<^sub>W_covering_models =
  conflict_driven_clause_learning\<^sub>W
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting
      \<comment> \<open>get state:\<close>
    init_state +
  covering_models \<rho>
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'v cov \<times> 'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and
    init_state :: "'v clauses \<Rightarrow> 'st" and
    \<rho> :: \<open>'v \<Rightarrow> bool\<close>  +
  fixes
    update_additional_info :: \<open>'v cov \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close>
  assumes
    update_additional_info:
      \<open>state S = (M, N, U, C, \<M>) \<Longrightarrow> state (update_additional_info K' S) = (M, N, U, C, K')\<close> and
    weight_init_state:
      \<open>\<And>N :: 'v clauses. fst (additional_info (init_state N)) = {#}\<close>
begin

definition update_weight_information :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
  \<open>update_weight_information M S =
    update_additional_info (add_mset (lit_of `# mset M) (fst (additional_info S)), snd (additional_info S)) S\<close>

lemma
  trail_update_additional_info[simp]: \<open>trail (update_additional_info w S) = trail S\<close> and
  init_clss_update_additional_info[simp]:
    \<open>init_clss (update_additional_info w S) = init_clss S\<close> and
  learned_clss_update_additional_info[simp]:
    \<open>learned_clss (update_additional_info w S) = learned_clss S\<close> and
  backtrack_lvl_update_additional_info[simp]:
    \<open>backtrack_lvl (update_additional_info w S) = backtrack_lvl S\<close> and
  conflicting_update_additional_info[simp]:
    \<open>conflicting (update_additional_info w S) = conflicting S\<close> and
  clauses_update_additional_info[simp]:
    \<open>clauses (update_additional_info w S) = clauses S\<close>
  using update_additional_info[of S] unfolding clauses_def
  by (subst (asm) state_prop; subst (asm) state_prop; auto; fail)+

lemma
  trail_update_weight_information[simp]:
    \<open>trail (update_weight_information w S) = trail S\<close> and
  init_clss_update_weight_information[simp]:
    \<open>init_clss (update_weight_information w S) = init_clss S\<close> and
  learned_clss_update_weight_information[simp]:
    \<open>learned_clss (update_weight_information w S) = learned_clss S\<close> and
  backtrack_lvl_update_weight_information[simp]:
    \<open>backtrack_lvl (update_weight_information w S) = backtrack_lvl S\<close> and
  conflicting_update_weight_information[simp]:
    \<open>conflicting (update_weight_information w S) = conflicting S\<close> and
  clauses_update_weight_information[simp]:
    \<open>clauses (update_weight_information w S) = clauses S\<close>
  using update_additional_info[of S] unfolding update_weight_information_def by auto

definition covering :: \<open>'st \<Rightarrow> 'v cov\<close> where
  \<open>covering S = fst (additional_info S)\<close>

lemma
  additional_info_update_additional_info[simp]:
  "additional_info (update_additional_info w S) = w"
  unfolding additional_info_def using update_additional_info[of S]
  by (cases \<open>state S\<close>; auto; fail)+

lemma
  covering_cons_trail2[simp]: \<open>covering (cons_trail L S) = covering S\<close> and
  clss_tl_trail2[simp]: "covering (tl_trail S) = covering S" and
  covering_add_learned_cls_unfolded:
    "covering (add_learned_cls U S) = covering S"
    and
  covering_update_conflicting2[simp]: "covering (update_conflicting D S) = covering S" and
  covering_remove_cls2[simp]:
    "covering (remove_cls C S) = covering S" and
  covering_add_learned_cls2[simp]:
    "covering (add_learned_cls C S) = covering S" and
  covering_update_covering_information2[simp]:
    "covering (update_weight_information M S) = add_mset (lit_of `# mset M) (covering S)"
  by (auto simp: update_weight_information_def covering_def)



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
  by unfold_locales

sublocale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_no_state
  where
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
    init_state = init_state and
    weight = covering and
    update_weight_information = update_weight_information and
    is_improving_int = is_improving_int and
    conflicting_clauses = conflicting_clauses
  by unfold_locales

lemma state_additional_info2':
  \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, covering S, additional_info' S)\<close>
  unfolding additional_info'_def by (cases \<open>state S\<close>; auto simp: state_prop covering_def)

lemma state_update_weight_information:
  \<open>state S = (M, N, U, C, w, other) \<Longrightarrow>
    \<exists>w'. state (update_weight_information T S) = (M, N, U, C, w', other)\<close>
  unfolding update_weight_information_def by (cases \<open>state S\<close>; auto simp: state_prop covering_def)


lemma conflicting_clss_incl_init_clss:
  \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close>
  unfolding conflicting_clss_def conflicting_clauses_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def atms_of_ms_def split: if_splits)

lemma conflict_clss_update_weight_no_alien:
  \<open>atms_of_mm (conflicting_clss (update_weight_information M S))
    \<subseteq> atms_of_mm (init_clss S)\<close>
  by (auto simp: conflicting_clss_def conflicting_clauses_def atms_of_ms_def
      cdcl\<^sub>W_restart_mset_state simple_clss_finite
    dest: simple_clssE)


lemma distinct_mset_mset_conflicting_clss2: \<open>distinct_mset_mset (conflicting_clss S)\<close>
  unfolding conflicting_clss_def conflicting_clauses_def distinct_mset_set_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def)


lemma total_over_m_atms_incl:
  assumes \<open>total_over_m M (set_mset N)\<close>
  shows
    \<open>x \<in> atms_of_mm N \<Longrightarrow> x \<in> atms_of_s M\<close>
  by (meson assms contra_subsetD total_over_m_alt_def)

lemma conflicting_clss_update_weight_information_in2:
  assumes \<open>is_improving M M' S\<close>
  shows \<open>negate_ann_lits M' \<in># conflicting_clss (update_weight_information M' S)\<close>
  using assms apply (auto simp: simple_clss_finite
    conflicting_clauses_def conflicting_clss_def is_improving_int_def)
  by (auto simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 simple_clss_def lits_of_def
      negate_ann_lits_pNeg_lit_of image_iff dest: total_over_m_atms_incl
      intro!: true_clss_cls_in)

lemma is_improving_conflicting_clss_update_weight_information: \<open>is_improving M M' S \<Longrightarrow>
       conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M' S)\<close>
  by (auto simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 le_less true_clss_cls_tautology_iff simple_clss_finite
      intro!: image_mset_subseteq_mono
      dest: simple_clssE
      split: enat.splits)

sublocale state\<^sub>W_no_state
  where
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
  by unfold_locales

sublocale state\<^sub>W_no_state where
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
  by unfold_locales

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
  by unfold_locales

sublocale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_ops
  where
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
    init_state = init_state and
    weight = covering and
    update_weight_information = update_weight_information and
    is_improving_int = is_improving_int and
    conflicting_clauses = conflicting_clauses
  apply unfold_locales
  subgoal by (rule state_additional_info2')
  subgoal by (rule state_update_weight_information)
  subgoal by (rule conflicting_clss_incl_init_clss)
  subgoal by (rule distinct_mset_mset_conflicting_clss2)
  subgoal by (rule is_improving_conflicting_clss_update_weight_information)
  subgoal by (rule conflicting_clss_update_weight_information_in2)
  done

definition covering_simple_clss where
  \<open>covering_simple_clss N S \<longleftrightarrow> (set_mset (covering S) \<subseteq> simple_clss (atms_of_mm N)) \<and>
     distinct_mset (covering S)\<close>

(*TODO Move*)
lemma (in -) distinct_mset_subset_iff_remdups:
  \<open>distinct_mset a \<Longrightarrow> a \<subseteq># b \<longleftrightarrow> a \<subseteq># remdups_mset b\<close>
  by (simp add: distinct_mset_inter_remdups_mset subset_mset.le_iff_inf)

lemma cdcl_bnb_covering_simple_clss:
  \<open>cdcl_bnb S T \<Longrightarrow> init_clss S = N \<Longrightarrow> covering_simple_clss N S \<Longrightarrow> covering_simple_clss N T\<close>
  by (auto simp: cdcl_bnb.simps covering_simple_clss_def is_improving_int_def
      model_is_dominated_refl ocdcl\<^sub>W_o.simps cdcl_bnb_bj.simps
    elim!: rulesE improveE conflict_optE obacktrackE
    dest!: multi_member_split[of _ \<open>covering S\<close>])

lemma wf_cdcl_bnb_fixed:
   \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bnb S T
       \<and> covering_simple_clss N S \<and> init_clss S = N}\<close>
  apply (rule wf_cdcl_bnb_with_additional_inv[of
     \<open>covering_simple_clss N\<close>
     N id \<open>{(T, S). (T, S) \<in> {(\<M>', \<M>). \<M> \<subset># \<M>' \<and> distinct_mset \<M>'
       \<and> set_mset \<M>' \<subseteq> simple_clss (atms_of_mm N)}}\<close>])
  subgoal
    by (auto simp: improvep.simps is_improving_int_def covering_simple_clss_def
         add_mset_eq_add_mset  model_is_dominated_refl
      dest!: multi_member_split)
  subgoal
    apply (rule wf_bounded_set[of _ \<open>\<lambda>_. simple_clss (atms_of_mm N)\<close> set_mset])
    apply (auto simp: distinct_mset_subset_iff_remdups[symmetric] simple_clss_finite
      simp flip: remdups_mset_def)
    by (metis distinct_mset_mono distinct_mset_set_mset_ident)
  subgoal
    by (rule cdcl_bnb_covering_simple_clss)
  done

end

end
