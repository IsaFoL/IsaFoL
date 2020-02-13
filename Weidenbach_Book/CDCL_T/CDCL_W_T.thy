theory CDCL_W_T
  imports CDCL_W_Bound Theory_Intf
begin

text \<open>The calculus here instantiate our CDCL with bounds with theories to define bounds.\<close>
locale conflict_driven_clause_learning_T =
  state\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state +
  theory_problem theory_entails_set theory_entails
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

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close> and
    theory_entails_set :: \<open>'a \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 90) and
    theory_entails :: \<open>'v literal set \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 90) +
  fixes
    "theory" :: \<open>'st \<Rightarrow> 'a\<close>
  assumes
    state_prop':
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>
begin

definition theory_entailed_clauses :: \<open>'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses\<close> where
\<open>theory_entailed_clauses N N\<^sub>\<T> =
   {#C \<in># mset_set (simple_clss (atms_of_mm N)).
      N\<^sub>\<T> \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}#}\<close>

sublocale conflict_driven_clause_learning_with_adding_init_clause_bound\<^sub>W_no_state where
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
  init_state = init_state and
  conflicting_clauses = theory_entailed_clauses and
  weight = "theory"
  by unfold_locales

lemma atms_of_conflicting_clss:
     \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close> and
   distinct_mset_mset_conflicting_clss:
    \<open>distinct_mset_mset (conflicting_clss S)\<close>
  unfolding conflicting_clss_def theory_entailed_clauses_def
  apply (auto simp: atms_of_ms_def simple_clss_finite distinct_mset_set_def)
  apply (auto simp: simple_clss_def)
  done

sublocale conflict_driven_clause_learning_with_adding_init_clause_bound\<^sub>W_ops where
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
  init_state = init_state and
  conflicting_clauses = theory_entailed_clauses and
  weight = "theory"
  by unfold_locales
    (simp_all add: atms_of_conflicting_clss state_prop' distinct_mset_mset_conflicting_clss)

sublocale conflict_driven_clause_learning_with_adding_init_clause_bound\<^sub>W_ops where
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
  init_state = init_state and
  conflicting_clauses = theory_entailed_clauses and
  weight = "theory"
  by unfold_locales
    (simp_all add: atms_of_conflicting_clss state_prop' distinct_mset_mset_conflicting_clss)

thm full_cdcl_bnb_final_state_conclusive
end


end