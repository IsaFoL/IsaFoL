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


lemma theory_entails_conflicting_clss:
  assumes \<open>theory S \<Turnstile>\<^sub>\<T>\<^sub>s init_clss S\<close>
  shows \<open>theory S \<Turnstile>\<^sub>\<T>\<^sub>s (init_clss S + conflicting_clss S)\<close>
proof -
  have \<open>theory S \<Turnstile>\<^sub>\<T>\<^sub>s (init_clss S + N)\<close> if \<open>set_mset N \<subseteq> set_mset (conflicting_clss S)\<close> for N
    using that
    by (induction N)
      (auto simp: assms conflicting_clss_def theory_entailed_clauses_def
        dest: mset_subset_eq_insertD intro!: entail_mono)
  from this[of \<open>conflicting_clss S\<close>] show ?thesis
    by auto
qed

find_theorems \<open>add_mset _ _ \<subseteq># _\<close>
lemma full_cdcl_T:
  assumes
    full: "full cdcl_bnb_stgy S T" and
    inv_s: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)" and
    inv: "cdcl_bnb_stgy_inv S" and
    learned_entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    th: \<open>theory S \<Turnstile>\<^sub>\<T>\<^sub>s init_clss S\<close>
  shows "(\<forall>I. consistent_interp I \<longrightarrow> atm_of ` I = atms_of_mm (init_clss S) \<longrightarrow> \<not>I \<Turnstile>\<^sub>\<T> theory S)
    \<or> lits_of_l (trail T) \<Turnstile>\<^sub>\<T> theory T" (is ?T)
proof -
  have nsc: \<open>no_step conflict_opt T\<close> and nsd: \<open>no_step decide T\<close> and st: \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close>
    using full unfolding full_def by (auto simp: cdcl_bnb_stgy.simps ocdcl\<^sub>W_o.simps
      dest: rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  have [simp]: \<open>init_clss T = init_clss S\<close>
    using rtranclp_cdcl_bnb_no_more_init_clss[OF st] ..
  have [simp]: \<open>theory T = theory S\<close>
    using rtranclp_cdcl_bnb_no_more_weight[OF st] ..
  have inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    by (metis inv_s rtranclp_cdcl_bnb_stgy_all_struct_inv st)
  consider
    \<open>conflicting T = Some {#}\<close> and \<open>unsatisfiable (set_mset (init_clss S + conflicting_clss S))\<close> |
    \<open>conflicting T = None\<close> and \<open>trail T \<Turnstile>asm init_clss S + conflicting_clss S\<close> and
      \<open>consistent_interp (lits_of_l (trail T))\<close> and
      \<open>satisfiable (set_mset (clauses S + conflicting_clss S))\<close>
     using full_cdcl_bnb_final_state_conclusive[OF assms(1-4)] by auto
   then show ?thesis
   proof cases
     case 2
     have no_confl: \<open>C \<in> simple_clss (atms_of_mm (init_clss S)) \<Longrightarrow>
        lits_of_l (trail T) \<Turnstile>s CNot C \<Longrightarrow> theory T \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> False\<close> for C
       using nsc by (auto simp: conflict_opt.simps conflicting_clss_def 2
         theory_entailed_clauses_def simple_clss_finite true_annots_true_cls)
     have \<open>consistent_interp (lits_of_l (trail T))\<close> and
       atms_trail: \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_mm (init_clss S)\<close>
       using inv_T atms_of_conflicting_clss[of T] unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
       by auto
     moreover have \<open>atm_of ` lits_of_l (trail T) = atms_of_mm (init_clss S)\<close>
       using nsd atms_trail apply (auto simp: decide.simps 2 lits_of_def image_image defined_lit_map)
       apply (drule_tac x= \<open>cons_trail (Decided (Pos x)) T\<close> in spec)
       apply (drule_tac x= \<open>Pos x\<close> in spec)
       apply auto
       done
     ultimately have \<open>lits_of_l (trail T) \<Turnstile>\<^sub>\<T> theory T\<close>
       using theory_model_found_or_conflict[of \<open>lits_of_l (trail T)\<close> \<open>(init_clss S + conflicting_clss S)\<close>
         \<open>theory T\<close>] 2
       by (auto simp: true_annots_true_cls dest: no_confl)
     then show ?thesis
       by auto
  next
    case 1
    then show ?thesis
      using theory_model_model_sat[of _ \<open>init_clss S + conflicting_clss S\<close> \<open>theory T\<close>]
        atms_of_conflicting_clss[of T] theory_entails_conflicting_clss[OF th]
      by auto
  qed
qed

end


end