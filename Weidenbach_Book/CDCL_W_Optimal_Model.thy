theory CDCL_W_Optimal_Model
imports CDCL_W_Incremental CDCL_W_Abstract_State
begin

notation image_mset (infixr "`#" 90)

locale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_no_state =
  state\<^sub>W_adding_init_clause_no_state
    state_eq state
    \<comment> \<open>functions for the state: \<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
      \<comment> \<open>Adding a clause:\<close>
    add_init_cls
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'a \<times> 'b" and
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
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    add_additional_information :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    conflicting_clauses :: "'a \<Rightarrow> 'v clauses" and
    weight :: \<open>'st \<Rightarrow> 'a\<close>
  assumes
    state_add_additional_information: \<open>state (add_additional_information C S) = state S\<close> and
  weight_state_eq:
    \<open>S \<sim> T \<Longrightarrow> weight S = weight T\<close>
begin

definition additional_info' :: "'st \<Rightarrow> 'b" where
"additional_info' S = (\<lambda>(_, _, _, _, _, D). D) (state S)"

end
  
locale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_ops =
  conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions for the state: \<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
      \<comment> \<open>Adding a clause:\<close>
    add_init_cls add_additional_information conflicting_clauses weight
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>  'v clause option \<times>
      'a \<times> 'b" and
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
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_additional_information :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    conflicting_clauses :: "'a \<Rightarrow> 'v clauses" and
    weight :: \<open>'st \<Rightarrow> 'a\<close> +
  assumes
    state_prop[simp]:
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close> 
    and
    weight_update_conflicting[simp]:
       \<open>weight (update_conflicting C S) = weight S\<close>
begin

sublocale conflict_driven_clause_learning_with_adding_init_clause\<^sub>W
  apply unfold_locales
  unfolding additional_info'_def additional_info_def by auto

lemma weight_cons_trail: \<open>weight (cons_trail L S) = weight S\<close>
  using cons_trail[of S _ _ L] by auto

lemma add_additional_information_simp[simp]:
  \<open>trail (add_additional_information C S) = trail S\<close>
  \<open>init_clss (add_additional_information C S) = init_clss S\<close>
  \<open>learned_clss (add_additional_information C S) = learned_clss S\<close>
  \<open>clauses (add_additional_information C S) = clauses S\<close>
  \<open>backtrack_lvl (add_additional_information C S) = backtrack_lvl S\<close>
  \<open>conflicting (add_additional_information C S) = conflicting S\<close>
  using state_add_additional_information[of C S] by (auto simp: clauses_def)

definition negate_trail :: "'st \<Rightarrow> 'v literal multiset" where
  \<open>negate_trail S = (\<lambda>L. - lit_of L) `# (mset (trail S))\<close>

lemma atms_of_negate_trail[simp]: \<open>atms_of (negate_trail S) = atm_of ` (lits_of_l (trail S))\<close>
  unfolding negate_trail_def lits_of_def atms_of_def by (auto simp: image_image)

lemma distinct_image_mset_not_equal:
  assumes 
    LL': \<open>L \<noteq> L'\<close> and
    dist: \<open>distinct_mset (f `# M)\<close> and
    L: \<open>L \<in># M\<close> and
    L': \<open>L' \<in># M\<close> and
    fLL'[simp]: \<open>f L = f L'\<close>
  shows \<open>False\<close>
proof -
  obtain M1 where M1: \<open>M = add_mset L M1\<close>
    using multi_member_split[OF L] by blast
  obtain M2 where M2: \<open>M1 = add_mset L' M2\<close>
    using multi_member_split[of L' M1] LL' L' unfolding M1 by (auto simp: add_mset_eq_add_mset)  
  show False
    using dist unfolding M1 M2 by auto
qed

lemma no_dup_distinct_mset[intro!]:
  assumes n_d: \<open>no_dup (trail S)\<close>
  shows \<open>distinct_mset (negate_trail S)\<close>
  unfolding negate_trail_def no_dup_def
proof (subst distinct_image_mset_inj)
  show \<open>inj_on (\<lambda>L. - lit_of L) (set_mset (mset (trail S)))\<close>
    unfolding inj_on_def Ball_def
  proof (intro allI impI, rule ccontr)
    fix L L'
    assume 
      L: \<open>L \<in># mset (trail S)\<close> and
      L': \<open>L' \<in># mset (trail S)\<close> and
      lit: \<open>- lit_of L = - lit_of L'\<close> and
      LL': \<open>L \<noteq> L'\<close>
    have \<open>atm_of (lit_of L) = atm_of (lit_of L')\<close>
      using lit by auto
    moreover have \<open>atm_of (lit_of L) \<in># (\<lambda>l. atm_of (lit_of l)) `# mset (trail S)\<close>
      using L by auto
    moreover have \<open>atm_of (lit_of L') \<in># (\<lambda>l. atm_of (lit_of l)) `# mset (trail S)\<close>
      using L' by auto
    ultimately show False
      using assms LL' L L' unfolding distinct_mset_mset_distinct[symmetric] mset_map no_dup_def
      apply - apply (rule distinct_image_mset_not_equal[of L L' \<open>(\<lambda>l. atm_of (lit_of l))\<close>])
      by auto
  qed
next
  show \<open>distinct_mset (mset (trail S))\<close>
    using no_dup_imp_distinct[OF n_d] by simp
qed 

lemma in_negate_trial_iff: \<open>L \<in># negate_trail S \<longleftrightarrow> - L \<in> lits_of_l (trail S)\<close>
  unfolding negate_trail_def lits_of_def by (auto simp: uminus_lit_swap)

fun abs_state :: "'st
     \<Rightarrow> ('v, 'v literal multiset) ann_lit list \<times>
        'v literal multiset multiset \<times>
        'v literal multiset multiset \<times>
        'v literal multiset option" where
  \<open>abs_state S = (trail S, init_clss S + {#C. C \<in># conflicting_clauses (weight S)#}, learned_clss S, 
  conflicting S)\<close>

inductive conflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
conflict_opt_rule:
  \<open>conflict_opt S T\<close>
  if
    \<open>negate_trail S \<in># conflicting_clauses (weight S)\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_trail S)) S\<close>

text \<open>Do we also want to reduce the trail to M? to ensure minimum conflict?\<close>
inductive improve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
  "trail S = M' @ M \<Longrightarrow>
  M \<Turnstile>asm init_clss S \<Longrightarrow>
  conflicting S = None \<Longrightarrow>
  T \<sim> update_conflicting (Some (negate_trail S)) S \<Longrightarrow> 
  improve S (add_additional_information (lit_of `# mset M) S)"

lemma invs_add_additional_information[simp]:
  \<open>no_strange_atm (add_additional_information C S) = (no_strange_atm S)\<close>
  \<open>cdcl\<^sub>W_M_level_inv (add_additional_information C S) = cdcl\<^sub>W_M_level_inv S\<close>
  \<open>distinct_cdcl\<^sub>W_state (add_additional_information C S) = distinct_cdcl\<^sub>W_state S\<close>
  \<open>cdcl\<^sub>W_conflicting (add_additional_information C S) = cdcl\<^sub>W_conflicting S\<close>
  \<open>cdcl\<^sub>W_learned_clause (add_additional_information C S) = cdcl\<^sub>W_learned_clause S\<close>
  unfolding no_strange_atm_def cdcl\<^sub>W_M_level_inv_def distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def
    cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_all_struct_inv_def by auto

lemma \<open>negate_trail S \<in># conflicting_clauses (weight (add_additional_information C S))\<close>
  oops

lemma conflict_opt_cdcl\<^sub>W_all_struct_inv:
  assumes \<open>conflict_opt S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> 
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms
  by (induction rule: conflict_opt.cases)
    (auto simp add: cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def  weight_state_eq
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def 
      true_annots_true_cls_def_iff_negation_in_model
      in_negate_trial_iff cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.clauses_def
      intro!: true_clss_cls_in)

end
end