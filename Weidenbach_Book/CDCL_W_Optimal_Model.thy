theory CDCL_W_Optimal_Model
imports CDCL_W_Incremental
begin

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
    add_additional_information :: "'st \<Rightarrow> 'st" and
    conflicting_clauses :: "'a \<Rightarrow> 'v literal clause" and
    weight :: \<open>'st \<Rightarrow> 'a\<close>
  assumes
    state_add_additional_information: \<open>state (add_additional_information S) = state S\<close> and
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
    add_additional_information :: "'st \<Rightarrow> 'st" and
    conflicting_clauses :: "'a \<Rightarrow> 'v literal clause" and
    weight :: \<open>'st \<Rightarrow> 'a\<close> +
  assumes
    state_prop[simp]:
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>  
begin

sublocale conflict_driven_clause_learning_with_adding_init_clause\<^sub>W
  apply unfold_locales
  unfolding additional_info'_def additional_info_def by auto

lemma 
  weight_cons_trail: \<open>weight (cons_trail L S) = weight S\<close>
  using cons_trail[of S _ _ L] by auto
  
lemma add_additional_information_simp:
  \<open>trail (add_additional_information S) = trail S\<close> and
  \<open>init_clss (add_additional_information S) = init_clss S\<close> and
  \<open>learned_clss (add_additional_information S) = learned_clss S\<close> and
  \<open>clauses (add_additional_information S) = clauses S\<close> and
  \<open>backtrack_lvl (add_additional_information S) = backtrack_lvl S\<close> and
  \<open>conflicting (add_additional_information S) = conflicting S\<close>
  using state_add_additional_information[of S] by (auto simp: clauses_def)

abbreviation negate_trail :: "'st \<Rightarrow> 'v literal multiset" where
  \<open>negate_trail S \<equiv> image_mset (\<lambda>L. - lit_of L) (mset (trail S))\<close>

inductive conflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
  "M \<in># conflicting_clauses (weight S) \<Longrightarrow> 
  T \<sim> update_conflicting (Some (negate_trail S)) S \<Longrightarrow> 
  conflict_opt S T"

inductive improve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
  "trail S = M' @ M \<Longrightarrow>
  M \<Turnstile>asm init_clss S \<Longrightarrow>
  T \<sim> update_conflicting (Some (negate_trail S)) S \<Longrightarrow> 
  improve S (add_additional_information S)"

end
end