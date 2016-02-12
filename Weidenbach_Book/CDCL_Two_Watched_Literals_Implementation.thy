(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals
begin

locale state\<^sub>W_with_candidates =
  state\<^sub>W trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail add_init_cls
   add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state
  for     trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow>'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  fixes
    get_propagate_candidates :: "'st \<Rightarrow> ('v literal \<times> 'v clause) list" and
    get_conflict_candidates :: "'st \<Rightarrow> 'v clause list" and
    get_not_decided :: "'st \<Rightarrow> 'v literal option"
  assumes
    get_conflict_candidates_empty:
      "\<And>S. get_conflict_candidates S = [] \<longleftrightarrow> (\<forall>D \<in># clauses S. \<not> trail S \<Turnstile>as CNot D)" and
    get_conflict_candidates_in_clauses:
      "\<And>S. \<forall>C \<in> set (get_conflict_candidates S). C \<in># clauses S \<and> trail S \<Turnstile>as CNot C" and
    get_propagate_candidates_lit_in_cls:
      "\<And>S. \<forall>(L, C) \<in> set (get_propagate_candidates S). undefined_lit (trail S) L \<and> C \<in># clauses S
        \<and> trail S \<Turnstile>as CNot (C - {#L#}) \<and> L \<in># C" and
    get_propagate_candidates_lit_empty:
      "\<And>S. get_propagate_candidates S = [] \<longleftrightarrow>
        \<not>(\<exists>C L. undefined_lit (trail S) L \<and> C + {#L#} \<in># clauses S \<and> trail S \<Turnstile>as CNot C)" and
    get_not_decided_Some:
      "\<And>S L. get_not_decided S = Some L \<Longrightarrow>
         undefined_lit (trail S) L \<and> atm_of L \<in> atms_of_msu (init_clss S)" and
    get_not_decided_None:
      "\<And>S. get_not_decided S = None \<Longrightarrow>
         \<not>(\<exists>L. undefined_lit (trail S) L \<and> atm_of L \<in> atms_of_msu (init_clss S))"

locale
  cdcl\<^sub>W_cands =
   state\<^sub>W_with_candidates trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
   add_init_cls add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state get_propagate_candidates get_conflict_candidates
  for
    trail :: "'st \<Rightarrow> ('v::linorder, nat, 'v::linorder clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" and
    get_propagate_candidates :: "'st \<Rightarrow> ('v literal \<times> 'v clause) list" and
    get_conflict_candidates :: "'st \<Rightarrow> 'v clause list"
begin
sublocale cdcl\<^sub>W_termination trail init_clss learned_clss backtrack_lvl conflicting cons_trail
  tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl update_conflicting
  init_state restart_state
 by unfold_locales

definition do_conflict_step :: "'st \<Rightarrow> 'st option" where
"do_conflict_step S =
  (case conflicting S of
    C_Clause _ \<Rightarrow> None
  | C_True \<Rightarrow>
      (case get_conflict_candidates S of
        [] \<Rightarrow> None
      | a # _ \<Rightarrow> Some (update_conflicting (C_Clause a) S)))"

lemma do_conflict_step_Some:
  assumes conf: "do_conflict_step S = Some T"
  shows "conflict S T"
proof (cases "conflicting S")
  case C_Clause
  then show ?thesis using conf unfolding do_conflict_step_def by simp
next
  case C_True
  then obtain C where
    C: "C \<in> set (get_conflict_candidates S)" and
    T: "T = update_conflicting (C_Clause C) S"
     using conf unfolding do_conflict_step_def by (auto split: list.splits)
  have "C \<in># clauses S" and "trail S \<Turnstile>as CNot C"
    using get_conflict_candidates_in_clauses by (simp_all add: C some_in_eq)
  then show ?thesis
    using conflict_rule[of S _ _ _ _ C T]  state_eq_ref T C_True
    by auto
qed

lemma do_conflict_step_None:
  assumes conf: "do_conflict_step S = None"
  shows "no_step conflict S"
proof (cases "conflicting S")
  case C_Clause
  then show ?thesis by auto
next
  case C_True
  then have "get_conflict_candidates S = []"
     using conf unfolding do_conflict_step_def by (auto split: list.splits)
  then show ?thesis
    using get_conflict_candidates_empty by auto
qed

end
end