(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals DPLL_CDCL_W_Implementation
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
   restart_state get_propagate_candidates get_conflict_candidates get_not_decided
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
    get_conflict_candidates :: "'st \<Rightarrow> 'v clause list" and
    get_not_decided :: "'st \<Rightarrow> 'v literal option"
begin
interpretation cdcl\<^sub>W_termination trail init_clss learned_clss backtrack_lvl conflicting cons_trail
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

type_synonym 'a cdcl\<^sub>W_mark = "'a clause"
type_synonym cdcl\<^sub>W_marked_level = nat

type_synonym 'v cdcl\<^sub>W_marked_lit = "('v, cdcl\<^sub>W_marked_level, 'v cdcl\<^sub>W_mark) marked_lit"
type_synonym 'v cdcl\<^sub>W_marked_lits = "('v, cdcl\<^sub>W_marked_level, 'v cdcl\<^sub>W_mark) marked_lits"
type_synonym 'v cdcl\<^sub>W_state =
  "'v cdcl\<^sub>W_marked_lits \<times> 'v clauses \<times> 'v clauses \<times> nat \<times> 'v clause conflicting_clause"

abbreviation trail :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a" where
"trail \<equiv> (\<lambda>(M, _). M)"

abbreviation cons_trail :: "'a \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e"
  where
"cons_trail \<equiv> (\<lambda>L (M, S). (L#M, S))"

abbreviation tl_trail :: "'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e" where
"tl_trail \<equiv> (\<lambda>(M, S). (tl M, S))"

abbreviation clauses :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'b" where
"clauses \<equiv> \<lambda>(M, N, _). N"

abbreviation learned_clss :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'c" where
"learned_clss \<equiv> \<lambda>(M, N, U, _). U"

abbreviation backtrack_lvl :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'd" where
"backtrack_lvl \<equiv> \<lambda>(M, N, U, k, _). k"

abbreviation update_backtrack_lvl :: "'d \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e"
  where
"update_backtrack_lvl \<equiv> \<lambda>k (M, N, U, _, S).  (M, N, U, k, S)"

abbreviation conflicting :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'e" where
"conflicting \<equiv> \<lambda>(M, N, U, k, D). D"

abbreviation update_conflicting :: "'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e"
  where
"update_conflicting \<equiv> \<lambda>S (M, N, U, k, _).  (M, N, U, k, S)"

abbreviation "S0_cdcl\<^sub>W N \<equiv> (([], N, {#}, 0, C_True):: 'v cdcl\<^sub>W_state)"

abbreviation add_learned_cls where
"add_learned_cls \<equiv> \<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"

abbreviation remove_cls where
"remove_cls \<equiv> \<lambda>C (M, N, U, S). (M, remove_mset C N, remove_mset C U, S)"

fun convert :: "('a, 'b, 'c list) marked_lit \<Rightarrow> ('a, 'b, 'c multiset) marked_lit"  where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Marked K i) = Marked K i"

fun convertC :: "'a list conflicting_clause \<Rightarrow> 'a multiset conflicting_clause"  where
"convertC (C_Clause C) = C_Clause (mset C)" |
"convertC C_True = C_True"

lemma convert_CTrue[iff]:
  "convertC e = C_True \<longleftrightarrow> e = C_True"
  by (cases e) auto

lemma convert_Propagated[elim!]:
  "convert z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto

type_synonym cdcl\<^sub>W_state_inv_st = "(nat, nat, nat clause) marked_lit list \<times>
  nat literal list list \<times> nat literal list list \<times> nat \<times> nat literal list conflicting_clause"

interpretation cdcl\<^sub>W: state\<^sub>W 
  trail 
  "\<lambda>S. mset (clauses S)" 
  "\<lambda>S. mset (learned_clss S)"  
  backtrack_lvl conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll C N, removeAll C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], sorted_list_of_multiset N, [], 0, C_True)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, C_True)"
  by unfold_locales (auto simp: add.commute)
fun find_conflict where
"find_conflict M [] = None" |
"find_conflict M (N # Ns) = (if (\<forall>c \<in> set N. -c \<in> lits_of M) then Some N else find_conflict M Ns)"

lemma find_conflict_Some:
  "find_conflict M Ns = Some N \<Longrightarrow> N \<in> set Ns \<and> M \<Turnstile>as CNot (mset N)"
  by (induction Ns rule: find_conflict.induct)
     (auto split: split_if_asm)

lemma find_conflict_None:
  "find_conflict M Ns = None \<longleftrightarrow> (\<forall>N \<in> set Ns. \<not>M \<Turnstile>as CNot (mset N))"
  by (induction Ns) auto

lemma find_conflict_sorted_list_of_multiset_None:
  "find_conflict M (map sorted_list_of_multiset Ns) = None \<longleftrightarrow> (\<forall>N \<in> set Ns. \<not>M \<Turnstile>as CNot N)"
  by (simp add: find_conflict_None)

lemma find_conflict_sorted_list_of_multiset_2_None:
  "find_conflict M (map sorted_list_of_multiset Ns @ map sorted_list_of_multiset Ns') = None 
  \<longleftrightarrow> (\<forall>N \<in> set Ns \<union> set Ns'. \<not>M \<Turnstile>as CNot N)"
  by (metis find_conflict_sorted_list_of_multiset_None map_append set_append)
  
declare cdcl\<^sub>W.state_simp[simp del] cdcl\<^sub>W.clauses_def[simp add]
(* 
interpretation cdcl\<^sub>W:  state\<^sub>W_with_candidates
  trail 
  "\<lambda>S. mset (clauses S)" 
  "\<lambda>S. mset (learned_clss S)"  
  backtrack_lvl conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll C N, removeAll C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], sorted_list_of_multiset N, [], 0, C_True)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, C_True)"
  "\<lambda>(M, N, U, S). 
    case find_first_unit_clause (map sorted_list_of_multiset (N @ U)) M of
      None \<Rightarrow> []
    | Some (L, a) \<Rightarrow> [(L, mset a)]"
  "\<lambda>(M, N, U, S). 
    case find_conflict M (map sorted_list_of_multiset (N @ U)) of
      None \<Rightarrow> []
    | Some a \<Rightarrow> [mset a]"
  "\<lambda>(M, N, U, S). find_first_unused_var (map sorted_list_of_multiset (N @ U)) (lits_of M)"
  apply unfold_locales
  apply (case_tac S)
  apply (auto split: option.splits simp: find_conflict_sorted_list_of_multiset_2_None
   dest!: find_conflict_Some)[]
  apply (case_tac S)
  apply (auto split: option.splits simp: find_conflict_sorted_list_of_multiset_2_None
   dest!: find_conflict_Some  sym[of "Some _" "find_conflict _ _"])[]
  apply (case_tac S)
  sorry *)

definition "do_conflict_step = cdcl\<^sub>W_cands.do_conflict_step"
interpretation gcdcl\<^sub>W2: cdcl\<^sub>W_cands
  trail
  "\<lambda>S. clauses S" 
  "\<lambda>S. learned_clss S"  
  backtrack_lvl 
  conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, {#C#} + N, S)"
  "\<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"
  "\<lambda>C (M, N, U, S). (M, remove_mset C N, remove_mset C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {#}, 0, C_True)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, C_True)"
  "\<lambda>(M, N, U, a, b). 
    case find_first_unit_clause (map sorted_list_of_multiset (sorted_list_of_multiset N @ sorted_list_of_multiset U)) M of
      None \<Rightarrow> []
    | Some (L, a) \<Rightarrow> [(L, mset a)]"
  "\<lambda>(M, N, U, a, b). 
    case find_conflict M (map sorted_list_of_multiset (sorted_list_of_multiset N @ sorted_list_of_multiset U)) of
      None \<Rightarrow> []
    | Some a \<Rightarrow> [mset a]"
  "\<lambda>(M, N, U, a, b). find_first_unused_var (map sorted_list_of_multiset (sorted_list_of_multiset N @ sorted_list_of_multiset U)) (lits_of M)"
  rewrites 
  "cdcl\<^sub>W_cands.do_conflict_step S = do_conflict_step S"
  apply unfold_locales
  sorry
thm do_conflict_step_def gcdcl\<^sub>W2.do_conflict_step_def do_conflict_step_def
lemmas [code] = do_conflict_step_def gcdcl\<^sub>W2.do_conflict_step_def


end