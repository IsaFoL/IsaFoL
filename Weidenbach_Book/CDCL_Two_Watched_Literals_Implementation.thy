(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals DPLL_CDCL_W_Implementation
begin

subsection \<open>Abstract Implementation\<close>

text \<open>We define here a locale serving as proxy between the abstract transition defined using
  multiset and a more concrete version using a representation that can be converted to lists.
  \<close>

subsubsection \<open>An Extend State\<close>

text \<open>The more concrete state has some way to find candidates. This is abstracted, since it can be
  integrated to the data-structure (see 2-watched literals) \<close>
locale conc_state\<^sub>W_with_candidates =
  state\<^sub>W trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail add_init_cls
   add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state
  for
    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause option" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow>'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  fixes
    raw_trail :: "'conc_st \<Rightarrow> 'trail" and
    raw_init_clss :: "'conc_st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'conc_st \<Rightarrow> 'clss" and
    raw_backtrack_lvl :: "'conc_st \<Rightarrow> nat" and
    raw_conflicting :: "'conc_st \<Rightarrow> 'cls option" and

    raw_cons_trail :: "('v, nat, 'cls) marked_lit \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_tl_trail :: "'conc_st \<Rightarrow>'conc_st" and
    raw_add_init_cls :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_add_learned_cls :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_remove_cls :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_update_backtrack_lvl :: "nat \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_update_conflicting :: "'cls option \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and

    raw_init_state :: "'clss \<Rightarrow> 'conc_st" and
    raw_restart_state :: "'conc_st \<Rightarrow> 'conc_st" and
    get_propagate_candidates :: "'conc_st \<Rightarrow> ('v literal \<times> 'cls) list" and
    get_conflict_candidates :: "'conc_st \<Rightarrow> 'cls list" and
    get_not_decided :: "'conc_st \<Rightarrow> 'v literal option" and

    st_of_raw :: "'conc_st \<Rightarrow> 'st" and
    cls_of_raw_cls :: "'cls \<Rightarrow> 'v clause" and
    clss_of_raw_clss :: "'clss \<Rightarrow> 'v clause list" and
    raw_cls_union :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remdups_raw_cls :: "'cls \<Rightarrow> 'cls" and
    marked_lit_of_raw :: "('v, nat, 'cls) marked_lit \<Rightarrow> ('v, nat, 'v clause) marked_lit" and
    maximum_level :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> nat" and
    raw_hd_trail :: "'conc_st \<Rightarrow> ('v, nat, 'cls) marked_lit" and
    remove :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls"

  assumes
    (* Mapping from 'cons_st to 'st *)
    raw_cons_trail[simp]:
      "\<And>L S. st_of_raw (raw_cons_trail L S) = cons_trail (marked_lit_of_raw L) (st_of_raw S)" and
    raw_tl_trail[simp]:
      "\<And>S. st_of_raw (raw_tl_trail S) = tl_trail (st_of_raw S)" and
    raw_add_init_cls[simp]:
      "\<And>C S. st_of_raw (raw_add_init_cls C S) = add_init_cls (cls_of_raw_cls C) (st_of_raw S)" and
    raw_add_learned_cls[simp]:
      "\<And>C S.
        st_of_raw (raw_add_learned_cls C S) = add_learned_cls (cls_of_raw_cls C) (st_of_raw S)" and
    raw_update_backtrack_lvl[simp]:
      "\<And>k S. st_of_raw (raw_update_backtrack_lvl k S) = update_backtrack_lvl k (st_of_raw S)" and
    raw_update_conflicting[simp]:
      "\<And>(C::'cls option) S. st_of_raw (raw_update_conflicting C S) =
         update_conflicting (map_option cls_of_raw_cls C) (st_of_raw S)" and
    raw_init_state:
      "\<And>N. st_of_raw (raw_init_state N) = init_state (mset (clss_of_raw_clss N))" and
    cls_of_raw_cls_raw_cls_union[simp]:
      "distinct_mset (cls_of_raw_cls a) \<Longrightarrow>
        distinct_mset (cls_of_raw_cls b) \<Longrightarrow>
          cls_of_raw_cls (raw_cls_union a b) = cls_of_raw_cls a #\<union> cls_of_raw_cls b" and
    cls_of_raw_cls_remdups_raw_cls[simp]:
      "cls_of_raw_cls (remdups_raw_cls a) = remdups_mset (cls_of_raw_cls a)" and
    conflicting_raw_conflicting:
      "conflicting (st_of_raw S) = map_option cls_of_raw_cls (raw_conflicting S)" and
    marked_lit_of_raw[simp]:
      "\<And>L C. marked_lit_of_raw (Propagated L C) = Propagated L (cls_of_raw_cls C)"
      "\<And>L i. marked_lit_of_raw (Marked L i) = Marked L i"
      and
    maximum_level[simp]:
      "maximum_level C S = get_maximum_level (trail (st_of_raw S)) (cls_of_raw_cls C)" and
    raw_hd_trail:
      "\<And>S. trail (st_of_raw S) \<noteq> [] \<Longrightarrow>
        marked_lit_of_raw (raw_hd_trail S) = hd (trail (st_of_raw S))" and
    remove[simp]:
      "cls_of_raw_cls (remove L C) = cls_of_raw_cls C - {#L#}" and

    (* getting answers from the data-structure *)
    get_conflict_candidates_empty:
      "\<And>S. get_conflict_candidates S = [] \<longleftrightarrow>
        (\<forall>D \<in># clauses (st_of_raw S). \<not> trail (st_of_raw S) \<Turnstile>as CNot D)" and
    get_conflict_candidates_in_clauses:
      "\<And>S. \<forall>C \<in> set (get_conflict_candidates S). cls_of_raw_cls C \<in># clauses (st_of_raw S) \<and>
        trail (st_of_raw S) \<Turnstile>as CNot (cls_of_raw_cls C)" and
    get_propagate_candidates_lit_in_cls:
      "\<And>S. \<forall>(L, C) \<in> set (get_propagate_candidates S). undefined_lit (trail (st_of_raw S)) L \<and>
        cls_of_raw_cls C \<in># clauses (st_of_raw S)
        \<and> trail (st_of_raw S) \<Turnstile>as CNot (cls_of_raw_cls C - {#L#}) \<and> L \<in># cls_of_raw_cls C" and
    get_propagate_candidates_empty:
      "\<And>S. get_propagate_candidates S = [] \<longleftrightarrow>
        \<not>(\<exists>C L. undefined_lit (trail (st_of_raw S)) L \<and> C + {#L#} \<in># clauses (st_of_raw S) \<and>
          trail (st_of_raw S) \<Turnstile>as CNot C)" and
    get_not_decided_Some:
      "\<And>S L. get_not_decided S = Some L \<Longrightarrow>
         undefined_lit (trail (st_of_raw S)) L \<and> atm_of L \<in> atms_of_msu (init_clss (st_of_raw S))"
      and
    get_not_decided_None:
      "\<And>S. get_not_decided S = None \<Longrightarrow>
         \<not>(\<exists>L. undefined_lit (trail (st_of_raw S)) L \<and>
         atm_of L \<in> atms_of_msu (init_clss (st_of_raw S)))"

subsubsection \<open>Lowering from Transitions to Functions\<close>
locale
  cdcl\<^sub>W_cands =
   conc_state\<^sub>W_with_candidates trail init_clss learned_clss backtrack_lvl conflicting cons_trail
   tl_trail
   add_init_cls add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state

   raw_trail raw_init_clss raw_learned_clss raw_backtrack_lvl raw_conflicting raw_cons_trail
   raw_tl_trail
   raw_add_init_cls raw_add_learned_cls raw_remove_cls raw_update_backtrack_lvl
   raw_update_conflicting raw_init_state
   raw_restart_state

   get_propagate_candidates get_conflict_candidates get_not_decided st_of_raw
   cls_of_raw_cls clss_of_raw_clss
   raw_cls_union remdups_raw_cls marked_lit_of_raw
   maximum_level raw_hd_trail remove
  for
    trail :: "'st \<Rightarrow> ('v::linorder, nat, 'v::linorder clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause option" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" and

    raw_trail :: "'conc_st \<Rightarrow> 'trail" and
    raw_init_clss :: "'conc_st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'conc_st \<Rightarrow> 'clss" and
    raw_backtrack_lvl :: "'conc_st \<Rightarrow> nat" and
    raw_conflicting :: "'conc_st \<Rightarrow> 'cls option" and

    raw_cons_trail :: "('v, nat, 'cls) marked_lit \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_tl_trail :: "'conc_st \<Rightarrow>'conc_st" and
    raw_add_init_cls :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_add_learned_cls :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_remove_cls :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_update_backtrack_lvl :: "nat \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and
    raw_update_conflicting :: "'cls option \<Rightarrow> 'conc_st \<Rightarrow> 'conc_st" and

    raw_init_state :: "'clss \<Rightarrow> 'conc_st" and
    raw_restart_state :: "'conc_st \<Rightarrow> 'conc_st" and
    get_propagate_candidates :: "'conc_st \<Rightarrow> ('v literal \<times> 'cls) list" and
    get_conflict_candidates :: "'conc_st \<Rightarrow> 'cls list" and
    get_not_decided :: "'conc_st \<Rightarrow> 'v literal option" and

    st_of_raw :: "'conc_st \<Rightarrow> 'st" and
    cls_of_raw_cls :: "'cls \<Rightarrow> 'v clause" and
    clss_of_raw_clss :: "'clss \<Rightarrow> 'v clause list" and
    raw_cls_union :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remdups_raw_cls :: "'cls \<Rightarrow> 'cls" and
    marked_lit_of_raw :: "('v, nat, 'cls) marked_lit \<Rightarrow> ('v, nat, 'v clause) marked_lit" and
    maximum_level :: "'cls \<Rightarrow> 'conc_st \<Rightarrow> nat" and
    raw_hd_trail :: "'conc_st \<Rightarrow> ('v, nat, 'cls) marked_lit" and
    remove :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls"
begin

interpretation cdcl\<^sub>W_termination trail init_clss learned_clss backtrack_lvl conflicting cons_trail
  tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl update_conflicting
  init_state restart_state
 by unfold_locales

paragraph \<open>The transitions\<close>
definition do_conflict_step :: "'conc_st \<Rightarrow> 'conc_st option" where
"do_conflict_step S =
  (case raw_conflicting S of
    Some _ \<Rightarrow> None
  | None \<Rightarrow>
      (case get_conflict_candidates S of
        [] \<Rightarrow> None
      | a # _ \<Rightarrow> Some (raw_update_conflicting (Some a) S)))"

lemma do_conflict_step_Some:
  assumes conf: "do_conflict_step S = Some T"
  shows "conflict (st_of_raw S) (st_of_raw T)"
proof (cases "raw_conflicting S")
  case Some
  then show ?thesis using conf unfolding do_conflict_step_def by simp
next
  case None
  then obtain C where
    C: "C \<in> set (get_conflict_candidates S)" and
    T: "T = raw_update_conflicting (Some C) S"
     using conf unfolding do_conflict_step_def by (auto split: list.splits)
  have
    "cls_of_raw_cls C \<in># clauses (st_of_raw S)" and
    "trail (st_of_raw S) \<Turnstile>as CNot (cls_of_raw_cls C)"
    using get_conflict_candidates_in_clauses by (simp_all add: C some_in_eq)
  then show ?thesis
    using conflict_rule[of "st_of_raw S" "trail (st_of_raw S)" "init_clss (st_of_raw S)"
      "learned_clss (st_of_raw S)" "backtrack_lvl (st_of_raw S)" "cls_of_raw_cls C" "st_of_raw T"]
      state_eq_ref T None
    by (auto simp: conflicting_raw_conflicting)
qed

lemma do_conflict_step_None:
  assumes conf: "do_conflict_step S = None"
  shows "no_step conflict (st_of_raw S)"
proof (cases "conflicting (st_of_raw S)")
  case Some
  then show ?thesis by auto
next
  case None
  then have "get_conflict_candidates S = []"
     using conf unfolding do_conflict_step_def
     by (auto split: list.splits option.splits simp: conflicting_raw_conflicting)
  then show ?thesis
    using get_conflict_candidates_empty by auto
qed

text \<open>We have a list of conflict candidates, but we take only the first element, in case a conflict
  appears. This is necessary for non-redundancy.\<close>
definition do_propagate_step :: "'conc_st \<Rightarrow> 'conc_st option" where
"do_propagate_step S =
  (case raw_conflicting S of
    Some _ \<Rightarrow> None
  | None \<Rightarrow>
      (case get_propagate_candidates S of
        [] \<Rightarrow> None
      | (L, C) # _ \<Rightarrow> Some (raw_cons_trail (Propagated L C) S)))"

lemma do_propagate_step_Some:
  assumes conf: "do_propagate_step S = Some T"
  shows "propagate (st_of_raw S) (st_of_raw T)"
proof (cases "conflicting (st_of_raw S)")
  case Some
  then show ?thesis
    using conf by (auto simp: do_propagate_step_def conflicting_raw_conflicting
      split: option.splits list.splits)
next
  case None
  then obtain L C where
    C: "(L, C) \<in> set (get_propagate_candidates S)" and
    T: "T = raw_cons_trail (Propagated L C) S"
     using conf unfolding do_propagate_step_def
    by (auto split: list.splits simp: conflicting_raw_conflicting)
  have
    "cls_of_raw_cls C \<in># clauses (st_of_raw S)" and
    undef: "undefined_lit (trail (st_of_raw S)) L"
    "trail (st_of_raw S) \<Turnstile>as CNot (cls_of_raw_cls C - {#L#})" and
    "L \<in># cls_of_raw_cls C"
    using get_propagate_candidates_lit_in_cls C by auto
  then show ?thesis
    using propagate_rule[of "st_of_raw S" "trail (st_of_raw S)" "init_clss (st_of_raw S)"
      "learned_clss (st_of_raw S)" "backtrack_lvl (st_of_raw S)" "cls_of_raw_cls C - {#L#}" L
      "st_of_raw T"]
      state_eq_ref T None
    by (auto simp: conflicting_raw_conflicting)
qed

lemma do_propagate_step_None:
  assumes conf: "do_propagate_step S = None"
  shows "no_step propagate (st_of_raw S)"
proof (cases "conflicting (st_of_raw S)")
  case Some
  then show ?thesis by auto
next
  case None
  then have "get_propagate_candidates S = []"
     using conf unfolding do_propagate_step_def
     by (auto split: list.splits option.splits simp: conflicting_raw_conflicting)
  then show ?thesis
    unfolding get_propagate_candidates_empty by (force elim!: propagateE)
qed

definition do_skip_step :: "'conc_st \<Rightarrow> 'conc_st option"  where
"do_skip_step S =
  (case conflicting (st_of_raw S) of
    None \<Rightarrow> None
  | Some D \<Rightarrow>
    (case trail (st_of_raw S) of
      Propagated L C' # _ \<Rightarrow>
        if -L \<notin># D \<and> D \<noteq> {#} then Some (raw_tl_trail S) else None
    | _ \<Rightarrow> None))"

lemma do_skip_step_Some:
  assumes conf: "do_skip_step S = Some T"
  shows "skip (st_of_raw S) (st_of_raw T)"
proof (cases "conflicting (st_of_raw S)")
  case None
  then show ?thesis
    using conf by (auto simp: do_skip_step_def)
next
  case (Some D)
  then obtain L C M  where
    C: "trail (st_of_raw S) = Propagated L C # M" and
    T: " -L \<notin># D" and
    "D \<noteq> {#}" and
    "st_of_raw T = tl_trail (st_of_raw S)"
    using conf unfolding do_skip_step_def
    by (auto split: list.splits marked_lit.splits split_if_asm simp: conflicting_raw_conflicting)
  then show ?thesis
    using skip_rule[of "st_of_raw S" L C M "init_clss (st_of_raw S)"
      "learned_clss (st_of_raw S)" "backtrack_lvl (st_of_raw S)"]
      state_eq_ref T Some
    by (auto simp: conflicting_raw_conflicting)
qed

lemma do_skip_step_None:
  assumes conf: "do_skip_step S = None"
  shows "no_step skip (st_of_raw S)"
proof (cases "conflicting (st_of_raw S)")
  case None
  then show ?thesis by auto
next
  case Some
  then show ?thesis
    using conf unfolding do_skip_step_def
    by (auto split: list.splits marked_lit.splits split_if_asm simp: conflicting_raw_conflicting)
qed

definition do_resolve_step :: "'conc_st \<Rightarrow> 'conc_st option" where
"do_resolve_step S =
  (case raw_conflicting S of
    None \<Rightarrow> None
  | Some D \<Rightarrow>
    if trail (st_of_raw S) \<noteq> []
    then
      (case raw_hd_trail S of
        Propagated L C \<Rightarrow>
          if -L \<in># cls_of_raw_cls D \<and> cls_of_raw_cls D \<noteq> {#} \<and>
             maximum_level (remove (-L) D) S = raw_backtrack_lvl S
          then Some (raw_update_conflicting
             (Some (raw_cls_union (remove (-L) D) (remove L C)))
             (raw_tl_trail S))
          else None
      | _ \<Rightarrow> None)
    else None)"


lemma do_resolve_step_Some:
  assumes conf: "do_resolve_step S = Some T" and inv: "cdcl\<^sub>W_all_struct_inv (st_of_raw S)"
  shows "resolve (st_of_raw S) (st_of_raw T)"
proof (cases "raw_conflicting S")
  case None
  then show ?thesis
    using conf by (auto simp: do_resolve_step_def)
next
  case (Some D)
  def M \<equiv> "tl (trail (st_of_raw S))"
  obtain L C where
    C: "raw_hd_trail S = Propagated L C" and
    T: " -L \<in># cls_of_raw_cls D" and
    "cls_of_raw_cls D \<noteq> {#}" and
    "T =
      raw_update_conflicting (Some (raw_cls_union (remove (-L) D) (remove L C))) (raw_tl_trail S)" and
    "maximum_level (remove (-L) D) S = raw_backtrack_lvl S \<or> raw_backtrack_lvl S = 0" and
    empty: "trail (st_of_raw S) \<noteq> []"
    using conf Some unfolding do_resolve_step_def
    by (auto split: list.splits marked_lit.splits split_if_asm simp: conflicting_raw_conflicting)
  moreover have "trail (st_of_raw S) = Propagated L (cls_of_raw_cls C) # M"
    using empty raw_hd_trail[of S] C M_def by (cases "trail (st_of_raw S)") simp_all
  moreover then have "L \<in># cls_of_raw_cls C"
    using inv unfolding  cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by force
  ultimately show ?thesis
    using resolve_rule[of "st_of_raw S" L "cls_of_raw_cls C - {#L#}" "tl (trail (st_of_raw S))"
      "init_clss (st_of_raw S)"
      "learned_clss (st_of_raw S)" "backtrack_lvl (st_of_raw S)" "cls_of_raw_cls D - {#-L#}"]
      state_eq_ref T Some
    apply (auto simp: conflicting_raw_conflicting)
    (* invariant needed *)
    sorry
qed

(*
"do_resolve_step (Propagated L C # Ls, N, U, k, Some D) =
  (if -L \<in> set D \<and> (maximum_level_code (remove1 (-L) D) (Propagated L C # Ls) = k \<or>  k = 0)
  then (Ls, N, U, k, Some (remdups (remove1 L C @ remove1 (-L) D)))
  else (Propagated L C # Ls, N, U, k, Some D))" |
"do_resolve_step S = S"
 *)
end

subsection \<open>Implementation as list\<close>
type_synonym 'a cdcl\<^sub>W_mark = "'a clause"
type_synonym cdcl\<^sub>W_marked_level = nat

type_synonym 'v cdcl\<^sub>W_marked_lit = "('v, cdcl\<^sub>W_marked_level, 'v cdcl\<^sub>W_mark) marked_lit"
type_synonym 'v cdcl\<^sub>W_marked_lits = "('v, cdcl\<^sub>W_marked_level, 'v cdcl\<^sub>W_mark) marked_lits"
type_synonym 'v cdcl\<^sub>W_state =
  "'v cdcl\<^sub>W_marked_lits \<times> 'v clauses \<times> 'v clauses \<times> nat \<times> 'v clause option"

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
"update_conflicting \<equiv> \<lambda>C (M, N, U, k, _).  (M, N, U, k, C)"

abbreviation "S0_cdcl\<^sub>W N \<equiv> (([], N, {#}, 0, None):: 'v cdcl\<^sub>W_state)"

abbreviation add_learned_cls where
"add_learned_cls \<equiv> \<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"

abbreviation remove_cls where
"remove_cls \<equiv> \<lambda>C (M, N, U, S). (M, remove_mset C N, remove_mset C U, S)"

fun convert :: "('a, 'b, 'c list) marked_lit \<Rightarrow> ('a, 'b, 'c multiset) marked_lit"  where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Marked K i) = Marked K i"

abbreviation convert_tr :: "('a, 'b, 'c list) marked_lits \<Rightarrow> ('a, 'b, 'c multiset) marked_lits"
  where
"convert_tr \<equiv> map convert
"
abbreviation convertC :: "'a list option \<Rightarrow> 'a multiset option"  where
"convertC \<equiv> map_option mset"

lemma convert_Propagated[elim!]:
  "convert z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto

type_synonym cdcl\<^sub>W_state_inv_st = "(nat, nat, nat clause) marked_lit list \<times>
  nat literal list list \<times> nat literal list list \<times> nat \<times> nat literal list option"

fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, nat, 'a literal list) marked_lit list \<Rightarrow> nat"
  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level M L) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[code, simp]:
  "maximum_level_code D M = get_maximum_level M (mset D)"
  by (induction D) (auto simp add: get_maximum_level_plus)

lemma get_rev_level_convert_tr:
  "get_rev_level (convert_tr M) n = get_rev_level M n"
  by (induction M arbitrary: n rule: marked_lit_list_induct) auto

lemma get_level_convert_tr:
  "get_level (convert_tr M) = get_level M"
  by (simp add: get_rev_level_convert_tr rev_map)

lemma get_maximum_level_convert_tr[simp]:
  "get_maximum_level (convert_tr M) (mset D) = get_maximum_level M (mset D)"
  by (induction D) (simp_all add: get_maximum_level_plus get_level_convert_tr)

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
  "\<lambda>N. ([], sorted_list_of_multiset N, [], 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"
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

lemma mset_map_mset_removeAll_remove_mset:
  "C \<in> set N \<Longrightarrow> distinct (map mset N) \<Longrightarrow>
  mset (map mset (removeAll C N)) = remove_mset (mset C) (mset (map mset N))"
proof (induction N)
  case Nil
  then show ?case by simp
next
  case (Cons a N) note IH = this(1) and C = this(2) and dist = this(3)
  have dist': "distinct (map mset N)"
    using dist by auto
  have H: "mset (map mset (removeAll C N)) = remove_mset (mset C) (mset (map mset N))"
    by (metis C IH count_mset_0 diff_zero dist distinct.simps(2) list.simps(9) removeAll_id
      replicate_mset_0 set_ConsD)
  have rall: "mset (map mset (removeAll C (a # N))) =
     (if C = a then {#} else {#mset a#}) + mset (map mset (removeAll C N))"
     by (auto simp: ac_simps)
  have rmset: "remove_mset (mset C) (mset (map mset (a # N))) =
     (if mset C = mset a then {#} else {#mset a#}) + remove_mset (mset C) (mset (map mset N))"
    proof -
      { assume a1: "mset C \<noteq> mset a"
        then have "remove_mset (mset C) (mset (map mset (a # N))) - {#mset a#} + {#mset a#}
          = remove_mset (mset C) (mset (map mset (a # N))) - {#}"
          by simp (* 3 ms *)
        then have ?thesis
          using a1 by (simp_all add: Multiset.diff_right_commute add.commute)}
      then show ?thesis
        by (cases "mset C \<noteq> mset a") (auto simp: ac_simps)
    qed
  have "C \<noteq> a \<longrightarrow> mset C \<noteq> mset a"
    by (metis C dist distinct.simps(2) image_eqI list.simps(9) set_ConsD set_map)
  then show ?case
    unfolding rall rmset H by simp
qed

interpretation cdcl\<^sub>W':  state\<^sub>W
  trail
  clauses
  learned_clss
  backtrack_lvl conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, {#C#} + N, S)"
  "\<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"
  "\<lambda>C (M, N, U, S). (M, remove_mset C N, remove_mset C U, S)"
  "\<lambda>k (M, N, (U::nat clauses), _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {#}, 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"
  by unfold_locales auto

interpretation cdcl\<^sub>W:  conc_state\<^sub>W_with_candidates
  trail
  clauses
  learned_clss
  backtrack_lvl conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, {#C#} + N, S)"
  "\<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"
  "\<lambda>C (M, N, U, S). (M, remove_mset C N, remove_mset C U, S)"
  "\<lambda>k (M, N, (U::nat clauses), _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {#}, 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"

  trail
  clauses
  learned_clss
  backtrack_lvl
  conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll C N, removeAll C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, [], 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"

  "\<lambda>(M, N, U, S).
    case find_first_unit_clause (N @ U) M of
      None \<Rightarrow> []
    | Some (L, a) \<Rightarrow> [(L, a)]"
  "\<lambda>(M, N, U, S).
    case find_conflict M (N @ U) of
      None \<Rightarrow> []
    | Some a \<Rightarrow> [a]"
  "\<lambda>(M, N, U, S). find_first_unused_var (N @ U) (lits_of M)"
  "\<lambda>(M, N, U, k, C).
    (convert_tr M, mset (map mset N), mset (map mset U), k, map_option mset C)"

  mset
  "\<lambda>N. (map mset N)"
  "\<lambda>a b. remdups (a @ b)"
  remdups
  convert
  "\<lambda>C (M, N, U, k, D). maximum_level_code C M"
  "\<lambda>S. (hd (trail S))"
  apply unfold_locales
  apply (auto simp: map_tl add.commute distinct_mset_rempdups_union_mset cdcl\<^sub>W'.clauses_def)[12]
  apply (auto split: option.splits simp: find_conflict_None cdcl\<^sub>W'.clauses_def)[2]
  apply (metis hd_map)

  sorry


definition truc :: "(nat, nat, nat literal list) marked_lit list \<times>
   nat literal list list \<times>
   nat literal list list \<times> nat \<times> nat literal list option
   \<Rightarrow> ((nat, nat, nat literal list) marked_lit list \<times>
       nat literal list list \<times>
       nat literal list list \<times>
       nat \<times> nat literal list option) option"
  where
"truc = cdcl\<^sub>W_cands.do_conflict_step  (\<lambda>(M, N, U, k, D). D) (\<lambda>C (M, N, U, k, _). (M, N, U, k, C))
     (\<lambda>(M, N, U, S). case find_conflict M (N @ U) of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"

 interpretation gcdcl\<^sub>W2: cdcl\<^sub>W_cands
  trail
  clauses
  learned_clss
  backtrack_lvl conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, {#C#} + N, S)"
  "\<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"
  "\<lambda>C (M, N, U, S). (M, remove_mset C N, remove_mset C U, S)"
  "\<lambda>k (M, N, (U::nat clauses), _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {#}, 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"

  trail
  clauses
  learned_clss
  backtrack_lvl
  conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll C N, removeAll C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, [], 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"

  "\<lambda>(M, N, U, S).
    case find_first_unit_clause (N @ U) M of
      None \<Rightarrow> []
    | Some (L, a) \<Rightarrow> [(L, a)]"
  "\<lambda>(M, N, U, S).
    case find_conflict M (N @ U) of
      None \<Rightarrow> []
    | Some a \<Rightarrow> [a]"
  "\<lambda>(M, N, U, S). find_first_unused_var (N @ U) (lits_of M)"
  "\<lambda>(M, N, U, k, C).
    (convert_tr M, mset (map mset N), mset (map mset U), k, map_option mset C)"

  mset
  "\<lambda>N. (map mset N)"
  "\<lambda>a b. remdups (a @ b)"
  remdups
  convert
  "\<lambda>C (M, N, U, k, D). maximum_level_code C M"
  "\<lambda>S. (hd (trail S))"
  rewrites
  "cdcl\<^sub>W_cands.do_conflict_step (\<lambda>(M, N, U, k, D). D) (\<lambda>C (M, N, U, k, _). (M, N, U, k, C))
     (\<lambda>(M, N, U, S). case find_conflict M (N @ U) of None \<Rightarrow> [] | Some a \<Rightarrow> [a])
  = truc"
   apply unfold_locales
   using [[show_abbrevs = false]]
   unfolding truc_def apply simp
  done


term cdcl\<^sub>W_cands.do_conflict_step
thm truc_def
declare [[show_abbrevs = false, show_types = true, show_sorts]]
thm  gcdcl\<^sub>W2.do_conflict_step_def
declare gcdcl\<^sub>W2.do_conflict_step_def[code]
export_code gcdcl\<^sub>W2.do_conflict_step in SML

end