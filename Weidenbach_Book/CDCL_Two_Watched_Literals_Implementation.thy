(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals DPLL_CDCL_W_Implementation
begin
  
type_synonym 'v conc_twl_state =
  "(('v, nat, 'v literal list) ann_literal, 'v literal list twl_clause list, nat, 'v literal list)
    twl_state"

fun convert :: "('a, 'b, 'c list) ann_literal \<Rightarrow> ('a, 'b, 'c multiset) ann_literal"  where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Marked K i) = Marked K i"

abbreviation convert_tr :: "('a, 'b, 'c list) ann_literals \<Rightarrow> ('a, 'b, 'c multiset) ann_literals"
  where
"convert_tr \<equiv> map convert"

abbreviation convertC :: "'a literal list option \<Rightarrow> 'a clause option"  where
"convertC \<equiv> map_option mset"

fun raw_clause_l :: "'v list twl_clause \<Rightarrow> 'v multiset twl_clause"  where
  "raw_clause_l (TWL_Clause UW W) = TWL_Clause (mset W) (mset UW)"

abbreviation convert_clss :: "'v literal list twl_clause list \<Rightarrow> 'v clause twl_clause multiset"
  where
"convert_clss S \<equiv> mset (map raw_clause_l S)"

fun raw_state_of_conc :: "'v conc_twl_state \<Rightarrow> ('v, nat, 'v clause) twl_state_abs" where
"raw_state_of_conc (TWL_State M N U k C) =
  TWL_State (convert_tr M) (convert_clss N) (convert_clss U) k (map_option mset C)"

lemma
  "raw_state_of_conc (tl_trail S) = tl_trail (raw_state_of_conc S)"
  unfolding tl_trail_def by (induction S) (auto simp: map_tl)

typedef 'v conv_twl_state = "{S:: 'v conc_twl_state. wf_twl_state (raw_state_of_conc S)}"
morphisms list_twl_state_of cls_twl_state
proof -
    have "TWL_State [] [] [] 0 None \<in> {S:: 'v conc_twl_state. wf_twl_state (raw_state_of_conc S)}"
      by (auto simp: wf_twl_state_def)
    then show ?thesis by blast
qed
term list_twl_state_of

definition watch_list :: "'v conv_twl_state \<Rightarrow> 'v literal list \<Rightarrow> 'v literal list twl_clause" where
  "watch_list S' C =
   (let
      M = trail (list_twl_state_of S');
      C' = remdups C;
      negation_not_assigned = filter (\<lambda>L. -L \<notin> lits_of M) C';
      negation_assigned_sorted_by_trail = filter (\<lambda>L. L \<in> set C) (map (\<lambda>L. -lit_of L) M);
      W = take 2 (negation_not_assigned @ negation_assigned_sorted_by_trail);
      UW = foldl (\<lambda>a l. remove1 l a) C W
    in TWL_Clause W UW)"

lemma wf_watch_nat: "no_dup (trail (list_twl_state_of S)) \<Longrightarrow> 
  wf_twl_cls (trail (list_twl_state_of S)) (raw_clause_l (watch_list S C))"
  apply (simp only: watch_list_def Let_def raw_clause_l.simps)
  using wf_watch_witness[of "(list_twl_state_of S)" "C" "mset C"]
oops
(* 
definition
  rewatch_nat ::
  "(nat, nat, nat literal list) ann_literal \<Rightarrow> conc_twl_state \<Rightarrow>
    nat literal list twl_clause \<Rightarrow> nat literal list twl_clause"
where
  "rewatch_nat L S C =
   (if - lit_of L \<in> set (watched C) then
      case filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> lits_of (L # trail S))
          (unwatched C) of
        [] \<Rightarrow> C
      | L' # _ \<Rightarrow>
        TWL_Clause (L' # remove1 (- lit_of L) (watched C)) 
          (- lit_of L # remove1 L' (unwatched C))
    else
      C)"

definition raw_candidates_conflict :: "conc_twl_state \<Rightarrow> nat literal list list" where
  "raw_candidates_conflict S =
    map (\<lambda>T. case T of TWL_Clause W UW \<Rightarrow> W @ UW)
       (filter (\<lambda>C. set (watched C) \<subseteq> (uminus ` lits_of (trail S))) 
       (init_clss S @ learned_clss S))"

definition do_conflict_step :: "conc_twl_state \<Rightarrow> conc_twl_state option" where
"do_conflict_step S =
  (case conflicting S of
    Some _ \<Rightarrow> None
  | None \<Rightarrow>
      (case raw_candidates_conflict S of
        [] \<Rightarrow> None
      | a # _ \<Rightarrow> Some (update_conflicting (Some a) S)))"
 *)
(* 
lemma do_conflict_step_Some:
  assumes conf: "do_conflict_step S = Some T"
  shows "twl.cdcl\<^sub>W_twl.conflict (st_of_raw S) (st_of_raw T)"
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
    by (auto split: list.splits ann_literal.splits split_if_asm simp: conflicting_raw_conflicting)
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
    by (auto split: list.splits ann_literal.splits split_if_asm simp: conflicting_raw_conflicting)
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
    "maximum_level (remove (-L) D) S = raw_backtrack_lvl S" and
    empty: "trail (st_of_raw S) \<noteq> []"
    using conf Some unfolding do_resolve_step_def
    by (auto split: list.splits ann_literal.splits split_if_asm simp: conflicting_raw_conflicting)
  moreover have "trail (st_of_raw S) = Propagated L (cls_of_raw_cls C) # M"
    using empty raw_hd_trail[of S] C M_def by (cases "trail (st_of_raw S)") simp_all
  moreover then have "L \<in># cls_of_raw_cls C"
    using inv unfolding  cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by force
  ultimately show ?thesis
    using resolve_rule[of "st_of_raw S" L "cls_of_raw_cls C - {#L#}" "tl (trail (st_of_raw S))"
      "init_clss (st_of_raw S)"
      "learned_clss (st_of_raw S)" "backtrack_lvl (st_of_raw S)" "cls_of_raw_cls D - {#-L#}"
      "st_of_raw T"]
      state_eq_ref T Some
    by (auto simp: conflicting_raw_conflicting raw_backtrack_lvl)
qed

definition do_backtrack_step :: "'conc_st \<Rightarrow> 'conc_st option" where
"do_backtrack_step S = None"

definition do_bj_step :: "'conc_st \<Rightarrow> 'conc_st option" where
"do_bj_step S =
  (case do_skip_step S of
    Some T \<Rightarrow> Some T
  | None \<Rightarrow>
    (case do_resolve_step S of
      Some T \<Rightarrow> Some T
    | None \<Rightarrow> do_backtrack_step S))"
 *)
end