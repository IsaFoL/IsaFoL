theory CDCL_2_Watched_Literals
imports CDCL_FW (* Have to decide which imports are the best *)
begin

text \<open>Only the 2-watched literals have to be verified here: the backtrack level and the trail can
  remain separate.\<close>

datatype 'v w_clause =
  W_Clause (watched: "'v clause") (not_watched: "'v clause")

abbreviation clause_of_w_clause :: "'v w_clause \<Rightarrow> 'v clause" where
"clause_of_w_clause C \<equiv> watched C + not_watched C"

type_synonym ('v, 'lvl, 'mark) two_wl_state =
  "('v, 'lvl, 'mark) annoted_lits \<times> 'v w_clause multiset \<times> 'v w_clause multiset \<times> 'lvl \<times>
   'v clause conflicting_clause"

abbreviation trail :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" where
"trail \<equiv> \<lambda>(M, _). M"

abbreviation init_clss :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'v w_clause multiset" where
"init_clss \<equiv> \<lambda>(_,N, _). N"

abbreviation learned_clss :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'v w_clause multiset" where
"learned_clss \<equiv> \<lambda>(_,_, U, _). U"

abbreviation backtrack_lvl :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'lvl" where
"backtrack_lvl \<equiv> \<lambda>(_,_, _,k, _). k"

abbreviation conflicting :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'v clause conflicting_clause" where
"conflicting \<equiv> \<lambda>(_,_, _,_, C). C"

fun candidates_propagate :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> ('v literal \<times> 'v clause) set" where
"candidates_propagate (M, N, U, _, _) = 
  {(L, clause_of_w_clause C)
     |L C. C \<in># N + U \<and> watched C - mset_set (uminus ` lits_of M) = {#L#} \<and> undefined_lit L M}"

fun candidates_conflict :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'v clause set" where
"candidates_conflict (M, N, U, k, _) = 
  {clause_of_w_clause C
     |L C. C \<in># N + U \<and> watched C \<subseteq># mset_set (uminus ` lits_of M) \<and> L \<in># watched C}"

definition clauses where
"clauses S = init_clss S + learned_clss S"


interpretation dpll_state trail "image_mset clause_of_w_clause o clauses" "\<lambda>M (_, S). (M, S)"
oops

primrec wf_two_wl_cls :: "('v, 'lvl, 'mark) marked_lit list \<Rightarrow> 'v w_clause \<Rightarrow> bool" where
  "wf_two_wl_cls M (W_Clause W NW) \<longleftrightarrow>
   distinct_mset W \<and> size W \<le> 2 \<and> (size W < 2 \<longrightarrow> set_mset NW \<subseteq> set_mset W) \<and>
   (\<forall>L \<in># W. -L \<in> lits_of M \<longrightarrow> (\<forall>L' \<in># NW. -L' \<in> lits_of M))"

fun
  wf_two_wl_state :: "('v, 'lvl, 'mark) marked_lit list \<Rightarrow> ('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool"
where
  "wf_two_wl_state M (_, N, U, _) \<longleftrightarrow> (\<forall>C \<in># N + U. wf_two_wl_cls M C)"

lemma wf_candidates_propagate_sound:
  assumes wf: "wf_two_wl_state (trail S) S" and
    cand: "(L, C) \<in> candidates_propagate S"
  shows "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L})) \<and> undefined_lit L (trail S)"
  proof
    obtain M N U k c where s: "S = (M, N, U, k, c)"
      using candidates_propagate.cases by blast
    then obtain Cw where cw:
      "C = clause_of_w_clause Cw" and
      "Cw \<in># N + U" and
      "watched Cw - mset_set (uminus ` lits_of M) = {#L#}" and
      "undefined_lit L M"
      using cand by auto

    obtain W NW where cw_eq: "Cw = W_Clause W NW" by (case_tac Cw, blast)

    have wf_c: "wf_two_wl_cls M Cw"
      using wf \<open>Cw \<in># N + U\<close> unfolding s by simp

    have "\<forall>L' \<in> set_mset C - {L}. -L' \<in> lits_of M"
      sorry
    show "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))"
      unfolding s
      apply simp
      unfolding true_annots_def CNot_def
      using \<open>\<forall>L'\<in>set_mset C - {L}. - L' \<in> lits_of M\<close> by auto
    show "undefined_lit L (trail S)"
      sorry
  qed

lemma wf_candidates_propagate_complete:
  assumes wf: "wf_two_wl_state (trail S) S" and
    unsat: "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))" and
    undef: "undefined_lit L (trail S)"
  shows "candidates_propagate S \<noteq> {}"
  sorry

lemma wf_candidates_conflict_sound:
  assumes wf: "wf_two_wl_state (trail S) S" and
    cand: "C \<in> candidates_conflict S"
  shows "trail S \<Turnstile>as CNot C \<and> C \<in># image_mset clause_of_w_clause (clauses S)"
  sorry

lemma wf_candidates_conflict_complete:
  assumes wf: "wf_two_wl_state (trail S) S" and
    unsat: "trail S \<Turnstile>as CNot C" and
    mem: "C \<in># image_mset clause_of_w_clause (clauses S)"
  shows "candidates_conflict S \<noteq> {}"
  sorry

locale structure_2_WL =
  fixes choose :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'v clause \<Rightarrow> 'v w_clause"
  assumes choose: "wf_two_wl_cls (trail S) (choose S C)"
begin

(* 
fun one_is_true :: "'v w_clause \<Rightarrow> ('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool"  where
"one_is_true (W_Clause w _) S = (\<exists>L\<in># w. L \<in> lits_of (trail S))"

fun one_is_false_and_candidate :: "'v w_clause \<Rightarrow> ('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool" where
"one_is_false_and_candidate (W_Clause w uw) S =
  (\<exists>L\<in># w. \<exists>L' \<in># w - {#L#}.  -L \<in> lits_of (trail S) \<and> Propagated L' (w + uw) \<in> (candidates S))"

fun two_unassigned :: "'v w_clause \<Rightarrow> ('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool" where
"two_unassigned (W_Clause w _) S \<longleftrightarrow> (\<forall>L \<in># w. undefined_lit L ((trail S)))"

text \<open>There are two watched literals except when there is no literal to watch.\<close>
fun less_than_two_watched :: "'v w_clause \<Rightarrow> ('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool" where
"less_than_two_watched C S \<longleftrightarrow>
  (size (watched C) \<le> 2
    \<and> (size (watched C) \<le> 1 \<longrightarrow> not_watched C = {#}))"

definition watched_lits :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool"  where
"watched_lits S =
  (\<forall>C \<in># clauses S. less_than_two_watched C S
    \<and> (one_is_true C S \<or> two_unassigned C S \<or> less_than_two_watched C S))"

fun tl_trail :: "('v, 'lvl, 'mark) two_wl_state  \<Rightarrow>  ('v, 'lvl, 'mark) two_wl_state " where
"tl_trail (M, S) = (tl M, S)"

lemma tl_trail:
  "watched_lits S \<Longrightarrow> watched_lits (tl_trail S)"
  unfolding watched_lits_def by (cases S) (auto simp: clauses_def)
 *)

end

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn _ _ _ _ (* propagate_conds is in candidates *) _ _ _ 
  (* backjump_conds is candidate_conflict *)
oops

(* implementation of choose *)
interpretation structure_2_WL
oops

interpretation cw_state
oops

interpretation cdcl_cw_ops
oops

end