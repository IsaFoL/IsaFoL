theory CDCL_2_Watched_Literals
imports CDCL_FW (* Have to decide which imports are the best *)
begin

text \<open>Only the 2-watched literals have to be verified here: the backtrack level and the trail can
  remain separate.\<close>

datatype 'v w_clause =
  W_Clause (watched: "'v clause") (not_watched: "'v clause")

abbreviation clause_of_w_clause :: "'v w_clause \<Rightarrow> 'v clause" where
"clause_of_w_clause C \<equiv> watched C + not_watched C"

datatype ('v, 'lvl, 'mark) two_wl_state =
  Two_WL_State (trail: "('v, 'lvl, 'mark) annoted_lits") (init_clss: "'v w_clause multiset")
    (learned_clss: "'v w_clause multiset") (backtrack_lvl: 'lvl)
    (conflicting: "'v clause conflicting_clause")

definition clauses where
"clauses S = init_clss S + learned_clss S"

definition
  candidates_propagate :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> ('v literal \<times> 'v clause) set"
where
"candidates_propagate S = 
  {(L, clause_of_w_clause C) |
   L C. C \<in># clauses S \<and> watched C - mset_set (uminus ` lits_of (trail S)) = {#L#} \<and>
        undefined_lit L (trail S)}"

definition candidates_conflict :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> 'v clause set" where
"candidates_conflict S = 
  {clause_of_w_clause C |
   L C. C \<in># clauses S \<and> watched C \<subseteq># mset_set (uminus ` lits_of (trail S)) \<and> L \<in># watched C}"

interpretation dpll_state trail "image_mset clause_of_w_clause o clauses"
  "\<lambda>M S. Two_WL_State M (init_clss S) (learned_clss S) (backtrack_lvl S) (conflicting S)"
oops

primrec wf_two_wl_cls :: "('v, 'lvl, 'mark) marked_lit list \<Rightarrow> 'v w_clause \<Rightarrow> bool" where
  "wf_two_wl_cls M (W_Clause W NW) \<longleftrightarrow>
   distinct_mset W \<and> size W \<le> 2 \<and> (size W < 2 \<longrightarrow> set_mset NW \<subseteq> set_mset W) \<and>
   (\<forall>L \<in># W. -L \<in> lits_of M \<longrightarrow> (\<forall>L' \<in># NW. -L' \<in> lits_of M))"

definition wf_two_wl_state :: "('v, 'lvl, 'mark) two_wl_state \<Rightarrow> bool" where
  "wf_two_wl_state S \<longleftrightarrow> (\<forall>C \<in># clauses S. wf_two_wl_cls (trail S) C)"

lemma wf_candidates_propagate_sound:
  assumes wf: "wf_two_wl_state S" and
    cand: "(L, C) \<in> candidates_propagate S"
  shows "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L})) \<and> undefined_lit L (trail S)"
  proof
    def M \<equiv> "trail S"
    def N \<equiv> "init_clss S"
    def U \<equiv> "learned_clss S"

    note MNU_defs [simp] = M_def N_def U_def

    obtain Cw where cw:
      "C = clause_of_w_clause Cw"
      "Cw \<in># N + U"
      "watched Cw - mset_set (uminus ` lits_of M) = {#L#}"
      "undefined_lit L M"
      using cand unfolding candidates_propagate_def MNU_defs clauses_def by blast

    obtain W NW where cw_eq: "Cw = W_Clause W NW" by (case_tac Cw, blast)

    have wf_c: "wf_two_wl_cls M Cw"
      using wf \<open>Cw \<in># N + U\<close> unfolding clauses_def wf_two_wl_state_def by simp

    have w_nw:
      "distinct_mset W"
      "size W \<le> 2"
      "size W < 2 \<Longrightarrow> set_mset NW \<subseteq> set_mset W"
      "\<And>L L'. L \<in># W \<Longrightarrow> -L \<in> lits_of M \<Longrightarrow> L' \<in># NW \<Longrightarrow> -L' \<in> lits_of M"
     using wf_c unfolding cw_eq by auto

    have "\<forall>L' \<in> set_mset C - {L}. -L' \<in> lits_of M"
    proof (cases "size W < 2")
      case True
      moreover have "size W \<noteq> 0"
        using cw(3) cw_eq by auto
      ultimately have "size W = 1"
        by linarith
      then have "W = {#L#}"
        by (metis (no_types, lifting) Multiset.diff_le_self cw(3) cw_eq single_not_empty
          size_1_singleton_mset subset_mset.add_diff_inverse union_is_single w_clause.sel(1))
      from True have "set_mset NW \<subseteq> set_mset W"
        using w_nw(3) by blast
      show ?thesis
        using \<open>W = {#L#}\<close> \<open>set_mset NW \<subseteq> set_mset W\<close> cw(1) cw_eq by auto
    next
      case False
      show ?thesis
        sorry
    qed

    show "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))"
      unfolding true_annots_def CNot_def
      using \<open>\<forall>L'\<in>set_mset C - {L}. - L' \<in> lits_of M\<close> by auto

    show "undefined_lit L (trail S)"
      using cw(4) M_def by blast
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