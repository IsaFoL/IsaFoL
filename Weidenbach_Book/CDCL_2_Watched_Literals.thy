theory CDCL_2_Watched_Literals
imports CDCL_FW (* Have to decide which imports are the best *)
begin

(* TODO: Move to Multiset_More *)
lemma distinct_mem_diff_mset:
  assumes dist: "distinct_mset M" and mem: "x \<in> set_mset (M - N)"
  shows "x \<notin> set_mset N"
proof -
  have "count M x = 1"
    using dist mem by (simp add: distinct_mset_def)
  then show ?thesis
    using mem by simp
qed

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

abbreviation clauses where
"clauses S \<equiv> init_clss S + learned_clss S"

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
      using cand unfolding candidates_propagate_def MNU_defs by blast

    obtain W NW where cw_eq: "Cw = W_Clause W NW"
      by (case_tac Cw, blast)

    have l_w: "L \<in># W"
      by (metis Multiset.diff_le_self cw(3) cw_eq mset_leD multi_member_last w_clause.sel(1))

    have wf_c: "wf_two_wl_cls M Cw"
      using wf \<open>Cw \<in># N + U\<close> unfolding wf_two_wl_state_def by simp

    have w_nw:
      "distinct_mset W"
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
      then have w: "W = {#L#}"
        by (metis (no_types, lifting) Multiset.diff_le_self cw(3) cw_eq single_not_empty
          size_1_singleton_mset subset_mset.add_diff_inverse union_is_single w_clause.sel(1))
      from True have "set_mset NW \<subseteq> set_mset W"
        using w_nw(2) by blast
      then show ?thesis
        using w cw(1) cw_eq by auto
    next
      case sz2: False
      show ?thesis
      proof
        fix L'
        assume l': "L' \<in> set_mset C - {L}"
        have ex_la: "\<exists>La. La \<noteq> L \<and> La \<in># W"
        proof (cases W)
          case empty
          thus ?thesis
            using l_w by auto
        next
          case lb: (add W' Lb)
          show ?thesis
          proof (cases W')
            case empty
            thus ?thesis
              using lb sz2 by simp
          next
            case lc: (add W'' Lc)
            thus ?thesis
              by (metis add_gr_0 count_union distinct_mset_single_add lb union_single_eq_member
                w_nw(1))
          qed
        qed
        then obtain La where la: "La \<noteq> L" "La \<in># W"
          by blast
        then have "La \<in># mset_set (uminus ` lits_of M)"
          using cw(3)[unfolded cw_eq, simplified, folded M_def]
          by (metis count_diff count_single diff_zero not_gr0)
        then have nla: "-La \<in> lits_of M"
          by auto
        then show "-L' \<in> lits_of M"
        (* generated by Sledgehammer *)
        proof -
          have f1: "L' \<in> set_mset C"
            using l' by blast
          have f2: "L' \<notin> {L}"
            using l' by fastforce
          have "\<And>l L. - (l::'a literal) \<in> L \<or> l \<notin> uminus ` L"
            by force
          then have "\<And>l. - l \<in> lits_of M \<or> count {#L#} l = count (C - NW) l"
            by (metis (no_types) add_diff_cancel_right' count_diff count_mset_set(3) cw(1) cw(3)
                  cw_eq diff_zero w_clause.sel(2))
          then show ?thesis
            using f2 f1 by (metis nla count_diff diff_zero la(2) mem_set_mset_iff not_gr0
              set_mset_single w_nw(3))
        qed
      qed
    qed
    then show "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))"
      unfolding true_annots_def by auto

    show "undefined_lit L (trail S)"
      using cw(4) M_def by blast
  qed

lemma wf_candidates_propagate_complete:
  assumes wf: "wf_two_wl_state S" and
    mem: "C \<in># image_mset clause_of_w_clause (clauses S)" and
    unsat: "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))" and
    undef: "undefined_lit L (trail S)"
  shows "(L, C) \<in> candidates_propagate S"
  proof -
    def M \<equiv> "trail S"
    def N \<equiv> "init_clss S"
    def U \<equiv> "learned_clss S"

    note MNU_defs [simp] = M_def N_def U_def

    obtain Cw where ca: "C = clause_of_w_clause Cw" "Cw \<in># N + U"
      using mem by force

    obtain W NW where cw_eq: "Cw = W_Clause W NW"
      by (case_tac Cw, blast)

    have wf_c: "wf_two_wl_cls M Cw"
      using wf \<open>Cw \<in># N + U\<close> unfolding wf_two_wl_state_def by simp

    have w_nw:
      "distinct_mset W"
      "size W < 2 \<Longrightarrow> set_mset NW \<subseteq> set_mset W"
      "\<And>L L'. L \<in># W \<Longrightarrow> -L \<in> lits_of M \<Longrightarrow> L' \<in># NW \<Longrightarrow> -L' \<in> lits_of M"
     using wf_c unfolding cw_eq by auto

(*
    have "\<And>L'. L' \<in> set_mset C \<Longrightarrow> L' \<noteq> L \<Longrightarrow> -L' \<in> lits_of M"
      sorry
*)

    have unit_set: "set_mset (W - mset_set (uminus ` lits_of M)) = {L}"
    proof
      show "set_mset (W - mset_set (uminus ` lits_of M)) \<subseteq> {L}"
      proof
        fix L'
        assume l': "L' \<in> set_mset (W - mset_set (uminus ` lits_of M))"
        hence l'_mem_w: "L' \<in> set_mset W"
          by auto
        have "L' \<notin> uminus ` lits_of M"
          using distinct_mem_diff_mset[OF w_nw(1) l'] by simp
        then have "\<not> M \<Turnstile>a {#-L'#}"
          using image_iff by fastforce
        moreover have "L' \<in># C"
          using ca(1) cw_eq l'_mem_w by auto
        ultimately have "L' = L"
          unfolding M_def by (metis unsat[unfolded CNot_def true_annots_def, simplified])
        then show "L' \<in> {L}"
          by simp
      qed
    next
      show "{L} \<subseteq> set_mset (W - mset_set (uminus ` lits_of M))"
        sorry
    qed

    have unit: "W - mset_set (uminus ` lits_of M) = {#L#}"
      sorry

    show ?thesis
      unfolding candidates_propagate_def using ca unit undef by blast
  qed

lemma wf_candidates_conflict_sound:
  assumes wf: "wf_two_wl_state S" and
    cand: "C \<in> candidates_conflict S"
  shows "trail S \<Turnstile>as CNot C \<and> C \<in># image_mset clause_of_w_clause (clauses S)"
  sorry

lemma wf_candidates_conflict_complete:
  assumes wf: "wf_two_wl_state S" and
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