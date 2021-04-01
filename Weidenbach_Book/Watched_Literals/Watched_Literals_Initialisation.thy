theory Watched_Literals_Initialisation
  imports Watched_Literals_List
begin

chapter \<open>Initialisation of Data structure\<close>

type_synonym 'v twl_st_init = \<open>'v twl_st  \<times> 'v clauses\<close>


fun get_trail_init :: \<open>'v twl_st_init \<Rightarrow> ('v, 'v clause) ann_lit list\<close> where
  \<open>get_trail_init ((M, _, _, _, _, _, _), _) = M\<close>

fun get_conflict_init :: \<open>'v twl_st_init \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_init ((_, _, _, D, _, _, _, _), _) = D\<close>

fun literals_to_update_init :: \<open>'v twl_st_init \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_init ((_, _, _, _, _, _, _, _, _, _, _, Q), _) = Q\<close>

fun get_init_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v twl_cls multiset\<close> where
  \<open>get_init_clauses_init ((_, N, _, _, _, _, _, _), _) = N\<close>

fun get_learned_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v twl_cls multiset\<close> where
  \<open>get_learned_clauses_init ((_, _, U, _, _, _, _, _), _) = U\<close>

fun get_unit_init_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clauses_init ((_, _, _, _, NE, _, _, _), _) = NE\<close>

fun get_unit_learned_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned_clauses_init ((_, _, _, _, _, UE, _, _), _) = UE\<close>

fun get_subsumed_init_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_init_clauses_init ((_, _, _, _, _, _, NS, US, _, _), _) = NS\<close>

fun get_subsumed_learned_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_learned_clauses_init ((_, _, _, _, _, _, NS, US, _, _), _) = US\<close>

fun get_subsumed_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_clauses_init ((_, _, _, _, _, _, NS, US, _, _), _) = NS + US\<close>

fun clauses_to_update_init :: \<open>'v twl_st_init \<Rightarrow> ('v literal \<times> 'v twl_cls) multiset\<close> where
  \<open>clauses_to_update_init ((_, _, _, _, _, _, _, _, _, _, WS, _), _) = WS\<close>

fun other_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>other_clauses_init ((_, _, _, _, _, _, _), OC) = OC\<close>

fun get_init_clauses0_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_init_clauses0_init ((_, _, _, _, _, _, NS, US, N0, U0,_, _), _) = N0\<close>

fun get_learned_clauses0_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_learned_clauses0_init ((_, _, _, _, _, _, NS, US, N0, U0,_, _), _) = U0\<close>

fun add_to_init_clauses :: \<open>'v clause_l \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
  \<open>add_to_init_clauses C ((M, N, U, D, NE, UE, NS, US, WS, Q), OC) =
      ((M, add_mset (twl_clause_of C) N, U, D, NE, UE, NS, US, WS, Q), OC)\<close>

fun add_to_unit_init_clauses :: \<open>'v clause \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
  \<open>add_to_unit_init_clauses C ((M, N, U, D, NE, UE, NS, US, WS, Q), OC) =
      ((M, N, U, D, add_mset C NE, UE, NS, US, WS, Q), OC)\<close>

fun set_conflict_init :: \<open>'v clause_l \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
 \<open>set_conflict_init C ((M, N, U, _, NE, UE, NS, US, N0, U0, WS, Q), OC) =
       ((M, N, U, Some (mset C), add_mset (mset C) NE, UE, NS, US, N0, U0, {#}, {#}), OC)\<close>

fun propagate_unit_init :: \<open>'v literal \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
 \<open>propagate_unit_init L ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC) =
       ((Propagated L {#L#} # M, N, U, D, add_mset {#L#} NE, UE, NS, US, N0, U0, WS, add_mset (-L) Q), OC)\<close>

fun add_empty_conflict_init :: \<open>'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
 \<open>add_empty_conflict_init ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC) =
       ((M, N, U, Some {#}, NE, UE, NS, US, add_mset {#} N0, U0, WS, {#}), OC)\<close>

fun add_to_clauses_init :: \<open>'v clause_l \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
   \<open>add_to_clauses_init C ((M, N, U, D, NE, UE, NS, US, WS, Q), OC) =
        ((M, add_mset (twl_clause_of C) N, U, D, NE, UE, NS, US, WS, Q), OC)\<close>

type_synonym 'v twl_st_l_init = \<open>'v twl_st_l \<times> 'v clauses\<close>

fun get_trail_l_init :: \<open>'v twl_st_l_init \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_l_init ((M, _, _, _, _, _, _), _) = M\<close>

fun get_conflict_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_l_init ((_, _, D, _, _, _, _), _) = D\<close>

fun get_unit_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_clauses_l_init ((M, N, D, NE, UE, NS, US, WS, Q), _) = NE + UE\<close>

fun get_learned_unit_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_learned_unit_clauses_l_init ((M, N, D, NE, UE, WS, Q), _) = UE\<close>

fun get_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_l_init ((M, N, D, NE, UE, NS, US, WS, Q), _) = N\<close>

fun literals_to_update_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_l_init ((_, _, _, _, _, NS, US, N0, U0, _, Q), _) = Q\<close>

fun clauses_to_update_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses_to_update_l\<close> where
  \<open>clauses_to_update_l_init ((_, _, _, _, _, NS, US, N0, U0, WS, _), _) = WS\<close>

fun other_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>other_clauses_l_init ((_, _, _, _, _, _, _), OC) = OC\<close>

fun pstate\<^sub>W_of_init :: "'v twl_st_init \<Rightarrow> 'v prag_st" where
\<open>pstate\<^sub>W_of_init ((M, N, U, C, NE, UE, NS, US, N0, U0, Q), OC) =
  (M, clause `# N + OC, clause `# U, C, NE, UE, NS, US, N0, U0)\<close>

fun state\<^sub>W_of_init :: "'v twl_st_init \<Rightarrow> 'v cdcl\<^sub>W_restart_mset" where
"state\<^sub>W_of_init (S) = state_of (pstate\<^sub>W_of_init S)"

fun get_subsumed_init_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_init_clauses_l_init ((_, _, _, _, _, NS, US, _, _), _) = NS\<close>

fun get_subsumed_learned_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_learned_clauses_l_init ((M, N, D, NE, UE, NS, US, WS, Q), _) = US\<close>

fun get_subsumed_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_clauses_l_init ((M, N, D, NE, UE, NS, US, WS, Q), _) = NS+US\<close>


fun get_init_clauses0_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_init_clauses0_l_init ((_, _, _, _, _, NS, US, N0, U0, _, _), _) = N0\<close>

fun get_learned_clauses0_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_learned_clauses0_l_init ((M, N, D, NE, UE, NS, US, N0, U0,WS, Q), _) = U0\<close>

fun get_clauses0_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_clauses0_l_init ((M, N, D, NE, UE, NS, US, N0, U0,WS, Q), _) = N0+U0\<close>


named_theorems twl_st_init \<open>Convertion for inital theorems\<close>

lemma [twl_st_init]:
  \<open>get_conflict_init (S, QC) = get_conflict S\<close>
  \<open>get_trail_init (S, QC) = get_trail S\<close>
  \<open>clauses_to_update_init (S, QC) = clauses_to_update S\<close>
  \<open>literals_to_update_init (S, QC) = literals_to_update S\<close>
  by (solves \<open>cases S; auto\<close>)+

lemma [twl_st_init]:
  \<open>clauses_to_update_init (add_to_unit_init_clauses (mset C) T) = clauses_to_update_init T\<close>
  \<open>literals_to_update_init (add_to_unit_init_clauses (mset C) T) = literals_to_update_init T\<close>
  \<open>get_conflict_init (add_to_unit_init_clauses (mset C) T) = get_conflict_init T\<close>
  apply (cases T; auto simp: twl_st_inv.simps; fail)+
  done
lemma [twl_st_init]:
  \<open>twl_st_inv (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow>  twl_st_inv (fst T)\<close>
  \<open>valid_enqueued (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow> valid_enqueued (fst T)\<close>
  \<open>no_duplicate_queued (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow> no_duplicate_queued (fst T)\<close>
  \<open>distinct_queued (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow> distinct_queued (fst T)\<close>
  \<open>confl_cands_enqueued (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow> confl_cands_enqueued (fst T)\<close>
  \<open>propa_cands_enqueued (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow> propa_cands_enqueued (fst T)\<close>
  \<open>twl_st_exception_inv (fst (add_to_unit_init_clauses (mset C) T)) \<longleftrightarrow> twl_st_exception_inv (fst T)\<close>
    apply (cases T; auto simp: twl_st_inv.simps; fail)+
  apply (cases \<open>get_conflict_init T\<close>; cases T;
      auto simp: twl_st_inv.simps twl_exception_inv.simps; fail)+
  done

lemma [twl_st_init]:
  \<open>trail (state\<^sub>W_of_init T) = get_trail_init T\<close>
  \<open>get_trail (fst T) = get_trail_init (T)\<close>
  \<open>conflicting (state\<^sub>W_of_init T) = get_conflict_init T\<close>
  \<open>init_clss (state\<^sub>W_of_init T) = clauses (get_init_clauses_init T) + get_unit_init_clauses_init T +
    get_subsumed_init_clauses_init T + get_init_clauses0_init T + other_clauses_init T\<close>
  \<open>learned_clss (state\<^sub>W_of_init T) = clauses (get_learned_clauses_init T) +
     get_unit_learned_clauses_init T + get_subsumed_learned_clauses_init T + get_learned_clauses0_init T\<close>
  \<open>conflicting (state\<^sub>W_of (fst T)) = conflicting (state\<^sub>W_of_init T)\<close>
  \<open>trail (state\<^sub>W_of (fst T)) = trail (state\<^sub>W_of_init T)\<close>
  \<open>clauses_to_update (fst T) = clauses_to_update_init T\<close>
  \<open>get_conflict (fst T) =  get_conflict_init T\<close>
  \<open>literals_to_update (fst T) = literals_to_update_init T\<close>
  \<open>subsumed_learned_clss (fst T) = get_subsumed_learned_clauses_init T\<close>
  by (cases T; auto simp: cdcl\<^sub>W_restart_mset_state; fail)+

definition twl_st_l_init :: \<open>('v twl_st_l_init \<times> 'v twl_st_init) set\<close> where
  \<open>twl_st_l_init = {(((M, N, C, NE, UE, NS, US, N0, U0, WS, Q), OC),
      ((M', N', C', NE', UE', NS', US', N0', U0', WS', Q'), OC')).
    (M , M') \<in> convert_lits_l N (NE+UE) \<and>
    ((N', C', NE', UE', NS', US', N0', U0', WS', Q'), OC') =
      ((twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N,
         C, NE, UE, NS, US, N0, U0, {#}, Q), OC)}\<close>

lemma twl_st_l_init_alt_def:
  \<open>(S, T) \<in> twl_st_l_init \<longleftrightarrow>
    (fst S, fst T) \<in> twl_st_l None \<and> other_clauses_l_init S = other_clauses_init T\<close>
  by (cases S; cases T) (auto simp: twl_st_l_init_def twl_st_l_def)

lemma [twl_st_init]:
  assumes \<open>(S, T) \<in> twl_st_l_init\<close>
  shows
   \<open>get_conflict_init T = get_conflict_l_init S\<close>
   \<open>get_conflict (fst T) = get_conflict_l_init S\<close>
   \<open>literals_to_update_init T = literals_to_update_l_init S\<close>
   \<open>clauses_to_update_init T = {#}\<close>
   \<open>other_clauses_init T = other_clauses_l_init S\<close>
   \<open>lits_of_l (get_trail_init T) = lits_of_l (get_trail_l_init S)\<close>
   \<open>lit_of `# mset (get_trail_init T) = lit_of `# mset (get_trail_l_init S)\<close>
   by (use assms in \<open>solves \<open>cases S; auto simp: twl_st_l_init_def\<close>\<close>)+

definition twl_struct_invs_init :: \<open>'v twl_st_init \<Rightarrow> bool\<close> where
  \<open>twl_struct_invs_init S \<longleftrightarrow>
    (twl_st_inv (fst S) \<and>
    valid_enqueued (fst S) \<and>
    pcdcl_all_struct_invs (pstate\<^sub>W_of_init S) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of_init S) \<and>
    twl_st_exception_inv (fst S) \<and>
    no_duplicate_queued (fst S) \<and>
    distinct_queued (fst S) \<and>
    confl_cands_enqueued (fst S) \<and>
    propa_cands_enqueued (fst S) \<and>
    (get_conflict_init S \<noteq> None \<longrightarrow> clauses_to_update_init S = {#} \<and> literals_to_update_init S = {#}) \<and>
    clauses_to_update_inv (fst S) \<and>
    past_invs (fst S))
  \<close>

lemma state\<^sub>W_of_state\<^sub>W_of_init:
  \<open>other_clauses_init W = {#} \<Longrightarrow> state\<^sub>W_of (fst W) = state\<^sub>W_of_init W\<close>
  by (cases W) auto

lemma twl_struct_invs_init_twl_struct_invs:
  \<open>other_clauses_init W = {#} \<Longrightarrow> twl_struct_invs_init W \<Longrightarrow> twl_struct_invs (fst W)\<close>
  unfolding twl_struct_invs_def twl_struct_invs_init_def
  apply (subst state\<^sub>W_of_state\<^sub>W_of_init; assumption?)+
  apply (intro iffI impI conjI)
  by (cases W; clarsimp simp: twl_st_init)+


(* lemma twl_struct_invs_init_add_mset:
 *   assumes \<open>twl_struct_invs_init (S, QC)\<close> and [simp]: \<open>distinct_mset C\<close> and
 *     count_dec: \<open>count_decided (trail (state\<^sub>W_of S)) = 0\<close>
 *   shows \<open>twl_struct_invs_init (S, add_mset C QC)\<close>
 * proof -
 *   have
 *     st_inv: \<open>twl_st_inv S\<close> and
 *     valid: \<open>valid_enqueued S\<close> and
 *     struct: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init (S, QC))\<close> and
 *     smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of_init (S, QC))\<close> and
 *     excep: \<open>twl_st_exception_inv S\<close> and
 *     no_dup: \<open>no_duplicate_queued S\<close> and
 *     dist: \<open>distinct_queued S\<close> and
 *     cands_confl: \<open>confl_cands_enqueued S\<close> and
 *     cands_propa: \<open>propa_cands_enqueued S\<close> and
 *     confl: \<open>get_conflict S \<noteq> None \<longrightarrow> clauses_to_update S = {#} \<and> literals_to_update S = {#}\<close> and
 *     to_upd: \<open>clauses_to_update_inv S\<close> and
 *     past: \<open>past_invs S\<close>
 *     using assms unfolding twl_struct_invs_init_def fst_conv
 *     by (auto simp add: twl_st_init)
 * 
 *   show ?thesis
 *     unfolding twl_struct_invs_init_def fst_conv
 *     apply (intro conjI)
 *     subgoal by (rule st_inv)
 *     subgoal by (rule valid)
 *     subgoal using struct count_dec no_dup unfolding pcdcl_all_struct_invs_def
 *       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
 *       apply (intro conjI)
 *       apply (cases S; simp add: clauses_def
 *           cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_strange_atm_def
 *           cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def psubsumed_invs_def
 *         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
 *            entailed_clss_inv_def
 *           cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
 *           cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def; fail)+
 *     subgoal using smaller count_dec by (cases S)(auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
 *           cdcl\<^sub>W_restart_mset_state)
 *     subgoal by (rule excep)
 *     subgoal by (rule no_dup)
 *     subgoal by (rule dist)
 *     subgoal by (rule cands_confl)
 *     subgoal by (rule cands_propa)
 *     subgoal using confl by (auto simp: twl_st_init)
 *     subgoal by (rule to_upd)
 *     subgoal by (rule past)
 *     done
 * qed *)

fun add_empty_conflict_init_l :: \<open>'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  add_empty_conflict_init_l_def[simp del]:
   \<open>add_empty_conflict_init_l ((M, N, D, NE, UE, NS, US, N0, U0, WS, Q), OC) =
       ((M, N, Some {#}, NE, UE, NS, US, add_mset {#} N0, U0, WS, {#}), OC)\<close>


fun propagate_unit_init_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l_init \<Rightarrow> ('v twl_st_l_init) nres\<close> where
  propagate_unit_init_l_def[simp del]:
   \<open>propagate_unit_init_l L ((M, N, D, NE, UE, NS, US, N0, U0, WS, Q), OC) = do {
       M \<leftarrow> cons_trail_propagate_l L 0 M;
       RETURN ((M, N, D, add_mset {#L#} NE, UE, NS, US, N0, U0, WS, add_mset (-L) Q), OC)
     }\<close>


fun already_propagated_unit_init_l :: \<open>'v clause \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  already_propagated_unit_init_l_def[simp del]:
   \<open>already_propagated_unit_init_l C ((M, N, D, NE, UE, NS, US, WS, Q), OC) =
       ((M, N, D, add_mset C NE, UE, NS, US, WS, Q), OC)\<close>


fun set_conflict_init_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  set_conflict_init_l_def[simp del]:
   \<open>set_conflict_init_l C ((M, N, _, NE, UE, NS, US, N0, U0, WS, Q), OC) =
       ((M, N, Some (mset C), add_mset (mset C) NE, UE, NS, US, N0, U0, {#}, {#}), OC)\<close>


fun add_to_clauses_init_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init nres\<close> where
  add_to_clauses_init_l_def[simp del]:
   \<open>add_to_clauses_init_l C ((M, N, _, NE, UE, NS, US, WS, Q), OC) = do {
        i \<leftarrow> get_fresh_index N;
        RETURN ((M, fmupd i (C, True) N, None, NE, UE, NS, US, WS, Q), OC)
    }\<close>

  (*TODO Move*)
fun add_to_tautology_init :: \<open>'v clause \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
  add_to_tautology_init_def[simp del]:
  \<open>add_to_tautology_init C ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC) =
  ((M, N, U, D, NE, UE, add_mset (remdups_mset C) NS, US, N0, U0, WS, Q), OC)\<close>


fun add_to_tautology_init_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  add_to_tautology_init_l_def[simp del]:
  \<open>add_to_tautology_init_l C ((M, N, D, NE, UE, NS, US, N0, U0, WS, Q), OC) =
  ((M, N, D, NE, UE, add_mset (remdups_mset (mset C)) NS, US, N0, U0, WS, Q), OC)\<close>

fun add_to_other_init where
  \<open>add_to_other_init C (S, OC) = (S, add_mset (remdups_mset (mset C)) OC)\<close>

lemma fst_add_to_other_init [simp]: \<open>fst (add_to_other_init a T) = fst T\<close>
  by (cases T) auto

definition remdups_clause where
  \<open>remdups_clause C = SPEC (\<lambda>C'. mset C' = remdups_mset (mset C))\<close>

definition init_dt_step :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init nres\<close> where
  \<open>init_dt_step C S =
  (case get_conflict_l_init S of
    None \<Rightarrow> 
      if tautology (mset C)
      then RETURN (add_to_tautology_init_l C S)
      else do {
        C \<leftarrow> remdups_clause C;
        if length C = 0
      then RETURN (add_empty_conflict_init_l S)
      else if length C = 1
      then
        let L = hd C in
        if undefined_lit (get_trail_l_init S) L
        then propagate_unit_init_l L S
        else if L \<in> lits_of_l (get_trail_l_init S)
        then RETURN (already_propagated_unit_init_l (mset C) S)
        else RETURN (set_conflict_init_l C S)
      else 
          add_to_clauses_init_l C S
    }
  | Some D \<Rightarrow>
      RETURN (add_to_other_init C S))\<close>

definition init_dt :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init nres\<close> where
  \<open>init_dt CS S = nfoldli CS (\<lambda>_. True) init_dt_step S\<close>

definition init_dt_pre :: \<open>'v clause_l list \<Rightarrow> _\<close> where
  \<open>init_dt_pre CS SOC \<longleftrightarrow>
    (\<exists>T. (SOC, T) \<in> twl_st_l_init \<and>
      twl_struct_invs_init T \<and>
      clauses_to_update_l_init SOC = {#} \<and>
      (\<forall>s\<in>set (get_trail_l_init SOC). \<not>is_decided s) \<and>
      (get_conflict_l_init SOC = None \<longrightarrow>
          literals_to_update_l_init SOC = uminus `# lit_of `# mset (get_trail_l_init SOC)) \<and>
      twl_list_invs (fst SOC) \<and>
      twl_stgy_invs (fst T) \<and>
      (other_clauses_l_init SOC \<noteq> {#} \<longrightarrow> get_conflict_l_init SOC \<noteq> None))\<close>

lemma init_dt_pre_ConsD: \<open>init_dt_pre (a # CS) SOC \<Longrightarrow> init_dt_pre CS SOC\<close>
  unfolding init_dt_pre_def
  apply normalize_goal+
  by fastforce

definition init_dt_spec where
  \<open>init_dt_spec CS SOC SOC' \<longleftrightarrow>
     (\<exists>T'. (SOC', T') \<in> twl_st_l_init \<and>
           twl_struct_invs_init T' \<and>
           clauses_to_update_l_init SOC' = {#} \<and>
           (\<forall>s\<in>set (get_trail_l_init SOC'). \<not>is_decided s) \<and>
           (get_conflict_l_init SOC' = None \<longrightarrow>
              literals_to_update_l_init SOC' = uminus `# lit_of `# mset (get_trail_l_init SOC')) \<and>
           (remdups_mset `# mset `# mset CS + mset `# ran_mf (get_clauses_l_init SOC) + other_clauses_l_init SOC +
                 get_unit_clauses_l_init SOC + get_subsumed_init_clauses_l_init SOC+ get_init_clauses0_l_init SOC =
            mset `# ran_mf (get_clauses_l_init SOC') + other_clauses_l_init SOC'  +
                get_unit_clauses_l_init SOC' + get_subsumed_init_clauses_l_init SOC' +
                get_init_clauses0_l_init SOC') \<and>
           learned_clss_lf (get_clauses_l_init SOC) = learned_clss_lf (get_clauses_l_init SOC') \<and>
           get_learned_unit_clauses_l_init SOC' = get_learned_unit_clauses_l_init SOC \<and>
           get_subsumed_learned_clauses_l_init SOC' = get_subsumed_learned_clauses_l_init SOC \<and>
           get_learned_clauses0_l_init SOC' = get_learned_clauses0_l_init SOC \<and>
           twl_list_invs (fst SOC') \<and>
           twl_stgy_invs (fst T') \<and>
           (other_clauses_l_init SOC' \<noteq> {#} \<longrightarrow> get_conflict_l_init SOC' \<noteq> None) \<and>
           ({#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l_init SOC' \<noteq> None) \<and>
           (get_conflict_l_init SOC \<noteq> None \<longrightarrow> get_conflict_l_init SOC = get_conflict_l_init SOC'))\<close>


lemma twl_struct_invs_init_add_to_other_init:
  assumes
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close>
  shows
    \<open>twl_struct_invs_init (add_to_other_init a T)\<close>
      (is ?twl_struct_invs_init)
proof -
  let ?a = \<open>remdups a\<close>
  obtain M N U D NE UE Q OC WS NS US N0 U0 where
    T: \<open>T = ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NE + NS + N0 + OC, clauses U + UE + US + U0, D)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + NS + N0 + OC, clauses U + UE + US + U0, D)\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by (auto simp: ac_simps)
  then have
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset ?a) (clauses N + NE + NS + N0 + OC),
      clauses U + UE + US + U0, D)\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
       clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
       cdcl\<^sub>W_restart_mset.reasons_in_clauses_def)
  then have \<open>pcdcl_all_struct_invs (M, add_mset (mset ?a) (clauses N + OC), clauses U, D, NE, UE, NS, US, N0, U0)\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def
    by (auto simp: ac_simps entailed_clss_inv_def psubsumed_invs_def clauses0_inv_def)

  moreover have
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset ?a) (clauses N + NE + NS + N0 + OC),
        clauses U + UE + US + U0, D)\<close>
    using lev smaller
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  ultimately show ?twl_struct_invs_init
    using invs
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by (clarsimp simp: ac_simps)
qed

lemma clauses_to_update_inv_add_subsumed[simp]:
  \<open>clauses_to_update_inv (M, N, U, D, NE, UE, add_mset a NS, US, N0, U0, WS, Q) =
  clauses_to_update_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  \<open>clauses_to_update_inv (M, N, U, D, NE, UE, NS, add_mset a US, N0, U0, WS, Q) =
  clauses_to_update_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  by (cases D; auto; fail)+

lemma confl_cands_enqueued_add_subsumed[simp]:
  \<open>confl_cands_enqueued (M, N, U, D, NE, UE, add_mset a NS, US, N0, U0, WS, Q) =
  confl_cands_enqueued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<close>
  by (cases D; auto; fail)+

lemma propa_cands_enqueued_add_subsumed[simp]:
  \<open>propa_cands_enqueued (M, N, U, D, NE, UE, add_mset a NS, US, N0, U0, WS, Q) =
  propa_cands_enqueued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<close>
  by (cases D; auto; fail)+

lemma twl_exception_inv_add_subsumed[simp]:
  \<open>twl_exception_inv (M, N, U, D, NE, UE, add_mset a NS, US, N0, U0, WS, Q) =
  twl_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  \<open>twl_exception_inv (M, N, U, D, NE, UE, NS, add_mset a US, N0, U0, WS, Q) =
  twl_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  by (cases D; auto simp: twl_exception_inv.simps; fail)+

lemma past_invs_add_subsumed[simp]:
  \<open>past_invs (M, N, U, D, NE, UE, add_mset a NS, US, N0, U0, WS, Q) =
  past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  \<open>past_invs (M, N, U, D, NE, UE, NS, add_mset a US, N0, U0, WS, Q) =
  past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  by (cases D; auto simp: past_invs.simps; fail)+

lemma twl_st_inv_add_subsumed[simp]:
  \<open>twl_st_inv (M, N, U, D, NE, UE, add_mset a NS, US, N0, U0, WS, Q) =
  twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  \<open>twl_st_inv (M, N, U, D, NE, UE, NS, add_mset a US, N0, U0, WS, Q) =
  twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  by (cases D; auto simp: twl_st_inv.simps; fail)+
 
lemma twl_struct_invs_init_add_to_tautology_init:
  assumes
    tauto: \<open>tautology a\<close> and
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close>
  shows
    \<open>twl_struct_invs_init (add_to_tautology_init a T)\<close>
      (is ?twl_struct_invs_init)
proof -
  let ?a = \<open>remdups_mset a\<close>
  obtain M N U D NE UE Q OC WS NS US N0 U0 where
    T: \<open>T = ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NE + NS + N0 + OC, clauses U + UE + US + U0, D)\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + NS + N0 + OC, clauses U + UE + US + U0, D)\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by (auto simp: ac_simps)
  then have
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset ?a (clauses N + NE + NS + N0 + OC),
      clauses U + UE + US + U0, D)\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
       clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
       cdcl\<^sub>W_restart_mset.reasons_in_clauses_def)
  then have \<open>pcdcl_all_struct_invs (M, (clauses N + OC), clauses U, D, NE, UE, add_mset ?a NS, US, N0, U0)\<close>
    using invs tauto unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def
    by (auto simp: ac_simps entailed_clss_inv_def psubsumed_invs_def clauses0_inv_def)

  moreover have
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset ?a (clauses N + NE + NS + N0 + OC),
        clauses U + UE + US + U0, D)\<close>
    using lev smaller
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  ultimately show ?twl_struct_invs_init
    using invs
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv state\<^sub>W_of_init.simps get_conflict.simps add_to_tautology_init_def
    by (clarsimp simp: ac_simps)
qed

lemma invariants_init_state:
  assumes
    lev: \<open>count_decided (get_trail_init T) = 0\<close> and
    wf: \<open>\<forall>C \<in># get_clauses (fst T). struct_wf_twl_cls C\<close> and
    MQ: \<open>literals_to_update_init T = uminus `# lit_of `# mset (get_trail_init T)\<close> and
    WS: \<open>clauses_to_update_init T = {#}\<close> and
    n_d: \<open>no_dup (get_trail_init T)\<close>
  shows \<open>propa_cands_enqueued (fst T)\<close> and \<open>confl_cands_enqueued (fst T)\<close> and \<open>twl_st_inv (fst T)\<close>
    \<open>clauses_to_update_inv (fst T)\<close> and \<open>past_invs (fst T)\<close> and \<open>distinct_queued (fst T)\<close> and
    \<open>valid_enqueued (fst T)\<close> and \<open>twl_st_exception_inv (fst T)\<close> and \<open>no_duplicate_queued (fst T)\<close>
proof -
  obtain M N U NE UE OC D NS US N0 U0 where
    T: \<open>T = ((M, N, U, D, NE, UE, NS, US, N0, U0, {#}, uminus `# lit_of `# mset M), OC)\<close>
    using MQ WS by (cases T) auto
  let ?Q = \<open>uminus `# lit_of `# mset M\<close>

  have [iff]: \<open>M = M' @ Decided K # Ma \<longleftrightarrow> False\<close> for M' K Ma
    using lev by (auto simp: count_decided_0_iff T)

  have struct: \<open>struct_wf_twl_cls C\<close> if \<open>C \<in># N + U\<close> for C
    using wf that by (simp add: T twl_st_inv.simps)
  let ?T = \<open>fst T\<close>
  have [simp]: \<open>propa_cands_enqueued ?T\<close> if D: \<open>D = None\<close>
    unfolding propa_cands_enqueued.simps Ball_def T fst_conv D
    apply - apply (intro conjI impI allI)
    subgoal for x C
      using struct[of C]
      apply (case_tac C; auto simp: uminus_lit_swap lits_of_def size_2_iff
          true_annots_true_cls_def_iff_negation_in_model Ball_def remove1_mset_add_mset_If
          all_conj_distrib conj_disj_distribR ex_disj_distrib
          split: if_splits)
      done
    done
  then show \<open>propa_cands_enqueued ?T\<close>
    by (cases D) (auto simp: T)

  have [simp]: \<open>confl_cands_enqueued ?T\<close> if D: \<open>D = None\<close>
    unfolding confl_cands_enqueued.simps Ball_def T D fst_conv
    apply - apply (intro conjI impI allI)
    subgoal for x
      using struct[of x]
      by (case_tac x; case_tac \<open>watched x\<close>; auto simp: uminus_lit_swap lits_of_def)
    done
  then show \<open>confl_cands_enqueued ?T\<close>
    by (cases D) (auto simp: T)
  have [simp]: \<open>get_level M L = 0\<close> for L
    using lev by (auto simp: T count_decided_0_iff)
  show [simp]: \<open>twl_st_inv ?T\<close>
    unfolding T fst_conv twl_st_inv.simps Ball_def
    apply - apply (intro conjI impI allI)
    subgoal using wf by (auto simp: T)
    subgoal for C
      by (cases C)
        (auto simp: T twl_st_inv.simps twl_lazy_update.simps twl_is_an_exception_def
          lits_of_def uminus_lit_swap)
    subgoal for C
      using lev by (cases C)
        (auto simp: T twl_st_inv.simps twl_lazy_update.simps)
    done
  have [simp]: \<open>{#C \<in># N. clauses_to_update_prop {#- lit_of x. x \<in># mset M#} M (L, C)#} = {#}\<close>
    for L N
    by (auto simp: filter_mset_empty_conv clauses_to_update_prop.simps lits_of_def
        uminus_lit_swap)
  have \<open>clauses_to_update_inv ?T\<close> if D: \<open>D = None\<close>
    unfolding T D
    by (auto simp: filter_mset_empty_conv lits_of_def uminus_lit_swap)
  then show \<open>clauses_to_update_inv (fst T)\<close>
    by (cases D) (auto simp: T)

  show \<open>past_invs ?T\<close>
    by (auto simp: T past_invs.simps)

  show \<open>distinct_queued ?T\<close>
    using WS n_d by (auto simp: T no_dup_distinct_uminus)
  show \<open>valid_enqueued ?T\<close>
    using lev by (auto simp: T lits_of_def)

  show \<open>twl_st_exception_inv (fst T)\<close>
    unfolding T fst_conv twl_st_exception_inv.simps Ball_def
    apply - apply (intro conjI impI allI)
    apply (case_tac x; cases D)
    by (auto simp: T twl_exception_inv.simps lits_of_def uminus_lit_swap)

  show \<open>no_duplicate_queued (fst T)\<close>
    by (auto simp: T)
qed

lemma twl_struct_invs_init_init_state:
  assumes
    lev: \<open>count_decided (get_trail_init T) = 0\<close> and
    wf: \<open>\<forall>C \<in># get_clauses (fst T). struct_wf_twl_cls C\<close> and
    MQ: \<open>literals_to_update_init T = uminus `# lit_of `# mset (get_trail_init T)\<close> and
    WS: \<open>clauses_to_update_init T = {#}\<close> and
    struct_invs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init T)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of_init T)\<close> and
    \<open>get_conflict_init T \<noteq> None \<longrightarrow> clauses_to_update_init T = {#} \<and> literals_to_update_init T = {#}\<close>
  shows \<open>twl_struct_invs_init T\<close>
proof -
  have n_d: \<open>no_dup (get_trail_init T)\<close>
    using struct_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (cases T) (auto simp: trail.simps)
  then show ?thesis
    using invariants_init_state[OF lev wf MQ WS n_d] assms unfolding twl_struct_invs_init_def
    by fast+
qed


lemma twl_struct_invs_init_add_to_unit_init_clauses:
  assumes
    dist: \<open>distinct a\<close> and
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close> and
    ex: \<open>\<exists>L \<in> set a. L \<in> lits_of_l (get_trail_init T)\<close>
  shows
    \<open>twl_struct_invs_init (add_to_unit_init_clauses (mset a) T)\<close>
      (is ?all_struct)
proof -
  have [simp]: \<open>remdups_mset (mset a) = mset a\<close>
    using dist by (simp add: mset_set_set remdups_mset_def) 
  obtain M N U D NE UE Q NS US N0 U0 OC WS where
    T: \<open>T = ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, D)\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by (auto simp: ac_simps)
  then have [simp]:
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset a) (OC + clauses N + NE + NS + N0),
      clauses U + UE + US + U0, D)\<close>
    using twl_struct_invs_init_add_to_other_init[OF lev invs, of a] dist
    unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def
    by (simp add: ac_simps)
  then have invs': \<open>pcdcl_all_struct_invs
                 (M,  clauses N + OC, clauses U, D, add_mset (mset a) NE, UE, NS, US, N0, U0)\<close>
    using invs count_decided_ge_get_level[of M] lev ex unfolding twl_struct_invs_init_def pcdcl_all_struct_invs_def
    by (auto simp: psubsumed_invs_def entailed_clss_inv_def T ac_simps clauses0_inv_def)
  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset a) (clauses N + OC + NE + NS + N0),
        clauses U + UE + US + U0, D)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  have [simp]: \<open>confl_cands_enqueued (M, N, U, D, add_mset (mset a) NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
     confl_cands_enqueued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    \<open>propa_cands_enqueued (M, N, U, D, add_mset (mset a) NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
      propa_cands_enqueued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    \<open>twl_st_inv (M, N, U, D, add_mset (mset a) NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
        twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    \<open>\<And>x.  twl_exception_inv (M, N, U, D, add_mset (mset a) NE, UE, NS, US, N0, U0, WS, Q) x \<longleftrightarrow>
          twl_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) x\<close>
    \<open>clauses_to_update_inv (M, N, U, D, add_mset (mset a) NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
       clauses_to_update_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    \<open>past_invs (M, N, U, D, add_mset (mset a) NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
        past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    by (cases D; auto simp: twl_st_inv.simps twl_exception_inv.simps past_invs.simps; fail)+
  show ?all_struct
    using invs ex invs'
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by (clarsimp simp del: entailed_clss_inv.simps)
qed


lemma twl_struct_invs_init_set_conflict_init:
  assumes
    dist: \<open>distinct C\<close> and
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close> and
    ex: \<open>\<forall>L \<in> set C. -L \<in> lits_of_l (get_trail_init T)\<close> and
    nempty: \<open>C \<noteq> []\<close> and
    confl: \<open>get_conflict_init T = None\<close>
  shows
    \<open>twl_struct_invs_init (set_conflict_init C T)\<close>
      (is ?all_struct)
proof -
  obtain M N U D NE UE Q OC WS NS US N0 U0 where
    T: \<open>T = ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, D)\<close> and
     pinvs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init ((M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q), OC))\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by auto
  then have
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset C) (clauses N + OC+ NE + NS + N0),
        clauses U + UE + US + U0, Some (mset C))\<close>
    using dist ex
    unfolding T twl_struct_invs_init_def
    by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
       clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
       true_annots_true_cls_def_iff_negation_in_model)
  then have H: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init ((M, N, U, Some (mset C), add_mset (mset C) NE, UE, NS, US, N0, U0, WS, Q), OC))\<close>
    using pinvs ex count_decided_ge_get_level[of M] lev nempty confl
    unfolding pcdcl_all_struct_invs_def entailed_clss_inv_def psubsumed_invs_def
    by (auto simp: entailed_clss_inv_def T clauses0_inv_def)

  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset C) (clauses N + OC + NE + NS + N0),
        clauses U + UE + US + U0, Some (mset C))\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  let ?T = \<open>(M, N, U, Some (mset C), add_mset (mset C) NE, UE, NS, US, N0, U0, {#}, {#})\<close>

  have [simp]: \<open>confl_cands_enqueued ?T\<close>
    \<open>propa_cands_enqueued ?T\<close>
    \<open>twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow> twl_st_inv ?T\<close>
    \<open>\<And>x.  twl_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) x \<Longrightarrow> twl_exception_inv ?T x\<close>
    \<open>clauses_to_update_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow> clauses_to_update_inv ?T\<close>
    \<open>past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow> past_invs ?T\<close>
    by (auto simp: twl_st_inv.simps twl_exception_inv.simps past_invs.simps; fail)+

  show ?all_struct
    using invs ex H
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by (clarsimp simp del: entailed_clss_inv.simps)
qed

lemma twl_struct_invs_init_propagate_unit_init:
  assumes
    lev: \<open>count_decided (get_trail_init T) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close> and
    undef: \<open>undefined_lit (get_trail_init T) L\<close> and
    confl: \<open>get_conflict_init T = None\<close> and
    MQ: \<open>literals_to_update_init T = uminus `# lit_of `# mset (get_trail_init T)\<close> and
    WS: \<open>clauses_to_update_init T = {#}\<close>
  shows
    \<open>twl_struct_invs_init (propagate_unit_init L T)\<close>
      (is ?all_struct)
proof -
  obtain M N U NE UE OC WS NS US N0 U0 where
    T: \<open>T = ((M, N, U, None, NE, UE, NS, US, N0, U0, WS, uminus `# lit_of `# mset M), OC)\<close>
    using confl MQ by (cases T) auto
  let ?Q = \<open>uminus `# lit_of `# mset M\<close>
  have [iff]: \<open>- L \<in> lits_of_l M \<longleftrightarrow> False\<close>
    using undef by (auto simp: T Decided_Propagated_in_iff_in_lits_of_l)
  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition) (use lev in \<open>auto simp: T count_decided_0_iff\<close>)
  have H: \<open>a @ Propagated L' mark' # b = Propagated L mark # M  \<longleftrightarrow>
     (a = [] \<and> L = L' \<and> mark = mark' \<and> b = M) \<or>
     (a \<noteq> [] \<and> hd a = Propagated L mark \<and> tl a @ Propagated L' mark' # b = M)\<close>
    for a mark mark' L' b
    using undef by (cases a) (auto simp: T atm_of_eq_atm_of)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0,  None)\<close> and
    excep: \<open>twl_st_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, ?Q)\<close> and
    st_inv: \<open>twl_st_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, ?Q)\<close> and
    pinvs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init T)\<close>
    using invs confl unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by auto
  then have [simp]:
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset {#L#} (clauses N + OC + NE + NS + N0),
       clauses U + UE + US + U0, None)\<close> and
    n_d: \<open>no_dup M\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def T
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
       clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
       cdcl\<^sub>W_restart_mset.reasons_in_clauses_def)
  then have
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (Propagated L {#L#} # M,
        add_mset {#L#} (clauses N + OC + NE + NS + N0), clauses U + UE + US + U0, None)\<close>
    using undef by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def T H
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
        clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
      consistent_interp_insert_iff)
  then have pinvs': \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init (propagate_unit_init L T))\<close>
    using pinvs lev count_decided_ge_get_level[of \<open>Propagated L {#L#} # M\<close>] unfolding pcdcl_all_struct_invs_def T
    by (auto simp: entailed_clss_inv_def psubsumed_invs_def clauses0_inv_def)
  have [iff]: \<open>Propagated L {#L#} # M = M' @ Decided K # Ma \<longleftrightarrow> False\<close> for M' K Ma
    using lev by (cases M') (auto simp: count_decided_0_iff T)
  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, None)\<close>
    using invs confl unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (Propagated L {#L#} # M, add_mset {#L#} (clauses N + NE + NS + N0 + OC),
        clauses U + UE + US + U0,  None)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)

  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N  + OC + NE + NS + N0, clauses U + UE + US + U0, None)\<close>
    using invs confl unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (Propagated L {#L#} # M, add_mset {#L#} (clauses N + OC + NE + NS + N0),
        clauses U + UE + US + U0, None)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, WS, ?Q)\<close>
  let ?T = \<open>(Propagated L {#L#} # M, N, U, None, add_mset {#L#} NE, UE, NS, US, N0, U0, WS, add_mset (-L) ?Q)\<close>

  have struct: \<open>struct_wf_twl_cls C\<close> if \<open>C \<in># N + U\<close> for C
    using st_inv that by (simp add: twl_st_inv.simps)
  show \<open>twl_struct_invs_init (propagate_unit_init L T)\<close>
    apply (rule twl_struct_invs_init_init_state)
    subgoal using lev by (auto simp: T)
    subgoal using struct by (auto simp: T)
    subgoal using MQ by (auto simp: T)
    subgoal using WS by (auto simp: T)
    subgoal using pinvs' by (simp add: T)
    subgoal by (auto simp: T)
    subgoal by (auto simp: T)
    done
qed

named_theorems twl_st_l_init
lemma [twl_st_l_init]:
  \<open>clauses_to_update_l_init (already_propagated_unit_init_l C S) = clauses_to_update_l_init S\<close>
  \<open>get_trail_l_init (already_propagated_unit_init_l C S) = get_trail_l_init S\<close>
  \<open>get_conflict_l_init (already_propagated_unit_init_l C S) = get_conflict_l_init S\<close>
  \<open>other_clauses_l_init (already_propagated_unit_init_l C S) = other_clauses_l_init S\<close>
  \<open>clauses_to_update_l_init (already_propagated_unit_init_l C S) = clauses_to_update_l_init S\<close>
  \<open>literals_to_update_l_init (already_propagated_unit_init_l C S) = literals_to_update_l_init S\<close>
  \<open>get_clauses_l_init (already_propagated_unit_init_l C S) = get_clauses_l_init S\<close>
  \<open>get_unit_clauses_l_init (already_propagated_unit_init_l C S) = add_mset C (get_unit_clauses_l_init S)\<close>
  \<open>get_learned_unit_clauses_l_init (already_propagated_unit_init_l C S) =
       get_learned_unit_clauses_l_init S\<close>
  \<open>get_subsumed_learned_clauses_l_init (already_propagated_unit_init_l C S) =
       get_subsumed_learned_clauses_l_init S\<close>
  \<open>get_subsumed_init_clauses_l_init (already_propagated_unit_init_l C S) =
       get_subsumed_init_clauses_l_init S\<close>
  \<open>get_learned_clauses0_l_init (already_propagated_unit_init_l C S) =  get_learned_clauses0_l_init S\<close>
  \<open>get_init_clauses0_l_init (already_propagated_unit_init_l C S) =  get_init_clauses0_l_init S\<close>
  \<open>get_conflict_l_init (T, OC) = get_conflict_l T\<close>
  by (solves \<open>cases S; cases T; auto simp: already_propagated_unit_init_l_def\<close>)+


lemma [twl_st_l_init]:
  \<open>clauses_to_update_l_init (add_to_tautology_init_l C S) = clauses_to_update_l_init S\<close>
  \<open>get_trail_l_init (add_to_tautology_init_l C S) = get_trail_l_init S\<close>
  \<open>get_conflict_l_init (add_to_tautology_init_l C S) = get_conflict_l_init S\<close>
  \<open>other_clauses_l_init (add_to_tautology_init_l C S) = other_clauses_l_init S\<close>
  \<open>clauses_to_update_l_init (add_to_tautology_init_l C S) = clauses_to_update_l_init S\<close>
  \<open>literals_to_update_l_init (add_to_tautology_init_l C S) = literals_to_update_l_init S\<close>
  \<open>get_clauses_l_init (add_to_tautology_init_l C S) = get_clauses_l_init S\<close>
  \<open>get_unit_clauses_l_init (add_to_tautology_init_l C S) = (get_unit_clauses_l_init S)\<close>
  \<open>get_learned_unit_clauses_l_init (add_to_tautology_init_l C S) =
       get_learned_unit_clauses_l_init S\<close>
  \<open>get_subsumed_learned_clauses_l_init (add_to_tautology_init_l C S) =
       get_subsumed_learned_clauses_l_init S\<close>
  \<open>get_subsumed_init_clauses_l_init (add_to_tautology_init_l C S) =
     add_mset (remdups_mset (mset C)) (get_subsumed_init_clauses_l_init S)\<close>
  \<open>get_learned_clauses0_l_init (add_to_tautology_init_l C S) =  get_learned_clauses0_l_init S\<close>
  \<open>get_init_clauses0_l_init (add_to_tautology_init_l C S) =  get_init_clauses0_l_init S\<close>
  by (solves \<open>cases S; auto simp: add_to_tautology_init_l_def\<close>)+

lemma [twl_st_l_init]:
  \<open>(V, W) \<in> twl_st_l_init \<Longrightarrow>
    count_decided (get_trail_init W) = count_decided (get_trail_l_init V)\<close>
  by (auto simp: twl_st_l_init_def)

lemma [twl_st_l_init]:
  \<open>(V, W) \<in> twl_st_l_init \<Longrightarrow>get_subsumed_learned_clauses_init W = get_subsumed_learned_clauses_l_init V\<close>
  by (cases V, cases W, auto simp: twl_st_l_init_def)

lemma [twl_st_l_init]:
  \<open>get_conflict_l (fst T) =  get_conflict_l_init T\<close>
  \<open>literals_to_update_l (fst T) = literals_to_update_l_init T\<close>
  \<open>clauses_to_update_l (fst T) = clauses_to_update_l_init T\<close>
  \<open>get_subsumed_learned_clauses_l (fst T) = get_subsumed_learned_clauses_l_init T\<close>
  \<open>get_subsumed_init_clauses_l (fst T) = get_subsumed_init_clauses_l_init T\<close>
  \<open>get_subsumed_clauses_l (fst T) = get_subsumed_clauses_l_init T\<close>
  \<open>get_conflict_l (fst T) = get_conflict_l_init T\<close>
  by (cases T; auto; fail)+

lemma entailed_clss_inv_add_to_unit_init_clauses:
  \<open>count_decided (get_trail_init T) = 0 \<Longrightarrow> C \<noteq> [] \<Longrightarrow> hd C \<in> lits_of_l (get_trail_init T) \<Longrightarrow>
     entailed_clss_inv (pstate\<^sub>W_of_init T) \<Longrightarrow> entailed_clss_inv (pstate\<^sub>W_of_init  (add_to_unit_init_clauses (mset C) T))\<close>
  using count_decided_ge_get_level[of \<open>get_trail_init T\<close>]
  by (cases T; cases C; auto simp: twl_st_inv.simps twl_exception_inv.simps entailed_clss_inv_def)

lemma convert_lits_l_no_decision_iff: \<open>(S, T) \<in> convert_lits_l M N \<Longrightarrow>
        (\<forall>s\<in>set T. \<not> is_decided s) \<longleftrightarrow>
        (\<forall>s\<in>set S. \<not> is_decided s)\<close>
  unfolding convert_lits_l_def
  by (induction rule: list_rel_induct)
    (auto simp: dest!: p2relD)

lemma twl_st_l_init_no_decision_iff:
   \<open>(S, T) \<in> twl_st_l_init \<Longrightarrow>
        (\<forall>s\<in>set (get_trail_init T). \<not> is_decided s) \<longleftrightarrow>
        (\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s)\<close>
  by (subst convert_lits_l_no_decision_iff[of _ _ \<open>get_clauses_l_init S\<close>
        \<open>get_unit_clauses_l_init S\<close>])
    (auto simp: twl_st_l_init_def)

lemma twl_st_l_init_defined_lit[twl_st_l_init]:
   \<open>(S, T) \<in> twl_st_l_init \<Longrightarrow>
        defined_lit (get_trail_init T) = defined_lit (get_trail_l_init S)\<close>
  by (auto simp: twl_st_l_init_def)
    
lemma [twl_st_l_init]:
  \<open>(S, T) \<in> twl_st_l_init \<Longrightarrow> get_learned_clauses_init T = {#} \<longleftrightarrow> learned_clss_l (get_clauses_l_init S) = {#}\<close>
  \<open>(S, T) \<in> twl_st_l_init \<Longrightarrow> get_unit_learned_clauses_init T = {#} \<longleftrightarrow> get_learned_unit_clauses_l_init S = {#}
    \<close>
  by (cases S; cases T; auto simp: twl_st_l_init_def; fail)+


lemma init_dt_pre_already_propagated_unit_init_l:
  assumes
    hd_C: \<open>hd C \<in> lits_of_l (get_trail_l_init S)\<close> and
    pre: \<open>init_dt_pre CS S\<close> and
    nempty: \<open>C \<noteq> []\<close> and
    dist_C: \<open>distinct C\<close> and
    lev: \<open>count_decided (get_trail_l_init S) = 0\<close> and
    C': \<open>mset (remdups C') = mset C\<close>
  shows
    \<open>init_dt_pre CS (already_propagated_unit_init_l (mset C) S)\<close> (is ?pre) and
    \<open>init_dt_spec [C'] S (already_propagated_unit_init_l (mset C) S)\<close>  (is ?spec)
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init S = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init S = None \<longrightarrow>
     literals_to_update_l_init S = uminus `# lit_of `# mset (get_trail_l_init S)\<close> and
    add_inv: \<open>twl_list_invs (fst S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init S \<noteq> {#} \<longrightarrow> get_conflict_l_init S \<noteq> None\<close>
    using pre unfolding init_dt_pre_def
    apply -
    apply normalize_goal+
    by presburger
  obtain M N D NE UE Q U OC NS US N0 U0 where
    S: \<open>S = ((M, N, U, D, NE, UE, NS, US, N0, U0, Q), OC)\<close>
    by (cases S) auto
  have [simp]: \<open>twl_list_invs (fst (already_propagated_unit_init_l (mset C) S))\<close>
    using add_inv by (auto simp:  already_propagated_unit_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(already_propagated_unit_init_l (mset C) S, add_to_unit_init_clauses (mset C) T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S)
      (auto simp: twl_st_l_init_def already_propagated_unit_init_l_def
        convert_lits_l_extend_mono)
  have dec': \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close>
    using SOC_T dec by (subst twl_st_l_init_no_decision_iff)
  have [simp]: \<open>twl_stgy_invs (fst (add_to_unit_init_clauses (mset C) T))\<close>
    using stgy_inv dec' unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T)
       (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (add_to_unit_init_clauses (mset C) T)\<close>
    apply (rule twl_struct_invs_init_add_to_unit_init_clauses)
    using inv hd_C nempty dist_C lev SOC_T dec'
    by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff intro: bexI[of _ \<open>hd C\<close>])
  show ?pre
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>add_to_unit_init_clauses (mset C) T\<close>])
    using WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
  show ?spec
    unfolding init_dt_spec_def
    apply (rule exI[of _ \<open>add_to_unit_init_clauses (mset C) T\<close>])
    using WS dec in_literals_to_update OC'_empty nempty dist_C C'
    by (auto simp: twl_st_init twl_st_l_init; fail)+
qed


lemma init_dt_pre_add_to_tautology_init_l:
  assumes
    pre: \<open>init_dt_pre CS S\<close> and
    tautology: \<open>tautology (mset C)\<close> and
    lev: \<open>count_decided (get_trail_l_init S) = 0\<close>
  shows
    \<open>init_dt_pre CS (add_to_tautology_init_l C S)\<close> (is ?pre) and
    \<open>init_dt_spec [C] S (add_to_tautology_init_l C S)\<close>  (is ?spec)
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init S = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init S = None \<longrightarrow>
     literals_to_update_l_init S = uminus `# lit_of `# mset (get_trail_l_init S)\<close> and
    add_inv: \<open>twl_list_invs (fst S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init S \<noteq> {#} \<longrightarrow> get_conflict_l_init S \<noteq> None\<close>
    using pre unfolding init_dt_pre_def
    apply -
    apply normalize_goal+
    by presburger
  obtain M N D NE UE Q U OC NS US N0 U0 where
    S: \<open>S = ((M, N, U, D, NE, UE, NS, US, N0, U0, Q), OC)\<close>
    by (cases S) auto
  let ?S = \<open>add_to_tautology_init_l C S\<close>
  have [simp]: \<open>twl_list_invs (fst ?S)\<close>
    using add_inv by (auto simp: add_to_tautology_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(add_to_tautology_init_l C S, add_to_tautology_init (mset C) T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S)
      (auto simp: twl_st_l_init_def add_to_tautology_init_l_def add_to_tautology_init_def
        convert_lits_l_extend_mono)
  have dec': \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close>
    using SOC_T dec by (subst twl_st_l_init_no_decision_iff)
  have [simp]: \<open>twl_stgy_invs (fst (add_to_tautology_init (mset C) T))\<close>
    using stgy_inv dec' unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T)
      (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def add_to_tautology_init_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (add_to_tautology_init (mset C) T)\<close>
    apply (rule twl_struct_invs_init_add_to_tautology_init)
    using inv tautology lev SOC_T dec'
    by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff intro: bexI[of _ \<open>hd C\<close>])
  show ?pre
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>add_to_tautology_init (mset C) T\<close>])
    using WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
  show ?spec
    unfolding init_dt_spec_def
    apply (rule exI[of _ \<open>add_to_tautology_init (mset C) T\<close>])
    using WS dec in_literals_to_update OC'_empty tautology
    by (auto simp: twl_st_init twl_st_l_init; fail)+
qed

lemma (in -) twl_stgy_invs_backtrack_lvl_0:
  \<open>count_decided (get_trail T) = 0 \<Longrightarrow> twl_stgy_invs T\<close>
  using count_decided_ge_get_level[of \<open>get_trail T\<close>]
  by (cases T)
    (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset_state
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)

lemma init_dt_pre_propagate_unit_init:
  assumes
    hd_C: \<open>undefined_lit (get_trail_l_init S) L\<close> and
    pre: \<open>init_dt_pre CS S\<close> and
    lev: \<open>count_decided (get_trail_l_init S) = 0\<close> and
    confl: \<open>get_conflict_l_init S = None\<close> and
    C': \<open>remdups C' = [L]\<close>
  shows
    \<open>propagate_unit_init_l L S \<le> SPEC(init_dt_pre CS)\<close> (is ?pre) and
    \<open>propagate_unit_init_l L S \<le> SPEC(init_dt_spec [C'] S)\<close> (is ?spec)
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init S = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init S = None \<longrightarrow>
     literals_to_update_l_init S = uminus `# lit_of `# mset (get_trail_l_init S)\<close> and
    add_inv: \<open>twl_list_invs (fst S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init S \<noteq> {#} \<longrightarrow> get_conflict_l_init S \<noteq> None\<close>
    using pre unfolding init_dt_pre_def
    apply -
    apply normalize_goal+
    by presburger
  obtain M N D NE UE Q U OC NS US N0 U0 where
    S: \<open>S = ((M, N, U, D, NE, UE, NS, US, N0, U0, Q), OC)\<close>
    by (cases S) auto
  have 1: \<open>propagate_unit_init_l L S \<le> SPEC( \<lambda>S'. (S', propagate_unit_init L T)
        \<in> twl_st_l_init)\<close>
    using SOC_T assms by (auto simp: twl_st_l_init_def propagate_unit_init_l_def
        convert_lit.simps cons_trail_propagate_l_def S convert_lits_l_extend_mono
        intro!: ASSERT_refine_right ASSERT_leI)
  have dec': \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close>
    using SOC_T dec by (subst twl_st_l_init_no_decision_iff)
  have [simp]: \<open>twl_stgy_invs (fst (propagate_unit_init L T))\<close>
    apply (rule twl_stgy_invs_backtrack_lvl_0)
    using lev SOC_T
    by (cases S) (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def twl_st_l_init_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have 2: \<open>twl_struct_invs_init (propagate_unit_init L T)\<close>
    apply (rule twl_struct_invs_init_propagate_unit_init)
    subgoal
      using inv hd_C lev SOC_T dec' confl in_literals_to_update WS
      by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff)
    subgoal
      using inv hd_C lev SOC_T dec' confl in_literals_to_update WS
      by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff)
    subgoal
      using inv hd_C lev SOC_T dec' confl in_literals_to_update WS
      by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff)
    subgoal
      using inv hd_C lev SOC_T dec' confl in_literals_to_update WS
      by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff)
    subgoal
      using inv hd_C lev SOC_T dec' confl in_literals_to_update WS
      by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff uminus_lit_of_image_mset)
    subgoal
      using inv hd_C lev SOC_T dec' confl in_literals_to_update WS
      by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff uminus_lit_of_image_mset)
    done
  have 3: \<open>propagate_unit_init_l L S \<le> SPEC(\<lambda>S. twl_list_invs (fst (S)))\<close>
    using add_inv assms
    by (auto simp: S twl_list_invs_def propagate_unit_init_l_def cons_trail_propagate_l_def
       intro!: ASSERT_leI)
  show ?pre
    using assms 3 2 1
    unfolding init_dt_pre_def cons_trail_propagate_l_def
    propagate_unit_init_l_def S
    apply (simp only: S get_trail_l_init.simps not_False_eq_True assert.ASSERT_simps
      nres_monad3 nres_monad1 nres_order_simps mem_Collect_eq)
    apply (rule exI[of _ \<open>propagate_unit_init L T\<close>])
    using WS dec in_literals_to_update OC'_empty confl
    by (auto simp: twl_st_init twl_st_l_init)
  show ?spec
    using assms 1 2 3
    unfolding init_dt_spec_def cons_trail_propagate_l_def propagate_unit_init_l_def S
    apply (simp only: S get_trail_l_init.simps not_False_eq_True assert.ASSERT_simps
      nres_monad3 nres_monad1 nres_order_simps mem_Collect_eq)
    apply (rule exI[of _ \<open>propagate_unit_init L T\<close>])
    using WS dec in_literals_to_update OC'_empty confl C'
    by (auto simp: twl_st_init twl_st_l_init S
      simp flip: mset_remdups_remdups_mset)
qed

lemma [twl_st_l_init]:
  \<open>get_trail_l_init (set_conflict_init_l C S) = get_trail_l_init S\<close>
  \<open>literals_to_update_l_init (set_conflict_init_l C S) = {#}\<close>
  \<open>clauses_to_update_l_init (set_conflict_init_l C S) = {#}\<close>
  \<open>get_conflict_l_init (set_conflict_init_l C S) = Some (mset C)\<close>
  \<open>get_unit_clauses_l_init (set_conflict_init_l C S) = add_mset (mset C) (get_unit_clauses_l_init S)\<close>
  \<open>get_subsumed_init_clauses_l_init (set_conflict_init_l C S) = get_subsumed_init_clauses_l_init S\<close>
  \<open>get_subsumed_learned_clauses_l_init (set_conflict_init_l C S) = get_subsumed_learned_clauses_l_init S\<close>
  \<open>get_learned_unit_clauses_l_init (set_conflict_init_l C S) = get_learned_unit_clauses_l_init S\<close>
  \<open>get_learned_clauses0_l_init (set_conflict_init_l C S) = get_learned_clauses0_l_init S\<close>
  \<open>get_init_clauses0_l_init (set_conflict_init_l C S) = get_init_clauses0_l_init S\<close>
  \<open>get_clauses_l_init (set_conflict_init_l C S) = get_clauses_l_init S\<close>
  \<open>other_clauses_l_init (set_conflict_init_l C S) = other_clauses_l_init S\<close>
  by (cases S; auto simp: set_conflict_init_l_def; fail)+

lemma init_dt_pre_set_conflict_init_l:
  assumes
    [simp]: \<open>get_conflict_l_init S = None\<close> and
    pre: \<open>init_dt_pre (C' # CS) S\<close> and
    false: \<open>\<forall>L \<in> set C.  -L \<in> lits_of_l (get_trail_l_init S)\<close> and
    nempty: \<open>C \<noteq> []\<close> and
    C': \<open>mset (remdups C') = mset C\<close>
  shows
    \<open>init_dt_pre CS (set_conflict_init_l C S)\<close> (is ?pre) and
    \<open>init_dt_spec [C'] S (set_conflict_init_l C S)\<close> (is ?spec)
proof -
  have dist_C: \<open>distinct C\<close>
    using C' using same_mset_distinct_iff by blast
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init S = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init S = None \<longrightarrow>
     literals_to_update_l_init S = uminus `# lit_of `# mset (get_trail_l_init S)\<close> and
    add_inv: \<open>twl_list_invs (fst S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init S \<noteq> {#} \<longrightarrow> get_conflict_l_init S \<noteq> None\<close>
    using pre C' unfolding init_dt_pre_def
    apply -
    apply normalize_goal+
    by force
  obtain M N D NE UE Q U OC NS US N0 U0 where
    S: \<open>S = ((M, N, U, D, NE, UE, NS, US, N0, U0, Q), OC)\<close>
    by (cases S) auto
  have [simp]: \<open>twl_list_invs (fst (set_conflict_init_l C S))\<close>
    using add_inv by (auto simp:  set_conflict_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(set_conflict_init_l C S, set_conflict_init C T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S) (auto simp: twl_st_l_init_def set_conflict_init_l_def convert_lit.simps
         convert_lits_l_extend_mono)
  have dec': \<open>count_decided (get_trail_init T) = 0\<close>
    apply (subst count_decided_0_iff)
    apply (subst twl_st_l_init_no_decision_iff)
    using SOC_T dec SOC_T by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def)
  have [simp]: \<open>twl_stgy_invs (fst (set_conflict_init C T))\<close>
    using stgy_inv dec' nempty count_decided_ge_get_level[of \<open>get_trail_init T\<close>]
    unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T; cases C)
       (auto 5 5 simp: cdcl\<^sub>W_restart_mset_state clauses_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (set_conflict_init C T)\<close>
    apply (rule twl_struct_invs_init_set_conflict_init)
    subgoal
      using inv nempty dist_C SOC_T dec false nempty
      by (auto simp: twl_st_init count_decided_0_iff)
    subgoal
      using inv nempty dist_C SOC_T dec' false nempty
      by (auto simp: twl_st_init count_decided_0_iff)
    subgoal
      using inv nempty dist_C SOC_T dec false nempty
      by (auto simp: twl_st_init count_decided_0_iff)
    subgoal
      using inv nempty dist_C SOC_T dec false nempty
      by (auto simp: twl_st_init count_decided_0_iff)
    subgoal
      using inv nempty dist_C SOC_T dec false nempty
      by (auto simp: twl_st_init count_decided_0_iff)
    subgoal
      using inv nempty dist_C SOC_T dec false nempty
      by (auto simp: twl_st_init count_decided_0_iff)
    done
  show ?pre
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>set_conflict_init C T\<close>])
    using WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
  show ?spec
    unfolding init_dt_spec_def
    apply (rule exI[of _ \<open>set_conflict_init C T\<close>])
    using WS dec in_literals_to_update OC'_empty C' by (auto simp: twl_st_init twl_st_l_init)
qed

lemma [twl_st_init]:
  \<open>get_trail_init (add_empty_conflict_init T) = get_trail_init T\<close>
  \<open>get_conflict_init (add_empty_conflict_init T) = Some {#}\<close>
  \<open>clauses_to_update_init (add_empty_conflict_init T) =  clauses_to_update_init T\<close>
  \<open>literals_to_update_init (add_empty_conflict_init T) = {#}\<close>
  by (cases T; auto simp:; fail)+

lemma [twl_st_l_init]:
  \<open>get_trail_l_init (add_empty_conflict_init_l T) = get_trail_l_init T\<close>
  \<open>get_conflict_l_init (add_empty_conflict_init_l T) = Some {#}\<close>
  \<open>clauses_to_update_l_init (add_empty_conflict_init_l T) =  clauses_to_update_l_init T\<close>
  \<open>literals_to_update_l_init (add_empty_conflict_init_l T) = {#}\<close>
  \<open>get_unit_clauses_l_init (add_empty_conflict_init_l T) = get_unit_clauses_l_init T\<close>
  \<open>get_subsumed_init_clauses_l_init (add_empty_conflict_init_l T) = get_subsumed_init_clauses_l_init T\<close>
  \<open>get_subsumed_learned_clauses_l_init (add_empty_conflict_init_l T) = get_subsumed_learned_clauses_l_init T\<close>
  \<open>get_learned_unit_clauses_l_init (add_empty_conflict_init_l T) = get_learned_unit_clauses_l_init T\<close>
  \<open>get_clauses_l_init (add_empty_conflict_init_l T) = get_clauses_l_init T\<close>
  \<open>get_init_clauses0_l_init (add_empty_conflict_init_l T) = add_mset {#} (get_init_clauses0_l_init T)\<close>
  \<open>get_learned_clauses0_l_init (add_empty_conflict_init_l T) = get_learned_clauses0_l_init T\<close>
  \<open>other_clauses_l_init (add_empty_conflict_init_l T) = (other_clauses_l_init T)\<close>
  by (cases T; auto simp: add_empty_conflict_init_l_def; fail)+

lemma twl_struct_invs_init_add_empty_conflict_init_l:
  assumes
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_init T = {#}\<close>
  shows \<open>twl_struct_invs_init (add_empty_conflict_init T)\<close>
      (is ?all_struct)
proof -
  obtain M N U D NE UE Q OC NS US N0 U0 where
    T: \<open>T = ((M, N, U, D, NE, UE, NS, US, N0, U0, {#}, Q), OC)\<close>
    using WS by (cases T) auto
  let ?T = \<open>(M, N, U, Some {#}, NE, UE, NS, US, add_mset {#} N0, U0, {#}, {#})\<close>
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, D)\<close> and
    pinvs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init ((M, N, U, D, NE, UE, NS, US, N0, U0, {#}, Q), OC))\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by auto
  then have
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset {#} (clauses N + OC + NE + NS + N0),
        clauses U + UE + US + U0, Some {#})\<close>
    unfolding T twl_struct_invs_init_def
    by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
       clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
       true_annots_true_cls_def_iff_negation_in_model)
  then have pinvs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init (?T, OC))\<close>
    using pinvs count_decided_ge_get_level[of M] lev
    unfolding pcdcl_all_struct_invs_def
    by (auto simp: T psubsumed_invs_def entailed_clss_inv_def clauses0_inv_def)
  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset {#} (clauses N + OC + NE + NS + N0),
        clauses U + UE + US + U0, Some {#})\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)

  have [simp]: \<open>confl_cands_enqueued ?T\<close>
    \<open>propa_cands_enqueued ?T\<close>
    \<open>twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, Q) \<Longrightarrow> twl_st_inv ?T\<close>
    \<open>\<And>x.  twl_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, Q) x \<Longrightarrow> twl_exception_inv ?T x\<close>
    \<open>clauses_to_update_inv (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, Q) \<Longrightarrow> clauses_to_update_inv ?T\<close>
    \<open>past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, Q) \<Longrightarrow> past_invs ?T\<close>
    by (auto simp: twl_st_inv.simps twl_exception_inv.simps past_invs.simps; fail)+

  show ?all_struct
    using invs pinvs
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by (clarsimp simp del: entailed_clss_inv.simps)
qed

lemma init_dt_pre_add_empty_conflict_init_l:
  assumes
    confl[simp]: \<open>get_conflict_l_init S = None\<close> and
    pre: \<open>init_dt_pre ([] # CS) S\<close>
  shows
    \<open>init_dt_pre CS (add_empty_conflict_init_l S)\<close> (is ?pre)
    \<open>init_dt_spec [[]] S (add_empty_conflict_init_l S)\<close> (is ?spec)
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init S = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init S = None \<longrightarrow>
     literals_to_update_l_init S = uminus `# lit_of `# mset (get_trail_l_init S)\<close> and
    add_inv: \<open>twl_list_invs (fst S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init S \<noteq> {#} \<longrightarrow> get_conflict_l_init S \<noteq> None\<close>
    using pre unfolding init_dt_pre_def
    apply -
    apply normalize_goal+
    by force
  obtain M N D NE UE Q U OC NS US N0 U0 where
    S: \<open>S = ((M, N, U, D, NE, UE, NS, US, N0, U0, Q), OC)\<close>
    by (cases S) auto
  have [simp]: \<open>twl_list_invs (fst (add_empty_conflict_init_l S))\<close>
    using add_inv by (auto simp: add_empty_conflict_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(add_empty_conflict_init_l S, add_empty_conflict_init T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S) (auto simp: twl_st_l_init_def add_empty_conflict_init_l_def)
  have dec': \<open>count_decided (get_trail_init T) = 0\<close>
    apply (subst count_decided_0_iff)
    apply (subst twl_st_l_init_no_decision_iff)
    using SOC_T dec SOC_T by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def)
  have [simp]: \<open>twl_stgy_invs (fst (add_empty_conflict_init T))\<close>
    using stgy_inv dec' count_decided_ge_get_level[of \<open>get_trail_init T\<close>]
    unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T)
       (auto 5 5 simp: cdcl\<^sub>W_restart_mset_state clauses_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (add_empty_conflict_init T)\<close>
    apply (rule twl_struct_invs_init_add_empty_conflict_init_l)
    using inv SOC_T dec' WS
    by (auto simp: twl_st_init twl_st_l_init count_decided_0_iff )
  show ?pre
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>add_empty_conflict_init T\<close>])
    using WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
  show ?spec
    unfolding init_dt_spec_def
    apply (rule exI[of _ \<open>add_empty_conflict_init T\<close>])
    using WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
qed

lemma [twl_st_l_init]:
  \<open>get_trail (fst (add_to_clauses_init a T)) = get_trail_init T\<close>
  by (cases T; auto; fail)

lemma [twl_st_l_init]:
  \<open>other_clauses_l_init (T, OC) = OC\<close>
  \<open>clauses_to_update_l_init (T, OC) = clauses_to_update_l T\<close>
  by (cases T; auto; fail)+

(*TODO Move*)
lemma remdups_mset_idem: \<open>remdups_mset (remdups_mset a) = remdups_mset a\<close>
  using distinct_mset_remdups_mset distinct_mset_remdups_mset_id by blast

lemma twl_struct_invs_init_add_to_clauses_init:
  assumes
    lev: \<open>count_decided (get_trail_init T) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close> and
    confl: \<open>get_conflict_init T = None\<close> and
    MQ: \<open>literals_to_update_init T = uminus `# lit_of `# mset (get_trail_init T)\<close> and
    WS: \<open>clauses_to_update_init T = {#}\<close> and
   dist_C: \<open>distinct C\<close> and
   le_2: \<open>length C \<ge> 2\<close>
  shows
    \<open>twl_struct_invs_init (add_to_clauses_init C T)\<close>
      (is ?all_struct)
proof -
  obtain M N U NE UE OC WS NS US N0 U0 where
    T: \<open>T = ((M, N, U, None, NE, UE, NS, US, N0, U0, WS, uminus `# lit_of `# mset M), OC)\<close>
    using confl MQ by (cases T) auto
  let ?Q = \<open>uminus `# lit_of `# mset M\<close>

  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, WS, ?Q)\<close>
  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition) (use lev in \<open>auto simp: T count_decided_0_iff\<close>)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, (clauses N + OC + NE + NS + N0), clauses U + UE + US + U0,  None)\<close> and
    excep: \<open>twl_st_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, ?Q)\<close> and
    st_inv: \<open>twl_st_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, ?Q)\<close> and
    pinvs: \<open>pcdcl_all_struct_invs
       (pstate\<^sub>W_of_init ((M, N, U, None, NE, UE, NS, US, N0, U0, WS, uminus `# lit_of `# mset M), OC))\<close>
    using invs confl unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def by auto
  then have
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset C) (clauses N + OC + NE + NS + N0),
     clauses U + UE + US + U0, None)\<close> and
   n_d: \<open>no_dup M\<close>
    using dist_C
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
      clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def)
  then have pinvs': \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of_init (add_to_clauses_init C T))\<close>
    using invs unfolding T twl_struct_invs_init_def pcdcl_all_struct_invs_def
    by (auto simp: entailed_clss_inv_def psubsumed_invs_def mset_take_mset_drop_mset' clauses0_inv_def)
  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + OC + NE + NS + N0, clauses U + UE + US + U0, None)\<close>
    using invs confl unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset C) (clauses N + OC + NE + NS + N0),
        clauses U + UE + US + U0,  None)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)

  have struct: \<open>struct_wf_twl_cls C\<close> if \<open>C \<in># N + U\<close> for C
    using st_inv that by (simp add: twl_st_inv.simps)

  show \<open>twl_struct_invs_init (add_to_clauses_init C T)\<close>
    apply (rule twl_struct_invs_init_init_state)
    subgoal using lev by (auto simp: T)
    subgoal using struct dist_C le_2 by (auto simp: T mset_take_mset_drop_mset')
    subgoal using MQ by (auto simp: T)
    subgoal using WS by (auto simp: T)
    subgoal using pinvs' by (simp add: T mset_take_mset_drop_mset')
    subgoal by (auto simp: T mset_take_mset_drop_mset')
    subgoal by (auto simp: T)
    done
qed

lemma get_trail_init_add_to_clauses_init[simp]:
  \<open>get_trail_init (add_to_clauses_init a T) = get_trail_init T\<close>
  by (cases T) auto

lemma init_dt_pre_add_to_clauses_init_l:
  assumes
    D: \<open>get_conflict_l_init S = None\<close> and
    a: \<open>length a \<noteq> Suc 0\<close> \<open>a \<noteq> []\<close> and
    pre: \<open>init_dt_pre (a' # CS) S\<close> and
    \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    C': \<open>mset (remdups a') = mset a\<close>
  shows
    \<open>add_to_clauses_init_l a S \<le> SPEC (init_dt_pre CS)\<close> (is ?pre) and
    \<open>add_to_clauses_init_l a S \<le> SPEC (init_dt_spec [a'] S)\<close> (is ?spec)
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init S = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init S = None \<longrightarrow>
     literals_to_update_l_init S = uminus `# lit_of `# mset (get_trail_l_init S)\<close> and
    add_inv: \<open>twl_list_invs (fst S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init S \<noteq> {#} \<longrightarrow> get_conflict_l_init S \<noteq> None\<close>
    using pre unfolding init_dt_pre_def
    apply -
    apply normalize_goal+
    by force
  have dec': \<open>\<forall>L \<in> set (get_trail_init T). \<not>is_decided L\<close>
    using SOC_T dec apply -
    apply (rule twl_st_l_init_no_decision_iff[THEN iffD2])
    using SOC_T dec SOC_T by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def)
  obtain M N NE UE Q OC NS US N0 U0 where
    S: \<open>S = ((M, N, None, NE, UE, NS, US, N0, U0, {#}, Q), OC)\<close>
    using D WS by (cases S) auto
  have le_2: \<open>length a \<ge> 2\<close>
    using a by (cases a) auto
  have
    \<open>init_dt_pre CS ((M, fmupd i (a, True) N, None, NE, UE, NS, US, N0, U0, {#}, Q), OC)\<close> (is ?pre1) and
    \<open>init_dt_spec [a'] S
          ((M, fmupd i (a, True) N, None, NE, UE, NS, US, N0, U0, {#}, Q), OC)\<close> (is ?spec1)
    if
      i_0: \<open>0 < i\<close> and
      i_dom: \<open>i \<notin># dom_m N\<close>
    for i :: \<open>nat\<close>
  proof -
    let ?S = \<open>((M, fmupd i (a, True) N, None, NE, UE, NS, US, N0, U0, {#}, Q), OC)\<close>
    have \<open>Propagated L i \<notin> set M\<close> for L
      using add_inv i_dom i_0 unfolding S
      by (auto simp: twl_list_invs_def)
    then have \<open>(?S, add_to_clauses_init a T) \<in> twl_st_l_init\<close>
      using SOC_T i_dom
      by (auto simp: S twl_st_l_init_def init_clss_l_mapsto_upd_notin
          learned_clss_l_mapsto_upd_notin_irrelev convert_lit.simps
          intro!: convert_lits_l_extend_mono[of _ _ N \<open>NE+UE\<close> \<open>fmupd i (a, True) N\<close>])
    moreover have \<open>twl_struct_invs_init (add_to_clauses_init a T)\<close>
      apply (rule twl_struct_invs_init_add_to_clauses_init)
      subgoal
        apply (subst count_decided_0_iff)
        apply (subst twl_st_l_init_no_decision_iff)
        using SOC_T dec SOC_T by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def)
      subgoal by (use dec SOC_T in_literals_to_update in
          \<open>auto simp: S count_decided_0_iff twl_st_l_init twl_st_init le_2 inv\<close>)
      subgoal by (use dec SOC_T in_literals_to_update in
          \<open>auto simp: S count_decided_0_iff twl_st_l_init twl_st_init le_2 inv\<close>)
      subgoal by (use dec SOC_T in_literals_to_update in
          \<open>auto simp: S count_decided_0_iff twl_st_l_init twl_st_init le_2 inv\<close>)
      subgoal by (use dec SOC_T in_literals_to_update in
          \<open>auto simp: S count_decided_0_iff twl_st_l_init twl_st_init le_2 inv\<close>)
      subgoal using C' same_mset_distinct_iff by blast
      subgoal by (use dec SOC_T in_literals_to_update in
          \<open>auto simp: S count_decided_0_iff twl_st_l_init twl_st_init le_2 inv\<close>)
      done
    moreover have \<open>twl_list_invs (M, fmupd i (a, True) N, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
      using add_inv i_dom i_0 by (auto simp: S twl_list_invs_def)
    moreover have \<open>twl_stgy_invs (fst (add_to_clauses_init a T))\<close>
      by (rule twl_stgy_invs_backtrack_lvl_0)
        (use dec' SOC_T in \<open>auto simp: S count_decided_0_iff twl_st_l_init twl_st_init
           twl_st_l_init_def\<close>)
    ultimately show ?pre1 ?spec1
      unfolding init_dt_pre_def init_dt_spec_def apply -
      subgoal
        apply (rule exI[of _ \<open>add_to_clauses_init a T\<close>])
        using dec OC'_empty in_literals_to_update by (auto simp: S)
      subgoal
        apply (rule exI[of _ \<open>add_to_clauses_init a T\<close>])
        using dec OC'_empty in_literals_to_update i_dom i_0 a C'
        by (auto simp: S learned_clss_l_mapsto_upd_notin_irrelev ran_m_mapsto_upd_notin
          remdups_mset_idem)
      done
  qed
  then show ?pre ?spec
    by (auto simp: S add_to_clauses_init_l_def get_fresh_index_def RES_RETURN_RES)
qed
(*TODO Move*)
lemma tautology_length_ge2: \<open>tautology C \<Longrightarrow> size C \<ge> 2\<close>
  by (auto simp: tautology_decomp add_mset_eq_add_mset dest!: multi_member_split)
lemma init_dt_pre_init_dt_step:
  assumes pre: \<open>init_dt_pre (a # CS) SOC\<close>
  shows \<open>init_dt_step a SOC \<le> SPEC (\<lambda>SOC'. init_dt_pre CS SOC' \<and> init_dt_spec [a] SOC SOC')\<close>
proof -
  obtain S OC where SOC: \<open>SOC = (S, OC)\<close>
    by (cases SOC) auto
  obtain T where
    SOC_T: \<open>((S, OC), T) \<in> twl_st_l_init\<close> and
    inv: \<open>twl_struct_invs_init T\<close> and
    WS: \<open>clauses_to_update_l_init (S, OC) = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init (S, OC)). \<not> is_decided s\<close> and
    in_literals_to_update: \<open>get_conflict_l_init (S, OC) = None \<longrightarrow>
     literals_to_update_l_init (S, OC) = uminus `# lit_of `# mset (get_trail_l_init (S, OC))\<close> and
    add_inv: \<open>twl_list_invs (fst (S, OC))\<close> and
    stgy_inv: \<open>twl_stgy_invs (fst T)\<close> and
    OC'_empty: \<open>other_clauses_l_init (S, OC) \<noteq> {#} \<longrightarrow> get_conflict_l_init (S, OC) \<noteq> None\<close>
    using pre unfolding SOC init_dt_pre_def
    apply -
    apply normalize_goal+
    by presburger
  have dec': \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close>
    using SOC_T dec by (rule twl_st_l_init_no_decision_iff[THEN iffD2])

  obtain M N D NE UE NS US N0 U0 Q where
    S: \<open>SOC = ((M, N, D, NE, UE, NS, US, N0, U0, {#}, Q), OC)\<close>
    using WS by (cases SOC) (auto simp: SOC)
  then have S': \<open>S = (M, N, D, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
    using S unfolding SOC by auto
  show ?thesis
  proof (cases \<open>get_conflict_l (fst SOC)\<close>)
    case None
    then show ?thesis
      using pre dec
      unfolding init_dt_step_def remdups_clause_def
      by refine_vcg
        (auto simp add: Let_def count_decided_0_iff SOC twl_st_l_init twl_st_init
          remdups_clause_def
          true_annot_iff_decided_or_true_lit length_list_Suc_0
          init_dt_step_def get_fresh_index_def RES_RETURN_RES
          intro: init_dt_pre_already_propagated_unit_init_l init_dt_pre_set_conflict_init_l
            init_dt_pre_propagate_unit_init init_dt_pre_add_empty_conflict_init_l
            init_dt_pre_add_to_clauses_init_l init_dt_pre_add_to_tautology_init_l
          intro!: SPEC_rule_conjI
          dest: init_dt_pre_ConsD in_lits_of_l_defined_litD tautology_length_ge2
          simp flip: mset_remdups_remdups_mset)
  next
    case  (Some D')
    then have [simp]: \<open>D = Some D'\<close>
      by (auto simp: S)
    have [simp]:
       \<open>(((M, N, Some D', NE, UE, NS, US, N0, U0, {#}, Q), add_mset (remdups_mset (mset a)) OC),
           add_to_other_init a T)
         \<in> twl_st_l_init\<close> for a
      using SOC_T by (cases T; auto simp: S S' twl_st_l_init_def; fail)+
    have \<open>init_dt_pre CS ((M, N, Some D', NE, UE, NS, US, N0, U0, {#}, Q), add_mset (remdups_mset (mset a)) OC)\<close>
      unfolding init_dt_pre_def
      apply (rule exI[of _ \<open>add_to_other_init (a) T\<close>])
      using inv WS dec' dec in_literals_to_update add_inv stgy_inv SOC_T
      by (auto simp: S' count_decided_0_iff twl_st_init
          intro!: twl_struct_invs_init_add_to_other_init)
    moreover have \<open>init_dt_spec [a] ((M, N, Some D', NE, UE, NS, US, N0, U0, {#}, Q), OC)
      ((M, N, Some D', NE, UE, NS, US, N0, U0, {#}, Q), add_mset (remdups_mset (mset a)) OC)\<close>
      unfolding init_dt_spec_def
      apply (rule exI[of _ \<open>add_to_other_init (a) T\<close>])
      using inv WS dec dec' in_literals_to_update add_inv stgy_inv SOC_T
      by (auto simp: S' count_decided_0_iff twl_st_init
          intro!: twl_struct_invs_init_add_to_other_init)
    ultimately show ?thesis
      by (auto simp: S init_dt_step_def)
  qed
qed

lemma [twl_st_l_init]:
  \<open>get_trail_l_init (S, OC) = get_trail_l S\<close>
  \<open>literals_to_update_l_init (S, OC) = literals_to_update_l S\<close>
  by (cases S; auto; fail)+

lemma init_dt_spec_append:
  assumes
    spec1: \<open>init_dt_spec CS S T\<close>  and
    spec: \<open>init_dt_spec CS' T U\<close>
  shows \<open>init_dt_spec (CS @ CS') S U\<close>
proof -
  obtain T' where
    TT': \<open>(T, T') \<in> twl_st_l_init\<close> and
    \<open>twl_struct_invs_init T'\<close> and
    \<open>clauses_to_update_l_init T = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l_init T). \<not> is_decided s\<close> and
    \<open>get_conflict_l_init T = None \<longrightarrow>
     literals_to_update_l_init T = uminus `# lit_of `# mset (get_trail_l_init T)\<close> and
    clss: \<open>remdups_mset `# mset `# mset CS + mset `# ran_mf (get_clauses_l_init S) + other_clauses_l_init S +
        get_unit_clauses_l_init S +
        get_subsumed_init_clauses_l_init S +
        get_init_clauses0_l_init S =
        mset `# ran_mf (get_clauses_l_init T) + other_clauses_l_init T + get_unit_clauses_l_init T +
        get_subsumed_init_clauses_l_init T +
        get_init_clauses0_l_init T\<close> and
    learned: \<open>learned_clss_lf (get_clauses_l_init S) = learned_clss_lf (get_clauses_l_init T)\<close> and
    unit_le:
      \<open>get_subsumed_learned_clauses_l_init S = get_subsumed_learned_clauses_l_init T\<close>
      \<open>get_learned_clauses0_l_init S = get_learned_clauses0_l_init T\<close>
      \<open>get_learned_unit_clauses_l_init S = get_learned_unit_clauses_l_init T\<close> and
    \<open>twl_list_invs (fst T)\<close> and
    \<open>twl_stgy_invs (fst T')\<close> and
    \<open>other_clauses_l_init T \<noteq> {#} \<longrightarrow> get_conflict_l_init T \<noteq> None\<close> and
    empty: \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l_init T \<noteq> None\<close> and
    confl_kept: \<open>get_conflict_l_init S \<noteq> None \<longrightarrow> get_conflict_l_init S = get_conflict_l_init T\<close>
    using spec1
    unfolding init_dt_spec_def apply -
    apply normalize_goal+
    by presburger

  obtain U' where
    UU': \<open>(U, U') \<in> twl_st_l_init\<close> and
    struct_invs: \<open>twl_struct_invs_init U'\<close> and
    WS: \<open>clauses_to_update_l_init U = {#}\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init U). \<not> is_decided s\<close> and
    confl: \<open>get_conflict_l_init U = None \<longrightarrow>
     literals_to_update_l_init U = uminus `# lit_of `# mset (get_trail_l_init U)\<close> and
    clss': \<open>remdups_mset `# mset `# mset CS' + mset `# ran_mf (get_clauses_l_init T) + other_clauses_l_init T +
     get_unit_clauses_l_init T + get_subsumed_init_clauses_l_init T + get_init_clauses0_l_init T =
     mset `# ran_mf (get_clauses_l_init U) + other_clauses_l_init U + get_unit_clauses_l_init U +
     get_subsumed_init_clauses_l_init U + get_init_clauses0_l_init U\<close> and
    learned': \<open>learned_clss_lf (get_clauses_l_init T) = learned_clss_lf (get_clauses_l_init U)\<close> and
    unit_le': \<open>get_learned_unit_clauses_l_init U = get_learned_unit_clauses_l_init T\<close>
      \<open>get_subsumed_learned_clauses_l_init U = get_subsumed_learned_clauses_l_init T\<close>
      \<open>get_learned_clauses0_l_init U = get_learned_clauses0_l_init T\<close> and
    list_invs: \<open>twl_list_invs (fst U)\<close> and
    stgy_invs: \<open>twl_stgy_invs (fst U')\<close> and
    oth: \<open>other_clauses_l_init U \<noteq> {#} \<longrightarrow> get_conflict_l_init U \<noteq> None\<close> and
    empty': \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_l_init U \<noteq> None\<close> and
    confl_kept': \<open>get_conflict_l_init T \<noteq> None \<longrightarrow> get_conflict_l_init T = get_conflict_l_init U\<close>
    using spec
    unfolding init_dt_spec_def apply -
    apply normalize_goal+
    by metis
  have \<open>remdups_mset `# mset `# mset (CS @ CS') + mset `# ran_mf (get_clauses_l_init S) + other_clauses_l_init S +
    get_unit_clauses_l_init S + get_subsumed_init_clauses_l_init S + get_init_clauses0_l_init S =
    remdups_mset `# mset `# mset CS' + (remdups_mset `# mset `# mset CS + mset `# ran_mf (get_clauses_l_init S) + other_clauses_l_init S +
    get_unit_clauses_l_init S + get_subsumed_init_clauses_l_init S + get_init_clauses0_l_init S)\<close>
    by auto
  also have \<open>... = remdups_mset `# mset `# mset CS' + mset `# ran_mf (get_clauses_l_init T) + other_clauses_l_init T +
        get_unit_clauses_l_init T + get_subsumed_init_clauses_l_init T + get_init_clauses0_l_init T\<close>
    unfolding clss by (auto simp: ac_simps)
  finally have eq: \<open>remdups_mset `# mset `# mset (CS @ CS') + mset `# ran_mf (get_clauses_l_init S) + other_clauses_l_init S +
    get_unit_clauses_l_init S +
    get_subsumed_init_clauses_l_init S +
    get_init_clauses0_l_init S =
    mset `# ran_mf (get_clauses_l_init U) + other_clauses_l_init U + get_unit_clauses_l_init U +
    get_subsumed_init_clauses_l_init U +
    get_init_clauses0_l_init U\<close>
    unfolding clss' .
  show ?thesis
    unfolding init_dt_spec_def apply -
    apply (rule exI[of _ U'])
    apply (intro conjI)
    subgoal using UU' .
    subgoal using struct_invs .
    subgoal using WS .
    subgoal using dec .
    subgoal using confl .
    subgoal using eq .
    subgoal using learned' learned by simp
    subgoal using unit_le unit_le' by simp
    subgoal using unit_le unit_le' learned by auto
    subgoal using unit_le unit_le' learned by auto
    subgoal using list_invs .
    subgoal using stgy_invs .
    subgoal using oth .
    subgoal using empty empty' oth confl_kept' by auto
    subgoal using confl_kept confl_kept' by auto
    done
qed

lemma init_dt_full:
  fixes CS :: \<open>'v literal list list\<close> and SOC :: \<open>'v twl_st_l_init\<close> and S'
  defines
    \<open>S \<equiv> fst SOC\<close> and
    \<open>OC \<equiv> snd SOC\<close>
  assumes
    \<open>init_dt_pre CS SOC\<close>
  shows
    \<open>init_dt CS SOC \<le> SPEC (init_dt_spec CS SOC)\<close>
  using assms unfolding S_def OC_def
proof (induction CS arbitrary: SOC)
  case Nil
  then obtain S OC where SOC: \<open>SOC = (S, OC)\<close>
    by (cases SOC) auto
  from Nil
  obtain T where
    T: \<open>(SOC, T) \<in> twl_st_l_init\<close>
      \<open>twl_struct_invs_init T\<close>
      \<open>clauses_to_update_l_init SOC = {#}\<close>
      \<open>\<forall>s\<in>set (get_trail_l_init SOC). \<not> is_decided s\<close>
      \<open>get_conflict_l_init SOC = None \<longrightarrow>
       literals_to_update_l_init SOC =
       uminus `# lit_of `# mset (get_trail_l_init SOC)\<close>
      \<open>twl_list_invs (fst SOC)\<close>
      \<open>twl_stgy_invs (fst T)\<close>
      \<open>other_clauses_l_init SOC \<noteq> {#} \<longrightarrow> get_conflict_l_init SOC \<noteq> None\<close>
    unfolding init_dt_pre_def apply -
    apply normalize_goal+
    by auto

  then show ?case
    unfolding init_dt_def SOC init_dt_spec_def nfoldli_simps
    apply (intro RETURN_rule)
    unfolding prod.simps
    apply (rule exI[of _ T])
    using T by (auto simp: SOC twl_st_init twl_st_l_init)
next
  case (Cons a CS) note IH = this(1) and pre = this(2)
  note init_dt_step_def[simp]
  have 1: \<open>init_dt_step a SOC \<le> SPEC (\<lambda>SOC'. init_dt_pre CS SOC' \<and> init_dt_spec [a] SOC SOC')\<close>
    by (rule init_dt_pre_init_dt_step[OF pre])
  have 2: \<open>init_dt_spec (a # CS) SOC UOC\<close>
    if spec: \<open>init_dt_spec CS T UOC\<close> and
       spec': \<open>init_dt_spec [a] SOC T\<close> for T UOC
    using init_dt_spec_append[OF spec' spec] by simp
  show ?case
    unfolding init_dt_def nfoldli_simps if_True
    apply (rule specify_left)
     apply (rule 1)
    apply (rule order.trans)
    unfolding init_dt_def[symmetric]
     apply (rule IH)
     apply (solves \<open>simp\<close>)
    apply (rule SPEC_rule)
    by (rule 2) fast+
qed

lemma init_dt_pre_empty_state:
  \<open>init_dt_pre [] (([], fmempty, None, {#}, {#}, {#}, {#}, {#},{#}, {#},{#}), {#})\<close>
  unfolding init_dt_pre_def
  by (auto simp: twl_st_l_init_def twl_struct_invs_init_def twl_st_inv.simps
      twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
      past_invs.simps clauses_def pcdcl_all_struct_invs_def clauses0_inv_def
      cdcl\<^sub>W_restart_mset_state twl_list_invs_def psubsumed_invs_def
      twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      cdcl\<^sub>W_restart_mset.no_smaller_confl_def entailed_clss_inv_def
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)

lemma twl_init_invs:
  \<open>twl_struct_invs_init (([], {#}, {#}, None, {#}, {#}, {#}, {#}, {#},{#}, {#},{#}), {#})\<close>
  \<open>twl_list_invs ([], fmempty, None, {#}, {#}, {#}, {#}, {#},{#}, {#},{#})\<close>
  \<open>twl_stgy_invs ([], {#}, {#}, None, {#}, {#}, {#}, {#}, {#}, {#}, {#},{#})\<close>
  by (auto simp: twl_struct_invs_init_def twl_st_inv.simps twl_list_invs_def twl_stgy_invs_def
      past_invs.simps
      twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
      past_invs.simps clauses_def pcdcl_all_struct_invs_def clauses0_inv_def
      cdcl\<^sub>W_restart_mset_state twl_list_invs_def psubsumed_invs_def
      twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      cdcl\<^sub>W_restart_mset.no_smaller_confl_def entailed_clss_inv_def
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
end
