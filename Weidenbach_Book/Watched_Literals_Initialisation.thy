theory Watched_Literals_Initialisation
  imports Watched_Literals_List "../lib/Explorer"
begin

subsection \<open>Initialise Data structure\<close>

type_synonym 'v twl_st_init = \<open>'v twl_st  \<times> 'v clauses\<close>


fun get_trail_init :: \<open>'v twl_st_init \<Rightarrow> ('v, 'v clause) ann_lit list\<close> where
  \<open>get_trail_init ((M, _, _, _, _, _, _), _) = M\<close>

fun get_conflict_init :: \<open>'v twl_st_init \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_init ((_, _, _, D, _, _, _, _), _) = D\<close>

fun literals_to_update_init :: \<open>'v twl_st_init \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_init ((_, _, _, _, _, _, _, Q), _) = Q\<close>

fun clauses_to_update_init :: \<open>'v twl_st_init \<Rightarrow> ('v literal \<times> 'v twl_cls) multiset\<close> where
  \<open>clauses_to_update_init ((_, _, _, _, _, _, WS, _), _) = WS\<close>

fun other_clauses_init :: \<open>'v twl_st_init \<Rightarrow> 'v clauses\<close> where
  \<open>other_clauses_init ((_, _, _, _, _, _, _), OC) = OC\<close>

fun add_to_init_clauses :: \<open>'v clause_l \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
  \<open>add_to_init_clauses C ((M, N, U, D, NE, UE, WS, Q), OC) =
      ((M, add_mset (twl_clause_of C) N, U, D, NE, UE, WS, Q), OC)\<close>

fun add_to_unit_init_clauses :: \<open>'v clause \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
  \<open>add_to_unit_init_clauses C ((M, N, U, D, NE, UE, WS, Q), OC) =
      ((M, N, U, D, add_mset C NE, UE, WS, Q), OC)\<close>

fun set_conflict_init :: \<open>'v clause_l \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
 \<open>set_conflict_init C ((M, N, U, _, NE, UE, WS, Q), OC) =
       ((M, N, U, Some (mset C), add_mset (mset C) NE, UE, {#}, {#}), OC)\<close>

fun propagate_unit_init :: \<open>'v literal \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init\<close> where
 \<open>propagate_unit_init L ((M, N, U, D, NE, UE, WS, Q), OC) =
       ((Propagated L {#L#} # M, N, U, D, add_mset {#L#} NE, UE, WS, add_mset (-L) Q), OC)\<close>

type_synonym 'v twl_st_l_init = \<open>'v twl_st_l \<times> 'v clauses\<close>

fun get_trail_l_init :: \<open>'v twl_st_l_init \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_l_init ((M, _, _, _, _, _, _), _) = M\<close>

fun get_conflict_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_l_init ((_, _, D, _, _, _, _), _) = D\<close>

fun get_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_l_init ((M, N, D, NE, UE, WS, Q), _) = N\<close>

fun literals_to_update_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_l_init ((_, _, _, _, _, _, Q), _) = Q\<close>

fun clauses_to_update_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses_to_update_l\<close> where
  \<open>clauses_to_update_l_init ((_, _, _, _, _, WS, _), _) = WS\<close>

fun other_clauses_l_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v clauses\<close> where
  \<open>other_clauses_l_init ((_, _, _, _, _, _, _), OC) = OC\<close>

fun state\<^sub>W_of_init :: "'v twl_st_init \<Rightarrow> 'v cdcl\<^sub>W_restart_mset" where
"state\<^sub>W_of_init ((M, N, U, C, NE, UE, Q), OC) =
  (M, clause `# N + NE + OC, clause `# U + UE, C)"


named_theorems twl_st_init \<open>Convertion for inital theorems\<close>

lemma [twl_st_init]:
  \<open>get_conflict_init (S, QC) = get_conflict S\<close>
  \<open>get_trail_init (S, QC) = get_trail S\<close>
  \<open>clauses_to_update_init (S, QC) = clauses_to_update S\<close>
  \<open>literals_to_update_init (S, QC) = literals_to_update S\<close>
  by (solves \<open>cases S; auto\<close>)+


definition twl_st_l_init :: \<open>('v twl_st_l_init \<times> 'v twl_st_init) set\<close> where
  \<open>twl_st_l_init = {(((M, N, C, NE, UE, WS, Q), OC), ((M', N', C', NE', UE', WS', Q'), OC')).
    ((M', N', C', NE', UE', WS', Q'), OC') =
      ((convert_lits_l N M, twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N,
         C, NE, UE, {#}, Q), OC)}\<close>


lemma [twl_st_init]:
  assumes \<open>(S, T) \<in> twl_st_l_init\<close>
  shows
   \<open>get_trail_init T = convert_lits_l (get_clauses_l_init S) (get_trail_l_init S)\<close>
   \<open>get_trail (fst T) = convert_lits_l (get_clauses_l_init S) (get_trail_l_init S)\<close>
  by (use assms in \<open>solves \<open>cases S; auto simp: twl_st_l_init_def\<close>\<close>)+

definition twl_struct_invs_init :: \<open>'v twl_st_init \<Rightarrow> bool\<close> where
  \<open>twl_struct_invs_init S \<longleftrightarrow>
    (twl_st_inv (fst S) \<and>
    valid_enqueued (fst S) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init S) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of_init S) \<and>
    twl_st_exception_inv (fst S) \<and>
    no_duplicate_queued (fst S) \<and>
    distinct_queued (fst S) \<and>
    confl_cands_enqueued (fst S) \<and>
    propa_cands_enqueued (fst S) \<and>
    (get_conflict_init S \<noteq> None \<longrightarrow> clauses_to_update_init S = {#} \<and> literals_to_update_init S = {#}) \<and>
    entailed_clss_inv (fst S) \<and>
    clauses_to_update_inv (fst S) \<and>
    past_invs (fst S))
  \<close>

lemma twl_struct_invs_init_add_mset:
  assumes \<open>twl_struct_invs_init (S, QC)\<close> and [simp]: \<open>distinct_mset C\<close> and
    count_dec: \<open>count_decided (trail (state\<^sub>W_of S)) = 0\<close>
  shows \<open>twl_struct_invs_init (S, add_mset C QC)\<close>
proof -
  have
    st_inv: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init (S, QC))\<close> and
    smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of_init (S, QC))\<close> and
    excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close> and
    cands_confl: \<open>confl_cands_enqueued S\<close> and
    cands_propa: \<open>propa_cands_enqueued S\<close> and
    confl: \<open>get_conflict S \<noteq> None \<longrightarrow> clauses_to_update S = {#} \<and> literals_to_update S = {#}\<close> and
    unit: \<open>entailed_clss_inv S\<close> and
    to_upd: \<open>clauses_to_update_inv S\<close> and
    past: \<open>past_invs S\<close>
    using assms unfolding twl_struct_invs_init_def fst_conv
    by (auto simp add: twl_st_init)

  show ?thesis
    unfolding twl_struct_invs_init_def fst_conv
    apply (intro conjI)
    subgoal by (rule st_inv)
    subgoal by (rule valid)
    subgoal using struct count_dec no_dup
      by (cases S)
        (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def clauses_def
          cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def)
    subgoal using smaller count_dec by (cases S)(auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
          cdcl\<^sub>W_restart_mset_state)
    subgoal by (rule excep)
    subgoal by (rule no_dup)
    subgoal by (rule dist)
    subgoal by (rule cands_confl)
    subgoal by (rule cands_propa)
    subgoal using confl by (auto simp: twl_st_init)
    subgoal by (rule unit)
    subgoal by (rule to_upd)
    subgoal by (rule past)
    done
qed

fun add_empty_conflict_init_l :: \<open>'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  add_empty_conflict_init_def[simp del]:
   \<open>add_empty_conflict_init_l ((M, N, D, NE, UE, WS, Q), OC) =
       ((M, N, Some {#}, NE, UE, WS, Q), add_mset {#} OC)\<close>


fun propagate_unit_init_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  propagate_unit_init_l_def[simp del]:
   \<open>propagate_unit_init_l L ((M, N, D, NE, UE, WS, Q), OC) =
       ((Propagated L 0 # M, N, D, add_mset {#L#} NE, UE, WS, add_mset (-L) Q), OC)\<close>


fun already_propagated_unit_init_l :: \<open>'v clause \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  already_propagated_unit_init_l_def[simp del]:
   \<open>already_propagated_unit_init_l C ((M, N, D, NE, UE, WS, Q), OC) =
       ((M, N, D, add_mset C NE, UE, WS, Q), OC)\<close>


fun set_conflict_init_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  set_conflict_init_l_def[simp del]:
   \<open>set_conflict_init_l C ((M, N, _, NE, UE, WS, Q), OC) =
       ((M, N, Some (mset C), add_mset (mset C) NE, UE, {#}, {#}), OC)\<close>


fun add_to_clauses_init_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init nres\<close> where
  add_to_clauses_init_l_def[simp del]:
   \<open>add_to_clauses_init_l C ((M, N, _, NE, UE, WS, Q), OC) = do {
        i \<leftarrow> get_fresh_index N;
        RETURN ((M, fmupd i (C, True) N, None, NE, UE, WS, Q), OC)
    }\<close>

fun add_to_other_init where
  \<open>add_to_other_init C (S, OC) = (S, add_mset (mset C) OC)\<close>

lemma fst_add_to_other_init [simp]: \<open>fst (add_to_other_init a T) = fst T\<close>
  by (cases T) auto

definition init_dt_step :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init nres\<close> where
  \<open>init_dt_step C S =
  (case get_conflict_l (fst S) of
    None \<Rightarrow>
    if length C = 0
    then RETURN (add_empty_conflict_init_l S)
    else if length C = 1
    then
      let L = hd C in
      if undefined_lit (get_trail_l_init S) L
      then RETURN (propagate_unit_init_l L S)
      else if L \<in> lits_of_l (get_trail_l_init S)
      then RETURN (already_propagated_unit_init_l (mset C) S)
      else RETURN (set_conflict_init_l C S)
    else
        add_to_clauses_init_l C S
  | Some D \<Rightarrow>
      RETURN (add_to_other_init C S))\<close>

fun init_dt :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init nres\<close> where
  \<open>init_dt [] S = RETURN S\<close>
| \<open>init_dt (C # CS) S =  do {
      S \<leftarrow> init_dt_step C S;
      init_dt CS S
   }\<close>

definition   init_dt_pre where
  \<open>init_dt_pre CS SOC \<longleftrightarrow>
    (\<exists>T. (SOC, T) \<in> twl_st_l_init \<and>
      (\<forall>C \<in> set CS. distinct C) \<and>
      twl_struct_invs_init T \<and>
      clauses_to_update_l_init SOC = {#} \<and>
      (\<forall>s\<in>set (get_trail_l_init SOC). \<not>is_decided s) \<and>
      (get_conflict_l_init SOC = None \<longrightarrow>
          literals_to_update_l_init SOC = uminus `# lit_of `# mset (get_trail_l_init SOC)) \<and>
      twl_list_invs (fst SOC) \<and>
      twl_stgy_invs (fst T) \<and>
      (other_clauses_l_init SOC \<noteq> {#} \<longrightarrow> get_conflict_l_init SOC \<noteq> None))\<close>

lemma init_dt_pre_ConsD: \<open>init_dt_pre (a # CS) SOC \<Longrightarrow> init_dt_pre CS SOC \<and> distinct a\<close>
  unfolding init_dt_pre_def
  apply normalize_goal+
  by fastforce

definition init_dt_spec where
  \<open>init_dt_spec CS SOC = (\<lambda>(S', OC'). 
       \<exists>T'. ((S', OC'), T') \<in> twl_st_l_init \<and>
           twl_struct_invs_init T' \<and>
           clauses_to_update_l S' = {#} \<and>
           (\<forall>s\<in>set (get_trail_l S'). \<not>is_decided s) \<and>
           (get_conflict_l S' = None \<longrightarrow>
              literals_to_update_l S' = uminus `# lit_of `# mset (get_trail_l S')) \<and>
           (mset `# mset CS + mset `# ran_mf (get_clauses_l (fst SOC)) + snd SOC =
              mset `# ran_mf (get_clauses_l S') + OC') \<and>
           learned_clss_lf (get_clauses_l (fst SOC)) = learned_clss_lf (get_clauses_l S') \<and>
           twl_list_invs S' \<and>
           twl_stgy_invs (fst T') \<and>
           (OC' \<noteq> {#} \<longrightarrow> get_conflict_l S' \<noteq> None) \<and>
           ({#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l S' \<noteq> None))\<close>


lemma twl_struct_invs_init_add_to_other_init:
  assumes 
    dist: \<open>distinct a\<close> and
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close>
  shows
    \<open>twl_struct_invs_init (add_to_other_init a T)\<close>
      (is ?twl_struct_invs_init)
proof -
  obtain M N U D NE UE Q OC WS where
    T: \<open>T = ((M, N, U, D, NE, UE, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]: 
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset a) (clauses N + NE + OC), clauses U + UE, D)\<close>
    using dist
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
        clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)

  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset a) (clauses N + NE + OC),
        clauses U + UE, D)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  show ?twl_struct_invs_init
    using invs
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by clarsimp
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
  obtain M N U D NE UE Q OC WS where
    T: \<open>T = ((M, N, U, D, NE, UE, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]: 
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset a) (clauses N + NE + OC), clauses U + UE, D)\<close>
    using twl_struct_invs_init_add_to_other_init[OF dist lev invs]
    unfolding T twl_struct_invs_init_def
    by simp

  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset a) (clauses N + NE + OC),
        clauses U + UE, D)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  have [simp]: \<open>confl_cands_enqueued (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) \<longleftrightarrow>
     confl_cands_enqueued (M, N, U, D, NE, UE, WS, Q)\<close>
    \<open>propa_cands_enqueued (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) \<longleftrightarrow>
      propa_cands_enqueued (M, N, U, D, NE, UE, WS, Q)\<close>
    \<open>twl_st_inv (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) \<longleftrightarrow>
        twl_st_inv (M, N, U, D, NE, UE, WS, Q)\<close>
    \<open>\<And>x.  twl_exception_inv (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) x \<longleftrightarrow>
          twl_exception_inv (M, N, U, D, NE, UE, WS, Q) x\<close>
    \<open>clauses_to_update_inv (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) \<longleftrightarrow>
       clauses_to_update_inv (M, N, U, D, NE, UE, WS, Q)\<close>
    \<open>past_invs (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) \<longleftrightarrow>
        past_invs (M, N, U, D, NE, UE, WS, Q)\<close>
    by (cases D; auto simp: twl_st_inv.simps twl_exception_inv.simps past_invs.simps; fail)+
  have [simp]: \<open>entailed_clss_inv (M, N, U, D, add_mset (mset a) NE, UE, WS, Q) \<longleftrightarrow>
     entailed_clss_inv (M, N, U, D, NE, UE, WS, Q)\<close>
    using ex count_decided_ge_get_level[of M] lev by (cases D) (auto simp: T)
  show ?all_struct
    using invs ex
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
    nempty: \<open>C \<noteq> []\<close>
  shows
    \<open>twl_struct_invs_init (set_conflict_init C T)\<close>
      (is ?all_struct)
proof -
  obtain M N U D NE UE Q OC WS where
    T: \<open>T = ((M, N, U, D, NE, UE, WS, Q), OC)\<close>
    by (cases T) auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]: 
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset (mset C) (clauses N + NE + OC),
        clauses U + UE, Some (mset C))\<close>
    using dist ex
    unfolding T twl_struct_invs_init_def
    by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
       clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
       true_annots_true_cls_def_iff_negation_in_model)

  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, add_mset (mset C) (clauses N + NE + OC),
        clauses U + UE, Some (mset C))\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  let ?T = \<open>(M, N, U, Some (mset C), add_mset (mset C) NE, UE, {#}, {#})\<close>
  have [simp]: \<open>confl_cands_enqueued ?T\<close>
    \<open>propa_cands_enqueued ?T\<close>
    \<open>twl_st_inv (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> twl_st_inv ?T\<close>
    \<open>\<And>x.  twl_exception_inv (M, N, U, D, NE, UE, WS, Q) x \<Longrightarrow> twl_exception_inv ?T x\<close>
    \<open>clauses_to_update_inv (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> clauses_to_update_inv ?T\<close>
    \<open>past_invs (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> past_invs ?T\<close>
    by (auto simp: twl_st_inv.simps twl_exception_inv.simps past_invs.simps; fail)+
  have [simp]: \<open> entailed_clss_inv (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> entailed_clss_inv ?T\<close>
    using ex count_decided_ge_get_level[of M] lev nempty by (auto simp: T)
  show ?all_struct
    using invs ex
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by (clarsimp simp del: entailed_clss_inv.simps)
qed

lemma twl_struct_invs_init_propagate_unit_init:
  assumes
    lev: \<open>count_decided (get_trail (fst T)) = 0\<close> and
    invs: \<open>twl_struct_invs_init T\<close> and
    undef: \<open>undefined_lit (get_trail_init T) L\<close>
  shows
    \<open>twl_struct_invs_init (propagate_unit_init L T)\<close>
      (is ?all_struct)
proof -
  obtain M N U D NE UE Q OC WS where
    T: \<open>T = ((M, N, U, D, NE, UE, WS, Q), OC)\<close>
    by (cases T) auto
  have [iff]: \<open>- L \<in> lits_of_l M \<longleftrightarrow> False\<close>
    using undef by (auto simp: T Decided_Propagated_in_iff_in_lits_of_l)
  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition) (use lev in \<open>auto simp: T count_decided_0_iff\<close>)
  have H: \<open>a @ Propagated L' mark' # b = Propagated L mark # M  \<longleftrightarrow>
     (a = [] \<and> L = L' \<and> mark = mark' \<and> b = M) \<or>
     (a \<noteq> [] \<and> hd a = Propagated L mark \<and> tl a @ Propagated L' mark' # b = M)\<close>
    for a mark mark' L' b
    using undef by (cases a) (auto simp: T atm_of_eq_atm_of)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]: 
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, add_mset {#L#} (clauses N + NE + OC), clauses U + UE, D)\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
        clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
  then have [simp]: 
   \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (Propagated L {#L#} # M,
        add_mset {#L#} (clauses N + NE + OC), clauses U + UE, D)\<close>
    using undef by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def T H
       cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def all_decomposition_implies_def
        clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
        consistent_interp_insert_iff)
  have [iff]: \<open>Propagated L {#L#} # M = M' @ Decided K # Ma \<longleftrightarrow> False\<close> for M' K Ma
    sorry
  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (Propagated L {#L#} # M, add_mset {#L#} (clauses N + NE + OC),
        clauses U + UE, D)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)

  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M, clauses N + NE + OC, clauses U + UE, D)\<close>
    using invs unfolding T twl_struct_invs_init_def by auto
  then have [simp]:
     \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (Propagated L {#L#} # M, add_mset {#L#} (clauses N + NE + OC),
        clauses U + UE, D)\<close>
    using lev
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state
        clauses_def T count_decided_0_iff)
  let ?T = \<open>(Propagated L {#L#} # M, N, U, D, add_mset {#L#} NE, UE, WS, add_mset (-L) Q)\<close>
  have [simp]:
     \<open>confl_cands_enqueued (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow>
       confl_cands_enqueued ?T\<close>
    \<open>propa_cands_enqueued (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow>propa_cands_enqueued ?T\<close>
    \<open>twl_st_inv (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> twl_st_inv ?T\<close>
    \<open>\<And>x.  twl_exception_inv (M, N, U, D, NE, UE, WS, Q) x \<Longrightarrow> twl_exception_inv ?T x\<close>
    \<open>clauses_to_update_inv (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> clauses_to_update_inv ?T\<close>
    \<open>past_invs (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> past_invs ?T\<close>
         apply (cases D; auto simp: twl_st_inv.simps twl_exception_inv.simps past_invs.simps)
    sorry
  have [simp]: \<open>entailed_clss_inv (M, N, U, D, NE, UE, WS, Q) \<Longrightarrow> entailed_clss_inv ?T\<close>
    using ex count_decided_ge_get_level[of M] lev by (cases D) (auto simp: T get_level_cons_if)
  show ?all_struct
    using invs ex
    unfolding twl_struct_invs_init_def T
    unfolding fst_conv add_to_other_init.simps state\<^sub>W_of_init.simps get_conflict.simps
    by (clarsimp simp del: entailed_clss_inv.simps clauses_to_update_inv.simps
        valid_enqueued_alt_simps)
qed

named_theorems twl_st_l_init
lemma [twl_st_l_init]:
  \<open>clauses_to_update_l_init (already_propagated_unit_init_l C S) = clauses_to_update_l_init S\<close>
  \<open>get_trail_l_init (already_propagated_unit_init_l C S) = get_trail_l_init S\<close>
  \<open>get_conflict_l_init (already_propagated_unit_init_l C S) = get_conflict_l_init S\<close>
  \<open>other_clauses_l_init (already_propagated_unit_init_l C S) = other_clauses_l_init S\<close>
  \<open>clauses_to_update_l_init (already_propagated_unit_init_l C S) = clauses_to_update_l_init S\<close>
  \<open>literals_to_update_l_init (already_propagated_unit_init_l C S) = literals_to_update_l_init S\<close>
  \<open>get_conflict_l_init (T, OC) = get_conflict_l T\<close>
  by (solves \<open>cases S; cases T; auto simp: already_propagated_unit_init_l_def\<close>)+

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

lemma entailed_clss_inv_add_to_unit_init_clauses:
  \<open>count_decided (get_trail_init T) = 0 \<Longrightarrow> C \<noteq> [] \<Longrightarrow> hd C \<in> lits_of_l (get_trail_init T) \<Longrightarrow>
     entailed_clss_inv (fst T) \<Longrightarrow> entailed_clss_inv (fst (add_to_unit_init_clauses (mset C) T))\<close>
  using count_decided_ge_get_level[of \<open>get_trail_init T\<close>]
  by (cases T; cases C; auto simp: twl_st_inv.simps twl_exception_inv.simps)

lemma init_dt_pre_already_propagated_unit_init_l:
  assumes 
    hd_C: \<open>hd C \<in> lits_of_l (get_trail_l_init S)\<close> and
    pre: \<open>init_dt_pre CS S\<close> and
    nempty: \<open>C \<noteq> []\<close> and
    dist_C: \<open>distinct C\<close> and
    lev: \<open>count_decided (get_trail_l_init S) = 0\<close>
  shows \<open>init_dt_pre CS (already_propagated_unit_init_l (mset C) S)\<close>
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    dist: \<open>Ball (set CS) distinct\<close> and
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
  obtain M N D NE UE Q U OC where
    S: \<open>S = ((M, N, U, D, NE, UE, Q), OC)\<close>
    by (cases S) auto
  have [simp]: \<open>twl_list_invs (fst (already_propagated_unit_init_l (mset C) S))\<close>
    using add_inv by (auto simp:  already_propagated_unit_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(already_propagated_unit_init_l (mset C) S, add_to_unit_init_clauses (mset C) T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S) (auto simp: twl_st_l_init_def already_propagated_unit_init_l_def)
  have dec': \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close>
    using SOC_T dec by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def)
  have [simp]: \<open>twl_stgy_invs (fst (add_to_unit_init_clauses (mset C) T))\<close>
    using stgy_inv dec' unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T)
       (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (add_to_unit_init_clauses (mset C) T)\<close>
    apply (rule twl_struct_invs_init_add_to_unit_init_clauses)
    using inv hd_C nempty dist_C lev SOC_T dec
    by (auto simp: twl_st_init count_decided_0_iff)
  show ?thesis
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>add_to_unit_init_clauses (mset C) T\<close>])
    using dist WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
qed

lemma [twl_st_l_init]:
  \<open>get_trail_l_init (set_conflict_init_l C S) = get_trail_l_init S\<close>
  \<open>literals_to_update_l_init (set_conflict_init_l C S) = {#}\<close>
  \<open>clauses_to_update_l_init (set_conflict_init_l C S) = {#}\<close>
  \<open>get_conflict_l_init (set_conflict_init_l C S) = Some (mset C)\<close>
  by (cases S; auto simp: set_conflict_init_l_def)+

lemma init_dt_pre_set_conflict_init_l:
  assumes 
    \<open>get_conflict_l_init S = None\<close> and
    pre: \<open>init_dt_pre (C # CS) S\<close> and
    false: \<open>\<forall>L \<in> set C.  -L \<in> lits_of_l (get_trail_l_init S)\<close> and
    nempty: \<open>C \<noteq> []\<close>
  shows \<open>init_dt_pre CS (set_conflict_init_l C S)\<close>
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    dist: \<open>Ball (set CS) distinct\<close> and
    dist_C: \<open>distinct C\<close> and
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
  obtain M N D NE UE Q U OC where
    S: \<open>S = ((M, N, U, D, NE, UE, Q), OC)\<close>
    by (cases S) auto
  have [simp]: \<open>twl_list_invs (fst (set_conflict_init_l C S))\<close>
    using add_inv by (auto simp:  set_conflict_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(set_conflict_init_l C S, set_conflict_init C T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S) (auto simp: twl_st_l_init_def set_conflict_init_l_def)
  have dec': \<open>count_decided (get_trail_init T) = 0\<close>
    using SOC_T dec SOC_T by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def
        count_decided_0_iff)
  have [simp]: \<open>twl_stgy_invs (fst (set_conflict_init C T))\<close>
    using stgy_inv dec' nempty count_decided_ge_get_level[of \<open>get_trail_init T\<close>]
    unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T; cases C)
       (auto 5 5 simp: cdcl\<^sub>W_restart_mset_state clauses_def)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (set_conflict_init C T)\<close>
    apply (rule twl_struct_invs_init_set_conflict_init)
    using inv nempty dist_C SOC_T dec false nempty
    by (auto simp: twl_st_init count_decided_0_iff)
  show ?thesis
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>set_conflict_init C T\<close>])
    using dist WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
qed

lemma
  assumes 
    \<open>get_conflict_l_init S = None\<close> and
    nempty: \<open>length C = Suc 0\<close> and
    pre: \<open>init_dt_pre (C # CS) S\<close> and
    dec: \<open>\<forall>s\<in>set (get_trail_l_init S). \<not> is_decided s\<close> and
    \<open>hd C \<notin> lits_of_l (get_trail_l_init S)\<close> and
    \<open>undefined_lit (get_trail_l_init S) (hd C)\<close>
  shows \<open>init_dt_pre CS (propagate_unit_init_l (hd C) S)\<close>
proof -
  obtain T where
    SOC_T: \<open>(S, T) \<in> twl_st_l_init\<close> and
    dist: \<open>Ball (set CS) distinct\<close> and
    dist_C: \<open>distinct C\<close> and
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
  let ?L = \<open>hd C\<close>
  obtain M N D NE UE Q U OC where
    S: \<open>S = ((M, N, U, D, NE, UE, Q), OC)\<close>
    by (cases S) auto
  have [simp]: \<open>twl_list_invs (fst (propagate_unit_init_l ?L S))\<close>
    using add_inv by (auto simp:  propagate_unit_init_l_def S
        twl_list_invs_def)
  have [simp]: \<open>(propagate_unit_init_l ?L S, propagate_unit_init ?L T)
        \<in> twl_st_l_init\<close>
    using SOC_T by (cases S) (auto simp: twl_st_l_init_def propagate_unit_init_l_def)
  have dec': \<open>count_decided (get_trail_init T) = 0\<close>
    using SOC_T dec SOC_T by (auto simp: twl_st_l_init twl_st_init convert_lits_l_def
        count_decided_0_iff)
  have dec': \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close>
    using SOC_T dec by (auto simp: twl_st_init twl_st_l_init convert_lits_l_def)
  then have \<open>Propagated (hd C) {#hd C#} # get_trail_init T = M' @ Decided K # M \<longleftrightarrow> False\<close>
    for M' K M
    by (cases M') auto
  then have [simp]: \<open>twl_stgy_invs (fst (propagate_unit_init ?L T))\<close>
    using stgy_inv dec' nempty count_decided_ge_get_level[of \<open>get_trail_init T\<close>]
    unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (cases T)
       (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def get_level_cons_if)
  note clauses_to_update_inv.simps[simp del] valid_enqueued_alt_simps[simp del]
  have [simp]: \<open>twl_struct_invs_init (propagate_unit_init ?L T)\<close>
    apply (rule twl_struct_invs_init_set_conflict_init)
    using inv nempty dist_C SOC_T dec false nempty
    by (auto simp: twl_st_init count_decided_0_iff)
  show ?thesis
    unfolding init_dt_pre_def
    apply (rule exI[of _ \<open>propagate_unit_init ?L T\<close>])
    using dist WS dec in_literals_to_update OC'_empty by (auto simp: twl_st_init twl_st_l_init)
qed


lemma
  assumes pre: \<open>init_dt_pre (a # CS) SOC\<close>
  shows \<open>init_dt_step a SOC \<le> SPEC (init_dt_pre CS)\<close>
proof -
  obtain S OC where SOC: \<open>SOC = (S, OC)\<close>
    by (cases SOC) auto

  obtain T where
    SOC_T: \<open>((S, OC), T) \<in> twl_st_l_init\<close> and
    dist: \<open>Ball (set (a # CS)) distinct\<close> and
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

(*   case 2 note dist = this(1) and inv = this(2) and
    WS = this(3) and dec = this(4) and in_literals_to_update = this(5) and add_inv = this(6) and
    len = this(7) and stgy_inv = this(8) and OC'_empty = this(9)
  let ?SOC' = \<open>init_dt CS (S, OC)\<close>
  let ?S' = \<open>fst (init_dt CS (S, OC))\<close>
  let ?OC' = \<open>snd (init_dt CS (S, OC))\<close>
  have
    twl: \<open>twl_struct_invs_init (twl_st_of_init ?SOC')\<close> and
    w_q: \<open>clauses_to_update_l ?S' = {#}\<close> and
    dec': \<open>\<forall>s\<in>set (get_trail_l ?S'). \<not> is_decided s\<close> and
    literals_to_update': \<open>get_conflict_l ?S' = None \<longrightarrow>
        literals_to_update_l ?S' = uminus `# lit_of `# mset (get_trail_l ?S')\<close>
      and
    clss': \<open>mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None S)) + OC =
      cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None ?S')) + ?OC'\<close>
      and
    learned': \<open>learned_clss (state\<^sub>W_of (twl_st_of None ?S')) = learned_clss (state\<^sub>W_of (twl_st_of None S))\<close>
      and
    add_inv': \<open>twl_list_invs ?S'\<close> and
    U': \<open>get_learned_l ?S' = length (get_clauses_l ?S') - 1\<close> and
    OC'_empty: \<open>snd ?SOC' \<noteq> {#} \<longrightarrow> get_conflict_l ?S' \<noteq> None\<close>and
    OC'_empty_conflict: \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l ?S' \<noteq> None\<close>
    using IH[OF _ inv WS dec in_literals_to_update add_inv len stgy_inv OC'_empty] dist by auto
 *)
  obtain M N D NE UE Q where
    S: \<open>SOC = ((M, N, D, NE, UE, {#}, Q), OC)\<close>
    using WS by (cases SOC) (auto simp: SOC)
  then have S': \<open>S = (M, N, D, NE, UE, {#}, Q)\<close>
    using S unfolding SOC by auto
  show ?thesis
  proof (cases \<open>get_conflict_l (fst SOC)\<close>)
    case None
    then show ?thesis
      apply (auto simp: init_dt_step_def get_fresh_index_def RES_RETURN_RES)
      using pre dec apply (auto simp add: Let_def count_decided_0_iff SOC twl_st_l_init twl_st_init
          intro!: init_dt_pre_already_propagated_unit_init_l init_dt_pre_set_conflict_init_l
          dest: init_dt_pre_ConsD in_lits_of_l_defined_litD)
      defer
      explore_lemma
      sorry
  next
    case [simp]: (Some D)
    have [simp]: \<open>(((M, N, Some D, NE, UE, {#}, Q), add_mset (mset a) OC), add_to_other_init (mset a) T)
       \<in> twl_st_l_init\<close>
      \<open>get_trail (fst T) = convert_lits_l N M\<close>
      using SOC_T by (cases T; auto simp: S S' twl_st_l_init_def; fail)+
    have \<open>init_dt_pre CS ((M, N, Some D, NE, UE, {#}, Q), add_mset (mset a) OC)\<close>
      unfolding init_dt_pre_def
      apply (rule exI[of _ \<open>add_to_other_init (mset a) T\<close>])
      using dist inv WS dec  in_literals_to_update add_inv stgy_inv SOC_T
      by (auto simp: S'  count_decided_0_iff
          intro!: twl_struct_invs_init_add_to_other_init)
    then show ?thesis
      by (auto simp: S init_dt_step_def)

  qed
    apply (auto simp: S init_dt_step_def init_dt_pre_def)

  obtain M N D NE UE Q OCS where
    S: \<open>init_dt CS (S, OC) = ((M, N, D, NE, UE, {#}, Q), OCS)\<close>
    using w_q by (cases \<open>init_dt CS (S, OC)\<close>) auto
  obtain M' N' U' D' NE' WS' UE' Q' where
    S': \<open>twl_st_of None (fst (init_dt (a # CS) (S, OC))) = (M', N', U', D', NE', UE', WS', Q')\<close>
    by (cases \<open>twl_st_of None (fst (init_dt (a # CS) (S, OC)))\<close>) auto
  then have [simp]: \<open>UE' = UE\<close>
    by (cases a; cases D) (auto simp: S split: if_splits)

  have dec_M: \<open>\<forall>s\<in>set M. \<not> is_decided s\<close>
    using dec' S by auto
  have N_not_empty: \<open>N \<noteq> []\<close>
    using add_inv' unfolding twl_list_invs_def S by auto
  have U_len_N: \<open>U = length N - 1\<close>
    using U' unfolding S by auto
  then have [simp]: \<open>take U (tl N) = tl N\<close> \<open>drop (Suc U) N = []\<close> \<open>drop U (tl N) = []\<close>
    by auto
  show ?case using w_q
    by (cases D) (auto simp: S Let_def)
  case 3
  show ?case
    using dec_M by (cases D) (auto simp: S Let_def)
  case 4
  show ?case
    using literals_to_update' by (cases D) (auto simp: S Let_def)
  have a_D: \<open>\<exists>x y a'. a = x # y # a'\<close> if \<open>\<forall>L. a \<noteq> [L]\<close> and \<open>a \<noteq> []\<close>
    apply (case_tac a, (use that in simp; fail))
    apply (rename_tac aa list, case_tac list; use that in simp)
    done
  have mset_tl_N: \<open>{#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (take U (tl N))#} + {#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (drop (Suc U) N)#} =
         {#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (tl N)#}\<close>
    unfolding image_mset_union[symmetric] mset_append[symmetric] append_take_drop_id drop_Suc ..
  case 5
  show ?case
    using clss' U_len_N N_not_empty by (cases D)
      (auto simp: S Let_def clauses_def length_list_Suc_0 cdcl\<^sub>W_restart_mset_state mset_tl_N
        dest!: a_D)
  case 6
  show ?case
    using learned' U_len_N by (cases D) (auto simp: S Let_def clauses_def length_list_Suc_0
        cdcl\<^sub>W_restart_mset_state)

  case 7
  show ?case
    using add_inv' N_not_empty
    by (cases D) (fastforce simp add: U_len_N S clauses_def twl_list_invs_def Let_def nth_append
        cdcl\<^sub>W_restart_mset_state)+
  case 8
  show ?case
    by (cases D) (auto simp add: U_len_N S clauses_def twl_list_invs_def Let_def nth_append
        cdcl\<^sub>W_restart_mset_state)

  let ?S' = \<open>(convert_lits_l N M, twl_clause_of `# mset (take U (tl N)),
       twl_clause_of `# mset (drop U (tl N)), D, NE, UE, {#}, Q)\<close>
  case 1
  let ?S' = \<open>((convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), D, NE, UE, {#}, Q), OCS)\<close>
  let ?T' = \<open>state\<^sub>W_of_init ?S'\<close>
  have
    struct: \<open>Multiset.Ball (twl_clause_of `# mset (tl N)) struct_wf_twl_cls\<close> and
    H: \<open>\<forall>C\<in>#twl_clause_of `# mset (tl N). D = None \<longrightarrow>
      \<not> twl_is_an_exception C Q ({#} :: ('v literal \<times> 'v twl_cls) multiset ) \<longrightarrow>
      (twl_lazy_update (convert_lits_l N M) C \<and> twl_inv (convert_lits_l N M) C)\<close> and
    lev: \<open>\<forall>C\<in>#twl_clause_of `# mset (tl N). D = None \<longrightarrow> watched_literals_false_of_max_level (convert_lits_l N M) C\<close> and
    valid: \<open>valid_enqueued (fst ?S')\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ?T'\<close> and
    no_smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa ?T'\<close> and
    excep: \<open>twl_st_exception_inv (fst ?S')\<close> and
    no_dup: \<open>no_duplicate_queued (fst ?S')\<close> and
    dist_q: \<open>distinct_queued (fst ?S')\<close> and
    confl_cands: \<open>confl_cands_enqueued (fst ?S')\<close> and
    propa_cands: \<open>propa_cands_enqueued (fst ?S')\<close> and
    get_confl: \<open>get_conflict (fst ?S') \<noteq> None \<longrightarrow> clauses_to_update (fst ?S') = {#} \<and>
    literals_to_update (fst ?S') = {#}\<close> and
    unit_clss: \<open>entailed_clss_inv (fst ?S')\<close> and
    w_q: \<open>clauses_to_update_inv (fst ?S')\<close> and
    past_invs: \<open>past_invs (fst ?S')\<close>
    using twl unfolding twl_st_inv.simps twl_struct_invs_init_def S twl_st_of.simps
    image_mset_union[symmetric] mset_append[symmetric] append_take_drop_id drop_Suc S
    twl_struct_invs_def fst_conv twl_st_of_init.simps by fast+

  have [simp]: \<open>get_level M L = 0\<close> and
    [simp]: \<open>count_decided M = 0\<close> for L
    using dec' S by (auto simp: count_decided_0_iff)
  have nm: \<open>\<forall>s\<in>set (convert_lits_l N M). \<not> is_decided s\<close>
      using dec_M by (auto simp: convert_lits_l_def)
  have convert_append_Decided_cons[iff]:
    \<open>convert_lits_l N M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
    \<open>Propagated L C # convert_lits_l N M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
    for M'a K Ma L C
    using nm apply fastforce
    by (metis (no_types, lifting) nm annotated_lit.disc(1)
          annotated_lit.distinct(1) append_eq_Cons_conv in_set_conv_decomp list_tail_coinc)
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm ?T'\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ?T'\<close> and
    learned_tauto: \<open>(\<forall>s\<in>#learned_clss ?T'. \<not> tautology s)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state ?T'\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting ?T'\<close> and
    all_decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ?T')
     (get_all_ann_decomposition (trail ?T'))\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause ?T'\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
    by fast+
  have propagated_trail_decomp_iff[iff]: \<open>a @ Propagated La C # b = Propagated L D # M' \<longleftrightarrow>
        (a = [] \<and> Propagated La C = Propagated L D \<and> b = M') \<or>
        (a \<noteq> [] \<and> tl a @ Propagated La C # b = M' \<and> hd a = Propagated L D)\<close> for a b La L C D M'
    by (cases a) auto

  have ex_two_watched_N: \<open>\<exists>L L'. watched_l x = [L, L']\<close> if \<open>x \<in> set (tl N)\<close> for x
  proof -
    have \<open>struct_wf_twl_cls (twl_clause_of x)\<close>
      using struct that by auto
    then show ?thesis
      by (cases \<open>twl_clause_of x\<close>) (auto simp: length_list_2 take_2_if)
  qed

  have in_M_IN_QD: \<open>- La \<in> lits_of_l M \<Longrightarrow> La \<in># Q\<close> if \<open>D = None\<close> for La
    using S literals_to_update' that by (auto simp: lits_of_def uminus_lit_swap)

  have \<open>x \<in> set M \<Longrightarrow> convert_lit (N @ N') x = convert_lit N x\<close> for x N'
    using add_inv' by (cases x) (auto simp: nth_append twl_list_invs_def S)
  then have [simp]: \<open>convert_lits_l (N @ N') M = convert_lits_l N M\<close> for N'
    unfolding convert_lits_l_def by auto
  consider
    (confl) \<open>D \<noteq> None\<close> |
    (empty) \<open>D = None\<close> and \<open>a = []\<close> |
    (True) \<open>D = None\<close> and \<open>length a = 1\<close> |
    (False) \<open>D = None\<close> and \<open>length a \<ge> 2\<close>
    by (cases a; cases \<open>tl a\<close>) auto
  then show ?case
  proof cases
    case confl
    then show ?thesis
      using S' twl dist by (auto simp: S cdcl\<^sub>W_restart_mset_state
          intro!: twl_struct_invs_init_add_mset)
  next
    case a: empty
    have [simp]: \<open>NE' = NE\<close>
    using S' by (cases D) (auto simp: a S split: if_splits)
  note in_M_IN_QD = in_M_IN_QD[OF a(1)]
  have all_inv':
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_lits_l N M,
      add_mset {#}
       ({#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (tl N)#} + NE' + OCS),
      UE', Some {#})\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
    apply (intro conjI)
    subgoal
      using alien by (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def
          mset_take_mset_drop_mset atms_of_def
          dest: in_lits_of_l_defined_litD split: if_splits)
    subgoal
      using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
    subgoal
      using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
    subgoal
      using all_struct by (auto simp: cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          split: if_splits)
    subgoal
      using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def Decided_Propagated_in_iff_in_lits_of_l
          split: if_splits)
    subgoal
      apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
      using all_decomp by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
          intro!: all_decomposition_implies_insert_single
          split: if_splits)
    subgoal
      using learned by (auto 5 5 simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def image_Un
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
          split: if_splits)
    done
  show ?thesis
    unfolding twl_struct_invs_init_def S' twl_st_inv.simps
    apply (intro conjI)
    subgoal
      using H S' dec' nm struct by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
          split: if_splits)
    subgoal
      using struct S' by (auto simp: a S split: if_splits)[]
    subgoal using all_inv' by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
          split: if_splits)
    subgoal
      using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' excep by (force simp: a S twl_exception_inv.simps split: if_splits)
    subgoal
      using S' by (auto simp: a S split: if_splits)
    subgoal
      using S' excep by (force simp: a S twl_exception_inv.simps split: if_splits)
    subgoal
      using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' dist_q literals_to_update' by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' confl_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
          dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
          split: if_splits)
    subgoal
      using S' propa_cands unit_clss by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
          dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
          split: if_splits)
    subgoal
      using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' past_invs by (auto simp: a S past_invs.simps
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    done
  next
    case True note _[simp] = this(1) and a = this(2)
    then obtain L where a: \<open>a = [L]\<close>
      using list_decomp_1 by blast
    note in_M_IN_QD = in_M_IN_QD[OF True(1)]
    have all_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init (twl_st_of_init (init_dt (a # CS) (S, OC))))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
        init_dt.simps S
      apply (intro conjI)
      subgoal
        using alien by (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: in_lits_of_l_defined_litD split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            split: if_splits)
      subgoal
        using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def Decided_Propagated_in_iff_in_lits_of_l
            split: if_splits)
      subgoal
        apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
        using all_decomp by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
            intro!: all_decomposition_implies_insert_single
            split: if_splits)
      subgoal
        using learned by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
            split: if_splits)
      done
    show ?thesis
      unfolding twl_struct_invs_init_def S' twl_st_inv.simps
      apply (intro conjI)
      subgoal
        using H S' dec' nm struct by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            split: if_splits)
      subgoal
        using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if split: if_splits)
      subgoal using all_inv'
        using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' excep by (force simp: a S twl_exception_inv.simps split: if_splits)
      subgoal
        using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' dist_q literals_to_update' by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' confl_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
            dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)
      subgoal
        using S' propa_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
            dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)
      subgoal
        using struct S' by (auto simp: a S split: if_splits)[]
      subgoal
        using S' unit_clss by (auto 3 3 simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' w_q by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
            clauses_to_update_prop.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits
            dest: in_M_IN_QD)
      subgoal
        using S' past_invs by (auto simp: a S past_invs.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      done
  next
    case False note [simp] = this(1) and a = this(2)
    then have [simp]: \<open>length a \<noteq> Suc 0\<close> by auto
    then obtain x y a' where a: \<open>a = x # y # a'\<close>
      apply (case_tac a, (use False in simp; fail))
      apply (rename_tac aa list, case_tac list; simp)
      done
    have all_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init (twl_st_of_init (init_dt (a # CS) (S, OC))))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
      apply (intro conjI)
      subgoal
        using alien N_not_empty
        by (auto 3 3 simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: (* in_lits_of_l_defined_litD *)
            split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct dist N_not_empty by (auto simp: cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            convert_lits_l_append split: if_splits)
      subgoal
        using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def propagated_trail_decomp_iff
            Decided_Propagated_in_iff_in_lits_of_l
            split: if_splits)
      subgoal
        apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
        using all_decomp N_not_empty by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
            intro!: all_decomposition_implies_insert_single
            split: if_splits)
      subgoal
        using learned N_not_empty by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
            split: if_splits)
      done
    show ?thesis
      unfolding twl_struct_invs_init_def S' twl_st_inv.simps
      apply (intro conjI)
      subgoal
        using H S' dec struct N_not_empty dist by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            split: if_splits)
      subgoal
        using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if
            split: if_splits)
      subgoal using all_inv' .
      subgoal
        using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' excep in_M_IN_QD by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap add_mset_eq_add_mset
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            split: if_splits)
      subgoal
        using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' dist_q in_literals_to_update by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' confl_cands in_M_IN_QD N_not_empty by (force simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap ex_disj_distrib conj_disj_distribR
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)+
      subgoal
        using S' propa_cands in_M_IN_QD N_not_empty by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap ex_disj_distrib conj_disj_distribR
            all_conj_distrib cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            dest!: ex_two_watched_N split: if_splits)
      subgoal by (auto simp: S Let_def a split: if_splits)

      subgoal
        using S' unit_clss by (cases D) (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' w_q in_M_IN_QD by (cases D) (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
            clauses_to_update_prop.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            split: if_splits)
      subgoal
        apply (cases D)
        using S' past_invs by (auto simp: a S past_invs.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      done
  qed
  case 9
  show ?case
    unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
    by (cases D; cases a)
        (auto simp: S cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def
        cdcl\<^sub>W_restart_mset_state Let_def)

  case 10
  show ?case
    using OC'_empty
    by (cases D; cases a) (auto simp: S cdcl\<^sub>W_restart_mset_state Let_def)
  case 11
  show ?case
    using OC'_empty_conflict
    by (cases D; cases a) (auto simp: S cdcl\<^sub>W_restart_mset_state Let_def)
qed

lemma init_dt_full:
  fixes CS :: \<open>'v literal list list\<close> and SOC :: \<open>'v twl_st_l_init\<close> and S'
(*   defines \<open>SOC' \<equiv> init_dt CS (S, OC)\<close>
  defines \<open>S' \<equiv> fst (init_dt CS (S, OC))\<close>
  defines \<open>OC' \<equiv> snd (init_dt CS (S, OC))\<close> *)
  defines
    \<open>S \<equiv> fst SOC\<close> and
    \<open>OC \<equiv> snd SOC\<close>
  assumes
    \<open>init_dt_pre CS SOC\<close>
  shows
    \<open>init_dt CS SOC \<le> SPEC (init_dt_spec CS SOC)\<close>
(*     \<open>twl_struct_invs_init (twl_st_of_init SOC')\<close> and
    \<open>clauses_to_update_l S' = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l S'). \<not>is_decided s\<close> and
    \<open>get_conflict_l S' = None \<longrightarrow> literals_to_update_l S' = uminus `# lit_of `# mset (get_trail_l S')\<close> and
    \<open>mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None S)) + OC =
      cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None S')) + OC'\<close> and
    \<open>learned_clss (state\<^sub>W_of (twl_st_of None S')) = learned_clss (state\<^sub>W_of (twl_st_of None S))\<close> and
    \<open>twl_list_invs S'\<close> and
    \<open>get_learned_l S' = length (get_clauses_l S') - 1\<close> and
    \<open>twl_stgy_invs (twl_st_of None S')\<close> and
    \<open>OC' \<noteq> {#} \<longrightarrow> get_conflict_l S' \<noteq> None\<close> and
    \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l S' \<noteq> None\<close> *)
  using assms unfolding S_def OC_def
proof (induction CS arbitrary: SOC)
  case Nil
  then obtain S OC where SOC: \<open>SOC = (S, OC)\<close>
    by (cases SOC) auto
  from Nil
  obtain T where
    T: \<open>(SOC, T) \<in> twl_st_l_init\<close>
      \<open>Ball (set []) distinct\<close> 
      \<open>twl_struct_invs_init T\<close> 
      \<open>clauses_to_update_l (fst SOC) = {#}\<close> 
      \<open>\<forall>s\<in>set (get_trail_l (fst SOC)). \<not> is_decided s\<close> 
      \<open>get_conflict_l (fst SOC) = None \<longrightarrow>
       literals_to_update_l (fst SOC) =
       uminus `# lit_of `# mset (get_trail_l (fst SOC))\<close> 
      \<open>twl_list_invs (fst SOC)\<close> 
      \<open>twl_stgy_invs (fst T)\<close> 
      \<open>snd SOC \<noteq> {#} \<longrightarrow> get_conflict_l (fst SOC) \<noteq> None\<close>
    unfolding init_dt_pre_def apply -
    apply normalize_goal+
    by auto

  show ?case
    unfolding init_dt.simps SOC init_dt_spec_def
    apply (intro RETURN_rule)
    unfolding prod.simps
    apply (rule exI[of _ T])
    using T by (auto simp: SOC)
next
  case (Cons a CS) note IH = this(1) and pre = this(2)
  note init_dt_step_def[simp]
  have 1: \<open>init_dt_step a SOC \<le> SPEC (init_dt_pre CS)\<close> if  \<open>init_dt_pre (a # CS) SOC\<close>
    unfolding init_dt_pre_def
    apply (cases SOC)
    apply (auto)
    sorry
  show ?case
    unfolding init_dt.simps
    apply (rule specify_left)
     apply (rule 1)
    apply (rule order.trans)
     apply (rule IH)
    apply assumption
    thm IH


    oops


  case 1 then show ?case by simp
  case 2 then show ?case by simp
  case 3 then show ?case by simp
  case 4 then show ?case by simp
  case 5 then show ?case by (auto simp add: clauses_def)
  case 6 then show ?case by auto
  case 7 then show ?case by auto
  case 8 then show ?case by auto
  case 9 then show ?case by simp
  case 10 then show ?case by simp
  case 11 then show ?case by simp
next
  case (Cons a CS) note IH = this(1-)
  note init_dt_step_def[simp]
  case 2 note dist = this(1) and inv = this(2) and
    WS = this(3) and dec = this(4) and in_literals_to_update = this(5) and add_inv = this(6) and
    len = this(7) and stgy_inv = this(8) and OC'_empty = this(9)
  let ?SOC' = \<open>init_dt CS (S, OC)\<close>
  let ?S' = \<open>fst (init_dt CS (S, OC))\<close>
  let ?OC' = \<open>snd (init_dt CS (S, OC))\<close>
  have
    twl: \<open>twl_struct_invs_init (twl_st_of_init ?SOC')\<close> and
    w_q: \<open>clauses_to_update_l ?S' = {#}\<close> and
    dec': \<open>\<forall>s\<in>set (get_trail_l ?S'). \<not> is_decided s\<close> and
    literals_to_update': \<open>get_conflict_l ?S' = None \<longrightarrow>
        literals_to_update_l ?S' = uminus `# lit_of `# mset (get_trail_l ?S')\<close>
      and
    clss': \<open>mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None S)) + OC =
      cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None ?S')) + ?OC'\<close>
      and
    learned': \<open>learned_clss (state\<^sub>W_of (twl_st_of None ?S')) = learned_clss (state\<^sub>W_of (twl_st_of None S))\<close>
      and
    add_inv': \<open>twl_list_invs ?S'\<close> and
    U': \<open>get_learned_l ?S' = length (get_clauses_l ?S') - 1\<close> and
    OC'_empty: \<open>snd ?SOC' \<noteq> {#} \<longrightarrow> get_conflict_l ?S' \<noteq> None\<close>and
    OC'_empty_conflict: \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l ?S' \<noteq> None\<close>
    using IH[OF _ inv WS dec in_literals_to_update add_inv len stgy_inv OC'_empty] dist by auto

  obtain M N U D NE UE Q OCS where
    S: \<open>init_dt CS (S, OC) = ((M, N, U, D, NE, UE, {#}, Q), OCS)\<close>
    using w_q by (cases \<open>init_dt CS (S, OC)\<close>) auto
  obtain M' N' U' D' NE' WS' UE' Q' where
    S': \<open>twl_st_of None (fst (init_dt (a # CS) (S, OC))) = (M', N', U', D', NE', UE', WS', Q')\<close>
    by (cases \<open>twl_st_of None (fst (init_dt (a # CS) (S, OC)))\<close>) auto
  then have [simp]: \<open>UE' = UE\<close>
    by (cases a; cases D) (auto simp: S split: if_splits)

  have dec_M: \<open>\<forall>s\<in>set M. \<not> is_decided s\<close>
    using dec' S by auto
  have N_not_empty: \<open>N \<noteq> []\<close>
    using add_inv' unfolding twl_list_invs_def S by auto
  have U_len_N: \<open>U = length N - 1\<close>
    using U' unfolding S by auto
  then have [simp]: \<open>take U (tl N) = tl N\<close> \<open>drop (Suc U) N = []\<close> \<open>drop U (tl N) = []\<close>
    by auto
  show ?case using w_q
    by (cases D) (auto simp: S Let_def)
  case 3
  show ?case
    using dec_M by (cases D) (auto simp: S Let_def)
  case 4
  show ?case
    using literals_to_update' by (cases D) (auto simp: S Let_def)
  have a_D: \<open>\<exists>x y a'. a = x # y # a'\<close> if \<open>\<forall>L. a \<noteq> [L]\<close> and \<open>a \<noteq> []\<close>
    apply (case_tac a, (use that in simp; fail))
    apply (rename_tac aa list, case_tac list; use that in simp)
    done
  have mset_tl_N: \<open>{#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (take U (tl N))#} + {#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (drop (Suc U) N)#} =
         {#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (tl N)#}\<close>
    unfolding image_mset_union[symmetric] mset_append[symmetric] append_take_drop_id drop_Suc ..
  case 5
  show ?case
    using clss' U_len_N N_not_empty by (cases D)
      (auto simp: S Let_def clauses_def length_list_Suc_0 cdcl\<^sub>W_restart_mset_state mset_tl_N
        dest!: a_D)
  case 6
  show ?case
    using learned' U_len_N by (cases D) (auto simp: S Let_def clauses_def length_list_Suc_0
        cdcl\<^sub>W_restart_mset_state)

  case 7
  show ?case
    using add_inv' N_not_empty
    by (cases D) (fastforce simp add: U_len_N S clauses_def twl_list_invs_def Let_def nth_append
        cdcl\<^sub>W_restart_mset_state)+
  case 8
  show ?case
    by (cases D) (auto simp add: U_len_N S clauses_def twl_list_invs_def Let_def nth_append
        cdcl\<^sub>W_restart_mset_state)

  let ?S' = \<open>(convert_lits_l N M, twl_clause_of `# mset (take U (tl N)),
       twl_clause_of `# mset (drop U (tl N)), D, NE, UE, {#}, Q)\<close>
  case 1
  let ?S' = \<open>((convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), D, NE, UE, {#}, Q), OCS)\<close>
  let ?T' = \<open>state\<^sub>W_of_init ?S'\<close>
  have
    struct: \<open>Multiset.Ball (twl_clause_of `# mset (tl N)) struct_wf_twl_cls\<close> and
    H: \<open>\<forall>C\<in>#twl_clause_of `# mset (tl N). D = None \<longrightarrow>
      \<not> twl_is_an_exception C Q ({#} :: ('v literal \<times> 'v twl_cls) multiset ) \<longrightarrow>
      (twl_lazy_update (convert_lits_l N M) C \<and> twl_inv (convert_lits_l N M) C)\<close> and
    lev: \<open>\<forall>C\<in>#twl_clause_of `# mset (tl N). D = None \<longrightarrow> watched_literals_false_of_max_level (convert_lits_l N M) C\<close> and
    valid: \<open>valid_enqueued (fst ?S')\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ?T'\<close> and
    no_smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa ?T'\<close> and
    excep: \<open>twl_st_exception_inv (fst ?S')\<close> and
    no_dup: \<open>no_duplicate_queued (fst ?S')\<close> and
    dist_q: \<open>distinct_queued (fst ?S')\<close> and
    confl_cands: \<open>confl_cands_enqueued (fst ?S')\<close> and
    propa_cands: \<open>propa_cands_enqueued (fst ?S')\<close> and
    get_confl: \<open>get_conflict (fst ?S') \<noteq> None \<longrightarrow> clauses_to_update (fst ?S') = {#} \<and>
    literals_to_update (fst ?S') = {#}\<close> and
    unit_clss: \<open>entailed_clss_inv (fst ?S')\<close> and
    w_q: \<open>clauses_to_update_inv (fst ?S')\<close> and
    past_invs: \<open>past_invs (fst ?S')\<close>
    using twl unfolding twl_st_inv.simps twl_struct_invs_init_def S twl_st_of.simps
    image_mset_union[symmetric] mset_append[symmetric] append_take_drop_id drop_Suc S
    twl_struct_invs_def fst_conv twl_st_of_init.simps by fast+

  have [simp]: \<open>get_level M L = 0\<close> and
    [simp]: \<open>count_decided M = 0\<close> for L
    using dec' S by (auto simp: count_decided_0_iff)
  have nm: \<open>\<forall>s\<in>set (convert_lits_l N M). \<not> is_decided s\<close>
      using dec_M by (auto simp: convert_lits_l_def)
  have convert_append_Decided_cons[iff]:
    \<open>convert_lits_l N M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
    \<open>Propagated L C # convert_lits_l N M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
    for M'a K Ma L C
    using nm apply fastforce
    by (metis (no_types, lifting) nm annotated_lit.disc(1)
          annotated_lit.distinct(1) append_eq_Cons_conv in_set_conv_decomp list_tail_coinc)
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm ?T'\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ?T'\<close> and
    learned_tauto: \<open>(\<forall>s\<in>#learned_clss ?T'. \<not> tautology s)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state ?T'\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting ?T'\<close> and
    all_decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ?T')
     (get_all_ann_decomposition (trail ?T'))\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause ?T'\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
    by fast+
  have propagated_trail_decomp_iff[iff]: \<open>a @ Propagated La C # b = Propagated L D # M' \<longleftrightarrow>
        (a = [] \<and> Propagated La C = Propagated L D \<and> b = M') \<or>
        (a \<noteq> [] \<and> tl a @ Propagated La C # b = M' \<and> hd a = Propagated L D)\<close> for a b La L C D M'
    by (cases a) auto

  have ex_two_watched_N: \<open>\<exists>L L'. watched_l x = [L, L']\<close> if \<open>x \<in> set (tl N)\<close> for x
  proof -
    have \<open>struct_wf_twl_cls (twl_clause_of x)\<close>
      using struct that by auto
    then show ?thesis
      by (cases \<open>twl_clause_of x\<close>) (auto simp: length_list_2 take_2_if)
  qed

  have in_M_IN_QD: \<open>- La \<in> lits_of_l M \<Longrightarrow> La \<in># Q\<close> if \<open>D = None\<close> for La
    using S literals_to_update' that by (auto simp: lits_of_def uminus_lit_swap)

  have \<open>x \<in> set M \<Longrightarrow> convert_lit (N @ N') x = convert_lit N x\<close> for x N'
    using add_inv' by (cases x) (auto simp: nth_append twl_list_invs_def S)
  then have [simp]: \<open>convert_lits_l (N @ N') M = convert_lits_l N M\<close> for N'
    unfolding convert_lits_l_def by auto
  consider
    (confl) \<open>D \<noteq> None\<close> |
    (empty) \<open>D = None\<close> and \<open>a = []\<close> |
    (True) \<open>D = None\<close> and \<open>length a = 1\<close> |
    (False) \<open>D = None\<close> and \<open>length a \<ge> 2\<close>
    by (cases a; cases \<open>tl a\<close>) auto
  then show ?case
  proof cases
    case confl
    then show ?thesis
      using S' twl dist by (auto simp: S cdcl\<^sub>W_restart_mset_state
          intro!: twl_struct_invs_init_add_mset)
  next
    case a: empty
    have [simp]: \<open>NE' = NE\<close>
    using S' by (cases D) (auto simp: a S split: if_splits)
  note in_M_IN_QD = in_M_IN_QD[OF a(1)]
  have all_inv':
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_lits_l N M,
      add_mset {#}
       ({#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (tl N)#} + NE' + OCS),
      UE', Some {#})\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
    apply (intro conjI)
    subgoal
      using alien by (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def
          mset_take_mset_drop_mset atms_of_def
          dest: in_lits_of_l_defined_litD split: if_splits)
    subgoal
      using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
    subgoal
      using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
    subgoal
      using all_struct by (auto simp: cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          split: if_splits)
    subgoal
      using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def Decided_Propagated_in_iff_in_lits_of_l
          split: if_splits)
    subgoal
      apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
      using all_decomp by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
          intro!: all_decomposition_implies_insert_single
          split: if_splits)
    subgoal
      using learned by (auto 5 5 simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def image_Un
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
          split: if_splits)
    done
  show ?thesis
    unfolding twl_struct_invs_init_def S' twl_st_inv.simps
    apply (intro conjI)
    subgoal
      using H S' dec' nm struct by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
          split: if_splits)
    subgoal
      using struct S' by (auto simp: a S split: if_splits)[]
    subgoal using all_inv' by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
          split: if_splits)
    subgoal
      using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' excep by (force simp: a S twl_exception_inv.simps split: if_splits)
    subgoal
      using S' by (auto simp: a S split: if_splits)
    subgoal
      using S' excep by (force simp: a S twl_exception_inv.simps split: if_splits)
    subgoal
      using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' dist_q literals_to_update' by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' confl_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
          dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
          split: if_splits)
    subgoal
      using S' propa_cands unit_clss by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
          dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
          split: if_splits)
    subgoal
      using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
          twl_exception_inv.simps uminus_lit_swap
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    subgoal
      using S' past_invs by (auto simp: a S past_invs.simps
          cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
    done
  next
    case True note _[simp] = this(1) and a = this(2)
    then obtain L where a: \<open>a = [L]\<close>
      using list_decomp_1 by blast
    note in_M_IN_QD = in_M_IN_QD[OF True(1)]
    have all_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init (twl_st_of_init (init_dt (a # CS) (S, OC))))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
        init_dt.simps S
      apply (intro conjI)
      subgoal
        using alien by (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: in_lits_of_l_defined_litD split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            split: if_splits)
      subgoal
        using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def Decided_Propagated_in_iff_in_lits_of_l
            split: if_splits)
      subgoal
        apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
        using all_decomp by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
            intro!: all_decomposition_implies_insert_single
            split: if_splits)
      subgoal
        using learned by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
            split: if_splits)
      done
    show ?thesis
      unfolding twl_struct_invs_init_def S' twl_st_inv.simps
      apply (intro conjI)
      subgoal
        using H S' dec' nm struct by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            split: if_splits)
      subgoal
        using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if split: if_splits)
      subgoal using all_inv'
        using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' excep by (force simp: a S twl_exception_inv.simps split: if_splits)
      subgoal
        using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' dist_q literals_to_update' by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' confl_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
            dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)
      subgoal
        using S' propa_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def conj_disj_distribR ex_disj_distrib
            dest: in_diffD dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)
      subgoal
        using struct S' by (auto simp: a S split: if_splits)[]
      subgoal
        using S' unit_clss by (auto 3 3 simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' w_q by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
            clauses_to_update_prop.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits
            dest: in_M_IN_QD)
      subgoal
        using S' past_invs by (auto simp: a S past_invs.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      done
  next
    case False note [simp] = this(1) and a = this(2)
    then have [simp]: \<open>length a \<noteq> Suc 0\<close> by auto
    then obtain x y a' where a: \<open>a = x # y # a'\<close>
      apply (case_tac a, (use False in simp; fail))
      apply (rename_tac aa list, case_tac list; simp)
      done
    have all_inv':
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init (twl_st_of_init (init_dt (a # CS) (S, OC))))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
      apply (intro conjI)
      subgoal
        using alien N_not_empty
        by (auto 3 3 simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: (* in_lits_of_l_defined_litD *)
            split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
      subgoal
        using all_struct dist N_not_empty by (auto simp: cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            convert_lits_l_append split: if_splits)
      subgoal
        using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def propagated_trail_decomp_iff
            Decided_Propagated_in_iff_in_lits_of_l
            split: if_splits)
      subgoal
        apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
        using all_decomp N_not_empty by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
            intro!: all_decomposition_implies_insert_single
            split: if_splits)
      subgoal
        using learned N_not_empty by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
            split: if_splits)
      done
    show ?thesis
      unfolding twl_struct_invs_init_def S' twl_st_inv.simps
      apply (intro conjI)
      subgoal
        using H S' dec struct N_not_empty dist by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            split: if_splits)
      subgoal
        using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if
            split: if_splits)
      subgoal using all_inv' .
      subgoal
        using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' excep in_M_IN_QD by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap add_mset_eq_add_mset
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            split: if_splits)
      subgoal
        using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' dist_q in_literals_to_update by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' confl_cands in_M_IN_QD N_not_empty by (force simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap ex_disj_distrib conj_disj_distribR
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)+
      subgoal
        using S' propa_cands in_M_IN_QD N_not_empty by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap ex_disj_distrib conj_disj_distribR
            all_conj_distrib cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            dest!: ex_two_watched_N split: if_splits)
      subgoal by (auto simp: S Let_def a split: if_splits)

      subgoal
        using S' unit_clss by (cases D) (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        using S' w_q in_M_IN_QD by (cases D) (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
            clauses_to_update_prop.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            split: if_splits)
      subgoal
        apply (cases D)
        using S' past_invs by (auto simp: a S past_invs.simps
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      done
  qed
  case 9
  show ?case
    unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
       cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
    by (cases D; cases a)
        (auto simp: S cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def
        cdcl\<^sub>W_restart_mset_state Let_def)

  case 10
  show ?case
    using OC'_empty
    by (cases D; cases a) (auto simp: S cdcl\<^sub>W_restart_mset_state Let_def)
  case 11
  show ?case
    using OC'_empty_conflict
    by (cases D; cases a) (auto simp: S cdcl\<^sub>W_restart_mset_state Let_def)
qed

lemma clauses_init_dt_not_Nil: \<open>fst (snd (fst (init_dt CS (([], [[]], 0, None, {#}, {#}, {#}, {#}), OC)))) \<noteq> []\<close>
  apply (induction CS)
  subgoal by (auto simp: init_dt_step_def)
  subgoal for C CS
    by (cases \<open>init_dt CS (([], [[]], 0, None, {#}, {#}, {#}, {#}), OC)\<close>)
     (auto simp: init_dt_step_def Let_def split: option.splits if_splits)
  done

lemma init_dt_conflict_remains:
  fixes CS :: \<open>'v literal list list\<close> and S :: \<open>'v twl_st_l\<close> and OC :: \<open>'v clauses\<close>
  defines \<open>S' \<equiv> fst (init_dt CS (S, OC))\<close>
  shows \<open>get_conflict_l S \<noteq> None \<longrightarrow> get_conflict_l S = get_conflict_l S'\<close>
  unfolding S'_def apply (induction CS)
  subgoal by simp
  subgoal for a CS
    by (cases \<open>init_dt CS (S, OC)\<close>; cases \<open>get_conflict_l S\<close>)
      (auto simp: init_dt_step_def Let_def split: option.splits if_splits)
  done

lemma init_dt_confl_in_clauses:
  fixes CS :: \<open>'v literal list list\<close> and S :: \<open>'v twl_st_l\<close> and OC :: \<open>'v clauses\<close>
  defines \<open>S' \<equiv> fst (init_dt CS (S, OC))\<close>
  assumes
    \<open>get_conflict_l S \<noteq> None \<longrightarrow> the (get_conflict_l S) \<in># mset `# mset CS\<close>
  shows
    \<open>get_conflict_l S' \<noteq> None \<longrightarrow> the (get_conflict_l S') \<in># mset `# mset CS\<close>
  using assms(2-) unfolding S'_def apply (induction CS)
  subgoal by simp
  subgoal for a CS
    using init_dt_conflict_remains[of S CS OC]
    by (cases \<open>init_dt CS (S, OC)\<close>; cases \<open>get_conflict_l S\<close>)
      (auto simp: init_dt_step_def Let_def split: option.splits if_splits)
  done

lemma clauses_state\<^sub>W_of_init_clauses_state\<^sub>W_of:
  \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of_init (twl_st_of_init S)) =
    cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (fst S))) + snd S\<close>
  by (cases S)  (auto simp: clauses_def)

theorem init_dt:
  fixes CS S
  defines S: \<open>S \<equiv> (([], [[]], 0, None, {#}, {#}, {#}, {#}), {#})\<close>
  assumes
    \<open>\<forall>C \<in> set CS. distinct C\<close>
  shows
    \<open>twl_struct_invs_init (twl_st_of_init (init_dt CS S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (fst (init_dt CS S)))) + snd (init_dt CS S) =
         mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of None (fst (init_dt CS S)))\<close> and
    \<open>clauses_to_update_l (fst (init_dt CS S)) = {#}\<close> and
    \<open>twl_list_invs (fst (init_dt CS S))\<close> and
    \<open>get_conflict_l (fst (init_dt CS S)) \<noteq> None \<longrightarrow>
         the (get_conflict_l (fst (init_dt CS S))) \<in># mset `# mset CS\<close> and
   \<open>snd (init_dt CS S) \<noteq> {#} \<longrightarrow> get_conflict_l (fst (init_dt CS S)) \<noteq> None\<close> and
   \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l (fst (init_dt CS S)) \<noteq> None\<close>

proof -
  have [simp]: \<open>twl_struct_invs_init (twl_st_of_init S)\<close>
    unfolding S
    by (auto simp: twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps twl_struct_invs_init_def
        cdcl\<^sub>W_restart_mset_state)
  have [simp]: \<open>clauses_to_update_l (fst S) = {#}\<close>
    \<open>\<forall>s\<in>set (get_trail_l (fst S)). \<not> is_decided s\<close>
    \<open>get_conflict_l (fst S) = None \<longrightarrow>
        literals_to_update_l (fst S) = {#- lit_of x. x \<in># mset (get_trail_l (fst S))#}\<close>
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of_init (twl_st_of_init S)) = {#}\<close>
    unfolding S
    by (auto simp: twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def
        cdcl\<^sub>W_restart_mset_state)
  have [simp]: \<open>twl_list_invs (fst S)\<close>
    unfolding S by (auto simp: twl_list_invs_def)
  have [simp]: \<open>get_learned_l (fst S) = length (get_clauses_l (fst S)) - 1\<close>
    unfolding S by auto
  have [simp]: \<open>twl_stgy_invs (twl_st_of None (fst S))\<close>
    unfolding S by (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_smaller_confl_def
        cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  have [simp]: \<open>get_conflict_l (fst S) = None\<close>
    unfolding S by auto
  have [simp]: \<open>snd S = {#}\<close> \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (fst S))) = {#}\<close>
    unfolding S by (auto simp: clauses_def)
  have confl:
     \<open>(snd S \<noteq> {#} \<longrightarrow> get_conflict_l (fst S) \<noteq> None) = True\<close>
     \<open>snd S \<noteq> {#} \<longrightarrow> get_conflict_l (fst S) \<noteq> None\<close>
    by auto
  show
    \<open>twl_struct_invs_init (twl_st_of_init (init_dt CS S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (fst (init_dt CS S)))) + snd (init_dt CS S) =
      mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of None (fst (init_dt CS S)))\<close> and
    \<open>clauses_to_update_l (fst (init_dt CS S)) = {#}\<close> and
    \<open>twl_list_invs (fst (init_dt CS S))\<close> and
    \<open>get_conflict_l (fst (init_dt CS S)) \<noteq> None \<longrightarrow>
      the (get_conflict_l (fst (init_dt CS S))) \<in># mset `# mset CS\<close>
    using init_dt_full(1-9)[of CS \<open>fst S\<close> \<open>snd S\<close>, OF assms(2)]
    init_dt_confl_in_clauses[of \<open>fst S\<close> CS \<open>snd S\<close>] unfolding prod.collapse confl
    by (simp_all add: clauses_state\<^sub>W_of_init_clauses_state\<^sub>W_of)
  show \<open>snd (init_dt CS S) \<noteq> {#} \<longrightarrow> get_conflict_l (fst (init_dt CS S)) \<noteq> None\<close>
    by (rule init_dt_full(10)[of CS \<open>fst S\<close> \<open>snd S\<close>, OF assms(2),
      unfolded prod.collapse]) auto
  show \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l (fst (init_dt CS S)) \<noteq> None\<close>
    by (rule init_dt_full(11)[of CS \<open>fst S\<close> \<open>snd S\<close>, OF assms(2),
      unfolded prod.collapse]) auto
qed

end
