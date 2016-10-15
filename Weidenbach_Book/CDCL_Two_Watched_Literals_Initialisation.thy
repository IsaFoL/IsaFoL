theory CDCL_Two_Watched_Literals_Initialisation
  imports CDCL_Two_Watched_Literals_Simple_Implementation_List_Refinement
begin

subsection \<open>Initialise Data structure\<close>

fun init_dt :: \<open>'v literal list list \<Rightarrow> 'v twl_st_list \<Rightarrow> 'v twl_st_list\<close> where
  \<open>init_dt [] S = S\<close>
| \<open>init_dt (C # CS) (M, N, U, None, NP, UP, WS, Q) =
  (if length C = 1
  then
    let L = hd C in
    if undefined_lit M L
    then (Propagated L C # M, N, U, None, add_mset {#L#} NP, UP, WS, add_mset (-L) Q)
    else if L \<in> lits_of_l M
    then (M, N, U, None, add_mset {#L#} NP, UP, WS, Q)
    else (M, N, U, Some C, add_mset {#L#} NP, UP, {#}, {#})
  else
    let L = hd C; L' = hd (tl C); C' = tl (tl C) in
    (M, add_mset (TWL_Clause [L, L'] C') N, U, None, NP, UP, WS, Q))\<close>
| \<open>init_dt (C # CS) (M, N, U, Some D, NP, UP, WS, Q) =
  (if length C = 1
  then
    let L = hd C in
    (M, N, U, Some D, add_mset {#L#} NP, UP, {#}, {#})
  else
    let L = hd C; L' = hd (tl C); C' = tl (tl C) in
    (M, add_mset (TWL_Clause [L, L'] C') N, U, Some D, NP, UP, {#}, {#}))\<close>

lemma twl_clause_of_def:
  \<open>twl_clause_of C = TWL_Clause (mset (watched C)) (mset (unwatched C))\<close>
  by (cases C) auto

(* TODO Move *)
lemma tautology_single[simp]: \<open>\<not>tautology {#L#}\<close>
  by (simp add: tautology_add_mset)
(* END Move *)

lemma
  fixes CS S
  defines \<open>S' \<equiv> init_dt CS S\<close>
  assumes
    \<open>\<forall>C \<in> set CS. distinct C\<close> and
    \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    \<open>twl_struct_invs (twl_st_of S)\<close> and
    \<open>working_queue_list S = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_list S). \<not>is_decided s\<close> and
    \<open>\<And>L. get_conflict_list S = None \<longrightarrow> pending_list S = uminus `# lit_of `# mset (get_trail_list S)\<close>
  shows
    \<open>twl_struct_invs (twl_st_of S')\<close> and
    \<open>working_queue_list S' = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_list S'). \<not>is_decided s\<close> and
    \<open>get_conflict_list S' = None \<longrightarrow> pending_list S' = uminus `# lit_of `# mset (get_trail_list S')\<close>
  using assms unfolding S'_def
proof (induction CS)
  case Nil
  case 1 then show ?case by simp
  case 2 then show ?case by simp
  case 3 then show ?case by simp
  case 4 then show ?case by simp
next
  case (Cons a CS) note IH = this(1-4)

  case 2 note dist = this(1) and length  = this(2) and inv = this(3) and
    WS = this(4) and dec = this(5) and in_pending = this(6)

  have
    twl: \<open>twl_struct_invs (twl_st_of (init_dt CS S))\<close> and
    w_q: \<open>working_queue_list (init_dt CS S) = {#}\<close> and
    dec': \<open>\<forall>s\<in>set (get_trail_list (init_dt CS S)). \<not> is_decided s\<close> and
    pending': \<open>get_conflict_list (init_dt CS S) = None \<longrightarrow> pending_list (init_dt CS S) = uminus `# lit_of `# mset (get_trail_list (init_dt CS S))\<close>
    using IH[OF _ _ inv WS dec in_pending] dist length by auto

  obtain M N U D NP UP Q where
    S: \<open>S = (M, N, U, D, NP, UP, {#}, Q)\<close>
    using WS by (cases S) auto
  obtain M' N' U' D' NP' WS' UP' Q' where
    S': \<open>twl_st_of (init_dt (a # CS) S) = (M', N', U', D', NP', UP', WS', Q')\<close>
    by (cases \<open>twl_st_of (init_dt (a # CS) S)\<close>) auto
  have dec_M: \<open>\<forall>s\<in>set M. \<not> is_decided s\<close>
    using dec S by auto

  show ?case
    by (cases D) (auto simp: S Let_def)
  case 3
  show ?case
    using dec_M by (cases D) (auto simp: S Let_def)
  case 4
  show ?case
    using in_pending by (cases D) (auto simp: S Let_def)

  case 1
  have
    struct: \<open>Multiset.Ball (twl_clause_of `# N + twl_clause_of `# U) struct_wf_twl_cls\<close> and
    H:\<open>(\<forall>C\<in>#twl_clause_of `# N + twl_clause_of `# U.
      map_option mset D = None \<longrightarrow>
      \<not> twl_is_an_exception C Q {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#} \<longrightarrow>
      twl_lazy_update (convert_lits M) C \<and>
      twl_inv (convert_lits M) C)\<close> and
    lev: \<open>\<forall>C\<in>#twl_clause_of `# N + twl_clause_of `# U.
      map_option mset D = None \<longrightarrow>
      watched_literals_false_of_max_level (convert_lits M) C\<close> and
    valid: \<open>valid_annotation (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state
       (convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close> and
    no_taut: \<open>(\<forall>D\<in>#init_clss (convert_to_state (convert_lits M, twl_clause_of `# N,
            twl_clause_of `# U, map_option mset D, NP, UP,
            {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)).
      \<not> tautology D)\<close> and
    no_smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa
     (convert_to_state (convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D,
       NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close> and
    excep: \<open>twl_st_exception_inv (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
    no_dup: \<open>no_duplicate_queued (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
    dist_q: \<open>distinct_queued (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
    confl_cand: \<open>confl_cands_enqueued (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
    propa_cands: \<open>propa_cands_enqueued (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
    get_confl: \<open>get_conflict (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
      map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q) \<noteq> None \<longrightarrow>
      working_queue (convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D, NP,
      UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q) = {#} \<and>
      pending (convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D, NP, UP,
       {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q) = {#}\<close> and
   unit_clss: \<open>unit_clss_inv (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
     map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
   w_q: \<open>working_queue_inv (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
     map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close> and
   past_invs: \<open>past_invs (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
     map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)\<close>
    using inv unfolding twl_st_inv.simps twl_struct_invs_def S twl_st_of.simps
    by (auto simp: twl_struct_invs_def S
        simp del: valid_annotation.simps
        twl_st_exception_inv.simps no_duplicate_queued.simps distinct_queued.simps
        confl_cands_enqueued.simps propa_cands_enqueued.simps unit_clss_inv.simps
        working_queue_inv.simps past_invs.simps)
  have [simp]: \<open>get_level M L = 0\<close> and
    [simp]: \<open>count_decided M = 0\<close> for L
    using dec S by (auto simp: count_decided_0_iff)
  have convert_append_Decided_cons[iff]:
    \<open>convert_lits M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
    \<open>Propagated L C # convert_lits M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
    for M'a K Ma L C
  proof -
    have \<open>\<forall>s\<in>set (convert_lits M). \<not> is_decided s\<close>
      using dec_M by auto
    then show
      \<open>convert_lits M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
      \<open>Propagated L C # convert_lits M = M'a @ Decided K # Ma \<longleftrightarrow> False\<close>
       apply fastforce
      by (metis (no_types, lifting) \<open>\<forall>s\<in>set (convert_lits M). \<not> is_decided s\<close> ann_lit.disc(1)
          ann_lit.distinct(1) append_eq_Cons_conv in_set_conv_decomp list_tail_coinc)
  qed
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state (convert_lits M, twl_clause_of `# N,
        twl_clause_of `# U, map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (convert_to_state (convert_lits M, twl_clause_of `# N,
        twl_clause_of `# U, map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close> and
    learned_tauto: \<open>(\<forall>s\<in>#learned_clss (convert_to_state (convert_lits M, twl_clause_of `# N, twl_clause_of `# U,
        map_option mset D, NP, UP, {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)).
        \<not> tautology s)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state (convert_lits M, twl_clause_of `# N,
        twl_clause_of `# U, map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (convert_to_state (convert_lits M, twl_clause_of `# N,
        twl_clause_of `# U, map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close> and
    all_decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (convert_to_state
         (convert_lits M, twl_clause_of `# N,
          twl_clause_of `# U, map_option mset D, NP, UP,
          {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q)))
     (get_all_ann_decomposition (trail (convert_to_state (convert_lits M, twl_clause_of `# N,
            twl_clause_of `# U, map_option mset D, NP, UP,
            {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))))\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (convert_to_state (convert_lits M, twl_clause_of `# N,
        twl_clause_of `# U, map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a, b) \<in># {#}#}, Q))\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
    by fast+
  have propagated_trail_decomp_iff: \<open>a @ Propagated La C # b = Propagated L D # M' \<longleftrightarrow>
        (a = [] \<and> Propagated La C = Propagated L D \<and> b = M') \<or>
        (a \<noteq> [] \<and> tl a @ Propagated La C # b = M' \<and> hd a = Propagated L D)\<close> for a b La L C D M'
    by (cases a) auto
  show ?case
  proof (cases \<open>length a = 1\<close>)
    case True
    then obtain L where a: \<open>a = [L]\<close>
      using list_decomp_1 by blast
    show ?thesis
    proof (cases D)
      case [simp]: None
      have in_M_IN_QD: \<open>- La \<in> lits_of_l M \<Longrightarrow> La \<in># Q\<close> for La
        using S in_pending by (auto simp: lits_of_def uminus_lit_swap)

      have all_inv':
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (M', N', U', D', NP', UP', WS', Q'))\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
        apply (intro conjI)
        subgoal
          using alien apply (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: in_lits_of_l_defined_litD split: if_splits)
          done
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
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def propagated_trail_decomp_iff
              Decided_Propagated_in_iff_in_lits_of_l
              split: if_splits)
        subgoal
          apply (cases \<open>get_all_ann_decomposition (convert_lits M)\<close>)
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
        unfolding twl_struct_invs_def S' twl_st_inv.simps
        apply (intro conjI)
        subgoal
          using struct S' by (auto simp: a S split: if_splits)[]
        subgoal
          using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_clause_of_def twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_clause_of_def twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_clause_of_def get_level_cons_if
              split: if_splits)
        subgoal using all_inv' .
        subgoal
          using S' no_taut by (auto simp: a S cdcl\<^sub>W_restart_mset_state split: if_splits)
        subgoal
          using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' excep by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def dest: in_M_IN_QD split: if_splits)
        subgoal
          using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' dist_q in_pending by (auto simp add: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' confl_cand apply (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap true_annots_true_cls_def_iff_negation_in_model
            Ball_def
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
          sorry
        subgoal
          using S' propa_cands apply (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
          sorry
        subgoal
          using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal (* TODO Proof *)
          using S' unit_clss apply (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
              twl_exception_inv.simps uminus_lit_swap get_level_cons_if
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
             apply blast+
          done
        subgoal (* TODO Proof *)
          using S' w_q by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
              twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
              working_queue_prop.simps
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits
              dest: in_M_IN_QD)
        subgoal
          using S' past_invs by (auto simp: a S past_invs.simps
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        done
    next
      case (Some D'') note [simp] = this
      have all_inv':
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (M', N', U', D', NP', UP', WS', Q'))\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
        apply (intro conjI)
        subgoal (* TODO proof *)
          using alien by (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: in_lits_of_l_defined_litD split: if_splits)
           blast
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
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def propagated_trail_decomp_iff
              Decided_Propagated_in_iff_in_lits_of_l
              split: if_splits)
        subgoal
          apply (cases \<open>get_all_ann_decomposition (convert_lits M)\<close>)
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
        unfolding twl_struct_invs_def S' twl_st_inv.simps
        apply (intro conjI)
        subgoal
          using struct S' by (auto simp: a S split: if_splits)[]
        subgoal
          using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_clause_of_def twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_clause_of_def twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_clause_of_def get_level_cons_if
              split: if_splits)
        subgoal using all_inv' .
        subgoal
          using S' no_taut by (auto simp: a S cdcl\<^sub>W_restart_mset_state split: if_splits)
        subgoal
          using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' excep by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' dist_q in_pending by (auto simp add: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' confl_cand by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' propa_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal (* TODO Proof *)
          using S' unit_clss by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
              twl_exception_inv.simps uminus_lit_swap get_level_cons_if
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal (* TODO Proof *)
          using S' w_q by (auto simp: a S cdcl\<^sub>W_restart_mset_state twl_clause_of_def
              twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
              working_queue_prop.simps
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' past_invs by (auto simp: a S past_invs.simps
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        done
    qed
  next
    case False
    then have [simp]: \<open>length a \<noteq> Suc 0\<close> by auto
    show ?thesis
      apply (cases D)
      using S' apply (auto simp: S Let_def split: if_splits)
  oops
end