theory CDCL_Two_Watched_Literals_Initialisation
  imports CDCL_Two_Watched_Literals_List
begin

subsection \<open>Initialise Data structure\<close>

definition init_dt_step :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>init_dt_step C S =
  (let (M, N, U, D, NP, UP, WS, Q) = S in
  (case D of
    None \<Rightarrow>
    if length C = 1
    then
      let L = hd C in
      if undefined_lit M L
      then (Propagated L 0 # M, N, U, None, add_mset {#L#} NP, UP, WS, add_mset (-L) Q)
      else if L \<in> lits_of_l M
      then (M, N, U, None, add_mset {#L#} NP, UP, WS, Q)
      else (M, N, U, Some C, add_mset {#L#} NP, UP, {#}, {#})
    else
      let L = hd C; L' = hd (tl C); C' = tl (tl C) in
      (M, N @ [[L, L'] @ C'], length N, None, NP, UP, WS, Q)
  | Some D \<Rightarrow>
    if length C = 1
    then
      let L = hd C in
      (M, N, U, Some D, add_mset {#L#} NP, UP, {#}, {#})
    else
      let L = hd C; L' = hd (tl C); C' = tl (tl C) in
      (M, N @ [[L, L'] @ C'], length N, Some D, NP, UP, {#}, {#})))\<close>

fun init_dt :: \<open>'v clauses_l \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>init_dt [] S = S\<close>
| \<open>init_dt (C # CS) S = init_dt_step C (init_dt CS S)\<close>

lemma init_dt_full:
  fixes CS :: \<open>'v literal list list\<close> and S :: \<open>'v twl_st_l\<close>
  defines \<open>S' \<equiv> init_dt CS S\<close>
  assumes
    \<open>\<forall>C \<in> set CS. distinct C\<close> and
    \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    \<open>\<forall>C \<in> set CS. \<not>tautology (mset C)\<close> and
    \<open>twl_struct_invs (twl_st_of None S)\<close> and
    \<open>working_queue_l S = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l S). \<not>is_decided s\<close> and
    \<open>\<And>L. get_conflict_l S = None \<longrightarrow> pending_l S = uminus `# lit_of `# mset (get_trail_l S)\<close> and
    \<open>additional_WS_invs S\<close> and
    \<open>get_learned_l S = length (get_clauses_l S) - 1\<close>and
    \<open>twl_stgy_invs (twl_st_of None S)\<close>
  shows
    \<open>twl_struct_invs (twl_st_of None S')\<close> and
    \<open>working_queue_l S' = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l S'). \<not>is_decided s\<close> and
    \<open>get_conflict_l S' = None \<longrightarrow> pending_l S' = uminus `# lit_of `# mset (get_trail_l S')\<close> and
    \<open>mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None S)) =
      cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None S'))\<close> and
    \<open>learned_clss (convert_to_state (twl_st_of None S')) = learned_clss (convert_to_state (twl_st_of None S))\<close> and
    \<open>additional_WS_invs S'\<close> and
    \<open>get_learned_l S' = length (get_clauses_l S') - 1\<close> and
    \<open>twl_stgy_invs (twl_st_of None S')\<close>
  using assms unfolding S'_def
proof (induction CS)
  case Nil
  case 1 then show ?case by simp
  case 2 then show ?case by simp
  case 3 then show ?case by simp
  case 4 then show ?case by simp
  case 5 then show ?case by (auto simp add: clauses_def)
  case 6 then show ?case by auto
  case 7 then show ?case by auto
  case 8 then show ?case by auto
  case 9 then show ?case by simp
next
  case (Cons a CS) note IH = this(1-)
  note init_dt_step_def[simp]
  case 2 note dist = this(1) and length = this(2) and no_taut_Cs = this(3) and inv = this(4) and
    WS = this(5) and dec = this(6) and in_pending = this(7) and add_inv = this(8) and len = this(9)
    and stgy_inv = this(10)

  have
    twl: \<open>twl_struct_invs (twl_st_of None (init_dt CS S))\<close> and
    w_q: \<open>working_queue_l (init_dt CS S) = {#}\<close> and
    dec': \<open>\<forall>s\<in>set (get_trail_l (init_dt CS S)). \<not> is_decided s\<close> and
    pending': \<open>get_conflict_l (init_dt CS S) = None \<longrightarrow> pending_l (init_dt CS S) = uminus `# lit_of `# mset (get_trail_l (init_dt CS S))\<close>
      and
    clss': \<open>mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None S)) =
      cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (init_dt CS S)))\<close>
      and
    learned': \<open>learned_clss (convert_to_state (twl_st_of None (init_dt CS S))) = learned_clss (convert_to_state (twl_st_of None S))\<close>
      and
    add_inv': \<open>additional_WS_invs (init_dt CS S)\<close> and
    U': \<open>get_learned_l (init_dt CS S) = length (get_clauses_l (init_dt CS S)) - 1\<close>
    using IH[OF _ _ _inv WS dec in_pending add_inv len stgy_inv] dist length no_taut_Cs by auto

  obtain M N U D NP UP Q where
    S: \<open>init_dt CS S = (M, N, U, D, NP, UP, {#}, Q)\<close>
    using w_q by (cases \<open>init_dt CS S\<close>) auto
  obtain M' N' U' D' NP' WS' UP' Q' where
    S': \<open>twl_st_of None (init_dt (a # CS) S) = (M', N', U', D', NP', UP', WS', Q')\<close>
    by (cases \<open>twl_st_of None (init_dt (a # CS) S)\<close>) auto
  have dec_M: \<open>\<forall>s\<in>set M. \<not> is_decided s\<close>
    using dec' S by auto
  have N_not_empty: \<open>N \<noteq> []\<close>
    using add_inv' unfolding additional_WS_invs_def S by auto
  have U_len_N: \<open>U = length N - 1\<close>
    using U' unfolding S by auto
  then have [simp]: \<open>take U (tl N) = tl N\<close> \<open>drop (Suc U) N = []\<close> \<open>drop U (tl N) = []\<close>
    by auto
  show ?case using w_q
    by (cases D) (auto simp: S Let_def init_dt_step_def)
  case 3
  show ?case
    using dec_M by (cases D) (auto simp: S Let_def init_dt_step_def)
  case 4
  show ?case
    using pending' by (cases D) (auto simp: S Let_def init_dt_step_def)
  have a_D: \<open>\<exists>x y a'. a = x # y # a'\<close> if \<open>\<forall>L. a \<noteq> [L]\<close>
    apply (case_tac a, (use length in simp; fail))
    apply (rename_tac aa list, case_tac list; use that in simp)
    done
  have mset_tl_N: \<open>{#mset (take 2 x) + mset (drop 2 x). x \<in># mset (take U (tl N))#} + {#mset (take 2 x) + mset (drop 2 x). x \<in># mset (drop (Suc U) N)#} =
         {#mset (take 2 x) + mset (drop 2 x). x \<in># mset (tl N)#}\<close>
    unfolding image_mset_union[symmetric] mset_append[symmetric] append_take_drop_id drop_Suc ..
  case 5
  show ?case
    using clss' U_len_N N_not_empty by (cases D)
      (auto simp: S Let_def clauses_def length_list_Suc_0 cdcl\<^sub>W_restart_mset_state mset_tl_N
          init_dt_step_def
        dest!: a_D)
  case 6
  show ?case
    using learned' U_len_N apply (cases D)
     apply (simp add: S clauses_def)
    apply (auto simp: S Let_def clauses_def length_list_Suc_0 cdcl\<^sub>W_restart_mset_state init_dt_step_def)
    done

  case 7
  show ?case
    using add_inv' N_not_empty
    by (cases D) (fastforce simp add: U_len_N S clauses_def additional_WS_invs_def Let_def nth_append
        cdcl\<^sub>W_restart_mset_state init_dt_step_def)+
  case 8
  show ?case
    by (cases D) (auto simp add: U_len_N S clauses_def additional_WS_invs_def Let_def nth_append
        cdcl\<^sub>W_restart_mset_state init_dt_step_def)

  let ?S' = \<open>(convert_lits_l N M, twl_clause_of `# mset (take U (tl N)),
       twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP,
             {#}, Q)\<close>
  case 1
  have
    struct: \<open>Multiset.Ball (twl_clause_of `# mset (tl N)) struct_wf_twl_cls\<close> and
    H: \<open>\<forall>C\<in>#twl_clause_of `# mset (tl N). map_option mset D = None \<longrightarrow>
      \<not> twl_is_an_exception C Q ({#} :: ('v literal \<times> 'v twl_cls) multiset ) \<longrightarrow>
      (twl_lazy_update (convert_lits_l N M) C \<and> twl_inv (convert_lits_l N M) C)\<close> and
    lev: \<open>\<forall>C\<in>#twl_clause_of `# mset (tl N). map_option mset D = None \<longrightarrow> watched_literals_false_of_max_level (convert_lits_l N M) C\<close> and
    valid: \<open>valid_annotation (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
      Q) \<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state
     (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
      Q))\<close> and
    no_taut: \<open>\<forall>D\<in>#init_clss (convert_to_state
                    (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP,
                     {#}, Q)).
      \<not> tautology D\<close> and
    no_smaller: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (convert_to_state
     (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
      Q))\<close> and
    excep: \<open>twl_st_exception_inv (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)),
      twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    no_dup: \<open>no_duplicate_queued (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    dist_q: \<open>distinct_queued (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    confl_cands: \<open>confl_cands_enqueued (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    propa_cands: \<open>propa_cands_enqueued (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    get_confl: \<open>get_conflict (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
     Q) \<noteq> None \<longrightarrow> working_queue (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
     Q) = {#} \<and>
    pending (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP,
            {#}, Q) = {#}\<close> and
    unit_clss: \<open>unit_clss_inv (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    w_q: \<open>working_queue_inv (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP, {#},
    Q)\<close> and
    past_invs: \<open>past_invs (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), map_option mset D, NP, UP,
             {#}, Q)\<close>
    using twl unfolding twl_st_inv.simps twl_struct_invs_def S twl_st_of.simps
    image_mset_union[symmetric] mset_append[symmetric] append_take_drop_id drop_Suc S
    twl_struct_invs_def by fast+

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
    by (metis (no_types, lifting) nm ann_lit.disc(1)
          ann_lit.distinct(1) append_eq_Cons_conv in_set_conv_decomp list_tail_coinc)
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state ?S')\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (convert_to_state ?S')\<close> and
    learned_tauto: \<open>(\<forall>s\<in>#learned_clss (convert_to_state ?S').
        \<not> tautology s)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state ?S')\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (convert_to_state ?S')\<close> and
    all_decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (convert_to_state ?S'))
     (get_all_ann_decomposition (trail (convert_to_state ?S')))\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (convert_to_state ?S')\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
    by fast+
  have propagated_trail_decomp_iff: \<open>a @ Propagated La C # b = Propagated L D # M' \<longleftrightarrow>
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
    using S pending' that by (auto simp: lits_of_def uminus_lit_swap)

  have \<open>x \<in> set M \<Longrightarrow> convert_lit (N @ N') x = convert_lit N x\<close> for x N'
    using add_inv' by (cases x) (auto simp: nth_append additional_WS_invs_def S)
  then have [simp]: \<open>convert_lits_l (N @ N') M =  convert_lits_l N M\<close> for N'
    unfolding convert_lits_l_def by auto

  show ?case
  proof (cases \<open>length a = 1\<close>)
    case True
    then obtain L where a: \<open>a = [L]\<close>
      using list_decomp_1 by blast
    show ?thesis
    proof (cases D)
      case [simp]: None
      note in_M_IN_QD = in_M_IN_QD[OF this]
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
        unfolding twl_struct_invs_def S' twl_st_inv.simps
        apply (intro conjI)
        subgoal
          using struct S' by (auto simp: a S split: if_splits)[]
        subgoal
          using H S' dec' nm by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' dec' nm by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if
              split: if_splits)
        subgoal using all_inv' .
        subgoal
          using S' no_taut by (auto simp: a S cdcl\<^sub>W_restart_mset_state split: if_splits)
        subgoal
          using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' excep by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def dest: in_M_IN_QD split: if_splits)
        subgoal
          using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' dist_q pending' by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
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
          using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal (* TODO Proof *)
          using S' unit_clss apply (auto simp: a S cdcl\<^sub>W_restart_mset_state
              twl_exception_inv.simps uminus_lit_swap get_level_cons_if
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
             apply blast+
          done
        subgoal
          using S' w_q by (auto simp: a S cdcl\<^sub>W_restart_mset_state
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
        unfolding twl_struct_invs_def S' twl_st_inv.simps
        apply (intro conjI)
        subgoal
          using struct S' by (auto simp: a S split: if_splits)[]
        subgoal
          using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
          propa_cands_enqueued.simps
          valid_annotation.simps
              split: if_splits)
        subgoal
          using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if
              split: if_splits)
        subgoal using all_inv' .
        subgoal
          using S' no_taut by (auto simp: a S cdcl\<^sub>W_restart_mset_state split: if_splits)
        subgoal
          using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' excep by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' dist_q in_pending by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' confl_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' propa_cands by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' unit_clss by (auto simp: a S cdcl\<^sub>W_restart_mset_state
              twl_exception_inv.simps uminus_lit_swap get_level_cons_if
              cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
        subgoal
          using S' w_q by (auto simp: a S cdcl\<^sub>W_restart_mset_state
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
    then obtain x y a' where a: \<open>a = x # y # a'\<close>
      apply (case_tac a, (use length in simp; fail))
      apply (rename_tac aa list, case_tac list; simp)
      done
      have all_inv':
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (M', N', U', D', NP', UP', WS', Q'))\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S'[symmetric]
        apply (intro conjI)
        subgoal (* TODO proof *)
          apply (cases D)
          using alien N_not_empty
            by (auto simp: a S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def Let_def dest: in_lits_of_l_defined_litD split: if_splits)
           blast
        subgoal
          apply (cases D)
          using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
        subgoal
          apply (cases D)
          using all_struct by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def split: if_splits)
        subgoal
          apply (cases D)
          using all_struct dist N_not_empty by (auto simp: cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def a S Let_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
              convert_lits_l_append split: if_splits)
        subgoal
          apply (cases D)
          using confl by (auto simp: a cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def propagated_trail_decomp_iff
              Decided_Propagated_in_iff_in_lits_of_l
              split: if_splits)
        subgoal
          apply (cases D)
          apply (cases \<open>get_all_ann_decomposition (convert_lits_l N M)\<close>)
          using all_decomp N_not_empty by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def clauses_def
              intro!: all_decomposition_implies_insert_single
              split: if_splits)
        subgoal
          apply (cases D)
          using learned N_not_empty by (auto simp: a cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S Let_def convert_lits_l_append
              cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def clauses_def
              split: if_splits)
        done
    show ?thesis
      unfolding twl_struct_invs_def S' twl_st_inv.simps
      apply (intro conjI)
      subgoal
        apply (cases D)
        using S' dist struct N_not_empty apply (auto simp: S Let_def a split: if_splits)
        done
      subgoal
        apply (cases D)
        using H S' dec apply (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
            propa_cands_enqueued.simps
            valid_annotation.simps
            split: if_splits)
        done
      subgoal
        apply (cases D)
        using H S' dec by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            twl_lazy_update.simps twl_st_exception_inv.simps
            watched_literals_false_of_max_level.simps
            propa_cands_enqueued.simps
            valid_annotation.simps
            split: if_splits)
      subgoal
        apply (cases D)
        using H S' valid by (auto simp: twl_struct_invs_def a S twl_st_inv.simps
            get_level_cons_if
            split: if_splits)
      subgoal using all_inv' .
      subgoal
        apply (cases D)
        using S' no_taut no_taut_Cs N_not_empty by (auto simp: a S cdcl\<^sub>W_restart_mset_state split: if_splits)
      subgoal
        apply (cases D)
        using S' no_smaller by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        apply (cases D)
        using S' excep in_M_IN_QD by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap add_mset_eq_add_mset
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            split: if_splits)
      subgoal
        apply (cases D)
        using S' no_dup by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        apply (cases D)
        using S' dist_q in_pending by (auto simp add: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps Decided_Propagated_in_iff_in_lits_of_l lits_of_def
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal
        apply (cases D)
        using S' confl_cands in_M_IN_QD N_not_empty by (force simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap ex_disj_distrib conj_disj_distribR
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            dest!: in_M_IN_QD dest!: ex_two_watched_N
            split: if_splits)+
      subgoal
        apply (cases D)
        using S' propa_cands in_M_IN_QD N_not_empty by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap ex_disj_distrib conj_disj_distribR
            all_conj_distrib cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def
            dest!: ex_two_watched_N split: if_splits)
      subgoal
        apply (cases D)
        using S' by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal (* TODO Proof *)
        apply (cases D)
        using S' unit_clss by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if
            cdcl\<^sub>W_restart_mset.no_smaller_propa_def clauses_def split: if_splits)
      subgoal (* TODO Proof *)
        apply (cases D)
        using S' w_q in_M_IN_QD by (auto simp: a S cdcl\<^sub>W_restart_mset_state
            twl_exception_inv.simps uminus_lit_swap get_level_cons_if filter_mset_empty_conv
            working_queue_prop.simps
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
    by (cases D; cases a) (auto simp: S cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def cdcl\<^sub>W_restart_mset_state
        Let_def)
qed

lemma clauses_init_dt_not_Nil: \<open>fst (snd (init_dt CS ([], [[]], 0, None, {#}, {#}, {#}, {#}))) \<noteq> []\<close>
  apply (induction CS)
  subgoal by (auto simp: init_dt_step_def)
  subgoal for C CS
    by (cases \<open>init_dt CS ([], [[]], 0, None, {#}, {#}, {#}, {#})\<close>)
     (auto simp: init_dt_step_def Let_def split: option.splits if_splits)
  done

theorem init_dt:
  fixes CS S
  defines S: \<open>S \<equiv> ([], [[]], 0, None, {#}, {#}, {#}, {#})\<close>
  assumes
    \<open>\<forall>C \<in> set CS. distinct C\<close> and
    \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    \<open>\<forall>C \<in> set CS. \<not>tautology (mset C)\<close>
  shows
    \<open>twl_struct_invs (twl_st_of None (init_dt CS S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (init_dt CS S))) = mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of None (init_dt CS S))\<close> and
    \<open>working_queue_l (init_dt CS S) = {#}\<close> and
    \<open>additional_WS_invs (init_dt CS S)\<close>
proof -
  have [simp]: \<open>twl_struct_invs (twl_st_of None S)\<close>
    unfolding S
    by (auto simp: twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps
        cdcl\<^sub>W_restart_mset_state)
  have [simp]: \<open>working_queue_l S = {#}\<close>
    \<open>\<forall>s\<in>set (get_trail_l S). \<not> is_decided s\<close>
    \<open>get_conflict_l S = None \<longrightarrow> pending_l S = {#- lit_of x. x \<in># mset (get_trail_l S)#}\<close>
    \<open>cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None S)) = {#}\<close>
    unfolding S
    by (auto simp: twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def
        cdcl\<^sub>W_restart_mset_state)
  have [simp]: \<open>additional_WS_invs S\<close>
    unfolding S by (auto simp: additional_WS_invs_def)
  have [simp]: \<open>get_learned_l S = length (get_clauses_l S) - 1\<close>
    unfolding S by auto
  have [simp]: \<open>twl_stgy_invs (twl_st_of None S)\<close>
    unfolding S by (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_smaller_confl_def)
  show
    \<open>twl_struct_invs (twl_st_of None (init_dt CS S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (init_dt CS S))) = mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of None (init_dt CS S))\<close> and
    \<open>working_queue_l (init_dt CS S) = {#}\<close> and
    \<open>additional_WS_invs (init_dt CS S)\<close>
  using init_dt_full[of CS S, OF assms(2-4)] by simp_all
qed

end