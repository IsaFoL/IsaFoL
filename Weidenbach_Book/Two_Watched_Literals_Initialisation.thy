theory Two_Watched_Literals_Initialisation
  imports Two_Watched_Literals_List "../lib/Explorer"
begin

subsection \<open>Initialise Data structure\<close>

type_synonym 'v twl_st_init = \<open>'v twl_st  \<times> 'v clauses\<close>
type_synonym 'v twl_st_l_init = \<open>'v twl_st_l \<times> 'v clauses\<close>

fun state\<^sub>W_of_init :: "'v twl_st_init \<Rightarrow> 'v cdcl\<^sub>W_restart_mset" where
"state\<^sub>W_of_init ((M, N, U, C, NP, UP, Q), OC) =
  (M, clause `# N + NP + OC, clause `# U + UP,  C)"

fun twl_st_of_init :: \<open>'v twl_st_l_init \<Rightarrow> 'v twl_st_init\<close> where
  \<open>twl_st_of_init ((M, N, U, C, NP, UP, WS, Q), OC) =
    ((convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop (Suc U) N),
       C, NP, UP, {#}, Q), OC)\<close>

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
    (get_conflict (fst S) \<noteq> None \<longrightarrow> clauses_to_update (fst S) = {#} \<and> literals_to_update (fst S) = {#}) \<and>
    unit_clss_inv (fst S) \<and>
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
    unit: \<open>unit_clss_inv S\<close> and
    to_upd: \<open>clauses_to_update_inv S\<close> and
    past: \<open>past_invs S\<close>
    using assms unfolding twl_struct_invs_init_def fst_conv
    by clarify+

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
    subgoal by (rule confl)
    subgoal by (rule unit)
    subgoal by (rule to_upd)
    subgoal by (rule past)
    done
qed

definition init_dt_step :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l_init \<Rightarrow> 'v twl_st_l_init\<close> where
  \<open>init_dt_step C S =
  (let ((M, N, U, D, NP, UP, WS, Q), OC) = S in
  (case D of
    None \<Rightarrow>
    if length C = 0
    then ((M, N, U, Some {#}, NP, UP, {#}, {#}), add_mset {#} OC)
    else if length C = 1
    then
      let L = hd C in
      if undefined_lit M L
      then ((Propagated L 0 # M, N, U, None, add_mset {#L#} NP, UP, WS, add_mset (-L) Q), OC)
      else if L \<in> lits_of_l M
      then ((M, N, U, None, add_mset {#L#} NP, UP, WS, Q), OC)
      else ((M, N, U, Some (mset C), add_mset {#L#} NP, UP, {#}, {#}), OC)
    else
      let L = hd C; L' = hd (tl C); C' = tl (tl C) in
      ((M, N @ [[L, L'] @ C'], length N, None, NP, UP, WS, Q), OC)
  | Some D \<Rightarrow>
      ((M, N, U, Some D, NP, UP, WS, Q), add_mset (mset C) OC)))\<close>

fun init_dt :: \<open>'v clauses_l \<Rightarrow> 'v twl_st_l \<times> 'v clauses \<Rightarrow> 'v twl_st_l \<times> 'v clauses\<close> where
  \<open>init_dt [] S = S\<close>
| \<open>init_dt (C # CS) S = init_dt_step C (init_dt CS S)\<close>

lemma init_dt_full:
  fixes CS :: \<open>'v literal list list\<close> and S :: \<open>'v twl_st_l\<close> and OC :: \<open>'v clauses\<close>
  defines \<open>SOC' \<equiv> init_dt CS (S, OC)\<close>
  defines \<open>S' \<equiv> fst (init_dt CS (S, OC))\<close>
  defines \<open>OC' \<equiv> snd (init_dt CS (S, OC))\<close>
  assumes
    \<open>\<forall>C \<in> set CS. distinct C\<close> and
    \<open>twl_struct_invs_init (twl_st_of_init (S, OC))\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l S). \<not>is_decided s\<close> and
    \<open>get_conflict_l S = None \<longrightarrow> literals_to_update_l S = uminus `# lit_of `# mset (get_trail_l S)\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>get_learned_l S = length (get_clauses_l S) - 1\<close> and
    \<open>twl_stgy_invs (twl_st_of None S)\<close> and
    \<open>OC \<noteq> {#} \<longrightarrow> get_conflict_l S \<noteq> None\<close>
  shows
    \<open>twl_struct_invs_init (twl_st_of_init SOC')\<close> and
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
    \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l S' \<noteq> None\<close>
  using assms unfolding S'_def OC'_def SOC'_def OC'_def
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

  obtain M N U D NP UP Q OCS where
    S: \<open>init_dt CS (S, OC) = ((M, N, U, D, NP, UP, {#}, Q), OCS)\<close>
    using w_q by (cases \<open>init_dt CS (S, OC)\<close>) auto
  obtain M' N' U' D' NP' WS' UP' Q' where
    S': \<open>twl_st_of None (fst (init_dt (a # CS) (S, OC))) = (M', N', U', D', NP', UP', WS', Q')\<close>
    by (cases \<open>twl_st_of None (fst (init_dt (a # CS) (S, OC)))\<close>) auto
  then have [simp]: \<open>UP' = UP\<close>
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
       twl_clause_of `# mset (drop U (tl N)), D, NP, UP, {#}, Q)\<close>
  case 1
  let ?S' = \<open>((convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop U (tl N)), D, NP, UP, {#}, Q), OCS)\<close>
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
    unit_clss: \<open>unit_clss_inv (fst ?S')\<close> and
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
    have [simp]: \<open>NP' = NP\<close>
    using S' by (cases D) (auto simp: a S split: if_splits)
  note in_M_IN_QD = in_M_IN_QD[OF a(1)]
  have all_inv':
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_lits_l N M,
      add_mset {#}
       ({#mset (watched_l x) + mset (unwatched_l x). x \<in># mset (tl N)#} + NP' + OCS),
      UP', Some {#})\<close>
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
    by (cases D; cases a) (auto simp: S cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def
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
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_smaller_confl_def)
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