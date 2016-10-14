theory CDCL_Two_Watched_Literals_Simple_Implementation_List_Refinement
imports CDCL_Two_Watched_Literals_Simple_Implementation_Algorithm
begin

section \<open>Second Refinement: Indexed Lists as Clause\<close>

subsection \<open>Types\<close>
type_synonym 'v working_queue_list = "(nat \<times> 'v literal list twl_clause) multiset"
type_synonym 'v lit_queue_list = "'v literal list"

type_synonym 'v clause_list = "'v literal list"
type_synonym 'v clauses_list = "'v literal list"

type_synonym 'v twl_st_list =
  "('v, 'v clause_list) ann_lits \<times> 'v literal list twl_clause multiset \<times> 'v clause_list twl_clause multiset \<times>
    'v clause_list option \<times> 'v clauses \<times> 'v clauses \<times> 'v working_queue_list \<times> 'v lit_queue"


fun working_queue_list :: "'v twl_st_list \<Rightarrow> (nat \<times> 'v clause_list twl_clause) multiset" where
  \<open>working_queue_list (_, _, _, _, _, _, WS, _) = WS\<close>

fun set_working_queue_list :: "(nat \<times> 'v clause_list twl_clause) multiset \<Rightarrow> 'v twl_st_list \<Rightarrow>
  'v twl_st_list" where
  \<open>set_working_queue_list WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun pending_list :: "'v twl_st_list \<Rightarrow> 'v literal multiset" where
  \<open>pending_list (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_pending_list :: "'v literal multiset \<Rightarrow> 'v twl_st_list \<Rightarrow> 'v twl_st_list" where
  \<open>set_pending_list Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun get_conflict_list :: "'v twl_st_list \<Rightarrow> 'v clause_list option" where
  \<open>get_conflict_list (_, _, _, D, _, _, _, _) = D\<close>

fun twl_clause_of where
  \<open>twl_clause_of (TWL_Clause W UW) = TWL_Clause (mset W) (mset UW)\<close>

fun convert_lit where
  \<open>convert_lit (Decided K) = Decided K\<close>
| \<open>convert_lit (Propagated K C) = Propagated K (mset C)\<close>

abbreviation convert_lits where
  \<open>convert_lits \<equiv> map convert_lit\<close>

fun twl_st_of :: \<open>'v twl_st_list  \<Rightarrow> 'v twl_st\<close>where
\<open>twl_st_of (M, N, U, C, NP, UP, WS, Q) =
(convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset C, NP, UP,
  (\<lambda>(a, b). (watched b ! a, twl_clause_of b)) `# WS, Q)
\<close>

fun get_clauses_list :: "'v twl_st_list \<Rightarrow> 'v literal list twl_clause multiset" where
  \<open>get_clauses_list (M, N, U, D, NP, UP, WS, Q) = N + U\<close>

lemma working_queu_empty_iff[iff]:
  \<open>working_queue (twl_st_of x) = {#} \<longleftrightarrow> working_queue_list x = {#}\<close>
  by (cases x) auto

lemma working_queue_list_set_working_queue_list:
  \<open>working_queue_list (set_working_queue_list WS S) = WS\<close>
  by (cases S) auto

lemma lit_of_convert_lit[iff]:
  \<open>lit_of (convert_lit x) = lit_of x\<close>
  by (cases x) auto

lemma lit_of_o_convert_lit[iff]:
  \<open>lit_of o convert_lit = lit_of\<close>
  by auto

lemma is_decided_convert_lit[iff]: \<open>is_decided (convert_lit L) = is_decided L\<close>
  by (cases L) auto

lemma is_decided_o_convert_lit[iff]: \<open>is_decided \<circ> convert_lit = is_decided\<close>
  by auto

lemma no_dup_convert_lits[iff]: \<open>no_dup (convert_lits M) \<longleftrightarrow> no_dup M\<close>
  by (auto simp: defined_lit_map comp_def no_dup_def)

lemma lits_of_convert_lit[iff]: \<open>lits_of (convert_lit ` set M) = lits_of_l M\<close>
  by (induction M) auto

lemma defined_lit_convert_lits[iff]: \<open>defined_lit (convert_lits M) = defined_lit M\<close>
  by (auto simp: defined_lit_map image_image)

lemma get_level_convert_lits[simp]: \<open>get_level (convert_lits M) = get_level M\<close>
  apply (rule ext)
  by (induction M) (auto simp: get_level_def)

lemma count_decided_convert_lits[simp]:
  \<open>count_decided (convert_lits M) = count_decided M\<close>
  by (auto simp: count_decided_def)

lemma get_maximum_level_convert_lits[simp]: \<open>get_maximum_level (convert_lits M) = get_maximum_level M\<close>
  unfolding get_maximum_level_def by auto

lemma pending_list_pending: \<open>pending (twl_st_of S) = pending_list S\<close>
  by (cases S) auto

lemma get_conflict_list_get_conflict:
  \<open>get_conflict (twl_st_of S) = None \<longleftrightarrow> get_conflict_list S = None\<close>
  \<open>get_conflict (twl_st_of S) = Some {#} \<longleftrightarrow> get_conflict_list S = Some []\<close>
  by (cases S, auto)+


subsection \<open>Additional Invariants and Definitions\<close>

definition additional_WS_invs where
  \<open>additional_WS_invs S \<longleftrightarrow> (\<forall>(i, C) \<in># working_queue_list S. (i = 0 \<or> i = 1))\<close>

definition valued where
  \<open>valued M L =
     RETURN (if undefined_lit M L then None else if L \<in> lits_of_l M then Some True else Some False)\<close>

lemma valued_spec:
  assumes \<open>no_dup M\<close>
  shows
  \<open>valued M L \<le> SPEC(\<lambda>v. (v = None \<longleftrightarrow> undefined_lit M L) \<and>
    (v = Some True \<longleftrightarrow> L \<in> lits_of_l M) \<and> (v = Some False \<longleftrightarrow> -L \<in> lits_of_l M))\<close>
  unfolding valued_def
  by (refine_vcg)
    (use assms in \<open>auto simp: defined_lit_map lits_of_def atm_of_eq_atm_of uminus_lit_swap
      no_dup_cannot_not_lit_and_uminus
      split: option.splits\<close>)

definition find_unwatched where
\<open>find_unwatched M C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<le> length C \<and> (\<forall>j<i. -(C!j) \<in> lits_of_l M) \<and>
    (found = Some False \<longrightarrow> (undefined_lit M (C!i) \<and> i < length C)) \<and>
    (found = Some True \<longrightarrow> (C!i \<in> lits_of_l M \<and> i < length C)) \<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      v \<leftarrow> valued M (C!i);
      case v of
        None \<Rightarrow> do { RETURN (Some False, i)}
      | Some True \<Rightarrow> do { RETURN (Some True, i)}
      | Some False \<Rightarrow> do { RETURN (None, i+1)}
      }
    )
    (None, 0::nat)
  }
\<close>

lemma (in transfer) transfer_bool[refine_transfer]:
  assumes "\<alpha> fa \<le> Fa"
  assumes "\<alpha> fb \<le> Fb"
  shows "\<alpha> (case_bool fa fb x) \<le> case_bool Fa Fb x"
  using assms by (auto split: bool.split)

(* Example of code generation *)
schematic_goal find_unwatched_impl: "RETURN ?c \<le> find_unwatched M C"
  unfolding find_unwatched_def valued_def
  apply (refine_transfer)
  done

concrete_definition find_unwatched_impl uses find_unwatched_impl
prepare_code_thms find_unwatched_impl_def
export_code find_unwatched_impl in SML
(* End of code generation *)

lemma find_unwatched:
  assumes \<open>no_dup M\<close>
  shows \<open>find_unwatched M C \<le> SPEC (\<lambda>(found, i).
      (found = None \<longleftrightarrow> (\<forall>L\<in>set C. -L \<in> lits_of_l M)) \<and>
      (found = Some False \<longleftrightarrow> (i < length C \<and> undefined_lit M (C!i))) \<and>
      (found = Some True \<longleftrightarrow> (i < length C \<and> C!i \<in> lits_of_l M)))\<close>
  unfolding find_unwatched_def
  apply (rule WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
     apply simp_all[2]

  subgoal for s unfolding valued_def
    apply refine_vcg
    apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l dest: less_SucE
        split: bool.split if_splits)
    done
  subgoal for s using distinct_consistent_interp[OF assms]
    apply (cases s, cases \<open>fst s\<close>)
     by (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth)
  done

fun update_clause_list where
"update_clause_list (TWL_Clause W UW) i j =
  TWL_Clause (list_update W i (UW!j)) (list_update UW j (W!i))"

inductive update_clauses_list ::
    "'a list twl_clause multiset \<times> 'a list twl_clause multiset \<Rightarrow>
    'a list twl_clause \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    'a list twl_clause multiset \<times> 'a list twl_clause multiset \<Rightarrow> bool" where
\<open>update_clauses_list (N, U) D i j (add_mset (update_clause_list D i j) (remove1_mset D' N), U)\<close>
  if
    \<open>twl_clause_of D' = twl_clause_of D\<close> and
    \<open>D' \<in># N\<close>
| \<open>update_clauses_list (N, U) D i j (N, add_mset (update_clause_list D i j) (remove1_mset D' U))\<close>
  if
    \<open>twl_clause_of D' = twl_clause_of D\<close> and
    \<open>D' \<in># U\<close>

inductive_cases update_clauses_listE: \<open>update_clauses_list (N, U) D i j (N', U')\<close>

text \<open>This theorem is written that strange way to allow the \<open>refine_rcg\<close> to use it automatically.\<close>
lemma update_clauses_list_spec:
  assumes \<open>twl_clause_of C \<in># twl_clause_of `# (N + U)\<close> and \<open>i < length (watched C)\<close> and
    \<open>j < length (unwatched C)\<close>
    \<open>L = watched C ! i\<close> and \<open>L' = unwatched C ! j\<close> and \<open>Nc = twl_clause_of `# N\<close> and
    \<open>Uc = twl_clause_of `# U\<close> and \<open>C' = twl_clause_of C\<close>
  shows
    \<open>SPEC (update_clauses_list (N, U) C i j)
    \<le> \<Down> {((N, U), (N', U')). twl_clause_of `# N = N' \<and> twl_clause_of `# U = U'}
    (SPEC
    (\<lambda>(N', U').
    update_clauses (Nc, Uc) C' L L' (N', U')))\<close>
  apply (rule RES_refine)
  apply (cases C)
  using assms by (auto elim!: update_clauses_listE
      simp: update_clauses.simps image_mset_remove1_mset_if mset_update rev_image_eqI)

definition unit_propagation_inner_loop_body_list :: "nat \<times> 'v clause_list twl_clause \<Rightarrow>
  'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>unit_propagation_inner_loop_body_list C' S = do {
    let (M, N, U, D, NP, UP, WS, Q) = S;
    let (i, C) = C';
    let L = (watched C) ! i;
    let L' = (watched C) ! (1 - i);
    ASSERT(L' \<in># mset (watched C) - {#L#});
    ASSERT (mset (watched C) = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    ASSERT(val_L' = Some True \<longleftrightarrow> L' \<in> lits_of_l M);
    ASSERT(val_L' = Some False \<longleftrightarrow> -L' \<in> lits_of_l M);
    ASSERT(val_L' = None \<longleftrightarrow> undefined_lit M L');
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (unwatched C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched C). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some ((watched C) @ (unwatched C)), NP, UP, {#}, {#})}
        else do {RETURN (Propagated L' (watched C @ unwatched C) # M, N, U, D, NP, UP, WS, add_mset (-L') Q)}
      else do {
        let K = unwatched C ! (snd f);
        (N', U') \<leftarrow> SPEC (update_clauses_list (N, U) C i (snd f));
        RETURN (M, N', U', D, NP, UP, WS, Q)
      }
    }
   }
\<close>

lemma refine_add_invariants:
  assumes
    \<open>(f S) \<le> SPEC(\<lambda>S'. Q S')\<close> and
    \<open>y \<le> \<Down> {(S, S'). P S S'} (f S)\<close>
  shows \<open>y \<le> \<Down> {(S, S'). P S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail by force

lemma unit_propagation_inner_loop_body_list:
  assumes
      WS: \<open>(i, C) \<in># working_queue_list S\<close> and
      i: \<open>i = 0 \<or> i = 1\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of S)\<close> and
      C_N_U: \<open>twl_clause_of C \<in># get_clauses (twl_st_of S)\<close> and
      add_inv: \<open>additional_WS_invs S\<close> and
      stgy_inv: \<open>twl_stgy_invs (twl_st_of S)\<close>
  shows
  \<open>unit_propagation_inner_loop_body_list (i, C) (set_working_queue_list (working_queue_list S - {#(i, C)#}) S) \<le>
      \<Down> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S \<and> twl_stgy_invs S' \<and> twl_struct_invs S'} (unit_propagation_inner_loop_body
      (watched C ! i, twl_clause_of C) (set_working_queue (working_queue (twl_st_of S) - {#(watched C ! i, twl_clause_of C)#}) (twl_st_of S)))\<close>
proof -
  let ?L = \<open>watched C ! i\<close>
  let ?L' = \<open>watched C ! (Suc 0 - i)\<close>
  let ?C' = \<open>twl_clause_of C\<close>
  let ?S = \<open>(set_working_queue_list (working_queue_list S - {#(i, C)#}) S)\<close>
  obtain M N U D NP UP WS Q where S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S) auto
  have S'_S: \<open>twl_st_of S = (convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D,
    NP, UP, (\<lambda>(a, b). (watched b ! a, twl_clause_of b)) `# WS, Q)\<close>
    unfolding S by auto
  have WS': \<open>(watched C ! i, twl_clause_of C) \<in># working_queue (twl_st_of S)\<close>
    using WS S by auto
  have S': \<open>set_working_queue_list (remove1_mset (i, C)
       (working_queue_list (M, N, U, D, NP, UP, WS, Q))) (M, N, U, D, NP, UP, WS, Q) =
    (M, N, U, D, NP, UP, remove1_mset (i, C) WS, Q)\<close>
    by auto
  have st_of_S': \<open>twl_st_of
     (M, N, U, D, NP, UP, remove1_mset (i, C) WS,
      Q) =
    (convert_lits M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D, NP, UP,
      {#(watched b ! a, twl_clause_of b). (a, b) \<in># remove1_mset (i, C) WS#}, Q)\<close>
    by simp
  have inv: \<open>twl_st_inv (twl_st_of S)\<close> and valid: \<open>valid_annotation (twl_st_of S)\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (twl_st_of S))\<close> and
    valid: \<open>valid_annotation (twl_st_of S)\<close>
    using struct_invs WS apply (auto simp: twl_struct_invs_def)
    done

  have n_d: \<open>no_dup M\<close>
    using cdcl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def S
    by (auto simp: trail.simps comp_def)
  then have consistent: \<open>- L \<notin> lits_of_l M\<close> if \<open>L \<in> lits_of_l M\<close> for L
    using consistent_interp_def distinct_consistent_interp that by blast

  have cons_M: \<open>consistent_interp (lits_of_l M)\<close>
    using n_d distinct_consistent_interp by fast

  have C'_N_U: \<open>?C' \<in># twl_clause_of `# (N + U)\<close> and
    uL_M: \<open>-?L \<in> lits_of_l M\<close>
    using WS valid by (auto simp: S twl_struct_invs_def split: prod.splits)
  then have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using inv by (auto simp: twl_st_inv.simps S)

  have watched_C': \<open>watched ?C' = {#?L, ?L'#}\<close>
    using struct i by (cases C) (auto simp: length_list_2)
  then have mset_watched_C: \<open>mset (watched C) = {#watched C ! i, watched C ! (Suc 0 - i)#}\<close>
    by (cases C) auto
  have unwatched_twl_clause_of[simp]: \<open>set_mset (unwatched (twl_clause_of C)) = set (unwatched C)\<close>
    by (cases C) auto
  have in_set_unwatched_conv: \<open>(\<forall>j<length (unwatched C). defined_lit M (unwatched C ! j)) \<longleftrightarrow>
    (\<forall>L \<in># mset (unwatched C). defined_lit M L)\<close>
    for C :: \<open>'b literal list twl_clause\<close> and M :: \<open>('b, 'c) ann_lit list\<close>
    unfolding set_mset_mset by (metis in_set_conv_nth)
  have twl_clause_of_update_C[simp]: \<open>twl_clause_of (update_clause_list C i j) = update_clause (twl_clause_of C) ?L (unwatched C ! j)\<close>
    if \<open>j < length (unwatched C)\<close> for j
    by (cases C) (use i that struct in \<open>auto simp: mset_eq_size_2 length_list_2 mset_update\<close>)
  have update_clause[simp]: \<open>add_mset ?L (add_mset ?L' (mset (unwatched C))) = clause (twl_clause_of C)\<close>
    using watched_C' by (cases C) simp
  have C_N_N: \<open>twl_clause_of `# remove1_mset C N = remove1_mset (twl_clause_of C) (twl_clause_of `# N)\<close>
    if \<open>C \<in># N\<close>
    by (auto simp: that image_mset_remove1_mset_if)
(*   have C_U_U: \<open>twl_clause_of `# remove1_mset C U = remove1_mset (twl_clause_of C) (twl_clause_of `# U)\<close>
    if \<open>C \<notin># N\<close>
    using that C'_N_U C_N_U by (auto simp: image_mset_remove1_mset_if remove_1_mset_id_iff_notin
        id_remove_1_mset_iff_notin S) *)
  have i_watched_C: \<open>i < length (watched C)\<close>
    using i watched_C' by (metis One_nat_def lessI less_SucI mset_watched_C size_add_mset size_empty size_mset)
  have init_invs: \<open>(?S, twl_st_of ?S) \<in> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S}\<close>
    using WS add_inv by (auto simp add: S additional_WS_invs_def dest: in_diffD)

  have init_invs: \<open>(?S, twl_st_of ?S) \<in> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S}\<close>
    using WS add_inv by (auto simp add: S additional_WS_invs_def dest: in_diffD)

  have D_None: \<open>D = None\<close>
    using WS' struct_invs unfolding twl_struct_invs_def S'_S get_conflict.simps working_queue.simps
    by (metis (no_types, lifting)ex_Melem_conv map_option_is_None)
  have upd_S_S': \<open>twl_st_of (set_working_queue_list (remove1_mset (i, C) (working_queue_list S)) S) =
    set_working_queue (remove1_mset (watched C ! i, twl_clause_of C) (working_queue (twl_st_of S)))
            (twl_st_of S)\<close>
    using S WS by (auto simp: image_mset_remove1_mset_if)


  have
    w_q_inv: \<open>working_queue_inv (twl_st_of S)\<close> and
    dist: \<open>distinct_queued (twl_st_of S)\<close> and
    no_dup: \<open>no_duplicate_queued (twl_st_of S)\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have H: \<open>\<And>L C. count {#(watched b ! a, twl_clause_of b). (a, b) \<in># WS#} (L, C) \<le>
    count (twl_clause_of `# (N + U)) C\<close>
    using dist unfolding S distinct_queued.simps twl_st_of.simps by simp

  have \<open>twl_clause_of C \<in># twl_clause_of `# (N + U)\<close>
    using H[of ?L \<open>twl_clause_of C\<close>] WS' C'_N_U by blast

  have \<open>unit_propagation_inner_loop_body_list (i, C) ?S \<le>
    \<Down> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S} (unit_propagation_inner_loop_body
    (?L, twl_clause_of C) (twl_st_of ?S))\<close>
    using n_d unfolding unit_propagation_inner_loop_body_list_def unit_propagation_inner_loop_body_def S
      S'_S[unfolded S] S' st_of_S'
    apply (rewrite at \<open>let _ = watched _ ! _ in _\<close> Let_def)
    supply [[goals_limit = 13]]
    apply (refine_rcg bind_refine_spec[where M' = \<open>find_unwatched _ _\<close>, OF _ find_unwatched]
        bind_refine_spec[where M' = \<open>valued _ _\<close>, OF _ valued_spec[]] update_clauses_list_spec
        case_prod_bind[of _ \<open>If _ _\<close>]; remove_dummy_vars)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal using init_invs by (simp add: S)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal using add_inv S stgy_inv struct_invs by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent additional_WS_invs_def split: option.splits bool.splits)
    subgoal using init_invs S by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent additional_WS_invs_def split: option.splits bool.splits dest: in_diffD)
    subgoal
      by (rule RETURN_rule) (use consistent in \<open>force simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)
    subgoal using C'_N_U S by (simp; fail)
    subgoal using i_watched_C by (simp; fail)
    subgoal by force
    subgoal by force
    subgoal for L' val_L f K N' U' Nc Uc
    proof -
      assume \<open>(Nc, Uc) \<in> Collect (update_clauses_list (N, U) C i (snd f))\<close> and
        upd: \<open>(N', U') \<in> {(N', U').
        update_clauses
         (twl_clause_of `# N, twl_clause_of `# U)
         (twl_clause_of C) (watched C ! i) K (N', U')}\<close> and
        NcUc: \<open>((Nc, Uc), N', U') \<in> {((N, U), N', U'). twl_clause_of `# N = N' \<and> twl_clause_of `# U = U'}\<close>

      have \<open>additional_WS_invs (M, Nc, Uc, D, NP, UP, remove1_mset (i, C) WS, Q)\<close>
        using add_inv S by (auto simp add: additional_WS_invs_def dest: in_diffD)
      then show
        \<open>((M, Nc, Uc, D, NP, UP, remove1_mset (i, C) WS, Q),
          (convert_lits M, N', U', map_option mset D, NP, UP,
            {#(watched b ! a, twl_clause_of b). (a, b) \<in># remove1_mset (i, C) WS#}, Q))
         \<in> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S}\<close>
        using NcUc by simp
    qed
    done
  note H = this
  have *: \<open>unit_propagation_inner_loop_body (watched C ! i, twl_clause_of C)
   (set_working_queue (remove1_mset (watched C ! i, twl_clause_of C) (working_queue (twl_st_of S)))
     (twl_st_of S))
   \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and>
                 twl_stgy_invs S' \<and>
                 cdcl_twl_cp\<^sup>*\<^sup>* (twl_st_of S) S' \<and>
              (S', twl_st_of S) \<in> measure (size \<circ> working_queue))\<close>
    apply (rule unit_propagation_inner_loop_body[of \<open>twl_st_of S\<close> \<open>(watched C ! i, twl_clause_of C)\<close>])
    using WS struct_invs stgy_inv D_None unfolding S by auto
  have H': \<open>unit_propagation_inner_loop_body (watched C ! i, twl_clause_of C) (twl_st_of ?S) \<le>
    SPEC (\<lambda>S'. twl_stgy_invs S' \<and> twl_struct_invs S')\<close>
    using * unfolding conj.left_assoc upd_S_S'
    by (simp add: weaken_SPEC)
  have \<open>unit_propagation_inner_loop_body_list (i, C) ?S
    \<le> \<Down> {(S, S'). (S' = twl_st_of S \<and> additional_WS_invs S) \<and> (twl_stgy_invs S' \<and> twl_struct_invs S')}
    (unit_propagation_inner_loop_body (watched C ! i, twl_clause_of C) (twl_st_of ?S))\<close>
    apply (rule refine_add_invariants)
     apply (rule H')
    by (rule H)
  then show ?thesis unfolding upd_S_S' by simp
qed


definition unit_propagation_inner_loop_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>unit_propagation_inner_loop_list S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
    cdcl_twl_cp\<^sup>*\<^sup>* (twl_st_of S\<^sub>0) (twl_st_of S)\<^esup>
      (\<lambda>S. working_queue_list S \<noteq> {#})
      (\<lambda>S. do {
        C \<leftarrow> SPEC (\<lambda>C. C \<in># working_queue_list S);
        let S' = set_working_queue_list (working_queue_list S - {#C#}) S;
        unit_propagation_inner_loop_body_list C S'
      })
      S\<^sub>0
  \<close>

lemma set_mset_working_queue_list_set_mset_working_queue_spec:
  \<open>RES (set_mset (working_queue_list S)) \<le> \<Down> {((i, C), (L, C')). L = watched C ! i \<and> C' = twl_clause_of C}
  (RES (set_mset (working_queue (twl_st_of S))))\<close>
proof -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S) auto

  show ?thesis
    unfolding S by (rule RES_refine) (auto simp add: Bex_def)
qed

lemma refine_add_inv:
  fixes f :: \<open>'a \<Rightarrow> 'a nres\<close> and f' :: \<open>'b \<Rightarrow> 'b nres\<close> and h :: \<open>'b \<Rightarrow> 'a\<close>
  assumes
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). S' = h S \<and> P' S}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> \<langle>{(S, S'). ?H S S' \<and> P' S}\<rangle> nres_rel\<close>)
  assumes
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q T)\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(S, S'). ?H S S' \<and> P' S \<and> Q (h S)}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma refine_add_inv_pair:
  fixes f :: \<open>'a \<Rightarrow> ('c \<times> 'a) nres\<close> and f' :: \<open>'b \<Rightarrow> ('c \<times> 'b) nres\<close> and h :: \<open>'b \<Rightarrow> 'a\<close>
  assumes
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). (fst S' = h' (fst S) \<and>
    snd S' = h (snd S)) \<and> P' S}\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?R \<rightarrow> \<langle>{(S, S'). ?H S S' \<and> P' S}\<rangle> nres_rel\<close>)
  assumes
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q (snd T))\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(S, S'). ?H S S' \<and> P' S \<and> Q (h (snd S))}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma unit_propagation_inner_loop_list:
  \<open>(unit_propagation_inner_loop_list, unit_propagation_inner_loop) \<in>
  {(S, S'). S' = twl_st_of S \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
  additional_WS_invs S} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of T \<and>
    additional_WS_invs T \<and> twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T)}\<rangle> nres_rel\<close>
proof -
  have \<open>(unit_propagation_inner_loop_list, unit_propagation_inner_loop) \<in>
    {(S, S'). S' = twl_st_of S \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
    additional_WS_invs S} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> additional_WS_invs T}\<rangle> nres_rel\<close>
    unfolding unit_propagation_inner_loop_list_def unit_propagation_inner_loop_def
    apply (refine_vcg set_mset_working_queue_list_set_mset_working_queue_spec; remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    apply (auto intro: set_mset_working_queue_list_set_mset_working_queue_spec)[]
    subgoal for S S' T T' iC LC
      apply (subgoal_tac \<open>unit_propagation_inner_loop_body_list
          (fst iC, snd iC)
          (set_working_queue_list
          (remove1_mset (fst iC, snd iC)
          (working_queue_list T))
          T)
          \<le> \<Down> {(S, S').
          S' = twl_st_of S \<and>
          additional_WS_invs S \<and>
          twl_stgy_invs S' \<and> twl_struct_invs S'}
          (unit_propagation_inner_loop_body
          (watched (snd iC) ! fst iC,
          twl_clause_of (snd iC))
          (set_working_queue
          (remove1_mset
          (watched (snd iC) ! fst iC,
          twl_clause_of (snd iC))
          (working_queue (twl_st_of T)))
          (twl_st_of T)))\<close>)
      subgoal
        by (auto simp add: pw_conc_inres pw_conc_nofail pw_ords_iff(1))
      subgoal
        apply (subgoal_tac \<open>twl_clause_of (snd iC) \<in># get_clauses (twl_st_of T)\<close>)
        subgoal by (rule unit_propagation_inner_loop_body_list[of \<open>fst iC\<close> \<open>snd iC\<close> T])
            (auto simp: additional_WS_invs_def)
        subgoal
        proof -
          assume
            iC: \<open>iC \<in> {C. C \<in># working_queue_list T}\<close> and
            \<open>twl_struct_invs (twl_st_of T)\<close>
          then have \<open>distinct_queued (twl_st_of T)\<close>
            unfolding twl_struct_invs_def by fast
          then have H: \<open>\<And>L C. count
            {#case x of (a, b) \<Rightarrow> (watched b ! a, twl_clause_of b)
            . x \<in># working_queue_list T#}
            (L, C)
            \<le> count (get_clauses (twl_st_of T)) C\<close>
            by (cases T) auto
          have \<open>count {#case x of (a, b) \<Rightarrow> (watched b ! a, twl_clause_of b).
            x \<in># working_queue_list T#} (watched (snd iC) ! (fst iC), twl_clause_of (snd iC)) \<ge> 1\<close>
            using iC by auto
          then show \<open>twl_clause_of (snd iC) \<in># get_clauses (twl_st_of T)\<close>
            using H[of \<open>watched (snd iC) ! (fst iC)\<close> \<open>twl_clause_of (snd iC)\<close>]
            by (meson count_greater_eq_one_iff le_trans)
        qed
        done
      done
    done
  note H = this
  show ?thesis
    apply (rule refine_add_inv)
    subgoal by (rule H)
    subgoal for S
      using unit_propagation_inner_loop[of \<open>twl_st_of S\<close>]
      apply (simp add: weaken_SPEC)
    done
  done
qed

definition clause_to_update :: \<open>'v literal \<Rightarrow> 'v twl_st_list \<Rightarrow> (nat \<times> 'v literal list twl_clause) multiset\<close>where
  \<open>clause_to_update L S =
    ((\<lambda>C. if watched C ! 0 = L then (0, C) else (1, C)) `#
      {#C|C \<in># get_clauses_list S. L \<in># mset (watched C)#})\<close>

definition unit_propagation_outer_loop_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>unit_propagation_outer_loop_list (S\<^sub>0 :: 'v twl_st_list) =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
      working_queue_list S = {#}\<^esup>
      (\<lambda>S. pending_list S \<noteq> {#})
      (\<lambda>S. do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># pending_list S);
        let S' = set_working_queue_list  (clause_to_update L S)
           (set_pending_list (pending_list S - {#L#}) S);
        unit_propagation_inner_loop_list S'
      })
      (S\<^sub>0 :: 'v twl_st_list)
\<close>

lemma refine_pair_to_SPEC:
  fixes f :: \<open>'s \<Rightarrow> 's nres\<close> and g :: \<open>'b \<Rightarrow> 'b nres\<close>
  assumes \<open>(f, g) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). S' = h S \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and [simp]: \<open>S' = h S\<close>
  shows \<open>f S \<le> \<Down> {(S, S'). S' = h S \<and> P' S} (g S')\<close>
proof -
  have \<open>(f S, g (h S)) \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

(* TODO MOVE to Multiset *)
lemma image_filter_cong:
  assumes \<open>\<And>C. C \<in># M \<Longrightarrow> P C \<Longrightarrow> f C = g C\<close>
  shows
    \<open>{#f C. C \<in># {#C \<in># M. P C#}#} = {#g C|C\<in># M. P C#}\<close>
  using assms apply (induction M)
  by auto

(* END Move *)

lemma watched_twl_clause_of_watched: \<open>watched (twl_clause_of x) = mset (watched x)\<close>
  by (cases x) auto
lemma twl_st_of_clause_to_update:
  assumes \<open>twl_struct_invs (twl_st_of T)\<close>
  shows
  \<open>twl_st_of
     (set_working_queue_list
       (clause_to_update L' T)
       (set_pending_list (remove1_mset L' (pending_list T)) T)) =
  set_working_queue
      (Pair L' `# {#C \<in># get_clauses (twl_st_of T). L' \<in># watched C#})
      (set_pending (remove1_mset L' (pending (twl_st_of T))) (twl_st_of T))\<close>
proof -
  obtain M N U D NP UP WS Q where
    T: \<open>T = (M, N, U, D , NP, UP, WS, Q)\<close>
    by (cases T) auto
  define M where \<open>M = N + U\<close>

  have \<open>\<exists>i j. watched x = [i, j]\<close> if \<open>x \<in># M\<close> for x
  proof -
    have \<open>Multiset.Ball (twl_clause_of `# M) struct_wf_twl_cls\<close>
      using assms unfolding T twl_struct_invs_def twl_st_inv.simps twl_st_of.simps M_def
      by auto
    then have \<open>struct_wf_twl_cls (twl_clause_of x)\<close>
      using that by auto
    then show ?thesis
      by (cases x) (auto simp: length_list_2)
  qed
  moreover have \<open>{#(watched
        (snd (if watched x ! 0 = L' then (0, x) else (1, x))) !
       fst (if watched x ! 0 = L' then (0, x) else (1, x)),
       twl_clause_of
        (snd (if watched x ! 0 = L' then (0, x) else (1, x)))).
      x \<in># {#C \<in># M. L' \<in> set (watched C)#}#} =
    {#(L', C) |C \<in># twl_clause_of `# M.
     L' \<in># watched C#}\<close>
    if \<open>\<forall>x \<in># M. \<exists>i j. watched x = [i, j]\<close>
    using that
    by (induction M) (auto simp: watched_twl_clause_of_watched)
  ultimately show ?thesis
    by (auto simp del: filter_union_mset simp: T split_beta M_def clause_to_update_def split: if_splits)
qed

lemma unit_propagation_outer_loop_list_spec:
  \<open>(unit_propagation_outer_loop_list, unit_propagation_outer_loop) \<in>
  {(S, S'). S' = twl_st_of S \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
  additional_WS_invs S \<and> working_queue_list S = {#} \<and> get_conflict_list S = None} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of T \<and>
    (additional_WS_invs T \<and> twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T)) \<and>
    pending (twl_st_of T) = {#} \<and> working_queue (twl_st_of T) = {#} \<and>
    no_step cdcl_twl_cp (twl_st_of T)}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
proof -
  have
    \<open>(unit_propagation_outer_loop_list, unit_propagation_outer_loop) \<in>?R \<rightarrow>
      \<langle>{(S, S').
          S' = twl_st_of S \<and>
          additional_WS_invs S \<and>
          twl_struct_invs (twl_st_of S) \<and>
          twl_stgy_invs (twl_st_of S)}\<rangle> nres_rel\<close>
    unfolding unit_propagation_outer_loop_list_def unit_propagation_outer_loop_def
    apply (refine_vcg unit_propagation_inner_loop_list[THEN refine_pair_to_SPEC])
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: pending_list_pending)
    subgoal by (auto simp: pending_list_pending)
    subgoal by (auto simp add: twl_st_of_clause_to_update
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs)
    subgoal by (auto simp add: twl_st_of_clause_to_update
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs)
    subgoal by (auto simp: additional_WS_invs_def working_queue_list_set_working_queue_list
          clause_to_update_def)
    subgoal
      by (auto simp add: twl_st_of_clause_to_update
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs)
    done
  note H = this
  show ?thesis
    apply (rule refine_add_inv)
    subgoal using H .
    subgoal for S
      apply (rule weaken_SPEC[OF unit_propagation_outer_loop[of \<open>twl_st_of S\<close>]])
          apply ((auto simp: get_conflict_list_get_conflict; fail)+)[4]
      using no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp by blast
    done
qed

fun decide_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>decide_list (M, N, U, D, NP, UP, WS, Q) = do {
     L \<leftarrow> SPEC (\<lambda>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# N));
     RETURN (Decided L # M, N, U, D, NP, UP, WS, {#-L#})
  }
\<close>

declare decide_list.simps[simp del]

lemma decide_list_spec:
  \<open>(decide_list, decide) \<in>
    {(S, S'). S' = twl_st_of S \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
        additional_WS_invs S \<and> working_queue_list S = {#} \<and> pending (twl_st_of S) = {#} \<and>
        get_conflict (twl_st_of S) = None} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of T \<and> additional_WS_invs T \<and>
    (twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and>
    working_queue (twl_st_of T) = {#} \<and> get_conflict (twl_st_of T) = None)}\<rangle> nres_rel\<close>
  (is \<open>?C \<in> ?R \<rightarrow> ?inv\<close>)
proof -
  have
    \<open>(decide_list, decide) \<in> ?R \<rightarrow> \<langle>{(T, T'). T' = twl_st_of T \<and> additional_WS_invs T}\<rangle> nres_rel\<close>
    apply clarify
    unfolding decide_list.simps decide.simps
    by (refine_vcg decide_list.simps decide.simps) (auto simp: additional_WS_invs_def)
  then show ?thesis
    apply (rule refine_add_inv)
    subgoal for S
      using decide_spec[of \<open>twl_st_of S\<close>]
      apply (simp add: weaken_SPEC)
      done
    done
qed

(* TODO Move *)
fun get_trail_list :: "'v twl_st_list \<Rightarrow> ('v, 'v clause_list) ann_lit list" where
  \<open>get_trail_list (M, _, _, _, _, _, _, _) = M\<close>

lemma get_conflict_list_Some_nil_iff:
  \<open>get_conflict_list S = Some [] \<longleftrightarrow> get_conflict (twl_st_of S) = Some {#}\<close>
  by (cases S) auto

abbreviation resolve_cls_list where
  \<open>resolve_cls_list L D' E \<equiv> union_mset_list (remove1 (-L) D') (remove1 L E)\<close>

lemma mset_resolve_cls_list_resolve_cls[iff]:
  \<open>mset (resolve_cls_list L D' E) = cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E)\<close>
  by (auto simp: union_mset_list[symmetric])

lemma resolve_cls_list_nil_iff:
  \<open>resolve_cls_list L D' E = [] \<longleftrightarrow> cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E) = {#}\<close>
  by (metis mset_resolve_cls_list_resolve_cls mset_zero_iff)

lemma get_conflict_list_get_conflict_state_spec:
  assumes \<open>S' = twl_st_of S\<close>
  shows \<open>((get_conflict_list S = Some [], S), (get_conflict S' = Some {#}, S'))
  \<in> {((brk, S), (brk', S')). brk = brk' \<and> S' = twl_st_of S}\<close>
  using assms by (auto simp: get_conflict_list_Some_nil_iff)

(* END Move *)

definition skip_and_resolve_loop_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>skip_and_resolve_loop_list S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv (twl_st_of S\<^sub>0) (brk, twl_st_of S)\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_list S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, WS, Q) = S in
          do {
            let D' = the (get_conflict_list S);
            (L, C) \<leftarrow> SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail_list S));
            if -L \<notin># mset D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, WS, Q))}
            else
              if get_maximum_level M (remove1_mset (-L) (mset D')) = count_decided M
              then
                do {RETURN (resolve_cls_list L D' C = [],
                   (tl M, N, U, Some (resolve_cls_list L D' C), NP, UP, WS, Q))}
              else
                do {RETURN (True, S)}
          }
        )
        (get_conflict_list S\<^sub>0 = Some [], S\<^sub>0);
      RETURN S
    }
  \<close>

lemma get_trail_twl_st_of_nil_iff: \<open>get_trail (twl_st_of T) = [] \<longleftrightarrow> get_trail_list T = []\<close>
  by (cases T) auto

lemma skip_and_resolve_loop_list_spec:
  \<open>(skip_and_resolve_loop_list, skip_and_resolve_loop) \<in>
    {(S::'v twl_st_list, S'). S' = twl_st_of S \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and>
        additional_WS_invs S \<and> working_queue_list S = {#} \<and> pending_list S = {#} \<and>
        get_conflict (twl_st_of S) \<noteq> None} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of T \<and> additional_WS_invs T \<and>
    (twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and>
    no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of T)) \<and>
    no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of T)) \<and>
    pending (twl_st_of T) = {#} \<and>
    working_queue (twl_st_of T) = {#} \<and> get_conflict (twl_st_of T) \<noteq> None)}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow> _\<close>)
proof -
  text \<open>Stupid placeholder to help the application of \<open>rule\<close> later:\<close>
  define TT where [simp]: \<open>TT = (\<lambda>_::'v twl_st_list. True)\<close>
  have is_dec[iff]: \<open>is_decided (hd (get_trail (twl_st_of S))) \<longleftrightarrow> is_decided (hd (get_trail_list S))\<close>
    if \<open>get_trail_list S \<noteq> []\<close> for S :: \<open>'v twl_st_list\<close>
    by (cases S, cases \<open>get_trail_list S\<close>; cases \<open>hd (get_trail_list S)\<close>) (use that in auto)
  have H: \<open>SPEC (\<lambda>(L, C). Propagated L C = hd (get_trail_list S))
    \<le> \<Down> {((L, C), (L', C')). L = L' \<and> C' = mset C}
    (SPEC (\<lambda>(L, C).
    Propagated L C = hd (get_trail S')))\<close> if [simp]: \<open>S' = twl_st_of S\<close> and \<open>get_trail_list S \<noteq> []\<close>
    for S :: \<open>'v twl_st_list\<close> and S' :: \<open>'v twl_st\<close>
    using that apply (cases S; cases S'; cases \<open>get_trail_list S\<close>; cases \<open>hd (get_trail_list S)\<close> ;
        cases \<open>get_trail S'\<close>; cases \<open>hd (get_trail S')\<close>)
    by (auto intro!: RES_refine)
  have H:
    \<open>(skip_and_resolve_loop_list, skip_and_resolve_loop) \<in>
    ?R \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> TT T}\<rangle> nres_rel\<close>
    apply clarify
    unfolding skip_and_resolve_loop_list_def skip_and_resolve_loop_def
    apply (refine_rcg get_conflict_list_get_conflict_state_spec H; remove_dummy_vars)
    subgoal by auto
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk T brk' T'
      apply (cases \<open>get_trail_list T\<close>; cases \<open>hd (get_trail_list T)\<close>)
      by (auto simp: skip_and_resolve_loop_inv_def get_trail_twl_st_of_nil_iff)
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      apply (auto simp: skip_and_resolve_loop_inv_def) done
    subgoal
      apply (auto simp: skip_and_resolve_loop_inv_def) done
    subgoal
      apply (auto simp: skip_and_resolve_loop_inv_def) done
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      apply (cases \<open>M''\<close>)
       apply (auto simp: skip_and_resolve_loop_inv_def) done
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      apply (auto simp: skip_and_resolve_loop_inv_def)
      done
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      apply (cases \<open>M''\<close>)
      apply (auto simp: resolve_cls_list_nil_iff skip_and_resolve_loop_inv_def)
      done
    subgoal by auto
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk T brk' T'
      by (cases T') (auto simp add: additional_WS_invs_def)
    done
  have H: \<open>(skip_and_resolve_loop_list, skip_and_resolve_loop)
    \<in> ?R \<rightarrow>
       \<langle>{(T::'v twl_st_list, T').
         T' = twl_st_of T \<and> TT T \<and>
         twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and>
         (no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of T))) \<and>
         (no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of T))) \<and>
         pending (twl_st_of T) = {#} \<and>
         working_queue (twl_st_of T) = {#} \<and>
         get_conflict (twl_st_of T) \<noteq> None}\<rangle>nres_rel\<close>
    apply (rule refine_add_inv)
    subgoal by (rule H)
    subgoal for S
      using skip_and_resolve_loop_spec[of \<open>twl_st_of S\<close>]
      apply (simp add: weaken_SPEC pending_list_pending)
      done
    done
  have st: \<open>{(T, T').
         T' = twl_st_of T \<and>
         TT T \<and>
         twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and>
         (no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of T))) \<and>
         (no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of T))) \<and>
         pending (twl_st_of T) = {#} \<and>
         working_queue (twl_st_of T) = {#} \<and>
         get_conflict (twl_st_of T) \<noteq> None} =
         {(T, T').
         T' = twl_st_of T \<and>
         additional_WS_invs T \<and>
         twl_struct_invs (twl_st_of T) \<and>
         twl_stgy_invs (twl_st_of T) \<and>
         (no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of T))) \<and>
         (no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of T))) \<and>
         pending (twl_st_of T) = {#} \<and>
         working_queue (twl_st_of T) = {#} \<and>
         get_conflict (twl_st_of T) \<noteq> None}\<close>
    by (auto simp: additional_WS_invs_def)
  show ?thesis
    using H unfolding st by simp
qed

definition backtrack_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres" where
  \<open>backtrack_list S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        L \<leftarrow> SPEC(\<lambda>L. L = lit_of (hd M));
         ASSERT(get_level M L = count_decided M);
         ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);

        if length (the D) > 1
        then do {
          L' \<leftarrow> SPEC(\<lambda>L'. L' \<in># mset (the D) \<and> get_level M L' = get_maximum_level M (mset (the D) - {#-L#}));
          RETURN (Propagated (-L) (the D) # M1, N,
            add_mset (TWL_Clause [-L, L'] (remove1 (-L) (remove1 L' (the D)))) U,
            None, NP, UP, WS, {#L#})
        }
        else do {
          RETURN (Propagated (-L) (the D) # M1, N, U, None, NP, add_mset (mset (the D)) UP, WS, {#L#})
        }
      }
    }
  \<close>

lemma get_all_ann_decomposition_convert_lits:
  shows \<open>get_all_ann_decomposition (convert_lits M) =
    map (\<lambda>(M, M'). (convert_lits M, convert_lits M')) (get_all_ann_decomposition M)\<close>
  apply (induction M rule: ann_lit_list_induct)
  subgoal by auto
  subgoal by auto
  subgoal for L m M by (cases \<open>get_all_ann_decomposition M\<close>) auto
  done

lemma get_level_convert_lits2[simp]:
  \<open>get_level (convert_lits M') K = get_level M' K\<close>
  using get_level_convert_lits[of M'] by simp

lemma backtrack_list_spec:
  \<open>(backtrack_list, backtrack) \<in>
    {(S, S'). S' = twl_st_of S \<and> get_conflict_list S \<noteq> None \<and> get_conflict_list S \<noteq> Some [] \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> get_conflict_list T = None \<and>
       twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and> working_queue_list T = {#} \<and>
       pending_list T \<noteq> {#}}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close>)
proof -
  have obtain_decom: \<open>\<exists>K. \<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd (convert_lits M')))
    (mset E)))\<close> if
    decomp: \<open>\<exists>K. \<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits M')) \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd (convert_lits M')))
    (mset E)))\<close>
    (is \<open>\<exists>K. \<exists>M1 M2. ?P K M1 M2 \<and> ?Q K\<close>)
    for M' E
  proof -
    obtain K M1 M2 where
      \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits M'))\<close> and
      Q: \<open>?Q K\<close>
      using decomp by auto
    then obtain K' M1' M2' where
      \<open>(K' # M1', M2') \<in> set (get_all_ann_decomposition M')\<close> and
      \<open>Decided K # M1 = convert_lits (K' # M1')\<close> and
      \<open>M2 = convert_lits M2'\<close>
      by (auto simp: get_all_ann_decomposition_convert_lits)
    then show ?thesis
      apply -
      apply (rule exI[of _ K], rule exI[of _ M1'], rule exI[of _ M2'])
      by (cases K') (use Q in auto)
  qed

  have H: \<open>SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
    get_level M' K = get_maximum_level M' (remove1_mset (- L) (mset (the D'))) + 1)
    \<le> \<Down> {(M1', M1). M1 = convert_lits M1'}
    (SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
    get_level M K = get_maximum_level M (remove1_mset (- L') (the D)) + 1))\<close>
    if H: \<open>L' = lit_of (hd (convert_lits M'))\<close> \<open>M = convert_lits M'\<close>
    \<open>D \<noteq> None\<close> \<open>L = lit_of (hd (convert_lits M'))\<close> \<open>mset (the D') = the D\<close>
    for M M' L' L D D'
  proof (rule RES_refine, clarify)
    fix M1 K M2
    assume
      lev: \<open>get_level M' K = get_maximum_level M' (remove1_mset (- L) (mset (the D'))) + 1\<close> and
      \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M')\<close>
    then have \<open>(Decided K # convert_lits M1, convert_lits M2) \<in> set (get_all_ann_decomposition M)\<close>
      by (force simp: get_all_ann_decomposition_convert_lits H)
    then show \<open>\<exists>s'\<in>{M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
                     get_level M K =
                     get_maximum_level M (remove1_mset (- L') (the D)) + 1}.
          (M1, s') \<in> {(M1', M1). M1 = convert_lits M1'}\<close>
      using lev by (auto simp: H)
  qed
  have bt:
    \<open>(backtrack_list, backtrack) \<in>
    {(S, S'). S' = twl_st_of S \<and> get_conflict_list S \<noteq> None \<and> get_conflict_list S \<noteq> Some [] \<and>
      working_queue_list S = {#} \<and> pending_list S = {#} \<and>
      no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) \<and>
      no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) \<and>
      twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> get_conflict_list T = None}\<rangle> nres_rel\<close>
    apply clarify
    unfolding backtrack_list_def backtrack_def
    apply (refine_vcg H; remove_dummy_vars)
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q'
      by (cases M) auto
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by (cases M) auto
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      using obtain_decom[of M'] by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by simp
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L' M1' M1
      by auto
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L' M1' M1
      by auto
    done
  have KK:
    \<open>get_conflict_list T = None \<longleftrightarrow> get_conflict (twl_st_of T) = None\<close>
    \<open>working_queue_list T = {#} \<longleftrightarrow> working_queue (twl_st_of T) = {#}\<close>
    \<open>pending_list T = {#} \<longleftrightarrow> pending (twl_st_of T) = {#}\<close>
    for T
    by (cases T; auto)+
  show bt': \<open>(backtrack_list, backtrack) \<in> ?R \<rightarrow> ?I\<close>
    unfolding KK
    apply (rule refine_add_inv)
    subgoal
      using bt unfolding KK .
    subgoal for S
      using backtrack_spec[of \<open>twl_st_of S\<close>] unfolding KK
      apply (cases S)
      apply (auto simp add: weaken_SPEC)
      done
    done
qed

definition cdcl_twl_o_prog_list :: "'v twl_st_list \<Rightarrow> (bool \<times> 'v twl_st_list) nres"  where
  \<open>cdcl_twl_o_prog_list S =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S in
      do {
        if D = None
        then
          if (\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# N))
          then do {S \<leftarrow> decide_list S; RETURN (False, S)}
          else do {RETURN (True, S)}
        else do {
          T \<leftarrow> skip_and_resolve_loop_list S;
          if get_conflict_list T \<noteq> Some []
          then do {U \<leftarrow> backtrack_list T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

thm decide_list_spec[unfolded nres_rel_def, unfolded fun_rel_def, simplified]
thm decide_list_spec
term decide


lemma cdcl_twl_o_prog_list_spec:
  \<open>(cdcl_twl_o_prog_list, cdcl_twl_o_prog) \<in>
    {(S, S'). S' = twl_st_of S \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and> no_step cdcl_twl_cp (twl_st_of S) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
    \<langle>{((brk, T), (brk', T')). T' = twl_st_of T \<and> brk = brk' \<and>
    (get_conflict_list T \<noteq> None \<longrightarrow> get_conflict_list T = Some [])\<and>
       twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and> working_queue_list T = {#} (* \<and>
       (\<not>brk \<longrightarrow> pending_list T \<noteq> {#}) *)}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have twl_prog:
    \<open>(cdcl_twl_o_prog_list, cdcl_twl_o_prog) \<in> ?R \<rightarrow>
      \<langle>{(S, S').
         (fst S' = (fst S) \<and> snd S' = twl_st_of (snd S))}\<rangle> nres_rel\<close>
    apply clarify
    unfolding cdcl_twl_o_prog_list_def cdcl_twl_o_prog_def
    apply (refine_vcg decide_list_spec[THEN refine_pair_to_SPEC]
        skip_and_resolve_loop_list_spec[THEN refine_pair_to_SPEC]
        backtrack_list_spec[THEN refine_pair_to_SPEC]; remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (auto simp add: get_conflict_list_Some_nil_iff)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T T'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    done
  have KK:
    \<open>get_conflict_list T = None \<longleftrightarrow> get_conflict (twl_st_of T) = None\<close>
    \<open>working_queue_list T = {#} \<longleftrightarrow> working_queue (twl_st_of T) = {#}\<close>
    \<open>pending_list T = {#} \<longleftrightarrow> pending (twl_st_of T) = {#}\<close>
    for T
    by (cases T; auto)+
  text \<open>Stupid placeholder to help the application of \<open>rule\<close> later:\<close>
  define TT where [simp]: \<open>TT = (\<lambda>_::bool \<times> 'a twl_st_list. True)\<close>
  let ?J' = \<open>{(U, U').
       (fst U' = id (fst U) \<and> snd U' = twl_st_of (snd U)) \<and> TT U \<and>
        (get_conflict (twl_st_of (snd U)) \<noteq> None \<longrightarrow> get_conflict (twl_st_of (snd U)) = Some {#}) \<and>
         twl_struct_invs (twl_st_of (snd U)) \<and>
         twl_stgy_invs (twl_st_of (snd U)) \<and>
         working_queue (twl_st_of (snd U)) = {#} (* \<and>
         (\<not>fst U \<longrightarrow> pending (twl_st_of (snd U)) \<noteq> {#}) *)}\<close>

  have J: \<open>?J = ?J'\<close>
    by auto
  show bt': ?thesis
    unfolding J
    apply (rule refine_add_inv_pair)
    subgoal
      using twl_prog by (auto simp:)
    subgoal for S
      apply (rule weaken_SPEC[OF cdcl_twl_o_prog_spec[of \<open>twl_st_of S\<close>]])
      apply (auto simp: KK(3))[5]
      apply auto
      done
    done
qed

subsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>cdcl_twl_stgy_prog_list S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and>
        (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of T)) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of S\<^sub>0) (twl_st_of T) \<and>
        working_queue_list T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict_list T = None)\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_list S;
          cdcl_twl_o_prog_list T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

lemma refine_pair_to_SPEC2:
  fixes f :: \<open>'s \<Rightarrow> ('c \<times> 's) nres\<close> and g :: \<open>'b \<Rightarrow> ('c \<times> 'b) nres\<close>
  assumes \<open>(f, g) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{((brk, S), (brk', S')). S' = h S \<and> brk = brk' \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and [simp]: \<open>S' = h S\<close>
  shows \<open>f S \<le> \<Down> {((brk, S), (brk', S')). S' = h S \<and> brk = brk' \<and> P' S} (g S')\<close>
proof -
  have \<open>(f S, g (h S)) \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

lemma cdcl_twl_stgy_prog_list_spec:
  \<open>(cdcl_twl_stgy_prog_list, cdcl_twl_stgy_prog) \<in>
    {(S, S'). S' = twl_st_of S \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow> ((False, a), (False, b)) \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> ?R}\<close>
    for a b by auto
  have KK:
    \<open>get_conflict_list T = None \<longleftrightarrow> get_conflict (twl_st_of T) = None\<close>
    \<open>working_queue_list T = {#} \<longleftrightarrow> working_queue (twl_st_of T) = {#}\<close>
    \<open>pending_list T = {#} \<longleftrightarrow> pending (twl_st_of T) = {#}\<close>
    for T
    by (cases T; auto)+
  show ?thesis
    unfolding cdcl_twl_stgy_prog_list_def cdcl_twl_stgy_prog_def
    apply (refine_rcg R cdcl_twl_o_prog_list_spec[THEN refine_pair_to_SPEC2]
        unit_propagation_outer_loop_list_spec[THEN refine_pair_to_SPEC]; remove_dummy_vars)
    subgoal unfolding KK by auto
    subgoal by auto
    subgoal by fastforce
    subgoal unfolding KK by fastforce
    subgoal by auto
    subgoal unfolding KK by auto
    subgoal unfolding KK by auto
    subgoal unfolding KK by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: additional_WS_invs_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding KK by auto
    subgoal by (auto simp: pending_list_pending)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_list_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of S)\<close> and \<open>twl_stgy_invs (twl_st_of S)\<close> and
    \<open>working_queue_list S = {#}\<close> and \<open>pending_list S = {#}\<close> and
    \<open>get_conflict_list S = None\<close>
  shows
    \<open>cdcl_twl_stgy_prog_list S \<le> SPEC(\<lambda>T. full cdcl_twl_stgy (twl_st_of S) (twl_st_of T))\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_list_spec[THEN refine_pair_to_SPEC,
          of S \<open>twl_st_of S\<close>]])
  using assms apply auto[2]
  apply (rule order_trans)
   apply (rule ref_two_step[OF _ cdcl_twl_stgy_prog_spec[of \<open>twl_st_of S\<close>],
        of _ \<open>{(S, S'). S' = twl_st_of S \<and> True}\<close>])
  using assms by (auto simp: full_def pending_list_pending get_conflict_list_get_conflict
      pw_conc_inres pw_conc_nofail pw_ords_iff(1))


end