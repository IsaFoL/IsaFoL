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
  "('v, 'v clause) ann_lits \<times> 'v literal list twl_clause multiset \<times> 'v clause_list twl_clause multiset \<times>
    'v clause_list option \<times> 'v clauses \<times> 'v clauses \<times> 'v working_queue_list \<times> 'v lit_queue"


fun working_queue_list :: "'v twl_st_list \<Rightarrow> (nat \<times> 'v clause_list twl_clause) multiset" where
  \<open>working_queue_list (_, _, _, _, _, _, WS, _) = WS\<close>

fun set_working_queue_list :: "(nat \<times> 'v clause_list twl_clause) multiset \<Rightarrow> 'v twl_st_list \<Rightarrow>
  'v twl_st_list" where
  \<open>set_working_queue_list WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun twl_clause_of where
  \<open>twl_clause_of (TWL_Clause W UW) = TWL_Clause (mset W) (mset UW)\<close>

fun twl_st_of :: \<open>'v twl_st_list  \<Rightarrow> 'v twl_st\<close>where
\<open>twl_st_of (M, N, U, C, NP, UP, WS, Q) =
(M, twl_clause_of `# N, twl_clause_of `# U, map_option mset C, NP, UP,
  (\<lambda>(a, b). (watched b ! a, twl_clause_of b)) `# WS, Q)
\<close>

fun get_clauses_list :: "'v twl_st_list \<Rightarrow> 'v literal list twl_clause multiset" where
  \<open>get_clauses_list (M, N, U, D, NP, UP, WS, Q) = N + U\<close>

lemma working_queu_empty_iff[iff]:
  \<open>working_queue (twl_st_of x) = {#} \<longleftrightarrow> working_queue_list x = {#}\<close>
  by (cases x) auto


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
        else do {RETURN (Propagated L' (mset (watched C) + mset (unwatched C)) # M, N, U, D, NP, UP, WS, add_mset (-L') Q)}
      else do {
        let K = unwatched C ! (snd f);
        (N', U') \<leftarrow> SPEC (update_clauses_list (N, U) C i (snd f));
        RETURN (M, N', U', D, NP, UP, WS, Q)
      }
    }
   }
\<close>


lemma distinct_mset_distinct_twl_clause_of:
  \<open>distinct_mset (clause `# twl_clause_of `# N) \<Longrightarrow> distinct_mset N\<close>
  by (induction N) auto

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
  have S'_S: \<open>twl_st_of S = (M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D,
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
    (M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D, NP, UP,
      {#(watched b ! a, twl_clause_of b). (a, b) \<in># remove1_mset (i, C) WS#}, Q)\<close>
    by simp
  have inv: \<open>twl_st_inv (twl_st_of S)\<close> and valid: \<open>valid_annotation (twl_st_of S)\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (twl_st_of S))\<close> and
    valid: \<open>valid_annotation (twl_st_of S)\<close>
    using struct_invs WS apply (auto simp: twl_struct_invs_def)
    done

  have n_d: \<open>no_dup M\<close>
    using cdcl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def S by (auto simp: trail.simps)
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
      then show \<open>((M, Nc, Uc, D, NP, UP,
        remove1_mset (i, C) WS, Q),
        M, N', U', map_option mset D, NP, UP,
        {#(watched b ! a, twl_clause_of b). (a,
        b) \<in># remove1_mset (i, C) WS#},
        Q)
        \<in> {(S, S').
        S' = twl_st_of S \<and> additional_WS_invs S}\<close>
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
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). S' = h S \<and> P' S}\<rangle> nres_rel\<close> and
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q T)\<close>
  shows
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). S' = h S \<and> P' S \<and> Q (h S)}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
  by auto

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

end