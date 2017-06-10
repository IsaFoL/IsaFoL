theory CDCL_Two_Watched_Literals_List
  imports CDCL_Two_Watched_Literals_Algorithm DPLL_CDCL_W_Implementation
begin

lemma mset_take_mset_drop_mset: \<open>(\<lambda>x. mset (take 2 x) + mset (drop 2 x)) = mset\<close>
  unfolding mset_append[symmetric] append_take_drop_id ..
lemma mset_take_mset_drop_mset': \<open>mset (take 2 x) + mset (drop 2 x) = mset x\<close>
  unfolding mset_append[symmetric] append_take_drop_id ..


section \<open>Second Refinement: Lists as Clause\<close>

subsection \<open>Types\<close>
type_synonym 'v clauses_to_update_l = "nat multiset"

type_synonym 'v clause_l = "'v literal list"
type_synonym 'v clauses_l = "'v clause_l list"
type_synonym 'v cconflict = "'v clause option"
type_synonym 'v cconflict_l = \<open>'v literal list option\<close>

type_synonym 'v twl_st_l =
  "('v, nat) ann_lits \<times> 'v clauses_l \<times> nat \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses_to_update_l \<times> 'v lit_queue"

fun clauses_to_update_l :: "'v twl_st_l \<Rightarrow> 'v clauses_to_update_l" where
  \<open>clauses_to_update_l (_, _, _, _, _, _, WS, _) = WS\<close>

fun get_trail_l :: "'v twl_st_l \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_l (M, _, _, _, _, _, _, _) = M\<close>

fun set_clauses_to_update_l :: "'v clauses_to_update_l \<Rightarrow> 'v twl_st_l \<Rightarrow>
  'v twl_st_l" where
  \<open>set_clauses_to_update_l WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun literals_to_update_l :: "'v twl_st_l \<Rightarrow> 'v clause" where
  \<open>literals_to_update_l (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_literals_to_update_l :: "'v clause \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l" where
  \<open>set_literals_to_update_l Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun get_conflict_l :: "'v twl_st_l \<Rightarrow> 'v cconflict" where
  \<open>get_conflict_l (_, _, _, D, _, _, _, _) = D\<close>

fun watched_l where
  \<open>watched_l l = take 2 l\<close>

fun unwatched_l where
  \<open>unwatched_l l = drop 2 l\<close>

fun twl_clause_of :: "'a list \<Rightarrow> 'a multiset twl_clause" where
  \<open>twl_clause_of l = TWL_Clause (mset (watched_l l)) (mset (unwatched_l l))\<close>

fun clause_of :: "'a::plus twl_clause \<Rightarrow> 'a" where
  \<open>clause_of (TWL_Clause W UW) = W + UW\<close>

fun convert_lit :: "'v clauses_l \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit" where
  \<open>convert_lit N (Decided K) = Decided K\<close>
| \<open>convert_lit N (Propagated K j) =
  (if j = 0 then Propagated K {#K#} else Propagated K (mset (N ! j)))\<close>

definition convert_lits_l :: "'v clauses_l \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits" where
  \<open>convert_lits_l N M = map (convert_lit N) M\<close>

lemma convert_lits_l_nil[simp]: \<open>convert_lits_l N [] = []\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_cons[simp]: \<open>convert_lits_l N (L # M) = convert_lit N L # convert_lits_l N M\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_append[simp]: \<open>convert_lits_l N (M @ M') = convert_lits_l N M @ convert_lits_l N M'\<close>
  by (auto simp: convert_lits_l_def)

fun get_learned_l :: "'v twl_st_l \<Rightarrow> nat" where
  \<open>get_learned_l (_, _, U, _, _, _, _, _) = U\<close>

abbreviation resolve_cls_l where
  \<open>resolve_cls_l L D' E \<equiv> union_mset_list (remove1 (-L) D') (remove1 L E)\<close>

lemma mset_resolve_cls_l_resolve_cls[iff]:
  \<open>mset (resolve_cls_l L D' E) = cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E)\<close>
  by (auto simp: union_mset_list[symmetric])

lemma resolve_cls_l_nil_iff:
  \<open>resolve_cls_l L D' E = [] \<longleftrightarrow> cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E) = {#}\<close>
  by (metis mset_resolve_cls_l_resolve_cls mset_zero_iff)

fun twl_st_of :: \<open>'v literal option \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st\<close> where
\<open>twl_st_of (Some L) (M, N, U, C, NP, UP, WS, Q) =
  (convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop (Suc U) N),
    C, NP, UP, image_mset (\<lambda>j. (L, twl_clause_of (N!j))) WS, Q)\<close> |
\<open>twl_st_of None (M, N, U, C, NP, UP, WS, Q) =
(convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop (Suc U) N),
    C, NP, UP, {#}, Q)
\<close>

fun get_clauses_l :: "'v twl_st_l \<Rightarrow> 'v clauses_l" where
  \<open>get_clauses_l (M, N, U, D, NP, UP, WS, Q) = N\<close>

lemma get_conflict_l_Some_nil_iff:
  \<open>get_conflict_l S = Some {#} \<longleftrightarrow> get_conflict (twl_st_of None S) = Some {#}\<close>
  by (cases S) auto

lemma clauses_to_update_empty_iff[iff]:
  \<open>clauses_to_update (twl_st_of (Some L) x) = {#} \<longleftrightarrow> clauses_to_update_l x = {#}\<close>
  by (cases x) auto

lemma clauses_to_update_twl_st_of_None[simp]: \<open>clauses_to_update (twl_st_of None x) = {#}\<close>
  by (cases x) auto

lemma clauses_to_update_l_set_clauses_to_update_l:
  \<open>clauses_to_update_l (set_clauses_to_update_l WS S) = WS\<close>
  by (cases S) auto

lemma lit_of_convert_lit[iff]:
  \<open>lit_of (convert_lit N x) = lit_of x\<close>
  by (cases x) auto

lemma lit_of_o_convert_lit[iff]:
  \<open>lit_of o (convert_lit N) = lit_of\<close>
  by auto

lemma is_decided_convert_lit[iff]: \<open>is_decided (convert_lit N L) = is_decided L\<close>
  by (cases L) auto

lemma is_decided_o_convert_lit[iff]: \<open>is_decided \<circ> (convert_lit N) = is_decided\<close>
  by auto

lemma no_dup_convert_lits_l[iff]: \<open>no_dup (convert_lits_l N M) \<longleftrightarrow> no_dup M\<close>
  by (auto simp: defined_lit_map comp_def no_dup_def convert_lits_l_def)

lemma lits_of_convert_lit[iff]: \<open>lits_of (convert_lit N ` set M) = lits_of_l M\<close>
  by (induction M) auto

lemma lits_of_l_convert_lits_l[simp]: \<open>lits_of_l (convert_lits_l N M) = lits_of_l M\<close>
  by (induction M) auto

lemma convert_lits_l_true_annot[simp]: \<open>convert_lits_l N M \<Turnstile>a A \<longleftrightarrow> M \<Turnstile>a A\<close>
  unfolding true_annot_def by auto

lemma convert_lits_l_true_annots[simp]: \<open>convert_lits_l N M \<Turnstile>as A \<longleftrightarrow> M \<Turnstile>as A\<close>
  unfolding true_annots_def by auto

lemma defined_lit_convert_lits_l[iff]: \<open>defined_lit (convert_lits_l N M) = defined_lit M\<close>
  by (auto simp: defined_lit_map image_image convert_lits_l_def)

lemma get_level_convert_lits_l[simp]: \<open>get_level (convert_lits_l N M) = get_level M\<close>
  apply (rule ext)
  by (induction M) (auto simp: get_level_def convert_lits_l_def)

lemma count_decided_convert_lits_l[simp]:
  \<open>count_decided (convert_lits_l N M) = count_decided M\<close>
  by (auto simp: count_decided_def convert_lits_l_def)

lemma get_maximum_level_convert_lits_l[simp]:
  \<open>get_maximum_level (convert_lits_l N M) = get_maximum_level M\<close>
  unfolding get_maximum_level_def by auto

lemma literals_to_update_l_literals_to_update: \<open>literals_to_update (twl_st_of L S) = literals_to_update_l S\<close>
  by (cases S, cases L) auto

lemma get_conflict_l_get_conflict:
  \<open>get_conflict (twl_st_of L S) = None \<longleftrightarrow> get_conflict_l S = None\<close>
  \<open>get_conflict (twl_st_of L S) = Some {#} \<longleftrightarrow> get_conflict_l S = Some {#}\<close>
  by (cases S; cases L, auto)+

lemma get_trail_twl_st_of_nil_iff: \<open>get_trail (twl_st_of L T) = [] \<longleftrightarrow> get_trail_l T = []\<close>
  by (cases T; cases L) (auto simp: convert_lits_l_def)


subsection \<open>Additional Invariants and Definitions\<close>

definition additional_WS_invs where
  \<open>additional_WS_invs S \<longleftrightarrow>
    (\<forall>C \<in># clauses_to_update_l S. C < length (get_clauses_l S) \<and> C > 0) \<and>
    (\<forall>L C. Propagated L C \<in> set (get_trail_l S) \<longrightarrow> (C < length (get_clauses_l S) \<and>
      (C > 0 \<longrightarrow> L \<in> set (watched_l ((get_clauses_l S) ! C))))) \<and>
    distinct_mset (clauses_to_update_l S) \<and> get_clauses_l S \<noteq> [] \<and>
    get_learned_l S < length (get_clauses_l S)\<close>

definition valued where
  \<open>valued M L = (if undefined_lit M L then None else if L \<in> lits_of_l M then Some True else Some False)\<close>

lemma valued_spec:
  assumes \<open>no_dup M\<close>
  shows
  \<open>RETURN (valued M L) \<le> SPEC(\<lambda>v. (v = None \<longleftrightarrow> undefined_lit M L) \<and>
    (v = Some True \<longleftrightarrow> L \<in> lits_of_l M) \<and> (v = Some False \<longleftrightarrow> -L \<in> lits_of_l M))\<close>
  unfolding valued_def
  by refine_vcg
    (use assms in \<open>auto simp: defined_lit_map lits_of_def atm_of_eq_atm_of uminus_lit_swap
      no_dup_cannot_not_lit_and_uminus
      split: option.splits\<close>)

definition find_unwatched :: "('a, 'b) ann_lits \<Rightarrow> 'a clause_l \<Rightarrow> (nat option) nres" where
\<open>find_unwatched M C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
    (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and> j < length C \<and> j \<ge> 2))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      ASSERT(i < length C);
      case valued M (C!i) of
        None \<Rightarrow> do { RETURN (Some i, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some i, i)} else do { RETURN (None, i+1)})
    })
    (None, 2::nat);
  RETURN (fst S)
  }
\<close>

(* Example of code generation *)
(* schematic_goal find_unwatched_impl: "RETURN ?c \<le> find_unwatched M C"
  unfolding find_unwatched_def valued_def
  apply (refine_transfer)
  done

concrete_definition find_unwatched_impl uses find_unwatched_impl
prepare_code_thms find_unwatched_impl_def
export_code find_unwatched_impl in SML *)
(* End of code generation *)

lemma find_unwatched:
  assumes \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close>
  shows \<open>find_unwatched M C \<le> SPEC (\<lambda>(found).
      (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l C). -L \<in> lits_of_l M)) \<and>
      (\<forall>j. found = Some j \<longrightarrow> (j < length C \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and> j \<ge> 2)))\<close>
  unfolding find_unwatched_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq valued_def
        split: if_splits intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq valued_def
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal by (auto simp: valued_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: valued_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using distinct_consistent_interp[OF assms(1)]
    apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth
       valued_def split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
    by (metis atLeastLessThan_iff less_antisym)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using no_dup_consistentD[OF assms(1)]
    by (cases s, cases \<open>fst s\<close>)
      (auto simp: Decided_Propagated_in_iff_in_lits_of_l all_set_conv_nth
        intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal by auto
  subgoal for s j by auto
  subgoal by auto
  done

definition unit_propagation_inner_loop_body_l :: "'v literal \<Rightarrow> nat \<Rightarrow>
  'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>unit_propagation_inner_loop_body_l L C S = do {
    let (M, N, U, D, NP, UP, WS, Q) = S;
    ASSERT(no_dup M);
    ASSERT(C < length N);
    ASSERT(0 < length (N!C));
    let i = (if (N!C) ! 0 = L then 0 else 1);
    ASSERT(i < length (N!C));
    ASSERT(1-i < length (N!C));
    let L = (N!C) ! i;
    let L' = (N!C) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> RETURN (valued M L');
    if val_L' = Some True
    then RETURN (M, N, U, D, NP, UP, WS, Q)
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      case f of
         None \<Rightarrow>
           if val_L' = Some False
           then RETURN (M, N, U, Some (mset (N!C)), NP, UP, {#}, {#})
           else RETURN (Propagated L' C # M, N, U, D, NP, UP, WS, add_mset (-L') Q)
      | Some f \<Rightarrow> do {
           ASSERT(f < length (N!C));
           let K = (N!C) ! f;
           let N' = list_update N C (swap (N!C) i f);
           ASSERT (K \<in># mset (unwatched_l (N!C)) \<and> -K \<notin> lits_of_l M);
           RETURN (M, N', U, D, NP, UP, WS, Q)
        }
    }
   }
\<close>

(* TOVO Move to WB_List_More *)
lemma take_2_if:
  \<open>take 2 C = (if C = [] then [] else if length C = 1 then [hd C] else [C!0, C!1])\<close>
  by (cases C; cases \<open>tl C\<close>) auto

lemma tl_update_swap:
  \<open>i \<ge> 1 \<Longrightarrow> tl (N[i := C]) = tl N[i-1 := C]\<close>
  by (auto simp:  drop_Suc[of 0, symmetric, simplified] drop_update_swap)
(* End Move *)

lemma refine_add_invariants:
  assumes
    \<open>(f S) \<le> SPEC(\<lambda>S'. Q S')\<close> and
    \<open>y \<le> \<Down> {(S, S'). P S S'} (f S)\<close>
  shows \<open>y \<le> \<Down> {(S, S'). P S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail by force

lemma unit_propagation_inner_loop_body_l:
  fixes i C :: nat and S :: \<open>'v twl_st_l\<close> and L :: \<open>'v literal\<close>
  defines
    C'[simp]: \<open>C' \<equiv> get_clauses_l S ! C\<close> and
    S'_def[simp]: \<open>S' \<equiv> twl_st_of (Some L) S\<close>
  assumes
    WS: \<open>C \<in># clauses_to_update_l S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>additional_WS_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close>
  shows
    \<open>unit_propagation_inner_loop_body_l L C (set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S) \<le>
        \<Down> {(S, S''). twl_st_of (Some L) S = S'' \<and> additional_WS_invs S \<and> twl_stgy_invs S'' \<and>
             twl_struct_invs S''}
          (unit_propagation_inner_loop_body (L, twl_clause_of C')
             (set_clauses_to_update (clauses_to_update (S') - {#(L, twl_clause_of C')#}) (S')))\<close>
proof -
  define i :: nat where \<open>i \<equiv> (if C'!0 = L then 0 else 1)\<close>
  let ?L = \<open>C' ! i\<close>
  let ?L' = \<open>C' ! (Suc 0 - i)\<close>
  let ?S = \<open>set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S\<close>
  obtain M N U D NP UP WS Q where S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S) auto

  have inv: \<open>twl_st_inv S'\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S')\<close> and
    valid: \<open>valid_annotation S'\<close>
    using struct_invs WS by (auto simp: twl_struct_invs_def)
  have
    w_q_inv: \<open>clauses_to_update_inv S'\<close> and
    dist: \<open>distinct_queued S'\<close> and
    no_dup: \<open>no_duplicate_queued S'\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have n_d: \<open>no_dup M\<close>
    using cdcl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps comp_def S)
  then have consistent: \<open>- L \<notin> lits_of_l M\<close> if \<open>L \<in> lits_of_l M\<close> for L
    using consistent_interp_def distinct_consistent_interp that by blast

  have cons_M: \<open>consistent_interp (lits_of_l M)\<close>
    using n_d distinct_consistent_interp by fast
  have N_take_drop: \<open>tl N = take U (tl N) @ drop (Suc U) N\<close>
    by (simp add: drop_Suc)
  let ?C' = \<open>twl_clause_of C'\<close>
  have C'_N_U_or: \<open>?C' \<in># twl_clause_of `# mset (take U (tl N)) \<or> ?C' \<in># twl_clause_of `# mset (drop (Suc U) N)\<close>
    using WS valid
    by (auto simp: S twl_struct_invs_def split: prod.splits simp del: twl_clause_of.simps)
  then have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using inv by (auto simp: twl_st_inv.simps S simp del: twl_clause_of.simps)
  have C'_N_U: \<open>?C' \<in># twl_clause_of `# mset (tl N)\<close>
    using C'_N_U_or apply (subst N_take_drop)
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric] take_tl .
  have watched_C': \<open>mset (watched_l C') = {#?L, ?L'#}\<close>
    using struct i_def by (cases C) (auto simp: length_list_2 take_2_if S)
  then have mset_watched_C: \<open>mset (watched_l C') = {#watched_l C' ! i, watched_l C' ! (Suc 0 - i)#}\<close>
    using i_def by (cases \<open>twl_clause_of (get_clauses_l S ! C)\<close>) (auto simp: take_2_if)
  have two_le_length_C: \<open>2 \<le> length C'\<close>
    by (metis length_take linorder_not_le min_less_iff_conj numeral_2_eq_2 order_less_irrefl
        size_add_mset size_eq_0_iff_empty size_mset watched_C' watched_l.simps)
  have C_N_U: \<open>C < length (get_clauses_l S)\<close>
    using WS add_inv by (auto simp: S additional_WS_invs_def)
  obtain WS' where WS'_def: \<open>WS = add_mset C WS'\<close>
    using multi_member_split[OF WS] by (auto simp: S)
  have L: \<open>L \<in> set (watched_l C')\<close>
    using valid by (auto simp: S WS'_def)
  have C'_i[simp]: \<open>C'!i = L\<close>
    using L two_le_length_C by (auto simp: take_2_if i_def split: if_splits)
  then have [simp]: \<open>N!C!i = L\<close>
    by (auto simp: S)

  have S'_S: \<open>twl_st_of (Some L) S =  (convert_lits_l N M,
     {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take U (tl N))#},
     {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc U) N)#},
     D, NP, UP,
     {#(L, TWL_Clause (mset (take 2 (N ! x))) (mset (drop 2 (N ! x)))).
        x \<in># WS#},
     Q)\<close>
    unfolding S by auto
  have i: \<open>i = 0 \<or> i = 1\<close>
    using i_def by auto
  have WS': \<open>(C' ! i, twl_clause_of C') \<in># clauses_to_update S'\<close>
    using WS S by auto
  have S': \<open>set_clauses_to_update_l (remove1_mset C
       (clauses_to_update_l (M, N, U, D, NP, UP, WS, Q))) (M, N, U, D, NP, UP, WS, Q) =
    (M, N, U, D, NP, UP, remove1_mset C WS, Q)\<close>
    by auto
  let ?N = \<open>{#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#}\<close>
  let ?U = \<open>{#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (drop (Suc U) N)#}\<close>
  have st_of_S': \<open>twl_st_of (Some L)
     (M, N, U, D, NP, UP, remove1_mset C WS, Q) = (convert_lits_l N M, ?N, ?U, D, NP,
       UP, {#(L, TWL_Clause (mset (take 2 (N ! j))) (mset (drop 2 (N ! j)))).
          j \<in># remove1_mset C WS#}, Q)\<close>
    by simp

  have unwatched_twl_clause_of[simp]: \<open>set_mset (unwatched (twl_clause_of C')) = set (unwatched_l C')\<close>
    by (cases C) auto
  have in_set_unwatched_conv: \<open>(\<forall>j<length (unwatched C). defined_lit M (unwatched C ! j)) \<longleftrightarrow>
    (\<forall>L \<in># mset (unwatched C). defined_lit M L)\<close>
    for C :: \<open>'b literal list twl_clause\<close> and M :: \<open>('b, 'c) ann_lit list\<close>
    unfolding set_mset_mset by (metis in_set_conv_nth)
  have init_invs: \<open>(?S, twl_st_of (Some L) ?S) \<in> {(S, S'). S' = twl_st_of (Some L) S \<and> additional_WS_invs S}\<close> and
    C_le_N: \<open>C < length N\<close> \<open>C > 0\<close> and
    dist_WS: \<open>distinct_mset WS\<close>
    using WS add_inv by (auto simp add: S additional_WS_invs_def dest: in_diffD)

  have init_invs: \<open>(?S, twl_st_of (Some L) ?S) \<in> {(S, S'). S' = twl_st_of (Some L) S \<and> additional_WS_invs S}\<close>
    using WS add_inv by (auto simp add: S additional_WS_invs_def dest: in_diffD)

  have D_None: \<open>D = None\<close>
    using WS' struct_invs unfolding twl_struct_invs_def S'_S get_conflict.simps clauses_to_update.simps
    by (metis S S'_def ex_Melem_conv get_conflict_l.simps get_conflict_l_get_conflict(1))
  have upd_S_S': \<open>twl_st_of (Some L) (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S) =
    set_clauses_to_update (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S'\<close>
    using S WS by (auto simp: image_mset_remove1_mset_if)

  have H: \<open>\<And>L' C. count {#(L, twl_clause_of (N!b)). b \<in># WS#} (L', C) \<le>
    count (twl_clause_of `# mset (tl N)) C\<close>
    using dist N_take_drop unfolding S distinct_queued.simps twl_st_of.simps mset_append[symmetric]
      image_mset_union[symmetric] S'_def by auto
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
    using no_dup by (simp add: S all_conj_distrib WS'_def)
  then have uL_M: \<open>-L \<in> lits_of_l (get_trail_l S)\<close>
    apply - by (drule mset_le_add_mset_decr_left2)
      (auto simp: convert_lits_l_def lits_of_def S dest!: mset_le_add_mset_decr_left2)
  have \<open>twl_clause_of C' \<in># twl_clause_of `# mset (tl N)\<close>
    using H[of ?L \<open>twl_clause_of C'\<close>] WS' C'_N_U by blast
  have \<open>length (watched_l C') = 2\<close>
    unfolding length_list_2
    using watched_C' i by (auto simp: mset_eq_size_2 take_2_if)
  then have set_take_2_watched: \<open>set (take 2 C') = {?L, ?L'}\<close>
    using watched_C' i by (auto simp: mset_eq_size_2 take_2_if)
  note C'[simp del]
  have N_C_C': \<open>N!C = C'\<close>
    using C' unfolding S by auto
  have [simp]: \<open>watched_l C' ! i = C' ! i\<close> \<open>watched_l C' ! (Suc 0 - i) = C' ! (Suc 0 - i)\<close>
    using i C'_i by (auto simp del: C'_i)
  have add_mset_C'_i:
    \<open>add_mset (C' ! i) (add_mset (watched_l C' ! (Suc 0 - i)) (mset (unwatched_l C'))) = mset C'\<close>
    using i watched_C' by (cases C'; cases \<open>tl C'\<close>) (auto simp: take_2_if split: if_splits)

  let ?UW = \<open>unwatched_l C'\<close>
  have update_clause_ll_spec:
    \<open>RETURN (NN[D := swap (NN ! D) ii k])
    \<le> \<Down> {(N, (N', U')). N' = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#} \<and>
         U' = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (drop (Suc U) N)#}}
        (SPEC (\<lambda>(N', U'). update_clauses
          (NNNNNN, UUUUUU)
          E F K (N', U')))\<close>
    if k_2: \<open>k \<ge> 2\<close> and k'': \<open>k'' = k - 2\<close> and [simp]: \<open>i' = i\<close> \<open>N'' = ?N\<close> \<open>U'' = ?U\<close>
     \<open>D = C\<close> \<open>D' = C'\<close> \<open>NN = N\<close> \<open>jj = C\<close> \<open>ii = i\<close> \<open>UU = U\<close> \<open>K = NN!C!k\<close> \<open>E = twl_clause_of D'\<close>
     \<open>NNNNNN = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#}\<close>
     \<open>UUUUUU = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (drop (Suc U) N)#}\<close>
     \<open>F = D' ! i\<close>
     and k_le: \<open>k < length (NN!C)\<close>
    for k k'' i' jj ii :: nat and N'' U'' NN UU K and D D' E NNNNNN UUUUUU F
  proof cases
    obtain k' where k': \<open>k = Suc (Suc k')\<close>
      using k_2 by (cases k; cases \<open>k - 1\<close>) auto
    assume J_NP: \<open>C \<le> U\<close>

    have L_L'_UW_N: \<open>C' \<in> set (take U (tl N))\<close>
    proof -
      have f1: "\<And>ls lss. length ((ls::'v clause_l) # lss) = Suc (length lss)"
        by simp
      have f2: "\<And>ls lsa lss. (ls::'v clause_l) \<noteq> lsa \<or> lsa \<in> set (ls # lss)"
        by simp
      have "\<And>ls lss. take (Suc 0) ((ls::'v clause_l) # lss) = [] @ [ls]"
        by simp
      then show ?thesis
        using f2 f1 by (metis (no_types) C_le_N(1) C_le_N(2) J_NP N_C_C' drop_all_conc in_set_dropD
            length_0_conv set_take_subset_set_take subset_code(1) take_Suc_conv_app_nth take_eq_Nil
            take_tl tl_append2)
    qed
    have TWL_L_L'_UW_N: \<open>TWL_Clause {#?L, ?L'#} (mset ?UW) \<in># twl_clause_of `# mset (take U (tl N))\<close>
      using imageI[OF L_L'_UW_N, of twl_clause_of] watched_C' by auto
    have C_le_U: \<open>C - Suc 0 < length (take U (tl N))\<close>
      using \<open>C < length N\<close> \<open>C > 0\<close> J_NP by auto
    have \<open>k' < length (drop 2 C')\<close>
      using N_C_C' k' k_le by auto
    then have H0: \<open>TWL_Clause {#?UW ! k', ?L'#} (mset (list_update ?UW k' ?L)) =
      update_clause (TWL_Clause {#?L, ?L'#} (mset ?UW)) ?L (?UW ! k')\<close>
      using i k_le k' by (auto simp: mset_update)

    have H1: \<open>mset (watched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := L])) =
        {#C' ! Suc (Suc k'), C' ! (Suc 0 - i)#}\<close>
      using k_le k_2 i by (auto simp: take_2_if N_C_C')
    have H2: \<open>mset (unwatched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := L])) =
      add_mset (L) (remove1_mset (C' ! Suc (Suc k')) (mset (unwatched_l C')))\<close>
      using k_le k_2 i k' by (auto simp: drop_update_swap N_C_C' mset_update)
    have H3:  \<open>{#L, C' ! (Suc 0 - i)#} = mset (watched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 \<open>C < length N\<close> \<open>C > 0\<close> C'_i i by (auto simp: take_2_if N_C_C' nth_tl simp del: C'_i)
    have H4: \<open>mset (unwatched_l C') = mset (unwatched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> by (auto simp: take_2_if N_C_C' nth_tl)
    let ?New_C = \<open>(TWL_Clause {#L, C' ! (Suc 0 - i)#} (mset (unwatched_l C')))\<close>
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _
          \<open>(add_mset (update_clause ?C' L (C' ! k))
                     (remove1_mset ?C' (twl_clause_of `# mset (take U (tl N)))),
            {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (drop (Suc U) N)#})\<close>])
      using update_clauses.intros(1)[OF TWL_L_L'_UW_N, of ?U ?L \<open>C'!k\<close>]
      using \<open>C > 0\<close> \<open>C < length N\<close>
      using J_NP C_le_U by (auto simp: mset_update
          image_mset_remove1_mset_if H1 H2 H3[symmetric] H4[symmetric]
          L_L'_UW_N H0 TWL_L_L'_UW_N k' C'[symmetric] N_C_C' mset_watched_C watched_C' nth_tl
      tl_update_swap swap_def simp del: watched_l.simps unwatched_l.simps)
  next
    obtain k' where k': \<open>k = Suc (Suc k')\<close>
      using k_2 by (cases k; cases \<open>k - 1\<close>) auto
    assume J_NP: \<open>\<not>C \<le> U\<close>
    then have L_L'_UW_N: \<open>C' \<in> set (drop (Suc U) N)\<close>
      using C_le_N unfolding N_C_C'[symmetric] by (auto simp: in_set_drop_conv_nth not_less_eq_eq)
    have TWL_L_L'_UW_N: \<open>TWL_Clause {#?L, ?L'#} (mset ?UW) \<in># twl_clause_of `# mset (drop (Suc U) N)\<close>
      using imageI[OF L_L'_UW_N, of twl_clause_of] watched_C' by auto
    have \<open>k' < length (drop 2 C')\<close>
      using N_C_C' k' k_le by auto
    then have H0: \<open>TWL_Clause {#?UW ! k', ?L'#} (mset (list_update ?UW k' ?L)) =
      update_clause (TWL_Clause {#?L, ?L'#} (mset ?UW)) ?L (?UW ! k')\<close>
      using i k_le k' by (auto simp: mset_update)

    have H1: \<open>mset (watched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := L])) =
        {#C' ! Suc (Suc k'), C' ! (Suc 0 - i)#}\<close>
      using k_le k_2 i by (auto simp: take_2_if N_C_C')
    have H2: \<open>mset (unwatched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := L])) =
      add_mset (L) (remove1_mset (C' ! Suc (Suc k')) (mset (unwatched_l C')))\<close>
      using k_le k_2 i k' by (auto simp: drop_update_swap N_C_C' mset_update)
    have H3:  \<open>{#L, C' ! (Suc 0 - i)#} = mset (watched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> C'_i i_def by (auto simp: take_2_if N_C_C' nth_tl)
    have H4: \<open>mset (unwatched_l C') = mset (unwatched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> by (auto simp: take_2_if N_C_C' nth_tl)
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>({#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#},
            add_mset (update_clause (TWL_Clause {#L, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (L) (C' ! k))
            (remove1_mset (TWL_Clause {#L, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (twl_clause_of `# mset (drop (Suc U) N))))\<close>])
      using update_clauses.intros(2)[OF TWL_L_L'_UW_N, of ?N ?L \<open>C'!k\<close>]
      using \<open>C > 0\<close> \<open>C < length N\<close>
      using J_NP by (auto simp: mset_update not_less_eq_eq
          image_mset_remove1_mset_if H1 H2 H3[symmetric] H4[symmetric]
          L_L'_UW_N TWL_L_L'_UW_N k' C'[symmetric] N_C_C' mset_watched_C watched_C' nth_tl
          watched_l.simps[symmetric] unwatched_l.simps[symmetric] drop_update_swap
          tl_update_swap swap_def simp del: watched_l.simps unwatched_l.simps)
  qed

  have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of S')\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have \<open>distinct_mset (mset (take 2 (N!C)) + mset (drop 2 (N!C)))\<close>
    using C'_N_U_or unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def S
    by (auto simp add: cdcl\<^sub>W_restart_mset_state C' S distinct_mset_set_def)
  then have distinct_C': \<open>distinct C'\<close>
    unfolding mset_append[symmetric] append_take_drop_id N_C_C' by simp

  have jC_notin_WS: \<open>C \<notin># remove1_mset C WS\<close>
    by (meson dist_WS distinct_mem_diff_mset multi_member_last)
  have i_def': \<open>(if (N ! C) ! 0 = L then 0 else 1) = i\<close>
    unfolding i_def C' S by auto
  have new_lit_not_defined:
    \<open>-N ! C ! the i \<notin> lits_of_l M\<close>
   if
     \<open>i \<noteq> None\<close> and
     \<open>\<not> (\<forall>L\<in>#unwatched (twl_clause_of C'). - L \<in> lits_of_l (convert_lits_l N M))\<close> and
     \<open>\<forall>j. i = Some j \<longrightarrow> j < length (N ! C) \<and> (undefined_lit M (N ! C ! j) \<or> N ! C ! j \<in> lits_of_l M) \<and> 2 \<le> j\<close>
    for L' f i K N'
    using that by (auto simp: Decided_Propagated_in_iff_in_lits_of_l dest: consistent)
  have conclusion_refinement:
    \<open>((M, N[C := swap (N ! C) i (the f)], U, D, NP, UP, remove1_mset C WS, Q),
      convert_lits_l N M, N', U', D, NP, UP,
       {#(L, TWL_Clause (mset (take 2 (N ! j))) (mset (drop 2 (N ! j)))). j \<in># remove1_mset C WS#},
       Q)
    \<in> {(S, S'). twl_st_of (Some L) S = S' \<and> additional_WS_invs S}\<close>
    if
      val_L'_not_True: \<open>val_L \<noteq> Some True\<close> and
      L'_notin_trail: \<open>L' \<notin> lits_of_l (convert_lits_l N M)\<close> and
      case_f_of: \<open>False = (\<forall>L\<in>set (unwatched_l (N ! C)). - L \<in> lits_of_l M)\<close> and
      not_forall_unwatched_defined: \<open>f \<noteq> None\<close> and
      fst_F_not_None: \<open>\<not> (\<forall>L\<in>#unwatched (twl_clause_of C'). - L \<in> lits_of_l (convert_lits_l N M))\<close> and
      not_forall_unwatched_in_trail: \<open>(\<forall>L\<in>#mset (unwatched_l (N ! C)). - L \<in> lits_of_l M) = False\<close> and
      snd_le_length: \<open>the f < length (N ! C)\<close> and
      N_C_K: \<open>N ! C ! the f \<in># mset (unwatched_l (N ! C))\<close> and
      upd_spec:
        \<open>(N[C := swap (N ! C) i (the f)], N', U')
        \<in> {(N, N', U'). N' = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#} \<and>
          U' = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (drop (Suc U) N)#}}\<close> and
        \<open>(val_L = None) = undefined_lit M (N ! C ! (1 - i))\<close>
        \<open>(\<forall>L\<in>#mset (unwatched_l (N ! C)). - L \<in> lits_of_l M) = False\<close>
        \<open>\<forall>j. f = Some j \<longrightarrow> j < length (N ! C) \<and> (undefined_lit M (N ! C ! j) \<or> N ! C ! j \<in> lits_of_l M) \<and> 2 \<le> j\<close>
        \<open>N ! C ! the f \<in># mset (unwatched_l (N ! C))\<close>
        \<open>- N ! C ! the f \<notin> lits_of_l M\<close>
        \<open>False = (N ! C ! (1 - i) \<in> lits_of_l M)\<close>
        \<open>(val_L = Some False) = (- N ! C ! (1 - i) \<in> lits_of_l M)\<close>
     for L' val_L f K N' U'
  proof -
    have \<open>Propagated K C \<notin> set M\<close> for K
    proof (rule ccontr)
      assume propa: \<open>\<not> ?thesis\<close>
      have propa': \<open>Propagated K (mset C') \<in> set (convert_lits_l N M)\<close>
        using imageI[OF propa[simplified], of \<open>convert_lit N\<close>] \<open>C > 0\<close>
        by (simp add: convert_lits_l_def N_C_C')
      from split_list[OF propa'] obtain M1 M2 where
        M1: \<open>convert_lits_l N M = M2 @ Propagated K (mset C') # M1\<close>
        by blast
      have \<open>\<forall>L mark a b. a @ Propagated L mark # b = trail (state\<^sub>W_of S') \<longrightarrow>
          b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
        using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by fast
      then have \<open>M1 \<Turnstile>as CNot (remove1_mset K (mset C'))\<close>
        by (auto simp: S trail.simps M1)
      from true_annots_append_l[OF this, of \<open>M2 @ [Propagated K (mset C')]\<close>]
      have \<open>convert_lits_l N M \<Turnstile>as CNot (remove1_mset K (mset C'))\<close>
        unfolding M1 by simp
      moreover {
        have \<open>K \<in> set (take 2 C')\<close>
          using add_inv propa \<open>C > 0\<close> by (auto simp: S additional_WS_invs_def C')
        with distinct_C' have \<open>K \<notin> set (drop 2 C')\<close>
          by (subst (asm)(1) append_take_drop_id[of 2, symmetric], subst (asm) distinct_append)
            auto }
      ultimately have \<open>\<forall>L\<in>#unwatched (twl_clause_of C'). - L \<in> lits_of_l (convert_lits_l N M)\<close>
        unfolding true_annots_true_cls_def_iff_negation_in_model
        by (metis in_remove1_mset_neq in_set_dropD set_mset_mset unwatched_l.elims
            unwatched_twl_clause_of)
      then show False
        using not_forall_unwatched_in_trail by (auto simp: N_C_C')
    qed
    then have \<open>additional_WS_invs (M, N[C := swap (N ! C) i (the f)], U, D, NP, UP, remove1_mset C WS, Q)\<close>
      using add_inv S by (auto simp add: additional_WS_invs_def N_C_C' nth_list_update'
          dest: in_diffD)
    moreover {
      have \<open>the f < length C'\<close>
        using snd_le_length by (auto simp: N_C_C')
      then have \<open>convert_lit N x = convert_lit (N[C := swap (N ! C) i (the f)]) x\<close>
          if \<open>x \<in> set M\<close> for x
        using i two_le_length_C by (cases x) (auto simp: nth_list_update' swap_def N_C_C'
            mset_update simp del: C'_i)
      then have \<open>convert_lits_l N M = convert_lits_l (N[C := swap (N ! C) i (the f)]) M\<close>
        unfolding convert_lits_l_def by auto }
    moreover have \<open>{#(L, TWL_Clause (mset (take 2 (N ! j))) (mset (drop 2 (N ! j)))).
          j \<in># remove1_mset C WS#} =
        {#(L,
          TWL_Clause
           (mset (take 2 (N[C := swap (N ! C) i (the f)] ! j)))
           (mset (drop 2 (N[C := swap (N ! C) i (the f)] ! j)))).
          j \<in># remove1_mset C WS#}\<close>
      by (rule image_mset_cong) (use jC_notin_WS in \<open>auto simp: nth_list_update' swap_def\<close>)
    ultimately show ?thesis
      using upd_spec by simp
  qed
  have H: \<open>unit_propagation_inner_loop_body_l L C ?S \<le>
    \<Down> {(S, S'). twl_st_of (Some L) S = S' \<and> additional_WS_invs S} (unit_propagation_inner_loop_body
    (?L, twl_clause_of C') (twl_st_of (Some L) ?S))\<close>
    unfolding unit_propagation_inner_loop_body_l_def unit_propagation_inner_loop_body_def
      S'_S[unfolded S] S' st_of_S' S option.case_eq_if
    apply (rewrite at \<open>let _ =  _ ! _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = if _ ! _ = _then _ else _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ =  (_ ! _, _) in _\<close> Let_def)
    apply (refine_rcg bind_refine_spec[where M' = \<open>find_unwatched _ _\<close>, OF _ find_unwatched]
        bind_refine_spec[where M' = \<open>RETURN (valued _ _)\<close>, OF _ valued_spec[]]
        update_clause_ll_spec
        case_prod_bind[of _ \<open>If _ _\<close>]; remove_dummy_vars)
    unfolding i_def'
    subgoal using n_d by simp
    subgoal using C_le_N by fast
    subgoal using i two_le_length_C unfolding N_C_C' by auto
    subgoal using i two_le_length_C unfolding N_C_C' by auto
    subgoal using i two_le_length_C unfolding N_C_C' by auto
    subgoal by (auto simp: mset_watched_C watched_C' in_set_unwatched_conv C'[symmetric] N_C_C'
          consistent split: option.splits bool.splits simp del: watched_l.simps unwatched_l.simps)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv C'[symmetric] N_C_C'
          consistent split: option.splits bool.splits simp del: watched_l.simps unwatched_l.simps)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv C'[symmetric] N_C_C'
          consistent split: option.splits bool.splits simp del: watched_l.simps unwatched_l.simps)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv C'[symmetric] N_C_C'
          consistent split: option.splits bool.splits simp del: watched_l.simps unwatched_l.simps)
    subgoal using init_invs by (simp add: S)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv C'[symmetric] N_C_C'
          consistent split: option.splits bool.splits)
    subgoal by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)
    subgoal using add_inv S stgy_inv struct_invs add_mset_C'_i
      by (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv consistent
        Decided_Propagated_in_iff_in_lits_of_l
          additional_WS_invs_def C'[symmetric] N_C_C' split: option.splits bool.splits)
    subgoal using init_invs S C_le_N add_mset_C'_i dist_WS by (vc_solve simp: mset_watched_C
          in_set_unwatched_conv set_take_2_watched watched_C' consistent additional_WS_invs_def
          N_C_C' split: option.splits bool.splits dest: in_diffD)
    subgoal for L' f f' by force
    subgoal
      apply (rule RETURN_rule)
      apply (use consistent in \<open>vc_solve simp: Decided_Propagated_in_iff_in_lits_of_l C'[symmetric]
          N_C_C'\<close>)
      by (meson in_set_drop_conv_nth)
    subgoal using C'_N_U S by (auto simp add: C'[symmetric] N_C_C')
    subgoal by (simp; fail)
    subgoal by auto
    subgoal by (auto simp: in_set_drop_conv_nth)
    subgoal for L' f D K N' by (rule new_lit_not_defined) assumption+
    subgoal for L' val_L f K N' U'
      by (rule conclusion_refinement) assumption+
    done

  have *: \<open>unit_propagation_inner_loop_body (C' ! i, twl_clause_of C')
   (set_clauses_to_update (remove1_mset (C' ! i, twl_clause_of C') (clauses_to_update S')) S')
   \<le> SPEC (\<lambda>S''. twl_struct_invs S'' \<and>
                 twl_stgy_invs S'' \<and>
                 cdcl_twl_cp\<^sup>*\<^sup>* S' S'' \<and>
              (S'', S') \<in> measure (size \<circ> clauses_to_update))\<close>
    apply (rule unit_propagation_inner_loop_body(1)[of S' \<open>(C' ! i, twl_clause_of C')\<close>])
    using imageI[OF WS, of \<open>(\<lambda>j. (L, twl_clause_of (N ! j)))\<close>]
      struct_invs stgy_inv D_None WS by (auto simp: N_C_C' S)
  have H': \<open>unit_propagation_inner_loop_body (?L, twl_clause_of C') (twl_st_of (Some L) ?S) \<le>
    SPEC (\<lambda>S'. twl_stgy_invs S' \<and> twl_struct_invs S')\<close>
    using * unfolding conj.left_assoc upd_S_S'
    by (simp add: weaken_SPEC)
  have \<open>unit_propagation_inner_loop_body_l L C ?S
    \<le> \<Down> {(S, S'). (twl_st_of (Some L) S = S' \<and> additional_WS_invs S) \<and>
           (twl_stgy_invs S' \<and> twl_struct_invs S')}
         (unit_propagation_inner_loop_body (?L, twl_clause_of C') (twl_st_of (Some L) ?S))\<close>
    apply (rule refine_add_invariants)
     apply (rule H')
    by (rule H)
  then show ?thesis unfolding upd_S_S' by simp
qed

lemma unit_propagation_inner_loop_body_l2:
  assumes
    WS: \<open>C \<in># clauses_to_update_l S\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of (Some L) S)\<close> and
    add_inv: \<open>additional_WS_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs (twl_st_of (Some L) S)\<close>
  shows
    \<open>(unit_propagation_inner_loop_body_l L C
        (set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S),
      unit_propagation_inner_loop_body (L, twl_clause_of (get_clauses_l S ! C))
        (set_clauses_to_update
          (remove1_mset (L, twl_clause_of (get_clauses_l S ! C))
          (clauses_to_update (twl_st_of (Some L) S))) (twl_st_of (Some L) S)))
    \<in> \<langle>{(S, S'). twl_st_of (Some L) S = S' \<and> additional_WS_invs S \<and> twl_stgy_invs S' \<and>
         twl_struct_invs S'}\<rangle>nres_rel\<close>
  using unit_propagation_inner_loop_body_l[OF assms]
  by (auto simp: nres_rel_def)

definition select_from_clauses_to_update :: \<open>'v twl_st_l \<Rightarrow> ('v twl_st_l \<times> nat) nres\<close> where
  \<open>select_from_clauses_to_update S = SPEC (\<lambda>(S', C). C \<in># clauses_to_update_l S \<and>
     S' = set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S)\<close>

definition unit_propagation_inner_loop_l :: "'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>unit_propagation_inner_loop_l L S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of (Some L) S) \<and> twl_stgy_invs (twl_st_of (Some L) S) \<and>
    cdcl_twl_cp\<^sup>*\<^sup>* (twl_st_of (Some L) S\<^sub>0) (twl_st_of (Some L) S) \<and>
    additional_WS_invs S\<^esup>
      (\<lambda>S. clauses_to_update_l S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT (clauses_to_update_l S \<noteq> {#});
        (S', C) \<leftarrow> select_from_clauses_to_update S;
        unit_propagation_inner_loop_body_l L C S'
      })
      S\<^sub>0
  \<close>

lemma set_mset_clauses_to_update_l_set_mset_clauses_to_update_spec:
  \<open>RES (set_mset (clauses_to_update_l S)) \<le> \<Down> {(C, (L', C')). L' = L \<and>
    C' = twl_clause_of (get_clauses_l S ! C)}
  (RES (set_mset (clauses_to_update (twl_st_of (Some L) S))))\<close>
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
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(T, T'). T' = h T \<and> P' T}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> \<langle>{(T, T'). ?H T T' \<and> P' T}\<rangle> nres_rel\<close>)
  assumes
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q T)\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(T, T'). ?H T T' \<and> P' T \<and> Q (h T)}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma refine_add_inv_generalised:
  fixes f :: \<open>'a \<Rightarrow> 'b nres\<close> and f' :: \<open>'c \<Rightarrow> 'd nres\<close>
  assumes
    \<open>(f', f) \<in> A \<rightarrow> \<langle>B\<rangle> nres_rel\<close>
  assumes
    \<open>\<And>S S'. (S, S') \<in> A \<Longrightarrow> f S' \<le> RES C\<close>
  shows
    \<open>(f', f) \<in> A \<rightarrow> \<langle>{(T, T'). (T, T') \<in> B \<and> T' \<in> C}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
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
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma clauses_to_update_l_empty_tw_st_of_Some_None[simp]:
  \<open>clauses_to_update_l S = {#} \<Longrightarrow> twl_st_of (Some L) S = twl_st_of None S\<close>
  by (cases S) auto

lemma unit_propagation_inner_loop_l:
  \<open>(uncurry unit_propagation_inner_loop_l,  unit_propagation_inner_loop) \<in>
  {((L, S), S'). S' = twl_st_of (Some L) S \<and> twl_struct_invs (twl_st_of (Some L) S) \<and>
     twl_stgy_invs (twl_st_of (Some L) S) \<and> additional_WS_invs S} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and>
    additional_WS_invs T \<and> twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T)}\<rangle>
  nres_rel\<close>
  (is \<open>?unit_prop_inner \<in> _\<close>)
proof -
  have SPEC_remove: \<open>select_from_clauses_to_update S
       \<le> \<Down> {((T', C), C').
             set_clauses_to_update (clauses_to_update S'' - {#C'#}) S'' = twl_st_of (Some L) T' \<and>
              T' = set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S \<and>
              C' \<in># clauses_to_update S'' \<and>
              C \<in># clauses_to_update_l S \<and>
              snd C' = twl_clause_of (get_clauses_l S ! C)}
             (SPEC (\<lambda>C. C \<in># clauses_to_update S''))\<close>
    if \<open>(S, S'') \<in> {(T, T'). T' = twl_st_of (Some L) T \<and> additional_WS_invs T}\<close> for S S'' L
    using that unfolding select_from_clauses_to_update_def
    by (cases S; cases S'') (auto simp: conc_fun_def image_mset_remove1_mset_if)
  have H: \<open>(uncurry unit_propagation_inner_loop_l, unit_propagation_inner_loop) \<in>
  {((L, S), S'). S' = twl_st_of (Some L) S \<and> twl_struct_invs (twl_st_of (Some L) S) \<and>
     twl_stgy_invs (twl_st_of (Some L) S) \<and> additional_WS_invs S} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and> additional_WS_invs T}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
    unfolding unit_propagation_inner_loop_l_def unit_propagation_inner_loop_def uncurry_def
      (* select_from_clauses_to_update_def *)
    apply clarify
    subgoal for L M' N' U' C' NP' UP' WS' Q' M N U C NP UP WS Q
    apply (refine_vcg set_mset_clauses_to_update_l_set_mset_clauses_to_update_spec
      WHILEIT_refine_genR[where R=\<open>?B\<close> and R' = \<open>{(T, T'). T' = twl_st_of (Some L) T \<and>
        additional_WS_invs T}\<close>]
      SPEC_remove;
      remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal for T T' LC S'' iC
      apply (rule refinement_trans_long[OF _ _ _ unit_propagation_inner_loop_body_l[of \<open>iC\<close> T L,
        unfolded prod.collapse]])
      subgoal by auto
      subgoal by (cases T) auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
    subgoal by auto
    done
  done
  have H': \<open>?unit_prop_inner
  \<in> {((L, S), S'). S' = twl_st_of (Some L) S \<and> twl_struct_invs (twl_st_of (Some L) S) \<and>
      twl_stgy_invs (twl_st_of (Some L) S) \<and> additional_WS_invs S} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and> additional_WS_invs T \<and>
      twl_struct_invs T' \<and> twl_stgy_invs T' \<and> clauses_to_update T' = {#}}\<rangle>nres_rel\<close>
    apply (rule refine_add_inv_generalised[OF H, of \<open>Collect (\<lambda>S'. twl_struct_invs S' \<and>
      twl_stgy_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S' S' \<and> clauses_to_update S' = {#})\<close>, simplified])
    subgoal for LS S'
      using unit_propagation_inner_loop[of \<open>twl_st_of (Some (fst LS)) (snd LS)\<close>]
      by match_spec_trans auto
    done

  show ?thesis
    using H' apply -
    apply (match_spec; (match_fun_rel; match_fun_rel?)+)
    by blast+
qed

definition clause_to_update :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v clauses_to_update_l\<close>where
  \<open>clause_to_update L S =
    filter_mset
      (\<lambda>C::nat. L \<in> set (watched_l (get_clauses_l S ! C)))
      (mset [1..<length (get_clauses_l S)])\<close>

lemma distinct_mset_clause_to_update: \<open>distinct_mset (clause_to_update L C)\<close>
  unfolding clause_to_update_def
  apply (rule distinct_mset_filter)
  apply (subst distinct_mset_mset_distinct)
  apply auto
  done

lemma in_clause_to_updateD: \<open>b \<in># clause_to_update L' T \<Longrightarrow> b < length (get_clauses_l T) \<and> 0 < b\<close>
  by (auto simp: clause_to_update_def)

definition select_and_remove_from_literals_to_update :: "'v twl_st_l \<Rightarrow>
    ('v twl_st_l \<times> 'v literal) nres" where
  \<open>select_and_remove_from_literals_to_update S = SPEC(\<lambda>(S', L). L \<in># literals_to_update_l S \<and>
    S' = set_clauses_to_update_l (clause_to_update L S)
          (set_literals_to_update_l (literals_to_update_l S - {#L#}) S))\<close>

definition unit_propagation_outer_loop_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>unit_propagation_outer_loop_l S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
      clauses_to_update_l S = {#}\<^esup>
      (\<lambda>S. literals_to_update_l S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_l S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update S;
        unit_propagation_inner_loop_l L S'
      })
      (S\<^sub>0 :: 'v twl_st_l)
\<close>

lemma refine_pair_to_SPEC_fst_pair:
  fixes f :: \<open>'a \<Rightarrow> 's \<Rightarrow> 's nres\<close> and g :: \<open>'b \<Rightarrow> 'b nres\<close>
  assumes \<open>(uncurry f, g) \<in> {((L, S), S'). S' = h L S \<and> R L S} \<rightarrow>
    \<langle>{(S, S'). S' = h' S \<and> P' S}\<rangle>nres_rel\<close> (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R L S\<close> and [simp]: \<open>S' = h L S\<close>
  shows \<open>f L S \<le> \<Down> {(S, S'). S' = h' S \<and> P' S} (g S')\<close>
proof -
  have \<open>(f L S, g (h L S)) \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

lemma refine_pair_to_SPEC:
  fixes f :: \<open>'s \<Rightarrow> 's nres\<close> and g :: \<open>'b \<Rightarrow> 'b nres\<close>
  assumes \<open>(f, g) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). S' = h' S \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and [simp]: \<open>S' = h S\<close>
  shows \<open>f S \<le> \<Down> {(S, S'). S' = h' S \<and> P' S} (g S')\<close>
proof -
  have \<open>(f S, g (h S)) \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

lemma watched_twl_clause_of_watched: \<open>watched (twl_clause_of x) = mset (watched_l x)\<close>
  by (cases x) auto

lemma twl_st_of_clause_to_update:
  assumes \<open>twl_struct_invs (twl_st_of None T)\<close>
  shows
  \<open>twl_st_of (Some L')
     (set_clauses_to_update_l
       (clause_to_update L' T)
       (set_literals_to_update_l (remove1_mset L' (literals_to_update_l T)) T)) =
  set_clauses_to_update
      (Pair L' `# {#C \<in># get_clauses (twl_st_of None T). L' \<in># watched C#})
      (set_literals_to_update (remove1_mset L' (literals_to_update (twl_st_of None T)))
        (twl_st_of None T))\<close>
proof -
  obtain M N U D NP UP WS Q where
    T: \<open>T = (M, N, U, D , NP, UP, WS, Q)\<close>
    by (cases T) auto

  have watched_tl_N: \<open>\<exists>i j. watched_l x = [i, j]\<close> if \<open>x \<in> set (tl N)\<close> for x
  proof -
    have \<open>Multiset.Ball (twl_clause_of `# mset (tl N)) struct_wf_twl_cls\<close>
      using assms unfolding T twl_struct_invs_def twl_st_inv.simps twl_st_of.simps
      image_mset_union[symmetric] mset_append[symmetric] drop_Suc by auto
    then have \<open>struct_wf_twl_cls (twl_clause_of x)\<close>
      using that by auto
    then show ?thesis
      by (cases \<open>twl_clause_of x\<close>) (auto simp: length_list_2 take_2_if)
  qed
  have
    \<open>{#(L',
        TWL_Clause (mset (take 2 (N ! x)))
          (mset (drop 2 (N ! x)))).
      x \<in># mset_set {x. Suc 0 \<le> x \<and> x < length N \<and> L' \<in> set (take 2 (N ! x))}#} =
    Pair L' `#
      {#C \<in># {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take U (tl N))#} +
            {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc U) N)#}.
      L' \<in># watched C#}\<close>
    (is \<open>{#(L', ?C x). x \<in># mset_set ?S#} = Pair L' `# ?C'\<close>)
  proof -
    have mset_tl_upto: \<open>mset (tl N) = {#N!i. i \<in># mset_set {1..<length N}#}\<close>
      unfolding tl_drop_def mset_drop_upto by simp
    have L'': \<open>{#(L', ?C x). x \<in># mset_set ?S#} = Pair L' `# {#?C x. x \<in># mset_set ?S#}\<close>
      by auto
    also have \<open>\<dots> = Pair L' `# ?C'\<close>
      apply (rule arg_cong[of _ _ \<open>op `# (Pair L')\<close>])
      unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc append_take_drop_id
        mset_tl_upto by (auto simp: image_mset_filter_swap2)
    finally show ?thesis .
  qed
  then show ?thesis
    by (auto simp del: filter_union_mset simp: T split_beta clause_to_update_def split: if_splits)
qed

lemma additional_WS_invs_set_clauses_to_update_iff:
  assumes \<open>additional_WS_invs T\<close>
  shows \<open>additional_WS_invs (set_clauses_to_update_l WS (set_literals_to_update_l Q T)) \<longleftrightarrow>
     ((\<forall>x\<in>#WS.
         case x of C \<Rightarrow>
           C < length (get_clauses_l T) \<and>
           0 < C) \<and>
     distinct_mset WS)\<close>
proof -
  obtain M N U C NP UP WS Q where
    T: \<open>T = (M, N, U, C, NP, UP, WS, Q)\<close>
    by (cases T) auto
  show ?thesis
    using assms
    unfolding additional_WS_invs_def T by simp
qed

lemma unit_propagation_outer_loop_l_spec:
  \<open>(unit_propagation_outer_loop_l, unit_propagation_outer_loop) \<in>
  {(S, S'). S' = twl_st_of None S \<and> twl_struct_invs (twl_st_of None S) \<and>
    twl_stgy_invs (twl_st_of None S) \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#} \<and>
    get_conflict_l S = None} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of None T \<and>
    (additional_WS_invs T \<and> twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
          clauses_to_update_l T = {#}) \<and>
    literals_to_update (twl_st_of None T) = {#} \<and> clauses_to_update (twl_st_of None T) = {#} \<and>
    no_step cdcl_twl_cp (twl_st_of None T)}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
proof -
  have H:
   \<open>select_and_remove_from_literals_to_update x
       \<le> \<Down> {((S', L'), L). L = L' \<and>  S' = set_clauses_to_update_l (clause_to_update L x)
              (set_literals_to_update_l (remove1_mset L (literals_to_update_l x)) x)}
           (SPEC (\<lambda>L. L \<in># literals_to_update x'))\<close>
     if \<open>x' = twl_st_of None x\<close> for x :: \<open>'v twl_st_l\<close> and x' :: \<open>'v twl_st\<close>
    using that unfolding select_and_remove_from_literals_to_update_def
    apply (cases x; cases x')
    unfolding conc_fun_def by (clarsimp simp add: conc_fun_def)
  have H:
    \<open>(unit_propagation_outer_loop_l, unit_propagation_outer_loop) \<in>?R \<rightarrow>
      \<langle>{(S, S').
          S' = twl_st_of None S \<and>
          clauses_to_update_l S = {#} \<and>
          additional_WS_invs S \<and>
          twl_struct_invs (twl_st_of None S) \<and>
          twl_stgy_invs (twl_st_of None S)}\<rangle> nres_rel\<close>
    unfolding unit_propagation_outer_loop_l_def unit_propagation_outer_loop_def
    apply (refine_vcg unit_propagation_inner_loop_l[THEN refine_pair_to_SPEC_fst_pair] H)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: literals_to_update_l_literals_to_update)
    subgoal by (auto simp: literals_to_update_l_literals_to_update)
    subgoal by (auto simp add: twl_st_of_clause_to_update
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs)
    subgoal by (auto simp add: twl_st_of_clause_to_update
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs)
    subgoal for S S' T T' L L'
      by (clarsimp simp add: additional_WS_invs_set_clauses_to_update_iff
          distinct_mset_clause_to_update in_clause_to_updateD)
    subgoal
      by (auto simp add: twl_st_of_clause_to_update
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs)
    done
  show ?thesis
    apply (rule refine_add_inv)
    subgoal using H apply -
      apply (match_spec; (match_fun_rel; match_fun_rel?)+)
       apply blast+
      done
    subgoal for S
      apply (rule weaken_SPEC[OF unit_propagation_outer_loop[of \<open>twl_st_of None S\<close>]])
      apply ((auto simp: get_conflict_l_get_conflict; fail)+)[4]
      using no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp by blast
    done
qed

definition decide_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>decide_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). do {
     L \<leftarrow> SPEC (\<lambda>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))));
     RETURN (Decided L # M, N, U, D, NP, UP, WS, {#-L#})
  })
\<close>

lemma decide_l_spec:
  \<open>(decide_l, decide) \<in>
    {(S, S'). S' = twl_st_of None S \<and> twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
        additional_WS_invs S \<and> clauses_to_update_l S = {#} \<and> literals_to_update (twl_st_of None S) = {#} \<and>
        get_conflict (twl_st_of None S) = None} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of None T \<and> additional_WS_invs T \<and>
    (twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
    clauses_to_update_l T = {#} \<and> get_conflict (twl_st_of None T) = None)}\<rangle> nres_rel\<close>
  (is \<open>?C \<in> ?R \<rightarrow> ?inv\<close>)
proof -
  have
    \<open>(decide_l, decide) \<in> ?R \<rightarrow> \<langle>{(T, T'). T' = twl_st_of None T \<and> (additional_WS_invs T \<and>
    clauses_to_update_l T = {#})}\<rangle> nres_rel\<close>
    apply clarify
    unfolding decide_l_def decide_def
    by refine_vcg (auto simp: additional_WS_invs_def)
  then have
    \<open>(decide_l, decide) \<in> ?R \<rightarrow>  \<langle>{(T, T'). T' = twl_st_of None T \<and>
    (additional_WS_invs T \<and> clauses_to_update_l T = {#}) \<and>
    (twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
    get_conflict (twl_st_of None T) = None)}\<rangle> nres_rel\<close>
    apply (rule refine_add_inv)
    subgoal for S
      using decide_spec[of \<open>twl_st_of None S\<close>]
      apply (simp add: weaken_SPEC)
      done
    done
  then show ?thesis
    apply -
    apply (match_spec; (match_fun_rel; match_fun_rel?)+)
    by force+
qed

lemma get_conflict_l_get_conflict_state_spec:
  assumes \<open>S' = twl_st_of None S\<close> and \<open>additional_WS_invs S\<close> and \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>((get_conflict_l S = Some {#}, S), (get_conflict S' = Some {#}, S'))
  \<in> {((brk, S), (brk', S')). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and>
    clauses_to_update_l S = {#}}\<close>
  using assms by (auto simp: get_conflict_l_Some_nil_iff)

fun lit_and_ann_of_propagated where
  \<open>lit_and_ann_of_propagated (Propagated L C) = (L, C)\<close>

text \<open>
  We here strictly follow \<^term>\<open>cdcl\<^sub>W_restart_mset.skip\<close> and \<^term>\<open>cdcl\<^sub>W_restart_mset.resolve\<close>:
  if the level is 0, we should directly return \<^term>\<open>{#}\<close>. This would also avoid the
  \<^term>\<open>If (C = 0)\<close> condition.
  \<close>
definition skip_and_resolve_loop_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>skip_and_resolve_loop_l S\<^sub>0 =
    do {
      ASSERT(get_conflict_l S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv (twl_st_of None S\<^sub>0) (brk, twl_st_of None S) \<and>
         additional_WS_invs S \<and> clauses_to_update_l S = {#}\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_l S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, WS, Q) = S in
          do {
            ASSERT(M \<noteq> []);
            ASSERT(get_conflict_l (M, N, U, D, NP, UP, WS, Q) \<noteq> None);
            let D' = the (get_conflict_l (M, N, U, D, NP, UP, WS, Q));
            ASSERT(is_proped (hd (get_trail_l (M, N, U, D, NP, UP, WS, Q))));
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_l (M, N, U, D, NP, UP, WS, Q)));
            ASSERT(C < length N);
            if -L \<notin># D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, WS, Q))}
            else
              if get_maximum_level M (remove1_mset (-L) D') = count_decided M
              then
                do {RETURN (remove1_mset (-L) D' \<union># (if C = 0 then {#} else mset (remove1 L (N!C))) = {#},
                   (tl M, N, U, Some (remove1_mset (-L) D' \<union># (if C = 0 then {#} else mset (remove1 L (N!C)))),
                     NP, UP, WS, Q))}
              else
                do {RETURN (True, (M, N, U, D, NP, UP, WS, Q))}
          }
        )
        (get_conflict_l S\<^sub>0 = Some {#}, S\<^sub>0);
      RETURN S
    }
  \<close>

context
begin
private lemma skip_and_resolve_loop_l_index_le_length_N':
  \<open>additional_WS_invs (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
    ((brk''', M'', N'', U'', D'', NP'', UP'', WS'', Q''), brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''')
    \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#}} \<Longrightarrow>
    case (brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''') of (brk, S) \<Rightarrow> \<not> brk \<and> \<not> is_decided (hd (get_trail S)) \<Longrightarrow>
    M'' \<noteq> [] \<Longrightarrow>
    ((L', C'), L, C) \<in> {((L, C), L', C'). L = L' \<and> C' = (if C = 0 then {#L#}
       else mset (get_clauses_l (M'', N'', U'', D'', NP'', UP'', WS'', Q'') ! C))} \<Longrightarrow>
    lit_and_ann_of_propagated (hd (get_trail_l (M'', N'', U'', D'', NP'', UP'', WS'', Q''))) = (L', C') \<Longrightarrow>
    C' < length N''\<close>
  by (cases \<open>hd M''\<close>) (auto elim!: list_not_emptyE simp add: additional_WS_invs_def)

private lemma skip_and_resolve_l_refines:
  \<open>((brk''', M'', N'', U'', D'', NP'', UP'', WS'', Q''), brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''')
    \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#}} \<Longrightarrow>
    M''' \<noteq> [] \<Longrightarrow>
    ((L', C'), L, C) \<in> {((L, C), L', C'). L = L' \<and> C' = (if C = 0 then {#L#} else mset (get_clauses_l (M'', N'', U'', D'', NP'', UP'', WS'', Q'') ! C))} \<Longrightarrow>
    ((remove1_mset (- L') (the (get_conflict_l (M'', N'', U'', D'', NP'', UP'', WS'', Q''))) \<union># (if C' = 0 then {#} else mset (remove1 L' (N'' ! C'))) = {#}, tl M'', N'', U'',
      Some (remove1_mset (- L') (the (get_conflict_l (M'', N'', U'', D'', NP'', UP'', WS'', Q''))) \<union># (if C' = 0 then {#} else mset (remove1 L' (N'' ! C')))), NP'', UP'', WS'', Q''),
     remove1_mset (- L) (the (get_conflict (M''', N''', U''', D''', NP''', UP''', WS''', Q'''))) \<union># remove1_mset L C = {#}, tl M''', N''', U''',
     Some (remove1_mset (- L) (the (get_conflict (M''', N''', U''', D''', NP''', UP''', WS''', Q'''))) \<union># remove1_mset L C), NP''', UP''', WS''', Q''')
    \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#}}\<close>
  by (cases M'') (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def
      resolve_cls_l_nil_iff)

private lemma skip_and_resolve_l_count_decided:
  \<open>((brk''', M'', N'', U'', D'', NP'', UP'', WS'', Q''), brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''')
     \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#}} \<Longrightarrow>
  skip_and_resolve_loop_inv (twl_st_of None (M, N, U, D, NP, UP, WS, Q))
    (brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''') \<Longrightarrow>
  ((L', C'), L, C) \<in> {((L, C), L', C'). L = L' \<and> C' =
    (if C = 0 then {#L#} else mset (get_clauses_l (M'', N'', U'', D'', NP'', UP'', WS'', Q'') ! C))} \<Longrightarrow>
  (get_maximum_level M'' (remove1_mset (- L')
    (the (get_conflict_l (M'', N'', U'', D'', NP'', UP'', WS'', Q'')))) = count_decided M'') =
  (get_maximum_level M''' (remove1_mset (- L)
    (the (get_conflict (M''', N''', U''', D''', NP''', UP''', WS''', Q''')))) = count_decided M''')\<close>
  by (auto simp: skip_and_resolve_loop_inv_def)

private lemma skip_and_resolve_skip_refine:
  \<open>((brk''', M'', N'', U'', D'', NP'', UP'', WS'', Q''),
     brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''')
    \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and>
         clauses_to_update_l S = {#}} \<Longrightarrow>
  skip_and_resolve_loop_inv (twl_st_of None (M, N, U, D, NP, UP, WS, Q))
    (brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''') \<Longrightarrow>
  M'' \<noteq> [] \<Longrightarrow>
  ((False, tl M'', N'', U'', D'', NP'', UP'', WS'', Q''), False, tl M''', N''', U''', D''', NP''', UP''', WS''', Q''')
    \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#}}\<close>
  by (cases \<open>M''\<close>) (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def
          resolve_cls_l_nil_iff)

private lemma skip_and_resolve_l_not_conflict_iff:
  \<open>(M', N', U', D', NP', UP', WS', Q') = twl_st_of None (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
   additional_WS_invs (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
   ((brk''', M'', N'', U'', D'', NP'', UP'', WS'', Q''), brk'', M''', N''', U''', D''', NP''', UP''', WS''', Q''')
    \<in> {((brk, S), brk', S'). brk = brk' \<and> S' = twl_st_of None S \<and> additional_WS_invs S \<and> clauses_to_update_l S = {#}} \<Longrightarrow>
   ((L', C'), L, C) \<in> {((L, C), L', C'). L = L' \<and> C' =
     (if C = 0 then {#L#} else mset (get_clauses_l (M'', N'', U'', D'', NP'', UP'', WS'', Q'') ! C))} \<Longrightarrow>
   lit_and_ann_of_propagated (hd (get_trail_l (M'', N'', U'', D'', NP'', UP'', WS'', Q''))) = (L', C') \<Longrightarrow>
   (- L' \<notin># the (get_conflict_l (M'', N'', U'', D'', NP'', UP'', WS'', Q''))) \<longleftrightarrow>
      (- L \<notin># the (get_conflict (M''', N''', U''', D''', NP''', UP''', WS''', Q''')))\<close>
  by (auto simp: get_trail_twl_st_of_nil_iff additional_WS_invs_def)

lemma skip_and_resolve_loop_l_spec:
  \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop) \<in>
    {(S::'v twl_st_l, S'). S' = twl_st_of None S \<and> twl_struct_invs (twl_st_of None S) \<and>
       twl_stgy_invs (twl_st_of None S) \<and>
       additional_WS_invs S \<and> clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and>
       get_conflict (twl_st_of None S) \<noteq> None} \<rightarrow>
  \<langle>{(T, T'). T' = twl_st_of None T \<and> additional_WS_invs T \<and>
    (twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
    no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None T)) \<and>
    no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None T)) \<and>
    literals_to_update (twl_st_of None T) = {#} \<and>
    clauses_to_update_l T = {#} \<and> get_conflict (twl_st_of None T) \<noteq> None)}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow> _\<close>)
proof -
  text \<open>Stupid placeholder to help the application of \<open>rule\<close> later:\<close>
  define TT where [simp]: \<open>TT = (\<lambda>_::'v twl_st_l. True)\<close>
  have is_dec[iff]: \<open>is_decided (hd (get_trail (twl_st_of None S))) \<longleftrightarrow> is_decided (hd (get_trail_l S))\<close>
    if \<open>get_trail_l S \<noteq> []\<close> for S :: \<open>'v twl_st_l\<close>
    by (cases S, cases \<open>get_trail_l S\<close>; cases \<open>hd (get_trail_l S)\<close>)
      (use that in \<open>auto split: if_splits\<close>)
  have H: \<open>RETURN (lit_and_ann_of_propagated (hd (get_trail_l S)))
    \<le> \<Down> {((L, C), (L', C')). L = L' \<and> C' = (if C = 0 then {#L#} else mset (get_clauses_l S! C))}
    (SPEC (\<lambda>(L, C). Propagated L C = hd (get_trail S')))\<close>
    if [simp]: \<open>S' = twl_st_of None S\<close> and \<open>get_trail_l S \<noteq> []\<close> and
      p: \<open>is_proped (hd (get_trail_l S))\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
    using that apply (cases S; cases S'; cases \<open>get_trail_l S\<close>; cases \<open>hd (get_trail_l S)\<close> ;
        cases \<open>get_trail S'\<close>; cases \<open>hd (get_trail S')\<close>)
                   apply ((solves \<open>auto split: if_splits\<close>)+)[15]
    unfolding RETURN_def
    apply (rule RES_refine)
    by (auto split: if_splits)
  have H:
    \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop) \<in>
    ?R \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of None T \<and> additional_WS_invs T \<and> clauses_to_update_l T = {#}}\<rangle> nres_rel\<close>
    supply [[goals_limit=1]]
    apply clarify
    unfolding skip_and_resolve_loop_l_def skip_and_resolve_loop_def
    apply (refine_rcg get_conflict_l_get_conflict_state_spec H; remove_dummy_vars)
    subgoal by auto \<comment> \<open>conflict is not none\<close>
    subgoal by auto \<comment> \<open>loop invariant init: @{term skip_and_resolve_loop_inv}\<close>
    subgoal by auto \<comment> \<open>loop invariant init: @{term additional_WS_invs}\<close>
    subgoal by auto \<comment> \<open>loop invariant init: @{term \<open>clauses_to_update S = {#}\<close>}\<close>
    subgoal by (auto simp: skip_and_resolve_loop_inv_def get_trail_twl_st_of_nil_iff)
      \<comment> \<open>align loop conditions\<close>
    subgoal by auto
      \<comment> \<open>trail not empty\<close>
    subgoal by (auto simp: skip_and_resolve_loop_inv_def)
      \<comment> \<open>conflict not none\<close>
    subgoal by (auto simp: is_decided_no_proped_iff)
      \<comment> \<open>head of the trail is a propagation\<close>
    subgoal by fastforce
      \<comment> \<open>state equality\<close>
    subgoal by fastforce
      \<comment> \<open>trail not empty\<close>
    subgoal by (rule skip_and_resolve_loop_l_index_le_length_N') assumption
      \<comment> \<open>annotation of the valid\<close>
    subgoal by (rule skip_and_resolve_l_not_conflict_iff) assumption
    subgoal by (rule skip_and_resolve_skip_refine)
        \<comment> \<open>skip final invariants\<close>
    subgoal by (rule skip_and_resolve_l_count_decided)
        \<comment> \<open>maximum level\<close>

    subgoal by (rule skip_and_resolve_l_refines) \<comment> \<open>needs around 1 min\<close>
    subgoal by fastforce
    subgoal by fastforce
    done
  have H: \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop)
    \<in> ?R \<rightarrow>
       \<langle>{(T::'v twl_st_l, T').
         T' = twl_st_of None T \<and> (additional_WS_invs T \<and>
         clauses_to_update_l T = {#}) \<and>
         twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
         (no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None T))) \<and>
         (no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None T))) \<and>
         literals_to_update (twl_st_of None T) = {#} \<and>
         get_conflict (twl_st_of None T) \<noteq> None}\<rangle>nres_rel\<close>
    apply (rule refine_add_inv)
    subgoal by (rule H)
    subgoal for S
      using skip_and_resolve_loop_spec[of \<open>twl_st_of None S\<close>]
      apply (simp add: weaken_SPEC literals_to_update_l_literals_to_update)
      done
    done
  show ?thesis
    using H apply -
    apply (match_spec; (match_fun_rel; match_fun_rel?)+)
    by blast+
qed

end


lemma not_is_decidedE:
  \<open>\<not>is_decided E \<Longrightarrow> (\<And>K C. E = Propagated K C \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (cases E) auto


definition find_decomp :: "'v twl_st_l \<Rightarrow> 'v literal \<Rightarrow> ('v, nat) ann_lits nres" where
  \<open>find_decomp =  (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

definition find_lit_of_max_level :: "'v twl_st_l \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres" where
  \<open>find_lit_of_max_level =  (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    SPEC(\<lambda>L'. L' \<in># the D - {#-L#} \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>

definition ex_decomp_of_max_lvl :: "('v, nat) ann_lits \<Rightarrow> 'v cconflict \<Rightarrow> 'v literal \<Rightarrow> bool" where
  \<open>ex_decomp_of_max_lvl M D L \<longleftrightarrow> (\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (remove1_mset (-L) (the D)) + 1)\<close>


fun add_mset_list :: "'a list \<Rightarrow> 'a multiset multiset \<Rightarrow> 'a multiset multiset"  where
  \<open>add_mset_list L UP = add_mset (mset L) UP\<close>

definition (in -)list_of_mset :: \<open>'v clause \<Rightarrow> 'v clause_l nres\<close> where
  \<open>list_of_mset D = SPEC(\<lambda>D'. D = mset D')\<close>

fun extract_shorter_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause nres\<close>
   where
  \<open>extract_shorter_conflict_l (M, N, U, D, NP, UP, WS, Q) = SPEC(\<lambda>D'. D' \<subseteq># the D \<and>
     clause `# twl_clause_of `# mset (tl N) + NP + UP \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')\<close>

declare extract_shorter_conflict_l.simps[simp del]
lemmas extract_shorter_conflict_l_def = extract_shorter_conflict_l.simps

definition backtrack_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>backtrack_l S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0;
      ASSERT(M \<noteq> []);
      let L = lit_of (hd M);
      ASSERT(twl_stgy_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)));
      ASSERT(twl_struct_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)));
      ASSERT(no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None (M, N, U, D, NP, UP, WS, Q))));
      ASSERT(no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None (M, N, U, D, NP, UP, WS, Q))));
      ASSERT(D ~= None);
      ASSERT(-L \<in># the D);
      D' \<leftarrow> extract_shorter_conflict_l  (M, N, U, D, NP, UP, WS, Q);

      ASSERT(get_level M L = count_decided M);
      ASSERT(D' \<noteq> {#});
      ASSERT(ex_decomp_of_max_lvl M (Some D') L);
      ASSERT(-L \<in># D');
      M1 \<leftarrow> find_decomp (M, N, U, Some D', NP, UP, WS, Q) L;

      if size D' > 1
      then do {
        ASSERT(\<forall>L' \<in># D' - {#-L#}. get_level M L' = get_level M1 L');
        ASSERT(\<exists>L' \<in># D' - {#-L#}. get_level M L' = get_maximum_level M (D' - {#-L#}));
        ASSERT(get_level M L > get_maximum_level M (D' - {#-L#}));
        L' \<leftarrow> find_lit_of_max_level (M, N, U, Some D', NP, UP, WS, Q) L;
        ASSERT(L \<noteq> -L');
        D'' \<leftarrow> list_of_mset D';
        RETURN (Propagated (-L) (length N) # M1,
          N @ [[-L, L'] @ (remove1 (-L) (remove1 L' D''))], U,
          None, NP, UP, WS, {#L#})
      }
      else do {
        _ \<leftarrow> list_of_mset D';
        RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset D' UP, WS, {#L#})
     }
  }\<close>

lemma get_all_ann_decomposition_convert_lits_l:
  shows \<open>get_all_ann_decomposition (convert_lits_l N M) =
    map (\<lambda>(M, M'). (convert_lits_l N M, convert_lits_l N M')) (get_all_ann_decomposition M)\<close>
  apply (induction M rule: ann_lit_list_induct)
  subgoal by auto
  subgoal by auto
  subgoal for L m M by (cases \<open>get_all_ann_decomposition M\<close>) auto
  done

lemma get_level_convert_lits_l2[simp]:
  \<open>get_level (convert_lits_l N M') K = get_level M' K\<close>
  using get_level_convert_lits_l[of N M'] by simp

lemma additional_WS_invs_backtrack_iff:
  assumes
   \<open>additional_WS_invs (M2 @ M1', N', U', C1, NP', UP', WS', Q)\<close>
  shows \<open>additional_WS_invs (Propagated L D # M1',
      N' @ N'', U'', C2, NP''', UP''', {#}, Q') \<longleftrightarrow>
    ((D > 0 \<longrightarrow> L \<in> set (watched_l ((N' @ N'') ! D))) \<and> D < length (N' @ N'') \<and> U'' < length (N' @ N''))\<close>
  using assms unfolding additional_WS_invs_def by (auto 0 5 simp add: all_conj_distrib nth_append)

lemma mset_take_drep_tl_id[simp]:
  \<open>mset (take x1i (tl x1h)) + mset (drop (Suc x1i) x1h) = mset (tl x1h)\<close>
  unfolding mset_append[symmetric] drop_Suc append_take_drop_id ..

lemma image_filter_mset_take_drep_tl_id[simp]:
  \<open>{#f L. L \<in># mset (take x1i (tl x1h))#} + {#f L. L \<in># mset (drop (Suc x1i) x1h)#}=
   {#f L. L \<in># mset (tl x1h)#}\<close>
  unfolding image_mset_union[symmetric] mset_take_drep_tl_id ..


lemma backtrak_l_ge1_rule_refinement:
  assumes
    state: \<open>(M, N, U, D\<^sub>0, NP, UP, WS, Q) = twl_st_of None (M', N', U', D\<^sub>0', NP', UP', WS', Q')\<close> and
    D: \<open>(D'', D) \<in> {(D, D'). D = D' \<and> -lit_of (hd (get_trail_l  (M', N', U', D\<^sub>0', NP', UP', WS', Q'))) \<in># D \<and>
         D \<subseteq># the (Some E\<^sub>0)}\<close>and
    confl: \<open>get_conflict_l (M', N', U', D\<^sub>0', NP', UP', WS', Q') = Some E\<^sub>0\<close> and
    E\<^sub>0: \<open>Some E\<^sub>0 \<noteq> Some {#}\<close> and
    wq: \<open>clauses_to_update_l (M', N', U', D\<^sub>0', NP', UP', WS', Q') = {#}\<close> and
    add_invs: \<open>additional_WS_invs (M', N', U', D\<^sub>0', NP', UP', WS', Q')\<close> and
    M_ne_empty: \<open>M \<noteq> []\<close> and
    M'_ne_empty: \<open>M' \<noteq> []\<close> and
    L_hd: \<open>(lit_of (hd M'), L) \<in> Id\<close> and
    uL_D: \<open>- lit_of (hd M') \<in># D''\<close> and
    M1'_M1: \<open>(M1', M1) \<in> {(M1', M1). M1 = convert_lits_l N' M1' \<and>
       (\<exists>K M2. (Decided K # M1', M2) \<in> set (get_all_ann_decomposition M') \<and>
          get_level M' K = get_maximum_level M' (D - {#-lit_of (hd M')#}) + 1)}\<close> and
    M1': \<open>M1 \<in> {M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and> 
       get_level M K = get_maximum_level M (remove1_mset (- L) D) + 1}\<close> and
    L''_L''': \<open>(L'', L''') \<in> Id\<close> and
    L''': \<open>L''' \<in> {L'. L' \<in># remove1_mset (- L) D \<and> 
        get_level M L' = get_maximum_level M (remove1_mset (- L) D)}\<close> and
    L_uL''': \<open>L \<noteq> - L'''\<close> and
    no_clause_to_upd: \<open>clauses_to_update_l (M', N', U', D\<^sub>0', NP', UP', WS', Q') = {#}\<close> and
    L_uL'': \<open>lit_of (hd M') \<noteq> - L''\<close> and
    E'_D\<^sub>0': \<open>(E', D) \<in> {(c, D). D = mset c}\<close> 
  shows
    \<open>((Propagated (- lit_of (hd M')) (length N') # M1', N' @ [[- lit_of (hd M'), L''] @ remove1 (- lit_of (hd M')) (remove1 L'' E')], U', None, NP', UP', WS', unmark (hd M')),
      Propagated (- L) D # M1, N, add_mset (TWL_Clause {#- L, L'''#} (D - {#- L, L'''#})) U, None, NP, UP, WS, {#L#})
    \<in> {(T, T'). T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and> additional_WS_invs T}\<close>
proof -
  have hd_convert_lits_M': \<open>lit_of (hd (convert_lits_l N' M')) = lit_of (hd M')\<close>
    using state M'_ne_empty by (cases M') auto
  have \<open>L''' \<in># D\<close>
    using state confl L''_L''' L''' E\<^sub>0 E'_D\<^sub>0' by (cases E\<^sub>0; auto dest: in_diffD)
  then have E: \<open>D = add_mset K (add_mset L''' (D - {#K, L'''#}))\<close>
    if \<open>K \<in># D\<close> and \<open>K \<noteq> L'''\<close>
    for K
    using that by (auto simp: multiset_eq_iff)
  let ?L' = \<open>lit_of (hd M')\<close>
  obtain c M2 K where
    M': \<open>M' = c @ M2 @ Decided K # M1'\<close>
    using M1' M1'_M1 by (auto dest!: get_all_ann_decomposition_exists_prepend)
  define M'' where \<open>M'' = c @ M2 @ Decided K # []\<close>
  then have M'': \<open>additional_WS_invs (M'' @ M1',  N', U', D\<^sub>0', NP', UP', WS', Q')\<close>
    using M' add_invs by auto
  have hd_M'_hd_M: \<open>lit_of (hd M') = lit_of (hd M)\<close>
    using state M'_ne_empty by (cases M'; cases M) auto

  have uL''_E: \<open>- lit_of (hd (convert_lits_l N' M')) \<in># D\<close>
    using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
        \<open>state\<^sub>W_of (twl_st_of None (M', N', U', D\<^sub>0', NP', UP', WS', Q'))\<close>, simplified]
    using state confl L_hd uL_D D by (auto simp: hd_M'_hd_M)
  have \<open>x \<in> set M1' \<Longrightarrow>
          convert_lit N' x =
          convert_lit (N' @ [- lit_of (hd (map (convert_lit N') M')) # L''' # remove1 (- lit_of (hd (map (convert_lit N') M')))
          (remove1 L''' E')]) x\<close> for x
    using add_invs by (cases x) (auto simp: nth_append additional_WS_invs_def M')
  then have conv: \<open>convert_lits_l N' M1' =
          convert_lits_l (N' @ [- lit_of (hd (convert_lits_l N' M')) # L''' #
          remove1 (- lit_of (hd (convert_lits_l N' M'))) (remove1 L''' E')]) M1'\<close>
    unfolding convert_lits_l_def by auto
  have L''_L''': \<open>L''' = L''\<close>
    using L''_L''' by simp
  have L': \<open>L = lit_of (hd M')\<close> and L: \<open>lit_of (hd (convert_lits_l N' M')) = lit_of (hd M)\<close>
    using L_hd state by (cases M'; cases \<open>hd M'\<close>; simp_all; fail)+
  have L_L': \<open>L = ?L'\<close>
    using state M'_ne_empty L_hd by (cases M') auto
  then have L''_not_hd: \<open>lit_of (hd (convert_lits_l N' M')) \<noteq> - L''\<close>
    using L_uL'' E'_D\<^sub>0' by (simp add: uminus_lit_swap hd_convert_lits_M')
  have \<open>L \<noteq> -L'''\<close>
    using L_uL''' by auto
  moreover have E': \<open>D = add_mset (- lit_of (hd (convert_lits_l N' M')))
        (add_mset L''' (D - {#- lit_of (hd (convert_lits_l N' M')), L'''#}))\<close>
    by (rule E) (use L_uL''' uL''_E L''_not_hd L L_L' hd_M'_hd_M in \<open>auto\<close>)
  moreover have N': \<open>N' \<noteq> []\<close> and U': \<open>U' < length N'\<close>
    using add_invs by (auto simp: additional_WS_invs_def)
  ultimately have 1: \<open>((Propagated (- ?L') (length N') # M1',
      N' @ [[- ?L', L''] @ remove1 (- ?L') (remove1 L'' E')],
      U', None, NP', UP', WS', {#?L'#}), Propagated (- L) E # M1, N,
       add_mset (TWL_Clause {#- L, L'''#} (E - {#- L, L'''#})) U,
        None, NP, UP, WS, {#L#})
      \<in> {(T, T'). additional_WS_invs T}\<close>
    using no_clause_to_upd M'' conv
    by (simp add: additional_WS_invs_backtrack_iff cdcl\<^sub>W_restart_mset_state)

  have 2: \<open>((Propagated (- ?L') (length N') # M1',
        N' @ [[- ?L', L''] @ remove1 (- ?L') (remove1 L'' E')],
        U', None, NP', UP', WS', {#?L'#}),
        Propagated (- L) D # M1, N,
        add_mset (TWL_Clause {#- L, L'''#} (D - {#- L, L'''#})) U,
        None, NP, UP, WS, {#L#})
        \<in> {(T, T'). T' = twl_st_of None T}\<close>
    using state confl M1'_M1 L''_L''' N' E'[symmetric] conv[symmetric] U' conv[symmetric] E'_D\<^sub>0'
    by (auto simp add: L_L' hd_convert_lits_M' inres_def list_of_mset_def)
  have 3: \<open>((Propagated (- ?L') (length N') # M1', N' @ [[- ?L', L''] @ remove1 (- ?L') (remove1 L'' E')], U', None, NP', UP', WS', {#?L'#}),
     Propagated (- L) D # M1, N, add_mset (TWL_Clause {#- L, L'''#} (D - {#- L, L'''#})) U, None, NP, UP, WS, {#L#})
      \<in> {(T, T'). clauses_to_update_l T = {#}}\<close>
    using wq by auto
  show ?thesis using 1 2 3 by fast
qed

lemma backtrack_l_size0_rule_refinement:
  assumes
    state: \<open>(M, N, U, D\<^sub>0, NP, UP, WS, Q) = twl_st_of None (M', N', U', D\<^sub>0', NP', UP', WS', Q')\<close> and
    confl: \<open>get_conflict_l (M', N', U', D\<^sub>0', NP', UP', WS', Q') = Some E\<^sub>0\<close> and
    E\<^sub>0: \<open>Some E\<^sub>0 \<noteq> Some {#}\<close> and
    wq: \<open>clauses_to_update_l (M', N', U', D\<^sub>0', NP', UP', WS', Q') = {#}\<close> and
    add_invs: \<open>additional_WS_invs (M', N', U', D\<^sub>0', NP', UP', WS', Q')\<close> and
    M_ne_empty: \<open>M \<noteq> []\<close> and
    M'_ne_empty: \<open>M' \<noteq> []\<close> and
    L_hd: \<open>(lit_of (hd M'), L) \<in> Id\<close> and
    uL_D: \<open>- lit_of (hd M') \<in># D''\<close> and
    M1'_M1: \<open>(M1', M1) \<in> {(M1', M1). M1 = convert_lits_l N' M1' \<and>
       (\<exists>K M2. (Decided K # M1', M2) \<in> set (get_all_ann_decomposition M') \<and>
          get_level M' K = get_maximum_level M' (D - {#-lit_of (hd M')#}) + 1)}\<close> and
    M1': \<open>M1 \<in> {M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and> get_level M K =
       get_maximum_level M (remove1_mset (- L) D) + 1}\<close> and
    no_clause_to_upd: \<open>clauses_to_update_l (M', N', U', D\<^sub>0', NP', UP', WS', Q') = {#}\<close> and
    D: \<open>(D'', D) \<in> {(D, D'). D = D' \<and> 
          -lit_of (hd (get_trail_l (M', N', U', D\<^sub>0', NP', UP', WS', Q'))) \<in># D \<and>
          D \<subseteq># the (Some E\<^sub>0)}\<close> and
    length_D'_ge_1:\<open>\<not> 1 < size D''\<close> and
    size_D_ge_1: \<open>\<not> 1 < size D\<close>
  shows
    \<open>((Propagated (- lit_of (hd M')) 0 # M1', N', U', None, NP', add_mset D'' UP', WS', unmark (hd M')),
       Propagated (- L) D # M1, N, U, None, NP, add_mset D UP, WS, {#L#})
    \<in> {(T, T'). T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and> additional_WS_invs T}\<close>
proof -
  obtain c M2 K where
    M': \<open>M' = c @ M2 @ Decided K # M1'\<close>
    using M1'_M1 by (auto dest!: get_all_ann_decomposition_exists_prepend)
  let ?L' = \<open>lit_of (hd M')\<close>
  have hd_M'_hd_M: \<open>lit_of (hd M') = lit_of (hd M)\<close>
    using state M'_ne_empty by (cases M'; cases M) auto
  define M'' where \<open>M'' = c @ M2 @ Decided K # []\<close>
  then have M'': \<open>additional_WS_invs (M'' @ M1',  N', U', D\<^sub>0', NP', UP', WS', Q')\<close>
    using M' add_invs by auto
  have uL''_E: \<open>- lit_of (hd (convert_lits_l N' M')) \<in># D\<close>
    using state confl L_hd uL_D D by (auto simp: hd_M'_hd_M)
  let ?fg = \<open>((Propagated (- ?L') 0 # M1', N', U', None, NP', add_mset D'' UP', WS',
           unmark (hd M')),
        Propagated (- L) D # M1, N, U, None, NP, add_mset D UP, WS, {#L#})\<close>
  have 1: \<open>?fg \<in> {(T, T'). additional_WS_invs T}\<close>
    using M'' by (simp add: additional_WS_invs_def cdcl\<^sub>W_restart_mset_state)

  have \<open>D'' = mset [- lit_of (hd (convert_lits_l N' M'))]\<close> \<open>D = D''\<close>
    using D state confl L_hd uL_D size_D_ge_1 uL''_E by (cases D; simp_all add: hd_M'_hd_M)+
  then have 2: \<open>?fg \<in> {(T, T'). T' = twl_st_of None T}\<close>
    using state confl L_hd uL_D M1'_M1 by simp
  have 3: \<open>?fg \<in> {(T, T'). clauses_to_update_l T = {#}}\<close>
    using wq by auto
  show ?thesis using 1 2 3 by fast
qed

lemma lit_of_hd_convert_lits_l[simp]: \<open>M \<noteq> [] \<Longrightarrow> lit_of (hd (convert_lits_l N M)) = lit_of (hd M)\<close>
  by (cases M) auto

lemma backtrack_l_spec:
  \<open>(backtrack_l, backtrack) \<in>
    {(S::'v twl_st_l, S'). S' = twl_st_of None S \<and> get_conflict_l S \<noteq> None \<and> get_conflict_l S \<noteq> Some {#} \<and>
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> additional_WS_invs S \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None S)) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None S)) \<and>
       twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S)} \<rightarrow>
    \<langle>{(T::'v twl_st_l, T'). T' = twl_st_of None T \<and> get_conflict_l T = None \<and> additional_WS_invs T \<and>
       twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and> clauses_to_update_l T = {#} \<and>
       literals_to_update_l T \<noteq> {#}}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close>)
proof -
  have backtrack_def':
    \<open>backtrack S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        L \<leftarrow> SPEC(\<lambda>L. L = lit_of (hd M));
        D' \<leftarrow> extract_shorter_conflict (M, N, U, D, NP, UP, WS, Q);
        ASSERT(get_level M L = count_decided M);
        ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (D' - {#-L#}) + 1);
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (D' - {#-L#}) + 1);

        if size D' > 1
        then do {
          ASSERT(\<forall>L' \<in># D' - {#-L#}. get_level M L' = get_level M1 L');
          ASSERT(\<exists>L' \<in># D' - {#-L#}. get_level M L' = get_maximum_level M (D' - {#-L#}));
          ASSERT(get_level M L > get_maximum_level M (D' - {#-L#}));
          L' \<leftarrow> SPEC(\<lambda>L'. L' \<in># D' - {#-L#} \<and> get_level M L' = get_maximum_level M (D' - {#-L#}));
          ASSERT(L \<noteq> -L');
          let D' = D';
          RETURN (Propagated (-L) D' #  M1, N, add_mset (TWL_Clause {#-L, L'#} (D' - {#-L, L'#})) U,
            None, NP, UP, WS, {#L#})
        }
        else do {
          let D' = D';
          RETURN (Propagated (-L) D' # M1, N, U, None, NP, add_mset D' UP, WS, {#L#})
        }
      }
    }
  \<close>
    for S\<^sub>0 :: \<open>'v twl_st\<close>
    unfolding backtrack_def
    apply (rewrite at \<open>let _ = _ in _\<close> Let_def)+ ..

  have obtain_decom: \<open>\<exists>K. \<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
    get_level M' K = (get_maximum_level M' (remove1_mset (- lit_of (hd M'))
    E)) + 1\<close> if
    decomp: \<open>\<exists>K. \<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits_l N M')) \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd (convert_lits_l N M')))
    E))\<close> (is \<open>\<exists>K. \<exists>M1 M2. ?P K M1 M2 \<and> ?Q K\<close> ) and
    M': \<open>M' \<noteq> []\<close>
    for M' E N
  proof -
    obtain K M1 M2 where
      \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits_l N M'))\<close> and
      Q: \<open>?Q K\<close>
      using decomp by auto
    then obtain K' M1' M2' where
      \<open>(K' # M1', M2') \<in> set (get_all_ann_decomposition M')\<close> and
      \<open>Decided K # M1 = convert_lits_l N (K' # M1')\<close> and
      \<open>M2 = convert_lits_l N M2'\<close>
      unfolding get_all_ann_decomposition_convert_lits_l by (auto simp: convert_lits_l_def)
    then show ?thesis
      using M' apply -
      apply (rule exI[of _ K], rule exI[of _ M1'], rule exI[of _ M2'])
      by (cases K') (use Q in \<open>auto split: if_splits\<close>)
  qed

  have H: \<open>find_decomp (M', N, U, C, NP, UP, WS, Q) L
    \<le> \<Down> {(M1', M1). M1 = convert_lits_l N M1' \<and>
       (\<exists>K M2. (Decided K # M1', M2) \<in> set (get_all_ann_decomposition M') \<and>
          get_level M' K = get_maximum_level M' (D - {#-L#}) + 1)}
    (SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
    get_level M K = get_maximum_level M (remove1_mset (- L') D) + 1))\<close>
    (is \<open>_ \<le> \<Down> ?decomp (SPEC ?decomp_spec)\<close>)
    if
      help_the_unificacton: \<open>additional_WS_invs (M', N, thing_we_dont_care)\<close> and
      H: \<open>L' = lit_of (hd (convert_lits_l N M'))\<close> \<open>M = convert_lits_l N M'\<close>
      \<open>L = lit_of (hd (convert_lits_l N M'))\<close> \<open>the C = D\<close>
    for M M' L' L D D' N thing_we_dont_care U C NP UP WS Q
    unfolding find_decomp_def
  proof (clarify, rule RES_refine, clarify)
    fix M1 K M2
    assume
      lev: \<open>get_level M' K = get_maximum_level M' (remove1_mset (- L) (the C)) + 1\<close> and
      decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M')\<close>
    then have \<open>(Decided K # convert_lits_l N M1, convert_lits_l N M2) \<in> set (get_all_ann_decomposition M)\<close>
      by (force simp: get_all_ann_decomposition_convert_lits_l H)
    then show \<open>\<exists>s'\<in>Collect ?decomp_spec. (M1, s') \<in> ?decomp\<close>
      using lev decomp by (auto simp: H)
  qed

  have list_of_mset: \<open>list_of_mset D' \<le> SPEC (\<lambda>c. (c, D'') \<in> {(c, D). D = mset c})\<close>
    if \<open>D' = D''\<close> for D' :: \<open>'v clause\<close> and D''
    using that by (cases D'') (auto simp: list_of_mset_def)
  have ext: \<open>extract_shorter_conflict_l S
    \<le> \<Down> {(D, D'). D = D' \<and> -lit_of (hd (get_trail_l S)) \<in># D \<and> D \<subseteq># the D\<^sub>0} (extract_shorter_conflict S')\<close>
    if \<open>S' = twl_st_of None S \<close> and
      \<open>D\<^sub>0 = get_conflict_l S\<close> and
      \<open>get_trail_l S ~= []\<close>
    for S S' and D\<^sub>0
    using that
    by (cases S; cases S'; cases \<open>get_trail_l S\<close>; cases \<open>get_trail S'\<close>)
     (auto intro!: SPEC_refine simp: extract_shorter_conflict_l_def extract_shorter_conflict_def)

  have uhd_in_D: \<open>L \<in># the D\<close>
    if
      inv_s: "twl_stgy_invs (twl_st_of None S)" and
      inv: "twl_struct_invs (twl_st_of None S)" and
      ns: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None S))\<close> and
      confl: \<open>conflicting (state\<^sub>W_of (twl_st_of None S)) \<noteq> None\<close> 
         \<open>conflicting (state\<^sub>W_of (twl_st_of None S)) \<noteq> Some {#}\<close> and
      M_nempty: \<open>get_trail_l S ~= []\<close> and
      D: \<open>D = get_conflict_l S\<close>
         \<open>L = - lit_of (hd (get_trail_l S))\<close>
    for L M D and S :: \<open>'v twl_st_l\<close>
    unfolding D
    using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of \<open>state\<^sub>W_of (twl_st_of None S)\<close>,
      OF _ _ ns confl]
    by (cases S; cases \<open>fst S\<close>) (use that in \<open>auto simp: cdcl\<^sub>W_restart_mset_state twl_stgy_invs_def
       twl_struct_invs_def\<close>)

  have bt:
    \<open>(backtrack_l, backtrack) \<in> ?R \<rightarrow>
    \<langle>{(T::'v twl_st_l, T'). T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and> additional_WS_invs T}\<rangle> nres_rel\<close>
    supply [[goals_limit=1]]
    apply clarify
    apply (rename_tac M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E)

    unfolding backtrack_l_def backtrack_def'
    apply (refine_vcg H list_of_mset ext; remove_dummy_vars)
    subgoal by auto
    subgoal by (auto simp: convert_lits_l_def elim: list_not_emptyE)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (rule uhd_in_D) (assumption, assumption, auto simp: cdcl\<^sub>W_restart_mset_state)
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal unfolding ex_decomp_of_max_lvl_def
      by (rule obtain_decom) auto
    subgoal by auto
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: find_lit_of_max_level_def)
    subgoal by (auto dest!: in_diffD)
    subgoal by simp
    subgoal by (rule backtrak_l_ge1_rule_refinement) assumption+
    subgoal by fast
    subgoal by (rule backtrack_l_size0_rule_refinement) assumption
    done
  have KK:
    \<open>get_conflict_l T = None \<longleftrightarrow> get_conflict (twl_st_of None T) = None\<close>
    \<open>get_conflict_l T = Some {#} \<longleftrightarrow> get_conflict (twl_st_of None T) = Some {#}\<close>
    \<open>literals_to_update_l T = {#} \<longleftrightarrow> literals_to_update (twl_st_of None T) = {#}\<close>
    for T :: \<open>'v twl_st_l\<close>
    by (cases T; auto; fail)+
  have R: \<open>?R = {(S, S'). S' = twl_st_of None S \<and>
                 get_conflict (twl_st_of None S) \<noteq> None \<and>
                 (get_conflict_l S \<noteq> Some {#} \<and> additional_WS_invs S) \<and>
                 clauses_to_update_l S = {#} \<and>
                 literals_to_update (twl_st_of None S) = {#} \<and>
                 (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None S)) S') \<and>
                 (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None S)) S') \<and>
                 twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S)}\<close>
    unfolding KK by fast
  have \<open>(backtrack_l, backtrack)
     \<in> {(S::'v twl_st_l, S'). S' = twl_st_of None S \<and>
         get_conflict_l S \<noteq> None \<and> get_conflict_l S \<noteq> Some {#} \<and>
         clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and>
         additional_WS_invs S \<and>
         (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None S)) S') \<and>
         (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None S)) S') \<and>
         twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S)} \<rightarrow>
     \<langle>{(T, T'). (T' = twl_st_of None T \<and> clauses_to_update_l T = {#} \<and> additional_WS_invs T) \<and>
         get_conflict T' = None \<and> twl_struct_invs T' \<and> twl_stgy_invs T' \<and> literals_to_update T' \<noteq> {#}}\<rangle>nres_rel\<close>
    apply (rule refine_add_inv_generalised[OF bt, of \<open>Collect (\<lambda>T'::'v twl_st. get_conflict T' = None \<and>
          twl_struct_invs T' \<and>
         twl_stgy_invs T' \<and>
         literals_to_update T' \<noteq> {#})\<close>, unfolded mem_Collect_eq prod.case])
    subgoal for S S'
      unfolding KK
      apply (cases S)
      by (rule order_trans[OF backtrack_spec[of S']]) auto
    done
  then show bt': \<open>(backtrack_l, backtrack) \<in> ?R \<rightarrow> ?I\<close>
    unfolding KK apply -
    apply match_spec
    apply (match_fun_rel; fast?)+
    apply force
    done
qed

definition find_unassigned_lit :: \<open>'v twl_st_l \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit = (\<lambda>(M, N, U, D, NP, UP, WS, Q).
     SPEC (\<lambda>L.
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)))) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))))))
     )\<close>

definition decide_l_or_skip :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>decide_l_or_skip S = (do {
    ASSERT(twl_struct_invs (twl_st_of None S));
    ASSERT(twl_stgy_invs (twl_st_of None S));
    ASSERT(additional_WS_invs S);
    ASSERT(get_conflict_l S = None);
    L \<leftarrow> find_unassigned_lit S;
    if L \<noteq> None
    then do {
      let (M, N, U, D, NP, UP, WS, Q) = S;
      ASSERT(L \<noteq> None);
      let K = the L;
      RETURN (False, (Decided K # M, N, U, D, NP, UP, WS, {#-K#}))}
    else do {RETURN (True, S)}
  })
\<close>

definition cdcl_twl_o_prog_l :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>cdcl_twl_o_prog_l S =
    do {
      ASSERT(twl_struct_invs (twl_st_of None S));
      ASSERT(twl_stgy_invs (twl_st_of None S));
      ASSERT(additional_WS_invs S);
      do {
        if get_conflict_l S = None
        then decide_l_or_skip S
        else do {
          T \<leftarrow> skip_and_resolve_loop_l S;
          ASSERT(get_conflict_l T \<noteq> None);
          if get_conflict_l T \<noteq> Some {#}
          then do {U \<leftarrow> backtrack_l T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

thm decide_l_spec[unfolded nres_rel_def, unfolded fun_rel_def, simplified]
thm decide_l_spec
thm decide[to_pred]

lemma twl_st_lE: \<open>(\<And>M N U D NP UP WS Q. T = (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow> P (M, N, U, D, NP, UP, WS, Q)) \<Longrightarrow> P T\<close> for T :: \<open>'a twl_st_l\<close>
  by (cases T) auto

lemma cdcl_twl_o_prog_l_spec:
  \<open>(cdcl_twl_o_prog_l, cdcl_twl_o_prog) \<in>
    {(S, S'). S' = twl_st_of None S \<and>
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> no_step cdcl_twl_cp (twl_st_of None S) \<and>
       twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and> additional_WS_invs S} \<rightarrow>
    \<langle>{((brk, T), (brk', T')). T' = twl_st_of None T \<and> brk = brk' \<and> additional_WS_invs T \<and> clauses_to_update_l T = {#} \<and>
    (get_conflict_l T \<noteq> None \<longrightarrow> get_conflict_l T = Some {#})\<and>
       twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) (* \<and>
       (\<not>brk \<longrightarrow> literals_to_update_l T \<noteq> {#}) *)}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have H:
    \<open>RETURN S'
       \<le> \<Down> {(S', S).
              S = (Decided L # M, N, U, D, NP, UP, WS, {#- L#}) \<and>
              (\<exists>Q. twl_st_of None S' = (M, N, U, D, NP, UP, WS, Q))}
           (do {
              L \<leftarrow> SPEC (\<lambda>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# N));
              RETURN (Decided L # M, N, U, D, NP, UP, WS, {#- L#})})\<close>
    if \<open>undefined_lit M L\<close> and
      \<open>atm_of L \<in> atms_of_mm (clause `# N)\<close> and
      \<open>\<exists>Q. twl_st_of None S' = (M, N, U, D, NP, UP, WS, Q)\<close>
    for M N U NP UP WS L and S' and D
    using that by (cases \<open>L\<close>) (auto intro!: rhs_step_bind_SPEC)
  have twl_prog:
    \<open>(cdcl_twl_o_prog_l, cdcl_twl_o_prog) \<in> ?R \<rightarrow>
      \<langle>{(S, S').
         (fst S' = (fst S) \<and> snd S' = twl_st_of None (snd S)) \<and> additional_WS_invs (snd S) \<and>
         clauses_to_update_l (snd S) = {#}}\<rangle> nres_rel\<close>
    supply [[goals_limit=1]]
    apply clarify
    unfolding cdcl_twl_o_prog_l_def cdcl_twl_o_prog_def decide_l_or_skip_def
      find_unassigned_lit_def decide_def
    apply (refine_vcg decide_l_spec[THEN refine_pair_to_SPEC]
        skip_and_resolve_loop_l_spec[THEN refine_pair_to_SPEC]
        backtrack_l_spec[THEN refine_pair_to_SPEC] H; remove_dummy_vars)
    subgoal by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
      apply (auto; fail) -- \<open>the variable L have to be guessed, so no subgoal\<close>
    subgoal
      by auto
    subgoal
      by simp
    subgoal
      by (auto simp add: additional_WS_invs_def)
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by (rule twl_st_lE) auto
    subgoal
      by (rule twl_st_lE) auto
    subgoal
      by (auto simp add: additional_WS_invs_def)
    subgoal
      by (rule twl_st_lE) auto
    subgoal
      by (auto simp add: get_conflict_l_Some_nil_iff)
    subgoal
      by fast
    subgoal
      by fast
    subgoal
      by auto
    subgoal
      by fast
    subgoal
      by fast
    subgoal
      by (auto simp add: additional_WS_invs_def)
    subgoal
      by (auto simp add: additional_WS_invs_def)
    done
  have KK:
    \<open>get_conflict_l T = None \<longleftrightarrow> get_conflict (twl_st_of None T) = None\<close>
    \<open>literals_to_update_l T = {#} \<longleftrightarrow> literals_to_update (twl_st_of None T) = {#}\<close>
    for T :: \<open>'v twl_st_l\<close>
    by (cases T; auto)+
  text \<open>Stupid placeholder to help the application of \<open>rule\<close> later:\<close>
  define TT where [simp]: \<open>TT = (\<lambda>_::bool \<times> 'a twl_st_l. True)\<close>
  let ?J' = \<open>{(U, U').
       (fst U' = id (fst U) \<and> snd U' = twl_st_of None (snd U)) \<and> (additional_WS_invs (snd U) \<and>
         clauses_to_update_l (snd U) = {#}) \<and>
        (get_conflict (twl_st_of None (snd U)) \<noteq> None \<longrightarrow> get_conflict (twl_st_of None (snd U)) = Some {#}) \<and>
         twl_struct_invs (twl_st_of None (snd U)) \<and>
         twl_stgy_invs (twl_st_of None (snd U)) (* \<and>
         (\<not>fst U \<longrightarrow> literals_to_update (twl_st_of (snd U)) \<noteq> {#}) *)}\<close>

  have J: \<open>?J = ?J'\<close>
    by (standard; standard) force+
  show bt': ?thesis
    unfolding J
    apply (rule refine_add_inv_pair)
    subgoal
      using twl_prog apply -
      apply (match_spec; (match_fun_rel; match_fun_rel?)+)
      by auto
    subgoal for S
      by (rule weaken_SPEC[OF cdcl_twl_o_prog_spec[of \<open>twl_st_of None S\<close>]])
        (force simp: KK(2))+
    done
qed


subsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_prog_l S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
        (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of None T)) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of None S\<^sub>0) (twl_st_of None T) \<and>
        clauses_to_update_l T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict_l T = None)\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_l S;
          cdcl_twl_o_prog_l T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

lemma refine_pair_to_SPEC_fst_pair2:
  fixes f :: \<open>'s \<Rightarrow> ('c \<times> 's) nres\<close> and g :: \<open>'b \<Rightarrow> ('c \<times> 'b) nres\<close>
  assumes H: \<open>(f, g) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{((brk, S), (brk', S')). S' = h S \<and> brk = brk' \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and [simp]: \<open>S' = h S\<close>
  shows \<open>f S \<le> \<Down> {((brk, S), (brk', S')). S' = h S \<and> brk = brk' \<and> P' S} (g S')\<close>
  by (rule H["to_\<Down>"]) (use assms in auto)

lemma cdcl_twl_stgy_prog_l_spec:
  \<open>(cdcl_twl_stgy_prog_l, cdcl_twl_stgy_prog) \<in>
    {(S, S'). S' = twl_st_of None S \<and> additional_WS_invs S \<and>
       clauses_to_update_l S = {#} \<and>
       twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S)} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of None T \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow> ((False, a), (False, b)) \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> ?R}\<close>
    for a b by auto
  have KK:
    \<open>get_conflict_l T = None \<longleftrightarrow> get_conflict (twl_st_of None T) = None\<close>
    \<open>literals_to_update_l T = {#} \<longleftrightarrow> literals_to_update (twl_st_of None T) = {#}\<close>
    for T :: \<open>'v twl_st_l\<close>
    by (cases T; auto)+
  show ?thesis
    unfolding cdcl_twl_stgy_prog_l_def cdcl_twl_stgy_prog_def cdcl_twl_o_prog_l_spec
    apply (refine_rcg R cdcl_twl_o_prog_l_spec[THEN refine_pair_to_SPEC_fst_pair2]
        unit_propagation_outer_loop_l_spec[THEN refine_pair_to_SPEC]; remove_dummy_vars)
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
    subgoal by (auto simp: literals_to_update_l_literals_to_update)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_l_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of None S)\<close> and \<open>twl_stgy_invs (twl_st_of None S)\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    \<open>get_conflict_l S = None\<close> and \<open>additional_WS_invs S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_l S \<le> SPEC(\<lambda>T. full cdcl_twl_stgy (twl_st_of None S) (twl_st_of None T))\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_l_spec[THEN refine_pair_to_SPEC,
          of S \<open>twl_st_of None S\<close>]])
  using assms apply auto[2]
  apply (rule order_trans)
   apply (rule ref_two_step[OF _ cdcl_twl_stgy_prog_spec[of \<open>twl_st_of None S\<close>],
        of _ \<open>{(S, S'). S' = twl_st_of None S \<and> True}\<close>])
  using assms by (auto simp: full_def literals_to_update_l_literals_to_update
      get_conflict_l_get_conflict pw_conc_inres pw_conc_nofail pw_ords_iff(1))

end