theory CDCL_Two_Watched_Literals_List
  imports CDCL_Two_Watched_Literals_Algorithm
  Eisbach
begin

section \<open>Second Refinement: Lists as Clause\<close>

subsection \<open>Types\<close>
type_synonym 'v working_queue_list = "(nat \<times> nat) multiset"
type_synonym 'v lit_queue_list = "'v literal list"

type_synonym 'v clause_list = "'v literal list"
type_synonym 'v clauses_list = "'v literal list"

type_synonym 'v twl_st_list =
  "('v, nat) ann_lits \<times> 'v clause_list list \<times> nat \<times>
    'v clause_list option \<times> 'v clauses \<times> 'v clauses \<times> 'v working_queue_list \<times> 'v lit_queue"


fun working_queue_list :: "'v twl_st_list \<Rightarrow> (nat \<times> nat) multiset" where
  \<open>working_queue_list (_, _, _, _, _, _, WS, _) = WS\<close>

fun get_trail_l :: "'v twl_st_list \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_l (M, _, _, _, _, _, _, _) = M\<close>

fun set_working_queue_list :: "(nat \<times> nat) multiset \<Rightarrow> 'v twl_st_list \<Rightarrow>
  'v twl_st_list" where
  \<open>set_working_queue_list WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun pending_list :: "'v twl_st_list \<Rightarrow> 'v literal multiset" where
  \<open>pending_list (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_pending_list :: "'v literal multiset \<Rightarrow> 'v twl_st_list \<Rightarrow> 'v twl_st_list" where
  \<open>set_pending_list Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun get_conflict_list :: "'v twl_st_list \<Rightarrow> 'v clause_list option" where
  \<open>get_conflict_list (_, _, _, D, _, _, _, _) = D\<close>

fun watched_l where
  \<open>watched_l l = take 2 l\<close>

fun unwatched_l where
  \<open>unwatched_l l = drop 2 l\<close>

fun twl_clause_of :: "'a list \<Rightarrow> 'a multiset twl_clause" where
  \<open>twl_clause_of l = TWL_Clause (mset (watched_l l)) (mset (unwatched_l l))\<close>

fun clause_of :: "'a::plus twl_clause \<Rightarrow> 'a"  where
  \<open>clause_of (TWL_Clause W UW) = W + UW\<close>

fun convert_lit :: "'v clause_list list \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit" where
  \<open>convert_lit N (Decided K) = Decided K\<close>
| \<open>convert_lit N (Propagated K j) =
  (if j = 0 then Propagated K {#K#} else Propagated K (mset (N ! j)))\<close>

definition convert_lits_l :: "'v clause_list list \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits" where
  \<open>convert_lits_l N M = map (convert_lit N) M\<close>

lemma convert_lits_l_nil[simp]: \<open>convert_lits_l N [] = []\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_cons[simp]: \<open>convert_lits_l N (L # M) = convert_lit N L # convert_lits_l N M\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_append[simp]: \<open>convert_lits_l N (M @ M') = convert_lits_l N M @ convert_lits_l N M'\<close>
  by (auto simp: convert_lits_l_def)

fun get_trail_list :: "'v twl_st_list \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_list (M, _, _, _, _, _, _, _) = M\<close>

fun get_learned_list :: "'v twl_st_list \<Rightarrow> nat" where
  \<open>get_learned_list (_, _, U, _, _, _, _, _) = U\<close>

abbreviation resolve_cls_list where
  \<open>resolve_cls_list L D' E \<equiv> union_mset_list (remove1 (-L) D') (remove1 L E)\<close>

lemma mset_resolve_cls_list_resolve_cls[iff]:
  \<open>mset (resolve_cls_list L D' E) = cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E)\<close>
  by (auto simp: union_mset_list[symmetric])

lemma resolve_cls_list_nil_iff:
  \<open>resolve_cls_list L D' E = [] \<longleftrightarrow> cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E) = {#}\<close>
  by (metis mset_resolve_cls_list_resolve_cls mset_zero_iff)

fun twl_st_of :: \<open>'v twl_st_list  \<Rightarrow> 'v twl_st\<close> where
\<open>twl_st_of (M, N, U, C, NP, UP, WS, Q) =
(convert_lits_l N M, twl_clause_of `# mset (take U (tl N)), twl_clause_of `# mset (drop (Suc U) N),
  map_option mset C, NP, UP,
  (\<lambda>(a, j). (N!j! a, twl_clause_of (N!j))) `# WS, Q)
\<close>

fun get_clauses_l :: "'v twl_st_list \<Rightarrow> 'v literal list list" where
  \<open>get_clauses_l (M, N, U, D, NP, UP, WS, Q) = N\<close>

lemma get_conflict_list_Some_nil_iff:
  \<open>get_conflict_list S = Some [] \<longleftrightarrow> get_conflict (twl_st_of S) = Some {#}\<close>
  by (cases S) auto

lemma working_queu_empty_iff[iff]:
  \<open>working_queue (twl_st_of x) = {#} \<longleftrightarrow> working_queue_list x = {#}\<close>
  by (cases x) auto

lemma working_queue_list_set_working_queue_list:
  \<open>working_queue_list (set_working_queue_list WS S) = WS\<close>
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

lemma pending_list_pending: \<open>pending (twl_st_of S) = pending_list S\<close>
  by (cases S) auto

lemma get_conflict_list_get_conflict:
  \<open>get_conflict (twl_st_of S) = None \<longleftrightarrow> get_conflict_list S = None\<close>
  \<open>get_conflict (twl_st_of S) = Some {#} \<longleftrightarrow> get_conflict_list S = Some []\<close>
  by (cases S, auto)+


subsection \<open>Additional Invariants and Definitions\<close>

definition additional_WS_invs where
  \<open>additional_WS_invs S \<longleftrightarrow>
    (\<forall>(i, C) \<in># working_queue_list S. (i = 0 \<or> i = 1) \<and> C < length (get_clauses_l S) \<and> C > 0) \<and>
    (\<forall>L C. Propagated L C \<in> set (get_trail_l S) \<longrightarrow> (C < length (get_clauses_l S) \<and>
      (C > 0 \<longrightarrow> L \<in> set (watched_l ((get_clauses_l S) ! C))))) \<and>
    distinct_mset (working_queue_list S) \<and> get_clauses_l S \<noteq> [] \<and>
    get_learned_list S < length (get_clauses_l S)\<close>

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

definition find_unwatched :: "('a, 'b) ann_lits \<Rightarrow> 'a clause_list \<Rightarrow> (bool option \<times> nat) nres" where
\<open>find_unwatched M C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
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
    (None, 2::nat)
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
  assumes \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close>
  shows \<open>find_unwatched M C \<le> SPEC (\<lambda>(found, i). i \<ge> 2 \<and>
      (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l C). -L \<in> lits_of_l M)) \<and>
      (found = Some False \<longleftrightarrow> (i < length C \<and> undefined_lit M (C!i))) \<and>
      (found = Some True \<longleftrightarrow> (i < length C \<and> C!i \<in> lits_of_l M)))\<close>
  unfolding find_unwatched_def
  apply (rule WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
     apply (simp_all add: assms)[2]

  subgoal for s unfolding valued_def
    by refine_vcg
      (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq dest: less_SucE
        split: bool.split if_splits)
  subgoal for s using distinct_consistent_interp[OF assms(1)]
    apply (cases s, cases \<open>fst s\<close>) (* TODO tune proof *)
     apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth)
    apply (metis One_nat_def Suc_diff_Suc Suc_le_D Suc_le_lessD diff_Suc_1 diff_less_mono numeral_2_eq_2)+
    done
  done


definition unit_propagation_inner_loop_body_list :: "nat \<times> nat \<Rightarrow>
  'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>unit_propagation_inner_loop_body_list C' S = do {
    let (M, N, U, D, NP, UP, WS, Q) = S;
    let (i, C::nat) = C';
    let L = (watched_l (N!C)) ! i;
    let L' = (watched_l (N!C)) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    ASSERT(val_L' = Some True \<longleftrightarrow> L' \<in> lits_of_l M);
    ASSERT(val_L' = Some False \<longleftrightarrow> -L' \<in> lits_of_l M);
    ASSERT(val_L' = None \<longleftrightarrow> undefined_lit M L');
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some (N!C), NP, UP, {#}, {#})}
        else do {RETURN (Propagated L' C # M, N, U, D, NP, UP, WS, add_mset (-L') Q)}
      else do {
        let K = (N!C) ! (snd f);
        let N' = list_update N C (swap (N!C) i (snd f));
        RETURN (M, N', U, D, NP, UP, WS, Q)
      }
    }
   }
\<close>
(* 
schematic_goal valued_impl: "RETURN ?c \<le> valued M L"
  unfolding unit_propagation_inner_loop_body_list_def valued_def Let_def
  apply (refine_transfer find_unwatched_impl)
  done

concrete_definition valued_impl uses valued_impl

prepare_code_thms valued_impl_def
export_code valued_impl in SML

declare  find_unwatched_impl[refine_transfer] valued_impl[refine_transfer]
schematic_goal unit_propagation_inner_loop_body_list: "RETURN ?c \<le> unit_propagation_inner_loop_body_list C S"
  unfolding unit_propagation_inner_loop_body_list_def
  apply (refine_transfer)
  done

concrete_definition unit_propagation_inner_loop_body_list_impl uses 
  unit_propagation_inner_loop_body_list
prepare_code_thms unit_propagation_inner_loop_body_list_impl_def
export_code find_unwatched_impl in SML
thm unit_propagation_inner_loop_body_list_impl_def
export_code unit_propagation_inner_loop_body_list_impl in Haskell *)

lemma take_2_if:
  \<open>take 2 C = (if C = [] then [] else if length C = 1 then [hd C] else [C!0, C!1])\<close>
  by (cases C; cases \<open>tl C\<close>) auto

lemma tl_update_swap:
  \<open>i \<ge> 1 \<Longrightarrow> tl (N[i := C]) = tl N[i-1 := C]\<close>
  by (auto simp:  drop_Suc[of 0, symmetric, simplified] drop_update_swap)

lemma refine_add_invariants:
  assumes
    \<open>(f S) \<le> SPEC(\<lambda>S'. Q S')\<close> and
    \<open>y \<le> \<Down> {(S, S'). P S S'} (f S)\<close>
  shows \<open>y \<le> \<Down> {(S, S'). P S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail by force

(* TODO Move *)
lemma true_annot_append_l:
  \<open>M \<Turnstile>a A \<Longrightarrow> M' @ M \<Turnstile>a A\<close>
  unfolding true_annot_def by auto

lemma true_annots_append_l:
  \<open>M \<Turnstile>as A \<Longrightarrow> M' @ M \<Turnstile>as A\<close>
  unfolding true_annots_def by (auto simp: true_annot_append_l)
(* TODO end move *)

lemma unit_propagation_inner_loop_body_list:
  fixes i C :: nat and S :: \<open>'v twl_st_list\<close>
  defines C'[simp]: \<open>C' \<equiv> get_clauses_l S ! C\<close>
  assumes
      WS: \<open>(i, C) \<in># working_queue_list S\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of S)\<close> and
      add_inv: \<open>additional_WS_invs S\<close> and
      stgy_inv: \<open>twl_stgy_invs (twl_st_of S)\<close>
  shows
  \<open>unit_propagation_inner_loop_body_list (i, C) (set_working_queue_list (working_queue_list S - {#(i, C)#}) S) \<le>
      \<Down> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S \<and> twl_stgy_invs S' \<and> twl_struct_invs S'} (unit_propagation_inner_loop_body
      (C' ! i, twl_clause_of C') (set_working_queue (working_queue (twl_st_of S) - {#(C' ! i, twl_clause_of C')#}) (twl_st_of S)))\<close>
proof -
  let ?L = \<open>C' ! i\<close>
  let ?L' = \<open>C' ! (Suc 0 - i)\<close>
  let ?S = \<open>(set_working_queue_list (working_queue_list S - {#(i, C)#}) S)\<close>
  obtain M N U D NP UP WS Q where S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S) auto
  have S'_S: \<open>twl_st_of S =  (convert_lits_l N M,
     {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take U (tl N))#},
     {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc U) N)#},
     map_option mset D, NP, UP,
     {#case x of (a, j) \<Rightarrow> (N ! j ! a, TWL_Clause (mset (take 2 (N ! j))) (mset (drop 2 (N ! j)))).
        x \<in># WS#},
     Q)\<close>
    unfolding S by auto
  have i: \<open>i = 0 \<or> i = 1\<close> and C_N_U: \<open>C < length (get_clauses_l S)\<close>
    using WS add_inv by (auto simp: S additional_WS_invs_def)
  have WS': \<open>(C' ! i, twl_clause_of C') \<in># working_queue (twl_st_of S)\<close>
    using WS S by auto
  have S': \<open>set_working_queue_list (remove1_mset (i, C)
       (working_queue_list (M, N, U, D, NP, UP, WS, Q))) (M, N, U, D, NP, UP, WS, Q) =
    (M, N, U, D, NP, UP, remove1_mset (i, C) WS, Q)\<close>
    by auto
  let ?N = \<open>{#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#}\<close>
  let ?U = \<open>{#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (drop (Suc U) N)#}\<close>
  have st_of_S': \<open>twl_st_of
     (M, N, U, D, NP, UP, remove1_mset (i, C) WS, Q) =
     (convert_lits_l N M,
     ?N, ?U,
     map_option mset D, NP, UP,
     {#case x of (a, j) \<Rightarrow> (N ! j ! a, TWL_Clause (mset (take 2 (N ! j))) (mset (drop 2 (N ! j))))
     . x \<in># remove1_mset (i, C) WS#},
     Q)\<close>
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
  have N_take_drop: \<open>tl N = take U (tl N) @ drop (Suc U) N\<close>
    by (simp add: drop_Suc)
  let ?C' = \<open>twl_clause_of C'\<close>
  have C'_N_U_or: \<open>?C' \<in># twl_clause_of `# mset (take U (tl N)) \<or> ?C' \<in># twl_clause_of `# mset (drop (Suc U) N)\<close> and
    uL_M: \<open>-?L \<in> lits_of_l M\<close>
    using WS valid
    by (auto simp: S twl_struct_invs_def split: prod.splits simp del: twl_clause_of.simps)
  then have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using inv by (auto simp: twl_st_inv.simps S simp del: twl_clause_of.simps)
  have C'_N_U: \<open>?C' \<in># twl_clause_of `# mset (tl N)\<close>
    using C'_N_U_or apply (subst N_take_drop)
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric] take_tl .
  have watched_C': \<open>mset (watched_l C') = {#?L, ?L'#}\<close>
    using struct i by (cases C) (auto simp: length_list_2 take_2_if)
  then have mset_watched_C: \<open>mset (watched_l C') = {#watched_l C' ! i, watched_l C' ! (Suc 0 - i)#}\<close>
    using i by (cases \<open>twl_clause_of (get_clauses_l S ! C)\<close>) (auto simp: take_2_if)
  have two_le_length_C: \<open>2 \<le> length C'\<close>
    by (metis length_take linorder_not_le min_less_iff_conj numeral_2_eq_2 order_less_irrefl
        size_add_mset size_eq_0_iff_empty size_mset watched_C' watched_l.simps)
  have unwatched_twl_clause_of[simp]: \<open>set_mset (unwatched (twl_clause_of C')) = set (unwatched_l C')\<close>
    by (cases C) auto
  have in_set_unwatched_conv: \<open>(\<forall>j<length (unwatched C). defined_lit M (unwatched C ! j)) \<longleftrightarrow>
    (\<forall>L \<in># mset (unwatched C). defined_lit M L)\<close>
    for C :: \<open>'b literal list twl_clause\<close> and M :: \<open>('b, 'c) ann_lit list\<close>
    unfolding set_mset_mset by (metis in_set_conv_nth)
  have init_invs: \<open>(?S, twl_st_of ?S) \<in> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S}\<close> and
    C_le_N: \<open>C < length N\<close> \<open>C > 0\<close> and
    dist_WS: \<open>distinct_mset WS\<close>
    using WS add_inv by (auto simp add: S additional_WS_invs_def dest: in_diffD)

  have init_invs: \<open>(?S, twl_st_of ?S) \<in> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S}\<close>
    using WS add_inv by (auto simp add: S additional_WS_invs_def dest: in_diffD)

  have D_None: \<open>D = None\<close>
    using WS' struct_invs unfolding twl_struct_invs_def S'_S get_conflict.simps working_queue.simps
    by (metis (no_types, lifting)ex_Melem_conv map_option_is_None)
  have upd_S_S': \<open>twl_st_of (set_working_queue_list (remove1_mset (i, C) (working_queue_list S)) S) =
    set_working_queue (remove1_mset (C' ! i, twl_clause_of C') (working_queue (twl_st_of S)))
            (twl_st_of S)\<close>
    using S WS by (auto simp: image_mset_remove1_mset_if)

  have
    w_q_inv: \<open>working_queue_inv (twl_st_of S)\<close> and
    dist: \<open>distinct_queued (twl_st_of S)\<close> and
    no_dup: \<open>no_duplicate_queued (twl_st_of S)\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have H: \<open>\<And>L C. count {#(N!b ! a, twl_clause_of (N!b)). (a, b) \<in># WS#} (L, C) \<le>
    count (twl_clause_of `# mset (tl N)) C\<close>
    using dist N_take_drop unfolding S distinct_queued.simps twl_st_of.simps mset_append[symmetric]
      image_mset_union[symmetric] by auto

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
    using i by auto
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
      have f1: "\<And>ls lss. length ((ls::'v literal list) # lss) = Suc (length lss)"
        by simp
      have f2: "\<And>ls lsa lss. (ls::'v literal list) \<noteq> lsa \<or> lsa \<in> set (ls # lss)"
        by simp
      have "\<And>ls lss. take (Suc 0) ((ls::'v literal list) # lss) = [] @ [ls]"
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

    have H1: \<open>mset (watched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := C' ! i])) =
        {#C' ! Suc (Suc k'), C' ! (Suc 0 - i)#}\<close>
      using k_le k_2 i by (auto simp: take_2_if N_C_C')
    have H2: \<open>mset (unwatched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := C' ! i])) =
      add_mset (C' ! i) (remove1_mset (C' ! Suc (Suc k')) (mset (unwatched_l C')))\<close>
      using k_le k_2 i k' by (auto simp: drop_update_swap N_C_C' mset_update)
    have H3:  \<open>{#C' ! i, C' ! (Suc 0 - i)#} = mset (watched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> by (auto simp: take_2_if N_C_C' nth_tl)
    have H4: \<open>mset (unwatched_l C') = mset (unwatched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> by (auto simp: take_2_if N_C_C' nth_tl)
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>(add_mset (update_clause (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (C' ! i) (C' ! k))
            (remove1_mset (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (twl_clause_of `# mset (take U (tl N)))),
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

    have H1: \<open>mset (watched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := C' ! i])) =
        {#C' ! Suc (Suc k'), C' ! (Suc 0 - i)#}\<close>
      using k_le k_2 i by (auto simp: take_2_if N_C_C')
    have H2: \<open>mset (unwatched_l (C'[i := C' ! Suc (Suc k'), Suc (Suc k') := C' ! i])) =
      add_mset (C' ! i) (remove1_mset (C' ! Suc (Suc k')) (mset (unwatched_l C')))\<close>
      using k_le k_2 i k' by (auto simp: drop_update_swap N_C_C' mset_update)
    have H3:  \<open>{#C' ! i, C' ! (Suc 0 - i)#} = mset (watched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> by (auto simp: take_2_if N_C_C' nth_tl)
    have H4: \<open>mset (unwatched_l C') = mset (unwatched_l (tl N ! (C - Suc 0)))\<close>
      using k_le k_2 i \<open>C < length N\<close> \<open>C > 0\<close> by (auto simp: take_2_if N_C_C' nth_tl)
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>({#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># mset (take U (tl N))#},
            add_mset (update_clause (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (C' ! i) (C' ! k))
            (remove1_mset (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (twl_clause_of `# mset (drop (Suc U) N))))\<close>])
      using update_clauses.intros(2)[OF TWL_L_L'_UW_N, of ?N ?L \<open>C'!k\<close>]
      using \<open>C > 0\<close> \<open>C < length N\<close>
      using J_NP by (auto simp: mset_update not_less_eq_eq
          image_mset_remove1_mset_if H1 H2 H3[symmetric] H4[symmetric]
          L_L'_UW_N  TWL_L_L'_UW_N k' C'[symmetric] N_C_C' mset_watched_C watched_C' nth_tl
          watched_l.simps[symmetric] unwatched_l.simps[symmetric] drop_update_swap
          tl_update_swap swap_def simp del: watched_l.simps unwatched_l.simps)
  qed

  have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state (twl_st_of S))\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have \<open>distinct_mset (mset (take 2 (N!C)) + mset (drop 2 (N!C)))\<close>
    using C'_N_U_or unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def S
    by (auto simp add: cdcl\<^sub>W_restart_mset_state C' S distinct_mset_set_def)
  then have distinct_C': \<open>distinct C'\<close>
    unfolding mset_append[symmetric] append_take_drop_id N_C_C' by simp

  have jC_notin_WS: \<open>(j, C) \<notin># remove1_mset (i, C) WS\<close> for j
  proof (rule ccontr)
    assume jC[simplified]: \<open>\<not> ?thesis\<close>
    have \<open>distinct_queued (twl_st_of S)\<close>
      using struct_invs unfolding twl_struct_invs_def by fast
    then have eq: \<open>\<And>L L' C C'.
      (L, C) \<in> (\<lambda>(a, j). (N ! j ! a, twl_clause_of (N ! j))) ` set_mset WS \<Longrightarrow>
      (L', C') \<in> (\<lambda>(a, j). (N ! j ! a, twl_clause_of (N ! j))) ` set_mset WS \<Longrightarrow>
      L = L'\<close>
      by (fastforce simp: S)
    have \<open>C' ! i = C' ! j\<close>
      apply (rule eq[of \<open>C'!i\<close> \<open>twl_clause_of C'\<close> \<open>C'!j\<close> \<open>twl_clause_of C'\<close>] )
       using imageI[OF WS, of \<open>(\<lambda>(a, j). (N ! j ! a, twl_clause_of (N ! j)))\<close>]
       apply (simp add: N_C_C' S image_iff)
      by (metis (no_types, lifting) N_C_C' in_diffD jC pair_imageI)
    moreover have \<open>j < length C'\<close>
      using add_inv jC two_le_length_C by (auto simp: S additional_WS_invs_def C' dest!: in_diffD)
    ultimately have \<open>i = j\<close>
      using distinct_C'
      by (metis One_nat_def Suc_le_lessD i index_nth_id less_imp_le_nat numeral_2_eq_2 two_le_length_C)
    then show False
      using dist_WS WS jC by (auto simp: S dest!: multi_member_split)
  qed
  have \<open>unit_propagation_inner_loop_body_list (i, C) ?S \<le>
    \<Down> {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S} (unit_propagation_inner_loop_body
    (?L, twl_clause_of C') (twl_st_of ?S))\<close>
    using n_d unfolding unit_propagation_inner_loop_body_list_def unit_propagation_inner_loop_body_def S
      S'_S[unfolded S] S' st_of_S'
    apply (rewrite at \<open>let _ = watched_l _ ! _ in _\<close> Let_def)
    supply [[goals_limit = 1]]
    apply (refine_rcg bind_refine_spec[where M' = \<open>find_unwatched _ _\<close>, OF _ find_unwatched]
        bind_refine_spec[where M' = \<open>valued _ _\<close>, OF _ valued_spec[]]
        update_clause_ll_spec
        case_prod_bind[of _ \<open>If _ _\<close>]; remove_dummy_vars)
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
          additional_WS_invs_def C'[symmetric] N_C_C' split: option.splits bool.splits)
    subgoal using init_invs S C_le_N add_mset_C'_i dist_WS by (vc_solve simp: mset_watched_C watched_C'
          in_set_unwatched_conv set_take_2_watched
          consistent additional_WS_invs_def N_C_C' split: option.splits bool.splits dest: in_diffD)
    subgoal
      apply (rule RETURN_rule)
      apply (use consistent in \<open>vc_solve simp: Decided_Propagated_in_iff_in_lits_of_l C'[symmetric]
          N_C_C'\<close>)
      by (meson in_set_drop_conv_nth)
    subgoal using C'_N_U S by (auto simp add: C'[symmetric] N_C_C')
    subgoal by (simp; fail)
    subgoal by auto
    subgoal premises p for L' val_L f K N' U'
    proof -
      note upd = p(16)
      have \<open>Propagated K C \<notin> set M\<close> for K
      proof (rule ccontr)
        assume propa: \<open>\<not> ?thesis\<close>
        have propa': \<open>Propagated K (mset C') \<in> set (convert_lits_l N M)\<close>
          using imageI[OF propa[simplified], of \<open>convert_lit N\<close>] \<open>C > 0\<close>
          by (simp add: convert_lits_l_def N_C_C')
        from split_list[OF propa'] obtain M1 M2 where
          M1: \<open>convert_lits_l N M = M2 @ Propagated K (mset C') # M1\<close>
          by blast
        have \<open>\<forall>L mark a b. a @ Propagated L mark # b = trail (convert_to_state (twl_st_of S)) \<longrightarrow>
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
          by (metis N_C_C' in_remove1_mset_neq in_set_dropD lits_of_l_convert_lits_l p(12)
              set_mset_mset unwatched_l.elims)
        then show False
          using p(14) by fast
      qed
      then have \<open>additional_WS_invs (M, N[C := swap (N ! C) i (snd f)], U, D, NP, UP, remove1_mset (i, C) WS, Q)\<close>
        using add_inv S by (auto simp add: additional_WS_invs_def N_C_C' nth_list_update'
             dest: in_diffD)
      moreover {
        have \<open>snd f < length C'\<close>
          using p(11,13) by (auto simp: N_C_C')
        then have \<open>convert_lit N x = convert_lit (N[C := swap (N ! C) i (snd f)]) x\<close> if \<open>x \<in> set M\<close>for x
          apply (cases x)
          using i two_le_length_C by (auto simp: nth_list_update' swap_def N_C_C' mset_update)
        then have \<open>convert_lits_l N M = convert_lits_l (N[C := swap (N ! C) i (snd f)]) M\<close>
          unfolding convert_lits_l_def by auto }
      moreover have \<open>{#(N ! j ! a, TWL_Clause (mset (take 2 (N ! j))) (mset (drop 2 (N ! j)))).
          (a, j) \<in># remove1_mset (i, C) WS#} =
        {#(N[C := swap (N ! C) i (snd f)] ! j ! a,
          TWL_Clause
           (mset (take 2 (N[C := swap (N ! C) i (snd f)] ! j)))
           (mset (drop 2 (N[C := swap (N ! C) i (snd f)] ! j)))).
          (a, j) \<in># remove1_mset (i, C) WS#}\<close>
        by (rule image_mset_cong) (use jC_notin_WS in \<open>auto simp: nth_list_update' swap_def\<close>)
      ultimately show ?thesis
         using upd by simp
    qed
    subgoal using two_le_length_C unfolding N_C_C' by simp
    done
  note H = this
  have *: \<open>unit_propagation_inner_loop_body (C' ! i, twl_clause_of C')
   (set_working_queue (remove1_mset (C' ! i, twl_clause_of C') (working_queue (twl_st_of S)))
     (twl_st_of S))
   \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and>
                 twl_stgy_invs S' \<and>
                 cdcl_twl_cp\<^sup>*\<^sup>* (twl_st_of S) S' \<and>
              (S', twl_st_of S) \<in> measure (size \<circ> working_queue))\<close>
    apply (rule unit_propagation_inner_loop_body(1)[of \<open>twl_st_of S\<close> \<open>(C' ! i, twl_clause_of C')\<close>])
    using imageI[OF WS, of \<open>(\<lambda>(a, j). (N ! j ! a, twl_clause_of (N ! j)))\<close>]
      struct_invs stgy_inv D_None unfolding S by (auto simp: N_C_C')
  have H': \<open>unit_propagation_inner_loop_body (C' ! i, twl_clause_of C') (twl_st_of ?S) \<le>
    SPEC (\<lambda>S'. twl_stgy_invs S' \<and> twl_struct_invs S')\<close>
    using * unfolding conj.left_assoc upd_S_S'
    by (simp add: weaken_SPEC)
  have \<open>unit_propagation_inner_loop_body_list (i, C) ?S
    \<le> \<Down> {(S, S'). (S' = twl_st_of S \<and> additional_WS_invs S) \<and> (twl_stgy_invs S' \<and> twl_struct_invs S')}
    (unit_propagation_inner_loop_body (C' ! i, twl_clause_of C') (twl_st_of ?S))\<close>
    apply (rule refine_add_invariants)
     apply (rule H')
    by (rule H)
  then show ?thesis unfolding upd_S_S' by simp
qed

lemma unit_propagation_inner_loop_body_list2:
  assumes
      WS: \<open>(i, C) \<in># working_queue_list S\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of S)\<close> and
      add_inv: \<open>additional_WS_invs S\<close> and
      stgy_inv: \<open>twl_stgy_invs (twl_st_of S)\<close>
  shows
  \<open>(unit_propagation_inner_loop_body_list (i, C) (set_working_queue_list (working_queue_list S - {#(i, C)#}) S),
    unit_propagation_inner_loop_body (get_clauses_l S ! C ! i, twl_clause_of (get_clauses_l S ! C))
      (set_working_queue
        (remove1_mset (get_clauses_l S ! C ! i, twl_clause_of (get_clauses_l S ! C))
        (working_queue (twl_st_of S))) (twl_st_of S)))
  \<in> \<langle>{(S, S'). S' = twl_st_of S \<and> additional_WS_invs S \<and> twl_stgy_invs S' \<and> twl_struct_invs S'}\<rangle>nres_rel\<close>
  using unit_propagation_inner_loop_body_list[OF assms]
  by (auto simp: nres_rel_def)

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
  \<open>RES (set_mset (working_queue_list S)) \<le> \<Down> {((i, C), (L, C')). L = get_clauses_l S ! C ! i \<and>
    C' = twl_clause_of (get_clauses_l S ! C)}
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
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(T, T'). T' = h T \<and> P' T}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> \<langle>{(T, T'). ?H T T' \<and> P' T}\<rangle> nres_rel\<close>)
  assumes
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q T)\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(T, T'). ?H T T' \<and> P' T \<and> Q (h T)}\<rangle> nres_rel\<close>
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
      by (rule order_trans[OF ],
          rule unit_propagation_inner_loop_body_list[of \<open>fst iC\<close> \<open>snd iC\<close> T, unfolded prod.collapse])
       (auto, auto simp add: pw_conc_inres pw_conc_nofail pw_ref_I)
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

definition clause_to_update :: \<open>'v literal \<Rightarrow> 'v twl_st_list \<Rightarrow> (nat \<times> nat) multiset\<close>where
  \<open>clause_to_update L S =
    (\<lambda>C. if get_clauses_l S ! C ! 0 = L then (0, C) else (1, C)) `#
      filter_mset
        (\<lambda>C::nat. L \<in> set (watched_l (get_clauses_l S ! C)))
        (mset [1..<length (get_clauses_l S)])\<close>

lemma distinct_mset_clause_to_update: \<open>distinct_mset (clause_to_update L C)\<close>
  unfolding clause_to_update_def
  apply (subst distinct_image_mset_inj)
   apply (auto simp: inj_on_def; fail)[]
  apply (rule distinct_mset_filter)
  apply (subst distinct_mset_mset_distinct)
  apply auto
  done

lemma in_clause_to_updateD: \<open>(a, b) \<in># clause_to_update L' T \<Longrightarrow>
       (a = 0 \<or> a = Suc 0) \<and> b < length (get_clauses_l T) \<and> 0 < b\<close>
  by (auto simp: clause_to_update_def)

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

lemma tl_drop_def: \<open>tl N = drop 1 N\<close>
  by (cases N)  auto

(* TODO MOVE to Multiset *)
lemma image_filter_cong:
  assumes \<open>\<And>C. C \<in># M \<Longrightarrow> P C \<Longrightarrow> f C = g C\<close>
  shows
    \<open>{#f C. C \<in># {#C \<in># M. P C#}#} = {#g C|C\<in># M. P C#}\<close>
  using assms by (induction M) auto

lemma image_mset_filter_swap2: \<open>{#C \<in># {#P x. x \<in># D#}. Q C #} = {#P x. x \<in># {#C| C \<in># D. Q (P C)#}#}\<close>
  by (simp add: image_mset_filter_swap)

lemma mset_dup_upto: \<open>mset (drop a N) = {#N!i. i \<in># mset_set {a..<length N}#}\<close>
proof (induction N arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons c N)
  have upt: \<open>{0..<Suc (length N)} = insert 0 {1..<Suc (length N)}\<close>
    by auto
  then have H: \<open>mset_set {0..<Suc (length N)} = add_mset 0 (mset_set {1..<Suc (length N)})\<close>
    unfolding upt by auto
  have mset_case_Suc: \<open>{#case x of 0 \<Rightarrow> c | Suc x \<Rightarrow> N ! x . x \<in># mset_set {Suc a..<Suc b}#} =
    {#N ! (x-1) . x \<in># mset_set {Suc a..<Suc b}#}\<close> for a b
    by (rule image_mset_cong) (auto split: nat.splits)
  have Suc_Suc: \<open>{Suc a..<Suc b} = Suc ` {a..<b}\<close> for a b
    by auto
  then have mset_set_Suc_Suc: \<open>mset_set {Suc a..<Suc b} = {#Suc n. n \<in># mset_set {a..<b}#}\<close> for a b
    unfolding Suc_Suc by (subst image_mset_mset_set[symmetric]) auto
  have *: \<open>{#N ! (x-Suc 0) . x \<in># mset_set {Suc a..<Suc b}#} = {#N ! x . x \<in># mset_set {a..<b}#}\<close>
    for a b
    by (auto simp add: mset_set_Suc_Suc)
  show ?case
    apply (cases a)
    using Cons[of 0] Cons by (auto simp: nth_Cons drop_Cons H mset_case_Suc *)
qed

(* END Move *)

lemma watched_twl_clause_of_watched: \<open>watched (twl_clause_of x) = mset (watched_l x)\<close>
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
    \<open>{#(N ! snd (if N ! x ! 0 = L' then (0, x) else (1, x)) ! fst (if N ! x ! 0 = L' then (0, x) else (1, x)),
        TWL_Clause (mset (take 2 (N ! snd (if N ! x ! 0 = L' then (0, x) else (1, x)))))
          (mset (drop 2 (N ! snd (if N ! x ! 0 = L' then (0, x) else (1, x)))))).
      x \<in># mset_set {x. Suc 0 \<le> x \<and> x < length N \<and> L' \<in> set (take 2 (N ! x))}#} =
    Pair L' `#
      {#C \<in># {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take U (tl N))#} +
            {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc U) N)#}.
      L' \<in># watched C#}\<close>
    (is \<open>{#(?L' x, ?C x). x \<in># mset_set ?S#} = Pair L' `# ?C'\<close>)
  proof -
    have mset_tl_upto: \<open>mset (tl N) = {#N!i. i \<in># mset_set {1..<length N}#}\<close>
      unfolding tl_drop_def mset_dup_upto by simp
    have L': \<open>{#(?L' x, ?C x). x \<in># mset_set ?S#} = {#(L', ?C x). x \<in># mset_set ?S#}\<close>
    proof (rule image_mset_cong, goal_cases)
      case (1 x)
      then have \<open>N!x \<in> set (tl N)\<close>
        unfolding tl_drop_def in_set_drop_conv_nth by auto
      then obtain i j where \<open>take 2 (N!x) = [i, j]\<close>
        using watched_tl_N[of \<open>N!x\<close>] by auto
      then show ?case using 1 by (auto simp: take_2_if split: if_splits)
    qed
    also have L'': \<open>\<dots> = Pair L' `# {#?C x. x \<in># mset_set ?S#}\<close>
      by auto
    also have \<open>\<dots> = Pair L' `# {#TWL_Clause
      (mset (take 2 (N ! x)))
      (mset (drop 2 (N ! x))). x \<in># mset_set ?S#}\<close>
      by (auto intro!: image_mset_cong)
    also have \<open>\<dots> = Pair L' `# ?C'\<close>
      apply (rule arg_cong[of _ _ \<open>op `# (Pair L')\<close>])
      unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc append_take_drop_id
        mset_tl_upto by (auto simp: image_mset_filter_swap2)
    finally show ?thesis .
  qed
  then show ?thesis
    by (auto simp del: filter_union_mset simp: T split_beta clause_to_update_def split: if_splits)
qed

lemma additional_WS_invs_set_working_queue_iff:
  assumes \<open>additional_WS_invs T\<close>
  shows \<open>additional_WS_invs (set_working_queue_list WS (set_pending_list Q T)) \<longleftrightarrow>
     ((\<forall>x\<in>#WS.
         case x of (i, C) \<Rightarrow>
           (i = 0 \<or> i = Suc 0) \<and>
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
    subgoal for S S' T T' L L'
      by (clarsimp simp add: additional_WS_invs_set_working_queue_iff
          distinct_mset_clause_to_update in_clause_to_updateD)
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
     L \<leftarrow> SPEC (\<lambda>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))));
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

lemma get_conflict_list_get_conflict_state_spec:
  assumes \<open>S' = twl_st_of S\<close> and \<open>additional_WS_invs S\<close>
  shows \<open>((get_conflict_list S = Some [], S), (get_conflict S' = Some {#}, S'))
  \<in> {((brk, S), (brk', S')). brk = brk' \<and> S' = twl_st_of S \<and> additional_WS_invs S}\<close>
  using assms by (auto simp: get_conflict_list_Some_nil_iff)

(* END Move *)

text \<open>
  We here strictly follow \<^term>\<open>cdcl\<^sub>W_restart_mset.skip\<close> and \<^term>\<open>cdcl\<^sub>W_restart_mset.resolve\<close>:
  if the level is 0, we should directly return \<^term>\<open>{#}\<close>. This also avoids the \<^term>\<open>If (C = 0)\<close>
  condition.
  \<close>
definition skip_and_resolve_loop_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>skip_and_resolve_loop_list S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv (twl_st_of S\<^sub>0) (brk, twl_st_of S) \<and>
         additional_WS_invs S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_list S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, WS, Q) = S in
          do {
            ASSERT(M \<noteq> []);
            let D' = the (get_conflict_list S);
            (L, C) \<leftarrow> SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail_list S));
            if -L \<notin># mset D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, WS, Q))}
            else
              if get_maximum_level M (remove1_mset (-L) (mset D')) = count_decided M
              then
                do {RETURN (resolve_cls_list L D' (if C = 0 then [L] else N!C) = [],
                   (tl M, N, U, Some (resolve_cls_list L D' (if C = 0 then [L] else N!C)),
                     NP, UP, WS, Q))}
              else
                do {RETURN (True, S)}
          }
        )
        (get_conflict_list S\<^sub>0 = Some [], S\<^sub>0);
      RETURN S
    }
  \<close>

lemma get_trail_twl_st_of_nil_iff: \<open>get_trail (twl_st_of T) = [] \<longleftrightarrow> get_trail_list T = []\<close>
  by (cases T) (auto simp: convert_lits_l_def)

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
    by (cases S, cases \<open>get_trail_list S\<close>; cases \<open>hd (get_trail_list S)\<close>)
      (use that in \<open>auto split: if_splits\<close>)
  have H: \<open>SPEC (\<lambda>(L, C). Propagated L C = hd (get_trail_list S))
    \<le> \<Down> {((L, C), (L', C')). L = L' \<and> C' = (if C = 0 then {#L#} else mset (get_clauses_l S! C))}
    (SPEC (\<lambda>(L, C).
    Propagated L C = hd (get_trail S')))\<close> if [simp]: \<open>S' = twl_st_of S\<close> and \<open>get_trail_list S \<noteq> []\<close>
    for S :: \<open>'v twl_st_list\<close> and S' :: \<open>'v twl_st\<close>
    using that apply (cases S; cases S'; cases \<open>get_trail_list S\<close>; cases \<open>hd (get_trail_list S)\<close> ;
        cases \<open>get_trail S'\<close>; cases \<open>hd (get_trail S')\<close>)
    apply (auto split: if_splits)[15]
    apply (rule RES_refine)
    by (auto split: if_splits)
  have H:
    \<open>(skip_and_resolve_loop_list, skip_and_resolve_loop) \<in>
    ?R \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> additional_WS_invs T}\<rangle> nres_rel\<close>
    apply clarify
    unfolding skip_and_resolve_loop_list_def skip_and_resolve_loop_def
    apply (refine_rcg get_conflict_list_get_conflict_state_spec H; remove_dummy_vars)
    subgoal by auto
    subgoal by auto
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk T brk' T'
      apply (cases \<open>get_trail_list T\<close>; cases \<open>hd (get_trail_list T)\<close>)
      by (auto simp: skip_and_resolve_loop_inv_def get_trail_twl_st_of_nil_iff)
    subgoal by (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def)
    subgoal by (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def)
    subgoal by (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def)
    subgoal by (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def)

    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      by (cases \<open>M''\<close>) (auto simp: skip_and_resolve_loop_inv_def get_trail_twl_st_of_nil_iff
          additional_WS_invs_def)
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      by (auto simp: skip_and_resolve_loop_inv_def)
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      by (cases \<open>M''\<close>) (auto simp: skip_and_resolve_loop_inv_def additional_WS_invs_def
          resolve_cls_list_nil_iff) -- \<open>needs 1 min\<close>
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' E brk'' brk'''
      M''' N''' U''' D''' NP''' UP''' WS''' Q'''
      M'' N'' U'' D'' NP'' UP'' WS'' Q''
      by (cases D'') (auto simp:  skip_and_resolve_loop_inv_def)

    subgoal
      by (auto simp: resolve_cls_list_nil_iff skip_and_resolve_loop_inv_def additional_WS_invs_def)
    done
  have H: \<open>(skip_and_resolve_loop_list, skip_and_resolve_loop)
    \<in> ?R \<rightarrow>
       \<langle>{(T::'v twl_st_list, T').
         T' = twl_st_of T \<and> additional_WS_invs T \<and>
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
  show ?thesis
    using H by simp
qed

definition backtrack_list :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres" where
  \<open>backtrack_list S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        L \<leftarrow> SPEC(\<lambda>L. L = lit_of (hd M));
        ASSERT(get_level M L = count_decided M);
        ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);

        if length (the D) > 1
        then do {
          L' \<leftarrow> SPEC(\<lambda>L'. L' \<in># mset (the D) \<and> get_level M L' = get_maximum_level M (mset (the D) - {#-L#}));
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, UP, WS, {#L#})
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset (mset (the D)) UP, WS, {#L#})
        }
      }
    }
  \<close>

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

lemma mem_set_trans:
  \<open>A = B \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> B\<close>
  by auto

lemma fun_rel_syn_invert:
  \<open>a = a' \<Longrightarrow> b = b' \<Longrightarrow> a \<rightarrow> b = a' \<rightarrow> b'\<close>
  by auto
lemma rel_invert:
  \<open>a = a'  \<Longrightarrow> \<langle>a\<rangle> R = \<langle>a'\<rangle>R\<close>
  by auto

method match_spec =
  (match conclusion in \<open>(f, g) \<in> R\<close> for f g R \<Rightarrow>
    \<open>match premises in I: \<open>(f, g) \<in> R'\<close> for R'
       \<Rightarrow> \<open>rule mem_set_trans[OF _ I]\<close>\<close>)

method match_fun_rel =
  ((match conclusion in \<open>_ \<rightarrow> _ = _ \<rightarrow> _\<close> \<Rightarrow> \<open>rule fun_rel_syn_invert\<close> |
   match conclusion in \<open>\<langle>_\<rangle>_ = \<langle>_\<rangle>_\<close> \<Rightarrow> \<open>rule rel_invert\<close>)+)

lemma additional_WS_invs_backtrack_iff:
  assumes
   \<open>additional_WS_invs (M2 @ M1', N', U', C1, NP', UP', WS', Q)\<close>
  shows \<open>additional_WS_invs (Propagated L D # M1',
      N' @ N'', U'', C2, NP''', UP''', {#}, Q') \<longleftrightarrow>
    ((D > 0 \<longrightarrow> L \<in> set (watched_l ((N' @ N'') ! D))) \<and> D < length (N' @ N'') \<and> U'' < length (N' @ N''))\<close>
  using assms unfolding additional_WS_invs_def by (auto 0 5 simp add: all_conj_distrib nth_append)


lemma backtrack_list_spec:
  \<open>(backtrack_list, backtrack) \<in>
    {(S::'v twl_st_list, S'). S' = twl_st_of S \<and> get_conflict_list S \<noteq> None \<and> get_conflict_list S \<noteq> Some [] \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and> additional_WS_invs S \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
    \<langle>{(T::'v twl_st_list, T'). T' = twl_st_of T \<and> get_conflict_list T = None \<and> additional_WS_invs T \<and>
       twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and> working_queue_list T = {#} \<and>
       pending_list T \<noteq> {#}}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close>)
proof -
  have obtain_decom: \<open>\<exists>K. \<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd (convert_lits_l N M')))
    (mset E)))\<close> if
    decomp: \<open>\<exists>K. \<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits_l N M')) \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd (convert_lits_l N M')))
    (mset E)))\<close>
    (is \<open>\<exists>K. \<exists>M1 M2. ?P K M1 M2 \<and> ?Q K\<close>)
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
      apply -
      apply (rule exI[of _ K], rule exI[of _ M1'], rule exI[of _ M2'])
      by (cases K') (use Q in \<open>auto split: if_splits\<close>)
  qed

  have H: \<open>SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
    get_level M' K = get_maximum_level M' (remove1_mset (- L) (mset (the D'))) + 1)
    \<le> \<Down> {(M1', M1). M1 = convert_lits_l N M1'}
    (SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
    get_level M K = get_maximum_level M (remove1_mset (- L') (the D)) + 1))\<close>
    if
      help_the_unificacton: \<open>additional_WS_invs (M', N, thing_we_dont_care)\<close> and
      H: \<open>L' = lit_of (hd (convert_lits_l N M'))\<close> \<open>M = convert_lits_l N M'\<close>
      \<open>D \<noteq> None\<close> \<open>L = lit_of (hd (convert_lits_l N M'))\<close> \<open>mset (the D') = the D\<close>
    for M M' L' L D D' N thing_we_dont_care
  proof (rule RES_refine, clarify)
    fix M1 K M2
    assume
      lev: \<open>get_level M' K = get_maximum_level M' (remove1_mset (- L) (mset (the D'))) + 1\<close> and
      \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M')\<close>
    then have \<open>(Decided K # convert_lits_l N M1, convert_lits_l N M2) \<in> set (get_all_ann_decomposition M)\<close>
      by (force simp: get_all_ann_decomposition_convert_lits_l H)
    then show \<open>\<exists>s'\<in>{M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
                     get_level M K =
                     get_maximum_level M (remove1_mset (- L') (the D)) + 1}.
          (M1, s') \<in> {(M1', M1). M1 = convert_lits_l N M1'}\<close>
      using lev by (auto simp: H)
  qed
  have bt:
    \<open>(backtrack_list, backtrack) \<in> ?R \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> (* get_conflict_list T = None \<and> *) additional_WS_invs T}\<rangle> nres_rel\<close>
    apply clarify
    unfolding backtrack_list_def backtrack_def
    apply (refine_vcg H; remove_dummy_vars)
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q'
      by (cases M) auto
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q'
      by (cases M) (auto simp: convert_lits_l_def)
    subgoal for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      by (cases M) auto
    subgoal for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L'
      using obtain_decom[of _ M'] by simp
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
    subgoal premises p for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L' L M1' M1 L'' L'''
    proof -
      have E: \<open>mset E = add_mset K (add_mset L''' (mset E - {#K, L'''#}))\<close>
        if \<open>K \<in> set E\<close> and \<open>K \<noteq> L'''\<close>
        for K
        using p(1-4,25-27) that by (auto simp: multiset_eq_iff)

      obtain c M2 K where
         M': \<open>M' = c @ M2 @ Decided K # M1'\<close>
        using p(22) by (auto dest!: get_all_ann_decomposition_exists_prepend)
      define M'' where \<open>M'' = c @ M2 @ Decided K # []\<close>
      then have M'': \<open>additional_WS_invs (M'' @ M1',  N', U', D', NP', UP', WS', Q')\<close>
        using M' p(6) by auto
      have uL''_E: \<open>- lit_of (hd (convert_lits_l N' M')) \<in># mset E\<close>
        using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
            \<open>convert_to_state (twl_st_of (M', N', U', D', NP', UP', WS', Q'))\<close>] p
        by (auto simp: )
        have \<open>x \<in> set M1' \<Longrightarrow>
          convert_lit N' x =
          convert_lit (N' @ [- lit_of (hd (map (convert_lit N') M')) # L''' # remove1 (- lit_of (hd (map (convert_lit N') M')))
          (remove1 L''' E)]) x\<close> for x
          using p(6) by (cases x) (auto simp: nth_append additional_WS_invs_def M')
        then have conv: \<open>convert_lits_l N' M1' =
          convert_lits_l (N' @ [- lit_of (hd (convert_lits_l N' M')) # L''' #
          remove1 (- lit_of (hd (convert_lits_l N' M'))) (remove1 L''' E)]) M1'\<close>
          unfolding convert_lits_l_def by auto
      have L'''_L'': \<open>L''' = L''\<close>
        using p(26) by simp
      have L': \<open>L' = lit_of (hd M')\<close> and L: \<open>L = lit_of (hd M)\<close>
        using p(14,15) by simp_all
      have L''_not_hd: \<open>lit_of (hd (convert_lits_l N' M')) \<noteq> - L''\<close>
        using p by (simp add: uminus_lit_swap)
      have \<open>no_dup M\<close>
        using p(1,9) unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
           cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
      then have \<open>L \<noteq> -L'''\<close>
        using p(16, 23-29) by auto
      moreover
        have E': \<open>mset E = add_mset (- lit_of (hd (convert_lits_l N' M')))
        (add_mset L''' (mset E - {#- lit_of (hd (convert_lits_l N' M')), L'''#}))\<close>
          by (rule E) (use L'''_L'' uL''_E L''_not_hd in \<open>auto intro!: simp: \<close>)
      moreover have N': \<open>N' \<noteq> []\<close> and U': \<open>U' < length N'\<close>
        using p(6) by (auto simp: additional_WS_invs_def)
      ultimately have 1: \<open>((Propagated (- L') (length N') # M1',
      N' @ [[- L', L''] @ remove1 (- L') (remove1 L'' (the D'))],
      U', None, NP', UP', WS', {#L'#}),
       Propagated (- L) (the D) # M1, N,
       add_mset (TWL_Clause {#- L, L'''#} (the D - {#- L, L'''#})) U,
        None, NP, UP, WS, {#L#})
      \<in> {(T, T'). additional_WS_invs T}\<close>
        using p M'' conv by (simp add: additional_WS_invs_backtrack_iff cdcl\<^sub>W_restart_mset_state)

      have 2: \<open>((Propagated (- L') (length N') # M1',
        N' @ [[- L', L''] @ remove1 (- L') (remove1 L'' (the D'))],
        U', None, NP', UP', WS', {#L'#}),
        Propagated (- L) (the D) # M1, N,
        add_mset (TWL_Clause {#- L, L'''#} (the D - {#- L, L'''#})) U,
        None, NP, UP, WS, {#L#})
        \<in> {(T, T'). T' = twl_st_of T}\<close>
        using p N' E'[symmetric] conv[symmetric] U' conv[symmetric] by simp
      show ?thesis using 1 2 by fast
    qed
    subgoal premises p for E M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' L L' M1' M1
    proof -
      obtain c M2 K where
         M': \<open>M' = c @ M2 @ Decided K # M1'\<close>
        using p(22) by (auto dest!: get_all_ann_decomposition_exists_prepend)
      define M'' where \<open>M'' = c @ M2 @ Decided K # []\<close>
      then have M'': \<open>additional_WS_invs (M'' @ M1',  N', U', D', NP', UP', WS', Q')\<close>
        using M' p(6) by auto
      have uL''_E: \<open>- lit_of (hd (convert_lits_l N' M')) \<in># mset E\<close>
        using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
            \<open>convert_to_state (twl_st_of (M', N', U', D', NP', UP', WS', Q'))\<close>] p
        by (auto simp: )

      have 1: \<open>((Propagated (- L) 0 # M1', N', U', None, NP', add_mset (mset (the D')) UP', WS',
       {#L#}), Propagated (- L') (the D) # M1, N, U, None, NP, add_mset (the D) UP, WS, {#L'#})
      \<in> {(T, T'). additional_WS_invs T}\<close>
        using p M'' by (simp add: additional_WS_invs_def cdcl\<^sub>W_restart_mset_state)

      have \<open>E = [- lit_of (hd (convert_lits_l N' M'))]\<close>
        using p by (cases E) simp_all
      then have 2: \<open>((Propagated (- L) 0 # M1', N', U', None, NP', add_mset (mset (the D')) UP', WS',
        {#L#}), Propagated (- L') (the D) # M1, N, U, None, NP, add_mset (the D) UP, WS, {#L'#})
        \<in> {(T, T'). T' = twl_st_of T}\<close>
        using p by simp
      show ?thesis using 1 2 by fast
    qed
    done
  have KK:
    \<open>get_conflict_list T = None \<longleftrightarrow> get_conflict (twl_st_of T) = None\<close>
    \<open>working_queue_list T = {#} \<longleftrightarrow> working_queue (twl_st_of T) = {#}\<close>
    \<open>pending_list T = {#} \<longleftrightarrow> pending (twl_st_of T) = {#}\<close>
    for T
    by (cases T; auto)+
  have R: \<open>?R = {(S, S'). S' = twl_st_of S \<and>
                 get_conflict (twl_st_of S) \<noteq> None \<and>
                 (get_conflict_list S \<noteq> Some [] \<and> additional_WS_invs S) \<and>
                 working_queue (twl_st_of S) = {#} \<and>
                 pending (twl_st_of S) = {#} \<and>
                 (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) S') \<and>
                 (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) S') \<and>
                 twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)}\<close>
    by auto
  have \<open> (backtrack_list, backtrack)
    \<in> {(S::'v twl_st_list, S'). S' = twl_st_of S \<and>
                 get_conflict (twl_st_of S) \<noteq> None \<and>
                 (get_conflict_list S \<noteq> Some [] \<and> additional_WS_invs S) \<and>
                 working_queue (twl_st_of S) = {#} \<and>
                 pending (twl_st_of S) = {#} \<and> (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) S') \<and> (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) S') \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
       \<langle>{(T, T'). T' = twl_st_of T \<and> additional_WS_invs T \<and> (get_conflict (twl_st_of T) = None) \<and> twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and> working_queue (twl_st_of T) = {#} \<and> pending (twl_st_of T) \<noteq> {#}}\<rangle>nres_rel\<close>
    unfolding KK
    apply (rule refine_add_inv)
    subgoal
      using bt unfolding R unfolding KK .
    subgoal for S
      unfolding KK
      apply (cases S)
      by (rule order_trans[OF backtrack_spec[of \<open>twl_st_of S\<close>]]) auto
    done
  then show bt': \<open>(backtrack_list, backtrack) \<in> ?R \<rightarrow> ?I\<close>
    unfolding KK apply -
    by match_spec (match_fun_rel; fast?)+
qed

definition cdcl_twl_o_prog_list :: "'v twl_st_list \<Rightarrow> (bool \<times> 'v twl_st_list) nres"  where
  \<open>cdcl_twl_o_prog_list S =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S in
      do {
        if D = None
        then
          if (\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))))
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
thm decide[to_pred]


lemma cdcl_twl_o_prog_list_spec:
  \<open>(cdcl_twl_o_prog_list, cdcl_twl_o_prog) \<in>
    {(S, S'). S' = twl_st_of S \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and> no_step cdcl_twl_cp (twl_st_of S) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and> additional_WS_invs S} \<rightarrow>
    \<langle>{((brk, T), (brk', T')). T' = twl_st_of T \<and> brk = brk' \<and> additional_WS_invs T \<and>
    (get_conflict_list T \<noteq> None \<longrightarrow> get_conflict_list T = Some [])\<and>
       twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and> working_queue_list T = {#} (* \<and>
       (\<not>brk \<longrightarrow> pending_list T \<noteq> {#}) *)}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have twl_prog:
    \<open>(cdcl_twl_o_prog_list, cdcl_twl_o_prog) \<in> ?R \<rightarrow>
      \<langle>{(S, S').
         (fst S' = (fst S) \<and> snd S' = twl_st_of (snd S)) \<and> additional_WS_invs (snd S)}\<rangle> nres_rel\<close>
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
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (auto simp add: get_conflict_list_Some_nil_iff)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T T'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
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
       (fst U' = id (fst U) \<and> snd U' = twl_st_of (snd U)) \<and> additional_WS_invs (snd U) \<and>
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
    {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S \<and>
       working_queue_list S = {#} \<and>
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
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_list_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of S)\<close> and \<open>twl_stgy_invs (twl_st_of S)\<close> and
    \<open>working_queue_list S = {#}\<close> and
    \<open>get_conflict_list S = None\<close> and \<open>additional_WS_invs S\<close>
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