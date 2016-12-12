theory CDCL_Two_Watched_Literals_List_Watched
  imports CDCL_Two_Watched_Literals_List
begin

section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>

type_synonym working_queue_wl = "nat multiset"
type_synonym watched = "nat list"
type_synonym 'v lit_queue_wl = "'v literal multiset"

type_synonym 'v twl_st_wl =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v clause_l option \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl \<times>
    ('v literal \<Rightarrow> watched)"


fun working_queue_wl :: "'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> working_queue_wl" where
  \<open>working_queue_wl (_, _, _, _, _, _, _, W) L i = mset (drop i (W L))\<close>

fun get_trail_wl :: "'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_wl (M, _, _, _, _, _, _, _) = M\<close>

fun pending_wl :: "'v twl_st_wl \<Rightarrow> 'v lit_queue_wl" where
  \<open>pending_wl (_, _, _, _, _, _, Q, _) = Q\<close>

fun set_pending_wl :: "'v lit_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl" where
  \<open>set_pending_wl Q (M, N, U, D, NP, UP, _, W) = (M, N, U, D, NP, UP, Q, W)\<close>

fun get_conflict_wl :: "'v twl_st_wl \<Rightarrow> 'v clause_l option" where
  \<open>get_conflict_wl (_, _, _, D, _, _, _, _) = D\<close>


definition lits_of_mm :: \<open>'a clauses \<Rightarrow> 'a literal multiset\<close> where
\<open>lits_of_mm Ls = \<Union># Ls\<close>

fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, U, D, NP, UP, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># lits_of_mm (mset `# mset (tl N)). mset (W L) = clause_to_update L (M, N, U, D, NP, UP, {#}, {#}))\<close>

fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> watched\<close> where
  \<open>watched_by (M, N, U, D, NP, UP, Q, W) L = W L\<close>

fun update_watched :: \<open>'v literal \<Rightarrow> watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, U, D, NP, UP, Q, W) = (M, N, U, D, NP, UP, Q, W(L:= WL))\<close>

fun delete_index_and_swap where
  \<open>delete_index_and_swap l i = (butlast(l[i := last l]))\<close>

text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>. It would be more memory efficient
  to directly iterate over \<^term>\<open>W L\<close>, but this is not compatible with multisets.\<close>
definition unit_propagation_inner_loop_body_wl :: "'v literal \<Rightarrow> nat \<Rightarrow>
  'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres"  where
  \<open>unit_propagation_inner_loop_body_wl K w S = do {
    ASSERT(w < length (watched_by S K));
    let C = (watched_by S K) ! w;
    let (M, N, U, D, NP, UP, Q, W) = S;
    ASSERT(no_dup M);
    ASSERT(C < length N);
    ASSERT(0 < length (N!C));
    let i = (if (N!C) ! 0 = K then 0 else 1);
    ASSERT(i < length (N!C));
    ASSERT(1-i < length (N!C));
    let L = ((N!C)) ! i;
    ASSERT(L = K);
    let L' = ((N!C)) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> RETURN (valued M L');
    if val_L' = Some True
    then RETURN (w+1, S)
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (w+1, (M, N, U, Some (N!C), NP, UP, {#}, W))}
        else do {RETURN (w+1, (Propagated L' C # M, N, U, D, NP, UP, add_mset (-L') Q, W))}
      else do {
        ASSERT(snd f < length (N!C));
        let K' = (N!C) ! (snd f);
        let N' = list_update N C (swap (N!C) i (snd f));
        ASSERT(K \<noteq> K');
        RETURN (w, (M, N', U, D, NP, UP, Q, W(K := delete_index_and_swap (watched_by S L) w, K':= W K' @ [C])))
      }
    }
   }
\<close>

fun st_l_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl  \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl None (M, N, C, D, NP, UP, Q, W) = (M, N, C, D, NP, UP, {#}, Q)\<close>
| \<open>st_l_of_wl (Some (L, j)) (M, N, C, D, NP, UP, Q, W) =
    (M, N, C, D, NP, UP, (if D \<noteq> None then {#} else working_queue_wl (M, N, C, D, NP, UP, Q, W) L j,
      Q))\<close>

fun twl_st_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl  \<Rightarrow> 'v twl_st\<close> where
  \<open>twl_st_of_wl L S = twl_st_of (map_option fst L) (st_l_of_wl L S)\<close>

fun remove_one_lit_from_wq :: "nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l" where
  \<open>remove_one_lit_from_wq L (M, N, C, D, NP, UP, WS, Q) = (M, N, C, D, NP, UP, remove1_mset L WS, Q)\<close>

lemma butlast_list_update:
  \<open>w < length xs \<Longrightarrow> butlast (xs[w := last xs]) = take w xs @ butlast (last xs # drop (Suc w) xs)\<close>
  by (induction xs arbitrary: w) (auto split: nat.splits if_splits simp: upd_conv_take_nth_drop)

lemma mset_butlast_remove1_mset: \<open>xs \<noteq> [] \<Longrightarrow> mset (butlast xs) = remove1_mset (last xs) (mset xs)\<close>
  apply (subst(2) append_butlast_last_id[of xs, symmetric])
   apply assumption
  apply (simp only: mset_append)
  by auto

lemma last_list_update_to_last:
  \<open>last (xs[x := last xs]) = last xs\<close>
  by (metis last_list_update list_update.simps(1))

lemma Collect_minus_single_Collect: \<open>{x. P x} - {a} = {x . P x \<and> x \<noteq> a}\<close>
  by auto

lemma mset_set_mset_set_minus_id_iff:
  assumes \<open>finite A\<close>
  shows \<open>mset_set A = mset_set (A - B) \<longleftrightarrow> (\<forall>b \<in> B. b \<notin> A)\<close>
proof -
 have f1: "mset_set A = mset_set (A - B) \<longleftrightarrow> A - B = A"
    using assms by (metis (no_types) finite_Diff finite_set_mset_mset_set)
  then show ?thesis
    by blast
qed

lemma mset_set_eq_mset_set_iff:
  \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set A = mset_set B \<longleftrightarrow> A = B\<close>
  using finite_set_mset_mset_set by fastforce

lemma mset_set_eq_mset_set_more_conds:
  \<open>finite {x. P x} \<Longrightarrow> mset_set {x. P x} = mset_set {x. Q x \<and> P x} \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)\<close>
  (is \<open>?F \<Longrightarrow> ?A \<longleftrightarrow> ?B\<close>)
proof -
  assume ?F
  then have \<open>?A \<longleftrightarrow> (\<forall>x \<in> {x. P x}. x \<in> {x. Q x \<and> P x})\<close>
    by (subst mset_set_eq_mset_set_iff) auto
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)\<close>
    by blast
  finally show ?thesis .
qed

lemma unit_propagation_inner_loop_body_wl_unit_propagation_inner_loop_body_l:
  fixes S :: \<open>'v twl_st_wl\<close> and L :: \<open>'v literal\<close> and w :: nat
  defines
    T_def[simp]:  \<open>T \<equiv> remove_one_lit_from_wq (watched_by S L ! w) (st_l_of_wl (Some (L, w)) S)\<close> and
    S'_def[simp]: \<open>S' \<equiv> st_l_of_wl (Some (L, w)) S\<close> and
    S''_def[simp]:\<open>S'' \<equiv> twl_st_of_wl (Some (L, w)) S\<close> and
    C'_def[simp]: \<open>C' \<equiv> watched_by S L ! w\<close>
  defines
    C''_def[simp]:\<open>C'' \<equiv> get_clauses_l S' ! C'\<close>
  assumes
    w_le: \<open>w < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    corr_w: \<open>correct_watching S\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>additional_WS_invs S'\<close> and
    stgy_inv: \<open>twl_stgy_invs S''\<close>
  shows \<open>unit_propagation_inner_loop_body_wl L w S \<le>
   \<Down> {((w', S'), S). S = st_l_of_wl (Some (L, w')) S' \<and> correct_watching S'}
     (unit_propagation_inner_loop_body_l L C' T)\<close>
proof -
  have val: \<open>(valued a b, valued a' b') \<in> Id\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' b b'
    by (auto simp: that)
  have f: \<open>find_unwatched a (b ! c) \<le> \<Down> Id (find_unwatched a' (b' ! c'))\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> and \<open>c = c'\<close> for a a' b b' c c'
    by (auto simp: that)
  obtain M N U NP UP Q W where
    S: \<open>S = (M, N, U, None, NP, UP, Q, W)\<close>
    using confl by (cases S) auto
  have T'[unfolded T_def, unfolded S]: \<open>remove_one_lit_from_wq (watched_by S L ! w)
           (st_l_of_wl (Some (L, w)) (M, N, U, None, NP, UP, Q, W)) =
           (M, N, U, None, NP, UP,
             remove1_mset (watched_by S L ! w) (working_queue_wl (M, N, U, None, NP, UP, Q, W) L w),
             Q)\<close>
    by auto
  have [simp]: \<open>remove1_mset (W L ! w) (mset (drop w (W L))) = mset (drop (Suc w) (W L))\<close>
    using w_le by (cases \<open>drop w (W L)\<close>) (auto simp: drop_Cons' drop_Suc drop_tl remove1_mset_add_mset_If
        trivial_add_mset_remove_iff nth_via_drop)
  have \<open>\<not> length xs \<le> Suc w  \<Longrightarrow> last xs \<in> set (drop (Suc w) xs)\<close>
    if \<open>w < length xs\<close> for xs w
    using that by (metis List.last_in_set drop_eq_Nil last_drop not_le)
  then have mset_drop_butlast[simp]: \<open>mset (drop w (butlast (xs[w := last xs]))) = mset (drop (Suc w) xs)\<close>
    if \<open>w < length xs\<close> for xs w
    using that by (auto simp: butlast_list_update S mset_butlast_remove1_mset
        single_remove1_mset_eq)

  have inv: \<open>twl_st_inv S''\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S'')\<close> and
    valid: \<open>valid_annotation S''\<close>
    using struct_invs by (auto simp: twl_struct_invs_def)
  have
    w_q_inv: \<open>working_queue_inv S''\<close> and
    dist: \<open>distinct_queued S''\<close> and
    no_dup: \<open>no_duplicate_queued S''\<close> and
    no_dup_queued:\<open>no_duplicate_queued S''\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have n_d: \<open>no_dup M\<close>
    using cdcl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps comp_def S)

  define i :: nat where
    \<open>i \<equiv> if N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! 0 = L then 0 else 1\<close>
  let ?L = \<open>C'' ! i\<close>
  let ?L' = \<open>C'' ! (Suc 0 - i)\<close>
  have cons_M: \<open>consistent_interp (lits_of_l M)\<close>
    using n_d distinct_consistent_interp by fast
  have N_take_drop: \<open>tl N = take U (tl N) @ drop (Suc U) N\<close>
    by (simp add: drop_Suc)
  let ?C' = \<open>twl_clause_of C''\<close>
  have WL_w_in_drop: \<open>W L ! w \<in> set (drop w (W L))\<close>
    using w_le by (auto simp: S in_set_drop_conv_nth)
  then have WS: \<open>C' \<in># working_queue_l S'\<close>
    using w_le by (auto simp: S)
  have C'_N_U_or: \<open>?C' \<in># twl_clause_of `# mset (take U (tl N)) \<or> ?C' \<in># twl_clause_of `# mset (drop (Suc U) N)\<close>
    using WS valid
    by (auto simp: S twl_struct_invs_def split: prod.splits simp del: twl_clause_of.simps)
  then have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using inv by (auto simp: twl_st_inv.simps S simp del: twl_clause_of.simps)
  have C'_N_U: \<open>?C' \<in># twl_clause_of `# mset (tl N)\<close>
    using C'_N_U_or apply (subst N_take_drop)
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric] take_tl .
  have watched_C': \<open>mset (watched_l C'') = {#?L, ?L'#}\<close>
    using struct i_def by (auto simp: length_list_2 take_2_if S)+
  have dist_C'': \<open>distinct C''\<close>
    using struct by (simp only: twl_clause_of.simps struct_wf_twl_cls.simps distinct_mset_mset_distinct
        mset_append[symmetric] watched_l.simps unwatched_l.simps append_take_drop_id)
  have mset_watched_C: \<open>mset (watched_l C'') = {#watched_l C'' ! i, watched_l C'' ! (Suc 0 - i)#}\<close>
    using i_def watched_C' by (cases \<open>twl_clause_of (get_clauses_l S' ! C')\<close>) (auto simp: take_2_if)
  have two_le_length_C: \<open>2 \<le> length C''\<close>
    by (metis length_take linorder_not_le min_less_iff_conj numeral_2_eq_2 order_less_irrefl
        size_add_mset size_eq_0_iff_empty size_mset watched_C' watched_l.simps)
  have C_N_U: \<open>C' < length (get_clauses_l S')\<close>
    using WS add_inv by (auto simp: S additional_WS_invs_def)
  obtain WS' where WS'_def: \<open>working_queue_l S' = add_mset C' WS'\<close>
    using multi_member_split[OF WS] by (auto simp: S)
  have L: \<open>L \<in> set (watched_l C'')\<close>
    using valid S WL_w_in_drop by (auto simp: WS'_def)
  have C'_i[simp]: \<open>C''!i = L\<close>
    using L two_le_length_C S by (auto simp: take_2_if i_def split: if_splits)
  then have [simp]: \<open>N! (W L ! w)!i = L\<close>
    by (auto simp: S)
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
    using WS'_def no_dup_queued by (simp add: S all_conj_distrib)
  from mset_le_add_mset_decr_left2[OF this] have uL_M: \<open>-L \<in> lits_of_l M\<close>
    (* TODO tune proof *)
    apply (auto dest!: simp: (* lits_of_def *) lits_of_l_convert_lits_l)
    by (metis imageI lits_of_def lits_of_l_convert_lits_l)
  show ?thesis
    using w_le confl corr_w
    unfolding T_def
    unfolding unit_propagation_inner_loop_body_wl_def unit_propagation_inner_loop_body_l_def S T'
      C'_def
    supply [[goals_limit=10]]
    apply (rewrite at \<open>let _ = watched_by _ _ ! _ in _\<close> Let_def)
    apply (refine_vcg val f; remove_dummy_vars)
    unfolding i_def[symmetric]
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: clause_to_update_def)
    subgoal by (simp add: clause_to_update_def)
    subgoal by simp
    subgoal using uL_M by auto
    subgoal premises p for val_L' val_L f' f
    proof -
      let ?K = \<open>N ! (W L ! w) ! snd f'\<close>
      thm p[unfolded S[symmetric], unfolded C'_def[symmetric], unfolded C''_def[symmetric]]
      note C'_le_length = p(6) and le_length_C'' = p(7) and i_le_C'' = p(11) and
        one_minus_i_le_C'' = p(12) and C''_i_eq_L = p(15) and mset_watched_C' = p(17) and
        val_L'_val_L = p(19) and val_L'_not_Some_True = p(20) and val_L_not_Some_True = p(21) and
        f'_f = p(22) and fst_f'_not_None = p(24) and fst_f'_not_None = p(25) and
        snd_f_le_C'' = p(26) and snd_f'_le_C'' = p(27) and L_ne_C''_snd_f = p(28) and
        C''_snd_f_unwatched = p(29) and uC''_snd_f_notin_M = p(30)
      have K_notin_watched[iff]: \<open>?K \<notin> set (watched_l (N ! (W L ! w)))\<close>
        using dist_C''
        apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
        apply (subst (asm) distinct_append)
        using C''_snd_f_unwatched f'_f
        by (auto simp: S)
      have snd_f'_ge_2: \<open>snd f' \<ge> 2\<close>
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then have \<open>?K \<in> set (watched_l (N ! (W L ! w)))\<close>
          using two_le_length_C f'_f by (auto simp add: S take_set
              intro!: exI[of _ \<open>snd f'\<close>])
        then show False
          using K_notin_watched f'_f by (auto simp: S)
      qed
      have \<open>?L \<noteq> ?L'\<close>
        using dist_C'' two_le_length_C i_def
        apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
        apply (subst (asm) distinct_append)
        by (auto simp: S take_2_if split: if_splits)
      then have [simp]: \<open>L \<notin> set (take 2 (swap (N ! x) i (snd f')))\<close> if \<open>W L ! w = x\<close> for x
        using snd_f'_le_C'' le_length_C'' C''_snd_f_unwatched snd_f'_ge_2 L_ne_C''_snd_f that f'_f
        by (auto simp: take_2_if i_def take_set S)
      have C'_N: \<open>W L ! w < length N\<close> \<open>0 < W L ! w\<close>
        using add_inv WL_w_in_drop by (auto simp: S additional_WS_invs_def)
      have C'_N_indirect: \<open>x < length N\<close> \<open>0 < length N\<close> if \<open>W L ! w = x\<close> for x
        using that add_inv WL_w_in_drop by (auto simp: S additional_WS_invs_def)
      have [simp]: \<open>{x. a \<noteq> x \<and> P x} = {x. P x} - {a}\<close> for P a
        by auto
      have KK: \<open>Suc 0 \<le> W L ! w\<close>
        using add_inv WL_w_in_drop by (auto simp: S additional_WS_invs_def)
      have [simp]: \<open>L \<in> set (take 2 (N ! (W L ! w)))\<close>
        using struct_invs valid WL_w_in_drop by (auto simp: S)
      have [simp]: \<open>N ! (W L ! w) ! snd f' \<in> set (take 2 (swap (N ! (W L ! w)) i (snd f')))\<close>
        using w_le snd_f'_ge_2 snd_f_le_C'' f'_f
        by (auto simp: i_def swap_def take_2_if)
      have [simp]: \<open>{x. (y = x \<longrightarrow> P x) \<and> (y \<noteq> x \<longrightarrow> Q x)} =
         (if P y then insert y {x. Q x} else {x. x \<noteq>  y \<and> Q x})\<close>
        for y :: 'a and P Q :: \<open>'a \<Rightarrow> bool\<close>
        by auto
      have i_le_length_C'': \<open>i < length C''\<close>
        using two_le_length_C i_def S by auto
      have [iff]: \<open>?K \<in> set (take 2 (N ! (W L ! w))) \<longleftrightarrow> False\<close>
        using f'_f[symmetric] K_notin_watched by auto
      have [simp]: \<open>set (take 2 (swap (N ! (W L ! w)) i (snd f'))) = {C''!(1-i), ?K}\<close>
        using snd_f'_ge_2 two_le_length_C by (auto simp: take_2_if S i_def swap_def)
      have [simp]: \<open>set (take 2 (N ! (W L ! w))) = {?L, ?L'}\<close>
        using snd_f'_ge_2 two_le_length_C by (auto simp: take_2_if S i_def)
      have [simp]: \<open>N ! (W L ! w) ! (Suc 0 - i) \<in> set (take 2 (N ! (W L ! w)))\<close>
        using i_def two_le_length_C by (auto simp: take_set S intro!: exI[of _ \<open>1-i\<close>])
      have [simp]: \<open>N ! (W L ! w) ! j = N ! (W L ! w) ! k \<longleftrightarrow> j = k\<close>
        if \<open>j < length (N ! (W L ! w))\<close> and \<open>k < length (N ! (W L ! w))\<close>
        for j k
        using dist_C'' that by (auto simp: S distinct_conv_nth)
      have \<open>N ! (W L ! w) \<in> set (tl N)\<close>
        by (metis C'_N(1) KK drop_0 drop_Suc in_set_drop_conv_nth)
      then have [simp]: \<open>mset `# mset (tl N[W L ! w - Suc 0 := swap (N ! (W L ! w)) i (snd f')]) = mset `# mset (tl N)\<close>
        using corr_w C_N_U C'_N i_le_C'' snd_f'_le_C''
        by (auto simp: S mset_update tl_update_swap image_mset_remove1_mset_if
            add_mset_remove_trivial_If nth_tl)
      show ?thesis
        apply clarify
        apply (intro conjI)
        subgoal using f'_f L_ne_C''_snd_f w_le by (simp add: S)
        subgoal
          using w_le L_ne_C''_snd_f KK i_le_length_C'' snd_f'_le_C'' one_minus_i_le_C'' snd_f'_ge_2
            KK corr_w
          by (auto simp add: S clause_to_update_def mset_butlast_remove1_mset nth_list_update'
              last_list_update_to_last mset_update mset_set_Diff mset_set.insert_remove
              tl_update_swap C'_N_indirect
              mset_set_mset_set_minus_id_iff mset_set_empty_iff mset_set_eq_mset_set_more_conds
              dest!: in_diffD)
        done
    qed
    done
qed


definition unit_propagation_inner_loop_wl_loop :: "'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres" where
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(w, S). twl_struct_invs (twl_st_of_wl (Some (L, w)) S) \<and>
        twl_stgy_invs (twl_st_of_wl (Some (L, w)) S) \<and>
        correct_watching S\<^esup>
      (\<lambda>(w, S). w < length (watched_by S L) \<and> get_conflict_wl S \<noteq> None)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl L w S
      })
      (0, S\<^sub>0)
  }
  \<close>

definition unit_propagation_inner_loop_wl :: "'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
     (w, S) \<leftarrow>unit_propagation_inner_loop_wl_loop L S\<^sub>0;
     RETURN S
  }\<close>

declare correct_watching.simps[simp del]
lemma
  assumes \<open>correct_watching S\<close>
  shows \<open>(uncurry unit_propagation_inner_loop_wl, uncurry unit_propagation_inner_loop_l) \<in>
    {((L', T'::'v twl_st_wl), (L, T::'v twl_st_l)). L = L' \<and> st_l_of_wl (Some (L, 0)) T' = T \<and>
      correct_watching T'} \<rightarrow>
        \<langle>{(T', T). st_l_of_wl None T' = T}\<rangle> nres_rel
    \<close> (is \<open>?fg \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  {
    fix L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close>
    assume corr_w: \<open>correct_watching S\<close> and
      \<open>twl_struct_invs (twl_st_of_wl (Some (L, 0)) S)\<close>
      \<open>twl_stgy_invs (twl_st_of_wl (Some (L, 0)) S)\<close>
    have \<open>unit_propagation_inner_loop_wl_loop L S \<le>
            \<Down> {((i, T'), T). T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T'}
              (unit_propagation_inner_loop_l L (st_l_of_wl (Some (L, 0)) S))\<close>
      unfolding unit_propagation_inner_loop_wl_loop_def unit_propagation_inner_loop_l_def uncurry_def
      apply (refine_rcg)
      subgoal using corr_w by auto
      subgoal by auto
      subgoal by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T'
        apply (cases T')
        apply (auto split: if_splits simp: )
           apply (clarsimp simp add: twl_struct_invs_def correct_watching.simps
              simp del:  unit_clss_inv.simps
              valid_annotation.simps)
        sorry
    subgoal sorry







    oops
    }
  have \<open>(uncurry unit_propagation_inner_loop_wl_loop, uncurry unit_propagation_inner_loop_l) \<in>
    {((L', T'::'v twl_st_wl), (L, T::'v twl_st_l)). L = L' \<and> st_l_of_wl (Some (L, 0)) T' = T \<and>
      correct_watching T'} \<rightarrow>
        \<langle>{((i, T'), T). st_l_of_wl None T' = T}\<rangle> nres_rel\<close>
  unfolding unit_propagation_inner_loop_wl_loop_def unit_propagation_inner_loop_l_def uncurry_def
  apply (refine_rcg)
  subgoal for L'T' LT L T L' T'
    apply (cases T')
    apply auto
  thm WHILET_refine
term FOREACH
proof -
  let ?loop =
    \<open>\<lambda>L S\<^sub>0. WHILE\<^sub>T\<^bsup>\<lambda>(WL, S). twl_struct_invs (twl_st_of_wl (Some L) S) \<and> twl_stgy_invs (twl_st_of_wl (Some L) S) \<and>
    cdcl_twl_cp\<^sup>*\<^sup>* (twl_st_of_wl (Some L) S\<^sub>0) (twl_st_of_wl (Some L) S)\<^esup>
      (\<lambda>(WL, S). working_queue_wl S \<noteq> {#})
      (\<lambda>(WL, S). do {
        (S', C) \<leftarrow> select_from_working_queue_wl S;
        unit_propagation_inner_loop_body_wl L C WL S'
      })
      ({#}, S\<^sub>0)\<close>
  have \<open>(uncurry ?loop, uncurry unit_propagation_inner_loop_l) \<in> ?A \<rightarrow>
     \<langle>{((WL, T'), T). st_l_of_wl T' = T}\<rangle>nres_rel\<close>
  unfolding unit_propagation_inner_loop_wl_def unit_propagation_inner_loop_l_def uncurry_def
  apply clarify
  thm WHILEIT_refine
  apply (refine_vcg WHILEIT_refine[])
    sorry

  show ?thesis
  unfolding unit_propagation_inner_loop_wl_def unit_propagation_inner_loop_l_def uncurry_def
  apply (subst (10) nres_monad2[symmetric])
  apply clarify
  apply (refine_vcg WHILEIT_refine[where R = \<open>{((WT'::watched, T'::'v twl_st_wl), T). st_l_of_wl T' = T}\<close>
        and I = \<open>\<lambda>(WL, S). correct_watching_except S L\<close>] )
  thm  WHILEIT_refine[where R = \<open>{((WT'::watched, T'::'v twl_st_wl), T). st_l_of_wl T' = T}\<close>]
  supply [[unify_trace_failure]]
  apply (rule WHILEIT_refine)
  apply (rule WHILEIT_refine[where R = \<open>{((WT'::watched, T'::'v twl_st_wl), T). st_l_of_wl T' = T}\<close>])
    oops
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp add: working_queue_l_working_queue_wl)
  subgoal by (auto simp add: working_queue_l_working_queue_wl)
  subgoal by (auto simp add: working_queue_l_working_queue_wl)
  subgoal by auto
oops

definition unit_propagation_outer_loop_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres"  where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      working_queue_wl S = {#}\<^esup>
      (\<lambda>S. pending_wl S \<noteq> {#})
      (\<lambda>S. do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># pending_wl S);
        let S' = set_working_queue_wl (watched_by S L) (set_pending_wl (remove1_mset L (pending_wl S)) S);
        unit_propagation_inner_loop_wl L S'
      })
      S\<^sub>0
\<close>

end
