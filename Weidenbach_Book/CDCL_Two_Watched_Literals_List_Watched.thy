theory CDCL_Two_Watched_Literals_List_Watched
  imports CDCL_Two_Watched_Literals_List CDCL_Two_Watched_Literals_List_Watched_Initialisation
begin

text \<open>Less ambiguities in the notations (TODO: using a bundle would probably be better):\<close>
no_notation Ref.update ("_ := _" 62)

(* TODO Move somewhere *)
lemma nth_in_set_tl: \<open>i > 0 \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i \<in> set (tl xs)\<close>
  by (cases xs) auto

lemma in_atms_of_mset_takeD:
  \<open>x \<in> atms_of_ms (mset ` set (take U (tl N))) \<Longrightarrow> x \<in> atms_of_ms (mset ` set ((tl N)))\<close>
  by (auto dest: in_set_takeD simp:atms_of_ms_def)
(* End Move *)


subsection \<open>Access Functions\<close>

fun clauses_to_update_wl :: "'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> clauses_to_update_wl" where
  \<open>clauses_to_update_wl (_, _, _, _, _, _, _, W) L i = mset (drop i (W L))\<close>

fun get_trail_wl :: "'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_wl (M, _, _, _, _, _, _, _) = M\<close>

fun literals_to_update_wl :: "'v twl_st_wl \<Rightarrow> 'v lit_queue_wl" where
  \<open>literals_to_update_wl (_, _, _, _, _, _, Q, _) = Q\<close>

fun set_literals_to_update_wl :: "'v lit_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl" where
  \<open>set_literals_to_update_wl Q (M, N, U, D, NP, UP, _, W) = (M, N, U, D, NP, UP, Q, W)\<close>

fun get_conflict_wl :: "'v twl_st_wl \<Rightarrow> 'v cconflict" where
  \<open>get_conflict_wl (_, _, _, D, _, _, _, _) = D\<close>


definition lits_of_atms_of_mm :: \<open>'a clauses \<Rightarrow> 'a literal multiset\<close> where
\<open>lits_of_atms_of_mm Ls = Pos `# (atm_of `# (\<Union># Ls)) + Neg `# (atm_of `# (\<Union># Ls))\<close>

text \<open>
  We cannot just extract the literals of the clauses: we cannot be sure that atoms appear \<^emph>\<open>both\<close>
  positively and negatively in the clauses. If we can ensure that there are no pure literals, the
  definition of \<^term>\<open>lits_of_atms_of_mm\<close> can be changed to \<open>lits_of_atms_of_mm Ls = \<Union># Ls\<close>.
\<close>
fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, U, D, NP, UP, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP). mset (W L) = clause_to_update L (M, N, U, D, NP, UP, {#}, {#}))\<close>

declare correct_watching.simps[simp del]

fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> watched\<close> where
  \<open>watched_by (M, N, U, D, NP, UP, Q, W) L = W L\<close>

fun update_watched :: \<open>'v literal \<Rightarrow> watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, U, D, NP, UP, Q, W) = (M, N, U, D, NP, UP, Q, W(L:= WL))\<close>

fun delete_index_and_swap where
  \<open>delete_index_and_swap l i = butlast(l[i := last l])\<close>


lemma in_lits_of_atms_of_mm_ain_atms_of_iff: \<open>L \<in># lits_of_atms_of_mm N \<longleftrightarrow> atm_of L \<in> atms_of_mm N\<close>
  by (cases L) (auto simp: lits_of_atms_of_mm_def atms_of_ms_def atms_of_def)

lemma lits_of_atms_of_mm_union:
  \<open>lits_of_atms_of_mm (M + N) = lits_of_atms_of_mm M + lits_of_atms_of_mm N\<close>
  unfolding lits_of_atms_of_mm_def by auto

definition lits_of_atms_of_m :: \<open>'a clause \<Rightarrow> 'a literal multiset\<close> where
\<open>lits_of_atms_of_m Ls = Pos `# (atm_of `# Ls) + Neg `# (atm_of `# Ls)\<close>

lemma in_lits_of_atms_of_m_ain_atms_of_iff: \<open>L \<in># lits_of_atms_of_m N \<longleftrightarrow> atm_of L \<in> atms_of N\<close>
  by (cases L) (auto simp: lits_of_atms_of_m_def atms_of_ms_def atms_of_def)

lemma lits_of_atms_of_mm_add_mset:
  \<open>lits_of_atms_of_mm (add_mset C N) = (lits_of_atms_of_m C) + (lits_of_atms_of_mm N)\<close>
  by (auto simp: lits_of_atms_of_mm_def lits_of_atms_of_m_def)

lemma lits_of_atms_of_m_add_mset:
  \<open>lits_of_atms_of_m (add_mset L C) = add_mset L (add_mset (-L) (lits_of_atms_of_m C))\<close>
  by (cases L) (auto simp: lits_of_atms_of_m_def)

lemma lits_of_atms_of_m_union:
  \<open>lits_of_atms_of_m (A + B) = lits_of_atms_of_m A + lits_of_atms_of_m B\<close>
  by (auto simp: lits_of_atms_of_m_def)

fun st_l_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl None (M, N, C, D, NP, UP, Q, W) = (M, N, C, D, NP, UP, {#}, Q)\<close>
| \<open>st_l_of_wl (Some (L, j)) (M, N, C, D, NP, UP, Q, W) =
    (M, N, C, D, NP, UP, (if D \<noteq> None then {#} else clauses_to_update_wl (M, N, C, D, NP, UP, Q, W) L j,
      Q))\<close>

fun twl_st_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st\<close> where
  \<open>twl_st_of_wl L S = twl_st_of (map_option fst L) (st_l_of_wl L S)\<close>

fun twl_st_of_wl2 :: \<open>('v literal) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st\<close> where
  \<open>twl_st_of_wl2 L S = twl_st_of L (st_l_of_wl None S)\<close>

fun remove_one_lit_from_wq :: "nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l" where
  \<open>remove_one_lit_from_wq L (M, N, C, D, NP, UP, WS, Q) = (M, N, C, D, NP, UP, remove1_mset L WS, Q)\<close>

lemma remove_one_lit_from_wq_def:
  \<open>remove_one_lit_from_wq L S = set_clauses_to_update_l (clauses_to_update_l S - {#L#}) S\<close>
  by (cases S) auto

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

lemma literals_to_update_wl_literals_to_update_l_iff: \<open>literals_to_update_l (st_l_of_wl L S) = literals_to_update_wl S\<close>
  by (cases S; cases L) auto

lemma correct_watching_set_literals_to_update: \<open>correct_watching (set_literals_to_update_wl WS T') = correct_watching T'\<close>
  by (cases T') (auto simp: correct_watching.simps)

lemma get_conflict_wl_set_literals_to_update_wl: \<open>get_conflict_wl (set_literals_to_update_wl P S) = get_conflict_wl S\<close>
  by (cases S) auto

lemma get_conflict_twl_st_of_st_l_of_wl:
  \<open>get_conflict (twl_st_of L (st_l_of_wl L' T')) = get_conflict_wl T'\<close>
  by (cases T'; cases L; cases L') auto

lemma literals_to_update_twl_st_of_st_l_of_wl: \<open>literals_to_update (twl_st_of L (st_l_of_wl L' T')) = literals_to_update_wl T'\<close>
  by (cases T'; cases L; cases L') auto

lemma get_conflict_l_st_l_of_wl:
  \<open>get_conflict_l (st_l_of_wl L S) = get_conflict_wl S\<close>
  by (cases S; cases L) auto

text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>.\<close>
definition unit_propagation_inner_loop_body_wl :: "'v literal \<Rightarrow> nat \<Rightarrow>
  'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres" where
  \<open>unit_propagation_inner_loop_body_wl K w S = do {
    let (M, N, U, D, NP, UP, Q, W) = (S::'v twl_st_wl);
    ASSERT(K \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP));
    ASSERT(w < length (watched_by S K));
    let C = (watched_by S K) ! w;
    ASSERT(C > 0);
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
      ASSERT (f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      case f of
        None \<Rightarrow>
          if val_L' = Some False
          then do {RETURN (w+1, (M, N, U, Some (mset (N!C)), NP, UP, {#}, W))}
          else do {RETURN (w+1, (Propagated L' C # M, N, U, D, NP, UP, add_mset (-L') Q, W))}
      | Some f \<Rightarrow> do {
          ASSERT(f < length (N!C));
          let K' = (N!C) ! f;
          ASSERT(K' \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP));
          let N' = list_update N C (swap (N!C) i f);
          ASSERT(K \<noteq> K');
          RETURN (w, (M, N', U, D, NP, UP, Q, W(K := delete_index_and_swap (watched_by S L) w, K':= W K' @ [C])))
        }
    }
   }
\<close>

lemma refine_add_invariants':
  assumes
    \<open>f S \<le> \<Down> {(S, S'). Q' S S' \<and> Q S} gS\<close> and
    \<open>y \<le> \<Down> {((i, S), S'). P i S S'} (f S)\<close> and
    \<open>nofail gS\<close>
  shows \<open>y \<le> \<Down> {((i, S), S'). P i S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail
  by force

lemma "weaken_\<Down>": \<open>R' \<subseteq> R \<Longrightarrow> f \<le> \<Down> R' g \<Longrightarrow> f \<le> \<Down> R g\<close>
  by (meson pw_ref_iff subset_eq)

method match_Down =
  (match conclusion in \<open>f \<le> \<Down> R g\<close> for f g R \<Rightarrow>
    \<open>print_term f; match premises in I: \<open>f \<le> \<Down> R' g\<close> for R'
       \<Rightarrow> \<open>rule "weaken_\<Down>"[OF _ I]\<close>\<close>)


subsection \<open>The Functions\<close>

subsubsection \<open>Inner Loop\<close>

lemma unit_propagation_inner_loop_body_wl_spec:
  fixes S :: \<open>'v twl_st_wl\<close> and L :: \<open>'v literal\<close> and w :: nat
  defines
    [simp]: \<open>T \<equiv> remove_one_lit_from_wq (watched_by S L ! w) (st_l_of_wl (Some (L, w)) S)\<close> and
    [simp]: \<open>S' \<equiv> st_l_of_wl (Some (L, w)) S\<close> and
    [simp]: \<open>S'' \<equiv> twl_st_of_wl (Some (L, w)) S\<close> and
    [simp]: \<open>C' \<equiv> watched_by S L ! w\<close>
  defines
    [simp]: \<open>C'' \<equiv> get_clauses_l S' ! C'\<close>
  assumes
    w_le: \<open>w < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    corr_w: \<open>correct_watching S\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>additional_WS_invs S'\<close> and
    stgy_inv: \<open>twl_stgy_invs S''\<close>
  shows \<open>unit_propagation_inner_loop_body_wl L w S \<le>
   \<Down> {((i, T'), T).
        T = st_l_of_wl (Some (L, i)) T' \<and>
        twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, i)) T')) \<and>
        twl_stgy_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, i)) T')) \<and>
        additional_WS_invs T \<and>
        correct_watching T' \<and>
        i \<le> length (watched_by T' L)}
     (unit_propagation_inner_loop_body_l L C' T)\<close>
proof -
  have val: \<open>(valued a b, valued a' b') \<in> Id\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' :: \<open>('a, 'b) ann_lits\<close> and b b' :: \<open>'a literal\<close>
    by (auto simp: that)
  have f: \<open>find_unwatched a (b ! c) \<le> \<Down> Id (find_unwatched a' (b' ! c'))\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> and \<open>c = c'\<close> for a a' :: \<open>('a, 'b) ann_lits\<close> and
      b b' :: \<open>'a clauses_l\<close>and c c' :: nat
    by (auto simp: that)
  obtain M N U NP UP Q W where
    S: \<open>S = (M, N, U, None, NP, UP, Q, W)\<close>
    using confl by (cases S) auto
  have T'[unfolded T_def, unfolded S]: \<open>remove_one_lit_from_wq (watched_by S L ! w)
           (st_l_of_wl (Some (L, w)) (M, N, U, None, NP, UP, Q, W)) =
           (M, N, U, None, NP, UP,
             remove1_mset (watched_by S L ! w) (clauses_to_update_wl (M, N, U, None, NP, UP, Q, W) L w),
             Q)\<close>
    by auto
  have [simp]: \<open>remove1_mset (W L ! w) (mset (drop w (W L))) = mset (drop (Suc w) (W L))\<close>
    using w_le by (cases \<open>drop w (W L)\<close>) (auto simp: drop_Cons' drop_Suc drop_tl remove1_mset_add_mset_If
        trivial_add_mset_remove_iff nth_via_drop)
  have \<open>\<not> length xs \<le> Suc w \<Longrightarrow> last xs \<in> set (drop (Suc w) xs)\<close>
    if \<open>w < length xs\<close> for xs :: \<open>'a list\<close> and w :: nat
    using that by (metis List.last_in_set drop_eq_Nil last_drop not_le)
  then have mset_drop_butlast[simp]: \<open>mset (drop w (butlast (xs[w := last xs]))) = mset (drop (Suc w) xs)\<close>
    if \<open>w < length xs\<close> for xs :: \<open>'a list\<close> and w :: nat
    using that by (auto simp: butlast_list_update S mset_butlast_remove1_mset
        single_remove1_mset_eq)

  have inv: \<open>twl_st_inv S''\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S'')\<close> and
    valid: \<open>valid_annotation S''\<close>
    using struct_invs by (auto simp: twl_struct_invs_def)
  have
    w_q_inv: \<open>clauses_to_update_inv S''\<close> and
    dist: \<open>distinct_queued S''\<close> and
    no_dup: \<open>no_duplicate_queued S''\<close> and
    no_dup_queued: \<open>no_duplicate_queued S''\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have n_d: \<open>no_dup M\<close> and alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S'')\<close>
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
  then have WS: \<open>C' \<in># clauses_to_update_l S'\<close>
    using w_le by (auto simp: S)
  have C'_N_U: \<open>?C' \<in># twl_clause_of `# mset ((tl N))\<close>
    using WS valid
    by (auto simp: S twl_struct_invs_def simp del: twl_clause_of.simps)
  then have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using inv by (auto simp: twl_st_inv.simps S simp del: twl_clause_of.simps)
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
  obtain WS' where WS'_def: \<open>clauses_to_update_l S' = add_mset C' WS'\<close>
    using multi_member_split[OF WS] by (auto simp: S)
  have L: \<open>L \<in> set (watched_l C'')\<close>
    using valid S WL_w_in_drop by (auto simp: WS'_def)
  have C'_i[simp]: \<open>C''!i = L\<close>
    using L two_le_length_C S by (auto simp: take_2_if i_def split: if_splits)
  then have N_W_w_i_L[simp]: \<open>N! (W L ! w)!i = L\<close>
    by (auto simp: S)
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
    using WS'_def no_dup_queued by (simp add: S all_conj_distrib)
  from mset_le_add_mset_decr_left2[OF this] have uL_M: \<open>-L \<in> lits_of_l M\<close>
    using imageI[of _ \<open>set M\<close> lit_of] lits_of_l_convert_lits_l[of N M]
    by (auto simp: lits_of_def)
  have \<open>L \<in># lits_of_atms_of_mm (mset `# mset (take U (tl N))+NP)\<close>
    using alien uL_M
    by (auto simp: S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        mset_take_mset_drop_mset in_lits_of_atms_of_mm_ain_atms_of_iff)
  then have L_in_N_NP: \<open>L \<in># lits_of_atms_of_mm (mset `# mset (tl N)+NP)\<close>
    by (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff atms_of_ms_def
        dest: in_set_takeD)
  then have \<open>mset (W L) = mset_set {x. Suc 0 \<le> x \<and> x < length N \<and> L \<in> set (take 2 (N ! x))}\<close>
    using corr_w by (auto simp: S correct_watching.simps clause_to_update_def)
  moreover have \<open>W L ! w \<in># mset (W L)\<close>
    using WL_w_in_drop by (auto dest: in_set_dropD)
  ultimately have zero_le_W_L_w: \<open>0 < W L ! w\<close>
    by (auto simp: S correct_watching.simps clause_to_update_def)

  have ref:
    \<open>((w, M, N[watched_by (M, N, U, None, NP, UP, Q, W) L ! w := swap (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w)) i f], U, None, NP, UP, Q, W
        (L := delete_index_and_swap (watched_by (M, N, U, None, NP, UP, Q, W) L) w,
          N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! f := W (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! f) @ [watched_by (M, N, U, None, NP, UP, Q, W) L ! w])),
      M, N[watched_by (M, N, U, None, NP, UP, Q, W) L ! w := swap (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w)) i thef], U, None, NP, UP,
      remove1_mset (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) (clauses_to_update_wl (M, N, U, None, NP, UP, Q, W) L w), Q)
    \<in> {((i, T'), T). T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>

  if
    C'_le_length: \<open>w < length (watched_by (M, N, U, None, NP, UP, Q, W) L)\<close> and
    le_length_C'': \<open>0 < watched_by (M, N, U, None, NP, UP, Q, W) L ! w\<close> and
    i_le_C'': \<open>i < length (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w))\<close> and
    one_minus_i_le_C'': \<open>1 - i < length (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w))\<close> and
    C''_i_eq_L: \<open>N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! i = L\<close> and
    mset_watched_C': \<open>mset (watched_l (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w))) = {#L, N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! (1 - i)#}\<close> and
    val_L'_val_L: \<open>(val_L', val_L) \<in> Id\<close> and
    val_L'_not_Some_True: \<open>val_L' \<noteq> Some True\<close> and
    val_L_not_Some_True: \<open>val_L \<noteq> Some True\<close> and
    f'_f: \<open>(Some f, f') \<in> Id\<close> \<open>(f, thef) \<in> nat_rel\<close> and
    fst_f'_not_None: \<open>(Some f = None) = (\<forall>L\<in>#mset (unwatched_l (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w))). - L \<in> lits_of_l M)\<close> and
    fst_f'_not_None: \<open>(f, thef) \<in> nat_rel\<close> and
    snd_f_le_C'': \<open>thef < length (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w))\<close> and
    snd_f'_le_C'': \<open>f < length (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w))\<close> and
    L_ne_C''_snd_f: \<open>L \<noteq> N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! f\<close> and
    C''_snd_f_unwatched: \<open>N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! thef \<in># mset (unwatched_l (N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w)))\<close> and
    uC''_snd_f_notin_M: \<open>- N ! (watched_by (M, N, U, None, NP, UP, Q, W) L ! w) ! thef \<notin> lits_of_l M\<close>
  for val_L val_L' f thef f'
  proof -
    let ?K = \<open>N ! (W L ! w) ! f\<close>
    have K_notin_watched[iff]: \<open>?K \<notin> set (watched_l (N ! (W L ! w)))\<close>
      using dist_C''
      apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
      apply (subst (asm) distinct_append)
      using C''_snd_f_unwatched f'_f
      by (auto simp: S)
    have snd_f'_ge_2: \<open>f \<ge> 2\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>?K \<in> set (watched_l (N ! (W L ! w)))\<close>
        using two_le_length_C f'_f by (auto simp add: S take_set
            intro!: exI[of _ \<open>the f'\<close>])
      then show False
        using K_notin_watched f'_f by (auto simp: S)
    qed
    have \<open>?L \<noteq> ?L'\<close>
      using dist_C'' two_le_length_C i_def
      apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
      apply (subst (asm) distinct_append)
      by (auto simp: S take_2_if split: if_splits)
    then have [simp]: \<open>L \<notin> set (take 2 (swap (N ! x) i f))\<close> if \<open>W L ! w = x\<close> for x
      using snd_f'_le_C'' le_length_C'' C''_snd_f_unwatched snd_f'_ge_2 L_ne_C''_snd_f that f'_f
      by (auto simp: take_2_if i_def take_set S)
    have C'_N: \<open>W L ! w < length N\<close> \<open>0 < W L ! w\<close>
      using add_inv WL_w_in_drop by (auto simp: S additional_WS_invs_def)
    have C'_N_indirect: \<open>x < length N\<close> \<open>0 < length N\<close> if \<open>W L ! w = x\<close> for x
      using that add_inv WL_w_in_drop by (auto simp: S additional_WS_invs_def)
    have [simp]: \<open>{x. a \<noteq> x \<and> P x} = {x. P x} - {a}\<close> for P :: \<open>'a \<Rightarrow> bool\<close> and a :: 'a
      by auto
    have KK: \<open>Suc 0 \<le> W L ! w\<close>
      using add_inv WL_w_in_drop by (auto simp: S additional_WS_invs_def)
    have [simp]: \<open>L \<in> set (take 2 (N ! (W L ! w)))\<close>
      using struct_invs valid WL_w_in_drop by (auto simp: S)
    have [simp]: \<open>N ! (W L ! w) ! f \<in> set (take 2 (swap (N ! (W L ! w)) i f))\<close>
      using w_le snd_f'_ge_2 snd_f_le_C'' f'_f
      by (auto simp: i_def swap_def take_2_if split: nat.splits)
    have [simp]: \<open>{x. (y = x \<longrightarrow> P x) \<and> (y \<noteq> x \<longrightarrow> Q x)} =
         (if P y then insert y {x. Q x} else {x. x \<noteq>  y \<and> Q x})\<close>
      for y :: 'a and P Q :: \<open>'a \<Rightarrow> bool\<close>
      by auto
    have i_le_length_C'': \<open>i < length C''\<close>
      using two_le_length_C i_def S by auto
    have [iff]: \<open>?K \<in> set (take 2 (N ! (W L ! w))) \<longleftrightarrow> False\<close>
      using f'_f[symmetric] K_notin_watched by auto
    have [simp]: \<open>set (take 2 (swap (N ! (W L ! w)) i f)) = {C''!(1-i), ?K}\<close>
      using snd_f'_ge_2 two_le_length_C f'_f by (auto simp: take_2_if S i_def swap_def)
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
    then have [simp]: \<open>mset `# mset (tl N[W L ! w - Suc 0 := swap (N ! (W L ! w)) i f]) = mset `# mset (tl N)\<close>
      using corr_w C_N_U C'_N i_le_C'' snd_f'_le_C'' f'_f
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
            tl_update_swap C'_N_indirect correct_watching.simps
            mset_set_mset_set_minus_id_iff mset_set_empty_iff mset_set_eq_mset_set_more_conds
            dest!: in_diffD)
      subgoal using w_le by (auto simp: S)
      done
  qed

  have 1: \<open>unit_propagation_inner_loop_body_wl L w S
    \<le> \<Down> {((i, T'), T).
          T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T' \<and>
          i \<le> length (watched_by T' L)}
        (unit_propagation_inner_loop_body_l L C' T)\<close>
    using w_le confl corr_w
    unfolding T_def
    unfolding unit_propagation_inner_loop_body_wl_def unit_propagation_inner_loop_body_l_def S T'
      C'_def
    supply [[goals_limit=1]]
    apply (rewrite at \<open>let _ = watched_by _ _ ! _ in _\<close> Let_def)
    apply (refine_vcg val f; remove_dummy_vars)
    unfolding i_def[symmetric]
    subgoal using L_in_N_NP .
    subgoal using zero_le_W_L_w by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: clause_to_update_def correct_watching.simps)
    subgoal by (simp add: clause_to_update_def correct_watching.simps)
    subgoal by simp

    subgoal
      using zero_le_W_L_w
      by (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff atms_of_ms_def correct_watching.simps
          intro!: nth_in_set_tl
          intro!: bexI[of _ \<open>N ! (W L ! w)\<close>])
    subgoal using uL_M by auto

    subgoal by (rule ref) assumption+
    done

  have \<open>unit_propagation_inner_loop_body_wl L w S \<le>
     \<Down> {((i, T'), T). (T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T' \<and>
              i \<le> length (watched_by T' L)) \<and>
         (additional_WS_invs T \<and> twl_stgy_invs (twl_st_of (Some L) T) \<and>
          twl_struct_invs (twl_st_of (Some L) T) )}
        (unit_propagation_inner_loop_body_l L C' T)\<close>
    unfolding T_def
    apply (rule refine_add_invariants'[where Q' = \<open>\<lambda>S S''. twl_st_of (Some L) S = S''\<close> and
          gS = \<open>(unit_propagation_inner_loop_body
      (L, twl_clause_of (get_clauses_l S' ! C'))
      (set_clauses_to_update
        (remove1_mset
          (L, twl_clause_of (get_clauses_l S' ! C'))
          (clauses_to_update (twl_st_of (Some L) S')))
        (twl_st_of (Some L) S')))\<close>])
    subgoal
    proof -
      have H: \<open>{(T', T). twl_st_of (Some L) T' = T \<and> additional_WS_invs T' \<and> twl_stgy_invs (twl_st_of (Some L) T') \<and> twl_struct_invs (twl_st_of (Some L) T')} =
        {(S, S''). twl_st_of (Some L) S = S'' \<and> additional_WS_invs S \<and> twl_stgy_invs S'' \<and> twl_struct_invs S''}\<close>
        by auto
      show ?thesis
      unfolding remove_one_lit_from_wq_def C'_def[symmetric] S'_def[symmetric] H
      apply (rule unit_propagation_inner_loop_body_l[of C' S' L])
       using struct_invs stgy_inv add_inv WL_w_in_drop by (auto simp: S)
    qed
    subgoal using 1 by auto
    subgoal
      apply (rule unit_propagation_inner_loop_body(2))
       using struct_invs stgy_inv add_inv WL_w_in_drop by (auto simp: S)
     done
   then show ?thesis
     apply -
     apply match_Down
     by blast
qed


definition unit_propagation_inner_loop_wl_loop :: "'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres" where
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(w, S). twl_struct_invs (twl_st_of_wl (Some (L, w)) S) \<and>
        twl_stgy_invs (twl_st_of_wl (Some (L, w)) S) \<and>
         additional_WS_invs (st_l_of_wl (Some (L, w)) S) \<and>
        correct_watching S \<and> w \<le> length (watched_by S L)\<^esup>
      (\<lambda>(w, S). w < length (watched_by S L) \<and> get_conflict_wl S = None)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl L w S
      })
      (0, S\<^sub>0)
  }
  \<close>

definition unit_propagation_inner_loop_wl :: "'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
     wS \<leftarrow> unit_propagation_inner_loop_wl_loop L S\<^sub>0;
     RETURN (snd wS)
  }\<close>


lemma unit_propagation_inner_loop_wl_spec:
  shows \<open>(uncurry unit_propagation_inner_loop_wl, uncurry unit_propagation_inner_loop_l) \<in>
    {((L', T'::'v twl_st_wl), (L, T::'v twl_st_l)). L = L' \<and> st_l_of_wl (Some (L, 0)) T' = T \<and>
      correct_watching T' \<and>
      twl_struct_invs (twl_st_of_wl2 (Some L) (set_literals_to_update_wl (add_mset L (literals_to_update_wl T')) T')) \<and>
      twl_stgy_invs (twl_st_of_wl2 None (set_literals_to_update_wl (add_mset L (literals_to_update_wl T')) T')) \<and>
      get_conflict_wl T' = None \<and>
      additional_WS_invs (st_l_of_wl None (set_literals_to_update_wl (add_mset L (literals_to_update_wl T')) T'))} \<rightarrow>
    \<langle>{(T', T). st_l_of_wl None T' = T \<and>
        twl_struct_invs (twl_st_of_wl None T') \<and>
        twl_stgy_invs (twl_st_of_wl None T') \<and>
        additional_WS_invs T \<and>
        correct_watching T'}\<rangle> nres_rel
    \<close> (is \<open>?fg \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close> is \<open>?fg \<in> ?A \<rightarrow> \<langle>{(T', T). ?f T' = T \<and> ?P T T'}\<rangle>nres_rel\<close>)
proof -
  {
    fix L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close>
    let ?S = \<open>twl_st_of_wl2 (Some L) (set_literals_to_update_wl (add_mset L (literals_to_update_wl S)) S)\<close>
    assume corr_w: \<open>correct_watching S\<close> and
      struct_invs: \<open>twl_struct_invs ?S\<close> and
      stgy_invs: \<open>twl_stgy_invs ?S\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None (set_literals_to_update_wl (add_mset L (literals_to_update_wl S)) S))\<close>
    text \<open>To ease the finding the correspondence between the body of the loops, we introduce
      following function:\<close>
    define unit_propagation_body_wl_loop_fantom where
      \<open>unit_propagation_body_wl_loop_fantom L w S = do {
        let C = watched_by S L! w;
        unit_propagation_inner_loop_body_wl L w S}\<close> for L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close> and w :: nat

    have unit_propagation_body_wl_loop_fantom: \<open>unit_propagation_inner_loop_body_wl L w S \<le> \<Down>Id
          (unit_propagation_body_wl_loop_fantom L w S)\<close>
      if \<open>w <  length (watched_by S L)\<close> for w and S :: \<open>'v twl_st_wl\<close>
      using that unfolding unit_propagation_body_wl_loop_fantom_def
      by auto
    have watched_by_select_from_clauses_to_update: \<open>RETURN (watched_by T L ! i)
    \<le> \<Down> {(C', (S, C)). C' = C \<and> S = remove_one_lit_from_wq (watched_by T L ! i)
             (st_l_of_wl (Some (L, i)) T)}
        (select_from_clauses_to_update
          (st_l_of_wl (Some (L, i)) T))\<close>
      if \<open>i < length (watched_by T L)\<close> and \<open>get_conflict_wl T = None\<close>
      for i :: nat and L :: \<open>'v literal\<close> and T :: \<open>'v twl_st_wl\<close>
      unfolding select_from_clauses_to_update_def
      apply (rule RETURN_SPEC_refine)
      by (cases T) (use that in \<open>auto simp: in_set_drop_conv_nth\<close>)
    have H: \<open>unit_propagation_body_wl_loop_fantom L i T'
    \<le> \<Down> {((i, T'), T).
          T = st_l_of_wl (Some (L, i)) T' \<and>
          twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, i)) T')) \<and>
          twl_stgy_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, i)) T')) \<and>
          additional_WS_invs T \<and>
          correct_watching T' \<and> i \<le> length (watched_by T' L)}
        (do {
           (S', C) \<leftarrow>
             select_from_clauses_to_update
              (st_l_of_wl (Some (L, i)) T');
           unit_propagation_inner_loop_body_l L C S'
         })\<close>
      if \<open>i < length (watched_by T' L)\<close> and \<open>get_conflict_wl T' = None\<close> and
      \<open>correct_watching T'\<close> and
      \<open>twl_struct_invs (twl_st_of_wl (Some (L, i)) T')\<close> and
      \<open>twl_stgy_invs (twl_st_of_wl (Some (L, i)) T')\<close> and
      \<open>additional_WS_invs (st_l_of_wl (Some (L, i)) T')\<close>
      for i T'
      unfolding unit_propagation_body_wl_loop_fantom_def
      apply (refine_rcg watched_by_select_from_clauses_to_update)
      using that
        apply (auto intro!: unit_propagation_inner_loop_body_wl_spec)
      done

    have \<open>unit_propagation_inner_loop_wl_loop L S \<le>
            \<Down> {((i, T'), T). T = st_l_of_wl None T' \<and> ?P T T'}
              (unit_propagation_inner_loop_l L (st_l_of_wl (Some (L, 0)) S))\<close>
      (is \<open>_ \<le> \<Down> ?R _\<close>)
      unfolding unit_propagation_inner_loop_wl_loop_def unit_propagation_inner_loop_l_def uncurry_def
      apply (refine_rcg WHILEIT_refine_genR[where
            R = \<open>?R\<close> and
            R' = \<open>{((i, T'), T). T = st_l_of_wl (Some (L, i)) T' \<and>
                      twl_struct_invs (twl_st_of_wl (Some (L, i)) T') \<and>
                      twl_stgy_invs (twl_st_of_wl (Some (L, i)) T') \<and>
                        additional_WS_invs T \<and> correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>])
      subgoal using corr_w struct_invs by auto
      subgoal by auto
      subgoal by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T'
        by (cases T') (solves \<open>auto simp del: unit_clss_inv.simps valid_annotation.simps split: if_splits\<close>)+
      subgoal for i'T' T i' T'
        apply (rule order_trans)
        by (rule unit_propagation_body_wl_loop_fantom; simp; fail) (auto intro!: H)
      subgoal by force
      done
    then have \<open>unit_propagation_inner_loop_wl_loop L S \<le> \<Down> {((i, T'), T).  T = st_l_of_wl None T' \<and>
      ?P T T'}
     (unit_propagation_inner_loop_l L' S')\<close>
     if \<open>L = L'\<close> and \<open>S' = st_l_of_wl (Some (L, 0)) S\<close>
     for S' and L' :: \<open>'v literal\<close>
     using that by auto
  }
  note H = this
  text \<open>Another phantom function to help the refine generator to align goals:\<close>
  define unit_propagation_inner_loop_l_fantom where
    \<open>unit_propagation_inner_loop_l_fantom L S = do {
        S' \<leftarrow> unit_propagation_inner_loop_l L S;
        RETURN S'}
      \<close> for L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_l\<close>
  have \<open>(uncurry unit_propagation_inner_loop_wl, uncurry unit_propagation_inner_loop_l_fantom)
    \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>
    unfolding unit_propagation_inner_loop_wl_def unit_propagation_inner_loop_l_fantom_def uncurry_def
    apply clarify
    apply (refine_rcg H)
    subgoal by force
    subgoal by auto
    subgoal by force
    subgoal by force
    done
  moreover have \<open>unit_propagation_inner_loop_l_fantom = unit_propagation_inner_loop_l\<close>
    by (intro ext) (auto simp: unit_propagation_inner_loop_l_fantom_def)
  ultimately show ?thesis
    by fast
qed


subsubsection \<open>Outer loop\<close>

definition select_and_remove_from_literals_to_update_wl :: "'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> 'v literal) nres" where
  \<open>select_and_remove_from_literals_to_update_wl S = SPEC(\<lambda>(S', L). L \<in># literals_to_update_wl S \<and>
     S' = set_literals_to_update_wl (literals_to_update_wl S - {#L#}) S)\<close>
term init_clss
definition unit_propagation_outer_loop_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      correct_watching S \<and> additional_WS_invs (st_l_of_wl None S)\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S'))));
        unit_propagation_inner_loop_wl L S'
      })
      (S\<^sub>0 :: 'v twl_st_wl)
\<close>

lemma unit_propagation_outer_loop_wl_spec:
  \<open>(unit_propagation_outer_loop_wl, unit_propagation_outer_loop_l)
 \<in> {(T'::'v twl_st_wl, T).
       st_l_of_wl None T' = T \<and>
       correct_watching T' \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       get_conflict_wl T' = None \<and>
       additional_WS_invs (st_l_of_wl None T')} \<rightarrow>
    \<langle>{(T', T).
       st_l_of_wl None T' = T \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       additional_WS_invs T \<and>
       literals_to_update_wl T' = {#} \<and>
       no_step cdcl_twl_cp (twl_st_of None T) \<and>
       correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?u \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have select_and_remove_from_literals_to_update_wl: \<open>select_and_remove_from_literals_to_update_wl S' \<le>
     \<Down> {((T', L'), (T, L)). L = L' \<and> T = st_l_of_wl (Some (L, 0)) T' \<and>
         T' = set_literals_to_update_wl (literals_to_update_wl S' - {#L#}) S' \<and> L \<in># literals_to_update_wl S' \<and>
         L \<in># lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S')))
       }
       (select_and_remove_from_literals_to_update S)\<close>
    if S: \<open>S = st_l_of_wl None S'\<close> and \<open>get_conflict_wl S' = None\<close> and
      corr_w: \<open>correct_watching S'\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S')\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
  proof -
    obtain M N U D NP UP W Q where
      S': \<open>S' = (M, N, U, D, NP, UP, Q, W)\<close>
      by (cases S') auto
    have
      no_dup_q: \<open>no_duplicate_queued (twl_st_of None (st_l_of_wl None S'))\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S')))\<close>
      using struct_invs that by (auto simp: twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
    then have H1: \<open>L \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP)\<close> if LQ: \<open>L \<in># Q\<close> for L
    proof -
      obtain K where \<open>L = - lit_of K\<close> and \<open>K \<in># mset (convert_lits_l N M)\<close>
        using that no_dup_q LQ
        by (auto simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          lits_of_atms_of_mm_def atms_of_ms_def)
      then have \<open>atm_of L \<in> atm_of ` lits_of_l M\<close>
        by (auto simp: convert_lits_l_def lits_of_def)
      moreover {
        have \<open>atm_of ` lits_of_l M \<subseteq> (\<Union>x\<in>set (take U (tl N)). atm_of ` set (take 2 x) \<union>
           atm_of ` set (drop 2 x)) \<union> (\<Union>x\<in>set_mset NP. atms_of x)\<close>
          using that alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
          by (auto simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              lits_of_atms_of_mm_def atms_of_ms_def)
        then have \<open>atm_of ` lits_of_l M \<subseteq> (\<Union>x\<in>set (take U (tl N)). atm_of ` set x) \<union>
           (\<Union>x\<in>set_mset NP. atms_of x)\<close>
          unfolding image_Un[symmetric]
            set_append[symmetric]
            append_take_drop_id
            .
          then have \<open>atm_of ` lits_of_l M \<subseteq> atms_of_mm (mset `# mset (tl N) + NP)\<close>
            by (smt UN_Un Un_iff append_take_drop_id atms_of_ms_def atms_of_ms_mset_unfold set_append
                set_image_mset set_mset_mset set_mset_union subset_eq)
          }
      ultimately have \<open>atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NP)\<close>
        using that by blast
      then show ?thesis
        using that by (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff)
    qed
    then have H: \<open>clause_to_update L S = mset (W L)\<close> if \<open>L \<in># Q\<close> for L
      using corr_w that S by (auto simp: correct_watching.simps S' clause_to_update_def)
    have m: \<open>mset `# mset (take U (tl N)) + NP + (mset `# mset (drop (Suc U) N) + UP) =
              mset `# mset (tl N) + NP + UP\<close>
      apply (subst (2) append_take_drop_id[symmetric, of \<open>tl N\<close> U])
      unfolding mset_append by (auto simp: drop_Suc)
    show ?thesis
      unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
      apply (rule RES_refine)
      using that S' by (auto 5 5 simp: literals_to_update_wl_literals_to_update_l_iff correct_watching.simps clauses_def
          mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state m lits_of_atms_of_mm_union
          dest: H H1)
  qed
  have set_literals_to_update_add_remove: \<open>(set_literals_to_update_wl (add_mset L (literals_to_update_wl (set_literals_to_update_wl (remove1_mset L (literals_to_update_wl T')) T'))) (set_literals_to_update_wl (remove1_mset L (literals_to_update_wl T')) T')) = T'\<close>
    if \<open>L \<in># literals_to_update_wl T' \<close>for T' :: \<open>'v twl_st_wl\<close> and L
    using that by (cases T') auto
  have unit_propagation_outer_loop_wl: \<open>?u \<in> ?A \<rightarrow>
    \<langle>{(T', T).
       st_l_of_wl None T' = T \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       additional_WS_invs T \<and>
       correct_watching T'}\<rangle>nres_rel\<close>
    unfolding unit_propagation_outer_loop_wl_def unit_propagation_outer_loop_l_def
    apply (refine_vcg select_and_remove_from_literals_to_update_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for T' T by (auto simp: literals_to_update_wl_literals_to_update_l_iff)
    subgoal by auto
    subgoal for S' S T' T
      apply (subgoal_tac \<open>get_conflict (twl_st_of None (st_l_of_wl None T')) \<noteq> None \<longrightarrow>
    literals_to_update (twl_st_of None (st_l_of_wl None T')) = {#}\<close>)
      subgoal by (cases T'; cases S') auto
      subgoal by (simp add: twl_struct_invs_def del: propa_cands_enqueued.simps
            confl_cands_enqueued.simps valid_annotation.simps no_duplicate_queued.simps
            twl_st_exception_inv.simps unit_clss_inv.simps
            clauses_to_update_inv.simps)
      done
    subgoal by auto
    subgoal by auto
    subgoal for S' S T' T U'L' UL U' L' U L
      by (cases T') auto
    subgoal for S' S T' T U'L' UL U' L' U L
      apply (subst do_uncurry[of unit_propagation_inner_loop_wl])
      apply (subst do_uncurry[of unit_propagation_inner_loop_l])
      apply (rule unit_propagation_inner_loop_wl_spec["to_\<Down>"])
      apply (subgoal_tac \<open>(get_conflict (twl_st_of None (st_l_of_wl None T')) \<noteq> None \<longrightarrow>
         clauses_to_update (twl_st_of None (st_l_of_wl None T')) = {#} \<and> literals_to_update (twl_st_of None (st_l_of_wl None T')) = {#})\<close>)
          \<comment> \<open>this goal is extracted from the invariant\<close>
       apply (auto simp: correct_watching_set_literals_to_update set_literals_to_update_add_remove get_conflict_wl_set_literals_to_update_wl
          get_conflict_twl_st_of_st_l_of_wl literals_to_update_twl_st_of_st_l_of_wl; fail)
      apply (simp add: twl_struct_invs_def)
      done
    done

  have H: \<open>unit_propagation_outer_loop_wl S' \<le> \<Down> ?B (unit_propagation_outer_loop_l S)\<close>
    if A: \<open>(S', S) \<in> ?A\<close>
    for S S'
  proof -
    have A': \<open>(S, twl_st_of None S) \<in> {(S, S'). S' = twl_st_of None S \<and>
     twl_struct_invs (twl_st_of None S) \<and>  twl_stgy_invs (twl_st_of None S) \<and>
      additional_WS_invs S \<and> clauses_to_update_l S = {#} \<and> get_conflict_l S = None}\<close>
      using A by (cases S') auto
    have SS': \<open>st_l_of_wl None S' = S\<close>
      using A by auto
    have nf: \<open>nofail (unit_propagation_outer_loop (twl_st_of None (st_l_of_wl None S')))\<close>
      apply (rule SPEC_nofail)
      apply (rule unit_propagation_outer_loop)
      using A' SS' by (solves \<open>cases S';auto simp: get_conflict_l_st_l_of_wl\<close>)+
    show ?thesis
      using unit_propagation_outer_loop_l_spec["to_\<Down>", of S \<open>twl_st_of None S\<close>, OF A']
      using unit_propagation_outer_loop_wl["to_\<Down>", of S' S, OF A]
      unfolding SS'[symmetric]
      apply -
      apply unify_Down_invs2+
      apply (rule "weaken_\<Down>")
       prefer 2 using nf apply fast
      apply auto done
  qed

  show ?thesis
    apply "to_\<Down>"
    apply (rule H)
    apply assumption
    done
qed


subsubsection \<open>Decide or Skip\<close>

definition find_unassigned_lit_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit_wl = (\<lambda>(M, N, U, D, NP, UP, WS, Q).
     SPEC (\<lambda>L.
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)))) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))))))
     )\<close>

definition decide_wl_or_skip :: "'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres" where
  \<open>decide_wl_or_skip S = (do {
    ASSERT(twl_struct_invs (twl_st_of_wl None S));
    ASSERT(twl_stgy_invs (twl_st_of_wl None S));
    ASSERT(additional_WS_invs (st_l_of_wl None S));
    ASSERT(get_conflict_wl S = None);
    L \<leftarrow> find_unassigned_lit_wl S;
    if L \<noteq> None
    then do {
      let (M, N, U, D, NP, UP, Q, W) = S;
      ASSERT(L \<noteq> None);
      let K = the L;
      RETURN (False, (Decided K # M, N, U, D, NP, UP, {#-K#}, W))}
    else do {RETURN (True, S)}
  })
\<close>

lemma decide_wl_or_skip_spec:
  \<open>(decide_wl_or_skip, decide_l_or_skip)
 \<in> {(T':: 'v twl_st_wl, T).
       st_l_of_wl None T' = T \<and>
       correct_watching T' \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       get_conflict_wl T' = None \<and>
       additional_WS_invs (st_l_of_wl None T')} \<rightarrow>
    \<langle>{((b', T'), (b, T)). b' = b \<and>
       st_l_of_wl None T' = T \<and>
       correct_watching T'}\<rangle>nres_rel\<close>
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S'
    \<le> \<Down> Id
        (find_unassigned_lit S)\<close>
    if \<open>S = st_l_of_wl None S'\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that
    by (cases S') (auto simp: find_unassigned_lit_wl_def find_unassigned_lit_def)

  show ?thesis
    unfolding decide_wl_or_skip_def decide_l_or_skip_def
    apply (refine_vcg find_unassigned_lit_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    subgoal by auto
    done
qed


subsubsection \<open>Skip or Resolve\<close>

definition skip_and_resolve_loop_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>skip_and_resolve_loop_wl S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv (twl_st_of_wl None S\<^sub>0) (brk, twl_st_of_wl None S) \<and>
         additional_WS_invs (st_l_of_wl None S) \<and> correct_watching S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, Q, W) = S in
          do {
            ASSERT(M \<noteq> []);
            ASSERT(get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None);
            let D' = the (get_conflict_wl (M, N, U, D, NP, UP, Q, W));
            ASSERT(is_proped (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))));
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)));
            ASSERT(C < length N);
            if -L \<notin># D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, Q, W))}
            else
              if get_maximum_level M (remove1_mset (-L) D') = count_decided M
              then
                do {RETURN (remove1_mset (-L) D' \<union># (if C = 0 then {#} else remove1_mset L (mset (N!C))) = {#},
                   (tl M, N, U, Some (remove1_mset (-L) D' \<union># (if C = 0 then {#} else remove1_mset L (mset (N!C)))),
                     NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, D, NP, UP, Q, W))}
          }
        )
        (get_conflict_wl S\<^sub>0 = Some {#}, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma skip_and_resolve_loop_wl_spec:
  \<open>(skip_and_resolve_loop_wl, skip_and_resolve_loop_l)
 \<in> {(T'::'v twl_st_wl, T).
       st_l_of_wl None T' = T \<and>
       correct_watching T' \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       get_conflict_wl T' \<noteq> None \<and>
       literals_to_update_wl T' = {#} \<and>
       additional_WS_invs (st_l_of_wl None T')} \<rightarrow>
    \<langle>{(T', T).
       st_l_of_wl None T' = T \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       additional_WS_invs T \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) \<and>
       literals_to_update_wl T' = {#} \<and>
       get_conflict_wl T' \<noteq> None \<and>
       correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?s \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have get_conflict_wl: \<open>((get_conflict_wl S' = Some {#}, S'), get_conflict_l S = Some {#}, S)
    \<in> Id \<times>\<^sub>r {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<close>
    if \<open>S = st_l_of_wl None S'\<close> and \<open>correct_watching S'\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that by (cases S') auto
  have H: \<open>?s \<in> ?A \<rightarrow> \<langle>{(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<rangle>nres_rel\<close>
    unfolding skip_and_resolve_loop_wl_def skip_and_resolve_loop_l_def
    apply (refine_vcg get_conflict_wl)
    subgoal by (auto simp add: get_conflict_l_st_l_of_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S b'T' bT b' T' by (cases T') (auto simp: correct_watching.simps)
    subgoal for S' S b'T' bT b' T' by (cases T') (auto simp: correct_watching.simps)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    subgoal by auto
    subgoal by auto
    done

  have skip_and_resolve_loop_wl:
    \<open>skip_and_resolve_loop_wl x \<le> \<Down> ?B (skip_and_resolve_loop_l y)\<close>
    if A: \<open>(x, y) \<in> ?A\<close> for x :: \<open>'v twl_st_wl\<close> and y :: \<open>'v twl_st_l\<close>
  proof -
    have A': \<open>(y, twl_st_of None y)
    \<in> {(S, S'). S' = twl_st_of None S \<and>
                 twl_struct_invs (twl_st_of None S) \<and>
                 twl_stgy_invs (twl_st_of None S) \<and> additional_WS_invs S \<and>
                 clauses_to_update_l S = {#} \<and>
                 literals_to_update_l S = {#} \<and> get_conflict (twl_st_of None S) \<noteq> None}\<close>
      using A by (cases x, cases y) auto
    have nf: \<open>nofail (skip_and_resolve_loop (twl_st_of None y))\<close>
      apply (rule SPEC_nofail)
      apply (rule skip_and_resolve_loop_spec)
      using A' by (solves \<open>cases y; auto\<close>)+
    show ?thesis
      using H["to_\<Down>", of x y, OF A]
      using skip_and_resolve_loop_l_spec["to_\<Down>", of y \<open>twl_st_of None y\<close>, OF A'] apply -
      apply unify_Down_invs2+
      apply (rule "weaken_\<Down>")
       prefer 2 using nf apply blast
      by force
  qed
  show ?thesis
    apply ("to_\<Down>")
    apply (rule skip_and_resolve_loop_wl)
    apply assumption
    done
qed


subsubsection \<open>Backtrack\<close>

definition find_decomp_wl :: "'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> ('v, nat) ann_lits nres" where
  \<open>find_decomp_wl = (\<lambda>(M, N, U, D, NP, UP, Q, WS) L.
    SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

definition find_lit_of_max_level_wl :: "'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres" where
  \<open>find_lit_of_max_level_wl =  (\<lambda>(M, N, U, D, NP, UP, Q, W) L.
    SPEC(\<lambda>L'. L' \<in># remove1_mset (-L) (the D) \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>


fun extract_shorter_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clause nres\<close>
   where
  \<open>extract_shorter_conflict_wl (M, N, U, D, NP, UP, WS, Q) = SPEC(\<lambda>D'. D' \<subseteq># the D \<and>
     clause `# twl_clause_of `# mset (tl N) + NP + UP \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')\<close>

declare extract_shorter_conflict_wl.simps[simp del]
lemmas extract_shorter_conflict_wl_def = extract_shorter_conflict_wl.simps

definition backtrack_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>backtrack_wl S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, Q, W) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(D ~= None);
        ASSERT(-L \<in># the D);
        D' \<leftarrow> extract_shorter_conflict_wl (M, N, U, D, NP, UP, Q, W);
        ASSERT(get_level M L = count_decided M);
        ASSERT(D' \<noteq> {#});
        ASSERT(ex_decomp_of_max_lvl M (Some D') L);
        ASSERT(-L \<in># D');
        M1 \<leftarrow> find_decomp_wl (M, N, U, Some D', NP, UP, Q, W) L;

        if size D' > 1
        then do {
          ASSERT(\<forall>L' \<in># D' - {#-L#}. get_level M L' = get_level M1 L');
          ASSERT(\<exists>L' \<in># D' - {#-L#}. get_level M L' = get_maximum_level M (D' - {#-L#}));
          ASSERT(get_level M L > get_maximum_level M (D' - {#-L#}));
          L' \<leftarrow> find_lit_of_max_level_wl (M1, N, U, Some D', NP, UP, Q, W) L;
          ASSERT(L \<noteq> -L');
          D' \<leftarrow> list_of_mset D';
          ASSERT(atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(atm_of L' \<in> atms_of_mm (mset `# mset (tl N) + NP));
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L'  D'))], U,
            None, NP, UP, add_mset L {#}, W(-L:= W (-L) @ [length N], L':= W L' @ [length N]))
        }
        else do {
          _ \<leftarrow> list_of_mset D';
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset D' UP, add_mset L {#}, W)
        }
      }
    }
  \<close>


lemma correct_watching_learn:
  assumes N_ne_Nil: \<open>N \<noteq> []\<close> and
    L1: \<open>atm_of L1 \<in> atms_of_mm (mset `# mset (tl N) + NP)\<close> and
    L2: \<open>atm_of L2 \<in> atms_of_mm (mset `# mset (tl N) + NP)\<close> and
    UW: \<open>atms_of (mset UW) \<subseteq> atms_of_mm (mset `# mset (tl N) + NP)\<close>
  shows
  \<open>correct_watching (K # M, N @ [[L1 , L2] @ UW],
    U, D, NP, UP, Q, W (L1 := W L1 @ [length N], L2 := W L2 @ [length N])) \<longleftrightarrow>
  correct_watching (M, N, U, D, NP, UP, Q, W)\<close> (is \<open>?l \<longleftrightarrow> ?c\<close>)
proof (rule iffI)
  assume corr: ?l
  have H: \<open>\<And>x. x \<in># lits_of_atms_of_mm (mset `# mset (tl (N @ [L1 # L2 # UW]))) +
              lits_of_atms_of_mm NP \<longrightarrow>
        mset ((W(L1 := W L1 @ [length N], L2 := W L2 @ [length N])) x) =
        clause_to_update x
         (K # M, N @ [L1 # L2 # UW], U, D, NP, UP, {#}, {#})\<close>
    using corr
    by (auto simp: lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset if_distrib[of mset]
        uminus_lit_swap correct_watching.simps lits_of_atms_of_mm_union Ball_def
        all_conj_distrib)
  have [simp]: \<open>{x. (P x \<longrightarrow> Q x) \<and> P x} = {x. Q x \<and> P x}\<close> for P Q :: \<open>'a \<Rightarrow> bool\<close>
    by auto
  have [simp]: \<open>mset (W x) = clause_to_update x (M, N, U, D, NP, UP, {#}, {#})\<close>
    if \<open>x \<in># lits_of_atms_of_mm NP\<close>
    for x
    using that H[of x]
    by (auto split: if_splits simp: clause_to_update_def nth_append
        intro!: arg_cong[of _ _ mset_set])
  have [simp]: \<open>mset (W x) = clause_to_update x (M, N, U, D, NP, UP, {#}, {#})\<close>
    if \<open>x \<in># lits_of_atms_of_mm (mset `# mset (tl N))\<close>
    for x
    using that H[of x]
    by (auto split: if_splits simp: clause_to_update_def nth_append
        lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset
        intro!: arg_cong[of _ _ mset_set]) \<comment> \<open>slow but auto magic\<close>
  show ?c
    unfolding correct_watching.simps Ball_def
    by (auto simp add: lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset
        all_conj_distrib lits_of_atms_of_mm_union)
next
  assume corr: ?c
  have [simp]: \<open>{x. (P x \<longrightarrow> Q x) \<and> P x} = {x. Q x \<and> P x}\<close> for P Q :: \<open>'a \<Rightarrow> bool\<close>
    by auto
  have [simp]: \<open>clause_to_update L (K # M, N @ [L1 # L2 # UW], U, D, NP, UP, {#}, {#}) =
     clause_to_update L (M, N, U, D, NP, UP, {#}, {#}) +
     (if L = L1 \<or> L = L2 then {#length N#} else {#})\<close>
    for L
    using N_ne_Nil by (auto simp: clause_to_update_def nth_append
        intro: arg_cong[of _ _ mset_set])
  have \<open>L1 \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP)\<close> and
    \<open>-L1 \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP)\<close> and
    \<open>L2 \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP)\<close> and
    \<open>-L2 \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP)\<close>
    using L1 L2 by (auto simp add: in_lits_of_atms_of_mm_ain_atms_of_iff)
  then have [simp]:
    \<open>mset (W L1) = clause_to_update L1 (M, N, U, D, NP, UP, {#}, {#})\<close>
    \<open>mset (W (- L1)) = clause_to_update (- L1) (M, N, U, D, NP, UP, {#}, {#})\<close>
    \<open>mset (W L2) = clause_to_update L2 (M, N, U, D, NP, UP, {#}, {#})\<close>
    \<open>mset (W (- L2)) = clause_to_update (- L2) (M, N, U, D, NP, UP, {#}, {#})\<close>
    using corr by (auto simp: correct_watching.simps)
  have \<open>set_mset (lits_of_atms_of_m (mset UW)) \<subseteq> set_mset (lits_of_atms_of_mm (mset `# mset (tl N)+ NP))\<close>
    using UW using in_lits_of_atms_of_m_ain_atms_of_iff in_lits_of_atms_of_mm_ain_atms_of_iff by blast
  then show ?l
    using corr N_ne_Nil
    unfolding correct_watching.simps Ball_def
    by (auto simp add: lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset
        all_conj_distrib lits_of_atms_of_mm_union)
qed

lemma in_set_image_subsetD: \<open> f ` A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow>f x \<in> B\<close>
  by blast

lemma nofail_Down_nofail: \<open>nofail gS \<Longrightarrow> fS \<le> \<Down> R gS \<Longrightarrow> nofail fS\<close>
  using pw_ref_iff by blast

lemma backtrack_wl_spec:
  \<open>(backtrack_wl, backtrack_l)
 \<in> {(T'::'v twl_st_wl, T).
       st_l_of_wl None T' = T \<and>
       correct_watching T' \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       get_conflict_wl T' \<noteq> None \<and>
       get_conflict_wl T' \<noteq> Some {#} \<and>
       literals_to_update_wl T' = {#} \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) \<and>
       additional_WS_invs (st_l_of_wl None T')} \<rightarrow>
    \<langle>{(T', T).
       st_l_of_wl None T' = T \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       additional_WS_invs T \<and>
       get_conflict_wl T' = None \<and>
       literals_to_update_wl T' \<noteq> {#} \<and>
       correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?bt \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have find_decomp_wl: \<open>find_decomp_wl S' L' \<le> \<Down> Id (find_decomp S L)\<close>
    if \<open>L = L'\<close> and \<open>st_l_of_wl None S' = S\<close>
    for S and S' :: \<open>'v twl_st_wl\<close> and L L' :: \<open>'v literal\<close>
    using that by (cases S') (auto simp: find_decomp_wl_def find_decomp_def)
  have find_lit_of_max_level_wl:
    \<open>find_lit_of_max_level_wl (M1', N', U', D', NP', UP', W', Q') L' \<le>
       \<Down> {(L, L'). L = L' \<and> L \<in># (the D')}
         (find_lit_of_max_level (M, N, U, D, NP, UP, W, Q) L)\<close>
    if LL': \<open>L = L'\<close> and D: \<open>\<forall>L'\<in>#remove1_mset (-L) (the D). get_level M L' = get_level M1 L'\<close> and
    \<open>D = D'\<close> and [simp]: \<open>M1 = M1'\<close>
    for M M1 M1' and N N' and U U' and D D' NP NP' UP UP' W W' Q Q' and L L' :: \<open>'v literal\<close>
  proof -
    have \<open>get_level M `# remove1_mset (-L') (the D) = get_level M1 `# remove1_mset (-L') (the D)\<close>
      by (rule image_mset_cong) (use D LL' in auto)
    then have \<open> get_maximum_level M (remove1_mset (-L') (the D)) =
        get_maximum_level M1 (remove1_mset (-L') (the D))\<close>
      unfolding get_maximum_level_def by auto
    then show ?thesis
      using that by (auto simp: find_lit_of_max_level_wl_def find_lit_of_max_level_def
          intro!: RES_refine dest: in_diffD)
  qed
  have H: \<open>A \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> B \<Longrightarrow>
            A \<subseteq> atms_of_ms (mset ` set (tl N)) \<union> B\<close> for U A B and N :: \<open>'v clauses_l\<close>
    by (auto dest: in_atms_of_mset_takeD)
  have atms_of_diffD: \<open>La \<in> atms_of (A - B) \<Longrightarrow> La \<in> atms_of A\<close> for La and A B :: \<open>'a clause\<close>
    by (auto simp: atms_of_def dest: in_diffD)
  have list_of_mset: \<open>list_of_mset D \<le> \<Down> {(E, F). E = F \<and> D = mset E} (list_of_mset D')\<close>
    if \<open>D = D'\<close> for D D'
    using that by (auto simp: list_of_mset_def intro!: RES_refine)

  have ext: \<open>extract_shorter_conflict_wl T' \<le> \<Down> {(D', D''). D' = D'' \<and> 
      -lit_of (hd (get_trail_wl T')) \<in># D' \<and> D' \<subseteq># the D}
    (extract_shorter_conflict_l T)\<close>
    if \<open>st_l_of_wl None T' = T\<close> \<open>D = get_conflict_wl T'\<close> for T T' D
    using that 
    by (cases T; cases T') 
      (auto intro!: SPEC_refine simp: extract_shorter_conflict_l_def extract_shorter_conflict_wl_def)

  have hd_not_alien:
    \<open>atm_of (lit_of (hd M')) \<in> atms_of_mm (mset `# mset (tl N') + NP')\<close>
    if
      st: \<open>((M', N', U', E', NP', UP', Q', W), M, N, U, E, NP, UP, WS, Q)
      \<in> {(T', T). st_l_of_wl None T' = T \<and>
                   correct_watching T' \<and>
                   twl_struct_invs (twl_st_of_wl None T') \<and>
                   twl_stgy_invs (twl_st_of_wl None T') \<and>
                   get_conflict_wl T' \<noteq> None \<and>
                   get_conflict_wl T' \<noteq> Some {#} \<and>
                   literals_to_update_wl T' = {#} \<and>
                   (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and>
                   (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and> additional_WS_invs (st_l_of_wl None T')}\<close> and
      M'_empty: \<open>M' \<noteq> []\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (M', N', U', E', NP', UP', Q', W))\<close>

      for M N U E NP UP WS Q M' N' U' E' NP' UP' Q' W M''' M'''' L L' D D' D''' D''''
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M', N', U', E', NP', UP', Q', W)))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then show ?thesis
      using M'_empty unfolding  cdcl\<^sub>W_restart_mset.no_strange_atm_def
        by (cases M') (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            mset_take_mset_drop_mset dest: in_atms_of_mset_takeD)
    qed

  have not_alien:
    "atm_of L' \<in> atms_of_mm (mset `# mset (tl N') + NP')"
    if
      stuct_invs: "twl_struct_invs (twl_st_of_wl None (M', N', U', E', NP', UP', Q', W))" and
      L': "(L', L'a) \<in> {(L, L'). L = L' \<and> L \<in># the (Some D')}" and
      D_D': "(D', D) \<in> {(D, D'). D = D' \<and> L'' \<in># D \<and> 
        D \<subseteq># the (get_conflict_wl (M', N', U', E', NP', UP', Q', W))}" and
      E': "((a, b, c, E', S'), T')
         \<in> {(T', T).
             st_l_of_wl None T' = T \<and>
             correct_watching T' \<and>
             twl_struct_invs (twl_st_of_wl None T') \<and>
             twl_stgy_invs (twl_st_of_wl None T') \<and>
             get_conflict_wl T' \<noteq> None \<and>
             get_conflict_wl T' \<noteq> Some {#} \<and>
             literals_to_update_wl T' = {#} \<and>
             (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip
                       (state\<^sub>W_of (twl_st_of_wl None T'))
                       S') \<and>
             (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve
                       (state\<^sub>W_of (twl_st_of_wl None T'))
                       S') \<and>
             additional_WS_invs (st_l_of_wl None T')}"
    for L' M' N' U' E' NP' UP' Q' W' D D' M L'a W T' a b c S' L''
  proof -
    have E': "E' \<noteq> None"
      using E' by (cases S') auto
    have no_alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M', N', U', E', NP', UP', Q', W)))\<close>
      using stuct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    moreover have \<open>L' \<in># the E'\<close>
      using E' D_D' L' by (auto simp: mset_take_mset_drop_mset)
    ultimately show ?thesis
      using E'
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          mset_take_mset_drop_mset dest!: atm_of_lit_in_atms_of in_atms_of_mset_takeD)
  qed
  have ref:
    \<open>((Propagated (- lit_of (hd M')) (length N') # L, N' @ [[- lit_of (hd M'), L'] @ remove1 (- lit_of (hd M')) (remove1 L' D'b)], U', None, NP', UP', unmark (hd M'), W
      (- lit_of (hd M') := W (- lit_of (hd M')) @ [length N'], L' := W L' @ [length N'])),
     (Propagated (- lit_of (hd M)) (length N) # M1a, N @ [[- lit_of (hd M), L'a] @ remove1 (- lit_of (hd M)) (remove1 L'a D'')], U, None, NP, UP, WS, unmark (hd M)))
    \<in> {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<close>
     (is \<open>(?U', ?V') \<in> {(T', T). ?conv T' = T \<and> correct_watching T'}\<close>)
     if
        S: \<open>((M', N', U', E', NP', UP', Q', W), M, N, U, E, NP, UP, WS, Q)
        \<in> {(T', T). st_l_of_wl None T' = T \<and>
                     correct_watching T' \<and>
                     twl_struct_invs (twl_st_of_wl None T') \<and>
                     twl_stgy_invs (twl_st_of_wl None T') \<and>
                     get_conflict_wl T' \<noteq> None \<and>
                     get_conflict_wl T' \<noteq> Some {#} \<and>
                     literals_to_update_wl T' = {#} \<and>
                     (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and>
                     (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and>
                     additional_WS_invs (st_l_of_wl None T')}\<close>
        (is \<open>(?U, ?V) \<in> _\<close>)and
        M'_empty: \<open>M' \<noteq> []\<close> and
        M: \<open>(M''', M'''') \<in> {(D', D''). D' = D'' \<and> 
               - lit_of (hd (get_trail_wl (M', N', U', E', NP', UP', Q', W))) \<in># D' \<and>
               D' \<subseteq># the (get_conflict_wl (M', N', U', E', NP', UP', Q', W))}\<close> and
        M''''_nempty: \<open>M'''' \<noteq> {#}\<close> and
        struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (M', N', U', E', NP', UP', Q', W))\<close> and
        L_M1a: \<open>(L, M1a) \<in> Id\<close> and
        size_M'''': \<open>1 < size M''''\<close> and
        L'_L'a: \<open>(L', L'a) \<in> {(L, L'). L = L' \<and> L \<in># the (Some M''')}\<close> and
        D'': \<open>(D'b, D'') \<in> {(E, F). E = F \<and> M''' = mset E}\<close> and
        atm_hd: \<open>atm_of (lit_of (hd M')) \<in> atms_of_mm (mset `# mset (tl N') + NP')\<close> and
        atm: \<open>atm_of L' \<in> atms_of_mm (mset `# mset (tl N') + NP')\<close>
     for M' N' U'  E' NP' UP' W Q' M N U E NP UP WS Q L M1a M''' M'''' L' L'a D'b D''
   proof -
     have conv: \<open>?conv ?U' = ?V'\<close> and corr: \<open>correct_watching ?U\<close>
       using S L_M1a L'_L'a M''''_nempty size_M'''' D'' by auto
     have add: \<open>additional_WS_invs (st_l_of_wl None ?U)\<close>
       using S by auto
     have E': \<open>E' \<noteq> None\<close>
       using S by auto
     have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M', N', U', E', NP', UP', Q', W)))\<close>
       using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       by fast
     then have \<open>atms_of (the E') \<subseteq> atms_of_ms (mset ` set (take U' (tl N'))) \<union> atms_of_mm NP'\<close>
       using D'' E'
       by (cases E') (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          mset_take_mset_drop_mset)
     moreover have \<open>mset D'b \<subseteq># the E'\<close>
       using M D'' by auto
     ultimately have atms_D: \<open>atms_of (mset D'b) \<subseteq> atms_of_mm (mset `# mset (tl N') + NP')\<close>
       using atms_of_subset_mset_mono in_atms_of_mset_takeD by fastforce

     have corr: \<open>correct_watching ?U'\<close>
      apply (subst correct_watching_learn)
      subgoal using add by (auto simp: additional_WS_invs_def)
      subgoal using atm_hd by simp
      subgoal using atm .
      subgoal using atms_D by (fastforce dest: atms_of_diffD)
      subgoal using corr by (auto simp add: correct_watching.simps clause_to_update_def)
      done
    show ?thesis
      using corr conv by blast
  qed


  have H: \<open>?bt \<in> ?A \<rightarrow> \<langle>{(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<rangle>nres_rel\<close>
    unfolding backtrack_wl_def backtrack_l_def
    apply (refine_vcg find_decomp_wl find_lit_of_max_level_wl list_of_mset ext; remove_dummy_vars)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule hd_not_alien) assumption+
    subgoal by (rule not_alien) assumption+
    subgoal by (rule ref) assumption+
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    done
  have bt: \<open>backtrack_wl S \<le> \<Down> ?B (backtrack_l T)\<close>
    if A: \<open>(S, T) \<in> ?A\<close>
    for S :: \<open>'v twl_st_wl\<close> and T :: \<open>'v twl_st_l\<close>
  proof -
    have A':
      \<open>(T, twl_st_of None T) \<in> {(S, S'). S' = twl_st_of None S \<and>
                 get_conflict_l S \<noteq> None \<and>
                 get_conflict_l S \<noteq> Some {#} \<and>
                 clauses_to_update_l S = {#} \<and>
                 literals_to_update_l S = {#} \<and>
                 additional_WS_invs S \<and>
                 (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None S)) S') \<and>
                 (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None S)) S') \<and>
                 twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S)}\<close>
      using A by (cases S) auto
    have nf: \<open>nofail (backtrack (twl_st_of None T))\<close>
      apply (rule SPEC_nofail)
      apply (rule backtrack_spec["to_\<Down>"])
      using A' by (solves \<open>cases T; auto\<close>)+
    show ?thesis
      using backtrack_l_spec["to_\<Down>", of \<open>T\<close> \<open>twl_st_of None T\<close>, OF A']
      using H["to_\<Down>", of S T, OF A]
      apply -
      apply unify_Down_invs2+
      apply (rule "weaken_\<Down>")
       prefer 2 using nf apply fast
      apply auto
      done
  qed
  show ?thesis
    apply "to_\<Down>"
    apply (rule bt)
    apply assumption
    done
qed


subsubsection \<open>Backtrack, Skip, Resolve or Decide\<close>

definition cdcl_twl_o_prog_wl :: "'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres" where
  \<open>cdcl_twl_o_prog_wl S =
    do {
      ASSERT(twl_struct_invs (twl_st_of_wl None S));
      ASSERT(twl_stgy_invs (twl_st_of_wl None S));
      ASSERT(additional_WS_invs (st_l_of_wl None S));
      do {
        if get_conflict_wl S = None
        then decide_wl_or_skip S
        else do {
          T \<leftarrow> skip_and_resolve_loop_wl S;
          ASSERT(get_conflict_wl T \<noteq> None);
          if get_conflict_wl T \<noteq> Some {#}
          then do {U \<leftarrow> backtrack_wl T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

lemma set_Collect_Pair_to_fst_snd:
  \<open>{((a, b), (a', b')). P a b a' b'} = {(e, f). P (fst e) (snd e) (fst f) (snd f)}\<close>
  by auto

lemma cdcl_twl_o_prog_wl_spec:
  \<open>(cdcl_twl_o_prog_wl, cdcl_twl_o_prog_l) \<in> {(S::'v twl_st_wl, S'::'v twl_st_l).
     S' = st_l_of_wl None S \<and>
     literals_to_update_wl S = {#} \<and>
     (\<forall>S'. \<not> cdcl_twl_cp (twl_st_of_wl None S) S') \<and>
     twl_struct_invs (twl_st_of_wl None S) \<and>
     twl_stgy_invs (twl_st_of_wl None S) \<and>
     additional_WS_invs (st_l_of_wl None S) \<and>
     correct_watching S} \<rightarrow>
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     T' = st_l_of_wl None T \<and>
     brk = brk' \<and>
     additional_WS_invs (st_l_of_wl None T) \<and>
     (get_conflict_wl T \<noteq> None \<longrightarrow>
      get_conflict_wl T = Some {#}) \<and>
     twl_struct_invs (twl_st_of_wl None T) \<and>
     twl_stgy_invs (twl_st_of_wl None T) \<and>
     correct_watching T}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S \<le> \<Down> Id (find_unassigned_lit S')\<close>
    if \<open>S' = st_l_of_wl None S\<close>
    for S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
    unfolding find_unassigned_lit_wl_def find_unassigned_lit_def that
    by (cases S) auto
  have cdcl_o: \<open>?o \<in> ?A \<rightarrow>
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     T' = st_l_of_wl None T \<and>
     brk = brk' \<and>
     correct_watching T}\<rangle>nres_rel\<close>
    unfolding cdcl_twl_o_prog_wl_def cdcl_twl_o_prog_l_def decide_wl_or_skip_def
      decide_l_or_skip_def
    apply (refine_vcg skip_and_resolve_loop_wl_spec["to_\<Down>"] backtrack_wl_spec["to_\<Down>"] find_unassigned_lit_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    subgoal by auto
    subgoal by auto
    subgoal for S S' T T' by (cases T) auto
    subgoal for S S' T T' by (cases T) auto
    subgoal for S S' T T' by auto
    subgoal by auto
    subgoal by auto
    done
  have cdcl_twl_o_prog_wl: \<open>cdcl_twl_o_prog_wl S \<le> \<Down> ?B (cdcl_twl_o_prog_l S')\<close>
    if A: \<open>(S, S') \<in> ?A\<close> for S S'
  proof -
    have A': \<open>(S', twl_st_of None S') \<in> {(S, S').
      S' = twl_st_of None S \<and>
      clauses_to_update_l S = {#} \<and>
      literals_to_update_l S = {#} \<and>
      (\<forall>S'. \<not> cdcl_twl_cp (twl_st_of None S) S') \<and>
      twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and> additional_WS_invs S}\<close>
      using A by (cases S) auto
    have SS': \<open>st_l_of_wl None S = S'\<close>
      using A by fast
    have nf: \<open>nofail (cdcl_twl_o_prog (twl_st_of None S'))\<close>
      apply (rule SPEC_nofail)
      apply (rule cdcl_twl_o_prog_spec["to_\<Down>"])
      using A' by (solves \<open>cases S'; auto\<close>)+
    show ?thesis
      using cdcl_twl_o_prog_l_spec["to_\<Down>", of S' \<open>twl_st_of None S'\<close>, OF A']
      using cdcl_o["to_\<Down>", of S S', OF A]
      unfolding SS'
      apply -
      unfolding set_Collect_Pair_to_fst_snd
      apply unify_Down_invs2+
      apply (rule "weaken_\<Down>")
       prefer 2 using nf apply fast
      by force
  qed
  show ?thesis
    apply "to_\<Down>"
    by (rule cdcl_twl_o_prog_wl) assumption
qed


subsubsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>cdcl_twl_stgy_prog_wl S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of_wl None T) \<and>
          twl_stgy_invs (twl_st_of_wl None T) \<and>
          (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of_wl None T)) \<and>
          cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of_wl None S\<^sub>0) (twl_st_of_wl None T) \<and>
          (\<not>brk \<longrightarrow> get_conflict_wl T = None)\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl S;
          cdcl_twl_o_prog_wl T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

theorem cdcl_twl_stgy_prog_wl_spec:
  \<open>(cdcl_twl_stgy_prog_wl, cdcl_twl_stgy_prog_l) \<in> {(S::'v twl_st_wl, S').
       S' = st_l_of_wl None S \<and>
       twl_struct_invs (twl_st_of_wl None S) \<and>
       twl_stgy_invs (twl_st_of_wl None S) \<and>
       additional_WS_invs (st_l_of_wl None S) \<and>
       correct_watching S} \<rightarrow>
    \<langle>{(S, S'). S' = st_l_of_wl None S }\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S'), False, S) \<in> {((brk', T'), (brk, T)). brk = brk' \<and> T = st_l_of_wl None T'}\<close>
    if \<open>S = st_l_of_wl None S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_def cdcl_twl_stgy_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec["to_\<Down>"] cdcl_twl_o_prog_wl_spec["to_\<Down>"])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' SS' by (cases SS') auto
    subgoal by auto
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' brk T U' U by (cases U') auto
    subgoal by auto
    done
qed


lemma cdcl_twl_stgy_prog_wl_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S = None\<close> and \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    \<open>correct_watching S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le>
      \<Down> {(S, S'). S' = st_l_of_wl None S}
        (SPEC(\<lambda>T. full cdcl_twl_stgy (twl_st_of_wl None S) (twl_st_of None T)))\<close>
  apply (rule order_trans)
   apply (rule cdcl_twl_stgy_prog_wl_spec["to_\<Down>", of _ \<open>st_l_of_wl None S\<close>])
  subgoal using assms by auto
  apply (rule order_trans)
   apply (rule ref_two_step)
    apply auto[]
   apply (rule cdcl_twl_stgy_prog_l_spec_final)
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by (cases S) auto
  subgoal using assms by (cases S) auto
  subgoal using assms by auto
  subgoal by auto
  done

lemma cdcl_twl_stgy_prog_wl_spec_final2_Down:
  assumes \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S = None\<close> and \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    \<open>correct_watching S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le>
      \<Down> {(S, S'). S' = st_l_of_wl None S}
        (SPEC(\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of (twl_st_of_wl None S))
          (state\<^sub>W_of (twl_st_of None T))))\<close>
  apply (rule ref_two_step)
   apply (rule cdcl_twl_stgy_prog_wl_spec_final[OF assms])
  apply (rule weaken_SPEC)
   apply (rule order.refl)
  using full_cdcl_twl_stgy_cdcl\<^sub>W_stgy[OF _ assms(1)] by blast


theorem cdcl_twl_stgy_prog_wl_spec_final2:
  assumes \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S = None\<close> and \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    \<open>correct_watching S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le>
       SPEC(\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of (twl_st_of_wl None S))
          (state\<^sub>W_of (twl_st_of_wl None T)))\<close>
  using cdcl_twl_stgy_prog_wl_spec_final2_Down[OF assms] unfolding conc_fun_SPEC
  by auto


subsection \<open>Final Theorem with Initialisation\<close>

fun init_wl_of :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>init_wl_of (M, N, U, D, NP, UP, _, Q) =
       (M, N, U, D, NP, UP, Q, calculate_correct_watching (tl N) (\<lambda>_. []) 1)\<close>

theorem init_dt_wl:
  fixes CS S
  defines S\<^sub>0: \<open>S\<^sub>0 \<equiv> ([], [[]], 0, None, {#}, {#}, {#}, {#})\<close>
  defines S: \<open>S \<equiv> init_wl_of (init_dt CS S\<^sub>0)\<close>
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    le: \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    taut: \<open>\<forall>C \<in> set CS. \<not>tautology (mset C)\<close> and
    no_confl: \<open>get_conflict_wl S = None\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le> SPEC (\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
             (state\<^sub>W_of (twl_st_of_wl None S))
             (state\<^sub>W_of (twl_st_of_wl None T)))\<close>
proof -
  obtain M N U D NP UP WS Q where
    init: \<open>init_dt CS S\<^sub>0 = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases \<open>init_dt CS S\<^sub>0\<close>) auto
  have \<open>N \<noteq> []\<close>
    using clauses_init_dt_not_Nil[of CS] init unfolding S\<^sub>0[symmetric] by auto
  then have corr_w: \<open>correct_watching S\<close>
    unfolding S init
    by (auto simp: correct_watching.simps
        calculate_correct_watching[of _ _ _ M \<open>hd N\<close> U D NP UP])
  have
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S)) = mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>additional_WS_invs (st_l_of_wl None S)\<close>
    unfolding S S\<^sub>0
    subgoal
      using init_dt(1)[OF dist le taut]
        by (cases \<open>(init_dt CS ([], [[]], 0, None, {#}, {#}, {#}, {#}))\<close>) auto
    subgoal
      using init_dt(2)[OF dist le taut]
        by (cases \<open>(init_dt CS ([], [[]], 0, None, {#}, {#}, {#}, {#}))\<close>) auto
    subgoal
      using init_dt(3)[OF dist le taut]
        by (cases \<open>(init_dt CS ([], [[]], 0, None, {#}, {#}, {#}, {#}))\<close>) auto
    subgoal
      using init_dt(5)[OF dist le taut]
      by (cases \<open>(init_dt CS ([], [[]], 0, None, {#}, {#}, {#}, {#}))\<close>)
        (auto simp: additional_WS_invs_def)
    done
  from cdcl_twl_stgy_prog_wl_spec_final2[OF this(1,3) no_confl this(4) corr_w]
  show ?thesis
    .
qed

end
