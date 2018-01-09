theory Watched_Literals_Watch_List
  imports Watched_Literals_List
begin

text \<open>Less ambiguities in the notations (TODO: using a bundle would probably be better):\<close>

(* TODO Move somewhere *)
lemma in_atms_of_mset_takeD:
  \<open>x \<in> atms_of_ms (mset ` set (take U (tl N))) \<Longrightarrow> x \<in> atms_of_ms (mset ` set ((tl N)))\<close>
  by (auto dest: in_set_takeD simp:atms_of_ms_def)
(* End Move *)


section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>

type_synonym clauses_to_update_wl = \<open>nat multiset\<close>
type_synonym watched = \<open>nat list\<close>
type_synonym 'v lit_queue_wl = \<open>'v literal multiset\<close>

type_synonym 'v twl_st_wl =
  \<open>('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl \<times>
    ('v literal \<Rightarrow> watched)\<close>

subsection \<open>Access Functions\<close>

fun clauses_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> clauses_to_update_wl\<close> where
  \<open>clauses_to_update_wl (_, _, _, _, _, _, _, W) L i = mset (drop i (W L))\<close>

fun get_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_wl (M, _, _, _, _, _, _, _) = M\<close>

fun literals_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v lit_queue_wl\<close> where
  \<open>literals_to_update_wl (_, _, _, _, _, _, Q, _) = Q\<close>

fun set_literals_to_update_wl :: \<open>'v lit_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_literals_to_update_wl Q (M, N, U, D, NE, UE, _, W) = (M, N, U, D, NE, UE, Q, W)\<close>

fun get_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_wl (_, _, _, D, _, _, _, _) = D\<close>

fun get_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_wl (M, N, U, D, NE, UE, WS, Q) = N\<close>

fun get_learned_wl :: \<open>'v twl_st_wl \<Rightarrow> nat\<close> where
  \<open>get_learned_wl (M, N, U, D, NE, UE, WS, Q) = U\<close>

definition get_unit_learned :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned = (\<lambda>(M, N, U, D, NE, UE, Q, W). UE)\<close>

definition get_unit_init_clss :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clss = (\<lambda>(M, N, U, D, NE, UE, Q, W). NE)\<close>

definition all_lits_of_mm :: \<open>'a clauses \<Rightarrow> 'a literal multiset\<close> where
\<open>all_lits_of_mm Ls = Pos `# (atm_of `# (\<Union># Ls)) + Neg `# (atm_of `# (\<Union># Ls))\<close>

lemma all_lits_of_mm_empty[simp]: \<open>all_lits_of_mm {#} = {#}\<close>
  by (auto simp: all_lits_of_mm_def)


text \<open>
  We cannot just extract the literals of the clauses: we cannot be sure that atoms appear \<^emph>\<open>both\<close>
  positively and negatively in the clauses. If we could ensure that there are no pure literals, the
  definition of \<^term>\<open>all_lits_of_mm\<close> can be changed to \<open>all_lits_of_mm Ls = \<Union># Ls\<close>.
\<close>
fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, U, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm (mset `# mset (tl N) + NE). mset (W L) = clause_to_update L (M, N, U, D, NE, UE, {#}, {#}))\<close>

declare correct_watching.simps[simp del]

fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> watched\<close> where
  \<open>watched_by (M, N, U, D, NE, UE, Q, W) L = W L\<close>

fun update_watched :: \<open>'v literal \<Rightarrow> watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, U, D, NE, UE, Q, W) = (M, N, U, D, NE, UE, Q, W(L:= WL))\<close>

fun delete_index_and_swap where
  \<open>delete_index_and_swap l i = butlast(l[i := last l])\<close>

lemma in_all_lits_of_mm_ain_atms_of_iff: \<open>L \<in># all_lits_of_mm N \<longleftrightarrow> atm_of L \<in> atms_of_mm N\<close>
  by (cases L) (auto simp: all_lits_of_mm_def atms_of_ms_def atms_of_def)

lemma all_lits_of_mm_union:
  \<open>all_lits_of_mm (M + N) = all_lits_of_mm M + all_lits_of_mm N\<close>
  unfolding all_lits_of_mm_def by auto

definition all_lits_of_m :: \<open>'a clause \<Rightarrow> 'a literal multiset\<close> where
  \<open>all_lits_of_m Ls = Pos `# (atm_of `# Ls) + Neg `# (atm_of `# Ls)\<close>

lemma all_lits_of_m_empty[simp]: \<open>all_lits_of_m {#} = {#}\<close>
  by (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_empty_iff[iff]: \<open>all_lits_of_m A = {#} \<longleftrightarrow> A = {#}\<close>
  by (cases A) (auto simp: all_lits_of_m_def)

lemma in_all_lits_of_m_ain_atms_of_iff: \<open>L \<in># all_lits_of_m N \<longleftrightarrow> atm_of L \<in> atms_of N\<close>
  by (cases L) (auto simp: all_lits_of_m_def atms_of_ms_def atms_of_def)

lemma in_clause_in_all_lits_of_m: \<open>x \<in># C \<Longrightarrow> x \<in># all_lits_of_m C\<close>
  using atm_of_lit_in_atms_of in_all_lits_of_m_ain_atms_of_iff by blast

lemma all_lits_of_mm_add_mset:
  \<open>all_lits_of_mm (add_mset C N) = (all_lits_of_m C) + (all_lits_of_mm N)\<close>
  by (auto simp: all_lits_of_mm_def all_lits_of_m_def)

lemma all_lits_of_m_add_mset:
  \<open>all_lits_of_m (add_mset L C) = add_mset L (add_mset (-L) (all_lits_of_m C))\<close>
  by (cases L) (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_union:
  \<open>all_lits_of_m (A + B) = all_lits_of_m A + all_lits_of_m B\<close>
  by (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_mono:
  \<open>D \<subseteq># D' \<Longrightarrow> all_lits_of_m D \<subseteq># all_lits_of_m D'\<close>
  by (auto elim!: mset_le_addE simp: all_lits_of_m_union)

fun st_l_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl None (M, N, C, D, NE, UE, Q, W) = (M, N, C, D, NE, UE, {#}, Q)\<close>
| \<open>st_l_of_wl (Some (L, j)) (M, N, C, D, NE, UE, Q, W) =
    (M, N, C, D, NE, UE, (if D \<noteq> None then {#} else clauses_to_update_wl (M, N, C, D, NE, UE, Q, W) L j,
      Q))\<close>

fun twl_st_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st\<close> where
  \<open>twl_st_of_wl L S = twl_st_of (map_option fst L) (st_l_of_wl L S)\<close>

fun remove_one_lit_from_wq :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>remove_one_lit_from_wq L (M, N, C, D, NE, UE, WS, Q) = (M, N, C, D, NE, UE, remove1_mset L WS, Q)\<close>

lemma remove_one_lit_from_wq_def:
  \<open>remove_one_lit_from_wq L S = set_clauses_to_update_l (clauses_to_update_l S - {#L#}) S\<close>
  by (cases S) auto

lemma literals_to_update_wl_literals_to_update_l_iff:
  \<open>literals_to_update_l (st_l_of_wl L S) = literals_to_update_wl S\<close>
  by (cases S; cases L) auto

lemma correct_watching_set_literals_to_update:
  \<open>correct_watching (set_literals_to_update_wl WS T') = correct_watching T'\<close>
  by (cases T') (auto simp: correct_watching.simps)

lemma get_conflict_wl_set_literals_to_update_wl:
  \<open>get_conflict_wl (set_literals_to_update_wl P S) = get_conflict_wl S\<close>
  by (cases S) auto

lemma get_conflict_twl_st_of_wl:
  \<open>get_conflict (twl_st_of_wl L' T') = get_conflict_wl T'\<close>
  by (cases T'; cases L') auto

lemma literals_to_update_twl_st_of_st_l_of_wl:
  \<open>literals_to_update (twl_st_of L (st_l_of_wl L' T')) = literals_to_update_wl T'\<close>
  by (cases T'; cases L; cases L') auto

lemma get_conflict_l_st_l_of_wl:
  \<open>get_conflict_l (st_l_of_wl L S) = get_conflict_wl S\<close>
  by (cases S; cases L) auto

lemma (in -) clauses_twl_st_of_wl:
  \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (M, N, U, y, NE, UE, Q, W))) =
     mset `# mset (tl N) + NE + UE\<close>
  by (auto simp del: append_take_drop_id simp: mset_take_mset_drop_mset' clauses_def)

lemma (in -) conflicting_twl_st_of_wl:
  \<open>conflicting (state\<^sub>W_of (twl_st_of_wl L S)) = get_conflict_wl S\<close>
  by (cases S; cases L) (auto simp: conflicting.simps)

lemma get_trail_l_st_l_of_wl: \<open>get_trail_l (st_l_of_wl None S) = get_trail_wl S\<close>
  by (cases S) auto


text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>.\<close>
definition unit_prop_body_wl_inv where
\<open>unit_prop_body_wl_inv T' i L \<longleftrightarrow>
    twl_struct_invs (twl_st_of_wl (Some (L, i)) T') \<and>
    twl_stgy_invs (twl_st_of_wl (Some (L, i)) T') \<and>
    twl_list_invs (st_l_of_wl (Some (L, i)) T') \<and>
    correct_watching T' \<and>
    i < length (watched_by T' L) \<and>
    get_conflict_wl T' = None \<and>
    (watched_by T' L) ! i > 0 \<and>
    i < length (watched_by T' L) \<and>
    watched_by T' L ! i < length (get_clauses_wl T') \<and>
    unit_propagation_inner_loop_body_l_inv L (watched_by T' L ! i) (st_l_of_wl (Some (L, Suc i)) T') \<and>
    L \<in># all_lits_of_mm (mset `# mset (tl (get_clauses_wl T')) + (get_unit_init_clss T'))
  \<close>


definition set_conflict_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl = (\<lambda>C (M, N, U, D, NE, UE, Q, W). (M, N, U, Some (mset C), NE, UE, {#}, W))\<close>


definition propagate_lit_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>propagate_lit_wl = (\<lambda>L' C i (M, N, U, D, NE, UE, Q, W).
      let N = list_update N C (swap (N!C) 0 (Suc 0 - i)) in
      (Propagated L' C # M, N, U, D, NE, UE, add_mset (-L') Q, W))\<close>

definition update_clause_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>update_clause_wl = (\<lambda>(L::'v literal) C w i f (M, N, U, D, NE, UE, Q, W). do {
     let K' = (N!C) ! f;
     let N' = list_update N C (swap (N!C) i f);
     RETURN (w, (M, N', U, D, NE, UE, Q, W(L := delete_index_and_swap (watched_by (M, N, U, D, NE, UE, Q, W) L) w, K':= W K' @ [C])))

  })\<close>

definition unit_prop_body_wl_find_unwatched_inv where
\<open>unit_prop_body_wl_find_unwatched_inv f C S \<longleftrightarrow>
   (get_clauses_wl S)!C \<noteq> [] \<and>
   (f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l ((get_clauses_wl S)!C)). - L \<in> lits_of_l (get_trail_wl S)))\<close>

definition unit_propagation_inner_loop_body_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl L w S = do {
      ASSERT(unit_prop_body_wl_inv S w L);
      let C = (watched_by S L) ! w;
      let i = (if ((get_clauses_wl S)!C) ! 0 = L then 0 else 1);
      let L' = ((get_clauses_wl S)!C) ! (1 - i);
      let val_L' = polarity (get_trail_wl S) L';
      if val_L' = Some True
      then RETURN (w+1, S)
      else do {
        f \<leftarrow> find_unwatched_l (get_trail_wl S) ((get_clauses_wl S)!C);
        ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
        case f of
          None \<Rightarrow>
            if val_L' = Some False
            then do {RETURN (w+1, set_conflict_wl ((get_clauses_wl S)!C) S)}
            else do {RETURN (w+1, propagate_lit_wl L' C i S)}
        | Some f \<Rightarrow> do {
            update_clause_wl L C w i f S
          }
      }
   }\<close>


subsection \<open>The Functions\<close>

subsubsection \<open>Inner Loop\<close>

lemma image_mset_mset_update: \<open>f `# mset (xs [i := x]) = mset ((map f xs) [i := f x])\<close>
  by (auto simp: map_update[symmetric])

lemma
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
    add_inv: \<open>twl_list_invs S'\<close> and
    stgy_inv: \<open>twl_stgy_invs S''\<close>
  shows  unit_propagation_inner_loop_body_wl_spec: \<open>unit_propagation_inner_loop_body_wl L w S \<le>
   \<Down> {((i, T'), T).
        T = st_l_of_wl (Some (L, i)) T' \<and>
        twl_struct_invs (twl_st_of_wl (Some (L, i)) T') \<and>
        twl_stgy_invs (twl_st_of_wl (Some (L, i)) T') \<and>
        twl_list_invs T \<and>
        correct_watching T' \<and>
        i \<le> length (watched_by T' L)}
     (unit_propagation_inner_loop_body_l L C' T)\<close> (is \<open>?propa\<close>)and
    unit_propagation_inner_loop_body_wl_update:
      \<open>mset `# mset (tl (get_clauses_wl S[watched_by S L ! w :=
                     swap (get_clauses_wl S ! (watched_by S L ! w)) 0
                           (1 - (if (get_clauses_wl S)!(watched_by S L ! w) ! 0 = L then 0 else 1))])) =
        mset `# mset ((tl (get_clauses_wl S)))\<close>
proof -
  have val: \<open>(polarity a b, polarity a' b') \<in> Id\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' :: \<open>('a, 'b) ann_lits\<close> and b b' :: \<open>'a literal\<close>
    by (auto simp: that)
  let ?M = \<open>get_trail_wl S\<close>
  have f: \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S ! (watched_by S L ! w))
      \<le> \<Down> {(found, found'). found = found' \<and>
             (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l C''). -L \<in> lits_of_l ?M)) \<and>
             (\<forall>j. found = Some j \<longrightarrow> (j < length C'' \<and> (undefined_lit ?M (C''!j) \<or> C''!j \<in> lits_of_l ?M) \<and> j \<ge> 2))
           }
            (find_unwatched_l (get_trail_l T) (get_clauses_l T ! C'))\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    by (cases S) (auto simp: find_unwatched_l_def intro!: RES_refine)
  obtain M N U NE UE Q W where
    S: \<open>S = (M, N, U, None, NE, UE, Q, W)\<close>
    using confl by (cases S) auto
  have T'[unfolded T_def, unfolded S]: \<open>remove_one_lit_from_wq (watched_by S L ! w)
           (st_l_of_wl (Some (L, w)) (M, N, U, None, NE, UE, Q, W)) =
           (M, N, U, None, NE, UE,
             remove1_mset (watched_by S L ! w) (clauses_to_update_wl (M, N, U, None, NE, UE, Q, W) L w),
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
    valid: \<open>valid_enqueued S''\<close>
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
    \<open>i \<equiv> (if get_clauses_wl S ! (watched_by S L ! w) ! 0 = L then 0 else 1)\<close>
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
        mset_append[symmetric] append_take_drop_id)
  have mset_watched_C: \<open>mset (watched_l C'') = {#watched_l C'' ! i, watched_l C'' ! (Suc 0 - i)#}\<close>
    using i_def watched_C' by (cases \<open>twl_clause_of (get_clauses_l S' ! C')\<close>) (auto simp: take_2_if)
  have two_le_length_C: \<open>2 \<le> length C''\<close>
    by (metis length_take linorder_not_le min_less_iff_conj numeral_2_eq_2 order_less_irrefl
        size_add_mset size_eq_0_iff_empty size_mset watched_C')
  have C_N_U: \<open>C' < length (get_clauses_l S')\<close>
    using WS add_inv by (auto simp: S twl_list_invs_def)
  obtain WS' where WS'_def: \<open>clauses_to_update_l S' = add_mset C' WS'\<close>
    using multi_member_split[OF WS] by (auto simp: S)
  have L: \<open>L \<in> set (watched_l C'')\<close>
    using valid S WL_w_in_drop by (auto simp: WS'_def)
  have C'_i[simp]: \<open>C''!i = L\<close>
    using L two_le_length_C S by (auto simp: take_2_if i_def split: if_splits)
  then have N_W_w_i_L[simp]: \<open>N ! (W L ! w) ! i = L\<close>
    by (auto simp: S)
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
    using WS'_def no_dup_queued by (simp add: S all_conj_distrib)
  from mset_le_add_mset_decr_left2[OF this] have uL_M: \<open>-L \<in> lits_of_l M\<close>
    using imageI[of _ \<open>set M\<close> lit_of] lits_of_l_convert_lits_l[of N M]
    by (auto simp: lits_of_def)
  have \<open>L \<in># all_lits_of_mm (mset `# mset (take U (tl N)) + NE)\<close>
    using alien uL_M
    by (auto simp: S cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        mset_take_mset_drop_mset in_all_lits_of_mm_ain_atms_of_iff)
  then have L_in_N_NE: \<open>L \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close>
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
        dest: in_set_takeD)
  then have \<open>mset (W L) = mset_set {x. Suc 0 \<le> x \<and> x < length N \<and> L \<in> set (watched_l (N ! x))}\<close>
    using corr_w by (auto simp: S correct_watching.simps clause_to_update_def)
  moreover have \<open>W L ! w \<in># mset (W L)\<close>
    using WL_w_in_drop by (auto dest: in_set_dropD)
  ultimately have zero_le_W_L_w: \<open>0 < W L ! w\<close> and W_L_w_le_N: \<open>W L ! w < length N\<close>
    by (auto simp: S correct_watching.simps clause_to_update_def)

  have ref:
    \<open>update_clause_wl L (watched_by S L ! w) w i f S
    \<le> \<Down> {((i, T'), T). T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T' \<and> i \<le> length (watched_by T' L)}
        (update_clause_l C' i f' T)\<close>
    if
      init_inv: \<open>unit_prop_body_wl_inv S w L\<close> and
      val_L'_not_Some_True: \<open>polarity (get_trail_wl S) (get_clauses_wl S ! (watched_by S L ! w) ! (1 - i)) \<noteq> Some True\<close> and
      f'_f: \<open>(Some f, Some f') \<in> ?find\<close> and
      ff': \<open>(f, f') \<in> nat_rel\<close> and
      \<open>f' < length (get_clauses_l T ! C')\<close> and
      C'_le_length: \<open>w < length (watched_by S L)\<close> and
      \<open>get_conflict_wl S = None\<close>
    for f f'
  proof -
    let ?K = \<open>N ! (W L ! w) ! f'\<close>
    have [simp]: \<open>f = f'\<close> \<open>f' < length (N ! (W L ! w))\<close>
      using ff' f'_f by (simp_all add: S)
    have C''_snd_f_unwatched: \<open>N ! C' ! f' \<in>#
       mset (unwatched_l (N ! C'))\<close>
      using f'_f by (auto simp: S in_set_drop_conv_nth)
    have [iff]: \<open>L \<noteq> N ! (W L ! w) ! f'\<close>
      using dist_C''
      apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
      apply (subst (asm) distinct_append)
      using f'_f C''_snd_f_unwatched uL_M n_d
      by (auto simp: S Decided_Propagated_in_iff_in_lits_of_l dest: no_dup_consistentD)
    have K_notin_watched: \<open>?K \<notin> set (watched_l (N ! (W L ! w)))\<close>
      using dist_C''
      apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
      apply (subst (asm) distinct_append)
      using f'_f C''_snd_f_unwatched
      by (auto simp: S)
    have snd_f'_ge_2: \<open>f' \<ge> 2\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>?K \<in> set (watched_l (N ! (W L ! w)))\<close>
        using two_le_length_C f'_f by (auto simp add: S take_set
            intro!: exI[of _ f'])
      then show False
        using K_notin_watched f'_f by (auto simp: S)
    qed
    have \<open>?L \<noteq> ?L'\<close>
      using dist_C'' two_le_length_C i_def
      apply (subst (asm) append_take_drop_id[of 2 \<open>C''\<close>, symmetric])
      apply (subst (asm) distinct_append)
      by (auto simp: S take_2_if split: if_splits)
    then have [simp]: \<open>L \<notin> set (watched_l (swap (N ! x) i f'))\<close> if \<open>W L ! w = x\<close> for x
      using f'_f C''_snd_f_unwatched snd_f'_ge_2  that f'_f
      by (auto simp: take_2_if i_def take_set S)
    have C'_N: \<open>W L ! w < length N\<close> \<open>0 < W L ! w\<close>
      using add_inv WL_w_in_drop by (auto simp: S twl_list_invs_def)
    have C'_N_indirect: \<open>x < length N\<close> \<open>0 < length N\<close> if \<open>W L ! w = x\<close> for x
      using that add_inv WL_w_in_drop by (auto simp: S twl_list_invs_def)
    have KK: \<open>Suc 0 \<le> W L ! w\<close>
      using add_inv WL_w_in_drop by (auto simp: S twl_list_invs_def)
    have [simp]: \<open>L \<in> set (watched_l (N ! (W L ! w)))\<close>
      using struct_invs valid WL_w_in_drop by (auto simp: S)
    have [simp]: \<open>N ! (W L ! w) ! f' \<in> set (watched_l (swap (N ! (W L ! w)) i f))\<close>
      using w_le snd_f'_ge_2 f'_f K_notin_watched
      by (auto simp: i_def swap_def take_2_if S split: nat.splits)
    have i_le_length_C'': \<open>i < length C''\<close>
      using two_le_length_C i_def S by auto

    have [simp]: \<open>set (watched_l (N ! (W L ! w))) = {?L, ?L'}\<close>
      using snd_f'_ge_2 two_le_length_C by (auto simp: take_2_if S i_def)
    have [simp]: \<open>N ! (W L ! w) ! j = N ! (W L ! w) ! k \<longleftrightarrow> j = k\<close>
      if \<open>j < length (N ! (W L ! w))\<close> and \<open>k < length (N ! (W L ! w))\<close>
      for j k
      using dist_C'' that by (auto simp: S distinct_conv_nth)

    have [simp]: \<open>Suc 0 - i < length (N ! (W L ! w))\<close> \<open>i < length (N ! (W L ! w))\<close> \<open>w < length (W L)\<close> \<open>W L \<noteq> []\<close>
      using init_inv unfolding unit_prop_body_wl_inv_def i_def unit_propagation_inner_loop_body_l_inv_def
      by (auto simp: S)
    have N_W_tl: \<open>N ! (W L ! w) \<in> set (tl N)\<close>
      by (metis C'_N(1) KK drop_0 drop_Suc in_set_drop_conv_nth)
    have T: \<open>T = (M, N, U, None, NE, UE, mset (drop (Suc w) (W L)), Q)\<close>
      using T_def unfolding S by auto
    have  WLx_length: \<open>(W L ! w = x \<longrightarrow> \<not> x < length N) \<equiv> W L ! w \<noteq> x\<close> for x
      using C'_N_indirect[of x] by auto
    have [simp]: \<open>{x. (y = x \<longrightarrow> P x) \<and> (y \<noteq> x \<longrightarrow> Q x)} =
         (if P y then insert y {x. Q x} else {x. x \<noteq>  y \<and> Q x})\<close>
      for y :: 'a and P Q :: \<open>'a \<Rightarrow> bool\<close>
      by auto
    have [simp]: \<open>{x. (y = x \<longrightarrow> \<not> P x) \<and> Q x \<and> P x \<and> R x} =
      {x. Q x \<and> P x \<and> R x} - {y}\<close> for P Q R y
      by auto
    have take_2_swap_i_f':
      \<open>set (watched_l (swap (N ! (W L ! w)) i f')) = {N ! (W L ! w) ! f', N ! (W L ! w) ! (1-i)}\<close>
      using two_le_length_C N_W_w_i_L snd_f'_ge_2 by (auto simp: take_2_if S i_def)
    let ?W = \<open>W
      (L := delete_index_and_swap (watched_by (M, N, U, None, NE, UE, Q, W) L) w,
       N ! (watched_by (M, N, U, None, NE, UE, Q, W) L ! w) ! f :=
         W (N ! (watched_by (M, N, U, None, NE, UE, Q, W) L ! w) ! f) @
         [watched_by (M, N, U, None, NE, UE, Q, W) L ! w])\<close>
    let ?N = \<open>N[watched_by (M, N, U, None, NE, UE, Q, W) L ! w :=
             swap (N ! (watched_by (M, N, U, None, NE, UE, Q, W) L ! w)) i f]\<close>
    have corr_w: \<open>correct_watching (M, ?N, U, None, NE, UE, Q, ?W)\<close>
      (is \<open>correct_watching ?S\<close>)
      unfolding correct_watching.simps Ball_def
    proof (intro allI conjI impI)
      fix x
      assume \<open>x \<in># all_lits_of_mm (mset `# mset (tl ?N) + NE)\<close>
      moreover have \<open>add_mset (mset (N ! (W L ! w))) (mset `# remove1_mset (N ! (W L ! w)) (mset (tl N)) + NE) =
        mset `# mset (tl N) + NE\<close>
        by (metis (no_types, lifting) N_W_tl image_mset_add_mset
            in_multiset_in_set insert_DiffM union_mset_add_mset_left)
      ultimately have  \<open>x \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close>
        using w_le KK i_le_length_C'' snd_f'_ge_2 C'_N
        by (auto simp add: S  mset_butlast_remove1_mset nth_list_update' swap_multiset
            mset_update nth_tl  tl_update_swap)
      then have Wx: \<open>mset (W x) = clause_to_update x (M, N, U, None, NE, UE, {#}, {#})\<close>
        using corr_w by (auto simp: S correct_watching.simps)

      have \<open>N ! (W L ! w) ! f' \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close>
        using KK  C'_N_indirect[OF refl]
        by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
            intro!: bexI[of _ \<open>N ! (W L ! w)\<close>] nth_in_set_tl)
      then have Wf': \<open>mset (W (N ! (W L ! w) ! f')) = clause_to_update (N ! (W L ! w) ! f') (M, N, U, None, NE, UE, {#}, {#})\<close>
        using corr_w by (auto simp: S correct_watching.simps)

      show \<open>mset (?W x) = clause_to_update x (M, ?N, U, None, NE, UE, {#}, {#})\<close>
      proof (cases \<open>x = L\<close>)
        case True
        moreover have
          \<open>remove1_mset (W L ! w) (mset_set {x. Suc 0 \<le> x \<and> x < length N \<and> L \<in> set (watched_l (N ! x))}) =
          mset_set ({x. Suc 0 \<le> x \<and> x < length N \<and> L \<in> set (watched_l (N ! x))} - {W L ! w})\<close>
          using C'_N_indirect[OF refl] KK  by (auto simp: S mset_set_Diff)
        ultimately show ?thesis
          using Wx
          by (auto simp add: S clause_to_update_def mset_butlast_remove1_mset nth_list_update'
              last_list_update_to_last mset_update tl_update_swap)
      next
        case [simp]: False
        show ?thesis
          using w_le KK i_le_length_C'' snd_f'_ge_2
            KK corr_w C'_N_indirect[OF refl]
          by (auto simp add: S clause_to_update_def mset_butlast_remove1_mset nth_list_update'
              Wf' WLx_length Wx take_2_swap_i_f' mset_set.insert_remove tl_update_swap
              mset_set_mset_set_minus_id_iff mset_set_eq_mset_set_more_conds
              intro!: mset_set.remove)
      qed
    qed
    show ?thesis
      unfolding update_clause_wl_def update_clause_l_def S Let_def T
      apply clarify
      apply (rule RETURN_refine)
      apply clarify
      apply (intro conjI)
      subgoal using f'_f w_le T_def by (simp add: S)
      subgoal by (rule corr_w)
      subgoal using w_le by (auto simp: S simp del: \<open>w < length (W L)\<close>)
      done
  qed

  have f': \<open>(f, f') \<in> \<langle>Id\<rangle>option_rel\<close>
    if \<open>f = f'\<close> for f f'
    using that by auto
  have i_alt_def: \<open>i = (if get_clauses_l T ! C' ! 0 = L then 0 else 1)\<close>
    by (cases S, cases T) (auto simp: i_def)

  have [simp]: \<open>set (watched_l (N[W L ! w := swap (N ! (W L ! w)) 0 (Suc 0 - i)] ! x)) = set (watched_l (N ! x))\<close> for x
    using i_alt_def C''_def two_le_length_C
    by (auto simp: nth_list_update' swap_def take_2_if S split: if_splits)
  have \<open>mset (swap (N ! (W L ! w)) 0 (Suc 0 - i)) = mset (N ! (W L ! w))\<close>
    apply (rule swap_multiset)
    using i_alt_def C''_def two_le_length_C
    by (auto simp: nth_list_update' take_2_if S mset_update split: if_splits)
  moreover {
    have \<open>tl N ! (W L ! w - Suc 0) = N ! (W L ! w)\<close>
      using C_N_U zero_le_W_L_w
      by (auto simp: S nth_tl)
    then have \<open>map mset (tl N)[W L ! w - Suc 0 := mset (N ! (W L ! w))] = map mset (tl N)\<close>
      using list_update_id[of \<open>map mset (tl N)\<close> \<open>W L ! w - Suc 0\<close>] C''_def two_le_length_C W_L_w_le_N
        zero_le_W_L_w
      by (auto simp del: list_update_id simp: nth_tl S map_tl[symmetric] W_L_w_le_N) }
  ultimately have [simp]: \<open>mset `# mset (tl (N[W L ! w := swap (N ! (W L ! w)) 0 (Suc 0 - i)])) = mset `# mset (tl N)\<close>
    using zero_le_W_L_w w_le by (auto simp: tl_update_swap S image_mset_mset_update)
  show \<open>mset `# mset (
             (tl (get_clauses_wl S[watched_by S L ! w :=
                  swap (get_clauses_wl S ! (watched_by S L ! w)) 0
                        (1 - (if ((get_clauses_wl S)!(watched_by S L ! w)) ! 0 = L then 0 else 1))]))) =
     mset `# mset ((tl (get_clauses_wl S)))\<close>
    unfolding i_def[symmetric] by (auto simp: S)
  have 1: \<open>unit_propagation_inner_loop_body_wl L w S
    \<le> \<Down> {((i, T'), T).
          T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T' \<and>
          i \<le> length (watched_by T' L)}
        (unit_propagation_inner_loop_body_l L C' T)\<close>
    (is \<open>_ \<le> \<Down> ?unit _\<close>)
    using w_le confl corr_w
    unfolding unit_propagation_inner_loop_body_wl_def unit_propagation_inner_loop_body_l_def
    supply [[goals_limit=1]]
    apply (refine_vcg val f f' ref; remove_dummy_vars)
    unfolding i_def[symmetric] i_alt_def[symmetric]
    subgoal using assms S zero_le_W_L_w C_N_U L_in_N_NE unfolding unit_prop_body_wl_inv_def
      by (auto simp: get_unit_init_clss_def)
    subgoal by (auto simp: S)
    subgoal using L_in_N_NE zero_le_W_L_w
      by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def correct_watching.simps S
          intro!: nth_in_set_tl
          intro!: bexI[of _ \<open>N ! (W L ! w)\<close>])
    subgoal using zero_le_W_L_w watched_C'
        by (auto simp add: S unit_prop_body_wl_find_unwatched_inv_def)
    subgoal by (simp add: S)
    subgoal by (simp add: S)
    subgoal by (auto simp add: clause_to_update_def correct_watching.simps set_conflict_wl_def S
       set_conflict_l_def)
    subgoal by (simp add: clause_to_update_def correct_watching.simps propagate_lit_wl_def S
       propagate_lit_l_def)
    subgoal by (rule ref) assumption
    done

  have \<open>unit_propagation_inner_loop_body_wl L w S \<le>
     \<Down> {((i, T'), T). (T = st_l_of_wl (Some (L, i)) T' \<and> correct_watching T' \<and>
              i \<le> length (watched_by T' L)) \<and>
         (twl_list_invs T \<and> twl_stgy_invs (twl_st_of (Some L) T) \<and>
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
      have H:
        \<open>{(T', T). twl_st_of (Some L) T' = T \<and> twl_list_invs T' \<and>
            twl_stgy_invs (twl_st_of (Some L) T') \<and> twl_struct_invs (twl_st_of (Some L) T')} =
        {(S, S''). twl_st_of (Some L) S = S'' \<and> twl_list_invs S \<and> twl_stgy_invs S'' \<and>
            twl_struct_invs S''}\<close>
        by auto
      show ?thesis
        unfolding remove_one_lit_from_wq_def C'_def[symmetric] S'_def[symmetric] H
        by (rule unit_propagation_inner_loop_body_l[of C' S' L])
          (use struct_invs stgy_inv add_inv WL_w_in_drop in \<open>auto simp: S\<close>)
    qed
    subgoal using 1 by auto
    subgoal
      by (rule unit_propagation_inner_loop_body(2))
       (use struct_invs stgy_inv add_inv WL_w_in_drop in \<open>auto simp: S\<close>)
     done
   then show ?propa
     apply -
     apply match_Down
     by force
qed


definition unit_propagation_inner_loop_wl_loop :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(w, S). twl_struct_invs (twl_st_of_wl (Some (L, w)) S) \<and>
        twl_stgy_invs (twl_st_of_wl (Some (L, w)) S) \<and>
         twl_list_invs (st_l_of_wl (Some (L, w)) S) \<and>
        correct_watching S \<and> w \<le> length (watched_by S L)\<^esup>
      (\<lambda>(w, S). w < length (watched_by S L) \<and> get_conflict_wl S = None)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl L w S
      })
      (0, S\<^sub>0)
  }
  \<close>

definition unit_propagation_inner_loop_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
     wS \<leftarrow> unit_propagation_inner_loop_wl_loop L S\<^sub>0;
     RETURN (snd wS)
  }\<close>


lemma unit_propagation_inner_loop_wl_spec:
  shows \<open>(uncurry unit_propagation_inner_loop_wl, uncurry unit_propagation_inner_loop_l) \<in>
    {((L', T'::'v twl_st_wl), (L, T::'v twl_st_l)). L = L' \<and> st_l_of_wl (Some (L, 0)) T' = T \<and>
      correct_watching T' \<and>
      twl_struct_invs
         (twl_st_of (Some L) (st_l_of_wl None
            (set_literals_to_update_wl (add_mset L (literals_to_update_wl T')) T'))) \<and>
      twl_stgy_invs
        (twl_st_of (Some L) (st_l_of_wl None
          (set_literals_to_update_wl (add_mset L (literals_to_update_wl T')) T'))) \<and>
      get_conflict_wl T' = None \<and>
      twl_list_invs
       (st_l_of_wl None (set_literals_to_update_wl (add_mset L (literals_to_update_wl T')) T'))} \<rightarrow>
    \<langle>{(T', T). st_l_of_wl None T' = T \<and>
        twl_struct_invs (twl_st_of_wl None T') \<and>
        twl_stgy_invs (twl_st_of_wl None T') \<and>
        twl_list_invs T \<and>
        correct_watching T'}\<rangle> nres_rel
    \<close> (is \<open>?fg \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close> is \<open>?fg \<in> ?A \<rightarrow> \<langle>{(T', T). ?f T' = T \<and> ?P T T'}\<rangle>nres_rel\<close>)
proof -
  {
    fix L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close>
    let ?S = \<open>twl_st_of (Some L) (st_l_of_wl None
        (set_literals_to_update_wl (add_mset L (literals_to_update_wl S)) S))\<close>
    assume corr_w: \<open>correct_watching S\<close> and
      struct_invs: \<open>twl_struct_invs ?S\<close> and
      stgy_invs: \<open>twl_stgy_invs ?S\<close> and
      add_invs: \<open>twl_list_invs (st_l_of_wl None (set_literals_to_update_wl (add_mset L (literals_to_update_wl S)) S))\<close>
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
          twl_struct_invs (twl_st_of_wl (Some (L, i)) T') \<and>
          twl_stgy_invs (twl_st_of_wl (Some (L, i)) T') \<and>
          twl_list_invs T \<and>
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
      \<open>twl_list_invs (st_l_of_wl (Some (L, i)) T')\<close>
      for i T'
      unfolding unit_propagation_body_wl_loop_fantom_def
      apply (refine_rcg watched_by_select_from_clauses_to_update)
      using that
        apply (auto intro!: unit_propagation_inner_loop_body_wl_spec
          simp del: twl_st_of_wl.simps)
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
                        twl_list_invs T \<and> correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>])
      subgoal using corr_w struct_invs by auto
      subgoal by auto
      subgoal by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T' by auto
      subgoal for i'T' T i' T'
        by (cases T')
          (solves \<open>auto simp del: entailed_clss_inv.simps valid_enqueued.simps split: if_splits\<close>)+
      subgoal for i'T' T i' T'
        apply (rule order_trans)
        by (rule unit_propagation_body_wl_loop_fantom; simp; fail) (auto intro!: H
          simp del: twl_st_of_wl.simps)
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
    done
  moreover have \<open>unit_propagation_inner_loop_l_fantom = unit_propagation_inner_loop_l\<close>
    by (intro ext) (auto simp: unit_propagation_inner_loop_l_fantom_def)
  ultimately show ?thesis
    by fast
qed


subsubsection \<open>Outer loop\<close>

definition select_and_remove_from_literals_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> 'v literal) nres\<close> where
  \<open>select_and_remove_from_literals_to_update_wl S = SPEC(\<lambda>(S', L). L \<in># literals_to_update_wl S \<and>
     S' = set_literals_to_update_wl (literals_to_update_wl S - {#L#}) S)\<close>

definition unit_propagation_outer_loop_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      correct_watching S \<and> twl_list_invs (st_l_of_wl None S)\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S'))));
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
       twl_list_invs (st_l_of_wl None T')} \<rightarrow>
    \<langle>{(T', T).
       st_l_of_wl None T' = T \<and>
       twl_struct_invs (twl_st_of_wl None T') \<and>
       twl_stgy_invs (twl_st_of_wl None T') \<and>
       twl_list_invs T \<and>
       literals_to_update_wl T' = {#} \<and>
       no_step cdcl_twl_cp (twl_st_of None T) \<and>
       correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?u \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have select_and_remove_from_literals_to_update_wl: \<open>select_and_remove_from_literals_to_update_wl S' \<le>
     \<Down> {((T', L'), (T, L)). L = L' \<and> T = st_l_of_wl (Some (L, 0)) T' \<and>
         T' = set_literals_to_update_wl (literals_to_update_wl S' - {#L#}) S' \<and> L \<in># literals_to_update_wl S' \<and>
         L \<in># all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S')))
       }
       (select_and_remove_from_literals_to_update S)\<close>
    if S: \<open>S = st_l_of_wl None S'\<close> and \<open>get_conflict_wl S' = None\<close> and
      corr_w: \<open>correct_watching S'\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S')\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
  proof -
    obtain M N U D NE UE W Q where
      S': \<open>S' = (M, N, U, D, NE, UE, Q, W)\<close>
      by (cases S') auto
    have
      no_dup_q: \<open>no_duplicate_queued (twl_st_of None (st_l_of_wl None S'))\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S')))\<close>
      using struct_invs that by (auto simp: twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
    then have H1: \<open>L \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close> if LQ: \<open>L \<in># Q\<close> for L
    proof -
      obtain K where \<open>L = - lit_of K\<close> and \<open>K \<in># mset (convert_lits_l N M)\<close>
        using that no_dup_q LQ
        by (auto simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          all_lits_of_mm_def atms_of_ms_def)
      then have \<open>atm_of L \<in> atm_of ` lits_of_l M\<close>
        by (auto simp: convert_lits_l_def lits_of_def)
      moreover {
        have \<open>atm_of ` lits_of_l M \<subseteq> (\<Union>x\<in>set (take U (tl N)). atm_of ` set (watched_l x) \<union>
           atm_of ` set (unwatched_l x)) \<union> (\<Union>x\<in>set_mset NE. atms_of x)\<close>
          using that alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
          by (auto simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              all_lits_of_mm_def atms_of_ms_def)
        then have \<open>atm_of ` lits_of_l M \<subseteq> (\<Union>x\<in>set (take U (tl N)). atm_of ` set x) \<union>
           (\<Union>x\<in>set_mset NE. atms_of x)\<close>
          unfolding image_Un[symmetric]
            set_append[symmetric]
            append_take_drop_id
            .
          then have \<open>atm_of ` lits_of_l M \<subseteq> atms_of_mm (mset `# mset (tl N) + NE)\<close>
            by (smt UN_Un Un_iff append_take_drop_id atms_of_ms_def atms_of_ms_mset_unfold set_append
                set_image_mset set_mset_mset set_mset_union subset_eq)
          }
      ultimately have \<open>atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NE)\<close>
        using that by blast
      then show ?thesis
        using that by (auto simp: in_all_lits_of_mm_ain_atms_of_iff)
    qed
    then have H: \<open>clause_to_update L S = mset (W L)\<close> if \<open>L \<in># Q\<close> for L
      using corr_w that S by (auto simp: correct_watching.simps S' clause_to_update_def)
    have m: \<open>mset `# mset (take U (tl N)) + NE + (mset `# mset (drop (Suc U) N) + UE) =
              mset `# mset (tl N) + NE + UE\<close>
      apply (subst (2) append_take_drop_id[symmetric, of \<open>tl N\<close> U])
      unfolding mset_append by (auto simp: drop_Suc)
    show ?thesis
      unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
      apply (rule RES_refine)
      using that S' by (auto 5 5 simp: literals_to_update_wl_literals_to_update_l_iff correct_watching.simps clauses_def
          mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state m all_lits_of_mm_union
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
       twl_list_invs T \<and>
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
            confl_cands_enqueued.simps valid_enqueued.simps no_duplicate_queued.simps
            twl_st_exception_inv.simps entailed_clss_inv.simps
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
          get_conflict_twl_st_of_wl literals_to_update_twl_st_of_st_l_of_wl get_conflict_l_st_l_of_wl; fail)
      apply (simp add: twl_struct_invs_def)
      done
    done

  have H: \<open>unit_propagation_outer_loop_wl S' \<le> \<Down> ?B (unit_propagation_outer_loop_l S)\<close>
    if A: \<open>(S', S) \<in> ?A\<close>
    for S S'
  proof -
    have A': \<open>(S, twl_st_of None S) \<in> {(S, S'). S' = twl_st_of None S \<and>
     twl_struct_invs (twl_st_of None S) \<and>  twl_stgy_invs (twl_st_of None S) \<and>
      twl_list_invs S \<and> clauses_to_update_l S = {#} \<and> get_conflict_l S = None}\<close>
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
  \<open>find_unassigned_lit_wl = (\<lambda>(M, N, U, D, NE, UE, WS, Q).
     SPEC (\<lambda>L.
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)) + NE)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)) + NE))))
     )\<close>

definition decide_wl_or_skip_pre where
\<open>decide_wl_or_skip_pre S \<longleftrightarrow>
   decide_l_or_skip_pre (st_l_of_wl None S)
  \<close>

definition decide_lit_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>decide_lit_wl = (\<lambda>L' (M, N, U, D, NE, UE, Q, W).
      (Decided L' # M, N, U, D, NE, UE, {#- L'#}, W))\<close>


definition decide_wl_or_skip :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>decide_wl_or_skip S = (do {
    ASSERT(decide_wl_or_skip_pre S);
    L \<leftarrow> find_unassigned_lit_wl S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> RETURN (False, decide_lit_wl L S)
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
          twl_list_invs (st_l_of_wl None T')} \<rightarrow>
        \<langle>{((b', T'), (b, T)). b' = b \<and>
          st_l_of_wl None T' = T \<and>
          correct_watching T'}\<rangle>nres_rel\<close>
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S'
    \<le> \<Down> Id
        (find_unassigned_lit_l S)\<close>
    if \<open>S = st_l_of_wl None S'\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that
    by (cases S') (auto simp: find_unassigned_lit_wl_def find_unassigned_lit_l_def
        mset_take_mset_drop_mset')
  have option: \<open>(x, x') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>x = x'\<close> for x x'
    using that by (auto)
  show ?thesis
    unfolding decide_wl_or_skip_def decide_l_or_skip_def
    apply (refine_vcg find_unassigned_lit_wl option)
    subgoal unfolding decide_wl_or_skip_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S S'
      by (cases S) (auto simp: correct_watching.simps clause_to_update_def
          decide_lit_l_def decide_lit_wl_def)
    done
qed


subsubsection \<open>Skip or Resolve\<close>

definition tl_state_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>tl_state_wl = (\<lambda>(M, N, U, D, NE, UE, WS, Q). (tl M, N, U, D, NE, UE, WS, Q))\<close>

definition resolve_cls_wl' :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v clause\<close> where
\<open>resolve_cls_wl' S C L  =
   remove1_mset (-L) (the (get_conflict_wl S)) \<union># (mset (tl (get_clauses_wl S!C)))\<close>

definition update_confl_tl_wl :: \<open>nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl\<close> where
  \<open>update_confl_tl_wl = (\<lambda>C L (M, N, U, D, NE, UE, WS, Q).
     let D = resolve_cls_wl' (M, N, U, D, NE, UE, WS, Q) C L in
        (False, (tl M, N, U, Some D, NE, UE, WS, Q)))\<close>

abbreviation skip_and_resolve_loop_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>skip_and_resolve_loop_wl_inv S\<^sub>0 brk S\<equiv>
     skip_and_resolve_loop_inv_l (st_l_of_wl None S\<^sub>0) brk (st_l_of_wl None S) \<and>
        correct_watching S\<close>

definition skip_and_resolve_loop_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>skip_and_resolve_loop_wl S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_wl_inv S\<^sub>0 brk S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          do {
            let D' = the (get_conflict_wl S);
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S));
            if -L \<notin># D' then
              do {RETURN (False, tl_state_wl S)}
            else
              if get_maximum_level (get_trail_wl S) (remove1_mset (-L) D') = count_decided (get_trail_wl S)
              then
                do {RETURN (update_confl_tl_wl C L S)}
              else
                do {RETURN (True, S)}
          }
        )
        (False, S\<^sub>0);
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
          twl_list_invs (st_l_of_wl None T') \<and>
          0 < count_decided (get_trail_wl T')} \<rightarrow>
      \<langle>{(T', T).
          st_l_of_wl None T' = T \<and>
          twl_struct_invs (twl_st_of_wl None T') \<and>
          twl_stgy_invs (twl_st_of_wl None T') \<and>
          twl_list_invs T \<and>
          no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) \<and>
          no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) \<and>
          literals_to_update_wl T' = {#} \<and>
          get_conflict_wl T' \<noteq> None \<and>
          correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?s \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have get_conflict_wl: \<open>((False, S'), False, S)
    \<in> Id \<times>\<^sub>r {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<close>
    if \<open>S = st_l_of_wl None S'\<close> and \<open>correct_watching S'\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that by (cases S') auto
  have [simp]: \<open>st_l_of_wl None (tl_state_wl S) = tl_state_l (st_l_of_wl None S)\<close> for S
    by (cases S) (auto simp: tl_state_wl_def tl_state_l_def)
  have [simp]: \<open>correct_watching (tl_state_wl S) = correct_watching S\<close> for S
    by (cases S) (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have [simp]: \<open>correct_watching  (tl aa, ba, ca, da, ea, fa, ha, h) \<longleftrightarrow>
    correct_watching (aa, ba, ca, None, ea, fa, ha, h)\<close>
    for aa ba ca L da ea fa ha h
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have [simp]: \<open>NO_MATCH None da \<Longrightarrow> correct_watching  (aa, ba, ca, da, ea, fa, ha, h) \<longleftrightarrow>
    correct_watching (aa, ba, ca, None, ea, fa, ha, h)\<close>
    for aa ba ca L da ea fa ha h
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have update_confl_tl_wl: \<open>
    (brkT, brkT') \<in> bool_rel \<times>\<^sub>f {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'} \<Longrightarrow>
    case brkT' of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S' brk S \<Longrightarrow>
    brkT' = (brk', T') \<Longrightarrow>
    brkT = (brk, T) \<Longrightarrow>
    lit_and_ann_of_propagated (hd (get_trail_l T')) = (L', C') \<Longrightarrow>
    lit_and_ann_of_propagated (hd (get_trail_wl T)) = (L, C) \<Longrightarrow>
    (update_confl_tl_wl C L T, update_confl_tl_l C' L' T') \<in> bool_rel \<times>\<^sub>f {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<close>
    for T' brkT brk brkT' brk' T C C' L L' S'
    unfolding update_confl_tl_wl_def update_confl_tl_l_def resolve_cls_wl'_def resolve_cls_l'_def
    by (cases T; cases T')
     (auto simp: Let_def)
  have [simp]:
    \<open>get_trail_l (st_l_of_wl None S) = get_trail_wl S\<close>
    \<open>get_conflict_l (st_l_of_wl None S) = get_conflict_wl S\<close> for S
    by (cases S; auto)+

  have H: \<open>?s \<in> ?A \<rightarrow> \<langle>{(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<rangle>nres_rel\<close>
    unfolding skip_and_resolve_loop_wl_def skip_and_resolve_loop_l_def
    apply (refine_rcg get_conflict_wl)
    subgoal by (auto simp add: get_conflict_l_st_l_of_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S b'T' bT b' T' by (cases T') (auto simp: correct_watching.simps)
    subgoal for S' S b'T' bT b' T' by (cases T') (auto simp: correct_watching.simps)
    subgoal by (auto simp: get_conflict_l_st_l_of_wl get_trail_l_st_l_of_wl)
    subgoal by (auto simp: get_trail_l_st_l_of_wl )
    subgoal by (auto simp: get_conflict_l_st_l_of_wl get_trail_l_st_l_of_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule update_confl_tl_wl) assumption+
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    done

  have skip_and_resolve_loop_wl:
    \<open>skip_and_resolve_loop_wl x \<le> \<Down> ?B (skip_and_resolve_loop_l y)\<close>
    if A: \<open>(x, y) \<in> ?A\<close> for x :: \<open>'v twl_st_wl\<close> and y :: \<open>'v twl_st_l\<close>
  proof -
    have A': \<open>(y, twl_st_of None y)
    \<in> {(S, S'). S' = twl_st_of None S \<and>
                 twl_struct_invs (twl_st_of None S) \<and>
                 twl_stgy_invs (twl_st_of None S) \<and> twl_list_invs S \<and>
                 clauses_to_update_l S = {#} \<and>
                 literals_to_update_l S = {#} \<and> get_conflict (twl_st_of None S) \<noteq> None \<and>
                 0 < count_decided (get_trail_l S)}\<close>
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

definition find_decomp_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl  nres\<close> where
  \<open>find_decomp_wl =  (\<lambda>L (M, N, U, D, NE, UE, Q, W).
    SPEC(\<lambda>S. \<exists>K M2 M1. S = (M1, N, U, D, NE, UE, Q, W) \<and> (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

definition find_lit_of_max_level_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres\<close> where
  \<open>find_lit_of_max_level_wl =  (\<lambda>(M, N, U, D, NE, UE, Q, W) L.
    SPEC(\<lambda>L'. L' \<in># remove1_mset (-L) (the D) \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>


fun extract_shorter_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>extract_shorter_conflict_wl (M, N, U, D, NE, UE, Q, W) = SPEC(\<lambda>S.
     \<exists>D'. D' \<subseteq># the D \<and> S = (M, N, U, Some D', NE, UE, Q, W) \<and>
     clause `# twl_clause_of `# mset (tl N) + NE + UE \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')\<close>

declare extract_shorter_conflict_wl.simps[simp del]
lemmas extract_shorter_conflict_wl_def = extract_shorter_conflict_wl.simps


definition backtrack_wl_inv where
  \<open>backtrack_wl_inv S \<longleftrightarrow> backtrack_l_inv (st_l_of_wl None S) \<and> correct_watching S
  \<close>

definition propagate_bt_wl :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_bt_wl = (\<lambda>L L' (M, N, U, D, NE, UE, Q, W). do {
    D'' \<leftarrow> list_of_mset (the D);
    RETURN (Propagated (-L) (length N) # M,
        N @ [[-L, L'] @ (remove1 (-L) (remove1 L' D''))], U,
          None, NE, UE, {#L#}, W(-L:= W (-L) @ [length N], L':= W L' @ [length N]))
      })\<close>

definition propagate_unit_bt_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>propagate_unit_bt_wl = (\<lambda>L (M, N, U, D, NE, UE, Q, W).
    (Propagated (-L) 0 # M, N, U, None, NE, add_mset (the D) UE, {#L#}, W))\<close>

definition backtrack_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>backtrack_wl S =
    do {
      ASSERT(backtrack_wl_inv S);
      let L = lit_of (hd (get_trail_wl S));
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propagate_bt_wl L L' S
      }
      else do {
        RETURN (propagate_unit_bt_wl L S)
     }
  }\<close>


lemma correct_watching_learn:
  assumes N_ne_Nil: \<open>N \<noteq> []\<close> and
    L1: \<open>atm_of L1 \<in> atms_of_mm (mset `# mset (tl N) + NE)\<close> and
    L2: \<open>atm_of L2 \<in> atms_of_mm (mset `# mset (tl N) + NE)\<close> and
    UW: \<open>atms_of (mset UW) \<subseteq> atms_of_mm (mset `# mset (tl N) + NE)\<close>
  shows
  \<open>correct_watching (K # M, N @ [[L1 , L2] @ UW],
    U, D, NE, UE, Q, W (L1 := W L1 @ [length N], L2 := W L2 @ [length N])) \<longleftrightarrow>
  correct_watching (M, N, U, D, NE, UE, Q, W)\<close> (is \<open>?l \<longleftrightarrow> ?c\<close>)
proof (rule iffI)
  assume corr: ?l
  have H: \<open>\<And>x. x \<in># all_lits_of_mm (mset `# mset (tl (N @ [L1 # L2 # UW]))) +
              all_lits_of_mm NE \<longrightarrow>
        mset ((W(L1 := W L1 @ [length N], L2 := W L2 @ [length N])) x) =
        clause_to_update x
         (K # M, N @ [L1 # L2 # UW], U, D, NE, UE, {#}, {#})\<close>
    using corr
    by (auto simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset if_distrib[of mset]
        uminus_lit_swap correct_watching.simps all_lits_of_mm_union Ball_def
        all_conj_distrib)
  have [simp]: \<open>{x. (P x \<longrightarrow> Q x) \<and> P x} = {x. Q x \<and> P x}\<close> for P Q :: \<open>'a \<Rightarrow> bool\<close>
    by auto
  have [simp]: \<open>mset (W x) = clause_to_update x (M, N, U, D, NE, UE, {#}, {#})\<close>
    if \<open>x \<in># all_lits_of_mm NE\<close>
    for x
    using that H[of x]
    by (auto split: if_splits simp: clause_to_update_def nth_append
        intro!: arg_cong[of _ _ mset_set])
  have [simp]: \<open>mset (W x) = clause_to_update x (M, N, U, D, NE, UE, {#}, {#})\<close>
    if \<open>x \<in># all_lits_of_mm (mset `# mset (tl N))\<close>
    for x
    using that H[of x]
    by (auto split: if_splits simp: clause_to_update_def nth_append
        all_lits_of_mm_add_mset all_lits_of_m_add_mset
        intro!: arg_cong[of _ _ mset_set]) \<comment> \<open>slow but auto magic\<close>
  show ?c
    unfolding correct_watching.simps Ball_def
    by (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset
        all_conj_distrib all_lits_of_mm_union)
next
  assume corr: ?c
  have [simp]: \<open>{x. (P x \<longrightarrow> Q x) \<and> P x} = {x. Q x \<and> P x}\<close> for P Q :: \<open>'a \<Rightarrow> bool\<close>
    by auto
  have [simp]: \<open>clause_to_update L (K # M, N @ [L1 # L2 # UW], U, D, NE, UE, {#}, {#}) =
     clause_to_update L (M, N, U, D, NE, UE, {#}, {#}) +
     (if L = L1 \<or> L = L2 then {#length N#} else {#})\<close>
    for L
    using N_ne_Nil by (auto simp: clause_to_update_def nth_append
        intro: arg_cong[of _ _ mset_set])
  have \<open>L1 \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close> and
    \<open>-L1 \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close> and
    \<open>L2 \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close> and
    \<open>-L2 \<in># all_lits_of_mm (mset `# mset (tl N) + NE)\<close>
    using L1 L2 by (auto simp add: in_all_lits_of_mm_ain_atms_of_iff)
  then have [simp]:
    \<open>mset (W L1) = clause_to_update L1 (M, N, U, D, NE, UE, {#}, {#})\<close>
    \<open>mset (W (- L1)) = clause_to_update (- L1) (M, N, U, D, NE, UE, {#}, {#})\<close>
    \<open>mset (W L2) = clause_to_update L2 (M, N, U, D, NE, UE, {#}, {#})\<close>
    \<open>mset (W (- L2)) = clause_to_update (- L2) (M, N, U, D, NE, UE, {#}, {#})\<close>
    using corr by (auto simp: correct_watching.simps)
  have \<open>set_mset (all_lits_of_m (mset UW)) \<subseteq> set_mset (all_lits_of_mm (mset `# mset (tl N)+ NE))\<close>
    using UW using in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff by blast
  then show ?l
    using corr N_ne_Nil
    unfolding correct_watching.simps Ball_def
    by (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset
        all_conj_distrib all_lits_of_mm_union)
qed


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
          twl_list_invs (st_l_of_wl None T')} \<rightarrow>
        \<langle>{(T', T).
          st_l_of_wl None T' = T \<and>
          twl_struct_invs (twl_st_of_wl None T') \<and>
          twl_stgy_invs (twl_st_of_wl None T') \<and>
          twl_list_invs T \<and>
          get_conflict_wl T' = None \<and>
          literals_to_update_wl T' \<noteq> {#} \<and>
          correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?bt \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have hd_not_alien:
    \<open>atm_of (-lit_of (hd M')) \<in> atms_of_mm (mset `# mset (tl N') + NE')\<close>
    if
      st: \<open>((M', N', U', E', NE', UE', Q', W), S')
      \<in> {(T', T). st_l_of_wl None T' = T \<and>
                   correct_watching T' \<and>
                   twl_struct_invs (twl_st_of_wl None T') \<and>
                   twl_stgy_invs (twl_st_of_wl None T') \<and>
                   get_conflict_wl T' \<noteq> None \<and>
                   get_conflict_wl T' \<noteq> Some {#} \<and>
                   literals_to_update_wl T' = {#} \<and>
                   (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and>
                   (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and> twl_list_invs (st_l_of_wl None T')}\<close> and
      M'_empty: \<open>M' \<noteq> []\<close>

    for M N U E NE UE WS Q M' N' U' E' NE' UE' Q' W S'
  proof -
    have struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (M', N', U', E', NE', UE', Q', W))\<close>
      using st by auto
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M', N', U', E', NE', UE', Q', W)))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then show ?thesis
      using M'_empty unfolding  cdcl\<^sub>W_restart_mset.no_strange_atm_def
        by (cases M') (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
            mset_take_mset_drop_mset dest: in_atms_of_mset_takeD)
    qed

  have ref:
    \<open>((Propagated (- lit_of (hd M')) (length N') # L, N' @ [[- lit_of (hd M'), L'] @ remove1 (- lit_of (hd M')) (remove1 L' D'b)], U', None, NE', UE', unmark (hd M'), W
      (- lit_of (hd M') := W (- lit_of (hd M')) @ [length N'], L' := W L' @ [length N'])),
     (Propagated (- lit_of (hd M)) (length N) # M1a, N @ [[- lit_of (hd M), L'a] @ remove1 (- lit_of (hd M)) (remove1 L'a D'')], U, None, NE, UE, WS, unmark (hd M)))
    \<in> {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<close>
     (is \<open>(?U', ?V') \<in> {(T', T). ?conv T' = T \<and> correct_watching T'}\<close>)
     if
        S: \<open>((M', N', U', E', NE', UE', Q', W), M, N, U, E, NE, UE, WS, Q)
        \<in> {(T', T). st_l_of_wl None T' = T \<and>
                     correct_watching T' \<and>
                     twl_struct_invs (twl_st_of_wl None T') \<and>
                     twl_stgy_invs (twl_st_of_wl None T') \<and>
                     get_conflict_wl T' \<noteq> None \<and>
                     get_conflict_wl T' \<noteq> Some {#} \<and>
                     literals_to_update_wl T' = {#} \<and>
                     (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and>
                     (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None T')) S') \<and>
                     twl_list_invs (st_l_of_wl None T')}\<close>
        (is \<open>(?U, ?V) \<in> _\<close>)and
        M: \<open>(M''', M'''') \<in> {(D', D''). D' = D'' \<and>
               - lit_of (hd (get_trail_wl (M', N', U', E', NE', UE', Q', W))) \<in># D' \<and>
               D' \<subseteq># the (get_conflict_wl (M', N', U', E', NE', UE', Q', W))}\<close> and
        M''''_nempty: \<open>M'''' \<noteq> {#}\<close> and
        struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (M', N', U', E', NE', UE', Q', W))\<close> and
        L_M1a: \<open>(L, M1a) \<in> Id\<close> and
        size_M'''': \<open>1 < size M''''\<close> and
        L'_L'a: \<open>(L', L'a) \<in> {(L, L'). L = L' \<and> L \<in># the (Some M''')}\<close> and
        D'': \<open>(D'b, D'') \<in> {(E, F). E = F \<and> M''' = mset E}\<close> and
        atm_hd: \<open>atm_of (lit_of (hd M')) \<in> atms_of_mm (mset `# mset (tl N') + NE')\<close> and
        atm: \<open>atm_of L' \<in> atms_of_mm (mset `# mset (tl N') + NE')\<close>
     for M' N' U'  E' NE' UE' W Q' M N U E NE UE WS Q L M1a M''' M'''' L' L'a D'b D''
   proof -
     have conv: \<open>?conv ?U' = ?V'\<close> and corr: \<open>correct_watching ?U\<close>
       using S L_M1a L'_L'a M''''_nempty size_M'''' D'' by auto
     have add: \<open>twl_list_invs (st_l_of_wl None ?U)\<close>
       using S by auto
     have E': \<open>E' \<noteq> None\<close>
       using S by auto
     have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M', N', U', E', NE', UE', Q', W)))\<close>
       using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       by fast
     then have \<open>atms_of (the E') \<subseteq> atms_of_ms (mset ` set (take U' (tl N'))) \<union> atms_of_mm NE'\<close>
       using D'' E'
       by (cases E') (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          mset_take_mset_drop_mset)
     moreover have \<open>mset D'b \<subseteq># the E'\<close>
       using M D'' by auto
     ultimately have atms_D: \<open>atms_of (mset D'b) \<subseteq> atms_of_mm (mset `# mset (tl N') + NE')\<close>
       using atms_of_subset_mset_mono in_atms_of_mset_takeD by fastforce

     have corr: \<open>correct_watching ?U'\<close>
      apply (subst correct_watching_learn)
      subgoal using add by (auto simp: twl_list_invs_def)
      subgoal using atm_hd by simp
      subgoal using atm .
      subgoal using atms_D by (fastforce dest: in_atms_of_minusD)
      subgoal using corr by (auto simp add: correct_watching.simps clause_to_update_def)
      done
    show ?thesis
      using corr conv by blast
  qed

  have extract_shorter_conflict_wl: \<open>extract_shorter_conflict_wl S'
    \<le> \<Down> {(U'::'v twl_st_wl, U).
          st_l_of_wl None U' = U \<and> equality_except_conflict U' S' \<and>
          the (get_conflict_wl U') \<subseteq># the (get_conflict_wl S') \<and>
          get_conflict_wl U' \<noteq> None} (extract_shorter_conflict_l S)\<close>
    (is \<open>_ \<le> \<Down> ?extract _\<close>)
    if  \<open>(S', S) \<in> ?A\<close>
    for S' S L
    using that
    by (cases S'; cases S)
       (auto simp: extract_shorter_conflict_wl_def extract_shorter_conflict_l_def mset_take_mset_drop_mset
        intro!: RES_refine)

  have find_decomp_wl: \<open>find_decomp_wl L T'
    \<le> \<Down> {(U'::'v twl_st_wl, U).
          st_l_of_wl None U' = U \<and> equality_except_trail U' T' \<and>
       (\<exists>M. get_trail_wl T' = M @ get_trail_wl U') } (find_decomp L' T)\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    if \<open>(S', S) \<in> ?A\<close> \<open>L = L'\<close> \<open>(T', T) \<in> ?extract S'\<close>
    for S' S T T' L L'
    using that
    apply (cases T; cases T')
    apply (auto intro!: RES_refine simp add: find_decomp_wl_def find_decomp_def)
    apply blast
    apply (auto dest!: get_all_ann_decomposition_exists_prepend)
    done

  have find_lit_of_max_level_wl: \<open>find_lit_of_max_level_wl T' L'
    \<le> \<Down> {(L', L). L = L' \<and> L' \<in># the (get_conflict_wl T')}
         (find_lit_of_max_level T L)\<close>
    (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if \<open>L = L'\<close> \<open>(T', T) \<in> ?find S'\<close>
    for S' S T T' L L'
    using that
    apply (cases T; cases T')
    apply (auto intro!: RES_refine simp add: find_lit_of_max_level_wl_def find_lit_of_max_level_def
     dest: in_diffD)
    done

  have propagate_bt_wl: \<open>propagate_bt_wl (lit_of (hd (get_trail_wl S'))) L' U'
    \<le> \<Down> {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}
        (propagate_bt_l (lit_of (hd (get_trail_l S))) L U)\<close>
    (is \<open>_ \<le> \<Down> ?propa _\<close>)
    if  SS': \<open>(S', S) \<in> ?A\<close> and
     UU': \<open>(U', U) \<in> ?find T'\<close> and
     LL': \<open>(L', L) \<in> ?find_lit U'\<close> and
     TT': \<open>(T', T) \<in> ?extract S'\<close> and
    bt: \<open>backtrack_wl_inv S'\<close>
    for S' S T T' L L' U U'
  proof -
    define K' where \<open>K' = lit_of (hd (get_trail_l S))\<close>
    obtain MS NS US DS NES UES W where
      S': \<open>S' = (MS, NS, US, Some DS, NES, UES, {#}, W)\<close>
      using SS' by (cases S'; cases \<open>get_conflict_wl S'\<close>) auto
    then obtain DT where
      T': \<open>T' = (MS, NS, US, Some DT, NES, UES, {#}, W)\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU MU' where
      U': \<open>U' = (MU, NS, US, Some DT, NES, UES, {#}, W)\<close> and
      MU: \<open>MS = MU' @ MU\<close> and
      U: \<open>U = st_l_of_wl None U'\<close>
      using UU' by (cases U') auto
    have NS: \<open>NS \<noteq> []\<close>
      using SS' by (auto simp: S' twl_list_invs_def)
    have MS: \<open>MS \<noteq> []\<close>
      using bt unfolding backtrack_wl_inv_def backtrack_l_inv_def S' by auto
    have \<open>correct_watching S'\<close>
      using SS' by fast
    then have corr: \<open>correct_watching (MU, NS, US, None, NES, UES, unmark (hd MS), W)\<close>
       unfolding S' correct_watching.simps clause_to_update_def get_clauses_l.simps .

    have no_alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S'))\<close>
      using SS' unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    moreover have \<open>L' \<in># DS\<close>
      using LL' TT'  by (auto simp: T' S' U' mset_take_mset_drop_mset)
    ultimately have
       atm_L': \<open>atm_of L' \<in> atms_of_mm (mset `# mset (tl NS) + NES)\<close> and
       atm_confl: \<open>\<forall>L\<in>#DS. atm_of L \<in> atms_of_mm (mset `# mset (tl NS) + NES)\<close>
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state S'
          mset_take_mset_drop_mset dest!: atm_of_lit_in_atms_of in_atms_of_mset_takeD)
    show ?thesis
      unfolding propagate_bt_wl_def propagate_bt_l_def S' T' U' U st_l_of_wl.simps get_trail_wl.simps
      list_of_mset_def K'_def[symmetric]
      apply clarify
      apply (refine_rcg ref)
      apply (clarify)
      apply (intro conjI)
      subgoal using LL' SS' by (auto simp: S' K'_def)
      subgoal
        apply (subst correct_watching_learn)
        subgoal using NS .
        subgoal using SS'[unfolded S'] MS by (rule hd_not_alien)
        subgoal using atm_L' .
        subgoal using atm_confl TT' by (fastforce simp: S' T' dest!: in_atms_of_minusD)
        subgoal by (rule corr)
      done
      done
  qed

  have propagate_unit_bt_wl: \<open>(propagate_unit_bt_wl (lit_of (hd (get_trail_wl S'))) U',
     propagate_unit_bt_l (lit_of (hd (get_trail_l S))) U)
    \<in> {(T', T). st_l_of_wl None T' = T \<and> correct_watching T'} \<close>
    (is \<open>(_, _) \<in> ?propagate_unit_bt_wl _\<close>)
    if
     SS': \<open>(S', S) \<in> ?A\<close> and
     TT': \<open>(T', T) \<in> ?extract S'\<close> and
     UU': \<open>(U', U) \<in> ?find T'\<close>
    for S' S T T' L L' U U' K'
  proof -
    obtain MS NS US DS NES UES W where
      S': \<open>S' = (MS, NS, US, Some DS, NES, UES, {#}, W)\<close>
      using SS' by (cases S'; cases \<open>get_conflict_wl S'\<close>) auto
    then obtain DT where
      T': \<open>T' = (MS, NS, US, Some DT, NES, UES, {#}, W)\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    have T: \<open>T = (MS, NS, US, Some DT, NES, UES, {#}, {#})\<close>
      using TT' by (auto simp: T')
    obtain MU MU' where
      U': \<open>U' = (MU, NS, US, Some DT, NES, UES, {#}, W)\<close> and
      MU: \<open>MS = MU' @ MU\<close> and
      U: \<open>U = st_l_of_wl None U'\<close>
      using UU' T' by (cases U') auto
    have U: \<open>U = (MU, NS, US, Some DT, NES, UES, {#}, {#})\<close>
      using UU' by (auto simp: U')

    have \<open>correct_watching S'\<close>
      using SS' by fast
    then have corr: \<open>correct_watching (Propagated (- lit_of (hd MS)) 0 # MU, NS, US, None, NES,
      add_mset (the (Some DT)) UES, unmark (hd MS), W)\<close>
       unfolding S' correct_watching.simps clause_to_update_def get_clauses_l.simps .

    show ?thesis
      unfolding propagate_unit_bt_wl_def propagate_unit_bt_l_def S' T' U U'
        st_l_of_wl.simps get_trail_wl.simps list_of_mset_def
      apply clarify
      apply (refine_rcg)
      subgoal using SS' by (auto simp: S')
      subgoal by (rule corr)
      done
  qed

  have H: \<open>?bt \<in> ?A \<rightarrow> \<langle>{(T', T). st_l_of_wl None T' = T \<and> correct_watching T'}\<rangle>nres_rel\<close>
    unfolding backtrack_wl_def backtrack_l_def
    apply (refine_vcg find_decomp_wl find_lit_of_max_level_wl extract_shorter_conflict_wl;
        remove_dummy_vars)
    subgoal unfolding backtrack_wl_inv_def by auto
    subgoal by (auto simp: get_trail_l_st_l_of_wl)
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal by (auto simp: get_trail_l_st_l_of_wl)
    subgoal by (rule propagate_bt_wl ) assumption+
    subgoal by (rule propagate_unit_bt_wl) assumption+
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
                 twl_list_invs S \<and>
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

definition cdcl_twl_o_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>cdcl_twl_o_prog_wl S =
    do {
      ASSERT(twl_struct_invs (twl_st_of_wl None S));
      ASSERT(twl_stgy_invs (twl_st_of_wl None S));
      ASSERT(twl_list_invs (st_l_of_wl None S));
      do {
        if get_conflict_wl S = None
        then decide_wl_or_skip S
        else do {
          if count_decided (get_trail_wl S) > 0
          then do {
            T \<leftarrow> skip_and_resolve_loop_wl S;
            ASSERT(get_conflict_wl T \<noteq> None \<and> get_conflict_wl T \<noteq> Some {#});
            U \<leftarrow> backtrack_wl T;
            RETURN (False, U)
          }
          else do {RETURN (True, S)}
        }
      }
    }
  \<close>


lemma cdcl_twl_o_prog_wl_spec:
  \<open>(cdcl_twl_o_prog_wl, cdcl_twl_o_prog_l) \<in> {(S::'v twl_st_wl, S'::'v twl_st_l).
     S' = st_l_of_wl None S \<and>
     literals_to_update_wl S = {#} \<and>
     (\<forall>S'. \<not> cdcl_twl_cp (twl_st_of_wl None S) S') \<and>
     twl_struct_invs (twl_st_of_wl None S) \<and>
     twl_stgy_invs (twl_st_of_wl None S) \<and>
     twl_list_invs (st_l_of_wl None S) \<and>
     correct_watching S} \<rightarrow>
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     T' = st_l_of_wl None T \<and>
     brk = brk' \<and>
     twl_list_invs (st_l_of_wl None T) \<and>
     (get_conflict_wl T \<noteq> None \<longrightarrow> count_decided (get_trail_wl T) = 0) \<and>
     twl_struct_invs (twl_st_of_wl None T) \<and>
     twl_stgy_invs (twl_st_of_wl None T) \<and>
     correct_watching T}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S \<le> \<Down> Id (find_unassigned_lit_l S')\<close>
    if \<open>S' = st_l_of_wl None S\<close>
    for S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
    unfolding find_unassigned_lit_wl_def find_unassigned_lit_l_def that
    by (cases S) auto
  have [iff]: \<open>correct_watching (decide_lit_wl L S) \<longleftrightarrow> correct_watching S\<close> for L S
    by (cases S; auto simp: decide_lit_wl_def correct_watching.simps clause_to_update_def)
  have [iff]: \<open>decide_lit_l L (st_l_of_wl None S) =
    st_l_of_wl None (decide_lit_wl L S)\<close> for L S
    by (cases S; auto simp: decide_lit_wl_def decide_lit_l_def)
  have option_id: \<open>x = x' \<Longrightarrow> (x,x') \<in> \<langle>Id\<rangle>option_rel\<close> for x x' by auto
  have [simp]: \<open>get_trail_l (st_l_of_wl None S) = get_trail_wl S\<close> for S
    by (cases S) auto
  have cdcl_o: \<open>?o \<in> ?A \<rightarrow>
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     T' = st_l_of_wl None T \<and>
     brk = brk' \<and>
     correct_watching T}\<rangle>nres_rel\<close>
    unfolding cdcl_twl_o_prog_wl_def cdcl_twl_o_prog_l_def decide_wl_or_skip_def
      decide_l_or_skip_def
    apply (refine_vcg skip_and_resolve_loop_wl_spec["to_\<Down>"] backtrack_wl_spec["to_\<Down>"]
      find_unassigned_lit_wl option_id)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal unfolding decide_wl_or_skip_pre_def by auto
    subgoal by auto
    subgoal by (auto simp: )
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal by auto
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
      twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and> twl_list_invs S}\<close>
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
      unfolding SS' set_Collect_Pair_to_fst_snd
      apply -
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

abbreviation cdcl_twl_stgy_prog_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl  \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_prog_wl_inv S\<^sub>0 \<equiv> \<lambda>(brk, T). twl_struct_invs (twl_st_of_wl None T) \<and>
        twl_stgy_invs (twl_st_of_wl None T) \<and>
        (brk \<longrightarrow> final_twl_state (twl_st_of_wl None T)) \<and>
        cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of_wl None S\<^sub>0) (twl_st_of_wl None T) \<and>
        (\<not>brk \<longrightarrow> get_conflict_wl T = None)\<close>

definition cdcl_twl_stgy_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_stgy_prog_wl S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_prog_wl_inv S\<^sub>0\<^esup>
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
       twl_list_invs (st_l_of_wl None S) \<and>
       correct_watching S} \<rightarrow>
    \<langle>{(S, S'). S' = st_l_of_wl None S }\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S'), False, S) \<in> {((brk', T'), (brk, T)). brk = brk' \<and> T = st_l_of_wl None T' \<and>
       correct_watching T' \<and> twl_list_invs (st_l_of_wl None T')}\<close>
    if \<open>S = st_l_of_wl None S'\<close> and \<open>correct_watching S'\<close> and \<open>twl_list_invs (st_l_of_wl None S')\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_def cdcl_twl_stgy_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec["to_\<Down>"])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' by auto
    subgoal by auto
    subgoal by (auto simp: get_conflict_l_st_l_of_wl)
    subgoal by auto
    subgoal by auto
    subgoal by (rule cdcl_twl_o_prog_wl_spec["to_\<Down>", THEN order_trans])
        (auto intro!: conc_fun_R_mono)
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_wl_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S = None\<close> and \<open>twl_list_invs (st_l_of_wl None S)\<close> and
    \<open>correct_watching S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le>
      \<Down> {(S, S'). S' = st_l_of_wl None S}
        (SPEC(\<lambda>T. cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of_wl None S) (twl_st_of None T) \<and>
            final_twl_state (twl_st_of None T)))\<close>
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

end
