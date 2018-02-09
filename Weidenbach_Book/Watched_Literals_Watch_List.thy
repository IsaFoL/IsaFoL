theory Watched_Literals_Watch_List
  imports Watched_Literals_List
begin
no_notation Ref.update ("_ := _" 62)
section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>

type_synonym clauses_to_update_wl = \<open>nat multiset\<close>
type_synonym watched = \<open>nat list\<close>
type_synonym 'v lit_queue_wl = \<open>'v literal multiset\<close>

type_synonym 'v twl_st_wl =
  \<open>('v, nat) ann_lits \<times> 'v clauses_l \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl \<times>
    ('v literal \<Rightarrow> watched)\<close>

subsection \<open>Access Functions\<close>

fun clauses_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> clauses_to_update_wl\<close> where
  \<open>clauses_to_update_wl (_, _, _, _, _, _, W) L i = mset (drop i (W L))\<close>

fun get_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_wl (M, _, _, _, _, _, _) = M\<close>

fun literals_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v lit_queue_wl\<close> where
  \<open>literals_to_update_wl (_, _, _, _, _, Q, _) = Q\<close>

fun set_literals_to_update_wl :: \<open>'v lit_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_literals_to_update_wl Q (M, N, D, NE, UE, _, W) = (M, N, D, NE, UE, Q, W)\<close>

fun get_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_wl (_, _, D, _, _, _, _) = D\<close>

fun get_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_wl (M, N, D, NE, UE, WS, Q) = N\<close>

fun get_unit_learned :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned (M, N, D, NE, UE, Q, W)  = UE\<close>

fun get_unit_init_clss :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clss (M, N, D, NE, UE, Q, W) =  NE\<close>

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
  \<open>correct_watching (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + NE).
       mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

declare correct_watching.simps[simp del]

fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> watched\<close> where
  \<open>watched_by (M, N, D, NE, UE, Q, W) L = W L\<close>

fun update_watched :: \<open>'v literal \<Rightarrow> watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, D, NE, UE, Q, W) = (M, N, D, NE, UE, Q, W(L:= WL))\<close>

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
  \<open>st_l_of_wl None (M, N, D, NE, UE, Q, W) = (M, N, D, NE, UE, {#}, Q)\<close>
| \<open>st_l_of_wl (Some (L, j)) (M, N, D, NE, UE, Q, W) =
    (M, N, D, NE, UE, (if D \<noteq> None then {#} else clauses_to_update_wl (M, N, D, NE, UE, Q, W) L j,
      Q))\<close>

definition state_wl_l :: \<open>('v literal \<times> nat) option \<Rightarrow> ('v twl_st_wl \<times> 'v twl_st_l) set\<close> where
\<open>state_wl_l L = {(T, T'). T' = st_l_of_wl L T \<and> finite (dom (get_clauses_wl T))}\<close>

fun twl_st_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> ('v twl_st_wl \<times> 'v twl_st) set\<close> where
  \<open>twl_st_of_wl L = state_wl_l L O twl_st_l (map_option fst L)\<close>

fun remove_one_lit_from_wq :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>remove_one_lit_from_wq L (M, N, D, NE, UE, WS, Q) = (M, N, D, NE, UE, remove1_mset L WS, Q)\<close>

named_theorems twl_st_wl \<open>Conversions from \<^typ>\<open>'v twl_st_l\<close> to \<^typ>\<open>'v twl_st_wl\<close>\<close>

lemma [twl_st_wl]:
  assumes \<open>(S, T) \<in> state_wl_l L\<close>
  shows
    \<open>get_trail_l T = get_trail_wl S\<close> and
    \<open>get_clauses_l T = get_clauses_wl S\<close> and
    \<open>get_conflict_l T = get_conflict_wl S\<close> and
    \<open>L = None \<Longrightarrow> clauses_to_update_l T = {#}\<close>
    \<open>L \<noteq> None \<Longrightarrow> get_conflict_wl S \<noteq> None \<Longrightarrow> clauses_to_update_l T = {#}\<close>
    \<open>L \<noteq> None \<Longrightarrow> get_conflict_wl S = None \<Longrightarrow> clauses_to_update_l T =
       clauses_to_update_wl S (fst (the L)) (snd (the L))\<close> and
    \<open>literals_to_update_l T = literals_to_update_wl S\<close>
  using assms unfolding state_wl_l_def all_clss_lf_ran_m[symmetric]
  by (cases S; cases T; cases L; auto split: option.splits simp: trail.simps; fail)+

lemma ge_length_watched_by_empty_iff[twl_st_wl]:
  \<open>clauses_to_update_wl S L i = {#} \<longleftrightarrow> i \<ge> length (watched_by S L)\<close>
  by (cases S) auto

lemma remove_one_lit_from_wq_def:
  \<open>remove_one_lit_from_wq L S = set_clauses_to_update_l (clauses_to_update_l S - {#L#}) S\<close>
  by (cases S) auto

lemma correct_watching_set_literals_to_update[simp]:
  \<open>correct_watching (set_literals_to_update_wl WS T') = correct_watching T'\<close>
  by (cases T') (auto simp: correct_watching.simps)

lemma get_conflict_wl_set_literals_to_update_wl:
  \<open>get_conflict_wl (set_literals_to_update_wl P S) = get_conflict_wl S\<close>
  by (cases S) auto

lemma [twl_st_l]:
  \<open>get_clauses_l (remove_one_lit_from_wq L S) = get_clauses_l S\<close>
  \<open>get_trail_l (remove_one_lit_from_wq L S) = get_trail_l S\<close>
  by (cases S; auto; fail)+

declare twl_st_l[simp]

text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>.\<close>
declare twl_st_wl[simp]

definition unit_prop_body_wl_inv where
\<open>unit_prop_body_wl_inv T i L \<longleftrightarrow>
    (\<exists>T'. (T, T') \<in> state_wl_l (Some (L, i)) \<and>
    unit_propagation_inner_loop_body_l_inv L (watched_by T L ! i)
       (remove_one_lit_from_wq (watched_by T L ! i) T')\<and>
    L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T) + get_unit_init_clss T) \<and>
    correct_watching T \<and>
    i < length (watched_by T L) \<and>
    get_conflict_wl T = None
(*     twl_struct_invs (twl_st_of_wl (Some (L, i)) T') \<and>
    twl_stgy_invs (twl_st_of_wl (Some (L, i)) T') \<and>
    twl_list_invs (st_l_of_wl (Some (L, i)) T')
    get_conflict_wl T' = None \<and>
    (watched_by T' L) ! i > 0 \<and>
    i < length (watched_by T' L) \<and>
    watched_by T' L ! i < length (get_clauses_wl T') *)
    )
  \<close>


definition set_conflict_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl = (\<lambda>C (M, N, D, NE, UE, Q, W). (M, N, Some (mset C), NE, UE, {#}, W))\<close>

definition propagate_lit_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>propagate_lit_wl = (\<lambda>L' C i (M, N,  D, NE, UE, Q, W).
      let N = N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)) in
      (Propagated L' C # M, N, D, NE, UE, add_mset (-L') Q, W))\<close>

definition update_clause_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>update_clause_wl = (\<lambda>(L::'v literal) C w i f (M, N,  D, NE, UE, Q, W). do {
     let K' = (N\<propto>C) ! f;
     let N' = N(C \<hookrightarrow> swap (N \<propto> C) i f);
     RETURN (w, (M, N', D, NE, UE, Q,
         W(L := delete_index_and_swap (watched_by (M, N, D, NE, UE, Q, W) L) w, K':= W K' @ [C])))

  })\<close>

definition unit_prop_body_wl_find_unwatched_inv where
\<open>unit_prop_body_wl_find_unwatched_inv f C S \<longleftrightarrow>
   get_clauses_wl S \<propto> C \<noteq> [] \<and>
   (f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S \<propto> C)). - L \<in> lits_of_l (get_trail_wl S)))\<close>

definition unit_propagation_inner_loop_body_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl L w S = do {
      ASSERT(unit_prop_body_wl_inv S w L);
      let C = (watched_by S L) ! w;
      let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
      let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
      let val_L' = polarity (get_trail_wl S) L';
      if val_L' = Some True
      then RETURN (w+1, S)
      else do {
        f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto>C);
        ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
        case f of
          None \<Rightarrow>
            if val_L' = Some False
            then do {RETURN (w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)}
            else do {RETURN (w+1, propagate_lit_wl L' C i S)}
        | Some f \<Rightarrow> do {
            update_clause_wl L C w i f S
          }
      }
   }\<close>


text \<open>TODO Move\<close>
lemma no_duplicate_queued_alt_def:
   \<open>no_duplicate_queued S =
    ((\<forall>C C'. C \<in># clauses_to_update S \<longrightarrow> C' \<in># clauses_to_update S \<longrightarrow> fst C = fst C') \<and>
     (\<forall>C. C \<in># clauses_to_update S \<longrightarrow> add_mset (fst C) (literals_to_update S) \<subseteq># uminus `# lit_of `# mset (get_trail S)) \<and>
     literals_to_update S \<subseteq># uminus `# lit_of `# mset (get_trail S))\<close>
  by (cases S) auto

declare clauses_to_update_l_set_clauses_to_update_l[twl_st_l]

lemma [twl_st_l]: \<open>get_conflict_l (set_clauses_to_update_l W S) = get_conflict_l S\<close>
  by (cases S) auto

lemma  [twl_st_l]: \<open>get_conflict_l (remove_one_lit_from_wq L S) = get_conflict_l S\<close>
  by (cases S) auto

lemma [twl_st_l]: \<open>literals_to_update_l (set_clauses_to_update_l Cs S) = literals_to_update_l S\<close>
  by (cases S) auto

lemma [twl_st_l]: \<open>get_unit_clauses_l (set_clauses_to_update_l Cs S) = get_unit_clauses_l S\<close>
  by (cases S) auto

lemma  [twl_st_l]: \<open>get_unit_clauses_l (remove_one_lit_from_wq L S) = get_unit_clauses_l S\<close>
  by (cases S) auto

lemma init_clss_state_to_l[twl_st_l]: \<open>(S, S') \<in> twl_st_l L \<Longrightarrow>
  init_clss (state\<^sub>W_of S') = mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses_l S\<close>
  by (cases S) (auto simp: twl_st_l_def init_clss.simps mset_take_mset_drop_mset')

text \<open>TODO get_unit_init_clss must be renamed\<close>
lemma get_unit_init_clauses_l_get_unit_init_clss[twl_st_wl]: \<open>(S, S') \<in> state_wl_l L \<Longrightarrow>
  get_unit_init_clauses_l S' = get_unit_init_clss S\<close>
  by (cases S; cases L) (auto simp: state_wl_l_def)


lemma [twl_st_l]:
  \<open>get_unit_init_clauses_l (set_clauses_to_update_l Cs S) = get_unit_init_clauses_l S\<close>
  by (cases S) auto

lemma [twl_st_l]:
  \<open>get_unit_init_clauses_l (remove_one_lit_from_wq L S) = get_unit_init_clauses_l S\<close>
  by (cases S) auto

lemma unit_init_clauses_get_unit_init_clauses_l[twl_st_l]:
  \<open>(S, T) \<in> twl_st_l L \<Longrightarrow> unit_init_clauses T = get_unit_init_clauses_l S\<close>
  by (cases S) (auto simp: twl_st_l_def init_clss.simps)

lemma clauses_state_to_l[twl_st_l]: \<open>(S, S') \<in> twl_st_l L \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of S') = mset `# ran_mf (get_clauses_l S) +
     get_unit_init_clauses_l S + get_unit_learned_clauses_l S\<close>
  by (cases S) (auto simp: twl_st_l_def init_clss.simps mset_take_mset_drop_mset')

text \<open>END Move\<close>


subsection \<open>The Functions\<close>

subsubsection \<open>Inner Loop\<close>

lemma clause_to_update_mapsto_upd_If:
  assumes
    i: \<open>i \<in> dom N\<close> and
    \<open>finite (dom N)\<close>
  shows
  \<open>clause_to_update L (M, N(i \<hookrightarrow> C'), C, NE, UE, WS, Q) =
    (if L \<in> set (watched_l C')
     then add_mset i (remove1_mset i (clause_to_update L (M, N, C, NE, UE, WS, Q)))
     else remove1_mset i (clause_to_update L (M, N, C, NE, UE, WS, Q)))\<close>
proof -
  define D' where \<open>D' = mset_set (dom N - {i})\<close>
  then have [simp]: \<open>mset_set (dom N) = add_mset i D'\<close>
    using assms by (simp add: mset_set.remove)
  have [simp]: \<open>mset_set (insert i (dom N)) = add_mset i D'\<close>
    using assms unfolding D'_def by (auto simp: mset_set.insert_remove)
  have [simp]: \<open>i \<notin># D'\<close>
    using assms unfolding D'_def by auto

  have \<open>{#C \<in># D'.
     (C = i \<longrightarrow> L \<in> set (watched_l C')) \<and>
     (C \<noteq> i \<longrightarrow> L \<in> set (watched_l (N \<propto> C)))#} =
    {#C \<in># D'. L \<in> set (watched_l (N \<propto> C))#}\<close>
    by (rule filter_mset_cong2) auto
  then show ?thesis
    unfolding clause_to_update_def
    by auto
qed

text \<open>TODO: Move\<close>
lemma mset_butlast_update_last[simp]:
  \<open>w < length xs \<Longrightarrow> mset (butlast (xs[w := last (xs)])) = remove1_mset (xs ! w) (mset xs)\<close>
  by (simp add: last_list_update_to_last mset_butlast_remove1_mset mset_update)

lemma
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close> and L :: \<open>'v literal\<close> and w :: nat
  defines
    [simp]: \<open>T \<equiv> remove_one_lit_from_wq (watched_by S L ! w) S'\<close> and
    (* [simp]: \<open>S'' \<equiv> twl_st_of_wl (Some (L, w)) S\<close> and *)
    [simp]: \<open>C' \<equiv> watched_by S L ! w\<close>
  defines
    [simp]: \<open>C'' \<equiv> get_clauses_l S' \<propto> C'\<close>
  assumes
    S_S': \<open>(S, S') \<in> state_wl_l (Some (L, w))\<close> and
    w_le: \<open>w < length (watched_by S L)\<close> and
    corr_w: \<open>correct_watching S\<close>
  shows  unit_propagation_inner_loop_body_wl_spec: \<open>unit_propagation_inner_loop_body_wl L w S \<le>
   \<Down> {((i, T'), T).
        (T', T) \<in> state_wl_l (Some (L, i)) \<and>
        correct_watching T' \<and>
        i \<le> length (watched_by T' L)}
     (unit_propagation_inner_loop_body_l L C' T)\<close> (is \<open>?propa\<close>)and
    unit_propagation_inner_loop_body_wl_update:
      \<open>unit_propagation_inner_loop_body_l_inv L C' T \<Longrightarrow>
         mset `# (ran_mf ((get_clauses_wl S)((watched_by S L ! w)\<hookrightarrow>
                     (swap (get_clauses_wl S \<propto> (watched_by S L ! w)) 0
                           (1 - (if (get_clauses_wl S)\<propto>(watched_by S L ! w) ! 0 = L then 0 else 1)))))) =
        mset `# (ran_mf (get_clauses_wl S))\<close> (is \<open>_ \<Longrightarrow> ?eq\<close>)
proof -
  have fin: \<open>finite (dom (get_clauses_wl S))\<close>
    using S_S' unfolding state_wl_l_def by blast
  have val: \<open>(polarity a b, polarity a' b') \<in> Id\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' :: \<open>('a, 'b) ann_lits\<close> and b b' :: \<open>'a literal\<close>
    by (auto simp: that)
  let ?M = \<open>get_trail_wl S\<close>
  have f: \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto> (watched_by S L ! w))
      \<le> \<Down> {(found, found'). found = found' \<and>
             (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l C''). -L \<in> lits_of_l ?M)) \<and>
             (\<forall>j. found = Some j \<longrightarrow> (j < length C'' \<and> (undefined_lit ?M (C''!j) \<or> C''!j \<in> lits_of_l ?M) \<and> j \<ge> 2))
           }
            (find_unwatched_l (get_trail_l T) (get_clauses_l T \<propto> C'))\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    using S_S' by (auto simp: find_unwatched_l_def intro!: RES_refine)

  define i :: nat where
    \<open>i \<equiv> (if get_clauses_wl S \<propto> (watched_by S L ! w) ! 0 = L then 0 else 1)\<close>
  have
    l_wl_inv: \<open>unit_prop_body_wl_inv S w L\<close> (is ?inv) and
    clause_ge_0: \<open>0 < length (get_clauses_l T \<propto> C')\<close> (is ?ge) and
    L_def: \<open>defined_lit (get_trail_wl S) L\<close> \<open>-L \<in> lits_of_l (get_trail_wl S)\<close>
      \<open>L \<notin> lits_of_l (get_trail_wl S)\<close> (is ?L_def) and
    i_le: \<open>i < length (get_clauses_wl S \<propto> C')\<close>  (is ?i_le) and
    i_le2: \<open>1-i < length (get_clauses_wl S \<propto> C')\<close>  (is ?i_le2) and
    C'_dom: \<open>C' \<in> dom (get_clauses_l T)\<close> (is ?C'_dom) and
    L_watched: \<open>L \<in> set (watched_l (get_clauses_l T \<propto> C'))\<close> (is ?L_w) and
    dist_clss: \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
  if
    \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
  proof -
    have \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that unfolding unit_prop_body_wl_inv_def by fast+
    then obtain T' where
      T_T': \<open>(set_clauses_to_update_l (clauses_to_update_l T + {#C'#}) T, T') \<in> twl_st_l (Some L)\<close> and
      struct_invs: \<open>twl_struct_invs T'\<close> and
       \<open>twl_stgy_invs T'\<close> and
      C'_dom: \<open>C' \<in> dom (get_clauses_l T)\<close> and
       \<open>0 < C'\<close> and
       ge_0: \<open>0 < length (get_clauses_l T \<propto> C')\<close> and
       \<open>no_dup (get_trail_l T)\<close> and
       i_le: \<open>(if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)
         < length (get_clauses_l T \<propto> C')\<close> and
       i_le2: \<open>1 - (if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)
         < length (get_clauses_l T \<propto> C')\<close> and
       L_watched: \<open>L \<in> set (watched_l (get_clauses_l T \<propto> C'))\<close>
      unfolding unit_propagation_inner_loop_body_l_inv_def by blast
    show ?i_le and ?C'_dom and ?L_w and ?i_le2
      using S_S' i_le C'_dom L_watched i_le2 unfolding i_def by auto
    have
        alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T')\<close> and
        dup: \<open>no_duplicate_queued T'\<close> and
        lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T')\<close> and
        dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of T')\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by blast+
    have n_d: \<open>no_dup (trail (state\<^sub>W_of T'))\<close>
       using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
    have 1: \<open>C \<in># clauses_to_update T' \<Longrightarrow>
         add_mset (fst C) (literals_to_update T') \<subseteq>#
         uminus `# lit_of `# mset (get_trail T')\<close> for C
      using dup unfolding no_duplicate_queued_alt_def
      by blast
    have H: \<open>(L, twl_clause_of C'') \<in># clauses_to_update T'\<close>
      using twl_st_l(5)[OF T_T']
      by (auto simp: twl_st_l)
    have uL_M: \<open>-L \<in> lits_of_l (get_trail T')\<close>
      using mset_le_add_mset_decr_left2[OF 1[OF H]]
      by (auto simp: lits_of_def)
    then show \<open>defined_lit (get_trail_wl S) L\<close> \<open>-L \<in> lits_of_l (get_trail_wl S)\<close>
      \<open>L \<notin> lits_of_l (get_trail_wl S)\<close>
      using S_S' T_T' n_d by (auto simp: Decided_Propagated_in_iff_in_lits_of_l twl_st
        dest: no_dup_consistentD)
    have \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss S)\<close>
      using alien uL_M twl_st_l(1-8)[OF T_T'] S_S'
        init_clss_state_to_l[OF T_T']
        unit_init_clauses_get_unit_init_clauses_l[OF T_T']
      unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: in_all_lits_of_mm_ain_atms_of_iff twl_st_wl twl_st twl_st_l)
    then show ?inv
      using that assms unfolding unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def
      apply -
      apply (rule exI[of _ S'])
      by (auto simp: twl_st_wl twl_st twl_st_l)
    show ?ge
      by (rule ge_0)
    show \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
      using dist S_S' twl_st_l(1-8)[OF T_T'] T_T' unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def
      by (auto simp: twl_st_l twl_st twl_st_wl)
  qed

  have f': \<open>(f, f') \<in> \<langle>Id\<rangle>option_rel\<close>
    if \<open>f = f'\<close> for f f'
    using that by auto
  have ref:
    \<open>update_clause_wl L (watched_by S L ! w) w i f S
    \<le> \<Down> {((i, T'), T). (T', T) \<in> state_wl_l (Some (L, i)) \<and> correct_watching T' \<and>
            i \<le> length (watched_by T' L)}
        (update_clause_l C' i f' T)\<close>
    if
      init_inv: \<open>unit_prop_body_wl_inv S w L\<close> and
      init_inv': \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close> and
      val_L'_not_Some_True: \<open>polarity (get_trail_wl S) (get_clauses_wl S \<propto> (watched_by S L ! w) ! (1 - i)) \<noteq> Some True\<close> and
      f'_f: \<open>(Some f, Some f') \<in> ?find\<close> and
      ff': \<open>(f, f') \<in> nat_rel\<close> and
      \<open>f' < length (get_clauses_l T \<propto> C')\<close> and
      C'_le_length: \<open>w < length (watched_by S L)\<close>
    for f f'
  proof -
    obtain M N NE UE Q W where
      S: \<open>S = (M, N, None, NE, UE, Q, W)\<close>
      using init_inv unfolding unit_prop_body_wl_inv_def by (cases S) auto
    have [iff]: \<open>defined_lit M L\<close> \<open>L \<notin> lits_of_l M\<close>
      using L_def[OF init_inv'] unfolding S by auto
    have 1: \<open>\<not> length (W L) \<le> Suc w \<Longrightarrow>
        add_mset (last (W L)) (mset (butlast (drop (Suc w) (W L)))) =
         mset (drop (Suc w) (W L))\<close>
        by (metis List.last_in_set drop_eq_Nil insert_DiffM last_drop
           mset_butlast_remove1_mset not_less set_mset_mset)
    have [simp]: \<open>mset (drop w (butlast (W L[w := last (W L)]))) = mset (drop (Suc w) (W L))\<close>
      apply (subst butlast_list_update)
      subgoal using C'_le_length by (auto simp: S)
      subgoal
        using 1 by (auto simp: mset_butlast_remove1_mset[symmetric])
     done
    let ?N = \<open>N(W L ! w \<hookrightarrow> swap (N \<propto> (W L ! w)) i f')\<close>
    let ?W = \<open>W(L := butlast (W L[w := last (W L)]),
            N \<propto> (W L ! w) ! f' := W (N \<propto> (W L ! w) ! f') @ [W L ! w])\<close>
    have [simp]: \<open>mset (swap (N \<propto> (W L ! w)) i f') = mset (N \<propto> (W L ! w))\<close>
      apply (rule swap_multiset)
      using f'_f i_le[OF init_inv'] S_S' unfolding i_def[symmetric]
      by (auto simp: S)
    have [simp]: \<open>{#mset (fst x). x \<in># ran_m ?N#} = {#mset (fst x). x \<in># ran_m N#}\<close>
      apply (subst ran_m_clause_upd)
      subgoal using fin S_S' by (auto simp: S)
      subgoal using C'_dom[OF init_inv'] S_S' by (auto simp: S)
      subgoal using C'_dom[OF init_inv'] S_S' fin by (auto simp: image_mset_remove1_mset_if S
         ran_m_def)
      done
    have [simp]: \<open>W L ! w \<in> dom N\<close> \<open>w < length (W L)\<close> \<open>w \<le> length (W L) - Suc 0\<close>
      using C'_dom[OF init_inv'] S_S' w_le by (auto simp: S)
    have [simp]: \<open>L \<noteq>  N \<propto> (W L ! w) ! f'\<close>
      using f'_f S_S' by (auto simp: S)
    have [simp]: \<open>set (watched_l (N \<propto> (W L ! w))) =
        {N \<propto> (W L ! w) ! i, N \<propto> (W L ! w) ! (1 - i)}\<close>
       using clause_ge_0[OF init_inv'] S_S' i_le f'_f
       by (auto simp: swap_def S i_def take_2_if)
    have [simp]: \<open>set (watched_l (swap (N \<propto> (W L ! w)) i f')) =
        {N \<propto> (W L ! w) ! f', N \<propto> (W L ! w) ! (1 - i)}\<close>
       using clause_ge_0[OF init_inv'] S_S' i_le f'_f
       by (auto simp: swap_def S i_def take_2_if)
    have N_W_L[simp]: \<open>N \<propto> (W L ! w) ! i = L\<close>
      using L_watched[OF init_inv'] S_S' by (auto simp: take_2_if S i_def hd_conv_nth
         split: if_splits)
    have \<open>N \<propto> (W L ! w) \<in># ran_mf N\<close>
      using C'_dom[OF init_inv'] S_S' fin by (auto simp: S ran_m_def)
    then have dist: \<open>distinct (N \<propto> (W L ! w))\<close>
      using dist_clss[OF init_inv'] S_S'
      by (auto simp: S distinct_mset_set_def)
    have [simp]:
       \<open>N \<propto> (W L ! w) ! (Suc 0 - i) \<noteq> L\<close>
       \<open>N \<propto> (W L ! w) ! (Suc 0 - i) \<noteq> N \<propto> (W L ! w) ! f'\<close>
       \<open>N \<propto> (W L ! w) ! f' \<noteq> N \<propto> (W L ! w) ! (Suc 0 - i)\<close>
      apply (subst (2) N_W_L[symmetric])
      using i_le[OF init_inv'] f'_f S_S' dist
      by (auto simp: nth_eq_iff_index_eq S i_def simp del: N_W_L)
    have corr_W: \<open>correct_watching
          (M, N(W L ! w \<hookrightarrow> swap (N \<propto> (W L ! w)) i f'), None, NE, UE, Q, W
           (L := butlast (W L[w := last (W L)]),
            N \<propto> (W L ! w) ! f' := W (N \<propto> (W L ! w) ! f') @ [W L ! w]))\<close>
      using corr_w fin unfolding  S  correct_watching.simps (* clause_to_update_def*)
      by (auto simp: clause_to_update_mapsto_upd_If
        id_remove_1_mset_iff_notin
        remove_1_mset_id_iff_notin
        in_clause_to_update_iff)
    show ?thesis
      using S_S' ff' corr_W
      by (auto simp: S update_clause_wl_def update_clause_l_def Let_def state_wl_l_def
        Cons_nth_drop_Suc[symmetric])
  qed
  have other_watched_is_true: \<open>((w + 1, S), T)
    \<in> {((i, T'), T).
       (T', T) \<in> state_wl_l (Some (L, i)) \<and>
       correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>
    using S_S' w_le corr_w
    apply (cases S)
    by (auto simp: state_wl_l_def
        Cons_nth_drop_Suc[symmetric])
  have conflict: \<open>((w + 1, set_conflict_wl (get_clauses_wl S \<propto> (watched_by S L ! w)) S),
     set_conflict_l (get_clauses_l T \<propto> C') T)
    \<in> {((i, T'), T).
       (T', T) \<in> state_wl_l (Some (L, i)) \<and>
       correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>
    using S_S' w_le corr_w
    by (cases S)
       (auto simp: state_wl_l_def set_conflict_wl_def
        correct_watching.simps clause_to_update_def
        Cons_nth_drop_Suc[symmetric] set_conflict_l_def)
  have propa: \<open>((w + 1,
      propagate_lit_wl (get_clauses_wl S \<propto> (watched_by S L ! w) ! (1 - i))
       (watched_by S L ! w) i S),
     propagate_lit_l (get_clauses_l T \<propto> C' ! (1 - i)) C' i T)
    \<in> {((i, T'), T).
       (T', T) \<in> state_wl_l (Some (L, i)) \<and>
       correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>
    if inv: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
  proof -
    obtain M N NE UE Q W where
      S: \<open>S = (M, N, None, NE, UE, Q, W)\<close>
      using inv S_S' unfolding unit_propagation_inner_loop_body_l_inv_def
      by (cases S) (auto simp: twl_st_l)
    have \<open>mset (swap (N \<propto> C') 0 (Suc 0 - i)) = mset (N \<propto> C')\<close>
      using i_le[OF inv] i_le2[OF inv]
      by (auto simp: take_2_if i_def S)
    moreover have \<open>set (watched_l (swap (N \<propto> C') 0 (Suc 0 - i))) = set (watched_l (N \<propto> C'))\<close>
      using i_le[OF inv] i_le2[OF inv]
      by (auto simp: take_2_if swap_def i_def S)
    ultimately
       have \<open>correct_watching ((Propagated (get_clauses_wl S \<propto> (watched_by S L ! w) ! (1 - i))
             (watched_by S L ! w) #
            M,
            N(watched_by S L ! w \<hookrightarrow>
                    swap (N \<propto> (watched_by S L ! w)) 0 (Suc 0 - i)), None, NE, UE,
            add_mset (- get_clauses_wl S \<propto> (watched_by S L ! w) ! (1 - i)) Q,
            W))\<close>
      using S_S' w_le corr_w fin C'_dom[OF inv] corr_w
      unfolding propagate_lit_l_def propagate_lit_wl_def
      by (auto simp: state_wl_l_def propagate_lit_wl_def  S image_mset_remove1_mset_if
        Cons_nth_drop_Suc[symmetric] clause_to_update_mapsto_upd_If in_ran_m_iff_ran ran_def
      ran_m_mapsto_upd correct_watching.simps clause_to_update_def)
    then show ?thesis
      using S_S' w_le corr_w fin C'_dom[OF inv] corr_w
      unfolding propagate_lit_l_def propagate_lit_wl_def
      by (auto simp: state_wl_l_def propagate_lit_wl_def  S
        Cons_nth_drop_Suc[symmetric] clause_to_update_mapsto_upd_If ran_m_mapsto_upd)
  qed
  have i_def': \<open>i = (if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)\<close>
    using S_S' unfolding i_def by auto

  show 1: \<open>unit_propagation_inner_loop_body_wl L w S
    \<le> \<Down> {((i, T'), T).
          (T', T) \<in> state_wl_l (Some (L, i)) \<and> correct_watching T' \<and>
          i \<le> length (watched_by T' L)}
        (unit_propagation_inner_loop_body_l L C' T)\<close>
    (is \<open>_ \<le> \<Down> ?unit _\<close>)
    unfolding unit_propagation_inner_loop_body_wl_def unit_propagation_inner_loop_body_l_def
      i_def[symmetric] i_def'[symmetric]
    apply (rewrite at "let _ = watched_by _ _ ! _ in _" Let_def)
    unfolding i_def[symmetric]
    apply (rewrite at "let _ = _ in let _ = _ in _" Let_def)
    apply (rewrite at "let _ = _ in let _ = get_clauses_l _ \<propto> _ ! _ in _" Let_def)
    supply [[goals_limit=1]]
    apply (refine_vcg val f f' ref (*f f' ref*); remove_dummy_vars)
    subgoal by (rule l_wl_inv)
    subgoal using S_S' by auto
    subgoal by (rule other_watched_is_true)
    subgoal
      using clause_ge_0 S_S'
      by (auto simp add: unit_prop_body_wl_find_unwatched_inv_def)
    subgoal by auto
    subgoal using S_S' by auto
    subgoal by (rule conflict)
    subgoal by (rule propa)
    subgoal using S_S' w_le by auto
    done
  have [simp]: \<open>add_mset a (remove1_mset a M) = M \<longleftrightarrow> a \<in># M\<close> for a M
    by (metis ab_semigroup_add_class.add.commute add.left_neutral multi_self_add_other_not_self
       remove1_mset_eqE union_mset_add_mset_left)

  show ?eq if inv: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
    using i_le[OF inv] i_le2[OF inv] C'_dom[OF inv] fin S_S'
    unfolding i_def[symmetric]
    by (auto simp: ran_m_clause_upd image_mset_remove1_mset_if
      in_ran_m_iff_ran ran_def)
qed

definition unit_propagation_inner_loop_wl_loop_inv where
  \<open>unit_propagation_inner_loop_wl_loop_inv L = (\<lambda>(w, S).
    (\<exists>S'. (S, S') \<in> state_wl_l (Some (L, w)) \<and>
       unit_propagation_inner_loop_l_inv L S' \<and>
      correct_watching S \<and> w \<le> length (watched_by S L)))\<close>

definition unit_propagation_inner_loop_wl_loop :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
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
    {((L', T'::'v twl_st_wl), (L, T::'v twl_st_l)). L = L' \<and> (T', T) \<in> state_wl_l (Some (L, 0)) \<and>
      correct_watching T' (*\<and>
      get_conflict_wl T' = None*)} \<rightarrow>
    \<langle>{(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'}\<rangle> nres_rel
    \<close> (is \<open>?fg \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close> is \<open>?fg \<in> ?A \<rightarrow> \<langle>{(T', T). _ \<and> ?P T T'}\<rangle>nres_rel\<close>)
proof -
  {
    fix L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
    assume
      corr_w: \<open>correct_watching S\<close> and
      SS': \<open>(S, S') \<in> state_wl_l (Some (L, 0))\<close>
    text \<open>To ease the finding the correspondence between the body of the loops, we introduce
      following function:\<close>
    define unit_propagation_body_wl_loop_fantom where
      \<open>unit_propagation_body_wl_loop_fantom L w S = do {
        let C = watched_by S L! w;
        unit_propagation_inner_loop_body_wl L w S}\<close>
      for L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close> and w :: nat

    have unit_propagation_body_wl_loop_fantom: \<open>unit_propagation_inner_loop_body_wl L w S \<le> \<Down>Id
          (unit_propagation_body_wl_loop_fantom L w S)\<close>
      if \<open>w <  length (watched_by S L)\<close> for w and S :: \<open>'v twl_st_wl\<close>
      using that unfolding unit_propagation_body_wl_loop_fantom_def
      by auto
    have watched_by_select_from_clauses_to_update:
      \<open>RETURN (watched_by T L ! i)
        \<le> \<Down> {(C', (S, C)). C' = C \<and> S = remove_one_lit_from_wq (watched_by T L ! i) T'}
        (select_from_clauses_to_update T')\<close>
      if
        \<open>i < length (watched_by T L)\<close> and
        \<open>get_conflict_wl T = None\<close> and
        \<open>(T, T') \<in> state_wl_l (Some (L, i))\<close>
      for i :: nat and L :: \<open>'v literal\<close> and T :: \<open>'v twl_st_wl\<close> and T'
      unfolding select_from_clauses_to_update_def
      apply (rule RETURN_SPEC_refine)
      by (cases T) (use that in \<open>auto simp: in_set_drop_conv_nth remove_one_lit_from_wq_def\<close>)
    have H: \<open>unit_propagation_body_wl_loop_fantom L i T'
    \<le> \<Down> {((i, T'), T).
          (T', T) \<in> state_wl_l (Some (L, i)) \<and>
            correct_watching T' \<and> i \<le> length (watched_by T' L)}
        (do {
           (S', C) \<leftarrow>
             select_from_clauses_to_update T;
           unit_propagation_inner_loop_body_l L C S'
         })\<close>
      if \<open>i < length (watched_by T' L)\<close> and
      \<open>correct_watching T'\<close> and
        \<open>(T', T) \<in> state_wl_l (Some (L, i))\<close> and
        \<open>get_conflict_wl T' = None\<close>
      for i T T'
      unfolding unit_propagation_body_wl_loop_fantom_def
      apply (refine_rcg watched_by_select_from_clauses_to_update)
      using that
        apply (auto intro!: unit_propagation_inner_loop_body_wl_spec
          simp del: twl_st_of_wl.simps)
      done
    let ?R' = \<open>{((i, T'), T). (T', T) \<in> state_wl_l (Some (L, i)) \<and>
                        correct_watching T' \<and> i \<le> length (watched_by T' L)}\<close>
    have inv: \<open>unit_propagation_inner_loop_wl_loop_inv L iT'\<close>
      if
        \<open>(iT', T) \<in> ?R'\<close> and
        \<open>unit_propagation_inner_loop_l_inv L T\<close>
        for T iT'
    proof -
      obtain i T' where iT': \<open>iT' = (i, T')\<close> by (cases iT')
      show ?thesis
        unfolding unit_propagation_inner_loop_wl_loop_inv_def iT' prod.simps
        apply (rule exI[of _ T])
        using that by (auto simp: iT')
    qed
    have cond: \<open>(i < length (watched_by T' L) \<and> get_conflict_wl T' = None) =
      (clauses_to_update_l T \<noteq> {#})\<close>
      if
        \<open>(iT', T) \<in> ?R'\<close> and
        \<open>iT' = (i, T')\<close>
        for iT' T i T'
      using that
      apply (cases \<open>get_conflict_wl T'\<close>)
      by (auto simp: twl_st_wl)

    have \<open>unit_propagation_inner_loop_wl_loop L S \<le>
            \<Down> {((i, T'), T). (T', T) \<in> state_wl_l None \<and> ?P T T'}
              (unit_propagation_inner_loop_l L S')\<close>
      (is \<open>_ \<le> \<Down> ?R _\<close>)
      unfolding unit_propagation_inner_loop_wl_loop_def unit_propagation_inner_loop_l_def uncurry_def
      apply (refine_rcg WHILEIT_refine_genR[where
            R = \<open>?R\<close> and
            R' = \<open>?R'\<close>])
      subgoal using corr_w SS' by auto
      subgoal by (rule inv)
      subgoal by (rule cond)
      subgoal for i'T' T i' T'
        apply (rule order_trans)
        by (rule unit_propagation_body_wl_loop_fantom; simp; fail) (auto intro!: H
          simp del: twl_st_of_wl.simps)
      subgoal for iT' T by (auto simp: state_wl_l_def)
      done
    (* then have \<open>unit_propagation_inner_loop_wl_loop L S \<le> \<Down> {((i, T'), T).  (T', T) \<in> state_wl_l None \<and>
      ?P T T'}
     (unit_propagation_inner_loop_l L' S')\<close>
     if \<open>L = L'\<close> and \<open>S' = st_l_of_wl (Some (L, 0)) S\<close>
     for S' and L' :: \<open>'v literal\<close>
     using that by auto *)
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

definition unit_propagation_outer_loop_wl_inv where
  \<open>unit_propagation_outer_loop_wl_inv S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
      unit_propagation_outer_loop_l_inv S')\<close>

definition unit_propagation_outer_loop_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_inv\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S') + get_unit_init_clss S'));
        unit_propagation_inner_loop_wl L S'
      })
      (S\<^sub>0 :: 'v twl_st_wl)
\<close>

text \<open>TODO Move\<close>
lemma [twl_st_wl]:
  \<open>get_clauses_wl (set_literals_to_update_wl W S) = get_clauses_wl S\<close>
  \<open>get_unit_init_clss (set_literals_to_update_wl W S) = get_unit_init_clss S\<close>
  by (cases S; auto; fail)+

lemma unit_propagation_outer_loop_wl_spec:
  \<open>(unit_propagation_outer_loop_wl, unit_propagation_outer_loop_l)
 \<in> {(T'::'v twl_st_wl, T).
       (T', T) \<in> state_wl_l None \<and>
       correct_watching T' \<and>
       get_conflict_wl T' = None} \<rightarrow>\<^sub>f
    \<langle>{(T', T).
       (T', T) \<in> state_wl_l None \<and>
      (* literals_to_update_wl T' = {#} \<and> *)
       correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?u \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have inv: \<open>unit_propagation_outer_loop_wl_inv T'\<close>
  if
    \<open>(T', T) \<in> {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'}\<close> and
    \<open>unit_propagation_outer_loop_l_inv T\<close>
    for T T'
  unfolding unit_propagation_outer_loop_wl_inv_def
  apply (rule exI[of _ T])
  using that by auto

  have select_and_remove_from_literals_to_update_wl:
   \<open>select_and_remove_from_literals_to_update_wl S' \<le>
     \<Down> {((T', L'), (T, L)). L = L' \<and> (T', T) \<in> state_wl_l (Some (L, 0)) \<and>
         T' = set_literals_to_update_wl (literals_to_update_wl S' - {#L#}) S' \<and> L \<in># literals_to_update_wl S' \<and>
         L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S') + get_unit_init_clss S')
       }
       (select_and_remove_from_literals_to_update S)\<close>
    if S: \<open>(S', S) \<in> state_wl_l None\<close> and \<open>get_conflict_wl S' = None\<close> and
      corr_w: \<open>correct_watching S'\<close> and
      inv_l: \<open>unit_propagation_outer_loop_l_inv S\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
  proof -
    obtain M N D NE UE W Q where
      S': \<open>S' = (M, N, D, NE, UE, Q, W)\<close>
      by (cases S') auto
    obtain R where
      S_R: \<open>(S, R) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs R\<close>
      using inv_l unfolding unit_propagation_outer_loop_l_inv_def by blast
    have [simp]: \<open>trail (state\<^sub>W_of R) = convert_lits_l N M\<close>
       \<open>init_clss (state\<^sub>W_of R) = mset `# (init_clss_lf N) + NE\<close>
      using S_R S by (auto simp: twl_st S' twl_st_wl)
    have
      no_dup_q: \<open>no_duplicate_queued R\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of R)\<close>
      using struct_invs that by (auto simp: twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
    then have H1: \<open>L \<in># all_lits_of_mm (mset `# ran_mf N + NE)\<close> if LQ: \<open>L \<in># Q\<close> for L
    proof -
      obtain K where \<open>L = - lit_of K\<close> and \<open>K \<in># mset (convert_lits_l N M)\<close>
        using that no_dup_q LQ S_R S
        mset_le_add_mset_decr_left2[of L \<open>remove1_mset L Q\<close>]
        by (force simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          all_lits_of_mm_def atms_of_ms_def twl_st_l_def state_wl_l_def
          dest!: multi_member_split[of L Q])
      then have \<open>atm_of L \<in> atm_of ` lits_of_l M\<close>
        by (auto simp: convert_lits_l_def lits_of_def)
      moreover {
        have \<open>atm_of ` lits_of_l M
         \<subseteq> (\<Union>x\<in>set_mset (init_clss_lf N). atm_of ` set x) \<union>
           (\<Union>x\<in>set_mset NE. atms_of x) \<close>
          using that alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
          by (auto simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              all_lits_of_mm_def atms_of_ms_def)
          then have \<open>atm_of ` lits_of_l M \<subseteq> (\<Union>x\<in>set_mset (init_clss_lf N). atm_of ` set x) \<union>
           (\<Union>x\<in>set_mset NE. atms_of x)\<close>
          unfolding image_Un[symmetric]
            set_append[symmetric]
            append_take_drop_id
            .
          then have \<open>atm_of ` lits_of_l M \<subseteq> atms_of_mm (mset `# init_clss_lf N + NE)\<close>
            by (smt UN_Un Un_iff append_take_drop_id atms_of_ms_def atms_of_ms_mset_unfold set_append
                set_image_mset set_mset_mset set_mset_union subset_eq)
          }
      ultimately have \<open>atm_of L \<in> atms_of_mm (mset `# ran_mf N + NE)\<close>
        using that
        unfolding all_lits_of_mm_union atms_of_ms_union all_clss_lf_ran_m[symmetric]
          image_mset_union set_mset_union
        by auto
      then show ?thesis
        using that by (auto simp: in_all_lits_of_mm_ain_atms_of_iff)
    qed
    then have H: \<open>clause_to_update L S = mset (W L)\<close> and
       \<open>L \<in># all_lits_of_mm (mset `# ran_mf N + NE)\<close>
        if \<open>L \<in># Q\<close> for L
      using corr_w that S by (auto simp: correct_watching.simps S' clause_to_update_def)
    show ?thesis
      unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
      apply (rule RES_refine)
      unfolding Bex_def
      apply (rule_tac x=\<open>(set_clauses_to_update_l (clause_to_update (snd s) S)
              (set_literals_to_update_l
                (remove1_mset (snd s) (literals_to_update_l S)) S), snd s)\<close> in exI)
      using that S' S by (auto 5 5 simp: correct_watching.simps clauses_def state_wl_l_def
          mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state all_lits_of_mm_union
          dest: H H1)
  qed
  have conflict_None: \<open>get_conflict_wl T = None\<close>
    if
      \<open>literals_to_update_wl T \<noteq> {#}\<close> and
      inv1: \<open>unit_propagation_outer_loop_wl_inv T\<close>
      for T
  proof -
    obtain T' where
      2: \<open>(T, T') \<in> state_wl_l None\<close> and
      inv2: \<open>unit_propagation_outer_loop_l_inv T'\<close>
      using inv1 unfolding unit_propagation_outer_loop_wl_inv_def by blast
    obtain T'' where
      3: \<open>(T', T'') \<in> twl_st_l None\<close> and
      \<open>twl_struct_invs T''\<close>
      using inv2 unfolding unit_propagation_outer_loop_l_inv_def by blast
    then have \<open>get_conflict T'' \<noteq> None \<longrightarrow>
       clauses_to_update T'' = {#} \<and> literals_to_update T'' = {#}\<close>
       unfolding twl_struct_invs_def by fast
    then show ?thesis
      using that 2 3 by (auto simp: twl_st_wl twl_st twl_st_l)
  qed
  show ?thesis
    unfolding unit_propagation_outer_loop_wl_def unit_propagation_outer_loop_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg select_and_remove_from_literals_to_update_wl
      unit_propagation_inner_loop_wl_spec[unfolded fref_param1, THEN fref_to_Down_curry])
    subgoal by (auto simp:)
    subgoal by (rule inv)
    subgoal by auto
    subgoal by auto
    subgoal by (rule conflict_None)
    subgoal for T' T by (auto simp: )
    subgoal by (auto simp: twl_st_wl)
    subgoal by auto
    done
qed


subsubsection \<open>Decide or Skip\<close>

definition find_unassigned_lit_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit_wl = (\<lambda>(M, N, D, NE, UE, WS, Q).
     SPEC (\<lambda>L.
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE))))
     )\<close>

definition decide_wl_or_skip_pre where
\<open>decide_wl_or_skip_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
   decide_l_or_skip_pre S'
  )\<close>

definition decide_lit_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>decide_lit_wl = (\<lambda>L' (M, N, D, NE, UE, Q, W).
      (Decided L' # M, N, D, NE, UE, {#- L'#}, W))\<close>


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
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and>
          get_conflict_wl T' = None} \<rightarrow>
        \<langle>{((b', T'), (b, T)). b' = b \<and>
         (T', T) \<in> state_wl_l None \<and>
          correct_watching T'}\<rangle>nres_rel\<close>
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S'
    \<le> \<Down> Id
        (find_unassigned_lit_l S)\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that
    by (cases S') (auto simp: find_unassigned_lit_wl_def find_unassigned_lit_l_def
        mset_take_mset_drop_mset' state_wl_l_def)
  have option: \<open>(x, x') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>x = x'\<close> for x x'
    using that by (auto)
  show ?thesis
    unfolding decide_wl_or_skip_def decide_l_or_skip_def
    apply (refine_vcg find_unassigned_lit_wl option)
    subgoal unfolding decide_wl_or_skip_pre_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S S'
      by (cases S) (auto simp: correct_watching.simps clause_to_update_def
          decide_lit_l_def decide_lit_wl_def state_wl_l_def)
    done
qed


subsubsection \<open>Skip or Resolve\<close>

definition tl_state_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>tl_state_wl = (\<lambda>(M, N, D, NE, UE, WS, Q). (tl M, N, D, NE, UE, WS, Q))\<close>

definition resolve_cls_wl' :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v clause\<close> where
\<open>resolve_cls_wl' S C L  =
   remove1_mset (-L) (the (get_conflict_wl S)) \<union># (mset (tl (get_clauses_wl S \<propto> C)))\<close>

definition update_confl_tl_wl :: \<open>nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl\<close> where
  \<open>update_confl_tl_wl = (\<lambda>C L (M, N, D, NE, UE, WS, Q).
     let D = resolve_cls_wl' (M, N, D, NE, UE, WS, Q) C L in
        (False, (tl M, N, Some D, NE, UE, WS, Q)))\<close>

definition skip_and_resolve_loop_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>skip_and_resolve_loop_wl_inv S\<^sub>0 brk S \<longleftrightarrow>
    (\<exists>S' S'\<^sub>0. (S, S') \<in> state_wl_l None \<and>
      (S\<^sub>0, S'\<^sub>0) \<in> state_wl_l None \<and>
     skip_and_resolve_loop_inv_l S'\<^sub>0 brk S' \<and>
        correct_watching S)\<close>

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

lemma tl_state_wl_tl_state_l:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> (tl_state_wl S, tl_state_l S') \<in> state_wl_l None\<close>
  by (cases S) (auto simp: state_wl_l_def tl_state_wl_def tl_state_l_def)

lemma skip_and_resolve_loop_wl_spec:
  \<open>(skip_and_resolve_loop_wl, skip_and_resolve_loop_l)
    \<in> {(T'::'v twl_st_wl, T).
         (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and>
          0 < count_decided (get_trail_wl T')} \<rightarrow>
      \<langle>{(T', T).
         (T', T) \<in> state_wl_l None \<and>
          correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?s \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have get_conflict_wl: \<open>((False, S'), False, S)
    \<in> Id \<times>\<^sub>r {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'}\<close>
    (is \<open>_ \<in> ?B\<close>)
    if \<open>(S', S) \<in> state_wl_l None\<close> and \<open>correct_watching S'\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that by (cases S') (auto simp: state_wl_l_def)
  have [simp]: \<open>correct_watching (tl_state_wl S) = correct_watching S\<close> for S
    by (cases S) (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have [simp]: \<open>correct_watching  (tl aa, ca, da, ea, fa, ha, h) \<longleftrightarrow>
    correct_watching (aa, ca, None, ea, fa, ha, h)\<close>
    for aa ba ca L da ea fa ha h
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have [simp]: \<open>NO_MATCH None da \<Longrightarrow> correct_watching  (aa, ca, da, ea, fa, ha, h) \<longleftrightarrow>
    correct_watching (aa, ca, None, ea, fa, ha, h)\<close>
    for aa ba ca L da ea fa ha h
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have update_confl_tl_wl: \<open>
    (brkT, brkT') \<in> bool_rel \<times>\<^sub>f {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'} \<Longrightarrow>
    case brkT' of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S' brk S \<Longrightarrow>
    brkT' = (brk', T') \<Longrightarrow>
    brkT = (brk, T) \<Longrightarrow>
    lit_and_ann_of_propagated (hd (get_trail_l T')) = (L', C') \<Longrightarrow>
    lit_and_ann_of_propagated (hd (get_trail_wl T)) = (L, C) \<Longrightarrow>
    (update_confl_tl_wl C L T, update_confl_tl_l C' L' T') \<in> bool_rel \<times>\<^sub>f {(T', T).
         (T', T) \<in> state_wl_l None \<and> correct_watching T'}\<close>
    for T' brkT brk brkT' brk' T C C' L L' S'
    unfolding update_confl_tl_wl_def update_confl_tl_l_def resolve_cls_wl'_def resolve_cls_l'_def
    by (cases T; cases T')
     (auto simp: Let_def state_wl_l_def)
  have inv: \<open>skip_and_resolve_loop_wl_inv S' b' T'\<close>
    if
      \<open>(S', S) \<in> ?A\<close> and
      \<open>get_conflict_wl S' \<noteq> None\<close> and
      bt_inv: \<open>case bT of (x, xa) \<Rightarrow> skip_and_resolve_loop_inv_l S x xa\<close> and
      \<open>(b'T', bT) \<in> ?B\<close> and
      b'T': \<open>b'T' = (b', T')\<close>
    for S' S b'T' bT b' T'
  proof -
    obtain b T where bT: \<open>bT = (b, T)\<close> by (cases bT)
    show ?thesis
      unfolding skip_and_resolve_loop_wl_inv_def
      apply (rule exI[of _ T])
      apply (rule exI[of _ S])
      using that by (auto simp: bT b'T')
  qed

  show H: \<open>?s \<in> ?A \<rightarrow> \<langle>{(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'}\<rangle>nres_rel\<close>
    unfolding skip_and_resolve_loop_wl_def skip_and_resolve_loop_l_def
    apply (refine_rcg get_conflict_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule inv)
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: tl_state_wl_tl_state_l)
    subgoal for S' S b'T' bT b' T' by (cases T') (auto simp: correct_watching.simps)
    subgoal by auto
    subgoal by (rule update_confl_tl_wl) assumption+
    subgoal by auto
    subgoal by (auto simp: correct_watching.simps clause_to_update_def)
    done
qed


subsubsection \<open>Backtrack\<close>

definition find_decomp_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl  nres\<close> where
  \<open>find_decomp_wl =  (\<lambda>L (M, N, D, NE, UE, Q, W).
    SPEC(\<lambda>S. \<exists>K M2 M1. S = (M1, N, D, NE, UE, Q, W) \<and> (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

definition find_lit_of_max_level_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres\<close> where
  \<open>find_lit_of_max_level_wl =  (\<lambda>(M, N, D, NE, UE, Q, W) L.
    SPEC(\<lambda>L'. L' \<in># remove1_mset (-L) (the D) \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>


fun extract_shorter_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>extract_shorter_conflict_wl (M, N, D, NE, UE, Q, W) = SPEC(\<lambda>S.
     \<exists>D'. D' \<subseteq># the D \<and> S = (M, N, Some D', NE, UE, Q, W) \<and>
     clause `# twl_clause_of `# init_clss_lf N + NE + UE \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')\<close>

declare extract_shorter_conflict_wl.simps[simp del]
lemmas extract_shorter_conflict_wl_def = extract_shorter_conflict_wl.simps


definition backtrack_wl_inv where
  \<open>backtrack_wl_inv S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> state_wl_l None \<and> backtrack_l_inv S' \<and> correct_watching S)
  \<close>

definition propagate_bt_wl :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_bt_wl = (\<lambda>L L' (M, N, D, NE, UE, Q, W). do {
    D'' \<leftarrow> list_of_mset (the D);
    i \<leftarrow> SPEC(\<lambda>i. i \<notin> dom N);
    RETURN (Propagated (-L) i # M,
        N(i := Some ([-L, L'] @ (remove1 (-L) (remove1 L' D'')), False)),
          None, NE, UE, {#L#}, W(-L:= W (-L) @ [i], L':= W L' @ [i]))
      })\<close>

definition propagate_unit_bt_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>propagate_unit_bt_wl = (\<lambda>L (M, N, D, NE, UE, Q, W).
    (Propagated (-L) 0 # M, N, None, NE, add_mset (the D) UE, {#L#}, W))\<close>

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
    D, NE, UE, Q, W (L1 := W L1 @ [length N], L2 := W L2 @ [length N])) \<longleftrightarrow>
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
