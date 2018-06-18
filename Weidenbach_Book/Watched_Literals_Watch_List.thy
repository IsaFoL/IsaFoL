theory Watched_Literals_Watch_List
  imports Watched_Literals_List Array_UInt
begin

text \<open>Remove notation that coonflicts with \<^term>\<open>list_update\<close>:\<close>
no_notation Ref.update ("_ := _" 62)


section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>

type_synonym clauses_to_update_wl = \<open>nat multiset\<close>
type_synonym 'v watched = \<open>(nat \<times> 'v literal) list\<close>
type_synonym 'v lit_queue_wl = \<open>'v literal multiset\<close>

type_synonym 'v twl_st_wl =
  \<open>('v, nat) ann_lits \<times> 'v clauses_l \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl \<times>
    ('v literal \<Rightarrow> 'v watched)\<close>

subsection \<open>Access Functions\<close>

fun clauses_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> clauses_to_update_wl\<close> where
  \<open>clauses_to_update_wl (_, N, _, _, _, _, W) L i =
      filter_mset (\<lambda>i. i \<in># dom_m N) (mset (drop i (map fst (W L))))\<close>

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

fun get_unit_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned_clss_wl (M, N, D, NE, UE, Q, W) = UE\<close>

fun get_unit_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clss_wl (M, N, D, NE, UE, Q, W) = NE\<close>

fun get_unit_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_clauses_wl (M, N, D, NE, UE, Q, W) = NE + UE\<close>

lemma get_unit_clauses_wl_alt_def:
  \<open>get_unit_clauses_wl S = get_unit_init_clss_wl S + get_unit_learned_clss_wl S\<close>
  by (cases S) auto

fun get_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v literal \<Rightarrow> 'v watched)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, W) = W\<close>

definition all_lits_of_mm :: \<open>'a clauses \<Rightarrow> 'a literal multiset\<close> where
\<open>all_lits_of_mm Ls = Pos `# (atm_of `# (\<Union># Ls)) + Neg `# (atm_of `# (\<Union># Ls))\<close>

lemma all_lits_of_mm_empty[simp]: \<open>all_lits_of_mm {#} = {#}\<close>
  by (auto simp: all_lits_of_mm_def)

text \<open>
  We cannot just extract the literals of the clauses: we cannot be sure that atoms appear \<^emph>\<open>both\<close>
  positively and negatively in the clauses. If we could ensure that there are no pure literals, the
  definition of \<^term>\<open>all_lits_of_mm\<close> can be changed to \<open>all_lits_of_mm Ls = \<Union># Ls\<close>.

  In this definition \<^term>\<open>K\<close> is the blocking literal.
\<close>

fun all_blits_are_in_problem where
  \<open> all_blits_are_in_problem (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
      (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)). (\<forall>(i, K)\<in>#mset (W L). K \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))))\<close>

declare all_blits_are_in_problem.simps[simp del]

fun correct_watching_except :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching_except i j K (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    all_blits_are_in_problem (M, N, D, NE, UE, Q, W) \<and>
    (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)).
       (L =K \<longrightarrow>
         ((\<forall>(i, K)\<in>#mset (take i (W L) @ drop j (W L)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (take i (W L) @ drop j (W L))) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))) \<and>
       (L \<noteq> K \<longrightarrow>
         ((\<forall>(i, K)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))))\<close>

fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    all_blits_are_in_problem (M, N, D, NE, UE, Q, W) \<and>
    (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)).
       (\<forall>(i, K)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

declare correct_watching.simps[simp del]

(* lemma
  \<open>j \<ge> length (W L) \<Longrightarrow> correct_watching_except i j L (M, N, D, NE, UE, Q, W) \<Longrightarrow>
    correct_watching (M, N, D, NE, UE, Q, W(L := take i (W L)))\<close>
    try0 simp: correct_watching.simps
    dest: multi_member_split
  apply (auto simp: correct_watching.simps
    dest: multi_member_split) *)

fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v watched\<close> where
  \<open>watched_by (M, N, D, NE, UE, Q, W) L = W L\<close>

fun update_watched :: \<open>'v literal \<Rightarrow> 'v watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, D, NE, UE, Q, W) = (M, N, D, NE, UE, Q, W(L:= WL))\<close>

lemma correct_watching_exceptD:
  assumes 
    \<open>correct_watching_except i j L S\<close> and
    \<open>L \<in># all_lits_of_mm
           (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S)\<close> and
    w: \<open>w < length (watched_by S L)\<close> \<open>w \<ge> j\<close> \<open>fst (watched_by S L ! w) \<in># dom_m (get_clauses_wl S)\<close>
  shows \<open>snd (watched_by S L ! w) \<in> set (get_clauses_wl S \<propto> (fst (watched_by S L ! w)))\<close>
proof -
  have H: \<open>\<And>x. x\<in>set (take i (watched_by S L)) \<union> set (drop j (watched_by S L)) \<Longrightarrow>
          case x of (i, K) \<Rightarrow> i \<in># dom_m (get_clauses_wl S) \<longrightarrow> K \<in> set (get_clauses_wl S \<propto> i) \<and> K \<noteq> L\<close>
    using assms
    by (cases S)
     (clarsimp simp add: correct_watching_except.simps dest!: multi_member_split)
  have \<open>\<exists>i\<ge>j. i < length (watched_by S L) \<and>
            watched_by S L ! w = watched_by S L ! i\<close>
    by (rule exI[of _ w])
      (use w in auto)
  then show ?thesis
    using H[of \<open>watched_by S L ! w\<close>] w
    by (auto simp: in_set_drop_conv_nth)
qed

lemma in_all_lits_of_mm_ain_atms_of_iff:
  \<open>L \<in># all_lits_of_mm N \<longleftrightarrow> atm_of L \<in> atms_of_mm N\<close>
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

lemma in_all_lits_of_mm_uminusD: \<open>x2 \<in># all_lits_of_mm N \<Longrightarrow> -x2 \<in># all_lits_of_mm N\<close>
  by (auto simp: all_lits_of_mm_def)

lemma in_all_lits_of_mm_uminus_iff: \<open>-x2 \<in># all_lits_of_mm N \<longleftrightarrow> x2 \<in># all_lits_of_mm N\<close>
  by (cases x2) (auto simp: all_lits_of_mm_def)

lemma all_lits_of_mm_diffD:
  \<open>L \<in># all_lits_of_mm (A - B) \<Longrightarrow> L \<in># all_lits_of_mm A\<close>
  apply (induction A arbitrary: B)
  subgoal by auto
  subgoal for a A' B
    by (cases \<open>a \<in># B\<close>)
      (fastforce dest!: multi_member_split[of a B] simp: all_lits_of_mm_add_mset)+
  done

lemma all_lits_of_mm_mono:
  \<open>set_mset A \<subseteq> set_mset B \<Longrightarrow> set_mset (all_lits_of_mm A) \<subseteq> set_mset (all_lits_of_mm B)\<close>
  by (auto simp: all_lits_of_mm_def)

fun st_l_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl None (M, N, D, NE, UE, Q, W) = (M, N, D, NE, UE, {#}, Q)\<close>
| \<open>st_l_of_wl (Some (L, j)) (M, N, D, NE, UE, Q, W) =
    (M, N, D, NE, UE, (if D \<noteq> None then {#} else clauses_to_update_wl (M, N, D, NE, UE, Q, W) L j,
      Q))\<close>

definition state_wl_l :: \<open>('v literal \<times> nat) option \<Rightarrow> ('v twl_st_wl \<times> 'v twl_st_l) set\<close> where
\<open>state_wl_l L = {(T, T'). T' = st_l_of_wl L T}\<close>

fun twl_st_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> ('v twl_st_wl \<times> 'v twl_st) set\<close> where
  \<open>twl_st_of_wl L = state_wl_l L O twl_st_l (map_option fst L)\<close>


named_theorems twl_st_wl \<open>Conversions simp rules\<close>

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
    \<open>get_unit_learned_clauses_l T = get_unit_learned_clss_wl S\<close>
    \<open>get_unit_init_clauses_l T = get_unit_init_clss_wl S\<close>
    \<open>get_unit_learned_clauses_l T = get_unit_learned_clss_wl S\<close>
   \<open>get_unit_clauses_l T = get_unit_clauses_wl S\<close>
  using assms unfolding state_wl_l_def all_clss_lf_ran_m[symmetric]
  by (cases S; cases T; cases L; auto split: option.splits simp: trail.simps; fail)+

lemma remove_one_lit_from_wq_def:
  \<open>remove_one_lit_from_wq L S = set_clauses_to_update_l (clauses_to_update_l S - {#L#}) S\<close>
  by (cases S) auto

lemma correct_watching_set_literals_to_update[simp]:
  \<open>correct_watching (set_literals_to_update_wl WS T') = correct_watching T'\<close>
  by (cases T') (auto simp: correct_watching.simps all_blits_are_in_problem.simps)

lemma [twl_st_wl]:
  \<open>get_clauses_wl (set_literals_to_update_wl W S) = get_clauses_wl S\<close>
  \<open>get_unit_init_clss_wl (set_literals_to_update_wl W S) = get_unit_init_clss_wl S\<close>
  by (cases S; auto; fail)+

lemma get_conflict_wl_set_literals_to_update_wl[twl_st_wl]:
  \<open>get_conflict_wl (set_literals_to_update_wl P S) = get_conflict_wl S\<close>
  \<open>get_unit_clauses_wl (set_literals_to_update_wl P S) = get_unit_clauses_wl S\<close>
  by (cases S; auto; fail)+

definition set_conflict_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl = (\<lambda>C (M, N, D, NE, UE, Q, W). (M, N, Some (mset C), NE, UE, {#}, W))\<close>

lemma [twl_st_wl]: \<open>get_clauses_wl (set_conflict_wl D S) = get_clauses_wl S\<close>
  by (cases S) (auto simp: set_conflict_wl_def)

lemma [twl_st_wl]:
  \<open>get_unit_init_clss_wl (set_conflict_wl D S) = get_unit_init_clss_wl S\<close>
  \<open>get_unit_clauses_wl (set_conflict_wl D S) = get_unit_clauses_wl S\<close>
  by (cases S; auto simp: set_conflict_wl_def; fail)+

text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>.\<close>
declare twl_st_wl[simp]

definition unit_prop_body_wl_inv where
\<open>unit_prop_body_wl_inv T j i L \<longleftrightarrow>
    (\<exists>T'. (T, T') \<in> state_wl_l (Some (L, i)) \<and>
    unit_propagation_inner_loop_body_l_inv L (fst (watched_by T L ! i))
       (remove_one_lit_from_wq (fst (watched_by T L ! i)) T')\<and>
    L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T) + get_unit_clauses_wl T) \<and>
    correct_watching_except j i L T \<and>
    i < length (watched_by T L) \<and>
    get_conflict_wl T = None)\<close>

definition propagate_lit_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>propagate_lit_wl = (\<lambda>L' C i (M, N,  D, NE, UE, Q, W).
      let N = N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)) in
      (Propagated L' C # M, N, D, NE, UE, add_mset (-L') Q, W))\<close>

definition keep_watch where
  \<open>keep_watch = (\<lambda>L i j (M, N,  D, NE, UE, Q, W).
      (M, N,  D, NE, UE, Q, W(L := W L[i := W L ! j])))\<close>

definition update_clause_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>update_clause_wl = (\<lambda>(L::'v literal) C j w i f (M, N,  D, NE, UE, Q, W). do {
     let K' = (N\<propto>C) ! f;
     let N' = N(C \<hookrightarrow> swap (N \<propto> C) i f);
     RETURN (j, w+1, (M, N', D, NE, UE, Q, W(K' := W K' @ [(C, L)])))
  })\<close>

definition unit_prop_body_wl_find_unwatched_inv where
\<open>unit_prop_body_wl_find_unwatched_inv f C S \<longleftrightarrow>
   get_clauses_wl S \<propto> C \<noteq> [] \<and>
   (f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S \<propto> C)). - L \<in> lits_of_l (get_trail_wl S)))\<close>

definition unit_propagation_inner_loop_wl_loop_inv where
  \<open>unit_propagation_inner_loop_wl_loop_inv L = (\<lambda>(j, w, S).
    (\<exists>S'. (S, S') \<in> state_wl_l (Some (L, w)) \<and>
       unit_propagation_inner_loop_l_inv L S' \<and>
      correct_watching_except j w L S \<and> w \<le> length (watched_by S L)))\<close>

definition unit_propagation_inner_loop_body_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_inv L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let val_K = polarity (get_trail_wl S) K;
      let S = keep_watch L j w S;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        ASSERT(unit_prop_body_wl_inv S j w L);
        if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
          let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
          let val_L' = polarity (get_trail_wl S) L';
          if val_L' = Some True
          then RETURN (j+1, w+1, S)
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto>C);
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)}
                else do {RETURN (j+1, w+1, propagate_lit_wl L' C i S)}
              }
            | Some f \<Rightarrow> do {
                update_clause_wl L C j w i f S
              }
          }
        }
      }
   }\<close>

thm unit_propagation_inner_loop_body_l_def
lemma unit_propagation_inner_loop_body_wl_alt_def:
 \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_inv L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let b = (C \<in># dom_m (get_clauses_wl S));
      let val_K = polarity (get_trail_wl S) K;
      let S = keep_watch L j w S;
      if \<not>b then
        if val_K = Some True
        then RETURN (j+1, w+1, S)
        else do { \<comment>\<open>Now the costly operations:\<close>
          ASSERT(unit_prop_body_wl_inv S j w L);
          if C \<notin># dom_m (get_clauses_wl S)
          then RETURN (j, w+1, S)
          else do {
            let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
            let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
            let val_L' = polarity (get_trail_wl S) L';
            if val_L' = Some True
            then RETURN (j+1, w+1, S)
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto>C);
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)}
                  else do {RETURN (j+1, w+1, propagate_lit_wl L' C i S)}
                }
              | Some f \<Rightarrow> do {
                  update_clause_wl L C j w i f S
                }
            }
          }
        }
      else
        let _ = (get_clauses_wl S)\<propto>C in
        let S = S in
        let _ = K in
        let _ = polarity (get_trail_wl S) K in
        if val_K = Some True
        then RETURN (j+1, w+1, S)
        else do { \<comment>\<open>Now the costly operations:\<close>
          ASSERT(unit_prop_body_wl_inv S j w L);
          if C \<notin># dom_m (get_clauses_wl S)
          then RETURN (j, w+1, S)
          else do {
            let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
            let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
            let val_L' = polarity (get_trail_wl S) L';
            if val_L' = Some True
            then RETURN (j+1, w+1, S)
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto>C);
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)}
                  else do {RETURN (j+1, w+1, propagate_lit_wl L' C i S)}
                }
              | Some f \<Rightarrow> do {
                  update_clause_wl L C j w i f S
                }
            }
          }
        }
   }\<close>
  unfolding unit_propagation_inner_loop_body_wl_def if_not_swap Let_def by auto


subsection \<open>The Functions\<close>

subsubsection \<open>Inner Loop\<close>

lemma int_xor_3_same2:  \<open>a XOR b XOR a = b\<close> for a b :: int
  by (metis bbw_lcs(3) bin_ops_same(3) int_xor_code(2))

lemma nat_xor_3_same2: \<open>a XOR b XOR a = b\<close> for a b :: nat
  unfolding bitXOR_nat_def
  by (auto simp: int_xor_3_same2)

lemma clause_to_update_mapsto_upd_If:
  assumes
    i: \<open>i \<in># dom_m N\<close>
  shows
  \<open>clause_to_update L (M, N(i \<hookrightarrow> C'), C, NE, UE, WS, Q) =
    (if L \<in> set (watched_l C')
     then add_mset i (remove1_mset i (clause_to_update L (M, N, C, NE, UE, WS, Q)))
     else remove1_mset i (clause_to_update L (M, N, C, NE, UE, WS, Q)))\<close>
proof -
  define D' where \<open>D' = dom_m N - {#i#}\<close>
  then have [simp]: \<open>dom_m N = add_mset i D'\<close>
    using assms by (simp add: mset_set.remove)
  have [simp]: \<open>i \<notin># D'\<close>
    using assms distinct_mset_dom[of N] unfolding D'_def by auto

  have \<open>{#C \<in># D'.
     (i = C \<longrightarrow> L \<in> set (watched_l C')) \<and>
     (i \<noteq> C \<longrightarrow> L \<in> set (watched_l (N \<propto> C)))#} =
    {#C \<in># D'. L \<in> set (watched_l (N \<propto> C))#}\<close>
    by (rule filter_mset_cong2) auto
  then show ?thesis
    unfolding clause_to_update_def
    by auto
qed

(* TODO Move *)
lemma (in -) ex_geI: \<open>P n \<Longrightarrow> n \<ge> m \<Longrightarrow> \<exists>n\<ge>m. P n\<close>
  by auto
(* End Move *)

lemma
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close> and L :: \<open>'v literal\<close> and w :: nat
  defines [simp]: \<open>C' \<equiv> fst (watched_by S L ! w)\<close>
  defines
    [simp]: \<open>T \<equiv> remove_one_lit_from_wq C' S'\<close>

  defines
    [simp]: \<open>C'' \<equiv> get_clauses_l S' \<propto> C'\<close>
  assumes
    S_S': \<open>(S, S') \<in> state_wl_l (Some (L, w))\<close> and
    w_le: \<open>w < length (watched_by S L)\<close> and
    corr_w: \<open>correct_watching_except j w L S\<close> and
    inner_loop_inv: \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
    n: \<open>n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl S)) (mset (drop w (watched_by S L))))\<close>
  shows unit_propagation_inner_loop_body_wl_spec: \<open>unit_propagation_inner_loop_body_wl L j w S \<le>
   \<Down> {((i, j, T'), (T, n)).
        (T', T) \<in> state_wl_l (Some (L, j)) \<and>
        correct_watching_except i j L T' \<and>
        j \<le> length (watched_by T' L) \<and>
        i \<le> j \<and>
        n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl T')) (mset (drop w (watched_by T' L))))}
     (unit_propagation_inner_loop_body_l_with_skip L (S', n))\<close> (is \<open>?propa\<close>)and
    unit_propagation_inner_loop_body_wl_update:
      \<open>unit_propagation_inner_loop_body_l_inv L C' T \<Longrightarrow>
         mset `# (ran_mf ((get_clauses_wl S) (C'\<hookrightarrow> (swap (get_clauses_wl S \<propto> C') 0
                           (1 - (if (get_clauses_wl S)\<propto>C' ! 0 = L then 0 else 1)))))) =
        mset `# (ran_mf (get_clauses_wl S))\<close> (is \<open>_ \<Longrightarrow> ?eq\<close>)
proof -
  obtain bL where SLw: \<open>watched_by S L ! w = (C', bL)\<close>
    using C'_def by (cases \<open>watched_by S L ! w\<close>) auto
  have val: \<open>(polarity a b, polarity a' b') \<in> Id\<close>
    if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' :: \<open>('a, 'b) ann_lits\<close> and b b' :: \<open>'a literal\<close>
    by (auto simp: that)
  let ?M = \<open>get_trail_wl S\<close>
  have f: \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto> C')
      \<le> \<Down> {(found, found'). found = found' \<and>
             (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l C''). -L \<in> lits_of_l ?M)) \<and>
             (\<forall>j. found = Some j \<longrightarrow> (j < length C'' \<and> (undefined_lit ?M (C''!j) \<or> C''!j \<in> lits_of_l ?M) \<and> j \<ge> 2))
           }
            (find_unwatched_l (get_trail_l T) (get_clauses_l T \<propto> C'))\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    using S_S' by (auto simp: find_unwatched_l_def intro!: RES_refine)

  define i :: nat where
    \<open>i \<equiv> (if get_clauses_wl S \<propto> C' ! 0 = L then 0 else 1)\<close>
  have
    l_wl_inv: \<open>unit_prop_body_wl_inv S j w L\<close> (is ?inv) and
    clause_ge_0: \<open>0 < length (get_clauses_l T \<propto> C')\<close> (is ?ge) and
    L_def: \<open>defined_lit (get_trail_wl S) L\<close> \<open>-L \<in> lits_of_l (get_trail_wl S)\<close>
      \<open>L \<notin> lits_of_l (get_trail_wl S)\<close> (is ?L_def) and
    i_le: \<open>i < length (get_clauses_wl S \<propto> C')\<close>  (is ?i_le) and
    i_le2: \<open>1-i < length (get_clauses_wl S \<propto> C')\<close>  (is ?i_le2) and
    C'_dom: \<open>C' \<in># dom_m (get_clauses_l T)\<close> (is ?C'_dom) and
    L_watched: \<open>L \<in> set (watched_l (get_clauses_l T \<propto> C'))\<close> (is ?L_w) and
    dist_clss: \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close> and
    confl: \<open>get_conflict_l T = None\<close> (is ?confl)
  if
    \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
  proof -
    have \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that unfolding unit_prop_body_wl_inv_def by fast+
    then obtain T' where
      T_T': \<open>(set_clauses_to_update_l (clauses_to_update_l T + {#C'#}) T, T') \<in> twl_st_l (Some L)\<close> and
      struct_invs: \<open>twl_struct_invs T'\<close> and
       \<open>twl_stgy_invs T'\<close> and
      C'_dom: \<open>C' \<in># dom_m (get_clauses_l T)\<close> and
       \<open>0 < C'\<close> and
       ge_0: \<open>0 < length (get_clauses_l T \<propto> C')\<close> and
       \<open>no_dup (get_trail_l T)\<close> and
       i_le: \<open>(if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)
         < length (get_clauses_l T \<propto> C')\<close> and
       i_le2: \<open>1 - (if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)
         < length (get_clauses_l T \<propto> C')\<close> and
       L_watched: \<open>L \<in> set (watched_l (get_clauses_l T \<propto> C'))\<close> and
       confl: \<open>get_conflict_l T = None\<close>
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
    have \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)\<close>
      using alien uL_M twl_st_l(1-8)[OF T_T'] S_S'
        init_clss_state_to_l[OF T_T']
        unit_init_clauses_get_unit_init_clauses_l[OF T_T']
      unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: in_all_lits_of_mm_ain_atms_of_iff twl_st_wl twl_st twl_st_l)
    then have \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
      apply (rule set_rev_mp)
      apply (rule all_lits_of_mm_mono)
      by (cases S) auto
    then have l_wl_inv: \<open>(S, S') \<in> state_wl_l (Some (L, w)) \<and>
         unit_propagation_inner_loop_body_l_inv L (fst (watched_by S L ! w))
          (remove_one_lit_from_wq (fst (watched_by S L ! w)) S') \<and>
         L \<in># all_lits_of_mm
               (mset `# init_clss_lf (get_clauses_wl S) +
                get_unit_clauses_wl S) \<and>
         correct_watching_except j w L S \<and>
         w < length (watched_by S L) \<and> get_conflict_wl S = None\<close> 
      using that assms unfolding unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def
      apply -
      by (auto simp: twl_st)
         
    then show ?inv
      using that assms unfolding unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def
      by blast
    show ?ge
      by (rule ge_0)
    show \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
      using dist S_S' twl_st_l(1-8)[OF T_T'] T_T' unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def
      by (auto simp: twl_st)
    show ?confl
      using confl .
  qed

  have f': \<open>(f, f') \<in> \<langle>Id\<rangle>option_rel\<close>
    if \<open>f = f'\<close> for f f'
    using that by auto
  (* have ref:
    \<open>update_clause_wl L C' j w i f S
    \<le> \<Down> {((i, j, T'), T). (T', T) \<in> state_wl_l (Some (L, j)) \<and> correct_watching_except j w L T' \<and>
            j \<le> length (watched_by T' L)}
        (update_clause_l C' i f' T)\<close>
    if
      init_inv: \<open>unit_prop_body_wl_inv S j w L\<close> and
      init_inv': \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close> and
      val_L'_not_Some_True: \<open>polarity (get_trail_wl S) (get_clauses_wl S \<propto> C' ! (1 - i)) \<noteq> Some True\<close> and
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
    let ?N = \<open>N(fst (W L ! w) \<hookrightarrow> swap (N \<propto> (fst (W L ! w))) i f')\<close>
    let ?W = \<open>W(L := butlast (W L[w := last (W L)]),
            N \<propto> (fst (W L ! w)) ! f' := W (N \<propto> (fst (W L ! w)) ! f') @ [W L ! w])\<close>
    have [simp]: \<open>mset (swap (N \<propto> (fst (W L ! w))) i f') = mset (N \<propto> (fst (W L ! w)))\<close>
      apply (rule swap_multiset)
      using f'_f i_le[OF init_inv'] S_S' unfolding i_def[symmetric]
      by (auto simp: S)
    have [simp]: \<open>{#mset (fst x). x \<in># ran_m ?N#} = {#mset (fst x). x \<in># ran_m N#}\<close>
      apply (subst ran_m_clause_upd)
      subgoal using C'_dom[OF init_inv'] S_S' by (auto simp: S)
      subgoal using C'_dom[OF init_inv'] S_S' by (auto simp: image_mset_remove1_mset_if S
         ran_m_def)
      done
    have [simp]: \<open>fst (W L ! w) \<in># dom_m N\<close> \<open>w < length (W L)\<close> \<open>w \<le> length (W L) - Suc 0\<close>
      using C'_dom[OF init_inv'] S_S' w_le by (auto simp: S)
    have [simp]: \<open>L \<noteq>  N \<propto> (fst (W L ! w)) ! f'\<close>
      using f'_f S_S' by (auto simp: S)
    have [simp]: \<open>set (watched_l (N \<propto> (fst (W L ! w)))) =
        {N \<propto> (fst (W L ! w)) ! i, N \<propto> (fst (W L ! w)) ! (1 - i)}\<close>
       using clause_ge_0[OF init_inv'] S_S' i_le f'_f
       by (auto simp: swap_def S i_def take_2_if)
    have [simp]: \<open>set (watched_l (swap (N \<propto> (fst (W L ! w))) i f')) =
        {N \<propto> (fst (W L ! w)) ! f', N \<propto> (fst (W L ! w)) ! (1 - i)}\<close>
       using clause_ge_0[OF init_inv'] S_S' i_le f'_f
       by (auto simp: swap_def S i_def take_2_if)
    have N_W_L[simp]: \<open>N \<propto> (fst (W L ! w)) ! i = L\<close>
      using L_watched[OF init_inv'] S_S' by (auto simp: take_2_if S i_def hd_conv_nth
         split: if_splits)
    have \<open>N \<propto> (fst (W L ! w)) \<in># ran_mf N\<close>
      using C'_dom[OF init_inv'] S_S' by (auto simp: S ran_m_def)
    then have dist: \<open>distinct (N \<propto> (fst (W L ! w)))\<close>
      using dist_clss[OF init_inv'] S_S'
      by (auto simp: S distinct_mset_set_def)
    have [simp]:
       \<open>N \<propto> (fst (W L ! w)) ! (Suc 0 - i) \<noteq> L\<close>
       \<open>N \<propto> (fst (W L ! w)) ! (Suc 0 - i) \<noteq> N \<propto> (fst (W L ! w)) ! f'\<close>
       \<open>N \<propto> (fst (W L ! w)) ! f' \<noteq> N \<propto> (fst (W L ! w)) ! (Suc 0 - i)\<close>
      apply (subst (2) N_W_L[symmetric])
      using i_le[OF init_inv'] f'_f S_S' dist
      by (auto simp: nth_eq_iff_index_eq S i_def simp del: N_W_L)
    have corr_W: \<open>correct_watching_except j w L
          (M, N(fst (W L ! w) \<hookrightarrow> swap (N \<propto> (fst (W L ! w))) i f'), None, NE, UE, Q, W
           (L := butlast (W L[w := last (W L)]),
            N \<propto> (fst (W L ! w)) ! f' := W (N \<propto> (fst (W L ! w)) ! f') @ [W L ! w]))\<close>
      using corr_w unfolding S correct_watching_except.simps
      by (auto simp: clause_to_update_mapsto_upd_If
        id_remove_1_mset_iff_notin
        remove_1_mset_id_iff_notin
        in_clause_to_update_iff)
    show ?thesis
      using S_S' ff' corr_W
      by (auto simp: S update_clause_wl_def update_clause_l_def Let_def state_wl_l_def
        Cons_nth_drop_Suc[symmetric])
  qed *)
  (* have \<open>RETURN (C', bL) \<le> \<Down> {((C', bL), K). K = bL} (SPEC (\<lambda>K. K \<in> set (get_clauses_l T \<propto> C')))\<close>
    if \<open>unit_prop_body_wl_inv S j w L\<close>
  proof -
    have blits: \<open>all_blits_are_in_problem S\<close>
      using corr_w
      unfolding correct_watching_except.simps 
      by (cases S) clarsimp
    have \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
      using that unfolding unit_prop_body_wl_inv_def by blast
    from multi_member_split[OF this] have \<open>bL \<in> set (get_clauses_l T \<propto> C')\<close>
      using blits
      unfolding all_blits_are_in_problem.simps 
      apply (cases S)
      apply (clarsimp simp add: Ball_def)
      try0
      apply simp

sorry
    show ?thesis
      apply (rule RETURN_RES_refine)
      apply (auto simp: intro!: )
      sorry *)
  (* have other_watched_is_true: \<open>((j+1, w + 1, S), T)
    \<in> {((j, i, T'), T).
       (T', T) \<in> state_wl_l (Some (L, i)) \<and>
       correct_watching_except j i L T' \<and> i \<le> length (watched_by T' L)}\<close>
    using S_S' w_le corr_w
    apply (cases S)
    by (auto simp: state_wl_l_def Cons_nth_drop_Suc[symmetric])
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
    have [iff]:
      \<open>K \<in># all_lits_of_mm (add_mset (mset (N \<propto> (W L ! w))) ({#mset (fst x). x \<in># ran_m N#} + NE)) \<longleftrightarrow>
       K \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + NE)\<close> for K
      using C'_dom[OF inv] S_S' by (auto simp: ran_m_def S state_wl_l_def all_lits_of_mm_add_mset
          dest!: multi_member_split)
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
      using S_S' w_le corr_w C'_dom[OF inv] corr_w
      unfolding propagate_lit_l_def propagate_lit_wl_def
      by (auto simp: state_wl_l_def propagate_lit_wl_def S image_mset_remove1_mset_if
        Cons_nth_drop_Suc[symmetric] clause_to_update_mapsto_upd_If ran_def
      ran_m_mapsto_upd correct_watching.simps clause_to_update_def
      intro!: filter_mset_cong)
    then show ?thesis
      using S_S' w_le corr_w C'_dom[OF inv] corr_w
      unfolding propagate_lit_l_def propagate_lit_wl_def
      by (auto simp: state_wl_l_def propagate_lit_wl_def S
        Cons_nth_drop_Suc[symmetric] clause_to_update_mapsto_upd_If ran_m_mapsto_upd)
  qed *)
  have i_def': \<open>i = (if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)\<close>
    using S_S' unfolding i_def by auto
  (* have \<open>RETURN (C', bL) \<le>
      \<Down> {((C', bL), K). fst (watched_by S L ! w) \<in># dom_m (get_clauses_wl S) \<longrightarrow> K = bL}
      (SPEC (\<lambda>K. K \<in> set (get_clauses_l T \<propto> C')))\<close> 
    if \<open>unit_prop_body_wl_inv S j w L\<close>
  proof -
    have blits: \<open>all_blits_are_in_problem S\<close>
      using corr_w
      unfolding correct_watching_except.simps 
      by (cases S) clarsimp
    have L: \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
      using that unfolding unit_prop_body_wl_inv_def by blast
    have \<open>bL \<in> set (get_clauses_l T \<propto> C')\<close>
      if \<open>fst (watched_by S L ! w) \<in># dom_m (get_clauses_wl S)\<close>
      using correct_watching_exceptD[OF corr_w L w_le _ ] that S_S' unfolding SLw by auto
    then show ?thesis
      apply -
      apply (rule RETURN_RES_refine)
      apply (rule_tac x=bL in exI)
      apply (auto )
      find_theorems bL
      using blits
      unfolding all_blits_are_in_problem.simps 
      apply (cases S)
      apply (clarsimp simp add: Ball_def)
      try0
      apply simp
      sorry *)
  (* qed *)
  have[refine0]: \<open>RETURN (C', bL) \<le> \<Down> {((C', bL), b). b \<longleftrightarrow> C'\<notin># dom_m (get_clauses_wl S)}
       (SPEC (\<lambda>b. b \<longrightarrow> 0 < n))\<close>
  proof -
    have \<open>(C', bL) \<in># {#(i, _) \<in># mset (drop w (watched_by S L)). i \<notin># dom_m (get_clauses_wl S)#}\<close>
      if \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S) \<close>
      using that w_le unfolding SLw apply -
      apply (auto simp add: in_set_drop_conv_nth intro!: ex_geI[of _ w])
      unfolding SLw
      apply auto
      done
    from multi_member_split[OF this] show ?thesis
      apply (intro RETURN_SPEC_refine)
      using n
      by auto
  qed
  have S_removal: \<open>(S, set_clauses_to_update_l
         (remove1_mset (fst (watched_by S L ! w)) (clauses_to_update_l S')) S')
    \<in> state_wl_l (Some (L, Suc w))\<close>
    using S_S' w_le by (cases S; cases S')
      (auto simp: state_wl_l_def Cons_nth_drop_Suc[symmetric])
  have fst_watched_in_clss: \<open>fst (watched_by S L ! w) \<in># clauses_to_update_l S'\<close>
    if \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close>
  proof -
    have \<open>get_conflict_l T = None\<close>
      using that unfolding unit_propagation_inner_loop_wl_loop_inv_def
       unit_propagation_inner_loop_l_inv_def prod.case apply -
      apply normalize_goal+
      apply auto
      sorry
    then show ?thesis
      using S_S' w_le by  (cases S; cases S')
      (auto simp: state_wl_l_def Cons_nth_drop_Suc[symmetric] in_set_drop_conv_nth)
  qed
  have K [refine0]: \<open>RETURN (get_clauses_wl (keep_watch L j w S) \<propto> C')
    \<le> \<Down> {(_, (U, C)). C = C' \<and> (S, U) \<in> state_wl_l (Some (L, Suc w))} (select_from_clauses_to_update S')\<close>
    if \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close>
    unfolding select_from_clauses_to_update_def
    apply (rule RETURN_RES_refine)
    apply (rule exI[of _ \<open>(T, C')\<close>])
    using fst_watched_in_clss[OF that]
    by (auto simp: remove_one_lit_from_wq_def S_removal)
  have \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S) \<Longrightarrow>
     (keep_watch L j w S, S') \<in> state_wl_l (Some (L, Suc w))\<close>
    using S_S' w_le apply (cases S; cases S')
    apply (auto simp: state_wl_l_def keep_watch_def Cons_nth_drop_Suc[symmetric])
    sorry

  show 1: ?propa
    (is \<open>_ \<le> \<Down> ?unit _\<close>)
    unfolding unit_propagation_inner_loop_body_wl_alt_def unit_propagation_inner_loop_body_l_def
      i_def[symmetric] i_def'[symmetric] unit_propagation_inner_loop_body_l_with_skip_def
      unit_propagation_inner_loop_body_l_def
    (* apply (rewrite at "let _ = watched_by _ _ ! _ in _" Let_def) *)
    apply (rewrite at "let _ = keep_watch _ _ _ _ in _" Let_def)
    unfolding i_def[symmetric] SLw prod.case
    apply (rewrite at "let _ = _ in let _ = get_clauses_l _ \<propto> _ ! _ in _" Let_def)
    apply (rewrite in \<open>if (\<not>_) then select_from_clauses_to_update _ >>= _ else _\<close> if_not_swap)
    supply [[goals_limit=5]]
    apply (refine_rcg val f f' (*ref*); remove_dummy_vars)
    subgoal using inner_loop_inv .
    subgoal by auto
    subgoal
        using S_S'
       apply (auto simp: split: if_splits)
       sorry
    apply (rule K)
    subgoal by assumption
    subgoal
    oops
    apply refine_vcg
    apply (auto split: if_splits)
      apply (auto intro!: ASSERT_refine_right)
      unfolding select_from_clauses_to_update_def
      apply (rule rhs_step_bind_SPEC[of _ \<open>(set_clauses_to_update_l
       (remove1_mset C
         (clauses_to_update_l
           (remove_one_lit_from_wq (fst (watched_by S L ! w)) S')))
       (remove_one_lit_from_wq (fst (watched_by S L ! w)) S'), _)\<close>])
      apply (auto intro!: ASSERT_refine_right)
      prefer 3
find_theorems "_ \<le> \<Down> _ (RES _ >>=  _)"    
     sorry


    oops
      unfolding unit_propagation_inner_loop_wl_loop_inv_def prod.case apply -
      apply (rule exI[of _ S'])
      apply auto
      try0
      find_theorems S'
      defer
     by (rule l_wl_inv)
    subgoal using S_S' n apply auto
    oops
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
    using i_le[OF inv] i_le2[OF inv] C'_dom[OF inv] S_S'
    unfolding i_def[symmetric]
    by (auto simp: ran_m_clause_upd image_mset_remove1_mset_if)
qed

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
      correct_watching T'} \<rightarrow>
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
        ASSERT(L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S') + get_unit_clauses_wl S'));
        unit_propagation_inner_loop_wl L S'
      })
      (S\<^sub>0 :: 'v twl_st_wl)
\<close>


lemma unit_propagation_outer_loop_wl_spec:
  \<open>(unit_propagation_outer_loop_wl, unit_propagation_outer_loop_l)
 \<in> {(T'::'v twl_st_wl, T).
       (T', T) \<in> state_wl_l None \<and>
       correct_watching T'} \<rightarrow>\<^sub>f
    \<langle>{(T', T).
       (T', T) \<in> state_wl_l None \<and>
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
         L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S') + get_unit_clauses_wl S')
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
    have [simp]: (* \<open>trail (state\<^sub>W_of R) = convert_lits_l N M\<close> *)
       \<open>init_clss (state\<^sub>W_of R) = mset `# (init_clss_lf N) + NE\<close>
      using S_R S by (auto simp: twl_st S' twl_st_wl)
    have
      no_dup_q: \<open>no_duplicate_queued R\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of R)\<close>
      using struct_invs that by (auto simp: twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
    then have H1: \<open>L \<in># all_lits_of_mm (mset `# ran_mf N + NE + UE)\<close> if LQ: \<open>L \<in># Q\<close> for L
    proof -
      have [simp]: \<open>(f o g) ` I = f ` g ` I\<close> for f g I
        by auto
      obtain K where \<open>L = - lit_of K\<close> and \<open>K \<in># mset (trail (state\<^sub>W_of R))\<close>
        using that no_dup_q LQ S_R S
        mset_le_add_mset_decr_left2[of L \<open>remove1_mset L Q\<close> Q]
        by (fastforce simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          all_lits_of_mm_def atms_of_ms_def twl_st_l_def state_wl_l_def uminus_lit_swap
          convert_lit.simps
          dest!: multi_member_split[of L Q] mset_subset_eq_insertD in_convert_lits_lD2)
      from imageI[OF this(2), of \<open>atm_of o lit_of\<close>]
      have \<open>atm_of L \<in> atm_of ` lits_of_l (get_trail_wl S')\<close> and
        [simp]: \<open>atm_of ` lits_of_l (trail (state\<^sub>W_of R)) = atm_of ` lits_of_l (get_trail_wl S')\<close>
        using S_R S S \<open>L = - lit_of K\<close>
        by (simp_all add: twl_st image_image[symmetric]
            lits_of_def[symmetric])
      then have \<open>atm_of L \<in> atm_of ` lits_of_l M\<close>
        using S'  by auto
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
       \<open>L \<in># all_lits_of_mm (mset `# ran_mf N + NE + UE)\<close>
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
   remove1_mset (-L) (the (get_conflict_wl S) \<union># (mset (tl (get_clauses_wl S \<propto> C))))\<close>

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

definition find_decomp_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>find_decomp_wl =  (\<lambda>L (M, N, D, NE, UE, Q, W).
    SPEC(\<lambda>S. \<exists>K M2 M1. S = (M1, N, D, NE, UE, Q, W) \<and> (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

definition find_lit_of_max_level_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres\<close> where
  \<open>find_lit_of_max_level_wl =  (\<lambda>(M, N, D, NE, UE, Q, W) L.
    SPEC(\<lambda>L'. L' \<in># remove1_mset (-L) (the D) \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>


fun extract_shorter_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>extract_shorter_conflict_wl (M, N, D, NE, UE, Q, W) = SPEC(\<lambda>S.
     \<exists>D'. D' \<subseteq># the D \<and> S = (M, N, Some D', NE, UE, Q, W) \<and>
     clause `# twl_clause_of `# ran_mf N + NE + UE \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')\<close>

declare extract_shorter_conflict_wl.simps[simp del]
lemmas extract_shorter_conflict_wl_def = extract_shorter_conflict_wl.simps


definition backtrack_wl_inv where
  \<open>backtrack_wl_inv S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> state_wl_l None \<and> backtrack_l_inv S' \<and> correct_watching S)
  \<close>

definition propagate_bt_wl :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_bt_wl = (\<lambda>L L' (M, N, D, NE, UE, Q, W). do {
    D'' \<leftarrow> list_of_mset (the D);
    i \<leftarrow> get_fresh_index N;
    RETURN (Propagated (-L) i # M,
        fmupd i ([-L, L'] @ (remove1 (-L) (remove1 L' D'')), False) N,
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
  assumes
    L1: \<open>atm_of L1 \<in> atms_of_mm (mset `# ran_mf N + NE)\<close> and
    L2: \<open>atm_of L2 \<in> atms_of_mm (mset `# ran_mf N + NE)\<close> and
    UW: \<open>atms_of (mset UW) \<subseteq> atms_of_mm (mset `# ran_mf N + NE)\<close> and
    i_dom: \<open>i \<notin># dom_m N\<close>
  shows
  \<open>correct_watching (K # M, fmupd i (L1 # L2 # UW,  b) N,
    D, NE, UE, Q, W (L1 := W L1 @ [i], L2 := W L2 @ [i])) \<longleftrightarrow>
  correct_watching (M, N, D, NE, UE, Q, W)\<close>
  (is \<open>?l \<longleftrightarrow> ?c\<close> is \<open>correct_watching (_, ?N, _) = _\<close>)
proof (rule iffI)
  assume corr: ?l
  have H: \<open>\<And>x. x \<in># all_lits_of_mm (mset `# ran_mf ?N) +
              all_lits_of_mm NE + all_lits_of_mm UE \<longrightarrow>
        mset ((W(L1 := W L1 @ [i], L2 := W L2 @ [i])) x) =
        clause_to_update x
         (K # M, ?N, D, NE, UE, {#}, {#})\<close>
    using corr
    by (auto simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset if_distrib[of mset]
        uminus_lit_swap correct_watching.simps all_lits_of_mm_union Ball_def
        all_conj_distrib)
  have K[iff]: \<open>{x.  x = i \<or> (x = i \<or> Q x) \<and> P x} = Set.insert i {x. x \<noteq> i \<and> Q x \<and> P x}\<close>
     for P Q :: \<open>nat \<Rightarrow> bool\<close> and i :: nat
    by auto
  have [simp]: \<open>mset (W x) = clause_to_update x (M, N, D, NE, UE, {#}, {#})\<close>
    if \<open>x \<in># all_lits_of_mm NE \<or> x \<in># all_lits_of_mm UE\<close>
    for x
    using that H[of x] i_dom
    by (auto split: if_splits simp: clause_to_update_def nth_append
        intro!: arg_cong[of _ _ mset_set] filter_mset_cong)
  have K:
    \<open>set_mset (all_lits_of_mm (mset `# ran_mf ?N + NE + UE)) =
       set_mset (all_lits_of_mm (mset `# ran_mf N + NE + UE))\<close>
    using i_dom L1 L2 UW
    by (auto 5 5 simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset
        ran_m_mapsto_upd ran_m_mapsto_upd_notin in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff atm_of_eq_atm_of
        dest: imageI[of _ \<open>set UW\<close> atm_of])

  have [simp]: \<open>mset (W x) = clause_to_update x (M, N, D, NE, UE, {#}, {#})\<close>
    if \<open>x \<in># all_lits_of_mm (mset `# ran_mf N)\<close>
    for x
    using that H[of x] i_dom L1 L2
    unfolding all_lits_of_mm_union[symmetric] K
    by (auto split: if_splits simp: clause_to_update_def
        in_all_lits_of_mm_ain_atms_of_iff atm_of_eq_atm_of intro: filter_mset_cong)
  show ?c
    unfolding correct_watching.simps Ball_def
    by (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset
        all_conj_distrib all_lits_of_mm_union)
next
  assume corr: ?c
  have [simp]: \<open>{x. (P x \<longrightarrow> Q x) \<and> P x} = {x. Q x \<and> P x}\<close> for P Q :: \<open>'a \<Rightarrow> bool\<close>
    by auto
  have H[simp]: \<open>{x. x \<noteq> i \<longrightarrow> P x \<and> Q x} = Set.insert i {x. P x \<and> Q x}\<close>
    for P Q :: \<open>nat \<Rightarrow> bool\<close> and i :: nat
    by auto
  have [simp]: \<open>clause_to_update L (K # M, ?N, D, NE, UE, {#}, {#}) =
     clause_to_update L (M, N, D, NE, UE, {#}, {#}) +
     (if L = L1 \<or> L = L2 then {#i#} else {#})\<close>
    for L
    using i_dom
    by (auto simp: clause_to_update_def intro: arg_cong[of _ _ mset_set] filter_mset_cong)
  have K:
    \<open>set_mset (all_lits_of_mm (mset `# ran_mf ?N + NE + UE)) =
       set_mset (all_lits_of_mm (mset `# ran_mf N + NE + UE))\<close>
    using i_dom L1 L2 UW
    by (auto 5 5 simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset
        ran_m_mapsto_upd ran_m_mapsto_upd_notin in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff atm_of_eq_atm_of
        dest: imageI[of _ \<open>set UW\<close> atm_of])
  have
    \<open>L1 \<in># all_lits_of_mm (mset `# ran_mf N + NE)\<close> and
    \<open>-L1 \<in># all_lits_of_mm (mset `# ran_mf N + NE)\<close> and
    \<open>L2 \<in># all_lits_of_mm (mset `# ran_mf N + NE)\<close> and
    \<open>-L2 \<in># all_lits_of_mm (mset `# ran_mf N + NE)\<close>
    using L1 L2 by (auto simp add: in_all_lits_of_mm_ain_atms_of_iff)
  then have [simp]:
    \<open>mset (W L1) = clause_to_update L1 (M, N, D, NE, UE, {#}, {#})\<close>
    \<open>mset (W (- L1)) = clause_to_update (- L1) (M, N, D, NE, UE, {#}, {#})\<close>
    \<open>mset (W L2) = clause_to_update L2 (M, N, D, NE, UE, {#}, {#})\<close>
    \<open>mset (W (- L2)) = clause_to_update (- L2) (M, N, D, NE, UE, {#}, {#})\<close> and
    \<open>x \<in># all_lits_of_mm (mset `# ran_mf N + NE + UE) \<Longrightarrow>
        mset (W x) = clause_to_update x (M, N, D, NE, UE, {#}, {#})\<close> for x
    using corr unfolding K by (auto simp: correct_watching.simps all_lits_of_mm_union)
  have \<open>set_mset (all_lits_of_m (mset UW)) \<subseteq> set_mset (all_lits_of_mm (mset `# ran_mf N + NE))\<close>
    using UW using in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff by blast
  then show ?l
    using corr
    unfolding correct_watching.simps Ball_def K
    by (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset
      all_conj_distrib all_lits_of_mm_union)
qed

fun equality_except_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>equality_except_conflict_wl (M, N, D, NE, UE, WS, Q) (M', N', D', NE', UE', WS', Q') \<longleftrightarrow>
    M = M' \<and> N = N' \<and> NE = NE' \<and> UE = UE' \<and> WS = WS' \<and> Q = Q'\<close>

fun equality_except_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>equality_except_trail_wl (M, N, D, NE, UE, WS, Q) (M', N', D', NE', UE', WS', Q') \<longleftrightarrow>
    N = N' \<and> D = D' \<and> NE = NE' \<and> UE = UE' \<and> WS = WS' \<and> Q = Q'\<close>

lemma equality_except_conflict_wl_get_clauses_wl:
  \<open>equality_except_conflict_wl S Y \<Longrightarrow> get_clauses_wl S = get_clauses_wl Y\<close>
  by (cases S; cases Y) (auto simp:)
lemma equality_except_trail_wl_get_clauses_wl:
 \<open>equality_except_trail_wl S Y\<Longrightarrow> get_clauses_wl S = get_clauses_wl Y\<close>
  by (cases S; cases Y) (auto simp:)

lemma backtrack_wl_spec:
  \<open>(backtrack_wl, backtrack_l)
    \<in> {(T'::'v twl_st_wl, T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and>
          get_conflict_wl T' \<noteq> None \<and>
          get_conflict_wl T' \<noteq> Some {#}} \<rightarrow>
        \<langle>{(T', T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T'}\<rangle>nres_rel\<close>
  (is \<open>?bt \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have extract_shorter_conflict_wl: \<open>extract_shorter_conflict_wl S'
    \<le> \<Down> {(U'::'v twl_st_wl, U).
          (U', U) \<in> state_wl_l None \<and> equality_except_conflict_wl U' S' \<and>
          the (get_conflict_wl U') \<subseteq># the (get_conflict_wl S') \<and>
          get_conflict_wl U' \<noteq> None} (extract_shorter_conflict_l S)\<close>
    (is \<open>_ \<le> \<Down> ?extract _\<close>)
    if  \<open>(S', S) \<in> ?A\<close>
    for S' S L
    apply (cases S'; cases S)
    apply clarify
    unfolding extract_shorter_conflict_wl_def extract_shorter_conflict_l_def
    apply (rule RES_refine)
    using that
    by (auto simp: extract_shorter_conflict_wl_def extract_shorter_conflict_l_def mset_take_mset_drop_mset
        state_wl_l_def)

  have find_decomp_wl: \<open>find_decomp_wl L T'
    \<le> \<Down> {(U'::'v twl_st_wl, U).
          (U', U) \<in> state_wl_l None \<and> equality_except_trail_wl U' T' \<and>
       (\<exists>M. get_trail_wl T' = M @ get_trail_wl U') } (find_decomp L' T)\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    if \<open>(S', S) \<in> ?A\<close> \<open>L = L'\<close> \<open>(T', T) \<in> ?extract S'\<close>
    for S' S T T' L L'
    using that
    apply (cases T; cases T')
    apply clarify
    unfolding find_decomp_wl_def find_decomp_def prod.case
    apply (rule RES_refine)
    apply (auto 5 5 simp add: state_wl_l_def find_decomp_wl_def find_decomp_def)
    done

  have find_lit_of_max_level_wl: \<open>find_lit_of_max_level_wl T' L'
    \<le> \<Down> {(L', L). L = L' \<and> L' \<in># the (get_conflict_wl T')}
         (find_lit_of_max_level T L)\<close>
    (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if \<open>L = L'\<close> \<open>(T', T) \<in> ?find S'\<close>
    for S' S T T' L L'
    using that
    apply (cases T; cases T'; cases S')
    apply clarify
    unfolding find_lit_of_max_level_wl_def find_lit_of_max_level_def prod.case
    apply (rule RES_refine)
    apply (auto simp add: find_lit_of_max_level_wl_def find_lit_of_max_level_def state_wl_l_def
     dest: in_diffD)
    done
  have empty: \<open>literals_to_update_wl S' = {#}\<close> if bt: \<open>backtrack_wl_inv S'\<close> for S'
    using bt apply -
    unfolding backtrack_wl_inv_def backtrack_l_inv_def
    apply normalize_goal+
    apply (auto simp: twl_struct_invs_def)
    done
  have propagate_bt_wl: \<open>propagate_bt_wl (lit_of (hd (get_trail_wl S'))) L' U'
    \<le> \<Down> {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'}
        (propagate_bt_l (lit_of (hd (get_trail_l S))) L U)\<close>
    (is \<open>_ \<le> \<Down> ?propa _\<close>)
    if SS': \<open>(S', S) \<in> ?A\<close> and
     UU': \<open>(U', U) \<in> ?find T'\<close> and
     LL': \<open>(L', L) \<in> ?find_lit U'\<close> and
     TT': \<open>(T', T) \<in> ?extract S'\<close> and
     bt: \<open>backtrack_wl_inv S'\<close>
    for S' S T T' L L' U U'
  proof -
    note empty = empty[OF bt]
    define K' where \<open>K' = lit_of (hd (get_trail_l S))\<close>
    obtain MS NS DS NES UES W where
      S': \<open>S' = (MS, NS, Some DS, NES, UES, {#}, W)\<close>
      using SS' empty by (cases S'; cases \<open>get_conflict_wl S'\<close>) auto
    then obtain DT where
      T': \<open>T' = (MS, NS, Some DT, NES, UES, {#}, W)\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU MU' where
      U': \<open>U' = (MU, NS, Some DT, NES, UES, {#}, W)\<close> and
      MU: \<open>MS = MU' @ MU\<close> and
      U'U: \<open>(U', U) \<in> state_wl_l None\<close>
      using UU' by (cases U') auto
    then have U: \<open>U = (MU, NS, Some DT, NES, UES, {#}, {#})\<close>
      by (cases U) (auto simp: state_wl_l_def)
    have MS: \<open>MS \<noteq> []\<close>
      using bt unfolding backtrack_wl_inv_def backtrack_l_inv_def S' by (auto simp: state_wl_l_def)
    have \<open>correct_watching S'\<close>
      using SS' by fast
    then have corr: \<open>correct_watching (MU, NS, None, NES, UES, {#K'#}, W)\<close>
       unfolding S' correct_watching.simps clause_to_update_def get_clauses_l.simps .
    have K_hd[simp]: \<open>lit_of (hd MS) = K'\<close>
      using SS' unfolding K'_def by (auto simp: S')
    have [simp]: \<open>L = L'\<close>
      using LL' by auto
    have trail_no_alien:
       \<open>atm_of ` lits_of_l (get_trail_wl S')
           \<subseteq> atms_of_ms
              ((\<lambda>x. mset (fst x)) `
               {a. a \<in># ran_m (get_clauses_wl S') \<and> snd a}) \<union>
             atms_of_mm (get_unit_init_clss_wl S')\<close> and
       no_alien: \<open>atms_of DS \<subseteq> atms_of_ms
                  ((\<lambda>x. mset (fst x)) `
                   {a. a \<in># ran_m (get_clauses_wl S') \<and> snd a}) \<union>
                 atms_of_mm (get_unit_init_clss_wl S')\<close>
      using SS' bt unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        backtrack_wl_inv_def backtrack_l_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      apply -
      apply normalize_goal+
      apply (simp add: twl_st twl_st_l twl_st_wl)
      apply normalize_goal+
      apply (simp add: twl_st twl_st_l twl_st_wl S')
      done
    moreover have \<open>L' \<in># DS\<close>
      using LL' TT'  by (auto simp: T' S' U' mset_take_mset_drop_mset)
    ultimately have
       atm_L': \<open>atm_of L' \<in> atms_of_mm (mset `# init_clss_lf NS + NES)\<close> and
       atm_confl: \<open>\<forall>L\<in>#DS. atm_of L \<in> atms_of_mm (mset `# init_clss_lf NS + NES)\<close>
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state S'
          mset_take_mset_drop_mset dest!: atm_of_lit_in_atms_of)
    have atm_K': \<open>atm_of K' \<in> atms_of_mm (mset `# init_clss_lf NS + NES)\<close>
      using trail_no_alien K_hd MS
      by (cases MS) (auto simp: S'
          mset_take_mset_drop_mset simp del:  K_hd dest!: atm_of_lit_in_atms_of)
    have fresh: \<open>get_fresh_index N \<le> \<Down> {(i, i'). i = i' \<and> i \<notin># dom_m N} (get_fresh_index N')\<close>
       if \<open>N = N'\<close> for N N'
       unfolding that get_fresh_index_def by (auto intro: RES_refine)
    show ?thesis
      unfolding propagate_bt_wl_def propagate_bt_l_def S' T' U' U st_l_of_wl.simps get_trail_wl.simps
      list_of_mset_def K'_def[symmetric]
      apply (refine_vcg fresh; remove_dummy_vars)
      apply simp
      apply (subst correct_watching_learn)
      subgoal using atm_K' unfolding all_clss_lf_ran_m[symmetric] image_mset_union by auto
      subgoal using atm_L' unfolding all_clss_lf_ran_m[symmetric] image_mset_union by auto
      subgoal using atm_confl TT'  unfolding all_clss_lf_ran_m[symmetric] image_mset_union
        by (fastforce simp: S' T' dest!: in_atms_of_minusD)
      subgoal by auto
      subgoal using SS' by (auto simp: corr state_wl_l_def S')
      done
  qed

  have propagate_unit_bt_wl: \<open>(propagate_unit_bt_wl (lit_of (hd (get_trail_wl S'))) U',
     propagate_unit_bt_l (lit_of (hd (get_trail_l S))) U)
    \<in> {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T'} \<close>
    (is \<open>(_, _) \<in> ?propagate_unit_bt_wl _\<close>)
    if
     SS': \<open>(S', S) \<in> ?A\<close> and
     TT': \<open>(T', T) \<in> ?extract S'\<close> and
     UU': \<open>(U', U) \<in> ?find T'\<close> and
     bt: \<open>backtrack_wl_inv S'\<close>
    for S' S T T' L L' U U' K'
  proof -
    obtain MS NS DS NES UES W where
      S': \<open>S' = (MS, NS, Some DS, NES, UES, {#}, W)\<close>
      using SS' UU' empty[OF bt] by (cases S'; cases \<open>get_conflict_wl S'\<close>) auto
    then obtain DT where
      T': \<open>T' = (MS, NS, Some DT, NES, UES, {#}, W)\<close> and
      DT_DS: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    have T: \<open>T = (MS, NS, Some DT, NES, UES, {#}, {#})\<close>
      using TT' by (auto simp: S' T' state_wl_l_def)
    obtain MU MU' where
      U': \<open>U' = (MU, NS, Some DT, NES, UES, {#}, W)\<close> and
      MU: \<open>MS = MU' @ MU\<close> and
      U: \<open>(U', U) \<in> state_wl_l None\<close>
      using UU' T' by (cases U') auto
    have U: \<open>U = (MU, NS, Some DT, NES, UES, {#}, {#})\<close>
      using UU' by (auto simp: U' state_wl_l_def)
    obtain S1 S2 where
      S1: \<open>(S', S1) \<in> state_wl_l None\<close> and
      S2: \<open>(S1, S2) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs S2\<close>
      using bt unfolding backtrack_wl_inv_def backtrack_l_inv_def
      by blast
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S2)\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then have K: \<open>set_mset (all_lits_of_mm (mset `# ran_mf NS + NES + add_mset (the (Some DT)) UES)) =
      set_mset (all_lits_of_mm (mset `# ran_mf NS + NES + UES))\<close>
      apply (subst all_clss_lf_ran_m[symmetric])+
      apply (subst image_mset_union)+
      using S1 S2 atms_of_subset_mset_mono[OF DT_DS]
      by (fastforce simp: all_lits_of_mm_union all_lits_of_mm_add_mset state_wl_l_def
        twl_st_l_def S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        mset_take_mset_drop_mset' in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff)
    have \<open>correct_watching S'\<close>
      using SS' by fast
    then have corr: \<open>correct_watching (Propagated (- lit_of (hd MS)) 0 # MU, NS, None, NES,
      add_mset (the (Some DT)) UES, unmark (hd MS), W)\<close>
       unfolding S' correct_watching.simps clause_to_update_def get_clauses_l.simps K .

    show ?thesis
      unfolding propagate_unit_bt_wl_def propagate_unit_bt_l_def S' T' U U'
        st_l_of_wl.simps get_trail_wl.simps list_of_mset_def
      apply clarify
      apply (refine_rcg)
      subgoal using SS' by (auto simp: S' state_wl_l_def)
      subgoal by (rule corr)
      done
  qed
  show ?thesis
    unfolding st_l_of_wl.simps get_trail_wl.simps list_of_mset_def
      backtrack_wl_def backtrack_l_def
     apply (refine_vcg find_decomp_wl find_lit_of_max_level_wl extract_shorter_conflict_wl
         propagate_bt_wl propagate_unit_bt_wl;
        remove_dummy_vars)
    subgoal using backtrack_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


subsubsection \<open>Backtrack, Skip, Resolve or Decide\<close>

definition cdcl_twl_o_prog_wl_pre where
  \<open>cdcl_twl_o_prog_wl_pre S \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
        correct_watching S \<and>
        cdcl_twl_o_prog_l_pre S')\<close>

definition cdcl_twl_o_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>cdcl_twl_o_prog_wl S =
    do {
      ASSERT(cdcl_twl_o_prog_wl_pre S);
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
     (S, S') \<in> state_wl_l None \<and>
     correct_watching S} \<rightarrow>\<^sub>f
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     (T, T') \<in> state_wl_l None \<and>
     brk = brk' \<and>
     correct_watching T}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S \<le> \<Down> Id (find_unassigned_lit_l S')\<close>
    if \<open>(S, S') \<in> state_wl_l None\<close>
    for S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
    unfolding find_unassigned_lit_wl_def find_unassigned_lit_l_def
    using that
    by (cases S; cases S') (auto simp: state_wl_l_def)
  have [iff]: \<open>correct_watching (decide_lit_wl L S) \<longleftrightarrow> correct_watching S\<close> for L S
    by (cases S; auto simp: decide_lit_wl_def correct_watching.simps clause_to_update_def)
  have [iff]: \<open>(decide_lit_wl L S, decide_lit_l L S') \<in> state_wl_l None\<close>
    if \<open>(S, S') \<in> state_wl_l None\<close>
    for L S S'
    using that by (cases S; auto simp: decide_lit_wl_def decide_lit_l_def state_wl_l_def)
  have option_id: \<open>x = x' \<Longrightarrow> (x,x') \<in> \<langle>Id\<rangle>option_rel\<close> for x x' by auto
  show cdcl_o: \<open>?o \<in> ?A \<rightarrow>\<^sub>f
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     (T, T') \<in> state_wl_l None \<and>
     brk = brk' \<and>
     correct_watching T}\<rangle>nres_rel\<close>
    unfolding cdcl_twl_o_prog_wl_def cdcl_twl_o_prog_l_def decide_wl_or_skip_def
      decide_l_or_skip_def fref_param1[symmetric]
    apply (refine_vcg skip_and_resolve_loop_wl_spec["to_\<Down>"] backtrack_wl_spec["to_\<Down>"]
      find_unassigned_lit_wl option_id)
    subgoal unfolding cdcl_twl_o_prog_wl_pre_def by blast
    subgoal by auto
    subgoal unfolding decide_wl_or_skip_pre_def by blast
    subgoal by (auto simp:)
    subgoal unfolding decide_wl_or_skip_pre_def by auto
    subgoal by auto
    subgoal by (auto simp: )
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: )
    subgoal by (auto simp: )
    subgoal by auto
    done
qed


subsubsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl  \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_prog_wl_inv S\<^sub>0 \<equiv> \<lambda>(brk, T).
      (\<exists> T' S\<^sub>0'.  (T, T') \<in> state_wl_l None \<and>
      (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
      cdcl_twl_stgy_prog_l_inv S\<^sub>0' (brk, T'))\<close>

definition cdcl_twl_stgy_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_stgy_prog_wl S\<^sub>0 =
  do {
    (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_prog_wl_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S). do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        cdcl_twl_o_prog_wl T
      })
      (False, S\<^sub>0);
    RETURN T
  }\<close>


theorem cdcl_twl_stgy_prog_wl_spec:
  \<open>(cdcl_twl_stgy_prog_wl, cdcl_twl_stgy_prog_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and>
       correct_watching S} \<rightarrow>
    \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S'), False, S) \<in> {((brk', T'), (brk, T)). (T', T) \<in> state_wl_l None \<and> brk' = brk \<and>
       correct_watching T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto
    thm unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_def cdcl_twl_stgy_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_prog_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' by auto
    subgoal by fast
    subgoal by auto
    done
qed

theorem cdcl_twl_stgy_prog_wl_spec':
  \<open>(cdcl_twl_stgy_prog_wl, cdcl_twl_stgy_prog_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>
    \<langle>{(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S'), False, S) \<in> {((brk', T'), (brk, T)). (T', T) \<in> state_wl_l None \<and> brk' = brk \<and>
       correct_watching T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto
    thm unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_def cdcl_twl_stgy_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_prog_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' by auto
    subgoal by fast
    subgoal by auto
    done
qed

definition cdcl_twl_stgy_prog_wl_pre where
  \<open>cdcl_twl_stgy_prog_wl_pre S U \<longleftrightarrow>
    (\<exists>T. (S, T) \<in> state_wl_l None \<and> cdcl_twl_stgy_prog_l_pre T U \<and> correct_watching S)\<close>

lemma cdcl_twl_stgy_prog_wl_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  obtain T where T: \<open>(S, T) \<in> state_wl_l None\<close> \<open>cdcl_twl_stgy_prog_l_pre T S'\<close> \<open>correct_watching S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_wl_spec["to_\<Down>", of S T]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_l_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by auto
      done
    done
qed


definition cdcl_twl_stgy_prog_break_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_stgy_prog_break_wl S\<^sub>0 =
  do {
    b \<leftarrow> SPEC(\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, S). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 S\<^esup>
      (\<lambda>(b, brk, _). b \<and> \<not>brk)
      (\<lambda>(_, brk, S). do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        T \<leftarrow> cdcl_twl_o_prog_wl T;
        b \<leftarrow> SPEC(\<lambda>_. True);
        RETURN (b, T)
      })
      (b, False, S\<^sub>0);
    if brk then RETURN T
    else cdcl_twl_stgy_prog_wl T
  }\<close>

theorem cdcl_twl_stgy_prog_break_wl_spec':
  \<open>(cdcl_twl_stgy_prog_break_wl, cdcl_twl_stgy_prog_break_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
    \<langle>{(S::'v twl_st_wl, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((b', False, S'), b, False, S) \<in> {((b', brk', T'), (b, brk, T)).
      (T', T) \<in> state_wl_l None \<and> brk' = brk \<and> b' = b \<and>
       correct_watching T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close> and
       \<open>(b', b) \<in> bool_rel\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close> and b' b :: bool
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_prog_break_wl_def cdcl_twl_stgy_prog_break_l_def fref_param1[symmetric]
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down]
      cdcl_twl_stgy_prog_wl_spec'[unfolded fref_param1, THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_prog_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
    done
qed


theorem cdcl_twl_stgy_prog_break_wl_spec:
  \<open>(cdcl_twl_stgy_prog_break_wl, cdcl_twl_stgy_prog_break_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and>
       correct_watching S} \<rightarrow>\<^sub>f
    \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_prog_break_wl_spec'
  apply -
  apply (rule mem_set_trans)
  prefer 2 apply assumption
  apply (match_fun_rel, solves simp)
  apply (match_fun_rel; solves auto)
  done

lemma cdcl_twl_stgy_prog_break_wl_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_break_wl S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  obtain T where T: \<open>(S, T) \<in> state_wl_l None\<close> \<open>cdcl_twl_stgy_prog_l_pre T S'\<close> \<open>correct_watching S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_break_wl_spec[unfolded fref_param1[symmetric], "to_\<Down>", of S T]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_break_l_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by auto
      done
    done
qed

end
