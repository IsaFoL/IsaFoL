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

lemma correct_watching_except_correct_watching:
  assumes
    j: \<open>j \<ge> length (W K)\<close> and
    corr: \<open>correct_watching_except i j K (M, N, D, NE, UE, Q, W)\<close>
 shows \<open>correct_watching (M, N, D, NE, UE, Q, W(K := take i (W K)))\<close>
proof -
  have
    bl: \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W)\<close> and
    H1: \<open>\<And>L i' K'. L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<Longrightarrow>
       (L =K \<Longrightarrow>
         (((i', K')\<in>#mset (take i (W L) @ drop j (W L)) \<longrightarrow> i' \<in># dom_m N \<longrightarrow> K' \<in> set (N \<propto> i') \<and> K' \<noteq> L) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (take i (W L) @ drop j (W L))) =
            clause_to_update L (M, N, D, NE, UE, {#}, {#})))\<close> and
    H2: \<open>\<And>L i K'. L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<Longrightarrow> (L \<noteq> K \<Longrightarrow>
         (((i, K')\<in>#mset (W L) \<longrightarrow> i \<in># dom_m N \<longrightarrow> K' \<in> set (N \<propto> i) \<and> K' \<noteq> L) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) =
             clause_to_update L (M, N, D, NE, UE, {#}, {#})))\<close>
    using corr unfolding correct_watching_except.simps
    by blast+
  show ?thesis
    unfolding correct_watching.simps
    apply (intro conjI allI impI ballI)
    subgoal
      using bl j by (auto simp: all_blits_are_in_problem.simps
          dest!: multi_member_split in_set_takeD)
    subgoal for L x
      apply (cases \<open>L = K\<close>)
      subgoal
        using H1[of L \<open>fst x\<close> \<open>snd x\<close>] j
        by (auto split: if_splits)
      subgoal
        using H2[of L \<open>fst x\<close> \<open>snd x\<close>]
        by auto
      done
    subgoal for L
      apply (cases \<open>L = K\<close>)
      subgoal
        using H1[of L _ _] j
        by (auto split: if_splits)
      subgoal
        using H2[of L _ _]
        by auto
      done
    done
qed

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

declare correct_watching_except.simps[simp del]

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
\<open>unit_prop_body_wl_inv T j i C L \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T) \<longrightarrow>
    (\<exists>T'. (T, T') \<in> state_wl_l (Some (L, i)) \<and>
    unit_propagation_inner_loop_body_l_inv L (fst (watched_by T L ! i))
       (remove_one_lit_from_wq (fst (watched_by T L ! i)) T')\<and>
    L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl T) + get_unit_clauses_wl T) \<and>
    correct_watching_except j i L T \<and>
    i < length (watched_by T L) \<and>
    get_conflict_wl T = None))\<close>

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


definition update_blit_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>update_blit_wl = (\<lambda>(L::'v literal) C j w K (M, N,  D, NE, UE, Q, W). do {
     RETURN (j+1, w+1, (M, N, D, NE, UE, Q, W(L := W L[j:=(C, K)])))
  })\<close>


definition unit_prop_body_wl_find_unwatched_inv where
\<open>unit_prop_body_wl_find_unwatched_inv f C S \<longleftrightarrow>
   get_clauses_wl S \<propto> C \<noteq> [] \<and>
   (f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S \<propto> C)). - L \<in> lits_of_l (get_trail_wl S)))\<close>

abbreviation remaining_nondom_wl where
\<open>remaining_nondom_wl w L S \<equiv>
  (if get_conflict_wl S = None
          then size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl S)) (mset (drop w (watched_by S L)))) else 0)\<close>

definition unit_propagation_inner_loop_wl_loop_inv where
  \<open>unit_propagation_inner_loop_wl_loop_inv L = (\<lambda>(j, w, S).
    (\<exists>S'. (S, S') \<in> state_wl_l (Some (L, w)) \<and>
       unit_propagation_inner_loop_l_inv L (S', remaining_nondom_wl w L S) \<and>
      correct_watching_except j w L S \<and> w \<le> length (watched_by S L)))\<close>

lemma correct_watching_except_correct_watching_except_Suc_Suc_keep_watch:
  assumes
    j_w: \<open>j \<le> w\<close> and
    w_le: \<open>w < length (watched_by S L)\<close> and
    corr: \<open>correct_watching_except j w L S\<close>
  shows \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
proof -
  obtain M N D NE UE Q W where S: \<open>S = (M, N, D, NE, UE, Q, W)\<close> by (cases S)
  have
    all_blits: \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W)\<close> and
    Hneq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
        (La \<noteq> L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset (W La). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (W La). i \<in># dom_m N#} = clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close> and
    Heq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
        (La = L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset (take j (W La) @ drop w (W La)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (take j (W La) @ drop w (W La)). i \<in># dom_m N#} =
         clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close>
    using corr unfolding S correct_watching_except.simps
    by blast+

  have eq: \<open>mset (take (Suc j) ((W(L := W L[j := W L ! w])) La) @ drop (Suc w) ((W(L := W L[j := W L ! w])) La)) =
     mset (take j (W La) @ drop w (W La))\<close> if [simp]: \<open>La = L\<close> for La
    using w_le j_w
    by (auto simp: S take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
        list_update_append)

  have \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W(L := W L[j := W L ! w]))\<close>
    using all_blits j_w w_le nth_mem_mset[of w \<open>W L\<close>] unfolding all_blits_are_in_problem.simps
    apply (auto dest!: multi_member_split[of L] simp: S simp del: nth_mem)
    apply (subst (asm)in_set_upd_eq_aux)
     apply (simp add: S; fail)
    apply (auto simp del: nth_mem)
    using S nth_mem_mset[of j \<open>W L\<close>]
    by (metis (mono_tags) case_prod_conv in_set_upd_cases)
  moreover have \<open>case x of (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La = L\<close> and
      \<open>x \<in># mset (take (Suc j) ((W(L := W L[j := W L ! w])) La) @
                 drop (Suc w) ((W(L := W L[j := W L ! w])) La))\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal\<close>
    using that Heq[of L]
    apply (subst (asm) eq)
    by (simp_all add: eq)
  moreover have \<open>{#i \<in># fst `#
              mset
               (take (Suc j) ((W(L := W L[j := W L ! w])) La) @
                drop (Suc w) ((W(L := W L[j := W L ! w])) La)).
       i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, {#}, {#})\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La = L\<close>
    for La :: \<open>'a literal\<close>
    using that Heq[of L]
    by (subst eq) simp_all
  moreover have \<open>case x of (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La \<noteq> L\<close> and
      \<open>x \<in># mset ((W(L := W L[j := W L ! w])) La)\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>{#i \<in># fst `# mset ((W(L := W L[j := W L ! w])) La). i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, {#}, {#})\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La \<noteq> L\<close>
    for La :: \<open>'a literal\<close>
    using that Hneq[of La]
    by simp
  ultimately show ?thesis
    unfolding S keep_watch_def prod.simps correct_watching_except.simps
    by blast
qed

lemma correct_watching_except_update_blit:
  assumes
    corr: \<open>correct_watching_except i j L (a, b, c, d, e, f, g(L := g L[j' := (x1, C)]))\<close> and
    C': \<open>C' \<in># all_lits_of_mm (mset `# ran_mf b + (d + e))\<close>
      \<open>C' \<in> set (b \<propto> x1)\<close>
      \<open>C' \<noteq> L\<close>
  shows \<open>correct_watching_except i j L (a, b, c, d, e, f, g(L := g L[j' := (x1, C')]))\<close>
proof -
  have
    all_bl: \<open>\<And>La i K. La\<in>#all_lits_of_mm (mset `# ran_mf b + (d + e)) \<Longrightarrow>
     (i, K)\<in>#mset ((g(L := g L[j' := (x1, C)])) La) \<Longrightarrow>
        K \<in># all_lits_of_mm (mset `# ran_mf b + (d + e))\<close> and
    Heq: \<open>\<And>La i' K'. La\<in>#all_lits_of_mm (mset `# ran_mf b + (d + e)) \<Longrightarrow>
        (La = L \<longrightarrow>
         ((i', K')\<in>#mset (take i ((g(L := g L[j' := (x1, C)])) La) @ drop j ((g(L := g L[j' := (x1, C)])) La)) \<longrightarrow>
             i' \<in># dom_m b \<longrightarrow> K' \<in> set (b \<propto> i') \<and> K' \<noteq> La) \<and>
         {#i \<in># fst `# mset (take i ((g(L := g L[j' := (x1, C)])) La) @ drop j ((g(L := g L[j' := (x1, C)])) La)).
          i \<in># dom_m b#} =
         clause_to_update La (a, b, c, d, e, {#}, {#}))\<close> and
    Hneq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf b + (d + e)) \<Longrightarrow> (La \<noteq> L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset ((g(L := g L[j' := (x1, C)])) La). i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset ((g(L := g L[j' := (x1, C)])) La). i \<in># dom_m b#} =
            clause_to_update La (a, b, c, d, e, {#}, {#}))\<close>
    using corr unfolding correct_watching_except.simps all_blits_are_in_problem.simps
    by blast+
  define g' where \<open>g' = g(L := g L[j' := (x1, C)])\<close>
  have g_g': \<open>g(L := g L[j' := (x1, C')]) =  g'(L := g' L[j' := (x1, C')])\<close>
    unfolding g'_def by auto

  have blits: \<open>all_blits_are_in_problem (a, b, c, d, e, f, g(L := g L[j' := (x1, C')]))\<close>
    unfolding all_blits_are_in_problem.simps g_g'
    apply (intro conjI impI ballI)
    subgoal for La x
      using all_bl[of La \<open>fst x\<close> \<open>snd x\<close>] C' unfolding g'_def[symmetric]
      by (auto split: if_splits simp: elim!: in_set_upd_cases)
    done
  have H2: \<open>fst `# mset ((g'(L := g' L[j' := (x1, C')])) La) = fst `# mset (g' La)\<close> for La
    unfolding g'_def
    by (auto simp flip: mset_map simp: map_update)
  have H3: \<open>fst `#
                 mset
                  (take i ((g'(L := g' L[j' := (x1, C')])) La) @
                   drop j ((g'(L := g' L[j' := (x1, C')])) La)) =
      fst `#
                 mset
                  (take i (g' La) @
                   drop j (g' La))\<close> for La
    unfolding g'_def
    by (auto simp flip: mset_map drop_map simp: map_update)
  have [simp]:
    \<open>fst `# mset (take i (g' L)[j' := (x1, C')]) = fst `# mset (take i (g' L))\<close>
    \<open>fst `# mset (drop j ((g' L)[j' := (x1, C')])) = fst `# mset (drop j (g' L))\<close>
    \<open>\<not>j' < j \<Longrightarrow> fst `# mset (drop j (g' L)[j' - j := (x1, C')]) = fst `# mset (drop j (g' L))\<close>
    unfolding g'_def
      apply (auto simp flip: mset_map drop_map simp: map_update drop_update_swap; fail)
     apply (auto simp flip: mset_map drop_map simp: map_update drop_update_swap; fail)
    apply (auto simp flip: mset_map drop_map simp: map_update drop_update_swap; fail)
    done

  have \<open>La\<in>#all_lits_of_mm (mset `# ran_mf b + (d + e)) \<Longrightarrow>
        (La = L \<longrightarrow>
         ((i', K)\<in>#mset (take i ((g'(L := g' L[j' := (x1, C')])) La) @ drop j ((g'(L := g' L[j' := (x1, C')])) La)) \<longrightarrow>
             i' \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i') \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (take i ((g'(L := g' L[j' := (x1, C')])) La) @ drop j ((g'(L := g' L[j' := (x1, C')])) La)).
          i \<in># dom_m b#} =
         clause_to_update La (a, b, c, d, e, {#}, {#}))\<close> for La i' K
    using C' Heq[of La i' K] unfolding  g_g'  g'_def[symmetric]
    by (cases \<open>j' < j\<close>)
     (auto elim!: in_set_upd_cases simp: drop_update_swap)

  then show ?thesis
    using Hneq blits
    unfolding correct_watching_except.simps g_g'  g'_def[symmetric]
    unfolding H2 H3
    by fastforce
qed

lemma correct_watching_except_correct_watching_except_Suc_notin:
  assumes
    \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S)\<close> and
    j_w: \<open>j \<le> w\<close> and
    w_le: \<open>w < length (watched_by S L)\<close> and
    corr: \<open>correct_watching_except j w L S\<close>
  shows \<open>correct_watching_except j (Suc w) L (keep_watch L j w S)\<close>
proof -
  obtain M N D NE UE Q W where S: \<open>S = (M, N, D, NE, UE, Q, W)\<close> by (cases S)
  have [simp]: \<open>fst (W L ! w) \<notin># dom_m N\<close>
    using assms unfolding S by auto
  have
    all_blits: \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W)\<close> and
    Hneq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
        (La \<noteq> L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset (W La). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (W La). i \<in># dom_m N#} = clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close> and
    Heq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
        (La = L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset (take j (W La) @ drop w (W La)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (take j (W La) @ drop w (W La)). i \<in># dom_m N#} =
         clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close>
    using corr unfolding S correct_watching_except.simps
    by blast+

  have eq: \<open>mset (take j ((W(L := W L[j := W L ! w])) La) @ drop (Suc w) ((W(L := W L[j := W L ! w])) La)) =
    remove1_mset (W L ! w) (mset (take j (W La) @ drop w (W La)))\<close> if [simp]: \<open>La = L\<close> for La
    using w_le j_w
    by (auto simp: S take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
        list_update_append)

  have \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W(L := W L[j := W L ! w]))\<close>
    using all_blits j_w w_le nth_mem_mset[of w \<open>W L\<close>] unfolding all_blits_are_in_problem.simps
    apply (auto dest!: multi_member_split[of L] simp: S simp del: nth_mem)
    apply (subst (asm)in_set_upd_eq_aux)
     apply (simp add: S; fail)
    apply (auto simp del: nth_mem)
    using S nth_mem_mset[of j \<open>W L\<close>]
    by (metis (mono_tags) case_prod_conv in_set_upd_cases)
  moreover have \<open>case x of (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La = L\<close> and
      \<open>x \<in># mset (take j ((W(L := W L[j := W L ! w])) La) @
                 drop (Suc w) ((W(L := W L[j := W L ! w])) La))\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal\<close>
    using that Heq[of L] w_le j_w
    by (subst (asm) eq) (auto dest!: in_diffD)
  moreover have \<open>{#i \<in># fst `#
              mset
               (take j ((W(L := W L[j := W L ! w])) La) @
                drop (Suc w) ((W(L := W L[j := W L ! w])) La)).
       i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, {#}, {#})\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La = L\<close>
    for La :: \<open>'a literal\<close>
    using that Heq[of L] w_le j_w
    by (subst eq) (auto dest!: in_diffD simp: image_mset_remove1_mset_if)
  moreover have \<open>case x of (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La \<noteq> L\<close> and
      \<open>x \<in># mset ((W(L := W L[j := W L ! w])) La)\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>{#i \<in># fst `# mset ((W(L := W L[j := W L ! w])) La). i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, {#}, {#})\<close>
    if
      \<open>La \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close> and
      \<open>La \<noteq> L\<close>
    for La :: \<open>'a literal\<close>
    using that Hneq[of La]
    by simp
  ultimately show ?thesis
    unfolding S keep_watch_def prod.simps correct_watching_except.simps
    by blast
qed

lemma correct_watching_except_correct_watching_except_update_clause:
  assumes
    corr: \<open>correct_watching_except (Suc j) (Suc w) L
       (M, N, D, NE, UE, Q, W(L := W L[j := W L ! w]))\<close> and
    j_w: \<open>j \<le> w\<close> and
    w_le: \<open>w < length (W L)\<close> and
    L': \<open>L' \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))\<close>
      \<open>L' \<in> set (N \<propto> x1)\<close>and
    L: \<open>L \<noteq> N \<propto> x1 ! xa\<close> and
    dom: \<open>x1 \<in># dom_m N\<close> and
    i_xa: \<open>i < length (N \<propto> x1)\<close> \<open>xa < length (N \<propto> x1)\<close> and
    [simp]: \<open>W L ! w = (x1, x2)\<close> and
    N_i: \<open>N \<propto> x1 ! i = L\<close> \<open>N \<propto> x1 ! (1 -i) \<noteq> L\<close>\<open>N \<propto> x1 ! xa \<noteq> L\<close> and
    N_xa: \<open>N \<propto> x1 ! xa \<noteq> N \<propto> x1 ! i\<close> \<open>N \<propto> x1 ! xa \<noteq> N \<propto> x1 ! (Suc 0 - i)\<close>and
    i_2: \<open>i < 2\<close> and \<open>xa \<ge> 2\<close> and
    L_neq: \<open>L' \<noteq> N \<propto> x1 ! xa\<close> \<comment>\<open>The new blocking literal is not the new watched literal.\<close>
  shows \<open>correct_watching_except j (Suc w) L
          (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, Q, W
           (L := W L[j := (x1, x2)],
            N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L')]))\<close>
proof -
  define W' where \<open>W' \<equiv> W(L := W L[j := W L ! w])\<close>
  have
    blits: \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W')\<close> and
    Heq: \<open>\<And>La i K. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<Longrightarrow>
          (La = L \<longrightarrow>
           ((i, K)\<in>#mset (take (Suc j) (W' La) @
                            drop (Suc w) (W' La)) \<longrightarrow>
               i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
           {#i \<in># fst `#
                   mset
                    (take (Suc j) (W' La) @ drop (Suc w) (W' La)).
            i \<in># dom_m N#} =
           clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close> and
    Hneq: \<open>\<And>La i K. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<Longrightarrow>
          (La \<noteq> L \<longrightarrow>
           ((i, K)\<in>#mset (W' La) \<longrightarrow>
               i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
           {#i \<in># fst `# mset (W' La). i \<in># dom_m N#} =
           clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close> and
    Hneq2: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<Longrightarrow>
          (La \<noteq> L \<longrightarrow>
           {#i \<in># fst `# mset (W' La). i \<in># dom_m N#} =
           clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close>
    using corr unfolding correct_watching_except.simps W'_def[symmetric]
    by blast+
  have H1: \<open>mset `# ran_mf (N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa)) = mset `# ran_mf N\<close>
    using dom i_xa distinct_mset_dom[of N]
    by (auto simp: ran_m_def dest!: multi_member_split intro!: image_mset_cong2)
  have W_W': \<open>W
      (L := W L[j := (x1, x2)], N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L')]) =
     W'(N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L')])\<close>
    unfolding W'_def
    by auto
  have W_W2: \<open>W (N \<propto> x1 ! xa) = W' (N \<propto> x1 ! xa)\<close>
    using L unfolding W'_def by auto
  have all_blits: \<open>all_blits_are_in_problem
     (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, Q, W
      (L := W L[j := (x1, x2)], N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L')]))\<close>
    using blits L' L unfolding all_blits_are_in_problem.simps H1 W'_def[symmetric] W_W'
    by (subst W_W2)
       (auto dest!: multi_member_split simp: add_mset_eq_add_mset
        elim!: in_set_upd_cases)
  have H2: \<open>set (swap (N \<propto> x1) i xa) =  set (N \<propto> x1)\<close>
    using i_xa by auto
  have [simp]:
    \<open>set (fst (the (if x1 = ia then Some (swap (N \<propto> x1) i xa, irred N x1) else fmlookup N ia))) =
     set (fst (the (fmlookup N ia)))\<close> for ia
    using H2
    by auto
  have H3: \<open>i = x1 \<or> i \<in># remove1_mset x1 (dom_m N) \<longleftrightarrow> i \<in># dom_m N\<close> for i
    using dom by (auto dest: multi_member_split)
  have set_N_swap_x1: \<open>set (watched_l (swap (N \<propto> x1) i xa)) = {N \<propto> x1 ! (1 -i), N \<propto> x1 ! xa}\<close>
    using i_2 i_xa \<open>xa \<ge> 2\<close> N_i
    by (cases \<open>N \<propto> x1\<close>; cases \<open>tl (N \<propto> x1)\<close>; cases i; cases \<open>i-1\<close>; cases xa)
      (auto simp: swap_def split: nat.splits)
  have set_N_x1: \<open>set (watched_l (N \<propto> x1)) = {N \<propto> x1 ! (1 -i), N \<propto> x1 ! i}\<close>
    using i_2 i_xa \<open>xa \<ge> 2\<close> N_i
    by (cases i) (auto simp: swap_def take_2_if)

  have La_in_notin_swap:  \<open>La \<in> set (watched_l (N \<propto> x1)) \<Longrightarrow>
       La \<notin> set (watched_l (swap (N \<propto> x1) i xa)) \<Longrightarrow> La = L\<close> for La
    using i_2 i_xa \<open>xa \<ge> 2\<close> N_i
    by (auto simp: set_N_x1 set_N_swap_x1)

  have L_notin_swap: \<open>L \<notin> set (watched_l (swap (N \<propto> x1) i xa))\<close>
    using i_2 i_xa \<open>xa \<ge> 2\<close> N_i
    by (auto simp: set_N_x1 set_N_swap_x1)
  have N_xa_in_swap: \<open>N \<propto> x1 ! xa \<in> set (watched_l (swap (N \<propto> x1) i xa))\<close>
    using i_2 i_xa \<open>xa \<ge> 2\<close> N_i
    by (auto simp: set_N_x1 set_N_swap_x1)
  have H4: \<open>(i = x1 \<longrightarrow> K \<in> set (N \<propto> x1) \<and> K \<noteq> La) \<and> (i \<in># remove1_mset x1 (dom_m N) \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<longleftrightarrow>
   (i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La)\<close> for i P K La
    using dom by (auto dest: multi_member_split)
  have [simp]: \<open>x1 \<notin># Ab \<Longrightarrow>
       {#C \<in># Ab.
        (x1 = C \<longrightarrow> Q C) \<and>
        (x1 \<noteq> C \<longrightarrow> R C)#} =
     {#C \<in># Ab. R C#}\<close> for Ab Q R
    by (auto intro: filter_mset_cong)

  have \<open> L \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE)) \<Longrightarrow> La = L \<Longrightarrow>
       x \<in> set (take j (W L)) \<or> x \<in> set (drop (Suc w) (W L)) \<Longrightarrow>
       case x of (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L\<close> for La x
    using Heq[of L \<open>fst x\<close> \<open>snd x\<close>] j_w  w_le
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append)
  moreover have \<open>L \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE)) \<Longrightarrow>
          La = L \<Longrightarrow>
          {#i \<in># fst `# mset (take j (W L)). i \<in># dom_m N#} + {#i \<in># fst `# mset (drop (Suc w) (W L)). i \<in># dom_m N#} =
          clause_to_update L (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, {#}, {#})\<close> for La
    using Heq[of L x1 x2] j_w  w_le dom  L_notin_swap N_xa_in_swap distinct_mset_dom[of N]
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append set_N_x1 assms(11)
        clause_to_update_def dest!: multi_member_split split: if_splits
        intro: filter_mset_cong2)
   moreover have \<open>La \<in># all_lits_of_mm
               ({#mset (fst x). x \<in># ran_m N#} + (NE + UE)) \<Longrightarrow>
       La \<noteq> L \<Longrightarrow>
       x \<in> set (if La = N \<propto> x1 ! xa
                 then W' (N \<propto> x1 ! xa) @ [(x1, L')]
                 else (W(L := W L[j := (x1, x2)])) La) \<Longrightarrow>
       case x of
       (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La\<close> for La x
    using Hneq[of La \<open>fst x\<close> \<open>snd x\<close>] j_w  w_le L' L_neq
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append split: if_splits)
  moreover {
    have \<open>N \<propto> x1 ! xa \<notin> set (watched_l (N \<propto> x1))\<close>
      using N_xa
      by (auto simp: set_N_x1 set_N_swap_x1)

    then have \<open> \<And>Ab Ac La.
       all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE)) = add_mset L' (add_mset (N \<propto> x1 ! xa) Ac) \<Longrightarrow>
       dom_m N = add_mset x1 Ab \<Longrightarrow>
       N \<propto> x1 ! xa \<noteq> L \<Longrightarrow>
       {#i \<in># fst `# mset (W (N \<propto> x1 ! xa)). i = x1 \<or> i \<in># Ab#} =
         {#C \<in># Ab. N \<propto> x1 ! xa \<in> set (watched_l (N \<propto> C))#} \<close>
      using Hneq2[of \<open>N \<propto> x1 ! xa\<close>] L_neq  unfolding W_W' W_W2
      by (auto simp: clause_to_update_def split: if_splits)
  then have \<open>La \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE)) \<Longrightarrow>
          La \<noteq> L \<Longrightarrow>
          (x1 \<in># dom_m N \<longrightarrow>
           (La = N \<propto> x1 ! xa \<longrightarrow>
            add_mset x1 {#i \<in># fst `# mset (W' (N \<propto> x1 ! xa)). i \<in># dom_m N#} =
            clause_to_update (N \<propto> x1 ! xa) (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, {#}, {#})) \<and>
           (La \<noteq> N \<propto> x1 ! xa \<longrightarrow>
            {#i \<in># fst `# mset (W La). i \<in># dom_m N#} =
            clause_to_update La (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, {#}, {#}))) \<and>
          (x1 \<notin># dom_m N \<longrightarrow>
           (La = N \<propto> x1 ! xa \<longrightarrow>
            {#i \<in># fst `# mset (W' (N \<propto> x1 ! xa)). i \<in># dom_m N#} =
            clause_to_update (N \<propto> x1 ! xa) (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, {#}, {#})) \<and>
           (La \<noteq> N \<propto> x1 ! xa \<longrightarrow>
            {#i \<in># fst `# mset (W La). i \<in># dom_m N#} =
            clause_to_update La (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, {#}, {#})))\<close> for La
    using Hneq2[of La] j_w  w_le L' dom distinct_mset_dom[of N] L_notin_swap N_xa_in_swap L_neq
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append clause_to_update_def
        add_mset_eq_add_mset set_N_x1 set_N_swap_x1 assms(11) N_i
        dest!: multi_member_split La_in_notin_swap
        split: if_splits
        intro: image_mset_cong2 intro: filter_mset_cong2)
  }
  ultimately show ?thesis
    using L all_blits j_w
    unfolding correct_watching_except.simps H1  W'_def[symmetric] W_W' H2 W_W2 H4 H3
    by (intro conjI impI ballI)
      (simp_all add: L' W_W' W_W2 H3 H4 drop_map)
qed

definition unit_propagation_inner_loop_body_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_inv L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let S = keep_watch L j w S;
      ASSERT(unit_prop_body_wl_inv S j w C L);
      let val_K = polarity (get_trail_wl S) K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
          let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
          let val_L' = polarity (get_trail_wl S) L';
          if val_L' = Some True
          then update_blit_wl L C j w L' S
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
                let K = get_clauses_wl S \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S) K;
                if val_L' = Some True
                then update_blit_wl L C j w K S
                else update_clause_wl L C j w i f S
              }
          }
        }
      }
   }\<close>

lemma bind_cong_nres: \<open>(\<And>x. g x = g' x) \<Longrightarrow> (do {a \<leftarrow> f :: 'a nres;  g a}) = (do {a \<leftarrow> f :: 'a nres;  g' a})\<close>
  by auto

lemma case_prod_cong:
  \<open>(\<And>a b. f a b = g a b) \<Longrightarrow> (case x of (a, b) \<Rightarrow> f a b) = (case x of (a, b) \<Rightarrow> g a b)\<close>
  by (cases x) auto

definition truc where "truc S = RETURN S"

lemma [twl_st_wl]: \<open>get_clauses_wl (keep_watch L j w S) = get_clauses_wl S\<close>
  by (cases S) (auto simp: keep_watch_def)

lemma if_replace_cond: \<open>(if b then P b else Q b) = (if b then P True else Q False)\<close>
  by auto

lemma unit_propagation_inner_loop_body_wl_alt_def:
 \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_inv L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let b = (C \<notin># dom_m (get_clauses_wl S));
      if b then do {
        let S = keep_watch L j w S;
        ASSERT(unit_prop_body_wl_inv S j w C L);
        let K = K;
        let val_K = polarity (get_trail_wl S) K in
        if val_K = Some True
        then RETURN (j+1, w+1, S)
        else \<comment>\<open>Now the costly operations:\<close>
          RETURN (j, w+1, S)
      }
      else do {
        let S' = keep_watch L j w S;
        ASSERT(unit_prop_body_wl_inv S' j w C L);
        K \<leftarrow> SPEC((=) K);
        let val_K = polarity (get_trail_wl S') K in
        if val_K = Some True
        then RETURN (j+1, w+1, S')
        else do { \<comment>\<open>Now the costly operations:\<close>
          let i = (if ((get_clauses_wl S')\<propto>C) ! 0 = L then 0 else 1);
          let L' = ((get_clauses_wl S')\<propto>C) ! (1 - i);
          let val_L' = polarity (get_trail_wl S') L';
          if val_L' = Some True
          then update_blit_wl L C j w L' S'
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S') (get_clauses_wl S'\<propto>C);
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S');
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S' \<propto> C) S')}
                else do {RETURN (j+1, w+1, propagate_lit_wl L' C i S')}
              }
            | Some f \<Rightarrow> do {
                let K = get_clauses_wl S' \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S') K;
                if val_L' = Some True
                then update_blit_wl L C j w K S'
                else update_clause_wl L C j w i f S'
             }
          }
        }
      }
   }\<close>
proof -
  text \<open>We first define an intermediate step where both then and else branches are the same.\<close>
  have E: \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_inv L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let b = (C \<notin># dom_m (get_clauses_wl S));
      if b then do {
        let S = keep_watch L j w S;
        ASSERT(unit_prop_body_wl_inv S j w C L);
        let K = K;
        let val_K = polarity (get_trail_wl S) K in
        if val_K = Some True
        then RETURN (j+1, w+1, S)
        else do { \<comment>\<open>Now the costly operations:\<close>
          if b
          then RETURN (j, w+1, S)
          else do {
            let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
            let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
            let val_L' = polarity (get_trail_wl S) L';
            if val_L' = Some True
            then update_blit_wl L C j w L' S
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
                let K = get_clauses_wl S \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S) K;
                if val_L' = Some True
                then update_blit_wl L C j w K S
                else update_clause_wl L C j w i f S
                }
            }
          }
        }
      }
      else do {
        let S' = keep_watch L j w S;
        ASSERT(unit_prop_body_wl_inv S' j w C L);
        K \<leftarrow> SPEC((=) K);
        let val_K = polarity (get_trail_wl S') K in
        if val_K = Some True
        then RETURN (j+1, w+1, S')
        else do { \<comment>\<open>Now the costly operations:\<close>
          if b
          then RETURN (j, w+1, S')
          else do {
            let i = (if ((get_clauses_wl S')\<propto>C) ! 0 = L then 0 else 1);
            let L' = ((get_clauses_wl S')\<propto>C) ! (1 - i);
            let val_L' = polarity (get_trail_wl S') L';
            if val_L' = Some True
            then update_blit_wl L C j w L' S'
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S') (get_clauses_wl S'\<propto>C);
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S');
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S' \<propto> C) S')}
                  else do {RETURN (j+1, w+1, propagate_lit_wl L' C i S')}
                }
              | Some f \<Rightarrow> do {
                let K = get_clauses_wl S' \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S') K;
                if val_L' = Some True
                then update_blit_wl L C j w K S'
                else update_clause_wl L C j w i f S'
                }
            }
          }
        }
      }
   }\<close>
  (is \<open>_ = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_inv L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let b = (C \<notin># dom_m (get_clauses_wl S));
      if b then do {
        ?P C K b
      }
      else do {
        ?Q C K b
      }
   }\<close>)
    unfolding unit_propagation_inner_loop_body_wl_def if_not_swap truc_def bind_to_let_conv
      SPEC_eq_is_RETURN twl_st_wl
    unfolding Let_def if_not_swap truc_def bind_to_let_conv
      SPEC_eq_is_RETURN twl_st_wl
    apply (subst if_cancel)
    apply (intro bind_cong_nres case_prod_cong if_cong[OF refl] refl)
    done
    show ?thesis
      unfolding E
      apply (subst if_replace_cond[of _ \<open>?P _ _\<close>])
      unfolding if_True if_False
      apply auto
      done
qed

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

lemma unit_propagation_inner_loop_body_l_with_skip_alt_def:
  \<open>unit_propagation_inner_loop_body_l_with_skip L (S', n) =
do {
      ASSERT (clauses_to_update_l S' \<noteq> {#} \<or> 0 < n);
      ASSERT (unit_propagation_inner_loop_l_inv L (S', n));
      b \<leftarrow> SPEC (\<lambda>b. (b \<longrightarrow> 0 < n) \<and> (\<not> b \<longrightarrow> clauses_to_update_l S' \<noteq> {#}));
      if \<not> b
      then do {
             ASSERT (clauses_to_update_l S' \<noteq> {#});
             X2 \<leftarrow> select_from_clauses_to_update S';
             ASSERT (unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2));
             x \<leftarrow> SPEC (\<lambda>K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2));
             let v = polarity (get_trail_l (fst X2)) x;
             if v = Some True then let T = fst X2 in RETURN (T, if get_conflict_l T = None then n else 0)
             else let v = if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1;
                      va = get_clauses_l (fst X2) \<propto> snd X2 ! (1 - v); vaa = polarity (get_trail_l (fst X2)) va
                  in if vaa = Some True then let T = fst X2 in RETURN (T, if get_conflict_l T = None then n else 0)
                     else do {
                            x \<leftarrow> find_unwatched_l (get_trail_l (fst X2)) (get_clauses_l (fst X2) \<propto> snd X2);
                            case x of
                            None \<Rightarrow>
                              if vaa = Some False
                              then let T = set_conflict_l (get_clauses_l (fst X2) \<propto> snd X2) (fst X2)
                                   in RETURN (T, if get_conflict_l T = None then n else 0)
                              else let T = propagate_lit_l va (snd X2) v (fst X2)
                                   in RETURN (T, if get_conflict_l T = None then n else 0)
                            | Some a \<Rightarrow> do {
                                  x \<leftarrow> ASSERT (a < length (get_clauses_l (fst X2) \<propto> snd X2));
                                  let K = (get_clauses_l (fst X2) \<propto> (snd X2))!a;
                                  let val_K = polarity (get_trail_l (fst X2)) K;
                                  if val_K = Some True
                                  then let T = fst X2 in RETURN (T, if get_conflict_l T = None then n else 0)
                                  else do {
                                         T \<leftarrow> update_clause_l (snd X2) v a (fst X2);
                                         RETURN (T, if get_conflict_l T = None then n else 0)
                                       }
                                }
                          }
           }
      else RETURN (S', n - 1)
    }\<close>
proof -
  have remove_pairs: \<open>do {(x2, x2') \<leftarrow> (b0 :: _ nres); F x2 x2'} =
        do {X2 \<leftarrow> b0; F (fst X2) (snd X2)}\<close> for T a0 b0 a b c f t F
    by (meson case_prod_unfold)

  have H1: \<open>do {T \<leftarrow> do {x \<leftarrow> a ; b x}; RETURN (f T)} =
        do {x \<leftarrow> a; T \<leftarrow> b x; RETURN (f T)}\<close> for T a0 b0 a b c f t
    by auto
  have H2: \<open>do{T \<leftarrow> let v = val in g v; (f T :: _ nres)} =
         do{let v = val; T \<leftarrow> g v; f T} \<close> for g f T val
    by auto
  have H3: \<open>do{T \<leftarrow> if b then g else g'; (f T :: _ nres)} =
         (if b then do{T \<leftarrow> g; f T} else do{T \<leftarrow> g'; f T}) \<close> for g g' f T b
    by auto
  have H4: \<open>do{T \<leftarrow> case x of None \<Rightarrow> g | Some a \<Rightarrow> g' a; (f T :: _ nres)} =
         (case x of None \<Rightarrow> do{T \<leftarrow> g; f T} | Some a \<Rightarrow> do{T \<leftarrow> g' a; f T}) \<close> for g g' f T b x
    by (cases x) auto
  show ?thesis
    unfolding unit_propagation_inner_loop_body_l_with_skip_def prod.case
      unit_propagation_inner_loop_body_l_def remove_pairs
    unfolding H1 H2 H3 H4 bind_to_let_conv
    by simp
qed

(* TODO Move *)
lemma (in -) ex_geI: \<open>P n \<Longrightarrow> n \<ge> m \<Longrightarrow> \<exists>n\<ge>m. P n\<close>
  by auto
(* End Move *)

lemma [twl_st_wl]:
  \<open>get_unit_clauses_wl (keep_watch L j w S) = get_unit_clauses_wl S\<close>
  \<open>get_conflict_wl (keep_watch L j w S) = get_conflict_wl S\<close>
  \<open>get_trail_wl (keep_watch L j w S) = get_trail_wl S\<close>
  by (cases S; auto simp: keep_watch_def; fail)+


lemma correct_watching_except_correct_watching_except_propagate_lit_wl:
  assumes
    corr: \<open>correct_watching_except j w L S\<close> and
    i_le: \<open>Suc 0 < length (get_clauses_wl S \<propto> C)\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
  shows \<open>correct_watching_except j w L (propagate_lit_wl L' C i S)\<close>
proof -
  obtain M N D NE UE Q W where S: \<open>S = (M, N, D, NE, UE, Q, W)\<close> by (cases S)
  have
    all_blits: \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q, W)\<close> and
    Hneq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
        (La \<noteq> L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset (W La). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (W La). i \<in># dom_m N#} = clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close> and
    Heq: \<open>\<And>La. La\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
        (La = L \<longrightarrow>
         (\<forall>(i, K)\<in>#mset (take j (W La) @ drop w (W La)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La) \<and>
         {#i \<in># fst `# mset (take j (W La) @ drop w (W La)). i \<in># dom_m N#} =
         clause_to_update La (M, N, D, NE, UE, {#}, {#}))\<close>
    using corr unfolding S correct_watching_except.simps
    by blast+
  let ?N = \<open>N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i))\<close>

  have \<open>Suc 0 - i < length (N \<propto> C)\<close> and \<open>0 < length (N \<propto> C)\<close>
    using i_le
    by (auto simp: S)
  then have [simp]: \<open>mset (swap (N \<propto> C) 0 (Suc 0 - i)) = mset (N \<propto> C)\<close>
    by (auto simp: S)
  have H1[simp]: \<open>{#mset (fst x). x \<in># ran_m (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)))#} =
     {#mset (fst x). x \<in># ran_m N#}\<close>
    using C
    by (auto dest!: multi_member_split simp: ran_m_def S
           intro!: image_mset_cong)
  then have blits:
   \<open>all_blits_are_in_problem (Propagated L' C # M, N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)), D, NE, UE,
     add_mset (- L') Q, W)\<close>
    using all_blits nth_mem_mset[of w \<open>W L\<close>] unfolding all_blits_are_in_problem.simps
    by (auto dest!: multi_member_split[of L] simp: S simp del: nth_mem)

  have H2: \<open>mset `# ran_mf (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i))) = mset `# ran_mf N\<close>
    using H1 by auto
  have H3: \<open>dom_m (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i))) = dom_m N\<close>
    using C by (auto simp: S)
  have H4: \<open>set (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)) \<propto> ia) =
    set (N \<propto> ia)\<close> for ia
    using i_le
    by (cases \<open>C = ia\<close>)  (auto simp: S)
  have H5: \<open>set (watched_l (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)) \<propto> ia)) = set (watched_l (N \<propto> ia))\<close> for ia
    using i_le
    by (cases \<open>C = ia\<close>; cases i; cases \<open>N \<propto> ia\<close>; cases \<open>tl (N \<propto> ia)\<close>) (auto simp: S swap_def)
  show ?thesis
    using blits corr
    unfolding S propagate_lit_wl_def prod.simps correct_watching_except.simps Let_def
      H1 H2 H3 H4 clause_to_update_def get_clauses_l.simps H5
    by blast
qed

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
    j_w: \<open>j \<le> w\<close> and
    corr_w: \<open>correct_watching_except j w L S\<close> and
    inner_loop_inv: \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
    n: \<open>n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl S)) (mset (drop w (watched_by S L))))\<close> and
    confl_S: \<open>get_conflict_wl S = None\<close>
  shows unit_propagation_inner_loop_body_wl_spec: \<open>unit_propagation_inner_loop_body_wl L j w S \<le>
   \<Down> {((i, j, T'), (T, n)).
        (T', T) \<in> state_wl_l (Some (L, j)) \<and>
        correct_watching_except i j L T' \<and>
        j \<le> length (watched_by T' L) \<and>
        i \<le> j \<and>
        (get_conflict_wl T' = None \<longrightarrow>
           n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl T')) (mset (drop j (watched_by T' L))))) \<and>
        (get_conflict_wl T' \<noteq> None \<longrightarrow> n = 0)}
     (unit_propagation_inner_loop_body_l_with_skip L (S', n))\<close> (is \<open>?propa\<close> is \<open>_ \<le> \<Down> ?unit _\<close>)and
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
    l_wl_inv: \<open>unit_prop_body_wl_inv S j w C' L\<close> (is ?inv) and
    clause_ge_0: \<open>0 < length (get_clauses_l T \<propto> C')\<close> (is ?ge) and
    L_def: \<open>defined_lit (get_trail_wl S) L\<close> \<open>-L \<in> lits_of_l (get_trail_wl S)\<close>
      \<open>L \<notin> lits_of_l (get_trail_wl S)\<close> (is ?L_def) and
    i_le: \<open>i < length (get_clauses_wl S \<propto> C')\<close>  (is ?i_le) and
    i_le2: \<open>1-i < length (get_clauses_wl S \<propto> C')\<close>  (is ?i_le2) and
    C'_dom: \<open>C' \<in># dom_m (get_clauses_l T)\<close> (is ?C'_dom) and
    L_watched: \<open>L \<in> set (watched_l (get_clauses_l T \<propto> C'))\<close> (is ?L_w) and
    dist_clss: \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close> and
    confl: \<open>get_conflict_l T = None\<close> (is ?confl) and
    alien_L:
       \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)\<close>
       (is ?alien) and
    alien_L':
       \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
       (is ?alien') and
    alien_L'':
       \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
       (is ?alien'')
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
    show L: ?alien
      using alien uL_M twl_st_l(1-8)[OF T_T'] S_S'
        init_clss_state_to_l[OF T_T']
        unit_init_clauses_get_unit_init_clauses_l[OF T_T']
      unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: in_all_lits_of_mm_ain_atms_of_iff twl_st_wl twl_st twl_st_l)
    then show ?alien'
      apply (rule set_rev_mp)
      apply (rule all_lits_of_mm_mono)
      by (cases S) auto
    show ?alien''
      using L
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
      using that assms L unfolding unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def
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

  have i_def': \<open>i = (if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)\<close>
    using S_S' unfolding i_def by auto
  have [refine0]: \<open>RETURN (C', bL) \<le> \<Down> {((C', bL), b). (b \<longleftrightarrow> C'\<notin># dom_m (get_clauses_wl S)) \<and>
           (b \<longrightarrow> 0 < n) \<and> (\<not>b \<longrightarrow> clauses_to_update_l S' \<noteq> {#})}
       (SPEC (\<lambda>b. (b \<longrightarrow> 0 < n) \<and> (\<not>b \<longrightarrow> clauses_to_update_l S' \<noteq> {#})))\<close>
       (is \<open>_ \<le> \<Down> ?blit _\<close>)
      if \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
        \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n \<close> \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close>
        \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close>
  proof -
    have 1: \<open>(C', bL) \<in># {#(i, _) \<in># mset (drop w (watched_by S L)). i \<notin># dom_m (get_clauses_wl S)#}\<close>
      if \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S) \<close>
      using that w_le unfolding SLw apply -
      apply (auto simp add: in_set_drop_conv_nth intro!: ex_geI[of _ w])
      unfolding SLw
      apply auto
      done
    have \<open>fst (watched_by S L ! w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
      clauses_to_update_l S' = {#} \<Longrightarrow> False\<close>
      using S_S' w_le that n 1 unfolding SLw unit_propagation_inner_loop_l_inv_def apply -
      by (cases S; cases S')
       (auto simp add: state_wl_l_def in_set_drop_conv_nth twl_st_l_def
         Cons_nth_drop_Suc[symmetric]
        intro: ex_geI[of _ w]
        split: if_splits)
    with multi_member_split[OF 1] show ?thesis
      apply (intro RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>C' \<notin># dom_m (get_clauses_wl S)\<close>])
      using n
      by auto
  qed
  have [simp]: \<open>length (watched_by (keep_watch L j w S) L) = length (watched_by S L)\<close> for S j w L
    by (cases S) (auto simp: keep_watch_def)
  have S_removal: \<open>(S, set_clauses_to_update_l
         (remove1_mset (fst (watched_by S L ! w)) (clauses_to_update_l S')) S')
    \<in> state_wl_l (Some (L, Suc w))\<close>
    using S_S' w_le by (cases S; cases S')
      (auto simp: state_wl_l_def Cons_nth_drop_Suc[symmetric])

  have K:
     \<open>RETURN (get_clauses_wl (keep_watch L j w S) \<propto> C')
    \<le> \<Down> {(_, (U, C)). C = C' \<and> (S, U) \<in> state_wl_l (Some (L, Suc w))} (select_from_clauses_to_update S')\<close>
     if \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
       \<open>fst (watched_by S L ! w) \<in># clauses_to_update_l S'\<close>
    unfolding select_from_clauses_to_update_def
    apply (rule RETURN_RES_refine)
    apply (rule exI[of _ \<open>(T, C')\<close>])
    by (auto simp: remove_one_lit_from_wq_def S_removal that)
  have keep_watch_state_wl: \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S) \<Longrightarrow>
     (keep_watch L j w S, S') \<in> state_wl_l (Some (L, Suc w))\<close>
    using S_S' w_le j_w by (cases S; cases S')
      (auto simp: state_wl_l_def keep_watch_def Cons_nth_drop_Suc[symmetric]
        drop_map)
  have [simp]: \<open>drop (Suc w) (watched_by (keep_watch L j w S) L) = drop (Suc w) (watched_by S L)\<close>
    using j_w w_le by (cases S) (auto simp: keep_watch_def)
  have [simp]: \<open>get_clauses_wl (keep_watch L j w S) = get_clauses_wl S\<close> for L j w S
    by (cases S) (auto simp: keep_watch_def)
  have keep_watch:
    \<open>RETURN (keep_watch L j w S) \<le> \<Down> {(T, (T', C)). (T, T') \<in> state_wl_l (Some (L, Suc w)) \<and>
         C = C' \<and> T' = set_clauses_to_update_l (clauses_to_update_l S' - {#C#}) S'}
      (select_from_clauses_to_update S')\<close>
    (is \<open>_ \<le> \<Down> ?keep_watch _\<close>)
  if
    cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
    inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
    \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
    \<open>\<not> C' \<notin># dom_m (get_clauses_wl S)\<close> and
    clss: \<open>clauses_to_update_l S' \<noteq> {#}\<close>
  proof -
    have \<open>get_conflict_l S' = None\<close>
      using clss inv unfolding unit_propagation_inner_loop_l_inv_def twl_struct_invs_def prod.case
      apply -
      apply normalize_goal+
      by auto
    then show ?thesis
      using S_S' that w_le j_w
      unfolding select_from_clauses_to_update_def  keep_watch_def
      by (cases S)
        (auto intro!: RETURN_RES_refine simp: state_wl_l_def drop_map
          Cons_nth_drop_Suc[symmetric])
  qed
  have trail_keep_w: \<open>get_trail_wl (keep_watch L j w S) = get_trail_wl S\<close> for L j w S
    by (cases S) (auto simp: keep_watch_def)
  have unit_prop_body_wl_inv: \<open>unit_prop_body_wl_inv (keep_watch L j w S) j w x1 L\<close>
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_l: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
      \<open>((C', bL), b) \<in> ?blit\<close> and
      \<open>(C', bL) = (x1, x2)\<close> and
      \<open>\<not> x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      inv: \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close>
    for x1 b X2 x2
  proof -
    have all_blits_are_in_problem:
      \<open>all_blits_are_in_problem (a, b, c, d, e, f, g) \<Longrightarrow> w < length (g L) \<Longrightarrow>
        all_blits_are_in_problem (a, b, c, d, e, f, g(L := g L[j := g L ! w]))\<close> for a b c d e f g
      using j_w w_le nth_mem[of w \<open>g L\<close>]
      unfolding all_blits_are_in_problem.simps
      apply (cases \<open>j < length (g L)\<close>)
       apply (auto dest!: multi_member_split simp: in_set_conv_nth split: if_splits simp del: nth_mem)
      using nth_mem apply force+
      done

    have corr_w':
       \<open>correct_watching_except j w L S \<Longrightarrow> correct_watching_except j w L (keep_watch L j w S)\<close>
      using j_w w_le
      apply (cases S)
      apply (simp only: correct_watching_except.simps keep_watch_def prod.case)
      apply (cases \<open>j = w\<close>)
      by (simp_all add: all_blits_are_in_problem)
    have [simp]:
      \<open>(keep_watch L j w S, S') \<in> state_wl_l (Some (L, w)) \<longleftrightarrow> (S, S') \<in> state_wl_l (Some (L, w))\<close>
      using j_w
      by (cases S ; cases \<open>j=w\<close>)
        (auto simp: state_wl_l_def keep_watch_def drop_map)
    have [simp]: \<open>watched_by (keep_watch L j w S) L ! w = watched_by S L ! w\<close>
      using j_w
      by (cases S ; cases \<open>j=w\<close>)
        (auto simp: state_wl_l_def keep_watch_def drop_map)
    have [simp]: \<open>get_conflict_wl S = None\<close>
      using S_S' inv X2 unfolding unit_propagation_inner_loop_body_l_inv_def apply -
      apply normalize_goal+
      by auto
    have \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that by (auto simp: remove_one_lit_from_wq_def)
    then have \<open>L \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
      using alien_L'' by fast
    then show ?thesis
      unfolding unit_prop_body_wl_inv_def
      apply (intro impI)
      apply (rule exI[of _ S'])
      using inv X2 w_le S_S'
      by (auto simp: corr_w' corr_w remove_one_lit_from_wq_def twl_st_wl)
  qed
  have [refine0]: \<open>SPEC ((=) x2) \<le> SPEC (\<lambda>K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2))\<close>
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
      bL: \<open>((C', bL), b) \<in> ?blit\<close> and
      x: \<open>(C', bL) = (x1, x2)\<close> and
      x1: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>unit_prop_body_wl_inv (keep_watch L j w S) j w x1 L\<close>
      for x1 x2 X2 b
  proof -
    have [simp]: \<open>x2 = bL\<close> \<open>x1 = C'\<close>
      using x by simp_all
    have \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that by (auto simp: remove_one_lit_from_wq_def)
    from alien_L'[OF this]
    have \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
      .
    from correct_watching_exceptD[OF corr_w this w_le]
    have \<open>bL \<in> set (get_clauses_wl S \<propto> fst (watched_by S L ! w))\<close>
      using x1 SLw
      by (cases S; cases \<open>watched_by S L ! w\<close>) (auto simp add: )
    then show ?thesis
      using bL X2 S_S' x1
      by auto
  qed
  have find_unwatched_l: \<open>find_unwatched_l (get_trail_wl (keep_watch L j w S))
        (get_clauses_wl (keep_watch L j w S) \<propto> x1)
        \<le> \<Down> {(k, k'). k = k' \<and> get_clauses_wl S \<propto> x1 \<noteq> [] \<and>
            (k \<noteq> None \<longrightarrow> (the k \<ge> 2 \<and> the k < length (get_clauses_wl (keep_watch L j w S) \<propto> x1) \<and>
               (undefined_lit (get_trail_wl S) (get_clauses_wl (keep_watch L j w S) \<propto> x1!(the k))
                  \<or> get_clauses_wl (keep_watch L j w S) \<propto> x1!(the k) \<in> lits_of_l (get_trail_wl S)))) \<and>
            ((k = None) \<longleftrightarrow>
              (\<forall>La\<in>#mset (unwatched_l (get_clauses_wl (keep_watch L j w S) \<propto> x1)).
              - La \<in> lits_of_l (get_trail_wl (keep_watch L j w S))))}
          (find_unwatched_l (get_trail_l (fst X2))
            (get_clauses_l (fst X2) \<propto> snd X2))\<close>
    (is \<open>_ \<le> \<Down> ?find_unw _\<close>)
    if
      C': \<open>(C', bL) = (x1, x2)\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      x: \<open>x \<in> {K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>(keep_watch L j w S, X2) \<in>  ?keep_watch\<close>
    for x1 x2 X2 x
  proof -
    show ?thesis
      using S_S' X2 SLw that unfolding C'
      by (auto simp: twl_st_wl find_unwatched_l_def intro!: SPEC_refine)
  qed

  have blit_final:
   \<open>(if polarity (get_trail_wl (keep_watch L j w S)) x2 = Some True
        then RETURN (j + 1, w + 1, keep_watch L j w S)
        else RETURN (j, w + 1, keep_watch L j w S))
        \<le> \<Down> ?unit
          (RETURN (S', n - 1))\<close>
    if
      \<open>((C', bL), b) \<in> ?blit\<close> and
      \<open>(C', bL) = (x1, x2)\<close> and
      \<open>x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>unit_prop_body_wl_inv (keep_watch L j w S) j w x1 L\<close>
    for b x1 x2
    using S_S' w_le j_w n that confl_S
    by (auto simp: keep_watch_state_wl assert_bind_spec_conv Let_def twl_st_wl
        Cons_nth_drop_Suc[symmetric] correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
        corr_w correct_watching_except_correct_watching_except_Suc_notin
        split: if_splits)

  have conflict_final: \<open>((j + 1, w + 1,
          set_conflict_wl (get_clauses_wl (keep_watch L j w S) \<propto> x1)
          (keep_watch L j w S)),
        set_conflict_l (get_clauses_l (fst X2) \<propto> snd X2) (fst X2),
        if get_conflict_l
            (set_conflict_l (get_clauses_l (fst X2) \<propto> snd X2) (fst X2)) =
            None
        then n else 0)
        \<in> ?unit\<close>
    if
      C'_bl: \<open>(C', bL) = (x1, x2)\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close>
    for b x1 x2 X2 K x f x'
  proof -
    have [simp]: \<open>get_conflict_l (set_conflict_l C S) \<noteq> None\<close>
      \<open>get_conflict_wl (set_conflict_wl C S') = Some (mset C)\<close>
      \<open>watched_by (set_conflict_wl C S') L = watched_by S' L\<close> for C S S' L
        apply (cases S; auto simp: set_conflict_l_def; fail)
       apply (cases S'; auto simp: set_conflict_wl_def; fail)
      apply (cases S'; auto simp: set_conflict_wl_def; fail)
      done
    have [simp]: \<open>correct_watching_except j w L (set_conflict_wl C S) \<longleftrightarrow>
      correct_watching_except j w L S\<close> for j w L C S
      apply (cases S)
      by (simp only: correct_watching_except.simps all_blits_are_in_problem.simps
        set_conflict_wl_def prod.case clause_to_update_def get_clauses_l.simps)
    have \<open>(set_conflict_wl (get_clauses_wl S \<propto> x1) (keep_watch L j w S),
      set_conflict_l (get_clauses_l (fst X2) \<propto> snd X2) (fst X2))
      \<in> state_wl_l (Some (L, Suc w))\<close>
      using S_S' X2 SLw C'_bl by (cases S; cases S') (auto simp: state_wl_l_def
        set_conflict_wl_def set_conflict_l_def keep_watch_def
        clauses_to_update_wl.simps)
    then show ?thesis
      using S_S' w_le j_w n
      by (auto simp: keep_watch_state_wl
          correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
          corr_w correct_watching_except_correct_watching_except_Suc_notin
          split: if_splits)
  qed
  have propa_final: \<open>((j + 1, w + 1,
          propagate_lit_wl
          (get_clauses_wl (keep_watch L j w S) \<propto> x1 !
            (1 -
            (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1)))
          x1 (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1)
          (keep_watch L j w S)),
        propagate_lit_l
          (get_clauses_l (fst X2) \<propto> snd X2 !
          (1 - (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)))
          (snd X2) (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)
          (fst X2),
        if get_conflict_l
            (propagate_lit_l
              (get_clauses_l (fst X2) \<propto> snd X2 !
                (1 - (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)))
              (snd X2) (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)
              (fst X2)) =
            None
        then n else 0)
        \<in> ?unit\<close>
    if
      C': \<open>(C', bL) = (x1, x2)\<close> and
      x1_dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      l_inv: \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close>

    for b x1 x2 X2 K x f x'
  proof -
    have [simp]: \<open>get_conflict_l (propagate_lit_l C L w S) = get_conflict_l S\<close>
      \<open>watched_by (propagate_lit_wl C L w S') L' = watched_by S' L'\<close>
      \<open>get_conflict_wl (propagate_lit_wl C L w S') = get_conflict_wl S'\<close>
      \<open>L \<in># dom_m (get_clauses_wl S') \<Longrightarrow>
         dom_m (get_clauses_wl (propagate_lit_wl C L w S')) = dom_m (get_clauses_wl S')\<close>
      \<open>dom_m (get_clauses_wl (keep_watch L' i j S')) = dom_m (get_clauses_wl S')\<close>
      for C L w S S' L' i j
          apply (cases S; auto simp: propagate_lit_l_def; fail)
         apply (cases S'; auto simp: propagate_lit_wl_def; fail)
        apply (cases S'; auto simp: propagate_lit_wl_def; fail)
       apply (cases S'; auto simp: propagate_lit_wl_def; fail)
      apply (cases S'; auto simp: propagate_lit_wl_def; fail)
      done
    define i :: nat where \<open>i \<equiv> if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1\<close>
    have i_alt_def: \<open>i = (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)\<close>
      using X2 S_S' SLw unfolding i_def C' by auto
    have x1_dom[simp]: \<open>x1 \<in># dom_m (get_clauses_wl S)\<close>
      using x1_dom by fast
    have [simp]: \<open>get_clauses_wl S \<propto> x1 ! 0 \<noteq> L \<Longrightarrow> get_clauses_wl S \<propto> x1 ! Suc 0 = L\<close> and
      \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close>
      using l_inv X2 S_S' SLw unfolding unit_propagation_inner_loop_body_l_inv_def C'
      apply - apply normalize_goal+
      by (cases \<open>get_clauses_wl S \<propto> x1\<close>; cases \<open>tl (get_clauses_wl S \<propto> x1)\<close>)
        auto

    have n: \<open>n = size {#(i, uu) \<in># mset (drop (Suc w) (watched_by S L)).
        i \<notin># dom_m (get_clauses_wl S)#}\<close>
      using n
      apply (subst (asm) Cons_nth_drop_Suc[symmetric])
      subgoal using w_le by simp
      subgoal using n SLw X2 S_S' unfolding i_def C' by auto
      done
    have [simp]: \<open>get_conflict_l (fst X2) = get_conflict_wl S\<close>
      using X2 S_S' by auto

    have
      \<open>(propagate_lit_wl (get_clauses_wl S \<propto> x1 ! (Suc 0 - i)) x1 i (keep_watch L j w S),
     propagate_lit_l (get_clauses_l (fst X2) \<propto> snd X2 ! (Suc 0 - i)) (snd X2) i (fst X2))
    \<in> state_wl_l (Some (L, Suc w))\<close>
      using X2 S_S' SLw j_w w_le multi_member_split[OF x1_dom] unfolding C'
      by (cases S; cases S')
        (auto simp: state_wl_l_def propagate_lit_wl_def keep_watch_def
          propagate_lit_l_def drop_map)
    moreover have \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S) \<Longrightarrow>
    correct_watching_except (Suc j) (Suc w) L
     (propagate_lit_wl (get_clauses_wl S \<propto> x1 ! (Suc 0 - i)) x1 i (keep_watch L j w S))\<close>
      apply (rule correct_watching_except_correct_watching_except_propagate_lit_wl)
      using w_le j_w \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close> by auto
    moreover have \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
      by (simp add: corr_w correct_watching_except_correct_watching_except_Suc_Suc_keep_watch j_w w_le)
    ultimately show ?thesis
      using w_le unfolding i_def[symmetric] i_alt_def[symmetric]
      by (auto simp: twl_st_wl j_w n)
  qed

  have update_blit_wl_final:
    \<open>update_blit_wl L x1 j w (get_clauses_wl (keep_watch L j w S) \<propto> x1 ! xa) (keep_watch L j w S)
      \<le> \<Down> ?unit
          (RETURN (fst X2, if get_conflict_l (fst X2) = None then n else 0))\<close>
    if
      cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
      \<open>((C', bL), b) \<in> ?blit\<close> and
      C'_bl: \<open>(C', bL) = (x1, x2)\<close> and
      dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>unit_prop_body_wl_inv (keep_watch L j w S) j w x1 L\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x2)\<close> and
      \<open>x \<in> {K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      fx': \<open>(f, x') \<in> ?find_unw x1\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f x1 (keep_watch L j w S)\<close> and
      f: \<open>f = Some xa\<close> and
      x': \<open>x' = Some x'a\<close> and
      xa: \<open>(xa, x'a) \<in> nat_rel\<close> and
      \<open>x'a < length (get_clauses_l (fst X2) \<propto> snd X2)\<close> and
      \<open>polarity (get_trail_wl (keep_watch L j w S)) (get_clauses_wl (keep_watch L j w S) \<propto> x1 ! xa) =
     Some True\<close> and
      pol: \<open>polarity (get_trail_l (fst X2)) (get_clauses_l (fst X2) \<propto> snd X2 ! x'a) = Some True\<close>
    for b x1 x2 X2 K x f x' xa x'a
  proof -
    have confl: \<open>get_conflict_wl S = None\<close>
      using S_S' loop_inv cond unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto

    have unit_T: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that by (auto simp: remove_one_lit_from_wq_def)

    have \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
      by (simp add: corr_w correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
          j_w w_le)
    moreover have \<open>correct_watching_except (Suc j) (Suc w) L
       (a, b, None, d, e, f, ga(L := ga L[j := (x1, b \<propto> x1 ! xa)]))\<close>
      if
        corr: \<open>correct_watching_except (Suc j) (Suc w) L
      (a, b, None, d, e, f, ga(L := ga L[j := (x1, x2)]))\<close> and
        \<open>ga L ! w = (x1, x2)\<close> and
        S[simp]: \<open>S = (a, b, None, d, e, f, ga)\<close> and
        \<open>X2 = (set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S', x1)\<close> and
        \<open>(a, b, None, d, e,
      {#i \<in># mset (drop (Suc w) (map fst (ga L[j := (x1, x2)]))). i \<in># dom_m b#}, f) =
     set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S'\<close>
      for a :: \<open>('v literal, 'v literal,
             nat) annotated_lit list\<close> and
        b :: \<open>(nat, 'v literal list \<times>  bool) fmap\<close> and
        d :: \<open>'v literal multiset multiset\<close> and
        e :: \<open>'v literal multiset multiset\<close> and
        f :: \<open>'v literal multiset\<close> and
        ga :: \<open>'v literal \<Rightarrow> (nat \<times> 'v literal) list\<close>
    proof -
      have \<open>b \<propto> x1 ! xa \<in># all_lits_of_mm (mset `# ran_mf b + (d + e))\<close>
        using dom fx' by (auto simp: ran_m_def all_lits_of_mm_add_mset x' f twl_st_wl
            dest!: multi_member_split
            intro!: in_clause_in_all_lits_of_m)
      moreover have \<open>b \<propto> x1 ! xa \<in> set (b \<propto> x1)\<close>
        using dom fx' by (auto simp: ran_m_def all_lits_of_mm_add_mset x' f twl_st_wl
            dest!: multi_member_split
            intro!: in_clause_in_all_lits_of_m)

      moreover have \<open>b \<propto> x1 ! xa \<noteq> L\<close>
        using pol X2 L_def[OF unit_T] S_S' SLw  fx' x' f' xa unfolding C'_bl
        by (auto simp: polarity_def  split: if_splits)

      ultimately show ?thesis
        by (rule correct_watching_except_update_blit[OF corr])
    qed
    ultimately have \<open>update_blit_wl L x1 j w (get_clauses_wl (keep_watch L j w S) \<propto> x1 ! xa) (keep_watch L j w S)
    \<le> SPEC(\<lambda>(i, j, T'). correct_watching_except i j L T')\<close>
      using X2 confl SLw unfolding C'_bl
      apply (cases S)
      by (auto simp: keep_watch_def state_wl_l_def
          update_blit_wl_def)
    moreover have \<open>get_conflict_wl S = None\<close>
      using S_S' loop_inv cond unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto
    moreover have \<open>n = size {#(i, _) \<in># mset (drop (Suc w) (watched_by S L)). i \<notin># dom_m (get_clauses_wl S)#}\<close>
      using n dom X2 w_le S_S' SLw unfolding C'_bl
      by (auto simp: Cons_nth_drop_Suc[symmetric])
    ultimately show ?thesis
      using j_w w_le S_S' X2
      by (cases S)
        (auto simp: update_blit_wl_def keep_watch_def state_wl_l_def drop_map)
  qed
  have update_clss_final: \<open>update_clause_wl L x1 j w
       (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1) xa
       (keep_watch L j w S)
      \<le> \<Down> ?unit
          (update_clause_l (snd X2)
            (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1) x'a (fst X2) \<bind>
           (\<lambda>T. RETURN (T, if get_conflict_l T = None then n else 0)))\<close>
    if
      cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
      \<open>((C', bL), b) \<in> ?blit\<close> and
      C'_bl: \<open>(C', bL) = (x1, x2)\<close> and
      dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      wl_inv: \<open>unit_prop_body_wl_inv (keep_watch L j w S) j w x1 L\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x2)\<close> and
      \<open>x \<in> {K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>polarity (get_trail_wl (keep_watch L j w S)) K \<noteq> Some True\<close> and
      \<open>polarity (get_trail_l (fst X2)) x \<noteq> Some True\<close> and
      \<open>polarity (get_trail_wl (keep_watch L j w S))
      (get_clauses_wl (keep_watch L j w S) \<propto> x1 !
       (1 - (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1))) \<noteq>
     Some True\<close> and
      \<open>polarity (get_trail_l (fst X2))
      (get_clauses_l (fst X2) \<propto> snd X2 !
       (1 - (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1))) \<noteq>
     Some True\<close> and
      fx': \<open>(f, x') \<in> ?find_unw x1\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f x1 (keep_watch L j w S)\<close> and
      f: \<open>f = Some xa\<close> and
      x': \<open>x' = Some x'a\<close> and
      xa: \<open>(xa, x'a) \<in> nat_rel\<close> and
      \<open>x'a < length (get_clauses_l (fst X2) \<propto> snd X2)\<close> and
      \<open>polarity (get_trail_wl (keep_watch L j w S))
      (get_clauses_wl (keep_watch L j w S) \<propto> x1 ! xa) \<noteq>
     Some True\<close> and
      pol: \<open>polarity (get_trail_l (fst X2)) (get_clauses_l (fst X2) \<propto> snd X2 ! x'a) \<noteq> Some True\<close> and
      \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close>
    for b x1 x2 X2 K x f x' xa x'a
  proof -
    have confl: \<open>get_conflict_wl S = None\<close>
      using S_S' loop_inv cond unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto

    then obtain M N NE UE Q W where
      S: \<open>S = (M, N, None, NE, UE, Q, W)\<close>
      by (cases S) (auto simp: twl_st_l)
    have dom': \<open>x1 \<in># dom_m (get_clauses_wl (keep_watch L j w S)) \<longleftrightarrow> True\<close>
      using dom by auto
    obtain x where
      S_x: \<open>(keep_watch L j w S, x) \<in> state_wl_l (Some (L, w))\<close> and
      unit_loop_inv:
        \<open>unit_propagation_inner_loop_body_l_inv L (fst (watched_by (keep_watch L j w S) L ! w))
      (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w)) x)\<close> and
      L: \<open>L \<in># all_lits_of_mm
            (mset `# init_clss_lf (get_clauses_wl (keep_watch L j w S)) +
             get_unit_clauses_wl (keep_watch L j w S))\<close> and
      \<open>correct_watching_except j w L (keep_watch L j w S)\<close> and
      \<open>w < length (watched_by (keep_watch L j w S) L)\<close> and
      \<open>get_conflict_wl (keep_watch L j w S) = None\<close>
      using wl_inv unfolding unit_prop_body_wl_inv_def dom' simp_thms apply -
      by blast
    obtain x' where
      x_x': \<open>(set_clauses_to_update_l
        (clauses_to_update_l
          (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
            x) +
          {#fst (watched_by (keep_watch L j w S) L ! w)#})
        (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w)) x),
        x') \<in> twl_st_l (Some L)\<close> and
      \<open>twl_struct_invs x'\<close> and
      \<open>twl_stgy_invs x'\<close> and
      \<open>fst (watched_by (keep_watch L j w S) L ! w)
      \<in># dom_m
          (get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x))\<close> and
      \<open>0 < fst (watched_by (keep_watch L j w S) L ! w)\<close> and
      \<open>0 < length
            (get_clauses_l
              (remove_one_lit_from_wq
                (fst (watched_by (keep_watch L j w S) L ! w)) x) \<propto>
            fst (watched_by (keep_watch L j w S) L ! w))\<close> and
      \<open>no_dup
        (get_trail_l
          (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
            x))\<close> and
      ge0: \<open>(if get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w) !
          0 =
          L
        then 0 else 1)
      < length
          (get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w))\<close> and
      ge1i: \<open>1 -
      (if get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w) !
          0 =
          L
        then 0 else 1)
      < length
          (get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w))\<close> and
      L_watched: \<open>L \<in> set (watched_l
                (get_clauses_l
                  (remove_one_lit_from_wq
                    (fst (watched_by (keep_watch L j w S) L ! w)) x) \<propto>
                  fst (watched_by (keep_watch L j w S) L ! w)))\<close> and
      \<open>get_conflict_l
        (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w)) x) =
      None\<close>
      using unit_loop_inv
      unfolding unit_propagation_inner_loop_body_l_inv_def
      by blast

    have [simp]: \<open>x'a = xa\<close>
      using xa by auto
    have unit_T: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that
      by (auto simp: remove_one_lit_from_wq_def)

    have corr: \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
      by (simp add: corr_w correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
          j_w w_le)
    have i:
      \<open>i = (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1)\<close>
      \<open>i = (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)\<close>
      using SLw X2 S_S' unfolding i_def C'_bl apply (cases X2; auto simp add: twl_st_wl; fail)
      using SLw X2 S_S' unfolding i_def C'_bl apply (cases X2; auto simp add: twl_st_wl; fail)
      done
    have i': \<open>i = (if get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w) !
          0 =
          L
        then 0 else 1)\<close>
      using j_w w_le S_x unfolding i_def
      by (cases S) (auto simp: keep_watch_def)
    have \<open>twl_st_inv x'\<close>
      using \<open>twl_struct_invs x'\<close> unfolding twl_struct_invs_def by fast
    then have \<open>\<exists>x. twl_st_inv
         (x, {#TWL_Clause (mset (watched_l (fst x)))
                (mset (unwatched_l (fst x)))
             . x \<in># init_clss_l N#},
          {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
          . x \<in># learned_clss_l N#},
          None, NE, UE,
          add_mset
           (L, TWL_Clause (mset (watched_l (N \<propto> fst (W L[j := W L ! w] ! w))))
                (mset (unwatched_l (N \<propto> fst (W L[j := W L ! w] ! w)))))
           {#(L, TWL_Clause (mset (watched_l (N \<propto> x)))
                  (mset (unwatched_l (N \<propto> x))))
           . x \<in># remove1_mset (fst (W L[j := W L ! w] ! w))
                   {#i \<in># mset (drop w (map fst (W L[j := W L ! w]))).
                    i \<in># dom_m N#}#},
          Q)\<close>
      using x_x' S_x
      apply (cases x)
      apply (auto simp: S twl_st_l_def state_wl_l_def keep_watch_def
        simp del: struct_wf_twl_cls.simps)
      done
    then have \<open>Multiset.Ball
       ({#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
        . x \<in># ran_m N#})
       struct_wf_twl_cls\<close>
      unfolding twl_st_inv.simps image_mset_union[symmetric] all_clss_l_ran_m
      by blast
    then have distinct_N_x1: \<open>distinct (N \<propto> x1)\<close>
      using dom
      by (auto simp: S ran_m_def mset_take_mset_drop_mset' dest!: multi_member_split)

    have watch_by_S_w: \<open>watched_by (keep_watch L j w S) L ! w = (x1, x2)\<close>
      using j_w w_le SLw unfolding i_def C'_bl
      by (cases S)
        (auto simp: keep_watch_def split: if_splits)
    then have L_i: \<open>L = N \<propto> x1 ! i\<close>
      using L_watched ge0 ge1i SLw S_x unfolding i_def C'_bl
      by (auto simp: take_2_if twl_st_wl S split: if_splits)
    have i_le: \<open>i < length (N \<propto> x1)\<close>  \<open>1-i < length (N \<propto> x1)\<close>
      using watch_by_S_w ge0 ge1i S_x unfolding i'[symmetric]
      by (auto simp: S)
    have X2: \<open>X2 = (set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S', x1)\<close>
      using SLw X2 S_S' unfolding i_def C'_bl by (cases X2; auto simp add: twl_st_wl)
    have \<open>n = size {#(i, _) \<in># mset (drop (Suc w) (watched_by S L)).
      i \<noteq> x1 \<and> i \<notin># remove1_mset x1 (dom_m (get_clauses_wl S))#}\<close>
      using dom n w_le SLw unfolding C'_bl
      by (auto simp: Cons_nth_drop_Suc[symmetric] dest!: multi_member_split)
    moreover have \<open>L \<noteq> get_clauses_wl S \<propto> x1 ! xa\<close>
      using pol X2 L_def[OF unit_T] S_S' SLw  xa fx' unfolding C'_bl f x'
      by (auto simp: polarity_def twl_st_wl split: if_splits)
    moreover have \<open>remove1_mset x1 {#i \<in># mset (drop w (map fst (watched_by S L))). i \<in># dom_m (get_clauses_wl S)#} =
       {#i \<in># mset (drop (Suc w) (map fst (watched_by S L[j := (x1, x2)]))). i = x1 \<or> i \<in># remove1_mset x1 (dom_m (get_clauses_wl S))#}\<close>
      using dom n w_le SLw j_w unfolding C'_bl
      by (auto simp: Cons_nth_drop_Suc[symmetric] drop_map dest!: multi_member_split)
    moreover have \<open>correct_watching_except j (Suc w) L
     (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), None, NE, UE, Q, W
      (L := W L[j := (x1, x2)],
       N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L)]))\<close>
      apply (rule correct_watching_except_correct_watching_except_update_clause)
      subgoal
        using corr j_w w_le unfolding S
        by (auto simp: keep_watch_def)
      subgoal using j_w .
      subgoal using w_le by (auto simp: S)
      subgoal using alien_L'[OF unit_T] by (auto simp: S twl_st_wl)
      subgoal using i_le unfolding L_i by auto
      subgoal using distinct_N_x1 i_le fx' xa i_le unfolding L_i x'
        by (auto simp: S nth_eq_iff_index_eq i_def)
      subgoal using dom by (simp add: S)
      subgoal using i_le by simp
      subgoal using xa fx' unfolding f xa by (auto simp: S)
      subgoal using SLw unfolding C'_bl by (auto simp: S)
      subgoal unfolding L_i ..
      subgoal using distinct_N_x1 i_le unfolding L_i
        by (auto simp: nth_eq_iff_index_eq i_def)
      subgoal using distinct_N_x1 i_le fx' xa i_le unfolding L_i x'
        by (auto simp: S nth_eq_iff_index_eq i_def)
      subgoal using distinct_N_x1 i_le fx' xa i_le unfolding L_i x'
        by (auto simp: S nth_eq_iff_index_eq i_def)
      subgoal using distinct_N_x1 i_le fx' xa i_le unfolding L_i x'
        by (auto simp: S nth_eq_iff_index_eq i_def)
      subgoal using i_def by (auto simp: S split: if_splits)
      subgoal using xa fx' unfolding f xa by (auto simp: S)
      subgoal using distinct_N_x1 i_le fx' xa i_le unfolding L_i x'
        by (auto simp: S nth_eq_iff_index_eq i_def)
      done
    ultimately show ?thesis
      using S_S' w_le j_w SLw confl
      unfolding update_clause_wl_def update_clause_l_def i[symmetric] C'_bl
      by (cases S')
        (auto simp: Let_def X2 keep_watch_def state_wl_l_def S)
  qed
  have blit_final_in_dom: \<open>update_blit_wl L x1 j w
        (get_clauses_wl (keep_watch L j w S) \<propto> x1 !
          (1 -
          (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1)))
        (keep_watch L j w S)
        \<le> \<Down> ?unit
          (RETURN (fst X2, if get_conflict_l (fst X2) = None then n else 0))\<close>
    if
      cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
      \<open>((C', bL), b) \<in> ?blit\<close> and
      C'_bl: \<open>(C', bL) = (x1, x2)\<close> and
      dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(keep_watch L j w S, X2) \<in> ?keep_watch\<close> and
      \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      wl_inv: \<open>unit_prop_body_wl_inv (keep_watch L j w S) j w x1 L\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x2)\<close> and
      \<open>x \<in> {K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>polarity (get_trail_wl (keep_watch L j w S)) K \<noteq> Some True\<close> and
      \<open>polarity (get_trail_l (fst X2)) x \<noteq> Some True\<close> and
      \<open>polarity (get_trail_wl (keep_watch L j w S))
        (get_clauses_wl (keep_watch L j w S) \<propto> x1 !
        (1 -
          (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1))) =
      Some True\<close> and
      \<open>polarity (get_trail_l (fst X2))
        (get_clauses_l (fst X2) \<propto> snd X2 !
        (1 - (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1))) =
      Some True\<close>
    for b x1 x2 X2 K x
  proof -
    have confl: \<open>get_conflict_wl S = None\<close>
      using S_S' loop_inv cond unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto

    then obtain M N NE UE Q W where
      S: \<open>S = (M, N, None, NE, UE, Q, W)\<close>
      by (cases S) (auto simp: twl_st_l)
    have dom': \<open>x1 \<in># dom_m (get_clauses_wl (keep_watch L j w S)) \<longleftrightarrow> True\<close>
      using dom by auto
    obtain x where
      S_x: \<open>(keep_watch L j w S, x) \<in> state_wl_l (Some (L, w))\<close> and
      unit_loop_inv:
        \<open>unit_propagation_inner_loop_body_l_inv L (fst (watched_by (keep_watch L j w S) L ! w))
      (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w)) x)\<close> and
      L: \<open>L \<in># all_lits_of_mm
            (mset `# init_clss_lf (get_clauses_wl (keep_watch L j w S)) +
             get_unit_clauses_wl (keep_watch L j w S))\<close> and
      \<open>correct_watching_except j w L (keep_watch L j w S)\<close> and
      \<open>w < length (watched_by (keep_watch L j w S) L)\<close> and
      \<open>get_conflict_wl (keep_watch L j w S) = None\<close>
      using wl_inv unfolding unit_prop_body_wl_inv_def dom' simp_thms apply -
      by blast
    obtain x' where
      x_x': \<open>(set_clauses_to_update_l
        (clauses_to_update_l
          (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
            x) +
          {#fst (watched_by (keep_watch L j w S) L ! w)#})
        (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w)) x),
        x') \<in> twl_st_l (Some L)\<close> and
      \<open>twl_struct_invs x'\<close> and
      \<open>twl_stgy_invs x'\<close> and
      \<open>fst (watched_by (keep_watch L j w S) L ! w)
      \<in># dom_m
          (get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x))\<close> and
      \<open>0 < fst (watched_by (keep_watch L j w S) L ! w)\<close> and
      \<open>0 < length
            (get_clauses_l
              (remove_one_lit_from_wq
                (fst (watched_by (keep_watch L j w S) L ! w)) x) \<propto>
            fst (watched_by (keep_watch L j w S) L ! w))\<close> and
      \<open>no_dup
        (get_trail_l
          (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
            x))\<close> and
      ge0: \<open>(if get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w) !
          0 =
          L
        then 0 else 1)
      < length
          (get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w))\<close> and
      ge1i: \<open>1 -
      (if get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w) !
          0 =
          L
        then 0 else 1)
      < length
          (get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w))\<close> and
      L_watched: \<open>L \<in> set (watched_l
                (get_clauses_l
                  (remove_one_lit_from_wq
                    (fst (watched_by (keep_watch L j w S) L ! w)) x) \<propto>
                  fst (watched_by (keep_watch L j w S) L ! w)))\<close> and
      \<open>get_conflict_l
        (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w)) x) =
      None\<close>
      using unit_loop_inv
      unfolding unit_propagation_inner_loop_body_l_inv_def
      by blast

    have unit_T: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that
      by (auto simp: remove_one_lit_from_wq_def)

    have corr: \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
      by (simp add: corr_w correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
          j_w w_le)
    have i:
      \<open>i = (if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1)\<close>
      \<open>i = (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)\<close>
      using SLw X2 S_S' unfolding i_def C'_bl apply (cases X2; auto simp add: twl_st_wl; fail)
      using SLw X2 S_S' unfolding i_def C'_bl apply (cases X2; auto simp add: twl_st_wl; fail)
      done
    have i': \<open>i = (if get_clauses_l
            (remove_one_lit_from_wq (fst (watched_by (keep_watch L j w S) L ! w))
              x) \<propto>
          fst (watched_by (keep_watch L j w S) L ! w) !
          0 =
          L
        then 0 else 1)\<close>
      using j_w w_le S_x unfolding i_def
      by (cases S) (auto simp: keep_watch_def)
    have \<open>twl_st_inv x'\<close>
      using \<open>twl_struct_invs x'\<close> unfolding twl_struct_invs_def by fast
    then have \<open>\<exists>x. twl_st_inv
         (x, {#TWL_Clause (mset (watched_l (fst x)))
                (mset (unwatched_l (fst x)))
             . x \<in># init_clss_l N#},
          {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
          . x \<in># learned_clss_l N#},
          None, NE, UE,
          add_mset
           (L, TWL_Clause (mset (watched_l (N \<propto> fst (W L[j := W L ! w] ! w))))
                (mset (unwatched_l (N \<propto> fst (W L[j := W L ! w] ! w)))))
           {#(L, TWL_Clause (mset (watched_l (N \<propto> x)))
                  (mset (unwatched_l (N \<propto> x))))
           . x \<in># remove1_mset (fst (W L[j := W L ! w] ! w))
                   {#i \<in># mset (drop w (map fst (W L[j := W L ! w]))).
                    i \<in># dom_m N#}#},
          Q)\<close>
      using x_x' S_x
      apply (cases x)
      apply (auto simp: S twl_st_l_def state_wl_l_def keep_watch_def
        simp del: struct_wf_twl_cls.simps)
      done
    have \<open>twl_st_inv x'\<close>
      using \<open>twl_struct_invs x'\<close> unfolding twl_struct_invs_def by fast
    then have \<open>\<exists>x. twl_st_inv
         (x, {#TWL_Clause (mset (watched_l (fst x)))
                (mset (unwatched_l (fst x)))
             . x \<in># init_clss_l N#},
          {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
          . x \<in># learned_clss_l N#},
          None, NE, UE,
          add_mset
           (L, TWL_Clause (mset (watched_l (N \<propto> fst (W L[j := W L ! w] ! w))))
                (mset (unwatched_l (N \<propto> fst (W L[j := W L ! w] ! w)))))
           {#(L, TWL_Clause (mset (watched_l (N \<propto> x)))
                  (mset (unwatched_l (N \<propto> x))))
           . x \<in># remove1_mset (fst (W L[j := W L ! w] ! w))
                   {#i \<in># mset (drop w (map fst (W L[j := W L ! w]))).
                    i \<in># dom_m N#}#},
          Q)\<close>
      using x_x' S_x
      apply (cases x)
      apply (auto simp: S twl_st_l_def state_wl_l_def keep_watch_def
        simp del: struct_wf_twl_cls.simps)
      done
    then have \<open>Multiset.Ball
       ({#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
        . x \<in># ran_m N#})
       struct_wf_twl_cls\<close>
      unfolding twl_st_inv.simps image_mset_union[symmetric] all_clss_l_ran_m
      by blast
    then have distinct_N_x1: \<open>distinct (N \<propto> x1)\<close>
      using dom
      by (auto simp: S ran_m_def mset_take_mset_drop_mset' dest!: multi_member_split)

    have watch_by_S_w: \<open>watched_by (keep_watch L j w S) L ! w = (x1, x2)\<close>
      using j_w w_le SLw unfolding i_def C'_bl
      by (cases S)
        (auto simp: keep_watch_def split: if_splits)
    then have L_i: \<open>L = N \<propto> x1 ! i\<close>
      using L_watched ge0 ge1i SLw S_x unfolding i_def C'_bl
      by (auto simp: take_2_if twl_st_wl S split: if_splits)
    have i_le: \<open>i < length (N \<propto> x1)\<close>  \<open>1-i < length (N \<propto> x1)\<close>
      using watch_by_S_w ge0 ge1i S_x unfolding i'[symmetric]
      by (auto simp: S)
    have X2: \<open>X2 = (set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S', x1)\<close>
      using SLw X2 S_S' unfolding i_def C'_bl by (cases X2; auto simp add: twl_st_wl)
    have N_x1_in_L: \<open>N \<propto> x1 ! (Suc 0 - i)
      \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE))\<close>
      using dom i_le by (auto simp: ran_m_def S all_lits_of_mm_add_mset
        intro!: in_clause_in_all_lits_of_m
        dest!: multi_member_split)
    have \<open>((M, N, None, NE, UE, Q, W (L := W L[j := (x1, N \<propto> x1 ! (Suc 0 - i))])),
       fst X2) \<in> state_wl_l (Some (L, Suc w))\<close>
     using S_S' X2 j_w w_le SLw unfolding C'_bl
     apply (auto simp: state_wl_l_def S keep_watch_def drop_map)
     apply (subst Cons_nth_drop_Suc[symmetric])
     apply auto[]
     apply (subst (asm)Cons_nth_drop_Suc[symmetric])
     apply auto[]
     unfolding mset.simps image_mset_add_mset filter_mset_add_mset
     subgoal premises p
       using p(1-5)
        by (auto simp: L_i)
     done
    moreover have \<open>n = size {#(i, _) \<in># mset (drop (Suc w) (watched_by S L)).
      i \<notin># dom_m (get_clauses_wl S)#}\<close>
      using dom n w_le SLw unfolding C'_bl
      by (auto simp: Cons_nth_drop_Suc[symmetric] dest!: multi_member_split)
    moreover {
      have \<open>Suc 0 - i \<noteq> i\<close>
        by (auto simp: i_def split: if_splits)
      then have \<open>correct_watching_except (Suc j) (Suc w) L
        (M, N, None, NE, UE, Q, W(L := W L[j := (x1, N \<propto> x1 ! (Suc 0 - i))]))\<close>
        using SLw unfolding C'_bl apply -
        apply (rule correct_watching_except_update_blit)
        using N_x1_in_L corr i_le distinct_N_x1 i_le unfolding S
        by (auto simp: keep_watch_def L_i nth_eq_iff_index_eq)
    }
    ultimately show ?thesis
    using j_w w_le
      unfolding i[symmetric]
      by (auto simp: S update_blit_wl_def keep_watch_def)
  qed

  show 1: ?propa
    (is \<open>_ \<le> \<Down> ?unit _\<close>)
    supply trail_keep_w[simp]
    unfolding unit_propagation_inner_loop_body_wl_alt_def
      i_def[symmetric] i_def'[symmetric] unit_propagation_inner_loop_body_l_with_skip_alt_def
      unit_propagation_inner_loop_body_l_def
    apply (rewrite at "let _ = keep_watch _ _ _ _ in _" Let_def)
    unfolding i_def[symmetric] SLw prod.case
    apply (rewrite at "let _ = _ in let _ = get_clauses_l _ \<propto> _ ! _ in _" Let_def)
    apply (rewrite in \<open>if (\<not>_) then ASSERT _ >>= _ else _\<close> if_not_swap)
    supply RETURN_as_SPEC_refine[refine2 del]
    supply [[goals_limit=50]]
    apply (refine_rcg val f f' (*r ef*) keep_watch find_unwatched_l)
    subgoal using inner_loop_inv .
    subgoal by auto
    subgoal unfolding unit_prop_body_wl_inv_def by auto
    subgoal by (rule blit_final)
    subgoal by fast
    subgoal by (rule unit_prop_body_wl_inv)
    apply assumption+
    subgoal
      using S_S' by auto
    subgoal
      using S_S' w_le j_w n confl_S
      by (auto simp: correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
        Cons_nth_drop_Suc[symmetric] corr_w twl_st_wl)
    subgoal
      using S_S' by auto
    subgoal for b x1 x2 X2 K x
      by (rule blit_final_in_dom)
    apply assumption+
    subgoal for b x1 x2 X2 K x
      unfolding unit_prop_body_wl_find_unwatched_inv_def
      by auto
    subgoal by auto
    subgoal using S_S' by (auto simp: twl_st_wl)
    subgoal for b x1 x2 X2 K x f x'
      by (rule conflict_final)
    subgoal for b x1 x2 X2 K x
      by (rule propa_final)
    subgoal
      using S_S' by auto
    subgoal for b x1 x2 X2 K x f x' xa x'a
      by (rule update_blit_wl_final)
    subgoal for b x1 x2 X2 K x f x' xa x'a
      by (rule update_clss_final)
    done

  have [simp]: \<open>add_mset a (remove1_mset a M) = M \<longleftrightarrow> a \<in># M\<close> for a M
    by (metis ab_semigroup_add_class.add.commute add.left_neutral multi_self_add_other_not_self
       remove1_mset_eqE union_mset_add_mset_left)

  show ?eq if inv: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
    using i_le[OF inv] i_le2[OF inv] C'_dom[OF inv] S_S'
    unfolding i_def[symmetric]
    by (auto simp: ran_m_clause_upd image_mset_remove1_mset_if)
qed

definition unit_propagation_inner_loop_wl_loop
   :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
      (\<lambda>(j, w, S). w < length (watched_by S L) \<and> get_conflict_wl S = None)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl L j w S
      })
      (0, 0, S\<^sub>0)
  }
  \<close>

lemma correct_watching_except_correct_watching_cut_watch:
  assumes corr: \<open>correct_watching_except j w L (a, b, c, d, e, f, g)\<close>
  shows \<open>correct_watching (a, b, c, d, e, f, g(L := take j (g L) @ drop w (g L)))\<close>
proof -
  have all: \<open>all_blits_are_in_problem (a, b, c, d, e, f, g)\<close> and
    Heq:
      \<open>\<And>La i K. La \<in>#all_lits_of_mm (mset `# ran_mf b + (d + e)) \<Longrightarrow>
      (La = L \<longrightarrow>
       ((i, K)\<in>#mset (take j (g La) @ drop w (g La)) \<longrightarrow>
           i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La) \<and>
       {#i \<in># fst `# mset (take j (g La) @ drop w (g La)). i \<in># dom_m b#} =
       clause_to_update La (a, b, c, d, e, {#}, {#}))\<close> and
    Hneq:
      \<open>\<And>La i K. La\<in>#all_lits_of_mm (mset `# ran_mf b + (d + e)) \<Longrightarrow>
      (La \<noteq> L \<longrightarrow>
       ((i, K)\<in>#mset (g La) \<longrightarrow> i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La) \<and>
       {#i \<in># fst `# mset (g La). i \<in># dom_m b#} =
       clause_to_update La (a, b, c, d, e, {#}, {#}))\<close>
    using corr
    unfolding correct_watching.simps correct_watching_except.simps
    by blast+
  have \<open>all_blits_are_in_problem (a, b, c, d, e, f, g(L := take j (g L) @ drop w (g L)))\<close>
    using all unfolding all_blits_are_in_problem.simps
    by (auto dest!: in_set_takeD in_set_dropD)
  moreover have
    \<open>((i, K)\<in>#mset ((g(L := take j (g L) @ drop w (g L))) La) \<Longrightarrow>
            i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La)\<close> and
    \<open>{#i \<in># fst `# mset ((g(L := take j (g L) @ drop w (g L))) La).
         i \<in># dom_m b#} =
        clause_to_update La (a, b, c, d, e, {#}, {#})\<close>
  if \<open>La\<in>#all_lits_of_mm (mset `# ran_mf b + (d + e))\<close>
  for La i K
    apply (cases \<open>La = L\<close>)
    subgoal
      using Heq[of La i K] that by auto
    subgoal
      using Hneq[of La i K] that by auto
    apply (cases \<open>La = L\<close>)
    subgoal
      using Heq[of La i K] that by auto
    subgoal
      using Hneq[of La i K] that by auto
    done
  ultimately show ?thesis
    unfolding correct_watching.simps
    by blast
qed

lemma unit_propagation_inner_loop_wl_loop_alt_def:
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    let (_ :: nat) = (if get_conflict_wl S\<^sub>0 = None then remaining_nondom_wl 0 L S\<^sub>0 else 0);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
      (\<lambda>(j, w, S). w < length (watched_by S L) \<and> get_conflict_wl S = None)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl L j w S
      })
      (0, 0, S\<^sub>0)
  }
  \<close>
  unfolding unit_propagation_inner_loop_wl_loop_def by auto

definition cut_watch_list :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cut_watch_list j w L =(\<lambda>(M, N, D, NE, UE, Q, W). do {
      ASSERT(j \<le> length (W L));
      RETURN (M, N, D, NE, UE, Q, W(L := take j (W L) @ drop w (W L)))
    })\<close>

definition unit_propagation_inner_loop_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop L S\<^sub>0;
     cut_watch_list j w L S
  }\<close>

lemma correct_watching_correct_watching_except00:
  \<open>correct_watching S \<Longrightarrow> correct_watching_except 0 0 L S\<close>
  apply (cases S)
  apply (simp only: correct_watching.simps correct_watching_except.simps
    take0 drop0 append.left_neutral)
  by fast

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
    let ?R' = \<open>{((i, j, T'), (T, n)).
        (T', T) \<in> state_wl_l (Some (L, j)) \<and>
        correct_watching_except i j L T' \<and>
        j \<le> length (watched_by T' L) \<and>
        i \<le> j \<and>
        (get_conflict_wl T' = None \<longrightarrow>
           n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl T')) (mset (drop j (watched_by T' L))))) \<and>
        (get_conflict_wl T' \<noteq> None \<longrightarrow> n = 0)}\<close>
    have inv: \<open>unit_propagation_inner_loop_wl_loop_inv L iT'\<close>
      if
        iT'_Tn: \<open>(iT', Tn) \<in> ?R'\<close> and
        \<open>unit_propagation_inner_loop_l_inv L Tn\<close>
        for Tn iT'
    proof -
      obtain i j :: nat and T' where iT': \<open>iT' = (i, j, T')\<close> by (cases iT')
      obtain T n where Tn[simp]: \<open>Tn = (T, n)\<close> by (cases Tn)
      have \<open>unit_propagation_inner_loop_l_inv L (T, 0::nat)\<close>
        if \<open>unit_propagation_inner_loop_l_inv L (T, n)\<close> and \<open>get_conflict_l T \<noteq> None\<close>
        using that iT'_Tn
        unfolding unit_propagation_inner_loop_l_inv_def iT' prod.case
        apply - apply normalize_goal+
        apply (rule_tac x=x in exI)
        by auto
      then show ?thesis
        unfolding unit_propagation_inner_loop_wl_loop_inv_def iT' prod.simps apply -
        apply (rule exI[of _ T])
        using that by (auto simp: iT')
    qed
    have cond: \<open>(j < length (watched_by T' L) \<and> get_conflict_wl T' = None) =
      (clauses_to_update_l T \<noteq> {#} \<or> n > 0)\<close>
      if
        iT'_T: \<open>(ijT', Tn) \<in> ?R'\<close> and
        [simp]: \<open>ijT' = (i, jT')\<close> \<open>jT' = (j, T')\<close>  \<open>Tn = (T, n)\<close>
        for ijT' Tn i j T' n T jT'
    proof -
      have [simp]: \<open>size {#(i, _) \<in># mset (drop j xs). i \<notin># dom_m b#} =
        size {#i \<in># fst `# mset (drop j xs). i \<notin># dom_m b#}\<close> for xs b
        apply (induction \<open>xs\<close> arbitrary: j)
        subgoal by auto
        subgoal premises p for a xs j
          using p[of 0] p
          by (cases j) auto
        done
      have [simp]: \<open>size (filter_mset (\<lambda>i. (i \<in># (dom_m b))) (fst `# (mset (drop j (g L))))) +
          size {#i \<in># fst `# mset (drop j (g L)). i \<notin># dom_m b#} =
          length (g L) - j\<close> for g j b
        apply (subst size_union[symmetric])
        apply (subst multiset_partition[symmetric])
        by auto
      have [simp]: \<open>A \<noteq> {#} \<Longrightarrow> size A > 0\<close> for A
        by (auto dest!: multi_member_split)
      have \<open>length (watched_by T' L) = size (clauses_to_update_wl T' L j) + n + j\<close>
        if \<open>get_conflict_wl T' = None\<close>
        using that iT'_T
        by (cases \<open>get_conflict_wl T'\<close>; cases T')
          (auto simp add: state_wl_l_def drop_map)
      then show ?thesis
        using iT'_T
        by (cases \<open>get_conflict_wl T' = None\<close>) auto
    qed
    have remaining: \<open>RETURN (if get_conflict_wl S = None then remaining_nondom_wl 0 L S else 0) \<le> SPEC (\<lambda>_. True)\<close>
      by auto

    have unit_propagation_inner_loop_l_alt_def: \<open>unit_propagation_inner_loop_l L S' = do {
        n \<leftarrow> SPEC (\<lambda>_::nat. True);
        (S, n) \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_l_inv L\<^esup>
              (\<lambda>(S, n). clauses_to_update_l S \<noteq> {#} \<or> 0 < n)
              (unit_propagation_inner_loop_body_l_with_skip L) (S', n);
        RETURN S}\<close> for L S'
      unfolding unit_propagation_inner_loop_l_def by auto
    have unit_propagation_inner_loop_wl_alt_def: \<open>unit_propagation_inner_loop_wl L S = do {
      let (n::nat) = (if get_conflict_wl S = None then remaining_nondom_wl 0 L S else 0);
      (j, w, S) \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
         (\<lambda>(j, w, S). w < length (watched_by S L) \<and> get_conflict_wl S = None)
         (\<lambda>(j, x, y). unit_propagation_inner_loop_body_wl L j x y) (0, 0, S);
      cut_watch_list j w L S}\<close>
      unfolding unit_propagation_inner_loop_wl_loop_alt_def unit_propagation_inner_loop_wl_def
      by auto
    have \<open>unit_propagation_inner_loop_wl L S \<le>
            \<Down> {((T'), T). (T', T) \<in> state_wl_l None \<and> ?P T T'}
              (unit_propagation_inner_loop_l L S')\<close>
      (is \<open>_ \<le> \<Down> ?R _\<close>)
      unfolding unit_propagation_inner_loop_l_alt_def uncurry_def
        unit_propagation_inner_loop_wl_alt_def
      apply (refine_vcg WHILEIT_refine_genR[where
            R' = \<open>?R'\<close> and
            R = \<open>{((i, j, T'), (T, n)). ((i, j, T'), (T, n)) \<in> ?R' \<and>
               (j \<ge> length (watched_by T' L) \<or> get_conflict_wl T' \<noteq> None)}\<close>]
          remaining)
      subgoal using corr_w SS' by (auto simp: correct_watching_correct_watching_except00)
      subgoal by (rule inv)
      subgoal by (rule cond)
      subgoal for n i'w'T' Tn i' w'T' w' T'
        apply (cases Tn)
        apply (rule order_trans)
        apply (rule unit_propagation_inner_loop_body_wl_spec[of _ \<open>fst Tn\<close>])
        apply (simp only: prod.case in_pair_collect_simp)
        apply normalize_goal+
        by (auto simp del: twl_st_of_wl.simps)
      subgoal by auto
      subgoal for n i'w'T' Tn i' w'T' j L' w' T'
        apply (cases T')
        by (auto simp: state_wl_l_def cut_watch_list_def
          dest!: correct_watching_except_correct_watching_cut_watch)
      done
  }
  note H = this

  show ?thesis
    unfolding fref_param1
    apply (intro frefI nres_relI)
    by (auto simp: intro!: H)
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
    have H: \<open>clause_to_update L S = {#i \<in># fst `# mset (W L). i \<in># dom_m N#}\<close> and
       \<open>L \<in># all_lits_of_mm (mset `# ran_mf N + NE + UE)\<close>
        if \<open>L \<in># Q\<close> for L
      using corr_w that S H1[OF that] by (auto simp: correct_watching.simps S' clause_to_update_def
        Ball_def ac_simps all_conj_distrib
        dest!: multi_member_split)
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
          decide_lit_l_def decide_lit_wl_def state_wl_l_def
          all_blits_are_in_problem.simps)
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
    by (cases S) (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def
     all_blits_are_in_problem.simps)
  have [simp]: \<open>correct_watching  (tl aa, ca, da, ea, fa, ha, h) \<longleftrightarrow>
    correct_watching (aa, ca, None, ea, fa, ha, h)\<close>
    for aa ba ca L da ea fa ha h
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def
     all_blits_are_in_problem.simps)
  have [simp]: \<open>NO_MATCH None da \<Longrightarrow> correct_watching  (aa, ca, da, ea, fa, ha, h) \<longleftrightarrow>
    correct_watching (aa, ca, None, ea, fa, ha, h)\<close>
    for aa ba ca L da ea fa ha h
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def
     all_blits_are_in_problem.simps)
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

text \<open>Rougly: we get a fresh index that has not yet been used.\<close>
definition get_fresh_index_wl :: \<open>'v clauses_l \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat nres\<close> where
\<open>get_fresh_index_wl N NUE W = SPEC(\<lambda>i. i > 0 \<and> i \<notin># dom_m N \<and>
   (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + NUE) . i \<notin> fst ` set (W L)))\<close>

definition propagate_bt_wl :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_bt_wl = (\<lambda>L L' (M, N, D, NE, UE, Q, W). do {
    D'' \<leftarrow> list_of_mset (the D);
    i \<leftarrow> get_fresh_index_wl N (NE + UE) W;
    RETURN (Propagated (-L) i # M,
        fmupd i ([-L, L'] @ (remove1 (-L) (remove1 L' D'')), False) N,
          None, NE, UE, {#L#}, W(-L:= W (-L) @ [(i, L')], L':= W L' @ [(i, -L)]))
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
    i_dom: \<open>i \<notin># dom_m N\<close> and
   fresh: \<open>\<And>L. L\<in>#all_lits_of_mm (mset `# ran_mf  N + (NE + UE)) \<Longrightarrow> i \<notin> fst ` set (W L)\<close> and
   [iff]: \<open>L1 \<noteq> L2\<close>
  shows
  \<open>correct_watching (K # M, fmupd i (L1 # L2 # UW, b) N,
    D, NE, UE, Q, W (L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)])) \<longleftrightarrow>
  correct_watching (M, N, D, NE, UE, Q', W)\<close>
  (is \<open>?l \<longleftrightarrow> ?c\<close> is \<open>correct_watching (_, ?N, _) = _\<close>)
proof -
  have [iff]: \<open>L2 \<noteq> L1\<close>
    using \<open>L1 \<noteq> L2\<close> by (subst eq_commute)
  have [simp]: \<open>clause_to_update L1 (M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, {#}, {#}) =
         add_mset i (clause_to_update L1 (M, N, D, NE, UE, {#}, {#}))\<close> for L2 UW
    using i_dom
    by (auto simp: clause_to_update_def intro: filter_mset_cong)
  have [simp]: \<open>clause_to_update L2 (M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, {#}, {#}) =
         add_mset i (clause_to_update L2 (M, N, D, NE, UE, {#}, {#}))\<close> for L1 UW
    using i_dom
    by (auto simp: clause_to_update_def intro: filter_mset_cong)
  have [simp]: \<open>x \<noteq> L1 \<Longrightarrow> x \<noteq> L2 \<Longrightarrow>
   clause_to_update x (M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, {#}, {#}) =
        clause_to_update x (M, N, D, NE, UE, {#}, {#})\<close> for x UW
    using i_dom
    by (auto simp: clause_to_update_def intro: filter_mset_cong)
  have [simp]: \<open>L1 \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE))\<close>
    \<open>L2 \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE))\<close>
    using i_dom L1 L2 UW
    by (fastforce simp: all_blits_are_in_problem.simps ran_m_mapsto_upd_notin
      all_lits_of_mm_add_mset all_lits_of_m_add_mset in_all_lits_of_m_ain_atms_of_iff
      in_all_lits_of_mm_ain_atms_of_iff)+
  have H':
     \<open>{#ia \<in># fst `# mset (W x). ia = i \<or> ia \<in># dom_m N#} =  {#ia \<in># fst `# mset (W x). ia \<in># dom_m N#}\<close>
     if \<open>x \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE))\<close> for x
    using i_dom fresh[of x] that
    by (auto simp: clause_to_update_def intro!: filter_mset_cong)
  have [simp]:
    \<open>clause_to_update L1 (K # M, N, D, NE, UE, {#}, {#}) = clause_to_update L1 (M, N, D, NE, UE, {#}, {#})\<close>
    for L1 N D NE UE M K
    by (auto simp: clause_to_update_def)

  have [simp]: \<open>set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m ?N#} + (NE + UE))) =
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE + UE)))\<close>
    using i_dom L1 L2 UW
    by (fastforce simp: all_blits_are_in_problem.simps ran_m_mapsto_upd_notin
        all_lits_of_mm_add_mset all_lits_of_m_add_mset in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff)

  show ?thesis
  proof (rule iffI)
    assume corr: ?l
    have blits: \<open>all_blits_are_in_problem
   (K # M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, Q, W
    (L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)]))\<close> and
      H: \<open>\<And>L ia K'. (L\<in>#all_lits_of_mm
        (mset `# ran_mf (fmupd i (L1 # L2 # UW, b) N) + (NE + UE)) \<Longrightarrow>
      ((ia, K')\<in>#mset ((W(L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)])) L) \<longrightarrow>
          ia \<in># dom_m (fmupd i (L1 # L2 # UW, b) N) \<longrightarrow>
          K' \<in> set (fmupd i (L1 # L2 # UW, b) N \<propto> ia) \<and> K' \<noteq> L) \<and>
      {#ia \<in># fst `#
              mset ((W(L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)])) L).
       ia \<in># dom_m (fmupd i (L1 # L2 # UW, b) N)#} =
      clause_to_update L
       (K # M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, {#}, {#}))\<close>
      using corr unfolding correct_watching.simps
      by blast+

    have blits': \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q', W)\<close>
      using blits by (auto simp: all_blits_are_in_problem.simps
          dest!: multi_member_split split: if_splits)

    have \<open>x \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<longrightarrow>
         (xa \<in># mset (W x) \<longrightarrow> (case xa of (i, K) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> x)) \<and>
         {#i \<in># fst `# mset (W x). i \<in># dom_m N#} = clause_to_update x (M, N, D, NE, UE, {#}, {#})\<close>
      for x xa
      using H[of x \<open>fst xa\<close> \<open>snd xa\<close>] fresh[of x] i_dom
      apply (cases \<open>x = L1\<close>; cases \<open>x = L2\<close>)
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      done
    then show ?c
      using blits'
      unfolding correct_watching.simps Ball_def
      by (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset
          all_conj_distrib all_lits_of_mm_union)
  next
    assume corr: ?c
    have blits: \<open>all_blits_are_in_problem (M, N, D, NE, UE, Q', W)\<close> and
      H: \<open>\<And>L ia K'. (L\<in>#all_lits_of_mm
        (mset `# ran_mf N + (NE + UE)) \<Longrightarrow>
      ((ia, K')\<in>#mset (W L) \<longrightarrow>
          ia \<in># dom_m N \<longrightarrow>
          K' \<in> set (N \<propto> ia) \<and> K' \<noteq> L) \<and>
      {#ia \<in># fst `# mset (W L). ia \<in># dom_m N#} = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>
      using corr unfolding correct_watching.simps
      by blast+
    have blits': \<open>all_blits_are_in_problem (K # M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, Q, W(L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)]))\<close>
      using blits unfolding all_blits_are_in_problem.simps
      by auto
    have \<open>x \<in># all_lits_of_mm (mset `# ran_mf (fmupd i (L1 # L2 # UW, b) N) + (NE + UE)) \<longrightarrow>
         (xa \<in># mset ((W(L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)])) x) \<longrightarrow>
               (case xa of (ia, K) \<Rightarrow> ia \<in># dom_m (fmupd i (L1 # L2 # UW, b) N) \<longrightarrow> K \<in> set (fmupd i (L1 # L2 # UW, b) N \<propto> ia) \<and> K \<noteq> x)) \<and>
         {#ia \<in># fst `# mset ((W(L1 := W L1 @ [(i, L2)], L2 := W L2 @ [(i, L1)])) x). ia \<in># dom_m (fmupd i (L1 # L2 # UW, b) N)#} =
         clause_to_update x (K # M, fmupd i (L1 # L2 # UW, b) N, D, NE, UE, {#}, {#})\<close>
      for x :: \<open>'a literal\<close> and xa
      using H[of x \<open>fst xa\<close> \<open>snd xa\<close>] fresh[of x] i_dom
      apply (cases \<open>x = L1\<close>; cases \<open>x = L2\<close>)
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      done
  then show ?l
      using blits'
      unfolding correct_watching.simps Ball_def
      by auto
  qed
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
    for S' S
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

  have find_lit_of_max_level_wl: \<open>find_lit_of_max_level_wl T' LLK'
    \<le> \<Down> {(L', L). L = L' \<and> L' \<in># the (get_conflict_wl T') \<and> L' \<in># the (get_conflict_wl T') - {#-LLK'#}}
         (find_lit_of_max_level T L)\<close>
    (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if \<open>L = LLK'\<close> \<open>(T', T) \<in> ?find S'\<close>
    for S' S T T' L LLK'
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
     LL': \<open>(L', L) \<in> ?find_lit U' (lit_of (hd (get_trail_wl S')))\<close> and
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
      T': \<open>T' = (MS, NS, Some DT, NES, UES, {#}, W)\<close> and
      \<open>DT \<subseteq># DS\<close>
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
       unfolding S' correct_watching.simps clause_to_update_def get_clauses_l.simps
       by (simp add: all_blits_are_in_problem.simps)
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
                 atms_of_mm (get_unit_init_clss_wl S')\<close> and
       dist: \<open>distinct_mset DS\<close>
      using SS' bt unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        backtrack_wl_inv_def backtrack_l_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      apply -
      apply normalize_goal+
      apply (simp add: twl_st twl_st_l twl_st_wl)
      apply normalize_goal+
      apply (simp add: twl_st twl_st_l twl_st_wl S')
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
    have dist: \<open>distinct_mset DT\<close>
      using \<open>DT \<subseteq># DS\<close> dist by (rule distinct_mset_mono)
    have fresh: \<open>get_fresh_index_wl N (NUE) W \<le>
      \<Down> {(i, i'). i = i' \<and> i \<notin># dom_m N \<and>  (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + NUE). i \<notin> fst ` set (W L))} (get_fresh_index N')\<close>
       if \<open>N = N'\<close> for N N' NUE W
      unfolding that get_fresh_index_def get_fresh_index_wl_def
      by (auto intro: RES_refine)
    show ?thesis
      unfolding propagate_bt_wl_def propagate_bt_l_def S' T' U' U st_l_of_wl.simps get_trail_wl.simps
      list_of_mset_def K'_def[symmetric]
      apply (refine_vcg fresh; remove_dummy_vars)
      apply (subst in_pair_collect_simp)
      apply (intro conjI)
      subgoal using SS' by (auto simp: corr state_wl_l_def S')
      subgoal
        apply simp
        apply (subst correct_watching_learn)
        subgoal using atm_K' unfolding all_clss_lf_ran_m[symmetric] image_mset_union by auto
        subgoal using atm_L' unfolding all_clss_lf_ran_m[symmetric] image_mset_union by auto
        subgoal using atm_confl TT'  unfolding all_clss_lf_ran_m[symmetric] image_mset_union
          by (fastforce simp: S' T' dest!: in_atms_of_minusD)
        subgoal by auto
        subgoal by auto
        subgoal using dist LL' by (auto simp: U' S' distinct_mset_remove1_All)
        apply (rule corr)
        done
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
      set_mset (all_lits_of_mm (mset `# ran_mf NS + (NES + UES)))\<close>
      apply (subst all_clss_lf_ran_m[symmetric])+
      apply (subst image_mset_union)+
      using S1 S2 atms_of_subset_mset_mono[OF DT_DS]
      by (fastforce simp: all_lits_of_mm_union all_lits_of_mm_add_mset state_wl_l_def
        twl_st_l_def S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        mset_take_mset_drop_mset' in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff)
    then have K': \<open>set_mset (all_lits_of_mm (mset `# ran_mf NS + (NES + add_mset (the (Some DT)) UES))) =
      set_mset (all_lits_of_mm (mset `# ran_mf NS + (NES + UES)))\<close>
      by (auto simp: ac_simps)
    have \<open>correct_watching S'\<close>
      using SS' by fast
    then have corr: \<open>correct_watching (Propagated (- lit_of (hd MS)) 0 # MU, NS, None, NES,
      add_mset (the (Some DT)) UES, unmark (hd MS), W)\<close>
      unfolding S' correct_watching.simps clause_to_update_def get_clauses_l.simps K
        all_blits_are_in_problem.simps K' .

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
    by (cases S; auto simp: decide_lit_wl_def correct_watching.simps clause_to_update_def
        all_blits_are_in_problem.simps)
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