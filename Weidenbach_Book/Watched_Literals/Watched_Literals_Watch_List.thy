theory Watched_Literals_Watch_List
  imports Watched_Literals_List Watched_Literals_All_Literals
begin

no_notation funcset (infixr "\<rightarrow>" 60)

chapter \<open>Third Refinement: Remembering watched\<close>

section \<open>Types\<close>

type_synonym clauses_to_update_wl = \<open>nat multiset\<close>
type_synonym 'v watcher = \<open>(nat \<times> 'v literal \<times> bool)\<close>
type_synonym 'v watched = \<open>'v watcher list\<close>
type_synonym 'v lit_queue_wl = \<open>'v literal multiset\<close>

type_synonym 'v twl_st_wl =
  \<open>('v, nat) ann_lits \<times> 'v clauses_l \<times>
  'v cconflict \<times> 'v clauses \<times> 'v clauses  \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times>
  'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl \<times> ('v literal \<Rightarrow> 'v watched)\<close>


section \<open>Access Functions\<close>

fun clauses_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> clauses_to_update_wl\<close> where
  \<open>clauses_to_update_wl (_, N, _, _, _, _, _ ,_ , _, _, _, _, W) L i =
      filter_mset (\<lambda>i. i \<in># dom_m N) (mset (drop i (map fst (W L))))\<close>

fun get_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_wl (M, _, _, _, _, _, _ ,_ , _) = M\<close>

fun literals_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v lit_queue_wl\<close> where
  \<open>literals_to_update_wl (_, _, _, _, _, _ ,_ , _, _, _, _, Q, _) = Q\<close>

fun set_literals_to_update_wl :: \<open>'v lit_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_literals_to_update_wl Q (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, _, W) =
     (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>

fun get_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_wl (_, _, D, _, _, _, _) = D\<close>

fun get_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_wl (M, N, D, NE, UE, NEk, UEk, WS, Q) = N\<close>

fun get_unit_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = UE + UEk\<close>

fun get_unit_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NE + NEk\<close>

fun get_unit_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_clauses_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NE + NEk + UE + UEk\<close>

fun get_kept_unit_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_kept_unit_clauses_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NEk + UEk\<close>

fun get_unkept_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unkept_learned_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, WS, Q) = UE\<close>

fun get_subsumed_init_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_init_clauses_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NS\<close>

fun get_subsumed_learned_clauses_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_learned_clauses_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = US\<close>

abbreviation get_subsumed_clauses_wl  :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_clauses_wl S \<equiv> get_subsumed_init_clauses_wl S + get_subsumed_learned_clauses_wl S\<close>

fun get_init_clauses0_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_init_clauses0_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) = N0\<close>

fun get_learned_clauses0_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_learned_clauses0_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) = U0\<close>

abbreviation get_clauses0_wl  :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_clauses0_wl S \<equiv> get_init_clauses0_wl S + get_learned_clauses0_wl S\<close>

definition get_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>get_learned_clss_wl S = learned_clss_lf (get_clauses_wl S)\<close>

abbreviation get_all_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clause multiset\<close> where
  \<open>get_all_learned_clss_wl S \<equiv> mset `# get_learned_clss_wl S + get_unit_learned_clss_wl S +
      get_subsumed_learned_clauses_wl S + get_learned_clauses0_wl S\<close>

lemma get_unit_clauses_wl_alt_def:
  \<open>get_unit_clauses_wl S = get_unit_init_clss_wl S + get_unit_learned_clss_wl S\<close>
  by (cases S) auto

fun get_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v literal \<Rightarrow> 'v watched)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, _, _, _, _, _, _, W) = W\<close>

fun get_unkept_unit_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unkept_unit_init_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NE\<close>

fun get_unkept_unit_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unkept_unit_learned_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = UE\<close>

fun get_kept_unit_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_kept_unit_init_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NEk\<close>

fun get_kept_unit_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_kept_unit_learned_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = UEk\<close>

lemma get_unit_init_clss_wl_alt_def:
  \<open>get_unit_init_clss_wl T = get_unkept_unit_init_clss_wl T + get_kept_unit_init_clss_wl T\<close>
  by (cases T) auto

lemma get_unit_learned_clss_wl_alt_def:
  \<open>get_unit_learned_clss_wl T = get_unkept_unit_learned_clss_wl T + get_kept_unit_learned_clss_wl T\<close>
  by (cases T) auto

abbreviation get_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>get_init_clss_wl S \<equiv> init_clss_lf (get_clauses_wl S)\<close>

definition all_lits_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal multiset\<close> where
  \<open>all_lits_st S \<equiv> all_lits (get_clauses_wl S) (get_unit_clauses_wl S + get_subsumed_clauses_wl S + get_clauses0_wl S)\<close>

definition all_init_lits_of_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clause\<close> where
  \<open>all_init_lits_of_wl S' \<equiv> all_lits_of_mm (mset `# get_init_clss_wl S' + get_unit_init_clss_wl S' +
          get_subsumed_init_clauses_wl S' + get_init_clauses0_wl S')\<close>

definition all_learned_lits_of_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clause\<close> where
  \<open>all_learned_lits_of_wl S' \<equiv> all_lits_of_mm (mset `# learned_clss_lf (get_clauses_wl S') + get_unit_learned_clss_wl S' +
          get_subsumed_learned_clauses_wl S' + get_learned_clauses0_wl S')\<close>

lemma all_lits_st_alt_def:
  \<open>Watched_Literals_Watch_List.all_lits_st S = all_init_lits_of_wl S + all_learned_lits_of_wl S\<close>
  apply (auto simp: all_lits_st_def all_init_lits_of_wl_def all_learned_lits_of_wl_def
    ac_simps all_lits_def all_lits_of_mm_union)
   by (metis all_clss_l_ran_m all_lits_of_mm_union get_unit_clauses_wl_alt_def image_mset_union union_assoc) 

lemma all_init_lits_of_wl_all_lits_st:
  \<open>set_mset (all_init_lits_of_wl S) \<subseteq> set_mset (all_lits_st S)\<close>
  unfolding all_lits_st_def all_init_lits_of_wl_def all_lits_def
  apply (subst (2) all_clss_l_ran_m[symmetric])
  unfolding image_mset_union
  apply (cases S)
  apply (auto simp: all_lits_of_mm_union)
  done

lemma in_all_lits_uminus_iff[simp]: \<open>- L \<in># all_lits_st S \<longleftrightarrow> L \<in># all_lits_st S\<close>
  by (auto simp: all_lits_st_def in_all_lits_of_mm_uminus_iff all_lits_def)

lemma all_lits_ofI[intro]:
  \<open>x = get_clauses_wl S \<Longrightarrow> C \<in># dom_m x \<Longrightarrow> n < length (x \<propto> C) \<Longrightarrow> x \<propto> C ! n \<in># all_lits_st S\<close>
  using in_clause_in_all_lits_of_m[of \<open>x \<propto> C ! n\<close>] nth_mem_mset[of n \<open>x \<propto> C\<close>]
  by (auto simp: all_lits_st_def all_lits_def all_lits_of_mm_union ran_m_def all_lits_of_mm_add_mset
    dest!: multi_member_split)


section \<open>Watch List Function\<close>

definition op_watch_list :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> 'v watcher\<close> where
  [simp]: \<open>op_watch_list W K i = W K ! i\<close>

definition mop_watch_list :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> 'v watcher nres\<close> where
  \<open>mop_watch_list W K i = do {
      ASSERT(i < length (W K));
      RETURN (W K ! i)
   }\<close>

definition op_watch_list_append :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v literal \<Rightarrow> 'v watcher \<Rightarrow> ('v literal \<Rightarrow> 'v watched)\<close> where
  [simp]: \<open>op_watch_list_append W K x = W (K := W K @ [x])\<close>

definition mop_watch_list_append :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v literal \<Rightarrow> 'v watcher \<Rightarrow> ('v literal \<Rightarrow> 'v watched) nres\<close> where
  \<open>mop_watch_list_append W K x = do {
      RETURN (W (K := W K @ [x]))
   }\<close>

definition op_watch_list_take :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> ('v literal \<Rightarrow> 'v watched)\<close> where
  [simp]: \<open>op_watch_list_take W K i = W (K := take i (W K))\<close>

definition mop_watch_list_take :: \<open>('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> ('v literal \<Rightarrow> 'v watched) nres\<close> where
  \<open>mop_watch_list_take W K i = do {
      ASSERT(i \<le> length (W K));
      RETURN (W (K := take i (W K)))
   }\<close>

lemma shows
  op_watch_list:
    \<open>i < length (W K) \<Longrightarrow> mop_watch_list W K i \<le> SPEC(\<lambda>c. (c, op_watch_list W K i) \<in> Id)\<close> and
  op_watch_list_append:
    \<open>mop_watch_list_append W K x \<le> SPEC(\<lambda>c. (c, op_watch_list_append W K x) \<in> Id)\<close> and
  op_watch_list_take:
    \<open>i \<le> length (W K) \<Longrightarrow> mop_watch_list_take W K i \<le> SPEC(\<lambda>c. (c, op_watch_list_take W K i) \<in> Id)\<close>
  by (auto simp: mop_watch_list_def mop_watch_list_append_def mop_watch_list_take_def
   intro!: ASSERT_leI)


section \<open>Watch List Invariants\<close>

text \<open>
  We cannot just extract the literals of the clauses: we cannot be sure that atoms appear \<^emph>\<open>both\<close>
  positively and negatively in the clauses. If we could ensure that there are no pure literals, the
  definition of \<^term>\<open>all_lits_of_mm\<close> can be changed to \<open>all_lits_of_mm Ls = \<Sum><^sub># Ls\<close>.

  In this definition \<^term>\<open>K\<close> is the blocking literal.


  We have several different version of the watch-list invariants, either because we need a different
  version or to simplify proofs.

  \<^enum> CDCL: This is the invariant that is the most important.
     \<^item> binary clauses cannot be deleted
     \<^item> blocking literals are in the clause
     \<^item> the watched literals belong to the clause and are at the beginning.
     \<^item> the set of all literals is the set of all literals (irred+red)

  \<^enum> Inprocessing, deduplicating binary clauses
     \<^item> binary clauses can be deleted
     \<^item> blocking literals still are in the clause
     \<^item> the watched literals belong to the clause and are at the beginning.
     \<^item> the set of all literals is the set of all irredundant literals (irred)

  \<^enum> Inprocessing, removing true/false literals
     \<^item> all clauses appear in the watch list
     \<^item> the set of all literals is the set of all irredundant literals (irred)

(We also have the version for all literals)


  \<^enum> Reduction
     \<^item> all clauses appear in the watch list
     \<^item> the set of all literals is the set of all irredundant literals (irred)

   We use the set of irredundant literals because it is easier to handle removing literals --
   deleting a clause does not change the set of all irredundant literals. We then rely on the
   invariants to go back to the set of all literals.


  One additional constraint is that the watch lists do not contain duplicates. This might seem like
  a consequence from the fact that we are correctly watching. However, the invariant talks only
  about non-deleted clauses. Technically we would not need the distinctiveness at this level, but
  during refinement we need it in order to bound the length of the watch lists.

\<close>
fun correctly_marked_as_binary where
  \<open>correctly_marked_as_binary N (i, K, b) \<longleftrightarrow> (b \<longleftrightarrow> (length (N \<propto> i) = 2))\<close>

declare correctly_marked_as_binary.simps[simp del]

abbreviation distinct_watched :: \<open>'v watched \<Rightarrow> bool\<close> where
  \<open>distinct_watched xs \<equiv> distinct (map (\<lambda>(i, j, k). i) xs)\<close>

lemma distinct_watched_alt_def: \<open>distinct_watched xs = distinct (map fst xs)\<close>
  by (induction xs; auto)


fun correct_watching_except :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching_except i j K (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       (L = K \<longrightarrow>
         distinct_watched (take i (W L) @ drop j (W L)) \<and>
         ((\<forall>(i, K, b)\<in>#mset (take i (W L) @ drop j (W L)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and>
             K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (take i (W L) @ drop j (W L)). b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (take i (W L) @ drop j (W L))) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))) \<and>
       (L \<noteq> K \<longrightarrow>
         distinct_watched (W L) \<and>
         ((\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (W L). b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))))\<close>

fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).  b \<longrightarrow> i \<in># dom_m N) \<and>
       filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>

declare correct_watching.simps[simp del]


lemma all_lits_st_simps[simp]:
   \<open>all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(K := WK)) =
   all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
   \<open>all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, add_mset K Q, W) =
   all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> \<comment> \<open>actually covered below, but still useful for 'unfolding' by hand\<close>
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
     all_lits_st (x1b, x1aa(x1 \<hookrightarrow> WB_More_Refinement_List.swap (x1aa \<propto> x1) n n'), D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e,
             x2e) =
   all_lits_st
            (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e,
             x2e)\<close>
  \<open>all_lits_st (L # M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH {#} Q \<Longrightarrow> all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
     all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)\<close>
  \<open>NO_MATCH [] M \<Longrightarrow> all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
     all_lits_st ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH None D \<Longrightarrow> all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
  all_lits_st (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>all_lits_st (set_literals_to_update_wl WS S) = all_lits_st S\<close>
  by (cases S; auto simp: all_lits_st_def all_lits_def all_lits_of_mm_union ran_m_clause_upd
    image_mset_remove1_mset_if; fail)+

lemma in_clause_in_all_lits_of_mm[simp]:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow>
     x1aa \<propto> x1 ! n \<in># all_lits_st (x1b, x1aa, D, x1c, x1d, NS, US, N0, U0, x1e,
             x2e)\<close>
  by (auto simp: all_lits_st_def all_lits_def all_lits_of_mm_union ran_m_clause_upd
    all_lits_of_mm_add_mset in_clause_in_all_lits_of_m
    image_mset_remove1_mset_if ran_m_def dest!: multi_member_split)

lemma correct_watching_except_correct_watching:
  assumes
    j: \<open>j \<ge> length (W K)\<close> and
    corr: \<open>correct_watching_except i j K (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
 shows \<open>correct_watching (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(K := take i (W K)))\<close>
proof -
  have
    H1: \<open>\<And>L i' K' b. L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<Longrightarrow>
       (L = K \<Longrightarrow>
         distinct_watched (take i (W L) @ drop j (W L)) \<and>
         (((i', K', b)\<in>#mset (take i (W L) @ drop j (W L)) \<longrightarrow> i' \<in># dom_m N \<longrightarrow>
                K' \<in> set (N \<propto> i') \<and> K' \<noteq> L \<and> correctly_marked_as_binary N (i', K', b)) \<and>
         ((i', K', b)\<in>#mset (take i (W L) @ drop j (W L)) \<longrightarrow> b \<longrightarrow> i' \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (take i (W L) @ drop j (W L))) =
            clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})))\<close> and
    H2: \<open>\<And>L i K' b. L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<Longrightarrow> (L \<noteq> K \<Longrightarrow>
         distinct_watched (W L) \<and>
         (((i, K', b)\<in>#mset (W L) \<longrightarrow> i \<in># dom_m N \<longrightarrow> K' \<in> set (N \<propto> i) \<and> K' \<noteq> L \<and>
             (correctly_marked_as_binary N (i, K', b))) \<and>
          ((i, K', b)\<in>#mset (W L) \<longrightarrow> b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) =
             clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})))\<close>
    using corr unfolding correct_watching_except.simps
    by fast+
  show ?thesis
    unfolding correct_watching.simps
    apply (intro conjI allI impI ballI)
    subgoal for L
      apply (cases \<open>L = K\<close>)
      subgoal
        using H1[of L] j
        by (auto split: if_splits simp: all_lits_st_def)
      subgoal
        using H2[of L] j
        by (auto split: if_splits simp: all_lits_st_def)
      done
    subgoal for L x
      apply (cases \<open>L = K\<close>)
      subgoal
        using H1[of L \<open>fst x\<close> \<open>fst (snd x)\<close> \<open>snd (snd x)\<close>] j
        by (auto split: if_splits simp: all_lits_st_def)
      subgoal
        using H2[of L \<open>fst x\<close> \<open>fst (snd x)\<close> \<open>snd (snd x)\<close>]
        by auto
      done
    subgoal for L
      apply (cases \<open>L = K\<close>)
      subgoal
        using H1[of L _ _] j
        by (auto split: if_splits simp: all_lits_st_def)
      subgoal
        using H2[of L _ _]
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

lemma length_ge2I: \<open>x \<noteq> y \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> length xs \<ge> 2\<close>
  using card_length[of xs] card_mono[of \<open>set xs\<close> \<open>{x, y}\<close>]
  by auto

lemma correct_watching_except_alt_def:
  \<open>correct_watching_except i j K (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       (L = K \<longrightarrow>
         distinct_watched (take i (W L) @ drop j (W L)) \<and>
         ((\<forall>(i, K, b)\<in>#mset (take i (W L) @ drop j (W L)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and>
             K \<noteq> L \<and> L \<in> set (watched_l (N \<propto> i)) \<and> length (N \<propto> i) \<ge> 2 \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (take i (W L) @ drop j (W L)). b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (take i (W L) @ drop j (W L))) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))) \<and>
       (L \<noteq> K \<longrightarrow>
         distinct_watched (W L) \<and>
         ((\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> L \<in> set (watched_l(N \<propto> i)) \<and> length (N \<propto> i) \<ge> 2 \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (W L). b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))))\<close>
proof -
  have 1: \<open>correct_watching_except i j K (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       (L = K \<longrightarrow>
         distinct_watched (take i (W L) @ drop j (W L)) \<and>
         ((\<forall>(i, K, b)\<in>#mset (take i (W L) @ drop j (W L)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and>
             K \<noteq> L \<and> L \<in> set (watched_l (N \<propto> i)) \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (take i (W L) @ drop j (W L)). b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (take i (W L) @ drop j (W L))) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))) \<and>
       (L \<noteq> K \<longrightarrow>
         distinct_watched (W L) \<and>
         ((\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> L \<in> set (watched_l (N \<propto> i)) \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (W L). b \<longrightarrow> i \<in># dom_m N) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))))\<close>
      unfolding correct_watching_except.simps
      apply (intro impI ballI conjI iffI)
      subgoal by auto[]
      defer
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal for K x
        using distinct_mset_dom[of N]
        apply (clarsimp dest!: multi_member_split simp:  ran_m_def clause_to_update_def)
        apply (frule bspec[of \<open>set (W K)\<close>], assumption)
        apply (auto split: if_splits dest: in_set_takeD union_single_eq_member filter_mset_eq_add_msetD
           simp: in_set_conv_decomp[of _ \<open>W K\<close>] filter_union_or_split filter_eq_replicate_mset)
       done
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal
        using distinct_mset_dom[of N]
        apply (clarsimp dest!: multi_member_split simp:  ran_m_def clause_to_update_def)
        apply (fastforce split: if_splits dest: in_set_takeD union_single_eq_member
          simp: in_set_conv_decomp[of \<open>(_, _, _)\<close> \<open>take _ _\<close>] in_set_conv_decomp[of  \<open>(_, _, _)\<close> \<open>drop _ _\<close>])[]
        done
     done
  have H: \<open>(K \<in> set (N \<propto> i) \<and>  K \<noteq> L \<and> L \<in> set (watched_l (N \<propto> i)) \<and> P) \<longleftrightarrow>
       (K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> L \<in> set (watched_l (N \<propto> i)) \<and> length (N \<propto> i) \<ge> 2 \<and> P)\<close> for i K P L
    using length_ge2I[of K L] by (auto dest: in_set_takeD)
   show ?thesis
      unfolding 1 H[symmetric] ..
qed

definition clause_to_update_wl:: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v clauses_to_update_l\<close>where
  \<open>clause_to_update_wl L S =
    filter_mset
      (\<lambda>C::nat. L \<in> set (watched_l (get_clauses_wl S \<propto> C)))
      (dom_m (get_clauses_wl S))\<close>

(*TODO kill, see alt def below*)
fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v watched\<close> where
  \<open>watched_by (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) L = W L\<close>

lemma watched_by_alt_def: \<open>watched_by S L = get_watched_wl S L\<close>
  by (cases S) auto
(*END*)
definition all_atms :: \<open>_ \<Rightarrow> _ \<Rightarrow> 'v multiset\<close> where
  \<open>all_atms N NUE = atm_of `# all_lits N NUE\<close>

definition all_atms_st :: \<open>'v twl_st_wl \<Rightarrow> 'v multiset\<close> where
  \<open>all_atms_st S \<equiv> all_atms (get_clauses_wl S) (get_unit_clauses_wl S + get_subsumed_clauses_wl S + get_clauses0_wl S)\<close>

lemma all_atms_st_alt_def: \<open>all_atms_st S = atm_of `# all_lits_st S\<close>
  by (auto simp: all_atms_def all_lits_st_def all_atms_st_def)

lemmas all_atms_st_alt_def_sym[simp] =  all_atms_st_alt_def[symmetric]

lemma in_all_lits_minus_iff: \<open>-L \<in># all_lits N NUE \<longleftrightarrow> L \<in># all_lits N NUE\<close>
  unfolding all_lits_def in_all_lits_of_mm_uminus_iff ..

lemma all_lits_of_all_atms_of: \<open>K \<in># all_lits N NUE \<longleftrightarrow> K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NUE)\<close>
  by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_atms_def all_lits_def)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NE)) = set_mset (all_lits N NE)\<close>
  unfolding all_atms_def \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_lits_def ..


definition blits_in_\<L>\<^sub>i\<^sub>n :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>blits_in_\<L>\<^sub>i\<^sub>n S = (\<forall>L \<in># all_lits_st S. \<forall>(i, K, b) \<in> set (watched_by S L). K \<in># all_lits_st S)\<close>


definition literals_are_\<L>\<^sub>i\<^sub>n :: \<open>'v multiset \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<equiv> (is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_st S) \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>


lemma literals_are_in_\<L>\<^sub>i\<^sub>n_nth:
  fixes C :: nat
  assumes dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
   \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (get_clauses_wl S \<propto> C))\<close>
proof -
  let ?N = \<open>get_clauses_wl S\<close>
  have \<open>?N \<propto> C \<in># ran_mf ?N\<close>
    using dom by (auto simp: ran_m_def)
  then have \<open>mset (?N \<propto> C) \<in># mset `# (ran_mf ?N)\<close>
    by blast
  from all_lits_of_m_subset_all_lits_of_mmD[OF this] show ?thesis
    using assms(2) unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n_def
    by (auto simp: all_lits_st_def all_lits_of_mm_union all_lits_alt_def)
qed

lemma literals_are_\<L>\<^sub>i\<^sub>n_set_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<Longrightarrow> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  using in_all_lits_of_mm_ain_atms_of_iff
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_st_def
    all_lits_def
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_atms_def simp del: all_atms_st_alt_def_sym
    simp: all_lits_def all_atms_st_def)

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_all_lits_st_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]:
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_st S) \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits N NUE) \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NUE)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits N NUE) \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits N NUE)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  using in_all_lits_of_mm_ain_atms_of_iff
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n all_lits_st_def all_atms_st_def
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_lits_def all_atms_def)


lemma in_set_all_atms_iff:
  \<open>y \<in># all_atms bu bw \<longleftrightarrow>
    y \<in> atms_of_mm (mset `# ran_mf bu) \<or> y \<in> atms_of_mm bw\<close>
  by (auto simp: all_atms_def all_lits_def in_all_lits_of_mm_ain_atms_of_iff
     atm_of_all_lits_of_mm)


lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch:
  assumes \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close> and
    w:\<open>w < length (watched_by (a, b, c, d, e,  NEk, UEk, NS, US, N0, U0, f, g) K)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g (K := (g K)[j := g K ! w]))\<close>
proof -
  let ?S = \<open>(a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  let ?T = \<open>(a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g (K := (g K)[j := g K ! w]))\<close>
  let ?g = \<open>g (K := (g K)[j := g K ! w])\<close>
  have H: \<open>\<And>L i K b. L\<in># all_lits_st ?S \<Longrightarrow> (i, K, b) \<in>set (g L) \<Longrightarrow>
        K \<in># all_lits_st ?S\<close>
    using assms
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
  have \<open> L\<in># all_lits_st ?S \<Longrightarrow> (i, K', b') \<in>set (?g L) \<Longrightarrow>
        K' \<in># all_lits_st ?S\<close> for L i K' b'
    using H[of L i K'] H[of L \<open>fst (g K ! w)\<close> \<open>fst (snd (g K ! w))\<close>]
      nth_mem[OF w]
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by (cases \<open>j < length (g K)\<close>; cases \<open>g K ! w\<close>)
      (auto split: if_splits elim!: in_set_upd_cases)
  moreover have \<open>all_atms_st ?S = all_atms_st ?T\<close>
    by (auto simp: all_lits_def all_atms_def all_atms_st_def)
  ultimately show ?thesis
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by force
qed

lemma all_lits_swap[simp]:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
   all_lits
            (x1aa(x1 \<hookrightarrow> swap (x1aa \<propto> x1) n n'))
            (x1cx1d) =
  all_lits x1aa (x1cx1d)\<close>
  using distinct_mset_dom[of x1aa]
  apply (auto simp: ran_m_def all_lits_def dest!: multi_member_split)
  apply (subst image_mset_cong[of _ \<open>%x. mset
           (fst (the (fmlookup x1aa x)))\<close>])
  apply auto
  done

lemma blits_in_\<L>\<^sub>i\<^sub>n_propagate:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (Propagated A x1' # x1b, x1aa
         (x1 \<hookrightarrow> swap (x1aa \<propto> x1) n n'), D, x1c, x1d,
          NEk, UEk, NS, US, N0, U0, add_mset A' x1e, x2e) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)\<close>
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa
         (x1 \<hookrightarrow> swap (x1aa \<propto> x1) n n'), D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)\<close>
  \<open>blits_in_\<L>\<^sub>i\<^sub>n
        (Propagated A x1' # x1b, x1aa, D, x1c, x1d,
         NEk, UEk, NS, US, N0, U0, add_mset A' x1e, x2e) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)\<close>
  \<open>x1' \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1') \<Longrightarrow> n' < length (x1aa \<propto> x1') \<Longrightarrow>
    K \<in># all_lits_st (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n
        (x1a, x1aa(x1' \<hookrightarrow> swap (x1aa \<propto> x1') n n'), D, x1c, x1d,
         NEk, UEk, NS, US, N0, U0, x1e, x2e
         (x1aa \<propto> x1' ! n' :=
            x2e (x1aa \<propto> x1' ! n') @ [(x1', K, b')])) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)\<close>
  \<open>K \<in># all_lits_st (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<Longrightarrow>
     blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, D, x1c, x1d,
         NEk, UEk, NS, US, N0, U0, x1e, x2e
         (K' := x2e K' @ [(x1', K, b')])) \<longleftrightarrow>
  blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)\<close>
  unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
  by (auto split: if_splits)

lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch':
  assumes K': \<open>fst (snd w) \<in># all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close> and
    w:\<open> blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g (K := (g K)[j := w]))\<close>
proof -
  let ?\<A> = \<open>all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  let ?g = \<open>g (K := (g K)[j := w])\<close>
  have H: \<open>\<And>L i K b'. L\<in># ?\<A> \<Longrightarrow> (i, K, b') \<in>set (g L) \<Longrightarrow> K \<in># ?\<A>\<close>
    using assms
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
  have \<open>L\<in># ?\<A> \<Longrightarrow> (i, K', b') \<in>set (?g L) \<Longrightarrow> K' \<in># ?\<A>\<close> for L i K' b'
    using H[of L i K'] K'
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by (cases \<open>j < length (g K)\<close>)
      (auto split: if_splits elim!: in_set_upd_cases)

  then show ?thesis
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by force
qed


lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'':
  assumes K': \<open>K' \<in># all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
    \<open>L' \<in># all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close> and
    w:\<open> blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f,
    g (K := (g K)[j := (i, K', b')], L := g L @ [(i', L', b'')]))\<close>
  using assms
  unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
  by (auto split: if_splits elim!: in_set_upd_cases)

lemma clause_to_update_wl_alt_def:
   \<open>clause_to_update_wl L (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g) =
     clause_to_update L (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
  unfolding clause_to_update_wl_def clause_to_update_def by simp

lemma correct_watching_except_alt_def2:
  \<open>correct_watching_except i j K S \<longleftrightarrow>
    (\<forall>L \<in># all_lits_st S.
       (L = K \<longrightarrow>
         distinct_watched (take i (watched_by S L) @ drop j (watched_by S L)) \<and>
         ((\<forall>(i, K, b)\<in>#mset (take i (watched_by S L) @ drop j (watched_by S L)). i \<in># dom_m (get_clauses_wl S) \<longrightarrow> K \<in> set (get_clauses_wl S \<propto> i) \<and>
             K \<noteq> L \<and> L \<in> set (watched_l (get_clauses_wl S \<propto> i)) \<and> length (get_clauses_wl S \<propto> i) \<ge> 2 \<and> correctly_marked_as_binary (get_clauses_wl S) (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (take i (watched_by S L) @ drop j (watched_by S L)). b \<longrightarrow> i \<in># dom_m (get_clauses_wl S)) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m (get_clauses_wl S)) (fst `# mset (take i (watched_by S L) @ drop j (watched_by S L))) = clause_to_update_wl L S)) \<and>
       (L \<noteq> K \<longrightarrow>
         distinct_watched (watched_by S L) \<and>
         ((\<forall>(i, K, b)\<in>#mset (watched_by S L). i \<in># dom_m (get_clauses_wl S) \<longrightarrow> K \<in> set (get_clauses_wl S \<propto> i) \<and> K \<noteq> L \<and> L \<in> set (watched_l (get_clauses_wl S \<propto> i)) \<and> length (get_clauses_wl S \<propto> i) \<ge> 2 \<and> correctly_marked_as_binary (get_clauses_wl S) (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (watched_by S L). b \<longrightarrow> i \<in># dom_m (get_clauses_wl S)) \<and>
         filter_mset (\<lambda>i. i \<in># dom_m (get_clauses_wl S)) (fst `# mset (watched_by S L)) = clause_to_update_wl L S)))\<close>
  by (cases S; hypsubst)
    (simp only: correct_watching_except_alt_def watched_by.simps
      get_clauses_wl.simps clause_to_update_wl_alt_def get_unit_clauses_wl.simps)

fun update_watched :: \<open>'v literal \<Rightarrow> 'v watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
     (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(L:= WL))\<close>

definition mop_watched_by_at :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> 'v watcher nres\<close> where
\<open>mop_watched_by_at = (\<lambda>S L w. do {
   ASSERT(L \<in># all_lits_st S);
   ASSERT(w < length (watched_by S L));
  RETURN (watched_by S L ! w)
})\<close>


lemma bspec': \<open>x \<in> a \<Longrightarrow> \<forall>x\<in>a. P x \<Longrightarrow> P x\<close>
  by (rule bspec)

lemma correct_watching_exceptD:
  assumes
    \<open>correct_watching_except i j L S\<close> and
    \<open>L \<in># all_lits_st S\<close> and
    w: \<open>w < length (watched_by S L)\<close> \<open>w \<ge> j\<close> \<open>fst (watched_by S L ! w) \<in># dom_m (get_clauses_wl S)\<close>
  shows \<open>fst (snd (watched_by S L ! w)) \<in> set (get_clauses_wl S \<propto> (fst (watched_by S L ! w)))\<close>
proof -
  have H: \<open>\<And>x. x\<in>set (take i (watched_by S L)) \<union> set (drop j (watched_by S L)) \<Longrightarrow>
          case x of (i, K, b) \<Rightarrow> i \<in># dom_m (get_clauses_wl S) \<longrightarrow> K \<in> set (get_clauses_wl S \<propto> i) \<and>
           K \<noteq> L\<close>
    using assms multi_member_split[OF assms(2)]
    by (cases S; cases \<open>watched_by S L ! w\<close>)
     (clarsimp, blast)
  have \<open>\<exists>i\<ge>j. i < length (watched_by S L) \<and>
            watched_by S L ! w = watched_by S L ! i\<close>
    by (rule exI[of _ w])
      (use w in auto)
  then show ?thesis
    using H[of \<open>watched_by S L ! w\<close>] w
    by (cases \<open>watched_by S L ! w\<close>) (auto simp: in_set_drop_conv_nth)
qed

declare correct_watching_except.simps[simp del]


fun st_l_of_wl :: \<open>('v literal \<times> nat) option \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl None (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, Q)\<close>
| \<open>st_l_of_wl (Some (L, j)) (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0,
     (if D \<noteq> None then {#} else clauses_to_update_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) L j,
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
    \<open>get_unit_learned_clss_l T = get_unit_learned_clss_wl S\<close>
    \<open>get_unit_init_clauses_l T = get_unit_init_clss_wl S\<close>
    \<open>get_unit_learned_clss_l T = get_unit_learned_clss_wl S\<close>
    \<open>get_unit_clauses_l T = get_unit_clauses_wl S\<close>
    \<open>get_kept_unit_clauses_l T = get_kept_unit_clauses_wl S\<close>
    \<open>get_subsumed_init_clauses_l T = get_subsumed_init_clauses_wl S\<close>
    \<open>get_subsumed_learned_clauses_l T = get_subsumed_learned_clauses_wl S\<close>
    \<open>get_subsumed_clauses_l T = get_subsumed_clauses_wl S\<close>
    \<open>get_init_clauses0_l T = get_init_clauses0_wl S\<close>
    \<open>get_learned_clauses0_l T = get_learned_clauses0_wl S\<close>
    \<open>get_clauses0_l T = get_clauses0_wl S\<close>
    \<open>get_init_clss_l T = get_init_clss_wl S\<close>
    \<open>all_lits_of_st_l T = all_lits_st S\<close>
    \<open>get_unkept_learned_clss_l T = get_unkept_learned_clss_wl S\<close>
    \<open>all_lits_of_mm (get_all_clss_l T) = all_lits_st S\<close>
  using assms unfolding state_wl_l_def all_clss_lf_ran_m[symmetric]
  apply (cases S; cases T; cases L; auto split: option.splits simp: get_init_clss_l_def
    all_lits_st_def all_lits_def all_lits_of_st_l_def ac_simps; fail)+
  using assms unfolding state_wl_l_def all_clss_lf_ran_m[symmetric] all_lits_st_def all_lits_def
  apply (subst all_clss_lf_ran_m)
  by (cases S; cases T; cases L; auto split: option.splits simp: get_init_clss_l_def ac_simps)

lemma [twl_st_wl]:
  \<open>(a, a') \<in> state_wl_l None \<Longrightarrow>
        get_learned_clss_l a' = get_learned_clss_wl a\<close>
  unfolding state_wl_l_def by (cases a; cases a')
   (auto simp: get_learned_clss_l_def get_learned_clss_wl_def)

lemma remove_one_lit_from_wq_def:
  \<open>remove_one_lit_from_wq L S = set_clauses_to_update_l (clauses_to_update_l S - {#L#}) S\<close>
  by (cases S) auto

lemma correct_watching_set_literals_to_update[simp]:
  \<open>correct_watching (set_literals_to_update_wl WS T') = correct_watching T'\<close>
  by (cases T') (auto simp: correct_watching.simps)

lemma [twl_st_wl]:
  \<open>get_clauses_wl (set_literals_to_update_wl W S) = get_clauses_wl S\<close>
  \<open>get_unit_init_clss_wl (set_literals_to_update_wl W S) = get_unit_init_clss_wl S\<close>
  by (cases S; auto; fail)+

lemma get_conflict_wl_set_literals_to_update_wl[twl_st_wl]:
  \<open>get_conflict_wl (set_literals_to_update_wl P S) = get_conflict_wl S\<close>
  \<open>get_unit_clauses_wl (set_literals_to_update_wl P S) = get_unit_clauses_wl S\<close>
  \<open>get_init_clauses0_wl (set_literals_to_update_wl P S) = get_init_clauses0_wl S\<close>
  \<open>get_learned_clauses0_wl (set_literals_to_update_wl P S) = get_learned_clauses0_wl S\<close>
  \<open>get_clauses0_wl (set_literals_to_update_wl P S) = get_clauses0_wl S\<close>
  by (cases S; auto; fail)+

definition set_conflict_wl_pre :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>set_conflict_wl_pre C S \<longleftrightarrow>
   (\<exists>S' b. (S, S') \<in> state_wl_l b \<and> set_conflict_l_pre C S' \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>

definition set_conflict_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>set_conflict_wl = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
     ASSERT(set_conflict_wl_pre C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     RETURN (M, N, Some (mset (N \<propto> C)), NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)
   })\<close>

lemma state_wl_l_mark_of_is_decided:
  \<open>(x, y) \<in> state_wl_l b \<Longrightarrow>
       get_trail_wl x \<noteq> [] \<Longrightarrow>
       is_decided (hd (get_trail_l y)) = is_decided (hd (get_trail_wl x))\<close>
  by (cases \<open>get_trail_wl x\<close>; cases \<open>get_trail_l y\<close>; cases \<open>hd (get_trail_wl x)\<close>;
     cases \<open>hd (get_trail_l y)\<close>; cases b; cases x)
   (auto simp: state_wl_l_def convert_lit.simps st_l_of_wl.simps)

lemma state_wl_l_mark_of_is_proped:
  \<open>(x, y) \<in> state_wl_l b \<Longrightarrow>
       get_trail_wl x \<noteq> [] \<Longrightarrow>
       is_proped (hd (get_trail_l y)) = is_proped (hd (get_trail_wl x))\<close>
  by (cases \<open>get_trail_wl x\<close>; cases \<open>get_trail_l y\<close>; cases \<open>hd (get_trail_wl x)\<close>;
     cases \<open>hd (get_trail_l y)\<close>; cases b; cases x)
   (auto simp: state_wl_l_def convert_lit.simps)

text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>.\<close>
declare twl_st_wl[simp]


lemma
  assumes
      x2_T: \<open>(x2, T) \<in> state_wl_l b\<close> and
      struct: \<open>twl_struct_invs U\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l b'\<close>
  shows
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail:
      \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2 \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n (get_trail_wl x2)\<close>
     (is \<open>_\<Longrightarrow> ?trail\<close>) and
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict:
      \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2 \<Longrightarrow> get_conflict_wl x2 \<noteq> None \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close> and
    conflict_not_tautology:
      \<open>get_conflict_wl x2 \<noteq> None \<Longrightarrow> \<not>tautology (the (get_conflict_wl x2))\<close>
proof -
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of U)\<close> and
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of U)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      pcdcl_all_struct_invs_def state\<^sub>W_of_def
   by fast+

  show lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n (get_trail_wl x2)\<close>
    if \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2\<close>
    using alien that x2_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def all_atms_def all_lits_st_def
    by (subst (asm) all_clss_l_ran_m[symmetric])
      (auto 5 2
        simp del: all_clss_l_ran_m union_filter_mset_complement
        simp: twl_st twl_st_l twl_st_wl all_lits_of_mm_union lits_of_def
        convert_lits_l_def image_image in_all_lits_of_mm_ain_atms_of_iff
        get_unit_clauses_wl_alt_def Un_assoc ac_simps
      simp flip: state\<^sub>W_of_def)

  {
    assume conf: \<open>get_conflict_wl x2 \<noteq> None\<close>
    show lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close>
      if \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2\<close>
      using x2_T T_U alien that conf unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def
       literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def all_atms_def all_lits_st_def
      apply (subst (asm) all_clss_l_ran_m[symmetric])
      unfolding image_mset_union all_lits_of_mm_union
      by (auto simp add: twl_st all_lits_of_mm_union lits_of_def
         image_image in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff
        get_unit_clauses_wl_alt_def
        simp del: all_clss_l_ran_m
      simp flip: state\<^sub>W_of_def)

    have M_confl: \<open>get_trail_wl x2 \<Turnstile>as CNot (the (get_conflict_wl x2))\<close>
      using confl conf x2_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto 5 5 simp: twl_st true_annots_def)
    moreover have n_d: \<open>no_dup (get_trail_wl x2)\<close>
      using M_lev x2_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: twl_st)
    ultimately show 4: \<open>\<not>tautology (the (get_conflict_wl x2))\<close>
      using n_d M_confl
      by (meson no_dup_consistentD tautology_decomp' true_annots_true_cls_def_iff_negation_in_model)
  }
qed



fun equality_except_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>equality_except_conflict_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
     (M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', WS', Q') \<longleftrightarrow>
  M = M' \<and> N = N' \<and> NE = NE' \<and> UE = UE' \<and> NEk = NEk' \<and> UEk = UEk' \<and> NS = NS' \<and> US = US' \<and>
  N0 = N0' \<and> U0 = U0' \<and> WS = WS' \<and> Q = Q'\<close>

fun equality_except_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>equality_except_trail_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
     (M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', WS', Q') \<longleftrightarrow>
  N = N' \<and> D = D' \<and> NE = NE' \<and> NEk = NEk' \<and> UEk = UEk' \<and> NS = NS' \<and> US = US' \<and> UE = UE' \<and>
  N0 = N0' \<and> U0 = U0' \<and> WS = WS' \<and> Q = Q'\<close>

lemma equality_except_conflict_wl_get_clauses_wl:
    \<open>equality_except_conflict_wl S Y \<Longrightarrow> get_clauses_wl S = get_clauses_wl Y\<close> and
  equality_except_conflict_wl_get_trail_wl:
    \<open>equality_except_conflict_wl S Y \<Longrightarrow> get_trail_wl S = get_trail_wl Y\<close> and
  equality_except_trail_wl_get_conflict_wl:
    \<open>equality_except_trail_wl S Y \<Longrightarrow> get_conflict_wl S = get_conflict_wl Y\<close> and
  equality_except_trail_wl_get_clauses_wl:
    \<open>equality_except_trail_wl S Y\<Longrightarrow> get_clauses_wl S = get_clauses_wl Y\<close> and
  equality_except_trail_wl_get_clauses0_wl:
    \<open>equality_except_trail_wl S Y\<Longrightarrow> get_clauses0_wl S = get_clauses0_wl Y\<close>
 by (cases S; cases Y; solves auto)+


definition unit_prop_body_wl_inv where
\<open>unit_prop_body_wl_inv T j i L \<longleftrightarrow> (i < length (watched_by T L) \<and> j \<le> i \<and>
    L \<in># all_lits_st T \<and> blits_in_\<L>\<^sub>i\<^sub>n T \<and>
   (fst (watched_by T L ! i) \<in># dom_m (get_clauses_wl T) \<longrightarrow>
    (\<exists>T'. (T, T') \<in> state_wl_l (Some (L, Suc i)) \<and> j \<le> i \<and>
    unit_propagation_inner_loop_body_l_inv L (fst (watched_by T L ! i)) T' \<and>
     correct_watching_except (Suc j) (Suc i) L T)))\<close>

lemma unit_prop_body_wl_inv_alt_def:
  \<open>unit_prop_body_wl_inv T j i L \<longleftrightarrow> (i < length (watched_by T L) \<and> j \<le> i \<and>
    L \<in># all_lits_st T \<and> blits_in_\<L>\<^sub>i\<^sub>n T \<and>
   (fst (watched_by T L ! i) \<in># dom_m (get_clauses_wl T) \<longrightarrow>
    (\<exists>T'. (T, T') \<in> state_wl_l (Some (L, Suc i)) \<and>
    unit_propagation_inner_loop_body_l_inv L (fst (watched_by T L ! i)) T' \<and>
     correct_watching_except (Suc j) (Suc i) L T \<and>
    get_conflict_wl T = None \<and>
    length (get_clauses_wl T \<propto> fst (watched_by T L ! i)) \<ge> 2)))\<close>
  (is \<open>?A = ?B\<close>)
proof
  assume ?B
  then show ?A
    unfolding unit_prop_body_wl_inv_def
    by blast
next
  assume ?A
  then show ?B
  proof (cases \<open>fst (watched_by T L ! i) \<in># dom_m (get_clauses_wl T)\<close>)
    case False
    then show ?B
      using \<open>?A\<close> unfolding unit_prop_body_wl_inv_def
      by blast
  next
    case True
    then obtain T' where
      \<open>i < length (watched_by T L)\<close>
      \<open>j \<le> i\<close> and
      TT': \<open>(T, T') \<in> state_wl_l (Some (L, Suc i))\<close> and
      inv: \<open>unit_propagation_inner_loop_body_l_inv L (fst (watched_by T L ! i))
         T'\<close> and
      \<open>L \<in># all_lits_st T\<close>
      \<open>correct_watching_except (Suc j) (Suc i) L T\<close>
      using \<open>?A\<close> unfolding unit_prop_body_wl_inv_def
      by blast

    obtain x where
      x: \<open>(set_clauses_to_update_l
         (clauses_to_update_l T' + {#fst (watched_by T L ! i)#}) T', x)
       \<in> twl_st_l (Some L)\<close> and
      struct_invs: \<open>twl_struct_invs x\<close> and
      \<open>twl_stgy_invs x\<close> and
      \<open>fst (watched_by T L ! i) \<in># dom_m (get_clauses_l T')\<close> and
      \<open>0 < fst (watched_by T L ! i)\<close> and
      \<open>0 < length (get_clauses_l T' \<propto> fst (watched_by T L ! i))\<close> and
      \<open>no_dup (get_trail_l T')\<close> and
      \<open>(if get_clauses_l T' \<propto> fst (watched_by T L ! i) ! 0 = L then 0 else 1)
       < length (get_clauses_l T' \<propto> fst (watched_by T L ! i))\<close> and
      \<open>1 - (if get_clauses_l T' \<propto> fst (watched_by T L ! i) ! 0 = L then 0 else 1)
       < length (get_clauses_l T' \<propto> fst (watched_by T L ! i))\<close> and
      \<open>L \<in> set (watched_l (get_clauses_l T' \<propto> fst (watched_by T L ! i)))\<close> and
      confl: \<open>get_conflict_l T' = None\<close>
      using inv unfolding unit_propagation_inner_loop_body_l_inv_def by blast

    have \<open>Multiset.Ball (get_clauses x) struct_wf_twl_cls\<close>
      using struct_invs unfolding twl_struct_invs_def twl_st_inv_alt_def by blast
    moreover have \<open>twl_clause_of (get_clauses_wl T \<propto> fst (watched_by T L ! i)) \<in># get_clauses x\<close>
      using TT' x True by auto
    ultimately have 1: \<open>length (get_clauses_wl T \<propto> fst (watched_by T L ! i)) \<ge> 2\<close>
      by auto
    have 2: \<open>get_conflict_wl T = None\<close>
      using confl TT' x by auto
    show ?B
      using \<open>?A\<close> 1 2 unfolding unit_prop_body_wl_inv_def
      by blast
  qed
qed

definition propagate_lit_wl_general :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_lit_wl_general = (\<lambda>L' C i (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(C \<in># dom_m N);
      ASSERT(D = None);
      ASSERT(L' \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
      ASSERT(i \<le> 1);
      M \<leftarrow> cons_trail_propagate_l L' C M;
      N \<leftarrow> (if length (N \<propto> C) > 2 then mop_clauses_swap N C 0 (Suc 0 - i) else RETURN N);
      RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, add_mset (-L') Q, W) })\<close>

definition propagate_lit_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_lit_wl = (\<lambda>L' C i (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(C \<in># dom_m N);
      ASSERT(D = None);
      ASSERT(L' \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
      ASSERT(i \<le> 1);
      M \<leftarrow> cons_trail_propagate_l L' C M;
      N \<leftarrow> mop_clauses_swap N C 0 (Suc 0 - i);
      RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, add_mset (-L') Q, W)
   })\<close>

definition propagate_lit_wl_bin :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_lit_wl_bin = (\<lambda>L' C (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(D = None);
      ASSERT(C \<in># dom_m N);
      ASSERT(L' \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
      M \<leftarrow> cons_trail_propagate_l L' C M;
      RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, add_mset (-L') Q, W)})\<close>

definition propagate_lit_wl_bin' ::\<open> 'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
   where
\<open>propagate_lit_wl_bin' L' C i = propagate_lit_wl_bin L' C\<close>

definition keep_watch :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>keep_watch = (\<lambda>L i j (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
      (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(L := (W L)[i := W L ! j])))\<close>

definition mop_keep_watch :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>mop_keep_watch = (\<lambda>L i j S. do {
    ASSERT(L \<in># all_lits_st S);
    ASSERT(i < length (watched_by S L));
    ASSERT(j < length (watched_by S L));
    RETURN (keep_watch L i j S)
  })\<close>

lemma length_watched_by_keep_watch[twl_st_wl]:
  \<open>length (watched_by (keep_watch L i j S) K) = length (watched_by S K)\<close>
  by (cases S) (auto simp: keep_watch_def)

lemma watched_by_keep_watch_neq[twl_st_wl, simp]:
  \<open>w < length (watched_by S L) \<Longrightarrow> watched_by (keep_watch L j w S) L ! w = watched_by S L ! w\<close>
  by (cases S) (auto simp: keep_watch_def)

lemma watched_by_keep_watch_eq[twl_st_wl, simp]:
  \<open>j < length (watched_by S L) \<Longrightarrow> watched_by (keep_watch L j w S) L ! j = watched_by S L ! w\<close>
  by (cases S) (auto simp: keep_watch_def)


definition update_clause_wl :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>update_clause_wl = (\<lambda>(L::'v literal) other_watched C b j w i f (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
     ASSERT(C \<in># dom_m N \<and> j \<le> w \<and> w < length (W L) \<and>
        correct_watching_except (Suc j) (Suc w) L (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     ASSERT(L \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     ASSERT(other_watched \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     K' \<leftarrow> mop_clauses_at N C f;
     ASSERT(K' \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<and> L \<noteq> K');
     N' \<leftarrow> mop_clauses_swap N C i f;
     RETURN (j, w+1, (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(K' := W K' @ [(C, other_watched, b)])))
  })\<close>


definition update_blit_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>update_blit_wl = (\<lambda>(L::'v literal) C b j w K (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
     ASSERT(L \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     ASSERT(K \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     ASSERT(j \<le> w);
     ASSERT(w < length (W L));
     ASSERT(C \<in># dom_m N);
     RETURN (j+1, w+1, (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(L := (W L)[j:=(C, K, b)])))
  })\<close>


definition unit_prop_body_wl_find_unwatched_inv where
\<open>unit_prop_body_wl_find_unwatched_inv f C S \<longleftrightarrow> True\<close>

abbreviation remaining_nondom_wl where
\<open>remaining_nondom_wl w L S \<equiv>
  (if get_conflict_wl S = None
          then size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl S)) (mset (drop w (watched_by S L)))) else 0)\<close>

definition unit_propagation_inner_loop_wl_loop_inv where
  \<open>unit_propagation_inner_loop_wl_loop_inv L = (\<lambda>(j, w, S).
    (\<exists>S'. (S, S') \<in> state_wl_l (Some (L, w)) \<and> j\<le> w \<and>
       unit_propagation_inner_loop_l_inv L (S', remaining_nondom_wl w L S) \<and>
      correct_watching_except j w L S \<and> w \<le> length (watched_by S L)))\<close>

lemma correct_watching_except_correct_watching_except_Suc_Suc_keep_watch:
  assumes
    j_w: \<open>j \<le> w\<close> and
    w_le: \<open>w < length (watched_by S L)\<close> and
    corr: \<open>correct_watching_except j w L S\<close>
  shows \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
proof -
  obtain M N D NE UE NEk UEk NS US N0 U0 Q W where S: \<open>S = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> by (cases S)
  let ?\<L> = \<open>all_lits_st S\<close>
  have
    Hneq: \<open>\<And>La. La\<in>#?\<L> \<longrightarrow>
        (La \<noteq> L \<longrightarrow>
	  distinct_watched (W La) \<and>
         (\<forall>(i, K, b)\<in>#mset (W La). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
             correctly_marked_as_binary N (i, K, b)) \<and>
         (\<forall>(i, K, b)\<in>#mset (W La). b \<longrightarrow> i \<in># dom_m N) \<and>
         {#i \<in># fst `# mset (W La). i \<in># dom_m N#} = clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close> and
    Heq: \<open>\<And>La. La\<in>#?\<L> \<longrightarrow>
        (La = L \<longrightarrow>
	 distinct_watched (take j (W La) @ drop w (W La)) \<and>
         (\<forall>(i, K, b)\<in>#mset (take j (W La) @ drop w (W La)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and>
            K \<noteq> La \<and> correctly_marked_as_binary N (i, K, b)) \<and>
         (\<forall>(i, K, b)\<in>#mset (take j (W La) @ drop w (W La)). b \<longrightarrow> i \<in># dom_m N) \<and>
         {#i \<in># fst `# mset (take j (W La) @ drop w (W La)). i \<in># dom_m N#} =
         clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>
    using corr unfolding S correct_watching_except.simps
    by fast+

  have eq: \<open>mset (take (Suc j) ((W(L := (W L)[j := W L ! w])) La) @ drop (Suc w) ((W(L := (W L)[j := W L ! w])) La)) =
     mset (take j (W La) @ drop w (W La))\<close> if [simp]: \<open>La = L\<close> for La
    using w_le j_w
    by (auto simp: S take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
        list_update_append)

  have \<open>case x of (i, K, b) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
           correctly_marked_as_binary N (i, K, b)\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close> and
      \<open>x \<in># mset (take (Suc j) ((W(L := (W L)[j := W L ! w])) La) @
                 drop (Suc w) ((W(L := (W L)[j := W L ! w])) La))\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Heq[of L]
    apply (subst (asm) eq)
    by (simp_all add: eq)
  moreover have \<open>case x of (i, K, b) \<Rightarrow> b \<longrightarrow> i \<in># dom_m N\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close> and
      \<open>x \<in># mset (take (Suc j) ((W(L := (W L)[j := W L ! w])) La) @
                 drop (Suc w) ((W(L := (W L)[j := W L ! w])) La))\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Heq[of L]
    by (subst (asm) eq) blast+
  moreover have \<open>{#i \<in># fst `#
              mset
               (take (Suc j) ((W(L := (W L)[j := W L ! w])) La) @
                drop (Suc w) ((W(L := (W L)[j := W L ! w])) La)).
       i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close>
    for La :: \<open>'a literal\<close>
    using that Heq[of L]
    by (subst eq) simp_all
  moreover have \<open>case x of (i, K, b) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
        correctly_marked_as_binary N (i, K, b)\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close> and
      \<open>x \<in># mset ((W(L := (W L)[j := W L ! w])) La)\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>case x of (i, K, b) \<Rightarrow> b \<longrightarrow> i \<in># dom_m N\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close> and
      \<open>x \<in># mset ((W(L := (W L)[j := W L ! w])) La)\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Hneq[of La]
    by auto
  moreover have \<open>{#i \<in># fst `# mset ((W(L := (W L)[j := W L ! w])) La). i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close>
    for La :: \<open>'a literal\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>distinct_watched ((W(L := (W L)[j := W L ! w])) La)\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close>
    for La :: \<open>'a literal\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>distinct_watched (take (Suc j) ((W(L := (W L)[j := W L ! w])) La) @
                drop (Suc w) ((W(L := (W L)[j := W L ! w])) La))\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close>
    for La :: \<open>'a literal\<close>
    using that Heq[of La]
    apply (subst distinct_mset_mset_distinct[symmetric])
    apply (subst mset_map)
    apply (subst eq)
    apply (simp add: that)
    apply (subst mset_map[symmetric])
    apply (subst distinct_mset_mset_distinct)
    apply simp
    done
  ultimately show ?thesis
    unfolding S keep_watch_def prod.simps correct_watching_except.simps all_lits_st_simps
    by meson
qed


lemma correct_watching_except_update_blit:
  assumes
    corr: \<open>correct_watching_except i j L (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g(L := (g L)[j' := (x1, C, b')]))\<close> and
    C': \<open>C' \<in># all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
      \<open>C' \<in> set (b \<propto> x1)\<close>
      \<open>C' \<noteq> L\<close> and
    corr_watched: \<open>correctly_marked_as_binary b (x1, C', b')\<close>
  shows \<open>correct_watching_except i j L (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g(L := (g L)[j' := (x1, C', b')]))\<close>
proof -
  let ?\<L> = \<open>all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  have
    Hdisteq: \<open>\<And>La i' K' b''. La\<in>#?\<L> \<Longrightarrow>
        (La = L \<longrightarrow>
	 distinct_watched (take i ((g(L := (g L)[j' := (x1, C, b')])) La) @ drop j ((g(L := (g L)[j' := (x1, C, b')])) La)))\<close> and
    Heq: \<open>\<And>La i' K' b''. La\<in>#?\<L> \<Longrightarrow>
        (La = L \<longrightarrow>
         (((i', K', b'')\<in>#mset (take i ((g(L := (g L)[j' := (x1, C, b')])) La) @ drop j ((g(L := (g L)[j' := (x1, C, b')])) La)) \<longrightarrow>
             i' \<in># dom_m b \<longrightarrow> K' \<in> set (b \<propto> i') \<and> K' \<noteq> La \<and> correctly_marked_as_binary b (i', K', b'')) \<and>
          ((i', K', b'')\<in>#mset (take i ((g(L := (g L)[j' := (x1, C, b')])) La) @ drop j ((g(L := (g L)[j' := (x1, C, b')])) La)) \<longrightarrow>
              b'' \<longrightarrow> i' \<in># dom_m b)) \<and>
         {#i \<in># fst `# mset (take i ((g(L := (g L)[j' := (x1, C, b')])) La) @ drop j ((g(L := (g L)[j' := (x1, C, b')])) La)).
          i \<in># dom_m b#} =
         clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close> and
    Hdistneq: \<open>\<And>La i' K' b''. La\<in>#?\<L> \<Longrightarrow>
        (La \<noteq> L \<longrightarrow> distinct_watched (((g(L := (g L)[j' := (x1, C, b')])) La)))\<close> and
    Hneq: \<open>\<And>La i K b''. La\<in>#?\<L> \<Longrightarrow> La \<noteq> L \<Longrightarrow>
         distinct_watched (((g(L := (g L)[j' := (x1, C, b')])) La)) \<and>
         ((i, K, b'')\<in>#mset ((g(L := (g L)[j' := (x1, C, b')])) La)\<longrightarrow> i \<in># dom_m b \<longrightarrow>
            K \<in> set (b \<propto> i) \<and> K \<noteq> La \<and> correctly_marked_as_binary b (i, K, b'')) \<and>
         ((i, K, b'')\<in>#mset ((g(L := (g L)[j' := (x1, C, b')])) La)\<longrightarrow> b'' \<longrightarrow> i \<in># dom_m b) \<and>
         {#i \<in># fst `# mset ((g(L := (g L)[j' := (x1, C, b')])) La). i \<in># dom_m b#} =
            clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    using corr unfolding correct_watching_except.simps all_lits_st_simps
    by fast+
  define g' where \<open>g' = g(L := (g L)[j' := (x1, C, b')])\<close>
  have g_g': \<open>g(L := (g L)[j' := (x1, C', b')]) = g'(L := (g' L)[j' := (x1, C', b')])\<close>
    unfolding g'_def by auto

  have H2: \<open>fst `# mset ((g'(L := (g' L)[j' := (x1, C', b')])) La) = fst `# mset (g' La)\<close> for La
    unfolding g'_def
    by (auto simp flip: mset_map simp: map_update)
  have H3: \<open>fst `#
                 mset
                  (take i ((g'(L := (g' L)[j' := (x1, C', b')])) La) @
                   drop j ((g'(L := (g' L)[j' := (x1, C', b')])) La)) =
      fst `#
                 mset
                  (take i (g' La) @
                   drop j (g' La))\<close> for La
    unfolding g'_def
    by (auto simp flip: mset_map drop_map simp: map_update)
  have [simp]:
    \<open>fst `# mset ((take i (g' L))[j' := (x1, C', b')]) = fst `# mset (take i (g' L))\<close>
    \<open>fst `# mset ((drop j ((g' L)[j' := (x1, C', b')]))) = fst `# mset (drop j (g' L))\<close>
    \<open>\<not>j' < j \<Longrightarrow> fst `# mset ((drop j (g' L))[j' - j := (x1, C', b')]) = fst `# mset (drop j (g' L))\<close>
    unfolding g'_def
      apply (auto simp flip: mset_map drop_map simp: map_update drop_update_swap; fail)
     apply (auto simp flip: mset_map drop_map simp: map_update drop_update_swap; fail)
    apply (auto simp flip: mset_map drop_map simp: map_update drop_update_swap; fail)
    done
  have \<open>j' < length (g' L) \<Longrightarrow> j' < i \<Longrightarrow> (x1, C, b') \<in> set ((take i (g L))[j' := (x1, C, b')])\<close>
    using nth_mem[of \<open>j'\<close> \<open>(take i (g L))[j' := (x1, C, b')]\<close>] unfolding g'_def
    by auto
  then have H: \<open>L \<in>#?\<L> \<Longrightarrow> j' < length (g' L) \<Longrightarrow>
       j' < i \<Longrightarrow> b' \<Longrightarrow> x1 \<in># dom_m b\<close>
    using C' Heq[of L x1 C b']
    by (cases \<open>j' < j\<close>) (simp, auto)
  have \<open>\<not> j' < j \<Longrightarrow> j' - j < length (g' L) - j \<Longrightarrow>
     (x1, C, b') \<in> set (drop j ((g L)[j' := (x1, C, b')]))\<close>
    using nth_mem[of \<open>j'-j\<close> \<open>drop j ((g L)[j' := (x1, C, b')])\<close>] unfolding g'_def
    by auto
  then have H': \<open>L \<in>#?\<L> \<Longrightarrow> \<not> j' < j \<Longrightarrow>
       j' - j < length (g' L) - j \<Longrightarrow> b' \<Longrightarrow> x1 \<in># dom_m b\<close>
    using C' Heq[of L x1 C b'] unfolding g'_def
    by auto

  have dist: \<open>La\<in>#?\<L> \<Longrightarrow>
        La = L \<Longrightarrow>
	 distinct_watched (take i ((g'(L := (g' L)[j' := (x1, C', b')])) La) @ drop j ((g'(L := (g' L)[j' := (x1, C', b')])) La))\<close>
    for La
    using Hdisteq[of L] unfolding g_g'[symmetric]
    by (cases \<open>j' < j\<close>)
       (auto simp: map_update drop_update_swap)
  have \<L>_alt: \<open>?\<L> = all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g')\<close>
    unfolding g'_def by simp
  have \<open>La\<in>#?\<L> \<Longrightarrow>
        La = L \<Longrightarrow>
	 distinct_watched (take i ((g'(L := (g' L)[j' := (x1, C', b')])) La) @ drop j ((g'(L := (g' L)[j' := (x1, C', b')])) La)) \<and>
         ((i', K, b'')\<in>#mset (take i ((g'(L := (g' L)[j' := (x1, C', b')])) La) @ drop j ((g'(L := (g' L)[j' := (x1, C', b')])) La)) \<longrightarrow>
             i' \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i') \<and> K \<noteq> La \<and> correctly_marked_as_binary b (i', K, b'')) \<and>
          ((i', K, b'')\<in>#mset (take i ((g'(L := (g' L)[j' := (x1, C', b')])) La) @ drop j ((g'(L := (g' L)[j' := (x1, C', b')])) La)) \<longrightarrow>
            b'' \<longrightarrow> i' \<in># dom_m b) \<and>
         {#i \<in># fst `# mset (take i ((g'(L := (g' L)[j' := (x1, C', b')])) La) @ drop j ((g'(L := (g' L)[j' := (x1, C', b')])) La)).
          i \<in># dom_m b#} =
         clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close> for La i' K b''
    using C' Heq[of La i' K] Heq[of La i' K b'] H H' dist[of La] corr_watched unfolding g_g' g'_def[symmetric]
    apply (auto elim!: in_set_upd_cases simp: drop_update_swap simp del: distinct_append)
    apply (cases \<open>j' < j\<close>; auto elim!: in_set_upd_cases simp: drop_update_swap simp del: distinct_append)+
    done
  moreover have \<open>La\<in>#?\<L> \<Longrightarrow>
       (La \<noteq> L \<longrightarrow>
        distinct_watched ((g'(L := (g' L)[j' := (x1, C', b')])) La) \<and>
        (\<forall>(i, K, ba)\<in>#mset ((g'(L := (g' L)[j' := (x1, C', b')])) La).
            i \<in># dom_m b \<longrightarrow>
            K \<in> set (b \<propto> i) \<and>
            K \<noteq> La \<and> correctly_marked_as_binary b (i, K, ba)) \<and>
        (\<forall>(i, K, ba)\<in>#mset ((g'(L := (g' L)[j' := (x1, C', b')])) La).
            ba \<longrightarrow> i \<in># dom_m b) \<and>
        {#i \<in># fst `# mset ((g'(L := (g' L)[j' := (x1, C', b')])) La).
         i \<in># dom_m b#} =
        clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>
     for La
    using Hneq Hdistneq
    unfolding correct_watching_except.simps g_g' g'_def[symmetric]
    by auto
  ultimately show ?thesis
    unfolding correct_watching_except.simps g_g' g'_def[symmetric]
    unfolding H2 H3 all_lits_st_simps \<L>_alt
    by blast
qed


lemma correct_watching_except_correct_watching_except_Suc_notin:
  assumes
    \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S)\<close> and
    j_w: \<open>j \<le> w\<close> and
    w_le: \<open>w < length (watched_by S L)\<close> and
    corr: \<open>correct_watching_except j w L S\<close>
  shows \<open>correct_watching_except j (Suc w) L (keep_watch L j w S)\<close>
proof -
  obtain M N D NE UE NEk UEk NS US N0 U0 Q W where
    S: \<open>S = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> by (cases S)
  let ?\<L> = \<open>all_lits_st S\<close>
  have [simp]: \<open>fst (W L ! w) \<notin># dom_m N\<close>
    using assms unfolding S by auto
  have
    Hneq: \<open>\<And>La. La\<in>#?\<L> \<longrightarrow>
        (La \<noteq> L \<longrightarrow>
	 distinct_watched (W La) \<and>
         ((\<forall>(i, K, b)\<in>#mset (W La). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
             correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (W La). b \<longrightarrow> i \<in># dom_m N)) \<and>
          {#i \<in># fst `# mset (W La). i \<in># dom_m N#} = clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close> and
    Heq: \<open>\<And>La. La\<in>#?\<L> \<longrightarrow>
        (La = L \<longrightarrow>
	 distinct_watched (take j (W La) @ drop w (W La)) \<and>
         ((\<forall>(i, K, b)\<in>#mset (take j (W La) @ drop w (W La)). i \<in># dom_m N \<longrightarrow>
              K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and> correctly_marked_as_binary N (i, K, b)) \<and>
          (\<forall>(i, K, b)\<in>#mset (take j (W La) @ drop w (W La)). b \<longrightarrow> i \<in># dom_m N) \<and>
         {#i \<in># fst `# mset (take j (W La) @ drop w (W La)). i \<in># dom_m N#} =
         clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})))\<close>
    using corr unfolding S correct_watching_except.simps
    by fast+

  have eq: \<open>mset (take j ((W(L := (W L)[j := W L ! w])) La) @ drop (Suc w) ((W(L := (W L)[j := W L ! w])) La)) =
    remove1_mset (W L ! w) (mset (take j (W La) @ drop w (W La)))\<close> if [simp]: \<open>La = L\<close> for La
    using w_le j_w
    by (auto simp: S take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
        list_update_append)

  have \<open>case x of (i, K, b) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
       correctly_marked_as_binary N (i, K, b)\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close> and
      \<open>x \<in># mset (take j ((W(L := (W L)[j := W L ! w])) La) @
                 drop (Suc w) ((W(L := (W L)[j := W L ! w])) La))\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Heq[of L] w_le j_w
    by (subst (asm) eq) (auto dest!: in_diffD)
  moreover have \<open>case x of (i, K, b) \<Rightarrow> b \<longrightarrow> i \<in># dom_m N\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close> and
      \<open>x \<in># mset (take j ((W(L := (W L)[j := W L ! w])) La) @
                 drop (Suc w) ((W(L := (W L)[j := W L ! w])) La))\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Heq[of L] w_le j_w unfolding S
    by (subst (asm) eq) (fastforce simp: S dest!: in_diffD)+
  moreover have \<open>{#i \<in># fst `#
              mset
               (take j ((W(L := (W L)[j := W L ! w])) La) @
                drop (Suc w) ((W(L := (W L)[j := W L ! w])) La)).
       i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close>
    for La :: \<open>'a literal\<close>
    using that Heq[of L] w_le j_w
    by (subst eq) (auto dest!: in_diffD simp: image_mset_remove1_mset_if)
  moreover have \<open>case x of (i, K, b) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
      correctly_marked_as_binary N (i, K, b)\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close> and
      \<open>x \<in># mset ((W(L := (W L)[j := W L ! w])) La)\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>case x of (i, K, b) \<Rightarrow> b \<longrightarrow> i \<in># dom_m N\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close> and
      \<open>x \<in># mset ((W(L := (W L)[j := W L ! w])) La)\<close>
    for La :: \<open>'a literal\<close> and x :: \<open>nat \<times> 'a literal \<times> bool\<close>
    using that Hneq[of La]
    by auto
  moreover have \<open>{#i \<in># fst `# mset ((W(L := (W L)[j := W L ! w])) La). i \<in># dom_m N#} =
      clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close>
    for La :: \<open>'a literal\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>distinct_watched ((W(L := (W L)[j := W L ! w])) La)\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La \<noteq> L\<close>
    for La :: \<open>'a literal\<close>
    using that Hneq[of La]
    by simp
  moreover have \<open>distinct_watched (take j ((W(L := (W L)[j := W L ! w])) La) @
                drop (Suc w) ((W(L := (W L)[j := W L ! w])) La))\<close>
    if
      \<open>La \<in># ?\<L>\<close> and
      \<open>La = L\<close>
    for La :: \<open>'a literal\<close>
    using that Heq[of L] w_le j_w apply -
    apply (subst distinct_mset_mset_distinct[symmetric])
    apply (subst mset_map)
    apply (subst eq)
    apply (solves simp)
    apply (subst (asm) distinct_mset_mset_distinct[symmetric])
    apply (subst (asm) mset_map)
    apply (rule distinct_mset_mono[of _ \<open>{#i. (i, j, k) \<in># mset (take j (W L) @ drop w (W L))#}\<close>])
    by (auto simp: image_mset_remove1_mset_if split: if_splits)
  ultimately show ?thesis
    unfolding S keep_watch_def prod.simps correct_watching_except.simps
    by simp
qed

lemma correct_watching_except_correct_watching_except_update_clause:
  assumes
    corr: \<open>correct_watching_except (Suc j) (Suc w) L
       (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(L := (W L)[j := W L ! w]))\<close> and
    j_w: \<open>j \<le> w\<close> and
    w_le: \<open>w < length (W L)\<close> and
    L': \<open>L' \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
      \<open>L' \<in> set (N \<propto> x1)\<close>and
    L_L: \<open>L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    L: \<open>L \<noteq> N \<propto> x1 ! xa\<close> and
    dom: \<open>x1 \<in># dom_m N\<close> and
    i_xa: \<open>i < length (N \<propto> x1)\<close> \<open>xa < length (N \<propto> x1)\<close> and
    [simp]: \<open>W L ! w = (x1, x2, b)\<close> and
    N_i: \<open>N \<propto> x1 ! i = L\<close> \<open>N \<propto> x1 ! (1 -i) \<noteq> L\<close>\<open>N \<propto> x1 ! xa \<noteq> L\<close> and
    N_xa: \<open>N \<propto> x1 ! xa \<noteq> N \<propto> x1 ! i\<close> \<open>N \<propto> x1 ! xa \<noteq> N \<propto> x1 ! (Suc 0 - i)\<close>and
    i_2: \<open>i < 2\<close> and \<open>xa \<ge> 2\<close> and
    L_neq: \<open>L' \<noteq> N \<propto> x1 ! xa\<close> \<comment>\<open>The new blocking literal is not the new watched literal.\<close>
  shows \<open>correct_watching_except j (Suc w) L
          (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W
           (L := (W L)[j := (x1, x2, b)],
            N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L', b)]))\<close>
proof -
  define W' where \<open>W' \<equiv> W(L := (W L)[j := W L ! w])\<close>
  have \<open>length (N \<propto> x1) > 2\<close>
    using i_2 i_xa assms
    by (auto simp: correctly_marked_as_binary.simps)
  let ?\<L> = \<open>all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  have \<L>: \<open>?\<L> = all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W')\<close>
    using assms unfolding W'_def by simp
  have
    Heq: \<open>\<And>La i K b. La\<in># ?\<L> \<Longrightarrow>
          La = L \<Longrightarrow>
	   distinct_watched (take (Suc j) (W' La) @ drop (Suc w) (W' La)) \<and>
           ((i, K, b)\<in>#mset (take (Suc j) (W' La) @ drop (Suc w) (W' La)) \<longrightarrow>
               i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and> correctly_marked_as_binary N (i, K, b)) \<and>
           ((i, K, b)\<in>#mset (take (Suc j) (W' La) @ drop (Suc w) (W' La)) \<longrightarrow>
               b \<longrightarrow> i \<in># dom_m N) \<and>
           {#i \<in># fst `#
                   mset
                    (take (Suc j) (W' La) @ drop (Suc w) (W' La)).
            i \<in># dom_m N#} =
           clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close> and
    Hneq: \<open>\<And>La i K b. La\<in>#?\<L> \<Longrightarrow>
          La \<noteq> L \<Longrightarrow>
	   distinct_watched (W' La) \<and>
           ((i, K, b)\<in>#mset (W' La) \<longrightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
               correctly_marked_as_binary N (i, K, b)) \<and>
           ((i, K, b)\<in>#mset (W' La) \<longrightarrow> b \<longrightarrow> i \<in># dom_m N) \<and>
           {#i \<in># fst `# mset (W' La). i \<in># dom_m N#} =
           clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close> and
    Hneq2: \<open>\<And>La. La\<in>#?\<L> \<Longrightarrow>
          (La \<noteq> L \<longrightarrow>
	   distinct_watched (W' La) \<and>
           {#i \<in># fst `# mset (W' La). i \<in># dom_m N#} =
           clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>
    using corr unfolding correct_watching_except.simps W'_def[symmetric] \<L>
    by fast+
  have H1: \<open>mset `# ran_mf (N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa)) = mset `# ran_mf N\<close>
    using dom i_xa distinct_mset_dom[of N]
    by (auto simp: ran_m_def dest!: multi_member_split intro!: image_mset_cong2)
  have W_W': \<open>W
      (L := (W L)[j := (x1, x2, b)], N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L', b)]) =
     W'(N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L', b)])\<close>
    unfolding W'_def
    by auto
  have W_W2: \<open>W (N \<propto> x1 ! xa) = W' (N \<propto> x1 ! xa)\<close>
    using L unfolding W'_def by auto
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
  have bin:
    \<open>correctly_marked_as_binary N (x1, x2, b)\<close>
    using Heq[of L \<open>fst (W L ! w)\<close> \<open>fst (snd (W L ! w ))\<close> \<open>snd (snd (W L ! w))\<close>] j_w w_le dom L'
       L_L unfolding all_lits_def
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append ac_simps)
  have x1_new: \<open>x1 \<notin> fst ` set (W (N \<propto> x1 ! xa))\<close>
  proof (rule ccontr)
    assume H: "\<not> ?thesis"
    have \<open>N \<propto> x1 ! xa \<in># ?\<L>\<close>
      using dom i_xa by auto
    then have \<open>{#i \<in># fst `# mset (W (N \<propto> x1 ! xa)). i \<in># dom_m N#} =
        clause_to_update (N \<propto> x1 ! xa) (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
      using Hneq[of \<open>N \<propto> x1 ! xa\<close>] L unfolding W'_def \<L>
      by simp
    then have \<open>x1 \<in># clause_to_update (N \<propto> x1 ! xa) (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
      using H dom by (metis (no_types, lifting) mem_Collect_eq set_image_mset
        set_mset_filter set_mset_mset)
    then show False
      using N_xa i_2 i_xa
      by (cases i; cases \<open>N \<propto> x1 ! xa\<close>)
        (auto simp: clause_to_update_def take_2_if split: if_splits)
  qed

  let ?N =  \<open>N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa)\<close>
  have \<open>L \<in># ?\<L> \<Longrightarrow> La = L \<Longrightarrow>
       x \<in> set (take j (W L)) \<or> x \<in> set (drop (Suc w) (W L)) \<Longrightarrow>
       case x of (i, K, b) \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
           correctly_marked_as_binary ?N (i, K, b)\<close> for La x
    using Heq[of L \<open>fst x\<close> \<open>fst (snd x)\<close> \<open>snd (snd x)\<close>] j_w w_le unfolding \<L>[symmetric]
    by (clarsimp simp: take_Suc_conv_app_nth W'_def list_update_append correctly_marked_as_binary.simps
      split: if_splits)
  moreover have \<open>L \<in># ?\<L> \<Longrightarrow> La = L \<Longrightarrow>
       x \<in> set (take j (W L)) \<or> x \<in> set (drop (Suc w) (W L)) \<Longrightarrow>
       case x of (i, K, b) \<Rightarrow>b \<longrightarrow> i \<in># dom_m N\<close> for La x
    using Heq[of L \<open>fst x\<close> \<open>fst (snd x)\<close> \<open>snd (snd x)\<close>] j_w w_le
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append correctly_marked_as_binary.simps
      split: if_splits)
  moreover  have \<open>L \<in># ?\<L> \<Longrightarrow>
          La = L \<Longrightarrow>
	  distinct_watched (take j (W L) @ drop (Suc w) (W L)) \<and>
          {#i \<in># fst `# mset (take j (W L)). i \<in># dom_m N#} + {#i \<in># fst `# mset (drop (Suc w) (W L)). i \<in># dom_m N#} =
          clause_to_update L (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close> for La
    using Heq[of L x1 x2 b] j_w w_le dom L_notin_swap N_xa_in_swap distinct_mset_dom[of N]
    i_xa i_2 assms(12)
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append set_N_x1 assms(11)
        clause_to_update_def dest!: multi_member_split split: if_splits
        intro: filter_mset_cong2)

  moreover have \<open>La \<in># ?\<L> \<Longrightarrow>
       La \<noteq> L \<Longrightarrow>
       x \<in> set (if La = N \<propto> x1 ! xa
                 then W' (N \<propto> x1 ! xa) @ [(x1, L', b)]
                 else (W(L := (W L)[j := (x1, x2, b)])) La) \<Longrightarrow>
       case x of
       (i, K, b) \<Rightarrow> i \<in># dom_m ?N \<longrightarrow> K \<in> set (?N \<propto> i) \<and> K \<noteq> La \<and> correctly_marked_as_binary ?N (i, K, b)\<close> for La x
    using Hneq[of La \<open>fst x\<close> \<open>fst (snd x)\<close> \<open>snd (snd x)\<close>] j_w w_le L' L_neq bin dom unfolding \<L>
    by (fastforce simp: take_Suc_conv_app_nth W'_def list_update_append
      correctly_marked_as_binary.simps split: if_splits)
  moreover have \<open>La \<in># ?\<L> \<Longrightarrow>
       La \<noteq> L \<Longrightarrow>
       x \<in> set (if La = N \<propto> x1 ! xa
                 then W' (N \<propto> x1 ! xa) @ [(x1, L', b)]
                 else (W(L := (W L)[j := (x1, x2, b)])) La) \<Longrightarrow>
       case x of (i, K, b) \<Rightarrow> b \<longrightarrow> i \<in># dom_m N\<close> for La x
    using Hneq[of La \<open>fst x\<close> \<open>fst (snd x)\<close> \<open>snd (snd x)\<close>] j_w w_le L' L_neq \<open>length (N \<propto> x1) > 2\<close>
      dom
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append correctly_marked_as_binary.simps split: if_splits)
  moreover have \<open>La \<in># ?\<L> \<Longrightarrow>
       La \<noteq> L \<Longrightarrow> distinct_watched  ((W
           (L := (W L)[j := (x1, x2, b)],
            N \<propto> x1 ! xa := W (N \<propto> x1 ! xa) @ [(x1, L', b)])) La)\<close> for La x
    using Hneq[of La] j_w w_le L' L_neq \<open>length (N \<propto> x1) > 2\<close>
      dom x1_new
    by (auto simp: take_Suc_conv_app_nth W'_def list_update_append correctly_marked_as_binary.simps split: if_splits)
  moreover {
    have \<open>N \<propto> x1 ! xa \<notin> set (watched_l (N \<propto> x1))\<close>
      using N_xa
      by (auto simp: set_N_x1 set_N_swap_x1)

    then have \<open> \<And>Ab Ac La.
       ?\<L> = add_mset L' (add_mset (N \<propto> x1 ! xa) Ac) \<Longrightarrow>
       dom_m N = add_mset x1 Ab \<Longrightarrow>
       N \<propto> x1 ! xa \<noteq> L \<Longrightarrow>
       {#i \<in># fst `# mset (W (N \<propto> x1 ! xa)). i = x1 \<or> i \<in># Ab#} =
         {#C \<in># Ab. N \<propto> x1 ! xa \<in> set (watched_l (N \<propto> C))#} \<close>
      using Hneq2[of \<open>N \<propto> x1 ! xa\<close>] L_neq unfolding W_W' W_W2 \<L>
      by (auto simp: clause_to_update_def split: if_splits)
    from this[symmetric] have \<open>La \<in># ?\<L> \<Longrightarrow>
          La \<noteq> L \<Longrightarrow>
	  distinct_watched (W' La) \<and>
          (x1 \<in># dom_m N \<longrightarrow>
           (La = N \<propto> x1 ! xa \<longrightarrow>
            add_mset x1 {#i \<in># fst `# mset (W' (N \<propto> x1 ! xa)). i \<in># dom_m N#} =
            clause_to_update (N \<propto> x1 ! xa) (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})) \<and>
           (La \<noteq> N \<propto> x1 ! xa \<longrightarrow>
            {#i \<in># fst `# mset (W La). i \<in># dom_m N#} =
            clause_to_update La (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))) \<and>
          (x1 \<notin># dom_m N \<longrightarrow>
           (La = N \<propto> x1 ! xa \<longrightarrow>
            {#i \<in># fst `# mset (W' (N \<propto> x1 ! xa)). i \<in># dom_m N#} =
            clause_to_update (N \<propto> x1 ! xa) (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NS, US, NEk, UEk, NE, UE, N0, U0, {#}, {#})) \<and>
           (La \<noteq> N \<propto> x1 ! xa \<longrightarrow>
            {#i \<in># fst `# mset (W La). i \<in># dom_m N#} =
            clause_to_update La (M, N(x1 \<hookrightarrow> swap (N \<propto> x1) i xa), D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})))\<close> for La
      using Hneq2[of La] j_w w_le L' dom distinct_mset_dom[of N] L_notin_swap N_xa_in_swap L_neq
      apply (auto simp: take_Suc_conv_app_nth W'_def list_update_append clause_to_update_def
        add_mset_eq_add_mset set_N_x1 set_N_swap_x1 assms(11) N_i all_lits_def ac_simps
        eq_commute[of x1]
        eq_commute[of \<open>{#y \<in># _. y \<noteq> _ \<longrightarrow> N \<propto> x1 ! xa \<in> set (watched_l (N \<propto> y))#}\<close>]
        dest!: multi_member_split La_in_notin_swap
        split: if_splits
        intro: image_mset_cong2 intro: filter_mset_cong2)
       by (smt (verit, ccfv_SIG) filter_mset_cong2) 
  }
  ultimately show ?thesis
    using L j_w dom i_xa
    unfolding correct_watching_except.simps H1  W'_def[symmetric] W_W' H2 W_W2 H4 H3 \<L>[symmetric]
    by (intro conjI impI ballI)
     (simp_all add: L' W_W' W_W2 H3 H4 drop_map)
qed

definition unit_propagation_inner_loop_wl_loop_pre where
  \<open>unit_propagation_inner_loop_wl_loop_pre L = (\<lambda>(j, w, S).
     w < length (watched_by S L) \<and> j \<le> w \<and> blits_in_\<L>\<^sub>i\<^sub>n S \<and>
     unit_propagation_inner_loop_wl_loop_inv L (j, w, S))\<close>

definition mop_watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> _ nres\<close> where
\<open>mop_watched_by S L w = do {
  ASSERT(w < length (watched_by S L));
  RETURN ((watched_by S L) ! w)
}\<close>

definition mop_polarity_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option nres\<close> where
  \<open>mop_polarity_wl S L = do {
    ASSERT(L \<in># all_lits_st S);
    ASSERT(no_dup (get_trail_wl S));
    RETURN(polarity (get_trail_wl S) L)
  }\<close>

lemma mop_polarity_wl_mop_polarity_l:
  \<open>(uncurry mop_polarity_wl, uncurry mop_polarity_l) \<in> state_wl_l b \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding mop_polarity_l_def mop_polarity_wl_def uncurry_def
  by (cases b)
    (intro frefI nres_relI; refine_rcg; auto simp: state_wl_l_def all_lits_def all_lits_of_mm_union
      all_lits_st_def)+

definition is_nondeleted_clause_pre :: \<open>nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>is_nondeleted_clause_pre C L S \<longleftrightarrow> C \<in> fst ` set (watched_by S L) \<and> L \<in># all_lits_st S\<close>
definition other_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v literal nres\<close> where
  \<open>other_watched_wl S L C i = do {
    ASSERT(get_clauses_wl S \<propto> C ! i = L \<and> i < length (get_clauses_wl S \<propto> C) \<and> i < 2 \<and>
      C \<in># dom_m (get_clauses_wl S) \<and> 1-i < length (get_clauses_wl S \<propto> C));
    mop_clauses_at (get_clauses_wl S) C (1 - i)
  }\<close>

lemma other_watched_wl_other_watched_l:
  \<open>(uncurry3 other_watched_wl, uncurry3 other_watched_l) \<in> state_wl_l b \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding other_watched_wl_def other_watched_l_def uncurry_def
  by (intro frefI nres_relI)
   (refine_rcg, auto simp: state_wl_l_def)

lemma other_watched_wl_other_watched_l_spec_itself:
  \<open>((S, L, C, i), (S', L', C', i')) \<in> state_wl_l b \<times>\<^sub>r (Id :: ('v literal \<times> _) set) \<times>\<^sub>r nat_rel \<times>\<^sub>r
     nat_rel \<Longrightarrow>
     other_watched_wl S L C i \<le>
       \<Down>{(L, L'). L = L' \<and> L = get_clauses_wl S \<propto> C ! (1 - i)}
        (other_watched_l S' L' C' i')\<close>
  using twl_st_wl(2)[of S S' b]
  unfolding other_watched_wl_def other_watched_l_def
    mop_clauses_at_def
  by refine_vcg clarsimp_all

text \<open>It was too hard to align the program unto a refinable form directly.\<close>
definition unit_propagation_inner_loop_body_wl_int :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl_int L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S \<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S);
      val_K \<leftarrow> mop_polarity_wl S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          ASSERT(unit_prop_body_wl_inv S j w L);
          i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
          ASSERT(i \<le> 1);
          L' \<leftarrow> other_watched_wl S L C i;
          val_L' \<leftarrow> mop_polarity_wl S L';
          if val_L' = Some True
          then update_blit_wl L C b j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {S \<leftarrow> set_conflict_wl C S; RETURN (j+1, w+1, S)}
                else do {S \<leftarrow> propagate_lit_wl_general L' C i S; RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                val_L' \<leftarrow> mop_polarity_wl S K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S
                else update_clause_wl L L' C b j w i f S
              }
          }
        }
      }
   }\<close>

definition propagate_proper_bin_case where
  \<open>propagate_proper_bin_case L L' S C \<longleftrightarrow>
    C \<in># dom_m (get_clauses_wl S) \<and> length ((get_clauses_wl S)\<propto>C) = 2 \<and>
    set (get_clauses_wl S\<propto>C) = {L, L'} \<and> L \<noteq> L'\<close>

definition unit_propagation_inner_loop_body_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S \<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S);
      val_K \<leftarrow> mop_polarity_wl S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do {
        if b then do {
           ASSERT(propagate_proper_bin_case L K S C);
           if val_K = Some False
           then do {S \<leftarrow> set_conflict_wl C S;
             RETURN (j+1, w+1, S)}
           else do {
             S \<leftarrow> propagate_lit_wl_bin K C S;
             RETURN (j+1, w+1, S)}
        }  \<comment>\<open>Now the costly operations:\<close>
        else if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          ASSERT(unit_prop_body_wl_inv S j w L);
          i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
          ASSERT(i \<le> 1);
          L' \<leftarrow> other_watched_wl S L C i;
          val_L' \<leftarrow> mop_polarity_wl S L';
          if val_L' = Some True
          then update_blit_wl L C b j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {S \<leftarrow> set_conflict_wl C S;
                   RETURN (j+1, w+1, S)}
                else do {S \<leftarrow> propagate_lit_wl L' C i S; RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                val_L' \<leftarrow> mop_polarity_wl S K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S
                else update_clause_wl L L' C b j w i f S
              }
          }
        }
      }
   }\<close>

lemma [twl_st_wl]: \<open>get_clauses_wl (keep_watch L j w S) = get_clauses_wl S\<close>
  by (cases S) (auto simp: keep_watch_def)


lemma unit_propagation_inner_loop_body_wl_int_alt_def:
 \<open>unit_propagation_inner_loop_body_wl_int L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      let _ = (C \<notin># dom_m (get_clauses_wl S));
      S \<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S);
      let b' = (C \<notin># dom_m (get_clauses_wl S));
      if b' then do {
        let K = K;
        val_K \<leftarrow> mop_polarity_wl S K;
        if val_K = Some True
        then RETURN (j+1, w+1, S)
        else \<comment>\<open>Now the costly operations:\<close>
          RETURN (j, w+1, S)
      }
      else do {
        let S = S;
        K \<leftarrow> SPEC((=) K);
        val_K \<leftarrow> mop_polarity_wl S K;
        if val_K = Some True
        then RETURN (j+1, w+1, S)
        else do { \<comment>\<open>Now the costly operations:\<close>
          ASSERT(unit_prop_body_wl_inv S j w L);
          i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
          ASSERT(i \<le> 1);
          L' \<leftarrow> other_watched_wl S L C i;
          val_L' \<leftarrow> mop_polarity_wl S L';
          if val_L' = Some True
          then update_blit_wl L C b j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {S \<leftarrow> set_conflict_wl C S; RETURN (j+1, w+1, S)}
                else do {S \<leftarrow> propagate_lit_wl_general L' C i S; RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                val_L' \<leftarrow> mop_polarity_wl S K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S
                else update_clause_wl L L' C b j w i f S
             }
          }
        }
      }
   }\<close>
proof -

  text \<open>We first define an intermediate step where both then and else branches are the same.\<close>
  have E: \<open>unit_propagation_inner_loop_body_wl_int L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S'\<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S');
      let b' = C \<notin># dom_m (get_clauses_wl S');
      if b' then do {
        let K = K;
        val_K \<leftarrow> mop_polarity_wl S' K;
        if val_K = Some True
        then RETURN (j+1, w+1, S')
        else do { \<comment>\<open>Now the costly operations:\<close>
          if b'
          then RETURN (j, w+1, S')
          else do {
            ASSERT(unit_prop_body_wl_inv S' j w L);
            i \<leftarrow> pos_of_watched (get_clauses_wl S') C L;
            ASSERT(i \<le> 1);
            L' \<leftarrow> other_watched_wl S' L C i;
            val_L' \<leftarrow> mop_polarity_wl S' L';
            if val_L' = Some True
            then update_blit_wl L C b j w L' S'
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S') (get_clauses_wl S') C;
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S');
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {S' \<leftarrow> set_conflict_wl C S'; RETURN (j+1, w+1, S')}
                  else do {S' \<leftarrow> propagate_lit_wl_general L' C i S'; RETURN (j+1, w+1, S')}
                }
              | Some f \<Rightarrow> do {
                ASSERT(C \<in># dom_m (get_clauses_wl S') \<and> f < length (get_clauses_wl S' \<propto> C) \<and> f \<ge> 2);
                K \<leftarrow> mop_clauses_at (get_clauses_wl S') C f;
                val_L' \<leftarrow> mop_polarity_wl S' K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S'
                else update_clause_wl L L' C b j w i f S'
                }
            }
          }
        }
      }
      else do {
        K \<leftarrow> SPEC((=) K);
        val_K \<leftarrow> mop_polarity_wl S' K;
        if val_K = Some True
        then RETURN (j+1, w+1, S')
        else do { \<comment>\<open>Now the costly operations:\<close>
          if b'
          then RETURN (j, w+1, S')
          else do {
            ASSERT(unit_prop_body_wl_inv S' j w L);
            i \<leftarrow> pos_of_watched (get_clauses_wl S') C L;
            ASSERT(i \<le> 1);
            L' \<leftarrow> other_watched_wl S' L C i;
            val_L' \<leftarrow> mop_polarity_wl S' L';
            if val_L' = Some True
            then update_blit_wl L C b j w L' S'
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S') (get_clauses_wl S') C;
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S');
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {S' \<leftarrow> set_conflict_wl C S'; RETURN (j+1, w+1, S')}
                  else do {S'\<leftarrow>propagate_lit_wl_general L' C i S';RETURN (j+1, w+1, S')}
                }
              | Some f \<Rightarrow> do {
                ASSERT(C \<in># dom_m (get_clauses_wl S') \<and> f < length (get_clauses_wl S' \<propto> C) \<and> f \<ge> 2);
                K \<leftarrow> mop_clauses_at (get_clauses_wl S') C f;
                val_L' \<leftarrow> mop_polarity_wl S' K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S'
                else update_clause_wl L L' C b j w i f S'
                }
            }
          }
        }
      }
   }\<close>
  (is \<open>_ = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S'\<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S');
      let b' = (C \<notin># dom_m (get_clauses_wl S'));
      if b' then
        ?P S' C K b b'
      else
        ?Q S' C K b b'
    }\<close>)
    unfolding unit_propagation_inner_loop_body_wl_int_def if_not_swap bind_to_let_conv
      SPEC_eq_is_RETURN twl_st_wl
    unfolding Let_def if_not_swap bind_to_let_conv
      SPEC_eq_is_RETURN twl_st_wl
    apply (subst if_cancel)
    apply (intro bind_cong case_prod_cong if_cong[OF refl] refl if_cong)
    done
  show ?thesis
    unfolding E
    apply (subst if_replace_cond[of _ \<open>?P _ _ _ _\<close>])
    unfolding if_True if_False Let_def
    apply (intro bind_cong_nres case_prod_cong if_cong[OF refl] refl)
    done
qed


section \<open>The Functions\<close>

subsection \<open>Inner Loop\<close>

lemma clause_to_update_mapsto_upd_If:
  assumes
    i: \<open>i \<in># dom_m N\<close>
  shows
  \<open>clause_to_update L (M, N(i \<hookrightarrow> C'), C, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q) =
    (if L \<in> set (watched_l C')
     then add_mset i (remove1_mset i (clause_to_update L (M, N, C, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)))
     else remove1_mset i (clause_to_update L (M, N, C, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)))\<close>
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

lemma keep_watch_st_wl[twl_st_wl]:
  \<open>get_unit_clauses_wl (keep_watch L j w S) = get_unit_clauses_wl S\<close>
  \<open>get_init_clauses0_wl (keep_watch L j w S) = get_init_clauses0_wl S\<close>
  \<open>get_learned_clauses0_wl (keep_watch L j w S) = get_learned_clauses0_wl S\<close>
  \<open>get_clauses0_wl (keep_watch L j w S) = get_clauses0_wl S\<close>
  \<open>get_conflict_wl (keep_watch L j w S) = get_conflict_wl S\<close>
  \<open>get_trail_wl (keep_watch L j w S) = get_trail_wl S\<close>
  by (cases S; auto simp: keep_watch_def; fail)+

declare twl_st_wl[simp]

lemma correct_watching_except_correct_watching_except_propagate_lit_wl:
  assumes
    corr: \<open>correct_watching_except j w L S\<close> and
    i_le: \<open>Suc 0 < length (get_clauses_wl S \<propto> C)\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and undef: \<open>undefined_lit (get_trail_wl S) L'\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    lit: \<open>L' \<in># all_lits_st S\<close> and
     i: \<open>i \<le> 1\<close>
  shows \<open>propagate_lit_wl_general L' C i S \<le> SPEC(\<lambda>c. correct_watching_except j w L c)\<close>
proof -
  obtain M N D NE UE NEk UEk NS US N0 U0 Q W where S: \<open>S = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> by (cases S)
  let ?\<L> = \<open>all_lits_st S\<close>
  have
    Hneq: \<open>\<And>La. La\<in>#?\<L> \<Longrightarrow>
        La \<noteq> L \<Longrightarrow>
         (\<forall>(i, K, b)\<in>#mset (W La). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
            correctly_marked_as_binary N (i, K, b)) \<and>
         (\<forall>(i, K, b)\<in>#mset (W La). b \<longrightarrow> i \<in># dom_m N) \<and>
         {#i \<in># fst `# mset (W La). i \<in># dom_m N#} = clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close> and
    Heq: \<open>\<And>La. La\<in>#?\<L> \<Longrightarrow>
        La = L \<Longrightarrow>
         (\<forall>(i, K, b)\<in>#mset (take j (W La) @ drop w (W La)). i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> La \<and>
              correctly_marked_as_binary N (i, K, b)) \<and>
         (\<forall>(i, K, b)\<in>#mset (take j (W La) @ drop w (W La)). b \<longrightarrow> i \<in># dom_m N) \<and>
         {#i \<in># fst `# mset (take j (W La) @ drop w (W La)). i \<in># dom_m N#} =
         clause_to_update La (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    using corr unfolding S correct_watching_except.simps
    by fast+
  define N' where \<open>N' \<equiv> if length (N \<propto> C) > 2 then N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)) else N\<close>

  have \<open>Suc 0 - i < length (N \<propto> C)\<close> and \<open>0 < length (N \<propto> C)\<close>
    using i_le
    by (auto simp: S)
  then have [simp]: \<open>mset (swap (N \<propto> C) 0 (Suc 0 - i)) = mset (N \<propto> C)\<close>
    by (auto simp: S)
  have H1[simp]: \<open>{#mset (fst x). x \<in># ran_m N'#} =
     {#mset (fst x). x \<in># ran_m N#}\<close>
    using C
    by (auto dest!: multi_member_split simp: ran_m_def S N'_def
           intro!: image_mset_cong)

  have H2: \<open>mset `# ran_mf N' = mset `# ran_mf N\<close>
    using H1 by auto
  have H3: \<open>dom_m N' = dom_m N\<close>
    using C by (auto simp: S N'_def)
  have H4: \<open>set (N' \<propto> ia) =
    set (N \<propto> ia)\<close> for ia
    using i_le
    by (cases \<open>C = ia\<close>) (auto simp: S N'_def)
  have H5: \<open>set (watched_l (N' \<propto> ia)) = set (watched_l (N \<propto> ia))\<close> for ia
    using i_le
    by (cases \<open>C = ia\<close>; cases i; cases \<open>N \<propto> ia\<close>; cases \<open>tl (N \<propto> ia)\<close>) (auto simp: N'_def S swap_def)
  have [iff]: \<open>correctly_marked_as_binary N C' \<longleftrightarrow> correctly_marked_as_binary N' C'\<close> for C' ia
    by (cases C')
      (auto simp: correctly_marked_as_binary.simps N'_def)
  have H6: \<open>propagate_lit_wl_general L' C i (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
     RETURN (Propagated L' C # M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, add_mset (- L') Q, W)\<close>
   using assms \<open>Suc 0 - i < length (N \<propto> C)\<close> undef confl lit
   by (auto simp: mop_clauses_swap_def S propagate_lit_wl_general_def N'_def
     cons_trail_propagate_l_def)
 have \<L>: \<open>all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
   all_lits_st (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
   using assms i_le unfolding N'_def by (auto simp: S)
  show ?thesis
    using corr lit unfolding S H6 apply -
    apply (rule RETURN_rule)
    unfolding S prod.simps Let_def correct_watching_except.simps \<L>
      H1 H2 H3 H4 H5 clause_to_update_def get_clauses_l.simps H5 all_lits_st_simps
    by simp
qed


lemma unit_propagation_inner_loop_body_wl_int_alt_def2:
  \<open>unit_propagation_inner_loop_body_wl_int L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S \<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S);
      val_K \<leftarrow> mop_polarity_wl S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        if b then
          if C \<notin># dom_m (get_clauses_wl S)
          then RETURN (j, w+1, S)
          else do {
            ASSERT(unit_prop_body_wl_inv S j w L);
            i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
            ASSERT(i \<le> 1);
            L' \<leftarrow> other_watched_wl S L C i;
            val_L' \<leftarrow> mop_polarity_wl S L';
            if val_L' = Some True
            then update_blit_wl L C b j w L' S
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {S \<leftarrow> set_conflict_wl C S; RETURN (j+1, w+1, S)}
                  else do {S \<leftarrow> propagate_lit_wl_general L' C i S; RETURN (j+1, w+1, S)}
                }
              | Some f \<Rightarrow> do {
                  ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                  K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                  val_L' \<leftarrow> mop_polarity_wl S K;
                  if val_L' = Some True
                  then update_blit_wl L C b j w K S
                  else update_clause_wl L L' C b j w i f S
                }
            }
          }
        else
          if C \<notin># dom_m (get_clauses_wl S)
          then RETURN (j, w+1, S)
          else do {
            ASSERT(unit_prop_body_wl_inv S j w L);
            i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
            ASSERT(i \<le> 1);
            L' \<leftarrow> other_watched_wl S L C i;
            val_L' \<leftarrow> mop_polarity_wl S L';
            if val_L' = Some True
            then update_blit_wl L C b j w L' S
            else do {
              f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
              ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
              case f of
                None \<Rightarrow> do {
                  if val_L' = Some False
                  then do {S \<leftarrow> set_conflict_wl C S; RETURN (j+1, w+1, S)}
                  else do {S \<leftarrow> propagate_lit_wl_general L' C i S; RETURN (j+1, w+1, S)}
                }
              | Some f \<Rightarrow> do {
                  ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                  K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                  val_L' \<leftarrow> mop_polarity_wl S K;
                  if val_L' = Some True
                  then update_blit_wl L C b j w K S
                  else update_clause_wl L L' C b j w i f S
                }
            }
          }
      }
   }\<close>
  unfolding unit_propagation_inner_loop_body_wl_int_def if_not_swap bind_to_let_conv
    SPEC_eq_is_RETURN twl_st_wl
  unfolding Let_def if_not_swap bind_to_let_conv
    SPEC_eq_is_RETURN twl_st_wl
  apply (subst if_cancel)
  apply (intro bind_cong_nres case_prod_cong if_cong[OF refl] refl)
  done

lemma unit_propagation_inner_loop_body_wl_alt_def:
  \<open>unit_propagation_inner_loop_body_wl (L :: 'v literal) j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S \<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S);
      val_K \<leftarrow> mop_polarity_wl S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do {
        if b then do {
          if False
          then RETURN (j, w+1, S)
          else do{
            let i::nat = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
                K = K; val_L' = val_K in
            if False \<comment> \<open>\<^term>\<open>val_L' = Some True\<close>\<close>
            then RETURN (j, w+1, S)
            else do {
              f \<leftarrow> RETURN (None :: nat option);
              case f of
               None \<Rightarrow> do {
                 ASSERT(propagate_proper_bin_case L K S C);
                 if val_K = Some False
                 then do {S \<leftarrow> set_conflict_wl C S; RETURN (j+1, w+1, S)}
                 else do {
                   S \<leftarrow> propagate_lit_wl_bin' K C (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1) S;
                   RETURN (j+1, w+1, S)}
               }
             | _ \<Rightarrow> RETURN (j, w+1, S)
            }}
        }  \<comment>\<open>Now the costly operations:\<close>
        else if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          ASSERT(unit_prop_body_wl_inv S j w L);
          i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
          ASSERT(i \<le> 1);
          L' \<leftarrow> other_watched_wl S L C i;
          val_L' \<leftarrow> mop_polarity_wl S L';
          if val_L' = Some True
          then update_blit_wl L C b j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {S \<leftarrow> set_conflict_wl C S; RETURN (j+1, w+1, S)}
                else do {S \<leftarrow> propagate_lit_wl L' C i S; RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                 ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                 K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                val_L'\<leftarrow> mop_polarity_wl S K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S
                else update_clause_wl L L' C b j w i f S
              }
          }
        }
      }
   }\<close>
  unfolding unit_propagation_inner_loop_body_wl_def if_not_swap bind_to_let_conv
    SPEC_eq_is_RETURN twl_st_wl propagate_lit_wl_bin'_def
  unfolding Let_def if_not_swap bind_to_let_conv
    SPEC_eq_is_RETURN twl_st_wl if_False
  apply (intro bind_cong_nres case_prod_cong if_cong[OF refl] refl option.case_cong)
  apply auto
  done

lemma find_unwatched_l_itself:
    \<open>(uncurry2 find_unwatched_l, uncurry2 find_unwatched_l) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel\<close>
   by (auto intro!: frefI nres_relI)

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
  shows unit_propagation_inner_loop_body_wl_wl_int: \<open>unit_propagation_inner_loop_body_wl L j w S \<le>
     \<Down> Id (unit_propagation_inner_loop_body_wl_int L j w S)\<close>
proof -
  have n_d: \<open>no_dup (get_trail_wl S)\<close>
    using inner_loop_inv unfolding unit_propagation_inner_loop_wl_loop_inv_def prod.case
      unit_propagation_inner_loop_l_inv_def twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def apply -
    by normalize_goal+ (simp only: twl_st_wl twl_st_l twl_st)

  have pos_of_watched: \<open>((N, C, L), (N', C', L')) \<in> Id \<Longrightarrow> pos_of_watched N C L \<le> \<Down> nat_rel (pos_of_watched N' C' L')\<close>
     for N N' C C' L L'
     by auto
  define SLW where \<open>SLW \<equiv> mop_watched_by_at S L w\<close>
  define R_SLW where [simp]: \<open>R_SLW = {((C, K, b), (C', K', b')). C = C' \<and> K = K' \<and> b = b' \<and>
               (b \<longrightarrow> length (get_clauses_wl S \<propto> C) = 2 \<and> C \<in># dom_m (get_clauses_wl S) \<and>
                  K \<in> set(get_clauses_wl S \<propto> C) \<and> L \<in> set(get_clauses_wl S \<propto> C) \<and> K \<noteq> L) \<and>
               (C \<in># dom_m (get_clauses_wl S) \<and> \<not>b \<longrightarrow> length (get_clauses_wl S \<propto> C) > 2)}\<close>
  define keep where \<open>keep \<equiv> mop_keep_watch L j w S\<close>
  have [refine]: \<open>unit_propagation_inner_loop_wl_loop_pre L(j, w, S) \<Longrightarrow>
    SLW \<le> \<Down> R_SLW (mop_watched_by_at S L w)\<close>
    using corr_w
    unfolding SLW_def mop_watched_by_at_def R_SLW_def
    apply (refine_rcg, cases S)
    apply  (clarsimp dest!: multi_member_split simp: mop_watched_by_def ASSERT_refine_right
         correctly_marked_as_binary.simps
         correct_watching_except_alt_def simp flip: Cons_nth_drop_Suc
         dest!: )
    apply auto
    done
  have [refine]: \<open>unit_propagation_inner_loop_wl_loop_pre L(j, w, S) \<Longrightarrow>
    keep \<le> \<Down> {(T, T'). (T, T') \<in> Id \<and> get_clauses_wl T = get_clauses_wl S \<and> get_trail_wl T = get_trail_wl S}
            (mop_keep_watch L j w S)\<close> (is \<open>_ \<Longrightarrow> _ \<le> \<Down> ?keep _\<close>)
    using corr_w
    unfolding keep_def mop_keep_watch_def
    by (refine_rcg, cases S)
      (clarsimp dest!: multi_member_split simp: mop_watched_by_def ASSERT_refine_right
         correct_watching_except.simps simp flip: Cons_nth_drop_Suc)

  have [refine]: \<open>unit_propagation_inner_loop_wl_loop_pre L(j, w, S) \<Longrightarrow>
    (x, x')  \<in> R_SLW \<Longrightarrow>
    (T', val_K) \<in> ?keep \<Longrightarrow>
    \<not> x1\<notin># dom_m (get_clauses_wl val_K) \<Longrightarrow>
    x'= (x1, x2) \<Longrightarrow>
    x= (x2b, x1c) \<Longrightarrow>
    RETURN (if get_clauses_wl T'\<propto> x2b! 0 = L then 0 else 1 )
    \<le> \<Down>  {(K', K). K = K' \<and> K = (if get_clauses_wl T'\<propto> x2b! 0 = L then 0 else 1)}
      (pos_of_watched (get_clauses_wl val_K) x1 L)\<close>
   (is \<open>\<lbrakk>_; _; _; _; _; _\<rbrakk> \<Longrightarrow> _ \<le> \<Down> ?pos _\<close>)
   for x x' x1 x2 x2a x1b x2b x1c x2c T T' val_Ka val_aK val_K
   unfolding pos_of_watched_def R_SLW_def
   by refine_rcg auto

  have bin_mop_clauses_at: \<open>unit_propagation_inner_loop_wl_loop_pre L(j, w, S) \<Longrightarrow>
    (x, x')  \<in> R_SLW \<Longrightarrow>
    (T', val_K) \<in> ?keep \<Longrightarrow>
    \<not> x1\<notin># dom_m (get_clauses_wl val_K) \<Longrightarrow>
    x2= (x2a, x1b) \<Longrightarrow>
    x'= (x1, x2) \<Longrightarrow>
    x1c = (x2d, x1d) \<Longrightarrow>
    x= (x2b, x1c) \<Longrightarrow> x1b \<Longrightarrow>
    (if get_clauses_wl T'\<propto> x2b! 0 = L then 0 else 1, i) \<in> ?pos x2b T' \<Longrightarrow>
    RETURN x2d
    \<le> \<Down>  {(K, K'). K = K' \<and> x2d = K'}
    (other_watched_wl val_K L x1 i)\<close>
   for x x' x1 x2 x2a x1b x2b x1c x2c T T' val_Ka val_aK val_K x2d x1d i
   unfolding mop_clauses_at_def R_SLW_def other_watched_wl_def
   by refine_rcg (auto simp: length_list_2)

  have bin_mop_polarity_wl: \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S) \<Longrightarrow>
    unit_propagation_inner_loop_wl_loop_pre L (j, w, S) \<Longrightarrow>
    (Saa, val_K) \<in> ?keep \<Longrightarrow>
    (val_Ka, i) \<in>{(v, v'). v = v' \<and> v = polarity (get_trail_wl Saa) x2c} \<Longrightarrow>
    \<not> x2 \<notin># dom_m (get_clauses_wl val_K) \<Longrightarrow>
    (if get_clauses_wl Saa \<propto> x2b ! 0 = L then 0 else 1, K)
    \<in> ?pos x2b Saa \<Longrightarrow>
    (x2c, K') \<in>{(K, K'). K = K' \<and> x2c = K'} \<Longrightarrow>
    (x', x1) \<in> R_SLW \<Longrightarrow>
    x1a =(x2a, x1b) \<Longrightarrow>
    x1 =(x2, x1a) \<Longrightarrow>
    x1c =(x2c, Sa) \<Longrightarrow>
    x' =(x2b, x1c) \<Longrightarrow>
    val_Ka \<noteq> Some True \<Longrightarrow>
    i \<noteq> Some True \<Longrightarrow>
    Sa \<Longrightarrow>
    x1b \<Longrightarrow>
    RETURN val_Ka
    \<le> \<Down> (\<langle>Id\<rangle>option_rel)
       (mop_polarity_wl val_K K')\<close>
    for x' x1 x2 x1a x2a x1b x2b x1c x2c Sa Saa val_K val_Ka i K K'
    unfolding mop_polarity_wl_def
    by refine_rcg auto

  have bin_find_unwatched: \<open>RETURN None
        \<le> \<Down> ({(b,b'). (b, b') \<in> \<langle>Id\<rangle>option_rel \<and> b = None})
           (find_unwatched_l (get_trail_wl Saa) (get_clauses_wl Saa) x1)\<close>
      (is \<open>_ \<le> \<Down> ?bin_unw _\<close>)
    if
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>(x, x') \<in> R_SLW\<close> and
      \<open>x2 =(x1a, x2a)\<close> and
      \<open>x' =(x1, x2)\<close> and
      \<open>x2b =(x1c, x2c)\<close> and
      \<open>x =(x1b, x2b)\<close> and
      \<open>(Sa, Saa) \<in> ?keep\<close> and
      \<open>(val_K, val_Ka)
       \<in>{(v, v'). v = v' \<and> v = polarity (get_trail_wl Sa) x1c}\<close> and
      \<open>val_K \<noteq> Some True\<close> and
      \<open>val_Ka \<noteq> Some True\<close> and
      \<open>x2c\<close> and
      \<open>x2a\<close> and
      \<open>\<not> False\<close> and
      \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Saa)\<close> and
      \<open>unit_prop_body_wl_inv Saa j w L\<close> and
      \<open>(if get_clauses_wl Sa \<propto> x1b ! 0 = L then 0 else 1, i)
       \<in>{(K', K).
          K = K' \<and>
          K = (if get_clauses_wl Sa \<propto> x1b ! 0 = L then 0 else 1)}\<close> and
      \<open>(x1c, L') \<in>{(K, K'). K = K' \<and> x1c = K'}\<close> and
      \<open>(val_K, val_L') \<in>\<langle>bool_rel\<rangle>option_rel\<close> and
      \<open>\<not> False\<close> and
      \<open>val_L' \<noteq> Some True\<close>
     for x x' x1 x2 x1a x2a x1b x2b x1c x2c Sa Saa val_K val_Ka i L' val_L'
     using that n_d
     unfolding find_unwatched_l_def
     by (auto simp: RETURN_RES_refine_iff length_list_2)


  have bin_unw_Id: \<open>x \<in> ?bin_unw \<Longrightarrow> x \<in> \<langle>Id\<rangle>option_rel\<close> for x
    by auto
  have prop_bin_prop_gen[THEN fref_to_Down_curry3, refine]:
     \<open>(uncurry3 propagate_lit_wl_bin', uncurry3 propagate_lit_wl_general) \<in>
        [\<lambda>(((L', C), _), S). length (get_clauses_wl S \<propto> C) = 2]\<^sub>f (Id \<times>\<^sub>f nat_rel  \<times>\<^sub>f {_. True}  \<times>\<^sub>f Id) \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    by (auto simp: propagate_lit_wl_bin'_def propagate_lit_wl_general_def  cons_trail_propagate_l_def le_ASSERT_iff propagate_lit_wl_bin_def
       intro!: frefI nres_relI)

  have prop_prop_gen[THEN fref_to_Down_curry3, refine]: \<open>(uncurry3 propagate_lit_wl, uncurry3 propagate_lit_wl_general) \<in>
    [\<lambda>(((L', C), _), S). length (get_clauses_wl S \<propto> C) > 2]\<^sub>f (Id \<times>\<^sub>f nat_rel  \<times>\<^sub>f nat_rel  \<times>\<^sub>f Id) \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    by (auto simp: propagate_lit_wl_def propagate_lit_wl_general_def
       intro!: frefI nres_relI)

  have [THEN fref_to_Down_curry2, refine]:
     \<open>(uncurry2 mop_clauses_at, uncurry2 mop_clauses_at) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
    by (auto intro!: frefI nres_relI)
  have [refine]:
    \<open>((S, L), (S', L')) \<in> Id \<Longrightarrow> mop_polarity_wl S L \<le> \<Down> {(v, v'). v=v' \<and> v = polarity (get_trail_wl S) L}
       (mop_polarity_wl S' L')\<close> for S S' L L'
    by (auto intro!: frefI nres_relI simp: mop_polarity_wl_def ASSERT_refine_right)

  have [THEN fref_to_Down_curry, refine]:
     \<open>(uncurry set_conflict_wl, uncurry set_conflict_wl) \<in> Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
    by (auto intro!: frefI nres_relI)

  have [THEN fref_to_Down_curry3, refine]:
    \<open>(uncurry3 other_watched_wl, uncurry3 other_watched_wl) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
    by (auto intro!: frefI nres_relI)

  show ?thesis
    supply [[goals_limit=1]]
    unfolding unit_propagation_inner_loop_body_wl_int_alt_def2
       unit_propagation_inner_loop_body_wl_alt_def
    apply (subst SLW_def[symmetric])
    apply (subst keep_def[symmetric])
    apply (refine_rcg pos_of_watched
      find_unwatched_l_itself[THEN fref_to_Down_curry2])
    subgoal for SLw SLw' C x2a bin bL C' x2b bin'  bL'
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption+
    apply (rule bin_mop_clauses_at; assumption)
    apply (rule bin_mop_polarity_wl; assumption)
    subgoal by auto
    subgoal by auto
    apply (rule bin_find_unwatched; assumption)
    apply (rule bin_unw_Id; assumption)
    subgoal
      unfolding propagate_proper_bin_case_def by (auto simp: length_list_2)
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
    apply assumption
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
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma nres_add_unrelated:
   \<open>P \<le> \<Down> {(S, S'). R1 S} Q \<Longrightarrow> P \<le> \<Down> {(S, S'). R2 S S'} Q \<Longrightarrow> P \<le> \<Down>{(S, S'). R1 S \<and> R2 S S'} Q\<close> for P R1 R2 Q
  by (simp add: pw_ref_iff)

lemma nres_add_unrelated2:
   \<open>P \<le> SPEC R1 \<Longrightarrow> P \<le> \<Down> {(S, S'). R2 S S'} Q \<Longrightarrow> P \<le> \<Down>{(S, S'). R1 S \<and> R2 S S'} Q\<close> for P R1 R2 Q
  using nres_add_unrelated[of P R1 Q R2]
  by (auto simp add: pw_ref_iff dest: inres_SPEC)

lemma nres_add_unrelated3:
   \<open>P \<le> \<Down> {(S, S'). R1 S} Q \<Longrightarrow> P \<le> \<Down> {(S, S'). R2 S} Q \<Longrightarrow> P \<le> \<Down>{(S, S'). R1 S \<and> R2 S} Q\<close> for P R1 R2 Q
  by (simp add: pw_ref_iff)

lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch2: \<open>w < length (watched_by S L) \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n (keep_watch L j w S)\<close>
   apply (cases S; clarsimp simp: blits_in_\<L>\<^sub>i\<^sub>n_def keep_watch_def)
  using nth_mem[of w \<open>(watched_by S L)\<close>]
  by (auto elim!: in_set_upd_cases simp: eq_commute[of _ \<open>_ ! w\<close>] simp del: nth_mem
     dest!: multi_member_split)


lemma unit_propagation_inner_loop_body_l_with_skip_alt_def:
  \<open>unit_propagation_inner_loop_body_l_with_skip L (S', n) = do {
      ASSERT (clauses_to_update_l S' \<noteq> {#} \<or> 0 < n);
      ASSERT (unit_propagation_inner_loop_l_inv L (S', n));
      let _ = ();
      b \<leftarrow> SPEC (\<lambda>b. (b \<longrightarrow> 0 < n) \<and> (\<not> b \<longrightarrow> clauses_to_update_l S' \<noteq> {#}));
      let S' = S';
      let b = b;
      if \<not> b
      then do {
        ASSERT (clauses_to_update_l S' \<noteq> {#});
        X2 \<leftarrow> select_from_clauses_to_update S';
        ASSERT (unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2));
        x \<leftarrow> SPEC (\<lambda>K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2));
        v \<leftarrow> mop_polarity_l (fst X2) x;
        if v = Some True then let T = fst X2 in RETURN (T, if get_conflict_l T = None then n else 0)
        else do {
          v \<leftarrow> pos_of_watched (get_clauses_l (fst X2)) (snd X2) L;
          va \<leftarrow> other_watched_l (fst X2) L (snd X2) v;
          vaa \<leftarrow> mop_polarity_l (fst X2) va;
          if vaa = Some True
         then let T = fst X2 in RETURN (T, if get_conflict_l T = None then n else 0)
          else do {
             x \<leftarrow> find_unwatched_l (get_trail_l (fst X2)) (get_clauses_l (fst X2)) (snd X2);
             case x of
             None \<Rightarrow>
               if vaa = Some False
               then do { T \<leftarrow> set_conflict_l (snd X2) (fst X2);
                    RETURN (T, if get_conflict_l T = None then n else 0) }
               else do { T \<leftarrow> propagate_lit_l va (snd X2) v (fst X2);
                     RETURN (T, if get_conflict_l T = None then n else 0)}
             | Some a \<Rightarrow> do {
                   x \<leftarrow> ASSERT (a < length (get_clauses_l (fst X2) \<propto> snd X2));
                   K \<leftarrow> mop_clauses_at (get_clauses_l (fst X2)) (snd X2) a;
                   val_K \<leftarrow> mop_polarity_l (fst X2) K;
                   if val_K = Some True
                   then let T = fst X2 in RETURN (T, if get_conflict_l T = None then n else 0)
                   else do {
                          T \<leftarrow> update_clause_l (snd X2) v a (fst X2);
                          RETURN (T, if get_conflict_l T = None then n else 0)
                        }
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
    apply (subst Let_def)
    apply (subst Let_def)
    apply (subst Let_def)
    apply (subst Let_def)
    unfolding unit_propagation_inner_loop_body_l_with_skip_def prod.case
      unit_propagation_inner_loop_body_l_def remove_pairs
    unfolding H1 H2 H3 H4 bind_to_let_conv
    by (intro bind_cong[OF refl] if_cong refl option.case_cong) auto
qed

lemma get_subsumed_init_clauses_l_remove_one_lit_from_wq[simp]:
  \<open>get_subsumed_init_clauses_l (remove_one_lit_from_wq a S) = get_subsumed_init_clauses_l S\<close>
  \<open>get_subsumed_clauses_wl (keep_watch L j w S') = get_subsumed_clauses_wl S'\<close>
  \<open>get_subsumed_clauses_wl (set_literals_to_update_wl x S') = get_subsumed_clauses_wl S'\<close>
  by (cases S; cases S'; auto simp: keep_watch_def; fail)+

lemma nth_in_all_lits_stI[simp]:
  \<open>x1 \<in># dom_m (get_clauses_wl S) \<Longrightarrow> i < length (get_clauses_wl S \<propto> x1) \<Longrightarrow>
  get_clauses_wl S \<propto> x1 ! ( i) \<in># all_lits_st S\<close>
  using in_clause_in_all_lits_of_m[of \<open>get_clauses_wl S \<propto> x1 ! i\<close> \<open>mset(get_clauses_wl S \<propto> x1)\<close>]
  by (auto simp: all_lits_def all_lits_st_def all_lits_of_mm_union ran_m_def
      all_lits_of_mm_add_mset dest!: multi_member_split)


lemma all_lits_st_keep_watch[simp]: \<open>all_lits_st (keep_watch L j w S) = all_lits_st S\<close>
  by (cases S) (auto simp: all_lits_st_def)

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
    blit_in_lit: \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    inner_loop_inv: \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
    n: \<open>n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl S)) (mset (drop w (watched_by S L))))\<close> and
    confl_S: \<open>get_conflict_wl S = None\<close>
  shows unit_propagation_inner_loop_body_wl_int_spec: \<open>unit_propagation_inner_loop_body_wl_int L j w S \<le>
    \<Down>{((i, j, T'), (T, n)).
        (T', T) \<in> state_wl_l (Some (L, j)) \<and>
        correct_watching_except i j L T' \<and>
        blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
        j \<le> length (watched_by T' L) \<and>
        length (watched_by S L) =  length (watched_by T' L) \<and>
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
  let ?M = \<open>get_trail_wl S\<close>

  define i :: nat where
    \<open>i \<equiv> (if get_clauses_wl S \<propto> C' ! 0 = L then 0 else 1)\<close>
  have n_d: \<open>no_dup ?M\<close>
    using S_S' inner_loop_inv apply -
    unfolding unit_propagation_inner_loop_wl_loop_inv_def
      unit_propagation_inner_loop_l_inv_def twl_struct_invs_def
   unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def prod.case
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def pcdcl_all_struct_invs_def state\<^sub>W_of_def
   by normalize_goal+
     (simp only: twl_st_l twl_st_wl twl_st)
  have
    alien_L':
       \<open>L \<in># all_lits_st S\<close>
       (is ?alien')
    using inner_loop_inv twl_struct_invs_no_alien_in_trail[of _ \<open>-L\<close>] unfolding unit_propagation_inner_loop_wl_loop_inv_def
     unit_propagation_inner_loop_l_inv_def prod.case apply - apply normalize_goal+
    by (drule twl_struct_invs_no_alien_in_trail[of _ \<open>-L\<close>])
    (simp_all only: twl_st_wl twl_st_l twl_st multiset.map_comp comp_def clause_twl_clause_of
        ac_simps in_all_lits_uminus_iff)

  have
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
       \<open>L \<in># all_lits_st S\<close>
       (is ?alien) and
    correctly_marked_as_binary: \<open>correctly_marked_as_binary (get_clauses_wl S) (C', bL)\<close>
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
        pcdcl_all_struct_invs_def state\<^sub>W_of_def
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
      using alien uL_M T_T' struct_invs twl_st_l(25)[OF T_T'] S_S'
        twl_struct_invs_no_alien_in_trail[of T' \<open>-L\<close>]
        unit_init_clauses_get_unit_init_clauses_l[OF T_T']
      unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: in_all_lits_of_mm_ain_atms_of_iff)
    then have l_wl_inv: \<open>(S, S') \<in> state_wl_l (Some (L, w)) \<and>
         unit_propagation_inner_loop_body_l_inv L (fst (watched_by S L ! w))
          (remove_one_lit_from_wq (fst (watched_by S L ! w)) S') \<and>
         L \<in># all_lits_st S \<and>
         correct_watching_except j w L S \<and>
         w < length (watched_by S L) \<and> get_conflict_wl S = None\<close>
      using that assms L unfolding unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def
      by (auto simp: twl_st)


    show ?ge
      by (rule ge_0)
    show \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
      using dist S_S' twl_st_l(1-8)[OF T_T'] T_T' unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def
      by (auto simp: twl_st)
    show ?confl
      using confl .
    have \<open>watched_by S L ! w \<in> set (take j (watched_by S L)) \<union> set (drop w (watched_by S L))\<close>
      using L alien_L' C'_dom SLw w_le
      by (cases S)
        (auto simp: in_set_drop_conv_nth)
    then show \<open>correctly_marked_as_binary (get_clauses_wl S) (C', bL)\<close>
      using corr_w alien_L' C'_dom SLw S_S'
      by (cases S; cases \<open>watched_by S L ! w\<close>)
       (clarsimp simp: correct_watching_except.simps Ball_def all_conj_distrib state_wl_l_def
          simp del: Un_iff
           simp flip: all_lits_alt_def2 all_lits_def
        dest!: multi_member_split[of L])
  qed

  have i_def': \<open>i = (if get_clauses_l T \<propto> C' ! 0 = L then 0 else 1)\<close>
    using S_S' unfolding i_def by auto

  have [simp]: \<open>length (watched_by (keep_watch L j w S) L) = length (watched_by S L)\<close> for S j w L
    by (cases S) (auto simp: keep_watch_def)
  have keep_watch_state_wl: \<open>fst (watched_by S L ! w) \<notin># dom_m (get_clauses_wl S) \<Longrightarrow>
     (keep_watch L j w S, S') \<in> state_wl_l (Some (L, Suc w))\<close>
    using S_S' w_le j_w by (cases S; cases S')
      (auto simp: state_wl_l_def keep_watch_def Cons_nth_drop_Suc[symmetric]
        drop_map)
  have [simp]: \<open>drop (Suc w) (watched_by (keep_watch L j w S) L) = drop (Suc w) (watched_by S L)\<close>
    using j_w w_le by (cases S) (auto simp: keep_watch_def)
  have [simp]: \<open>get_clauses_wl (keep_watch L j w S) = get_clauses_wl S\<close> for L j w S
    by (cases S) (auto simp: keep_watch_def)

  have trail_keep_w: \<open>get_trail_wl (keep_watch L j w S) = get_trail_wl S\<close> for L j w S
    by (cases S) (auto simp: keep_watch_def)


  let ?pos_of_watched = \<open>{(j, j'). j = j' \<and> j < 2 \<and> j = i}\<close>

  have pos_of_watched:
     \<open>((N, C, K), (N', C', K')) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<and> N = get_clauses_wl S \<and> C = fst (watched_by S L ! w) \<and> K = L \<Longrightarrow>
     pos_of_watched N C K \<le> \<Down> ?pos_of_watched (pos_of_watched N' C' K')\<close>
     for N N' C C' K K'
     unfolding pos_of_watched_def by refine_rcg (auto simp: i_def)
  have [refine]: \<open>mop_watched_by_at S L w \<le> \<Down> {(Slw, _). Slw = watched_by S L ! w \<and>
           fst (snd (Slw)) \<in># all_lits_st S \<and>
          (fst Slw \<in># dom_m (get_clauses_wl S) \<longrightarrow>
             fst (snd Slw) \<in> set (get_clauses_l S' \<propto> fst (watched_by S L ! w)))} (RETURN ())\<close> (is \<open>_ \<le> \<Down> ?Slw _\<close>)
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close>
    using assms that
    unfolding mop_watched_by_at_def unit_propagation_inner_loop_l_inv_def
       prod.case apply -
    apply normalize_goal+
    apply (cases \<open>watched_by S L ! w\<close>)
    subgoal for T
       using nth_mem[OF w_le] twl_struct_invs_no_alien_in_trail[of T \<open>-L\<close>] apply -
      by refine_vcg
       (auto simp: in_all_lits_of_mm_uminus_iff
         mset_take_mset_drop_mset' correct_watching_except_alt_def2
          blits_in_\<L>\<^sub>i\<^sub>n_def in_all_lits_minus_iff
        dest!: multi_member_split[of L \<open>all_lits_st S\<close>]
        simp flip: Cons_nth_drop_Suc all_lits_def all_lits_alt_def2)
    done
  have [refine]:
     \<open>mop_keep_watch L j w S \<le> \<Down> {(T, T'). T = keep_watch L j w S \<and> T' = S'} (RETURN S')\<close>
    using j_w w_le alien_L' unfolding mop_keep_watch_def all_lits_def
    by refine_rcg (auto simp: ac_simps)

  have keep_watch: \<open>RETURN Sa
        \<le> \<Down>  {(T, (T', C)). (T, T') \<in> state_wl_l (Some (L, Suc w)) \<and>
         C = C' \<and> T' = set_clauses_to_update_l (clauses_to_update_l S' - {#C#}) S'}
        (select_from_clauses_to_update S')\<close>
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>(x', ()) \<in> ?Slw\<close> and
      \<open>x' =(x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      \<open>(Sa, S') \<in>{(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close> and
      \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Sa)\<close>
     for x' x1 x2 x1a x2a b Sa
  proof -
    have \<open>get_conflict_l S' = None\<close>
      using that unfolding unit_propagation_inner_loop_l_inv_def twl_struct_invs_def prod.case
      apply -
      apply normalize_goal+
      by auto
    then show ?thesis
      using S_S' that w_le j_w
      unfolding select_from_clauses_to_update_def keep_watch_def
      by (cases S)
        (auto intro!: RETURN_RES_refine simp: state_wl_l_def drop_map
          Cons_nth_drop_Suc[symmetric] eq_commute[of _ \<open>_ ! w\<close>])
  qed


  have f: \<open>((M, N, C), (M', N', C')) \<in> Id \<Longrightarrow> find_unwatched_l M N C
      \<le> \<Down> {(found, found'). found = found' \<and>
             (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l (N \<propto> C)). -L \<in> lits_of_l M)) \<and>
             (\<forall>j. found = Some j \<longrightarrow> (j < length (N \<propto> C) \<and> (undefined_lit M ((N \<propto> C)!j) \<or> (N \<propto> C)!j \<in> lits_of_l M) \<and> j \<ge> 2)) \<and> distinct (N \<propto> C)
           }
            (find_unwatched_l M' N' C')\<close>
    (is \<open>_ \<Longrightarrow> _ \<le> \<Down> ?find _\<close>) for M M' N N' C C'
    using S_S' unfolding find_unwatched_l_def
    by refine_rcg (auto intro!: RES_refine)

  have update_blit_wl: \<open>update_blit_wl L x1 x2a j w L' Sa
        \<le> \<Down>?unit
           (RETURN(fst X2, if get_conflict_l (fst X2) = None then n else 0))\<close>
    if
      cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>inres (mop_watched_by_at S L w) x'\<close> and
      x': \<open>(x', ()) \<in> ?Slw\<close>
        \<open>x2 =(x1a, x2a)\<close>
        \<open>x' =(x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      \<open>inres (mop_keep_watch L j w S) Sa\<close> and
      Sa: \<open>(Sa, S') \<in>{(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close> and
      dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Sa)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(Sa, X2)
       \<in>{(T, T', C).
          (T, T') \<in> state_wl_l (Some(L, Suc w)) \<and>
          C = C' \<and>
          T' =
          set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S'))
           S'}\<close> and
      l_inv: \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x1a)\<close> and
      \<open>x \<in>{K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>(val_K, v) \<in> Id\<close> and
      \<open>val_K \<noteq> Some True\<close> and
      \<open>v \<noteq> Some True\<close> and
      wl_inv: \<open>unit_prop_body_wl_inv Sa j w L\<close> and
      i: \<open>(ia, va) \<in>{(j, j'). j = j' \<and> j < 2 \<and> j = i}\<close> and
      L': \<open>(L', vaa)
       \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! (1 - ia)}\<close> and
      \<open>val_L' = Some True\<close> and
      \<open>(val_L', vaaa) \<in> Id\<close> and
      \<open>vaaa = Some True\<close>
   for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa
  proof -
    have confl: \<open>get_conflict_wl S = None\<close> and [simp]: \<open>Sa = keep_watch L j w S\<close>
      using S_S' loop_inv cond Sa unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto

    then obtain M N NE UE NEk UEk NS US N0 U0 Q W where
      S: \<open>S = (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
      by (cases S) (auto simp: twl_st_l)
    have dom': \<open>x1 \<in># dom_m (get_clauses_wl (keep_watch L j w S)) \<longleftrightarrow> True\<close>
      using dom by auto
    then have SLW_dom': \<open>fst (watched_by Sa L ! w)
        \<in># dom_m (get_clauses_wl Sa)\<close> and
      SLw': \<open>watched_by S L ! w = (x1, x1a, x2a)\<close>
      using w_le x' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
    have bin: \<open>correctly_marked_as_binary N (x1, N \<propto> x1 ! (Suc 0 - i), x2a)\<close>
      using X2 correctly_marked_as_binary l_inv x' dom' SLw
      by (cases \<open>bL\<close>; cases \<open>W L ! w\<close>)
       (auto simp: S remove_one_lit_from_wq_def correctly_marked_as_binary.simps)

    obtain x where
      S_x: \<open>(Sa, x) \<in> state_wl_l (Some (L, Suc w))\<close> and
      unit_loop_inv:
        \<open>unit_propagation_inner_loop_body_l_inv L (fst (watched_by Sa L ! w))
      x\<close> and
      L: \<open>L \<in># all_lits_st Sa\<close> and
      corr_Sa: \<open>correct_watching_except (Suc j) (Suc w) L Sa\<close> and
      \<open>w < length (watched_by Sa L)\<close> and
      \<open>get_conflict_wl Sa = None\<close>
      using wl_inv SLW_dom' unfolding unit_prop_body_wl_inv_alt_def
      by blast
    obtain x' where
      x_x': \<open>(set_clauses_to_update_l
        (clauses_to_update_l
          x +
          {#fst (watched_by Sa L ! w)#})
        x,
        x') \<in> twl_st_l (Some L)\<close> and
       \<open>twl_struct_invs x'\<close> and
      ge0: \<open>(if get_clauses_l x \<propto> fst (watched_by Sa L ! w) ! 0 = L
        then 0 else 1) < length (get_clauses_l x \<propto> fst (watched_by Sa L ! w))\<close> and
      ge1i: \<open>1 -
      (if get_clauses_l x \<propto> fst (watched_by Sa L ! w) ! 0 = L then 0 else 1)
      < length
          (get_clauses_l x \<propto>
          fst (watched_by Sa L ! w))\<close> and
      L_watched: \<open>L \<in> set (watched_l
                (get_clauses_l x \<propto>
                  fst (watched_by Sa L ! w)))\<close> and
      \<open>get_conflict_l x = None\<close>
      using unit_loop_inv
      unfolding unit_propagation_inner_loop_body_l_inv_def
      by blast

    have unit_T: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that
      by (auto simp: remove_one_lit_from_wq_def)

    have \<open>twl_st_inv x'\<close>
      using \<open>twl_struct_invs x'\<close> unfolding twl_struct_invs_def by fast
    then have \<open>\<exists>x. twl_st_inv
         (x,{#TWL_Clause (mset (watched_l (fst x)))
                (mset (unwatched_l (fst x)))
             . x \<in># init_clss_l N#},
          {#TWL_Clause (mset (watched_l (fst x)))
             (mset (unwatched_l (fst x)))
          . x \<in># learned_clss_l N#},
          None, NE+NEk, UE+UEk, NS, US, N0, U0,
          add_mset
           (L, TWL_Clause
                (mset (watched_l (N \<propto> fst ((W L)[j := W L ! w] ! w))))
                (mset (unwatched_l (N \<propto> fst ((W L)[j := W L ! w] ! w)))))
           {#(L, TWL_Clause (mset (watched_l (N \<propto> x)))
                  (mset (unwatched_l (N \<propto> x))))
           . x \<in>#{#i \<in># mset
                          (drop (Suc w) (map fst ((W L)[j := W L ! w]))).
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

    have watch_by_S_w: \<open>watched_by (keep_watch L j w S) L ! w = (x1, x1a, x2a)\<close>
      using j_w w_le SLw x' Sa unfolding i_def
      by (cases S)
        (auto simp: keep_watch_def split: if_splits)
    have i_le: \<open>i < length (N \<propto> x1)\<close>  \<open>1-i < length (N \<propto> x1)\<close>
      using watch_by_S_w ge0 ge1i S_x assms i
      by (auto simp: S)
    have X2: \<open>X2 = (set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S', x1)\<close>
      using SLw X2 S_S' x' unfolding i_def Sa
      by (auto simp add: twl_st_wl eq_commute[of _ \<open>_ ! w\<close>])
    let ?\<L> = \<open>all_lits_st S\<close>
    have N_x1_in_L: \<open>N \<propto> x1 ! (Suc 0 - i) \<in># ?\<L>\<close>
      using dom i_le by (auto simp: ran_m_def S all_lits_of_mm_add_mset
        intro!: in_clause_in_all_lits_of_m
        dest!: multi_member_split)
    then have L_i: \<open>L = N \<propto> x1 ! i\<close>
      using j_w w_le L_watched ge0 ge1i SLw S_x i Sa SLw' unfolding i_def
      by (auto simp: take_2_if twl_st_wl S keep_watch_def split: if_splits)

    have \<open>((M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W (L := (W L)[j := (x1, L', x2a)])),
       fst X2) \<in> state_wl_l (Some (L, Suc w))\<close>
     using S_S' X2 j_w w_le SLw x' dom L' i SLw' dom unfolding Sa
     by (cases \<open>W L ! w\<close>)
       (auto simp: state_wl_l_def S keep_watch_def drop_map Cons_nth_drop_Suc[symmetric])
    moreover have \<open>n = size {#(i, _) \<in># mset (drop (Suc w) (watched_by S L)).
      i \<notin># dom_m (get_clauses_wl S)#}\<close>
      using dom n w_le
      by (clarsimp_all simp add: SLw' Cons_nth_drop_Suc[symmetric]
          dest!: multi_member_split)
    moreover {
      have \<open>Suc 0 - i \<noteq> i\<close>
        using i by (auto simp: i_def split: if_splits)
      then have \<open>correct_watching_except (Suc j) (Suc w) L
        (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(L := (W L)[j := (x1, L', x2a)]))\<close>
        using SLw apply -
        apply (rule correct_watching_except_update_blit)
        using N_x1_in_L corr_Sa i_le distinct_N_x1 i_le bin SLw' L' i unfolding S Sa
        by (auto simp: L_i keep_watch_def nth_eq_iff_index_eq S all_lits_def ac_simps)
    }
    ultimately show ?thesis
      using j_w w_le i alien_L' dom unit_T N_x1_in_L L' N_x1_in_L blit_in_lit
      unfolding i[symmetric] T_def[symmetric]
      by (auto simp: S update_blit_wl_def keep_watch_def all_lits_def ac_simps
        intro!: ASSERT_leI blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'
         blits_in_\<L>\<^sub>i\<^sub>n_propagate)

  qed

  have set_conflict_wl: \<open>set_conflict_wl x1 Sa
        \<le> \<Down> {(U, U'). get_conflict_l U' \<noteq> None \<and> ((Suc j, Suc w, U), (U', 0)) \<in> ?unit}
           (set_conflict_l (snd X2) (fst X2))\<close>
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>inres (mop_watched_by_at S L w) x'\<close> and
      x': \<open>(x', ())  \<in> ?Slw\<close>
        \<open>x2 =(x1a, x2a)\<close>
        \<open>x' =(x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      \<open>inres (mop_keep_watch L j w S) Sa\<close> and
      Sa: \<open>(Sa, S') \<in>{(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close> and
      \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Sa)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(Sa, X2)
       \<in>{(T, T', C).
          (T, T') \<in> state_wl_l (Some(L, Suc w)) \<and>
          C = C' \<and>
          T' =
          set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S'))
           S'}\<close> and
      \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x1a)\<close> and
      \<open>x \<in>{K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>(val_K, v) \<in> Id\<close> and
      \<open>val_K \<noteq> Some True\<close> and
      \<open>v \<noteq> Some True\<close> and
      \<open>unit_prop_body_wl_inv Sa j w L\<close> and
      \<open>(ia, va) \<in>{(j, j'). j = j' \<and> j < 2 \<and> j = i}\<close> and
      \<open>(L', vaa)
       \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! (1 - ia)}\<close> and
      \<open>(val_L', vaaa) \<in> Id\<close> and
      \<open>val_L' \<noteq> Some True\<close> and
      \<open>vaaa \<noteq> Some True\<close> and
      \<open>(f, x'a) \<in> ?find (get_trail_wl Sa) (get_clauses_wl Sa) x1\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f x1 Sa\<close> and
      \<open>f = None\<close> and
      \<open>x'a = None\<close> and
      \<open>val_L' = Some False\<close> and
      \<open>vaaa = Some False\<close>
   for  x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a
  proof -
    have [simp]: \<open>correct_watching_except a b L (M, N, Some D', NE, UE, NEk, UEk, NS, US, N0, U0, W, oth) \<longleftrightarrow>
        correct_watching_except a b L (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, W, oth)\<close>
         \<open>NO_MATCH {#} W \<Longrightarrow> correct_watching_except a b L (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, W, oth) \<longleftrightarrow>
        correct_watching_except a b L (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, oth)\<close>
      for a b M N D' NE UE W oth NS US N0 U0 NEk UEk
      by (simp_all add: correct_watching_except.simps all_lits_st_def
        set_conflict_wl_def prod.case clause_to_update_def get_clauses_l.simps)
     have [simp]: \<open>NO_MATCH None d \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n(x1b, x1aa, d, x1c, x1d, NEk, UEk, NS, US, N0, U0, x2e, g) \<longleftrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n(x1b, x1aa, None, x1c, x1d, NEk, UEk, NS, US, N0, U0, x2e, g)\<close> and
       [simp]: \<open>NO_MATCH {#} x2e \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n(x1b, x1aa, None, x1c, x1d, NEk, UEk,  NS, US, N0, U0, x2e, g) \<longleftrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n(x1b, x1aa, None, x1c, x1d, NEk, UEk, NS, US, N0, U0, {#}, g)\<close> for x1b x1aa x1c x1d x2e g d NS US N0 U0 NEk UEk
        unfolding blits_in_\<L>\<^sub>i\<^sub>n_def by auto
    have \<open>get_conflict_wl (keep_watch L j w S) = None\<close>
      using confl_S by (cases S) (auto simp: keep_watch_def)
      then have \<open>set_conflict_wl_pre D (keep_watch L j w S) \<Longrightarrow>
        set_conflict_wl D (keep_watch L j w S) \<le> (SPEC(correct_watching_except (Suc j) (Suc w) L))\<close> for D
      using S_S' SLw w_le j_w n that corr_w
        correct_watching_except_correct_watching_except_Suc_Suc_keep_watch[of j w S L]
      by (cases \<open>keep_watch L j w S\<close>)
        (auto intro!: frefI nres_relI simp: set_conflict_wl_def state_wl_l_def
           keep_watch_state_wl
            corr_w correct_watching_except_correct_watching_except_Suc_notin
        intro!: ASSERT_refine_right intro: ASSERT_leI)

    moreover have N_x1_in_L: \<open>get_clauses_wl S \<propto> x1 ! (Suc 0 - i) \<in># all_lits_st S\<close>
      using that i_le2 by (auto simp: ran_m_def all_lits_of_mm_add_mset all_lits_def
          remove_one_lit_from_wq_def eq_commute[of _ \<open>_ ! w\<close>] all_lits_st_def
        intro!: in_clause_in_all_lits_of_m nth_mem
        dest!: multi_member_split[of x1])
    ultimately show ?thesis
      using S_S' Sa X2 SLw w_le j_w n corr_w n blit_in_lit x'
      unfolding set_conflict_wl_def set_conflict_l_def
      apply (cases S; cases S'; cases X2; cases \<open>watched_by S L ! w\<close>)
      apply (refine_rcg)
      subgoal premises p for a ba c d e fa g aa baa ca da ea faa ga x1b x2b x1aa x2aa x1ba x2ba x1c
        x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k unfolding set_conflict_wl_pre_def
        using p apply - by (rule exI[of _ \<open>fst X2\<close>], rule exI[of _ \<open>Some(L, Suc w)\<close>])
         (auto simp add: keep_watch_def eq_commute [of _ \<open>_ ! w\<close>] all_lits_def ac_simps
         intro!: blits_in_\<L>\<^sub>i\<^sub>n_keep_watch' blits_in_\<L>\<^sub>i\<^sub>n_propagate
         simp del: )
     using that
     by (simp_all flip: all_lits_alt_def2 all_lits_def
           add: set_conflict_l_def set_conflict_wl_def state_wl_l_def
           keep_watch_state_wl keep_watch_def drop_map Cons_nth_drop_Suc[symmetric]
            correct_watching_except_correct_watching_except_Suc_Suc_keep_watch
         corr_w correct_watching_except_correct_watching_except_Suc_notin
         blits_in_\<L>\<^sub>i\<^sub>n_keep_watch' blits_in_\<L>\<^sub>i\<^sub>n_propagate)
  qed

  have propagate_lit_wl_general: \<open>propagate_lit_wl_general L' x1 ia Sa
        \<le> \<Down> {(U, U'). ((Suc j, Suc w, U), (U', if get_conflict_l U' = None then n else 0)) \<in> ?unit}
           (propagate_lit_l vaa (snd X2) va (fst X2))\<close>
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>inres (mop_watched_by_at S L w) x'\<close> and
      Slw: \<open>(x', ()) \<in> ?Slw\<close> and
      x': \<open>x2 =(x1a, x2a)\<close>
        \<open>x' =(x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      Sa: \<open>(Sa, S') \<in>{(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close> and
      x1_dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Sa)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(Sa, X2)
       \<in>{(T, T', C).
          (T, T') \<in> state_wl_l (Some(L, Suc w)) \<and>
          C = C' \<and>
          T' =
          set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S'))
           S'}\<close> and
      l_inv: \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x1a)\<close> and
      \<open>x \<in>{K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>(val_K, v) \<in> Id\<close> and
      \<open>val_K \<noteq> Some True\<close> and
      \<open>v \<noteq> Some True\<close> and
      \<open>unit_prop_body_wl_inv Sa j w L\<close> and
      i: \<open>(ia, va) \<in>{(j, j'). j = j' \<and> j < 2 \<and> j = i}\<close> and
      L': \<open>(L', vaa)
       \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! (1 - ia)}\<close> and
      \<open>(val_L', vaaa) \<in> Id\<close> and
      \<open>val_L' \<noteq> Some True\<close> and
      \<open>vaaa \<noteq> Some True\<close> and
      \<open>(f, x'a) \<in> ?find (get_trail_wl Sa) (get_clauses_wl Sa) x1\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f x1 Sa\<close> and
      \<open>f = None\<close> and
      \<open>x'a = None\<close> and
      \<open>val_L' \<noteq> Some False\<close> and
      \<open>vaaa \<noteq> Some False\<close>
    for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a
  proof -
    define i' :: nat where \<open>i' \<equiv> if get_clauses_wl (keep_watch L j w S) \<propto> x1 ! 0 = L then 0 else 1\<close>
    have x[simp]: \<open>watched_by S L ! w = (x1, x1a, x2a)\<close> \<open>Sa = keep_watch L j w S\<close>
      using x' Slw Sa by auto
    have i_alt_def: \<open>i' = (if get_clauses_l (fst X2) \<propto> snd X2 ! 0 = L then 0 else 1)\<close> \<open>i = i'\<close>
      using X2 S_S' i unfolding i'_def x' i_def by (auto)
    have x1_dom[simp]: \<open>x1 \<in># dom_m (get_clauses_wl S)\<close>
      using x1_dom X2 by (cases S) (auto simp: keep_watch_def)
    have [simp]: \<open>get_clauses_wl S \<propto> x1 ! 0 \<noteq> L \<Longrightarrow> get_clauses_wl S \<propto> x1 ! Suc 0 = L\<close> and
      \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close>
      using l_inv X2 S_S' SLw unfolding unit_propagation_inner_loop_body_l_inv_def
      apply - apply normalize_goal+
      by (cases \<open>get_clauses_wl S \<propto> x1\<close>; cases \<open>tl (get_clauses_wl S \<propto> x1)\<close>)
        auto

    have n: \<open>n = size {#(i, _) \<in># mset (drop (Suc w) (watched_by S L)).
        i \<notin># dom_m (get_clauses_wl S)#}\<close>
      using n
      apply (subst (asm) Cons_nth_drop_Suc[symmetric])
      subgoal using w_le by simp
      subgoal using n SLw X2 S_S' unfolding i_def by auto
      done
    have [simp]: \<open>get_conflict_l (fst X2) = get_conflict_wl S\<close>
      using X2 S_S' by auto

    have eq: \<open>a = b \<and> a = get_clauses_wl S \<Longrightarrow> (a, b) \<in> {(a, b). a = b \<and> b = get_clauses_wl S}\<close>
      for a b
      by auto
    have ignored: \<open>P \<le> SPEC P' \<Longrightarrow> P \<le> \<Down> {(S, S'). P' S} (RETURN Q)\<close> for P P' Q
      by (auto simp: conc_fun_RES RETURN_def)
    have [simp]: \<open>i\<le> Suc 0\<close>
      by (simp add: i'_def i_alt_def(2))
    have \<open>get_clauses_wl S \<propto> x1 ! (Suc 0 - i) \<in># all_lits_st S\<close>
      using i_le x1_dom  \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close>
      by (auto simp: i'_def)
    then have
      \<open>(propagate_lit_wl_general (get_clauses_wl S \<propto> x1 ! (Suc 0 - i)) x1 i (keep_watch L j w S)
     \<le> \<Down> (state_wl_l (Some (L, Suc w)))
         (propagate_lit_l (get_clauses_l (fst X2) \<propto> snd X2 ! (Suc 0 - i)) (snd X2) i (fst X2)))\<close>
      using X2 S_S' SLw j_w w_le multi_member_split[OF x1_dom] confl_S x
      by (cases S; cases S')
       (auto simp: state_wl_l_def propagate_lit_wl_general_def keep_watch_def
        propagate_lit_l_def drop_map mop_clauses_swap_def cons_trail_propagate_l_def
          simp flip: all_lits_alt_def2
          intro!: ASSERT_refine_right)
    have \<open>correct_watching_except (Suc j) (Suc w) L (keep_watch L j w S)\<close>
      by (simp add: corr_w correct_watching_except_correct_watching_except_Suc_Suc_keep_watch j_w w_le)
    then have \<open>propagate_lit_wl_general L' x1 ia Sa
       \<le> \<Down> {(S, S'). (correct_watching_except (Suc j) (Suc w) L S)}
          (propagate_lit_l vaa (snd X2) va (fst X2))\<close>
      using X2 Sa
      apply (cases X2, cases \<open>fst X2\<close>, hypsubst)
      unfolding propagate_lit_l_def cons_trail_propagate_l_def nres_monad3
        mop_clauses_swap_def If_bind_distrib apply -
      apply (clarsimp; intro conjI impI ASSERT_refine_right ignored;
         (rule correct_watching_except_correct_watching_except_propagate_lit_wl)?)
      using w_le j_w \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close> confl_S i S_S' L'
      by (cases S; auto simp: keep_watch_def state_wl_l_def simp flip: all_lits_alt_def2; fail)+


    moreover have N_x1_in_L: \<open>x1a \<in># all_lits_st S\<close>
      using that i_le2 by (auto simp: ran_m_def all_lits_of_mm_add_mset all_lits_def
          remove_one_lit_from_wq_def eq_commute[of _ \<open>_ ! w\<close>] ac_simps
        intro!: in_clause_in_all_lits_of_m nth_mem
        dest!: multi_member_split[of x1])
    then have \<open>propagate_lit_wl_general L' x1 ia Sa
       \<le> \<Down> {(S, S'). (blits_in_\<L>\<^sub>i\<^sub>n S)}
          (propagate_lit_l vaa (snd X2) va (fst X2))\<close>
      using X2 Sa
      apply (cases X2, cases \<open>fst X2\<close>, hypsubst)
      unfolding propagate_lit_l_def propagate_lit_wl_general_def cons_trail_propagate_l_def nres_monad3
        mop_clauses_swap_def If_bind_distrib apply -
      apply (clarsimp; intro conjI impI ASSERT_refine_right ignored)
      using w_le j_w \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close> confl_S i S_S' L' x x1_dom blit_in_lit
      apply (cases S; auto simp: keep_watch_def state_wl_l_def blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'
         blits_in_\<L>\<^sub>i\<^sub>n_propagate simp flip: all_lits_alt_def2 all_lits_def)
      using w_le j_w \<open>Suc 0 < length (get_clauses_wl S \<propto> x1)\<close> confl_S i S_S' L' x x1_dom blit_in_lit
      apply (cases S; auto simp: keep_watch_def state_wl_l_def blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'
         blits_in_\<L>\<^sub>i\<^sub>n_propagate simp flip: all_lits_alt_def2 all_lits_def)
      done
    moreover have \<open>propagate_lit_wl_general L' x1 ia Sa
    \<le> \<Down>{(U, U').
         ((Suc j, Suc w, U), U', if get_conflict_l U' = None then n else 0)
         \<in>{((i, j, T'), T, n).
           (T', T) \<in> state_wl_l (Some (L, Suc w)) \<and>
            j \<le> length (watched_by T' L) \<and>
            length (watched_by S L) = length (watched_by T' L) \<and>
            i \<le> j \<and>
            (get_conflict_wl T' = None \<longrightarrow>
             n =
             size
              {#(i, _)\<in># mset (drop j (watched_by T' L)).
               i \<notin># dom_m (get_clauses_wl T')#}) \<and>
            (get_conflict_wl T' \<noteq> None \<longrightarrow> n = 0)}}
       (propagate_lit_l vaa (snd X2) va (fst X2))\<close>
      using w_le n j_w x1_dom that S_S' confl_S i_le2 x
      unfolding i'_def[symmetric] i_alt_def[symmetric] propagate_lit_wl_general_def
         propagate_lit_l_def If_bind_distrib
      apply (refine_rcg refine_itself2[of cons_trail_propagate_l, THEN fref_to_Down_curry2])
      subgoal by (cases S) (auto simp: keep_watch_def)
      subgoal by (cases S) (auto simp: keep_watch_def)
      subgoal using S_S'  by (cases S) (auto simp: keep_watch_def state_wl_l_def all_lits_st_def
           all_lits_of_st_l_def all_lits_def
         simp flip: all_lits_alt_def2)
      subgoal by fast
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      subgoal by (auto simp: state_wl_l_def)
      apply (rule mop_clauses_swap_itself_spec2)
      subgoal by (auto simp: state_wl_l_def)
      subgoal
        by (cases X2; cases S; cases S')
         (clarsimp simp: state_wl_l_def mop_clauses_swap_def drop_map
          op_clauses_swap_def keep_watch_def)
      apply (rule eq)
      subgoal by (cases X2; cases S; cases S')
         (auto simp: twl_st_wl simp: op_clauses_swap_def keep_watch_def
             propagate_lit_l_def mop_clauses_swap_def drop_map state_wl_l_def
           intro!: ASSERT_refine_right)
      subgoal by (cases X2; cases S; cases S')
         (clarsimp simp add:  op_clauses_swap_def keep_watch_def
          propagate_lit_l_def mop_clauses_swap_def  state_wl_l_def
          intro!: ASSERT_refine_right)
      done
    ultimately show ?thesis
      apply (rule nres_add_unrelated[OF nres_add_unrelated3, THEN order_trans])
      apply (rule conc_fun_R_mono)
      apply fastforce
      done
  qed

  have update_blit: \<open>update_blit_wl L x1 x2a j w Ka Sa
        \<le> \<Down>?unit
           (RETURN(fst X2, if get_conflict_l (fst X2) = None then n else 0))\<close>
    if
      cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>inres (mop_watched_by_at S L w) x'\<close> and
      x': \<open>(x', ()) \<in> ?Slw\<close>
        \<open>x2 =(x1a, x2a)\<close>
        \<open>x' =(x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      \<open>inres (mop_keep_watch L j w S) Sa\<close> and
      Sa: \<open>(Sa, S') \<in>{(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close> and
      dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Sa)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
     X2: \<open>(Sa, X2)
       \<in>{(T, T', C).
          (T, T') \<in> state_wl_l (Some(L, Suc w)) \<and>
          C = C' \<and>
          T' =
          set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S'))
           S'}\<close> and
      \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x1a)\<close> and
      \<open>x \<in>{K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>(val_K, v) \<in> Id\<close> and
      \<open>val_K \<noteq> Some True\<close> and
      \<open>v \<noteq> Some True\<close> and
      \<open>unit_prop_body_wl_inv Sa j w L\<close> and
      \<open>(ia, va) \<in>{(j, j'). j = j' \<and> j < 2 \<and> j = i}\<close> and
      \<open>(L', vaa)
       \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! (1 - ia)}\<close> and
      \<open>(val_L', vaaa) \<in> Id\<close> and
      \<open>val_L' \<noteq> Some True\<close> and
      \<open>vaaa \<noteq> Some True\<close> and
      fx': \<open>(f, x'a) \<in> ?find (get_trail_wl Sa) (get_clauses_wl Sa) x1\<close>
        \<open>f = Some xa\<close>
        \<open>x'a = Some x'b\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f x1 Sa\<close> and
      \<open>(xa, x'b) \<in> nat_rel\<close> and
      \<open>x'b < length (get_clauses_l (fst X2) \<propto> snd X2)\<close> and
      Ka: \<open>(Ka, Kb) \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! xa}\<close> and
      \<open>(val_L'a, val_Ka) \<in> Id\<close> and
      \<open>val_L'a = Some True\<close> and
      \<open>val_Ka = Some True\<close>
   for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a xa
       x'b Ka Kb val_L'a val_Ka
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
       (a, b, None, d, e, NEk, UEk, NS, US, N0, U0, f, ga(L := (ga L)[j := (x1, b \<propto> x1 ! xa, x2a)]))\<close>
      if
        corr: \<open>correct_watching_except (Suc j) (Suc w) L
      (a, b, None, d, e, NEk, UEk, NS, US, N0, U0, f, ga(L := (ga L)[j := (x1, x1a, x2a)]))\<close> and
        \<open>ga L ! w = (x1, x1a, x2a)\<close> and
        S[simp]: \<open>S = (a, b, None, d, e, NEk, UEk, NS, US, N0, U0, f, ga)\<close> and
        \<open>X2 = (set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S', x1)\<close> and
        \<open>(a, b, None, d, e, NEk, UEk, NS, US, N0, U0, 
      {#i \<in># mset (drop (Suc w) (map fst ((ga L)[j := (x1, x1a, x2a)]))). i \<in># dom_m b#}, f) =
      set_clauses_to_update_l (remove1_mset x1 (clauses_to_update_l S')) S'\<close>
      for a :: \<open>('v literal, 'v literal,nat) annotated_lit list\<close> and
        b :: \<open>(nat, 'v literal list \<times>  bool) fmap\<close> and
        d e NS US N0 U0 NEk UEk :: \<open>'v literal multiset multiset\<close> and
        f :: \<open>'v literal multiset\<close> and
        ga :: \<open>'v literal \<Rightarrow> (nat \<times> 'v literal \<times> bool) list\<close>
    proof -
      have \<open>b \<propto> x1 ! xa \<in># all_lits_st (a, b, None, d, e, NEk, UEk, NS, US, N0, U0, f, ga)\<close>
        using dom fx' Sa by (auto simp: ran_m_def all_lits_of_mm_add_mset x' f twl_st_wl
            dest!: multi_member_split
            simp: all_lits_def
            intro!: in_clause_in_all_lits_of_m)
      moreover have \<open>b \<propto> x1 ! xa \<in> set (b \<propto> x1)\<close>
        using dom fx' Sa by (auto simp: ran_m_def all_lits_of_mm_add_mset x' f twl_st_wl
            dest!: multi_member_split
            intro!: in_clause_in_all_lits_of_m)

      moreover have \<open>b \<propto> x1 ! xa \<noteq> L\<close>
        using X2 L_def[OF unit_T] S_S' SLw fx' x' that Sa
        by (auto simp: polarity_def split: if_splits)
      moreover have \<open>correctly_marked_as_binary b (x1, b \<propto> x1 ! xa, x2a)\<close>
        using correctly_marked_as_binary unit_T dom Sa SLw
        by (auto simp: correctly_marked_as_binary.simps \<open>ga L ! w = (x1, x1a, x2a)\<close>)
      ultimately show ?thesis
        by (rule correct_watching_except_update_blit[OF corr])
    qed
    moreover have in_all: \<open>get_clauses_wl S \<propto> x1 ! xa \<in># all_lits_st S\<close>
      using dom fx' Sa unfolding x'
      by (auto dest!: multi_member_split[of x1]
        simp: ran_m_def all_lits_of_mm_add_mset all_lits_of_mm_union
          in_clause_in_all_lits_of_m all_lits_def)
    moreover have w: \<open>watched_by S L ! w = (x1, x1a, x2a)\<close>
      using x' by auto
    ultimately have u: \<open>update_blit_wl L x1 x2a j w Ka Sa
    \<le> SPEC(\<lambda>(i, j, T'). correct_watching_except i j L T')\<close>
      using X2 confl Sa SLw alien_L' unit_T Ka dom  j_w w_le unfolding T_def[symmetric]
        update_blit_wl_def
      apply (cases S; cases Sa, hypsubst) apply simp
      apply  (auto simp: keep_watch_def state_wl_l_def
           simp flip: all_lits_alt_def2 all_lits_def
           intro!: ASSERT_leI)
      done
    have b: \<open>update_blit_wl L x1 x2a j w Ka Sa
    \<le> SPEC(\<lambda>(i, j, T'). blits_in_\<L>\<^sub>i\<^sub>n T')\<close>
      using X2 confl Sa SLw alien_L' in_all unit_T Ka blit_in_lit j_w w_le dom unfolding T_def[symmetric]
        update_blit_wl_def
      apply (cases S; cases Sa, hypsubst) apply simp
      apply  (auto simp: keep_watch_def state_wl_l_def blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'
              blits_in_\<L>\<^sub>i\<^sub>n_propagate all_lits_def ac_simps
           intro!: ASSERT_leI blits_in_\<L>\<^sub>i\<^sub>n_keep_watch')
      done
    have \<open>get_conflict_wl S = None\<close>
      using S_S' loop_inv cond unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto
    moreover have \<open>n = size {#(i, _) \<in># mset (drop (Suc w) (watched_by S L)). i \<notin># dom_m (get_clauses_wl S)#}\<close>
      using n dom X2 w_le S_S' SLw Sa
      by (auto simp: Cons_nth_drop_Suc[symmetric] w)
    ultimately have \<open>update_blit_wl L x1 x2a j w Ka Sa
    \<le> \<Down>{((i, j, T'), T, n).
         (T', T) \<in> state_wl_l (Some(L, j)) \<and>
         j \<le> length (watched_by T' L) \<and>
         length (watched_by S L) = length (watched_by T' L) \<and>
         i \<le> j \<and>
         (get_conflict_wl T' = None \<longrightarrow>
          n =
          size
           {#(i, _)\<in># mset (drop j (watched_by T' L)).
            i \<notin># dom_m (get_clauses_wl T')#}) \<and>
         (get_conflict_wl T' \<noteq> None \<longrightarrow> n = 0)}
       (RETURN(fst X2, if get_conflict_l (fst X2) = None then n else 0))\<close>
      using j_w w_le S_S' X2 alien_L' unit_T in_all Sa in_all Ka dom unfolding T_def[symmetric]
      by (cases S)
        (auto simp: update_blit_wl_def keep_watch_def state_wl_l_def drop_map w
           simp flip: all_lits_alt_def2 all_lits_def
           intro!: ASSERT_leI)

    then show ?thesis
      apply (rule nres_add_unrelated2[OF SPEC_rule_conjI[OF u b] _, THEN order_trans])
      apply (rule conc_fun_R_mono)
      apply fastforce
      done
  qed

  have find_is_nat_rel: \<open>x \<in> ?find a b c \<Longrightarrow> x \<in> \<langle>nat_rel\<rangle>option_rel\<close> for x a b c
    by auto
  have update_clause_wl: \<open>update_clause_wl L L' x1 x2a j w ia xa Sa
        \<le> \<Down>?unit
           (do{
              T \<leftarrow> update_clause_l (snd X2) va x'b (fst X2);
              RETURN(T, if get_conflict_l T = None then n else 0)
            })\<close>
    if
      cond: \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      loop_inv: \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>inres (mop_watched_by_at S L w) x'\<close> and
      x': \<open>(x', ())
       \<in> ?Slw\<close> and
      [simp]: \<open>x2 =(x1a, x2a)\<close> \<open>x' =(x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      \<open>inres (mop_keep_watch L j w S) Sa\<close> and
      Sa: \<open>(Sa, S') \<in>{(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close> and
      dom: \<open>\<not> x1 \<notin># dom_m (get_clauses_wl Sa)\<close> and
      \<open>\<not> b\<close> and
      \<open>clauses_to_update_l S' \<noteq> {#}\<close> and
      X2: \<open>(Sa, X2)
       \<in>{(T, T', C).
          (T, T') \<in> state_wl_l (Some(L, Suc w)) \<and>
          C = C' \<and>
          T' = set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S')) S'}\<close> and
      pre: \<open>unit_propagation_inner_loop_body_l_inv L (snd X2) (fst X2)\<close> and
      \<open>(K, x) \<in> Id\<close> and
      \<open>K \<in> Collect ((=) x1a)\<close> and
      \<open>x \<in>{K. K \<in> set (get_clauses_l (fst X2) \<propto> snd X2)}\<close> and
      \<open>(val_K, v) \<in> Id\<close> and
      \<open>val_K \<noteq> Some True\<close> and
      \<open>v \<noteq> Some True\<close> and
      wl_inv: \<open>unit_prop_body_wl_inv Sa j w L\<close> and
      i: \<open>(ia, va) \<in>{(j, j'). j = j' \<and> j < 2 \<and> j = i}\<close> and
      L': \<open>(L', vaa)
       \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! (1 - ia)}\<close> and
      \<open>(val_L', vaaa) \<in> Id\<close> and
      \<open>val_L' \<noteq> Some True\<close> and
      \<open>vaaa \<noteq> Some True\<close> and
      fx': \<open>(f, x'a) \<in> ?find (get_trail_wl Sa) (get_clauses_wl Sa) x1\<close> and
      \<open>unit_prop_body_wl_find_unwatched_inv f x1 Sa\<close> and
      [simp]: \<open>f = Some xa\<close> \<open>x'a = Some x'b\<close> and
      \<open>(xa, x'b) \<in> nat_rel\<close> and
      \<open>x'b < length (get_clauses_l (fst X2) \<propto> snd X2)\<close> and
      Ka: \<open>(Ka, Kb) \<in>{(L, L'). L = L' \<and> L = get_clauses_wl Sa \<propto> x1 ! xa}\<close> and
      \<open>(val_L'a, val_Ka) \<in> Id\<close> and
      \<open>val_L'a \<noteq> Some True\<close> and
      \<open>val_Ka \<noteq> Some True\<close>
    for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a xa
       x'b Ka Kb val_L'a val_Ka
  proof -
    have [simp]: \<open>xa = x'b\<close> \<open>Ka = Kb\<close> \<open>Kb = get_clauses_wl Sa \<propto> x1 ! xa\<close> \<open>ia = va\<close>
       using fx' Ka i by auto
    have update_clause_l_alt_def:
      \<open>update_clause_l = (\<lambda>C i f (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
           ASSERT (update_clause_l_pre  C i f (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
           K \<leftarrow> RETURN (op_clauses_at N C f);
           N' \<leftarrow> mop_clauses_swap N C i f;
           RETURN (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
      })\<close>
      unfolding update_clause_l_def by (auto intro!: ext)
    have unit_T: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
      using that by (auto simp: remove_one_lit_from_wq_def)
    have w: \<open>watched_by S L ! w = (x1, x1a, x2a)\<close>
      using x' by auto
    have alien_K: \<open>Ka \<in># all_lits_st Sa\<close>
      using Sa dom fx' unfolding all_lits_def
      by (cases S; cases Sa)
        (auto simp: keep_watch_def ran_m_def all_lits_of_mm_add_mset
        intro!: in_clause_in_all_lits_of_m
        dest!: multi_member_split)
    have L_in_watched: \<open>L \<in> set (watched_l (get_clauses_wl Sa \<propto> x1))\<close>
      using corr_w alien_L' Sa X2 w_le w dom by (cases S)
        (clarsimp simp: correct_watching_except_alt_def keep_watch_def
          simp flip: Cons_nth_drop_Suc all_lits_alt_def2 all_lits_def
          dest!: multi_member_split)
    then have LKa: \<open>L \<noteq> Ka\<close>
       using fx' Ka by (auto simp: in_set_conv_nth nth_eq_iff_index_eq)
    have L: \<open>get_clauses_wl Sa \<propto> x1 ! i = L\<close>  \<open>get_clauses_wl Sa \<propto> x1 ! (Suc 0 - i) \<noteq> L\<close>
       \<open>get_clauses_wl Sa \<propto> x1 ! (Suc 0 - i) \<noteq> Ka\<close>
      using i Sa w L_in_watched fx' Ka unfolding i_def
      by (auto simp: in_set_conv_nth nth_eq_iff_index_eq)
    have corr: \<open>correct_watching_except (Suc j) (Suc w) L Sa\<close>
      using wl_inv dom w Sa unfolding unit_prop_body_wl_inv_def by auto
    have confl: \<open>get_conflict_wl S = None\<close>
      using S_S' loop_inv cond unfolding unit_propagation_inner_loop_l_inv_def prod.case apply -
      by normalize_goal+ auto
  have
    alien_L'':
       \<open>L' \<in># all_lits_st Sa\<close>
    using L' i_le2[OF unit_T] i dom Sa w
    by (auto intro!: nth_in_all_lits_stI)

    show ?thesis
      supply RETURN_as_SPEC_refine[refine2 del]
      unfolding update_clause_l_alt_def update_clause_wl_def
      apply (cases X2; cases \<open>fst X2\<close>; cases Sa; hypsubst; unfold fst_conv; hypsubst;
        unfold prod.case snd_conv nres_monad3)
      apply (refine_rcg mop_clauses_at_op_clauses_at_spec2
         mop_clauses_swap_itself_spec2)
      subgoal using alien_L' Sa X2 dom by (cases S; auto simp: keep_watch_def)
      subgoal using alien_L' Sa X2 j_w w_le dom by (cases S; auto simp: keep_watch_def)
      subgoal using alien_L' Sa X2 j_w w_le dom by (cases S; auto simp: keep_watch_def)
      subgoal using alien_L' Sa X2 j_w w_le dom corr by (cases S; auto simp: keep_watch_def)
      subgoal using alien_L' Sa X2 by (cases S; auto simp: keep_watch_def
           simp flip: all_lits_alt_def2 all_lits_def)
      subgoal using alien_L'' by auto
      subgoal using dom Sa X2 w S_S' by (cases S; cases S'; auto simp: state_wl_l_def keep_watch_def)
      subgoal using fx' Sa S_S' X2 w dom by (cases S; cases S'; auto simp: state_wl_l_def keep_watch_def)
      subgoal using fx' Sa S_S' X2 w alien_K by (cases S; cases S'; auto simp: state_wl_l_def keep_watch_def all_lits_def)
      subgoal using fx' Sa S_S' X2 w alien_K by (cases S; cases S'; auto simp: state_wl_l_def
        keep_watch_def all_lits_def ac_simps)
      subgoal using LKa Ka by (auto simp: state_wl_l_def keep_watch_def)
      subgoal using fx' Sa S_S' X2 w by (cases S; cases S'; auto simp: state_wl_l_def keep_watch_def)

      subgoal supply [[goals_limit=1]]
        using Sa S_S' X2 w w_le j_w n corr LKa i L_in_watched Ka L fx' blit_in_lit alien_L' L'
           alien_K confl x' unfolding all_lits_def[symmetric] all_lits_alt_def[symmetric]
        apply (cases S; cases S')
        apply (clarsimp simp add: state_wl_l_def  keep_watch_def op_clauses_swap_def  blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'
              blits_in_\<L>\<^sub>i\<^sub>n_propagate correct_watching_except_correct_watching_except_update_clause
          simp flip: Cons_nth_drop_Suc
          intro!: blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'')
        apply (intro conjI correct_watching_except_correct_watching_except_update_clause
          blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'')
        apply (clarsimp intro!: correct_watching_except_correct_watching_except_update_clause)[]
        apply (auto simp: state_wl_l_def keep_watch_def op_clauses_swap_def  blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'
              blits_in_\<L>\<^sub>i\<^sub>n_propagate all_lits_def ac_simps
          simp flip: Cons_nth_drop_Suc  dest: in_set_takeD
          intro!: correct_watching_except_correct_watching_except_update_clause
               blits_in_\<L>\<^sub>i\<^sub>n_keep_watch'')
         done
      done
  qed

  have in_watched_keepD: \<open>x \<in> set (watched_by (keep_watch L j w S) L') \<Longrightarrow> x \<in> set (watched_by S L')\<close>
     for x L'
    using j_w w_le by (cases S) (clarsimp simp: keep_watch_def elim!: in_set_upd_cases split: if_splits)

  have is_nondeleted_clause_pre: \<open>is_nondeleted_clause_pre x1 L Sa\<close>
    if
      \<open>clauses_to_update_l S' \<noteq> {#} \<or> 0 < n\<close> and
      \<open>unit_propagation_inner_loop_l_inv L (S', n)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_pre L (j, w, S)\<close> and
      \<open>inres (mop_watched_by_at S L w) x'\<close> and
      x': \<open>(x', ()) \<in> ?Slw\<close> and
      [simp]: \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close> and
      \<open>(x1 \<notin># dom_m (get_clauses_wl S), b) \<in> bool_rel\<close> and
      \<open>inres (mop_keep_watch L j w S) Sa\<close> and
      Sa: \<open>(Sa, S') \<in> {(T, T'). T = keep_watch L j w S \<and> T' = S'}\<close>
     for x' x1 x2 x1a x2a b Sa
  proof -
    have \<open>watched_by Sa L ! w = x'\<close> \<open>w < length (watched_by Sa L)\<close>
      using that using j_w w_le by auto
    then have  \<open>x' \<in> set (watched_by Sa L)\<close>
      using j_w w_le by force
    then show ?thesis using j_w w_le x' alien_L' Sa
      by (auto simp: is_nondeleted_clause_pre_def eq_commute[of \<open>(_, _)\<close> \<open>_ ! w\<close>]
        simp flip: all_lits_alt_def2)
  qed


  have other_watched_wl_itself_spec2[refine]:
    \<open>((N, C, i, j), (N', C', i', j')) \<in> Id \<Longrightarrow>
       other_watched_wl N C i j \<le> \<Down> Id (other_watched_wl N' C' i' j')\<close>
    for N i j N' i' j' and C C' :: \<open>'v literal\<close>
    by (auto intro!: frefI nres_relI ASSERT_refine_right simp: mop_clauses_swap_def
      op_clauses_swap_def)

  show 1: ?propa
    (is \<open>_ \<le> \<Down> ?unit _\<close>)
    supply trail_keep_w[simp]
    unfolding unit_propagation_inner_loop_body_wl_int_alt_def
      i_def[symmetric] i_def'[symmetric] unit_propagation_inner_loop_body_l_with_skip_alt_def
      unit_propagation_inner_loop_body_l_def
    unfolding i_def[symmetric] SLw prod.case all_lits_alt_def2[symmetric] all_lits_def[symmetric]
    apply (rewrite in \<open>if (\<not>_) then ASSERT _ >>= _ else _\<close> if_not_swap)
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (refine_rcg f (*val f f' find_unwatched_l*)
       mop_polarity_wl_mop_polarity_l[where b = \<open>Some(L, Suc w)\<close>, THEN fref_to_Down_curry]
       mop_clauses_at_itself_spec pos_of_watched
       other_watched_wl_other_watched_l_spec_itself[of _ _ _ _ _ _ _ _  \<open>Some(L, Suc w)\<close>])
    subgoal using inner_loop_inv w_le j_w blit_in_lit
      unfolding unit_propagation_inner_loop_wl_loop_pre_def by auto
    subgoal
      using j_w w_le S_S'
      by (cases S; cases S')
       (auto simp: n state_wl_l_def unit_propagation_inner_loop_wl_loop_pre_def
           unit_propagation_inner_loop_l_inv_def twl_st_l_def
         simp flip: Cons_nth_drop_Suc)
    subgoal by (rule is_nondeleted_clause_pre)
    subgoal by simp
    subgoal for x' x1 x2 x1a x2a b Sa
      using assms j_w w_le n_d blit_in_lit unfolding unit_prop_body_wl_inv_def mop_polarity_wl_def
         nres_monad3 unit_propagation_inner_loop_wl_loop_pre_def
     using S_S' w_le j_w n confl_S apply -
     apply refine_vcg
     apply (auto simp: keep_watch_state_wl assert_bind_spec_conv Let_def twl_st_wl
        Cons_nth_drop_Suc[symmetric] correct_watching_except_correct_watching_except_Suc_Suc_keep_watch  blits_in_\<L>\<^sub>i\<^sub>n_def
        corr_w correct_watching_except_correct_watching_except_Suc_notin
        simp flip: all_lits_alt_def2
        split: if_splits dest: multi_member_split dest!: in_watched_keepD)
    done
    apply (rule keep_watch; assumption+)
    subgoal by auto \<comment> \<open>selection of K\<close>
    subgoal by fast
    subgoal by auto
    subgoal by auto \<comment> \<open>If condition\<close>
    subgoal for x' x1 x2 x1a x2a b Sa
      using j_w w_le S_S' blit_in_lit
      by (auto simp: n keep_watch_state_wl assert_bind_spec_conv Let_def twl_st_wl
          Cons_nth_drop_Suc[symmetric] correct_watching_except_correct_watching_except_Suc_Suc_keep_watch  blits_in_\<L>\<^sub>i\<^sub>n_def
          corr_w correct_watching_except_correct_watching_except_Suc_notin
          simp flip: all_lits_def
          split: if_splits dest: multi_member_split dest!: in_watched_keepD)
    subgoal for x' x1 x2 x1a x2a b Sa X2 K x val_K v
      using w_le j_w corr_w alien_L' S_S' blit_in_lit unfolding unit_prop_body_wl_inv_def
           all_lits_def[symmetric] all_lits_alt_def[symmetric] all_lits_alt_def2[symmetric]
       apply (intro conjI impI)
      apply (auto simp: blits_in_\<L>\<^sub>i\<^sub>n_keep_watch2)[4]
      apply (rule exI[of _ \<open>fst X2\<close>])
      apply (auto simp: remove_one_lit_from_wq_def
       correct_watching_except_correct_watching_except_Suc_Suc_keep_watch simp flip: all_lits_def)
      done
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal by simp
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal by fast
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal by simp \<comment> \<open>polarity\<close>
     subgoal for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa
         by (rule update_blit_wl)
     subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
     subgoal unfolding unit_prop_body_wl_find_unwatched_inv_def by fast
     apply (rule find_is_nat_rel; assumption)
     subgoal by auto
     apply (rule set_conflict_wl; assumption)
     subgoal for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a
       by force
     apply (rule propagate_lit_wl_general; assumption)
    subgoal
      by auto
    subgoal using S_S' by (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
    subgoal by fast
    subgoal by auto
    subgoal for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a xa
      using S_S' by (cases \<open>X2\<close>) (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
    subgoal by fast
    subgoal for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a xa
      using S_S' by (cases \<open>X2\<close>) (auto simp: eq_commute[of _ \<open>_ ! w\<close>])
    subgoal by simp \<comment> \<open>polarity\<close>
    subgoal for x' x1 x2 x1a x2a b Sa X2 K x val_K v ia va L' vaa val_L' vaaa f x'a xa
         x'b Ka Kb val_L'a val_Ka
      by (rule update_blit)
    subgoal by (rule update_clause_wl)
    done

  have [simp]: \<open>add_mset a (remove1_mset a M) = M \<longleftrightarrow> a \<in># M\<close> for a M
    by (metis ab_semigroup_add_class.add.commute add.left_neutral multi_self_add_other_not_self
       remove1_mset_eqE union_mset_add_mset_left)

  show ?eq if inv: \<open>unit_propagation_inner_loop_body_l_inv L C' T\<close>
    using i_le[OF inv] i_le2[OF inv] C'_dom[OF inv] S_S'
    unfolding i_def[symmetric]
    by (auto simp: ran_m_clause_upd image_mset_remove1_mset_if)
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
    blit_in_lit: \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    inner_loop_inv: \<open>unit_propagation_inner_loop_wl_loop_inv L (j, w, S)\<close> and
    n: \<open>n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl S)) (mset (drop w (watched_by S L))))\<close> and
    confl_S: \<open>get_conflict_wl S = None\<close>
  shows unit_propagation_inner_loop_body_wl_spec: \<open>unit_propagation_inner_loop_body_wl L j w S \<le>
    \<Down>{((i, j, T'), (T, n)).
        (T', T) \<in> state_wl_l (Some (L, j)) \<and>
        correct_watching_except i j L T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
        j \<le> length (watched_by T' L) \<and>
        length (watched_by S L) =  length (watched_by T' L) \<and>
        i \<le> j \<and>
        (get_conflict_wl T' = None \<longrightarrow>
           n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl T')) (mset (drop j (watched_by T' L))))) \<and>
        (get_conflict_wl T' \<noteq> None \<longrightarrow> n = 0)}
     (unit_propagation_inner_loop_body_l_with_skip L (S', n))\<close>
  apply (rule order_trans)
   apply (rule unit_propagation_inner_loop_body_wl_wl_int[OF S_S' w_le j_w corr_w inner_loop_inv n
       confl_S])
  apply (subst Down_id_eq)
   apply (rule unit_propagation_inner_loop_body_wl_int_spec[OF S_S' w_le j_w corr_w blit_in_lit inner_loop_inv n
       confl_S])
  done




definition unit_propagation_inner_loop_wl_loop
   :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> (nat \<times> nat \<times> 'v twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    ASSERT(L \<in># all_lits_st S\<^sub>0);
    let n = length (watched_by S\<^sub>0 L);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
      (\<lambda>(j, w, S). w < n \<and> get_conflict_wl S = None)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl L j w S
      })
      (0, 0, S\<^sub>0)
  }\<close>

lemma blits_in_\<L>\<^sub>i\<^sub>n_cut_watch:
  assumes corr: \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g(L := take j (g L) @ drop w (g L)))\<close>
  using assms by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def dest!: in_set_takeD in_set_dropD)

lemma correct_watching_except_correct_watching_cut_watch:
  assumes corr: \<open>correct_watching_except j w L (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  shows \<open>correct_watching (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g(L := take j (g L) @ drop w (g L)))\<close>
proof -
  let ?\<L> = \<open>all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g(L := take j (g L) @ drop w (g L)))\<close>
  have \<L>: \<open>?\<L> =  all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
    by (auto simp: all_lits_st_def)
  have
    Heq:
      \<open>\<And>La i K b'. La \<in># ?\<L> \<Longrightarrow>
      (La = L \<longrightarrow>
       distinct_watched (take j (g La) @ drop w (g La)) \<and>
       ((i, K, b')\<in>#mset (take j (g La) @ drop w (g La)) \<longrightarrow>
           i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La \<and> correctly_marked_as_binary b (i, K, b')) \<and>
       ((i, K, b')\<in>#mset (take j (g La) @ drop w (g La)) \<longrightarrow>
           b' \<longrightarrow> i \<in># dom_m b) \<and>
       {#i \<in># fst `# mset (take j (g La) @ drop w (g La)). i \<in># dom_m b#} =
       clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close> and
    Hneq:
      \<open>\<And>La i K b'. La\<in>#?\<L> \<Longrightarrow>
      (La \<noteq> L \<longrightarrow>
       distinct_watched (g La) \<and>
       ((i, K, b')\<in>#mset (g La) \<longrightarrow> i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La
          \<and> correctly_marked_as_binary b (i, K, b')) \<and>
        ((i, K, b')\<in>#mset (g La) \<longrightarrow> b' \<longrightarrow> i \<in># dom_m b) \<and>
       {#i \<in># fst `# mset (g La). i \<in># dom_m b#} =
       clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>
    using corr
    unfolding correct_watching.simps correct_watching_except.simps \<L>
    by fast+
  have
    \<open>((i, K, b')\<in>#mset ((g(L := take j (g L) @ drop w (g L))) La) \<Longrightarrow>
            i \<in># dom_m b \<longrightarrow> K \<in> set (b \<propto> i) \<and> K \<noteq> La \<and> correctly_marked_as_binary b (i, K, b'))\<close> and
    \<open>(i, K, b')\<in>#mset ((g(L := take j (g L) @ drop w (g L))) La) \<Longrightarrow>
            b' \<longrightarrow> i \<in># dom_m b\<close> and
    \<open>{#i \<in># fst `# mset ((g(L := take j (g L) @ drop w (g L))) La).
         i \<in># dom_m b#} =
        clause_to_update La (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>and
    \<open>distinct_watched ((g(L := take j (g L) @ drop w (g L))) La)\<close>
  if \<open>La\<in>#?\<L>\<close>
  for La i K b'
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
  then show ?thesis
    unfolding correct_watching.simps
    by blast
qed

lemma unit_propagation_inner_loop_wl_loop_alt_def:
  \<open>unit_propagation_inner_loop_wl_loop L S\<^sub>0 = do {
    ASSERT(L \<in># all_lits_st S\<^sub>0);
    let (_ :: nat) = (if get_conflict_wl S\<^sub>0 = None then remaining_nondom_wl 0 L S\<^sub>0 else 0);
    let n = length (watched_by S\<^sub>0 L);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
      (\<lambda>(j, w, S). w < n \<and> get_conflict_wl S = None)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl L j w S
      })
      (0, 0, S\<^sub>0)
  }
  \<close>
  unfolding unit_propagation_inner_loop_wl_loop_def Let_def by auto

definition cut_watch_list :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cut_watch_list j w L =(\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(j \<le> w \<and> j \<le> length (W L) \<and> w \<le> length (W L) \<and> L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
      RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(L := take j (W L) @ drop w (W L)))
    })\<close>

definition unit_propagation_inner_loop_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop L S\<^sub>0;
     ASSERT(j \<le> w \<and> w \<le> length (watched_by S L) \<and> L \<in># all_lits_st S);
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
      correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'} \<rightarrow>
    \<langle>{(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<rangle> nres_rel
    \<close> (is \<open>?fg \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close> is \<open>?fg \<in> ?A \<rightarrow> \<langle>{(T', T). _ \<and> ?P T T'}\<rangle>nres_rel\<close>)
proof -
  {
    fix L :: \<open>'v literal\<close> and S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
    assume
      corr_w: \<open>correct_watching S\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
      SS': \<open>(S, S') \<in> state_wl_l (Some (L, 0))\<close>
    text \<open>To ease the finding the correspondence between the body of the loops, we introduce
      following function:\<close>
    let ?R' = \<open>{((i, j, T'), (T, n)).
        (T', T) \<in> state_wl_l (Some (L, j)) \<and>
        correct_watching_except i j L T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
        j \<le> length (watched_by T' L) \<and>
        length (watched_by S L) = length (watched_by T' L) \<and>
        i \<le> j \<and>
        (get_conflict_wl T' = None \<longrightarrow>
           n = size (filter_mset (\<lambda>(i, _). i \<notin># dom_m (get_clauses_wl T')) (mset (drop j (watched_by T' L))))) \<and>
        (get_conflict_wl T' \<noteq> None \<longrightarrow> n = 0) \<and>
        blits_in_\<L>\<^sub>i\<^sub>n T'}\<close>
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
    have cond: \<open>(j < length (watched_by S L) \<and> get_conflict_wl T' = None) =
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

    have [intro]: \<open>unit_propagation_inner_loop_wl_loop_inv L
         (j, w, T) \<Longrightarrow> L \<in># all_lits_st T\<close> for j w T
       unfolding unit_propagation_inner_loop_wl_loop_inv_def
          unit_propagation_inner_loop_l_inv_def prod.case
       apply normalize_goal+
       apply (drule twl_struct_invs_no_alien_in_trail[of _ \<open>-L\<close>])
       apply (simp_all only: in_all_lits_of_mm_uminus_iff twl_st_wl twl_st_l twl_st
         all_lits_def multiset.map_comp comp_def clause_twl_clause_of ac_simps
         in_all_lits_uminus_iff)
      done
    have unit_propagation_inner_loop_l_alt_def: \<open>unit_propagation_inner_loop_l L S' = do {
        ASSERT(L \<in># all_lits_of_st_l S');
        n \<leftarrow> SPEC (\<lambda>_::nat. True);
        (S, n) \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_l_inv L\<^esup>
              (\<lambda>(S, n). clauses_to_update_l S \<noteq> {#} \<or> 0 < n)
              (unit_propagation_inner_loop_body_l_with_skip L) (S', n);
        RETURN S}\<close> for L S'
      unfolding unit_propagation_inner_loop_l_def by auto
    have unit_propagation_inner_loop_wl_alt_def: \<open>unit_propagation_inner_loop_wl L S = do {
      ASSERT(L \<in># all_lits_st S);
      let (n::nat) = (if get_conflict_wl S = None then remaining_nondom_wl 0 L S else 0);
      (j, w, S) \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_inv L\<^esup>
         (\<lambda>(j, w, T). w < length (watched_by S L)  \<and> get_conflict_wl T = None)
         (\<lambda>(j, x, y). unit_propagation_inner_loop_body_wl L j x y) (0, 0, S);
      ASSERT (j \<le> w \<and> w \<le> length (watched_by S L) \<and> L \<in># all_lits_st S);
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
            R = \<open>{((i, j, T'), (T, n)). ((i, j, T'), (T, n)) \<in> ?R' \<and> i \<le> j \<and>
                length (watched_by S L) =  length (watched_by T' L) \<and>
               (j \<ge> length (watched_by T' L) \<or> get_conflict_wl T' \<noteq> None) \<and>
               unit_propagation_inner_loop_wl_loop_inv L (i, j, T')}\<close>]
          remaining)
      subgoal using SS' by (auto simp: all_lits_def ac_simps)
      subgoal using corr_w SS' by (auto simp: correct_watching_correct_watching_except00)
      subgoal by (rule inv)
      subgoal by (rule cond)
      subgoal for n i'w'T' Tn i' w'T' w' T'
        apply (cases Tn)
        apply (rule order_trans)
        apply (rule unit_propagation_inner_loop_body_wl_spec[of _ \<open>fst Tn\<close>])
        apply (simp only: prod.case in_pair_collect_simp)
        apply normalize_goal+
        apply (auto simp del: twl_st_of_wl.simps intro!: conc_fun_R_mono)
        done
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal for n i'w'T' Tn i' w'T' j L' w' T'
        apply (cases T')
        by (auto simp: state_wl_l_def cut_watch_list_def all_lits_def intro: blits_in_\<L>\<^sub>i\<^sub>n_cut_watch
          dest!: correct_watching_except_correct_watching_cut_watch)
      done
  }
  note H = this

  show ?thesis
    unfolding fref_param1
    apply (intro frefI nres_relI)
    by (auto simp: intro!: H)
qed


subsection \<open>Outer loop\<close>

definition select_and_remove_from_literals_to_update_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> 'v literal) nres\<close> where
  \<open>select_and_remove_from_literals_to_update_wl S = SPEC(\<lambda>(S', L). L \<in># literals_to_update_wl S \<and>
     S' = set_literals_to_update_wl (literals_to_update_wl S - {#L#}) S)\<close>

definition unit_propagation_outer_loop_wl_inv where
  \<open>unit_propagation_outer_loop_wl_inv S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
      correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S \<and>
      unit_propagation_outer_loop_l_inv S')\<close>

definition unit_propagation_outer_loop_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_inv\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># all_lits_st S');
        unit_propagation_inner_loop_wl L S'
      })
      (S\<^sub>0 :: 'v twl_st_wl)
\<close>

lemma blits_in_\<L>\<^sub>i\<^sub>n_simps[simp]: \<open>blits_in_\<L>\<^sub>i\<^sub>n (set_literals_to_update_wl C  xa) \<longleftrightarrow> blits_in_\<L>\<^sub>i\<^sub>n xa\<close>
  by (cases xa; auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma unit_propagation_outer_loop_wl_spec:
  \<open>(unit_propagation_outer_loop_wl, unit_propagation_outer_loop_l)
 \<in> {(T'::'v twl_st_wl, T).
       (T', T) \<in> state_wl_l None \<and>
       correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'} \<rightarrow>\<^sub>f
    \<langle>{(T', T).
       (T', T) \<in> state_wl_l None \<and>
       correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<rangle>nres_rel\<close>
  (is \<open>?u \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have inv: \<open>unit_propagation_outer_loop_wl_inv T'\<close>
  if
    \<open>(T', T) \<in> {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<close> and
    \<open>unit_propagation_outer_loop_l_inv T\<close>
    for T T'
  unfolding unit_propagation_outer_loop_wl_inv_def
  apply (rule exI[of _ T])
  using that by auto

  have select_and_remove_from_literals_to_update_wl:
   \<open>select_and_remove_from_literals_to_update_wl S' \<le>
     \<Down> {((T', L'), (T, L)). L = L' \<and> (T', T) \<in> state_wl_l (Some (L, 0)) \<and>
         T' = set_literals_to_update_wl (literals_to_update_wl S' - {#L#}) S' \<and> L \<in># literals_to_update_wl S' \<and>
         L \<in># all_lits_st S'
       }
       (select_and_remove_from_literals_to_update S)\<close>
    if S: \<open>(S', S) \<in> state_wl_l None\<close> and \<open>get_conflict_wl S' = None\<close> and
      corr_w: \<open>correct_watching S'\<close> and
      inv_l: \<open>unit_propagation_outer_loop_l_inv S\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
  proof -
    obtain M N D NE UE NEk UEk NS US N0 U0 W Q where
      S': \<open>S' = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
      by (cases S') auto
    obtain R where
      S_R: \<open>(S, R) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs R\<close>
      using inv_l unfolding unit_propagation_outer_loop_l_inv_def by blast
    have [simp]: (* \<open>trail (state\<^sub>W_of R) = convert_lits_l N M\<close> *)
      \<open>init_clss (state\<^sub>W_of R) = mset `# (init_clss_lf N) + NE + NEk + NS + N0\<close>
      \<open>atm_of ` lits_of_l (get_trail R) = atm_of ` lits_of_l M\<close>
      using S_R S by (auto simp: twl_st S' twl_st_wl simp flip: state\<^sub>W_of_def)
    have
      no_dup_q: \<open>no_duplicate_queued R\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of R)\<close>
      using struct_invs that by (auto simp: twl_struct_invs_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        pcdcl_all_struct_invs_def state\<^sub>W_of_def)
    then have H1: \<open>L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE) + (NEk + UEk) + (NS + US) + (N0 + U0))\<close>
      if LQ: \<open>L \<in># Q\<close> for L
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
           (\<Union>x\<in>set_mset NE. atms_of x) \<union>
           (\<Union>x\<in>set_mset NEk. atms_of x) \<union>
           (\<Union>x\<in>set_mset NS. atms_of x) \<union>
           (\<Union>x\<in>set_mset N0. atms_of x)\<close>
          using that alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
          by (auto simp: S' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
              all_lits_of_mm_def atms_of_ms_def simp flip: state\<^sub>W_of_def)
        then have \<open>atm_of ` lits_of_l M \<subseteq> (\<Union>x\<in>set_mset (init_clss_lf N). atm_of ` set x) \<union>
         (\<Union>x\<in>set_mset NE. atms_of x) \<union>
         (\<Union>x\<in>set_mset NEk. atms_of x) \<union>
         (\<Union>x\<in>set_mset NS. atms_of x) \<union>
         (\<Union>x\<in>set_mset N0. atms_of x)\<close>
        unfolding image_Un[symmetric]
          set_append[symmetric]
          append_take_drop_id
          .
        then have \<open>atm_of ` lits_of_l M \<subseteq> atms_of_mm (mset `# init_clss_lf N + NE + NEk + NS + N0)\<close>
          by (smt UN_Un Un_iff append_take_drop_id atms_of_ms_def atms_of_ms_mset_unfold set_append
              set_image_mset set_mset_mset set_mset_union subset_eq)
      }
      ultimately have \<open>atm_of L \<in> atms_of_mm (mset `# ran_mf N + NE + NEk + NS + N0)\<close>
        using that
        unfolding all_lits_of_mm_union atms_of_ms_union all_clss_lf_ran_m[symmetric]
          image_mset_union set_mset_union
        by auto
      then show ?thesis
        using that by (auto simp: in_all_lits_of_mm_ain_atms_of_iff)
    qed
    have H: \<open>clause_to_update L S = {#i \<in># fst `# mset (W L). i \<in># dom_m N#}\<close>
       \<open>L \<in># all_lits_st ([], N, None, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)\<close>
        if \<open>L \<in># Q\<close> for L
      using corr_w that S H1[OF that] by (auto simp: correct_watching.simps S' clause_to_update_def
        Ball_def ac_simps all_conj_distrib all_lits_st_def all_lits_def
        dest!: multi_member_split)
    show ?thesis
      unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
      apply (rule RES_refine)
      unfolding Bex_def
      by (rule_tac x=\<open>(set_clauses_to_update_l (clause_to_update (snd s) S)
              (set_literals_to_update_l
                (remove1_mset (snd s) (literals_to_update_l S)) S), snd s)\<close> in exI)
         (use that S' S in \<open>auto simp: correct_watching.simps clauses_def state_wl_l_def
          mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state all_lits_of_mm_union
          dest: H1 H\<close>)
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
    subgoal by (auto simp: twl_st_wl ac_simps)
    subgoal by auto
    done
qed


subsection \<open>Decide or Skip\<close>

definition find_unassigned_lit_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> 'v literal option) nres\<close> where
  \<open>find_unassigned_lit_wl = (\<lambda>S.
     SPEC (\<lambda>(T, L). T = S \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit (get_trail_wl S) (the L) \<and>
            the L \<in># all_lits_st S) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit (get_trail_wl S) L' \<and>
            L' \<in># all_lits_st S)))
     )\<close>

definition decide_wl_or_skip_pre where
\<open>decide_wl_or_skip_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
   decide_l_or_skip_pre S' \<and> blits_in_\<L>\<^sub>i\<^sub>n S
  )\<close>

definition decide_lit_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>decide_lit_wl = (\<lambda>L' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
      (Decided L' # M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#- L'#}, W))\<close>


definition decide_wl_or_skip :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>decide_wl_or_skip S = (do {
    ASSERT(decide_wl_or_skip_pre S);
    (S, L) \<leftarrow> find_unassigned_lit_wl S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> RETURN (False, decide_lit_wl L S)
  })
\<close>

lemma decide_wl_or_skip_spec:
  \<open>(decide_wl_or_skip, decide_l_or_skip)
    \<in> {(T':: 'v twl_st_wl, T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
          get_conflict_wl T' = None} \<rightarrow>
        \<langle>{((b', T'), (b, T)). b' = b \<and>
         (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<rangle>nres_rel\<close>
proof -
  have find_unassigned_lit_wl: \<open>find_unassigned_lit_wl S'
    \<le> \<Down> {((T, L), L'). T = S' \<and> L = L'}
        (find_unassigned_lit_l S)\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that
    by (auto simp: find_unassigned_lit_l_def find_unassigned_lit_wl_def
      intro!: RES_refine)

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
          decide_lit_l_def decide_lit_wl_def state_wl_l_def blits_in_\<L>\<^sub>i\<^sub>n_def)
    done
qed


subsection \<open>Skip or Resolve\<close>


definition mop_tl_state_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>mop_tl_state_wl_pre S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> mop_tl_state_l_pre S')\<close>

definition tl_state_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>tl_state_wl = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q).
    (tl M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q))\<close>

definition mop_tl_state_wl :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>mop_tl_state_wl = (\<lambda>S. do {
    ASSERT(mop_tl_state_wl_pre S);
    RETURN(False, tl_state_wl S)})\<close>

definition resolve_cls_wl' :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v clause\<close> where
\<open>resolve_cls_wl' S C L  =
   remove1_mset L (remove1_mset (-L) (the (get_conflict_wl S) \<union># (mset (get_clauses_wl S \<propto> C))))\<close>

definition update_confl_tl_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool \<times> 'v twl_st_wl\<close> where
  \<open>update_confl_tl_wl = (\<lambda>L C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q).
     let D = resolve_cls_wl' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q) C L in
        (False, (tl M, N, Some D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)))\<close>

definition update_confl_tl_wl_pre :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>update_confl_tl_wl_pre L C S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> update_confl_tl_l_pre L C S' \<and>
     correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>

definition mop_update_confl_tl_wl :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>mop_update_confl_tl_wl = (\<lambda>L C S. do {
     ASSERT(update_confl_tl_wl_pre L C S);
     RETURN (update_confl_tl_wl L C S)
  })\<close>

definition mop_hd_trail_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>mop_hd_trail_wl_pre S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> state_wl_l None \<and> mop_hd_trail_l_pre S' \<and>
     correct_watching S)\<close>


definition mop_hd_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v literal \<times> nat) nres\<close> where
  \<open>mop_hd_trail_wl S = do{
     ASSERT(mop_hd_trail_wl_pre S);
     SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail_wl S))
  }\<close>

definition skip_and_resolve_loop_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>skip_and_resolve_loop_wl_inv S\<^sub>0 brk S \<longleftrightarrow>
    (\<exists>S' S'\<^sub>0. (S, S') \<in> state_wl_l None \<and>
      (S\<^sub>0, S'\<^sub>0) \<in> state_wl_l None \<and>
     skip_and_resolve_loop_inv_l S'\<^sub>0 brk S' \<and>
        correct_watching S)\<close>

definition mop_lit_notin_conflict_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>mop_lit_notin_conflict_wl L S = do {
    ASSERT(get_conflict_wl S \<noteq> None \<and> -L \<notin># the (get_conflict_wl S) \<and> L \<in># all_lits_st S);
    RETURN (L \<notin># the (get_conflict_wl S))
  }\<close>

definition mop_maximum_level_removed_wl_pre :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>mop_maximum_level_removed_wl_pre L S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> state_wl_l None \<and> mop_maximum_level_removed_l_pre L S' \<and>
      correct_watching S)\<close>

definition mop_maximum_level_removed_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool nres\<close> where
\<open>mop_maximum_level_removed_wl L S = do {
   ASSERT (mop_maximum_level_removed_wl_pre L S);
   RETURN (get_maximum_level (get_trail_wl S) (remove1_mset (-L) (the (get_conflict_wl S))) =
      count_decided (get_trail_wl S))
}\<close>

definition skip_and_resolve_loop_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>skip_and_resolve_loop_wl S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_wl_inv S\<^sub>0 brk S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          do {
            (L, C) \<leftarrow> mop_hd_trail_wl S;
            b \<leftarrow> mop_lit_notin_conflict_wl (-L) S;
            if b then
              mop_tl_state_wl S
            else do {
              b \<leftarrow> mop_maximum_level_removed_wl L S;
              if b
              then
                mop_update_confl_tl_wl L C S
              else
                do {RETURN (True, S)}
           }
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma tl_state_wl_tl_state_l:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> correct_watching S \<Longrightarrow>  blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow>
    mop_tl_state_wl S \<le> \<Down>(bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S})
      (mop_tl_state_l S')\<close>
  by (cases S) (auto simp: state_wl_l_def tl_state_wl_def tl_state_l_def blits_in_\<L>\<^sub>i\<^sub>n_def
        mop_tl_state_wl_def mop_tl_state_l_def mop_tl_state_wl_pre_def
        assert_bind_spec_conv correct_watching.simps clause_to_update_def
     intro!: ASSERT_refine_right ASSERT_leI)


lemma mop_update_confl_tl_wl_mop_update_confl_tl_l:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> correct_watching S \<Longrightarrow>  blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow>
   ((L, C), (L', C')) \<in> Id \<Longrightarrow>
    mop_update_confl_tl_wl L C S \<le>
     \<Down>(bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S})
      (mop_update_confl_tl_l L' C' S')\<close>
  by (cases S) (auto simp: state_wl_l_def tl_state_wl_def tl_state_l_def blits_in_\<L>\<^sub>i\<^sub>n_def
        mop_update_confl_tl_wl_def mop_update_confl_tl_l_def
        update_confl_tl_wl_def update_confl_tl_l_def resolve_cls_l'_def
        resolve_cls_wl'_def update_confl_tl_wl_pre_def
        assert_bind_spec_conv correct_watching.simps clause_to_update_def
     intro!: ASSERT_refine_right ASSERT_leI)

lemma mop_hd_trail_wl_mop_hd_trail_l:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> correct_watching S \<Longrightarrow>  blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow>
   mop_hd_trail_wl S
    \<le> \<Down> (Id)
        (mop_hd_trail_l S')\<close>
  unfolding mop_hd_trail_wl_def mop_hd_trail_l_def
  apply refine_rcg
  subgoal unfolding mop_hd_trail_wl_pre_def by blast
  subgoal by auto
  done

lemma mop_lit_notin_conflict_wl_mop_lit_notin_conflict_l:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> correct_watching S \<Longrightarrow>  blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow>
   L = L' \<Longrightarrow>
    mop_lit_notin_conflict_wl L S \<le> \<Down>bool_rel (mop_lit_notin_conflict_l L' S')\<close>
  unfolding mop_lit_notin_conflict_wl_def mop_lit_notin_conflict_l_def
  apply refine_rcg
  subgoal by auto
  subgoal by auto
  subgoal unfolding all_lits_def by (auto simp: ac_simps)
  subgoal by auto
  done

lemma mop_maximum_level_removed_wl_mop_maximum_level_removed_l:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> correct_watching S \<Longrightarrow>  blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow>
   L = L' \<Longrightarrow>
    mop_maximum_level_removed_wl L S \<le> \<Down>bool_rel (mop_maximum_level_removed_l L' S')\<close>
  unfolding mop_maximum_level_removed_wl_def mop_maximum_level_removed_l_def
  apply refine_rcg
  subgoal unfolding mop_maximum_level_removed_wl_pre_def by blast
  subgoal by auto
  done


lemma skip_and_resolve_loop_wl_spec:
  \<open>(skip_and_resolve_loop_wl, skip_and_resolve_loop_l)
    \<in> {(T'::'v twl_st_wl, T).
         (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
          0 < count_decided (get_trail_wl T')} \<rightarrow>
      \<langle>{(T', T).
         (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<rangle>nres_rel\<close>
  (is \<open>?s \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have get_conflict_wl: \<open>((False, S'), False, S)
    \<in> Id \<times>\<^sub>r {(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<close>
    (is \<open>_ \<in> ?B\<close>)
    if \<open>(S', S) \<in> state_wl_l None\<close> and \<open>correct_watching S'\<close> and \<open>blits_in_\<L>\<^sub>i\<^sub>n S'\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st_wl\<close>
    using that by (cases S') (auto simp: state_wl_l_def)
  have [simp]: \<open>correct_watching  (tl aa, ca, da, ea, fa, NEk, UEk, NS, US, N0, U0, ha, h) \<longleftrightarrow>
    correct_watching (aa, ca, None, ea, fa, NEk, UEk, NS, US, N0, U0, ha, h)\<close>
    for aa ba ca L da ea fa ha h NS US NEk UEk
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)
  have [simp]: \<open>NO_MATCH None da \<Longrightarrow> correct_watching  (aa, ca, da, ea, fa, NEk, UEk, NS, US, N0, U0, ha, h) \<longleftrightarrow>
    correct_watching (aa, ca, None, ea, fa, NEk, UEk, NS, US, N0, U0, ha, h)\<close>
    for aa ba ca L da ea fa ha h NS US N0 U0
    by (auto simp: correct_watching.simps tl_state_wl_def clause_to_update_def)

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

  show H: \<open>?s \<in> ?A \<rightarrow> \<langle>{(T', T). (T', T) \<in> state_wl_l None \<and> correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<rangle>nres_rel\<close>
    unfolding skip_and_resolve_loop_wl_def skip_and_resolve_loop_l_def
    apply (refine_rcg get_conflict_wl tl_state_wl_tl_state_l
       mop_update_confl_tl_wl_mop_update_confl_tl_l mop_hd_trail_wl_mop_hd_trail_l
       mop_lit_notin_conflict_wl_mop_lit_notin_conflict_l
       mop_maximum_level_removed_wl_mop_maximum_level_removed_l)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule inv)
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: tl_state_wl_tl_state_l)
    subgoal for S' S b'T' bT b' T' by auto
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
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


subsection \<open>Backtrack\<close>

definition find_decomp_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>find_decomp_wl = (\<lambda>L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
    SPEC(\<lambda>S. \<exists>K M2 M1. S = (M1, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<and>
         (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

definition find_lit_of_max_level_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres\<close> where
  \<open>find_lit_of_max_level_wl =  (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) L.
    SPEC(\<lambda>L'. L' \<in># remove1_mset (-L) (the D) \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>


fun extract_shorter_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>extract_shorter_conflict_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) = SPEC(\<lambda>S.
     \<exists>D'. D' \<subseteq># the D \<and> S = (M, N, Some D', NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<and>
     clause `# twl_clause_of `# ran_mf N + NE + NEk + UE + UEk + NS + US \<Turnstile>pm D' \<and> -lit_of (hd M) \<in># D')\<close>

declare extract_shorter_conflict_wl.simps[simp del]
lemmas extract_shorter_conflict_wl_def = extract_shorter_conflict_wl.simps


definition backtrack_wl_inv where
  \<open>backtrack_wl_inv S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> state_wl_l None \<and> backtrack_l_inv S' \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S)
  \<close>

text \<open>Rougly: we get a fresh index that has not yet been used.\<close>
definition get_fresh_index_wl :: \<open>'v clauses_l \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat nres\<close> where
\<open>get_fresh_index_wl N NUE W = SPEC(\<lambda>i. i > 0 \<and> i \<notin># dom_m N \<and>
   (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf N + NUE) . i \<notin> fst ` set (W L)))\<close>

definition (in -) list_of_mset2
  :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v clause \<Rightarrow> 'v clause_l nres\<close>
where
  \<open>list_of_mset2 L L' D =
    SPEC (\<lambda>E. mset E = D \<and> E!0 = L \<and> E!1 = L' \<and> length E \<ge> 2)
\<close>
definition propagate_bt_wl_pre where
  \<open>propagate_bt_wl_pre L L' S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> state_wl_l None \<and> propagate_bt_l_pre L L' S')\<close>

definition propagate_bt_wl :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_bt_wl = (\<lambda>L L' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT(propagate_bt_wl_pre L L' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    i \<leftarrow> get_fresh_index_wl N (NE + UE + NEk + UEk + NS + US + N0 + U0) W;
    let b = (length ([-L, L'] @ (remove1 (-L) (remove1 L' D''))) = 2);
    M \<leftarrow> cons_trail_propagate_l (-L) i M;
    RETURN (M,
        fmupd i ([-L, L'] @ (remove1 (-L) (remove1 L' D'')), False) N,
          None, NE, UE, NEk, UEk, NS, US, N0, U0, {#L#}, W(-L:= W (-L) @ [(i, L', b)], L':= W L' @ [(i, -L, b)]))
      })\<close>

definition propagate_unit_bt_wl_pre where
  \<open>propagate_unit_bt_wl_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> propagate_unit_bt_l_pre L S')\<close>

definition propagate_unit_bt_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_unit_bt_wl = (\<lambda>L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT(L \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    ASSERT(propagate_unit_bt_wl_pre L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    M \<leftarrow> cons_trail_propagate_l (-L) 0 M;
    RETURN (M, N, None, NE, UE, NEk, add_mset (the D) UEk, NS, US, N0, U0, {#L#}, W)})\<close>

definition mop_lit_hd_trail_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>mop_lit_hd_trail_wl_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> mop_lit_hd_trail_l_pre S')\<close>

definition mop_lit_hd_trail_wl :: \<open>'v twl_st_wl \<Rightarrow> ('v literal) nres\<close> where
  \<open>mop_lit_hd_trail_wl S = do{
     ASSERT(mop_lit_hd_trail_wl_pre S);
     SPEC(\<lambda>L. L = lit_of (hd (get_trail_wl S)))
  }\<close>

definition backtrack_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>backtrack_wl S =
    do {
      ASSERT(backtrack_wl_inv S);
      L \<leftarrow> mop_lit_hd_trail_wl S;
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propagate_bt_wl L L' S
      }
      else do {
        propagate_unit_bt_wl L S
     }
  }\<close>

lemma all_lits_st_learn_simps:
  assumes
    L1: \<open>L1 \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    L2: \<open>L2 \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    UW: \<open>set_mset (all_lits_of_m (mset UW)) \<subseteq>
       set_mset (all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))\<close> and
    i_dom: \<open>i \<notin># dom_m N\<close>
  shows
    \<open>set_mset (all_lits_st (M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)) =
     set_mset (all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))\<close>
  using assms
  by (auto 5 3 simp: all_lits_st_def all_lits_def all_lits_of_mm_union all_lits_of_mm_add_mset
        ran_m_mapsto_upd_notin all_lits_of_m_add_mset in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff atm_of_eq_atm_of)

lemma correct_watching_learn2:
  assumes
    L1: \<open>L1 \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    L2: \<open>L2 \<in># all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> and
    UW: \<open>set_mset (all_lits_of_m (mset UW)) \<subseteq>
       set_mset (all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))\<close> and
    i_dom: \<open>i \<notin># dom_m N\<close> and
    fresh: \<open>\<And>L. L\<in>#all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<Longrightarrow> i \<notin> fst ` set (W L)\<close> and
    [iff]: \<open>L1 \<noteq> L2\<close> and
    b: \<open>b \<longleftrightarrow> length (L1 # L2 # UW) = 2\<close>
  shows
  \<open>correct_watching (K # M, fmupd i (L1 # L2 # UW, b') N,
    D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W (L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) \<longleftrightarrow>
  correct_watching (M, N, D', NE, UE, NEk, UEk, NS, US, N0, U0, Q', W)\<close>
  (is \<open>?l \<longleftrightarrow> ?c\<close> is \<open>correct_watching (_, ?N, _) = _\<close>)
proof -
  let ?S = \<open>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  let ?T = \<open>(M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)\<close>
  let ?\<L> = \<open>all_lits_st ?S\<close>
  have \<L>_mono: \<open>set_mset ?\<L> = set_mset (all_lits_st ?T)\<close>
    using assms(1-3) i_dom
    by (auto 5 3 simp: all_lits_st_def all_lits_def all_lits_of_mm_union all_lits_of_mm_add_mset
        ran_m_mapsto_upd_notin all_lits_of_m_add_mset in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff atm_of_eq_atm_of)

  have \<L>\<T>: \<open>set_mset ?\<L> = set_mset (all_lits_st (K # M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE,
       NEk, UEk, NS, US, N0, U0, Q, W (L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])))\<close>
      using \<L>_mono by (auto simp: all_lits_st_def)

  have [iff]: \<open>L2 \<noteq> L1\<close>
    using \<open>L1 \<noteq> L2\<close> by (subst eq_commute)
  have [simp]: \<open>clause_to_update L1 (M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) =
         add_mset i (clause_to_update L1 (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close> for L2 UW
    using i_dom
    by (auto simp: clause_to_update_def intro: filter_mset_cong)
  have [simp]: \<open>clause_to_update L2 (M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) =
         add_mset i (clause_to_update L2 (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close> for L1 UW
    using i_dom
    by (auto simp: clause_to_update_def intro: filter_mset_cong)
  have [simp]: \<open>x \<noteq> L1 \<Longrightarrow> x \<noteq> L2 \<Longrightarrow>
   clause_to_update x (M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) =
        clause_to_update x (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close> for x UW
    using i_dom
    by (auto simp: clause_to_update_def intro: filter_mset_cong)

  have H':
     \<open>{#ia \<in># fst `# mset (W x). ia = i \<or> ia \<in># dom_m N#} =  {#ia \<in># fst `# mset (W x). ia \<in># dom_m N#}\<close>
     if \<open>x \<in># ?\<L>\<close> for x
    using i_dom fresh[of x] that
    by (auto simp: clause_to_update_def intro!: filter_mset_cong)
  have [simp]:
    \<open>clause_to_update L1 (K # M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}) =
       clause_to_update L1 (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
    for L1 N D NE UE M K NS US
    by (auto simp: clause_to_update_def)

  show ?thesis
  proof (rule iffI)
    assume corr: ?l
    have
      H: \<open>\<And>L ia K' b''. (L\<in>#?\<L> \<Longrightarrow>
      distinct_watched ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) L) \<and>
      ((ia, K', b'')\<in>#mset ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) L) \<longrightarrow>
          ia \<in># dom_m (fmupd i (L1 # L2 # UW, b') N) \<longrightarrow>
          K' \<in> set (fmupd i (L1 # L2 # UW, b') N \<propto> ia) \<and> K' \<noteq> L \<and>
          correctly_marked_as_binary (fmupd i (L1 # L2 # UW, b') N) (ia, K', b'') ) \<and>
      ((ia, K', b'')\<in>#mset ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) L) \<longrightarrow>
          b'' \<longrightarrow> ia \<in># dom_m (fmupd i (L1 # L2 # UW, b') N)) \<and>
      {#ia \<in># fst `#
              mset ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) L).
       ia \<in># dom_m (fmupd i (L1 # L2 # UW, b') N)#} =
      clause_to_update L
       (K # M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>
      using corr unfolding correct_watching.simps \<L>\<T>
      by fast+

    have \<open>x \<in># ?\<L> \<Longrightarrow>
          distinct_watched (W x) \<and>
         (xa \<in># mset (W x) \<longrightarrow> (((case xa of (i, K, b'') \<Rightarrow> i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> x \<and>
           correctly_marked_as_binary N (i, K, b'')) \<and>
           (case xa of (i, K, b'') \<Rightarrow> b'' \<longrightarrow> i \<in># dom_m N)))) \<and>
         {#i \<in># fst `# mset (W x). i \<in># dom_m N#} = clause_to_update x (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
      for x xa
      supply correctly_marked_as_binary.simps[simp]
      using H[of x \<open>fst xa\<close> \<open>fst (snd xa)\<close> \<open>snd (snd xa)\<close>] fresh[of x] i_dom
      apply (cases \<open>x = L1\<close>; cases \<open>x = L2\<close>)
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        by (cases xa) (force simp add: H' split: if_splits)
      subgoal
        by (cases xa)
          (force simp add: H' split: if_splits)
      subgoal
        by (cases xa)
          (force simp add: H' split: if_splits)
      done
    then show ?c
      unfolding correct_watching.simps Ball_def
      by (auto 5 5 simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset
          all_conj_distrib all_lits_of_mm_union clause_to_update_def
         dest: multi_member_split)
  next
    assume corr: ?c
    have \<open>?\<L> = all_lits_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q', W)\<close>
      by auto
    then have
      H: \<open>\<And>L ia K' b''. (L\<in># ?\<L> \<Longrightarrow>
      distinct_watched (W L) \<and>
      ((ia, K', b'')\<in>#mset (W L) \<longrightarrow>
          ia \<in># dom_m N \<longrightarrow>
          K' \<in> set (N \<propto> ia) \<and> K' \<noteq> L \<and> correctly_marked_as_binary N (ia, K', b'')) \<and>
      ((ia, K', b'')\<in>#mset (W L) \<longrightarrow> b'' \<longrightarrow> ia \<in># dom_m N) \<and>
      {#ia \<in># fst `# mset (W L). ia \<in># dom_m N#} = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>
      using corr unfolding correct_watching.simps clause_to_update_def get_clauses_l.simps
      by auto
    have \<open>x \<in># ?\<L> \<longrightarrow>
         distinct_watched ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) x) \<and>
         (xa \<in># mset ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) x) \<longrightarrow>
               (case xa of (ia, K, b'') \<Rightarrow> ia \<in># dom_m (fmupd i (L1 # L2 # UW, b') N) \<longrightarrow>
                 K \<in> set (fmupd i (L1 # L2 # UW, b') N \<propto> ia) \<and> K \<noteq> x \<and>
                    correctly_marked_as_binary (fmupd i (L1 # L2 # UW, b') N) (ia, K, b''))) \<and>
         (xa \<in># mset ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) x) \<longrightarrow>
               (case xa of (ia, K, b'') \<Rightarrow> b'' \<longrightarrow> ia \<in># dom_m (fmupd i (L1 # L2 # UW, b') N))) \<and>
         {#ia \<in># fst `# mset ((W(L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) x). ia \<in># dom_m (fmupd i (L1 # L2 # UW, b') N)#} =
         clause_to_update x (K # M, fmupd i (L1 # L2 # UW, b') N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#})\<close>
      for x :: \<open>'a literal\<close> and xa
      supply correctly_marked_as_binary.simps[simp]
      using H[of x \<open>fst xa\<close> \<open>fst (snd xa)\<close> \<open>snd (snd xa)\<close>] fresh[of x] i_dom b
      apply (cases \<open>x = L1\<close>; cases \<open>x = L2\<close>)
      subgoal
        by (cases xa)
          (auto dest!: multi_member_split simp: H')
      subgoal
        using \<L>_mono
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
    using \<L>_mono
    unfolding correct_watching.simps Ball_def
    by auto
  qed
qed

lemma all_lits_fmupd_new[simp]:
   \<open>i \<notin># dom_m NU \<Longrightarrow> all_lits (fmupd i C NU) NUE = all_lits_of_m (mset (fst C)) + all_lits NU NUE\<close>
  unfolding all_lits_def by (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset)



lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch''':
  assumes
    K': \<open>K' \<in># all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
      \<open>L' \<in># all_lits_st (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close> and
    w:\<open> blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f, g (K := (g K) @[(i, K', b')], L := g L @ [(i', L', b'')]))\<close>
  using assms
  unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
  by (auto split: if_splits elim!: in_set_upd_cases)

lemma backtrack_wl_spec:
  \<open>(backtrack_wl, backtrack_l)
    \<in> {(T'::'v twl_st_wl, T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
          get_conflict_wl T' \<noteq> None \<and>
          get_conflict_wl T' \<noteq> Some {#}} \<rightarrow>
        \<langle>{(T', T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<rangle>nres_rel\<close>
  (is \<open>?bt \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have H: \<open>A \<Turnstile>p C \<Longrightarrow> \<not>B \<Turnstile>p C \<Longrightarrow> A \<subseteq> B \<Longrightarrow> False\<close> for A B C
    by (meson true_clss_cls_subset)
  have extract_shorter_conflict_wl: \<open>extract_shorter_conflict_wl S'
    \<le> \<Down> {(U'::'v twl_st_wl, U).
          (U', U) \<in> state_wl_l None \<and> equality_except_conflict_wl U' S' \<and>
          the (get_conflict_wl U') \<subseteq># the (get_conflict_wl S') \<and>
          get_conflict_wl U' \<noteq> None \<and> correct_watching U' \<and> blits_in_\<L>\<^sub>i\<^sub>n U'}
        (extract_shorter_conflict_l S)\<close>
    (is \<open>_ \<le> \<Down> ?extract _\<close>)
    if  \<open>(S', S) \<in> ?A\<close>
    for S' S
    apply (cases S'; cases S)
    apply clarify
    unfolding extract_shorter_conflict_wl_def extract_shorter_conflict_l_def
    apply (refine_rcg, rule RES_refine)
    using that
    by  (auto simp: extract_shorter_conflict_wl_def extract_shorter_conflict_l_def
        mset_take_mset_drop_mset' state_wl_l_def correct_watching.simps Un_assoc
      clause_to_update_def blits_in_\<L>\<^sub>i\<^sub>n_def dest!: multi_member_split
      dest: H)
  have find_decomp_wl: \<open>find_decomp_wl L T'
    \<le> \<Down> {(U'::'v twl_st_wl, U).
          (U', U) \<in> state_wl_l None \<and> equality_except_trail_wl U' T' \<and>
          (\<exists>M. get_trail_wl T' = M @ get_trail_wl U') \<and>
          correct_watching U' \<and> blits_in_\<L>\<^sub>i\<^sub>n U'} (find_decomp L' T)\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    if \<open>(S', S) \<in> ?A\<close> \<open>L = L'\<close> \<open>(T', T) \<in> ?extract S'\<close>
    for S' S T T' L L'
    using that
    apply (cases T; cases T')
    apply clarify
    unfolding find_decomp_wl_def find_decomp_def prod.case
    apply (rule RES_refine)
    apply (auto 5 5 simp add: state_wl_l_def find_decomp_wl_def find_decomp_def correct_watching.simps
        clause_to_update_def blits_in_\<L>\<^sub>i\<^sub>n_def dest!: multi_member_split)
    done

  have find_lit_of_max_level_wl: \<open>find_lit_of_max_level_wl T' LLK'
    \<le> \<Down> {(L', L). L = L' \<and> L' \<in># the (get_conflict_wl T') \<and> L' \<in># the (get_conflict_wl T') - {#-LLK'#}}
         (find_lit_of_max_level_l T L)\<close>
    (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if \<open>L = LLK'\<close> \<open>(T', T) \<in> ?find S'\<close>
    for S' S T T' L LLK'
    using that
    apply (cases T; cases T'; cases S')
    apply clarify
    unfolding find_lit_of_max_level_wl_def find_lit_of_max_level_l_def prod.case
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

  have [refine]: \<open>(S, S') \<in> {(T', T).
        (T', T) \<in> state_wl_l None \<and>
        correct_watching T' \<and>
        blits_in_\<L>\<^sub>i\<^sub>n T' \<and>
        get_conflict_wl T' \<noteq> None \<and>
        get_conflict_wl T' \<noteq> Some {#}} \<Longrightarrow>
    mop_lit_hd_trail_wl S \<le> \<Down>Id (mop_lit_hd_trail_l S')\<close> for S S'
    unfolding mop_lit_hd_trail_wl_def mop_lit_hd_trail_l_def
    apply refine_rcg
    subgoal unfolding mop_lit_hd_trail_wl_pre_def
      by blast
    subgoal by auto
    done

  have id: \<open>(x, x') \<in> Id \<Longrightarrow> f x \<le> \<Down>Id (f x')\<close> for x x' f
    by auto

  have id3: \<open>((x, y, z), (x', y', z')) \<in> Id \<Longrightarrow> f x y z \<le> \<Down>Id (f x' y' z')\<close> for x x' f y y' z z'
    by auto


  have cons_trail_propagate_l: \<open>cons_trail_propagate_l L i M0
     \<le> \<Down>{(M, M'). M = M' \<and> M' = Propagated L i # M0}
         (cons_trail_propagate_l L' i' M')\<close>
    if \<open>L = L'\<close> \<open>i = i'\<close> \<open>M0 = M'\<close> for L i L' i' M' M0
    using that unfolding cons_trail_propagate_l_def
    by (auto intro!: ASSERT_refine_right)

  have fresh: \<open>get_fresh_index_wl N (NE + UE + NEk + UEk + NS + US + N0 + U0) W \<le>
    \<Down> {(i, i'). i = i' \<and> i \<notin># dom_m N \<and>
         (\<forall>L \<in># all_lits_st (x1, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, x1e, x2e). i \<notin> fst ` set (W L))}
       (get_fresh_index N')\<close>
    if \<open>N = N'\<close> \<open>propagate_bt_wl_pre L L' (x1, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, x1e, x2e)\<close>
    for N N' NUE W NE UE N0 U0 x1e x2e NS US x1 D L L' NEk UEk
    unfolding that get_fresh_index_def get_fresh_index_wl_def all_lits_def all_lits_st_def
    by (auto intro: RES_refine simp: ac_simps)

  have blit: \<open>i \<notin># dom_m x1a \<Longrightarrow>
   set_mset (all_lits_of_m (mset C)) \<subseteq> set_mset (all_lits_st (x1, x1a, Some xd, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)) \<Longrightarrow>
     blits_in_\<L>\<^sub>i\<^sub>n
        (x1, x1a, Some xd, x1c, x1d, NEk, UEk, NS, US, N0, U0,  x1e, x2e) \<Longrightarrow>
       blits_in_\<L>\<^sub>i\<^sub>n
        (x1,
         fmupd i (C, b)  x1a,
         None, x1c, x1d, NEk, UEk, NS, US, N0, U0, {#}, x2e)\<close> for x x1a x1 xd x1d x1c x1e x2e i C b NS US N0 U0 NEk UEk
    by (auto simp:  blits_in_\<L>\<^sub>i\<^sub>n_def dest!: multi_member_split simp: all_lits_st_def)
  have [simp]: \<open>mset (unwatched_l (x)) + mset (watched_l (x)) = mset x\<close> for x
    by (metis add.commute mset_take_mset_drop_mset')

  have propagate_bt_wl: \<open>(Sb, Sc)
    \<in> {(U', U).
        (U', U) \<in> state_wl_l None \<and>
        equality_except_trail_wl U' S \<and>
        (\<exists>M. get_trail_wl S = M @ get_trail_wl U')  \<and>
          correct_watching U' \<and> blits_in_\<L>\<^sub>i\<^sub>n U'} \<Longrightarrow>
    (L, La) \<in> Id \<Longrightarrow>
    (L', L'a)
    \<in> {(L', La).
        La = L' \<and>
        L' \<in># the (get_conflict_wl Sb) \<and>
        L' \<in># remove1_mset (- L)
                (the (get_conflict_wl Sb))} \<Longrightarrow>
    propagate_bt_wl L L' Sb
    \<le> \<Down> {(T', T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}
        (propagate_bt_l La L'a Sc)\<close> for a a' L La S Sa Sb Sc L' L'a
    unfolding propagate_bt_wl_def propagate_bt_l_def Let_def list_of_mset2_def list_of_mset_def
    apply (cases Sc; hypsubst)
    unfolding prod.case
    apply (refine_rcg fresh)
    subgoal unfolding propagate_bt_wl_pre_def by fast
    subgoal by (auto simp: propagate_bt_wl_pre_def state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    apply assumption
    apply (rule cons_trail_propagate_l)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal
      unfolding propagate_bt_l_pre_def propagate_bt_pre_def
      apply normalize_goal+
      apply (simp add: eq_commute[of _ \<open>(_, _)\<close>])
      apply (auto simp: state_wl_l_def)
      apply (auto 5 3 simp: ran_m_mapsto_upd_notin mset_take_mset_drop_mset'
         uminus_lit_swap blits_in_\<L>\<^sub>i\<^sub>n_propagate all_lits_of_m_add_mset
        state_wl_l_def twl_st_l_def
        dest: all_lits_of_m_diffD
        simp flip: image_mset_union
        intro!: blit blits_in_\<L>\<^sub>i\<^sub>n_keep_watch''' correct_watching_learn2[THEN iffD2]
        all_lits_st_learn_simps[THEN arg_cong[of _ _ \<open> \<lambda>x. _ \<in> x\<close>], THEN iffD2])
      done
    done

  have correct_watching_unit: \<open>La \<in># all_lits_st (x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<Longrightarrow>
        correct_watching (x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<Longrightarrow>
          correct_watching
           (Propagated (- La) 0 # x1, x1a, None, x1c,
           x1d, NEk, add_mset {#-La#} UEk, NS, US, N0, U0, {#La#}, x2e)\<close>
     \<open>La \<in># all_lits_st (x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<Longrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n
        (x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<Longrightarrow>
       blits_in_\<L>\<^sub>i\<^sub>n
        (Propagated (- La) 0 # x1, x1a, None, x1c, x1d, NEk, add_mset {#-La#} UEk, NS, US, N0, U0, {#La#},
         x2e)\<close>
     for a b c d e f g x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
       M Ma La NS US N0 U0 NEk UEk
     unfolding all_lits_st_def all_lits_def
    apply (subst (asm) in_all_lits_of_mm_uminus_iff[symmetric])
    apply (auto simp: correct_watching.simps all_lits_of_mm_add_mset
      all_lits_of_m_add_mset clause_to_update_def blits_in_\<L>\<^sub>i\<^sub>n_def
      all_lits_st_def all_lits_def
      dest: multi_member_split)
    apply (auto simp: correct_watching.simps all_lits_of_mm_add_mset all_lits_def
        all_lits_of_m_add_mset clause_to_update_def in_all_lits_of_mm_uminus_iff ac_simps
      dest: multi_member_split)
    done

  have propagate_unit_bt_wl: \<open>(Sb, Sc)
    \<in> {(U', U).
        (U', U) \<in> state_wl_l None \<and>
        equality_except_trail_wl U' S \<and>
        (\<exists>M. get_trail_wl S = M @ get_trail_wl U')  \<and>
          correct_watching U' \<and> blits_in_\<L>\<^sub>i\<^sub>n U'} \<Longrightarrow>
    (L, La) \<in> Id \<Longrightarrow>
    propagate_unit_bt_wl L Sb
    \<le> \<Down> {(T', T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}
        (propagate_unit_bt_l La Sc)\<close> for a a' L La S Sa Sb Sc L' L'a
    unfolding propagate_unit_bt_wl_def propagate_unit_bt_l_def Let_def list_of_mset_def
    apply (cases Sc; hypsubst)
    unfolding prod.case
    apply (refine_rcg fresh)
    subgoal unfolding in_pair_collect_simp by normalize_goal+ (simp add: eq_commute[of _ \<open>(_, _)\<close>])
    subgoal using propagate_unit_bt_wl_pre_def by blast
    apply (rule cons_trail_propagate_l)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal for a b c d e f g x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
       M Ma
      unfolding propagate_unit_bt_l_pre_def propagate_unit_bt_pre_def
      by normalize_goal+
        (auto simp: all_lits_def ran_m_mapsto_upd_notin all_lits_of_mm_add_mset state_wl_l_def
          twl_st_l_def all_lits_of_m_add_mset mset_take_mset_drop_mset' in_all_lits_of_mm_uminus_iff
          ac_simps
        simp flip: image_mset_union intro!: blit correct_watching_unit dest!: all_lits_of_m_diffD)
    done

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


subsection \<open>Backtrack, Skip, Resolve or Decide\<close>

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

lemma [simp]: \<open>blits_in_\<L>\<^sub>i\<^sub>n (decide_lit_wl L S) \<longleftrightarrow> blits_in_\<L>\<^sub>i\<^sub>n S\<close>
  by (cases S) (auto simp: decide_lit_wl_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma cdcl_twl_o_prog_wl_spec:
  \<open>(cdcl_twl_o_prog_wl, cdcl_twl_o_prog_l) \<in> {(S::'v twl_st_wl, S'::'v twl_st_l).
     (S, S') \<in> state_wl_l None \<and>
        correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     (T, T') \<in> state_wl_l None \<and>
     brk = brk' \<and>
     correct_watching T \<and> blits_in_\<L>\<^sub>i\<^sub>n T}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -

  have [iff]: \<open>correct_watching (decide_lit_wl L S) \<longleftrightarrow> correct_watching S\<close> for L S
    by (cases S; auto simp: decide_lit_wl_def correct_watching.simps clause_to_update_def)
  have [iff]: \<open>(decide_lit_wl L S, decide_lit_l L S') \<in> state_wl_l None\<close>
    if \<open>(S, S') \<in> state_wl_l None\<close>
    for L S S'
    using that by (cases S; auto simp: decide_lit_wl_def decide_lit_l_def state_wl_l_def)
  have option_id: \<open>x = x' \<Longrightarrow> (x,x') \<in> \<langle>Id\<rangle>option_rel\<close> for x x' by auto
  have damn_you_are_stupid_isabelle: \<open>(a, a')
       \<in> {(S, S').
          (S, S') \<in> state_wl_l None \<and>
          correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<Longrightarrow>
       get_conflict_l a' = None \<Longrightarrow>
       (a, a')
       \<in> {(T', T).
          (T', T) \<in> state_wl_l None \<and>
          correct_watching T' \<and>
          blits_in_\<L>\<^sub>i\<^sub>n T' \<and> get_conflict_wl T' = None}\<close> for a a'
   by auto
  show cdcl_o: \<open>?o \<in> ?A \<rightarrow>\<^sub>f
   \<langle>{((brk::bool, T::'v twl_st_wl), brk'::bool, T'::'v twl_st_l).
     (T, T') \<in> state_wl_l None \<and>
     brk = brk' \<and>
     correct_watching T \<and> blits_in_\<L>\<^sub>i\<^sub>n T}\<rangle>nres_rel\<close>
    unfolding cdcl_twl_o_prog_wl_def cdcl_twl_o_prog_l_def
      fref_param1[symmetric]
    apply (refine_vcg skip_and_resolve_loop_wl_spec["to_\<Down>"] backtrack_wl_spec["to_\<Down>"]
      decide_wl_or_skip_spec["to_\<Down>", THEN order_trans]
      option_id)
    subgoal unfolding cdcl_twl_o_prog_wl_pre_def by blast
    subgoal by auto
    apply (rule damn_you_are_stupid_isabelle; assumption)
    subgoal by (auto intro!: conc_fun_R_mono)
    subgoal unfolding decide_wl_or_skip_pre_def by auto
    subgoal by auto
    subgoal by (auto simp: )
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


subsection \<open>Full Strategy\<close>

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
       correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>
    \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S'), False, S) \<in> {((brk', T'), (brk, T)). (T', T) \<in> state_wl_l None \<and> brk' = brk \<and>
       correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto

  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_def cdcl_twl_stgy_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
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
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>
    \<langle>{(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((False, S'), False, S) \<in> {((brk', T'), (brk, T)). (T', T) \<in> state_wl_l None \<and> brk' = brk \<and>
       correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close>
    using that by auto
    thm unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_def cdcl_twl_stgy_prog_l_def
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
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
    (\<exists>T. (S, T) \<in> state_wl_l None \<and> cdcl_twl_stgy_prog_l_pre T U \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>

lemma cdcl_twl_stgy_prog_wl_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_norestart_run S')\<close>
proof -
  obtain T where T: \<open>(S, T) \<in> state_wl_l None\<close> \<open>cdcl_twl_stgy_prog_l_pre T S'\<close> \<open>correct_watching S\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close>
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
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
    \<langle>{(S::'v twl_st_wl, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((b', False, S'), b, False, S) \<in> {((b', brk', T'), (b, brk, T)).
      (T', T) \<in> state_wl_l None \<and> brk' = brk \<and> b' = b \<and>
       correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close> and
       \<open>(b', b) \<in> bool_rel\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close> and b' b :: bool
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_prog_break_wl_def cdcl_twl_stgy_prog_break_l_def fref_param1[symmetric]
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down]
      cdcl_twl_stgy_prog_wl_spec'[unfolded fref_param1, THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
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
       correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
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
    \<open>cdcl_twl_stgy_prog_break_wl S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_norestart_run S')\<close>
proof -
  obtain T where T: \<open>(S, T) \<in> state_wl_l None\<close> \<open>cdcl_twl_stgy_prog_l_pre T S'\<close> \<open>correct_watching S\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close>
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


definition cdcl_twl_stgy_prog_early_wl :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close> where
  \<open>cdcl_twl_stgy_prog_early_wl S\<^sub>0 =
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
    RETURN (brk, T)
  }\<close>

theorem cdcl_twl_stgy_prog_early_wl_spec':
  \<open>(cdcl_twl_stgy_prog_early_wl, cdcl_twl_stgy_prog_early_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r {(S::'v twl_st_wl, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H: \<open>((b', False, S'), b, False, S) \<in> {((b', brk', T'), (b, brk, T)).
      (T', T) \<in> state_wl_l None \<and> brk' = brk \<and> b' = b \<and>
       correct_watching T' \<and> blits_in_\<L>\<^sub>i\<^sub>n T'}\<close>
    if \<open>(S', S) \<in> state_wl_l None\<close> and
       \<open>correct_watching S'\<close> and
       \<open>(b', b) \<in> bool_rel\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S'\<close>
    for S' :: \<open>'v twl_st_wl\<close> and S :: \<open>'v twl_st_l\<close> and b' b :: bool
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_prog_early_wl_def cdcl_twl_stgy_prog_early_l_def fref_param1[symmetric]
    apply (refine_rcg H unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down]
      cdcl_twl_stgy_prog_wl_spec'[unfolded fref_param1, THEN fref_to_Down])
    subgoal for S' S by (cases S') auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_prog_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    subgoal for S' S brk'T' brkT brk' T' by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    done
qed


theorem cdcl_twl_stgy_prog_early_wl_spec:
  \<open>(cdcl_twl_stgy_prog_early_wl, cdcl_twl_stgy_prog_early_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and>
       correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_prog_early_wl_spec'
  apply -
  apply (rule mem_set_trans)
  prefer 2 apply assumption
  apply (match_fun_rel, solves simp)
  apply (match_fun_rel; solves auto)
  done

lemma cdcl_twl_stgy_prog_early_wl_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_early_wl S \<le> \<Down> (bool_rel \<times>\<^sub>r (state_wl_l None O twl_st_l None)) (partial_conclusive_TWL_norestart_run S')\<close>
proof -
  obtain T where T: \<open>(S, T) \<in> state_wl_l None\<close> \<open>cdcl_twl_stgy_prog_l_pre T S'\<close> \<open>correct_watching S\<close> \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_pre_def by blast
  have H: \<open>{((a, b), a', b'). (a, a') \<in> bool_rel \<and> (b, b') \<in> state_wl_l None} O
       (bool_rel \<times>\<^sub>f twl_st_l None) = bool_rel \<times>\<^sub>r state_wl_l None O twl_st_l None\<close>
    by fastforce
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_early_wl_spec[unfolded fref_param1[symmetric], "to_\<Down>", of S T]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_early_l_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding H conc_fun_chain by auto
      done
    done
qed

subsection \<open>Shared for restarts and inprocessing\<close>

definition clauses_pointed_to :: \<open>'v literal set \<Rightarrow> ('v literal \<Rightarrow> 'v watched) \<Rightarrow> nat set\<close>
  where
  \<open>clauses_pointed_to \<A> W \<equiv> \<Union>(((`) fst) ` set ` W ` \<A>)\<close>

lemma clauses_pointed_to_insert[simp]:
  \<open>clauses_pointed_to (insert A \<A>) W =
  fst ` set (W A) \<union>
  clauses_pointed_to \<A> W\<close> and
  clauses_pointed_to_empty[simp]:
  \<open>clauses_pointed_to {} W = {}\<close>
  by (auto simp: clauses_pointed_to_def)

lemma clauses_pointed_to_remove1_if:
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow> xa \<in># dom_m aa \<Longrightarrow>
    xa \<in> clauses_pointed_to (set_mset (remove1_mset L \<A>))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    xa \<in> clauses_pointed_to (set_mset (remove1_mset L \<A>)) W\<close>
  by (cases \<open>L \<in># \<A>\<close>)
    (fastforce simp: clauses_pointed_to_def
    dest!: multi_member_split)+

lemma clauses_pointed_to_remove1_if2:
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow> xa \<in># dom_m aa \<Longrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L, L'#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L, L'#})) W\<close>
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow> xa \<in># dom_m aa \<Longrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L', L#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    xa \<in> clauses_pointed_to (set_mset (\<A> - {#L', L#})) W\<close>
  by (cases \<open>L \<in># \<A>\<close>; fastforce simp: clauses_pointed_to_def
    dest!: multi_member_split)+

lemma clauses_pointed_to_remove1_if2_eq:
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow>
    set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L, L'#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
    set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L, L'#})) W\<close>
  \<open>\<forall>L\<in>set (W L). fst L \<notin># dom_m aa \<Longrightarrow>
     set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L', L#}))
      (\<lambda>a. if a = L then [] else W a) \<longleftrightarrow>
     set_mset (dom_m aa) \<subseteq> clauses_pointed_to (set_mset (\<A> - {#L', L#})) W\<close>
  by (auto simp: clauses_pointed_to_remove1_if2)

lemma negs_remove_Neg: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Neg A, Pos A#} =
   negs \<A> + poss \<A>\<close>
  by (induction \<A>) auto
lemma poss_remove_Pos: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Pos A, Neg A#} =
   negs \<A> + poss \<A>\<close>
  by (induction \<A>)  auto

end
