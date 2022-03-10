theory Watched_Literals_Watch_List_Restart
  imports Watched_Literals_Watch_List
    Watched_Literals_List_Simp
begin

(*TODO Move*)
lemma cdcl_twl_restart_get_all_init_clss:
  assumes \<open>cdcl_twl_restart S T\<close>
  shows \<open>get_all_init_clss T = get_all_init_clss S\<close>
  using assms by (induction rule: cdcl_twl_restart.induct) auto

lemma rtranclp_cdcl_twl_restart_get_all_init_clss:
  assumes \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close>
  shows \<open>get_all_init_clss T = get_all_init_clss S\<close>
  using assms by (induction rule: rtranclp_induct) (auto simp: cdcl_twl_restart_get_all_init_clss)
(*END Move*)

text \<open>As we have a specialised version of \<^term>\<open>correct_watching\<close>, we defined a special version for
the inclusion of the domain:\<close>

definition all_init_lits :: \<open>(nat, 'v literal list \<times> bool) fmap \<Rightarrow> 'v literal multiset multiset \<Rightarrow>
   'v literal multiset\<close> where
  \<open>all_init_lits S NUE = all_lits_of_mm ((\<lambda>C. mset C) `# init_clss_lf S + NUE)\<close>

lemma all_init_lits_alt_def:
  \<open>all_init_lits S (NUE + NUS + N0S) = all_lits_of_mm ((\<lambda>C. mset C) `# init_clss_lf S + NUE + NUS + N0S)\<close>
  \<open>all_init_lits b (d + f + g) = all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l b#} + d + f + g)\<close>
  by (auto simp: all_init_lits_def ac_simps)

(* abbreviation all_init_lits_of_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal multiset\<close> where
 *   \<open>all_init_lits_of_wl S \<equiv> all_init_lits (get_clauses_wl S)
 *     (get_unit_init_clss_wl S + get_subsumed_init_clauses_wl S + get_init_clauses0_wl S)\<close> *)

definition all_init_atms :: \<open>_ \<Rightarrow> _ \<Rightarrow> 'v multiset\<close> where
  \<open>all_init_atms N NUE = atm_of `# all_init_lits N NUE\<close>

declare all_init_atms_def[symmetric, simp]

lemma all_init_atms_alt_def:
  \<open>set_mset (all_init_atms N NE) = atms_of_mm (mset `# init_clss_lf N) \<union> atms_of_mm NE\<close>
  unfolding all_init_atms_def all_init_lits_def
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff
      all_lits_of_mm_def atms_of_ms_def image_UN
      atms_of_def
    dest!: multi_member_split[of \<open>(_, _)\<close> \<open>ran_m N\<close>]
    dest: multi_member_split atm_of_lit_in_atms_of
    simp del: set_image_mset)

lemma in_set_all_init_atms_iff:
  \<open>y \<in># all_init_atms bu bw \<longleftrightarrow>
    y \<in> atms_of_mm (mset `# init_clss_lf bu) \<or> y \<in> atms_of_mm bw\<close>
  by (auto simp: all_lits_def atm_of_all_lits_of_mm all_init_atms_alt_def atms_of_def
        in_all_lits_of_mm_ain_atms_of_iff all_lits_of_mm_def atms_of_ms_def image_UN
    dest!: multi_member_split[of \<open>(_, _)\<close> \<open>ran_m N\<close>]
    dest: multi_member_split atm_of_lit_in_atms_of
    simp del: set_image_mset)

lemma all_init_atms_fmdrop_add_mset_unit:
  \<open>C \<in># dom_m baa \<Longrightarrow> irred baa C \<Longrightarrow>
    all_init_atms (fmdrop C baa) (add_mset (mset (baa \<propto> C)) da) =
   all_init_atms baa da\<close>
  \<open>C \<in># dom_m baa \<Longrightarrow> \<not>irred baa C \<Longrightarrow>
    all_init_atms (fmdrop C baa) da =
   all_init_atms baa da\<close>
  by (auto simp del: all_init_atms_def[symmetric]
    simp: all_init_atms_def all_init_lits_def
      init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if)

lemma all_init_lits_of_wl_simps[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
  all_init_lits_of_wl (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH {#} US \<Longrightarrow>
  all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, {#}, N0, U0, Q, W)\<close>
  \<open>NO_MATCH [] M \<Longrightarrow>
  all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow>
   all_init_lits_of_wl (M, fmdrop C N, D, add_mset (mset (N \<propto> C)) NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
  all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>all_init_lits_of_wl (M, N, D, NE, add_mset E UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH {#} UEk \<Longrightarrow>
  all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, {#}, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH {#} U0 \<Longrightarrow>
  all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, {#}, Q, W)\<close>
  \<open>NO_MATCH {#} UE \<Longrightarrow>
  all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, {#}, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  by (auto simp: all_init_lits_of_wl_def all_lits_of_mm_add_mset
    image_mset_remove1_mset_if)

lemma all_learned_lits_of_wl_simps[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow>
  all_learned_lits_of_wl (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  (* \<open>NO_MATCH {#} NS \<Longrightarrow>
   * all_learned_lits_of_wl (M, N, D, NE, UE, NS, US, N0, U0, Q, W) =
   *   all_learned_lits_of_wl (M, N, D, NE, UE, {#}, US, N0, U0, Q, W)\<close> *)
  \<open>NO_MATCH [] M \<Longrightarrow>
  all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_learned_lits_of_wl ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>all_learned_lits_of_wl (M, N, D, add_mset E NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, add_mset E NS, US, N0, U0, Q, W) =
    all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
  all_learned_lits_of_wl (M, fmdrop C N, D, NE, add_mset (mset (N \<propto> C)) UE, NEk, UEk, NS, US, N0, U0, Q, W) =
  all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  by (auto simp: all_learned_lits_of_wl_def all_lits_of_mm_add_mset
    image_mset_remove1_mset_if)
  
text \<open>To ease the proof, we introduce the following ``alternative'' definitions, that only considers
  variables that are present in the initial clauses (which are never deleted from the set of
  clauses, but only moved to another component).
\<close>
fun correct_watching' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             b \<longrightarrow> i \<in># dom_m N) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) =
          clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>

(*TODO duplicate of leaking bin*)
fun correct_watching'_nobin :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching'_nobin (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) =
          clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>

lemma correct_watching'_correct_watching': \<open>correct_watching' S \<Longrightarrow> correct_watching' S\<close>
  by (cases S) auto

declare correct_watching'_nobin.simps[simp del] correct_watching'.simps[simp del]

text \<open>Now comes a weaker version of the invariants on watch lists: instead of knowing that
  the watch lists are correct, we only know that the clauses appear somewhere in the watch lists.
  From a conceptual point of view, this is sufficient to specify all operations, but this is not
  sufficient to derive bounds on the length. Hence, we also add the invariants that each watch list
  does not contain duplicates.
\<close>
definition no_lost_clause_in_WL :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>no_lost_clause_in_WL S \<equiv>
  set_mset (dom_m (get_clauses_wl S))
    \<subseteq> clauses_pointed_to (set_mset (all_init_lits_of_wl S)) (get_watched_wl S) \<and>
  (\<forall>L\<in># all_init_lits_of_wl S. distinct_watched (watched_by S L))\<close>

definition no_lost_clause_in_WL0 :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>no_lost_clause_in_WL0 S \<equiv>
  set_mset (dom_m (get_clauses_wl S))
  \<subseteq> clauses_pointed_to (set_mset (all_init_lits_of_wl S)) (get_watched_wl S)\<close>


definition blits_in_\<L>\<^sub>i\<^sub>n' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>blits_in_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow>
    (\<forall>L \<in># all_init_lits_of_wl S.
      \<forall>(i, K, b) \<in> set (watched_by S L). K \<in># all_init_lits_of_wl S)\<close>

definition literals_are_\<L>\<^sub>i\<^sub>n' :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<equiv>
    set_mset (all_learned_lits_of_wl S) \<subseteq> set_mset (all_init_lits_of_wl S) \<and>
     blits_in_\<L>\<^sub>i\<^sub>n' S\<close>

definition all_init_atms_st :: \<open>'v twl_st_wl \<Rightarrow> 'v multiset\<close> where
  \<open>all_init_atms_st S \<equiv> all_init_atms (get_clauses_wl S)
    (get_unit_init_clss_wl S + get_subsumed_init_clauses_wl S + get_init_clauses0_wl S)\<close>

lemma all_init_atms_st_alt_def: \<open>all_init_atms_st S = atm_of `# all_init_lits_of_wl S\<close>
  by (auto simp: all_atms_def all_lits_st_def all_init_atms_st_def all_init_lits_of_wl_def
    atm_of_all_lits_of_mm all_init_atms_def all_init_lits_def ac_simps
    simp del: all_init_atms_def[symmetric])

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NU)) = set_mset (all_init_lits N NU)\<close>
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S)) = set_mset (all_init_lits_of_wl S)\<close>
  by (simp_all add: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_init_atms_def all_init_lits_def
    all_init_lits_of_wl_def ac_simps all_init_atms_st_def)

lemma literals_are_\<L>\<^sub>i\<^sub>n_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> S = literals_are_\<L>\<^sub>i\<^sub>n \<B> S\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma all_learned_lits_of_wl_all_lits_st:
  \<open>set_mset (all_learned_lits_of_wl S) \<subseteq> set_mset (all_lits_st S)\<close>
  unfolding all_learned_lits_of_wl_def all_lits_st_def all_lits_def
  apply (subst (2) all_clss_l_ran_m[symmetric])
  unfolding image_mset_union
  by (cases S) (auto simp: all_lits_of_mm_union)

lemma all_lits_st_init_learned:
  \<open>set_mset (all_lits_st S) = set_mset (all_init_lits_of_wl S) \<union> set_mset (all_learned_lits_of_wl S)\<close>
  unfolding all_learned_lits_of_wl_def all_lits_st_def all_lits_def all_init_lits_of_wl_def
  apply (subst (1) all_clss_l_ran_m[symmetric])
  unfolding image_mset_union
  by (cases S) (auto simp: all_lits_of_mm_union)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)) = set_mset (all_lits_st S)\<close>
  by (metis \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_atms_st_alt_def_sym all_lits_def all_lits_st_def)

lemma literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff:
  assumes
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs xa\<close>
  shows
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> (is ?A)
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> (is ?B)
    \<open>set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close> (is ?C) and
    \<open>set_mset (all_init_lits_of_wl S) = set_mset (all_lits_st S)\<close> (is ?D)
proof -
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of xa)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      pcdcl_all_struct_invs_def state\<^sub>W_of_def
    by fast+
  then have \<open>\<And>L. L \<in> atm_of ` lits_of_l (get_trail_wl S) \<Longrightarrow> L \<in> atms_of_ms
      ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m (get_clauses_wl S) \<and> snd a}) \<union>
      atms_of_mm (get_unit_init_clss_wl S) \<union>
      atms_of_mm (get_subsumed_init_clauses_wl S) \<union>
      atms_of_mm (get_init_clauses0_wl S)\<close> and
    alien_learned: \<open>atms_of_mm (learned_clss (state\<^sub>W_of xa))
      \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of xa))\<close>
    using Sx x_xa unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto 5 2 simp add: twl_st twl_st_l twl_st_wl)

  show 1: \<open>set_mset (all_init_lits_of_wl S) = set_mset (all_lits_st S)\<close>
    unfolding all_lits_st_def all_lits_def all_init_lits_of_wl_def
    apply (subst (2) all_clss_l_ran_m[symmetric])
    using alien_learned Sx x_xa
    unfolding image_mset_union all_lits_of_mm_union
    by (auto simp : in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def
      twl_st twl_st_l twl_st_wl get_learned_clss_wl_def)
  have \<open>set_mset (all_init_lits_of_wl S) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S))\<close>
    unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) ..
 show A: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> for \<A>
  proof -
    have sub: \<open>set_mset (all_lits_st S) \<subseteq> set_mset (all_init_lits_of_wl S) \<longleftrightarrow>
      is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S) (all_lits_st S)\<close>
     using all_init_lits_of_wl_all_lits_st[of S]
     unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) by auto
   have \<open>set_mset (all_learned_lits_of_wl S) \<subseteq> set_mset (all_lits_st S) \<longleftrightarrow>
     is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) (all_lits_st S)\<close>
     using all_init_lits_of_wl_all_lits_st[of S]
     unfolding all_lits_st_init_learned is_\<L>\<^sub>a\<^sub>l\<^sub>l_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms
     by auto
   then show ?thesis
      unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def
	literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def sub
	all_init_lits_def[symmetric] all_lits_alt_def2[symmetric]
        all_lits_alt_def[symmetric] all_init_lits_alt_def[symmetric]
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_def[symmetric] all_init_atms_def[symmetric] 1
      by simp
   qed

   show C: ?C
     using 1 unfolding all_atms_st_alt_def all_init_atms_st_alt_def
     apply (simp add: 1 del: all_init_atms_def[symmetric])
     by (metis all_atms_st_alt_def set_image_mset)

  show ?B
    apply (subst A)
    ..
qed

lemma correct_watching'_nobin_clauses_pointed_to0:
  assumes
    xa_xb: \<open>(xa, xb) \<in> state_wl_l None\<close> and
    corr: \<open>correct_watching'_nobin xa\<close> and
    L: \<open>literals_are_\<L>\<^sub>i\<^sub>n' xa\<close> and
    xb_x: \<open>(xb, x) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs x\<close>

  shows \<open>set_mset (dom_m (get_clauses_wl xa))
    \<subseteq> clauses_pointed_to
    (Neg ` set_mset (all_init_atms_st xa) \<union>
    Pos ` set_mset (all_init_atms_st xa))
    (get_watched_wl xa)\<close>
    (is ?G1 is \<open>_ \<subseteq> ?A\<close>) and
    \<open>no_lost_clause_in_WL xa\<close> (is ?G2)
proof -
  let ?\<A> = \<open>all_init_atms (get_clauses_wl xa) (get_unit_init_clss_wl xa)\<close>
  show ?G1
  proof
    fix C
    assume C: \<open>C \<in># dom_m (get_clauses_wl xa)\<close>
    obtain M N D NE UE NEk UEk NS US N0 U0 Q W where
      xa: \<open>xa = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
      by (cases xa)
    have \<open>twl_st_inv x\<close>
      using xb_x C struct_invs
      by (auto simp: twl_struct_invs_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
    then have le0: \<open>get_clauses_wl xa \<propto> C \<noteq> []\<close>
      using xb_x C xa_xb
      by (cases x; cases \<open>irred N C\<close>)
        (auto simp: twl_struct_invs_def twl_st_inv.simps
          twl_st_l_def state_wl_l_def xa ran_m_def conj_disj_distribR
          Collect_disj_eq Collect_conv_if
        dest!: multi_member_split)
    then have le: \<open>N \<propto> C ! 0 \<in> set (watched_l (N \<propto> C))\<close>
      by (cases \<open>N \<propto> C\<close>) (auto simp: xa)
    have eq: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NE)) =
          set_mset (all_lits_of_mm (mset `# init_clss_lf N + NE))\<close>
       by (auto simp del: all_init_atms_def[symmetric]
          simp: all_init_atms_def xa \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm[symmetric]
            all_init_lits_def)

    have H: \<open>get_clauses_wl xa \<propto> C ! 0 \<in># all_init_lits_of_wl xa\<close>
      using L C le0 apply -
      unfolding all_init_atms_def[symmetric] all_init_lits_def[symmetric]
      apply (subst literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4)[OF xa_xb xb_x struct_invs])
      apply (cases \<open>N \<propto> C\<close>; auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def ran_m_def eq
            all_lits_of_mm_add_mset is_\<L>\<^sub>a\<^sub>l\<^sub>l_def xa all_lits_of_m_add_mset
            \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits all_lits_st_def
          dest!: multi_member_split)
      done
    moreover {
      have \<open>{#i \<in># fst `# mset (W (N \<propto> C ! 0)). i \<in># dom_m N#} =
             add_mset C {#Ca \<in># remove1_mset C (dom_m N). N \<propto> C ! 0 \<in> set (watched_l (N \<propto> Ca))#}\<close>
        using corr H C le unfolding xa
        by (auto simp: clauses_pointed_to_def correct_watching'_nobin.simps xa
          simp flip: all_init_atms_def all_init_lits_def all_init_atms_alt_def
            all_init_lits_alt_def
          simp: clause_to_update_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split)
      from arg_cong[OF this, of set_mset] have \<open>C \<in> fst ` set (W (N \<propto> C ! 0))\<close>
        using corr H C le unfolding xa
        by (auto simp: clauses_pointed_to_def correct_watching'.simps xa
          simp: all_init_atms_def all_init_lits_def clause_to_update_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split) }
    ultimately show \<open>C \<in> ?A\<close>
      by (cases \<open>N \<propto> C ! 0\<close>)
        (auto simp: clauses_pointed_to_def correct_watching'.simps xa
          simp flip: all_init_lits_def all_init_atms_alt_def
            all_init_lits_alt_def 
          simp: clause_to_update_def all_init_atms_st_def all_init_lits_of_wl_def all_init_atms_def
          simp del: all_init_atms_def[symmetric]
        dest!: multi_member_split)
  qed
  moreover have \<open>set_mset (all_init_lits_of_wl xa) =
    Neg ` set_mset (all_init_atms_st xa) \<union> Pos ` set_mset (all_init_atms_st xa)\<close>
    unfolding all_init_lits_of_wl_def
      all_lits_of_mm_def all_init_atms_st_def all_init_atms_def
    by (auto simp: all_init_atms_def all_init_lits_def all_lits_of_mm_def image_image
      image_Un
      simp del: all_init_atms_def[symmetric]) 
  moreover have \<open>distinct_watched (watched_by xa (Pos L))\<close>
    \<open>distinct_watched (watched_by xa (Neg L))\<close>
    if \<open>L \<in># all_init_atms_st xa\<close> for L
    using that corr
    by (cases xa;
        auto simp: correct_watching'_nobin.simps all_init_lits_of_wl_def all_init_atms_def
        all_lits_of_mm_union all_init_lits_def all_init_atms_st_def literal.atm_of_def
        in_all_lits_of_mm_uminus_iff[symmetric, of \<open>Pos _\<close>]
        simp del: all_init_atms_def[symmetric]
        split: literal.splits; fail)+
  ultimately show ?G2
    unfolding no_lost_clause_in_WL_def
    by (auto simp del: all_init_atms_def[symmetric]) 
qed

lemma correct_watching'_clauses_pointed_to2:
  assumes
    xa_xb: \<open>(xa, xb) \<in> state_wl_l None\<close> and
    corr: \<open>correct_watching'_nobin xa\<close> and
    pre: \<open>mark_to_delete_clauses_l_pre xb\<close> and
    L: \<open>literals_are_\<L>\<^sub>i\<^sub>n' xa\<close>
  shows \<open>set_mset (dom_m (get_clauses_wl xa))
         \<subseteq> clauses_pointed_to
            (Neg ` set_mset (all_init_atms_st xa) \<union>
             Pos ` set_mset (all_init_atms_st xa))
            (get_watched_wl xa)\<close>
        (is ?G1 is \<open>_ \<subseteq> ?A\<close>) and
    \<open>no_lost_clause_in_WL xa\<close> (is ?G2)
  using correct_watching'_nobin_clauses_pointed_to0[OF xa_xb corr L] pre
  unfolding mark_to_delete_clauses_l_pre_def
  by fast+


definition (in -) restart_abs_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_pre S last_GC last_Restart brk \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_abs_l_pre S' last_GC last_Restart brk
      \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>

definition (in -) cdcl_twl_local_restart_wl_spec :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_local_restart_wl_spec = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(\<exists>last_GC last_Restart. restart_abs_wl_pre (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) last_GC last_Restart False);
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#}) \<or> (M' = M \<and> Q' = Q));
      RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)
   })\<close>

lemma cdcl_twl_local_restart_wl_spec_cdcl_twl_local_restart_l_spec:
  \<open>(cdcl_twl_local_restart_wl_spec, cdcl_twl_local_restart_l_spec)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  have [simp]:
    \<open>all_lits N (NE + UE + (NS + US) + (N0 + U0)) = all_lits N (NE + UE + NS + US + N0 + U0)\<close>
    \<open>all_lits N ((NE + UE) + (NS + US) + (N0 + U0)) = all_lits N (NE + UE + NS + US + N0 + U0)\<close>
    for NE UE NS US N N0 U0
    by (auto simp: ac_simps)
  have [refine0]:
    \<open>\<And>x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n
    x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w xa x1x x2x.
    (x, y) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<Longrightarrow>
    x2j = (x1k, x2k) \<Longrightarrow>
    x2i = (x1j, x2j) \<Longrightarrow>
    x2h = (x1i, x2i) \<Longrightarrow>
    x2g = (x1h, x2h) \<Longrightarrow>
    x2f = (x1g, x2g) \<Longrightarrow>
    x2e = (x1f, x2f) \<Longrightarrow>
    x2d = (x1e, x2e) \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    x2a = (x1b, x2b) \<Longrightarrow>
    x2 = (x1a, x2a) \<Longrightarrow>
    y = (x1, x2) \<Longrightarrow>
    x2v = (x1w, x2w) \<Longrightarrow>
    x2u = (x1v, x2v) \<Longrightarrow>
    x2t = (x1u, x2u) \<Longrightarrow>
    x2s = (x1t, x2t) \<Longrightarrow>
    x2r = (x1s, x2s) \<Longrightarrow>
    x2q = (x1r, x2r) \<Longrightarrow>
    x2p = (x1q, x2q) \<Longrightarrow>
    x2o = (x1p, x2p) \<Longrightarrow>
    x2n = (x1o, x2o) \<Longrightarrow>
    x2m = (x1n, x2n) \<Longrightarrow>
    x2l = (x1m, x2m) \<Longrightarrow>
    x = (x1l, x2l) \<Longrightarrow>
    case xa of
    (M', Q') \<Rightarrow> (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition x1l) \<and> Q' = {#}) \<or> M' = x1l \<and> Q' = x1w \<Longrightarrow>
    xa = (x1x, x2x) \<Longrightarrow>
    (\<exists>K M2. (Decided K # x1x, M2) \<in> set (get_all_ann_decomposition x1) \<and> x2x = {#}) \<or> x1x = x1 \<and> x2x = x2k\<close>
    by (auto 5 3 simp: state_wl_l_def)
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_spec_def cdcl_twl_local_restart_l_spec_def
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal unfolding restart_abs_wl_pre_def by fast
    apply assumption+
    subgoal
      by (fastforce simp: state_wl_l_def correct_watching.simps clause_to_update_def
          blits_in_\<L>\<^sub>i\<^sub>n_def
        simp flip: all_lits_alt_def2)
    done
qed

definition cdcl_twl_restart_wl_prog where
\<open>cdcl_twl_restart_wl_prog S = do {
   cdcl_twl_local_restart_wl_spec S
  }\<close>

lemma cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(cdcl_twl_restart_wl_prog, cdcl_twl_restart_l_prog)
    \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_prog_def cdcl_twl_restart_l_prog_def
  apply (intro frefI nres_relI)
  apply (refine_vcg cdcl_twl_local_restart_wl_spec_cdcl_twl_local_restart_l_spec[THEN fref_to_Down])
  done

definition cdcl_twl_full_restart_wl_GC_prog_post :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_GC_prog_post S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
    cdcl_twl_full_restart_l_GC_prog_pre S' \<and>
    cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S' T' \<and> correct_watching' T \<and>
    set_mset (all_init_lits_of_wl T) =
    set_mset (all_lits_st T) \<and>
    get_unkept_learned_clss_wl T = {#} \<and>
    get_subsumed_learned_clauses_wl T = {#} \<and>
    get_learned_clauses0_wl T = {#}
)\<close>

definition cdcl_twl_full_restart_wl_GC_prog_post_confl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_GC_prog_post_confl  S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
    cdcl_twl_full_restart_l_GC_prog_pre S' \<and>
    cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S' T' \<and>
    set_mset (all_init_lits_of_wl T) =
    set_mset (all_lits_st T))\<close>

definition (in -) restart_abs_wl_pre2 :: \<open>'v twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_pre2 S brk \<longleftrightarrow>
    (\<exists>S' last_GC last_Restart. (S, S') \<in> state_wl_l None \<and> restart_abs_l_pre S' last_GC last_Restart brk
      \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition (in -) cdcl_twl_local_restart_wl_spec0 :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_twl_local_restart_wl_spec0 = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
      ASSERT(restart_abs_wl_pre2 (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) False);
      (M, Q) \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
            Q' = {#} \<and> count_decided M' = 0) \<or> (M' = M \<and> Q' = Q \<and> count_decided M' = 0));
      RETURN (M, N, D, NE, UE, NEk, UEk, NS, {#}, N0, {#}, Q, W)
   })\<close>

definition cdcl_twl_full_restart_wl_GC_prog_pre
  :: \<open>'v twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>cdcl_twl_full_restart_wl_GC_prog_pre S \<longleftrightarrow>
   (\<exists>T. (S, T) \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> cdcl_twl_full_restart_l_GC_prog_pre T)\<close>

lemma blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0:
  \<open>NO_MATCH {#} f' \<Longrightarrow>
  literals_are_\<L>\<^sub>i\<^sub>n' (a, b, c, d, e, NEk, UEk, NS, US, N0, U0, f', g) \<longleftrightarrow>
      literals_are_\<L>\<^sub>i\<^sub>n' (ah, b, c, d, e, NEk, UEk, NS, US, N0, U0, {#}, g)\<close>
  by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def all_init_lits_of_wl_def all_learned_lits_of_wl_def)

lemma all_init_lits_of_wl_keepUSD:
  \<open>L \<in># all_init_lits_of_wl ([], x1k, x1l, x1m, x1n, NEk, UEk, x1o, {#}, x1q, x1r, {#}, x2s) \<Longrightarrow>
  L \<in># all_init_lits_of_wl ([], x1k, x1l, x1m, x1n, NEk, UEk, x1o, {#}, x1q, x1r, Q, x2s)\<close>
  by (auto simp: all_init_lits_of_wl_def all_lits_of_mm_def)

lemma (in -)[twl_st,simp]: \<open>learned_clss (state\<^sub>W_of S) = get_all_learned_clss S\<close>
  by (cases S) auto

lemma (in -)[twl_st,simp]: \<open>init_clss (state\<^sub>W_of S) = get_all_init_clss S\<close>
  by (cases S) auto
 
lemma literals_are_\<L>\<^sub>i\<^sub>n'_empty:
  \<open>NO_MATCH {#} x2m \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<longleftrightarrow>
     literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, {#}, Q)\<close>
   \<open>NO_MATCH {#} x2l \<Longrightarrow> correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<longleftrightarrow>
    correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', {#}, N0, U0, x2m, Q)\<close>
   \<open>NO_MATCH {#} x2m \<Longrightarrow> correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<longleftrightarrow>
    correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, {#}, Q)\<close>
   \<open>NO_MATCH {#} U0 \<Longrightarrow> correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<longleftrightarrow>
    correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', x2l, N0, {#}, x2m, Q)\<close>
   \<open>NO_MATCH {#} b \<Longrightarrow> correct_watching' (x1h, x1i, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<longleftrightarrow>
    correct_watching' (x1h, x1i, x1j, x1k, {#}, NEk, UEk, x', x2l, N0, U0, x2m, Q)\<close>
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<Longrightarrow>
     literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', {#}, N0, U0, x2m, Q)\<close>
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<Longrightarrow>
     literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, {#}, x2m, Q)\<close>
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<Longrightarrow>
     literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j, x1k, {#}, NEk, UEk, x', x2l, N0, U0, x2m, Q)\<close>
   by (auto 5 3 simp: literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_of_mm_union
     correct_watching'.simps correct_watching'.simps clause_to_update_def all_init_lits_of_wl_def
     all_learned_lits_of_wl_def)

lemma literals_are_\<L>\<^sub>i\<^sub>n'_decompD:
  \<open>(K # x1h', M2) \<in> set (get_all_ann_decomposition x1h) \<Longrightarrow>
  literals_are_\<L>\<^sub>i\<^sub>n' (x1h, x1p, x1j', x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q) \<Longrightarrow>
     literals_are_\<L>\<^sub>i\<^sub>n' (x1h', x1p, x1j, x1k, b, NEk, UEk, x', x2l, N0, U0, x2m, Q)\<close>
  by (auto 5 3 simp: literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_of_mm_union
     correct_watching'.simps correct_watching'.simps clause_to_update_def all_init_lits_of_wl_def
     all_learned_lits_of_wl_def
     dest!: get_all_ann_decomposition_exists_prepend)


lemma all_init_learned_lits_simps_Q:
  \<open>NO_MATCH {#} Q \<Longrightarrow> all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)\<close>
  \<open>NO_MATCH {#} U0 \<Longrightarrow> all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, {#}, Q, W)\<close>
  \<open>NO_MATCH {#} Q \<Longrightarrow> all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)\<close>
  by (auto simp: all_init_lits_of_wl_def all_learned_lits_of_wl_def all_lits_of_mm_def)

lemma in_all_learned_lits_of_wl_addUS:
  \<open>x \<in> set_mset (all_learned_lits_of_wl (M, x1k, x1l, x1m, x1n, NEk, UEk, x1o,  {#}, x1q, x1r, x1s, x2s)) \<Longrightarrow>
  x \<in> set_mset (all_learned_lits_of_wl (M, x1k, x1l, x1m, x1n, NEk, UEk, x1o, x1p, x1q, x1r, x1s, x2s))\<close>
  \<open>x \<in> set_mset (all_learned_lits_of_wl (M, x1k, x1l, x1m, x1n, NEk, UEk, x1o,  x1p, x1q, {#}, x1s, x2s)) \<Longrightarrow>
  x \<in> set_mset (all_learned_lits_of_wl (M, x1k, x1l, x1m, x1n, NEk, UEk, x1o, x1p, x1q, x1r, x1s, x2s))\<close>
  \<open>x \<in> set_mset (all_learned_lits_of_wl (M, x1k, x1l, x1m, {#}, NEk, UEk, x1o, x1p, x1q, x1r, x1s, x2s)) \<Longrightarrow>
  x \<in> set_mset (all_learned_lits_of_wl (M, x1k, x1l, x1m, x1n, NEk, UEk, x1o, x1p, x1q, x1r, x1s, x2s))\<close>
  by (auto simp: all_learned_lits_of_wl_def all_lits_of_mm_union)

lemma cdcl_twl_local_restart_wl_spec0_cdcl_twl_local_restart_l_spec0:
  \<open>(x, y) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<Longrightarrow>
          cdcl_twl_local_restart_wl_spec0 x
          \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}
	    (cdcl_twl_local_restart_l_spec0 y)\<close>
  unfolding cdcl_twl_local_restart_wl_spec0_def cdcl_twl_local_restart_l_spec0_def curry_def
  apply refine_vcg
  subgoal unfolding restart_abs_wl_pre2_def by (rule exI[of _ y]) fast
  subgoal
    by (auto simp add: literals_are_\<L>\<^sub>i\<^sub>n'_empty
        state_wl_l_def image_iff correct_watching'.simps clause_to_update_def
      conc_fun_RES RES_RETURN_RES2 blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0
      intro: literals_are_\<L>\<^sub>i\<^sub>n'_decompD literals_are_\<L>\<^sub>i\<^sub>n'_empty(4))
  subgoal
    by (auto 4 3 simp add: literals_are_\<L>\<^sub>i\<^sub>n'_empty
        state_wl_l_def image_iff correct_watching'.simps clause_to_update_def
      conc_fun_RES RES_RETURN_RES2 blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0 
      literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_learned_lits_simps_Q blits_in_\<L>\<^sub>i\<^sub>n'_def
      dest: all_init_lits_of_wl_keepUSD
      in_all_learned_lits_of_wl_addUS)
  done

lemma cdcl_twl_full_restart_wl_GC_prog_post_correct_watching:
  assumes
    pre: \<open>cdcl_twl_full_restart_l_GC_prog_pre y\<close> and
    y_Va: \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* y Va\<close> and
    \<open>(V, Va) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
  shows \<open>(V, Va) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close> and
    \<open>set_mset (all_init_lits_of_wl V) = set_mset (all_lits_st V)\<close>
proof -
  obtain x where
    y_x: \<open>(y, x) \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs x\<close> and
    list_invs: \<open>twl_list_invs y\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of x)\<close>
    using pre unfolding cdcl_twl_full_restart_l_GC_prog_pre_def by blast
  obtain V' where \<open>cdcl_twl_inp\<^sup>*\<^sup>* x V'\<close> and Va_V': \<open>(Va, V') \<in> twl_st_l None\<close>
    using rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[OF y_Va y_x list_invs struct_invs ent]
    by blast
  then have \<open>twl_struct_invs V'\<close>
    using struct_invs ent rtranclp_cdcl_twl_inp_twl_struct_invs by blast
  then show eq: \<open>set_mset (all_init_lits_of_wl V) = set_mset (all_lits_st V)\<close>
    using assms(3) Va_V'  \<open>twl_struct_invs V'\<close> literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4) by blast
  then have \<open>correct_watching' V \<Longrightarrow>  correct_watching V\<close>
    by (cases V) (auto simp: correct_watching.simps correct_watching'.simps)
  moreover
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n' V \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n V\<close>
    using eq by (cases V)
      (clarsimp simp: blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def ac_simps)
  ultimately show \<open>(V, Va) \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close>
    using assms by (auto simp: cdcl_twl_full_restart_wl_GC_prog_post_def)
qed

(*TODO move within this file, seems to be Watched_Literals_Watch_List_Restart.ℒ\<^sub>a\<^sub>l\<^sub>l_all_init_atms(1)*)
lemma \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NE)) = set_mset (all_init_lits N NE)\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms ..
end
