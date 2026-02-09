theory IsaSAT_Simplify_Forward_Subsumption
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Simplify_Forward_Subsumption_Defs
begin


lemma subsume_clauses_match2_subsume_clauses_match:
  assumes
    \<open>(C, E) \<in> nat_rel\<close>
    \<open>(C', F) \<in> nat_rel\<close> and
    DG: \<open>(D, G) \<in> clause_hash_ref (all_init_atms_st S)\<close> and
    N: \<open>N = get_clauses_wl S\<close> and
    G: \<open>G = mset (get_clauses_wl S \<propto> C')\<close> and
    lin: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows \<open>subsume_clauses_match2 C C' S D \<le> \<Down>Id (subsume_clauses_match E F N)\<close>
proof -
  have eq: \<open>E = C\<close> \<open>F = C'\<close>
    using assms by auto
  have [simp]: \<open>set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close>
    using lin unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def all_atms_st_alt_def
    by (metis Un_subset_iff \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) all_atms_st_alt_def_sym
      all_lits_st_init_learned atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_cong_set_mset dual_order.antisym subset_refl)
  have [intro!]: \<open>C \<in># dom_m (get_clauses_wl S) \<Longrightarrow> x1a < length (get_clauses_wl S \<propto> C) \<Longrightarrow>
    atm_of (get_clauses_wl S \<propto> C ! x1a) \<in># all_atms_st S\<close> for x1a
    unfolding all_atms_st_alt_def
    by (auto intro!: nth_in_all_lits_stI simp del: all_atms_st_alt_def[symmetric])
  have [refine]: \<open>((0, SUBSUMED_BY C), 0, SUBSUMED_BY C) \<in> nat_rel \<times>\<^sub>f Id\<close>
    by auto
  have subsume_clauses_match_alt_def:
  \<open>subsume_clauses_match C C' N = do {
  ASSERT (subsume_clauses_match_pre C C' N);
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). try_to_subsume C' C (N (C \<hookrightarrow> take i (N \<propto> C))) s\<^esup> (\<lambda>(i, st). i < length (N \<propto> C) \<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      let L = N \<propto> C ! i;
      let lin = L \<in># mset (N \<propto> C');
      if lin
      then RETURN (i+1, st)
      else let lin = -L \<in># mset (N \<propto> C') in
      if lin
      then if is_subsumed st
      then RETURN (i+1, STRENGTHENED_BY L C)
      else RETURN (i+1, NONE)
      else RETURN (i+1, NONE)
    })
     (0, SUBSUMED_BY C);
  RETURN st
    }\<close> for C C' N
    unfolding subsume_clauses_match_def Let_def by (auto cong: if_cong)
  have [refine]: \<open>(x1a, x1) \<in> nat_rel \<Longrightarrow> (get_clauses_wl S \<propto> C ! x1a, get_clauses_wl S \<propto> C ! x1) \<in> Id\<close> for x1 x1a
    by auto
  show ?thesis
    unfolding N subsume_clauses_match2_def subsume_clauses_match_alt_def Let_def[of \<open>length _\<close>] eq
      mop_clauses_at_def nres_monad3
    apply (refine_rcg DG[unfolded G] mop_ch_in)
    subgoal using DG G unfolding subsume_clauses_match2_pre_def clause_hash_ref_def
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: subsume_clauses_match_pre_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: subsume_clauses_match_pre_def)
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

definition forward_subsumption_one_wl2_rel where
  \<open>forward_subsumption_one_wl2_rel S\<^sub>0 occs cands n C D = {((S, changed, occs', D'), (T, changed')). (\<not>changed \<longrightarrow> C \<in># dom_m (get_clauses_wl S)) \<and>
     changed = changed' \<and> set_mset (all_init_atms_st S) = set_mset (all_init_atms_st S\<^sub>0) \<and>
      (changed \<longrightarrow> (D', {#}) \<in> clause_hash_ref (all_init_atms_st S)) \<and>
      (\<not>changed \<longrightarrow> D' = D \<and> occs' = occs \<and> get_clauses_wl S \<propto> C = get_clauses_wl S\<^sub>0 \<propto> C) \<and>
      correct_occurence_list S occs' (if changed then remove1_mset C cands else cands)
        (if changed then size (get_clauses_wl S\<^sub>0 \<propto> C) else n) \<and>
      all_occurrences (all_init_atms_st S) occs' \<subseteq># add_mset C (all_occurrences  (all_init_atms_st S) occs) \<and>
     (S,T)\<in>Id
    }\<close>


lemma literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' S \<Longrightarrow>
  set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def all_atms_st_alt_def
  by (metis Un_subset_iff \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) all_atms_st_alt_def_sym
    all_lits_st_init_learned atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_cong_set_mset dual_order.antisym subset_refl)

lemma
  inter_mset_empty_remove1_msetI:
    \<open>A \<inter># B = {#} \<Longrightarrow> A \<inter># remove1_mset c B = {#}\<close> and
  inter_mset_empty_removeAll_msetI:
    \<open>A \<inter># B = {#} \<Longrightarrow> A \<inter># removeAll_mset c B = {#}\<close>
  apply (meson disjunct_not_in in_diffD)
  by (metis count_le_replicate_mset_subset_eq dual_order.refl inter_mset_empty_distrib_right
    subset_mset.diff_add)

lemma push_to_occs_list2:
  assumes occs: \<open>correct_occurence_list S occs cands n\<close>
    \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    \<open>2 \<le> length (get_clauses_wl S \<propto> C)\<close> and
    lin: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
    undef: \<open>\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L\<close> and
    notin: \<open>C \<notin># all_occurrences (mset_set (fst occs)) occs\<close>
  shows \<open>push_to_occs_list2 C S occs \<le> SPEC (\<lambda>c. (c, ()) \<in> {(occs', occs'').
    all_occurrences (all_init_atms_st S) occs' = add_mset C (all_occurrences  (all_init_atms_st S) occs) \<and>
    correct_occurence_list S occs' (remove1_mset C cands) (max n (length (get_clauses_wl S \<propto> C))) \<and> fst occs = fst occs'})\<close>
proof -
  have 1: \<open>atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_atms_st S)\<close>
    using nth_in_all_lits_stI[of C S] assms(2)
    unfolding all_atms_st_alt_def
    by (auto simp del: all_atms_st_alt_def[symmetric] simp: in_set_conv_nth)
  moreover have \<open>atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_init_atms_st S)\<close>
    using 1 lin unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def by (simp add: lin literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def)
  moreover have \<open>L \<in> set (get_clauses_wl S \<propto> C) \<Longrightarrow>
    L \<in># all_init_lits_of_wl S\<close> for L
    by (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) calculation(2) image_subset_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)

  ultimately show ?thesis
    using literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[OF lin]
    unfolding push_to_occs_list2_def
    apply (refine_vcg mop_occ_list_append[THEN order_trans])
    subgoal using assms unfolding push_to_occs_list2_pre_def correct_occurence_list_def by fast
    subgoal using assms unfolding occ_list_append_pre_def correct_occurence_list_def
      by auto
    subgoal for L occs'
      using multi_member_split[of \<open>atm_of L\<close> \<open>all_init_atms_st S\<close>]
      apply (subgoal_tac \<open>atm_of L \<in># all_init_atms_st S\<close>)
      apply (cases occs)
      by (use assms literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[OF lin] in
        \<open>auto 4 2 simp: occ_list_append_def correct_occurence_list_def
        all_occurrences_add_mset occ_list_def all_occurrences_insert_lit
        all_occurrences_occ_list_append_r distinct_mset_remove1_All all_init_atms_st_alt_def
        intro: inter_mset_empty_removeAll_msetI\<close>)
   done
qed

lemma maybe_push_to_occs_list2:
  assumes occs: \<open>correct_occurence_list S occs cands n\<close>
    \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    \<open>2 \<le> length (get_clauses_wl S \<propto> C)\<close> and
    lin: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
    undef: \<open>\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L\<close> and
    notin: \<open>C \<notin># all_occurrences (mset_set (fst occs)) occs\<close>
  shows \<open>maybe_push_to_occs_list2 C S occs \<le> SPEC (\<lambda>c. (c, ()) \<in> {(occs', occs'').
   (all_occurrences (all_init_atms_st S) occs' = add_mset C (all_occurrences  (all_init_atms_st S) occs) \<or>
      all_occurrences (all_init_atms_st S) occs' = all_occurrences  (all_init_atms_st S) occs) \<and>
    correct_occurence_list S occs' (remove1_mset C cands) (max n (length (get_clauses_wl S \<propto> C))) \<and> fst occs = fst occs'})\<close>
proof -
  have 1: \<open>atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_atms_st S)\<close>
    using nth_in_all_lits_stI[of C S] assms(2)
    unfolding all_atms_st_alt_def
    by (auto simp del: all_atms_st_alt_def[symmetric] simp: in_set_conv_nth)
  moreover have \<open>atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_init_atms_st S)\<close>
    using 1 lin unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def by (simp add: lin literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def)
  moreover have \<open>L \<in> set (get_clauses_wl S \<propto> C) \<Longrightarrow>
    L \<in># all_init_lits_of_wl S\<close> for L
    by (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) calculation(2) image_subset_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)

  ultimately show ?thesis
    using literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[OF lin]
    unfolding maybe_push_to_occs_list2_def
    apply (refine_vcg mop_occ_list_append[THEN order_trans])
    subgoal using assms unfolding push_to_occs_list2_pre_def correct_occurence_list_def by fast
    subgoal using assms unfolding occ_list_append_pre_def correct_occurence_list_def
      by auto
    subgoal for keep L occs'
      using multi_member_split[of \<open>atm_of L\<close> \<open>all_init_atms_st S\<close>]
      apply (subgoal_tac \<open>atm_of L \<in># all_init_atms_st S\<close>)
      apply (cases occs)
      by (use assms literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[OF lin] in
        \<open>auto 4 2 simp: occ_list_append_def correct_occurence_list_def
        all_occurrences_add_mset occ_list_def all_occurrences_insert_lit
        all_occurrences_occ_list_append_r distinct_mset_remove1_All all_init_atms_st_alt_def
        intro: inter_mset_empty_removeAll_msetI\<close>)
    subgoal for keep
      using assms by (auto 4 2 simp: occ_list_append_def correct_occurence_list_def
        all_occurrences_add_mset occ_list_def all_occurrences_insert_lit
        all_occurrences_occ_list_append_r distinct_mset_remove1_All all_init_atms_st_alt_def
        intro: inter_mset_empty_removeAll_msetI)
   done
qed

definition forward_subsumption_one_wl2 :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> nat literal \<Rightarrow> occurences \<Rightarrow> clause_hash \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> bool \<times> occurences \<times> clause_hash) nres\<close> where
  \<open>forward_subsumption_one_wl2 = (\<lambda>C cands L occs D S. do {
  ASSERT (forward_subsumption_one_wl2_pre C cands L S);
  ASSERT (atm_of L \<in> fst occs);
  let ys = occ_list occs L;
  let n = length ys;
  (_, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl2_inv S C cands ys \<^esup> (\<lambda>(i, s). i < n \<and> s = NONE)
    (\<lambda>(i, s). do {
      C' \<leftarrow> mop_occ_list_at occs L i;
      if C' \<notin># dom_m (get_clauses_wl S)
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> subsume_clauses_match2 C' C S D;
       RETURN (i+1, s)
      }
    })
        (0, NONE);
  D \<leftarrow> (if s \<noteq> NONE then mop_ch_remove_all (mset (get_clauses_wl S \<propto> C)) D else RETURN D);
  occs \<leftarrow> (if is_strengthened s then maybe_push_to_occs_list2 C S occs else RETURN occs);
  S \<leftarrow> subsume_or_strengthen_wl C s S;
  RETURN (S, s \<noteq> NONE, occs, D)
 })\<close>

lemma case_wl_split:
  \<open>(case T of (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<Rightarrow> P M N D NE UE NEk UEk NS US N0 U0 Q W) =
  P (get_trail_wl T) (get_clauses_wl T) (get_conflict_wl T) (IsaSAT_Setup.get_unkept_unit_init_clss_wl T)
      (IsaSAT_Setup.get_unkept_unit_learned_clss_wl T) (IsaSAT_Setup.get_kept_unit_init_clss_wl T)
      (IsaSAT_Setup.get_kept_unit_learned_clss_wl T) (get_subsumed_init_clauses_wl T)
      (get_subsumed_learned_clauses_wl T) (get_init_clauses0_wl T) (get_learned_clauses0_wl T)
  (literals_to_update_wl T) (get_watched_wl T)\<close> and
  state_wl_recompose:
  \<open>(get_trail_wl T, get_clauses_wl T, get_conflict_wl T, IsaSAT_Setup.get_unkept_unit_init_clss_wl T,
      IsaSAT_Setup.get_unkept_unit_learned_clss_wl T, IsaSAT_Setup.get_kept_unit_init_clss_wl T,
      IsaSAT_Setup.get_kept_unit_learned_clss_wl T, get_subsumed_init_clauses_wl T,
      get_subsumed_learned_clauses_wl T, get_init_clauses0_wl T, get_learned_clauses0_wl T,
      literals_to_update_wl T, get_watched_wl T) = T\<close>
  by (cases T; auto; fail)+


lemma clause_hash_ref_cong: \<open>set_mset A = set_mset B \<Longrightarrow> clause_hash_ref A = clause_hash_ref B\<close> for A B
  unfolding clause_hash_ref_def
  by auto
lemma remdups_mset_set_mset_cong: \<open>set_mset A = set_mset B \<Longrightarrow> remdups_mset A = remdups_mset B\<close> for A B
  by (simp add: remdups_mset_def)
lemma all_occurrences_cong: \<open>set_mset A = set_mset B \<Longrightarrow> all_occurrences A = all_occurrences B\<close> for A B
  using remdups_mset_set_mset_cong[of A B]
  unfolding all_occurrences_def
  by auto

lemma correct_occurence_list_mono_candsI:
  \<open>correct_occurence_list Sa occs (cands) n \<Longrightarrow>
  correct_occurence_list Sa occs (remove1_mset C cands) n\<close>
  unfolding correct_occurence_list_def
  by (auto intro: inter_mset_empty_remove1_msetI)

lemma correct_occurence_list_mono_candsI2:
  \<open>correct_occurence_list Sa occs (add_mset C cands) n \<Longrightarrow>
  correct_occurence_list Sa occs (cands) n\<close>
  unfolding correct_occurence_list_def
  by auto

lemma correct_occurence_list_size_mono:
  \<open>correct_occurence_list x1h occs cands n \<Longrightarrow> m \<ge> n \<Longrightarrow>
    correct_occurence_list x1h occs cands m\<close>
  by (auto simp: correct_occurence_list_def ball_conj_distrib dest!: multi_member_split)

lemma all_occurrences_remove_dups_atms[simp]:
  \<open>set_mset (all_occurrences (mset_set (set_mset (all_init_atms_st S\<^sub>0))) occs) =
    set_mset (all_occurrences (all_init_atms_st S\<^sub>0) occs)\<close>
  unfolding all_occurrences_def
  by (cases occs) auto

lemma forward_subsumption_one_wl2_forward_subsumption_one_wl:
  fixes S\<^sub>0 C
  defines G: \<open>G \<equiv>  mset (get_clauses_wl S\<^sub>0 \<propto> C)\<close>
  assumes
    \<open>(C, E) \<in> nat_rel\<close> and
    DG: \<open>(D, G) \<in> clause_hash_ref (all_init_atms_st S\<^sub>0)\<close> and
    occs: \<open>correct_occurence_list S\<^sub>0 occs cands n\<close> and
    n: \<open>n\<le> size (get_clauses_wl S\<^sub>0 \<propto> C)\<close> and
    C_occs: \<open>C \<notin># all_occurrences (all_init_atms_st S\<^sub>0) occs\<close> and
    L: \<open>atm_of L \<in># all_init_atms_st S\<^sub>0\<close> and
    \<open>(S\<^sub>0, T\<^sub>0) \<in> Id\<close>
    \<open>(cands, cands') \<in> Id\<close>
  shows \<open>forward_subsumption_one_wl2 C cands L occs D S\<^sub>0 \<le> \<Down>
    (forward_subsumption_one_wl2_rel S\<^sub>0 occs cands n C D)
    (forward_subsumption_one_wl E cands' T\<^sub>0)\<close>
proof -
  have \<open>cands \<inter># mset (occ_list occs L) = {#}\<close>
    using occs L n unfolding correct_occurence_list_def
    by (auto simp: all_occurrences_add_mset inter_mset_empty_distrib_right subset_mset.inf.commute
      dest!: multi_member_split[of \<open>atm_of L\<close>])
  then have [refine]:
    \<open>RETURN (occ_list occs L)
    \<le> \<Down> list_mset_rel (SPEC (forward_subsumption_one_wl_select C cands S\<^sub>0))\<close>
    using occs C_occs L n unfolding forward_subsumption_one_wl_select_def
    by (auto simp: correct_occurence_list_def all_occurrences_add_mset
      forward_subsumption_one_select_def list_mset_rel_def br_def
      dest!: multi_member_split
      intro!: RETURN_RES_refine
      intro: le_trans[OF _ n])
  have [refine]: \<open>(occ_list occs L, ys) \<in> list_mset_rel \<Longrightarrow>
    ((0, NONE), ys, NONE) \<in> {(n, z). z = mset (drop n (occ_list occs L))} \<times>\<^sub>f Id\<close> for ys
    by (auto simp: list_mset_rel_def br_def)
  define ISABELLE_YOU_ARE_SO_STUPID :: \<open>nat multiset \<Rightarrow> _\<close> where
    \<open>ISABELLE_YOU_ARE_SO_STUPID xs = SPEC (\<lambda>C'. C' \<in># xs)\<close> for xs
  have H: \<open>(if s \<noteq> NONE then RETURN ({#} :: nat clause) else RETURN G) =
    RETURN ((if s \<noteq> NONE then ({#} :: nat clause) else G))\<close> for s
    by auto
  have forward_subsumption_one_wl_alt_def:
    \<open>forward_subsumption_one_wl = (\<lambda>C cands S\<^sub>0. do {
    ASSERT (forward_subsumption_one_wl_pre C cands S\<^sub>0);
    ys \<leftarrow> SPEC (forward_subsumption_one_wl_select C cands S\<^sub>0);
    let _ = size ys;
    (xs, s) \<leftarrow>
      WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl_inv S\<^sub>0 C ys \<^esup> (\<lambda>(xs, s). xs \<noteq> {#} \<and> s = NONE)
      (\<lambda>(xs, s). do {
        C'  \<leftarrow>ISABELLE_YOU_ARE_SO_STUPID xs;
        if C' \<notin># dom_m (get_clauses_wl S\<^sub>0)
        then RETURN (remove1_mset C' xs, s)
        else do  {
          s \<leftarrow> subsume_clauses_match C' C (get_clauses_wl S\<^sub>0);
         RETURN (remove1_mset C' xs, s)
        }
      })
      (ys, NONE);
    _ \<leftarrow> RETURN (if s \<noteq> NONE then ({#} :: nat clause) else G);
    let _ = (if is_strengthened s then () else ());
    S \<leftarrow> subsume_or_strengthen_wl C s S\<^sub>0;
    ASSERT
      (literals_are_\<L>\<^sub>i\<^sub>n' S \<and>
       set_mset (all_init_lits_of_wl S) = set_mset (all_init_lits_of_wl S\<^sub>0));
    RETURN (S, s \<noteq> NONE)
      })\<close>
    unfolding forward_subsumption_one_wl_def ISABELLE_YOU_ARE_SO_STUPID_def bind_to_let_conv H
    by (auto split: intro!: bind_cong[OF refl] ext)

  have ISABELLE_YOU_ARE_SO_STUPID: \<open>(x, x') \<in> {(n, z). z = mset (drop n (occ_list occs L))} \<times>\<^sub>f Id \<Longrightarrow>
    case x of (i, s) \<Rightarrow> i < length (occ_list occs L) \<and> s = NONE \<Longrightarrow>
    x' = (x1, x2) \<Longrightarrow>
    x = (x1a, x2a) \<Longrightarrow>
    SPEC (\<lambda>c. (c, occ_list_at occs L x1a) \<in> nat_rel)
      \<le> \<Down> {(a,b). a = b \<and> b = occ_list_at occs L x1a}
      (ISABELLE_YOU_ARE_SO_STUPID x1)\<close> for x1 x1a x x' x2 x2a
      by (cases occs, auto simp: ISABELLE_YOU_ARE_SO_STUPID_def occ_list_at_def occ_list_def
        RES_refine
        intro!: in_set_dropI RES_refine)
  have H: \<open>is_strengthened x2a \<Longrightarrow>
    (xa, ()) \<in> R \<Longrightarrow>
    (xa, if is_strengthened x2 then () else ()) \<in> (if \<not>is_strengthened x2a then {(a,b). a = occs} else R)\<close> for xa x2 x2a R
    by auto
  have itself: \<open>subsume_or_strengthen_wl C s S \<le>\<Down>{(x,y). x = y \<and>
    get_trail_wl x = get_trail_wl S \<and> (\<not>is_subsumed s \<longrightarrow> C\<in>#dom_m (get_clauses_wl x)) \<and>
    (s = NONE \<longrightarrow> x = S) \<and>
    (dom_m (get_clauses_wl x) \<subseteq># dom_m (get_clauses_wl S)) \<and>
    (\<forall>Ca\<in>#dom_m (get_clauses_wl x). Ca\<in>#dom_m (get_clauses_wl S) \<and>  length (get_clauses_wl x \<propto> Ca) \<le> length (get_clauses_wl S \<propto> Ca)) \<and>
    (\<forall>Ca\<in>#dom_m (get_clauses_wl x). Ca\<in>#dom_m (get_clauses_wl S) \<and> set (get_clauses_wl x \<propto> Ca) \<subseteq> set (get_clauses_wl S \<propto> Ca))
    } b\<close> if b: \<open>b = subsume_or_strengthen_wl C s S\<close> and
    S: \<open>forward_subsumption_one_wl_pre C ys S\<close>
    for a b s S ys
  proof -
    have [simp]: \<open>x1 \<in># dom_m b \<Longrightarrow> {#mset (fst x). x \<in># ran_m (fmupd x1 (b \<propto> x1, True) b)#} =
      {#mset (fst x). x \<in># ran_m b#}\<close> for b x1
      by (auto simp: ran_m_def dest!: multi_member_split intro: image_mset_cong)
    have [simp]:
      \<open>get_conflict_wl S = None \<Longrightarrow> (get_trail_wl S, get_clauses_wl S, None, IsaSAT_Setup.get_unkept_unit_init_clss_wl S,
        IsaSAT_Setup.get_unkept_unit_learned_clss_wl S, IsaSAT_Setup.get_kept_unit_init_clss_wl S,
        IsaSAT_Setup.get_kept_unit_learned_clss_wl S, get_subsumed_init_clauses_wl S,
        get_subsumed_learned_clauses_wl S, get_init_clauses0_wl S, get_learned_clauses0_wl S,
        literals_to_update_wl S, get_watched_wl S) = S\<close> for S
      by (cases S) auto
    have [simp]: \<open>C \<notin># remove1_mset C (dom_m S)\<close> for C S
      using distinct_mset_dom[of \<open>S\<close>]
      by (cases \<open>C \<in># dom_m S\<close>) (auto dest!: multi_member_split)
    have H: \<open>mset Ea = remove1_mset (- x21) (mset (get_clauses_wl S \<propto> C)) \<Longrightarrow>
          length (get_clauses_wl S \<propto> C) = length (get_clauses_wl S \<propto> x22) \<Longrightarrow>
      length Ea \<le> length (get_clauses_wl S \<propto> x22)\<close>for Ea x21 S C x22
      by (metis size_Diff1_le size_mset)
    have H2: \<open>mset Ea = remove1_mset (- x21) (mset (get_clauses_wl S \<propto> C)) \<Longrightarrow>
      x \<in> set Ea \<Longrightarrow> x \<in> set (get_clauses_wl S \<propto> C)\<close>for Ea x21 S C x22 x
      by (metis in_diffD in_multiset_in_set)
    show ?thesis
      unfolding subsume_or_strengthen_wl_def b strengthen_clause_wl_def case_wl_split
        state_wl_recompose
      apply refine_vcg
      subgoal
        using S unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
          subsume_or_strengthen_wl_pre_def subsume_or_strengthen_pre_def
        apply -
        apply normalize_goal+
        subgoal for T U
          apply (simp only: split: subsumption.splits)
          apply (intro conjI)
          subgoal
            by refine_vcg
             (auto split: subsumption.splits simp: state_wl_recompose)
          subgoal
            by (auto split: subsumption.splits simp: state_wl_recompose)
          subgoal
            by (auto split: subsumption.splits simp: state_wl_recompose)
          subgoal
            by refine_vcg
              (auto split: subsumption.splits simp: state_wl_recompose
              intro: H H2)
          subgoal
            by (auto split: subsumption.splits simp: state_wl_recompose)
          done
      done
    done
  qed
  have mop_ch_remove_all2:
    \<open>mop_ch_remove_all D C \<le> SPEC(\<lambda>c. (c, {#}) \<in> clause_hash_ref \<A>)\<close>
    if  \<open>(C, D) \<in> clause_hash_ref \<A>\<close> for C D  \<A>
    using that unfolding mop_ch_remove_all_def
    apply refine_vcg
    subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def)
    subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def dest!: multi_member_split)
    subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def)
    done
  have K: \<open>(xa, {#}) \<in> clause_hash_ref (all_init_atms_st S\<^sub>0) \<Longrightarrow> x2 \<noteq> NONE \<Longrightarrow>
    (xa, if x2 \<noteq> NONE then {#} else G) \<in>
    {(xa, b). if x2 \<noteq> NONE then b = {#} \<and> (xa, b)\<in> clause_hash_ref (all_init_atms_st S\<^sub>0)
    else (xa,b) = (D,G)}\<close> for xa x2
    by auto

  have correct_occurence_list_cong:
    \<open>correct_occurence_list T occs ys (length (get_clauses_wl S\<^sub>0 \<propto> C)) \<Longrightarrow>
    set_mset (all_init_atms_st T) = set_mset (all_init_atms_st U) \<Longrightarrow>
    get_trail_wl T = get_trail_wl U \<Longrightarrow>
    dom_m (get_clauses_wl U) \<subseteq># dom_m (get_clauses_wl T) \<Longrightarrow>
    (\<forall>Ca\<in>#dom_m (get_clauses_wl U). Ca\<in>#dom_m (get_clauses_wl T) \<and> length (get_clauses_wl U \<propto> Ca) \<le> length (get_clauses_wl T \<propto> Ca)) \<Longrightarrow>
    (\<forall>Ca\<in>#dom_m (get_clauses_wl U). Ca\<in>#dom_m (get_clauses_wl T) \<and> set (get_clauses_wl U \<propto> Ca) \<subseteq> set (get_clauses_wl T \<propto> Ca)) \<Longrightarrow>
    correct_occurence_list U occs ys (length (get_clauses_wl S\<^sub>0 \<propto> C))\<close> for T U occs ys
    using remdups_mset_set_mset_cong[of \<open>all_init_atms_st T\<close> \<open>all_init_atms_st U\<close>]
      all_occurrences_cong[of \<open>all_init_atms_st T\<close> \<open>all_init_atms_st U\<close>] n
    unfolding correct_occurence_list_def
    apply (cases occs)
    apply (auto)
    apply (meson mset_subset_eqD order_trans)
    apply (meson mset_subset_eqD subsetD)
    done

  have eq: \<open>T\<^sub>0 = S\<^sub>0\<close> \<open>E = C\<close> \<open>cands' = cands\<close>
    using assms by auto
  show ?thesis
    unfolding forward_subsumption_one_wl2_def eq
      forward_subsumption_one_wl_alt_def
    apply (refine_vcg mop_occ_list_at[THEN order_trans] DG mop_ch_remove_all2 occs
      subsume_clauses_match2_subsume_clauses_match maybe_push_to_occs_list2 DG[unfolded G])
    subgoal
      using assms \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
      unfolding forward_subsumption_one_wl2_pre_def by blast
    subgoal
      using assms occs
      by (auto simp: correct_occurence_list_def)
    subgoal for ys x x'
      unfolding forward_subsumption_one_wl2_inv_def
      by (cases x') (auto simp: list_mset_rel_def br_def)
    subgoal by auto
    subgoal using occs L unfolding occ_list_at_pre_def correct_occurence_list_def
      by (cases occs, auto simp: occ_list_def)
    apply (rule ISABELLE_YOU_ARE_SO_STUPID)
    apply assumption+
    subgoal by (cases occs, auto simp: occ_list_at_def occ_list_def in_set_dropI)
    subgoal by (auto simp flip: Cons_nth_drop_Suc occ_list_at_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using G by auto
    subgoal unfolding forward_subsumption_one_wl_pre_def by blast
    subgoal by (auto simp flip: Cons_nth_drop_Suc occ_list_at_def)
    apply (rule K; assumption?)
    subgoal by auto
    subgoal by auto
    subgoal unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by normalize_goal+ simp
    subgoal unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by normalize_goal+ simp
    subgoal unfolding forward_subsumption_one_wl_pre_def by blast
    subgoal unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by normalize_goal+ simp
    subgoal using C_occs occs unfolding correct_occurence_list_def by auto
    apply (rule H; assumption)
    subgoal by auto
    apply (rule itself)
    subgoal by auto
    apply assumption
    subgoal for ys x x' x1 x2 x1a x2a Da _ occsa S Sa
      using occs n
        clause_hash_ref_cong[of \<open>all_init_atms_st S\<^sub>0\<close> \<open>atm_of `# all_init_lits_of_wl Sa\<close>]
        all_occurrences_cong[of \<open>all_init_atms_st S\<^sub>0\<close> \<open>atm_of `# all_init_lits_of_wl Sa\<close>]
      by (auto simp: forward_subsumption_one_wl2_rel_def all_init_atms_st_alt_def
           correct_occurence_list_cong[of S\<^sub>0]
        intro: correct_occurence_list_size_mono intro!: correct_occurence_list_mono_candsI
        simp del: multiset.set_map
        intro: correct_occurence_list_cong
        split: if_splits)
    done
qed

definition try_to_forward_subsume_wl2 :: \<open>nat \<Rightarrow> occurences \<Rightarrow> nat multiset \<Rightarrow> clause_hash \<Rightarrow> nat multiset \<Rightarrow> nat twl_st_wl \<Rightarrow> (occurences \<times> clause_hash \<times> nat multiset \<times> nat twl_st_wl) nres\<close> where
  \<open>try_to_forward_subsume_wl2 C occs cands D shrunken S = do {
  ASSERT (try_to_forward_subsume_wl2_pre C cands shrunken S);
  let n = length (get_clauses_wl S \<propto> C);
  let n = 2 * n;
  ebreak \<leftarrow> RES {_::bool. True};
  (_, changed, _, occs, D, S) \<leftarrow> WHILE\<^sub>T\<^bsup> try_to_forward_subsume_wl2_inv S cands C\<^esup>
    (\<lambda>(i, changed, break, occs, D, S). \<not>break \<and> i < n)
    (\<lambda>(i, changed, break, occs, D, S). do {
      L \<leftarrow> mop_clauses_at (get_clauses_wl S) C (i div 2);
      let L = (if i mod 2 = 0 then L else - L);
      (S, subs, occs, D) \<leftarrow> forward_subsumption_one_wl2 C cands L occs D S;
      ebreak \<leftarrow> RES {_::bool. True};
      RETURN (i+1, subs, subs \<or> ebreak, occs, D, S)
    })
  (0, False, ebreak, occs, D, S);
  ASSERT (\<not>changed \<longrightarrow> C \<in># dom_m (get_clauses_wl S));
  D \<leftarrow> (if \<not>changed then mop_ch_remove_all (mset (get_clauses_wl S \<propto> C)) D else RETURN D);
  add_to_shrunken \<leftarrow> RES (UNIV :: bool set);
  let shrunken = (if add_to_shrunken then add_mset C shrunken else shrunken);
  RETURN (occs, D, shrunken, S)
  }\<close>

definition try_to_forward_subsume_wl2_pre0 :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl2_pre0 G C occs cands D S\<^sub>0 n \<longleftrightarrow>
  correct_occurence_list S\<^sub>0 occs cands n \<and>
  n\<le> length (get_clauses_wl S\<^sub>0 \<propto> C) \<and>
  C \<notin># all_occurrences (all_init_atms_st S\<^sub>0) occs \<and>
  distinct_mset cands \<and>
  C \<in># dom_m (get_clauses_wl S\<^sub>0) \<and>
  G = mset (get_clauses_wl S\<^sub>0 \<propto> C)\<close>

definition try_to_forward_subsume_wl_rel :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl_rel S\<^sub>0 C cands occs n shrunken \<equiv>
  {((occs', D', shrunken', T), U). (T, U) \<in> Id \<and> (D', {#}) \<in> clause_hash_ref (all_init_atms_st T) \<and>
       correct_occurence_list U occs' (remove1_mset C cands) (max (length (get_clauses_wl S\<^sub>0 \<propto> C)) n) \<and>
       shrunken' \<subseteq># add_mset C shrunken \<and>
       all_occurrences (all_init_atms_st U) occs' \<subseteq># add_mset C (all_occurrences  (all_init_atms_st S\<^sub>0) occs)}\<close>

lemma try_to_forward_subsume_wl2_try_to_forward_subsume_wl:
  assumes \<open>(C, E) \<in> nat_rel\<close> and
    DG: \<open>(D, G) \<in> clause_hash_ref (all_init_atms_st T\<^sub>0)\<close> and
    pre: \<open>try_to_forward_subsume_wl2_pre0 G C occs cands D S\<^sub>0 n\<close> and
    \<open>(S\<^sub>0, T\<^sub>0) \<in> Id\<close>
    \<open>(cands, cands') \<in> Id\<close>
  shows \<open>try_to_forward_subsume_wl2 C occs cands D shrunken S\<^sub>0 \<le>
    \<Down>(try_to_forward_subsume_wl_rel S\<^sub>0 C cands occs n shrunken)
    (try_to_forward_subsume_wl E cands' T\<^sub>0)\<close>
proof -
  have eq: \<open>T\<^sub>0 = S\<^sub>0\<close> \<open>E = C\<close> \<open>cands' = cands\<close>
    using assms by auto
  have
    occs: \<open>correct_occurence_list S\<^sub>0 occs cands n\<close> and
    n: \<open>n\<le> length (get_clauses_wl S\<^sub>0 \<propto> C)\<close> and
    C_occs: \<open>C \<notin># all_occurrences (all_init_atms_st T\<^sub>0) occs\<close> and
    \<open>distinct_mset cands\<close> and
    G: \<open>G = mset (get_clauses_wl S\<^sub>0 \<propto> C)\<close>
    using pre unfolding try_to_forward_subsume_wl2_pre0_def eq
   by auto
  have try_to_forward_subsume_wl_alt_def:
  \<open>try_to_forward_subsume_wl C cands S = do {
  ASSERT (try_to_forward_subsume_wl_pre C cands S);
  n \<leftarrow> RES {_::nat. True};
  ebreak \<leftarrow> RES {_::bool. True};
  (_, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup> try_to_forward_subsume_wl_inv S cands C\<^esup>
    (\<lambda>(i, break, S). \<not>break \<and> i < n)
    (\<lambda>(i, break, S). do {
      _ \<leftarrow> SPEC (\<lambda>L :: nat literal. True);
      (S, subs) \<leftarrow> forward_subsumption_one_wl C cands S;
      ebreak \<leftarrow> RES {_::bool. True};
      RETURN (i+1, subs \<or> ebreak, S)
    })
  (0, ebreak, S);
  _ \<leftarrow> RETURN ({#} :: nat clause);
  RETURN S
  }
  \<close> for S
  unfolding try_to_forward_subsume_wl_def nres_monad3
  by auto

  have [refine]: \<open>(ebreak, ebreaka) \<in> bool_rel \<Longrightarrow> try_to_forward_subsume_wl_pre C cands S\<^sub>0 \<Longrightarrow>
    ((0, False, ebreak, occs, D, S\<^sub>0), 0, ebreaka, S\<^sub>0) \<in>
    {((p, changed, ebreak, occs', D', U), (q, ebreak', V)). (p,q)\<in>nat_rel \<and> (\<not>changed \<longrightarrow> C\<in>#dom_m (get_clauses_wl U)) \<and>
      (\<not>changed \<longrightarrow> (D', mset (get_clauses_wl U \<propto> C)) \<in> clause_hash_ref (all_init_atms_st U)) \<and> 
      (changed \<longrightarrow> ebreak \<and> (D', {#}) \<in> clause_hash_ref (all_init_atms_st U)) \<and> 
    (ebreak, ebreak') \<in> bool_rel \<and>
    (\<not>changed \<longrightarrow> correct_occurence_list U occs' cands n \<and> occs' = occs \<and> get_clauses_wl U \<propto> C = get_clauses_wl S\<^sub>0 \<propto> C \<and>
        all_occurrences (all_init_atms_st V) occs' = all_occurrences  (all_init_atms_st S\<^sub>0) occs) \<and>
    (changed \<longrightarrow> correct_occurence_list U occs' (remove1_mset C cands) (max (length (get_clauses_wl S\<^sub>0 \<propto> C)) n) \<and>
       all_occurrences (all_init_atms_st V) occs' \<subseteq># add_mset C (all_occurrences  (all_init_atms_st S\<^sub>0) occs)) \<and>
    U = V}\<close> (is \<open>_ \<Longrightarrow> _ \<Longrightarrow>  _ \<in> ?R\<close>)
    for ebreak ebreaka
    using assms unfolding try_to_forward_subsume_wl_pre_def try_to_forward_subsume_pre_def
    by - (normalize_goal+; simp add: try_to_forward_subsume_wl2_pre0_def try_to_forward_subsume_wl_pre_def)
  have try_to_forward_subsume_wl2_invD:
    \<open>try_to_forward_subsume_wl2_inv S\<^sub>0 cands C x \<Longrightarrow> set_mset (all_init_atms_st (snd (snd (snd (snd (snd x)))))) = set_mset
    (all_init_atms_st S\<^sub>0)\<close> for x
    unfolding try_to_forward_subsume_wl2_inv_def
      try_to_forward_subsume_wl_inv_def
      try_to_forward_subsume_inv_def case_prod_beta
    apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
    by (simp add: all_init_atms_st_alt_def)
  have H: \<open>C \<in># dom_m (get_clauses_wl x2a) \<Longrightarrow> x1 < 2 * length (get_clauses_wl x2a \<propto> C) \<Longrightarrow>
    atm_of (get_clauses_wl x2a \<propto> C ! (x1 div 2))
    \<in> atm_of `
      (set_mset (all_lits_of_m (mset (get_clauses_wl x2a \<propto> C))))\<close> for x1 x2a
    by (rule imageI)
       (auto intro!: in_clause_in_all_lits_of_m nth_mem)


  have K: \<open>try_to_forward_subsume_wl_inv S\<^sub>0 cands C (x1, False, x2a) \<Longrightarrow>
    x1 < 2 * length (get_clauses_wl x2a \<propto> C) \<Longrightarrow>
    atm_of (get_clauses_wl x2a \<propto> C ! (x1 div 2)) \<in># all_init_atms_st x2a\<close> for x1 x2a
    using H[of x2a x1]
    unfolding try_to_forward_subsume_wl_inv_def prod.simps try_to_forward_subsume_inv_def
      literals_are_\<L>\<^sub>i\<^sub>n'_def apply -
    apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l,
      frule rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
    apply (simp add: all_init_atms_st_alt_def)
    apply (auto simp: all_init_atms_st_def ran_m_def all_init_atms_alt_def all_init_atms_def
      all_init_lits_of_wl_def
      all_init_lits_def all_lits_of_mm_add_mset all_learned_lits_of_wl_def
      dest!: multi_member_split[of C]
      simp del: all_init_atms_def[symmetric] all_init_lits_of_wl_def[symmetric])
    by blast

  have K0: \<open>try_to_forward_subsume_wl_inv S\<^sub>0 cands C (x1, False, x2a) \<Longrightarrow>
     atm_of ` set (get_clauses_wl x2a \<propto> C) \<subseteq> set_mset (all_init_atms_st x2a)\<close> for x1 x2a
    unfolding try_to_forward_subsume_wl_inv_def prod.simps try_to_forward_subsume_inv_def
      literals_are_\<L>\<^sub>i\<^sub>n'_def apply -
    apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l,
      frule rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
    apply (simp add: all_init_atms_st_alt_def)
    apply (auto simp: all_init_atms_st_def ran_m_def all_init_atms_alt_def all_init_atms_def
      all_init_lits_of_wl_def
      all_init_lits_def all_lits_of_mm_add_mset all_learned_lits_of_wl_def in_clause_in_all_lits_of_m
      dest!: multi_member_split[of C]
      simp del: all_init_atms_def[symmetric] all_init_lits_of_wl_def[symmetric])
    by (meson image_eqI in_clause_in_all_lits_of_m in_multiset_in_set subsetD)

  have mop_ch_remove_all2:
    \<open>(x, x') \<in> ?R \<Longrightarrow>
    x2 = (x1a, x2a) \<Longrightarrow>
    x' = (x1, x2) \<Longrightarrow>
    x2e = (x1f, x2f) \<Longrightarrow>
    x2d = (x1e, x2e) \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    x = (x1b, x2b) \<Longrightarrow> \<not>x1c \<Longrightarrow>
    mop_ch_remove_all (mset (get_clauses_wl x2f \<propto>  C)) x1f \<le> SPEC(\<lambda>c. (c, {#}) \<in> {(a,b). b = {#} \<and> (a,b) \<in> clause_hash_ref (all_init_atms_st x2f)})\<close>
    for na ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f 
    unfolding mop_ch_remove_all_def
    apply refine_vcg
    subgoal
      using DG G
      by (auto simp: clause_hash_ref_def ch_remove_all_def)
    subgoal by (auto 5 3 simp add: clause_hash_ref_def) 
    subgoal
      by (auto simp: clause_hash_ref_def ch_remove_all_def)
    done
  show ?thesis
    unfolding try_to_forward_subsume_wl2_def try_to_forward_subsume_wl_alt_def eq mop_clauses_at_def
      nres_monad3 bind_to_let_conv try_to_forward_subsume_wl_rel_def
    apply (subst Let_def[of \<open>get_clauses_wl _ \<propto> _ ! _\<close>])
    apply (subst Let_def[of \<open>length (get_clauses_wl _ \<propto> _)\<close>])
    apply (refine_vcg DG[unfolded G]
      forward_subsumption_one_wl2_forward_subsumption_one_wl[where n=n])
    subgoal using assms unfolding try_to_forward_subsume_wl2_pre_def try_to_forward_subsume_wl2_pre0_def by fast
    subgoal by fast
    subgoal using G unfolding try_to_forward_subsume_wl2_inv_def by auto
    subgoal by auto
    subgoal unfolding try_to_forward_subsume_wl_inv_def case_prod_beta try_to_forward_subsume_inv_def
      by normalize_goal+ auto
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by auto
    subgoal using n by auto
    subgoal using C_occs by (auto dest: all_occurrences_cong[OF try_to_forward_subsume_wl2_invD] simp: eq)
    subgoal for a ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
      using K[of x1 x2a] by auto
    subgoal by auto
    subgoal by auto
    subgoal for na ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f uu_ xa x'a x1g x2g x1h x2h x1i x2i
      x1j x2j ebreakb ebreakc
      apply (frule all_occurrences_cong[OF try_to_forward_subsume_wl2_invD])
      apply (clarsimp simp add: forward_subsumption_one_wl2_rel_def)
      apply (auto dest: 
        intro: correct_occurence_list_size_mono[of _ _ _ _ \<open>(max (length (get_clauses_wl S\<^sub>0 \<propto> C)) n)\<close>]
        simp: clause_hash_ref_cong[of \<open>all_init_atms_st x1g\<close>]
        all_occurrences_cong[of \<open>all_init_atms_st x1g\<close> \<open>all_init_atms_st x2a\<close>]
        forward_subsumption_one_wl2_rel_def
        simp: )
     done
   subgoal
     apply simp
     by auto
    apply (rule mop_ch_remove_all2; assumption)
    subgoal by auto
    subgoal for na ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
      using n by (auto simp: eq intro: correct_occurence_list_size_mono correct_occurence_list_mono_candsI)
    done
qed


definition populate_occs_spec where
  \<open>populate_occs_spec S = (\<lambda>(occs, cands).
  all_occurrences (all_init_atms_st S) occs + mset cands \<subseteq># dom_m (get_clauses_wl S) \<and>
  distinct cands \<and> sorted_wrt (\<lambda>a b. length (get_clauses_wl S \<propto> a) \<le> length (get_clauses_wl S \<propto> b)) cands \<and>
  correct_occurence_list S occs (mset cands) 2 \<and>
  (\<forall>C\<in>set cands. \<forall>L\<in> set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L) \<and>
  (\<forall>C\<in>set cands. length (get_clauses_wl S \<propto> C) > 2))\<close>

definition all_lit_clause_unset :: \<open>_\<close> where
  \<open>all_lit_clause_unset S C = do {
    ASSERT (forward_subsumption_all_wl_pre S);
    let b = C \<in># dom_m (get_clauses_wl S);
    if \<not>b then RETURN False
    else do {
       let n = length (get_clauses_wl S \<propto> C);
      (i, all_undef) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, all_undef). i < n \<and> all_undef)
        (\<lambda>(i, _). do {
          ASSERT (i<n);
          L \<leftarrow> mop_clauses_at (get_clauses_wl S) C i;
         ASSERT (L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S));
          val \<leftarrow> mop_polarity_wl S L;
          RETURN (i+1, val = None)
       }) (0, True);
      other \<leftarrow> SPEC (\<lambda>_. True);
      RETURN (all_undef \<and> other)
   }
  }\<close>

lemma forward_subsumption_all_wl_preD: \<open>forward_subsumption_all_wl_pre S \<Longrightarrow> no_dup (get_trail_wl S)\<close>
  unfolding forward_subsumption_all_wl_pre_def
    forward_subsumption_all_pre_def twl_list_invs_def
    twl_struct_invs_def pcdcl_all_struct_invs_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
  by normalize_goal+ simp

lemma all_lit_clause_unset_spec:
  \<open>forward_subsumption_all_wl_pre S \<Longrightarrow>
  all_lit_clause_unset S C \<le> SPEC (\<lambda>b. b \<longrightarrow> C\<in>#dom_m (get_clauses_wl S) \<and> (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L))\<close>
  unfolding all_lit_clause_unset_def mop_clauses_at_def nres_monad3 mop_polarity_wl_def
  apply (refine_vcg WHILET_rule[where R=\<open>measure (\<lambda>(i,_). length (get_clauses_wl S \<propto> C) -i)\<close> and
    I=\<open>\<lambda>(i, all_undef). i \<le> length (get_clauses_wl S \<propto> C) \<and>
    (all_undef \<longleftrightarrow> (\<forall>L\<in>set (take i (get_clauses_wl S \<propto> C)). undefined_lit (get_trail_wl S) L))\<close>])
  subgoal by fast
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of S, THEN \<L>\<^sub>a\<^sub>l\<^sub>l_cong]
    unfolding forward_subsumption_all_wl_pre_def
      forward_subsumption_all_pre_def apply -
    by normalize_goal+
     (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms)
  subgoal by auto
  subgoal by (auto dest: forward_subsumption_all_wl_preD)
  subgoal by (auto dest: forward_subsumption_all_wl_preD)
  subgoal by (auto simp: take_Suc_conv_app_nth polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done


definition populate_occs :: \<open>nat twl_st_wl \<Rightarrow> _ nres\<close> where
  \<open>populate_occs S = do {
    ASSERT (forward_subsumption_all_wl_pre S);
    xs \<leftarrow> SPEC (\<lambda>xs. distinct xs);
    let n = size xs;
    occs \<leftarrow> mop_occ_list_create (set_mset (all_init_atms_st S));
    let cands = [];
    (_, occs, cands) \<leftarrow> WHILE\<^sub>T\<^bsup>populate_occs_inv S xs\<^esup> (\<lambda>(i, occs, cands). i < n)
    (\<lambda>(i, occs, cands). do {
      let C = xs ! i;
      ASSERT (C \<notin> set cands);
      all_undef \<leftarrow> all_lit_clause_unset S C;
      if \<not>all_undef then
        RETURN (i+1, occs, cands)
      else do {
        ASSERT(C \<in># dom_m (get_clauses_wl S));
        let le = length (get_clauses_wl S \<propto> C) in
        if le = 2 then do {
          occs \<leftarrow> push_to_occs_list2 C S occs;
          RETURN (i+1, occs, cands)
        }
        else  do {
          ASSERT(C \<in># dom_m (get_clauses_wl S));
          cand \<leftarrow> RES (UNIV::bool set);
          if cand then RETURN (i+1, occs, cands @ [C])
          else RETURN (i+1, occs, cands)
          }
        }
      }
      )
      (0, occs, cands);
     ASSERT (\<forall>C\<in>set cands. C\<in>#dom_m(get_clauses_wl S) \<and> C\<in>set xs\<and> length (get_clauses_wl S \<propto> C) > 2);
     cands \<leftarrow> SPEC (\<lambda>cands'. mset cands' = mset cands \<and> sorted_wrt (\<lambda>a b. length (get_clauses_wl S \<propto> a) \<le> length (get_clauses_wl S \<propto> b)) cands');
     RETURN (occs, cands)
  }\<close>

lemma forward_subsumption_all_wl_pre_length_ge2:
  \<open>forward_subsumption_all_wl_pre S \<Longrightarrow> C \<in>#dom_m (get_clauses_wl S) \<Longrightarrow> length (get_clauses_wl S \<propto> C) \<ge> 2\<close>
  unfolding forward_subsumption_all_wl_pre_def forward_subsumption_all_pre_def
    twl_struct_invs_def twl_st_inv_alt_def
  by normalize_goal+
   simp

lemma populate_occs_populate_occs_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> \<open>forward_subsumption_all_wl_pre S\<close>
  shows \<open>populate_occs S \<le> \<Down>Id (SPEC(populate_occs_spec S))\<close>
proof -
  have [refine]: \<open>distinct xs \<Longrightarrow>wf (measure (\<lambda>(i, occs, cands). length xs - i))\<close> for xs
    by auto
  have correct_occurence_list:  \<open>\<And>x xa s a b aa ba.
    distinct x \<Longrightarrow>
    populate_occs_inv S x s \<Longrightarrow>
    s = (a, b) \<Longrightarrow>
    b = (aa, ba) \<Longrightarrow>
    correct_occurence_list S aa (mset (drop a x)) 2\<close>
    by (auto simp: populate_occs_inv_def)
  have G0: \<open>A \<subseteq># B \<Longrightarrow> a \<notin># A \<Longrightarrow> a \<in># B \<Longrightarrow> add_mset a A \<subseteq># B\<close> for A B :: \<open>nat multiset\<close> and a
    by (metis add_mset_remove_trivial_eq insert_subset_eq_iff subset_add_mset_notin_subset_mset)
  have G: \<open>distinct x \<Longrightarrow>
    a < length x \<Longrightarrow>
    all_occurrences (all_init_atms_st S) aa + mset ba \<subseteq># mset (take a x) \<Longrightarrow>
    x ! a \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
    all_occurrences (all_init_atms_st S) xc = add_mset (x ! a) (all_occurrences (all_init_atms_st S) aa) \<Longrightarrow>
    all_occurrences (all_init_atms_st S) aa + mset ba \<subseteq># dom_m (get_clauses_wl S) \<Longrightarrow>
    distinct ba \<Longrightarrow>
    correct_occurence_list S aa (add_mset (x ! a) (mset (drop (Suc a) x))) 2 \<Longrightarrow>
    add_mset (x ! a) (all_occurrences (all_init_atms_st S) aa + mset ba) \<subseteq>#     dom_m (get_clauses_wl S)\<close>
    for x xa s a b aa ba xb xc
    apply (rule G0)
    apply auto
    apply (meson correct_occurence_list_def disjunct_not_in union_single_eq_member)
    by (meson distinct_in_set_take_iff in_multiset_in_set less_Suc_eq mset_le_decr_left2 mset_subset_eqD not_less_eq)
  have G': \<open>distinct x \<Longrightarrow>
    a < length x \<Longrightarrow>
    all_occurrences (all_init_atms_st S) aa + mset ba \<subseteq># mset (take a x) \<Longrightarrow>
    x ! a \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
    all_occurrences (all_init_atms_st S) aa + mset ba \<subseteq># dom_m (get_clauses_wl S) \<Longrightarrow>
    distinct ba \<Longrightarrow>
    correct_occurence_list S aa (add_mset (x ! a) (mset (drop (Suc a) x))) 2 \<Longrightarrow>
    add_mset (x ! a) (all_occurrences (all_init_atms_st S) aa + mset ba) \<subseteq># dom_m (get_clauses_wl S)\<close>
    \<open>distinct x \<Longrightarrow>
    a < length x \<Longrightarrow>
    all_occurrences (all_init_atms_st S) aa + mset ba \<subseteq># mset (take a x) \<Longrightarrow>
    x ! a \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
    all_occurrences (all_init_atms_st S) aa + mset ba \<subseteq># dom_m (get_clauses_wl S) \<Longrightarrow>
    distinct ba \<Longrightarrow>
    correct_occurence_list S aa (add_mset (x ! a) (mset (drop (Suc a) x))) 2 \<Longrightarrow> x ! a \<in> set ba \<Longrightarrow> False\<close>
    for x xa s a b aa ba xb xc
    apply (rule G0)
    apply (auto simp add: correct_occurence_list_def)
    by (smt (verit, ccfv_threshold) distinct_in_set_take_iff in_multiset_in_set nat_in_between_eq(2) not_less_eq set_mset_mono subsetD union_iff)+

  show ?thesis
    unfolding populate_occs_def Let_def
    apply (refine_vcg mop_occ_list_create[THEN order_trans] push_to_occs_list2 all_lit_clause_unset_spec)
    subgoal using assms(2) by fast
    apply assumption
    subgoal unfolding populate_occs_inv_def by (auto simp: occurrence_list_def all_occurrences_def correct_occurence_list_def)
    subgoal
      unfolding populate_occs_inv_def by (auto simp: occurrence_list_def take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      dest: subset_mset_imp_subset_add_mset intro: correct_occurence_list_mono_candsI2 intro: G')
    subgoal unfolding populate_occs_inv_def by (auto simp: occurrence_list_def take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      dest: subset_mset_imp_subset_add_mset intro: correct_occurence_list_mono_candsI2)
    subgoal by auto
    subgoal by auto
    apply (rule correct_occurence_list; assumption)
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal unfolding populate_occs_inv_def
      apply auto
      by (metis add.commute distinct_in_set_take_iff mset_subset_eqD mset_subset_eq_add_right nat_neq_iff set_mset_mset)
    subgoal for x xa s a b aa ba xb xc
      unfolding populate_occs_inv_def apply simp
      by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric] intro: G)
    subgoal by auto
    subgoal for x xa s a b aa ba xb xc
      unfolding populate_occs_inv_def by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      intro: correct_occurence_list_mono_candsI2 dest: forward_subsumption_all_wl_pre_length_ge2 intro!: G')
    subgoal by auto
    subgoal unfolding populate_occs_inv_def by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      intro: correct_occurence_list_mono_candsI2 dest: subset_mset_imp_subset_add_mset)
    subgoal by auto
    subgoal by (auto simp: populate_occs_inv_def populate_occs_spec_def correct_occurence_list_def
      dest: mset_eq_setD simp flip: distinct_mset_mset_distinct)
    subgoal by (auto simp: populate_occs_inv_def populate_occs_spec_def correct_occurence_list_def
      dest: mset_eq_setD simp flip: distinct_mset_mset_distinct)
    done
qed

definition forward_subsumption_all_wl2 :: \<open>nat twl_st_wl \<Rightarrow> _ nres\<close> where
  \<open>forward_subsumption_all_wl2 = (\<lambda>S. do {
  ASSERT (forward_subsumption_all_wl_pre S);
  (occs, xs) \<leftarrow> SPEC (populate_occs_spec S);
  let m = length xs;
  D \<leftarrow> mop_ch_create (set_mset (all_init_atms_st S));
  let shrunken = {#};
  (_, occs, D, S, _, shrunken) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_all_wl2_inv S xs \<^esup> (\<lambda>(i, occs, D, S, n, shrunken). i < m \<and> get_conflict_wl S = None)
    (\<lambda>(i, occs, D, S, n, shrunken). do {
       let C = xs!i;
       ASSERT(C\<in>#dom_m (get_clauses_wl S));
       D \<leftarrow> mop_ch_add_all (mset (get_clauses_wl S \<propto> C)) D;
       (occs, D, shrunken, T) \<leftarrow> try_to_forward_subsume_wl2 C occs (mset (drop (i) xs)) D shrunken S;
       RETURN (i+1, occs, D, T, (length (get_clauses_wl S \<propto> C)), shrunken)
    })
    (0, occs, D, S, 2, shrunken);
  ASSERT (fst occs = set_mset (all_init_atms_st S));
  ASSERT (shrunken \<subseteq># mset xs);
  ASSERT (literals_are_\<L>\<^sub>i\<^sub>n' S);
  RETURN S
  }
)\<close>

lemma forward_subsumption_all_wl2_forward_subsumption_all_wl:
  \<open>forward_subsumption_all_wl2 S \<le> \<Down>Id (forward_subsumption_all_wl S)\<close>
proof -
  have forward_subsumption_all_wl_alt_def:
    \<open>forward_subsumption_all_wl = (\<lambda>S. do {
  ASSERT (forward_subsumption_all_wl_pre S);
    xs \<leftarrow> SPEC (forward_subsumption_wl_all_cands S);
  let _ = size xs;
   D \<leftarrow> RETURN ({#} :: nat clause);
   let _ = ({#} :: nat multiset);
  ASSERT (D = {#});
  (xs, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_all_wl_inv S xs \<^esup> (\<lambda>(xs, S). xs \<noteq> {#} \<and> get_conflict_wl S = None)
    (\<lambda>(xs, S). do {
       C \<leftarrow> SPEC (\<lambda>C. C \<in># xs);
       let _ = mset (get_clauses_wl S \<propto> C) + {#};
       T \<leftarrow> try_to_forward_subsume_wl C xs S;
       ASSERT (\<forall>D\<in>#remove1_mset C xs. get_clauses_wl T \<propto> D = get_clauses_wl S \<propto> D);
       RETURN (remove1_mset C xs, T)
    })
    (xs, S);
  RETURN S
  }
           )\<close>
    unfolding forward_subsumption_all_wl_def Let_def by (auto intro!: ext)
  have [refine]: \<open>SPEC
  (\<lambda>xs. mset xs \<subseteq># dom_m (get_clauses_wl S) \<and>
     sorted_wrt (\<lambda>a b. length (get_clauses_wl S \<propto> a) \<le> length (get_clauses_wl S \<propto> b)) xs)
    \<le> \<Down> {(xs,ys). mset xs = ys \<and> mset xs \<subseteq># dom_m (get_clauses_wl S) \<and>
     sorted_wrt (\<lambda>a b. length (get_clauses_wl S \<propto> a) \<le> length (get_clauses_wl S \<propto> b)) xs}
    (SPEC (\<lambda>xs. xs \<subseteq># dom_m (get_clauses_wl S)))\<close>
    by (auto intro!: RES_refine)
  have [refine]: \<open>SPEC (populate_occs_spec S) \<le> \<Down> {((occs,xs), ys).  ys = mset xs \<and> populate_occs_spec S (occs, xs)}(SPEC (forward_subsumption_wl_all_cands S))\<close>
    (is \<open>_ \<le> \<Down> ?populate _\<close>)
    unfolding populate_occs_spec_def prod.simps forward_subsumption_wl_all_cands_def
    by (rule RES_refine)
     (auto dest: mset_le_decr_left2 mset_le_decr_left1)
  define loop_inv where \<open>loop_inv xs = {((i, occs', D :: clause_hash, U, n, shrunken :: nat multiset), (xsa, V)). (U,V)\<in>Id \<and> i \<le> length xs \<and>
    (D, {#}) \<in> clause_hash_ref (all_init_atms_st V) \<and> shrunken \<subseteq># mset (take i xs) \<and>
    (i < length xs \<longrightarrow> length (get_clauses_wl U \<propto> (xs!i)) \<ge> n)\<and>
    correct_occurence_list U occs' xsa n \<and> xsa = mset (drop i xs)}\<close> for xs
  have loop_init: \<open>(occsxs, xsa) \<in> ?populate \<Longrightarrow>
    occsxs = (occs, xs) \<Longrightarrow>
    (D, D') \<in> clause_hash_ref (all_init_atms_st S) \<Longrightarrow>
    D' = {#} \<Longrightarrow>
    forward_subsumption_all_wl_inv S (xsa) (xsa, S) \<Longrightarrow> ((0, occs, D, S, 2, {#}), xsa, S) \<in> loop_inv xs\<close> 
    (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow>_ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?loopinv\<close>) for D occs xsa aa xs occsxs uu D'
    by (cases xs) (auto simp: populate_occs_spec_def loop_inv_def)
  have [refine]: \<open>(a,b) \<in> Id \<Longrightarrow> (c, d) \<in> Id \<Longrightarrow> simplify_clause_with_unit_st_wl a c \<le>\<Down>Id (simplify_clause_with_unit_st_wl b d)\<close> for a b c d
    by auto


  have try_to_forward_subsume_wl2_pre0:  \<open>\<And>x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db shrunken x2d'.
    forward_subsumption_all_wl_pre S \<Longrightarrow>
    (x, xs) \<in> ?populate \<Longrightarrow>
    x = (x1, x2) \<Longrightarrow>
    (D, Da) \<in> clause_hash_ref (all_init_atms_st S) \<Longrightarrow>
    Da = {#} \<Longrightarrow>
    (xa, x')  \<in> loop_inv x2 \<Longrightarrow>
    (case xa of (i, occs, D, S, n, shrunken) \<Rightarrow> i < length x2 \<and> get_conflict_wl S = None) \<Longrightarrow>
    (case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_wl S = None) \<Longrightarrow>
    forward_subsumption_all_wl2_inv S x2 xa \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
    x' = (x1a, x2a) \<Longrightarrow>
    x2d' = (x2e, shrunken) \<Longrightarrow>
    x2d = (x1e, x2d') \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    xa = (x1b, x2b) \<Longrightarrow>
    (x2 ! x1b, C) \<in> nat_rel \<Longrightarrow>
    (Db, mset (get_clauses_wl x2a \<propto> C) + {#}) \<in> clause_hash_ref (all_init_atms_st x1e) \<Longrightarrow>
    try_to_forward_subsume_wl2_pre0 (mset (get_clauses_wl x2a \<propto> C) + {#}) (x2 ! x1b) x1c (mset (drop x1b x2)) Db x1e x2e\<close>
    unfolding forward_subsumption_all_inv_def forward_subsumption_all_wl_inv_def
      forward_subsumption_all_wl2_inv_def loop_inv_def
    apply (hypsubst, unfold prod.simps, normalize_goal+)
    subgoal for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db xb xc
      apply (auto simp add: try_to_forward_subsume_wl2_pre0_def populate_occs_spec_def drop_Suc_nth)
      apply (metis add_mset_disjoint(2) correct_occurence_list_def insert_DiffM union_single_eq_member)
      by (metis add_mset_add_mset_same_iff correct_occurence_list_def distinct_mem_diff_mset
        insert_DiffM set_mset_mset union_single_eq_member)
   done

  have subsumed_postinv: \<open>
    forward_subsumption_all_wl_pre S \<Longrightarrow>
    (x, xs) \<in> ?populate \<Longrightarrow>
    x \<in> Collect (populate_occs_spec S) \<Longrightarrow>
    xs \<in> Collect (forward_subsumption_wl_all_cands S) \<Longrightarrow>
    x = (x1, x2) \<Longrightarrow>
    (xa, x') \<in> loop_inv x2 \<Longrightarrow>
    case xa of (i, occs, D, S, n, shrunken) \<Rightarrow> i < length x2 \<and> get_conflict_wl S = None \<Longrightarrow>
    case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_wl S = None \<Longrightarrow>
    forward_subsumption_all_wl2_inv S x2 xa \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
    x' = (x1a, x2a) \<Longrightarrow>
    x2d' = (x2e, shrunken) \<Longrightarrow>
    x2d = (x1e, x2d') \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    xa = (x1b, x2b) \<Longrightarrow>
    (x2 ! x1b, C) \<in> nat_rel \<Longrightarrow>
    x2 ! x1b \<in># dom_m (get_clauses_wl x1e) \<Longrightarrow>
    inres (mop_ch_add_all (mset (get_clauses_wl x1e \<propto> (x2 ! x1b))) x1d) Db \<Longrightarrow>
    (Db, mset (get_clauses_wl x2a \<propto> C) + {#}) \<in> clause_hash_ref (all_init_atms_st x1e) \<Longrightarrow>
    (xb, Sa) \<in> try_to_forward_subsume_wl_rel x1e (x2 ! x1b) (mset (drop x1b x2)) x1c x2e shrunken \<Longrightarrow>
    \<forall>D\<in>#remove1_mset C x1a. get_clauses_wl Sa \<propto> D = get_clauses_wl x2a \<propto> D \<Longrightarrow>
    xb = (a, b) \<Longrightarrow>
    b = (aa, ba) \<Longrightarrow>
    ba = (ab, bb) \<Longrightarrow>
    ((x1b + 1, a, aa, bb, length (get_clauses_wl x1e \<propto> (x2 ! x1b)), ab), remove1_mset C x1a, Sa)
    \<in> loop_inv x2\<close>
    for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db xb Sa a b aa ba shrunken x2d' ab bb
    unfolding forward_subsumption_all_inv_def forward_subsumption_all_wl_inv_def
      forward_subsumption_all_wl2_inv_def loop_inv_def populate_occs_spec_def mem_Collect_eq
      try_to_forward_subsume_wl_rel_def
    apply (hypsubst, unfold prod.simps, normalize_goal+)
    apply (auto simp add: try_to_forward_subsume_wl2_pre0_def populate_occs_spec_def drop_Suc_nth take_Suc_conv_app_nth
        dest: sorted_wrt_nth_less[of _ _  x1b \<open>Suc x1b\<close>] intro: subset_mset_imp_subset_add_mset)
    by (meson mset_subset_eq_add_mset_cancel subset_mset.dual_order.trans)

  have in_all_lits_in_cls: \<open>xaa \<in> set (get_clauses_wl S \<propto> C) \<Longrightarrow> C \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
    xaa \<in># all_lits_st S\<close> for C S xaa
    by (auto simp: all_lits_st_def all_lits_def ran_m_def all_lits_of_mm_add_mset in_clause_in_all_lits_of_m
      dest!: multi_member_split)

  have in_atms: \<open>forward_subsumption_all_wl_pre S \<Longrightarrow>
    forward_subsumption_all_wl_pre S \<Longrightarrow>
    (x, xs) \<in> {((occs, xs), ys). ys = mset xs \<and> populate_occs_spec S (occs, xs)} \<Longrightarrow>
    x \<in> Collect (populate_occs_spec S) \<Longrightarrow>
    xs \<in> Collect (forward_subsumption_wl_all_cands S) \<Longrightarrow>
    x = (x1, x2) \<Longrightarrow>
    (D, Da) \<in> clause_hash_ref (all_init_atms_st S) \<Longrightarrow>
    Da = {#} \<Longrightarrow>
    (xa, x') \<in> loop_inv x2 \<Longrightarrow>
    case xa of (i, occs, D, S, n, shrunken) \<Rightarrow> i < length x2 \<and> get_conflict_wl S = None \<Longrightarrow>
    case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_wl S = None \<Longrightarrow>
    forward_subsumption_all_wl2_inv S x2 xa \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
    x' = (x1a, x2a) \<Longrightarrow>
    x2d = (x1e, x2d') \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    xa = (x1b, x2b) \<Longrightarrow>
    (x2 ! x1b, C) \<in> nat_rel \<Longrightarrow>
    atms_of (mset (get_clauses_wl x1e \<propto> (x2 ! x1b))) \<subseteq> set_mset (all_init_atms_st x1e)\<close>
    for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C x2d' shrunken
    unfolding forward_subsumption_all_inv_def forward_subsumption_all_wl_inv_alt_def
      forward_subsumption_all_wl2_inv_def loop_inv_def populate_occs_spec_def mem_Collect_eq
      all_init_atms_st_alt_def atms_of_def
    apply (cases x2d', hypsubst, unfold prod.simps, normalize_goal+)
    apply (frule literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[of x1e])
    subgoal
      by (auto simp: all_init_atms_st_alt_def all_atms_st_alt_def drop_Suc_nth
        simp del: all_atms_st_alt_def[symmetric] intro!: imageI
        in_all_lits_in_cls[of _ _ \<open>x2 ! x1b\<close>])
    done
  have distinct: \<open>forward_subsumption_all_wl_pre S \<Longrightarrow>
      forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
      x' = (x1a, x2a) \<Longrightarrow>
     (C', C) \<in> nat_rel \<Longrightarrow>
      C' \<in># dom_m (get_clauses_wl x2a) \<Longrightarrow> 
    distinct_mset (mset (get_clauses_wl x2a \<propto> C))\<close>
    for x' x1a x2a xa x1b x2b x1c x2c x1d x2d x1e x2e x2 C xs C'
    unfolding forward_subsumption_all_wl_inv_alt_def case_prod_beta
      forward_subsumption_all_inv_def
    apply normalize_goal+
    apply (elim rtranclp_cdcl_twl_inprocessing_l_twl_st_l)
    apply assumption+
    unfolding  twl_struct_invs_def twl_st_inv_alt_def
    by (simp add: mset_take_mset_drop_mset')

  show ?thesis
    unfolding forward_subsumption_all_wl_alt_def forward_subsumption_all_wl2_def
    apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
    apply (refine_vcg mop_occ_list_create mop_ch_create mop_ch_add_all
      try_to_forward_subsume_wl2_try_to_forward_subsume_wl
      WHILEIT_refine_with_inv)
    apply (rule loop_init; assumption)
    subgoal unfolding forward_subsumption_all_wl2_inv_def loop_inv_def by auto
    subgoal by (auto simp: loop_inv_def)
    subgoal by (auto simp: in_set_dropI loop_inv_def)
    subgoal
      unfolding loop_inv_def populate_occs_spec_def mem_Collect_eq
        forward_subsumption_all_inv_def forward_subsumption_all_wl_inv_alt_def
        forward_subsumption_all_wl2_inv_def case_prod_beta apply normalize_goal+
      by (auto simp add: forward_subsumption_wl_all_cands_def
          simp flip: Cons_nth_drop_Suc dest: mset_subset_eq_insertD)
    apply (solves \<open>auto simp: loop_inv_def\<close>)
    subgoal by (rule in_atms)
    subgoal by (auto simp: loop_inv_def)
    subgoal by auto
    subgoal apply (rule distinct)
      by  assumption+ (simp add: loop_inv_def case_prod_beta)
    apply (subst clause_hash_ref_cong)
    defer apply assumption
    apply (rule try_to_forward_subsume_wl2_pre0; assumption?)
    subgoal by (auto simp: loop_inv_def)
    subgoal by (auto simp: loop_inv_def)
    subgoal for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2d' x2e shrunken C Db
      xb Sa a b aa ba
      by (rule subsumed_postinv)
    subgoal by (auto simp: loop_inv_def correct_occurence_list_def)
    subgoal by (auto simp: loop_inv_def intro: subset_mset.dual_order.trans[OF mset_take_subseteq])
    subgoal by (auto simp: forward_subsumption_all_wl2_inv_def
      dest!: forward_subsumption_all_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n'D)
    subgoal by (auto simp: loop_inv_def)
    subgoal by (auto simp: loop_inv_def)
    done
qed


subsection \<open>Refinement to isasat.\<close>
definition is_candidate_forward_subsumption where
  \<open>is_candidate_forward_subsumption C N = do {
    ASSERT (C \<in># dom_m N);
    SPEC (\<lambda>b :: bool. b \<longrightarrow> \<not>irred  N C \<and> length (N \<propto> C) \<noteq> 2)
  }\<close>


lemma incr_forward_rounds_st:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow>
  (incr_forward_rounds_st S, S') \<in> twl_st_heur_restart_occs' r u\<close>
  by (simp add: IsaSAT_Restart.all_init_atms_alt_def twl_st_heur_restart_occs_def incr_forward_rounds_st_def)

lemma red_in_dom_number_of_learned_ge1_twl_st_heur_restart_occs:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_occs' r u\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close>
    \<open>arena_status (get_clauses_wl_heur S) C \<noteq> IRRED\<close>
  shows \<open>1 \<le> get_learned_count_number S\<close>
proof -
  have \<open>clss_size_corr_restart (get_clauses_wl T) (IsaSAT_Setup.get_unkept_unit_init_clss_wl T) {#}
  (IsaSAT_Setup.get_kept_unit_init_clss_wl T) (IsaSAT_Setup.get_kept_unit_learned_clss_wl T)
    (get_subsumed_init_clauses_wl T) {#} (get_init_clauses0_wl T) {#} (get_learned_count S)\<close> and
    \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
    using assms(1) unfolding twl_st_heur_restart_occs_def Let_def by auto
  then show ?thesis
    using assms(2-) red_in_dom_number_of_learned_ge1[of C \<open>get_clauses_wl T\<close>]
    by (auto simp: clss_size_corr_restart_def clss_size_def clss_size_lcount_def
      arena_lifting)
qed


lemma red_in_dom_number_of_learned_ge1_twl_st_heur_restart_occs2:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_occs' r u\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close>
    \<open>\<not>irred (get_clauses_wl T) C\<close>
  shows \<open>1 \<le> get_learned_count_number S\<close>
proof -
  have \<open>clss_size_corr_restart (get_clauses_wl T) (IsaSAT_Setup.get_unkept_unit_init_clss_wl T) {#}
  (IsaSAT_Setup.get_kept_unit_init_clss_wl T) (IsaSAT_Setup.get_kept_unit_learned_clss_wl T)
    (get_subsumed_init_clauses_wl T) {#} (get_init_clauses0_wl T) {#} (get_learned_count S)\<close> 
    using assms(1) unfolding twl_st_heur_restart_occs_def Let_def by auto
  then show ?thesis
    using assms(2-) red_in_dom_number_of_learned_ge1[of C \<open>get_clauses_wl T\<close>]
    by (auto simp: clss_size_corr_restart_def clss_size_def clss_size_lcount_def
      arena_lifting)
qed

lemma mop_cch_remove_one_mop_ch_remove_one:
  assumes
    \<open>(L,L')\<in>Id\<close> and
    DD': \<open>(D,D')\<in>clause_hash\<close>
  shows \<open>mop_cch_remove_one L D
    \<le> \<Down> clause_hash
    (mop_ch_remove L' D')\<close>
  using assms
  unfolding mop_cch_remove_one_def mop_ch_remove_def
  apply (refine_vcg,
    auto simp: ch_remove_pre_def clause_hash_def ch_remove_def distinct_mset_remove1_All
    dest: bspec[of _ _ L])
  apply (cases L; auto)
  done


(*TODO: this version is much more logical than the current one*)

lemma mop_arena_status2:
  assumes \<open>(C,C')\<in>nat_rel\<close> \<open>C \<in> vdom\<close>
    \<open>valid_arena arena N vdom\<close>
  shows
    \<open>mop_arena_status arena C
    \<le> SPEC
    (\<lambda>c. (c, C' \<in># dom_m N)
    \<in> {(a,b). (b \<longrightarrow> (a = IRRED \<longleftrightarrow> irred N C) \<and> (a = LEARNED \<longleftrightarrow> \<not>irred N C)) \<and>  (a = DELETED \<longleftrightarrow> \<not>b)})\<close>
  using assms arena_dom_status_iff[of arena N vdom C] unfolding mop_arena_status_def
  by (cases \<open>C \<in># dom_m N\<close>)
    (auto intro!: ASSERT_leI simp: arena_is_valid_clause_vdom_def
     arena_lifting)

lemma isa_subsume_clauses_match2_subsume_clauses_match2:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close> and
    EE': \<open>(E,E')\<in>nat_rel\<close> and
    DD': \<open>(D,D')\<in>clause_hash\<close>
  shows
    \<open>isa_subsume_clauses_match2 C E S D
    \<le> \<Down> Id
    (subsume_clauses_match2 C' E' S' D')\<close>
proof -
  have [refine]: \<open>((0, SUBSUMED_BY C), 0, SUBSUMED_BY C') \<in> nat_rel \<times>\<^sub>r Id\<close>
    using assms by auto
  show ?thesis
    unfolding isa_subsume_clauses_match2_def subsume_clauses_match2_def mop_arena_length_st_def
      Let_def[of \<open>mark_literal_for_unit_deletion _\<close>]
    apply (refine_vcg mop_arena_length[where vdom=\<open>set (get_vdom S)\<close>, THEN fref_to_Down_curry, unfolded comp_def]
      mop_arena_lit2[where vdom=\<open>set (get_vdom S)\<close>] mop_cch_in_mop_ch_in)
    subgoal using assms unfolding isa_subsume_clauses_match2_pre_def by fast
    subgoal unfolding subsume_clauses_match2_pre_def subsume_clauses_match_pre_def
      by auto
    subgoal using SS' CC' EE' by (auto simp: twl_st_heur_restart_occs_def)
    subgoal using SS' CC' arena_lifting(10)[of \<open>get_clauses_wl_heur S\<close> \<open>get_clauses_wl S'\<close> \<open>set (get_vdom S)\<close> C] apply -
      unfolding isa_subsume_clauses_match2_pre_def subsume_clauses_match2_pre_def subsume_clauses_match_pre_def
      by normalize_goal+ (simp add: twl_st_heur_restart_occs_def)
    subgoal using EE' by auto
    subgoal by auto
    subgoal by auto
    subgoal using SS' CC' by (auto simp: twl_st_heur_restart_occs_def)
    subgoal using CC' by auto
    subgoal by auto
    subgoal using DD' by auto
    subgoal by auto
    subgoal by auto
    subgoal using DD' by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using CC' by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma valid_occs_in_vdomI:
  \<open>valid_occs occs (get_aivdom S) \<Longrightarrow> x1 < length (occs ! nat_of_lit L) \<Longrightarrow>
  nat_of_lit L < length occs \<Longrightarrow> cocc_list_at occs L x1 \<in> set (get_vdom S)\<close>
  apply (drule nth_mem)
  unfolding valid_occs_def cocc_list_at_def Union_eq subset_iff
  by (auto dest: spec[of _ \<open>occs ! nat_of_lit L ! x1\<close>] simp: cocc_content_set_def)


definition mop_ch_remove_all_clauses where
  \<open>mop_ch_remove_all_clauses C D = do {
     (_, D) \<leftarrow> WHILE\<^sub>T (\<lambda>(C, D). C \<noteq> {#})
       (\<lambda>(C, D). do {L \<leftarrow> SPEC (\<lambda>L. L \<in># C); D \<leftarrow> mop_ch_remove L D; RETURN (remove1_mset L C, D)})
      (C, D);
    RETURN D
  } \<close>

(*TODO Move*)
lemma diff_mono_mset: "a \<subseteq># b \<Longrightarrow> a - c \<subseteq># b - c"
  by (meson subset_eq_diff_conv subset_mset.dual_order.eq_iff subset_mset.dual_order.trans)

lemma mop_ch_remove_all_clauses_mop_ch_remove_all:
  \<open>mop_ch_remove_all_clauses C D \<le> \<Down>Id (mop_ch_remove_all C D)\<close>
  unfolding mop_ch_remove_all_clauses_def mop_ch_remove_all_def mop_ch_remove_def nres_monad3
  apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i, _). size i)\<close> and
    I = \<open> \<lambda>(C', D').  C' \<subseteq># C \<and>  C' \<subseteq># snd D' \<and> snd D = snd D' + C - C' \<and> fst D = fst D'\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s x b unfolding ch_remove_pre_def by force
  subgoal by auto
  subgoal unfolding ch_remove_def by (auto simp: case_prod_beta diff_mono_mset)
  subgoal
    by (drule multi_member_split)
      (clarsimp simp: ch_remove_def case_prod_beta ch_remove_pre_def)
  subgoal by (auto simp: ch_remove_def case_prod_beta)
  subgoal by (clarsimp dest!: multi_member_split simp: size_Diff_singleton_if)
  subgoal for s a b by (cases b) (auto simp: ch_remove_all_def case_prod_beta)
  done

lemma mop_cch_remove_all_clauses_mop_ch_remove_all_clauses:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close>and
    \<open>(C,C')\<in>nat_rel\<close> and
    DD': \<open>(D,D')\<in>clause_hash\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl S')\<close>
  shows \<open>mop_cch_remove_all_clauses S C D
    \<le> \<Down> clause_hash
    (mop_ch_remove_all (mset (get_clauses_wl S' \<propto> C')) D')\<close>
proof -
  define f where "f C = SPEC (\<lambda>L. L \<in># C)" for C :: \<open>nat clause\<close>
  have eq[simp]: \<open>C' = C\<close>
    using assms by auto
  have valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close>
    using SS' C unfolding arena_is_valid_clause_idx_and_access_def arena_is_valid_clause_idx_def twl_st_heur_restart_occs_def
    by (auto simp: arena_lifting)
  have f: \<open>(x, x')
    \<in> {((n, D), m, D'). (D, D') \<in> clause_hash \<and> m = mset (drop n (get_clauses_wl S' \<propto> C))} \<Longrightarrow>
    case x of (i, D) \<Rightarrow> i < arena_length (get_clauses_wl_heur S) C \<Longrightarrow>
    case x' of (C, D) \<Rightarrow> C \<noteq> {#} \<Longrightarrow>
    x' = (x1, x2) \<Longrightarrow>
    x = (x1a, x2a) \<Longrightarrow>SPEC (\<lambda>c. (c, get_clauses_wl S' \<propto> C ! x1a) \<in> nat_lit_lit_rel)
    \<le> \<Down> {(a,b). a = b \<and> a = get_clauses_wl S' \<propto> C ! x1a} (f x1)\<close> for x1 x1a x2 x2a x x'
    unfolding f_def by (auto intro!: RES_refine in_set_dropI)
  show ?thesis
    apply (rule ref_two_step[OF _ mop_ch_remove_all_clauses_mop_ch_remove_all[unfolded Down_id_eq]])
    unfolding mop_cch_remove_all_clauses_def mop_ch_remove_all_clauses_def mop_arena_length_def
      nres_monad3 bind_to_let_conv f_def[symmetric]
    apply (subst Let_def[of \<open>arena_length _ _\<close>])
    apply (refine_vcg WHILET_refine[where R = \<open>{((n, D), (m, D')). (D,D')\<in> clause_hash \<and>
      m = mset (drop n (get_clauses_wl S' \<propto> C))}\<close>] mop_cch_remove_one_mop_ch_remove_one)
    subgoal using valid C unfolding arena_is_valid_clause_idx_def twl_st_heur_restart_occs_def apply -
      by (rule exI[of _ \<open>get_clauses_wl S'\<close>], auto intro!: exI[of _ \<open>get_vdom S\<close>])
   subgoal using DD' by auto
   subgoal using valid by (auto simp: arena_lifting C)
   subgoal using valid arena_lifting(4,7)[OF valid C] by (force simp:  C)
   apply (rule mop_arena_lit[THEN order_trans])
   apply (rule valid)
   apply (rule C)
   subgoal by auto
   apply (rule refl)
   subgoal using valid by (auto simp: arena_lifting C)
   apply (rule f; assumption)
   subgoal by (auto intro!: in_set_dropI)
   subgoal using DD' by auto
   subgoal by (auto simp flip: Cons_nth_drop_Suc add_mset_remove_trivial_If)
   subgoal by auto
   done
qed

lemma find_best_subsumption_candidate:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    pre0: \<open>push_to_occs_list2_pre C S' occs\<close> and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    le_bound: \<open>length (get_clauses_wl S' \<propto> C) \<le> Suc (unat32_max div 2)\<close>
  shows \<open>find_best_subsumption_candidate C S \<le> SPEC (\<lambda>L. L \<in># mset (get_clauses_wl S' \<propto> C))\<close>
proof -
  have valid: \<open>valid_occs (get_occs S) (get_aivdom S)\<close> and
    arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close>
    using SS' by (auto simp: twl_st_heur_restart_occs_def)
  have
    C: \<open>C \<in># dom_m (get_clauses_wl S')\<close> and
    le: \<open>2 \<le> length (get_clauses_wl S' \<propto> C)\<close> and
    fst: \<open>fst occs = set_mset (all_init_atms_st S')\<close> and
    lits: \<open>atm_of ` set (get_clauses_wl S' \<propto> C) \<subseteq> set_mset (all_init_atms_st S')\<close>
    using pre0 unfolding push_to_occs_list2_pre_def by blast+
  have pre2: \<open>arena_lit_pre (get_clauses_wl_heur S) (C+i)\<close>
    if \<open>i < length (get_clauses_wl S' \<propto> C)\<close> for i
    using that unfolding arena_lit_pre_def apply -
    by (rule exI[of _ C])
     (use SS' arena C le in \<open>auto simp: arena_is_valid_clause_idx_and_access_def intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _ \<open>set (get_vdom S)\<close>]\<close>)

  have pre: \<open>arena_lit_pre (get_clauses_wl_heur S) C\<close>
    unfolding arena_lit_pre_def
    by (rule exI[of _ C])
     (use SS' arena C le in \<open>auto simp: arena_is_valid_clause_idx_and_access_def intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _ \<open>set (get_vdom S)\<close>]\<close>)

  have lit[simp]: \<open>arena_lit (get_clauses_wl_heur S) (C + i) = get_clauses_wl S' \<propto> C ! i\<close>
    if \<open>i < length (get_clauses_wl S' \<propto> C)\<close> for i
    using that C arena by (auto simp: arena_lifting)
  from this[of 0] have [simp]: \<open>arena_lit (get_clauses_wl_heur S) C = get_clauses_wl S' \<propto> C ! 0\<close>
    using le by fastforce
  have [simp]: \<open>arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl S' \<propto> C)\<close>
    using arena C by (auto simp: arena_lifting)
  have H[intro]: \<open>ba \<in> set (get_clauses_wl S' \<propto> C) \<Longrightarrow> nat_of_lit ba < length (get_occs S)\<close> for ba
    using lits occs by (cases ba) (auto simp: map_fun_rel_def occurrence_list_ref_def
      dest!: bspec[of _ _ \<open>ba\<close>] simp flip: fst)
  have [intro]: \<open>nat_of_lit (get_clauses_wl S' \<propto> C ! i) < length (get_occs S)\<close>
    if \<open>i < length (get_clauses_wl S' \<propto> C)\<close> for i
     by (rule H) (metis (no_types, opaque_lifting) access_lit_in_clauses_def nth_mem that)

  show ?thesis
    using le
    unfolding find_best_subsumption_candidate_def mop_arena_lit_def nres_monad3 mop_arena_length_st_def
      mop_arena_length_def mop_arena_lit2_def mop_cocc_list_length_def
    apply (refine_vcg arena WHILET_rule[where R = \<open>measure (\<lambda>(i, _). length (get_clauses_wl S' \<propto> C) - i)\<close> and
      I = \<open> \<lambda>(i, score, L). L \<in> set (get_clauses_wl S' \<propto> C)\<close>])
    subgoal using pre by auto
    subgoal by auto
    subgoal unfolding cocc_list_length_pre_def by auto
    subgoal using C arena unfolding arena_is_valid_clause_idx_def by fast
    subgoal by auto
    subgoal by (use le in \<open>auto intro!: nth_mem\<close>)
    subgoal using le_bound by auto
    subgoal by (auto intro!: pre2)
    subgoal by auto
    subgoal unfolding cocc_list_length_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma find_best_subsumption_candidate_and_push:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    pre0: \<open>push_to_occs_list2_pre C S' occs\<close> and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    le_bound: \<open>length (get_clauses_wl S' \<propto> C) \<le> Suc (unat32_max div 2)\<close>
  shows \<open>find_best_subsumption_candidate_and_push C S \<le> SPEC (\<lambda>(L, push). L \<in># mset (get_clauses_wl S' \<propto> C))\<close>
proof -
  have valid: \<open>valid_occs (get_occs S) (get_aivdom S)\<close> and
    arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close> and
    heur: \<open>heuristic_rel (all_init_atms_st S') (get_heur S)\<close>
    using SS' by (auto simp: twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def)
  have
    C: \<open>C \<in># dom_m (get_clauses_wl S')\<close> and
    le: \<open>2 \<le> length (get_clauses_wl S' \<propto> C)\<close> and
    fst: \<open>fst occs = set_mset (all_init_atms_st S')\<close> and
    lits: \<open>atm_of ` set (get_clauses_wl S' \<propto> C) \<subseteq> set_mset (all_init_atms_st S')\<close>
    using pre0 unfolding push_to_occs_list2_pre_def by blast+
  have pre2: \<open>arena_lit_pre (get_clauses_wl_heur S) (C+i)\<close>
    if \<open>i < length (get_clauses_wl S' \<propto> C)\<close> for i
    using that unfolding arena_lit_pre_def apply -
    by (rule exI[of _ C])
     (use SS' arena C le in \<open>auto simp: arena_is_valid_clause_idx_and_access_def intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _ \<open>set (get_vdom S)\<close>]\<close>)

  have pre: \<open>arena_lit_pre (get_clauses_wl_heur S) C\<close>
    unfolding arena_lit_pre_def
    by (rule exI[of _ C])
     (use SS' arena C le in \<open>auto simp: arena_is_valid_clause_idx_and_access_def intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _ \<open>set (get_vdom S)\<close>]\<close>)

  have lit[simp]: \<open>arena_lit (get_clauses_wl_heur S) (C + i) = get_clauses_wl S' \<propto> C ! i\<close>
    if \<open>i < length (get_clauses_wl S' \<propto> C)\<close> for i
    using that C arena by (auto simp: arena_lifting)
  from this[of 0] have [simp]: \<open>arena_lit (get_clauses_wl_heur S) C = get_clauses_wl S' \<propto> C ! 0\<close>
    using le by fastforce
  have [simp]: \<open>arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl S' \<propto> C)\<close>
    using arena C by (auto simp: arena_lifting)
  have H[intro]: \<open>ba \<in> set (get_clauses_wl S' \<propto> C) \<Longrightarrow> nat_of_lit ba < length (get_occs S)\<close> for ba
    using lits occs by (cases ba) (auto simp: map_fun_rel_def occurrence_list_ref_def
      dest!: bspec[of _ _ \<open>ba\<close>] simp flip: fst)
  have [intro]: \<open>nat_of_lit (get_clauses_wl S' \<propto> C ! i) < length (get_occs S)\<close>
    if \<open>i < length (get_clauses_wl S' \<propto> C)\<close> for i
     by (rule H) (metis (no_types, opaque_lifting) access_lit_in_clauses_def nth_mem that)

  have [intro!]: \<open>is_marked_added_heur_pre (get_heur S) (atm_of L)\<close>
    if \<open>L \<in> set (get_clauses_wl S' \<propto> C)\<close> for L
  proof -
    have \<open>atm_of L \<in> atm_of ` set (get_clauses_wl S' \<propto> C)\<close>
      using that by auto
    then have \<open>atm_of L \<in># all_init_atms_st S'\<close>
      using lits by auto
    then show ?thesis
      using heur lits that
      unfolding is_marked_added_heur_pre_def
      by (auto simp: is_marked_added_heur_pre_stats_def heuristic_rel_def phase_saving_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset atms_of_def
        heuristic_rel_stats_def dest!: multi_member_split)
  qed
  show ?thesis
    using le
    unfolding find_best_subsumption_candidate_and_push_def mop_arena_lit_def nres_monad3 mop_arena_length_st_def
      mop_arena_length_def mop_arena_lit2_def mop_cocc_list_length_def mop_is_marked_added_heur_def
    apply (refine_vcg arena WHILET_rule[where R = \<open>measure (\<lambda>(i, _). length (get_clauses_wl S' \<propto> C) - i)\<close> and
      I = \<open> \<lambda>(i, score, L, _). L \<in> set (get_clauses_wl S' \<propto> C)\<close>])
    subgoal using pre by auto
    subgoal by auto
    subgoal unfolding cocc_list_length_pre_def by auto
    subgoal using C arena unfolding arena_is_valid_clause_idx_def by fast
    subgoal by auto
    subgoal by (use le in \<open>auto intro!: nth_mem\<close>)
    subgoal using le_bound by auto
    subgoal by (auto intro!: pre2)
    subgoal by auto
    subgoal unfolding cocc_list_length_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma twl_st_heur_restart_occs_set_occsI:
  \<open>(S,S')\<in>twl_st_heur_restart_occs \<Longrightarrow> valid_occs occs (get_aivdom S) \<Longrightarrow> (set_occs_wl_heur occs S, S') \<in> twl_st_heur_restart_occs\<close>
  by (auto simp: twl_st_heur_restart_occs_def)


lemma valid_occs_append:
  \<open>C \<in> set (get_vdom_aivdom vdm) \<Longrightarrow>
  C \<notin># cocc_content coccs \<Longrightarrow> valid_occs coccs vdm \<Longrightarrow> nat_of_lit La < length coccs \<Longrightarrow> valid_occs (cocc_list_append C coccs La) vdm\<close>
  by (auto simp: valid_occs_def in_set_upd_eq[of \<open>nat_of lit La\<close> coccs])


lemma in_cocc_content_iff: \<open>C \<in># cocc_content occs \<longleftrightarrow> (\<exists>xs. xs \<in> set occs \<and> C \<in> set xs)\<close>
  by (induction occs) auto

lemma notin_all_occurrences_notin_cocc: \<open>(occs, occs') \<in> occurrence_list_ref \<Longrightarrow> finite (fst occs') \<Longrightarrow> C \<notin># all_occurrences (mset_set (fst occs')) occs' \<Longrightarrow> C \<notin># cocc_content occs\<close>
  apply (auto simp: occurrence_list_ref_def all_occurrences_def image_Un map_fun_rel_def image_image
    in_cocc_content_iff in_set_conv_nth)
  apply (subgoal_tac \<open>ia div 2 \<in> x\<close>)
  defer
  subgoal for x y i ia
    by (drule_tac x=\<open>ia\<close> in spec) auto
  subgoal for x y i ia
    apply (drule_tac x= \<open>if even ia then (ia, Pos (ia div 2)) else (ia, Neg (ia div 2))\<close> in bspec)
    apply auto
    apply (rule_tac x=\<open>ia div 2\<close> in image_eqI)
    apply auto
    by (auto split: if_splits dest: spec[of _ ia])
  done

lemma set_mset_cocc_content_set[simp]: \<open>set_mset (cocc_content occs) = cocc_content_set occs\<close>
  by (auto simp: cocc_content_set_def in_mset_sum_list_iff)

lemma isa_push_to_occs_list_st_push_to_occs_list2:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close>and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    C: \<open>C \<in> set (get_vdom S)\<close> and
    length: \<open>length (get_clauses_wl S' \<propto> C) \<le> Suc (unat32_max div 2)\<close>
  shows \<open>isa_push_to_occs_list_st C S
    \<le> \<Down> {(U, occs'). (get_occs U, occs') \<in> occurrence_list_ref \<and> (U, S') \<in> twl_st_heur_restart_occs' r u \<and> get_aivdom U = get_aivdom S} (push_to_occs_list2 C' S' occs)\<close>
proof -
  have eq: \<open>C' = C\<close>
    using CC' by auto
  have  push_to_occs_list2_alt_def:
  \<open>push_to_occs_list2 C S occs = do {
     ASSERT (push_to_occs_list2_pre C S occs);
     L \<leftarrow> SPEC (\<lambda>L. L \<in># mset (get_clauses_wl S \<propto> C));
     ASSERT (occ_list_append_pre occs L);
     occs \<leftarrow> mop_occ_list_append C occs L;
     RETURN occs
  }\<close> for C S occs
    unfolding push_to_occs_list2_def mop_occ_list_append_def
    apply (subst (3)conj_absorb[symmetric])
    unfolding summarize_ASSERT_conv[symmetric] by auto
  have valid: \<open>valid_occs (get_occs S) (get_aivdom S)\<close>
    using SS' unfolding twl_st_heur_restart_occs_def by auto
  have length_bounded: \<open>length (get_occs S ! nat_of_lit L) < length (get_clauses_wl_heur S)\<close>
    if
      push: \<open>push_to_occs_list2_pre C S' occs\<close> and
      \<open>(L, La) \<in> nat_lit_lit_rel\<close> and
      \<open>La \<in> {L. L \<in># mset (get_clauses_wl S' \<propto> C)}\<close> and
      pre: \<open>occ_list_append_pre occs La\<close>
      for L La
  proof -
    define n where \<open>n = get_occs S ! nat_of_lit L\<close>
    have arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close> and
      occs: \<open>valid_occs (get_occs S) (get_aivdom S)\<close> and
      aivdom: \<open>aivdom_inv_dec (get_aivdom S) (dom_m (get_clauses_wl S'))\<close>
      using SS' unfolding twl_st_heur_restart_occs_def
      by fast+
    have H: \<open>add_mset C (cocc_content (get_occs S)) \<subseteq># mset (get_vdom S)\<close>
      using occs notin_all_occurrences_notin_cocc[OF assms(3), of C] unfolding valid_occs_def apply -
      by (subst distinct_subseteq_iff[symmetric])
       (use push C in \<open>auto simp: push_to_occs_list2_pre_def\<close>)
    have \<open>nat_of_lit L < length (get_occs S)\<close>
      using pre that(2) assms(3) unfolding occ_list_append_pre_def by (cases L) (auto simp: occurrence_list_ref_def map_fun_rel_def
        dest!: bspec[of _ _ L])
    from nth_mem[OF this] have \<open>length (get_occs S ! nat_of_lit L) < length (get_vdom S)\<close>
      using multi_member_split[of \<open>get_occs S ! nat_of_lit L\<close> \<open>mset (get_occs S)\<close>] H[THEN size_mset_mono]
      by (auto dest!: split_list simp: n_def[symmetric])
    moreover have \<open>length (get_vdom S) \<le> length (get_clauses_wl_heur S)\<close>
      using valid_arena_vdom_le(2)[OF arena] aivdom unfolding aivdom_inv_dec_alt_def
      by (simp add: distinct_card)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding isa_push_to_occs_list_st_def push_to_occs_list2_alt_def eq
    apply (refine_vcg find_best_subsumption_candidate[OF SS' _ occs]
      mop_cocc_list_append_mop_occ_list_append occs)
    subgoal using length by auto
    subgoal by (rule length_bounded)
    subgoal by auto
    subgoal using SS' C valid notin_all_occurrences_notin_cocc[OF occs, of C]
      by (auto 9 2 intro!: twl_st_heur_restart_occs_set_occsI
      intro!: valid_occs_append
      simp: push_to_occs_list2_pre_def)
    done
qed

lemma isa_maybe_push_to_occs_list_st_push_to_occs_list2:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close>and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    C: \<open>C \<in> set (get_vdom S)\<close> and
    length: \<open>length (get_clauses_wl S' \<propto> C) \<le> Suc (unat32_max div 2)\<close>
  shows \<open>isa_maybe_push_to_occs_list_st C S
    \<le> \<Down> {(U, occs'). (get_occs U, occs') \<in> occurrence_list_ref \<and> (U, S') \<in> twl_st_heur_restart_occs' r u \<and> get_aivdom U = get_aivdom S} (maybe_push_to_occs_list2 C' S' occs)\<close>
proof -
  have eq: \<open>C' = C\<close>
    using CC' by auto
  have  maybe_push_to_occs_list2_alt_def:
  \<open>maybe_push_to_occs_list2 C S occs = do {
    ASSERT (push_to_occs_list2_pre C S occs);
    b \<leftarrow> SPEC (\<lambda>_. True);
   if b then do {
     L \<leftarrow> SPEC (\<lambda>L. L \<in># mset (get_clauses_wl S \<propto> C));
     ASSERT (occ_list_append_pre occs L);
     occs \<leftarrow> mop_occ_list_append C occs L;
     RETURN occs
   } else RETURN occs
  }\<close> for C S occs
    unfolding maybe_push_to_occs_list2_def mop_occ_list_append_def
    apply (subst (3)conj_absorb[symmetric])
    unfolding nres_monad3
    unfolding summarize_ASSERT_conv[symmetric] 
    by (auto cong: if_cong intro: bind_cong[OF refl] simp: bind_ASSERT_eq_if)

  have valid: \<open>valid_occs (get_occs S) (get_aivdom S)\<close>
    using SS' unfolding twl_st_heur_restart_occs_def by auto
  have length_bounded: \<open>length (get_occs S ! nat_of_lit L) < length (get_clauses_wl_heur S)\<close>
    if
      push: \<open>push_to_occs_list2_pre C S' occs\<close> and
      \<open>(L, La) \<in> nat_lit_lit_rel\<close> and
      \<open>(x, b) \<in> {((L, push), push'). L \<in># mset (get_clauses_wl S' \<propto> C) \<and> push = push'}\<close>
      \<open>x = (L, x2)\<close> and
      pre: \<open>occ_list_append_pre occs La\<close>
      for L La x1 b x2 x
  proof -
    define n where \<open>n = get_occs S ! nat_of_lit L\<close>
    have arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close> and
      occs: \<open>valid_occs (get_occs S) (get_aivdom S)\<close> and
      aivdom: \<open>aivdom_inv_dec (get_aivdom S) (dom_m (get_clauses_wl S'))\<close>
      using SS' unfolding twl_st_heur_restart_occs_def
      by fast+
    have H: \<open>add_mset C (cocc_content (get_occs S)) \<subseteq># mset (get_vdom S)\<close>
      using occs notin_all_occurrences_notin_cocc[OF assms(3), of C] unfolding valid_occs_def apply -
      by (subst distinct_subseteq_iff[symmetric])
       (use push C in \<open>auto simp: push_to_occs_list2_pre_def\<close>)
    have \<open>nat_of_lit L < length (get_occs S)\<close>
      using pre that(2) assms(3) unfolding occ_list_append_pre_def by (cases L) (auto simp: occurrence_list_ref_def map_fun_rel_def
        dest!: bspec[of _ _ L])
    from nth_mem[OF this] have \<open>length (get_occs S ! nat_of_lit L) < length (get_vdom S)\<close>
      using multi_member_split[of \<open>get_occs S ! nat_of_lit L\<close> \<open>mset (get_occs S)\<close>] H[THEN size_mset_mono]
      by (auto dest!: split_list simp: n_def[symmetric])
    moreover have \<open>length (get_vdom S) \<le> length (get_clauses_wl_heur S)\<close>
      using valid_arena_vdom_le(2)[OF arena] aivdom unfolding aivdom_inv_dec_alt_def
      by (simp add: distinct_card)
    finally show ?thesis .
  qed
  have find_best_subsumption_candidate_and_push:
   \<open>find_best_subsumption_candidate_and_push C S \<le> \<Down> {((L, push), push'). L \<in># mset (get_clauses_wl S' \<propto> C)\<and> push = push'} (SPEC (\<lambda>_. True))\<close>
   if
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    pre0: \<open>push_to_occs_list2_pre C S' occs\<close> and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    le_bound: \<open>length (get_clauses_wl S' \<propto> C) \<le> Suc (unat32_max div 2)\<close>
   by (rule find_best_subsumption_candidate_and_push[OF that, THEN order_trans]) (auto simp: conc_fun_RES)
  show ?thesis
    unfolding isa_maybe_push_to_occs_list_st_def maybe_push_to_occs_list2_alt_def eq
    apply (refine_vcg find_best_subsumption_candidate_and_push[OF SS' _ occs]
      mop_cocc_list_append_mop_occ_list_append occs)
    subgoal using length by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule length_bounded)
    subgoal by auto
    subgoal using SS' C valid notin_all_occurrences_notin_cocc[OF occs, of C]
      by (auto 9 2 intro!: twl_st_heur_restart_occs_set_occsI
      intro!: valid_occs_append
      simp: push_to_occs_list2_pre_def)
    subgoal using SS' C valid occs by auto
    done
qed

lemma subsumption_cases_lhs:
  assumes
    \<open>(a,a')\<in>Id\<close>
    \<open>\<And>b b'. a = SUBSUMED_BY b \<Longrightarrow> a' = SUBSUMED_BY b' \<Longrightarrow> f b \<le> \<Down>S (f' b')\<close>
    \<open>\<And>b b' c c'. a = STRENGTHENED_BY b c \<Longrightarrow> a' = STRENGTHENED_BY b' c' \<Longrightarrow> g b c \<le> \<Down>S (g' b' c')\<close>
    \<open>\<And>b b' c c'. a = NONE \<Longrightarrow> a' = NONE \<Longrightarrow> h \<le> \<Down>S h'\<close>
  shows \<open>(case a of SUBSUMED_BY b \<Rightarrow> f b | STRENGTHENED_BY b c \<Rightarrow> g b c | NONE \<Rightarrow> h) \<le>\<Down> S
     (case a' of SUBSUMED_BY b \<Rightarrow> f' b| STRENGTHENED_BY b c \<Rightarrow> g' b c | NONE \<Rightarrow> h')\<close>
  using assms by (auto split: subsumption.splits)


definition arena_promote_st_wl :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>arena_promote_st_wl = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q) C.
  (M, fmupd C (N \<propto> C, True) N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q))\<close>

lemma clss_size_corr_restart_promote:
  \<open>clss_size_corr_restart b d {#} f g h {#} j {#} (lcount) \<Longrightarrow>
   \<not>irred b C \<Longrightarrow> C \<in># dom_m b \<Longrightarrow>
    clss_size_corr_restart (fmupd C (b \<propto> C, True) b) d {#} f g h {#} j {#}
  (clss_size_decr_lcount (lcount))\<close>
  unfolding clss_size_corr_restart_def
  by (auto simp: clss_size_decr_lcount_def clss_size_def
    learned_clss_l_mapsto_upd_in_irrelev size_remove1_mset_If)

lemma vdom_m_promote_same:
  \<open>C \<in># dom_m b \<Longrightarrow> vdom_m A m (fmupd C (b \<propto> C, True) b) =  vdom_m A m ( b)\<close>
  by (auto simp: vdom_m_def)

lemma mop_arena_promote_st_spec:
  assumes T: \<open>(S, T) \<in> twl_st_heur_restart_occs' r u\<close> and
   C: \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    irred: \<open>\<not>irred (get_clauses_wl T) C\<close> and
    eq: \<open>set_mset (all_init_atms_st (arena_promote_st_wl T C)) = set_mset (all_init_atms_st T)\<close>
  shows \<open>mop_arena_promote_st S C \<le> SPEC (\<lambda>U. (U, arena_promote_st_wl T C)\<in>{(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs S \<and> get_aivdom U = get_aivdom S})\<close>
proof -
    have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
      by auto
    have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
      by auto

    note cong =  trail_pol_cong[of _ _ \<open>(get_trail_wl_heur S, get_trail_wl T)\<close>]
      heuristic_rel_cong[of _ _ \<open>get_heur S\<close>]
      option_lookup_clause_rel_cong[of _ _ \<open>(get_conflict_wl_heur S, get_conflict_wl T)\<close>]
      isa_vmtf_cong[of _ _ \<open>get_vmtf_heur S\<close>]
      vdom_m_cong[THEN H, of _ _ _ \<open>get_watched_wl T\<close> \<open>get_clauses_wl (T)\<close>]
      isasat_input_nempty_cong[THEN iffD1]
      isasat_input_bounded_cong[THEN iffD1]
       cach_refinement_empty_cong[THEN H', of _ _ \<open>get_conflict_cach S\<close>]
       phase_saving_cong[THEN H']
       \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
      D\<^sub>0_cong[THEN H]
      map_fun_rel_D\<^sub>0_cong[of _ _ \<open>(get_watched_wl_heur S, get_watched_wl T)\<close>]
      vdom_m_cong[symmetric, of _ _ \<open>get_watched_wl T\<close> \<open>get_clauses_wl (T)\<close>]
      \<L>\<^sub>a\<^sub>l\<^sub>l_cong isasat_input_nempty_cong
  note cong = cong[OF eq[symmetric]]
  have valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close> and
    size: \<open>clss_size_corr_restart (get_clauses_wl T)
    (IsaSAT_Setup.get_unkept_unit_init_clss_wl T) {#}
    (IsaSAT_Setup.get_kept_unit_init_clss_wl T)
    (IsaSAT_Setup.get_kept_unit_learned_clss_wl T) (get_subsumed_init_clauses_wl T) {#}
    (get_init_clauses0_wl T) {#} (get_learned_count S)\<close>
    using T unfolding twl_st_heur_restart_occs_def by fast+
  then have irred': \<open>arena_status (get_clauses_wl_heur S) C \<noteq> IRRED\<close>
    using irred by (simp add: C arena_lifting(24))
  have 1: \<open>1 \<le> get_learned_count_number S\<close>
    by (rule red_in_dom_number_of_learned_ge1_twl_st_heur_restart_occs[OF T C irred'])
  have 2: \<open>arena_is_valid_clause_idx (get_clauses_wl_heur S) C\<close>
    using C valid unfolding arena_is_valid_clause_idx_def by auto
  have valid': \<open>valid_arena (arena_set_status (get_clauses_wl_heur S) C IRRED)
    (fmupd C (get_clauses_wl T \<propto> C, True) (get_clauses_wl T)) (set (get_vdom S))\<close>
    by (rule valid_arena_arena_set_status[OF valid])
      (use C in auto)
  show ?thesis
    unfolding mop_arena_promote_st_def mop_arena_set_status_def
      nres_monad3
    apply refine_vcg
    subgoal by (rule 1)
    subgoal by (rule 2)
    subgoal
      apply (cases T)
      using T C valid' irred vdom_m_promote_same cong[unfolded all_init_atms_st_def] cong[unfolded all_init_atms_st_def]
      by (auto simp add: twl_st_heur_restart_occs_def arena_promote_st_wl_def
        clss_size_corr_restart_promote vdom_m_promote_same simp flip: learned_clss_count_def)
   done
qed

definition mark_garbage_wl2 :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>mark_garbage_wl2 = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q).
  (M, fmdrop C N, D, NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
     (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, WS, Q))\<close>

definition mark_garbage_wl_no_learned_reset :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>mark_garbage_wl_no_learned_reset = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q).
  (M, fmdrop C N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q))\<close>

definition add_clauses_to_subsumed_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>add_clauses_to_subsumed_wl = (\<lambda>C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q).
  (M, N, D, NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
     (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, WS, Q))\<close>

lemma subsume_or_strengthen_wl_alt_def[unfolded Down_id_eq]:
  \<open>\<Down>Id (subsume_or_strengthen_wl C s T) \<ge> do {
   ASSERT(subsume_or_strengthen_wl_pre C s T);
   (case s of
     NONE \<Rightarrow> RETURN T
  | SUBSUMED_BY C' \<Rightarrow> do {
       let _ = C \<in>#dom_m (get_clauses_wl T);
       let _ = C' \<in>#dom_m (get_clauses_wl T);
       let _ = log_clause T C;
       let U = mark_garbage_wl2 C T;
       let V = (if \<not>irred (get_clauses_wl T) C' \<and> irred (get_clauses_wl T) C then arena_promote_st_wl U C' else U);
       ASSERT (set_mset (all_init_atms_st V) = set_mset (all_init_atms_st T));
       let V = V;
       RETURN V
     }
   | STRENGTHENED_BY L C' \<Rightarrow> strengthen_clause_wl C C' L T)
         }\<close>
proof -
  have subsume_or_strengthen_wl_def:
  \<open>subsume_or_strengthen_wl = (\<lambda>C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
   ASSERT(subsume_or_strengthen_wl_pre C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
   (case s of
     NONE \<Rightarrow> RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)
   | SUBSUMED_BY C' \<Rightarrow> do {
       let _ = ();
       let T = (M, fmdrop C (if \<not>irred N C' \<and> irred N C then fmupd C' (N \<propto> C', True) N else N), D,
          NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
         (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, Q, W);
        ASSERT (set_mset (all_init_atms_st T) = set_mset (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)));
        RETURN T
     }
   | STRENGTHENED_BY L C' \<Rightarrow> strengthen_clause_wl C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))
         })\<close>
    unfolding subsume_or_strengthen_wl_def Let_def by auto
  show ?thesis
    unfolding subsume_or_strengthen_wl_def
      case_wl_split state_wl_recompose
    apply (refine_vcg subsumption_cases_lhs)
    subgoal by auto
    subgoal
      by (cases T)
        (auto simp: arena_promote_st_wl_def mark_garbage_wl2_def state_wl_l_def fmdrop_fmupd
        subsume_or_strengthen_wl_pre_def subsume_or_strengthen_pre_def)
    subgoal
      by (cases T)
        (auto simp: arena_promote_st_wl_def mark_garbage_wl2_def state_wl_l_def fmdrop_fmupd
        subsume_or_strengthen_wl_pre_def subsume_or_strengthen_pre_def)
    subgoal by auto
    done
qed

lemma mark_garbage_wl2_simp[simp]:
  \<open>get_trail_wl (mark_garbage_wl2 C S) = get_trail_wl S\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_init_clss_wl (mark_garbage_wl2 C S) = IsaSAT_Setup.get_unkept_unit_init_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_init_clss_wl (mark_garbage_wl2 C S) = IsaSAT_Setup.get_kept_unit_init_clss_wl S\<close>
  \<open>irred (get_clauses_wl S) C \<Longrightarrow>
    get_subsumed_init_clauses_wl (mark_garbage_wl2 C S) = add_mset (mset (get_clauses_wl S \<propto> C)) (get_subsumed_init_clauses_wl S)\<close>
  \<open>\<not>irred (get_clauses_wl S) C \<Longrightarrow>
    get_subsumed_init_clauses_wl (mark_garbage_wl2 C S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_learned_clss_wl (mark_garbage_wl2 C S) = IsaSAT_Setup.get_unkept_unit_learned_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_learned_clss_wl (mark_garbage_wl2 C S) = IsaSAT_Setup.get_kept_unit_learned_clss_wl S\<close>
  \<open>irred (get_clauses_wl S) C \<Longrightarrow>
  get_subsumed_learned_clauses_wl (mark_garbage_wl2 C S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>\<not>irred (get_clauses_wl S) C \<Longrightarrow>
  get_subsumed_learned_clauses_wl (mark_garbage_wl2 C S) = add_mset (mset (get_clauses_wl S \<propto> C)) (get_subsumed_learned_clauses_wl S)\<close>
  \<open>literals_to_update_wl (mark_garbage_wl2 C S) = literals_to_update_wl S\<close>
  \<open>get_watched_wl (mark_garbage_wl2 C S) = get_watched_wl S\<close>
  \<open>get_clauses_wl (mark_garbage_wl2 C S) = fmdrop C (get_clauses_wl S)\<close>
  \<open>get_init_clauses0_wl (mark_garbage_wl2 C S) = get_init_clauses0_wl (S)\<close>
  \<open>get_learned_clauses0_wl (mark_garbage_wl2 C S) = get_learned_clauses0_wl (S)\<close>
  \<open>get_conflict_wl (mark_garbage_wl2 C S) = get_conflict_wl S\<close>
  apply (solves \<open>cases S; auto simp: mark_garbage_wl2_def\<close>)+
  done

lemma mark_garbage_wl2_simp2[simp]:
  \<open>C \<in>#dom_m (get_clauses_wl S) \<Longrightarrow> all_init_atms_st (mark_garbage_wl2 C S) = all_init_atms_st (S)\<close>
  by (cases S)
   (auto simp: mark_garbage_wl2_def all_init_atms_st_def all_init_atms_def all_init_lits_def
    learned_clss_l_mapsto_upd_in_irrelev size_remove1_mset_If init_clss_l_fmdrop_if image_mset_remove1_mset_if
    simp del: all_init_atms_def[symmetric]
    cong: image_mset_cong2 filter_mset_cong2)

definition remove_lit_from_clause_wl :: \<open>_\<close> where
  \<open>remove_lit_from_clause_wl C L' = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
  (M, fmupd C (remove1 L' (N \<propto> C), irred N C) N, D, NE, UE, NEk, UEk,
    (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
    (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, Q, W))\<close>

lemma remove_lit_from_clauses_wl_simp[simp]:
  \<open>C \<in># dom_m (get_clauses_wl S) \<Longrightarrow> dom_m (get_clauses_wl (remove_lit_from_clause_wl C L' S)) = dom_m (get_clauses_wl S)\<close>
  \<open>get_trail_wl (remove_lit_from_clause_wl C L' S) = get_trail_wl S\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_init_clss_wl (remove_lit_from_clause_wl C L' S) = IsaSAT_Setup.get_unkept_unit_init_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_init_clss_wl (remove_lit_from_clause_wl C L' S) = IsaSAT_Setup.get_kept_unit_init_clss_wl S\<close>
  \<open>irred (get_clauses_wl S) C \<Longrightarrow>
    get_subsumed_init_clauses_wl (remove_lit_from_clause_wl C L' S) = add_mset (mset (get_clauses_wl S \<propto> C)) (get_subsumed_init_clauses_wl S)\<close>
  \<open>\<not>irred (get_clauses_wl S) C \<Longrightarrow>
    get_subsumed_init_clauses_wl (remove_lit_from_clause_wl C L' S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_learned_clss_wl (remove_lit_from_clause_wl C L' S) = IsaSAT_Setup.get_unkept_unit_learned_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_learned_clss_wl (remove_lit_from_clause_wl C L' S) = IsaSAT_Setup.get_kept_unit_learned_clss_wl S\<close>
  \<open>irred (get_clauses_wl S) C \<Longrightarrow>
    get_subsumed_learned_clauses_wl (remove_lit_from_clause_wl C L' S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>\<not>irred (get_clauses_wl S) C \<Longrightarrow>
     get_subsumed_learned_clauses_wl (remove_lit_from_clause_wl C L' S) = add_mset (mset (get_clauses_wl S \<propto> C)) (get_subsumed_learned_clauses_wl S)\<close>
  \<open>literals_to_update_wl (remove_lit_from_clause_wl C L' S) = literals_to_update_wl S\<close>
  \<open>get_watched_wl (remove_lit_from_clause_wl C L' S) = get_watched_wl S\<close>
  \<open>get_clauses_wl (remove_lit_from_clause_wl C L' S) = (get_clauses_wl S) (C \<hookrightarrow> remove1 L' (get_clauses_wl S \<propto> C))\<close>
  \<open>get_init_clauses0_wl (remove_lit_from_clause_wl C L' S) = get_init_clauses0_wl (S)\<close>
  \<open>get_learned_clauses0_wl (remove_lit_from_clause_wl C L' S) = get_learned_clauses0_wl (S)\<close>
  \<open>get_conflict_wl (remove_lit_from_clause_wl C L' S) = get_conflict_wl S\<close>
  by (solves \<open>cases S; auto simp: remove_lit_from_clause_wl_def\<close>)+

lemma in_all_lits_of_wl_ain_atms_of_iff: \<open>L \<in># all_init_lits_of_wl N \<longleftrightarrow> atm_of L \<in># all_init_atms_st N\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n by blast
lemma init_clss_lf_mapsto_upd_irrelev: \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
  init_clss_lf (fmupd C (D, True) N) = add_mset D (init_clss_lf N)\<close>
  by (simp add: init_clss_l_mapsto_upd_irrelev)

lemma arena_promote_dom_m_get_clauses_wl[simp]:
  \<open>C \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
  dom_m (get_clauses_wl (arena_promote_st_wl S C)) = dom_m (get_clauses_wl S)\<close>
  by (cases S) (auto simp: arena_promote_st_wl_def)

text \<open>
The assertions here are an artefact of how the refinement frameworks handles if-then-else. It splits
lhs ifs, but not rhs splits when they appear whithin an expression.
\<close>
lemma strengthen_clause_wl_alt_def[unfolded Down_id_eq]:
  \<open>\<Down>Id(strengthen_clause_wl C D L' S) \<ge> do {
    ASSERT (subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L' D) S);
    let m = length (get_clauses_wl S \<propto> C);
    let n = length (get_clauses_wl S \<propto> D);
    let E = remove1 (- L') (get_clauses_wl S \<propto> C);
    let _ = C \<in># dom_m (get_clauses_wl S);
    let _ = D \<in># dom_m (get_clauses_wl S);
    let T = remove_lit_from_clause_wl C (-L') S;
    _ \<leftarrow> log_clause2 T C;
    if False then RETURN T
    else if m = n then do {
      let T = add_clauses_to_subsumed_wl D (T);
      ASSERT (set_mset (all_init_atms_st T) = set_mset (all_init_atms_st S));
      ASSERT (set_mset (all_init_atms_st (if \<not>irred (get_clauses_wl S) C \<and> irred (get_clauses_wl S) D then arena_promote_st_wl T C else T)) = set_mset (all_init_atms_st S));
      let U = (if \<not>irred (get_clauses_wl S) C \<and> irred (get_clauses_wl S) D then arena_promote_st_wl T C else T);
      ASSERT (set_mset (all_init_atms_st (mark_garbage_wl_no_learned_reset D U)) = set_mset (all_init_atms_st S));
      let U = mark_garbage_wl_no_learned_reset D U;
      RETURN U
     }
    else RETURN T
  }\<close>
proof -
  have le2: \<open>length (get_clauses_wl S \<propto> C) \<noteq> 2\<close> and
    CD: \<open>C \<noteq> D\<close> and
    C_dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close>and
    D_dom: \<open>D \<in># dom_m (get_clauses_wl S)\<close> and
    subs: \<open>remove1_mset L' (mset (get_clauses_wl S \<propto> D)) \<subseteq># remove1_mset (- L') (mset (get_clauses_wl S \<propto> C))\<close> and
    eq_le: \<open>length (get_clauses_wl S \<propto> D) = length (get_clauses_wl S \<propto> C) \<Longrightarrow>
    remove1_mset L' (mset (get_clauses_wl S \<propto> D)) = remove1_mset (- L') (mset (get_clauses_wl S \<propto> C))\<close>
    if pre: \<open>subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L' D) S\<close>
  proof -
    have
      L: \<open>-L' \<in># mset (get_clauses_wl S \<propto> C)\<close>
      \<open>L' \<in># mset (get_clauses_wl S \<propto> D)\<close> and
      \<open>remove1_mset L' (mset (get_clauses_wl S \<propto> D)) \<subseteq># remove1_mset (- L') (mset (get_clauses_wl S \<propto> C))\<close>
      \<open>\<not> tautology (mset (get_clauses_wl S \<propto> D))\<close>
      \<open>\<not> tautology
        (remove1_mset L' (mset (get_clauses_wl S \<propto> D)) +
         remove1_mset (- L') (mset (get_clauses_wl S \<propto> C)))\<close>
      using that unfolding subsume_or_strengthen_wl_pre_def
        subsume_or_strengthen_pre_def apply -
      by (solves \<open>normalize_goal+; clarsimp\<close>)+
    show \<open>length (get_clauses_wl S \<propto> C) \<noteq> 2\<close> and \<open>C \<noteq> D\<close> and \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
      \<open>D \<in># dom_m (get_clauses_wl S)\<close> and
      subs: \<open>remove1_mset L' (mset (get_clauses_wl S \<propto> D)) \<subseteq># remove1_mset (- L') (mset (get_clauses_wl S \<propto> C))\<close>
      using that unfolding subsume_or_strengthen_wl_pre_def
        subsume_or_strengthen_pre_def apply -
      by (solves \<open>normalize_goal+; clarsimp\<close>)+

    show \<open>remove1_mset L' (mset (get_clauses_wl S \<propto> D)) = remove1_mset (- L') (mset (get_clauses_wl S \<propto> C))\<close>
      if \<open>length (get_clauses_wl S \<propto> D) = length (get_clauses_wl S \<propto> C)\<close>
      using multi_member_split[OF L(1)] multi_member_split[OF L(2)] subs that
      by (auto simp del: size_mset simp flip: size_mset simp: subseteq_mset_size_eql_iff)

  qed
  have add_subsumed_same:
    \<open>set_mset (all_init_atms_st (add_clauses_to_subsumed_wl D S)) =  set_mset (all_init_atms_st S)\<close>
    if \<open>D \<in># dom_m (get_clauses_wl S)\<close> for S D
    using that
    apply (cases S)
    apply (auto simp: all_init_atms_def all_init_atms_st_def add_clauses_to_subsumed_wl_def
      all_init_lits_def ran_m_def all_lits_of_mm_add_mset
      dest!: multi_member_split[of D]
      simp del: all_init_atms_def[symmetric])
    done

  have H1: \<open>set_mset (all_init_atms_st (arena_promote_st_wl S C)) = set_mset (all_init_atms_st S)\<close>
    if \<open>set_mset (all_lits_of_m (mset (get_clauses_wl S \<propto> C))) \<subseteq> set_mset (all_init_lits_of_wl S)\<close> and
      \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    for C S
    using that
    apply (cases \<open>irred (get_clauses_wl S) C\<close>)
    subgoal
      using fmupd_same[of C \<open>get_clauses_wl S\<close>]
      apply (cases S; cases \<open>fmlookup (get_clauses_wl S) C\<close>)
      apply (auto simp:  all_init_atms_st_def add_clauses_to_subsumed_wl_def
        all_init_atms_def all_init_lits_def ran_m_def all_lits_of_mm_add_mset arena_promote_st_wl_def
        remove_lit_from_clause_wl_def image_Un
        dest!: multi_member_split[of D]
        simp del: all_init_atms_def[symmetric] fmupd_same
        cong: filter_mset_cong image_mset_cong2)
      apply auto
     done
    subgoal
      by (cases S)
       (auto simp:  all_init_atms_st_def add_clauses_to_subsumed_wl_def all_init_atms_def
        all_init_lits_def all_lits_of_mm_add_mset arena_promote_st_wl_def init_clss_l_mapsto_upd
        init_clss_l_mapsto_upd_irrelev all_init_lits_of_wl_def ac_simps
        dest!: multi_member_split[of D]
        simp del: all_init_atms_def[symmetric])
    done
  have K: \<open>set_mset
   (all_init_atms_st
     (arena_promote_st_wl (add_clauses_to_subsumed_wl D (remove_lit_from_clause_wl C (- L') S)) C)) =
    set_mset (all_init_atms_st S)\<close> (is ?A) and
    K2: \<open>set_mset (all_init_atms_st (remove_lit_from_clause_wl C (- L') S)) = set_mset (all_init_atms_st S)\<close> (is ?B) and
    K3: \<open>length (get_clauses_wl S \<propto> C) = length (get_clauses_wl S \<propto> D) \<Longrightarrow>
    set_mset (all_init_atms_st (mark_garbage_wl_no_learned_reset D
      (if \<not> irred (get_clauses_wl S) C \<and> irred (get_clauses_wl S) D
    then arena_promote_st_wl (add_clauses_to_subsumed_wl D (remove_lit_from_clause_wl C (- L') S)) C
    else add_clauses_to_subsumed_wl D (remove_lit_from_clause_wl C (- L') S)))) =
    set_mset (all_init_atms_st S)\<close> (is \<open>_ \<Longrightarrow> ?C\<close>)
    if pre: \<open>subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L' D) S\<close>
  proof -
    obtain x xa where
      Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
      \<open>2 < length (get_clauses_wl S \<propto> C)\<close> and
      \<open>2 \<le> length (get_clauses_l x \<propto> C)\<close> and
      \<open>C \<in># dom_m (get_clauses_l x)\<close> and
      \<open>count_decided (get_trail_l x) = 0\<close> and
      \<open>distinct (get_clauses_l x \<propto> C)\<close> and
      \<open>\<forall>L\<in>set (get_clauses_l x \<propto> C). undefined_lit (get_trail_l x) L\<close> and
      \<open>get_conflict_l x = None\<close> and
      \<open>C \<notin> set (get_all_mark_of_propagated (get_trail_l x))\<close> and
      \<open>clauses_to_update_l x = {#}\<close> and
      \<open>twl_list_invs x\<close> and
      xxa: \<open>(x, xa) \<in> twl_st_l None\<close> and
      struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of xa)\<close> and
      inv: \<open>twl_struct_invs xa\<close> and
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of xa)\<close> and
      \<open>L' \<in># mset (get_clauses_l x \<propto> D)\<close> and
      \<open>- L' \<in># mset (get_clauses_l x \<propto> C)\<close> and
      \<open>\<not> tautology (mset (get_clauses_l x \<propto> D))\<close> and
      \<open>D \<noteq> 0\<close> and
      \<open>remove1_mset L' (mset (get_clauses_l x \<propto> D)) \<subseteq># remove1_mset (- L') (mset (get_clauses_l x \<propto> C))\<close> and
      \<open>D \<in># dom_m (get_clauses_l x)\<close> and
      \<open>distinct (get_clauses_l x \<propto> D)\<close> and
      \<open>D \<notin> set (get_all_mark_of_propagated (get_trail_l x))\<close> and
      \<open>2 \<le> length (get_clauses_l x \<propto> D)\<close> and
      \<open>\<not> tautology
       (remove1_mset L' (mset (get_clauses_l x \<propto> D)) +
        remove1_mset (- L') (mset (get_clauses_l x \<propto> C)))\<close>
      using pre unfolding subsume_or_strengthen_wl_pre_def subsume_or_strengthen_pre_def subsumption.simps
      apply - apply normalize_goal+ by blast

    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of xa)\<close>
      using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
    then have \<open>atms_of_mm (learned_clss (state\<^sub>W_of xa)) \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of xa))\<close>
      unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def by fast
    then have lits_C_in_all:
      \<open>set_mset (all_lits_of_m (mset (get_clauses_wl S \<propto> C))) \<subseteq> set_mset (all_init_lits_of_wl S)\<close>
      if \<open>\<not>irred (get_clauses_wl S) C\<close>
      using that C_dom[OF pre] Sx xxa unfolding set_eq_iff in_set_all_atms_iff
          in_set_all_atms_iff in_set_all_init_atms_iff get_unit_clauses_wl_alt_def
      by (cases xa; cases x; cases S)
       (auto 4 3 simp: twl_st_l_def state_wl_l_def mset_take_mset_drop_mset' ran_m_def image_image
        conj_disj_distribR Collect_disj_eq image_Un Collect_conv_if all_init_lits_of_wl_def
        in_all_lits_of_mm_ain_atms_of_iff in_all_lits_of_m_ain_atms_of_iff atm_of_eq_atm_of
        dest!: multi_member_split[of \<open>C :: nat\<close>])
    have [simp]: \<open>get_clauses_wl (add_clauses_to_subsumed_wl D (remove_lit_from_clause_wl C (- L') S)) \<propto> C =
      get_clauses_wl (remove_lit_from_clause_wl C (- L') S) \<propto> C\<close>
      by (cases S) (auto simp: add_clauses_to_subsumed_wl_def remove_lit_from_clause_wl_def)

    have init_decomp:
      \<open>irred N D \<Longrightarrow> D \<in># dom_m N \<Longrightarrow> init_clss_l N = add_mset ((N \<propto> D, irred N D)) (init_clss_l (fmdrop D N))\<close> for D N
      using distinct_mset_dom[of N] apply (cases \<open>the (fmlookup N D)\<close>)
      by (auto simp: ran_m_def dest!: multi_member_split
        intro!: image_mset_cong2 intro!: filter_mset_cong2)

    have [simp]: \<open>fmdrop C (fmdrop D (fmupd C E b)) = fmdrop C (fmdrop D b)\<close> for E b
      by (metis fmdrop_comm fmdrop_fmupd_same)

    show ?A
      using C_dom[OF that] D_dom[OF that] CD[OF that] subs[OF that]
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> C))\<close>
          \<open>mset (get_clauses_wl S \<propto> C)\<close>, THEN set_mset_mono]
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> D))\<close>
          \<open>mset (get_clauses_wl S \<propto> D)\<close>, THEN set_mset_mono]
      apply (cases S)
      apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ D] init_decomp[of \<open>fmdrop D _\<close> C]
        init_clss_l_fmdrop_irrelev
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of D])
      apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ D] init_decomp[of \<open>_\<close> C] init_clss_l_fmdrop_irrelev
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of D])
      using lits_C_in_all[unfolded all_init_lits_of_wl_def, simplified]
      apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ D] init_decomp[of \<open>_\<close> C] ac_simps
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of D])
      done

    show ?B
      using C_dom[OF that] D_dom[OF that] CD[OF that] subs[OF that]
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> C))\<close>
          \<open>mset (get_clauses_wl S \<propto> C)\<close>, THEN set_mset_mono]
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> D))\<close>
          \<open>mset (get_clauses_wl S \<propto> D)\<close>, THEN set_mset_mono]
      apply (cases S)
      apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ D] init_decomp[of \<open>fmdrop D _\<close> C]
        init_clss_l_fmdrop_irrelev
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of D])
      apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ D] init_decomp[of \<open>_\<close> C] init_clss_l_fmdrop_irrelev init_clss_l_mapsto_upd_irrel
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of D])
      done
    have KK[simp]: \<open>E \<in># b \<Longrightarrow> add_mset (mset E) (mset `# remove1_mset E b + F) = mset `# b + F\<close> for b E F
      by (auto dest!: multi_member_split)

    have 1: \<open>set_mset (all_init_atms_st (mark_garbage_wl_no_learned_reset D (add_clauses_to_subsumed_wl D S))) =
      set_mset (all_init_atms_st S)\<close>
      if \<open>D \<in># dom_m (get_clauses_wl S)\<close> for S
      using that
      apply (cases S)
      apply (clarsimp simp only: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ D]
        init_clss_l_fmdrop_irrelev mark_garbage_wl_no_learned_reset_def arena_promote_st_wl_def
        all_init_atms_st_def all_init_atms_def get_clauses_wl.simps all_init_lits_def fmupd_idem
        init_clss_l_mapsto_upd_irrel init_clss_lf_fmdrop_irrelev init_clss_lf_mapsto_upd_irrelev
        split: if_splits intro!: impI conjI
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of D])
      apply (intro conjI impI)
      apply simp
      apply simp
      apply (subst (2)init_decomp[of _ D])
      apply (auto simp add: all_lits_of_mm_add_mset)[3]
      apply (subst (2)init_decomp[of _ D])
      apply (auto simp add: all_lits_of_mm_add_mset)[3]
      done

    have 2: \<open>set_mset (all_init_atms_st (remove_lit_from_clause_wl C (- L') S)) =
    set_mset (all_init_atms_st S)\<close> if \<open>C \<in># dom_m (get_clauses_wl S)\<close>for S
      using that
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> C))\<close>
          \<open>mset (get_clauses_wl S \<propto> C)\<close>, THEN set_mset_mono]
      apply (cases S)
      apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
        arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_decomp[of _ C]
        init_clss_l_fmdrop_irrelev init_clss_l_mapsto_upd_irrel
        simp del: all_init_atms_def[symmetric] dest!: multi_member_split[of C])
     done

    have init_decomp:
      \<open>NO_MATCH (fmdrop D N') N \<Longrightarrow> irred N D \<Longrightarrow> D \<in># dom_m N \<Longrightarrow> init_clss_l N = add_mset ((N \<propto> D, irred N D)) (init_clss_l (fmdrop D N))\<close> for D N
      using distinct_mset_dom[of N] apply (cases \<open>the (fmlookup N D)\<close>)
      by (auto simp: ran_m_def dest!: multi_member_split
        intro!: image_mset_cong2 intro!: filter_mset_cong2)
    assume \<open>length (get_clauses_wl S \<propto> C) = length (get_clauses_wl S \<propto> D)\<close>
    note eq = eq_le[OF pre this[symmetric]]
    have 3: \<open>irred (get_clauses_wl S) D \<Longrightarrow>
     (mark_garbage_wl_no_learned_reset D
  (arena_promote_st_wl (add_clauses_to_subsumed_wl D (remove_lit_from_clause_wl C (- L') S)) C)) =
  (mark_garbage_wl_no_learned_reset D
       (add_clauses_to_subsumed_wl D (arena_promote_st_wl (remove_lit_from_clause_wl C (- L') S) C)))\<close>
     apply (cases S)
     apply (auto simp: mark_garbage_wl_no_learned_reset_def arena_promote_st_wl_def
  add_clauses_to_subsumed_wl_def remove_lit_from_clause_wl_def)
     done
   have \<open>set_mset (all_init_atms_st (arena_promote_st_wl (remove_lit_from_clause_wl C (- L') S) C)) =
    set_mset (all_init_atms_st S)\<close>
     if \<open>\<not>irred (get_clauses_wl S) C\<close> \<open>irred (get_clauses_wl S) D\<close>
     using that D_dom[OF pre] C_dom[OF pre] eq[symmetric]
        all_lits_of_m_mono[of \<open>mset (remove1 (L') (get_clauses_wl S \<propto> D))\<close>
          \<open>mset (get_clauses_wl S \<propto> D)\<close>, THEN set_mset_mono]
     apply (cases S)
     apply (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def
       arena_promote_st_wl_def all_init_atms_def all_init_atms_st_def all_init_lits_def image_Un fmdrop_fmupd_same
       all_lits_of_mm_add_mset init_clss_l_mapsto_upd init_clss_l_mapsto_upd_irrel
       init_clss_l_fmdrop_irrelev init_clss_l_mapsto_upd_irrel all_init_atms_st_def
       init_clss_l_mapsto_upd_irrel init_clss_lf_mapsto_upd_irrelev
       simp del: all_init_atms_def[symmetric] dest!: ) 
     apply (subst init_decomp[of D])
     apply (auto simp add: all_lits_of_mm_add_mset image_Un)
     done
   then show ?C
      using C_dom[OF that] D_dom[OF that] CD[OF that] subs[OF that]
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> C))\<close>
          \<open>mset (get_clauses_wl S \<propto> C)\<close>, THEN set_mset_mono]
        all_lits_of_m_mono[of \<open>mset (remove1 (-L') (get_clauses_wl S \<propto> D))\<close>
          \<open>mset (get_clauses_wl S \<propto> D)\<close>, THEN set_mset_mono]
      apply (cases \<open>\<not> irred (get_clauses_wl S) C \<and> irred (get_clauses_wl S) D\<close>)
      subgoal
        apply (simp only: if_True simp_thms)
        apply (simp add: 1 2 3)
        done
      subgoal
        apply (simp only: if_False 1)
        apply (auto simp: 2 1)
        done
     done
  qed

  have strengthen_clause_wl_alt_def:
    \<open>strengthen_clause_wl = (\<lambda>C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT (subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L C') (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    E \<leftarrow> SPEC (\<lambda>E. mset E = mset (remove1 (-L) (N \<propto> C)));
    let _ = ();
    let _ = ();
    let _ = ();
    _ \<leftarrow> RETURN ();
    if length (N \<propto> C) = 2
    then do {
       ASSERT (length (remove1 (-L) (N \<propto> C)) = 1);
       let L = hd E;
         RETURN (Propagated L 0 # M, fmdrop C' (fmdrop C N), D,
         (if irred N C' then add_mset (mset (N \<propto> C')) else id) NE,
         (if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) UE,
          (if irred N C then add_mset {#L#} else id) NEk, (if \<not>irred N C then add_mset {#L#} else id) UEk,
          ((if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
         ((if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US,
         N0, U0, add_mset (-L) Q, W)
    }
    else if length (N \<propto> C) = length (N \<propto> C')
    then RETURN (M, fmdrop C' (fmupd C (E, irred N C \<or> irred N C') N), D, NE, UE, NEk, UEk,
       ((if irred N C' then add_mset (mset (N \<propto> C')) else id)  o (if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
      ((if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) o (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US,
       N0, U0, Q, W)
    else RETURN (M, fmupd C (E, irred N C) N, D, NE, UE, NEk, UEk,
      (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
      (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, Q, W)})\<close>
      unfolding strengthen_clause_wl_def Let_def by auto
  have [refine0]: \<open>subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L' D) S \<Longrightarrow>
     subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L' D) S \<Longrightarrow>
     (remove1 (- L') (get_clauses_wl S \<propto> C), E) \<in> Id \<Longrightarrow>
     log_clause2 (remove_lit_from_clause_wl C (- L') S) C
    \<le> Refine_Basic.SPEC (\<lambda>c. (c, ()) \<in> Id)\<close> for E
    by (rule log_clause2_log_clause[THEN fref_to_Down_curry, THEN order_trans]) auto

  show ?thesis
    unfolding strengthen_clause_wl_alt_def case_wl_split state_wl_recompose Let_def [of \<open>length _\<close>]
    apply (refine_vcg )
    subgoal by auto
    apply assumption
    subgoal using le2 by blast
    subgoal by auto
    subgoal by auto
    subgoal using D_dom by (clarsimp simp add: add_subsumed_same K K2)
    subgoal using D_dom by (clarsimp simp add: add_subsumed_same K K2)
    subgoal using D_dom by (clarsimp simp add: add_subsumed_same K3)
    subgoal
      using CD
      by (cases S)
        (auto simp: mark_garbage_wl_no_learned_reset_def add_clauses_to_subsumed_wl_def
          arena_promote_st_wl_def remove_lit_from_clause_wl_def)
    subgoal
      by (cases S) (auto simp: remove_lit_from_clause_wl_def add_clauses_to_subsumed_wl_def)
    done
qed

(*TODO Move*)
fun set_clauses_wl :: \<open>_ \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>set_clauses_wl N (M, _, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q) =
    (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q) \<close>
fun add_clause_to_subsumed :: \<open>_ \<Rightarrow> _ \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close>  where
  \<open>add_clause_to_subsumed b E (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q) =
    (M, N, D, NE, UE, NEk, UEk, (if b then add_mset E else id) NS,
    (if \<not>b then add_mset E else id) US, N0, U0, WS, Q) \<close>

(*TODO Move*)
lemma fmap_eq_iff_dom_m_lookup: \<open>f = g \<longleftrightarrow> (dom_m f = dom_m g \<and> (\<forall>k\<in>#dom_m f. fmlookup f k = fmlookup g k))\<close>
  by (metis fmap_ext in_dom_m_lookup_iff)

lemma mop_arena_shorten:
  assumes \<open>valid_arena N N' vdom\<close> and
    \<open>(i,j)\<in>nat_rel\<close> and
    \<open>(C,C')\<in>nat_rel\<close> and
    \<open>C \<in># dom_m N'\<close> and
    \<open>i\<ge>2\<close> \<open>i \<le> length (N' \<propto> C)\<close>
  shows
    \<open>mop_arena_shorten C i N
    \<le> SPEC (\<lambda>c. (c, N'(C' \<hookrightarrow> take j (N' \<propto> C')))
    \<in> {(N\<^sub>1,N\<^sub>1'). valid_arena N\<^sub>1 N\<^sub>1' vdom \<and> length N\<^sub>1 = length N})\<close>
proof -
  show ?thesis
    unfolding mop_arena_shorten_def
    apply refine_vcg
    subgoal using assms unfolding arena_shorten_pre_def arena_is_valid_clause_idx_def
      by (auto intro!: exI[of _ N'] simp: arena_lifting)
    subgoal
      using assms by (auto intro!: valid_arena_arena_shorten simp: arena_lifting)
    done
qed

lemma count_list_distinct_If: \<open>distinct xs \<Longrightarrow> count_list xs x = (if x \<in> set xs then 1 else 0)\<close>
  by (simp add: count_mset_count_list distinct_count_atmost_1)

lemma set_clauses_wl_simp[simp]:
  \<open>get_trail_wl (set_clauses_wl N S) = get_trail_wl S\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_init_clss_wl (set_clauses_wl N S) = IsaSAT_Setup.get_unkept_unit_init_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_init_clss_wl (set_clauses_wl N S) = IsaSAT_Setup.get_kept_unit_init_clss_wl S\<close>
  \<open>get_subsumed_init_clauses_wl (set_clauses_wl N S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>get_subsumed_init_clauses_wl (set_clauses_wl N S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_learned_clss_wl (set_clauses_wl N S) = IsaSAT_Setup.get_unkept_unit_learned_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_learned_clss_wl (set_clauses_wl N S) = IsaSAT_Setup.get_kept_unit_learned_clss_wl S\<close>
  \<open>get_subsumed_learned_clauses_wl (set_clauses_wl N S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>get_subsumed_learned_clauses_wl (set_clauses_wl N S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>literals_to_update_wl (set_clauses_wl N S) = literals_to_update_wl S\<close>
  \<open>get_watched_wl (set_clauses_wl N S) = get_watched_wl S\<close>
  \<open>get_clauses_wl (set_clauses_wl N S) = N\<close>
  \<open>get_init_clauses0_wl (set_clauses_wl N S) = get_init_clauses0_wl (S)\<close>
  \<open>get_learned_clauses0_wl (set_clauses_wl N S) = get_learned_clauses0_wl (S)\<close>
  \<open>get_conflict_wl (set_clauses_wl N S) = get_conflict_wl S\<close>
  apply (solves \<open>cases S; auto simp: \<close>)+
  done


lemma add_clause_to_subsumed_simp[simp]:
  \<open>get_trail_wl (add_clause_to_subsumed b N S) = get_trail_wl S\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_init_clss_wl (add_clause_to_subsumed b N S) = IsaSAT_Setup.get_unkept_unit_init_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_init_clss_wl (add_clause_to_subsumed b N S) = IsaSAT_Setup.get_kept_unit_init_clss_wl S\<close>
  \<open>b \<Longrightarrow> get_subsumed_init_clauses_wl (add_clause_to_subsumed b N S) = add_mset N (get_subsumed_init_clauses_wl S)\<close>
  \<open>\<not>b \<Longrightarrow> get_subsumed_init_clauses_wl (add_clause_to_subsumed b N S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_learned_clss_wl (add_clause_to_subsumed b N S) = IsaSAT_Setup.get_unkept_unit_learned_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_learned_clss_wl (add_clause_to_subsumed b N S) = IsaSAT_Setup.get_kept_unit_learned_clss_wl S\<close>
  \<open>b \<Longrightarrow>
  get_subsumed_learned_clauses_wl (add_clause_to_subsumed b N S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>\<not>b \<Longrightarrow> get_subsumed_learned_clauses_wl (add_clause_to_subsumed b N S) = add_mset N (get_subsumed_learned_clauses_wl S)\<close>
  \<open>literals_to_update_wl (add_clause_to_subsumed b N S) = literals_to_update_wl S\<close>
  \<open>get_watched_wl (add_clause_to_subsumed b N S) = get_watched_wl S\<close>
  \<open>get_clauses_wl (add_clause_to_subsumed b N S) = get_clauses_wl S\<close>
  \<open>get_init_clauses0_wl (add_clause_to_subsumed b N S) = get_init_clauses0_wl (S)\<close>
  \<open>get_learned_clauses0_wl (add_clause_to_subsumed b N S) = get_learned_clauses0_wl (S)\<close>
  \<open>get_conflict_wl (add_clause_to_subsumed b N S) = get_conflict_wl S\<close>
  apply (solves \<open>cases S; auto simp: \<close>)+
  done

lemma add_clauses_to_subsumed_wl_simp[simp]:
  \<open>get_trail_wl (add_clauses_to_subsumed_wl N S) = get_trail_wl S\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_init_clss_wl (add_clauses_to_subsumed_wl N S) = IsaSAT_Setup.get_unkept_unit_init_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_init_clss_wl (add_clauses_to_subsumed_wl N S) = IsaSAT_Setup.get_kept_unit_init_clss_wl S\<close>
  \<open>irred (get_clauses_wl S) N \<Longrightarrow>
  get_subsumed_init_clauses_wl (add_clauses_to_subsumed_wl N S) = add_mset (mset (get_clauses_wl S \<propto> N)) (get_subsumed_init_clauses_wl S)\<close>
  \<open>\<not>irred (get_clauses_wl S) N \<Longrightarrow>
  get_subsumed_init_clauses_wl (add_clauses_to_subsumed_wl N S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_learned_clss_wl (add_clauses_to_subsumed_wl N S) = IsaSAT_Setup.get_unkept_unit_learned_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_learned_clss_wl (add_clauses_to_subsumed_wl N S) = IsaSAT_Setup.get_kept_unit_learned_clss_wl S\<close>
  \<open>irred (get_clauses_wl S) N \<Longrightarrow>
  get_subsumed_learned_clauses_wl (add_clauses_to_subsumed_wl N S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>\<not>irred (get_clauses_wl S) N \<Longrightarrow> get_subsumed_learned_clauses_wl (add_clauses_to_subsumed_wl N S) = add_mset (mset (get_clauses_wl S \<propto> N)) (get_subsumed_learned_clauses_wl S)\<close>
  \<open>literals_to_update_wl (add_clauses_to_subsumed_wl N S) = literals_to_update_wl S\<close>
  \<open>get_watched_wl (add_clauses_to_subsumed_wl N S) = get_watched_wl S\<close>
  \<open>get_clauses_wl (add_clauses_to_subsumed_wl N S) = get_clauses_wl S\<close>
  \<open>get_init_clauses0_wl (add_clauses_to_subsumed_wl N S) = get_init_clauses0_wl (S)\<close>
  \<open>get_learned_clauses0_wl (add_clauses_to_subsumed_wl N S) = get_learned_clauses0_wl (S)\<close>
  \<open>get_conflict_wl (add_clauses_to_subsumed_wl N S) = get_conflict_wl S\<close>
  apply (solves \<open>cases S; auto simp: add_clauses_to_subsumed_wl_def\<close>)+
  done

lemma remove_lit_from_clause_st:
  assumes
    T: \<open>(T, S) \<in> twl_st_heur_restart_occs' r u\<close> and
    LL': \<open>(L,L')\<in>nat_lit_lit_rel\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close> and
    C_dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
    dist: \<open>distinct (get_clauses_wl S \<propto> C)\<close>and
    le: \<open>length (get_clauses_wl S \<propto> C) > 2\<close>
 shows
  \<open>remove_lit_from_clause_st T C L
   \<le> SPEC (\<lambda>c. (c, remove_lit_from_clause_wl C' L' S) \<in> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T})\<close>
proof -
  define I where
    \<open>I = (\<lambda>(i,j,N). dom_m N = dom_m (get_clauses_wl S) \<and>
    (\<forall>D\<in>#dom_m (get_clauses_wl S). D \<noteq> C \<longrightarrow> fmlookup N D = fmlookup (get_clauses_wl S) D) \<and>
       (take i (N \<propto> C) = (removeAll L (take j (get_clauses_wl S \<propto> C')))) \<and>
       (\<forall>k < length (N \<propto> C). k \<ge> j \<longrightarrow> (N \<propto> C) !k = (get_clauses_wl S \<propto> C') ! k) \<and>
       (length (N \<propto> C) = length (get_clauses_wl S \<propto> C')) \<and>
       irred N C = irred (get_clauses_wl S) C \<and>
    i \<le> j \<and> j \<le> length (get_clauses_wl S \<propto> C'))\<close>
  define \<Phi> where
    \<open>\<Phi> = (\<lambda>(i,j,N). dom_m N = dom_m (get_clauses_wl S) \<and>
    (\<forall>D\<in>#dom_m (get_clauses_wl S). D \<noteq> C \<longrightarrow> fmlookup N D = fmlookup (get_clauses_wl S) D) \<and>
       j = length (get_clauses_wl S \<propto> C') \<and>
       (take i (N \<propto> C) = (removeAll L (get_clauses_wl S \<propto> C'))) \<and>
       (length (N \<propto> C) = length (get_clauses_wl S \<propto> C')) \<and>
       irred N C = irred (get_clauses_wl S) C \<and> C' \<in># dom_m N \<and>
       i \<le> j \<and> j = length (get_clauses_wl S \<propto> C'))\<close>
  have ge: \<open>\<Down>Id (RETURN (remove_lit_from_clause_wl C' L' S)) \<ge>  do {
   let n = length (get_clauses_wl S \<propto> C');
   (i, j, N) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, j, N). j < n)
     (\<lambda>(i, j, N). do {
         ASSERT (i < n);
         ASSERT (j < n);
       K \<leftarrow> mop_clauses_at N C j;
       if K \<noteq> L then do {
         N \<leftarrow> mop_clauses_swap N C i j;
         RETURN (i+1, j+1, N)}
      else RETURN (i, j+1, N)
    }) (0, 0, get_clauses_wl S);
   ASSERT (C' \<in># dom_m N);
   ASSERT (i \<le> length (N \<propto> C'));
   ASSERT (i \<ge> 2);
   let N = N(C' \<hookrightarrow> take i (N \<propto> C'));
   ASSERT (N = (get_clauses_wl S)(C' \<hookrightarrow> removeAll L (get_clauses_wl S \<propto> C')));
   let N = N;
   RETURN (set_clauses_wl N (add_clause_to_subsumed (irred (get_clauses_wl S) C') (mset (get_clauses_wl S \<propto> C')) S))
     }\<close>
     unfolding Let_def
     apply (refine_vcg)
     apply (rule WHILET_rule[where I= \<open>I\<close> and R = \<open>measure (\<lambda>(i,j,N). length (get_clauses_wl S \<propto> C') - j)\<close> and \<Phi>=\<Phi>, THEN order_trans])
     subgoal by auto
     subgoal using CC' unfolding I_def by auto
     subgoal
       unfolding mop_clauses_at_def nres_monad3 mop_clauses_swap_def
       apply (refine_vcg)
       subgoal using C_dom by (auto simp: I_def)
       subgoal using CC' by (auto simp: I_def)
       subgoal using CC' C_dom by (auto simp: I_def)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal unfolding I_def prod.simps apply (intro conjI)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal
         using CC' apply (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
         by (metis order_mono_setup.refl take_update take_update_cancel)+
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       subgoal using CC' by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
       done
     subgoal by (auto simp: I_def)
     subgoal by (auto simp: I_def swap_only_first_relevant take_Suc_conv_app_nth)
     subgoal by (auto simp: I_def)
     done
   subgoal using C_dom CC' unfolding \<Phi>_def I_def by auto
   subgoal using dist CC' LL' le
     unfolding \<Phi>_def by (cases S)  (auto 4 4 simp: remove_lit_from_clause_wl_def distinct_remove1_removeAll
       fmap_eq_iff_dom_m_lookup count_list_distinct_If length_removeAll_count_list
       intro!: ASSERT_leI dest: arg_cong[of \<open>take _ _\<close> _ length])
    done
  have valid: \<open>valid_arena (get_clauses_wl_heur T) (get_clauses_wl S) (set (get_vdom T))\<close> and
   corr: \<open>clss_size_corr_restart (get_clauses_wl S)
  (IsaSAT_Setup.get_unkept_unit_init_clss_wl S) {#} (IsaSAT_Setup.get_kept_unit_init_clss_wl S)
  (IsaSAT_Setup.get_kept_unit_learned_clss_wl S)
  (get_subsumed_init_clauses_wl S)
  {#} (get_init_clauses0_wl S) {#} (get_learned_count T)\<close>
    using T unfolding twl_st_heur_restart_occs_def by fast+
  have [refine]: \<open>((0, 0, get_clauses_wl_heur T), 0, 0, get_clauses_wl S) \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r {(N,N'). valid_arena N N' (set (get_vdom T)) \<and> length N = length (get_clauses_wl_heur T)}\<close>
    using valid by auto
    have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
      by auto
    have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
      by auto

    note cong =  trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong isa_vmtf_cong
       vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
      isasat_input_bounded_cong[THEN iffD1]
       cach_refinement_empty_cong[THEN H']
       phase_saving_cong[THEN H']
       \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
      D\<^sub>0_cong[THEN H]
      map_fun_rel_D\<^sub>0_cong
      vdom_m_cong[symmetric] \<L>\<^sub>a\<^sub>l\<^sub>l_cong isasat_input_nempty_cong

    have mset_removeAll_subseteq: \<open>mset (removeAll L M) \<subseteq># mset M\<close> for L M
      by (subst mset_removeAll[symmetric]) (rule diff_subset_eq_self)
    have [simp]: \<open>    C' \<in># dom_m b \<Longrightarrow> irred b C' \<Longrightarrow>
   set_mset (all_lits_of_mm
        (add_mset (mset (removeAll L (b \<propto> C')))
       ({#mset (fst x). x \<in># init_clss_l b#} + dj))) =
   set_mset (all_lits_of_mm
       ({#mset (fst x). x \<in># init_clss_l b#} + dj))\<close> for b dj i
    using all_lits_of_m_mono[of \<open>mset (removeAll L (b \<propto> C'))\<close> \<open>mset (b \<propto> C')\<close>]
    by (auto simp: all_lits_of_mm_add_mset ran_m_def mset_take_subseteq mset_removeAll_subseteq
        dest!: multi_member_split[of C'])

  have \<open>set_mset (all_init_atms_st (set_clauses_wl ((get_clauses_wl S)(C' \<hookrightarrow> removeAll L (get_clauses_wl S \<propto> C')))
    (add_clause_to_subsumed (irred (get_clauses_wl S) C') (mset (get_clauses_wl S \<propto> C')) S))) =
    set_mset (all_init_atms_st S)\<close> for i
    using C_dom CC'
    by (cases S)
     (auto simp: all_init_atms_st_def simp del: all_init_atms_def[symmetric]
      simp: all_init_lits_def all_init_atms_def init_clss_l_fmdrop_if init_clss_l_mapsto_upd init_clss_l_clause_upd
      image_mset_remove1_mset_if add_mset_commute[of _ \<open>mset (removeAll _ _)\<close>] init_clss_l_mapsto_upd_irrel)
  note cong1 = cong[OF this(1)[symmetric]]

  have [simp]: \<open>clss_size_corr_restart ((get_clauses_wl S)(C' \<hookrightarrow> removeAll L (get_clauses_wl S \<propto> C')))
  (IsaSAT_Setup.get_unkept_unit_init_clss_wl S) {#} (IsaSAT_Setup.get_kept_unit_init_clss_wl S)
  (IsaSAT_Setup.get_kept_unit_learned_clss_wl S)
  (get_subsumed_init_clauses_wl
    (add_clause_to_subsumed (irred (get_clauses_wl S) C') (mset (get_clauses_wl S \<propto> C')) S))
  {#} (get_init_clauses0_wl S) {#} (get_learned_count T)\<close>
    using C_dom CC' corr by (auto simp: clss_size_corr_restart_def clss_size_def)
  have[simp]:
    \<open>vdom_m (all_init_atms_st S) (get_watched_wl S) ((get_clauses_wl S)(C' \<hookrightarrow> removeAll L (get_clauses_wl S \<propto> C'))) =
     vdom_m (all_init_atms_st S) (get_watched_wl S) ((get_clauses_wl S))\<close>
    using C_dom CC' by (auto simp: vdom_m_def)

  have still_in_dom_after_shortening: \<open>C' \<in># dom_m x2c \<Longrightarrow>
    x1b  \<le> length (x2c \<propto> C') \<Longrightarrow>
    TIER_ONE_MAXIMUM  \<le> x1b \<Longrightarrow>
    (xb, x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C')))
    \<in> {(N\<^sub>1, N\<^sub>1'). valid_arena N\<^sub>1 N\<^sub>1' (set (get_vdom T)) \<and> length N\<^sub>1 = length x2a} \<Longrightarrow>
    C \<in># dom_m (x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C')))\<close>for x1b x2c xb x2a
   using CC' by auto
  have H: \<open>(xb, x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C')))
    \<in> {(N\<^sub>1, N\<^sub>1'). valid_arena N\<^sub>1 N\<^sub>1' (set (get_vdom T)) \<and> length N\<^sub>1 = length x2a} \<Longrightarrow>
    (xc, x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C')))
    \<in> {(c, N').
    N' = x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C')) \<and>
    valid_arena c (x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C'))) (set (get_vdom T)) \<and>
    length c = length xb} \<Longrightarrow>
    (xc, x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C'))) \<in> {(c, N').
    N' = x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C')) \<and>
    valid_arena c (x2c(C' \<hookrightarrow> take x1b (x2c \<propto> C'))) (set (get_vdom T)) \<and>
    length c = length x2a}\<close>for x1b xb x2a xc x2c
   by auto
  show ?thesis
   unfolding conc_fun_RETURN[symmetric]
   apply (rule ref_two_step)
   defer apply (rule ge[unfolded Down_id_eq])
   unfolding remove_lit_from_clause_st_def remove_lit_from_clause_def nres_monad3
   apply (refine_vcg mop_arena_length[of \<open>set (get_vdom T)\<close>, THEN fref_to_Down_curry, unfolded comp_def]
     mop_arena_lit2[of _ _ \<open>set (get_vdom T)\<close>] mop_arena_swap2[of _ _ \<open>set (get_vdom T)\<close>]
     mop_arena_shorten[of _ _ _ _ _ C C'] update_lbd_shrunk_clause_valid[of _ _ _ \<open>set (get_vdom T)\<close>])
   subgoal using C_dom CC' by auto
   subgoal using CC' valid by auto
   subgoal using CC' C_dom by auto
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
   apply (solves auto)[]
   apply (solves auto)[]
   subgoal using CC' by auto
   subgoal using CC' by auto
   subgoal by auto
   subgoal using CC' by auto
   apply (rule still_in_dom_after_shortening; assumption)
   subgoal by auto
   apply (rule H; assumption)
   subgoal using T CC' C_dom
     by (clarsimp simp add: twl_st_heur_restart_occs_def cong1 IsaSAT_Restart.all_init_atms_alt_def
       simp del: isasat_input_nempty_def)
   done
qed

lemma add_clauses_to_subsumed_wl_twl_st_heur_restart_occs:
  assumes \<open>(S, T) \<in> twl_st_heur_restart_occs' r u\<close> and
    D: \<open>D \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>(S, add_clauses_to_subsumed_wl D T) \<in> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs S \<and> get_aivdom U = get_aivdom S}\<close>
proof -
  have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
    by auto
  have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
    by auto

  note cong =  trail_pol_cong heuristic_rel_cong
    option_lookup_clause_rel_cong isa_vmtf_cong
    vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
    isasat_input_bounded_cong[THEN iffD1]
    cach_refinement_empty_cong[THEN H']
    phase_saving_cong[THEN H']
    \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
    D\<^sub>0_cong[THEN H]
    map_fun_rel_D\<^sub>0_cong
    vdom_m_cong[symmetric] \<L>\<^sub>a\<^sub>l\<^sub>l_cong isasat_input_nempty_cong
  have \<open>set_mset (all_init_atms_st (add_clauses_to_subsumed_wl D T)) =
    set_mset (all_init_atms_st T)\<close>
    using D by (cases T)
      (auto simp: all_init_atms_st_def add_clauses_to_subsumed_wl_def all_init_atms_def
      all_init_lits_def ran_m_def all_lits_of_mm_add_mset
      dest!: multi_member_split[of \<open>_ :: nat\<close>]
      simp del: all_init_atms_def[symmetric])
  note cong1 = cong[OF this[symmetric]]
  show ?thesis
    using assms
    unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
    by (cases \<open>irred (get_clauses_wl T) D\<close>)
     (clarsimp_all simp add: cong1 simp del: isasat_input_bounded_def isasat_input_nempty_def)
qed


lemma mark_garbage_wl_no_learned_reset_simp[simp]:
  \<open>get_trail_wl (mark_garbage_wl_no_learned_reset C S) = get_trail_wl S\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_init_clss_wl (mark_garbage_wl_no_learned_reset C S) = IsaSAT_Setup.get_unkept_unit_init_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_init_clss_wl (mark_garbage_wl_no_learned_reset C S) = IsaSAT_Setup.get_kept_unit_init_clss_wl S\<close>
  \<open>get_subsumed_init_clauses_wl (mark_garbage_wl_no_learned_reset C S) = (get_subsumed_init_clauses_wl S)\<close>
  \<open>IsaSAT_Setup.get_unkept_unit_learned_clss_wl (mark_garbage_wl_no_learned_reset C S) = IsaSAT_Setup.get_unkept_unit_learned_clss_wl S\<close>
  \<open>IsaSAT_Setup.get_kept_unit_learned_clss_wl (mark_garbage_wl_no_learned_reset C S) = IsaSAT_Setup.get_kept_unit_learned_clss_wl S\<close>
  \<open>get_subsumed_learned_clauses_wl (mark_garbage_wl_no_learned_reset C S) = (get_subsumed_learned_clauses_wl S)\<close>
  \<open>literals_to_update_wl (mark_garbage_wl_no_learned_reset C S) = literals_to_update_wl S\<close>
  \<open>get_watched_wl (mark_garbage_wl_no_learned_reset C S) = get_watched_wl S\<close>
  \<open>get_clauses_wl (mark_garbage_wl_no_learned_reset C S) = fmdrop C (get_clauses_wl S)\<close>
  \<open>get_init_clauses0_wl (mark_garbage_wl_no_learned_reset C S) = get_init_clauses0_wl (S)\<close>
  \<open>get_learned_clauses0_wl (mark_garbage_wl_no_learned_reset C S) = get_learned_clauses0_wl (S)\<close>
  \<open>get_conflict_wl (mark_garbage_wl_no_learned_reset C S) = get_conflict_wl S\<close>
  apply (solves \<open>cases S; auto simp: mark_garbage_wl_no_learned_reset_def\<close>)+
  done

lemma [simp]: \<open>get_occs (incr_wasted_st b S) = get_occs S\<close>
  \<open>learned_clss_count (incr_wasted_st b S) = learned_clss_count S\<close>
  by (auto simp: incr_wasted_st_def)

lemma log_clause_heur_log_clause2_occs:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_occs' r u\<close> \<open>(C,C') \<in> nat_rel\<close>
  shows \<open>log_clause_heur S C \<le>\<Down>unit_rel (log_clause2 T C')\<close>
proof -
  have [refine0]: \<open>(0,0)\<in>nat_rel\<close>
    by auto
  have length: \<open>\<Down> nat_rel ((RETURN \<circ> (\<lambda>c. length (get_clauses_wl T \<propto> c))) C') \<le> SPEC (\<lambda>c. (c, length (get_clauses_wl T \<propto> C')) \<in> {(a,b). a=b \<and> a = length (get_clauses_wl T \<propto> C)})\<close>
    by (use assms in auto)
  show ?thesis
    unfolding log_clause_heur_def log_clause2_def comp_def uncurry_def mop_arena_length_st_def
      mop_access_lit_in_clauses_heur_def
    apply (refine_vcg mop_arena_lit[where vdom = \<open>set (get_vdom S)\<close> and N = \<open>get_clauses_wl T\<close>, THEN order_trans] 
      mop_arena_length[where vdom = \<open>set (get_vdom S)\<close>, THEN fref_to_Down_curry, THEN order_trans, unfolded prod.simps])
    apply assumption
    subgoal using assms by (auto simp: twl_st_heur_restart_occs_def twl_st_heur_restart_def)
    apply (rule length)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_restart_occs_def twl_st_heur_restart_def dest: arena_lifting(10)\<close>)
    subgoal by auto
    subgoal using assms by (auto simp: twl_st_heur_restart_occs_def twl_st_heur_restart_def)
    apply assumption
    subgoal by (use assms in auto)
    apply (rule refl)
    subgoal by auto
    by auto
qed

lemma log_del_clause_heur_log_clause:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_occs' r u\<close> \<open>(C,C') \<in> nat_rel\<close> \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>log_del_clause_heur S C \<le> SPEC (\<lambda>c. (c, log_clause T C') \<in> unit_rel)\<close>
    unfolding log_del_clause_heur_alt_def
    apply (rule log_clause_heur_log_clause2_occs[THEN order_trans, OF assms(1,2)])
    apply (rule order_trans)
    apply (rule ref_two_step')
    apply (rule log_clause2_log_clause[THEN fref_to_Down_curry])
    using assms by auto

lemma mark_garbage_heur_as_subsumed:
  assumes
    T: \<open>(S,T)\<in> twl_st_heur_restart_occs' r u\<close> and
    D: \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>(C',C)\<in>nat_rel\<close> and
    eq: \<open>set_mset (all_init_atms_st (mark_garbage_wl_no_learned_reset C' T)) = set_mset (all_init_atms_st T)\<close>
  shows \<open>mark_garbage_heur_as_subsumed C S \<le> SPEC (\<lambda>c. (c, mark_garbage_wl_no_learned_reset C' T) \<in> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs S \<and> get_aivdom U = get_aivdom S})\<close>
proof -
  have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
    by auto
  have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
    by auto

  note cong =  trail_pol_cong heuristic_rel_cong
    option_lookup_clause_rel_cong isa_vmtf_cong
    vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
    isasat_input_bounded_cong[THEN iffD1]
    cach_refinement_empty_cong[THEN H']
    phase_saving_cong[THEN H']
    \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
    D\<^sub>0_cong[THEN H]
    map_fun_rel_D\<^sub>0_cong
    vdom_m_cong[symmetric] \<L>\<^sub>a\<^sub>l\<^sub>l_cong isasat_input_nempty_cong
    heuristic_rel_cong
  have CC': \<open>C' = C\<close>
    using assms by auto
  note cong1 = cong[OF eq[unfolded CC', symmetric]]


  have valid: \<open>valid_occs (get_occs S) (get_aivdom S)\<close> and
    arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
    using T by (auto simp: twl_st_heur_restart_occs_def)

  have pre: \<open>arena_is_valid_clause_idx (get_clauses_wl_heur S) C\<close>
    unfolding arena_is_valid_clause_idx_def
    by (use T arena D in \<open>auto simp: arena_is_valid_clause_idx_and_access_def intro!: exI[of _ \<open>get_clauses_wl T\<close>] exI[of _ \<open>set (get_vdom S)\<close>]\<close>)
  show ?thesis
    using pre
    unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
      mark_garbage_heur_as_subsumed_def mop_arena_length_def nres_monad3
    apply (refine_vcg log_del_clause_heur_log_clause[where r=r and u=u and C'=C, THEN order_trans] T)
    subgoal
      using arena D unfolding arena_is_valid_clause_vdom_def by auto
    subgoal by simp
    subgoal using arena D by simp
    subgoal using arena D unfolding mark_garbage_pre_def by simp
    subgoal
      using arena red_in_dom_number_of_learned_ge1[of C \<open>get_clauses_wl T\<close>] assms assms
        red_in_dom_number_of_learned_ge1_twl_st_heur_restart_occs[of S T r u C]
      by (cases \<open>arena_status (get_clauses_wl_heur S) C\<close>)
       (auto simp add: arena_lifting)
    subgoal
      using assms pre
      unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
      mark_garbage_heur_as_subsumed_def mop_arena_length_def nres_monad3
      apply (clarsimp_all simp add: cong1 valid_arena_extra_information_mark_to_delete'
        aivdom_inv_dec_remove_clause arena_lifting
        simp del: isasat_input_bounded_def isasat_input_nempty_def
        simp flip: learned_clss_count_def
        )
      apply (intro conjI impI)
      subgoal
        by (auto dest: in_vdom_m_fmdropD simp add: incr_wasted_st_def cong1 intro!: heuristic_relI)
      subgoal
        by (auto simp add: incr_wasted_st_def cong1 intro!: heuristic_relI)
      subgoal
        by (auto simp add: incr_wasted_st_def cong1 intro!: heuristic_relI)
      subgoal
        by (auto dest: in_vdom_m_fmdropD simp add: incr_wasted_st_def cong1 intro!: heuristic_relI)
      subgoal
        by (auto simp add: incr_wasted_st_def cong1 intro!: heuristic_relI)
      subgoal
        by (auto simp flip: learned_clss_count_def simp add: incr_wasted_st_def cong1 intro!: heuristic_relI)
      done
    done
qed

lemma twl_st_heur_restart_occs'_with_occs:
  \<open>a\<in>{(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs T \<and> get_aivdom U = get_aivdom S} \<Longrightarrow>
  a \<in> twl_st_heur_restart_occs' r u\<close>
  by auto

lemma isa_strengthen_clause_wl2:
  assumes
    T: \<open>(T, S) \<in> twl_st_heur_restart_occs' r u\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close>and
    DD': \<open>(D,D')\<in>nat_rel\<close> and
    LL': \<open>(L,L')\<in>nat_lit_lit_rel\<close>
  shows \<open>isa_strengthen_clause_wl2 C D L T
    \<le> \<Down> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T}
    (strengthen_clause_wl C' D' L' S)\<close>
proof -
  have arena: \<open>((get_clauses_wl_heur T, C), get_clauses_wl S, C')
    \<in> {(N, N'). valid_arena N N' (set (get_vdom T))} \<times>\<^sub>f nat_rel\<close>
    \<open>((get_clauses_wl_heur T, D), get_clauses_wl S, D')
    \<in> {(N, N'). valid_arena N N' (set (get_vdom T))} \<times>\<^sub>f nat_rel\<close>
    using T CC' DD' unfolding twl_st_heur_restart_occs_def
    by auto
  have C': \<open>C' \<in># dom_m (get_clauses_wl S)\<close> and D': \<open>D' \<in># dom_m (get_clauses_wl S)\<close> and
    C'_in_dom: \<open>(get_clauses_wl S, C') = (x1, x2) \<Longrightarrow> x2 \<in># dom_m x1\<close> and
    D'_in_dom: \<open>(get_clauses_wl S, D') = (x1, x2) \<Longrightarrow> x2 \<in># dom_m x1\<close> and
    C'_vdom: \<open>C' \<in> set (get_vdom T)\<close> and
    D'_vdom: \<open>D' \<in> set (get_vdom T)\<close> and
    C'_dist: \<open>distinct (get_clauses_wl S \<propto> C')\<close> and
    le2: \<open>2 < length (get_clauses_wl S \<propto> C')\<close>
    if pre: \<open>subsume_or_strengthen_wl_pre C' (STRENGTHENED_BY L' D') S\<close>
    for x1 x2
  proof -
    show C': \<open>C' \<in># dom_m (get_clauses_wl S)\<close> and D': \<open>D' \<in># dom_m (get_clauses_wl S)\<close>
      using pre unfolding subsume_or_strengthen_wl_pre_def subsume_or_strengthen_pre_def apply -
      by (normalize_goal+; auto)+
    then show \<open>x2 \<in># dom_m x1\<close> if \<open>(get_clauses_wl S, C') = (x1, x2)\<close>
      using that by auto
    show \<open>x2 \<in># dom_m x1\<close> if \<open>(get_clauses_wl S, D') = (x1, x2)\<close>
      using D' that by auto
    have
      ai: \<open>aivdom_inv_dec (get_aivdom T) (dom_m (get_clauses_wl S))\<close>
      using T unfolding twl_st_heur_restart_occs_def by auto
    then have H: \<open>C' \<in> set (get_vdom T)\<close> if \<open>C' \<in># dom_m (get_clauses_wl S)\<close> for C'
      using ai that
      by (smt (verit, ccfv_threshold) UnE aivdom_inv_dec_alt_def2 in_multiset_in_set mset_subset_eqD subsetD)
    show \<open>C' \<in> set (get_vdom T)\<close> and \<open>D' \<in> set (get_vdom T)\<close>
      using H[OF C'] H[OF D'] CC' DD'
      by auto
    show \<open>distinct (get_clauses_wl S \<propto> C')\<close> \<open>2 < length (get_clauses_wl S \<propto> C')\<close>
      using CC' pre unfolding subsume_or_strengthen_wl_pre_def subsume_or_strengthen_pre_def subsumption.simps apply -
      by (solves \<open>normalize_goal+; simp\<close>)+
  qed
  have [refine]: \<open>(Sa, U)     \<in> {(U, V).
    (U, V) \<in> twl_st_heur_restart_occs' r u \<and>
    get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T} \<Longrightarrow>
    (set_stats_wl_heur (incr_forward_strengethening (get_stats_heur Sa)) Sa, U)
    \<in> {(U, V).
    (U, V) \<in> twl_st_heur_restart_occs' r u \<and>
    get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T}\<close> for Sa U
  by (auto simp: twl_st_heur_restart_occs_def)

  have H: \<open>(x, y') \<in> R \<Longrightarrow> y=y' \<Longrightarrow> (x, y) \<in> R\<close> for x y y' R
     by auto
  show ?thesis
    unfolding isa_strengthen_clause_wl2_def
    apply (rule ref_two_step[OF _ strengthen_clause_wl_alt_def])
    unfolding if_False Let_def[of \<open>remove1 _ _\<close>]
      log_new_clause_heur_alt_def
      Let_def[of \<open>mark_clause_for_unit_as_changed _\<close>]
    apply (refine_vcg mop_arena_length[of \<open>set (get_vdom T)\<close>, THEN fref_to_Down_curry, unfolded comp_def]
      remove_lit_from_clause_st T mop_arena_status2[of _ _ \<open>set (get_vdom T)\<close>]
      mop_arena_promote_st_spec[where r=r and u=u] mark_garbage_heur_as_subsumed)
    subgoal by (rule C'_in_dom)
    subgoal by (rule arena)
    subgoal by (rule D'_in_dom)
    subgoal by (rule arena)
    subgoal using CC' by auto
    subgoal using CC' C'_vdom by auto
    subgoal using arena by auto
    subgoal using DD' by auto
    subgoal using DD' D'_vdom by auto
    subgoal using arena by auto
    subgoal using LL' by auto
    subgoal using CC' by auto
    subgoal using C' CC' by auto
    subgoal using CC' C'_dist by fast
    subgoal using CC' le2 by fast
      apply (rule log_clause_heur_log_clause2_occs[where r=r and u=u])
    subgoal by auto
    subgoal using CC' by auto
    subgoal by auto
    apply (rule add_clauses_to_subsumed_wl_twl_st_heur_restart_occs[where r=r and u=u])
    subgoal by simp
    subgoal using DD' D' by auto
    apply (rule twl_st_heur_restart_occs'_with_occs, assumption)
    subgoal using CC' C' by auto
    subgoal by auto
    subgoal using DD' CC' C' D' arena by (clarsimp simp add: arena_lifting)
    apply (rule H, assumption)
    subgoal using DD' CC' by auto
    subgoal using DD' CC' C' D' arena by (auto simp: arena_lifting)
    apply (rule twl_st_heur_restart_occs'_with_occs, assumption)
    subgoal using DD' D' by simp
    subgoal using DD' by simp
    subgoal premises p
      using p(18,21) by simp
    subgoal by simp
    done
qed

lemma isa_subsume_or_strengthen_wl_subsume_or_strengthen_wl:
  assumes
    T: \<open>(T, S) \<in> twl_st_heur_restart_occs' r u\<close> and
    x: \<open>(x2a, x2) \<in> Id\<close>
  shows \<open>isa_subsume_or_strengthen_wl C x2a T
    \<le> \<Down> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T}
    (subsume_or_strengthen_wl C x2 S)\<close>
proof -

    have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
      by auto
    have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
      by auto

    note cong =  trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong isa_vmtf_cong
       vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
      isasat_input_bounded_cong[THEN iffD1]
       cach_refinement_empty_cong[THEN H']
       phase_saving_cong[THEN H']
       \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
      D\<^sub>0_cong[THEN H]
      map_fun_rel_D\<^sub>0_cong
      vdom_m_cong[symmetric] \<L>\<^sub>a\<^sub>l\<^sub>l_cong isasat_input_nempty_cong

  have atms_eq[symmetric]: \<open>C \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
    irred (get_clauses_wl S) C \<Longrightarrow>
    set_mset (all_init_atms (fmdrop C (get_clauses_wl S))
      (add_mset (mset (get_clauses_wl S \<propto> C))
     (IsaSAT_Setup.get_unkept_unit_init_clss_wl S + IsaSAT_Setup.get_kept_unit_init_clss_wl S +
      get_subsumed_init_clauses_wl S +
    get_init_clauses0_wl S))) =
    set_mset (all_init_atms (get_clauses_wl S)
      (IsaSAT_Setup.get_unkept_unit_init_clss_wl S + IsaSAT_Setup.get_kept_unit_init_clss_wl S +
      get_subsumed_init_clauses_wl S +
    get_init_clauses0_wl S))\<close>
     \<open>C \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
    \<not>irred (get_clauses_wl S) C \<Longrightarrow>
    set_mset (all_init_atms (fmdrop C (get_clauses_wl S))
      ((IsaSAT_Setup.get_unkept_unit_init_clss_wl S + IsaSAT_Setup.get_kept_unit_init_clss_wl S +
      get_subsumed_init_clauses_wl S +
    get_init_clauses0_wl S))) =
    set_mset (all_init_atms (get_clauses_wl S)
      (IsaSAT_Setup.get_unkept_unit_init_clss_wl S + IsaSAT_Setup.get_kept_unit_init_clss_wl S +
      get_subsumed_init_clauses_wl S +
    get_init_clauses0_wl S))\<close>
    by (simp_all add: all_init_atms_fmdrop_add_mset_unit)
  note cong1 = cong[OF this(1)] cong[OF this(2)]

  have H: \<open>x2a = x2\<close>
    using x by auto
  have C_vdom: \<open>C \<in> set (get_vdom T)\<close> and
    C_dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
    valid: \<open>valid_arena (get_clauses_wl_heur T) (get_clauses_wl S) (set (get_vdom T))\<close> and
    C'_vdom: \<open>x2 = SUBSUMED_BY C' \<Longrightarrow> C' \<in> set (get_vdom T)\<close> and
    C'_dom: \<open>x2 = SUBSUMED_BY C' \<Longrightarrow> C' \<in># dom_m (get_clauses_wl S)\<close> and
    mark_garbage: \<open>mark_garbage_heur2 C T
    \<le> SPEC (\<lambda>c. (c, mark_garbage_wl2 C S) \<in> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U=get_occs T \<and> get_aivdom U = get_aivdom T})\<close>
    if \<open>isa_subsume_or_strengthen_wl_pre C x2 T\<close> and
      pre2: \<open>subsume_or_strengthen_wl_pre C x2 S\<close>
    for C'
  proof -
    show C: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
      using pre2 T unfolding isa_subsume_or_strengthen_wl_pre_def subsume_or_strengthen_wl_pre_def
        subsume_or_strengthen_pre_def
      apply - by normalize_goal+ simp
    show valid: \<open>valid_arena (get_clauses_wl_heur T) (get_clauses_wl S) (set (get_vdom T))\<close>
      using T unfolding twl_st_heur_restart_occs_def by auto
    have
      ai: \<open>aivdom_inv_dec (get_aivdom T) (dom_m (get_clauses_wl S))\<close>
      using T unfolding twl_st_heur_restart_occs_def by auto
    then have H: \<open>C' \<in> set (get_vdom T)\<close> if \<open>C' \<in># dom_m (get_clauses_wl S)\<close> for C'
      using ai that
      by (smt (verit, ccfv_threshold) UnE aivdom_inv_dec_alt_def2 in_multiset_in_set mset_subset_eqD subsetD)
    show \<open>C \<in> set (get_vdom T)\<close>
      by (rule H[OF C])
    have [simp]: \<open>(all_init_atms (fmdrop C (get_clauses_wl S))
      (IsaSAT_Setup.get_unkept_unit_init_clss_wl S +
    IsaSAT_Setup.get_kept_unit_init_clss_wl S +
    get_subsumed_init_clauses_wl (mark_garbage_wl2 C S) +
      get_init_clauses0_wl S)) =
      (all_init_atms ((get_clauses_wl S))
      (IsaSAT_Setup.get_unkept_unit_init_clss_wl S +
    IsaSAT_Setup.get_kept_unit_init_clss_wl S +
    get_subsumed_init_clauses_wl (S) +
      get_init_clauses0_wl (mark_garbage_wl2 C S)))\<close>
      by (cases \<open>irred (get_clauses_wl S) C\<close>)
       (use C in \<open>auto simp: all_init_atms_def all_init_lits_def image_mset_remove1_mset_if
        simp del: all_init_atms_def[symmetric]\<close>)
    have [simp]: \<open>valid_arena (extra_information_mark_to_delete (get_clauses_wl_heur T) C)
      (fmdrop C (get_clauses_wl S)) (set (get_vdom T))\<close>
      using valid C valid_arena_extra_information_mark_to_delete' by presburger
    have [simp]: \<open>arena_status (get_clauses_wl_heur T) C = IRRED \<Longrightarrow>
    clss_size_corr_restart ((get_clauses_wl S))
  (IsaSAT_Setup.get_unkept_unit_init_clss_wl S) {#}
  (IsaSAT_Setup.get_kept_unit_init_clss_wl S)
  (IsaSAT_Setup.get_kept_unit_learned_clss_wl S)
  (get_subsumed_init_clauses_wl (S)) {#}
      (get_init_clauses0_wl S) {#} (get_learned_count T) \<Longrightarrow>
    clss_size_corr_restart (fmdrop C (get_clauses_wl S))
  (IsaSAT_Setup.get_unkept_unit_init_clss_wl S) {#}
  (IsaSAT_Setup.get_kept_unit_init_clss_wl S)
  (IsaSAT_Setup.get_kept_unit_learned_clss_wl S)
  (get_subsumed_init_clauses_wl (mark_garbage_wl2 C S)) {#}
      (get_init_clauses0_wl S) {#} (get_learned_count T)\<close>
    \<open>arena_status (get_clauses_wl_heur T) C \<noteq> IRRED \<Longrightarrow>
    clss_size_corr_restart ((get_clauses_wl S))
  (IsaSAT_Setup.get_unkept_unit_init_clss_wl S) {#}
  (IsaSAT_Setup.get_kept_unit_init_clss_wl S)
  (IsaSAT_Setup.get_kept_unit_learned_clss_wl S)
  (get_subsumed_init_clauses_wl (S)) {#}
      (get_init_clauses0_wl S) {#} (get_learned_count T) \<Longrightarrow>
      clss_size_corr_restart (fmdrop C (get_clauses_wl S))
  (IsaSAT_Setup.get_unkept_unit_init_clss_wl S) {#}
  (IsaSAT_Setup.get_kept_unit_init_clss_wl S)
  (IsaSAT_Setup.get_kept_unit_learned_clss_wl S)
  (get_subsumed_init_clauses_wl (mark_garbage_wl2 C S)) {#}
  (get_init_clauses0_wl S) {#} (clss_size_decr_lcount (get_learned_count T))\<close>
      using C arena_lifting(24)[OF valid C] by (auto simp add: clss_size_corr_restart_def clss_size_def
        clss_size_decr_lcount_def size_remove1_mset_If split: prod.splits)
    show \<open>mark_garbage_heur2 C T \<le> SPEC(\<lambda>c. (c, mark_garbage_wl2 C S) \<in> {(U,V). (U,V)\<in>twl_st_heur_restart_occs' r u \<and> get_occs U=get_occs T \<and> get_aivdom U = get_aivdom T})\<close>
      unfolding mark_garbage_heur2_def nres_monad3
      apply refine_vcg
      subgoal 
        using T C unfolding mark_garbage_pre_def arena_is_valid_clause_idx_def
        by (auto simp add: twl_st_heur_restart_occs_def aivdom_inv_dec_remove_clause cong1
          valid_arena_extra_information_mark_to_delete' arena_lifting clss_size_corr_restart_intro
          simp flip: learned_clss_count_def learned_clss_count_def
          simp del: isasat_input_nempty_def
          dest: in_vdom_m_fmdropD)
      subgoal by (rule red_in_dom_number_of_learned_ge1_twl_st_heur_restart_occs[OF T C])
      subgoal
        using T
        by (auto simp add: twl_st_heur_restart_occs_def aivdom_inv_dec_remove_clause cong1
          valid_arena_extra_information_mark_to_delete' arena_lifting clss_size_corr_restart_intro
          simp flip: learned_clss_count_def learned_clss_count_def
          simp del: isasat_input_nempty_def
          dest: in_vdom_m_fmdropD)
      done
    assume \<open>x2 = SUBSUMED_BY C'\<close>
    then show C': \<open>C' \<in># dom_m (get_clauses_wl S)\<close>
      using pre2 T unfolding isa_subsume_or_strengthen_wl_pre_def subsume_or_strengthen_wl_pre_def
        subsume_or_strengthen_pre_def
      apply - by normalize_goal+ simp
    show \<open>C' \<in> set (get_vdom T)\<close>
      by (rule H[OF C'])
  qed
  have [refine, intro!]: \<open>(Sa, U)     \<in> {(U, V).
    (U, V) \<in> twl_st_heur_restart_occs' r u \<and>
    get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T} \<Longrightarrow>
    (set_stats_wl_heur (incr_forward_subsumed (get_stats_heur Sa)) Sa, U)
    \<in> {(U, V).
    (U, V) \<in> twl_st_heur_restart_occs' r u \<and>
    get_occs U = get_occs T \<and> get_aivdom U = get_aivdom T}\<close> for Sa U
    by (auto simp: twl_st_heur_restart_occs_def)
  show ?thesis
    apply (rule order_trans)
    defer
    apply (rule ref_two_step'[OF subsume_or_strengthen_wl_alt_def])
    unfolding isa_subsume_or_strengthen_wl_def Let_def[of \<open>If _ _ _\<close>] Let_def[of \<open>log_clause _ _\<close>]
      case_wl_split state_wl_recompose H
    apply (refine_vcg subsumption_cases_lhs mop_arena_status2[where vdom = \<open>set (get_vdom T)\<close>]
      mark_garbage mop_arena_promote_st_spec[where T=\<open>mark_garbage_wl2 C S\<close> and r=r and u=u]
      isa_strengthen_clause_wl2[where r=r and u=u]
      log_del_clause_heur_log_clause[where r=r and u=u and T=S and C'=C] T)
    subgoal using T unfolding isa_subsume_or_strengthen_wl_pre_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by (rule C_vdom)
    subgoal by (rule valid)
    subgoal by auto
    subgoal by (rule C'_vdom)
    subgoal by (rule valid)
    subgoal by auto
    subgoal using C'_dom C_dom by auto
    subgoal by auto
    subgoal by auto
    subgoal using valid C'_dom C_dom by (auto simp add: arena_lifting)
    subgoal using valid C'_dom C_dom by (auto simp add: arena_lifting)
    subgoal using valid C'_dom C_dom by (auto simp add: arena_lifting)
    subgoal using valid C'_dom C_dom by (auto simp add: arena_lifting)
    subgoal by auto
    subgoal using T by auto
    done
qed

lemma isa_forward_subsumption_one_forward_subsumption_wl_one:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close> and
    DD': \<open>(D,D')\<in>clause_hash\<close> and
    \<open>(L,L')\<in>Id\<close> and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close>
  shows \<open>isa_forward_subsumption_one_wl C D L S \<le>
    \<Down>{((U, changed, E), (S', changed', occs', E')). (get_occs U, occs') \<in> occurrence_list_ref \<and>
          get_aivdom U = get_aivdom S \<and> changed' = (changed \<noteq> NONE) \<and>
       ((U, E), (S', E')) \<in> twl_st_heur_restart_occs' r u \<times>\<^sub>r clause_hash}
    (forward_subsumption_one_wl2 C' cands L' occs D' S')\<close>
proof -
  have valid: \<open>valid_occs (get_occs S) (get_aivdom S)\<close> and
    dom_m_incl: \<open>set_mset (dom_m (get_clauses_wl S')) \<subseteq> set (get_vdom S)\<close>
    using SS' by (auto simp: twl_st_heur_restart_occs_def vdom_m_def)
  have C_vdom: \<open>C \<in>set (get_vdom S)\<close>
    if \<open>forward_subsumption_one_wl2_pre C cands L S'\<close>
  proof -
    have \<open>C \<in># dom_m (get_clauses_wl S')\<close>
      using that unfolding forward_subsumption_one_wl2_pre_def forward_subsumption_one_wl_pre_def
        forward_subsumption_one_pre_def by - (normalize_goal+; simp)
    then show ?thesis
      using dom_m_incl by fast
   qed

  have lits:  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_init_atms_st S') (mset (get_clauses_wl S' \<propto> C))\<close> and
    dist: \<open>distinct_mset (mset (get_clauses_wl S' \<propto> C))\<close> and
    tauto: \<open>\<not> tautology (mset (get_clauses_wl S' \<propto> C))\<close>
    if \<open>forward_subsumption_one_wl2_pre C' cands L' S'\<close>
    using that CC' unfolding forward_subsumption_one_wl2_pre_def forward_subsumption_one_wl_pre_def
      forward_subsumption_one_pre_def
    apply -
    subgoal
      apply normalize_goal+
      apply (frule literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def)
      apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth)
      apply (simp add: literals_are_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n'_def)
      apply (simp add: literals_are_in_\<L>\<^sub>i\<^sub>n_nth literals_are_\<L>\<^sub>i\<^sub>n_cong
        literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff)
      done
    subgoal
      apply normalize_goal+
      unfolding twl_struct_invs_def twl_st_inv_alt_def
      by (simp add:mset_take_mset_drop_mset')
    subgoal
      apply normalize_goal+
      unfolding twl_list_invs_def
      by (simp add:mset_take_mset_drop_mset')
   done
  have forward_subsumption_one_wl2_alt_def:
  \<open>forward_subsumption_one_wl2 = (\<lambda>C cands L occs D S. do {
  ASSERT (forward_subsumption_one_wl2_pre C cands L S);
  ASSERT (atm_of L \<in> fst occs);
  let ys = occ_list occs L;
  let n = length ys;
  (_, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl2_inv S C cands ys \<^esup> (\<lambda>(i, s). i < n \<and> s = NONE)
    (\<lambda>(i, s). do {
      C' \<leftarrow> mop_occ_list_at occs L i;
      b \<leftarrow> RETURN (C' \<in># dom_m (get_clauses_wl S));
      if \<not>b
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> subsume_clauses_match2 C' C S D;
       RETURN (i+1, s)
      }
    })
        (0, NONE);
  D \<leftarrow> (if s \<noteq> NONE then mop_ch_remove_all (mset (get_clauses_wl S \<propto> C)) D else RETURN D);
  occs \<leftarrow> (if is_strengthened s then maybe_push_to_occs_list2 C S occs else RETURN occs);
  S \<leftarrow> subsume_or_strengthen_wl C s S;
  RETURN (S, s \<noteq> NONE, occs, D)
  })\<close>
   unfolding forward_subsumption_one_wl2_def Let_def by auto
  have eq: \<open>L' = L\<close> \<open>C' = C\<close>
    using assms by auto
  have [refine]: \<open>((0, NONE), 0, NONE) \<in> nat_rel \<times>\<^sub>r Id\<close>
    by auto
  have H[simp]: \<open>forward_subsumption_one_wl2_pre C cands L S' \<Longrightarrow> atm_of L \<in> fst occs \<Longrightarrow>
    (occ_list occs L) = (get_occs S ! nat_of_lit L)\<close>
    using occs
    by (cases L)
     (auto simp: forward_subsumption_one_wl2_pre_def occ_list_def occurrence_list_ref_def map_fun_rel_def
      dest: bspec[of _ _ L])
  have set_stats_twl_heur: \<open>(U, V) \<in> twl_st_heur_restart_occs \<Longrightarrow> (set_stats_wl_heur stats U, V)
          \<in> twl_st_heur_restart_occs\<close> for U V stats
    by (auto simp: twl_st_heur_restart_occs_def)
  show ?thesis
    unfolding isa_forward_subsumption_one_wl_def forward_subsumption_one_wl2_alt_def eq Let_def mop_cocc_list_length_def nres_monad3
      cocc_list_length_def
      bind_to_let_conv[of \<open>length (get_occs _ ! _)\<close>]
    apply (refine_vcg mop_cocc_list_at_mop_occ_list_at occs mop_arena_status2[where arena=\<open>get_clauses_wl_heur S\<close> and vdom=\<open>set (get_vdom S)\<close> and
      N=\<open>get_clauses_wl S'\<close>] isa_subsume_clauses_match2_subsume_clauses_match2 SS' mop_cch_remove_all_clauses_mop_ch_remove_all_clauses CC' DD'
      isa_maybe_push_to_occs_list_st_push_to_occs_list2
      isa_subsume_or_strengthen_wl_subsume_or_strengthen_wl[where r=r and u=u])
    subgoal using assms unfolding isa_forward_subsumption_one_wl_pre_def by fast
    subgoal using occs by (cases L) (auto simp: occurrence_list_ref_def map_fun_rel_def dest: bspec[of _ _ \<open>L\<close>])
    subgoal by (auto simp: cocc_list_length_pre_def)
    subgoal using assms H unfolding isa_forward_subsumption_one_wl2_inv_def apply - by (rule exI[of _ S']) auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using valid occs by (auto simp: forward_subsumption_one_wl2_pre_def occurrence_list_ref_def all_init_atms_st_alt_def
        all_occurrences_add_mset2 intro: valid_occs_in_vdomI)
    subgoal using SS' by (auto simp: twl_st_heur_restart_occs_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using DD' by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding forward_subsumption_one_wl2_pre_def forward_subsumption_one_wl_pre_def
      forward_subsumption_one_pre_def
      by normalize_goal+ auto
    subgoal by auto
    subgoal by auto
    subgoal using C_vdom by fast
    subgoal
      using assms(1,2,3,4) simple_clss_size_upper_div2[of \<open>all_init_atms_st S'\<close> \<open>mset (get_clauses_wl S' \<propto> C)\<close>, OF _ lits dist tauto]
      by (auto simp del: isasat_input_bounded_def simp: clause_not_marked_to_delete_def
        simp: twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def)
    subgoal using SS' occs by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto 4 3 simp: forward_subsumption_one_wl2_pre_def isa_forward_subsumption_one_wl_pre_def
      forward_subsumption_one_wl_pre_def intro: set_stats_twl_heur)
    done
qed


lemma isa_try_to_forward_subsume_wl2_try_to_forward_subsume_wl2:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    CC': \<open>(C,C')\<in>nat_rel\<close> and
    DD': \<open>(D,D')\<in>clause_hash\<close> and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    shrunken: \<open>shrunken = mset shrunken'\<close> and
    cands: \<open>Suc (length shrunken') \<le> length (get_tvdom S)\<close>
  shows \<open>isa_try_to_forward_subsume_wl2 C D shrunken' S \<le>
    \<Down>{((D, shrunken, U), (occs, D', shrunken', S')). (D,D')\<in>clause_hash \<and> (get_occs U, occs) \<in> occurrence_list_ref \<and>
       (U, S') \<in> twl_st_heur_restart_occs' r u \<and> get_aivdom U = get_aivdom S \<and> shrunken' = mset shrunken}
    (try_to_forward_subsume_wl2 C' occs cands D' shrunken S')\<close>
proof -
  have le: \<open>length (get_clauses_wl S' \<propto> C) \<le> Suc (unat32_max div 2)\<close>
    if \<open>try_to_forward_subsume_wl2_pre C' cands shrunken S'\<close>
  proof -
    have lits:  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_init_atms_st S') (mset (get_clauses_wl S' \<propto> C'))\<close> and
      dist: \<open>distinct_mset (mset (get_clauses_wl S' \<propto> C'))\<close> and
      tauto: \<open>\<not> tautology (mset (get_clauses_wl S' \<propto> C'))\<close>
      using that unfolding try_to_forward_subsume_wl2_pre_def try_to_forward_subsume_wl_pre_def
        try_to_forward_subsume_pre_def
      apply -
      subgoal
        apply normalize_goal+
        apply (frule literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def)
        apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth)
        apply (simp add: literals_are_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n'_def)
        apply (simp add: literals_are_in_\<L>\<^sub>i\<^sub>n_nth literals_are_\<L>\<^sub>i\<^sub>n_cong
          literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff)
        done
      subgoal
        apply normalize_goal+
        unfolding twl_struct_invs_def twl_st_inv_alt_def
        by (simp add:mset_take_mset_drop_mset')
      subgoal
        apply normalize_goal+
        unfolding twl_list_invs_def
        by (simp add:mset_take_mset_drop_mset')
      done
    have \<open>isasat_input_bounded (all_init_atms_st S')\<close>
      using SS' unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
      by (simp del: isasat_input_bounded_def)
    then show ?thesis
      using simple_clss_size_upper_div2[of \<open>all_init_atms_st S'\<close> \<open>mset (get_clauses_wl S' \<propto> C')\<close>, OF _ lits dist tauto] CC'
      by auto
  qed
  have loop_rel: \<open>(ebreak, ebreaka) \<in> bool_rel \<Longrightarrow>
    try_to_forward_subsume_wl2_inv S' cands C' (0, False, ebreaka, occs, D', S') \<Longrightarrow>
    ((0, NONE, ebreak, D, S), 0, False, ebreaka, occs, D', S') \<in> 
    {((m, b, brk, D, U),(m', b', brk', occs, D', V)). (m,m')\<in>nat_rel \<and> b'=(b\<noteq>NONE) \<and> (brk,brk')\<in>bool_rel \<and>
    (D,D')\<in>clause_hash \<and> (get_occs U, occs) \<in> occurrence_list_ref \<and> (U, V) \<in> twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<and>
    get_aivdom U = get_aivdom S}\<close>
    for ebreak ebreaka
    using assms by auto
  have [refine]: \<open>RETURN (is_strengthened x1f) \<le> \<Down> bool_rel (RES UNIV)\<close> for x1f
    by (auto simp:)

  have [refine]: \<open>isa_try_to_forward_subsume_wl2_break S \<le> SPEC (\<lambda>_. True)\<close> for S
    unfolding isa_try_to_forward_subsume_wl2_break_def by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isa_try_to_forward_subsume_wl2_def
      try_to_forward_subsume_wl2_def mop_arena_length_st_def Let_def[of \<open>if _ then mark_clause_for_unit_as_unchanged _ else _\<close>]
    apply (refine_vcg mop_arena_lit[of \<open>get_clauses_wl_heur S\<close> _ \<open>set (get_vdom S)\<close> for S]
      mop_arena_length[THEN fref_to_Down_curry, of _ _ _ _ \<open>set (get_vdom S)\<close>, unfolded comp_def] loop_rel
      isa_forward_subsumption_one_forward_subsumption_wl_one[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>]
      mop_cch_remove_all_clauses_mop_ch_remove_all_clauses[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>])
    subgoal
      using assms unfolding isa_try_to_forward_subsume_wl_pre_def apply -
      by (rule exI[of _ S'], rule exI[of _ r], rule exI[of _ u], rule exI[of _ cands], rule exI[of _ occs])
        auto
    subgoal using SS' CC' unfolding isa_try_to_forward_subsume_wl_pre_def try_to_forward_subsume_wl2_pre_def try_to_forward_subsume_wl_pre_def
      try_to_forward_subsume_pre_def
      by - (normalize_goal+; auto)
    subgoal using SS' CC' unfolding twl_st_heur_restart_occs_def by simp
    subgoal using le CC' by auto
    subgoal for n ebreak ebreaka x x' using CC' SS' unfolding isa_try_to_forward_subsume_wl_inv_def case_prod_beta apply -
      by (rule exI[of _ S'], rule exI[of _ \<open>snd (snd (snd (snd (snd (x')))))\<close>],
        rule exI[of _ cands], rule exI[of _ \<open>fst ((snd (snd (snd (x')))))\<close>], rule exI[of _ \<open>fst (snd (snd (snd (snd (x')))))\<close>]; cases x')
        auto
    subgoal by simp
    subgoal by auto
    subgoal for n ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g
      x2g x1h x2h
      by (auto simp: twl_st_heur_restart_occs_def)
    subgoal using CC' by auto
    subgoal by auto
    subgoal by auto
    subgoal using CC' by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using CC' by auto
    subgoal by auto
    subgoal using CC' by auto
    subgoal by auto
    subgoal using cands by auto
    subgoal using SS' CC' shrunken by auto
    done
qed



definition clause_not_marked_to_delete_init_pre where
  \<open>clause_not_marked_to_delete_init_pre =
    (\<lambda>(S, C). C \<in> vdom_m (all_init_atms_st S) (get_watched_wl S) (get_clauses_wl S))\<close>

lemma clause_not_marked_to_delete_rel_occs:
  \<open>(S,T)\<in>twl_st_heur_restart_occs \<Longrightarrow> (C,C')\<in>nat_rel \<Longrightarrow> C \<in> set(get_vdom S) \<Longrightarrow>
  (clause_not_marked_to_delete_heur S C, clause_not_marked_to_delete T C') \<in> bool_rel\<close>
    by (cases S, cases T)
     (use arena_dom_status_iff[of \<open>get_clauses_wl_heur S\<close> \<open>get_clauses_wl T\<close>
      \<open>set (get_vdom S)\<close> \<open>C\<close>] in_dom_in_vdom in
      \<open>auto 5 5 simp: clause_not_marked_to_delete_def twl_st_heur_restart_occs_def Let_def
        clause_not_marked_to_delete_heur_def all_init_atms_st_def
        clause_not_marked_to_delete_init_pre_def ac_simps; blast\<close>)

lemma mop_polarity_pol_mop_polarity_wl:
  \<open>(S,T)\<in>twl_st_heur_restart_occs \<Longrightarrow> (L,L')\<in>nat_lit_lit_rel\<Longrightarrow>L'\<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)\<Longrightarrow>
  mop_polarity_pol (get_trail_wl_heur S) L \<le> \<Down>Id (mop_polarity_wl T L')\<close>
  unfolding mop_polarity_pol_def mop_polarity_wl_def
  apply refine_vcg
  subgoal
    by (rule polarity_pol_pre[of _ \<open>get_trail_wl T\<close> \<open>all_init_atms_st T\<close>])
     (auto simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def)
  subgoal
    by (auto intro!: polarity_pol_polarity[of \<open>(all_init_atms_st T)\<close>, unfolded option_rel_id_simp, THEN fref_to_Down_unRET_uncurry_Id] simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms IsaSAT_Restart.all_init_atms_alt_def twl_st_heur_restart_occs_def)
      done


lemma isa_all_lit_clause_unset_all_lit_clause_unset:
  assumes \<open>(S, T) \<in> twl_st_heur_restart_occs' r u\<close> \<open>(C,C')\<in>nat_rel\<close> and
    \<open>isa_all_lit_clause_unset_pre C S\<close>
  shows
    \<open>isa_all_lit_clause_unset C S \<le> \<Down> bool_rel (all_lit_clause_unset T C')\<close>
proof -
  have [refine]: \<open>((0,True, added), (0,True))\<in>{((a,b,c), (d,e)). ((a,b), (d,e))\<in>nat_rel \<times>\<^sub>f bool_rel}\<close> for added
    by auto
  have lits:  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_init_atms_st T) (mset (get_clauses_wl T \<propto> C))\<close> and
    dist: \<open>distinct_mset (mset (get_clauses_wl T \<propto> C))\<close> and
    tauto: \<open>\<not> tautology (mset (get_clauses_wl T \<propto> C))\<close>
    if \<open>C \<in># dom_m (get_clauses_wl T)\<close> \<open>forward_subsumption_all_wl_pre T\<close>
    using that unfolding forward_subsumption_all_wl_pre_def forward_subsumption_all_pre_def
    apply -
    subgoal
      apply normalize_goal+
      apply (frule literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def)
      apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth)
      apply (simp add: literals_are_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n'_def)
      apply (simp add: literals_are_in_\<L>\<^sub>i\<^sub>n_nth literals_are_\<L>\<^sub>i\<^sub>n_cong
        literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff)
      done
    subgoal
      apply normalize_goal+
      unfolding twl_struct_invs_def twl_st_inv_alt_def
      by (simp add:mset_take_mset_drop_mset')
    subgoal
      apply normalize_goal+
      unfolding twl_list_invs_def
      by (simp add:mset_take_mset_drop_mset')
    done
  have \<open>heuristic_rel (all_init_atms_st T) (get_heur S)\<close>
    using assms unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def by fast
  then have is_marked_added_heur_pre_stats: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T) \<Longrightarrow>is_marked_added_heur_pre (get_heur S) (atm_of L)\<close> for L
    by (auto simp: is_marked_added_heur_pre_stats_def heuristic_rel_def heuristic_rel_stats_def phase_saving_def is_marked_added_heur_pre_def
      dest!: multi_member_split)
  show ?thesis
    unfolding isa_all_lit_clause_unset_def all_lit_clause_unset_def mop_clause_not_marked_to_delete_heur_def
      nres_monad3 clause_not_marked_to_delete_def[symmetric] mop_arena_length_st_def
      mop_is_marked_added_heur_st_def mop_is_marked_added_heur_def
    apply (refine_vcg clause_not_marked_to_delete_rel_occs mop_arena_lit[where vdom=\<open>set (get_vdom S)\<close>]
      mop_polarity_pol_mop_polarity_wl
      mop_arena_length[THEN fref_to_Down_curry, unfolded comp_def, of _ _ \<open>get_clauses_wl_heur S\<close> _ \<open>set (get_vdom S)\<close> for S])
    subgoal using assms by fast
    subgoal using assms unfolding clause_not_marked_to_delete_heur_pre_def isa_all_lit_clause_unset_pre_def
      by (auto simp: arena_is_valid_clause_vdom_def twl_st_heur_restart_occs_def
        intro!: exI[of _ \<open>get_clauses_wl T\<close>]
        exI[of _ \<open>set (get_vdom S)\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms unfolding clause_not_marked_to_delete_init_pre_def
      by (auto simp: isa_all_lit_clause_unset_pre_def)
    subgoal using assms by auto
    subgoal by (auto simp: clause_not_marked_to_delete_def)
    subgoal using assms unfolding twl_st_heur_restart_occs_def by auto
    subgoal by auto
    subgoal
      using assms(1,2) simple_clss_size_upper_div2[of \<open>all_init_atms_st T\<close> \<open>mset (get_clauses_wl T \<propto> C)\<close>, OF _ lits dist tauto]
      by (auto simp del: isasat_input_bounded_def simp: clause_not_marked_to_delete_def
        simp: twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def)
    subgoal by (auto simp: unat32_max_def)
    subgoal using assms unfolding twl_st_heur_restart_occs_def by auto
    subgoal using assms by fast
    subgoal by auto
    subgoal using assms by auto
    subgoal by (rule is_marked_added_heur_pre_stats) auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma valid_occs_empty:
  assumes \<open>(occs, empty_occs_list A) \<in> occurrence_list_ref\<close>
  shows \<open>valid_occs occs vdom\<close> and \<open>cocc_content_set occs = {}\<close>
proof -
  show \<open>cocc_content_set occs = {}\<close>
    using assms
    apply (auto simp: valid_occs_def empty_occs_list_def occurrence_list_ref_def
    map_fun_rel_def cocc_content_set_def in_set_conv_nth)
    by (smt (verit, del_insts) fst_conv image_iff)
  then show \<open>valid_occs occs vdom\<close>
    using in_cocc_content_iff by (fastforce simp: valid_occs_def empty_occs_list_def occurrence_list_ref_def
    map_fun_rel_def cocc_content_set_def)
qed

lemma twl_st_heur_restart_occs'_avdom_nth_vdom:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow> i < length (get_avdom S) \<Longrightarrow>
  get_avdom S ! i \<in> set (get_vdom S)\<close> and
  twl_st_heur_restart_occs'_ivdom_nth_vdom:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow> i < length (get_ivdom S) \<Longrightarrow>
  get_ivdom S ! i \<in> set (get_vdom S)\<close> 
  using nth_mem[of i \<open>get_avdom S\<close>] nth_mem[of i \<open>get_ivdom S\<close>]
  by (auto simp: twl_st_heur_restart_occs_def aivdom_inv_dec_alt_def simp del: nth_mem)

lemma isa_is_candidate_forward_subsumption:
  assumes S: \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> \<open>C \<in># dom_m (get_clauses_wl S')\<close> and
    pre: \<open>forward_subsumption_all_wl_pre S'\<close>
  shows \<open>isa_is_candidate_forward_subsumption S C \<le> \<Down> bool_rel (RES UNIV)\<close>
proof -
  have 1: \<open>\<Down> bool_rel (RES UNIV) = SPEC (\<lambda>_::bool. True)\<close>
    by (auto)
  have valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close> and
    heur: \<open>heuristic_rel (all_init_atms_st S') (get_heur S)\<close> and
    trail: \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_init_atms_st S')\<close>
    using assms unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def by fast+
  have H: \<open>is_marked_added_heur_pre (get_heur S)
    (atm_of (arena_lit (get_clauses_wl_heur S) (C + a)))\<close> and
    H': \<open>(atm_of (arena_lit (get_clauses_wl_heur S) (C + a))) \<in># all_init_atms_st S'\<close>
    if \<open>a < arena_length (get_clauses_wl_heur S) C\<close> for a
  proof -
    have no_alien: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S')) = set_mset (all_lits_st S')\<close>
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of S', THEN \<L>\<^sub>a\<^sub>l\<^sub>l_cong] pre
      unfolding forward_subsumption_all_wl_pre_def
        forward_subsumption_all_pre_def apply -
      by normalize_goal+
       (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms)

    have \<open>a < length (get_clauses_wl S' \<propto> C)\<close>
      using valid assms that by (auto simp: arena_lifting)
    then have \<open>atm_of (get_clauses_wl S' \<propto> C ! a) \<in># all_atms_st S'\<close>
      using assms that by (auto simp: arena_lifting all_lits_def ran_m_def all_lits_of_mm_add_mset image_Un atm_of_all_lits_of_m(2)
        all_atms_st_def all_atms_def simp del: all_atms_def[symmetric] dest!: multi_member_split[of C])
    then show \<open>(atm_of (arena_lit (get_clauses_wl_heur S) (C + a))) \<in># all_init_atms_st S'\<close>
      using valid assms that no_alien  apply (auto simp: arena_lifting)
      using \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n by blast
    then show \<open>is_marked_added_heur_pre (get_heur S) (atm_of (arena_lit (get_clauses_wl_heur S) (C + a)))\<close>
      using heur unfolding heuristic_rel_def
      by (auto simp: is_marked_added_heur_pre_def is_marked_added_heur_pre_stats_def
        heuristic_rel_stats_def phase_saving_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
  qed
  show ?thesis
    using valid
    unfolding isa_is_candidate_forward_subsumption_def
      mop_arena_lbd_st_def mop_arena_lbd_def mop_arena_status_st_def nres_monad3
      mop_arena_status_def bind_to_let_conv mop_arena_length_st_def
      mop_arena_length_def 1 mop_arena_lit_def mop_arena_lit2_def
      mop_is_marked_added_heur_def mop_polarity_st_heur_def mop_polarity_pol_def
    apply (refine_vcg 
       WHILET_rule[where R = \<open>measure (\<lambda>(i,_). length (get_clauses_wl S' \<propto> C) - i)\<close> and I = \<open>\<lambda>(i,_). i \<le> length (get_clauses_wl S' \<propto> C)\<close>])
    subgoal
      using assms by (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def)
    subgoal
      using assms by (auto simp: get_clause_LBD_pre_def arena_is_valid_clause_idx_def)
    subgoal
      using assms by (auto simp: arena_is_valid_clause_idx_def)
    subgoal
      using assms by (auto simp: arena_is_valid_clause_vdom_def)
    subgoal using arena_lifting[OF valid, of C] assms by auto
    subgoal
      by (auto intro!: RETURN_SPEC_refine)
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto simp: arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
        arena_lifting
      intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _ C])
    subgoal using assms by (auto intro: H)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal by auto
    done
qed

lemma valid_occs_push_to_tvdom[intro!]:
  \<open>valid_occs occs aivdom \<Longrightarrow> valid_occs occs (push_to_tvdom C aivdom)\<close>
  unfolding valid_occs_def by auto

lemma valid_occs_empty_vdom[intro!]:
  \<open>valid_occs occs vdom \<Longrightarrow> valid_occs occs (empty_tvdom vdom)\<close>
  by (auto simp: valid_occs_def)


lemma valid_arena_vdom_le_strong:
  assumes \<open>valid_arena arena N ovdm\<close>
  shows \<open>card ovdm \<le> length arena - 2\<close>
proof -
  have incl: \<open>ovdm \<subseteq> {MIN_HEADER_SIZE..< length arena}\<close>
    apply auto
    using assms valid_arena_in_vdom_le_arena by blast+
  from card_mono[OF _ this] show \<open>card ovdm \<le> length arena - 2\<close> by auto
qed

lemma
  assumes SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close>
  shows
    twl_st_heur_restart_occs'_avdom_vdom: \<open>x1 < length (get_avdom S) \<Longrightarrow> get_avdom S ! x1 \<in> set (get_vdom S)\<close> and
    twl_st_heur_restart_occs'_ivdom_vdom: \<open>x1 < length (get_ivdom S) \<Longrightarrow> get_ivdom S ! x1 \<in> set (get_vdom S)\<close> and
    twl_st_heur_restart_occs'_length_vdom_clauses: \<open>length (get_vdom S) \<le> length (get_clauses_wl_heur S)\<close> and
    twl_st_heur_restart_occs'_length_tvdom_clauses: \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur S)\<close> and
    twl_st_heur_restart_occs'_length_tvdom_clauses_notin: \<open>C \<in> set (get_vdom S) \<Longrightarrow> Suc (length (get_tvdom S)) < length (get_clauses_wl_heur S)\<close>
      \<open>C \<in> set (get_vdom S) \<Longrightarrow>  (length (get_tvdom S)) < length (get_clauses_wl_heur S)\<close> and
    twl_st_heur_restart_occs'_length_avdom_ivdom: \<open>length (get_avdom S @ get_ivdom S) \<le> length (get_vdom S)\<close> and
    twl_st_heur_restart_occs'_length_avdom_ivdom_clauses: \<open>length (get_avdom S @ get_ivdom S) \<le> length (get_clauses_wl_heur S)\<close>
proof -
  have arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close> and
    aivdom: \<open>aivdom_inv_dec (get_aivdom S) (dom_m (get_clauses_wl S'))\<close>
    using SS' unfolding twl_st_heur_restart_occs_def by fast+
  show \<open>x1 < length (get_avdom S) \<Longrightarrow> get_avdom S ! x1 \<in> set (get_vdom S)\<close>
    using aivdom nth_mem[of x1 \<open>get_avdom S\<close>] unfolding aivdom_inv_dec_alt_def
    by (auto simp add: distinct_card simp del: nth_mem)
  show \<open>x1 < length (get_ivdom S) \<Longrightarrow> get_ivdom S ! x1 \<in> set (get_vdom S)\<close>
    using aivdom nth_mem[of x1 \<open>get_ivdom S\<close>] unfolding aivdom_inv_dec_alt_def
    by (auto simp add: distinct_card simp del: nth_mem)
  show 1: \<open>length (get_vdom S) \<le> length (get_clauses_wl_heur S)\<close>
    using valid_arena_vdom_le_strong[OF arena] aivdom unfolding aivdom_inv_dec_alt_def
    by (simp add: distinct_card)
  show \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur S)\<close>
    using valid_arena_vdom_le(2)[OF arena] aivdom unfolding aivdom_inv_dec_alt_def
    by (auto simp add: distinct_card dest!: size_mset_mono)
  have WTF: \<open>a \<ge>1 \<Longrightarrow> a \<le> b - 2 \<Longrightarrow> Suc a < b\<close> for a b :: nat
    by auto

  have \<open>mset (get_avdom S @ get_ivdom S) \<subseteq># mset (get_vdom S)\<close>
    unfolding aivdom_inv_dec_alt_def2
    apply (auto simp del: size_mset simp flip: size_mset)
    by (smt (z3) List.finite_set Un_iff aivdom aivdom_inv_dec_alt_def2 mset_set_Union mset_set_set mset_set_subset_iff subset_iff)
  from size_mset_mono[OF this] show 2: \<open>length (get_avdom S @ get_ivdom S) \<le> length (get_vdom S)\<close>
    using aivdom distinct_mset_mono[of \<open>mset (get_avdom S)\<close> \<open>mset (get_vdom S)\<close>] distinct_mset_mono[of \<open>mset (get_ivdom S)\<close> \<open>mset (get_vdom S)\<close>]
    unfolding aivdom_inv_dec_alt_def2
    by (auto simp del: size_mset simp flip: size_mset)

  show \<open>length (get_avdom S @ get_ivdom S) \<le> length (get_clauses_wl_heur S)\<close>
    using 1 2 by linarith
  assume \<open>C \<in> set (get_vdom S)\<close>
  then have \<open>get_vdom S \<noteq> []\<close>
    by auto
  then show \<open>C \<in> set (get_vdom S) \<Longrightarrow> Suc (length (get_tvdom S)) < length (get_clauses_wl_heur S)\<close>
    \<open>C \<in> set (get_vdom S) \<Longrightarrow>  (length (get_tvdom S)) < length (get_clauses_wl_heur S)\<close>
    using valid_arena_vdom_le_strong[OF arena] aivdom WTF[of \<open>length (get_vdom S)\<close> \<open>length (get_clauses_wl_heur S)\<close>]
    unfolding aivdom_inv_dec_alt_def
    by (auto simp add: distinct_card dest!: size_mset_mono)
qed

lemma isa_populate_occs:
  assumes SS': \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_populate_occs S \<le> \<Down>{(U,(occs, cands')). (U, S') \<in> twl_st_heur_restart_occs' r u \<and>
    (get_tvdom U, cands')\<in>Id \<and> get_vdom U = get_vdom S \<and> (get_occs U, occs) \<in> occurrence_list_ref} (populate_occs S')\<close>
proof -
  have SS'': \<open>(S,S')\<in>twl_st_heur_restart_occs' r u\<close> and
    aivdom: \<open>aivdom_inv_dec (get_aivdom S) (dom_m (get_clauses_wl S'))\<close> and
    occs: \<open>(get_occs S, empty_occs_list (all_init_atms_st S')) \<in> occurrence_list_ref\<close>
    using SS' unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
      twl_st_heur_restart_ana_def case_wl_split state_wl_recompose twl_st_heur_restart_def
    by (auto simp add: valid_occs_empty)
  have [refine]: \<open>RETURN (get_occs S) \<le> \<Down> occurrence_list_ref (mop_occ_list_create (set_mset (all_init_atms_st S')))\<close>
    using valid_occs_empty[OF occs] occs
    by (auto simp: mop_occ_list_create_def empty_occs_list_def)

  have [refine0]: \<open>empty_tvdom_st S \<le> SPEC (\<lambda>c. (c, []) \<in> {(V,cands). cands=[] \<and>
      (V,S')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<and>
      get_tvdom V = [] \<and> get_occs V = get_occs S \<and> get_clauses_wl_heur V = get_clauses_wl_heur S \<and>
      get_vdom V = get_vdom S \<and> get_ivdom V = get_ivdom S\<and> get_avdom V = get_avdom S})\<close>
    (is \<open>_ \<le> SPEC (\<lambda>c. (c, _) \<in> ?empty)\<close>)
    using SS'' unfolding empty_tvdom_st_def
    by (auto simp add: twl_st_heur_restart_occs_def)

  have [refine]: \<open>(get_occs T, occs) \<in> occurrence_list_ref \<Longrightarrow> (T, cands) \<in> ?empty \<Longrightarrow>
    ((0, T), 0, occs, []) \<in> {((w, U), (w', occs, cands')).
      get_avdom U = get_avdom S \<and>
      get_ivdom U = get_ivdom S \<and>
      get_vdom U = get_vdom S \<and>
      (w,w')\<in>nat_rel \<and> (get_tvdom U, cands')\<in>Id \<and> (get_occs U, occs)\<in>occurrence_list_ref \<and>
    (U, S')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S)}\<close> (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?loop\<close>) for occs xs cands T
   by simp

 have sorted: \<open>sort_cands_by_length x2b
   \<le> \<Down> {(U, cands). (U, S') \<in> twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<and>  get_avdom U = get_avdom x2b \<and>
   get_ivdom U = get_ivdom x2b \<and> get_vdom U = get_vdom x2b \<and> get_occs U = get_occs x2b \<and>
   get_tvdom U = cands}
   (SPEC
   (\<lambda>cands'.
   mset cands' = mset x2a \<and>
   sorted_wrt (\<lambda>a b. length (get_clauses_wl S' \<propto> a) \<le> length (get_clauses_wl S' \<propto> b))
   cands'))\<close>
   if
     H: \<open>forward_subsumption_all_wl_pre S'\<close>
     \<open>(get_avdom S @ get_ivdom S, xs) \<in> Id\<close>
     \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close>
     \<open>(x, x') \<in> ?loop\<close>
     \<open>x2 = (x1a, x2a)\<close>
     \<open>x' = (x1, x2)\<close>
     \<open>x = (x1b, x2b)\<close>
     \<open>(S\<^sub>0, cands) \<in> ?empty\<close>
     \<open>\<forall>C\<in>set x2a. C \<in># dom_m (get_clauses_wl S') \<and> C \<in> set xs \<and> 2 < length (get_clauses_wl S' \<propto> C)\<close>
   for xs occs x x' x1 x2 x1a x2a x1b x2b cands S\<^sub>0
 proof -
   have K: \<open>sorted_wrt (\<lambda>a b. length (get_clauses_wl S' \<propto> a) \<le> length (get_clauses_wl S' \<propto> b)) tvdom\<close>
     if \<open>sorted_wrt (\<lambda>a b. arena_length (get_clauses_wl_heur x2b) a \<le> arena_length (get_clauses_wl_heur x2b) b)
       (tvdom)\<close> and
       \<open>mset tvdom = mset (get_tvdom x2b)\<close>
     for tvdom
     apply (rule sorted_wrt_mono_rel[of _ \<open>(\<lambda>a b. arena_length (get_clauses_wl_heur x2b) a
       \<le> arena_length (get_clauses_wl_heur x2b) b)\<close>
       \<open>(\<lambda>a b. length (get_clauses_wl S' \<propto> a) \<le> length (get_clauses_wl S' \<propto> b))\<close>])
     subgoal for a b
       using H(1-7,9) mset_eq_setD[OF that(2)] by (auto simp: twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
         arena_lifting)
     subgoal  using that(1) . done
     show ?thesis
       using that unfolding sort_cands_by_length_def
       apply refine_vcg
       subgoal
         by (auto intro!: ASSERT_leI
           simp: arena_lifting twl_st_heur_restart_occs_def
           arena_is_valid_clause_idx_def
           intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _ \<open>set (get_vdom S)\<close>]
           dest: mset_eq_setD)
       subgoal for tvdom
         apply (subst RETURN_RES_refine_iff)
         apply (rule_tac x=tvdom in bexI)
         defer
       subgoal
         by (auto simp: twl_st_heur_restart_occs_def RETURN_RES_refine_iff valid_occs_def
           aivdom_inv_dec_alt_def simp del: distinct_mset_mset_distinct
           simp flip: distinct_mset_mset_distinct dest: mset_eq_setD
           dest!: K)
       subgoal
         apply (clarsimp simp: twl_st_heur_restart_occs_def
           aivdom_inv_dec_alt_def simp del: distinct_mset_mset_distinct
           simp flip: distinct_mset_mset_distinct dest: mset_eq_setD)
         apply (simp add: valid_occs_def)
         done
       done
     done
  qed

  have [simp]: \<open>\<not> x1 < length (get_avdom S) \<Longrightarrow> x1 - length (get_avdom S) < length (get_ivdom S) \<longleftrightarrow> x1 < length (get_avdom S) + length (get_ivdom S)\<close> for x1
    by linarith
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isa_populate_occs_def populate_occs_def mop_arena_length_st_def
      push_to_tvdom_st_def Let_def[of \<open>length (get_avdom S)\<close>]
    apply (refine_vcg isa_all_lit_clause_unset_all_lit_clause_unset[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>]
      mop_arena_length[where vdom=\<open>set(get_vdom S)\<close>, THEN fref_to_Down_curry, unfolded comp_def]
      isa_push_to_occs_list_st_push_to_occs_list2[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>learned_clss_count S\<close>]
      isa_is_candidate_forward_subsumption[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>learned_clss_count S\<close>])
    subgoal using twl_st_heur_restart_occs'_length_avdom_ivdom_clauses[OF SS''] by auto
    subgoal using aivdom unfolding aivdom_inv_dec_alt_def by (auto dest: distinct_mset_mono)
    subgoal by auto
    apply assumption
    subgoal for xs occs Sa x x' unfolding isa_populate_occs_inv_def case_prod_beta
      by (rule exI[of _ S'], rule exI[of _ \<open>S'\<close>], rule exI[of _ \<open>fst (snd (x'))\<close>], cases x') (use SS'' in clarsimp)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_avdom_at_pre_def)
    subgoal by (auto simp: access_ivdom_at_pre_def)
    subgoal for xs occs T x x' x1 x2 x1a x2a x1b x2b
      using
        twl_st_heur_restart_occs'_avdom_vdom[of x2b S' _ \<open>learned_clss_count S\<close> x1]
        twl_st_heur_restart_occs'_ivdom_vdom[of x2b S' _ \<open>learned_clss_count S\<close> \<open>x1 - length (get_avdom S)\<close>]
      by (auto simp: nth_append)
    subgoal by auto
    subgoal by (auto simp: nth_append)
    subgoal
      using SS''
      unfolding isa_all_lit_clause_unset_pre_def apply -
      by (rule  exI[of _ S'], rule exI[of _ \<open>length (get_clauses_wl_heur S)\<close>] , rule exI[of _ \<open>learned_clss_count S\<close>])
       (simp add: twl_st_heur_restart_occs'_avdom_nth_vdom twl_st_heur_restart_occs'_ivdom_nth_vdom SS''
        eq_commute[of \<open>get_avdom S @ get_ivdom S\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal premises p using p(2-) by (clarsimp simp add: twl_st_heur_restart_occs_def nth_append)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: nth_append)
    subgoal by auto
    subgoal by (auto simp: unat32_max_def nth_append)
    subgoal by auto
    apply (solves auto)
    subgoal by (auto simp: nth_append)
    subgoal by auto
    subgoal by auto
    subgoal for xs occs T x x' x1 x2 x1a x2a x1b x2b all_undef all_undefa n cand canda
      using twl_st_heur_restart_occs'_length_vdom_clauses[of x2b S' _ \<open>learned_clss_count S\<close>] by simp
    subgoal for xs occs T x x' x1 x2 x1a x2a x1b x2b all_undef all_undefa n cand canda
      using twl_st_heur_restart_occs'_length_tvdom_clauses_notin[of x2b S' _ \<open>learned_clss_count S\<close> \<open>xs ! x1\<close>]
        twl_st_heur_restart_occs'_avdom_vdom[of x2b S' _ \<open>learned_clss_count S\<close> x1]
        twl_st_heur_restart_occs'_ivdom_vdom[of x2b S' _ \<open>learned_clss_count S\<close> \<open>x1 - length (get_avdom S)\<close>]
      by (auto simp: nth_append)
    subgoal premises p using p(2-) by (clarsimp intro!: aivdom_push_to_tvdom simp: nth_append twl_st_heur_restart_occs_def)
       (intro conjI impI aivdom_push_to_tvdom; clarsimp)
    subgoal by auto
      apply (rule sorted; assumption)
    subgoal for xs occs x x' x1 x2 x1a x2a x1b x2b V sorted_cands
      using SS' by (auto simp: twl_st_heur_restart_ana_def)
    done
qed


lemma empty_occs2_replicate_empty: \<open>empty_occs2 occs \<le> SPEC (\<lambda>c. (c, replicate (length occs) []) \<in> Id)\<close>
proof -
  show ?thesis
    unfolding empty_occs2_def
    apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i,_). length occs -i)\<close> and
      I = \<open> \<lambda>(i, occs'). i \<le> length occs \<and> length occs = length occs' \<and> take i occs' = replicate i []\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: take_Suc_conv_app_nth replicate_Suc_conv_snoc list_update_append simp del: replicate_Suc)
    subgoal by auto
    subgoal by auto
    done
qed


lemma empty_occs2_st_empty_occs_st: \<open>empty_occs2_st S \<le> \<Down>Id (empty_occs_st S)\<close>
  unfolding empty_occs2_st_def empty_occs_st_def
  by (refine_vcg empty_occs2_replicate_empty) auto

lemma empty_occs_st:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow>
  fst occs = set_mset (all_init_atms_st S') \<Longrightarrow>
  (get_occs S, occs) \<in> occurrence_list_ref \<Longrightarrow>
  empty_occs_st S\<le>SPEC(\<lambda>c. (c,S')\<in>twl_st_heur_restart_ana' r u)\<close>
  unfolding empty_occs_st_def twl_st_heur_restart_occs_def twl_st_heur_restart_ana_def IsaSAT_Restart.all_init_atms_alt_def
    twl_st_heur_restart_def occurrence_list_ref_def empty_occs_list_def
  by (auto, auto simp: map_fun_rel_def)

lemma empty_occs2_st:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow>
  fst occs = set_mset (all_init_atms_st S') \<Longrightarrow>
  (get_occs S, occs) \<in> occurrence_list_ref \<Longrightarrow>
  empty_occs2_st S\<le>SPEC(\<lambda>c. (c,S')\<in>twl_st_heur_restart_ana' r u)\<close>
  apply (rule order_trans[OF empty_occs2_st_empty_occs_st])
  apply (subst Down_id_eq)
  by (rule empty_occs_st)


lemma [intro!]: \<open>heuristic_rel A heur \<Longrightarrow> heuristic_rel A (reset_added_heur heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def reset_added_heur_def reset_added_heur_stats_def
    schedule_next_pure_lits_stats_def phase_saving_def)


lemma mop_mark_added_heur_st_it:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_occs' r u\<close> and \<open>A \<in># all_init_atms_st T\<close>
  shows \<open>mop_mark_added_heur_st A S \<le> SPEC (\<lambda>c. (c, T) \<in> {(U, V). (U, V) \<in> twl_st_heur_restart_occs' r u \<and> (get_clauses_wl_heur U) = get_clauses_wl_heur S \<and>
       learned_clss_count U = learned_clss_count S \<and> get_vdom U = get_vdom S \<and> get_occs U = get_occs S})\<close>
proof -
  have heur: \<open>heuristic_rel (all_init_atms_st T) (get_heur S)\<close>
    using assms(1)
    by (auto simp: twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def)

  show ?thesis
    unfolding mop_mark_added_heur_st_def mop_mark_added_heur_def
    apply refine_vcg
    subgoal
      using heur assms(2)
      unfolding mark_added_heur_pre_def mark_added_heur_pre_stats_def
      by (auto simp: heuristic_rel_def heuristic_rel_stats_def
        phase_saving_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        dest!: multi_member_split)
    subgoal by (use assms in \<open>auto simp add: twl_st_heur_restart_occs_def\<close>)
    done
qed
lemma mark_added_clause_heur2_id:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_occs' r u\<close> and \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
  shows \<open>mark_added_clause_heur2 S C
     \<le> \<Down>{(U, V). (U, V) \<in> twl_st_heur_restart_occs' r u \<and> (get_clauses_wl_heur U) = get_clauses_wl_heur S \<and>
       learned_clss_count U = learned_clss_count S \<and> get_vdom U = get_vdom S \<and>
       get_occs U = get_occs S} (RETURN T)\<close> (is \<open>_ \<le>\<Down>?R _\<close>)
proof -
  have 1: \<open>mark_added_clause2 T C \<le> \<Down>Id (RETURN T)\<close>
    unfolding mark_added_clause2_def mop_clauses_at_def nres_monad3
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i,_). length (get_clauses_wl T \<propto> C) -i)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (use assms in auto)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  have eq: \<open>set_mset (all_init_atms_st T) = set_mset (all_atms_st T)\<close>
    using lits by (simp add: literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def)
  have [refine]: \<open>y' \<in># dom_m x' \<Longrightarrow>
    ((x, y), x', y') \<in> {(N, N'). valid_arena N N' (set (get_vdom S))} \<times>\<^sub>f nat_rel \<Longrightarrow>
    mop_arena_length x y \<le> SPEC (\<lambda>y. (y, length (x' \<propto> y')) \<in> {(a,b). (a,b)\<in>nat_rel \<and> a = length (x' \<propto> y')})\<close> for x y x' y'
    apply (rule mop_arena_length[THEN fref_to_Down_curry, of _ _ _ _ \<open>set (get_vdom S)\<close>, unfolded comp_def conc_fun_RETURN prod.simps, THEN order_trans])
    apply assumption
    apply assumption
    by auto
  have [refine]: \<open>((0, S), 0, T) \<in> nat_rel \<times>\<^sub>r ?R\<close>
    using assms by auto
  have 2: \<open>mark_added_clause_heur2 S C \<le> \<Down>?R (mark_added_clause2 T C)\<close>
    unfolding mark_added_clause_heur2_def mop_arena_length_st_def mop_access_lit_in_clauses_heur_def
      mark_added_clause2_def
    apply (refine_vcg mop_mark_added_heur_st_it[where r=r and u=u])
    subgoal by (use assms in auto)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_restart_occs_def\<close>)
    subgoal using assms by (auto simp: twl_st_heur_restart_occs_def dest: arena_lifting(10))
    subgoal by auto
    subgoal by auto
    apply (rule_tac vdom = \<open>set (get_vdom (x2a))\<close> in mop_arena_lit2)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_restart_occs_def\<close>)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (use assms in \<open>auto simp: eq all_atms_st_def all_atms_def all_lits_def ran_m_def
        all_lits_of_mm_add_mset image_Un atm_of_all_lits_of_m(2)
      dest!: multi_member_split\<close>)
    subgoal by auto
    subgoal by auto
    done
  show ?thesis
    unfolding mop_arena_length_st_def mop_access_lit_in_clauses_heur_def
    apply (rule order_trans[OF 2])
    apply (rule ref_two_step')
    apply (rule 1[unfolded Down_id_eq])
    done
qed

lemma isa_forward_reset_added_and_stats:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow>
  (isa_forward_reset_added_and_stats S, S') \<in> twl_st_heur_restart_occs' r u\<close>
  by (auto simp add: IsaSAT_Restart.all_init_atms_alt_def twl_st_heur_restart_occs_def incr_forward_rounds_st_def
    isa_forward_reset_added_and_stats_def)

(*TODO Move*)
lemma [intro!]: \<open>heuristic_rel \<A> (get_heur S) \<Longrightarrow> heuristic_rel \<A> (schedule_next_subsume delta (get_heur S))\<close>
  by (auto simp: schedule_next_subsume_def heuristic_rel_def heuristic_rel_stats_def
    schedule_next_subsume_stats_def)

lemma schedule_next_subsume_st:
  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow>
  (schedule_next_subsume_st delta S, S') \<in> twl_st_heur_restart_occs' r u\<close>
  by (auto simp add: IsaSAT_Restart.all_init_atms_alt_def twl_st_heur_restart_occs_def incr_forward_rounds_st_def
    schedule_next_subsume_st_def)

lemma
  get_occs_schedule_next_subsume_st[simp]: \<open>get_occs (schedule_next_subsume_st delta S) = get_occs S\<close> and
  get_vdom_schedule_next_subsume_st[simp]: \<open>get_vdom (schedule_next_subsume_st delta S) = get_vdom S\<close>
  by (auto simp: schedule_next_subsume_st_def)

lemma forward_subsumption_finalize:
  assumes
    \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close>
    \<open>fst occs = set_mset (all_init_atms_st S')\<close>
    \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    shrunken: \<open>\<forall>C\<in>#mset shrunken. C \<in> set (get_vdom S)\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S'\<close>
 shows \<open>forward_subsumption_finalize shrunken S\<le>SPEC(\<lambda>c. (c,S')\<in>twl_st_heur_restart_ana' r u)\<close> (is \<open>_ \<le> ?C\<close>)
proof -
  have
    1: \<open>(RETURN S') \<ge> do {
    let S = S;
    let _ = True;
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i,S). i \<le> length shrunken \<and> S=S'\<^esup>(\<lambda>(i,S). i < length shrunken) (\<lambda>(i,S). do {
      ASSERT (i < length shrunken);
      let C = shrunken ! i;
      b \<leftarrow> RES (UNIV :: bool set);
      let S = S';
      RETURN (i+1, S)
    }) (0, S');
    ASSERT (S = S');
    RETURN S
        }\<close>
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i,_). length shrunken - i)\<close>])
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
  have [refine]: \<open>isasat_current_progress c (isa_forward_reset_added_and_stats (schedule_next_subsume_st delta S))  \<le> SPEC (\<lambda>c. (c, True) \<in> UNIV)\<close> for c delta
   unfolding isasat_current_progress_def by auto
  have [refine]: \<open>((0, isa_forward_reset_added_and_stats (schedule_next_subsume_st delta S)), 0, S') \<in> nat_rel \<times>\<^sub>r {(U,U'). (U,U') \<in> twl_st_heur_restart_occs' r u \<and> get_vdom U = get_vdom S \<and>
    get_occs U = get_occs S}\<close> (is \<open>_ \<in> _ \<times>\<^sub>r ?state\<close>) for delta
    using assms isa_forward_reset_added_and_stats[of \<open>schedule_next_subsume_st delta S\<close> S' r u]
      schedule_next_subsume_st[of S S' r u]
    by (auto simp: isa_forward_reset_added_and_stats_def)
  have [refine]: \<open>RETURN (clause_not_marked_to_delete_heur x2a (shrunken ! x1a))
    \<le> \<Down> {(b,b'). b=b' \<and> b'=(shrunken!x1a\<in>#dom_m (get_clauses_wl S'))} (RES UNIV)\<close>
    if \<open>(x2a, S') \<in> ?state\<close> \<open>x1a < length shrunken\<close>
    for x2a x1a
    using that shrunken arena_dom_status_iff(1)[of \<open>get_clauses_wl_heur x2a\<close> \<open>get_clauses_wl S'\<close> \<open>set (get_vdom x2a)\<close> \<open>shrunken ! x1a\<close>]
    by (auto simp: clause_not_marked_to_delete_heur_def IsaSAT_Restart.all_init_atms_alt_def
      twl_st_heur_restart_occs_def conc_fun_RES)
  show ?thesis
    unfolding forward_subsumption_finalize_def
      mop_clause_not_marked_to_delete_heur_def nres_monad3
      conc_fun_RETURN[symmetric] Let_def[of \<open>isasat_current_progress _ _\<close>]
    apply (rule ref_two_step[OF _ 1])
    apply (refine_vcg clause_not_marked_to_delete_rel[THEN fref_to_Down_unRET_uncurry]
      mark_added_clause_heur2_id[unfolded conc_fun_RETURN, of _ S' r u, THEN order_trans]
      empty_occs2_st[where occs = occs])
    subgoal by auto
    subgoal by auto
    subgoal using shrunken
      by (auto simp: clause_not_marked_to_delete_heur_pre_def twl_st_heur_restart_occs_def
          arena_is_valid_clause_vdom_def
        intro!: exI[of _ \<open>get_clauses_wl S'\<close>] exI[of _  \<open>set (get_vdom S)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using lits by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by (auto simp: isa_forward_reset_added_and_stats_def)
    subgoal using assms by auto
    done
qed


lemma all_init_lits_of_wl_Pos_Neg_def:
  \<open>set_mset (all_init_lits_of_wl S') = Pos ` set_mset (all_init_atms_st S') \<union> Neg ` set_mset (all_init_atms_st S')\<close>
  apply (auto simp: all_init_atms_st_alt_def image_image)
  using literal.exhaust_sel apply blast
  apply (simp add: in_all_lits_of_wl_ain_atms_of_iff)
  apply (simp add: in_all_lits_of_wl_ain_atms_of_iff)
  done

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_restart_occs:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_restart_occs \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_restart_occs_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def
     split: option.splits)

lemma mop_cch_add_all_clause_mop_ch_add_all:
  assumes  \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> \<open>(C,C')\<in>nat_rel\<close>
    \<open>(D, D')\<in>clause_hash\<close> and \<open>C'\<in>#dom_m (get_clauses_wl S')\<close>
  shows \<open>mop_cch_add_all_clause S C D \<le> \<Down>clause_hash (mop_ch_add_all (mset (get_clauses_wl S' \<propto> C')) D')\<close>
proof -
  have 1: \<open>mop_ch_add_all_clause S' C' D' \<le>\<Down>Id (mop_ch_add_all (mset (get_clauses_wl S' \<propto> C')) D')\<close>
    unfolding mop_ch_add_all_clause_def mop_ch_add_all_def mop_clauses_at_def mop_ch_add_def
    apply (refine_vcg
      WHILET_rule[where I=\<open>\<lambda>(i, D). i \<le> length (get_clauses_wl S' \<propto> C') \<and>
      D=ch_add_all (mset (take i (get_clauses_wl S' \<propto> C'))) D'\<close> and
      R = \<open>measure (\<lambda>(i,_). length (get_clauses_wl S' \<propto> C') - i)\<close>])
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: ch_add_all_def)
    subgoal by auto
    subgoal unfolding ch_add_pre_def ch_add_all_pre_def ch_add_all_def
      by (auto simp: take_Suc_conv_app_nth distinct_in_set_take_iff)
       (meson disjunct_not_in nth_mem_mset)
    subgoal by auto
    subgoal by (auto simp: ch_add_all_def take_Suc_conv_app_nth ch_add_def case_prod_beta)
    subgoal by auto
    subgoal by auto
    done
  have [refine]: \<open>((0, D), 0, D') \<in> nat_rel \<times>\<^sub>r clause_hash\<close>
    using assms by auto
  show ?thesis
    apply (rule ref_two_step[OF _ 1[unfolded Down_id_eq]])
    unfolding mop_cch_add_all_clause_def mop_ch_add_all_clause_def mop_arena_length_st_def
      mark_literal_for_unit_deletion_def Let_def[of "()"]
    apply (refine_vcg mop_arena_length[where vdom = \<open>set (get_vdom S)\<close>,THEN fref_to_Down_curry, unfolded comp_def, of \<open>get_clauses_wl S'\<close> C']
      mop_arena_lit[where vdom=\<open>set (get_vdom S)\<close>] mop_cch_add_mop_cch_add)
    subgoal using assms by auto
    subgoal using assms unfolding twl_st_heur_restart_occs_def by auto
    subgoal
      using arena_lifting(10)[of \<open>get_clauses_wl_heur S\<close> \<open>get_clauses_wl S'\<close> \<open>set (get_vdom S)\<close> C] assms
      unfolding twl_st_heur_restart_occs_def by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal using assms unfolding twl_st_heur_restart_occs_def by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma isa_forward_set_budget:
  assumes SS': \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_forward_set_budget S \<le> \<Down>{(U,V). (U, V) \<in> twl_st_heur_restart_ana' r u \<and> V = S' \<and>
    get_clauses_wl_heur U = get_clauses_wl_heur S \<and> learned_clss_count U = learned_clss_count S \<and> get_vdom U = get_vdom S} (RETURN S')\<close>
proof -
  show ?thesis
    using assms
    unfolding isa_forward_set_budget_def
    by (auto simp add: Let_def twl_st_heur_restart_ana_def twl_st_heur_restart_def)
qed

lemma get_occs_incr_forward_rounds_st[simp]: \<open>get_occs (incr_forward_rounds_st S) = get_occs S\<close>
  \<open>get_occs (isa_forward_reset_added_and_stats S) = get_occs S\<close>
  \<open>get_clauses_wl_heur (incr_forward_tried_st S) = (get_clauses_wl_heur S)\<close>
  \<open>learned_clss_count (incr_forward_tried_st S) = learned_clss_count S\<close>
  \<open>get_aivdom (incr_forward_tried_st S) = get_aivdom S\<close>
  \<open>get_occs (incr_forward_tried_st S) = get_occs S\<close>
  by (auto simp: incr_forward_rounds_st_def isa_forward_reset_added_and_stats_def
    incr_forward_tried_st_def)

lemma isa_forward_subsumption_all_forward_subsumption_wl_all2:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_forward_subsumption_all S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (forward_subsumption_all_wl2 S')\<close>
proof -
  have SS'': \<open>(S,S')\<in>twl_st_heur_restart_occs' r u\<close>
    using assms unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
      twl_st_heur_restart_ana_def case_wl_split state_wl_recompose twl_st_heur_restart_def
    by (auto simp add: valid_occs_empty)

  have [refine]: \<open> (get_occs x2a, occs) \<in> occurrence_list_ref \<and> (D, D') \<in>clause_hash \<and> (x2a, S') \<in> twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<Longrightarrow>
   ((0, D, [], x2a), 0, occs, D', S', 2, {#}) \<in>
    {((m, D, shrunken, U), (n, occs, D', U', _, shrunken')). (m,n)\<in>nat_rel \<and> (D,D')\<in>clause_hash \<and> (get_occs U, occs) \<in> occurrence_list_ref \<and>
      shrunken' = mset shrunken \<and>
    (U, U') \<in> twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S)\<and> get_aivdom U = get_aivdom x2a}\<close> for x2a occs D D' S'
    by auto
  have H: \<open>(S, S') \<in> twl_st_heur_restart_occs' r u \<Longrightarrow>
    \<forall>L\<in>fst ` D\<^sub>1 (set_mset (all_init_atms_st S')). L < length (get_watched_wl_heur S)\<close> for S S' r u
    apply (intro ballI impI)
    unfolding  twl_st_heur_restart_occs_def map_fun_rel_def IsaSAT_Restart.all_init_atms_alt_def
        in_pair_collect_simp \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) all_init_lits_of_wl_Pos_Neg_def[symmetric]
      by normalize_goal+ auto

  have H2: \<open>(Sa, U)   \<in> twl_st_heur_restart_occs \<Longrightarrow>
    (incr_forward_tried_st Sa, U) \<in> twl_st_heur_restart_occs\<close> for Sa U
    by (auto simp: twl_st_heur_restart_occs_def incr_forward_tried_st_def)
  have H3: \<open>C \<in> set x1h \<Longrightarrow>
     (Sa, S') \<in> twl_st_heur_restart_occs \<Longrightarrow>
     mset x1h \<subseteq># mset (get_tvdom Sa) \<Longrightarrow>
     get_vdom Sa = get_vdom S \<Longrightarrow>
     C \<in> set (get_vdom S)\<close>
    for C x1h Sa
    using multi_member_split[of C \<open>mset x1h\<close>] multi_member_split[of C \<open>mset (get_tvdom Sa)\<close>]
    unfolding twl_st_heur_restart_occs_def IsaSAT_Restart.all_init_atms_alt_def
      aivdom_inv_dec_alt_def
    by (auto dest: mset_subset_eqD dest!: mset_subset_eq_insertD)
  have forward_subsumption_all_wl2_alt_def:
    \<open>forward_subsumption_all_wl2 = (\<lambda>S. do {
      ASSERT (forward_subsumption_all_wl_pre S);
      S \<leftarrow> RETURN S;
      (occs, xs) \<leftarrow> SPEC (populate_occs_spec S);
      let m = length xs;
      D \<leftarrow> mop_ch_create (set_mset (all_init_atms_st S));
      let shrunken = {#};
      (_, occs, D, S, _, shrunken) \<leftarrow>
        WHILE\<^sub>T\<^bsup> forward_subsumption_all_wl2_inv S xs \<^esup> (\<lambda>(i, occs, D, S, n, shrunken). i < m \<and> get_conflict_wl S = None)
          (\<lambda>(i, occs, D, S, n, shrunken). do {
          let C = xs!i;
          ASSERT(C\<in>#dom_m (get_clauses_wl S));
          D \<leftarrow> mop_ch_add_all (mset (get_clauses_wl S \<propto> C)) D;
          (occs, D, shrunken, T) \<leftarrow> try_to_forward_subsume_wl2 C occs (mset (drop (i) xs)) D shrunken S;
          RETURN (i+1, occs, D, T, (length (get_clauses_wl S \<propto> C)), shrunken)
        })
        (0, occs, D, S, 2, shrunken);
      ASSERT (fst occs = set_mset (all_init_atms_st S));
      ASSERT (shrunken \<subseteq># mset xs);
      ASSERT (literals_are_\<L>\<^sub>i\<^sub>n' S);
      RETURN S
    })\<close>
    unfolding forward_subsumption_all_wl2_def nres_monad3 by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isa_forward_subsumption_all_def
      forward_subsumption_all_wl2_alt_def Let_def
    apply (refine_vcg ref_two_step[OF isa_populate_occs populate_occs_populate_occs_spec,
      unfolded Down_id_eq, of _ _ \<open>length (get_clauses_wl_heur S)\<close>  \<open>(learned_clss_count S)\<close>]
      forward_subsumption_finalize[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>]
      mop_cch_create_mop_cch_create
      mop_cch_add_all_clause_mop_ch_add_all[where r=\<open>length (get_clauses_wl_heur S)\<close> and u=\<open>(learned_clss_count S)\<close>]
      isa_try_to_forward_subsume_wl2_try_to_forward_subsume_wl2[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>]
      isa_forward_reset_added_and_stats[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>]
      isa_forward_set_budget[where r=\<open>length (get_clauses_wl_heur S)\<close>  and u=\<open>(learned_clss_count S)\<close>])
    subgoal using assms unfolding isa_forward_subsumption_pre_all_def by blast
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: isasat_fast_relaxed_def)
    subgoal by (auto simp: isasat_fast_relaxed_def)
    subgoal unfolding forward_subsumption_all_wl_pre_def by blast
    subgoal unfolding forward_subsumption_all_wl_pre_def by blast
    subgoal by (auto simp: isasat_fast_relaxed_def)
    subgoal by (rule H) auto
    subgoal by auto
    subgoal by auto
    subgoal for S\<^sub>0 Sa Saa x' x1 x2 D Da x x'a
      using SS'' unfolding isa_forward_subsumption_all_wl_inv_def apply (case_tac x, hypsubst, unfold prod.simps)
      by (rule exI[of _ S'], rule exI[of _ S'], rule exI[of _ \<open>fst (snd (snd (snd x'a)))\<close>],
        rule_tac x= \<open>fst (snd (snd (x'a)))\<close> in exI, rule_tac x= \<open>fst (snd x'a)\<close> in exI,
        rule_tac x=\<open>fst (snd (snd (snd (snd x'a))))\<close> in exI)
       auto
    subgoal by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None_restart_occs[THEN fref_to_Down_unRET_Id])
      (auto simp: get_conflict_wl_is_None_def)
    subgoal by auto
    subgoal by (auto simp: access_tvdom_at_pre_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp
    subgoal by (clarsimp dest!: size_mset_mono simp add: forward_subsumption_all_wl2_inv_def)
    subgoal by (auto simp add:H2)
    subgoal by (clarsimp simp add: H3)
    apply (solves auto)
    apply assumption
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    done
qed

lemma isa_forward_subsumption_all_forward_subsumption_wl_all:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_forward_subsumption_all S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (forward_subsumption_all_wl S')\<close>
  apply (rule ref_two_step)
  apply (rule isa_forward_subsumption_all_forward_subsumption_wl_all2)
  apply (rule assms)
  apply (rule forward_subsumption_all_wl2_forward_subsumption_all_wl[unfolded Down_id_eq])
  done

lemma isa_forward_subsume_forward_subsume_wl:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_forward_subsume S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (forward_subsume_wl S')\<close>
proof -
  have [refine]: \<open>RETURN (should_subsume_st S)  \<le> \<Down> bool_rel (forward_subsume_wl_needed S')\<close>
    unfolding forward_subsume_wl_needed_def by auto
  show ?thesis
    using assms
    unfolding forward_subsume_wl_def isa_forward_subsume_def
    by (refine_vcg isa_forward_subsumption_all_forward_subsumption_wl_all) auto
qed

end
