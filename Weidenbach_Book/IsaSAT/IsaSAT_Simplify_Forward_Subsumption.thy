theory IsaSAT_Simplify_Forward_Subsumption
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Restart
  (*  IsaSAT_Simplify_Units*)
    IsaSAT_Occurence_List
begin


section \<open>Forward subsumption\<close>

subsection \<open>Algorithm\<close>

text \<open>We first refine the algorithm to use occurence lists, while keeping as many things as possible
  abstract (like the candidate selection or the selection of the literal with the least number
  of occurrences). We also include the marking structure (at least abstractly, because why not)

  For simplicity, we keep the occurrence list outside of the state (unlike the current solver where
  this is part of the state.)\<close>



definition subsume_clauses_match2_pre :: \<open>nat \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>subsume_clauses_match2_pre C C' N D  \<longleftrightarrow>
  subsume_clauses_match_pre C C' (get_clauses_wl N) \<and>
  snd D = mset (get_clauses_wl N \<propto> C')\<close>

definition subsume_clauses_match2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> clause_hash \<Rightarrow> nat subsumption nres\<close> where
  \<open>subsume_clauses_match2 C C' N D = do {
  ASSERT (subsume_clauses_match2_pre C C' N D);
  let n = length (get_clauses_wl N \<propto> C);
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). try_to_subsume C' C ((get_clauses_wl N)(C \<hookrightarrow> take i (get_clauses_wl N \<propto> C))) s\<^esup> (\<lambda>(i, st). i < n\<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      L \<leftarrow> mop_clauses_at (get_clauses_wl N) C i;
      lin \<leftarrow> mop_ch_in L D;
      if lin
      then RETURN (i+1, st)
      else do {
      lin \<leftarrow> mop_ch_in (-L) D;
      if lin
      then if is_subsumed st
      then RETURN (i+1, STRENGTHENED_BY L C)
      else RETURN (i+1, NONE)
      else RETURN (i+1, NONE)
    }})
     (0, SUBSUMED_BY C);
  RETURN st
  }\<close>
(*TODO move*)
lemma image_msetI: \<open>x \<in># A \<Longrightarrow> f x \<in># f `# A\<close>
  by (auto)

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
    by (auto intro!: nth_in_all_lits_stI image_msetI
      simp del: all_atms_st_alt_def[symmetric])
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


definition forward_subsumption_one_wl2_inv :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat multiset \<Rightarrow> nat list \<Rightarrow>
  nat \<times> 'v subsumption \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl2_inv = (\<lambda>S C cands ys (i, x). forward_subsumption_one_wl_inv S C (mset ys) (mset (drop i ys), x))\<close>

definition push_to_occs_list2_pre :: \<open>_\<close> where
  \<open>push_to_occs_list2_pre C S occs \<longleftrightarrow>
    C \<in># dom_m (get_clauses_wl S) \<and> length (get_clauses_wl S \<propto> C) \<ge> 2\<close>

definition push_to_occs_list2 where
  \<open>push_to_occs_list2 C S occs = do {
     ASSERT (push_to_occs_list2_pre C S occs);
     L \<leftarrow> SPEC (\<lambda>L. L \<in># mset (get_clauses_wl S \<propto> C));
     mop_occ_list_append C occs L
  }\<close>


definition correct_occurence_list where
  \<open>correct_occurence_list S occs cands n \<longleftrightarrow>
  distinct_mset cands \<and>
  all_occurrences (all_init_atms_st S) occs \<inter># cands = {#} \<and>
  (\<forall>C\<in># all_occurrences (all_init_atms_st S) occs. C \<in># dom_m (get_clauses_wl S) \<longrightarrow> length (get_clauses_wl S \<propto> C) \<le> n)\<and>
  (\<forall>C\<in># all_occurrences (all_init_atms_st S) occs. C \<in># dom_m (get_clauses_wl S) \<longrightarrow>
    (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L)) \<and>
  fst occs = set_mset (all_init_atms_st S)\<close>

definition forward_subsumption_one_wl2_rel where
  \<open>forward_subsumption_one_wl2_rel S\<^sub>0 occs cands n C D = {((S, changed, occs', D'), (T, changed')).
     changed = changed' \<and> set_mset (all_init_atms_st S) = set_mset (all_init_atms_st S\<^sub>0) \<and>
      (changed \<longrightarrow> (D', {#}) \<in> clause_hash_ref (all_init_atms_st S)) \<and>
      (\<not>changed \<longrightarrow> D' = D \<and> occs' = occs \<and> get_clauses_wl S \<propto> C = get_clauses_wl S\<^sub>0 \<propto> C) \<and>
      correct_occurence_list S occs' (if changed then remove1_mset C cands else cands)
        (if changed then size (get_clauses_wl S\<^sub>0 \<propto> C) else n) \<and>
      all_occurrences (all_init_atms_st S) occs' \<subseteq># add_mset C (all_occurrences  (all_init_atms_st S) occs) \<and>
     (S,T)\<in>Id
    }\<close>

lemma remdups_mset_removeAll: \<open>remdups_mset (removeAll_mset a A) = removeAll_mset a (remdups_mset A)\<close>
  by (smt (verit, ccfv_threshold) add_mset_remove_trivial count_eq_zero_iff diff_zero
    distinct_mset_remdups_mset distinct_mset_remove1_All insert_DiffM order.refl remdups_mset_def
    remdups_mset_singleton_sum removeAll_subseteq_remove1_mset replicate_mset_eq_empty_iff
    set_mset_minus_replicate_mset(1) set_mset_remdups_mset subset_mset_removeAll_iff)

(*TODO move*)
text \<open>This is an alternative to @{thm [source] remdups_mset_singleton_sum}.\<close>
lemma remdups_mset_singleton_removeAll:
  "remdups_mset (add_mset a A) = add_mset a (removeAll_mset a (remdups_mset A))"
  by (metis dual_order.refl finite_set_mset mset_set.insert_remove remdups_mset_def
    remdups_mset_removeAll set_mset_add_mset_insert set_mset_minus_replicate_mset(1))

lemma all_occurrences_add_mset: \<open>all_occurrences (add_mset (atm_of L) A) occs =
  all_occurrences (removeAll_mset (atm_of L) A) occs + mset (occ_list occs L) + mset (occ_list occs (-L))\<close>
  by (cases L; cases occs)
    (auto simp: all_occurrences_def occ_list_def remdups_mset_removeAll
    remdups_mset_singleton_removeAll
    removeAll_notin simp del: remdups_mset_singleton_sum)

lemma all_occurrences_add_mset2: \<open>all_occurrences (add_mset (L) A) occs =
  all_occurrences (removeAll_mset (L) A) occs + mset (occ_list occs (Pos L)) + mset (occ_list occs (Neg L))\<close>
  by (cases occs)
    (auto simp: all_occurrences_def occ_list_def remdups_mset_removeAll
    remdups_mset_singleton_removeAll
    removeAll_notin simp del: remdups_mset_singleton_sum)

lemma all_occurrences_insert_lit:
  \<open>all_occurrences A (insert (atm_of L) B, occs) = all_occurrences (A) (B, occs)\<close> and
  all_occurrences_occ_list_append_r:
  \<open>all_occurrences (removeAll_mset (atm_of L) A) (B, occ_list_append_r L C b) =
    all_occurrences (removeAll_mset (atm_of L) A) (B, b)\<close>
  apply (auto simp: all_occurrences_def)
  by (smt (verit) distinct_mset_remdups_mset distinct_mset_remove1_All image_mset_cong2
    literal.sel(1) literal.sel(2) remdups_mset_removeAll removeAll_subseteq_remove1_mset
    subset_mset_removeAll_iff)

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
    undef: \<open>\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L\<close>
  shows \<open>push_to_occs_list2 C S occs \<le> SPEC (\<lambda>c. (c, ()) \<in> {(occs', occs'').
    all_occurrences (all_init_atms_st S) occs' = add_mset C (all_occurrences  (all_init_atms_st S) occs) \<and>
    correct_occurence_list S occs' (remove1_mset C cands) (max n (length (get_clauses_wl S \<propto> C)))})\<close>
proof -
  have \<open>atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_atms_st S)\<close>
    using nth_in_all_lits_stI[of C S] assms(2)
    unfolding all_atms_st_alt_def
    by (auto simp del: all_atms_st_alt_def[symmetric] simp: in_set_conv_nth)

  then show ?thesis
    using literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[OF lin]
    unfolding push_to_occs_list2_def
    apply (refine_vcg mop_occ_list_append[THEN order_trans])
    subgoal using assms unfolding push_to_occs_list2_pre_def by fast
    subgoal using assms unfolding occ_list_append_pre_def correct_occurence_list_def
      by auto
    subgoal for L occs'
      using multi_member_split[of \<open>atm_of L\<close> \<open>all_init_atms_st S\<close>]
      apply (subgoal_tac \<open>atm_of L \<in># all_init_atms_st S\<close>)
      apply (cases occs)
      by (use assms literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[OF lin] in
        \<open>auto 4 2 simp: occ_list_append_def correct_occurence_list_def
        all_occurrences_add_mset occ_list_def all_occurrences_insert_lit
        all_occurrences_occ_list_append_r distinct_mset_remove1_All
        intro: inter_mset_empty_removeAll_msetI\<close>)
   done
qed

definition forward_subsumption_one_wl2_pre :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl2_pre = (\<lambda>C cands L S.
  forward_subsumption_one_wl_pre C cands S \<and> L \<in># all_init_lits_of_wl S)\<close>

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
  occs \<leftarrow> (if is_strengthened s then push_to_occs_list2 C S occs else RETURN occs);
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
    get_trail_wl x = get_trail_wl S \<and>
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
            by (auto split: subsumption.splits simp: state_wl_recompose)
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
      subsume_clauses_match2_subsume_clauses_match push_to_occs_list2 DG[unfolded G])
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


definition try_to_forward_subsume_wl2_inv :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl2_inv S cands  C = (\<lambda>(i, changed, break, occs, D, T).
  try_to_forward_subsume_wl_inv S cands C (i, break, T) \<and>
  (\<not>changed \<longrightarrow> (D, mset (get_clauses_wl T \<propto> C)) \<in> clause_hash_ref (all_init_atms_st T)) \<and>
  (changed \<longrightarrow> (D, {#}) \<in> clause_hash_ref (all_init_atms_st T)))\<close>

definition try_to_forward_subsume_wl2_pre :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl2_pre C cands S \<longleftrightarrow>
    distinct_mset cands \<and>
    try_to_forward_subsume_wl_pre C cands S\<close>

definition try_to_forward_subsume_wl2 :: \<open>nat \<Rightarrow> occurences \<Rightarrow> nat multiset \<Rightarrow> clause_hash \<Rightarrow> nat twl_st_wl \<Rightarrow> (occurences \<times> clause_hash \<times> nat twl_st_wl) nres\<close> where
  \<open>try_to_forward_subsume_wl2 C occs cands D S = do {
  ASSERT (try_to_forward_subsume_wl2_pre C cands S);
  let n = 2 * length (get_clauses_wl S \<propto> C);
  ebreak \<leftarrow> RES {_::bool. True};
  (_, changed, _, occs, D, S) \<leftarrow> WHILE\<^sub>T\<^bsup> try_to_forward_subsume_wl2_inv S cands C\<^esup>
    (\<lambda>(i, changed, break, occs, D, S). \<not>break \<and> i < n)
    (\<lambda>(i, changed, break, occs, D, S). do {
      let L = (if i mod 2 = 0 then get_clauses_wl S \<propto> C ! (i div 2) else - (get_clauses_wl S \<propto> C ! (i div 2)));
      (S, subs, occs, D) \<leftarrow> forward_subsumption_one_wl2 C cands L occs D S;
      ebreak \<leftarrow> RES {_::bool. True};
      RETURN (i+1, subs, subs \<or> ebreak, occs, D, S)
    })
  (0, False, ebreak, occs, D, S);
  D \<leftarrow> (if \<not>changed then mop_ch_remove_all (mset (get_clauses_wl S \<propto>  C)) D else RETURN D);
  RETURN (occs, D, S)
  }\<close>

definition try_to_forward_subsume_wl2_pre0 :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl2_pre0 G C occs cands D S\<^sub>0 n \<longleftrightarrow>
  correct_occurence_list S\<^sub>0 occs cands n \<and>
  n\<le> length (get_clauses_wl S\<^sub>0 \<propto> C) \<and>
  C \<notin># all_occurrences (all_init_atms_st S\<^sub>0) occs \<and>
  distinct_mset cands \<and>
  G = mset (get_clauses_wl S\<^sub>0 \<propto> C)\<close>

lemma try_to_forward_subsume_wl2_try_to_forward_subsume_wl:
  assumes \<open>(C, E) \<in> nat_rel\<close> and
    DG: \<open>(D, G) \<in> clause_hash_ref (all_init_atms_st T\<^sub>0)\<close> and
    pre: \<open>try_to_forward_subsume_wl2_pre0 G C occs cands D S\<^sub>0 n\<close> and
    \<open>(S\<^sub>0, T\<^sub>0) \<in> Id\<close>
    \<open>(cands, cands') \<in> Id\<close>
  shows \<open>try_to_forward_subsume_wl2 C occs cands D S\<^sub>0 \<le>
    \<Down>{((occs', D', T), U). (T, U) \<in> Id \<and> (D', {#}) \<in> clause_hash_ref (all_init_atms_st T) \<and>
       correct_occurence_list U occs' (remove1_mset C cands) (max (length (get_clauses_wl S\<^sub>0 \<propto> C)) n) \<and>
       all_occurrences (all_init_atms_st U) occs' \<subseteq># add_mset C (all_occurrences  (all_init_atms_st S\<^sub>0) occs)}
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

  have [refine]: \<open>(ebreak, ebreaka) \<in> bool_rel \<Longrightarrow>
    ((0, False, ebreak, occs, D, S\<^sub>0), 0, ebreaka, S\<^sub>0) \<in>
    {((p, changed, ebreak, occs', D', U), (q, ebreak', V)). (p,q)\<in>nat_rel \<and>
      (\<not>changed \<longrightarrow> (D', mset (get_clauses_wl U \<propto> C)) \<in> clause_hash_ref (all_init_atms_st U)) \<and> 
      (changed \<longrightarrow> ebreak \<and> (D', {#}) \<in> clause_hash_ref (all_init_atms_st U)) \<and> 
    (ebreak, ebreak') \<in> bool_rel \<and>
    (\<not>changed \<longrightarrow> correct_occurence_list U occs' cands n \<and> occs' = occs \<and> get_clauses_wl U \<propto> C = get_clauses_wl S\<^sub>0 \<propto> C \<and>
        all_occurrences (all_init_atms_st V) occs' = all_occurrences  (all_init_atms_st S\<^sub>0) occs) \<and>
    (changed \<longrightarrow> correct_occurence_list U occs' (remove1_mset C cands) (max (length (get_clauses_wl S\<^sub>0 \<propto> C)) n) \<and>
       all_occurrences (all_init_atms_st V) occs' \<subseteq># add_mset C (all_occurrences  (all_init_atms_st S\<^sub>0) occs)) \<and>
    U = V}\<close> (is \<open>_ \<Longrightarrow> _ \<in> ?R\<close>)
    for ebreak ebreaka
    using assms by (auto simp: try_to_forward_subsume_wl2_pre0_def)
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
    subgoal
      by (auto simp: clause_hash_ref_def ch_remove_all_def)
    done
  show ?thesis
    unfolding try_to_forward_subsume_wl2_def try_to_forward_subsume_wl_alt_def eq
    apply (refine_vcg DG[unfolded G]
      forward_subsumption_one_wl2_forward_subsumption_one_wl[where n=n])
    subgoal using assms unfolding try_to_forward_subsume_wl2_pre_def try_to_forward_subsume_wl2_pre0_def by fast
    subgoal by fast
    subgoal using G unfolding try_to_forward_subsume_wl2_inv_def by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal using DG G by (auto dest: clause_hash_ref_cong[OF try_to_forward_subsume_wl2_invD])
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
    apply (rule mop_ch_remove_all2; assumption)
    subgoal by auto
    subgoal for na ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
      using n by (auto simp: eq intro: correct_occurence_list_size_mono correct_occurence_list_mono_candsI)
    done
qed


definition forward_subsumption_all_wl2_inv :: \<open>nat twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> _ \<times> _ \<times> nat twl_st_wl \<times> nat \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_wl2_inv = (\<lambda>S xs (i, occs, D, s, n).
  (D, {#}) \<in> clause_hash_ref (all_init_atms_st s) \<and>
  forward_subsumption_all_wl_inv S (mset xs) (mset (drop i xs), s))
  \<close>

(*TODO populate occs*)

definition populate_occs_inv where
  \<open>populate_occs_inv S xs = (\<lambda>(i, occs, cands).
  all_occurrences (all_init_atms_st S) occs + mset cands \<subseteq># mset (take i xs) \<inter># dom_m (get_clauses_wl S) \<and>
  distinct cands \<and>
  correct_occurence_list S occs (mset (drop i xs)) 2 \<and>
  all_occurrences (all_init_atms_st S) occs \<inter># mset cands = {#} \<and>
  (\<forall>C\<in># all_occurrences (all_init_atms_st S) occs. C \<in># dom_m (get_clauses_wl S) \<and>
    (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L) \<and> length (get_clauses_wl S \<propto> C) = 2) \<and>
  (\<forall>C\<in>set cands. C \<in># dom_m (get_clauses_wl S) \<and>  length (get_clauses_wl S \<propto> C) > 2 \<and> (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L)))\<close>


definition populate_occs_spec where
  \<open>populate_occs_spec S = (\<lambda>(occs, cands).
  all_occurrences (all_init_atms_st S) occs + mset cands \<subseteq># dom_m (get_clauses_wl S) \<and>
  distinct cands \<and> sorted_wrt (\<lambda>a b. length (get_clauses_wl S \<propto> a) \<le> length (get_clauses_wl S \<propto> b)) cands \<and>
  correct_occurence_list S occs (mset cands) 2 \<and>
  (\<forall>C\<in>set cands. \<forall>L\<in> set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L) \<and>
  (\<forall>C\<in>set cands. length (get_clauses_wl S \<propto> C) > 2))\<close>

definition populate_occs :: \<open>nat twl_st_wl \<Rightarrow> _ nres\<close> where
  \<open>populate_occs S = do {
    xs \<leftarrow> SPEC (\<lambda>xs. distinct xs);
    let n = size xs;
    occs \<leftarrow> mop_occ_list_create (set_mset (all_init_atms_st S));
    let cands = [];
    (xs, occs, cands) \<leftarrow> WHILE\<^sub>T\<^bsup>populate_occs_inv S xs\<^esup> (\<lambda>(i, occs, cands). i < n)
    (\<lambda>(i, occs, cands). do {
      let C = xs ! i;
      all_undef \<leftarrow> SPEC (\<lambda>b. b \<longrightarrow> (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L));
      if C \<notin># dom_m (get_clauses_wl S) \<or> \<not>all_undef then
        RETURN (i+1, occs, cands)
      else if length (get_clauses_wl S \<propto> C) = 2 then do {
        occs \<leftarrow> push_to_occs_list2 C S occs;
        RETURN (i+1, occs, cands)
      }
      else  do {
        cand \<leftarrow> SPEC (\<lambda>b. b \<longrightarrow> C \<in># dom_m (get_clauses_wl S) \<and> length (get_clauses_wl S \<propto> C) > 2);
        if cand then RETURN (i+1, occs, cands @ [C])
        else RETURN (i+1, occs, cands)
        }
      }
      )
      (0, occs, cands);
     cands \<leftarrow> SPEC (\<lambda>cands'. mset cands' = mset cands \<and> sorted_wrt (\<lambda>a b. length (get_clauses_wl S \<propto> a) \<le> length (get_clauses_wl S \<propto> b)) cands');
     RETURN (occs, cands)
  }\<close>

lemma populate_occs_populate_occs_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
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
    apply (refine_vcg mop_occ_list_create[THEN order_trans] push_to_occs_list2)
    apply assumption
    subgoal unfolding populate_occs_inv_def by (auto simp: occurrence_list_def all_occurrences_def correct_occurence_list_def)
    subgoal unfolding populate_occs_inv_def by (auto simp: occurrence_list_def take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      dest: subset_mset_imp_subset_add_mset intro: correct_occurence_list_mono_candsI2)
    subgoal by auto
    apply (rule correct_occurence_list; assumption)
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal for x xa s a b aa ba xb xc
      unfolding populate_occs_inv_def apply simp
      by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric] intro: G)
    subgoal by auto
    subgoal for x xa s a b aa ba xb xc
      unfolding populate_occs_inv_def by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      intro: correct_occurence_list_mono_candsI2 intro!: G')
    subgoal by auto
    subgoal unfolding populate_occs_inv_def by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      intro: correct_occurence_list_mono_candsI2 dest: subset_mset_imp_subset_add_mset)
    subgoal by auto
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
  (xs, occs, D, S, _) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_all_wl2_inv S xs \<^esup> (\<lambda>(i, occs, D, S, n). i < m \<and> get_conflict_wl S = None)
    (\<lambda>(i, occs, D, S, n). do {
       let C = xs!i;
       D \<leftarrow> mop_ch_add_all (mset (get_clauses_wl S \<propto> C)) D;
       (occs, D, T) \<leftarrow> try_to_forward_subsume_wl2 C occs (mset (drop (i) xs)) D S;
       RETURN (i+1, occs, D, T, (length (get_clauses_wl S \<propto> C)))
    })
    (0, occs, D, S, 2);
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
  define loop_inv where \<open>loop_inv xs = {((i, occs', D :: clause_hash, U, n), (xsa, V)). (U,V)\<in>Id \<and> i \<le> length xs \<and>
    (D, {#}) \<in> clause_hash_ref (all_init_atms_st V) \<and>
    (i < length xs \<longrightarrow> length (get_clauses_wl U \<propto> (xs!i)) \<ge> n)\<and>
    correct_occurence_list U occs' xsa n \<and> xsa = mset (drop i xs)}\<close> for xs
  have loop_init: \<open>(occsxs, xsa) \<in> ?populate \<Longrightarrow>
    occsxs = (occs, xs) \<Longrightarrow>
    (D, D') \<in> clause_hash_ref (all_init_atms_st S) \<Longrightarrow>
    D' = {#} \<Longrightarrow>
    forward_subsumption_all_wl_inv S (xsa) (xsa, S) \<Longrightarrow> ((0, occs, D, S, 2), xsa, S) \<in> loop_inv xs\<close> 
    (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow>_ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?loopinv\<close>) for D occs xsa aa xs occsxs uu D'
    by (cases xs) (auto simp: populate_occs_spec_def loop_inv_def)
  have [refine]: \<open>(a,b) \<in> Id \<Longrightarrow> (c, d) \<in> Id \<Longrightarrow> simplify_clause_with_unit_st_wl a c \<le>\<Down>Id (simplify_clause_with_unit_st_wl b d)\<close> for a b c d
    by auto


  have try_to_forward_subsume_wl2_pre0:  \<open>\<And>x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db.
    forward_subsumption_all_wl_pre S \<Longrightarrow>
    (x, xs) \<in> ?populate \<Longrightarrow>
    x = (x1, x2) \<Longrightarrow>
    (D, Da) \<in> clause_hash_ref (all_init_atms_st S) \<Longrightarrow>
    Da = {#} \<Longrightarrow>
    (xa, x')  \<in> loop_inv x2 \<Longrightarrow>
    (case xa of (i, occs, D, S, n) \<Rightarrow> i < length x2 \<and> get_conflict_wl S = None) \<Longrightarrow>
    (case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_wl S = None) \<Longrightarrow>
    forward_subsumption_all_wl2_inv S x2 xa \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
    x' = (x1a, x2a) \<Longrightarrow>
    x2d = (x1e, x2e) \<Longrightarrow>
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
  have subsumed_postinv: \<open>\<And>x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db xb Sa a b aa ba.
    forward_subsumption_all_wl_pre S \<Longrightarrow>
    (x, xs) \<in> ?populate \<Longrightarrow>
    x \<in> Collect (populate_occs_spec S) \<Longrightarrow>
    xs \<in> Collect (forward_subsumption_wl_all_cands S) \<Longrightarrow>
    x = (x1, x2) \<Longrightarrow>
    (xa, x') \<in> loop_inv x2 \<Longrightarrow>
    case xa of (i, occs, D, S, n) \<Rightarrow> i < length x2 \<and> get_conflict_wl S = None \<Longrightarrow>
    case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_wl S = None \<Longrightarrow>
    forward_subsumption_all_wl2_inv S x2 xa \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
    x' = (x1a, x2a) \<Longrightarrow>
    x2d = (x1e, x2e) \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    xa = (x1b, x2b) \<Longrightarrow>
    (x2 ! x1b, C) \<in> nat_rel \<Longrightarrow>
    (Db, mset (get_clauses_wl x2a \<propto> C) + {#}) \<in> clause_hash_ref (all_init_atms_st x1e) \<Longrightarrow>
    (xb, Sa)
    \<in> {((occs', D', T), U).
    (T, U) \<in> Id \<and>
    (D', {#}) \<in> clause_hash_ref (all_init_atms_st T) \<and>
    correct_occurence_list U occs' (remove1_mset (x2 ! x1b) (mset (drop x1b x2)))
     (max (length (get_clauses_wl x1e \<propto> (x2 ! x1b))) x2e) \<and>
      all_occurrences (all_init_atms_st U) occs' \<subseteq># add_mset (x2 ! x1b) (all_occurrences (all_init_atms_st x1e) x1c)} \<Longrightarrow>
    \<forall>D\<in>#remove1_mset C x1a. get_clauses_wl Sa \<propto> D = get_clauses_wl x2a \<propto> D \<Longrightarrow>
    xb = (a, b) \<Longrightarrow>
    b = (aa, ba) \<Longrightarrow>
      ((x1b + 1, a, aa, ba, (length (get_clauses_wl x1e \<propto> (x2 ! x1b)))), remove1_mset C x1a, Sa) \<in> loop_inv x2\<close>
    unfolding forward_subsumption_all_inv_def forward_subsumption_all_wl_inv_def
      forward_subsumption_all_wl2_inv_def loop_inv_def populate_occs_spec_def mem_Collect_eq
    apply (hypsubst, unfold prod.simps, normalize_goal+)
    subgoal for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db xb Sa a b aa ba xc xd xe xf
      by (auto simp add: try_to_forward_subsume_wl2_pre0_def populate_occs_spec_def drop_Suc_nth
        dest: sorted_wrt_nth_less[of _ _  x1b \<open>Suc x1b\<close>])
    done

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
    case xa of (i, occs, D, S, n) \<Rightarrow> i < length x2 \<and> get_conflict_wl S = None \<Longrightarrow>
    case x' of (xs, S) \<Rightarrow> xs \<noteq> {#} \<and> get_conflict_wl S = None \<Longrightarrow>
    forward_subsumption_all_wl2_inv S x2 xa \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs x' \<Longrightarrow>
    x' = (x1a, x2a) \<Longrightarrow>
    x2d = (x1e, x2e) \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    xa = (x1b, x2b) \<Longrightarrow>
    (x2 ! x1b, C) \<in> nat_rel \<Longrightarrow>
      atms_of (mset (get_clauses_wl x1e \<propto> (x2 ! x1b))) \<subseteq> set_mset (all_init_atms_st x1e)\<close>
      for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C
    unfolding forward_subsumption_all_inv_def forward_subsumption_all_wl_inv_alt_def
      forward_subsumption_all_wl2_inv_def loop_inv_def populate_occs_spec_def mem_Collect_eq
      all_init_atms_st_alt_def atms_of_def
    apply (hypsubst, unfold prod.simps, normalize_goal+)
    apply (frule literals_are_\<L>\<^sub>i\<^sub>n'_all_init_atms_alt_def[of x1e])
    subgoal
    apply (auto simp: all_init_atms_st_alt_def all_atms_st_alt_def drop_Suc_nth
      simp del: all_atms_st_alt_def[symmetric] intro!: imageI
      in_all_lits_in_cls[of _ _ \<open>x2 ! x1b\<close>])
    done
  done

  show ?thesis
    unfolding forward_subsumption_all_wl_alt_def forward_subsumption_all_wl2_def
    apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
    apply (refine_vcg mop_occ_list_create mop_ch_create mop_ch_add_all
      try_to_forward_subsume_wl2_try_to_forward_subsume_wl)
    apply (rule loop_init; assumption)
    subgoal unfolding forward_subsumption_all_wl2_inv_def loop_inv_def by auto
    subgoal by (auto simp: loop_inv_def)
    subgoal by (auto simp: in_set_dropI loop_inv_def)
    apply (solves \<open>auto simp: loop_inv_def\<close>)
    subgoal by (rule in_atms)
    subgoal by (auto simp: loop_inv_def)
    subgoal by auto
    apply (subst clause_hash_ref_cong)
    defer apply assumption
    apply (rule try_to_forward_subsume_wl2_pre0; assumption)
    subgoal by (auto simp: loop_inv_def)
    subgoal by (auto simp: loop_inv_def)
    subgoal for x xs x1 x2 D Da xa x' x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C Db xb Sa a b aa ba
      by (rule subsumed_postinv)
    subgoal by (auto simp: loop_inv_def)
    subgoal by (auto simp: loop_inv_def)
    done
qed


subsection \<open>Refinement to isasat.\<close>
definition valid_occs where \<open>valid_occs occs vdom \<longleftrightarrow> \<Union> (image set (set occs)) \<subseteq> set (vdom)\<close>

text \<open>This version is equivalent to \<^term>\<open>twl_st_heur_restart\<close>, without any information on the occurrence list.\<close>
definition twl_st_heur_restart_occs :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_restart_occs =
  {(S,T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S; occs = get_occs S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_init_atms N (NE+NEk+NS+N0)) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_init_atms N (NE+NEk+NS+N0)) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N (NE+NEk+NS+N0))) \<and>
    vm \<in> isa_vmtf (all_init_atms N (NE+NEk+NS+N0)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms N (NE+NEk+NS+N0)) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} lcount \<and>
    vdom_m (all_init_atms N (NE+NEk+NS+N0)) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_init_atms N (NE+NEk+NS+N0)) \<and>
    isasat_input_nempty (all_init_atms N (NE+NEk+NS+N0)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_init_atms N (NE+NEk+NS+N0)) heur \<and>
    valid_occs occs (get_vdom_aivdom vdom)
  }\<close>

abbreviation twl_st_heur_restart_occs' :: \<open>_\<close> where
  \<open>twl_st_heur_restart_occs' r u \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart_occs \<and> length (get_clauses_wl_heur S) = r \<and> learned_clss_count S \<le> u}\<close>

(*TODO: this is dumbed currently*)
definition is_candidate_forward_subsumption where
  \<open>is_candidate_forward_subsumption C N = do {
    ASSERT (C \<in># dom_m N);
    SPEC (\<lambda>b :: bool. b \<longrightarrow> \<not>irred  N C \<and> length (N \<propto> C) \<noteq> 2)
  }\<close>


(*TODO dumbed down too*)
definition isa_is_candidate_forward_subsumption where
  \<open>isa_is_candidate_forward_subsumption S C= do {
    ASSERT(arena_act_pre (get_clauses_wl_heur S) C);
    lbd \<leftarrow> mop_arena_lbd (get_clauses_wl_heur S) C;
    length \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
    status \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
    used \<leftarrow> mop_marked_as_used (get_clauses_wl_heur S) C;
    (_, added, unit) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, added, unit). \<not>unit \<and> i < length) 
       (\<lambda>(i, added, unit). do {
           L \<leftarrow> mop_arena_lit (get_clauses_wl_heur S) C;
           is_added \<leftarrow> mop_is_marked_added_heur (get_heur S) (atm_of L);
           val \<leftarrow> mop_polarity_st_heur S L;
           RETURN (i+1, added + (if is_added then 1 else 0), val = None)
    }) (0, 0 :: 64 word, False);
    let can_del =
      length \<noteq> 2 \<and> (status = LEARNED \<longrightarrow> lbd < 100) \<and> (added \<ge> 2) \<and> \<not>unit;
    RETURN can_del
  }\<close>


definition find_best_subsumption_candidate where
  \<open>find_best_subsumption_candidate C S = do {
    L \<leftarrow> mop_arena_lit (get_clauses_wl_heur S) 0;
    ASSERT (nat_of_lit L < length (get_occs S));
    score \<leftarrow> RETURN (length (get_occs S ! nat_of_lit L));
    n \<leftarrow> mop_arena_length_st S C;
   (i,score,L) \<leftarrow> WHILE\<^sub>T (\<lambda>(i,score,L). i < n)
     (\<lambda>(i,score,L). do {
       new_L \<leftarrow> mop_arena_lit (get_clauses_wl_heur S) i;
       ASSERT (nat_of_lit L < length (get_occs S));
       new_score \<leftarrow> RETURN (length (get_occs S ! nat_of_lit new_L));
       if new_score < score then RETURN (i+1, new_score, new_L) else RETURN (i+1, score, L)
    })
    (1, score, L);
    RETURN L
  }\<close>

definition isa_push_to_occs_list_st where
  \<open>isa_push_to_occs_list_st C S = do {
     L \<leftarrow> find_best_subsumption_candidate C S;
     occs \<leftarrow> mop_cocc_list_append C (get_occs S) L;
     RETURN (set_occs_wl_heur occs S)
  }\<close>

definition isa_forward_accumulate_candidades_st :: \<open>_\<close> where
\<open>isa_forward_accumulate_candidades_st S = do {
  ASSERT(length (get_avdom_aivdom (get_aivdom S)) \<le> length (get_clauses_wl_heur S));
  let n = length (get_avdom_aivdom (get_aivdom S));
  (i, S) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i, _). True\<^esup>
    (\<lambda>(i, S). i < n)
    (\<lambda>(i, S). do {
     let C = (get_avdom_aivdom (get_aivdom S)) ! i;
     ASSERT(i < n);
     ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur S) C);
     status \<leftarrow> mop_arena_status_st S C;
     if status \<noteq> DELETED then do{
        should_push \<leftarrow> isa_is_candidate_forward_subsumption S C;
         S \<leftarrow> if should_push then  isa_push_to_occs_list_st C S else RETURN S;
       RETURN (i+1, S)
      }
      else RETURN (i+1, S)
    }) (0, S);
  RETURN (S)
 }\<close>


definition isa_forward_subsumption_one_wl_pre :: \<open>_\<close> where
  \<open>isa_forward_subsumption_one_wl_pre C L S \<longleftrightarrow>
  (\<exists>T r u cands. (S,T)\<in>twl_st_heur_restart_occs' r u \<and> forward_subsumption_one_wl2_pre C cands L T \<and> C \<in> set (get_vdom S)) \<close>

definition isa_forward_subsumption_one_wl2_inv :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow>
  nat \<times> nat subsumption \<Rightarrow> bool\<close> where
  \<open>isa_forward_subsumption_one_wl2_inv = (\<lambda>S C L (ix).
  (\<exists>T r u cands. (S,T)\<in>twl_st_heur_restart_occs' r u \<and>
    forward_subsumption_one_wl2_inv T C cands (get_occs S ! nat_of_lit L) (ix)))\<close>

definition isa_subsume_clauses_match2_pre :: \<open>_\<close> where
  \<open>isa_subsume_clauses_match2_pre C C' S D \<longleftrightarrow> (
  \<exists>T r u D'. (S,T)\<in>twl_st_heur_restart_occs' r u \<and> subsume_clauses_match2_pre C C' T D' \<and>
    (D,D') \<in> clause_hash) \<close>

definition isa_subsume_clauses_match2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> bool list \<Rightarrow> nat subsumption nres\<close> where
  \<open>isa_subsume_clauses_match2 C' C N D = do {
  ASSERT (isa_subsume_clauses_match2_pre C' C N D);
  n \<leftarrow> mop_arena_length_st N C';
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). True\<^esup> (\<lambda>(i, st). i < n\<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur N) C' i;
      lin \<leftarrow> mop_cch_in L D;
      if lin
      then RETURN (i+1, st)
      else do {
      lin \<leftarrow> mop_cch_in (-L) D;
      if lin
      then if is_subsumed st
      then RETURN (i+1, STRENGTHENED_BY L C')
      else RETURN (i+1, NONE)
      else RETURN (i+1, NONE)
    }})
     (0, SUBSUMED_BY C');
  RETURN st
  }\<close>

definition isa_subsume_or_strengthen_wl_pre :: \<open>_\<close> where
  \<open>isa_subsume_or_strengthen_wl_pre C s S \<longleftrightarrow>
   (\<exists>T r u.  (S,T)\<in>twl_st_heur_restart_occs' r u \<and> subsume_or_strengthen_wl_pre C s T)\<close>

(*TODO Move to arena definitions*)
definition mop_arena_set_status where
  \<open>mop_arena_set_status arena C b= do {
    ASSERT(arena_is_valid_clause_vdom arena C);
    RETURN(arena[C - STATUS_SHIFT := AStatus b (arena_used arena C) (arena_lbd arena C)])
  }\<close>

definition  mop_arena_promote_st where
  \<open>mop_arena_promote_st S C = do {
    let N' = get_clauses_wl_heur S;
    let lcount = get_learned_count S;
    ASSERT( clss_size_lcount lcount \<ge> 1);
    let lcount = clss_size_decr_lcount lcount;
    RETURN (set_clauses_wl_heur N' (set_learned_count_wl_heur lcount S))
  }\<close>

definition remove_lit_from_clause where
  \<open>remove_lit_from_clause N C L = do {
    n \<leftarrow> mop_arena_length N C;
   (i, j, N) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, j, N). i < n)
     (\<lambda>(i, j, N). do {
       K \<leftarrow> mop_arena_lit2 N C j;
       if K \<noteq> L then do {
         N \<leftarrow> mop_arena_swap C i j N;
         RETURN (i+1, j+1, N)}
      else RETURN (i+1, j, N)
    }) (0, 0, N);
   RETURN N
  }\<close>

(*
TODO the wasted bits should be incremented in the deletion functions
TODO rename the mark_garbage_heurX functions with proper name like below
*)
definition mark_garbage_heur_as_subsumed :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mark_garbage_heur_as_subsumed C S = (do{
    let N' = get_clauses_wl_heur S;
    let st = arena_status N' C = IRRED;
    let N' = extra_information_mark_to_delete (N') C;
    size \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
    let lcount = get_learned_count S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else clss_size_incr_lcountUS (clss_size_decr_lcount lcount));
    let stats = get_stats_heur S;
    let stats = (if st then decr_irred_clss stats else stats);
    let S = set_clauses_wl_heur N' S;
    let S = set_learned_count_wl_heur lcount S;
    let S = set_stats_wl_heur stats S;
    let S = incr_wasted_st (of_nat size) S;
    RETURN S
  })\<close>

definition isa_strengthen_clause_wl2 where
  \<open>isa_strengthen_clause_wl2 C C' L S = do {
    m \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
    n \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C';
    N \<leftarrow> remove_lit_from_clause (get_clauses_wl_heur S) C (-L);
    st1 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
    st2 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
    let S = set_clauses_wl_heur N S;

    if m = n
    then do {
      S \<leftarrow> mark_garbage_heur_as_subsumed C' S;
      S \<leftarrow> (if st1 = LEARNED \<and> st2 = IRRED \<and> m=n then mop_arena_promote_st S C else RETURN S);
      RETURN S
    }
    else
    RETURN S
  }\<close>

definition isa_subsume_or_strengthen_wl :: \<open>nat \<Rightarrow> nat subsumption \<Rightarrow> isasat \<Rightarrow> _ nres\<close> where
  \<open>isa_subsume_or_strengthen_wl = (\<lambda>C s S. do {
   ASSERT(isa_subsume_or_strengthen_wl_pre C s S);
   (case s of
     NONE \<Rightarrow> RETURN S
  | SUBSUMED_BY C' \<Rightarrow> do {
     st1 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
     st2 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
     S \<leftarrow> mark_garbage_heur2 C' S;
     S \<leftarrow> (if st1 = LEARNED \<and> st2 = IRRED then mop_arena_promote_st S C else RETURN S);
     RETURN S
  }
   | STRENGTHENED_BY L C' \<Rightarrow> isa_strengthen_clause_wl2 C C' L S)
  })\<close>

definition mop_cch_remove_all_clauses where
  \<open>mop_cch_remove_all_clauses S C D = do {
     n \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
     (_, D) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, D). i < n)
       (\<lambda>(i, D). do {L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i; RETURN (i+1, D[nat_of_lit L := False])})
      (0, D);
    RETURN D
  } \<close>

definition isa_forward_subsumption_one_wl :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat literal \<Rightarrow> isasat \<Rightarrow> (isasat \<times> bool \<times> bool list) nres\<close> where
  \<open>isa_forward_subsumption_one_wl = (\<lambda>C D L S. do {
  ASSERT (isa_forward_subsumption_one_wl_pre C L S);
  ASSERT (nat_of_lit L < length (get_occs S));
  let n = length (get_occs S ! nat_of_lit L);
  (_, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> isa_forward_subsumption_one_wl2_inv S C L \<^esup> (\<lambda>(i, s). i < n \<and> s = NONE)
    (\<lambda>(i, s). do {
      C' \<leftarrow> mop_cocc_list_at (get_occs S) L i;
      status \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
      if status = DELETED
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> isa_subsume_clauses_match2 C' C S D;
       RETURN (i+1, s)
      }
    })
        (0, NONE);
  D \<leftarrow> (if s \<noteq> NONE then mop_cch_remove_all_clauses S C D else RETURN D);
  S \<leftarrow> (if is_strengthened s then isa_push_to_occs_list_st C S else RETURN S);
  S \<leftarrow> isa_subsume_or_strengthen_wl C s S;
  RETURN (S, s \<noteq> NONE, D)
  })\<close>

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
    apply (refine_vcg mop_arena_length[where vdom=\<open>set (get_vdom S)\<close>, THEN fref_to_Down_curry, unfolded comp_def]
      mop_arena_lit2[where vdom=\<open>set (get_vdom S)\<close>] mop_cch_in_mop_ch_in)
    subgoal using assms unfolding isa_subsume_clauses_match2_pre_def by fast
    subgoal unfolding subsume_clauses_match2_pre_def subsume_clauses_match_pre_def
      by auto
    subgoal using SS' CC' EE' by (auto simp: twl_st_heur_restart_occs_def)
    subgoal using EE' by auto
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
  \<open>valid_occs occs (get_vdom S) \<Longrightarrow>
  x1 < length (occs ! nat_of_lit L) \<Longrightarrow>
     nat_of_lit L < length occs \<Longrightarrow> 
  cocc_list_at occs L x1 \<in> set (get_vdom S)\<close>
  apply (drule nth_mem)
  unfolding valid_occs_def cocc_list_at_def Union_eq subset_iff
  by (auto dest: spec[of _ \<open>occs ! nat_of_lit L ! x1\<close>])

lemma isa_forward_subsumption_all_forward_subsumption_wl_all:
  assumes
    SS': \<open>(S, S') \<in> twl_st_heur_restart_occs' r u\<close> and
    \<open>(C,C')\<in>nat_rel\<close> and
    DD': \<open>(D,D')\<in>clause_hash\<close> and
    \<open>(L,L')\<in>Id\<close> and
    occs: \<open>(get_occs S, occs) \<in> occurrence_list_ref\<close> and
    \<open>C \<in> set (get_vdom S)\<close> and
    incl: \<open>set_mset (all_occurrences (all_init_atms_st S') occs) \<subseteq> set (get_vdom S)\<close>
  shows \<open>isa_forward_subsumption_one_wl C D L S \<le>
    \<Down>{((S, changed, E), (S', changed', occs', E')). (get_occs S, occs') \<in> occurrence_list_ref \<and>
       ((S, changed, E), (S', changed', E')) \<in> twl_st_heur_restart_occs' r u \<times>\<^sub>r bool_rel \<times>\<^sub>r clause_hash}
    (forward_subsumption_one_wl2 C' cands L' occs D' S')\<close>
proof -
  have valid: \<open>valid_occs (get_occs S) (get_vdom S)\<close>
    using SS' by (auto simp: twl_st_heur_restart_occs_def)
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
  occs \<leftarrow> (if is_strengthened s then push_to_occs_list2 C S occs else RETURN occs);
  S \<leftarrow> subsume_or_strengthen_wl C s S;
  RETURN (S, s \<noteq> NONE, occs, D)
  })\<close>
   unfolding forward_subsumption_one_wl2_def by auto
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
  show ?thesis
    unfolding isa_forward_subsumption_one_wl_def forward_subsumption_one_wl2_alt_def eq Let_def
    apply (refine_vcg mop_cocc_list_at_mop_occ_list_at occs mop_arena_status2[where arena=\<open>get_clauses_wl_heur S\<close> and vdom=\<open>set (get_vdom S)\<close> and
      N=\<open>get_clauses_wl S'\<close>] isa_subsume_clauses_match2_subsume_clauses_match2 SS')
    subgoal using assms unfolding isa_forward_subsumption_one_wl_pre_def by fast
    subgoal using occs by (cases L) (auto simp: occurrence_list_ref_def map_fun_rel_def dest: bspec[of _ _ \<open>L\<close>])
    subgoal using assms H unfolding isa_forward_subsumption_one_wl2_inv_def apply - by (rule exI[of _ S']) auto
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
    subgoal using DD' by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal apply (auto simp: forward_subsumption_one_wl2_pre_def isa_forward_subsumption_one_wl_pre_def
      forward_subsumption_one_wl_pre_def)
find_theorems "If _ _ _ \<le> \<Down>_ (If _ _ _ )"
thm mop_arena_status
find_theorems mop_arena_status DELETED
oops
definition isa_try_to_forward_subsume_wl_pre :: \<open>_\<close> where
  \<open>isa_try_to_forward_subsume_wl_pre C S \<longleftrightarrow>
  (\<exists>T r u cands occs'. (S,T)\<in>twl_st_heur_restart_occs' r u \<and>  (get_occs S, occs') \<in> occurrence_list_ref \<and>
  try_to_forward_subsume_wl_pre C cands T \<and>
  all_occurrences (all_atms_st T) (occs') \<subseteq># dom_m (get_clauses_wl T))\<close>


definition isa_try_to_forward_subsume_wl_inv :: \<open>_\<close> where
  \<open>isa_try_to_forward_subsume_wl_inv S C = (\<lambda>(i, break, T).
  (\<exists>S' T' r u cands occs'. (S,S')\<in>twl_st_heur_restart_occs' r u \<and> (T,T')\<in>twl_st_heur_restart_ana' r u \<and>
  (get_occs T, occs') \<in> occurrence_list_ref \<and>
  try_to_forward_subsume_wl_inv S' cands C (i, break, T') \<and>
  all_occurrences (all_atms_st T') occs' \<subseteq># dom_m (get_clauses_wl T')))\<close>

  (*TODO: Missing ticks*)

thm try_to_forward_subsume_wl2_def
  thm forward_subsumption_all_wl2_def



definition isa_forward_subsumption_all_wl_inv :: \<open>_\<close> where
  \<open>isa_forward_subsumption_all_wl_inv  S =
  (\<lambda>(i, T, occs). \<exists>S' T' r u cands. (S, S')\<in>twl_st_heur_restart_occs' r u \<and>
     (T,T')\<in>twl_st_heur_restart_occs' r u \<and>
    forward_subsumption_all_wl_inv S' cands (mset (drop i (get_tvdom_aivdom (get_aivdom S))), T')) \<close>

definition append_clause_to_occs_pre where
  \<open>append_clause_to_occs_pre C S occs =
  (\<exists>S' r u. (S, S')\<in>twl_st_heur_restart_ana' r u \<and> C \<in># dom_m (get_clauses_wl S') \<and>
  length (get_clauses_wl S' \<propto> C) > 0)\<close>

definition append_clause_to_occs where
  \<open>append_clause_to_occs C S occs = do {
     ASSERT (append_clause_to_occs_pre C S occs);
    L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C 0;
    mop_occ_list_append C occs L
  }
  \<close>
end

definition isa_forward_subsumption_pre_all :: \<open>_\<close> where
  \<open>isa_forward_subsumption_pre_all  S \<longleftrightarrow>
  (\<exists>T r u. (S,T)\<in>twl_st_heur_restart_ana' r u \<and> forward_subsumption_all_wl_pre T) \<close>


definition isa_forward_subsumption_all where
  \<open>isa_forward_subsumption_all S = do {
    ASSERT (isa_forward_subsumption_pre_all S);
    RETURN S
  }\<close>


lemma isa_forward_subsumption_all_forward_subsumption_wl_all:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_forward_subsumption_all S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (forward_subsumption_all_wl S')\<close>
proof -
  have isa_forward_subsumption_all_def: \<open>isa_forward_subsumption_all S = do {
    ASSERT (isa_forward_subsumption_pre_all S);
    let xs = ({#} :: nat multiset);
    RETURN S
  }\<close>
  unfolding isa_forward_subsumption_all_def by auto
  show ?thesis
    unfolding isa_forward_subsumption_all_def forward_subsumption_all_wl_def
    apply (refine_vcg)
    subgoal using assms unfolding isa_forward_subsumption_pre_all_def by fast
    subgoal unfolding forward_subsumption_wl_all_cands_def by auto
    subgoal
      by (subst WHILEIT_unfold)
       (use assms in auto)
    done
qed

end