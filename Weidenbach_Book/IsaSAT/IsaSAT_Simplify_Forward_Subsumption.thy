theory IsaSAT_Simplify_Forward_Subsumption
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Restart
    IsaSAT_Simplify_Units
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
      let L = get_clauses_wl N \<propto> C ! i;
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
  show ?thesis
    unfolding N subsume_clauses_match2_def subsume_clauses_match_alt_def Let_def[of \<open>length _\<close>] eq
    apply (refine_rcg DG[unfolded G] mop_ch_in)
    subgoal using DG G unfolding subsume_clauses_match2_pre_def clause_hash_ref_def
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: subsume_clauses_match_pre_def)
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

definition forward_subsumption_one_wl2 :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> nat literal \<Rightarrow> occurences \<Rightarrow> clause_hash \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> bool \<times> occurences \<times> clause_hash) nres\<close> where
  \<open>forward_subsumption_one_wl2 = (\<lambda>C cands L occs D S. do {
  ASSERT (forward_subsumption_one_wl_pre C cands S);
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
  D \<leftarrow> (if s \<noteq> NONE then mop_ch_remove_all D else RETURN D);
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
    \<open>mop_ch_remove_all C \<le> SPEC(\<lambda>c. (c, {#}) \<in> clause_hash_ref \<A>)\<close>
    if  \<open>(C, D) \<in> clause_hash_ref \<A>\<close> for C D  \<A>
    using that unfolding mop_ch_remove_all_def
    apply refine_vcg
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
      subsume_clauses_match2_subsume_clauses_match push_to_occs_list2)
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
  D \<leftarrow> (if \<not>changed then mop_ch_remove_all D else RETURN D);
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
    x = (x1b, x2b) \<Longrightarrow>
    mop_ch_remove_all x1f \<le> SPEC(\<lambda>c. (c, {#}) \<in> {(a,b). b = {#} \<and> (a,b) \<in> clause_hash_ref (all_init_atms_st x2f)})\<close>
    for na ebreak ebreaka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f 
    unfolding mop_ch_remove_all_def
    apply refine_vcg
    subgoal
      by (auto simp: clause_hash_ref_def ch_remove_all_def)
    done
  show ?thesis
    unfolding try_to_forward_subsume_wl2_def try_to_forward_subsume_wl_alt_def eq
    apply (refine_vcg
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

lemma
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

lemma
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
    subgoal by auto
    subgoal
      by (subst WHILEIT_unfold)
       (use assms in auto)
    done
qed

(*TODO: this is dumbed currently*)
definition is_candidate_forward_subsumption where
  \<open>is_candidate_forward_subsumption C N = do {
    ASSERT (C \<in># dom_m N);
    SPEC (\<lambda>b :: bool. b \<longrightarrow> \<not>irred  N C \<and> length (N \<propto> C) \<noteq> 2)
  }\<close>

definition isa_is_candidate_forward_subsumption where
  \<open>isa_is_candidate_forward_subsumption M C arena = do {
    ASSERT(arena_act_pre arena C);
    L \<leftarrow> mop_arena_lit arena C;
    lbd \<leftarrow> mop_arena_lbd arena C;
    length \<leftarrow> mop_arena_length arena C;
    status \<leftarrow> mop_arena_status arena C;
    used \<leftarrow> mop_marked_as_used arena C;
    let can_del =
      length \<noteq> 2 \<and> (status = LEARNED \<longrightarrow> lbd < 100);
    RETURN can_del
  }
\<close>
definition isa_forward_accumulate_candidades :: \<open>_\<close> where
\<open>isa_forward_accumulate_candidades M arena avdom0 = do {
  ASSERT(length (get_avdom_aivdom avdom0) \<le> length arena);
  ASSERT(length (get_avdom_aivdom avdom0) \<le> length (get_vdom_aivdom avdom0));
  let n = length (get_avdom_aivdom avdom0);
  (arena, i, j, avdom) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(_, i, j, _). i \<le> j \<and> j \<le> n\<^esup>
    (\<lambda>(arena, i, j, avdom). j < n)
    (\<lambda>(arena, i, j, avdom). do {
      ASSERT(j < n);
      ASSERT(arena_is_valid_clause_vdom arena (get_avdom_aivdom avdom!j) \<and> j < length (get_avdom_aivdom avdom) \<and> i < length (get_avdom_aivdom avdom));
     ASSERT (length (get_tvdom_aivdom avdom) \<le> i);
     if arena_status arena (get_avdom_aivdom avdom ! j) \<noteq> DELETED then do{
        ASSERT(arena_act_pre arena (get_avdom_aivdom avdom ! j));
        should_push \<leftarrow> isa_is_candidate_forward_subsumption M (get_avdom_aivdom avdom ! j) arena;
        let arena = mark_unused arena (get_avdom_aivdom avdom ! j);
       if should_push then  RETURN (arena, i+1, j+1, push_to_tvdom (get_avdom_aivdom avdom ! j) (swap_avdom_aivdom avdom i j))
       else RETURN (arena, i+1, j+1, swap_avdom_aivdom avdom i j)
      }
      else RETURN (arena, i, j+1, avdom)
    }) (arena, 0, 0, empty_tvdom avdom0);
  ASSERT(i \<le> length (get_avdom_aivdom avdom));
  RETURN (arena, take_avdom_aivdom i avdom)
 }\<close>

definition isa_forward_accumulate_candidades_st where
  \<open>isa_forward_accumulate_candidades_st S = do {
  let M = get_trail_wl_heur S;
  let arena = get_clauses_wl_heur S;
  let avdom = get_aivdom S;
  (arena, avdom) \<leftarrow> isa_forward_accumulate_candidades M arena avdom;
  let S = set_clauses_wl_heur arena S;
  let S = set_aivdom_wl_heur avdom S;
  RETURN S
  }\<close>

thm subsume_clauses_match_def

definition isa_forward_subsumption_one_wl_pre :: \<open>_\<close> where
  \<open>isa_forward_subsumption_one_wl_pre C S \<longleftrightarrow>
  (\<exists>T r u. (S,T)\<in>twl_st_heur_restart_ana' r u \<and> forward_subsumption_one_wl_pre C T) \<close>


thm forward_subsumption_one_wl_def
definition isa_forward_subsumption_one_wl :: \<open>nat \<Rightarrow> isasat \<Rightarrow> occurences \<Rightarrow> (isasat \<times> bool) nres\<close> where
  \<open>isa_forward_subsumption_one_wl = (\<lambda>C S occs. do {
  ASSERT (isa_forward_subsumption_one_wl_pre C S);
  RETURN (S, False)
  })\<close>


definition isa_try_to_forward_subsume_wl_pre :: \<open>_\<close> where
  \<open>isa_try_to_forward_subsume_wl_pre C S occs \<longleftrightarrow>
  (\<exists>T r u. (S,T)\<in>twl_st_heur_restart_ana' r u \<and> try_to_forward_subsume_wl_pre C T \<and>
  all_occurrences occs \<subseteq># dom_m (get_clauses_wl T))\<close>


definition isa_try_to_forward_subsume_wl_inv :: \<open>_\<close> where
  \<open>isa_try_to_forward_subsume_wl_inv S C occs = (\<lambda>(i, break, T).
  (\<exists>S' T' r u. (S,S')\<in>twl_st_heur_restart_ana' r u \<and> (T,T')\<in>twl_st_heur_restart_ana' r u \<and>
  try_to_forward_subsume_wl_inv S' C (i, break, T') \<and>
  all_occurrences occs \<subseteq># dom_m (get_clauses_wl T')))\<close>

(*TODO: Missing ticks*)
definition isa_try_to_forward_subsume_wl :: \<open>nat \<Rightarrow> isasat \<Rightarrow> occurences \<Rightarrow> isasat nres\<close> where
  \<open>isa_try_to_forward_subsume_wl C S occs = do {
  ASSERT (isa_try_to_forward_subsume_wl_pre C S occs);
  n \<leftarrow> mop_arena_length_st S C;
  ebreak \<leftarrow> RETURN False;
  (_, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup> isa_try_to_forward_subsume_wl_inv S C occs\<^esup>
    (\<lambda>(i, break, S). \<not>break \<and> i < n)
    (\<lambda>(i, break, S). do {
      (S, subs) \<leftarrow> isa_forward_subsumption_one_wl C S occs;
      ebreak \<leftarrow> RETURN False;
      RETURN (i+1, subs \<or> ebreak, S)
    })
  (0, ebreak, S);
  RETURN S
  }\<close>


definition isa_forward_subsumption_all_wl_inv :: \<open>_\<close> where
  \<open>isa_forward_subsumption_all_wl_inv  S =
  (\<lambda>(i, T, occs). \<exists>S' T' r u. (S, S')\<in>twl_st_heur_restart_ana' r u \<and>
     (T,T')\<in>twl_st_heur_restart_ana' r u \<and>
    forward_subsumption_all_wl_inv S' (mset (drop i (get_tvdom_aivdom (get_aivdom S))), T')) \<close>

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


definition isa_forward_subsumption_all2 where
  \<open>isa_forward_subsumption_all2 S = do {
  ASSERT (isa_forward_subsumption_pre_all S);
  S \<leftarrow> isa_forward_accumulate_candidades_st S;
  let n = length (get_tvdom_aivdom (get_aivdom S));
  ASSERT (n < length (get_clauses_wl_heur S));
  occs \<leftarrow> mop_occ_list_create (length (get_watched_wl_heur S));
  let mark = (0, replicate (length (get_watched_wl_heur S) >> 1) None);
  (_, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> isa_forward_subsumption_all_wl_inv S \<^esup> (\<lambda>(i, S, occs). i < n \<and> get_conflict_wl_is_None_heur S)
    (\<lambda>(i, S, occs). do {
       ASSERT (access_tvdom_at_pre S i);
       C \<leftarrow> RETURN (access_tvdom_at S i);
       if clause_not_marked_to_delete_heur S C
       then RETURN (i+1, S, occs)
       else do {
         S \<leftarrow> isa_simplify_clause_with_unit_st2 C S;
         length \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
         if get_conflict_wl_is_None_heur S \<and> clause_not_marked_to_delete_heur S C \<and> length > 2 then do {
           S \<leftarrow> isa_try_to_forward_subsume_wl C S occs;
           occs \<leftarrow> (if clause_not_marked_to_delete_heur S C then append_clause_to_occs C S occs else RETURN occs);
           RETURN (i+1, S, occs)
         }
         else RETURN (i+1, S, occs)
      }
    })
    (0, S, occs);
  RETURN S
  }\<close>

end