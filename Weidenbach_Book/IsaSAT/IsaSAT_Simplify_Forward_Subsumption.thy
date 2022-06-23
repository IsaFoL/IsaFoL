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
    DG: \<open>(D, G) \<in> clause_hash_ref (all_atms_st S)\<close> and
    N: \<open>N = get_clauses_wl S\<close> and
    G: \<open>G = mset (get_clauses_wl S \<propto> C')\<close>
  shows \<open>subsume_clauses_match2 C C' S D \<le> \<Down>Id (subsume_clauses_match E F N)\<close>
proof -
  have eq: \<open>E = C\<close> \<open>F = C'\<close>
    using assms by auto
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


definition forward_subsumption_one_wl2_inv :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
  nat \<times> 'v subsumption \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl2_inv = (\<lambda>S C ys (i, x). forward_subsumption_one_wl_inv S C (mset (drop i ys), x))\<close>

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
  \<open>correct_occurence_list S occs n \<longleftrightarrow>
  (all_occurrences  (all_atms_st S) occs) \<subseteq># dom_m (get_clauses_wl S) \<and>
  (\<forall>C\<in># all_occurrences (all_atms_st S) occs. length (get_clauses_wl S \<propto> C) \<le> n)\<and>
  (\<forall>C\<in># all_occurrences (all_atms_st S) occs. \<forall>L\<in>set (get_clauses_wl S \<propto> C).
     undefined_lit (get_trail_wl S) L) \<and> fst occs = set_mset (all_atms_st S)\<close>

definition forward_subsumption_one_wl2_rel where
  \<open>forward_subsumption_one_wl2_rel S\<^sub>0 occs n C = {((S, changed, occs', D), (T, changed')).
     changed = changed' \<and>
      (changed \<longrightarrow> (D, {#}) \<in> clause_hash_ref (all_atms_st S)) \<and>
      (\<not>changed \<longrightarrow> occs' = occs) \<and>
      correct_occurence_list S occs (if changed then size (get_clauses_wl S\<^sub>0 \<propto> C) else n) \<and>
     all_occurrences (all_atms_st S) occs' \<subseteq># add_mset C (all_occurrences  (all_atms_st S) occs)
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
  \<open>all_occurrences A (insert (atm_of L) B, occs) =
  all_occurrences (A) (B, occs)\<close>
  and
  all_occurrences_occ_list_append_r:
  \<open>all_occurrences (removeAll_mset (atm_of L) A)
     (B, occ_list_append_r L C b) =
    all_occurrences (removeAll_mset (atm_of L) A) (B, b)\<close>
  apply (auto simp: all_occurrences_def)
  by (smt (verit) distinct_mset_remdups_mset distinct_mset_remove1_All image_mset_cong2
    literal.sel(1) literal.sel(2) remdups_mset_removeAll removeAll_subseteq_remove1_mset
    subset_mset_removeAll_iff)

lemma push_to_occs_list2:
  assumes occs: \<open>correct_occurence_list S occs n\<close>
    \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    \<open>2 \<le> length (get_clauses_wl S \<propto> C)\<close>
  shows \<open>push_to_occs_list2 C S occs \<le> SPEC (\<lambda>c. (c, ()) \<in> {(occs', occs'').
    all_occurrences (all_atms_st S) occs' = add_mset C (all_occurrences  (all_atms_st S) occs) \<and>
    correct_occurence_list S occs (max n (length (get_clauses_wl S \<propto> C)))})\<close>
proof -
  have \<open>atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_atms_st S)\<close>
    using nth_in_all_lits_stI[of C S] assms(2)
    unfolding all_atms_st_alt_def
    by (auto simp del: all_atms_st_alt_def[symmetric] simp: in_set_conv_nth)

  then show ?thesis
    unfolding push_to_occs_list2_def
    apply (refine_vcg mop_occ_list_append[THEN order_trans])
    subgoal using assms unfolding push_to_occs_list2_pre_def by fast
    subgoal using assms unfolding occ_list_append_pre_def correct_occurence_list_def
      by auto
    subgoal for L occs'
      using multi_member_split[of \<open>atm_of L\<close> \<open>all_atms_st S\<close>]
      apply (subgoal_tac \<open>atm_of L \<in># all_atms_st S\<close>)
      apply (cases occs)
      apply (use assms in \<open>auto simp: occ_list_append_def correct_occurence_list_def
        all_occurrences_add_mset occ_list_def all_occurrences_insert_lit
        all_occurrences_occ_list_append_r\<close>)
      done
   done
qed

definition forward_subsumption_one_wl2 :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> occurences \<Rightarrow> clause_hash \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> bool \<times> occurences \<times> clause_hash) nres\<close> where
  \<open>forward_subsumption_one_wl2 = (\<lambda>C L occs D S. do {
  ASSERT (forward_subsumption_one_wl_pre C S);
  let ys = occ_list occs L;
  let n = length ys;
  (_, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl2_inv S C ys \<^esup> (\<lambda>(i, s). i < n \<and> s = NONE)
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




lemma forward_subsumption_one_wl2_rel_forward_subsumption_one_wl_rel:
  assumes
    \<open>(C, E) \<in> nat_rel\<close>
    \<open>(C', F) \<in> nat_rel\<close>
    \<open>(N, N') \<in> Id\<close> and
    DG: \<open>(D, G) \<in> clause_hash_ref (all_atms_st S\<^sub>0)\<close> and
    G: \<open>G = mset (get_clauses_wl S\<^sub>0 \<propto> C)\<close> and
    occs: \<open>correct_occurence_list S\<^sub>0 occs n\<close> and
    n: \<open>n\<le> size (get_clauses_wl S\<^sub>0 \<propto> C)\<close> and
    C_occs: \<open>C \<notin># all_occurrences (all_atms_st S\<^sub>0) occs\<close> and
    L: \<open>atm_of L \<in># all_atms_st S\<^sub>0\<close>
  shows \<open>forward_subsumption_one_wl2 C L occs D S\<^sub>0 \<le> \<Down>
    (forward_subsumption_one_wl2_rel S\<^sub>0 occs n C)
    (forward_subsumption_one_wl C S\<^sub>0)\<close>
proof -
  have [refine]:
    \<open>RETURN (occ_list occs L)
    \<le> \<Down> list_mset_rel (SPEC (forward_subsumption_one_wl_select C S\<^sub>0))\<close>
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
    \<open>forward_subsumption_one_wl = (\<lambda>C S . do {
    ASSERT (forward_subsumption_one_wl_pre C S);
    ys \<leftarrow> SPEC (forward_subsumption_one_wl_select C S);
    let _ = size ys;
    (xs, s) \<leftarrow>
      WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl_inv S C \<^esup> (\<lambda>(xs, s). xs \<noteq> {#} \<and> s = NONE)
      (\<lambda>(xs, s). do {
        C'  \<leftarrow>ISABELLE_YOU_ARE_SO_STUPID xs;
        if C' \<notin># dom_m (get_clauses_wl S)
        then RETURN (remove1_mset C' xs, s)
        else do  {
          s \<leftarrow> subsume_clauses_match C' C (get_clauses_wl S);
         RETURN (remove1_mset C' xs, s)
        }
      })
      (ys, NONE);
    _ \<leftarrow> RETURN (if s \<noteq> NONE then ({#} :: nat clause) else G);
    let _ = (if is_strengthened s then () else ());
    S \<leftarrow> subsume_or_strengthen_wl C s S;
    RETURN (S, s \<noteq> NONE)
      })\<close>
    unfolding forward_subsumption_one_wl_def ISABELLE_YOU_ARE_SO_STUPID_def bind_to_let_conv H
    by (auto split: )
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
  have itself: \<open>subsume_or_strengthen_wl C s S \<le>\<Down>{(x,y). x = y \<and> set_mset (all_atms_st S) = set_mset (all_atms_st x)} b\<close> if b: \<open>b = subsume_or_strengthen_wl C s S\<close> and
    S: \<open>forward_subsumption_one_wl_pre C S\<close>
    for a b s S
    unfolding subsume_or_strengthen_wl_def b strengthen_clause_wl_def
    apply (cases S, hypsubst, unfold prod.simps)
    apply refine_vcg
    subgoal
      using S unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      apply -
      apply normalize_goal+
        supply [[goals_limit=1]]
      apply (auto split: subsumption.splits
        simp: all_atms_st_alt_def all_lits_st_def all_atms_def all_lits_def ran_m_fmdrop_If
        simp del: all_atms_st_alt_def[symmetric] all_atms_def[symmetric] all_lits_def[symmetric])
      sorry
     done
     find_theorems ran_m fmdrop If
  have mop_ch_remove_all2:
    \<open>mop_ch_remove_all C \<le> SPEC(\<lambda>c. (c, {#}) \<in> clause_hash_ref \<A>)\<close>
    if  \<open>(C, D) \<in> clause_hash_ref \<A>\<close> for C D  \<A>
    using that unfolding mop_ch_remove_all_def
    apply refine_vcg
    subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def)
    done
  have K: \<open>(xa, {#}) \<in> clause_hash_ref (all_atms_st S\<^sub>0) \<Longrightarrow> x2 \<noteq> NONE \<Longrightarrow>
    (xa, if x2 \<noteq> NONE then {#} else G) \<in>
    {(xa, b). if x2 \<noteq> NONE then b = {#} \<and> (xa, b)\<in> clause_hash_ref (all_atms_st S\<^sub>0)
    else (xa,b) = (D,G)}\<close> for xa x2
    by auto

  show ?thesis
    unfolding forward_subsumption_one_wl2_def
      forward_subsumption_one_wl_alt_def
    apply (refine_vcg mop_occ_list_at[THEN order_trans] DG mop_ch_remove_all2 occs
      subsume_clauses_match2_subsume_clauses_match push_to_occs_list2)
    subgoal for ys x x'
      unfolding forward_subsumption_one_wl2_inv_def
      by (cases x') auto
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
    subgoal by (auto simp flip: Cons_nth_drop_Suc occ_list_at_def)
    apply (rule K; assumption?)
    subgoal by auto
    subgoal by auto
    subgoal unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by normalize_goal+ simp
    subgoal unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by normalize_goal+ simp
    apply (rule H; assumption)
    subgoal by auto
    apply (rule itself)
    subgoal by auto
    subgoal apply (auto simp: forward_subsumption_one_wl2_rel_def split: if_splits)
(*missing: proving that the set of atoms has not changed*)
      sorry
    done
qed

  find_theorems drop Suc nth
thm subsume_clauses_match_def
thm forward_subsumption_one_wl_def
thm try_to_forward_subsume_wl_def
thm forward_subsumption_all_wl_def

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