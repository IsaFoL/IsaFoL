theory Watched_Literals_Watch_List_Inprocessing
  imports Watched_Literals_Watch_List Watched_Literals_List_Inprocessing
begin

definition simplify_clause_with_unit_st_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>simplify_clause_with_unit_st_wl = (\<lambda>C (M, N, D, NE, UE, NS, US, N0, U0, Q, W). do {
    ASSERT (C \<in># dom_m N \<and> count_decided M = 0 \<and> D = None );
    if C \<in> set (get_all_mark_of_propagated M)
    then RETURN (M, N, D, NE, UE, NS, US, N0, U0, Q, W)
    else do {
      let E = mset (N \<propto> C);
      let irr = irred N C;
      (b, N) \<leftarrow> simplify_clause_with_unit C M N;
      if b then
        RETURN (M, fmdrop C N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NS, US, N0, U0, Q, W)
      else if size (N \<propto> C) = 1
      then do {
        let L = ((N \<propto> C) ! 0);
        RETURN (Propagated L 0 # M, fmdrop C N, D, (if irr then add_mset {#L#} else id) NE, (if \<not>irr then add_mset {#L#} else id)UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W)}
      else if size (N \<propto> C) = 0
        then RETURN (M, fmdrop C N, Some {#}, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W)
      else
          RETURN (M, N, D, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W)
    }
     })\<close>

definition simplify_clauses_with_unit_st_wl_pre where
  \<open>simplify_clauses_with_unit_st_wl_pre S \<longleftrightarrow> (\<exists>T.
  (S, T) \<in> state_wl_l None \<and>
  set_mset (dom_m (get_clauses_wl S)) \<subseteq>
    clauses_pointed_to (set_mset (all_init_lits_of_wl S))
    (get_watched_wl S) \<and>
  simplify_clauses_with_unit_st_pre T)\<close>

definition simplify_clauses_with_unit_st_wl_inv where
  \<open>simplify_clauses_with_unit_st_wl_inv S\<^sub>0 it S \<longleftrightarrow> (\<exists>T\<^sub>0 T.
  (S\<^sub>0, T\<^sub>0) \<in> state_wl_l None \<and>
  (S, T) \<in> state_wl_l None \<and>
  simplify_clauses_with_unit_st_inv T\<^sub>0 it T \<and>
  set_mset (dom_m (get_clauses_wl S)) \<subseteq>
  clauses_pointed_to (set_mset (all_init_lits_of_wl S))
  (get_watched_wl S))\<close>

definition simplify_clauses_with_unit_st_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>  where
  \<open>simplify_clauses_with_unit_st_wl S =
  do {
    ASSERT(simplify_clauses_with_unit_st_wl_pre S);
    xs \<leftarrow> SPEC(\<lambda>xs. xs \<subseteq>set_mset (dom_m (get_clauses_wl S)));
    FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
    (xs)
    (\<lambda>S. get_conflict_wl S = None)
    (\<lambda>i S. simplify_clause_with_unit_st_wl i S)
    S
  }\<close>
lemma clauses_pointed_to_union:
  \<open>clauses_pointed_to (A \<union> B) W = clauses_pointed_to A W \<union> clauses_pointed_to B W\<close>
  by (auto simp: clauses_pointed_to_def)

lemma clauses_pointed_to_mono: \<open>A \<subseteq> B \<Longrightarrow> clauses_pointed_to A W \<subseteq> clauses_pointed_to B W\<close>
  by (auto simp: clauses_pointed_to_def)
 
lemma simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and \<open>(i,j) \<in> nat_rel\<close> and
    point: \<open>set_mset (dom_m (get_clauses_wl S)) \<subseteq>
      clauses_pointed_to (set_mset (all_init_lits_of_wl S))
      (get_watched_wl S)\<close>
  shows
  \<open>simplify_clause_with_unit_st_wl i S \<le> \<Down> {(S,T). (S,T) \<in> state_wl_l None \<and>
    set_mset (dom_m (get_clauses_wl S)) \<subseteq>
    clauses_pointed_to (set_mset (all_init_lits_of_wl S))
    (get_watched_wl S)}
  (simplify_clause_with_unit_st j T)\<close>
proof -
  have Id: \<open>A = B \<Longrightarrow> A \<le> \<Down>Id B\<close> for A B
    by auto
  have ij: \<open>i = j\<close>
    using assms by auto
  have [simp]:
    \<open>irred b j \<Longrightarrow> j \<in># dom_m b \<Longrightarrow> add_mset (mset (b \<propto> j))
    ({#mset (fst x). x \<in># remove1_mset (the (fmlookup b j)) (init_clss_l b)#} + d + f + h) =
    ({#mset (fst x). x \<in># (init_clss_l b)#} + d + f + h)\<close> for C D d b f h j
    by (auto simp: image_mset_remove1_mset_if ran_m_def
      dest!: multi_member_split)
  have H: \<open>fmdrop j x2 = fmdrop j b \<Longrightarrow>
    mset (x2 \<propto> j) \<subseteq># mset (b \<propto> j) \<Longrightarrow>
    irred x2 j \<Longrightarrow>
    irred b j \<Longrightarrow>
    j \<in># dom_m b \<Longrightarrow>
    j \<in># dom_m x2 \<Longrightarrow>
    set_mset (all_lits_of_mm (add_mset (mset (b \<propto> j)) ({#mset (fst x). x \<in># init_clss_l x2#} +
    d + f + h))) =
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l b#} + d + f + h))\<close>
    for j x2 b d f h
    using distinct_mset_dom[of x2] distinct_mset_dom[of b]
    apply (subgoal_tac \<open>{#mset (fst x). x \<in># filter_mset snd {#the (fmlookup b x). x \<in># remove1_mset j (dom_m b)#}#} =
      {#mset (fst x). x \<in># filter_mset snd {#the (fmlookup x2 x). x \<in># remove1_mset j (dom_m x2)#} #}\<close>)

    apply (auto 5 3 simp: ran_m_def all_lits_of_mm_add_mset
      dest!: multi_member_split[of _ \<open>dom_m _\<close>]
      dest: all_lits_of_m_mono
      intro!: image_mset_cong2 filter_mset_cong2)
    apply (metis fmdrop_eq_update_eq fmupd_lookup union_single_eq_member)
    by (metis add_mset_remove_trivial dom_m_fmdrop) 

  show ?thesis
    supply [[goals_limit=1]]
    using ST point
    apply (cases S; hypsubst)
    apply (cases T; hypsubst)
    unfolding simplify_clause_with_unit_st_wl_def simplify_clause_with_unit_st_def ij
      state_wl_l_def prod.simps
    apply refine_rcg
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
      apply (rule Id)
      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev
        dest: in_diffD)
      subgoal by auto
      subgoal apply (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev add_mset_commute
        dest: in_diffD)
        apply (subst add_mset_commute)
        apply (auto simp: all_lits_of_mm_add_mset clauses_pointed_to_union
          dest: in_diffD)
        done
      subgoal by auto
      subgoal by (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev all_lits_of_mm_add_mset
        dest: in_diffD)
      subgoal for a b c d e f g h i ja k aa ba ca da ea fa ga ha ia jaa ka x x' x1 x2 x1a x2a
        
        apply
        (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev H
        dest: in_diffD
          intro: )
        apply (metis (no_types, lifting) basic_trans_rules(31) dom_m_fmdrop insert_DiffM) 
        by (metis (no_types, lifting) basic_trans_rules(31) dom_m_fmdrop init_clss_l_fmdrop_irrelev insert_DiffM)
      done
qed


lemma simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    point: \<open>set_mset (dom_m (get_clauses_wl S)) \<subseteq>
    clauses_pointed_to (set_mset (all_init_lits_of_wl S))
    (get_watched_wl S)\<close>
  shows
    \<open>simplify_clauses_with_unit_st_wl S \<le> \<Down> {(S,T). (S,T) \<in> state_wl_l None \<and>
    set_mset (dom_m (get_clauses_wl S)) \<subseteq>
    clauses_pointed_to (set_mset (all_init_lits_of_wl S))
    (get_watched_wl S)}
    (simplify_clauses_with_unit_st T)\<close>
proof -
  have [refine0]: \<open>inj_on id xs\<close> for xs
    by auto
  show ?thesis
    unfolding simplify_clauses_with_unit_st_wl_def simplify_clauses_with_unit_st_def
    apply (refine_vcg simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st)
    subgoal
      using assms unfolding simplify_clauses_with_unit_st_wl_pre_def
      by blast
    subgoal
      using ST by auto
    subgoal
      by auto
    subgoal
      using assms unfolding simplify_clauses_with_unit_st_wl_pre_def by auto
    subgoal
      by auto
    subgoal for xs xsa it \<sigma> it' \<sigma>'
      using assms apply -
      unfolding simplify_clauses_with_unit_st_wl_inv_def
      apply (rule exI[of _ T])
      apply (rule exI[of _ \<sigma>'])
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    done
qed


end