theory Watched_Literals_Watch_List_Inprocessing
  imports Watched_Literals_Watch_List Watched_Literals_List_Simp
    Watched_Literals_Watch_List_Restart
begin

definition simplify_clause_with_unit_st_wl_pre where
  \<open>simplify_clause_with_unit_st_wl_pre C S \<longleftrightarrow> (\<exists>T.
  (S, T) \<in> state_wl_l None \<and>
  simplify_clause_with_unit_st_pre C T)\<close>

definition simplify_clause_with_unit_st_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>simplify_clause_with_unit_st_wl = (\<lambda>C (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, W). do {
    ASSERT(simplify_clause_with_unit_st_wl_pre C (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, W));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None \<and> no_dup M \<and> C \<noteq> 0);
    let S = (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, W);
    if False
    then RETURN S
    else do {
      let E = mset (N\<^sub>0 \<propto> C);
      let irr = irred N\<^sub>0 C;
      (unc, b, N) \<leftarrow> simplify_clause_with_unit C M N\<^sub>0;
      if unc then do {
        ASSERT (N = N\<^sub>0);
        RETURN S
      }
      else if b then do {
        let T = (M, fmdrop C N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NS, US, N0, U0, Q, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN (M, fmdrop C N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NS, US, N0, U0, Q, W)
      }
      else if size (N \<propto> C) = 1
      then do {
        let L = ((N \<propto> C) ! 0);
        let T = (Propagated L 0 # M, fmdrop C N, D, (if irr then add_mset {#L#} else id) NE, (if \<not>irr then add_mset {#L#} else id)UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN T
      }
      else if size (N \<propto> C) = 0
      then do {
         let T =  (M, fmdrop C N, Some {#}, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN T
      }
      else do {
        let T =  (M, N, D, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN T
     }
    }
     })\<close>

definition simplify_clauses_with_unit_st_wl_pre where
  \<open>simplify_clauses_with_unit_st_wl_pre S \<longleftrightarrow> (\<exists>T.
  (S, T) \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and>
  simplify_clauses_with_unit_st_pre T)\<close>

definition simplify_clauses_with_unit_st_wl_inv where
  \<open>simplify_clauses_with_unit_st_wl_inv S\<^sub>0 it S \<longleftrightarrow> (\<exists>T\<^sub>0 T.
  (S\<^sub>0, T\<^sub>0) \<in> state_wl_l None \<and>
  (S, T) \<in> state_wl_l None \<and>
  simplify_clauses_with_unit_st_inv T\<^sub>0 it T \<and>
  no_lost_clause_in_WL S)\<close>

definition simplify_clauses_with_unit_st_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>  where
  \<open>simplify_clauses_with_unit_st_wl S =
  do {
    ASSERT(simplify_clauses_with_unit_st_wl_pre S);
    xs \<leftarrow> SPEC(\<lambda>xs. xs \<subseteq>set_mset (dom_m (get_clauses_wl S)));
    T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
      (xs)
      (\<lambda>S. get_conflict_wl S = None)
      (\<lambda>i S. simplify_clause_with_unit_st_wl i S)
       S;
    ASSERT(set_mset (all_learned_lits_of_wl T) \<subseteq> set_mset (all_learned_lits_of_wl S));
    ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
    RETURN T
  }\<close>
lemma clauses_pointed_to_union:
  \<open>clauses_pointed_to (A \<union> B) W = clauses_pointed_to A W \<union> clauses_pointed_to B W\<close>
  by (auto simp: clauses_pointed_to_def)

lemma clauses_pointed_to_mono: \<open>A \<subseteq> B \<Longrightarrow> clauses_pointed_to A W \<subseteq> clauses_pointed_to B W\<close>
  by (auto simp: clauses_pointed_to_def)
 
lemma simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and \<open>(i,j) \<in> nat_rel\<close> and
    point: \<open>no_lost_clause_in_WL S\<close>
  shows
  \<open>simplify_clause_with_unit_st_wl i S \<le> \<Down> {(S',T). (S',T) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S' \<and>
    get_watched_wl S' = get_watched_wl S}
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
  have KK[simp]: \<open>irred b j \<Longrightarrow> j \<in># dom_m b \<Longrightarrow>  C \<subseteq># mset (b \<propto> j) \<Longrightarrow>
    set_mset (all_lits_of_mm (add_mset (mset (b \<propto> j))
    (add_mset C
    (mset `# remove1_mset (b \<propto> j) (init_clss_lf b) + d + f + h)))) =
    set_mset (all_lits_of_mm (mset `# (init_clss_lf b) + d + f + h))\<close>
    for b j C d f h
    using all_lits_of_m_mono[of C \<open>mset (b \<propto> j)\<close>]
    by (auto simp: image_mset_remove1_mset_if ran_m_def conj_disj_distribR Collect_disj_eq
      image_Un Collect_conv_if all_lits_of_mm_add_mset
      simp flip: insert_compr
      dest!: multi_member_split[of j])
 
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
  have [simp]: \<open>mset a \<subseteq># mset b \<Longrightarrow> length a= 1 \<Longrightarrow> a ! 0 \<in> set b\<close> for a b
     by (cases a, auto)
   have K1: \<open>\<forall>L\<in>#all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l b#} + d + f + h).
     distinct_watched (k L) \<Longrightarrow>
     irred b j \<Longrightarrow>
     j \<in># dom_m b \<Longrightarrow>
     L \<in># all_lits_of_m (mset (b \<propto> j)) \<Longrightarrow> distinct_watched (k L)\<close> for b d f h k j L
     by (auto simp: ran_m_def all_lits_of_mm_add_mset dest!: multi_member_split)
   have K2: \<open>\<forall>L\<in>#all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l b#} + d + f + h).
     distinct_watched (k L) \<Longrightarrow>
     irred b j \<Longrightarrow>
     j \<in># dom_m b \<Longrightarrow>
     mset C \<subseteq># mset (b \<propto> j) \<Longrightarrow>
     length C = Suc 0 \<Longrightarrow>
     L \<in># all_lits_of_m ({#C!0#}) \<Longrightarrow> distinct_watched (k L)\<close> for b d f h k j L C
     using all_lits_of_m_mono[of \<open>mset C\<close> \<open>mset (b \<propto> j)\<close>]
      all_lits_of_m_mono[of \<open>{#C!0#}\<close> \<open>mset C\<close>]
     by (auto simp: ran_m_def all_lits_of_mm_add_mset dest!: multi_member_split[of _ \<open>dom_m _\<close>])
   have K3: \<open>\<forall>L\<in>#all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l b#} + d + f + h).
     distinct_watched (k L) \<Longrightarrow>
     L \<in># all_lits_of_mm ({#mset (fst x). x \<in># remove1_mset (the (fmlookup b j)) (init_clss_l b)#} + d + f + h) \<Longrightarrow>
     distinct_watched (k L)\<close> for b d f h k j L C
     by (cases \<open>j \<in># dom_m b\<close>; cases \<open>irred b j\<close>)
      (auto  dest!: multi_member_split[of _ \<open>dom_m _\<close>] simp: ran_m_def
         all_lits_of_mm_union all_lits_of_mm_add_mset image_mset_remove1_mset_if
       split: if_splits)
  have K4: \<open>
    irred b j \<Longrightarrow> j \<in># dom_m b \<Longrightarrow>
    all_lits_of_mm
    (add_mset (mset (b \<propto> j))
    ({#mset (fst x). x \<in># init_clss_l (fmdrop j b)#} + d + f + h)) =
    all_lits_of_mm
    ({#mset (fst x). x \<in># init_clss_l b#} + d + f + h)\<close>
    \<open>\<not>irred b j \<Longrightarrow> j \<in># dom_m b \<Longrightarrow>
    all_lits_of_mm
    (add_mset (mset (b \<propto> j))
    ({#mset (fst x). x \<in># learned_clss_l (fmdrop j b)#} + d + f + h)) =
    all_lits_of_mm
    ({#mset (fst x). x \<in># learned_clss_l b#} + d + f + h)\<close>
    for d f h j b
    using distinct_mset_dom[of b]
    apply (auto simp add: init_clss_l_fmdrop learned_clss_l_fmdrop_if)
    by (smt (z3) fmupd_same image_mset_add_mset learned_clss_l_mapsto_upd prod.collapse
        union_mset_add_mset_left)

  show ?thesis
    supply [[goals_limit=1]]
    using ST point
    apply (cases S; hypsubst)
    apply (cases T; hypsubst)
    unfolding simplify_clause_with_unit_st_wl_def simplify_clause_with_unit_st_def ij
      state_wl_l_def prod.simps Let_def[of \<open>(_,_)\<close>]
    apply refine_rcg
    subgoal for a b c d e f g h i ja k aa ba ca da ea fa ga ha ia jaa ka
      using ST
      unfolding simplify_clause_with_unit_st_wl_pre_def
      by (rule_tac x = \<open>(aa, ba, ca, da, ea, fa, ga, ha, ia, jaa, ka)\<close> in exI)
       simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
      apply (rule Id)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal
        by (auto simp add: all_learned_lits_of_wl_def all_init_lits_of_l_def
          all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
          all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def
        no_lost_clause_in_WL_def
        dest: in_diffD)
      subgoal by auto
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by  (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal apply (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev add_mset_commute
        no_lost_clause_in_WL_def
        dest: in_diffD
        intro:)
        done
      subgoal by auto
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal by (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev all_lits_of_mm_add_mset
        no_lost_clause_in_WL_def
        dest: in_diffD)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal for a b c d e f g h i ja k aa ba ca da ea fa ga ha ia jaa ka x x' x1 x2 x1a x2a
        apply (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
          init_clss_l_fmdrop_irrelev H
          no_lost_clause_in_WL_def
        dest: in_diffD
          intro: )
        apply (metis (no_types, lifting) basic_trans_rules(31) dom_m_fmdrop insert_DiffM) 
        apply (metis (no_types, lifting) basic_trans_rules(31) dom_m_fmdrop init_clss_l_fmdrop_irrelev insert_DiffM)
        done
      done
qed

lemma [twl_st_wl, simp]:
  assumes \<open>(\<sigma>, \<sigma>') \<in> state_wl_l None\<close>
  shows
    all_learned_lits_of_l_all_learned_lits_of_wl:
      \<open>all_learned_lits_of_l \<sigma>' = all_learned_lits_of_wl \<sigma>\<close> and
    all_init_lits_of_l_all_init_lits_of_wl:
      \<open>all_init_lits_of_l \<sigma>' = all_init_lits_of_wl \<sigma>\<close>
  using assms by (auto simp: state_wl_l_def all_learned_lits_of_l_def
    all_learned_lits_of_wl_def all_init_lits_of_l_def
    all_init_lits_of_wl_def)

lemma simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    point: \<open>correct_watching'' S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows
    \<open>simplify_clauses_with_unit_st_wl S \<le> \<Down> {(S',T). (S',T) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S' \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S' \<and> get_watched_wl S' = get_watched_wl S}
    (simplify_clauses_with_unit_st T)\<close>
proof -
  have [refine0]: \<open>inj_on id xs\<close> for xs
    by auto
  have 1: \<open>simplify_clauses_with_unit_st_wl S = do {
    T \<leftarrow> simplify_clauses_with_unit_st_wl S;
    RETURN T}\<close>
    by auto
  have 2: \<open>simplify_clauses_with_unit_st T = do {
    T \<leftarrow> simplify_clauses_with_unit_st T;
    RETURN T}\<close>
    by auto
  have ST2: \<open>(S,T) \<in>  {(S',U). (S',U) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S' \<and>
    get_watched_wl S = get_watched_wl S'}\<close>
    if \<open>simplify_clauses_with_unit_st_pre T\<close>
    using assms correct_watching''_clauses_pointed_to0[OF ST] that
    unfolding simplify_clauses_with_unit_st_inv_def
      simplify_clauses_with_unit_st_pre_def
    by auto
  show ?thesis
    apply (subst 1)
    unfolding simplify_clauses_with_unit_st_wl_def simplify_clauses_with_unit_st_def
      nres_monad3
    apply (refine_rcg simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st)
    subgoal
      using assms ST2 unfolding simplify_clauses_with_unit_st_wl_pre_def
      by blast
    subgoal
      using ST by auto
      subgoal by auto
        apply (rule ST2, assumption)
    subgoal by auto
    subgoal for xs xsa it \<sigma> it' \<sigma>'
      using assms apply -
      unfolding simplify_clauses_with_unit_st_wl_inv_def
      apply (rule exI[of _ T])
      apply (rule exI[of _ \<sigma>'])
      by auto
    apply (rule_tac T1=\<sigma>' and j1 = x' in
        simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st[THEN order_trans])
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (rule conc_fun_R_mono)
        (use assms(3) in \<open>auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_def
        blits_in_\<L>\<^sub>i\<^sub>n'_def\<close>)
    subgoal
      using ST lits
      by (auto 4 3 simp: literals_are_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def
        blits_in_\<L>\<^sub>i\<^sub>n'_def)
    subgoal
      using ST by auto
    subgoal
      using ST lits
      by (auto 4 3 simp: literals_are_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def
        blits_in_\<L>\<^sub>i\<^sub>n'_def)
    done
qed


end