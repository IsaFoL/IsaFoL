theory Watched_Literals_Watch_List_Inprocessing
  imports Watched_Literals_Watch_List Watched_Literals_List_Inprocessing
    Watched_Literals_Watch_List_Restart
begin

definition simplify_clause_with_unit_st_wl_pre where
  \<open>simplify_clause_with_unit_st_wl_pre C S \<longleftrightarrow> (\<exists>T.
  (S, T) \<in> state_wl_l None \<and>
  simplify_clause_with_unit_st_pre C T)\<close>

definition simplify_clause_with_unit_st_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>simplify_clause_with_unit_st_wl = (\<lambda>C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT(simplify_clause_with_unit_st_wl_pre C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None \<and> no_dup M \<and> C \<noteq> 0);
    let S = (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
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
        let T = (M, fmdrop C N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NEk, UEk, NS, US, N0, U0, Q, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN T
      }
      else if size (N \<propto> C) = 1
      then do {
        let L = ((N \<propto> C) ! 0);
        let T = (Propagated L 0 # M, fmdrop C N, D, NE, UE, (if irr then add_mset {#L#} else id) NEk, (if \<not>irr then add_mset {#L#} else id)UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        ASSERT (undefined_lit M L \<and> L \<in># all_lits_st S);
        RETURN T
      }
      else if size (N \<propto> C) = 0
      then do {
         let T =  (M, fmdrop C N, Some {#}, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W);
        ASSERT(set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN T
      }
      else do {
        let T =  (M, N, D, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W);
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
    xs \<leftarrow> SPEC(\<lambda>xs. finite xs);
    T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
      (xs)
      (\<lambda>S. get_conflict_wl S = None)
      (\<lambda>i S. if i \<in># dom_m (get_clauses_wl S) then simplify_clause_with_unit_st_wl i S else RETURN S)
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
    subgoal for a b c d e f g h i ja k l m aa ba ca da ea fa ga ha ia jaa ka la ma
      using ST
      unfolding simplify_clause_with_unit_st_wl_pre_def
      by (rule_tac x = \<open>(aa, ba, ca, da, ea, fa, ga, ha, ia, jaa, ka, la, ma)\<close> in exI)
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
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal by auto
      subgoal by (auto simp: all_lits_st_alt_def all_learned_lits_of_wl_def
        all_init_lits_of_l_def all_init_lits_of_wl_def get_init_clss_l_def)
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
        apply (rule ST2, assumption)
    subgoal by auto
    subgoal for xs xsa it \<sigma> it' \<sigma>'
      using assms apply -
      unfolding simplify_clauses_with_unit_st_wl_inv_def
      apply (rule exI[of _ T])
      apply (rule exI[of _ \<sigma>'])
      by auto
    subgoal by auto
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
      using ST by auto
    subgoal
      using ST lits
      by (auto 4 3 simp: literals_are_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def
        blits_in_\<L>\<^sub>i\<^sub>n'_def)
    subgoal
      using ST lits
      by (auto 4 3 simp: literals_are_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def
        blits_in_\<L>\<^sub>i\<^sub>n'_def)
    done
qed

definition simplify_clauses_with_units_st_wl_pre where
  \<open>simplify_clauses_with_units_st_wl_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> correct_watching'' S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition simplify_clauses_with_units_st_wl where
  \<open>simplify_clauses_with_units_st_wl S = do {
    ASSERT(simplify_clauses_with_units_st_wl_pre S);
    new_units \<leftarrow> SPEC (\<lambda>_. True);
    if new_units
    then simplify_clauses_with_unit_st_wl S
    else RETURN S}\<close>

lemma simplify_clauses_with_units_st_wl_simplify_clause_with_units_st:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    point: \<open>correct_watching'' S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows
    \<open>simplify_clauses_with_units_st_wl S \<le> \<Down> {(S',T). (S',T) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S' \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S' \<and> get_watched_wl S' = get_watched_wl S}
    (simplify_clauses_with_units_st T)\<close>
  unfolding simplify_clauses_with_units_st_wl_def simplify_clauses_with_units_st_def
  apply (refine_vcg simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st)
  subgoal using assms unfolding simplify_clauses_with_units_st_wl_pre_def by fast
  subgoal by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms unfolding simplify_clauses_with_units_st_pre_def
    by (fast intro!: correct_watching''_clauses_pointed_to0(2))
  done


subsection \<open>Forward subsumption\<close>

text \<open>We follow the implementation of forward that is in Splatz and not the more advanced one
in CaDiCaL that relies on occurrence lists. Both version are similar
(so changing it is not a problem), but IsaSAT needs a way to say that the state is not watching.
This in turns means that GC needs to go over the clause domain instead of the watch lists, but
makes it possible to reuse the watch lists for other things, like forward subsumption (that again
only differs by the lists we use to check subsumption).

  Compared to Splatz the literal-move-to-front trick is not included (at least not currently).

There is critical but major subtility: The algorithm does not work on binary clauses: Binary clauses
can yield new units, which in turn, can shorten clauses later, forcing a rehash of the clauses.
There are two solutions to this problem:
  \<^item> avoid it completely by making sure that there are no binary clauses, requiring to duplicate the
    code (even if only few invariants change)
  \<^item> give up on the invariant
  \<^item> implement forward subsumption directly.

Long story short: we gave up and implemented the forward approach directly.


We do the simplifications in two rounds:
  \<^item> one with binary clauses only
  \<^item> one with all other clauses

TODO
This has the advantage that we do not have to care new units when subsuming all other clauses, 
avoiding various special causes. To reduce the effort, we use the same code base with a flag
to indicate which code we use.
\<close>

definition subsume_clauses_match_pre :: \<open>_\<close> where
  \<open>subsume_clauses_match_pre C C' N  \<longleftrightarrow>
  length (N \<propto> C) \<le> length (N \<propto> C') \<and> C \<in># dom_m N \<and> C' \<in># dom_m N \<and> distinct (N \<propto> C) \<and> distinct (N \<propto> C') \<and>
  \<not>tautology (mset (N \<propto> C))\<close>

definition subsume_clauses_match :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat, 'v literal list \<times> bool) fmap \<Rightarrow> 'v subsumption nres\<close> where
  \<open>subsume_clauses_match C C' N = do {
  ASSERT (subsume_clauses_match_pre C C' N);
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). try_to_subsume C' C (N (C \<hookrightarrow> take i (N \<propto> C))) s\<^esup> (\<lambda>(i, st). i < length (N \<propto> C) \<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      let L = N \<propto> C ! i;
      if L \<in> set (N \<propto> C')
      then RETURN (i+1, st)
      else if -L \<in> set (N \<propto> C')
      then if is_subsumed st
      then RETURN (i+1, STRENGTHENED_BY L C)
      else RETURN (i+1, NONE)
      else RETURN (i+1, NONE)
    })
     (0, SUBSUMED_BY C);
  RETURN st
  }\<close>

lemma subset_remove1_mset_notin:
  \<open>b \<notin># A \<Longrightarrow> A \<subseteq># remove1_mset b B \<longleftrightarrow> A\<subseteq>#B\<close>
  by (metis diff_subset_eq_self mset_le_subtract remove1_mset_eqE subset_mset.order_trans)

lemma subsume_clauses_match:
  assumes \<open>subsume_clauses_match_pre C C' N\<close>
  shows \<open>subsume_clauses_match C C' N \<le> \<Down> Id (SPEC(try_to_subsume C' C N))\<close>
proof -
  let ?R = \<open>measure (\<lambda>(i, _). Suc (length(N \<propto> C)) - i)\<close>
  have [refine]: \<open>wf ?R\<close>
    by auto
  have H: \<open>distinct_mset(mset (N \<propto> C))\<close>  \<open>distinct (N \<propto> C')\<close>
    using assms by (auto simp: subsume_clauses_match_pre_def)
  then have [simp]: \<open>a < length (N \<propto> C) \<Longrightarrow> distinct_mset (add_mset (N \<propto> C ! a) (mset (take a (N \<propto> C))))\<close>
    \<open>a < length (N \<propto> C) \<Longrightarrow> distinct_mset ((mset (take a (N \<propto> C))))\<close>for a
    by (simp_all add: distinct_in_set_take_iff)
  then have [simp]: \<open>a < length (N \<propto> C) \<Longrightarrow> distinct_mset (add_mset (N \<propto> C ! a) (remove1_mset L (mset (take a (N \<propto> C)))))\<close> for a L
    using diff_subset_eq_self distinct_mset_add_mset in_diffD distinct_mset_mono by metis
  have neg_notin: \<open>a < length (N \<propto> C) \<Longrightarrow>- N \<propto> C ! a \<notin> set (N \<propto> C)\<close> for a
    using assms
    by (smt (z3) mset_le_trans mset_lt_single_iff nth_mem set_mset_mset subsume_clauses_match_pre_def tautology_minus)
  have neg_notin2: \<open>a < length (N \<propto> C) \<Longrightarrow>- N \<propto> C ! a \<notin> set (take a (N \<propto> C))\<close> for a
    using assms by (meson in_set_takeD neg_notin)
  have [simp]: \<open>fmupd C (the (fmlookup N C)) N = N\<close>
    by (meson assms fmupd_same subsume_clauses_match_pre_def)
  have [simp]: \<open>try_to_subsume C' C N NONE\<close>
    by (auto simp: try_to_subsume_def)
  have [simp]: \<open>a < length (N \<propto> C) \<Longrightarrow>
    x21 \<in> set (take a (N \<propto> C)) \<Longrightarrow>
    N \<propto> C ! a \<in># remove1_mset (- x21) (mset (N \<propto> C')) \<longleftrightarrow> N \<propto> C ! a \<in># mset (N \<propto> C')\<close> for a x21
    apply (cases \<open>(- x21) \<in># mset (N \<propto> C')\<close>)
    apply (drule multi_member_split)
    by (auto simp del: set_mset_mset in_multiset_in_set simp: uminus_lit_swap neg_notin2
       eq_commute[of \<open>N \<propto> C ! _\<close>])
  show ?thesis
    unfolding subsume_clauses_match_def
    apply (refine_vcg)
    subgoal using assms by auto
    subgoal by (auto simp add: try_to_subsume_def)
    subgoal for s a b x1 x2
      by (auto 9 7 simp: try_to_subsume_def take_Suc_conv_app_nth subset_remove1_mset_notin neg_notin2
        split: subsumption.splits
        simp del: distinct_mset_add_mset
        simp flip: distinct_subseteq_iff)
    subgoal
      by auto
    subgoal for s a b x1 x2
      by (auto 7 4 simp: try_to_subsume_def take_Suc_conv_app_nth subset_remove1_mset_notin neg_notin2
        split: subsumption.splits
        simp del: distinct_mset_add_mset
        simp flip: distinct_subseteq_iff)
    subgoal by auto
    subgoal for s a b x1 x2
      by (auto 7 4 simp: try_to_subsume_def take_Suc_conv_app_nth 
        split: subsumption.splits
        simp del: distinct_mset_add_mset
        simp flip: distinct_subseteq_iff)
    subgoal by auto
    subgoal by (auto simp: try_to_subsume_def)
    subgoal by auto
    subgoal by auto
    done
qed


definition forward_subsumption_all_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_wl_pre S = 
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> forward_subsumption_all_pre T)\<close>

definition forward_subsumption_all_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_wl_inv S xs = (\<lambda>(i, T).
  (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
    forward_subsumption_all_inv  S' (mset (drop i xs), T')))\<close>


definition forward_subsumption_one_wl_inv :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> _ \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl_inv = (\<lambda>C S xs (i, s).
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> forward_subsumption_one_inv C T (mset (drop i xs), s)))\<close>

definition subsume_or_strengthen_wl_pre :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>subsume_or_strengthen_wl_pre C s S = (\<exists>T. (S, T) \<in> state_wl_l None \<and> subsume_or_strengthen_pre C s T)\<close>

definition strengthen_clause_wl :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow>
   'v twl_st_wl  \<Rightarrow>  'v twl_st_wl nres\<close> where
  \<open>strengthen_clause_wl = (\<lambda>C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
  if length (N \<propto> C) = 2
  then do {
     ASSERT (length (remove1 (-L) (N \<propto> C)) = 1);
     let L = hd (remove1 (-L) (N \<propto> C));
       RETURN (Propagated L 0 # M, fmdrop C' (fmdrop C N), D,
       (if irred N C' then add_mset (mset (N \<propto> C')) else id) NE,
       (if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) UE,
        (if irred N C then add_mset {#L#} else id) NEk, (if \<not>irred N C then add_mset {#L#} else id) UEk,
        ((if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
       ((if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US,
       N0, U0, add_mset (-L) Q, W)
  }
  else if length (N \<propto> C) = length (N \<propto> C')
  then RETURN (M, fmdrop C' (fmupd C ((remove1 (-L) (N \<propto> C)), irred N C \<or> irred N C') N), D, NE, UE, NEk, UEk,
     ((if irred N C' then add_mset (mset (N \<propto> C')) else id)  o (if irred N C then add_mset (mset (N \<propto> C)) else id)) NS,
    ((if \<not>irred N C' then add_mset (mset (N \<propto> C')) else id) o (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id)) US,
     N0, U0, Q, W)
  else RETURN (M, fmupd C (remove1 (-L) (N \<propto> C), irred N C) N, D, NE, UE, NEk, UEk,
    (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
    (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, Q, W))\<close>

definition subsume_or_strengthen_wl :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> 'v twl_st_wl \<Rightarrow> _ nres\<close> where
  \<open>subsume_or_strengthen_wl = (\<lambda>C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
   ASSERT(subsume_or_strengthen_wl_pre C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
   (case s of
     NONE \<Rightarrow> RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)
   | SUBSUMED_BY C' \<Rightarrow> RETURN (M, fmdrop C (if \<not>irred N C' \<and> irred N C then fmupd C' (N \<propto> C', True) N else N), D,
          NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
      (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, Q, W)
   | STRENGTHENED_BY L C' \<Rightarrow> strengthen_clause_wl C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))
  })\<close>


definition forward_subsumption_one_wl_pre :: \<open>bool \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl_pre = (\<lambda>binary_only k S xs.
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and>  forward_subsumption_one_pre (xs!k) S' \<and> k < length xs \<and>
    (binary_only \<longrightarrow> (\<forall>C \<in> set xs. C \<in># dom_m (get_clauses_wl S) \<longrightarrow> length (get_clauses_wl S \<propto> C) = 2))))\<close>


definition forward_subsumption_one_wl :: \<open>bool \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> bool) nres\<close> where
  \<open>forward_subsumption_one_wl binary_only = (\<lambda>k xs S . do {
  ASSERT (forward_subsumption_one_wl_pre binary_only k S xs);
  let C = xs!k;
  let ys = take k xs;
  (xs, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl_inv C S ys \<^esup> (\<lambda>(i, s). i < k \<and> s = NONE)
    (\<lambda>(i, s). do {
      let C' = xs ! i;
      if C' \<notin># dom_m (get_clauses_wl S)
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> subsume_clauses_match C' C (get_clauses_wl S);
       RETURN (i+1, s)
      }
    })
    (0, NONE);
  S \<leftarrow> subsume_or_strengthen_wl C s S;
  RETURN (S, s \<noteq> NONE)
  })\<close>

definition strengthen_clause_pre :: \<open>_\<close> where
  \<open>strengthen_clause_pre xs C s t S \<longleftrightarrow>
     distinct xs \<and> C \<in># dom_m (get_clauses_wl S) \<close>

lemma strengthen_clause_wl_strengthen_clause:
  assumes 
    \<open>(C, C') \<in> nat_rel\<close> and
    \<open>(s, s') \<in> nat_rel\<close> and
    \<open>(t, t') \<in> Id\<close> and
    \<open>(S, S') \<in> state_wl_l None\<close> and
    \<open>C = xs ! k\<close> and
    \<open>s' = xs ! j'\<close> and
    \<open>j' < k\<close> and
    \<open>k < length xs\<close> and
    b: \<open>strengthen_clause_pre xs C s t S\<close>
  shows \<open>strengthen_clause_wl C s t S
      \<le> \<Down> {(T, T').
        (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S}
      (strengthen_clause C' s' t' S')\<close>
proof -
  have dist: \<open>distinct xs\<close>
    using b unfolding strengthen_clause_pre_def by auto
  have [simp]: \<open>x \<notin># dom_m x1m - {#a, x#}\<close>
    \<open>x \<notin># dom_m x1m - {#x, a#}\<close> 
    \<open>x \<notin># dom_m x1m - {#x#}\<close>  for x1m a x
    by (smt (z3) add_mset_commute add_mset_diff_bothsides add_mset_remove_trivial_eq
      distinct_mset_add_mset distinct_mset_dom in_diffD)+
  have [simp]: \<open>j < length xs \<Longrightarrow> j\<ge>Suc k \<Longrightarrow> xs ! j \<in># dom_m x1m - {#xs ! j', xs ! k#} \<longleftrightarrow> xs ! j \<in># dom_m x1m\<close> for j x1m
    using nth_eq_iff_index_eq[OF dist, of j' \<open>j\<close>]  \<open>j' < k\<close> 
      nth_eq_iff_index_eq[OF dist, of k \<open>j\<close>]
    by auto
  have [simp]: \<open>k < length xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! k = xs ! i \<longleftrightarrow> k = i\<close> for i
    using nth_eq_iff_index_eq[OF dist, of k \<open>i\<close>] by auto
  have H: \<open>xs ! k \<in># dom_m (get_clauses_wl S)\<close>
    using assms by (auto simp: strengthen_clause_pre_def)

  show ?thesis
    using assms
    unfolding strengthen_clause_wl_def strengthen_clause_def
    apply refine_vcg
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j
    x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t
      x2t x1u x2u x1v x2v x1w x2w
      by (auto 5 2 simp: state_wl_l_def intro: split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def length_remove1 no_lost_clause_in_WL_def split: subsumption.splits)
    subgoal using H
      apply (cases \<open>irred (get_clauses_wl S) (xs ! k)\<close>)
      by (auto simp: state_wl_l_def no_lost_clause_in_WL_def all_init_lits_of_wl_def
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd all_lits_of_mm_union init_clss_l_mapsto_upd_irrel
        dest!: all_lits_of_m_diffD split: subsumption.splits)
    done
qed

lemma subsume_or_strengthen_wl_subsume_or_strengthen:
  assumes 
    \<open>(C, C') \<in> nat_rel\<close> and
    \<open>(s, s') \<in> Id\<close> and
    \<open>(S, S') \<in> state_wl_l None\<close> and
    \<open>C = xs ! k\<close> and
    \<open>is_subsumed s' \<Longrightarrow> \<exists>j'. subsumed_by s' = xs ! j' \<and> j' < k\<close> and
    \<open>is_strengthened s' \<Longrightarrow> \<exists>j'. strengthened_by s' = xs ! j' \<and> j' < k\<close> and
    \<open>k < length xs\<close> and
    \<open>distinct xs \<and> C \<in># dom_m (get_clauses_wl S)\<close>
  shows \<open>subsume_or_strengthen_wl C s S \<le> \<Down>{(T, T'). (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S}
    (subsume_or_strengthen C' s' S')\<close>
    using assms
  unfolding subsume_or_strengthen_wl_def subsume_or_strengthen_def
  apply (refine_vcg strengthen_clause_wl_strengthen_clause)
  subgoal unfolding subsume_or_strengthen_wl_pre_def by fast
  subgoal by (auto simp: state_wl_l_def subsume_or_strengthen_pre_def strengthen_clause_pre_def
    intro!: strengthen_clause_wl_strengthen_clause[THEN order_trans]
    split: subsumption.splits)
  done

lemma forward_subsumption_one_wl:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    C: \<open>C = xs!k\<close> and
    [simp]: \<open>k < length xs\<close> and
    inv: \<open>distinct xs\<close>
  shows
   \<open>forward_subsumption_one_wl k xs S \<le> \<Down>({(T, T').
    (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S} \<times>\<^sub>f bool_rel)
    (forward_subsumption_one C S')\<close>
proof -
  let ?ys = \<open>take k xs\<close>
  have [refine0]: \<open>RETURN (take k xs) \<le> \<Down> {(xs,ys). mset xs = ys} (SPEC (\<lambda>xs. C \<notin># xs))\<close>
    (is \<open>_ \<le> \<Down>?XS _\<close>)
    using inv C by (auto simp: RETURN_def conc_fun_RES distinct_in_set_take_iff)
  have [refine0]: \<open>(take k xs, xsa) \<in> ?XS \<Longrightarrow>
    ((0, NONE), xsa, NONE) \<in> {((i, s), (ys, s')). s = s' \<and> ys = mset (drop i (take k xs)) \<and>
      (is_subsumed s \<longrightarrow> (\<exists>j'. subsumed_by s' = xs ! j' \<and> j' < k))\<and>
      (is_strengthened s \<longrightarrow> (\<exists>j'. strengthened_by s' = xs ! j' \<and> j' < k))}\<close> (is \<open>_ \<Longrightarrow> _ \<in> ?A\<close>) for xsa
    by (auto simp: Misc.slice_def)
  have H: \<open>(get_trail_l S', get_clauses_l S', get_conflict_l S', get_unkept_init_clauses_l S',
   get_unkept_learned_clss_l S', get_kept_init_clauses_l S', get_kept_learned_clss_l S',
   get_subsumed_init_clauses_l S', get_subsumed_learned_clauses_l S', get_init_clauses0_l S',
    get_learned_clauses0_l S', clauses_to_update_l S', literals_to_update_l S') = S'\<close>
    by (cases S') auto
  have subsume_clauses_match_pre: \<open>subsume_clauses_match_pre (xs ! x1a) (xs ! k) (get_clauses_wl S)\<close>
    if
      pre: \<open>forward_subsumption_one_pre C S'\<close> and
      wl_pre: \<open>forward_subsumption_one_wl_pre k S xs\<close> and
      xsa: \<open>(take k xs, xsa) \<in> ?XS\<close> and
      xx': \<open>(x, x') \<in> ?A\<close> and
      le: \<open>case x of (i, s) \<Rightarrow> i < k \<and> s = NONE\<close> and
      \<open>case x' of (xs, s) \<Rightarrow> xs \<noteq> {#} \<and> s = NONE\<close> and
      wl_inv: \<open>forward_subsumption_one_wl_inv (xs ! k) S (take k xs) x\<close> and
      inv: \<open>forward_subsumption_one_inv C S' x'\<close> and
      st: \<open>x' = (x1, x2)\<close> \<open>x = (x1a, x2a)\<close> and
      C': \<open>(xs ! x1a, C') \<in> nat_rel\<close> and
      \<open>\<not> xs ! x1a \<notin># dom_m (get_clauses_wl S)\<close> and
      C'_dom: \<open>\<not> C' \<notin># dom_m (get_clauses_l S')\<close>
    for xsa x x' x1 x2 x1a x2a C'
  proof -
    obtain S'' where
      inv: \<open>forward_subsumption_one_inv (xs ! k) S' (mset (drop x1a (take k xs)), x2a)\<close> and
      C': \<open>C' = xs ! x1a\<close> and
      \<open>k < length xs\<close> and
      x1a: \<open>x1a < k\<close>
      \<open>C \<noteq> 0\<close> and
      S'S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
      struct: \<open>twl_struct_invs S''\<close> and
      list_invs: \<open>twl_list_invs S'\<close>
      using inv C' le pre assms st xsa xx' unfolding forward_subsumption_one_wl_inv_def prod.simps
        forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by auto
    have \<open>length (get_clauses_wl S \<propto> (xs ! x1a)) \<le> length (get_clauses_wl S \<propto> (xs ! k))\<close> and
      k_dom: \<open>xs ! k \<in># dom_m (get_clauses_wl S)\<close>
      using C'_dom x1a SS' unfolding C'
      by (auto)
    moreover have \<open>distinct (get_clauses_wl S \<propto> (xs ! x1a))\<close> \<open>distinct (get_clauses_wl S \<propto> (xs ! k))\<close>
      \<open>\<not>tautology (mset (get_clauses_wl S \<propto> (xs ! k)))\<close>
      \<open>\<not>tautology (mset (get_clauses_wl S \<propto> (xs ! x1a)))\<close>
      using  C'_dom SS' S'S'' struct k_dom list_invs unfolding C' st twl_list_invs_def
      by (auto simp: subsume_or_strengthen_pre_def state_wl_l_def twl_struct_invs_def
        pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def ran_m_def add_mset_eq_add_mset
        split: subsumption.splits
        dest!: multi_member_split)
    ultimately show ?thesis
      using C'_dom SS' unfolding subsume_clauses_match_pre_def C'
      by auto
  qed
  show ?thesis
    unfolding forward_subsumption_one_wl_def forward_subsumption_one_def state_decomp_to_state_l
      H
    apply (rewrite at \<open>let _ = _ ! _ in _\<close> Let_def)
    apply (refine_vcg subsume_or_strengthen_wl_subsume_or_strengthen[where xs=xs and k=k]
      subsume_clauses_match[unfolded Down_id_eq])
    subgoal
      unfolding forward_subsumption_one_wl_pre_def
      by (rule_tac x=S' in exI)
        (cases S'; use assms in auto)
    subgoal for xsa x x' unfolding forward_subsumption_one_wl_inv_def case_prod_beta
      by (rule_tac x=S' in exI)
       (cases x'; cases x; use assms in \<open>auto simp:\<close>)
    subgoal by auto
    subgoal by (auto simp flip: Cons_nth_drop_Suc)
    subgoal using assms by auto
    subgoal by (auto simp flip: Cons_nth_drop_Suc)
    subgoal for xsa x x' x1 x2 x1a x2a C'
      by (rule subsume_clauses_match_pre)
    subgoal using assms by (auto simp: C)
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: try_to_subsume_def split: subsumption.splits)
    subgoal using assms by (auto simp: C)
    subgoal using assms by (auto simp: C)
    subgoal using assms by (auto simp: C)
      apply (rule refl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using inv by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition forward_subsumption_all_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>forward_subsumption_all_wl = (\<lambda>S. do {
  ASSERT (forward_subsumption_all_wl_pre S);
  xs \<leftarrow> SPEC (\<lambda>xs. mset xs \<subseteq># dom_m (get_clauses_wl S) \<and>
     sorted_wrt (\<lambda>i j. length (get_clauses_wl S \<propto> i) \<le> length (get_clauses_wl S \<propto> j)) xs);
  (xs, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_all_wl_inv S xs \<^esup> (\<lambda>(i, S). i < length xs \<and> get_conflict_wl S = None)
    (\<lambda>(i, S). do {
       let C = xs!i;
       if C \<notin># dom_m (get_clauses_wl S)
       then RETURN (i+1, S)
       else do {
         S \<leftarrow> simplify_clause_with_unit_st_wl C S;
         if get_conflict_wl S = None \<and> C \<in># dom_m (get_clauses_wl S) then do {
           S \<leftarrow> forward_subsumption_one_wl i xs S;
           RETURN (i+1, S)
         }
         else RETURN (i+1, S)
      }
    })
    (0, S);
  RETURN S
  }
)\<close>

lemma cdcl_twl_inprocessing_l_dom_get_clauses_l_mono:
  \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> dom_m (get_clauses_l T) \<subseteq># dom_m (get_clauses_l S)\<close>
  by (auto simp: cdcl_twl_inprocessing_l.simps cdcl_twl_unitres_true_l.simps cdcl_twl_unitres_l.simps
    cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps add_mset_eq_add_mset
    dest!: multi_member_split)

lemma rtranclp_cdcl_twl_inprocessing_l_dom_get_clauses_l_mono:
  \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<Longrightarrow> dom_m (get_clauses_l T) \<subseteq># dom_m (get_clauses_l S)\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_twl_inprocessing_l_dom_get_clauses_l_mono)
lemma forward_subsumption_one_wl:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    lost: \<open>no_lost_clause_in_WL S\<close>
  shows
   \<open>forward_subsumption_all_wl S \<le> \<Down>
    (state_wl_l None)
    (forward_subsumption_all S')\<close>
proof -
  have [refine]:
    \<open>SPEC
  (\<lambda>xs. mset xs \<subseteq># dom_m (get_clauses_wl S) \<and>
     sorted_wrt
      (\<lambda>i j. length (get_clauses_wl S \<propto> i) \<le> length (get_clauses_wl S \<propto> j)) xs)
    \<le> \<Down> {(xs,ys). mset xs = ys \<and> backward_correctly_sorted S xs 0}
    (SPEC (\<lambda>xs. xs \<subseteq># dom_m (get_clauses_l S')))\<close> (is \<open>_ \<le>\<Down>?XS _\<close>)
    using SS' distinct_mset_mono[OF _ distinct_mset_dom[of \<open>get_clauses_wl S\<close>], of \<open>mset _\<close>]
    by (auto simp: conc_fun_RES
      intro!: backward_correctly_sorted_init)
  have [refine]: \<open>(xs,ys) \<in> ?XS \<Longrightarrow>
    forward_subsumption_all_inv S' (ys, S') \<Longrightarrow>
    ((0, S), ys, S') \<in> {((i, T), (xsa, T')). xsa = mset (drop i xs) \<and> get_watched_wl T = get_watched_wl S \<and>
    (T, T') \<in> state_wl_l None \<and> backward_correctly_sorted T xs (i)}\<close>
    for xs ys
    using SS' unfolding forward_subsumption_all_wl_inv_def prod.simps mem_Collect_eq
    apply (intro conjI)
    apply (solves simp)
    apply (solves simp)
    by (use SS' in \<open>auto simp: forward_subsumption_all_wl_inv_def\<close>)
  have forward_subsumption_all_wl_inv_Suc_nothing:
    \<open>forward_subsumption_all_wl_inv S xs (x1a, x2a) \<Longrightarrow>
    x1a < length xs \<Longrightarrow>
  forward_subsumption_all_wl_inv S xs (Suc x1a, x2a)\<close> for xs x1a x2a S
    unfolding forward_subsumption_all_wl_inv_def prod.simps
    apply normalize_goal+
    apply (rename_tac S' T')
    apply (rule_tac x=S' in exI, rule_tac x=T' in exI)
    apply (cases \<open>x1a < length xs\<close>)
    by (auto simp add: backward_correctly_sorted_def
      forward_subsumption_all_inv_def simp flip: Cons_nth_drop_Suc
      intro: backward_correctly_sorted_intI1 backward_correctly_sorted_intI2
      dest: mset_le_add_mset_decr_left1)
 
  have forward_subsumption_all_wl_inv_no_lost:
    \<open>forward_subsumption_all_wl_inv S xs (x1a, x2a) \<Longrightarrow> get_watched_wl x2a = get_watched_wl S \<Longrightarrow>
    no_lost_clause_in_WL x2a\<close> for x2a x1a xs
    using lost
    unfolding forward_subsumption_all_wl_inv_def prod.simps forward_subsumption_all_inv_def apply -
    apply normalize_goal+
    apply (frule rtranclp_cdcl_twl_inprocessing_l_dom_get_clauses_l_mono)
    apply (frule rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
    by (auto simp add: no_lost_clause_in_WL_def watched_by_alt_def)

  show ?thesis
    unfolding forward_subsumption_all_wl_def  forward_subsumption_all_def
    apply (refine_vcg forward_subsumption_one_wl
      simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st)
    subgoal using SS' unfolding forward_subsumption_all_wl_pre_def by fast
    apply assumption+
    subgoal for xs xsa x x'
      unfolding forward_subsumption_all_wl_inv_def prod.simps mem_Collect_eq case_prod_beta
      apply (rule_tac x= S' in exI)
      apply (rule_tac x= \<open>snd x'\<close> in exI)
      apply (cases x'; use SS' in \<open>auto simp: forward_subsumption_all_wl_inv_def\<close>)
      done
    subgoal by auto
    subgoal by (auto simp flip: Cons_nth_drop_Suc)
    subgoal by auto
    subgoal by (auto simp flip: Cons_nth_drop_Suc
      simp: backward_correctly_sorted_def
      intro!: forward_subsumption_all_wl_inv_Suc_nothing backward_correctly_sorted_intI2)
    subgoal by auto
    subgoal by (auto intro!: forward_subsumption_all_wl_inv_no_lost)
    subgoal by auto
    subgoal by auto
    subgoal
      oops

text \<open>For documentation purpose, we keep the current try (because one day we might actually add
  backward subsumption and anyway a lot of it can be used for forward subsumption).\<close>

subsection \<open>Forward subsumption\<close>


definition forward_subsumption_one_wl :: \<open>nat \<Rightarrow> nat list \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>forward_subsumption_one_wl = (\<lambda>k xs S . do {
  ASSERT (forward_subsumption_one_wl_pre k S xs);
  let C = xs!k;
  let ys = take k xs;
S \<leftarrow> simplify_clause_with_unit_st_wl C S;
         if get_conflict_wl S = None \<and> C \<in># dom_m (get_clauses_wl S) then do {

  (xs, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl_inv C S ys \<^esup> (\<lambda>(i, s). i < k \<and> s = NONE)
    (\<lambda>(i, s). do {
      let C' = xs ! i;
      if C' \<notin># dom_m (get_clauses_wl S)
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> subsume_clauses_match C' C (get_clauses_wl S);
       RETURN (i+1, s)
      }
    })
    (0, NONE);
  S \<leftarrow> subsume_or_strengthen_wl C s S;
  RETURN S
  })\<close>

end