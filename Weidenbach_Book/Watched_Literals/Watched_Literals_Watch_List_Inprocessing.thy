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


subsection \<open>Backward subsumption\<close>

text \<open>We follow the implementation of backward that is in Splatz and not the more advanced one
in CaDiCaL that relies on occurrence lists. Both version are similar
(so changing it is not a problem), but IsaSAT needs a way to say that the state is not watching.
This in turns means that GC needs to go over the clause domain instead of the watch lists, but
makes it possible to reuse the watch lists for other things, like forward subsumption (that again
only differs by the lists we use to check subsumption).

Compared to Splatz the literal-move-to-front trick is not included (at least not currently).
  \<close>
definition backward_correctly_sorted_int where
  \<open>backward_correctly_sorted_int N xs k \<longleftrightarrow> distinct xs \<and> k \<le> length xs \<and>
  (\<forall>i<length xs. i \<ge> k \<longrightarrow>
    (xs!i \<in># dom_m N \<longrightarrow>
    (\<forall>j<i. xs!j \<in># dom_m N \<longrightarrow> length (N \<propto> (xs!j)) \<le> length (N \<propto> (xs!i))))) \<and>
  (\<forall>j< length xs. j\<ge>k \<longrightarrow> xs!j \<in># dom_m (N))\<close>

definition backward_correctly_sorted where
  \<open>backward_correctly_sorted S xs k \<longleftrightarrow>
    backward_correctly_sorted_int (get_clauses_wl S) xs k\<close>

lemma backward_correctly_sorted_init:
  \<open>(\<forall>i \<in> set xs. i \<in># dom_m (get_clauses_wl S)) \<Longrightarrow> distinct xs \<Longrightarrow> k < length xs \<Longrightarrow>
  sorted_wrt (\<lambda>j i. length (get_clauses_wl S \<propto> j) \<le> length (get_clauses_wl S \<propto> i)) xs \<Longrightarrow>
  backward_correctly_sorted S xs k\<close>
  unfolding backward_correctly_sorted_def backward_correctly_sorted_int_def
  apply (intro conjI impI allI ballI)
  subgoal by auto
  subgoal by auto
  subgoal for i j
    by (auto dest: sorted_wrt_nth_less)
  subgoal
    by auto
  done

definition subsume_clauses_match_pre :: \<open>_\<close> where
  \<open>subsume_clauses_match_pre C C' N  \<longleftrightarrow>
  length (N \<propto> C) \<le> length (N \<propto> C') \<and> C \<in># dom_m N \<and> C' \<in># dom_m N \<and> distinct (N \<propto> C) \<and> distinct (N \<propto> C') \<and>
  \<not>tautology (mset (N \<propto> C'))\<close>

definition subsume_clauses_match :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat, 'v literal list \<times> bool) fmap \<Rightarrow> 'v subsumption nres\<close> where
  \<open>subsume_clauses_match C C' N = do {
  ASSERT (subsume_clauses_match_pre C C' N);
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). try_to_subsume C C' (N (C' \<hookrightarrow> take i (N \<propto> C'))) s\<^esup> (\<lambda>(i, st). i < length (N \<propto> C') \<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      let L = N \<propto> C' ! i;
      if L \<in> set (N \<propto> C)
      then RETURN (i+1, st)
      else if -L \<in> set (N \<propto> C)
      then if is_subsumed st
      then RETURN (i+1, STRENGTHENED_BY L C')
      else RETURN (i+1, NONE)
      else RETURN (i+1, NONE)
    })
     (0, SUBSUMED_BY C');
  RETURN st
  }\<close>

lemma subset_remove1_mset_notin:
  \<open>b \<notin># A \<Longrightarrow> A \<subseteq># remove1_mset b B \<longleftrightarrow> A\<subseteq>#B\<close>
  by (metis diff_subset_eq_self mset_le_subtract remove1_mset_eqE subset_mset.order_trans)

lemma subsume_clauses_match:
  assumes \<open>subsume_clauses_match_pre C C' N\<close>
  shows \<open>subsume_clauses_match C C' N \<le> \<Down> Id (SPEC(try_to_subsume C C' N))\<close>
proof -
  let ?R = \<open>measure (\<lambda>(i, _). Suc (length(N \<propto> C')) - i)\<close>
  have [refine]: \<open>wf ?R\<close>
    by auto
  have H: \<open>distinct_mset(mset (N \<propto> C))\<close>  \<open>distinct (N \<propto> C')\<close>
    using assms by (auto simp: subsume_clauses_match_pre_def)
  then have [simp]: \<open>a < length (N \<propto> C') \<Longrightarrow> distinct_mset (add_mset (N \<propto> C' ! a) (mset (take a (N \<propto> C'))))\<close>
    \<open>a < length (N \<propto> C') \<Longrightarrow> distinct_mset ((mset (take a (N \<propto> C'))))\<close>for a
    by (simp_all add: distinct_in_set_take_iff)
  then have [simp]: \<open>a < length (N \<propto> C') \<Longrightarrow> distinct_mset (add_mset (N \<propto> C' ! a) (remove1_mset L (mset (take a (N \<propto> C')))))\<close> for a L
    using diff_subset_eq_self distinct_mset_add_mset in_diffD distinct_mset_mono by metis
  have neg_notin: \<open>a < length (N \<propto> C') \<Longrightarrow>- N \<propto> C' ! a \<notin> set (N \<propto> C')\<close> for a
    using assms
    by (smt (z3) mset_le_trans mset_lt_single_iff nth_mem set_mset_mset subsume_clauses_match_pre_def tautology_minus)
  have neg_notin2: \<open>a < length (N \<propto> C') \<Longrightarrow>- N \<propto> C' ! a \<notin> set (take a (N \<propto> C'))\<close> for a
    using assms by (meson in_set_takeD neg_notin)
  have [simp]: \<open>fmupd C' (the (fmlookup N C')) N = N\<close>
    by (meson assms fmupd_same subsume_clauses_match_pre_def)
  have [simp]: \<open>try_to_subsume C C' N NONE\<close>
    by (auto simp: try_to_subsume_def)
  have [simp]: \<open>a < length (N \<propto> C') \<Longrightarrow>
    x21 \<in> set (take a (N \<propto> C')) \<Longrightarrow>
    N \<propto> C' ! a \<in># remove1_mset (- x21) (mset (N \<propto> C)) \<longleftrightarrow> N \<propto> C' ! a \<in># mset (N \<propto> C)\<close> for a x21
    apply (cases \<open>(- x21) \<in># mset (N \<propto> C)\<close>)
    apply (drule multi_member_split)
    by (auto simp del: set_mset_mset in_multiset_in_set simp: uminus_lit_swap neg_notin2
       eq_commute[of \<open>N \<propto> C' ! _\<close>])
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


definition backward_subsumption_all_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>backward_subsumption_all_wl_pre S = 
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> backward_subsumption_all_pre T)\<close>

definition backward_subsumption_all_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>backward_subsumption_all_wl_inv S xs = (\<lambda>(i, T).
  (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
    backward_subsumption_all_inv  S' (mset (drop i xs), T') \<and> backward_correctly_sorted S xs i))\<close>


definition backward_subsumption_one_wl_inv :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> _ \<Rightarrow> bool\<close> where
  \<open>backward_subsumption_one_wl_inv = (\<lambda>C S xs (i, s).
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> backward_subsumption_one_inv C T (mset (take i xs), s)))\<close>

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

definition backward_subsumption_one_wl_pre :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>backward_subsumption_one_wl_pre = (\<lambda>k S xs.
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and>  backward_subsumption_one_pre (xs!k) S' \<and>
  backward_correctly_sorted S xs k \<and> k < length xs))\<close>


definition backward_subsumption_one_wl :: \<open>nat \<Rightarrow> nat list \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>backward_subsumption_one_wl = (\<lambda>k xs S . do {
  ASSERT (backward_subsumption_one_wl_pre k S xs);
  let C = xs!k;
  let ys = take k xs;
  (xs, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> backward_subsumption_one_wl_inv C S ys \<^esup> (\<lambda>(i, s). i < k \<and> s = NONE)
    (\<lambda>(i, s). do {
      let C' = xs ! i;
      if C' \<notin># dom_m (get_clauses_wl S)
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> subsume_clauses_match C C' (get_clauses_wl S);
       RETURN (i+1, s)
      }
    })
    (0, NONE);
  S \<leftarrow> subsume_or_strengthen_wl C s S;
  RETURN S
  }
        )\<close>

lemma
  assumes \<open>backward_correctly_sorted_int N xs k\<close>
  shows backward_correctly_sorted_intI1:
      \<open>i < k \<Longrightarrow> backward_correctly_sorted_int (fmdrop (xs!i) N) xs k\<close>
      \<open>j' < k \<Longrightarrow> xs!j' \<in># dom_m N \<Longrightarrow> backward_correctly_sorted_int (fmupd (xs ! j') (N \<propto> (xs ! j'), b) N) xs k\<close> and
   backward_correctly_sorted_intI2:
      \<open>k < length xs \<Longrightarrow> backward_correctly_sorted_int N xs (Suc k)\<close>
      \<open>k < length xs \<Longrightarrow> backward_correctly_sorted_int (fmupd (xs ! k) (remove1 (- t') (N \<propto> (xs ! k)), b) N) xs (Suc k)\<close>
proof -
  have [simp]: \<open>x \<notin># dom_m N - {#a, x#}\<close>
    \<open>x \<notin># dom_m N - {#x, a#}\<close> 
    \<open>x \<notin># dom_m N - {#x#}\<close>  for x1m a x
    by (smt (z3) add_mset_commute add_mset_diff_bothsides add_mset_remove_trivial_eq
      distinct_mset_add_mset distinct_mset_dom in_diffD)+
  have [simp]: \<open>j \<noteq> i \<Longrightarrow> j < length xs \<Longrightarrow> i < length xs \<Longrightarrow>
    xs ! j \<in># remove1_mset (xs ! i) (dom_m N) \<longleftrightarrow>  xs ! j \<in># (dom_m N)\<close>
    \<open>j < length xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! j = xs ! i \<longleftrightarrow> j = i\<close> for j i
    by (metis assms backward_correctly_sorted_int_def in_remove1_mset_neq nth_eq_iff_index_eq)+
  show \<open>i < k \<Longrightarrow> backward_correctly_sorted_int (fmdrop (xs!i) N) xs k\<close>
    using assms
    by (auto simp: backward_correctly_sorted_int_def)

  show \<open>k < length xs \<Longrightarrow> backward_correctly_sorted_int N xs (Suc k)\<close>
    using assms
    by (auto simp: backward_correctly_sorted_int_def)
  have \<open>i < length xs \<Longrightarrow>
    Suc k \<le> i \<Longrightarrow> length ((N \<propto> (xs ! k))) \<le> length (N \<propto> (xs ! i))\<close> for i
    using assms unfolding backward_correctly_sorted_int_def by auto
  
  then have [simp]: \<open>i < length xs \<Longrightarrow>
    Suc k \<le> i \<Longrightarrow> length (remove1 L (N \<propto> (xs ! k))) \<le> length (N \<propto> (xs ! i))\<close> for i L
    apply (auto simp: length_remove1)
    by (meson diff_le_self le_trans)
  show \<open>k < length xs \<Longrightarrow> backward_correctly_sorted_int (fmupd (xs ! k) (remove1 (- t') (N \<propto> (xs ! k)), b) N) xs (Suc k)\<close>
    using assms
    by (auto simp: backward_correctly_sorted_int_def)
  show \<open>j' < k \<Longrightarrow> xs!j' \<in># dom_m N \<Longrightarrow> backward_correctly_sorted_int (fmupd (xs ! j') (N \<propto> (xs ! j'), b) N) xs k\<close>
    using assms
    by (auto simp: backward_correctly_sorted_int_def)
qed
 
lemma strengthen_clause_wl_strengthen_clause:
  assumes 
    \<open>(C, C') \<in> nat_rel\<close> and
    \<open>(s, s') \<in> nat_rel\<close> and
    \<open>(t, t') \<in> Id\<close> and
    \<open>(S, S') \<in> state_wl_l None\<close> and
    b: \<open>backward_correctly_sorted S xs k\<close> and
    \<open>C = xs ! k\<close> and
    \<open>s' = xs ! j'\<close> and
    \<open>j' < k\<close> and
    \<open>k < length xs\<close>
  shows \<open>strengthen_clause_wl C s t S
      \<le> \<Down> {(S, S').
        (S, S') \<in> state_wl_l None \<and> backward_correctly_sorted S xs (Suc k)}
      (strengthen_clause C' s' t' S')\<close>
proof -
  have dist: \<open>distinct xs\<close>
    using b unfolding backward_correctly_sorted_def backward_correctly_sorted_int_def by auto
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
  show ?thesis
    using assms
    unfolding strengthen_clause_wl_def strengthen_clause_def
    apply refine_vcg
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto 5 2 simp: state_wl_l_def backward_correctly_sorted_def
        intro!: backward_correctly_sorted_intI1 intro: backward_correctly_sorted_intI2 split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def backward_correctly_sorted_def length_remove1
      intro!: backward_correctly_sorted_intI1 intro: backward_correctly_sorted_intI2 split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def backward_correctly_sorted_def 
      intro!: backward_correctly_sorted_intI1 intro: backward_correctly_sorted_intI2 split: subsumption.splits)
    done
qed

lemma subsume_or_strengthen_wl_subsume_or_strengthen:
  assumes 
    \<open>(C, C') \<in> nat_rel\<close> and
    \<open>(s, s') \<in> Id\<close> and
    \<open>(t, t') \<in> Id\<close> and
    \<open>(S, S') \<in> state_wl_l None\<close> and
    \<open>C = xs ! k\<close> and
    \<open>is_subsumed s' \<Longrightarrow> subsumed_by s' = xs ! j' \<and> j' < k\<close> and
    \<open>is_strengthened s' \<Longrightarrow> strengthened_by s' = xs ! j' \<and> j' < k\<close> and
    \<open>k < length xs\<close>
    \<open>backward_correctly_sorted S xs k\<close>
  shows \<open>subsume_or_strengthen_wl C s S \<le> \<Down>{(S, S'). (S, S') \<in> state_wl_l None \<and> backward_correctly_sorted S xs (k + 1)}
    (subsume_or_strengthen C' s' S')\<close>
    using assms
  unfolding subsume_or_strengthen_wl_def subsume_or_strengthen_def
  apply (refine_vcg strengthen_clause_wl_strengthen_clause)
  subgoal unfolding subsume_or_strengthen_wl_pre_def by fast
  subgoal by (auto simp: state_wl_l_def backward_correctly_sorted_def subsume_or_strengthen_pre_def
    intro!: backward_correctly_sorted_intI1 intro: backward_correctly_sorted_intI2
    intro!: strengthen_clause_wl_strengthen_clause[THEN order_trans]
    split: subsumption.splits)
  done

definition backward_subsumption_all_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>backward_subsumption_all_wl = (\<lambda>S. do {
  ASSERT (backward_subsumption_all_wl_pre S);
  xs \<leftarrow> SPEC (\<lambda>xs. mset xs \<subseteq># dom_m (get_clauses_wl S) \<and>
     sorted_wrt (\<lambda>i j. length (get_clauses_wl S \<propto> i) \<le> length (get_clauses_wl S \<propto> j)) xs);
  (xs, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> backward_subsumption_all_wl_inv S xs \<^esup> (\<lambda>(i, S). i < length xs \<and> get_conflict_wl S = None)
    (\<lambda>(i, S). do {
       let C = xs!i;
       if C \<notin># dom_m (get_clauses_wl S)
       then RETURN (i+1, S)
       else do {
         S \<leftarrow> simplify_clause_with_unit_st_wl C S;
         if get_conflict_wl S = None \<and> C \<in># dom_m (get_clauses_wl S) then do {
           S \<leftarrow> backward_subsumption_one_wl i xs S;
           RETURN (i+1, S)
         }
         else RETURN (i+1, S)
      }
    })
    (0, S);
  RETURN S
  }
)\<close>

end