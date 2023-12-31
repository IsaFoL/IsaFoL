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
    (*TODO fix, broke during update to 2021-1*)
    apply (auto simp: ran_m_def all_lits_of_mm_add_mset
      dest!: multi_member_split[of _ \<open>dom_m _\<close>]
      dest: all_lits_of_m_mono
      intro!: image_mset_cong2 filter_mset_cong2)
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
    point: \<open>correct_watching'_nobin S\<close> and
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
    using assms that correct_watching'_nobin_clauses_pointed_to0[OF ST]
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



lemma simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st2:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    point: \<open>no_lost_clause_in_WL S\<close> and
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
    using assms that correct_watching'_nobin_clauses_pointed_to0[OF ST]
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
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition simplify_clauses_with_units_st_wl where
  \<open>simplify_clauses_with_units_st_wl S = do {
    ASSERT(simplify_clauses_with_units_st_wl_pre S);
    new_units \<leftarrow> SPEC (\<lambda>b. b \<longrightarrow> get_conflict_wl S = None);
    if new_units
    then simplify_clauses_with_unit_st_wl S
    else RETURN S}\<close>

lemma simplify_clauses_with_units_st_wl_simplify_clause_with_units_st:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    point: \<open>correct_watching'_nobin S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows
    \<open>simplify_clauses_with_units_st_wl S \<le> \<Down> {(S',T). (S',T) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S' \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S' \<and> get_watched_wl S' = get_watched_wl S}
    (simplify_clauses_with_units_st T)\<close>
  unfolding simplify_clauses_with_units_st_wl_def simplify_clauses_with_units_st_def
  apply (refine_vcg simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st)
  subgoal using assms unfolding simplify_clauses_with_units_st_wl_pre_def by fast
  subgoal using ST by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms unfolding simplify_clauses_with_units_st_pre_def
    by (fast intro!: correct_watching'_nobin_clauses_pointed_to0(2))
  done


lemma simplify_clauses_with_units_st_wl_simplify_clause_with_units_st2:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and
    point: \<open>no_lost_clause_in_WL S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows
    \<open>simplify_clauses_with_units_st_wl S \<le> \<Down> {(S',T). (S',T) \<in> state_wl_l None \<and>
    no_lost_clause_in_WL S' \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S' \<and> get_watched_wl S' = get_watched_wl S}
    (simplify_clauses_with_units_st T)\<close>
  unfolding simplify_clauses_with_units_st_wl_def simplify_clauses_with_units_st_def
  apply (refine_vcg simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st2)
  subgoal using assms unfolding simplify_clauses_with_units_st_wl_pre_def by fast
  subgoal using ST by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms unfolding simplify_clauses_with_units_st_pre_def
    by (fast intro!: correct_watching'_nobin_clauses_pointed_to0(2))
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
  \<^item> once with binary clauses only (this was part of the sc2020 version)
  \<^item> once with all other clauses (this is onging work)
\<close>


subsubsection \<open>Binary clauses\<close>

text \<open>This version does not enforce that binary clauses have not been deleted.\<close>
fun correct_watching'_leaking_bin :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching'_leaking_bin (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_init_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<longrightarrow> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> correctly_marked_as_binary N (i, K, b)) \<and>
        filter_mset (\<lambda>i. i \<in># dom_m N) (fst `# mset (W L)) =
  clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>

declare correct_watching'_leaking_bin.simps[simp del]

definition clause_remove_duplicate_clause_wl_pre :: \<open>_\<close> where
  \<open>clause_remove_duplicate_clause_wl_pre C S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
     clause_remove_duplicate_clause_pre C S' \<and> correct_watching'_leaking_bin S)\<close>

definition clause_remove_duplicate_clause_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>clause_remove_duplicate_clause_wl C = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q). do {
   ASSERT (clause_remove_duplicate_clause_wl_pre C (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q));
   RETURN (M, fmdrop C N, D, NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS, (if irred N C then id else add_mset (mset (N \<propto> C))) US, N0, U0, WS, Q)
 })\<close>

(*TODO Move*)
lemma filter_image_mset_removeAll:
  \<open>{#C \<in># A. P C#} - {#C \<in># replicate_mset (count A C') C'. P C#} =
    {#C \<in># A. P C \<and> C \<noteq> C'#}\<close>
  by (metis count_filter_mset filter_filter_mset filter_mset_neq image_filter_replicate_mset replicate_mset_0)

lemma filter_image_mset_swap: \<open>distinct_mset A \<Longrightarrow> distinct_mset B \<Longrightarrow>
  {#i \<in># A. i \<in># B \<and> P i#} = {#i \<in># B. i \<in># A \<and> P i#}\<close>
  by (smt (z3) Collect_cong distinct_mset_filter distinct_set_mset_eq set_mset_filter)
(*END Move*)

lemma correctly_marked_as_binary_fmdrop:
  \<open>i \<in># dom_m x1m \<Longrightarrow> i \<noteq> C' \<Longrightarrow> correctly_marked_as_binary x1m (i, K, b)\<Longrightarrow> correctly_marked_as_binary (fmdrop C' x1m) (i, K, b) \<close>
  by (auto simp: correctly_marked_as_binary.simps)

lemma correct_watching'_leaking_bin_remove_subsumedI:
  \<open>correct_watching'_leaking_bin (x1l, x1m, x1n, x1o, x1p, x1q, x1r, x1s, x1t, x1u, x1v, x1w, x2w) \<Longrightarrow>
    C' \<in># dom_m x1m \<Longrightarrow>
    irred x1m C' \<Longrightarrow>
    correct_watching'_leaking_bin
  (x1l, fmdrop C' x1m, x1n, x1o, x1p, x1q, x1r, add_mset (mset (x1m \<propto> C')) x1s, x1t, x1u,
   x1v, x1w, x2w)\<close>
  \<open>correct_watching'_leaking_bin (x1l, x1m, x1n, x1o, x1p, x1q, x1r, x1s, x1t, x1u, x1v, x1w, x2w) \<Longrightarrow>
    C' \<in># dom_m x1m \<Longrightarrow>
    \<not> irred x1m C' \<Longrightarrow>
    correct_watching'_leaking_bin
  (x1l, fmdrop C' x1m, x1n, x1o, x1p, x1q, x1r, x1s, add_mset (mset (x1m \<propto> C')) x1t, x1u,
  x1v, x1w, x2w)\<close>

  \<open>correct_watching'_leaking_bin (x1l, x1m, x1n, x1o, x1p, x1q, x1r, x1s, x1t, x1u, x1v, x1w, x2w) \<Longrightarrow>
    C' \<in># dom_m x1m \<Longrightarrow>
    irred x1m C' \<Longrightarrow>
    correct_watching'_leaking_bin
  (x1l, fmdrop C' x1m, x1n, add_mset (mset (x1m \<propto> C')) x1o, x1p, x1q, x1r, x1s, x1t, x1u,
   x1v, x1w, x2w)\<close>
  \<open>correct_watching'_leaking_bin (x1l, x1m, x1n, x1o, x1p, x1q, x1r, x1s, x1t, x1u, x1v, x1w, x2w) \<Longrightarrow>
    C' \<in># dom_m x1m \<Longrightarrow>
    \<not> irred x1m C' \<Longrightarrow>
    correct_watching'_leaking_bin
  (x1l, fmdrop C' x1m, x1n, x1o, add_mset (mset (x1m \<propto> C')) x1p, x1q, x1r, x1s, x1t, x1u,
  x1v, x1w, x2w)\<close>
  apply (auto simp: correct_watching'_leaking_bin.simps all_init_lits_of_wl_def
    image_mset_remove1_mset_if distinct_mset_remove1_All distinct_mset_dom correctly_marked_as_binary.simps
    clause_to_update_def filter_image_mset_removeAll)
  apply (drule bspec)
  apply assumption
  apply normalize_goal+
  apply (drule arg_cong[where f=\<open>filter_mset (\<lambda>C. C \<noteq> C')\<close>])
  apply (auto simp add: filter_filter_mset intro: filter_mset_cong)
  apply (drule bspec)
  apply assumption
  apply normalize_goal+
  apply (drule arg_cong[where f=\<open>filter_mset (\<lambda>C. C \<noteq> C')\<close>])
  apply (auto simp add: filter_filter_mset intro: filter_mset_cong)
  apply (drule bspec)
  apply assumption
  apply normalize_goal+
  apply (drule arg_cong[where f=\<open>filter_mset (\<lambda>C. C \<noteq> C')\<close>])
  apply (auto simp add: filter_filter_mset intro: filter_mset_cong)
  apply (drule bspec)
  apply assumption
  apply normalize_goal+
  apply (drule arg_cong[where f=\<open>filter_mset (\<lambda>C. C \<noteq> C')\<close>])
  apply (auto simp add: filter_filter_mset intro: filter_mset_cong)
  done

lemma clause_remove_duplicate_clause_wl_clause_remove_duplicate_clause:
  assumes \<open>(C,C')\<in>nat_rel\<close> \<open>(S,T)\<in> state_wl_l None\<close> \<open>correct_watching'_leaking_bin S\<close>
  shows \<open>clause_remove_duplicate_clause_wl C S \<le>
      \<Down>{(U, V). (U,V)\<in> state_wl_l None \<and> correct_watching'_leaking_bin U \<and> get_watched_wl U = get_watched_wl S} (clause_remove_duplicate_clause C' T)\<close>
  using assms unfolding clause_remove_duplicate_clause_wl_def
    clause_remove_duplicate_clause_def
  apply (refine_vcg)
  subgoal unfolding clause_remove_duplicate_clause_wl_pre_def
    by fast
  subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j
    x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u
    x2u x1v x2v x1w x2w
    by (auto simp: state_wl_l_def clause_remove_duplicate_clause_pre_def
      intro!: correct_watching'_leaking_bin_remove_subsumedI)
  done


definition binary_clause_subres_lits_wl_pre :: \<open>_\<close> where
  \<open>binary_clause_subres_lits_wl_pre C L L' S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> state_wl_l None \<and>
     binary_clause_subres_lits_pre C L L' S')\<close>

definition binary_clause_subres_wl :: \<open>nat \<Rightarrow> 'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>binary_clause_subres_wl C L L' = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
   ASSERT (binary_clause_subres_lits_wl_pre C L L' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
   RETURN (Propagated L 0 # M, fmdrop C N, D, NE, UE,
      (if irred N C then add_mset {#L#} else id) NEk, (if irred N C then id else add_mset {#L#}) UEk,
      (if irred N C then add_mset (mset (N \<propto> C)) else id) NS, (if irred N C then id else add_mset (mset (N \<propto> C))) US,
       N0, U0, add_mset (-L) Q, W)
 })\<close>

lemma all_init_lits_of_wl_add_drop_irred:
  assumes \<open>C' \<in># dom_m (x1m)\<close> \<open>irred x1m C'\<close>
  shows \<open>all_init_lits_of_wl
             ([], fmdrop C' x1m, x1n, x1o, {#}, x1q, {#},
              add_mset (mset (x1m \<propto> C')) x1s, {#}, x1u, {#}, x1w, x2w) =
  all_init_lits_of_wl
             ([], x1m, x1n, x1o, {#}, x1q, {#},
    x1s, {#}, x1u, {#}, x1w, x2w)\<close> (is ?A) and
    \<open>K' \<in> set (x1m \<propto> C') \<Longrightarrow> set_mset (all_init_lits_of_wl
     (x1l, x1m, None, x1o, x1p, add_mset {#K'#} x1q, x1r, x1s, x1t, x1u, x1v,
      add_mset (- K') x1w, x2w)) = set_mset (all_init_lits_of_wl
     (x1l, x1m, None, x1o, x1p, x1q, x1r, x1s, x1t, x1u, x1v, x1w, x2w))\<close> (is \<open>_ \<Longrightarrow> ?B\<close>)
proof -
  have A: \<open>init_clss_l x1m = add_mset (x1m \<propto> C', irred x1m C') (init_clss_l (fmdrop C' x1m))\<close>
    by (smt (z3) assms(1) assms(2) eq_fst_iff fmdrop_eq_update_eq2 init_clss_l_fmdrop_if
      init_clss_l_mapsto_upd le_boolD le_boolI' sndE)
  show ?A
    using assms
    by (auto simp: all_init_lits_of_wl_def all_lits_of_mm_add_mset init_clss_l_fmdrop_if
        image_mset_remove1_mset_if
      dest!: multi_member_split)[]
  show ?B if \<open>K' \<in> set (x1m \<propto> C')\<close>
    using assms that apply -
    apply (auto simp: all_init_lits_of_wl_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      in_all_lits_of_mm_uminus_iff)
   apply (subst A)
   apply (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset add_mset_eq_add_mset
     in_clause_in_all_lits_of_m in_set_mset_eq_in)
   apply (subst A)
   apply (auto simp add: all_lits_of_mm_add_mset all_lits_of_m_add_mset add_mset_eq_add_mset
     in_clause_in_all_lits_of_m in_set_mset_eq_in)
   done
qed

lemma correct_watching'_leaking_bin_fmdropI:
  assumes \<open>C' \<in># dom_m (x1m)\<close> \<open>irred x1m C'\<close>
  shows
     \<open>correct_watching'_leaking_bin
    (x1l, x1m, x1n, x1o, x1p,
    x1q, x1r, x1s, x1t, x1u,
    x1v, x1w, x2w) \<Longrightarrow> correct_watching'_leaking_bin
     (Propagated K' 0 # x1l, fmdrop C' x1m, x1n, x1o, x1p,
    x1q, x1r, add_mset (mset (x1m \<propto> C')) x1s, x1t, x1u,
    x1v, x1w, x2w)\<close>
  using assms distinct_mset_dom[of x1m]
  unfolding correct_watching'_leaking_bin.simps
  apply (auto simp: all_init_lits_of_wl_add_drop_irred distinct_mset_remove1_All clause_to_update_def
      filter_image_mset_removeAll correctly_marked_as_binary.simps
    dest: multi_member_split[of C'])
  apply (drule bspec)
  apply assumption
  apply normalize_goal+
  apply (drule arg_cong[where f=\<open>filter_mset (\<lambda>C. C \<noteq> C')\<close>])
  apply (auto simp add: filter_filter_mset intro: filter_mset_cong)
  done

lemma correct_watching'_leaking_bin_fmdropI_red:
  assumes \<open>C' \<in># dom_m (x1m)\<close> \<open>\<not>irred x1m C'\<close>
  shows
     \<open>correct_watching'_leaking_bin
    (x1l, x1m, x1n, x1o, x1p,
    x1q, x1r, x1s, x1t, x1u,
    x1v, x1w, x2w) \<Longrightarrow> correct_watching'_leaking_bin
     (Propagated K' 0 # x1l, fmdrop C' x1m, x1n, x1o, x1p,
    x1q, x1r, x1s, add_mset (mset (x1m \<propto> C')) x1t, x1u,
    x1v, x1w, x2w)\<close>
    \<open>correct_watching'_leaking_bin
    (x1l, x1m, x1n, x1o, x1p,
    x1q, x1r, x1s, x1t, x1u,
    x1v, x1w, x2w) \<Longrightarrow> correct_watching'_leaking_bin
     (x1l, x1m, None, x1o, x1p, x1q, add_mset {#K'#} x1r, x1s, x1t, x1u, x1v,
    add_mset (- K') x1w, x2w)\<close>
  subgoal
    using assms distinct_mset_dom[of x1m]
    unfolding correct_watching'_leaking_bin.simps
    apply (auto simp: all_init_lits_of_wl_add_drop_irred distinct_mset_remove1_All clause_to_update_def
      filter_image_mset_removeAll correctly_marked_as_binary.simps
      dest: multi_member_split[of C'])[]
    apply (drule bspec)
    apply assumption
    apply normalize_goal+
    apply (drule arg_cong[where f=\<open>filter_mset (\<lambda>C. C \<noteq> C')\<close>])
    apply (auto simp add: filter_filter_mset intro: filter_mset_cong)
    done
  subgoal
    using assms distinct_mset_dom[of x1m]
    unfolding correct_watching'_leaking_bin.simps
    by (auto simp: all_init_lits_of_wl_add_drop_irred distinct_mset_remove1_All clause_to_update_def
      filter_image_mset_removeAll all_init_lits_of_wl_def correctly_marked_as_binary.simps
      dest: multi_member_split[of C'])[]
  done

lemma correct_watching'_leaking_bin_add_unitI:
  assumes \<open>K' \<in># mset (x1m \<propto> C')\<close> \<open>C' \<in># dom_m x1m\<close> \<open>irred x1m C'\<close>
  shows \<open>correct_watching'_leaking_bin
     (x1l, x1m, None, x1o, x1p, x1q, x1r, x1s, x1t, x1u, x1v, x1w, x2w) \<Longrightarrow>
    correct_watching'_leaking_bin
     (x1l, x1m, None, x1o, x1p, add_mset {#K'#} x1q, x1r, x1s, x1t, x1u, x1v,
      add_mset (- K') x1w, x2w)\<close>
  using assms
  by (auto simp: correct_watching'_leaking_bin.simps clause_to_update_def
    all_init_lits_of_wl_add_drop_irred)

lemma binary_clause_subres_wl_binary_clause_subres:
  assumes \<open>(C,C')\<in>nat_rel\<close> \<open>(K,K')\<in>Id\<close> \<open>(L,L')\<in>Id\<close> \<open>(S,S')\<in> state_wl_l None\<close>
    \<open>correct_watching'_leaking_bin S\<close>
  shows \<open>binary_clause_subres_wl C K L S \<le>
      \<Down>{(U, V). (U,V)\<in> state_wl_l None \<and> correct_watching'_leaking_bin U \<and> get_watched_wl U = get_watched_wl S} (binary_clause_subres C' K' L' S')\<close>
  using assms unfolding binary_clause_subres_wl_def binary_clause_subres_def
  apply (refine_vcg)
  subgoal unfolding binary_clause_subres_lits_wl_pre_def
    by fast
  subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
    x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
    x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w
    apply (auto simp: state_wl_l_def
      intro!: correct_watching'_leaking_bin_fmdropI correct_watching'_leaking_bin_add_unitI
      correct_watching'_leaking_bin_fmdropI_red)
    apply (auto simp: binary_clause_subres_lits_pre_def)[2]
    apply (auto simp: state_wl_l_def
      intro!: correct_watching'_leaking_bin_fmdropI correct_watching'_leaking_bin_add_unitI
      correct_watching'_leaking_bin_fmdropI_red)
    apply (auto simp: binary_clause_subres_lits_pre_def)[2]
    apply (auto simp: state_wl_l_def
      intro!: correct_watching'_leaking_bin_fmdropI correct_watching'_leaking_bin_add_unitI
      correct_watching'_leaking_bin_fmdropI_red)
    done
  done

definition deduplicate_binary_clauses_pre_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>deduplicate_binary_clauses_pre_wl L S \<longleftrightarrow> (\<exists>T. (S, T) \<in> state_wl_l None \<and>
     deduplicate_binary_clauses_pre L T \<and> correct_watching'_leaking_bin S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition deduplicate_binary_clauses_inv_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool \<times> nat \<times> _\<times> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>deduplicate_binary_clauses_inv_wl S L = (\<lambda>(abort, i, mark, T).
   (\<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and>
     deduplicate_binary_clauses_inv L (fst `# mset (watched_by T L)) S'
       (abort, fst `# mset (drop i (watched_by T L)), mark, T') \<and> correct_watching'_leaking_bin T \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S \<and> get_watched_wl T = get_watched_wl S))\<close>

lemma deduplicate_binary_clauses_inv_wl_literals_are_in:
  \<open>deduplicate_binary_clauses_inv_wl S L  (abort, i, mark, T) \<Longrightarrow>
  literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
  supply [[goals_limit=1]]
  unfolding deduplicate_binary_clauses_inv_wl_def prod.simps
    deduplicate_binary_clauses_inv_def literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def
  apply normalize_goal+
  apply (frule rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l)
  apply (frule rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
  by (auto simp: watched_by_alt_def)

definition deduplicate_binary_clauses_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>deduplicate_binary_clauses_wl L S = do {
    ASSERT (deduplicate_binary_clauses_pre_wl L S);
    let CS = (\<lambda>_. None);
    let l = length (watched_by S L);
    (_, _, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup>deduplicate_binary_clauses_inv_wl S L\<^esup> (\<lambda>(abort, i, CS, S). \<not>abort \<and> i < l \<and> get_conflict_wl S = None)
      (\<lambda>(abort, i, CS, S).
      do {
         let (C,L', b) = (watched_by S L ! i);
         if C \<notin># dom_m (get_clauses_wl S) \<or> \<not>b then
           RETURN (abort, i+1, CS, S)
         else do {
           let L' = L';
           if defined_lit (get_trail_wl S) L' then do {
             U \<leftarrow> simplify_clause_with_unit_st_wl C S;
             ASSERT (set_mset (all_init_atms_st U) = set_mset (all_init_atms_st S));
             RETURN (defined_lit (get_trail_wl U) L, i+1, CS, U)
           }
           else if CS L' \<noteq> None then do {
             let C' = (if \<not>snd (the (CS L')) \<longrightarrow> \<not>irred (get_clauses_wl S) C then C else fst (the (CS L')));
             let CS = (if \<not>snd (the (CS L')) \<longrightarrow> \<not>irred (get_clauses_wl S) C then CS else CS (L' := Some (C, irred (get_clauses_wl S) C)));
             S \<leftarrow> clause_remove_duplicate_clause_wl C' S;
             RETURN (abort, i+1, CS, S)
           } else if CS (-L') \<noteq> None then do {
             S \<leftarrow> binary_clause_subres_wl C L (-L') S;
             RETURN (True, i+1, CS, S)
           } else do {
             RETURN (abort, i+1, CS (L' := Some (C, irred (get_clauses_wl S) C)), S)
           }
        }
      })
      (defined_lit (get_trail_wl S) L, 0, CS, S);
   RETURN S
}\<close>


lemma correct_watching'_leaking_bin_pure_lit:
  assumes
    \<open>correct_watching'_leaking_bin (a, b, c, d, e, f, g, h, i, ja, k, l, m)\<close>
    \<open>L \<in># all_init_lits_of_wl (a, b, c, d, e, f, g, h, i, ja, k, l, m)\<close>
  shows \<open>correct_watching'_leaking_bin
    (Propagated L 0 # a, b, c, d, e,
     add_mset {#L#} f, g, h, i, ja, k,
     add_mset (-L) l, m)\<close>
proof -
  have [simp]: \<open>set_mset (all_init_lits_of_wl
        ([], b, c, d, {#}, add_mset {#L#} f, {#}, h,
    {#}, ja, {#}, add_mset (-L) l, m)) =
    set_mset (all_init_lits_of_wl
    ([], b, c, d, {#}, f, {#}, h, {#}, ja, {#}, l, m))\<close>
    using assms unfolding all_init_lits_of_wl_def
    by (auto simp: all_init_lits_of_wl_def all_lits_of_mm_add_mset
      all_lits_of_m_add_mset all_lits_of_mm_union in_all_lits_of_mm_uminus_iff)
  show ?thesis
    using assms
    by (auto simp: correct_watching'_leaking_bin.simps clause_to_update_def)
qed

lemma correct_watching'_leaking_bin_propagate_unit_irred:
  assumes 
    \<open>irred b j\<close> and
    \<open>j \<in># dom_m b\<close> and
    \<open>correct_watching'_leaking_bin (a, b, c, d, e, f, g, h, i, ja, k, l, m)\<close>
    \<open>L \<in> set (b \<propto> j)\<close>
  shows \<open>correct_watching'_leaking_bin
    (Propagated L 0 # a, b, c, d, e,
     add_mset {#L#} f, g, h, i, ja, k,
     add_mset (-L) l, m)\<close>
proof -
  have \<open>L \<in># all_init_lits_of_wl (a, b, c, d, e, f, g, h, i, ja, k, l, m)\<close>
    using assms by (auto simp: all_lits_of_mm_union all_lits_of_mm_add_mset all_init_lits_of_wl_def
      ran_m_def in_clause_in_all_lits_of_m
      dest!: multi_member_split)
  from correct_watching'_leaking_bin_pure_lit[OF _ this] show ?thesis
    using assms by blast
qed


lemma correct_watching'_leaking_bin_propagate_unit_red:
  assumes 
    \<open>\<not>irred b j\<close> and
    \<open>j \<in># dom_m b\<close> and
    \<open>correct_watching'_leaking_bin (a, b, None, d, e, f, g, h, i, ja, k, l, m)\<close>
    \<open>L \<in> set (b \<propto> j)\<close>
  shows \<open>correct_watching'_leaking_bin
    (Propagated L 0 # a, b, None, d, e,
     f, add_mset {#L#} g, h, i, ja, k,
     add_mset (-L) l, m)\<close>
proof -
  have [simp]: \<open>set_mset (all_init_lits_of_wl
         ([], b, None, d, {#}, f, {#}, h, {#}, ja, {#},
        add_mset (- L) l, m)) =
    set_mset (all_init_lits_of_wl
     ([], b, None, d, {#}, f, {#}, h, {#}, ja, {#},
        l, m))\<close>
    using assms unfolding all_init_lits_of_wl_def
    by (auto simp: all_init_lits_of_wl_def all_lits_of_mm_add_mset
      all_lits_of_m_add_mset all_lits_of_mm_union)
  show ?thesis
    using assms
    by (auto simp: correct_watching'_leaking_bin.simps clause_to_update_def)
qed

lemma correct_watching'_leaking_bin_empty_conflict:
  \<open>correct_watching'_leaking_bin (a, b, c, d, e, f, g, h, i, ja, k, l, m) \<Longrightarrow>
  correct_watching'_leaking_bin (a, b, Some {#}, d, e, f, g, h, i, add_mset {#} ja, k, {#}, m)\<close>
  \<open>correct_watching'_leaking_bin (a, b, c, d, e, f, g, h, i, ja, k, l, m) \<Longrightarrow>
  correct_watching'_leaking_bin (a, b, Some {#}, d, e, f, g, h, i, ja, add_mset {#} k, {#}, m)\<close>
  by (auto simp: correct_watching'_leaking_bin.simps all_init_lits_of_wl_def
    all_lits_of_mm_add_mset all_lits_of_m_add_mset clause_to_update_def)

text \<open>For binary clauses, we can prove a stronger version of
  @{thm simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st}, because watched literals do
  not have to be changed.\<close>
lemma simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st_correct_watching:
  assumes ST: \<open>(S, T) \<in> state_wl_l None\<close> and ij: \<open>(i,j) \<in> nat_rel\<close> and
    point: \<open>correct_watching'_leaking_bin S\<close> and
    \<open>i \<in># dom_m (get_clauses_wl S)\<close> and
    Si: \<open>length (get_clauses_wl S \<propto> i) = 2\<close>
  shows
  \<open>simplify_clause_with_unit_st_wl i S \<le> \<Down> {(S',T). (S',T) \<in> state_wl_l None \<and>
    correct_watching'_leaking_bin S' \<and>
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
    apply (auto 5 2 simp: ran_m_def all_lits_of_mm_add_mset
      dest!: multi_member_split[of _ \<open>dom_m _\<close>]
      dest: all_lits_of_m_mono
      intro!: image_mset_cong2 filter_mset_cong2)
    apply (metis all_lits_of_m_union mset_subset_eq_exists_conv union_iff)
    apply (metis fmdrop_eq_update_eq fmupd_lookup union_single_eq_member)
    apply (metis add_mset_remove_trivial dom_m_fmdrop)
    done
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

  text \<open>This case is most likely impossible. It comes from the fact that we do not attempt to prove
    that the unchanged exactly captures when things are unchanged (missing backimplication).\<close>
  have correct_watching_after_same_length: \<open>\<not> irred b j \<longrightarrow>
    correct_watching'_leaking_bin
    (a, x2a, None, d, e, f, g, h, add_mset (mset (b \<propto> j)) i, ja, k,
    l, m)\<close> (is ?A)
     \<open>irred b j \<longrightarrow>
    correct_watching'_leaking_bin
    (a, x2a, None, d, e, f, g, add_mset (mset (b \<propto> j)) h, i, ja, k,
    l, m)\<close> (is ?B)
    if
      st: \<open>aa = a \<and>
      ba = b \<and>
      da = d \<and>
      ea = e \<and>
      fa = f \<and> ga = g \<and> ha = h \<and> ia = i \<and> jaa = ja \<and> ka = k \<and> ma = l\<close> and
      corr: \<open>correct_watching'_leaking_bin (a, b, None, d, e, f, g, h, i, ja, k, l, m)\<close> and
      S: \<open>S = (a, b, None, d, e, f, g, h, i, ja, k, l, m)\<close> and
      \<open>T = (a, b, None, d, e, f, g, h, i, ja, k, {#}, l)\<close> and
      \<open>simplify_clause_with_unit_st_pre j
      (a, b, None, d, e, f, g, h, i, ja, k, {#}, l)\<close> and
      \<open>ca = None \<and> la = {#}\<close> and
      \<open>simplify_clause_with_unit_st_wl_pre j
      (a, b, None, d, e, f, g, h, i, ja, k, l, m)\<close> and
      \<open>j \<in># dom_m b \<and>
      count_decided a = 0 \<and> c = None \<and> no_dup a \<and> 0 < j\<close> and
      \<open>x2c = x2a\<close> and
      \<open>x2 = (False, x2a)\<close> and
      \<open>x' = (False, False, x2a)\<close> and
      \<open>x2b = (False, x2a)\<close> and
      \<open>x = (False, False, x2a)\<close> and
      b: \<open>fmdrop j x2a = fmdrop j b \<and>
      irred x2a j = irred b j \<and>
      mset (x2a \<propto> j) \<subseteq># mset (b \<propto> j) \<and> j \<in># dom_m x2a\<close> and
      \<open>\<not> x1b\<close> and
      \<open>\<not> x1\<close> and
      \<open>\<not> x1c\<close> and
      \<open>\<not> x1a\<close> and
      le: \<open>length (x2a \<propto> j) \<noteq> Suc 0\<close>  \<open>x2a \<propto> j \<noteq> []\<close> and
      eq: \<open>set_mset
      (all_init_lits_of_l
      (a, x2a, None, d, e, f, g,
      (if irred b j then add_mset (mset (ba \<propto> j)) else id) h,
      (if irred b j then id else add_mset (mset (ba \<propto> j))) i, ja, k,
      {#}, l)) =
      set_mset
      (all_init_lits_of_l
      (a, b, None, d, e, f, g, h, i, ja, k, {#}, l))\<close>
      \<open>set_mset
      (all_learned_lits_of_l
      (a, x2a, None, d, e, f, g,
      (if irred b j then add_mset (mset (ba \<propto> j)) else id) h,
      (if irred b j then id else add_mset (mset (ba \<propto> j))) i, ja, k,
      {#}, l)) =
      set_mset
      (all_learned_lits_of_l
      (a, b, None, d, e, f, g, h, i, ja, k, {#}, l))\<close>
      \<open>set_mset
      (all_learned_lits_of_wl
      ([], x2a, None, d, e, f, g,
      (if irred b j then add_mset (mset (b \<propto> j)) else id) h,
      (if irred b j then id else add_mset (mset (b \<propto> j))) i, ja, k,
      l, m)) =
      set_mset
      (all_learned_lits_of_wl
      ([], b, None, d, e, f, g, h, i, ja, k, l, m))\<close>
      \<open>set_mset
      (all_init_lits_of_wl
      ([], x2a, None, d, {#}, f, {#},
      (if irred b j then add_mset (mset (b \<propto> j)) else id) h, {#}, ja,
      {#}, l, m)) =
      set_mset
      (all_init_lits_of_wl
      ([], b, None, d, {#}, f, {#}, h, {#}, ja, {#}, l, m))\<close>
    for a b c d e f g h i ja k l m aa ba ca da ea fa ga ha ia jaa ka la ma
      x x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    note [[goals_limit=1]]
    have [simp]: \<open>aa \<in># dom_m x2a \<Longrightarrow> length (x2a \<propto> aa) = length (b \<propto> aa)\<close> for aa
      apply (cases \<open>aa = j\<close>)
      subgoal
        using le b Si ij size_mset_mono[of \<open>mset (x2a \<propto> aa)\<close> \<open>mset (b \<propto> aa)\<close>]
        by (cases \<open>x2a \<propto> aa\<close>; cases \<open>tl (x2a \<propto> aa)\<close>)
         (clarsimp simp add: length_list_2 S subseteq_mset_size_eql_iff add_mset_eq_add_mset)+
      subgoal
        using b apply -
        apply normalize_goal+
        by (drule arg_cong [of _ _ \<open>\<lambda>a. a \<propto> aa\<close>]) auto
      done
    have [simp]: \<open>aa \<in># dom_m x2a \<Longrightarrow> set (x2a \<propto> aa) = set (b \<propto> aa)\<close> for aa
      apply (cases \<open>aa = j\<close>)
      subgoal
        using le b Si ij size_mset_mono[of \<open>mset (x2a \<propto> aa)\<close> \<open>mset (b \<propto> aa)\<close>]
        apply (simp add: S)
        apply (clarsimp_all simp add: length_list_2 S)
        by (cases \<open>x2a \<propto> aa\<close>; cases \<open>tl (x2a \<propto> aa)\<close>)
         (auto simp add: length_list_2 S subseteq_mset_size_eql_iff add_mset_eq_add_mset)
      subgoal
        using b apply -
        apply normalize_goal+
        by (drule arg_cong [of _ _ \<open>\<lambda>a. a \<propto> aa\<close>]) auto
      done
    have [simp]: \<open>aa \<in># dom_m x2a \<Longrightarrow> set (watched_l (x2a \<propto> aa)) = set (watched_l (b \<propto> aa))\<close> for aa
      apply (cases \<open>aa = j\<close>)
      subgoal
        using le b Si ij size_mset_mono[of \<open>mset (x2a \<propto> aa)\<close> \<open>mset (b \<propto> aa)\<close>]
        by (simp add: S)
      subgoal
        using b apply -
        apply normalize_goal+
        by (drule arg_cong [of _ _ \<open>\<lambda>a. a \<propto> aa\<close>]) auto
      done
    have [simp]: \<open>dom_m x2a = dom_m b\<close>
      using b by (metis dom_m_fmdrop insert_DiffM that(8))
    show ?A ?B
      using corr eq
      by (auto simp: st correct_watching'_leaking_bin.simps clause_to_update_def correctly_marked_as_binary.simps
        intro!: filter_mset_cong)
  qed
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
        intro: correct_watching'_leaking_bin_remove_subsumedI
        dest: in_diffD)
      subgoal by auto
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal by auto
      subgoal by (auto simp: all_lits_st_alt_def all_learned_lits_of_wl_def
        all_init_lits_of_l_def all_init_lits_of_wl_def get_init_clss_l_def)
      subgoal for a b c d e f g h i ja k l m aa ba ca da ea fa ga ha ia jaa ka la ma
        x x' x1 x2 x1a x2a x1b x2b x1c x2c
        apply (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
          init_clss_l_fmdrop_irrelev add_mset_commute
          no_lost_clause_in_WL_def
        intro: correct_watching'_leaking_bin_remove_subsumedI correct_watching'_leaking_bin_propagate_unit_irred[where j=j]
          correct_watching'_leaking_bin_propagate_unit_red[where j=j]
        dest: in_diffD
        intro:)
        apply (rule correct_watching'_leaking_bin_remove_subsumedI)
        apply (rule correct_watching'_leaking_bin_propagate_unit_irred[where j=j])
        apply auto
        apply (rule correct_watching'_leaking_bin_remove_subsumedI)
        apply (rule correct_watching'_leaking_bin_propagate_unit_red[where j=j])
        apply auto
        done
      subgoal by auto
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal by (auto simp: all_init_lits_of_wl_def init_clss_l_fmdrop
        init_clss_l_fmdrop_irrelev all_lits_of_mm_add_mset
        intro: correct_watching'_leaking_bin_remove_subsumedI correct_watching'_leaking_bin_empty_conflict
        dest: in_diffD)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def)
      subgoal by (auto simp: all_learned_lits_of_wl_def all_init_lits_of_l_def
        all_learned_lits_of_l_def get_init_clss_l_def all_init_lits_of_wl_def)
      subgoal for a b c d e f g h i ja k l m aa ba ca da ea fa ga ha ia jaa ka la ma
    x x' x1 x2 x1a x2a x1b x2b x1c x2c
        by (simp)
          (intro conjI; rule correct_watching_after_same_length; assumption)+
      done
qed

(*TODO Move*)
lemma WHILEIT_refine_with_inv:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>{(a,b). (a,b) \<in> R \<and> I a \<and> I' b} (WHILEIT I' b' f' x')" 
  apply (rule WHILEIT_refine_with_post)
  subgoal using R0 IREF by blast
  subgoal using IREF by blast
  subgoal using COND_REF by blast
  subgoal using STEP_REF IREF by (smt (verit, best) in_pair_collect_simp inres_SPEC pw_ref_iff)
  done

lemma deduplicate_binary_clauses_wl_deduplicate_binary_clauses:
  assumes \<open>(L,L')\<in>Id\<close> \<open>(S,S')\<in> state_wl_l None\<close>
    \<open>correct_watching'_leaking_bin S\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows \<open>deduplicate_binary_clauses_wl L S \<le>
      \<Down>{(S, T). (S,T)\<in> state_wl_l None \<and> correct_watching'_leaking_bin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} (deduplicate_binary_clauses L' S')\<close>
proof -
  let ?watched = \<open>{(i, CS). i = (length (watched_by S L)) \<and> CS = fst `# mset (watched_by S L) \<and>
       (\<forall>C. (C \<in># CS \<longrightarrow> C \<in># dom_m (get_clauses_l S') \<longrightarrow> L' \<in> set (get_clauses_l S' \<propto> C)))}\<close>
  have [refine0]: \<open>deduplicate_binary_clauses_pre_wl L S \<Longrightarrow> RETURN (length (watched_by S L))
    \<le> \<Down> ?watched (SPEC (\<lambda>CS. \<forall>C. (C \<in># CS \<longrightarrow> C \<in># dom_m (get_clauses_l S') \<longrightarrow> L' \<in> set (get_clauses_l S' \<propto> C)) \<and> distinct_mset CS))\<close>
    using assms
    apply (cases S)
    apply (auto simp: RETURN_RES_refine_iff correct_watching'_leaking_bin.simps
      deduplicate_binary_clauses_pre_wl_def deduplicate_binary_clauses_pre_def)
    apply (drule bspec)
     apply assumption
    apply auto
    apply (drule bspec)
     apply assumption
     apply (auto simp: clause_to_update_def distinct_mset_image_mset distinct_watched_alt_def dest: in_set_takeD
        dest!: multi_member_split split: if_splits)
     apply (meson in_set_takeD)
     apply (smt (z3) filter_mset_add_mset filter_mset_eq_add_msetD fst_conv image_mset_add_mset in_multiset_in_set multi_member_split)
     done
   let ?S = \<open>{((abort, i, CS, U), (abort', xs, CS', U')). abort=abort' \<and> fst `# mset (drop i (watched_by S L)) = xs \<and> CS=CS' \<and>
     (U,U')\<in> state_wl_l None \<and> get_watched_wl U = get_watched_wl S \<and> correct_watching'_leaking_bin U}\<close>
  have [refine0]: \<open>(length (watched_by S L), xs) \<in> ?watched \<Longrightarrow>
    ((defined_lit (get_trail_wl S) L, 0, Map.empty, S), defined_lit (get_trail_l S') L', xs,
    Map.empty, S') \<in> ?S\<close> for xs
    using assms by auto
  have watched_by: \<open>RETURN (watched_by x2e L ! x1d)
    \<le> \<Down> {((C, K, b), C'). C=C' \<and>
           (C \<in># dom_m (get_clauses_wl x2e) \<longrightarrow> b = (length (get_clauses_wl x2e \<propto> C) = 2) \<and> K \<noteq> L \<and> K \<in> set (get_clauses_wl x2e \<propto> C) \<and> L \<in> set (get_clauses_wl x2e \<propto> C))}
    (SPEC (\<lambda>C. C \<in># x1a))\<close> (is \<open>_ \<le> \<Down>?watch _\<close>)
    if
      LL': \<open>(L, L') \<in> Id\<close> and
      SS': \<open>(S, S') \<in> state_wl_l None\<close> and
      \<open>correct_watching'_leaking_bin S\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
      pre: \<open>deduplicate_binary_clauses_pre L' S'\<close> and
      \<open>deduplicate_binary_clauses_pre_wl L S\<close> and
      watched: \<open>(length (watched_by S L), xs) \<in> ?watched\<close> and
      xx': \<open>(x, x') \<in> ?S\<close> and
      abort: \<open>case x of
      (abort, i, CS, Sa) \<Rightarrow>
      \<not> abort \<and> i < length (watched_by S L) \<and> get_conflict_wl Sa = None\<close> and
      \<open>case x' of
      (abort, xs, CS, S) \<Rightarrow> \<not> abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      inv: \<open>deduplicate_binary_clauses_inv_wl S L x\<close> and
      inv2: \<open>deduplicate_binary_clauses_inv L' xs S' x'\<close> and
      st: \<open>x2a = (x1b, x2b)\<close>
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1c, x2c)\<close>
    for xs x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
  proof -
    have L_S: \<open>L \<in># all_init_lits_of_wl S\<close> \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S' x2b\<close>
      \<open>set_mset (all_init_lits_of_l x2b) = set_mset (all_init_lits_of_l S')\<close>
       \<open>set_mset (all_init_lits_of_wl x2e) = set_mset (all_init_lits_of_wl S)\<close>
      using pre SS' LL' inv2 xx' by (auto simp: deduplicate_binary_clauses_pre_def
        deduplicate_binary_clauses_inv_def st
        dest: rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l)
    have \<open>x1d < length (get_watched_wl S L)\<close>
      using xx' abort by (auto simp: watched_by_alt_def st)
    then have \<open>watched_by x2e L ! x1d \<in> set (get_watched_wl S L)\<close>
      \<open>get_watched_wl x2e = get_watched_wl S\<close>
      \<open>correct_watching'_leaking_bin x2e\<close>
      \<open>x1a = fst `# mset (drop x1d (watched_by S L))\<close>
      \<open>get_watched_wl S L ! x1d \<in> set (drop x1d (get_watched_wl S L))\<close>
      using xx' abort by (auto simp: watched_by_alt_def st intro!: in_set_dropI)
    moreover have \<open>fst (get_watched_wl S L ! x1d) \<in># dom_m (get_clauses_wl x2e) \<Longrightarrow>
        L \<in> set (get_clauses_wl x2e \<propto> fst (get_watched_wl S L ! x1d))\<close>
      using L_S(1) xx' \<open>watched_by x2e L ! x1d \<in> set (get_watched_wl S L)\<close> xx'
        multi_member_split[of \<open>watched_by x2e L ! x1d\<close> \<open>mset (get_watched_wl S L)\<close>]
      unfolding L_S(4)[symmetric]
      by (cases x2e)
       (auto simp: watched_by_alt_def correct_watching'_leaking_bin.simps st
        clause_to_update_def dest!: multi_member_split[of L]
        dest!: filter_mset_eq_add_msetD' in_set_takeD)
    ultimately show ?thesis
      using L_S unfolding st
      by (cases x2e)
       (auto simp: RETURN_RES_refine_iff watched_by_alt_def eq_commute[of \<open>(_, _, _)\<close>]
        correct_watching'_leaking_bin.simps correctly_marked_as_binary.simps 
        intro!: bexI[of _ \<open>watched_by x2e L ! x1d\<close>]
        dest!: multi_member_split[of L])
  qed
  have correct_blit: \<open>mset (get_clauses_l x2b \<propto> C) = {#L', x1g#}\<close>
    if
      LL': \<open>(L, L') \<in> Id\<close> and
      SS': \<open>(S, S') \<in> state_wl_l None\<close> and
      \<open>correct_watching'_leaking_bin S\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
      pre: \<open>deduplicate_binary_clauses_pre L' S'\<close> and
      \<open>deduplicate_binary_clauses_pre_wl L S\<close> and
      xs: \<open>(length (watched_by S L), xs) \<in> ?watched\<close> and
      xx': \<open>(x, x') \<in> ?S\<close> and
      abort: \<open>case x of
      (abort, i, CS, Sa) \<Rightarrow>
      \<not> abort \<and>
      i < length (watched_by S L) \<and> get_conflict_wl Sa = None\<close> and
      \<open>case x' of
      (abort, xs, CS, S) \<Rightarrow>
      \<not> abort \<and> xs \<noteq> {#} \<and> get_conflict_l S = None\<close> and
      inv: \<open>deduplicate_binary_clauses_inv_wl S L x\<close> and
      inv2: \<open>deduplicate_binary_clauses_inv L' xs S' x'\<close> and
      st: \<open>x2a = (x1b, x2b)\<close>
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1c, x2c)\<close>  and
      watch: \<open>(watched_by x2e L ! x1d, C) \<in> ?watch x2e\<close> and
      watcher: \<open>watched_by x2e L ! x1d = (x1f, x2f)\<close> 
        \<open>x2f = (x1g, x2g)\<close> and
      bin: \<open>\<not> (x1f \<notin># dom_m (get_clauses_wl x2e) \<or> \<not> x2g)\<close>
        \<open>\<not> (C \<notin># dom_m (get_clauses_l x2b) \<or> length (get_clauses_l x2b \<propto> C) \<noteq> 2)\<close>
    for xs x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e C x1f x2f x1g
      x2g
  proof -
    show ?thesis
      using watch xs bin SS' xx' LL' watcher
      by (auto simp: st length_list_2 watched_by_alt_def)
  qed

  have post_inv: \<open>(x2e, x2b)
     \<in> {(S, T).
        (S, T) \<in> state_wl_l None \<and>
        correct_watching'_leaking_bin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
    if 
      \<open>(L, L') \<in> Id\<close> and
      SS': \<open>(S, S') \<in> state_wl_l None\<close> and
      \<open>correct_watching'_leaking_bin S\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
      \<open>deduplicate_binary_clauses_pre L' S'\<close> and
      \<open>deduplicate_binary_clauses_pre_wl L S\<close> and
      \<open>(length (watched_by S L), xs) \<in> ?watched\<close> and
      xx': \<open>(x, x') \<in>{(a,b). (a,b) \<in> ?S \<and>
        deduplicate_binary_clauses_inv_wl S L a \<and>
       deduplicate_binary_clauses_inv L' xs S' b}\<close> and
      st: \<open>x2a = (x1b, x2b)\<close>
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1c, x2c)\<close>
      for xs x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
  proof -
    show ?thesis
      using xx' assms(4) SS' apply - unfolding mem_Collect_eq prod.simps st deduplicate_binary_clauses_inv_def
      apply normalize_goal+
      using rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l[of S' x2b]
        rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[of S' x2b]
      by (auto simp add: literals_are_\<L>\<^sub>i\<^sub>n'_def st blits_in_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def)
  qed
  show ?thesis
    supply [[goals_limit=1]]
    using assms unfolding deduplicate_binary_clauses_wl_def deduplicate_binary_clauses_def
    apply (refine_vcg simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st_correct_watching
      clause_remove_duplicate_clause_wl_clause_remove_duplicate_clause
      binary_clause_subres_wl_binary_clause_subres WHILEIT_refine_with_inv)
    subgoal unfolding deduplicate_binary_clauses_pre_wl_def
      by fast
    subgoal for xs x x'
      unfolding deduplicate_binary_clauses_inv_wl_def prod.simps case_prod_beta
      apply (rule exI[of _ S'])
      apply (rule exI[of _ \<open>snd (snd (snd x'))\<close>])
      by (auto simp: watched_by_alt_def)
    subgoal for xs x x'
      by auto
    apply (rule watched_by; assumption)
    subgoal for xs x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      by (auto intro!: imageI in_set_dropI simp: watched_by_alt_def)
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: watched_by_alt_def)
    subgoal by (rule correct_blit)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (clarsimp dest!: rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l
        simp: all_init_atms_st_alt_def)
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: watched_by_alt_def
      dest: deduplicate_binary_clauses_inv_wl_literals_are_in)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: watched_by_alt_def
      dest: deduplicate_binary_clauses_inv_wl_literals_are_in)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: watched_by_alt_def
      dest: deduplicate_binary_clauses_inv_wl_literals_are_in)
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: watched_by_alt_def
      dest: deduplicate_binary_clauses_inv_wl_literals_are_in)
    subgoal by (auto simp flip: Cons_nth_drop_Suc simp: watched_by_alt_def
      dest: deduplicate_binary_clauses_inv_wl_literals_are_in)
    subgoal by (rule post_inv)
    done
qed


definition mark_duplicated_binary_clauses_as_garbage_pre_wl :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_pre_wl = (\<lambda>S. (\<exists>T. (S,T) \<in> state_wl_l None  \<and>
     correct_watching'_leaking_bin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S))\<close>

definition mark_duplicated_binary_clauses_as_garbage_wl_inv :: \<open>'v multiset \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<times> 'v multiset \<Rightarrow> bool\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_wl_inv = (\<lambda>xs S (U, ys).
  \<exists>S' U'. (U, U') \<in> state_wl_l None \<and> (S, S') \<in> state_wl_l None \<and>
    mark_duplicated_binary_clauses_as_garbage_inv xs S' (U', ys))\<close>
  
definition mark_duplicated_binary_clauses_as_garbage_wl :: \<open>_ \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_wl S = do {
     ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl S);
     Ls \<leftarrow> SPEC (\<lambda>Ls:: 'v multiset. \<forall>L\<in>#Ls. L \<in># atm_of `# all_init_lits_of_wl S);
     (S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_duplicated_binary_clauses_as_garbage_wl_inv Ls S\<^esup>(\<lambda>(S, Ls). Ls \<noteq> {#} \<and> get_conflict_wl S = None)
      (\<lambda>(S, Ls). do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># Ls);
        ASSERT (L \<in># atm_of `# all_init_lits_of_wl S);
        skip \<leftarrow> RES (UNIV :: bool set);
        if skip then RETURN (S, remove1_mset L Ls)
        else do {
          S \<leftarrow> deduplicate_binary_clauses_wl (Pos L) S;
          S \<leftarrow> deduplicate_binary_clauses_wl (Neg L) S;
          RETURN (S, remove1_mset L Ls)
        }
     })
     (S, Ls);
    RETURN S
  }\<close>


lemma mark_duplicated_binary_clauses_as_garbage_wl:
  assumes  \<open>(S, S') \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_leaking_bin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}\<close>
  shows \<open>mark_duplicated_binary_clauses_as_garbage_wl S \<le>
    \<Down> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_leaking_bin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S}
    (mark_duplicated_binary_clauses_as_garbage S')\<close>
proof -
  let ?R = \<open>{(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching'_leaking_bin S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<times>\<^sub>f Id\<close>
  have loop: \<open>(Ls,Ls')\<in>Id \<Longrightarrow> ((S, Ls), (S', Ls')) \<in> ?R\<close> for Ls Ls'
    using assms by auto
  show ?thesis
    unfolding mark_duplicated_binary_clauses_as_garbage_wl_def mark_duplicated_binary_clauses_as_garbage_def
    apply (refine_vcg loop deduplicate_binary_clauses_wl_deduplicate_binary_clauses)
    subgoal using assms unfolding mark_duplicated_binary_clauses_as_garbage_pre_wl_def apply -
      by (rule exI[of _ S']) auto
    subgoal using assms by auto
    subgoal for Ls Lsa x x'
      unfolding mark_duplicated_binary_clauses_as_garbage_wl_inv_def
      apply (cases x, cases x', hypsubst, unfold prod.simps)
      apply (rule exI[of _ S'], rule exI[of _ \<open>fst x'\<close>])
      apply (use assms in simp)
      done
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


subsubsection \<open>Large clauses\<close>

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

definition subsume_or_strengthen_wl_pre :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>subsume_or_strengthen_wl_pre C s S \<longleftrightarrow> (\<exists>T. (S, T) \<in> state_wl_l None \<and>
     subsume_or_strengthen_pre C s T \<and> length (get_clauses_wl S \<propto> C) > 2)\<close>

definition strengthen_clause_wl :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow>
   'v twl_st_wl  \<Rightarrow>  'v twl_st_wl nres\<close> where
  \<open>strengthen_clause_wl = (\<lambda>C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
  ASSERT (subsume_or_strengthen_wl_pre C (STRENGTHENED_BY L C') (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
  E \<leftarrow> SPEC (\<lambda>E. mset E = mset (remove1 (-L) (N \<propto> C)));
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

definition subsume_or_strengthen_wl :: \<open>nat \<Rightarrow> 'v subsumption \<Rightarrow> 'v twl_st_wl \<Rightarrow> _ nres\<close> where
  \<open>subsume_or_strengthen_wl = (\<lambda>C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
   ASSERT(subsume_or_strengthen_wl_pre C s (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
   (case s of
     NONE \<Rightarrow> RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)
   | SUBSUMED_BY C' \<Rightarrow> do {
       let T = (M, fmdrop C (if \<not>irred N C' \<and> irred N C then fmupd C' (N \<propto> C', True) N else N), D,
          NE, UE, NEk, UEk, (if irred N C then add_mset (mset (N \<propto> C)) else id) NS,
         (if \<not>irred N C then add_mset (mset (N \<propto> C)) else id) US, N0, U0, Q, W);
        ASSERT (set_mset (all_init_atms_st T) = set_mset (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)));
        RETURN T
     }
   | STRENGTHENED_BY L C' \<Rightarrow> strengthen_clause_wl C C' L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))
  })\<close>


definition strengthen_clause_pre :: \<open>_\<close> where
  \<open>strengthen_clause_pre xs C s t S \<longleftrightarrow>
     distinct xs \<and> C \<in># dom_m (get_clauses_wl S) \<close>

lemma no_lost_clause_in_WLI:
  \<open>no_lost_clause_in_WL S \<Longrightarrow> set_mset (dom_m (get_clauses_wl T)) \<subseteq> set_mset (dom_m (get_clauses_wl S)) \<Longrightarrow>
  set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S) \<Longrightarrow>
  get_watched_wl S = get_watched_wl T \<Longrightarrow>
  no_lost_clause_in_WL T\<close>
  by (auto simp: no_lost_clause_in_WL_def clauses_pointed_to_def watched_by_alt_def dest!: multi_member_split)

lemma filter_mset_remove_add_mset: \<open>a \<in># M \<Longrightarrow>
  {#x \<in># M - add_mset a M'. P x#} = (if P a then remove1_mset a {#x \<in># M - M'. P x#} else {#x \<in># M - M'. P x#})\<close>
  by (auto dest!: multi_member_split)

lemma image_mset_remove_add_mset: \<open>a \<in># M \<Longrightarrow> a \<notin># M' \<Longrightarrow>
  {#f x. x \<in># M - add_mset a M'#} = remove1_mset (f a) {#f x. x \<in># M - M'#}\<close>
  by (auto dest!: multi_member_split)

lemma strengthen_clause_wl_strengthen_clause:
  assumes
    \<open>(C, C') \<in> nat_rel\<close> and
    \<open>(s, s') \<in> nat_rel\<close> and
    \<open>(t, t') \<in> Id\<close> and
    \<open>(S, S') \<in> state_wl_l None\<close> and
    b: \<open>strengthen_clause_pre xs C s t S\<close> and
    pre2: \<open>subsume_or_strengthen_wl_pre C (STRENGTHENED_BY t' s') S\<close>
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
  have H: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    using assms by (auto simp: strengthen_clause_pre_def)
  have [simp]: \<open>s' \<in># remove1_mset C (dom_m a) \<longleftrightarrow> s' \<noteq> C \<and> s' \<in>#dom_m a\<close> for a s' C
    by (auto dest: in_diffD)
  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding strengthen_clause_wl_def strengthen_clause_def
    apply refine_vcg
    subgoal using pre2 by fast
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j
    x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t
      x2t x1u x2u x1v x2v x1w x2w
      using distinct_mset_dom[of \<open>get_clauses_wl S\<close>]
      by (auto 5 2 simp: state_wl_l_def all_init_lits_of_wl_def init_clss_l_fmdrop_if strengthen_clause_pre_def
        Watched_Literals_List_Inprocessing.strengthen_clause_pre_def image_mset_remove_add_mset
        split: subsumption.splits dest: in_diffD dest: multi_member_split)
    subgoal by (auto simp: state_wl_l_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def length_remove1 no_lost_clause_in_WL_def split: subsumption.splits)
    subgoal by (auto simp: state_wl_l_def length_remove1 no_lost_clause_in_WL_def split: subsumption.splits)
    subgoal using H
      apply (cases \<open>irred (get_clauses_wl S) C\<close>)
      by (auto simp: state_wl_l_def no_lost_clause_in_WL_def all_init_lits_of_wl_def
        all_lits_of_mm_add_mset init_clss_l_mapsto_upd all_lits_of_mm_union init_clss_l_mapsto_upd_irrel
        dest!: all_lits_of_m_diffD split: subsumption.splits)
    done
qed

lemma case_subsumption_refine:
  \<open>(a,b)\<in>Id \<Longrightarrow>
  (is_subsumed a \<Longrightarrow> f(subsumed_by a )\<le> \<Down>R (f' (subsumed_by b))) \<Longrightarrow>
  (is_strengthened a \<Longrightarrow> g (strengthened_on_lit a) (strengthened_by a) \<le> \<Down>R (g' (strengthened_on_lit a) (strengthened_by a))) \<Longrightarrow>
  (a = NONE \<Longrightarrow> h \<le>\<Down>R h') \<Longrightarrow>
  case_subsumption f g h a \<le> \<Down> R (case_subsumption f' g' h' b)\<close>
  by (cases a) auto

lemma subsume_or_strengthen_wl_subsume_or_strengthen:
  assumes
    \<open>(C, C') \<in> nat_rel\<close> and
    \<open>(s, s') \<in> Id\<close> and
    \<open>(S, S') \<in> state_wl_l None\<close> and
    \<open>C \<in># dom_m (get_clauses_wl S)\<close> \<open>length (get_clauses_wl S \<propto> C) > 2\<close>
  shows \<open>subsume_or_strengthen_wl C s S \<le> \<Down>{(T, T'). (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S}
    (subsume_or_strengthen C' s' S')\<close>
  using assms
  unfolding subsume_or_strengthen_wl_def subsume_or_strengthen_def Let_def
  apply (refine_vcg strengthen_clause_wl_strengthen_clause case_subsumption_refine)
  subgoal unfolding subsume_or_strengthen_wl_pre_def by fast
  subgoal premises p
    using assms p(32-) unfolding p(1-31)
    by (auto simp: state_wl_l_def all_init_lits_of_wl_def all_init_lits_of_l_def
      all_init_atms_st_alt_def get_init_clss_l_def)
  subgoal
    unfolding in_pair_collect_simp
    by (auto simp: state_wl_l_def subsume_or_strengthen_pre_def strengthen_clause_pre_def
      intro!: strengthen_clause_wl_strengthen_clause[THEN order_trans] ASSERT_leI
      split: subsumption.splits)
  subgoal
    by (auto simp: state_wl_l_def subsume_or_strengthen_pre_def strengthen_clause_pre_def
      intro!: strengthen_clause_wl_strengthen_clause[THEN order_trans]
      split: subsumption.splits)
  subgoal
    by (auto simp: state_wl_l_def subsume_or_strengthen_pre_def strengthen_clause_pre_def
      no_lost_clause_in_WL_def
      intro!: strengthen_clause_wl_strengthen_clause[THEN order_trans]
      split: subsumption.splits)
  done


definition forward_subsumption_one_wl_pre :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl_pre = (\<lambda>C cands S.
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> no_lost_clause_in_WL S \<and> forward_subsumption_one_pre C cands S' \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' S))\<close>

definition forward_subsumption_one_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat multiset \<Rightarrow> nat multiset \<times> 'v subsumption \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl_inv = (\<lambda>S C cands (i, x).
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and>  forward_subsumption_one_inv C S' cands (i, x)))\<close>


definition forward_subsumption_one_wl_select where
  \<open>forward_subsumption_one_wl_select C cands S = (\<lambda>xs. C \<notin># xs \<and> cands \<inter># xs = {#} \<and>
 (\<forall>D\<in>#xs. D \<in># dom_m (get_clauses_wl S) \<longrightarrow>
    (\<forall>L\<in> set (get_clauses_wl S \<propto> D). undefined_lit (get_trail_wl S) L) \<and>
    (length (get_clauses_wl S \<propto> D) \<le> length (get_clauses_wl S \<propto> C))))\<close>

definition forward_subsumption_one_wl :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> bool) nres\<close> where
  \<open>forward_subsumption_one_wl = (\<lambda>C cands S\<^sub>0 . do {
  ASSERT (forward_subsumption_one_wl_pre C cands S\<^sub>0);
  ys \<leftarrow> SPEC (forward_subsumption_one_wl_select C cands S\<^sub>0);
  (xs, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_one_wl_inv S\<^sub>0 C ys \<^esup> (\<lambda>(xs, s). xs \<noteq> {#} \<and> s = NONE)
    (\<lambda>(xs, s). do {
      C' \<leftarrow> SPEC (\<lambda>C'. C' \<in># xs);
      if C' \<notin># dom_m (get_clauses_wl S\<^sub>0)
      then RETURN (remove1_mset C' xs, s)
      else do  {
       s \<leftarrow> subsume_clauses_match C' C (get_clauses_wl S\<^sub>0);
       RETURN (remove1_mset C' xs, s)
      }
    })
    (ys, NONE);
  S \<leftarrow> subsume_or_strengthen_wl C s S\<^sub>0;
  ASSERT (literals_are_\<L>\<^sub>i\<^sub>n' S \<and> set_mset (all_init_lits_of_wl S) = set_mset (all_init_lits_of_wl S\<^sub>0));
  RETURN (S, s \<noteq> NONE)
  })\<close>


lemma forward_subsumption_one_wl:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and \<open>no_lost_clause_in_WL S\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
    cands: \<open>(cands, cands') \<in> Id\<close>
  shows
   \<open>forward_subsumption_one_wl C cands S \<le> \<Down>({(T, T').
    (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S} \<times>\<^sub>f bool_rel)
    (forward_subsumption_one C cands' S')\<close>
proof -
  have [refine0]: \<open>(xs, ys) \<in> Id \<Longrightarrow> ((xs, NONE), (ys, NONE)) \<in> {(a,b). a = b \<and> b \<subseteq># ys} \<times>\<^sub>f Id\<close> (is \<open>_ \<Longrightarrow> _ \<in> ?loop\<close>) for xs ys :: \<open>nat multiset\<close>
    by auto
  have subsume_clauses_match_pre: \<open>subsume_clauses_match_pre C' C (get_clauses_wl S)\<close>
    if 
      pre: \<open>forward_subsumption_one_pre C cands' S'\<close> and
      \<open>forward_subsumption_one_wl_pre C cands S\<close> and
      xs_ys: \<open>(ys, xs) \<in> Id\<close> and
      ys: \<open>ys \<in> Collect (forward_subsumption_one_wl_select C cands S)\<close> and
      xs: \<open>xs \<in> Collect (forward_subsumption_one_select C cands' S')\<close> and
      xx': \<open>(x, x') \<in> ?loop xs\<close> and
      x: \<open>case x of (xs, s) \<Rightarrow> xs \<noteq> {#} \<and> s = NONE\<close> and
      x': \<open>case x' of (xs, s) \<Rightarrow> xs \<noteq> {#} \<and> s = NONE\<close> and
      \<open>forward_subsumption_one_wl_inv S C xs0 x\<close> and
      inv: \<open>forward_subsumption_one_inv C S' ys0 x'\<close> and
      st: \<open>x' = (x1, x2)\<close> \<open>x = (x1a, x2a)\<close> and
      C': \<open>(C', C'a) \<in> nat_rel\<close>
        \<open>C' \<in> {C'. C' \<in># x1a}\<close>
        \<open>C'a \<in> {C'. C' \<in># x1}\<close>
        \<open>\<not> C' \<notin># dom_m (get_clauses_wl S)\<close>
        \<open>\<not> C'a \<notin># dom_m (get_clauses_l S')\<close>
    for C C' C'a x x' x1 x2 x1a x2a xs ys ys0 xs0
  proof -
      obtain S'' where
        inv: \<open>forward_subsumption_one_inv C S' ys0 (x1a, x2a)\<close> and
        \<open>C \<noteq> 0\<close> and
        S'S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
        struct: \<open>twl_struct_invs S''\<close> and
        list_invs: \<open>twl_list_invs S'\<close> and
        C_dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
        using inv C' pre assms xx' unfolding forward_subsumption_one_wl_inv_def prod.simps
          forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def st
        by auto
      have \<open>length (get_clauses_wl S \<propto> C') \<le> length (get_clauses_wl S \<propto> C)\<close> and
        k_dom: \<open>C' \<in># dom_m (get_clauses_wl S)\<close>
        using xs_ys xx' xs C' SS' unfolding C' st forward_subsumption_one_select_def
        by (auto)
      moreover have \<open>distinct (get_clauses_wl S \<propto> C)\<close> \<open>distinct (get_clauses_wl S \<propto> C')\<close>
        \<open>\<not>tautology (mset (get_clauses_wl S \<propto> C))\<close>
        \<open>\<not>tautology (mset (get_clauses_wl S \<propto> C'))\<close>
        using  C' SS' S'S'' struct k_dom list_invs C_dom unfolding C' st twl_list_invs_def
        by (auto simp: subsume_or_strengthen_pre_def state_wl_l_def twl_struct_invs_def
          pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def ran_m_def add_mset_eq_add_mset
          split: subsumption.splits
          dest!: multi_member_split)
      ultimately show ?thesis
        using C_dom C' SS' unfolding subsume_clauses_match_pre_def
        by auto
  qed
  show ?thesis
    unfolding forward_subsumption_one_wl_def forward_subsumption_one_def
    apply (refine_vcg
      subsume_clauses_match[unfolded Down_id_eq])
    subgoal using assms unfolding forward_subsumption_one_wl_pre_def by fast
    subgoal using assms unfolding forward_subsumption_one_wl_select_def forward_subsumption_one_select_def
      by auto
    subgoal for ys xs x x'
        using assms unfolding forward_subsumption_one_wl_inv_def case_prod_beta by (cases x; cases x') fastforce
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    apply (rule subsume_clauses_match_pre; assumption?)
    subgoal using assms by auto
    subgoal by auto
    apply (rule subsume_or_strengthen_wl_subsume_or_strengthen)
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms unfolding forward_subsumption_one_inv_def subsume_or_strengthen_pre_def
      prod.simps
      apply - apply normalize_goal+ 
      by (simp add: try_to_subsume_def
        forward_subsumption_one_inv_def subsume_or_strengthen_pre_def split: subsumption.splits)
    subgoal unfolding forward_subsumption_one_wl_pre_def forward_subsumption_one_pre_def
      by normalize_goal+ auto
    subgoal using assms(3) SS' by (force simp: literals_are_\<L>\<^sub>i\<^sub>n'_def blits_in_\<L>\<^sub>i\<^sub>n'_def
      watched_by_alt_def)
    subgoal using SS' by auto
    subgoal by auto
    done
qed


definition try_to_forward_subsume_wl_pre :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>try_to_forward_subsume_wl_pre C cands S = (\<exists>T. (S,T)\<in>state_wl_l None \<and> try_to_forward_subsume_pre C cands T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> no_lost_clause_in_WL S)\<close>

definition try_to_forward_subsume_wl_inv :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl_inv S cands C = (\<lambda>(i,break, T).
  (\<exists>S' T'. (S,S')\<in>state_wl_l None \<and> (T,T')\<in>state_wl_l None \<and> no_lost_clause_in_WL S \<and>
  try_to_forward_subsume_inv S' cands C (i, break, T') \<and> get_watched_wl T = get_watched_wl S \<and>
  literals_are_\<L>\<^sub>i\<^sub>n' S)) \<close>

definition try_to_forward_subsume_wl :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>try_to_forward_subsume_wl C cands S = do {
  ASSERT (try_to_forward_subsume_wl_pre C cands S);
  n \<leftarrow> RES {_::nat. True};
  ebreak \<leftarrow> RES {_::bool. True};
  (_, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup> try_to_forward_subsume_wl_inv S cands C\<^esup>
    (\<lambda>(i, break, S). \<not>break \<and> i < n)
    (\<lambda>(i, break, S). do {
      (S, subs) \<leftarrow> forward_subsumption_one_wl C cands S;
      ebreak \<leftarrow> RES {_::bool. True};
      RETURN (i+1, subs \<or> ebreak, S)
    })
  (0, ebreak, S);
  RETURN S
  }
  \<close>

lemma cdcl_twl_inprocessing_l_dom_get_clauses_mono: \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow>
  set_mset (dom_m (get_clauses_l T)) \<subseteq> set_mset (dom_m (get_clauses_l S))\<close>
  by (cases rule: cdcl_twl_inprocessing_l.cases)
   (auto simp: cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
    cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps
    cdcl_twl_pure_remove_l.simps dest: in_diffD)

lemma rtranclp_cdcl_twl_inprocessing_l_dom_get_clauses_mono:
  \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<Longrightarrow>
  set_mset (dom_m (get_clauses_l T)) \<subseteq> set_mset (dom_m (get_clauses_l S))\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_twl_inprocessing_l_dom_get_clauses_mono)

lemma try_to_forward_subsume_wl_inv_no_lost_clause_in_WLD:
   assumes
    \<open>try_to_forward_subsume_wl_inv S cands C (i, break, T)\<close>
  shows \<open>no_lost_clause_in_WL T\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
proof -
  obtain S' T' where
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    TT': \<open>(T, T') \<in> state_wl_l None\<close> and
    lost: \<open>no_lost_clause_in_WL S\<close>
    \<open>try_to_forward_subsume_inv S' cands C (i, break, T')\<close> and
    S'T': \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S' T'\<close> and
    w: \<open>get_watched_wl T = get_watched_wl S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
    using assms unfolding try_to_forward_subsume_wl_inv_def prod.simps
      try_to_forward_subsume_inv_def
    by blast

  have \<open>set_mset (dom_m (get_clauses_wl T)) \<subseteq> set_mset (dom_m (get_clauses_wl S))\<close>
    using SS' TT' rtranclp_cdcl_twl_inprocessing_l_dom_get_clauses_mono[OF S'T'] by auto
  moreover have eq: \<open>set_mset (all_init_lits_of_l S') = set_mset (all_init_lits_of_l T')\<close>
   using S'T' rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l by blast
  ultimately show \<open>no_lost_clause_in_WL T\<close>
    using lost SS' TT' w unfolding no_lost_clause_in_WL_def
    by (auto simp: watched_by_alt_def)

  show \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
    using eq SS' TT' rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[OF S'T'] w lits
    unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def
    by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def)
qed

lemma try_to_forward_subsume_wl:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    \<open>no_lost_clause_in_WL S\<close> and
    \<open>(C,C')\<in>nat_rel\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> and
    \<open>(cands, cands') \<in>Id\<close>
  shows
   \<open>try_to_forward_subsume_wl C cands S \<le> \<Down>({(T, T').
    (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S})
    (try_to_forward_subsume C' cands' S')\<close>
proof -
  have CC': \<open>C' = C\<close>
    using assms by auto
  have [refine0]: \<open>(xs, ys) \<in> Id \<Longrightarrow> (ebreak, ebreak') \<in> Id \<Longrightarrow>
    ((xs, ebreak, S), (ys, ebreak', S')) \<in> Id \<times>\<^sub>r bool_rel \<times>\<^sub>r {(U,V). (U,V)\<in> state_wl_l None \<and> get_watched_wl U = get_watched_wl S}\<close> (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?loop\<close>) for xs ys :: \<open>nat\<close> and ebreak ebreak'
    using assms by auto
  show ?thesis
    unfolding try_to_forward_subsume_wl_def try_to_forward_subsume_def CC'
    apply (refine_vcg simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st
      forward_subsumption_one_wl)
    subgoal using assms unfolding try_to_forward_subsume_wl_pre_def by fast
    subgoal using assms by auto
    subgoal for xs xsa ebreak ebreak' x x'
      using assms unfolding try_to_forward_subsume_wl_inv_def case_prod_beta prod_rel_fst_snd_iff
      by (rule_tac x=S' in exI, rule_tac x=\<open>snd (snd x')\<close> in exI) (auto)
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest: try_to_forward_subsume_wl_inv_no_lost_clause_in_WLD)
    subgoal by (auto dest: try_to_forward_subsume_wl_inv_no_lost_clause_in_WLD)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition forward_subsumption_all_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_wl_pre S = 
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> forward_subsumption_all_pre T \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition forward_subsumption_all_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> nat multiset \<Rightarrow> nat multiset \<times> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_wl_inv = (\<lambda>S cands (xs, s).
  (\<exists>T s'. (S, T) \<in> state_wl_l None \<and> (s, s') \<in> state_wl_l None \<and> forward_subsumption_all_inv T (xs, s') \<and>
   no_lost_clause_in_WL S \<and> get_watched_wl s = get_watched_wl S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S))\<close>

definition forward_subsumption_wl_all_cands where
  \<open>forward_subsumption_wl_all_cands S xs \<longleftrightarrow> xs \<subseteq># dom_m (get_clauses_wl S) \<and>
  (\<forall>C\<in>#xs. (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L) \<and>
  length (get_clauses_wl S \<propto> C) > 2)\<close>

definition forward_subsumption_all_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>forward_subsumption_all_wl = (\<lambda>S. do {
  ASSERT (forward_subsumption_all_wl_pre S);
  xs \<leftarrow> SPEC (forward_subsumption_wl_all_cands S);
  (xs, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> forward_subsumption_all_wl_inv S xs \<^esup> (\<lambda>(xs, S). xs \<noteq> {#} \<and> get_conflict_wl S = None)
    (\<lambda>(xs, S). do {
       C \<leftarrow> SPEC (\<lambda>C. C \<in># xs);
       T \<leftarrow> try_to_forward_subsume_wl C xs S;
       ASSERT (\<forall>D\<in>#remove1_mset C xs. get_clauses_wl T \<propto> D = get_clauses_wl S \<propto> D);
       RETURN (remove1_mset C xs, T)
    })
    (xs, S);
  RETURN S
  }
)\<close>


definition forward_subsume_wl_needed :: \<open>'v twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>forward_subsume_wl_needed S = SPEC (\<lambda>_. True)\<close>

definition forward_subsume_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>forward_subsume_wl S = do {
    ASSERT (forward_subsumption_all_wl_pre S);
    b \<leftarrow> forward_subsume_wl_needed S;
    if b then forward_subsumption_all_wl S else RETURN S
}\<close>

lemma
  assumes \<open>forward_subsumption_all_wl_inv S cands (xs, T)\<close>
  shows
    forward_subsumption_all_wl_inv_no_lost_clause_in_WLD: \<open>no_lost_clause_in_WL T\<close> and
    forward_subsumption_all_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n'D: \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
proof -
  obtain S' T' where
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    TT': \<open>(T, T') \<in> state_wl_l None\<close> and
    lost: \<open>no_lost_clause_in_WL S\<close> and
    S'T': \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S' T'\<close> and
    w: \<open>get_watched_wl T = get_watched_wl S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
    using assms unfolding forward_subsumption_all_wl_inv_def prod.simps
      forward_subsumption_all_inv_def
    by blast

  have \<open>set_mset (dom_m (get_clauses_wl T)) \<subseteq> set_mset (dom_m (get_clauses_wl S))\<close>
    using SS' TT' rtranclp_cdcl_twl_inprocessing_l_dom_get_clauses_mono[OF S'T'] by auto
  moreover have eq: \<open>set_mset (all_init_lits_of_l S') = set_mset (all_init_lits_of_l T')\<close>
   using S'T' rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l by blast
  ultimately show \<open>no_lost_clause_in_WL T\<close>
    using lost SS' TT' w unfolding no_lost_clause_in_WL_def
    by (auto simp: watched_by_alt_def)
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close>
    using eq SS' TT' rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[OF S'T'] w lits
    unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def
    by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def)
qed

lemma forward_subsumption_all_wl_inv_alt_def:
  \<open>forward_subsumption_all_wl_inv = (\<lambda>S cands (xs, s).
  (\<exists>T s'. (S, T) \<in> state_wl_l None \<and> (s, s') \<in> state_wl_l None \<and> forward_subsumption_all_inv T (xs, s') \<and>
  no_lost_clause_in_WL S \<and> get_watched_wl s = get_watched_wl S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' s))\<close>
  using forward_subsumption_all_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n'D unfolding forward_subsumption_all_wl_inv_def
  by fast

lemma forward_subsumption_all_wl:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    lost: \<open>correct_watching'_leaking_bin S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows
   \<open>forward_subsumption_all_wl S \<le> \<Down>({(T, T').
    (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S \<and> no_lost_clause_in_WL T \<and> literals_are_\<L>\<^sub>i\<^sub>n' T})
    (forward_subsumption_all S')\<close>
proof -

  have lost: \<open>no_lost_clause_in_WL S\<close> if pre: \<open>forward_subsumption_all_pre S'\<close>
  proof -
    obtain S'' where
      S'S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs S''\<close> and
      \<open>twl_list_invs S'\<close>
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S'')\<close> and
      \<open>set (get_all_mark_of_propagated (get_trail_l S')) \<subseteq> {0}\<close> and
      \<open>clauses_to_update_l S' = {#}\<close> and
      \<open>count_decided (get_trail_l S') = 0\<close>
      using pre unfolding forward_subsumption_all_pre_def by fast
    have \<open>correct_watching'_nobin S\<close>
      using assms(2) by (cases S) (auto simp: correct_watching'_leaking_bin.simps
        correct_watching'_nobin.simps)
    then show ?thesis
      using correct_watching'_nobin_clauses_pointed_to0[OF assms(1) _ assms(3) S'S'' struct_invs]
      by fast
  qed
  then have [refine0]: \<open>(xs, ys) \<in> Id \<Longrightarrow> forward_subsumption_all_pre S' \<Longrightarrow> forward_subsumption_all_inv S' (ys, S') \<Longrightarrow>
    forward_subsumption_all_wl_inv S xs (xs, S)\<close> for xs ys :: \<open>nat multiset\<close>
    using assms unfolding forward_subsumption_all_wl_inv_def case_prod_beta prod_rel_fst_snd_iff
    by (rule_tac x=S' in exI, rule_tac x=\<open>S'\<close> in exI) auto
  then have [refine0]: \<open>(xs, ys) \<in> Id \<Longrightarrow>
    ((xs, S), (ys, S')) \<in> Id \<times>\<^sub>f {(U,V). (U,V)\<in> state_wl_l None \<and> get_watched_wl U = get_watched_wl S}\<close> (is \<open>_ \<Longrightarrow> _ \<in> ?loop\<close>) for xs ys :: \<open>nat multiset\<close>
    using assms by auto

  show ?thesis
    unfolding forward_subsumption_all_wl_def forward_subsumption_all_def
    apply (refine_vcg simplify_clause_with_unit_st_wl_simplify_clause_with_unit_st
      forward_subsumption_one_wl try_to_forward_subsume_wl WHILEIT_refine_with_all_loopinvariants)
    subgoal using assms unfolding forward_subsumption_all_wl_pre_def by fast
    subgoal using assms unfolding forward_subsumption_all_cands_def forward_subsumption_wl_all_cands_def by auto
    subgoal for xs xsa x x'
      using assms lost unfolding forward_subsumption_all_wl_inv_def case_prod_beta prod_rel_fst_snd_iff
      by (rule_tac x=S' in exI, rule_tac x=\<open>snd x'\<close> in exI; auto)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest: forward_subsumption_all_wl_inv_no_lost_clause_in_WLD
      forward_subsumption_all_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n'D)
    subgoal by (auto dest: forward_subsumption_all_wl_inv_no_lost_clause_in_WLD
      forward_subsumption_all_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n'D)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest: forward_subsumption_all_wl_inv_no_lost_clause_in_WLD
      forward_subsumption_all_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n'D)
    done
qed

lemma forward_subsume_wl:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    lost: \<open>correct_watching'_leaking_bin S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows
   \<open>forward_subsume_wl S \<le> \<Down>({(T, T').
    (T, T') \<in> state_wl_l None \<and> get_watched_wl T = get_watched_wl S \<and> no_lost_clause_in_WL T \<and> literals_are_\<L>\<^sub>i\<^sub>n' T})
    (forward_subsume_l S')\<close>
proof -
  have lost: \<open>no_lost_clause_in_WL S\<close> if pre: \<open>forward_subsumption_all_pre S'\<close>
  proof -
    obtain S'' where
      S'S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs S''\<close> and
      \<open>twl_list_invs S'\<close>
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S'')\<close> and
      \<open>set (get_all_mark_of_propagated (get_trail_l S')) \<subseteq> {0}\<close> and
      \<open>clauses_to_update_l S' = {#}\<close> and
      \<open>count_decided (get_trail_l S') = 0\<close>
      using pre unfolding forward_subsumption_all_pre_def by fast
    have \<open>correct_watching'_nobin S\<close>
      using assms(2) by (cases S) (auto simp: correct_watching'_leaking_bin.simps
        correct_watching'_nobin.simps)
    then show ?thesis
      using correct_watching'_nobin_clauses_pointed_to0[OF assms(1) _ assms(3) S'S'' struct_invs]
      by fast
  qed
  show ?thesis
    unfolding forward_subsume_wl_def forward_subsume_l_def
      forward_subsumption_needed_l_def forward_subsume_wl_needed_def
    apply (refine_vcg forward_subsumption_all_wl)
    subgoal using assms unfolding forward_subsumption_all_wl_pre_def by fast
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms lost by simp
    done
qed

lemma cdcl_twl_inprocessing_l_dom_get_clauses_l_mono:
  \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> dom_m (get_clauses_l T) \<subseteq># dom_m (get_clauses_l S)\<close>
  by (auto simp: cdcl_twl_inprocessing_l.simps cdcl_twl_unitres_true_l.simps cdcl_twl_unitres_l.simps
    cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps add_mset_eq_add_mset
    cdcl_twl_pure_remove_l.simps
    dest!: multi_member_split)

lemma rtranclp_cdcl_twl_inprocessing_l_dom_get_clauses_l_mono:
  \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<Longrightarrow> dom_m (get_clauses_l T) \<subseteq># dom_m (get_clauses_l S)\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_twl_inprocessing_l_dom_get_clauses_l_mono)


subsection \<open>Pure literal deletion\<close>

definition propagate_pure_wl_pre:: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>propagate_pure_wl_pre L S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> propagate_pure_l_pre L S' \<and> no_lost_clause_in_WL S \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>


definition propagate_pure_bt_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>propagate_pure_bt_wl = (\<lambda>L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS). do {
    ASSERT(propagate_pure_wl_pre L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS));
    M \<leftarrow> cons_trail_propagate_l L 0 M;
    RETURN (M, N, D, NE, UE, add_mset {#L#} NEk, UEk, NS, US, N0, U0, add_mset (-L) Q, WS)})\<close>

lemma propagate_pure_bt_wl_propagate_pure_bt_l:
  assumes \<open>(S,S')\<in> state_wl_l None\<close> and \<open>no_lost_clause_in_WL S\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> \<open>(L,L')\<in> Id\<close>
  shows
    \<open>propagate_pure_bt_wl L S \<le>\<Down>{(S,T). no_lost_clause_in_WL S \<and> (S,T)\<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} (propagate_pure_bt_l L' S')\<close>
proof -
  have K: \<open>cons_trail_propagate_l L 0 a = cons_trail_propagate_l L 0 b \<Longrightarrow>
    cons_trail_propagate_l L 0 a \<le>\<Down>{(x,y). x = y \<and> y = Propagated L 0 # a} (cons_trail_propagate_l L' 0 b)\<close> for a b
    using assms unfolding cons_trail_propagate_l_def
    by refine_rcg auto
  show ?thesis
    unfolding propagate_pure_bt_wl_def propagate_pure_bt_l_def
    apply refine_rcg
    subgoal using assms unfolding propagate_pure_wl_pre_def apply - by (rule exI[of _ S']) fast
    apply (rule K)
    subgoal using assms by (auto simp: state_wl_l_def no_lost_clause_in_WL_def)
    subgoal
      using assms
      by (auto simp: state_wl_l_def propagate_pure_l_pre_def in_all_lits_of_mm_uminusD
        all_init_lits_of_wl_def all_init_lits_of_l_def get_init_clss_l_def
        simp: no_lost_clause_in_WL_def
        simp: literals_are_\<L>\<^sub>i\<^sub>n'_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
          all_learned_lits_of_wl_def blits_in_\<L>\<^sub>i\<^sub>n'_def)
    done
qed

definition pure_literal_deletion_wl_pre where
  \<open>pure_literal_deletion_wl_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> state_wl_l None \<and> pure_literal_deletion_pre S' \<and>
    no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>

definition pure_literal_deletion_candidates_wl where
  \<open>pure_literal_deletion_candidates_wl S = SPEC (\<lambda>Ls. set_mset Ls \<subseteq> set_mset (all_init_atms_st S))\<close>

definition pure_literal_deletion_wl_inv where
  \<open>pure_literal_deletion_wl_inv S xs0 = (\<lambda>(T, xs).
  \<exists>S' T'. (S, S') \<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and> pure_literal_deletion_l_inv S' xs0 (T', xs) \<and>
    no_lost_clause_in_WL T \<and> literals_are_\<L>\<^sub>i\<^sub>n' T)\<close>

definition pure_literal_deletion_wl :: \<open>('v literal \<Rightarrow> bool) \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>pure_literal_deletion_wl occs S = do {
    ASSERT (pure_literal_deletion_wl_pre S);
    let As =  \<Union>(set_mset ` set_mset (mset `# get_init_clss_wl S));
    xs \<leftarrow> pure_literal_deletion_candidates_wl S;
    (S, xs) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_deletion_wl_inv S xs\<^esup> (\<lambda>(S, xs). xs \<noteq> {#})
      (\<lambda>(S, xs). do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># xs);
        let A = (if occs (Pos L) \<and> \<not>occs (Neg L) then Pos L else Neg L);
        if \<not>occs (-A) \<and> undefined_lit (get_trail_wl S) A
        then do {S \<leftarrow> propagate_pure_bt_wl A S;
          RETURN (S, remove1_mset L xs)}
        else RETURN (S, remove1_mset L xs)
      })
    (S, xs);
  RETURN S
  }\<close>

lemma pure_literal_deletion_wl_pure_literal_deletion_l:
  assumes \<open>(S,S')\<in> state_wl_l None\<close> and \<open>no_lost_clause_in_WL S\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close> \<open>(occs, occs') \<in> Id\<close>
  shows
    \<open>pure_literal_deletion_wl occs S \<le>\<Down>{(S,T). no_lost_clause_in_WL S \<and> (S,T)\<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} (pure_literal_deletion_l2 occs' S')\<close> (is \<open>_ \<le>\<Down> ?A _\<close>)
proof -
  have [refine0]: \<open>(xs, ys) \<in> Id \<Longrightarrow> ((S, xs), (S', ys)) \<in> ?A \<times>\<^sub>f Id\<close> for xs ys
    by (use assms in auto)
  have [refine0]: \<open>pure_literal_deletion_candidates_wl S \<le> \<Down> Id (pure_literal_deletion_candidates S')\<close>
    using assms by (auto simp: pure_literal_deletion_candidates_wl_def pure_literal_deletion_candidates_def
      all_init_atms_st_def all_init_atms_alt_def)
  show ?thesis
    unfolding pure_literal_deletion_wl_def pure_literal_deletion_l2_def
    apply (refine_rcg propagate_pure_bt_wl_propagate_pure_bt_l)
    subgoal using assms unfolding pure_literal_deletion_wl_pre_def by blast
    subgoal for xs xsa x x'
      using assms unfolding pure_literal_deletion_wl_inv_def case_prod_beta
      by (rule_tac x=S' in exI, rule_tac x=\<open>fst x'\<close> in exI, case_tac x, case_tac x') auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (subst twl_st_wl, use assms in auto)
    subgoal by auto
    subgoal unfolding pure_literal_deletion_wl_inv_def by blast
    subgoal by simp
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition pure_literal_count_occs_clause_wl_invs :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v literal \<Rightarrow> bool) \<Rightarrow> nat \<times> ('v literal \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>pure_literal_count_occs_clause_wl_invs C S occs = (\<lambda>(i, occs2).
  \<exists>S'. (S,S')\<in>state_wl_l None \<and> pure_literal_count_occs_l_clause_invs C S' occs (i, occs2))\<close>

definition pure_literal_count_occs_clause_wl_pre :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>pure_literal_count_occs_clause_wl_pre C S occs =
    (\<exists>S'. (S,S')\<in>state_wl_l None \<and> pure_literal_count_occs_l_clause_pre C S' occs)\<close>

definition pure_literal_count_occs_clause_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> _\<close> where
  \<open>pure_literal_count_occs_clause_wl C S occs = do {
    ASSERT (pure_literal_count_occs_clause_wl_pre C S occs);
    (i, occs) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_count_occs_clause_wl_invs C S occs\<^esup> (\<lambda>(i, occs). i < length (get_clauses_wl S \<propto> C))
      (\<lambda>(i, occs). do {
        let L = get_clauses_wl S \<propto> C ! i;
        let occs = occs (L := True);
        RETURN (i+1, occs)
      })
      (0, occs);
   RETURN occs
 }\<close>

lemma pure_literal_count_occs_clause_wl_pure_literal_count_occs_l_clause:
  assumes \<open>(S, S') \<in> state_wl_l None\<close> \<open>(C,C')\<in>nat_rel\<close> \<open>(occs, occs') \<in> Id\<close>
  shows \<open>pure_literal_count_occs_clause_wl C S occs \<le> \<Down>Id (pure_literal_count_occs_l_clause C' S' occs')\<close>
proof -
  have [refine0]: \<open>((0, occs), 0, occs') \<in> nat_rel \<times>\<^sub>f Id\<close>
    using assms by auto
  show ?thesis
    unfolding pure_literal_count_occs_clause_wl_def pure_literal_count_occs_l_clause_def
    apply (refine_vcg)
    subgoal using assms unfolding pure_literal_count_occs_clause_wl_pre_def by fast
    subgoal using assms unfolding pure_literal_count_occs_clause_wl_invs_def case_prod_beta prod.collapse
      by fastforce
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    done
qed

definition pure_literal_count_occs_wl_pre :: \<open>_\<close> where
  \<open>pure_literal_count_occs_wl_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> 
    no_lost_clause_in_WL S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S \<and> pure_literal_count_occs_l_pre S')\<close>

definition pure_literal_count_occs_wl_inv :: \<open>_\<close> where
  \<open>pure_literal_count_occs_wl_inv S T \<longleftrightarrow>
    (\<exists>S' T'. (S,S')\<in> state_wl_l None \<and> (T, T') \<in> state_wl_l None \<and> cdcl_twl_inprocessing_l S' T')\<close>

definition pure_literal_count_occs_wl :: \<open>'v twl_st_wl \<Rightarrow> _\<close> where
  \<open>pure_literal_count_occs_wl S = do {
  ASSERT (pure_literal_count_occs_wl_pre S);
  xs \<leftarrow> SPEC (\<lambda>xs. distinct_mset xs \<and> (\<forall>C\<in>#dom_m (get_clauses_wl S). irred (get_clauses_wl S) C \<longrightarrow> C \<in># xs));
  abort \<leftarrow> RES (UNIV :: bool set);
  let occs = (\<lambda>_. False);
  (_, occs, abort) \<leftarrow> WHILE\<^sub>T(\<lambda>(A, occs, abort). A \<noteq> {#} \<and> \<not>abort)
      (\<lambda>(A, occs, abort). do {
        ASSERT (A \<noteq> {#});
        C \<leftarrow> SPEC (\<lambda>C. C \<in># A);
        if (C \<in># dom_m (get_clauses_wl S) \<and> irred (get_clauses_wl S) C) then do {
          occs \<leftarrow> pure_literal_count_occs_clause_wl C S occs;
          abort \<leftarrow> RES (UNIV :: bool set);
          RETURN (remove1_mset C A, occs, abort)
        } else RETURN  (remove1_mset C A, occs, abort)
      })
      (xs, occs, abort);
   RETURN (abort, occs)
  }\<close>

lemma pure_literal_count_occs_wl_pure_literal_count_occs_l:
  assumes
    \<open>(S, S') \<in> state_wl_l None\<close>
    \<open>no_lost_clause_in_WL S\<close>
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows \<open>pure_literal_count_occs_wl S \<le> \<Down>Id (pure_literal_count_occs_l S')\<close>
proof -
  have [refine0]: \<open>(xs, xsa)\<in> Id \<Longrightarrow> (abort, abort') \<in> bool_rel \<Longrightarrow>
    ((xs, \<lambda>_. False, abort), xsa, \<lambda>_. False, abort') \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r bool_rel\<close> for xs xsa abort abort'
    by auto
  show ?thesis
    unfolding pure_literal_count_occs_wl_def pure_literal_count_occs_l_def
    apply (refine_vcg pure_literal_count_occs_clause_wl_pure_literal_count_occs_l_clause)
    subgoal using assms unfolding pure_literal_count_occs_wl_pre_def by fast
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition pure_literal_elimination_round_wl_pre where
  \<open>pure_literal_elimination_round_wl_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> pure_literal_elimination_round_pre T)\<close>

definition pure_literal_elimination_round_wl where
  \<open>pure_literal_elimination_round_wl S = do {
    ASSERT (pure_literal_elimination_round_wl_pre S);
    S \<leftarrow> simplify_clauses_with_units_st_wl S;
    if get_conflict_wl S = None
    then do {
     (abort, occs) \<leftarrow> pure_literal_count_occs_wl S;
      if \<not>abort then pure_literal_deletion_wl occs S
      else RETURN S}
    else RETURN S
}\<close>

lemma pure_literal_elimination_round_wl_pure_literal_elimination_round_l:
  assumes
    \<open>(S, S') \<in> state_wl_l None\<close>
    \<open>no_lost_clause_in_WL S\<close>
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows \<open>pure_literal_elimination_round_wl S \<le>
    \<Down>{(S,T). no_lost_clause_in_WL S \<and> (S,T)\<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} (pure_literal_elimination_round S')\<close>
proof -
  show ?thesis
    unfolding pure_literal_elimination_round_wl_def pure_literal_elimination_round_def
    apply (refine_vcg
      simplify_clauses_with_units_st_wl_simplify_clause_with_units_st2
      pure_literal_count_occs_wl_pure_literal_count_occs_l
      pure_literal_deletion_wl_pure_literal_deletion_l)
    subgoal using assms unfolding pure_literal_elimination_round_wl_pre_def by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal by auto
    subgoal by auto
    subgoal by blast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by blast
    subgoal by auto
    subgoal by auto
    subgoal by blast
    subgoal by blast
    done
qed



definition pure_literal_elimination_wl_pre where
  \<open>pure_literal_elimination_wl_pre S \<longleftrightarrow>
  (\<exists>T. (S, T) \<in> state_wl_l None \<and> pure_literal_elimination_l_pre T \<and> no_lost_clause_in_WL S \<and>
  literals_are_\<L>\<^sub>i\<^sub>n' S)\<close>


definition pure_literal_elimination_wl_inv where
  \<open>pure_literal_elimination_wl_inv S max_rounds =
  (\<lambda>(U,m,abort). \<exists>T U'. (S, T) \<in> state_wl_l None \<and> (U, U') \<in> state_wl_l None \<and>
  no_lost_clause_in_WL U \<and> literals_are_\<L>\<^sub>i\<^sub>n' U \<and> pure_literal_elimination_l_inv T max_rounds (U',m,abort))\<close>

definition pure_literal_elimination_wl :: \<open>_\<close> where
  \<open>pure_literal_elimination_wl S = do {
     ASSERT (pure_literal_elimination_wl_pre S);
     max_rounds \<leftarrow> RES (UNIV :: nat set);
    (S, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_elimination_wl_inv S max_rounds\<^esup> (\<lambda>(S, m, abort). m < max_rounds \<and> \<not>abort)
     (\<lambda>(S, m, abort). do {
         S \<leftarrow> pure_literal_elimination_round_wl S;
         abort \<leftarrow> RES (UNIV :: bool set);
         RETURN (S, m+1, abort)
       })
    (S, 0, False);
   RETURN S
  }\<close>


lemma pure_literal_elimination_wl:
  assumes
    \<open>(S, S') \<in> state_wl_l None\<close>
    \<open>no_lost_clause_in_WL S\<close>
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows \<open>pure_literal_elimination_wl S \<le>
    \<Down>{(S,T). no_lost_clause_in_WL S \<and> (S,T)\<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} (pure_literal_elimination_l S')\<close>
proof -
  have [refine0]: \<open>pure_literal_elimination_l_pre S' \<Longrightarrow>
    ((S, 0, False), S', 0, False) \<in> {(S,T). no_lost_clause_in_WL S \<and> (S,T)\<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<times>\<^sub>r nat_rel \<times>\<^sub>r bool_rel\<close>
     using assms by auto
  show ?thesis
    unfolding pure_literal_elimination_wl_def pure_literal_elimination_l_def
    apply (refine_vcg pure_literal_elimination_round_wl_pure_literal_elimination_round_l)
    subgoal using assms unfolding pure_literal_elimination_wl_pre_def by blast
    subgoal for max_rounds max_roundsa x x'
      using assms unfolding pure_literal_elimination_wl_inv_def case_prod_beta prod_rel_fst_snd_iff
      apply -
      by (rule exI[of _ S'], rule exI[of _ \<open>fst x'\<close>]) auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition pure_literal_eliminate_wl_needed :: \<open>_\<close> where
  \<open>pure_literal_eliminate_wl_needed S = SPEC (\<lambda>_. True)\<close>

definition pure_literal_eliminate_wl :: \<open>_\<close> where
  \<open>pure_literal_eliminate_wl S = do {
     ASSERT (pure_literal_elimination_wl_pre S);
    b \<leftarrow> pure_literal_eliminate_wl_needed S;
   if b then pure_literal_elimination_wl S else RETURN S
}\<close>



lemma pure_literal_eliminate_wl:
  assumes
    \<open>(S, S') \<in> state_wl_l None\<close>
    \<open>no_lost_clause_in_WL S\<close>
    \<open>literals_are_\<L>\<^sub>i\<^sub>n' S\<close>
  shows \<open>pure_literal_eliminate_wl S \<le>
    \<Down>{(S,T). no_lost_clause_in_WL S \<and> (S,T)\<in> state_wl_l None \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} (pure_literal_eliminate_l S')\<close>
  unfolding pure_literal_eliminate_wl_def pure_literal_eliminate_l_def
    pure_literal_eliminate_wl_needed_def pure_literal_elimination_l_needed_def
  apply (refine_vcg pure_literal_elimination_wl)
  subgoal using assms unfolding pure_literal_elimination_wl_pre_def by blast
  subgoal by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  done

end
