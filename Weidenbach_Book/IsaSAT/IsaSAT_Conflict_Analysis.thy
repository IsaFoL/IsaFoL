theory IsaSAT_Conflict_Analysis
  imports IsaSAT_Conflict_Analysis_Defs
begin

(*TODO Move*)
lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_all_atms_self[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms ca NUE) {#mset (fst x). x \<in># ran_m ca#}\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
    all_atms_def all_lits_def in_all_lits_of_mm_ain_atms_of_iff)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_ran_m[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm  (all_atms_st (x1a, x1b, y))
      {#mset (fst x). x \<in># ran_m x1b#}\<close>
  by (cases y; auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_lits_st_def all_lits_def all_lits_of_mm_union
    simp flip: all_lits_st_alt_def)
(*END Move*)

paragraph \<open>Skip and resolve\<close>

definition maximum_level_removed_eq_count_dec where
  \<open>maximum_level_removed_eq_count_dec L S \<longleftrightarrow>
      get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L =
       count_decided (get_trail_wl S)\<close>

definition maximum_level_removed_eq_count_dec_pre where
  \<open>maximum_level_removed_eq_count_dec_pre =
     (\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> count_decided (get_trail_wl S) \<ge> 1)\<close>


lemma maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec:
  \<open>(uncurry maximum_level_removed_eq_count_dec_heur,
      uncurry mop_maximum_level_removed_wl) \<in>
   [\<lambda>_. True]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur_conflict_ana \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def mop_maximum_level_removed_wl_def
    uncurry_def
  apply (intro frefI nres_relI)
  subgoal for x y
    apply refine_rcg
    apply (cases x)
    apply (auto simp: count_decided_st_def counts_maximum_level_def twl_st_heur_conflict_ana_def
      maximum_level_removed_eq_count_dec_heur_def maximum_level_removed_eq_count_dec_def
      maximum_level_removed_eq_count_dec_pre_def mop_maximum_level_removed_wl_pre_def
     mop_maximum_level_removed_l_pre_def mop_maximum_level_removed_pre_def state_wl_l_def
     twl_st_l_def get_maximum_level_card_max_lvl_ge1 card_max_lvl_remove_hd_trail_iff)
    done
  done


lemma lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
   \<open>(lit_and_ann_of_propagated_st_heur, mop_hd_trail_wl) \<in>
   [\<lambda>S. True]\<^sub>f twl_st_heur_conflict_ana \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lit_and_ann_of_propagated_st_heur_def mop_hd_trail_wl_def
  apply refine_rcg
  apply (case_tac \<open>get_trail_wl_heur x\<close>)
  apply (auto simp: twl_st_heur_conflict_ana_def mop_hd_trail_wl_def mop_hd_trail_wl_pre_def
     mop_hd_trail_l_pre_def twl_st_l_def state_wl_l_def mop_hd_trail_pre_def last_rev hd_map
      lit_and_ann_of_propagated_st_def trail_pol_alt_def ann_lits_split_reasons_def
    intro!: ASSERT_leI ASSERT_refine_right simp flip: rev_map elim: is_propedE)
  apply (auto elim!: is_propedE)
  done

definition tl_state_wl_pre where
  \<open>tl_state_wl_pre S \<longleftrightarrow> get_trail_wl S \<noteq> [] \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) (get_trail_wl S) \<and>
     (lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
     -(lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
    \<not>tautology (the (get_conflict_wl S)) \<and>
    distinct_mset (the (get_conflict_wl S)) \<and>
    \<not>is_decided (hd (get_trail_wl S)) \<and>
    count_decided (get_trail_wl S) > 0\<close>

lemma tl_state_out_learned:
   \<open>lit_of (hd a) \<notin># the at' \<Longrightarrow>
       - lit_of (hd a) \<notin># the at' \<Longrightarrow>
       \<not> is_decided (hd a) \<Longrightarrow>
       out_learned (tl a) at' an \<longleftrightarrow> out_learned a at' an\<close>
  by (cases a)  (auto simp: out_learned_def get_level_cons_if atm_of_eq_atm_of
      intro!: filter_mset_cong)

lemma mop_tl_state_wl_pre_tl_state_wl_heur_pre:
  \<open>(x, y) \<in> twl_st_heur_conflict_ana \<Longrightarrow> mop_tl_state_wl_pre y \<Longrightarrow> tl_state_wl_heur_pre x\<close>
  \<open>(x, y) \<in> twl_st_heur_conflict_ana \<Longrightarrow> mop_tl_state_wl_pre y \<Longrightarrow>
    isa_bump_unset_pre (atm_of (lit_of_last_trail_pol (get_trail_wl_heur x)))
  (get_vmtf_heur x)
\<close>
  using tl_trailt_tr_pre[of \<open>get_trail_wl y\<close> \<open>get_trail_wl_heur x\<close> \<open>all_atms_st y\<close>]
  subgoal
    unfolding mop_tl_state_wl_pre_def tl_state_wl_heur_pre_def mop_tl_state_l_pre_def
      mop_tl_state_pre_def tl_state_wl_heur_pre_def
    by (cases \<open>get_trail_wl_heur x\<close>; cases y)
      (clarsimp_all simp: twl_st_heur_conflict_ana_def state_wl_l_def twl_st_l_def trail_pol_alt_def
      rev_map[symmetric] last_rev hd_map simp flip: all_lits_st_alt_def
    intro!: isa_bump_unset_pre[where M = \<open>get_trail_wl y\<close>])
  subgoal
    unfolding mop_tl_state_wl_pre_def tl_state_wl_heur_pre_def mop_tl_state_l_pre_def
      mop_tl_state_pre_def tl_state_wl_heur_pre_def
    apply normalize_goal+
    apply (cases \<open>get_trail_wl y\<close>)
    apply (solves simp)
    apply (rule isa_bump_unset_pre[of _ \<open>all_atms_st y\<close> \<open>get_trail_wl y\<close>])
    apply (simp add: twl_st_heur_conflict_ana_def)
    apply (simp add: twl_st_heur_conflict_ana_def lit_of_last_trail_pol_def)
    apply (clarsimp_all simp: twl_st_heur_conflict_ana_def state_wl_l_def twl_st_l_def trail_pol_alt_def
      rev_map[symmetric] last_rev hd_map lit_of_last_trail_pol_def
      simp flip: all_lits_st_alt_def IsaSAT_Setup.all_lits_st_alt_def
    intro!: isa_bump_unset_pre[where M = \<open>get_trail_wl y\<close>])
    using IsaSAT_Setup.all_lits_st_alt_def by blast
  done

lemma mop_tl_state_wl_pre_simps:
  \<open>mop_tl_state_wl_pre ([], ax, ay, az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<longleftrightarrow> False\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow>
     lit_of (hd xa) \<in># all_lits_st (xa', ax, ay'', az, bga, NEk, UEk, NS, US, N0, U0, bh'', bi'')\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow> lit_of (hd xa) \<notin># the ay\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow> -lit_of (hd xa) \<notin># the ay\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, Some ay', az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow> lit_of (hd xa) \<notin># ay'\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, Some ay', az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow> -lit_of (hd xa) \<notin># ay'\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow> is_proped (hd xa)\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NEk, UEk, NS, US, N0, U0, bh, bi) \<Longrightarrow> count_decided xa > 0\<close>
  unfolding mop_tl_state_wl_pre_def tl_state_wl_heur_pre_def mop_tl_state_l_pre_def
    mop_tl_state_pre_def tl_state_wl_heur_pre_def
  apply (auto simp: twl_st_heur_conflict_ana_def state_wl_l_def twl_st_l_def trail_pol_alt_def
      rev_map[symmetric] last_rev hd_map mset_take_mset_drop_mset' \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits
    simp flip: image_mset_union all_lits_def all_lits_st_alt_def; fail)[]
  apply (normalize_goal+; simp add: all_lits_st_def; fail)+
  done

lemma all_atms_st_st_simps2[simp]:
  \<open>all_atms_st (tl xaa, bu, bv, bw, bx, by, NEk, UEk, bz, ca, cb, cc, cd) =
  all_atms_st (xaa, bu, bv, bw, bx, by, NEk, UEk, bz, ca, cb, cc, cd)\<close>
  \<open>all_atms_st (xaa, bu, Some (bv' \<union># tt - uu), bw, bx, by, NEk, UEk, bz, ca, cb, cc, cd) =
  all_atms_st (xaa, bu, Some bv', bw, bx, by, NEk, UEk, bz, ca, cb, cc, cd)\<close>
  by (auto simp: all_atms_st_def)

declare isasat_input_bounded_def[simp del]
lemma tl_state_wl_heur_tl_state_wl:
   \<open>(tl_state_wl_heur, mop_tl_state_wl) \<in>
  [\<lambda>_. True]\<^sub>f twl_st_heur_conflict_ana' r lcount \<rightarrow>
    \<langle>bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r lcount\<rangle>nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding tl_state_wl_heur_def mop_tl_state_wl_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  subgoal for x y
    using mop_tl_state_wl_pre_tl_state_wl_heur_pre[of x y] by simp
  subgoal for x y
    using mop_tl_state_wl_pre_tl_state_wl_heur_pre[of x y] by simp
  subgoal for x y
    apply (cases y)
    apply (auto simp: twl_st_heur_conflict_ana_def tl_state_wl_heur_def tl_state_wl_def vmtf_unset_vmtf_tl
         mop_tl_state_wl_pre_simps lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id]
         card_max_lvl_tl tl_state_out_learned
      dest: no_dup_tlD simp flip: all_lits_st_alt_def
      intro!: tl_trail_tr[THEN fref_to_Down_unRET] isa_bump_unset_vmtf_tl)
  apply (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id])
  apply (auto simp: mop_tl_state_wl_pre_simps lit_of_hd_trail_def mop_tl_state_wl_pre_simps counts_maximum_level_def
    intro!: isa_bump_unset_vmtf_tl[THEN order_trans] IsaSAT_Trail.tl_trail_tr[THEN fref_to_Down_unRET]
    intro: no_dup_tlD)
  apply (metis (no_types, lifting) IsaSAT_Setup.all_lits_st_alt_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff mop_tl_state_wl_pre_simps(2))
  apply (metis (no_types, lifting) IsaSAT_Setup.all_lits_st_alt_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff mop_tl_state_wl_pre_simps(2))
  apply (rule no_dup_tlD, assumption)
  apply (subst card_max_lvl_tl)
    apply (auto simp: mop_tl_state_wl_pre_simps lookup_clause_rel_not_tautolgy lookup_clause_rel_distinct_mset
      option_lookup_clause_rel_def)
  apply (subst tl_state_out_learned)
    apply (auto simp: mop_tl_state_wl_pre_simps lookup_clause_rel_not_tautolgy lookup_clause_rel_distinct_mset
      option_lookup_clause_rel_def)
  apply (subst tl_state_out_learned)
    apply (auto simp: mop_tl_state_wl_pre_simps lookup_clause_rel_not_tautolgy lookup_clause_rel_distinct_mset
      option_lookup_clause_rel_def)
  done
  done

lemma arena_act_pre_mark_used:
  \<open>arena_act_pre arena C \<Longrightarrow>
  arena_act_pre (mark_used arena C) C\<close>
  unfolding arena_act_pre_def arena_is_valid_clause_idx_def
  apply clarify
  apply (rule_tac x=N in exI)
  apply (rule_tac x=vdom in exI)
  by (auto simp: arena_act_pre_def
    simp: valid_arena_mark_used)


definition (in -) get_max_lvl_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>get_max_lvl_st S L = get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L\<close>

lemma card_max_lvl_remove1_mset_hd:
  \<open>-lit_of (hd M) \<in># y \<Longrightarrow> is_proped (hd M) \<Longrightarrow>
     card_max_lvl M (remove1_mset (-lit_of (hd M)) y) = card_max_lvl M y - 1\<close>
  by (cases M) (auto dest!: multi_member_split simp: card_max_lvl_add_mset)

lemma update_confl_tl_wl_heur_state_helper:
   \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<Longrightarrow> get_trail_wl S \<noteq> [] \<Longrightarrow>
    is_proped (hd (get_trail_wl S)) \<Longrightarrow> L = lit_of (hd (get_trail_wl S))\<close>
  by (cases S; cases \<open>hd (get_trail_wl S)\<close>) auto

lemma (in -) not_ge_Suc0: \<open>\<not>Suc 0 \<le> n \<longleftrightarrow> n = 0\<close> (* WTF *)
  by auto

definition update_confl_tl_wl_pre' :: \<open>((nat literal \<times> nat) \<times> nat twl_st_wl) \<Rightarrow> bool\<close> where
  \<open>update_confl_tl_wl_pre' = (\<lambda>((L, C), S).
      C \<in># dom_m (get_clauses_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and>
      - L \<in># the (get_conflict_wl S) \<and>
      L \<notin># the (get_conflict_wl S) \<and>
      (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and>
      L \<in># all_lits_st S \<and>
      is_proped (hd (get_trail_wl S)) \<and>
      C > 0 \<and>
      card_max_lvl (get_trail_wl S) (the (get_conflict_wl S)) \<ge> 1 \<and>
      distinct_mset (the (get_conflict_wl S)) \<and>
      - L \<notin> set (get_clauses_wl S \<propto> C) \<and>
      (length (get_clauses_wl S \<propto> C) \<noteq> 2 \<longrightarrow>
        L \<notin> set (tl (get_clauses_wl S \<propto> C)) \<and>
        get_clauses_wl S \<propto> C ! 0 = L \<and>
        mset (tl (get_clauses_wl S \<propto> C)) = remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<and>
        (\<forall>L\<in>set (tl(get_clauses_wl S \<propto> C)). - L \<notin># the (get_conflict_wl S)) \<and>
        card_max_lvl (get_trail_wl S) (mset (tl (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) =
          card_max_lvl (get_trail_wl S) (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S))) \<and>
      L \<in> set (watched_l (get_clauses_wl S \<propto> C)) \<and>
      distinct (get_clauses_wl S \<propto> C) \<and>
      \<not>tautology (the (get_conflict_wl S)) \<and>
      \<not>tautology (mset (get_clauses_wl S \<propto> C)) \<and>
      \<not>tautology (remove1_mset L (remove1_mset (- L)
        ((the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C))))) \<and>
      count_decided (get_trail_wl S) > 0 \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (the (get_conflict_wl S)) \<and>
      literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) (get_trail_wl S) \<and>
      (\<forall>K. K \<in># remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<longrightarrow> - K \<notin># the (get_conflict_wl S)) \<and>
      size (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) > 0 \<and>
      Suc 0 \<le> card_max_lvl (get_trail_wl S) (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) \<and>
      size (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) =
       size (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#}) + Suc 0 \<and>
      lit_of (hd (get_trail_wl S)) = L \<and>
       card_max_lvl (get_trail_wl S) ((mset (get_clauses_wl S \<propto> C) - unmark (hd (get_trail_wl S))) \<union># the (get_conflict_wl S))  =
        card_max_lvl (tl (get_trail_wl S)) (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#}) + Suc 0 \<and>
     out_learned (tl (get_trail_wl S)) (Some (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#})) =
        out_learned (get_trail_wl S) (Some ((mset (get_clauses_wl S \<propto> C) - unmark (hd (get_trail_wl S))) \<union># the (get_conflict_wl S)))
    )\<close>

lemma remove1_mset_union_distrib1:
     \<open>L \<notin># B \<Longrightarrow> remove1_mset L (A \<union># B) = remove1_mset L A \<union># B\<close> and
  remove1_mset_union_distrib2:
     \<open>L \<notin># A \<Longrightarrow> remove1_mset L (A \<union># B) = A \<union># remove1_mset L B\<close>
  by (auto simp: remove1_mset_union_distrib)


lemma update_confl_tl_wl_pre_update_confl_tl_wl_pre':
   assumes \<open>update_confl_tl_wl_pre L C S\<close>
   shows \<open>update_confl_tl_wl_pre' ((L, C), S)\<close>
proof -
  obtain x xa where
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    \<open>correct_watching S\<close> and
    x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    st_invs: \<open>twl_struct_invs xa\<close> and
    list_invs: \<open>twl_list_invs x\<close> and
    \<open>twl_stgy_invs xa\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
    nempty: \<open>get_trail_wl S \<noteq> []\<close> and
    \<open>literals_to_update_wl S = {#}\<close> and
    hd: \<open>hd (get_trail_wl S) = Propagated L C\<close> and
    C_0: \<open>0 < C\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>0 < count_decided (get_trail_wl S)\<close> and
    \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
    \<open>L \<in> set (get_clauses_wl S \<propto> C)\<close> and
    uL_D: \<open>- L \<in># the (get_conflict_wl S)\<close> and
    xa: \<open>hd (get_trail xa) = Propagated L (mset (get_clauses_wl S \<propto> C))\<close> and
    L: \<open>L \<in># all_lits_st S\<close> and
    blits: \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close>
    using assms
    unfolding update_confl_tl_wl_pre_def
    update_confl_tl_l_pre_def update_confl_tl_pre_def
    prod.case apply -
    by normalize_goal+
      (simp flip: all_lits_def all_lits_alt_def2
        add: mset_take_mset_drop_mset' \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits)

  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of xa)\<close> and
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of xa)\<close> and
    confl': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of xa)\<close> and
    st_inv: \<open>twl_st_inv xa\<close>
    using st_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      pcdcl_all_struct_invs_def state\<^sub>W_of_def[symmetric]
    by fast+

  have eq: \<open>lits_of_l (tl (get_trail_wl S)) = lits_of_l (tl (get_trail xa))\<close>
     using Sx x_xa unfolding list.set_map[symmetric] lits_of_def
     by (cases S; cases x; cases xa;
       auto simp: state_wl_l_def twl_st_l_def map_tl list_of_l_convert_map_lit_of simp del: list.set_map)

  have card_max: \<open>card_max_lvl (get_trail_wl S) (the (get_conflict_wl S)) \<ge> 1\<close>
    using hd uL_D nempty by (cases \<open>get_trail_wl S\<close>; auto dest!: multi_member_split simp: card_max_lvl_def)

  have dist_C: \<open>distinct_mset (the (get_conflict_wl S))\<close>
    using dist Sx x_xa confl C unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: twl_st)
  have dist:  \<open>distinct (get_clauses_wl S \<propto> C)\<close>
    using dist Sx x_xa confl C unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def
    by (auto simp: image_image ran_m_def dest!: multi_member_split)

  have n_d: \<open>no_dup (get_trail_wl S)\<close>
    using Sx x_xa M_lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: twl_st)
  have CNot_D: \<open>get_trail_wl S \<Turnstile>as CNot (the (get_conflict_wl S))\<close>
   using confl' confl Sx x_xa unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: twl_st)
   then have \<open>tl (get_trail_wl S) \<Turnstile>as CNot (the (get_conflict_wl S) - {#-L#})\<close>
     using dist_C uL_D n_d hd nempty by (cases \<open>get_trail_wl S\<close>)
       (auto dest!: multi_member_split simp: true_annots_true_cls_def_iff_negation_in_model)
  moreover have CNot_C':  \<open>tl (get_trail_wl S) \<Turnstile>as CNot (mset (get_clauses_wl S \<propto> C) - {#L#})\<close> and
    L_C: \<open>L \<in># mset (get_clauses_wl S \<propto> C)\<close>
   using confl' nempty x_xa xa hd Sx nempty eq
   unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
   by (cases \<open>get_trail xa\<close>; fastforce simp: twl_st twl_st_l true_annots_true_cls_def_iff_negation_in_model
      dest: spec[of _ \<open>[]\<close>])+

  ultimately have tl: \<open>tl (get_trail_wl S) \<Turnstile>as CNot ((the (get_conflict_wl S) - {#-L#}) \<union># (mset (get_clauses_wl S \<propto> C) - {#L#}))\<close>
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
  then have \<open>(the (get_conflict_wl S) - {#-L#}) \<union># (mset (get_clauses_wl S \<propto> C) - {#L#}) =
      (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) -
      {#L, - L#})\<close>
    using multi_member_split[OF L_C] uL_D dist dist_C n_d hd nempty
    apply (cases \<open>get_trail_wl S\<close>; auto dest!: multi_member_split
      simp: true_annots_true_cls_def_iff_negation_in_model)
    apply (subst sup_union_left1)
    apply (auto dest!: multi_member_split dest: in_lits_of_l_defined_litD)
    done
  with tl have \<open>tl (get_trail_wl S) \<Turnstile>as CNot (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) -
      {#L, - L#})\<close> by simp
  with distinct_consistent_interp[OF no_dup_tlD[OF n_d]] have 1: \<open>\<not>tautology
     (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) -
      {#L, - L#})\<close>
    unfolding true_annots_true_cls
    by (rule consistent_CNot_not_tautology)
  have False if \<open>- L \<in># mset (get_clauses_wl S \<propto> C)\<close>
     using multi_member_split[OF L_C] hd nempty n_d CNot_C' multi_member_split[OF that]
     by (cases \<open>get_trail_wl S\<close>; auto dest!: multi_member_split
         simp: add_mset_eq_add_mset true_annots_true_cls_def_iff_negation_in_model
         dest!: in_lits_of_l_defined_litD)
   then have 2: \<open>-L \<notin> set (get_clauses_wl S \<propto> C)\<close>
      by auto

  have \<open>length (get_clauses_wl S \<propto> C) \<ge> 2\<close>
    using st_inv C  Sx x_xa by (cases xa; cases x; cases S; cases \<open>irred (get_clauses_wl S) C\<close>;
      auto simp: twl_st_inv.simps state_wl_l_def twl_st_l_def conj_disj_distribR Collect_disj_eq image_Un
        ran_m_def Collect_conv_if dest!: multi_member_split)
  then have [simp]: \<open>length (get_clauses_wl S \<propto> C) \<noteq> 2 \<longleftrightarrow> length (get_clauses_wl S \<propto> C) > 2\<close>
    by (cases \<open>get_clauses_wl S \<propto> C\<close>; cases \<open>tl (get_clauses_wl S \<propto> C)\<close>;
      auto simp: twl_list_invs_def all_conj_distrib dest: in_set_takeD)


  have CNot_C:  \<open>\<not>tautology (mset (get_clauses_wl S \<propto> C))\<close>
    using CNot_C' Sx hd nempty C_0 dist multi_member_split[OF L_C] dist
        consistent_CNot_not_tautology[OF distinct_consistent_interp[OF no_dup_tlD[OF n_d]]
           CNot_C'[unfolded true_annots_true_cls]] 2
    unfolding true_annots_true_cls_def_iff_negation_in_model
    apply (auto simp: tautology_add_mset dest: arg_cong[of \<open>mset _\<close> _ set_mset])
    by (metis member_add_mset set_mset_mset)


  have stupid: \<open>K \<in># removeAll_mset L D \<longleftrightarrow> K \<noteq> L \<and> K \<in># D\<close> for K L D
    by auto
  have K: \<open>K \<in># remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<Longrightarrow> - K \<notin># the (get_conflict_wl S)\<close> and
     uL_C: \<open>-L \<notin># (mset (get_clauses_wl S \<propto> C))\<close> for K
    apply (subst (asm) distinct_mset_remove1_All)
    subgoal using dist by auto
    apply (subst (asm)stupid)
    apply (rule conjE, assumption)
   apply (drule multi_member_split)
    using 1 uL_D CNot_C dist 2[unfolded in_multiset_in_set[symmetric]] dist_C
      consistent_CNot_not_tautology[OF distinct_consistent_interp[OF n_d]
           CNot_D[unfolded true_annots_true_cls]]  \<open>L \<in># mset (get_clauses_wl S \<propto> C)\<close>
     by (auto dest!: multi_member_split[of \<open>-L\<close>] multi_member_split in_set_takeD
       simp: tautology_add_mset add_mset_eq_add_mset uminus_lit_swap diff_union_swap2
       simp del: set_mset_mset in_multiset_in_set
         distinct_mset_mset_distinct simp flip: distinct_mset_mset_distinct)
 have size: \<open>size (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) > 0\<close>
    using uL_D uL_C by (auto dest!: multi_member_split)

  have max_lvl: \<open>Suc 0 \<le> card_max_lvl (get_trail_wl S) (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S))\<close>
    using uL_D hd nempty uL_C by (cases \<open>get_trail_wl S\<close>; auto simp: card_max_lvl_def dest!: multi_member_split)


  have s: \<open>size (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) =
       size (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#}) + 1\<close>
    using uL_D hd nempty uL_C dist_C apply (cases \<open>get_trail_wl S\<close>; auto simp: dest!: multi_member_split)
    by (metis (no_types, opaque_lifting) \<open>remove1_mset (- L) (the (get_conflict_wl S)) \<union># remove1_mset L (mset (get_clauses_wl S \<propto> C)) = the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#}\<close> add_mset_commute add_mset_diff_bothsides add_mset_remove_trivial set_mset_mset subset_mset.sup_commute sup_union_left1)


  have SC_0: \<open>length (get_clauses_wl S \<propto> C) > 2 \<Longrightarrow> L \<notin> set (tl (get_clauses_wl S \<propto> C)) \<and> get_clauses_wl S \<propto> C ! 0 = L \<and>
       mset (tl (get_clauses_wl S \<propto> C)) = remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<and>
        (\<forall>L\<in>set (tl(get_clauses_wl S \<propto> C)). - L \<notin># the (get_conflict_wl S)) \<and>
       card_max_lvl (get_trail_wl S) (mset (tl (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S)) =
          card_max_lvl (get_trail_wl S) (remove1_mset L (mset (get_clauses_wl S \<propto> C)) \<union># the (get_conflict_wl S))\<close>
     \<open>L \<in> set (watched_l (get_clauses_wl S \<propto> C))\<close>
      \<open>L \<in># mset (get_clauses_wl S \<propto> C)\<close>
    using list_invs Sx hd nempty C_0 dist L_C K
    by (cases \<open>get_trail_wl S\<close>; cases \<open>get_clauses_wl S \<propto> C\<close>;
      auto simp: twl_list_invs_def all_conj_distrib dest: in_set_takeD; fail)+

  have max: \<open>card_max_lvl (get_trail_wl S) ((mset (get_clauses_wl S \<propto> C) - unmark (hd (get_trail_wl S))) \<union># the (get_conflict_wl S))  =
        card_max_lvl (tl (get_trail_wl S)) (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#}) + Suc 0\<close>
    using multi_member_split[OF uL_D] L_C hd nempty n_d dist dist_C 1 \<open>0 < count_decided (get_trail_wl S)\<close> uL_C n_d
        consistent_CNot_not_tautology[OF distinct_consistent_interp[OF n_d]
           CNot_D[unfolded true_annots_true_cls]] CNot_C apply (cases \<open>get_trail_wl S\<close>;
           auto simp: card_max_lvl_Cons card_max_lvl_add_mset subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close> ]
             subset_mset.sup_commute[of _ \<open>mset _\<close>] tautology_add_mset)
    apply (subst card_max_lvl_Cons)
    apply (auto simp: card_max_lvl_Cons card_max_lvl_add_mset subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close> ]
             subset_mset.sup_commute[of _ \<open>mset _\<close>] tautology_add_mset remove1_mset_union_distrib1)
    using K uL_D apply presburger
    done


  have xx: \<open>out_learned (tl (get_trail_wl S)) (Some (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#})) outl \<longleftrightarrow>
      out_learned (get_trail_wl S) (Some (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#})) outl\<close> for outl
  apply (subst tl_state_out_learned)
   apply (cases \<open>get_trail_wl S\<close>; use L_C hd nempty dist dist_C in auto)
   apply (meson distinct_mem_diff_mset distinct_mset_mset_distinct distinct_mset_union_mset union_single_eq_member)
   apply (cases \<open>get_trail_wl S\<close>; use L_C hd nempty dist dist_C in auto)
   apply (metis add_mset_commute distinct_mem_diff_mset distinct_mset_mset_distinct distinct_mset_union_mset union_single_eq_member)
   apply (cases \<open>get_trail_wl S\<close>; use L_C hd nempty dist dist_C in auto)
   ..

  have [simp]: \<open>get_level (get_trail_wl S) L = count_decided (get_trail_wl S)\<close>
    by (cases \<open>get_trail_wl S\<close>; use L_C hd nempty dist dist_C in auto)
  have yy: \<open>out_learned (get_trail_wl S) (Some ((the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C)) - {#L, - L#})) outl \<longleftrightarrow>
      out_learned (get_trail_wl S) (Some ((mset (get_clauses_wl S \<propto> C) - unmark (hd (get_trail_wl S))) \<union># the (get_conflict_wl S))) outl\<close> for outl
   by (use L_C hd nempty dist dist_C in \<open>auto simp add: out_learned_def ac_simps\<close>)

  have xx: \<open>out_learned (tl (get_trail_wl S)) (Some (the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#})) =
      out_learned (get_trail_wl S) (Some ((mset (get_clauses_wl S \<propto> C) - unmark (hd (get_trail_wl S))) \<union># the (get_conflict_wl S)))\<close>
    using xx yy by (auto intro!: ext)
  show ?thesis
    using Sx x_xa C C_0 confl nempty uL_D L blits 1 2 card_max dist_C dist SC_0 max
        consistent_CNot_not_tautology[OF distinct_consistent_interp[OF n_d]
           CNot_D[unfolded true_annots_true_cls]] CNot_C K xx
        \<open>0 < count_decided (get_trail_wl S)\<close>  size max_lvl s
     literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict[OF Sx st_invs x_xa _ , of \<open>all_atms_st S\<close>]
     literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail[OF Sx st_invs x_xa _ , of \<open>all_atms_st S\<close>]
    unfolding update_confl_tl_wl_pre'_def
    by (clarsimp simp flip: all_lits_def simp add: hd mset_take_mset_drop_mset' \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits)

qed

lemma (in -)out_learned_add_mset_highest_level:
   \<open>L = lit_of (hd M) \<Longrightarrow> out_learned M (Some (add_mset (- L) A)) outl \<longleftrightarrow>
    out_learned M (Some A) outl\<close>
  by (cases M)
    (auto simp: out_learned_def get_level_cons_if atm_of_eq_atm_of count_decided_ge_get_level
      uminus_lit_swap cong: if_cong
      intro!: filter_mset_cong2)

lemma (in -)out_learned_tl_Some_notin:
  \<open>is_proped (hd M) \<Longrightarrow> lit_of (hd M) \<notin># C \<Longrightarrow> -lit_of (hd M) \<notin># C \<Longrightarrow>
    out_learned M (Some C) outl \<longleftrightarrow> out_learned (tl M) (Some C) outl\<close>
  by (cases M) (auto simp: out_learned_def get_level_cons_if atm_of_eq_atm_of
      intro!: filter_mset_cong2)


lemma update_confl_tl_wl_heur_update_confl_tl_wl:
  \<open>(uncurry2 (update_confl_tl_wl_heur), uncurry2 mop_update_confl_tl_wl) \<in>
  [\<lambda>_. True]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r lcount \<rightarrow>
    \<langle>bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r lcount\<rangle>nres_rel\<close>
proof -
  have mop_update_confl_tl_wl_alt_def: \<open>mop_update_confl_tl_wl = (\<lambda>L C (M, N, D, NE, UE, WS, Q). do {
      ASSERT(update_confl_tl_wl_pre L C (M, N, D, NE, UE, WS, Q));
      N \<leftarrow> calculate_LBD_st M N C;
      D \<leftarrow> RETURN (resolve_cls_wl' (M, N, D, NE, UE, WS, Q) C L);
      N \<leftarrow> RETURN N;
      _ \<leftarrow> RETURN ();
      N \<leftarrow> RETURN N;
      _ \<leftarrow> RETURN ();
      RETURN (False, (tl M, N, Some D, NE, UE, WS, Q))
    })\<close>
    by (auto simp: mop_update_confl_tl_wl_def update_confl_tl_wl_def calculate_LBD_st_def
      intro!: ext)
  define rr where
  \<open>rr L M N C b n xs clvls outl = do {
          ((b, (n, xs)), clvls, outl) \<leftarrow>
            if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C (b, (n, xs)) clvls outl
           else isa_resolve_merge_conflict_gt2 M N C (b, (n, xs)) clvls outl;
         ASSERT(curry lookup_conflict_remove1_pre L (n, xs) \<and> clvls \<ge> 1);
         let (nxs) = lookup_conflict_remove1 L (n, xs);
         RETURN ((b, (nxs)), clvls, outl) }\<close>
    for  L M N C b n xs clvls lbd outl
  have update_confl_tl_wl_heur_alt_def:
    \<open>update_confl_tl_wl_heur = (\<lambda>L C S. do {
      let M = get_trail_wl_heur S;
      let N = get_clauses_wl_heur S;
      let lbd = get_lbd S;
      let outl = get_outlearned_heur S;
      let clvls = get_count_max_lvls_heur S;
      let vm = get_vmtf_heur S;
      let (b, (n, xs)) = get_conflict_wl_heur S;
      (N, lbd) \<leftarrow> calculate_LBD_heur_st M N lbd C;
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_is_valid_clause_idx N C);
      ((b, (n, xs)), clvls, outl) \<leftarrow> rr L M N C b n xs clvls outl;
      ASSERT(arena_act_pre N C);
      vm \<leftarrow> isa_vmtf_bump_to_rescore_also_reasons_cl_maybe (rate_should_bump_reason_st S) M N C (-L) vm;
      ASSERT(isa_bump_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      vm \<leftarrow> isa_bump_unset L' vm;
      let S = set_trail_wl_heur (tl_trailt_tr M) S;
      let S = set_conflict_wl_heur (b, (n, xs)) S;
      let S = set_vmtf_wl_heur vm S;
      let S = set_count_max_wl_heur (clvls - 1) S;
      let S = set_outl_wl_heur outl S;
      let S = set_clauses_wl_heur N S;
      let S = set_lbd_wl_heur lbd S;
      RETURN (False, S)
   })\<close>
  by (auto simp: update_confl_tl_wl_heur_def Let_def rr_def intro!: ext bind_cong[OF refl])

note [[goals_limit=1]]
  have rr: \<open>(((x1g, x2g), S),
     (x1, x2), x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r lcount \<Longrightarrow>
    CLS = ((x1, x2), x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) \<Longrightarrow>
    CLS' = ((x1g, x2g), S, s, t) \<Longrightarrow>
    update_confl_tl_wl_pre x1 x2 (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) \<Longrightarrow>
    1 \<le> x1q \<Longrightarrow>
    arena_is_valid_clause_idx x1i x2g \<Longrightarrow>
    (x1k, (x1l, x2k)) = get_conflict_wl_heur S \<Longrightarrow>
    rr x1g (get_trail_wl_heur S) (get_clauses_wl_heur S) x2g x1k x1l x2k (get_count_max_lvls_heur S)
      (get_outlearned_heur S)
    \<le> \<Down> {((C, clvls, outl), D). (C, Some D) \<in> option_lookup_clause_rel (all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f))  \<and>
          clvls = card_max_lvl x1a (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c)  \<and>
         out_learned x1a (Some (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c)) (outl) \<and>
         size (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c) =
           size ((mset (x1b \<propto> x2)) \<union># the x1c - {#x1, -x1#}) + Suc 0 \<and>
        D = resolve_cls_wl' (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) x2 x1}
       (RETURN (resolve_cls_wl' (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) x2 x1))\<close>
     for m n p q ra s t x1 x2 x1a x1b x1c x1d x1e x1f x2f x1g x2g x1h x1i x1k
       x1l x2k x1m x1n x1p x1q x1r x1t CLS CLS' NS US x1s S
     unfolding rr_def
     apply (refine_vcg lhs_step_If)
     apply (rule isasat_lookup_merge_eq2_lookup_merge_eq2[where
        vdom = \<open>set (get_vdom S)\<close> and M = x1a and  N = x1b and C = x1c and
      \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) \<close>, THEN order_trans])
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre' simp: update_confl_tl_wl_pre'_def)
     subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_lits_st_def all_lits_of_mm_union
         all_lits_def
       simp flip: all_lits_st_alt_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal unfolding Down_id_eq
      apply (rule lookup_merge_eq2_spec[where M = x1a and C = \<open>the x1c\<close> and
      \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f)\<close>, THEN order_trans])
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_lits_st_def all_lits_of_mm_union
         all_lits_def simp flip: all_lits_st_alt_def
        intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_literals_are_in_\<L>\<^sub>i\<^sub>n)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def counts_maximum_level_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_lifting twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_lifting twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def merge_conflict_m_eq2_def conc_fun_SPEC lookup_conflict_remove1_pre_def
           atms_of_def
           option_lookup_clause_rel_def lookup_clause_rel_def resolve_cls_wl'_def lookup_conflict_remove1_def
           remove1_mset_union_distrib1 remove1_mset_union_distrib2 subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
        subset_mset.sup_commute[of _ \<open>mset (_ \<propto> _)\<close>]
        simp flip: all_lits_st_alt_def[symmetric]
         intro!: mset_as_position_remove3
         intro!: ASSERT_leI)
     done
    subgoal
      apply (subst (asm) arena_lifting(4)[where vdom = \<open>set (get_vdom_aivdom (get_aivdom S))\<close> and N = x1b, symmetric])
      subgoal by (auto simp: twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def)
      apply (rule isa_resolve_merge_conflict_gt2[where
         \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f)\<close> and vdom = \<open>set (get_vdom_aivdom (get_aivdom S))\<close>,
       THEN fref_to_Down_curry5, of x1a x1b x2g x1c \<open>get_count_max_lvls_heur S\<close> \<open>get_outlearned_heur S\<close>,
       THEN order_trans])
     subgoal unfolding merge_conflict_m_pre_def
       by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def counts_maximum_level_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal
        by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def conc_fun_SPEC lookup_conflict_remove1_pre_def atms_of_def
           option_lookup_clause_rel_def lookup_clause_rel_def resolve_cls_wl'_def
           merge_conflict_m_def lookup_conflict_remove1_def subset_mset.sup_commute[of _ \<open>mset (_ \<propto> _)\<close>]
           remove1_mset_union_distrib1 remove1_mset_union_distrib2
         simp flip: all_lits_st_alt_def[symmetric]
         intro!: mset_as_position_remove3
         intro!: ASSERT_leI)
      done
    done
  have rr: \<open>(((x1g, x2g), S),
        (x1, x2), x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja)
       \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r lcount \<Longrightarrow>
       CLS = ((x1, x2), x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja) \<Longrightarrow>
       CLS' = ((x1g, x2g), S) \<Longrightarrow>
       get_conflict_wl_heur S = (x1k, (x1l, x2k)) \<Longrightarrow>
       update_confl_tl_wl_pre x1 x2
        (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja) \<Longrightarrow>
       ((x1t, x2t :: bool list), x1b)
       \<in> {((arena', lbd), N').
          valid_arena arena' N'
           (set (get_vdom
                  (snd ((x1g, x2g), S)))) \<and>
          N = N' \<and> length x1i = length arena'} \<Longrightarrow>
       1 \<le> x1p \<Longrightarrow>
       arena_is_valid_clause_idx x1t x2g \<Longrightarrow>
       rr x1g (get_trail_wl_heur S) x1t x2g x1k x1l x2k (get_count_max_lvls_heur S)
      (get_outlearned_heur S)
       \<le> \<Down> {((C, clvls, outl), D). (C, Some D) \<in> option_lookup_clause_rel (all_atms_st (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja))  \<and>
          clvls = card_max_lvl x1a (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c)  \<and>
         out_learned x1a (Some (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c)) (outl) \<and>
         size (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c) =
           size ((mset (x1b \<propto> x2)) \<union># the x1c - {#x1, -x1#}) + Suc 0 \<and>
        D = resolve_cls_wl' (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja) x2 x1}
       (RETURN (resolve_cls_wl' (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja) x2 x1))\<close>
   for l m n p q ra s ha ia ja x1 x2 x1a x1b x1c x1d x1e x1f x1g x2g x1h x1i
       x1k x1l x2k x1m x1n x1o x1p x1q x1r x1s N x1t x2t CLS CLS' S
     unfolding rr_def
     apply (refine_vcg lhs_step_If)
     apply (rule isasat_lookup_merge_eq2_lookup_merge_eq2[where
        vdom = \<open>set (get_vdom S)\<close> and M = x1a and  N = x1b and C = x1c and
      \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja)\<close>, THEN order_trans])
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre' simp: update_confl_tl_wl_pre'_def)
     subgoal by auto
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal unfolding Down_id_eq
      apply (rule lookup_merge_eq2_spec[where M = x1a and C = \<open>the x1c\<close> and
      \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja)\<close>, THEN order_trans])
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_literals_are_in_\<L>\<^sub>i\<^sub>n)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def counts_maximum_level_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_lifting twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
        simp: update_confl_tl_wl_pre'_def arena_lifting twl_st_heur_conflict_ana_def
        dest: in_set_takeD)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def merge_conflict_m_eq2_def conc_fun_SPEC lookup_conflict_remove1_pre_def
           atms_of_def
           option_lookup_clause_rel_def lookup_clause_rel_def resolve_cls_wl'_def lookup_conflict_remove1_def
           remove1_mset_union_distrib1 remove1_mset_union_distrib2 subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
           subset_mset.sup_commute[of _ \<open>mset (_ \<propto> _)\<close>]
         simp flip: all_lits_st_alt_def
         intro!: mset_as_position_remove3
         intro!: ASSERT_leI)
     done
    subgoal
      apply (subst (asm) arena_lifting(4)[where vdom = \<open>set (get_vdom_aivdom (get_aivdom S))\<close> and N = x1b, symmetric])
      subgoal by (auto simp: twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def)
      apply (rule isa_resolve_merge_conflict_gt2[where
         \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja)\<close> and vdom = \<open>set (get_vdom_aivdom (get_aivdom S))\<close>,
       THEN fref_to_Down_curry5, of x1a x1b x2g x1c \<open>get_count_max_lvls_heur S\<close>  \<open>get_outlearned_heur S\<close>,
       THEN order_trans])
     subgoal unfolding merge_conflict_m_pre_def
       by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def counts_maximum_level_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal
        by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def conc_fun_SPEC lookup_conflict_remove1_pre_def atms_of_def
           option_lookup_clause_rel_def lookup_clause_rel_def resolve_cls_wl'_def
           merge_conflict_m_def lookup_conflict_remove1_def subset_mset.sup_commute[of _ \<open>mset (_ \<propto> _)\<close>]
           remove1_mset_union_distrib1 remove1_mset_union_distrib2
         intro!: mset_as_position_remove3
         simp flip: all_lits_st_alt_def
         intro!: ASSERT_leI)
      done
    done
  have all_in_dom: \<open>\<forall>C\<in>set (N \<propto> x2).
    C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la))\<close> if
    \<open>valid_arena x1t N vdom\<close>
    \<open>x2 \<in># dom_m N\<close>
    for x2 x1t C x1a N x1c x2d x1e x1f ha ia ja ka la x1d vdom
    apply (intro ballI)
    subgoal for C
      using that(2)
      by (auto intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l in_clause_in_all_lits_of_m
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_atms_st_def all_atms_def all_lits_def
        all_lits_of_mm_add_mset \<L>\<^sub>a\<^sub>l\<^sub>l_union ran_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm
        dest!: multi_member_split[of _ \<open>dom_m _\<close>])
   done
  have all_in_do: \<open>C\<in>set [x2..<x2 + arena_length x1t x2] \<Longrightarrow>
    arena_lit x1t C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la))\<close> if
    \<open>valid_arena x1t N vdom\<close>
    \<open>x2 \<in># dom_m N\<close>
    for x2 x1t C x1a N x1c x2d x1e x1f ha ia ja ka la x1d vdom
    apply (subst (asm) arena_lifting(4)[OF that, symmetric])
      using that(2) arena_lifting(5)[OF that, of \<open>C - x2\<close>, symmetric]
      by (auto intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l in_clause_in_all_lits_of_m
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_atms_st_def all_atms_def all_lits_def
        all_lits_of_mm_add_mset \<L>\<^sub>a\<^sub>l\<^sub>l_union ran_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm
        dest!: multi_member_split[of _ \<open>dom_m _\<close>])

 have isa_vmtf_mark_to_rescore_clause: \<open>
    (((x1g, x2g), S), (x1, x2), x1a, x1b, x1c, x1d,
     x1e, x1f, ha, ia, ja, ka, la)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r lcount \<Longrightarrow>
    CLS = ((x1, x2), x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la) \<Longrightarrow>
    CLS' = ((x1g, x2g), S) \<Longrightarrow>
    update_confl_tl_wl_pre x1 x2 (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la) \<Longrightarrow>
    ((x1t, x2t), N)
    \<in> {((arena', lbd), N').
    valid_arena arena' N'
     (set (get_vdom (snd ((x1g, x2g), S)))) \<and>
    x1b = N' \<and> length x1i = length arena'} \<Longrightarrow>
    1 \<le> x1p \<Longrightarrow>
    arena_is_valid_clause_idx x1t x2g \<Longrightarrow>
    (((x1v, x1w, x2v), x1x, x2x), D)
    \<in> {a. case a of
       (a, b) \<Rightarrow>
      (case a of
       (C, a) \<Rightarrow>
         case a of
         (clvls, outl) \<Rightarrow>
        \<lambda>D. (C, Some D) \<in> option_lookup_clause_rel (all_atms_st (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la)) \<and>
            clvls = card_max_lvl x1a (remove1_mset x1 (mset (N \<propto> x2)) \<union># the x1c) \<and>
            out_learned x1a (Some (remove1_mset x1 (mset (N \<propto> x2)) \<union># the x1c)) outl \<and>
            size (remove1_mset x1 (mset (N \<propto> x2)) \<union># the x1c) = size (mset (N \<propto> x2) \<union># the x1c - {#x1, - x1#}) + Suc 0 \<and>
            D = resolve_cls_wl' (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la) x2 x1)
       b} \<Longrightarrow>
    arena_act_pre x1t x2g \<Longrightarrow>
    isa_vmtf_bump_to_rescore_also_reasons_cl_maybe b (get_trail_wl_heur S) x1t x2g (-x1g) (get_vmtf_heur S)
           \<le> \<Down> {(vm, N'). N = N' \<and> vm \<in> bump_heur (all_atms_st (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la)) x1a}
    (RETURN N)\<close>
   for l m n p q ra s ha ia ja ka la x1 x2 x1a x1b x1c x1d x1e x1f x1g x2g x1h x1i x1k x1l x2k
     x1m x1n x1o x1p x1q x1r x1s N x1t x2t D x1v x1w x2v x1x x2x CLS CLS' S b
  unfolding twl_st_heur_conflict_ana_def apply (clarsimp simp only: prod_rel_iff)
  subgoal
    apply (rule isa_vmtf_bump_to_rescore_also_reasons_cl_maybe_vmtf_mark_to_rescore_also_reasons_cl[
      where \<A> = \<open>all_atms_st (x1a, N, x1c, x1d, x1e, x1f, ha, ia, ja, ka, la)\<close>,
  THEN fref_to_Down_curry5,
    of _ b x1a _ _ _ _ _ _ x1t  x2 \<open>-x1\<close>  \<open>get_vmtf_heur S\<close>,
  THEN order_trans])
    apply  (auto simp: update_confl_tl_wl_pre_def update_confl_tl_l_pre_def ran_m_def
      isa_vmtf_bump_to_rescore_also_reasons_cl_maybe_pre_def RETURN_def conc_fun_RES
      twl_st_l_def state_wl_l_def twl_list_invs_def intro!: all_in_dom)
    apply (meson all_in_dom)
    apply (meson all_in_dom)
    done
   done

  have isa_bump_unset: \<open>isa_bump_unset L x \<le> \<Down>{(a, _). a \<in> bump_heur \<A> (tl M)} (RETURN ())\<close>
  if
    vmtf: \<open>x\<in> bump_heur \<A> M\<close> and
    L_N: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and [simp]: \<open>M \<noteq> []\<close> and
    nz: \<open>count_decided M > 0\<close> and
    L: \<open>L = atm_of (lit_of (hd M))\<close> for L x M \<A>
    unfolding L
    by (rule isa_bump_unset_vmtf_tl[OF that(1-4)[unfolded L], THEN order_trans])
      (auto simp: conc_fun_RES RETURN_def)

  have mset_tl_nth_0: \<open>length Na > 0 \<Longrightarrow> mset (tl (Na)) = mset Na - {#(Na ! 0)#}\<close> for Na
    by (cases Na) auto
  show ?thesis
    supply [[goals_limit = 1]]
    supply RETURN_as_SPEC_refine[refine2 del]
       update_confl_tl_wl_pre_update_confl_tl_wl_pre'[dest!]
    apply (intro frefI nres_relI)
    subgoal for CLS' CLS
      apply (cases CLS'; cases CLS; hypsubst+)
      unfolding uncurry_def update_confl_tl_wl_heur_alt_def comp_def Let_def
        update_confl_tl_wl_def mop_update_confl_tl_wl_alt_def prod.case
      apply (refine_rcg calculate_LBD_heur_st_calculate_LBD_st[where
          vdom = \<open>set (get_vdom (snd CLS'))\<close> and
          \<A> = \<open>all_atms_st (snd CLS)\<close>]
        isa_bump_unset[where \<A>3 = \<open>all_atms_st (snd CLS)\<close> and M3 = \<open>get_trail_wl (snd CLS)\<close>];
        remove_dummy_vars)
      subgoal
        by (auto simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
            RES_RETURN_RES RETURN_def counts_maximum_level_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def)
      subgoal
        using literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of \<open>snd (fst CLS)\<close> \<open>snd CLS\<close>
         \<open>all_atms_st (snd CLS)\<close>, simplified]
        by (auto
         simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def)
      subgoal by auto
      subgoal
        by (auto simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
            RES_RETURN_RES RETURN_def counts_maximum_level_def)
      subgoal by (auto intro!: exI[of _ \<open>get_clauses_wl (snd CLS)\<close>] exI[of _ \<open>set (get_vdom (snd CLS'))\<close>]
         simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def)
      apply (rule rr; assumption)
      subgoal by (simp add: arena_act_pre_def)
      apply (rule isa_vmtf_mark_to_rescore_clause; assumption)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
        simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def
        simp flip: all_lits_st_alt_def
        intro!: isa_bump_unset_pre
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of _ M \<open>lit_of (hd M)\<close> for M])
      subgoal for m n p q ra s t ha ia ja x1 x2 x1a x1b x1c x1d x1e x1f x1g x2g x1h x1i
       x1k x1l x2k x1m x1n x1o x1p x1q x1r x1t
         by (rule tl_trailt_tr_pre[of x1 _ \<open>all_atms_st (x1, x1i, x1a, x1b, x1c, x1d, n, p, q, ra, s, t, ha)\<close>])
          (clarsimp_all dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
             simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def
             simp flip: all_lits_st_alt_def
             intro!: tl_trailt_tr_pre)
      subgoal by auto
      subgoal apply (clarsimp simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
           valid_arena_mark_used subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
          tl_trail_tr[THEN fref_to_Down_unRET] resolve_cls_wl'_def isa_bump_unset_vmtf_tl no_dup_tlD
          counts_maximum_level_def
        simp flip: all_lits_st_alt_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of _ M \<open>lit_of (hd M)\<close> for M])
        apply (meson all_in_dom atm_of_lit_in_atms_of)
        by (meson atm_of_in_atms_of literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l)+
      subgoal by (clarsimp simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
           valid_arena_mark_used subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
          tl_trail_tr[THEN fref_to_Down_unRET] resolve_cls_wl'_def isa_bump_unset_vmtf_tl no_dup_tlD
          counts_maximum_level_def
        simp flip: all_lits_st_alt_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of _ M \<open>lit_of (hd M)\<close> for M])
      subgoal by (clarsimp simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
           valid_arena_mark_used subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
          tl_trail_tr[THEN fref_to_Down_unRET] resolve_cls_wl'_def isa_bump_unset_vmtf_tl no_dup_tlD
          counts_maximum_level_def
        simp flip: all_lits_st_alt_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of _ M \<open>lit_of (hd M)\<close> for M])
      subgoal by (clarsimp simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
           valid_arena_mark_used subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
          tl_trail_tr[THEN fref_to_Down_unRET] resolve_cls_wl'_def isa_bump_unset_vmtf_tl no_dup_tlD
          counts_maximum_level_def
        simp flip: all_lits_st_alt_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of _ M \<open>lit_of (hd M)\<close> for M])
      subgoal by (clarsimp simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
           valid_arena_mark_used subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close>]
          tl_trail_tr[THEN fref_to_Down_unRET] resolve_cls_wl'_def isa_bump_unset_vmtf_tl no_dup_tlD
          counts_maximum_level_def
        simp flip: all_lits_st_alt_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of _ M \<open>lit_of (hd M)\<close> for M])
      done
  done
qed

lemma phase_saving_le: \<open>phase_saving \<A> \<phi> \<Longrightarrow> A \<in># \<A> \<Longrightarrow> A < length \<phi>\<close>
   \<open>phase_saving \<A> \<phi> \<Longrightarrow> B \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of B < length \<phi>\<close>
  by (auto simp: phase_saving_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

lemma trail_pol_nempty: \<open>\<not>(([], aa, ab, ac, ad, b), L # ys) \<in> trail_pol \<A>\<close>
  by (auto simp: trail_pol_def ann_lits_split_reasons_def)

lemma is_decided_hd_trail_wl_heur_hd_get_trail:
  \<open>(RETURN o is_decided_hd_trail_wl_heur, RETURN o (\<lambda>M. is_decided (hd (get_trail_wl M))))
   \<in> [\<lambda>M. get_trail_wl M \<noteq> []]\<^sub>f twl_st_heur_conflict_ana' r lcount \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
   by (intro frefI nres_relI)
     (auto simp: is_decided_hd_trail_wl_heur_def twl_st_heur_conflict_ana_def neq_Nil_conv
        trail_pol_def ann_lits_split_reasons_def is_decided_no_proped_iff last_trail_pol_def
      split: option.splits)


lemma skip_and_resolve_loop_wl_D_heur_alt_def:
  \<open>skip_and_resolve_loop_wl_D_heur S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided_hd_trail_wl_heur S)
        (\<lambda>(brk, S).
          do {
            ASSERT(\<not>brk \<and> \<not>is_decided_hd_trail_wl_heur S);
            (L, C) \<leftarrow> lit_and_ann_of_propagated_st_heur S;
            b \<leftarrow> atm_is_in_conflict_st_heur (-L) S;
            if b then
	      tl_state_wl_heur S
            else do {
              b \<leftarrow> maximum_level_removed_eq_count_dec_heur L S;
              if b
              then do {
                update_confl_tl_wl_heur L C S
              }
              else
                RETURN (True, S)
            }
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>
  unfolding IsaSAT_Profile.start_def IsaSAT_Profile.stop_def nres_monad1
    skip_and_resolve_loop_wl_D_heur_def ..


lemma atm_is_in_conflict_st_heur_is_in_conflict_st:
  \<open>(uncurry (atm_is_in_conflict_st_heur), uncurry (mop_lit_notin_conflict_wl)) \<in>
   [\<lambda>(L, S). True]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_conflict_ana \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have 1: \<open>aaa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l A \<Longrightarrow> atm_of aaa  \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l A)\<close> for aaa A
    by (auto simp: atms_of_def)
  show ?thesis
  unfolding atm_is_in_conflict_st_heur_def twl_st_heur_def option_lookup_clause_rel_def uncurry_def comp_def
    mop_lit_notin_conflict_wl_def twl_st_heur_conflict_ana_def
  apply (intro frefI nres_relI)
  apply refine_rcg
  apply clarsimp
  subgoal
     apply (rule atm_in_conflict_lookup_pre[of _ \<open>all_atms_st _\<close>])
     unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits[symmetric] all_lits_st_alt_def[symmetric]
     apply auto
     done
  subgoal for x y x1 x2 x1a x2a x1b x2b 
    apply (subst atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id, of \<open>all_atms_st x2\<close>  \<open>atm_of x1\<close> \<open>the (get_conflict_wl (snd y))\<close>])
    apply (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def all_lits_st_alt_def[symmetric])[]
    apply (auto simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def option_lookup_clause_rel_def)[]
    apply (simp add: atm_in_conflict_def atm_of_in_atms_of)
    done
  done
qed

lemma skip_and_resolve_loop_wl_alt_def:
  \<open>skip_and_resolve_loop_wl S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_wl_inv S\<^sub>0 brk S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          do {
            (L, C) \<leftarrow> mop_hd_trail_wl S;
            b \<leftarrow> mop_lit_notin_conflict_wl (-L) S;
            if b then
              mop_tl_state_wl S
            else do {
              b \<leftarrow> mop_maximum_level_removed_wl L S;
              if b
              then do {
                mop_update_confl_tl_wl L C S
              }
              else
                do {RETURN (True, S)}
           }
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }\<close>
  unfolding skip_and_resolve_loop_wl_def calculate_LBD_st_def IsaSAT_Profile.start_def
    IsaSAT_Profile.stop_def
  by (auto cong: if_cong)

lemma skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D:
  \<open>(skip_and_resolve_loop_wl_D_heur, skip_and_resolve_loop_wl)
    \<in> twl_st_heur_conflict_ana' r lcount \<rightarrow>\<^sub>f \<langle>twl_st_heur_conflict_ana' r lcount\<rangle>nres_rel\<close>
proof -
  have H[refine0]: \<open>(x, y) \<in> twl_st_heur_conflict_ana' r lcount  \<Longrightarrow>
           ((False, x), False, y)
           \<in> bool_rel \<times>\<^sub>f
              twl_st_heur_conflict_ana' r lcount\<close> for x y
    by auto
  have H1: \<open>(xa, x')
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur_conflict_ana' r lcount \<Longrightarrow>
    case x' of (x, xa) \<Rightarrow> skip_and_resolve_loop_wl_inv y x xa \<Longrightarrow>
    xa = (x1, x2) \<Longrightarrow>
      x' = (x1a, x2a) \<Longrightarrow> (x2, x2a) \<in> twl_st_heur_conflict_ana' r lcount\<close> for xa x' x1 x2 x1a x2a y
   by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding skip_and_resolve_loop_wl_D_heur_alt_def skip_and_resolve_loop_wl_alt_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
        update_confl_tl_wl_heur_update_confl_tl_wl[THEN fref_to_Down_curry2, unfolded comp_def]
        maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec
          [THEN fref_to_Down_curry] lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st[THEN fref_to_Down]
       tl_state_wl_heur_tl_state_wl[THEN fref_to_Down]
       atm_is_in_conflict_st_heur_is_in_conflict_st[THEN fref_to_Down_curry])
   subgoal for S T brkS brkT
     unfolding skip_and_resolve_loop_wl_D_heur_inv_def
     apply (subst case_prod_beta)
     apply (rule exI[of _ \<open>snd brkT\<close>])
     apply (rule exI[of _ \<open>T\<close>])
     apply (subst (asm) (1) surjective_pairing[of brkS])
     apply (subst (asm) surjective_pairing[of brkT])
     unfolding prod_rel_iff
     by auto
   subgoal for x y xa x' x1 x2 x1a x2a
     apply (subst is_decided_hd_trail_wl_heur_hd_get_trail[of r, THEN fref_to_Down_unRET_Id, of x2a])
     subgoal
       unfolding skip_and_resolve_loop_wl_inv_def skip_and_resolve_loop_inv_l_def skip_and_resolve_loop_inv_def
       apply (subst (asm) case_prod_beta)+
       unfolding prod.case
       apply normalize_goal+
       by (auto simp: )
    apply (rule H1; assumption)
    subgoal by auto
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
   done
qed

lemmas get_learned_count_learned_clss_countD =
  get_learned_count_learned_clss_countD2

end
