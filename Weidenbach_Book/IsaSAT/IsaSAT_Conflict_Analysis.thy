theory IsaSAT_Conflict_Analysis
  imports IsaSAT_Setup IsaSAT_VMTF
begin

paragraph \<open>Skip and resolve\<close>

definition maximum_level_removed_eq_count_dec where
  \<open>maximum_level_removed_eq_count_dec L S \<longleftrightarrow>
      get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L =
       count_decided (get_trail_wl S)\<close>

definition maximum_level_removed_eq_count_dec_pre where
  \<open>maximum_level_removed_eq_count_dec_pre =
     (\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> count_decided (get_trail_wl S) \<ge> 1)\<close>

definition maximum_level_removed_eq_count_dec_heur where
  \<open>maximum_level_removed_eq_count_dec_heur L S =
      RETURN (get_count_max_lvls_heur S > 1)\<close>

(*TODO Move*)
lemma get_maximum_level_eq_count_decided_iff:
  \<open>ya \<noteq> {#} \<Longrightarrow> get_maximum_level xa ya = count_decided xa \<longleftrightarrow> (\<exists>L \<in># ya. get_level xa L = count_decided xa)\<close>
  apply (rule iffI)
  defer
  subgoal
    using count_decided_ge_get_maximum_level[of xa]
    apply (auto dest!: multi_member_split dest: le_antisym simp: get_maximum_level_add_mset max_def)
    using le_antisym by blast
  subgoal
    using get_maximum_level_exists_lit_of_max_level[of ya xa]
    by auto
  done

lemma get_maximum_level_card_max_lvl_ge1:
  \<open>count_decided xa > 0 \<Longrightarrow> get_maximum_level xa ya = count_decided xa \<longleftrightarrow> card_max_lvl xa ya > 0\<close>
  apply (cases \<open>ya = {#}\<close>)
  subgoal by auto
  subgoal
    by (auto simp: card_max_lvl_def get_maximum_level_eq_count_decided_iff dest: multi_member_split
      dest!: multi_nonempty_split[of \<open>filter_mset _ _\<close>] filter_mset_eq_add_msetD
      simp flip: nonempty_has_size)
  done

lemma card_max_lvl_remove_hd_trail_iff:
  \<open>xa \<noteq> [] \<Longrightarrow> - lit_of (hd xa) \<in># ya \<Longrightarrow> 0 < card_max_lvl xa (remove1_mset (- lit_of (hd xa)) ya) \<longleftrightarrow> Suc 0 < card_max_lvl xa ya\<close>
  by (cases xa)
    (auto dest!: multi_member_split simp: card_max_lvl_add_mset)

(*END Move*)

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

lemma get_trail_wl_heur_def: \<open>get_trail_wl_heur = (\<lambda>(M, S). M)\<close>
  by (intro ext, rename_tac S, case_tac S) auto

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition lit_and_ann_of_propagated_st_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> (nat literal \<times> nat) nres\<close>
where
  \<open>lit_and_ann_of_propagated_st_heur = (\<lambda>((M, _, _, reasons, _), _). do {
     ASSERT(M \<noteq> [] \<and> atm_of (last M) < length reasons);
     RETURN (last M, reasons ! (atm_of (last M)))})\<close>

lemma lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
   \<open>(lit_and_ann_of_propagated_st_heur, mop_hd_trail_wl) \<in>
   [\<lambda>S. True]\<^sub>f twl_st_heur_conflict_ana \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lit_and_ann_of_propagated_st_heur_def mop_hd_trail_wl_def
  apply refine_rcg
  apply (auto simp: twl_st_heur_conflict_ana_def mop_hd_trail_wl_def mop_hd_trail_wl_pre_def
     mop_hd_trail_l_pre_def twl_st_l_def state_wl_l_def mop_hd_trail_pre_def last_rev hd_map
      lit_and_ann_of_propagated_st_def trail_pol_alt_def ann_lits_split_reasons_def
    intro!: ASSERT_leI ASSERT_refine_right simp flip: rev_map elim: is_propedE)
  apply (auto elim!: is_propedE)
  done

definition tl_state_wl_heur_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>tl_state_wl_heur_pre =
      (\<lambda>(M, N, D, WS, Q, ((A, m, fst_As, lst_As, next_search), to_remove), _). fst M \<noteq> [] \<and>
         tl_trailt_tr_pre M \<and>
	 vmtf_unset_pre (atm_of (last (fst M))) ((A, m, fst_As, lst_As, next_search), to_remove) \<and>
         atm_of (last (fst M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow>  the next_search < length A))\<close>

definition tl_state_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close> where
  \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, clvls). do {
       ASSERT(tl_state_wl_heur_pre (M, N, D, WS, Q, vmtf, clvls));
       RETURN (False, (tl_trailt_tr M, N, D, WS, Q, isa_vmtf_unset (atm_of (lit_of_last_trail_pol M)) vmtf, clvls))
  })\<close>

lemma tl_state_wl_heur_alt_def:
    \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, clvls). do {
       ASSERT(tl_state_wl_heur_pre (M, N, D, WS, Q, vmtf, clvls));
       let L = lit_of_last_trail_pol M;
       RETURN (False, (tl_trailt_tr M, N, D, WS, Q, isa_vmtf_unset (atm_of L) vmtf, clvls))
    })\<close>
  by (auto simp: tl_state_wl_heur_def Let_def intro!: ext)




lemma card_max_lvl_Cons:
  assumes \<open>no_dup (L # a)\<close> \<open>distinct_mset y\<close>\<open>\<not>tautology y\<close> \<open>\<not>is_decided L\<close>
  shows \<open>card_max_lvl (L # a) y =
    (if (lit_of L \<in># y \<or> -lit_of L \<in># y) \<and> count_decided a \<noteq> 0 then card_max_lvl a y + 1
    else card_max_lvl a y)\<close>
proof -
  have [simp]: \<open>count_decided a = 0 \<Longrightarrow> get_level a L = 0\<close> for L
    by (simp add: count_decided_0_iff)
  have [simp]: \<open>lit_of L \<notin># A \<Longrightarrow>
         - lit_of L \<notin># A \<Longrightarrow>
          {#La \<in># A. La \<noteq> lit_of L \<and> La \<noteq> - lit_of L \<longrightarrow> get_level a La = b#} =
          {#La \<in># A. get_level a La = b#}\<close> for A b
    apply (rule filter_mset_cong)
     apply (rule refl)
    by auto
  show ?thesis
    using assms by (auto simp: card_max_lvl_def get_level_cons_if tautology_add_mset
        atm_of_eq_atm_of
        dest!: multi_member_split)
qed

lemma card_max_lvl_tl:
  assumes \<open>a \<noteq> []\<close> \<open>distinct_mset y\<close>\<open>\<not>tautology y\<close> \<open>\<not>is_decided (hd a)\<close> \<open>no_dup a\<close>
   \<open>count_decided a \<noteq> 0\<close>
  shows \<open>card_max_lvl (tl a) y =
      (if (lit_of(hd a) \<in># y \<or> -lit_of(hd a) \<in># y)
        then card_max_lvl a y - 1 else card_max_lvl a y)\<close>
  using assms by (cases a) (auto simp: card_max_lvl_Cons)

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
   \<open>lit_of (hd a) \<notin># the at \<Longrightarrow>
       - lit_of (hd a) \<notin># the at \<Longrightarrow>
       \<not> is_decided (hd a) \<Longrightarrow>
       out_learned (tl a) at an \<longleftrightarrow> out_learned a at an\<close>
  by (cases a)  (auto simp: out_learned_def get_level_cons_if atm_of_eq_atm_of
      intro!: filter_mset_cong)

lemma mop_tl_state_wl_pre_tl_state_wl_heur_pre:
  \<open>(x, y) \<in> twl_st_heur_conflict_ana \<Longrightarrow> mop_tl_state_wl_pre y \<Longrightarrow> tl_state_wl_heur_pre x\<close>
  using tl_trailt_tr_pre[of \<open>get_trail_wl y\<close> \<open>get_trail_wl_heur x\<close> \<open>all_atms_st y\<close>]
  unfolding mop_tl_state_wl_pre_def tl_state_wl_heur_pre_def mop_tl_state_l_pre_def
    mop_tl_state_pre_def tl_state_wl_heur_pre_def
  apply (auto simp: twl_st_heur_conflict_ana_def state_wl_l_def twl_st_l_def trail_pol_alt_def
      rev_map[symmetric] last_rev hd_map
    intro!: vmtf_unset_pre'[where M = \<open>get_trail_wl y\<close>])
  apply (auto simp: neq_Nil_conv literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons phase_saving_def isa_vmtf_def
      vmtf_def
    dest!: multi_member_split)
  done

lemma mop_tl_state_wl_pre_simps:
  \<open>mop_tl_state_wl_pre ([], ax, ay, az, bga, NS, US, bh, bi) \<longleftrightarrow> False\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NS, US, bh, bi) \<Longrightarrow>
     lit_of (hd xa) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms ax (az + bga + NS + US))\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NS, US, bh, bi) \<Longrightarrow> lit_of (hd xa) \<notin># the ay\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NS, US, bh, bi) \<Longrightarrow> -lit_of (hd xa) \<notin># the ay\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, Some ay', az, bga, NS, US, bh, bi) \<Longrightarrow> lit_of (hd xa) \<notin># ay'\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, Some ay', az, bga, NS, US, bh, bi) \<Longrightarrow> -lit_of (hd xa) \<notin># ay'\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NS, US, bh, bi) \<Longrightarrow> is_proped (hd xa)\<close>
  \<open>mop_tl_state_wl_pre (xa, ax, ay, az, bga, NS, US, bh, bi) \<Longrightarrow> count_decided xa > 0\<close>
  unfolding mop_tl_state_wl_pre_def tl_state_wl_heur_pre_def mop_tl_state_l_pre_def
    mop_tl_state_pre_def tl_state_wl_heur_pre_def
  apply (auto simp: twl_st_heur_conflict_ana_def state_wl_l_def twl_st_l_def trail_pol_alt_def
      rev_map[symmetric] last_rev hd_map mset_take_mset_drop_mset' \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits
    simp flip: image_mset_union all_lits_def all_lits_alt_def2)
  done

abbreviation twl_st_heur_conflict_ana' :: \<open>nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
  \<open>twl_st_heur_conflict_ana' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur_conflict_ana \<and>
     length (get_clauses_wl_heur S) = r}\<close>

lemma tl_state_wl_heur_tl_state_wl:
   \<open>(tl_state_wl_heur, mop_tl_state_wl) \<in>
   [\<lambda>_. True]\<^sub>f twl_st_heur_conflict_ana' r \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r\<rangle>nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding tl_state_wl_heur_def mop_tl_state_wl_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  subgoal for x y a b aa ba ab bb ac bc ad bd ae be
    using mop_tl_state_wl_pre_tl_state_wl_heur_pre[of x y] by simp
  subgoal
    apply (auto simp: twl_st_heur_conflict_ana_def tl_state_wl_heur_def tl_state_wl_def vmtf_unset_vmtf_tl
         mop_tl_state_wl_pre_simps lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id]
         card_max_lvl_tl tl_state_out_learned
      dest: no_dup_tlD
      intro!: tl_trail_tr[THEN fref_to_Down_unRET] isa_vmtf_tl_isa_vmtf)
  apply (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id])
  apply (auto simp: lit_of_hd_trail_def mop_tl_state_wl_pre_simps counts_maximum_level_def)
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

definition update_confl_tl_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_confl_tl_wl_heur = (\<lambda>L C (M, N, (b, (n, xs)), Q, W, vm, clvls, cach, lbd, outl, stats). do {
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_is_valid_clause_idx N C);
      ((b, (n, xs)), clvls, lbd, outl) \<leftarrow>
        if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C (b, (n, xs)) clvls lbd outl
        else isa_resolve_merge_conflict_gt2 M N C (b, (n, xs)) clvls lbd outl;
      ASSERT(curry lookup_conflict_remove1_pre L (n, xs) \<and> clvls \<ge> 1);
      let (n, xs) = lookup_conflict_remove1 L (n, xs);
      ASSERT(arena_act_pre N C);
      let N = mark_used N C;
      ASSERT(arena_act_pre N C);
      let N = arena_incr_act N C;
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      RETURN (False, (tl_trailt_tr M, N, (b, (n, xs)), Q, W, isa_vmtf_unset L' vm,
          clvls - 1, cach, lbd, outl, stats))
   })\<close>

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
      L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<and>
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


  have stupid: "K \<in># removeAll_mset L D \<longleftrightarrow> K \<noteq> L \<and> K \<in># D" for K L D
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
    apply (subst (2) subset_mset.sup.commute)
    using uL_D hd nempty uL_C dist_C apply (cases \<open>get_trail_wl S\<close>; auto simp: dest!: multi_member_split)
    by (metis (no_types, hide_lams) \<open>remove1_mset (- L) (the (get_conflict_wl S)) \<union># remove1_mset L (mset (get_clauses_wl S \<propto> C)) = the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C) - {#L, - L#}\<close> add_mset_commute add_mset_diff_bothsides add_mset_remove_trivial set_mset_mset subset_mset.sup_commute sup_union_left1)


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
           auto dest!:  simp: card_max_lvl_Cons card_max_lvl_add_mset subset_mset.sup_commute[of _ \<open>remove1_mset _ _\<close> ]
             subset_mset.sup_commute[of _ \<open>mset _\<close>] tautology_add_mset remove1_mset_union_distrib1 remove1_mset_union_distrib2)
    by (simp add: distinct_mset_remove1_All[of \<open>mset (get_clauses_wl S \<propto> C)\<close>])


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

(*TODO*)
lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_all_atms_self[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms ca NUE) {#mset (fst x). x \<in># ran_m ca#}\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
    all_atms_def all_lits_def in_all_lits_of_mm_ain_atms_of_iff)

lemma mset_as_position_remove3:
  \<open>mset_as_position xs (D - {#L#}) \<Longrightarrow> atm_of L < length xs \<Longrightarrow> distinct_mset D \<Longrightarrow>
   mset_as_position (xs[atm_of L := None]) (D - {#L, -L#})\<close>
  using mset_as_position_remove2[of xs \<open>D - {#L#}\<close> \<open>L\<close>] mset_as_position_tautology[of xs \<open>remove1_mset L D\<close>]
    mset_as_position_distinct_mset[of xs \<open>remove1_mset L D\<close>]
  by (cases \<open>L \<in># D\<close>; cases \<open>-L \<in># D\<close>)
    (auto dest!: multi_member_split simp: minus_notin_trivial ac_simps add_mset_eq_add_mset tautology_add_mset)

lemma update_confl_tl_wl_heur_update_confl_tl_wl:
  \<open>(uncurry2 (update_confl_tl_wl_heur), uncurry2 mop_update_confl_tl_wl) \<in>
  [\<lambda>_. True]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r\<rangle>nres_rel\<close>
proof -
  have mop_update_confl_tl_wl_alt_def: \<open>mop_update_confl_tl_wl = (\<lambda>L C (M, N, D, NE, UE, WS, Q). do {
      ASSERT(update_confl_tl_wl_pre L C (M, N, D, NE, UE, WS, Q));
      D \<leftarrow> RETURN (resolve_cls_wl' (M, N, D, NE, UE, WS, Q) C L);
      N \<leftarrow> RETURN N;
      N \<leftarrow> RETURN N;
      RETURN (False, (tl M, N, Some D, NE, UE, WS, Q))
    })\<close>
  by (auto simp: mop_update_confl_tl_wl_def update_confl_tl_wl_def intro!: ext)
  define rr where
  \<open>rr L M N C b n xs clvls lbd outl = do {
          ((b, (n, xs)), clvls, lbd, outl) \<leftarrow>
            if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C (b, (n, xs)) clvls lbd outl
           else isa_resolve_merge_conflict_gt2 M N C (b, (n, xs)) clvls lbd outl;
         ASSERT(curry lookup_conflict_remove1_pre L (n, xs) \<and> clvls \<ge> 1);
         let (nxs) = lookup_conflict_remove1 L (n, xs);
         RETURN ((b, (nxs)), clvls, lbd, outl) }\<close>
    for  L M N C b n xs clvls lbd outl
  have update_confl_tl_wl_heur_alt_def:
    \<open>update_confl_tl_wl_heur = (\<lambda>L C (M, N, (b, (n, xs)), Q, W, vm, clvls, cach, lbd, outl, stats). do {
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_is_valid_clause_idx N C);
      ((b, (n, xs)), clvls, lbd, outl) \<leftarrow> rr L M N C b n xs clvls lbd outl;
      ASSERT(arena_act_pre N C);
      let N = mark_used N C;
      ASSERT(arena_act_pre N C);
      let N = arena_incr_act N C;
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      RETURN (False, (tl_trailt_tr M, N, (b, (n, xs)), Q, W, isa_vmtf_unset L' vm,
          clvls - 1, cach, lbd, outl, stats))
   })\<close>
  by (auto simp: update_confl_tl_wl_heur_def Let_def rr_def intro!: ext bind_cong[OF refl])

note [[goals_limit=1]]
  have rr: \<open>(((x1g, x2g), x1h, x1i, (x1k, x1l, x2k), x1m, x1n, x1p, x1q, x1r,
      x1s, x1t, m, n, p, q, ra, s, t),
     (x1, x2), x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r \<Longrightarrow>
    CLS = ((x1, x2), x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) \<Longrightarrow>
    CLS' =
    ((x1g, x2g), x1h, x1i, (x1k, x1l, x2k), x1m, x1n, x1p, x1q, x1r,
     x1s, x1t, m, n, p, q, ra, s, t) \<Longrightarrow>
    update_confl_tl_wl_pre x1 x2 (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) \<Longrightarrow>
    1 \<le> x1q \<Longrightarrow>
    arena_is_valid_clause_idx x1i x2g \<Longrightarrow>
    rr x1g x1h x1i x2g x1k x1l x2k x1q x1s x1t
    \<le> \<Down> {((C, clvls, lbd, outl), D). (C, Some D) \<in> option_lookup_clause_rel (all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f))  \<and>
          clvls = card_max_lvl x1a (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c)  \<and>
         out_learned x1a (Some (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c)) (outl) \<and>
         size (remove1_mset x1 (mset (x1b \<propto> x2)) \<union># the x1c) =
           size ((mset (x1b \<propto> x2)) \<union># the x1c - {#x1, -x1#}) + Suc 0 \<and>
        D = resolve_cls_wl' (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) x2 x1}
       (RETURN (resolve_cls_wl' (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) x2 x1))\<close>
     for m n p q ra s t x1 x2 x1a x1b x1c x1d x1e x1f x2f x1g x2g x1h x1i x1k
       x1l x2k x1m x1n x1p x1q x1r x1s x1t CLS CLS' NS US
     unfolding rr_def
     apply (refine_vcg lhs_step_If)
     apply (rule isasat_lookup_merge_eq2_lookup_merge_eq2[where
        vdom = \<open>set (get_vdom (x1h, x1i, (x1k, x1l, x2k), x1m, x1n, x1p, x1q, x1r,
      x1s, x1t, m, n, p, q, ra, s, t))\<close> and M = x1a and  N = x1b and C = x1c and
      \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f) \<close>, THEN order_trans])
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre' simp: update_confl_tl_wl_pre'_def)
     subgoal by auto
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
         simp: update_confl_tl_wl_pre'_def arena_lifting twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def merge_conflict_m_eq2_def conc_fun_SPEC lookup_conflict_remove1_pre_def
           atms_of_def
           option_lookup_clause_rel_def lookup_clause_rel_def resolve_cls_wl'_def lookup_conflict_remove1_def
           remove1_mset_union_distrib1 remove1_mset_union_distrib2 subset_mset.sup.commute[of _ \<open>remove1_mset _ _\<close>]
          subset_mset.sup.commute[of _ \<open>mset (_ \<propto> _)\<close>]
         intro!: mset_as_position_remove3
         intro!: ASSERT_leI)
     done
    subgoal
      apply (subst (asm) arena_lifting(4)[where vdom = \<open>set p\<close> and N = x1b, symmetric])
      subgoal by (auto simp: twl_st_heur_conflict_ana_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def)
      apply (rule isa_resolve_merge_conflict_gt2[where
         \<A> = \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, NS, US, x1f, x2f)\<close> and vdom = \<open>set p\<close>,
       THEN fref_to_Down_curry6, of x1a x1b x2g x1c x1q x1s x1t,
       THEN order_trans])
     subgoal unfolding merge_conflict_m_pre_def
       by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def twl_st_heur_conflict_ana_def counts_maximum_level_def)
     subgoal by (auto simp: twl_st_heur_conflict_ana_def)
     subgoal
        by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def conc_fun_SPEC lookup_conflict_remove1_pre_def atms_of_def
           option_lookup_clause_rel_def lookup_clause_rel_def resolve_cls_wl'_def
           merge_conflict_m_def lookup_conflict_remove1_def subset_mset.sup.commute[of _ \<open>mset (_ \<propto> _)\<close>]
           remove1_mset_union_distrib1 remove1_mset_union_distrib2
         intro!: mset_as_position_remove3
         intro!: ASSERT_leI)
      done
    done

 show ?thesis
    supply [[goals_limit = 1]]
    supply RETURN_as_SPEC_refine[refine2 del]
       update_confl_tl_wl_pre_update_confl_tl_wl_pre'[dest!]
    apply (intro frefI nres_relI)
    subgoal for CLS' CLS
      apply (cases CLS'; cases CLS; hypsubst+)
      unfolding uncurry_def update_confl_tl_wl_heur_alt_def comp_def Let_def
        update_confl_tl_wl_def mop_update_confl_tl_wl_alt_def prod.case
      apply (refine_rcg; remove_dummy_vars)
      subgoal
        by (auto simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
            RES_RETURN_RES RETURN_def counts_maximum_level_def)
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def)
      apply (rule rr; assumption)
      subgoal by (simp add: arena_act_pre_def)
      subgoal using arena_act_pre_mark_used by blast
      subgoal by (auto dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
         simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def
           intro!: vmtf_unset_pre')
      subgoal for m n p q ra s t ha ia ja x1 x2 x1a x1b x1c x1d x1e x1f x1g x2g x1h x1i
       x1k x1l x2k x1m x1n x1o x1p x1q x1r x1s x1t D x1v x1w x2v x1x x1y
         by (rule tl_trailt_tr_pre[of x1a _ \<open>all_atms_st (x1a, x1b, x1c, x1d, x1e, x1f, ha, ia, ja)\<close>])
           (clarsimp_all dest!: update_confl_tl_wl_pre_update_confl_tl_wl_pre'
             simp: update_confl_tl_wl_pre'_def arena_is_valid_clause_idx_def twl_st_heur_conflict_ana_def
             intro!: tl_trailt_tr_pre)
      subgoal by (clarsimp simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre'_def
           valid_arena_arena_incr_act valid_arena_mark_used subset_mset.sup.commute[of _ \<open>remove1_mset _ _\<close>]
          tl_trail_tr[THEN fref_to_Down_unRET] resolve_cls_wl'_def isa_vmtf_tl_isa_vmtf no_dup_tlD
          counts_maximum_level_def)
    done
  done
qed

lemma phase_saving_le: \<open>phase_saving \<A> \<phi> \<Longrightarrow> A \<in># \<A> \<Longrightarrow> A < length \<phi>\<close>
   \<open>phase_saving \<A> \<phi> \<Longrightarrow> B \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of B < length \<phi>\<close>
  by (auto simp: phase_saving_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

lemma isa_vmtf_le:
  \<open>((a, b), M) \<in> isa_vmtf \<A> M' \<Longrightarrow> A \<in># \<A> \<Longrightarrow> A < length a\<close>
  \<open>((a, b), M) \<in> isa_vmtf \<A> M' \<Longrightarrow> B \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of B < length a\<close>
  by (auto simp:  isa_vmtf_def vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

lemma isa_vmtf_next_search_le:
  \<open>((a, b, c, c', Some d), M) \<in> isa_vmtf \<A> M' \<Longrightarrow> d < length a\<close>
  by (auto simp: isa_vmtf_def vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

lemma trail_pol_nempty: \<open>\<not>(([], aa, ab, ac, ad, b), L # ys) \<in> trail_pol \<A>\<close>
  by (auto simp: trail_pol_def ann_lits_split_reasons_def)

definition is_decided_hd_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>S. is_None (snd (last_trail_pol (get_trail_wl_heur S))))\<close>

lemma is_decided_hd_trail_wl_heur_hd_get_trail:
  \<open>(RETURN o is_decided_hd_trail_wl_heur, RETURN o (\<lambda>M. is_decided (hd (get_trail_wl M))))
   \<in> [\<lambda>M. get_trail_wl M \<noteq> []]\<^sub>f twl_st_heur_conflict_ana' r \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
   by (intro frefI nres_relI)
     (auto simp: is_decided_hd_trail_wl_heur_def twl_st_heur_conflict_ana_def neq_Nil_conv
        trail_pol_def ann_lits_split_reasons_def is_decided_no_proped_iff last_trail_pol_def
      split: option.splits)


definition is_decided_hd_trail_wl_heur_pre where
  \<open>is_decided_hd_trail_wl_heur_pre =
    (\<lambda>S. fst (get_trail_wl_heur S) \<noteq> [] \<and> last_trail_pol_pre (get_trail_wl_heur S))\<close>

definition skip_and_resolve_loop_wl_D_heur_inv where
 \<open>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0' =
    (\<lambda>(brk, S'). \<exists>S S\<^sub>0. (S', S) \<in> twl_st_heur_conflict_ana \<and> (S\<^sub>0', S\<^sub>0) \<in> twl_st_heur_conflict_ana \<and>
      skip_and_resolve_loop_wl_inv S\<^sub>0 brk S \<and>
       length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S\<^sub>0'))\<close>

definition update_confl_tl_wl_heur_pre
   :: \<open>(nat \<times> nat literal) \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
\<open>update_confl_tl_wl_heur_pre =
  (\<lambda>((i, L), (M, N, D, W, Q, ((A, m, fst_As, lst_As, next_search), _), clvls, cach, lbd,
        outl, _)).
      i > 0 \<and>
      (fst M) \<noteq> [] \<and>
      atm_of ((last (fst M))) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = (last (fst M))
      )\<close>

definition lit_and_ann_of_propagated_st_heur_pre where
  \<open>lit_and_ann_of_propagated_st_heur_pre = (\<lambda>((M, _, _, reasons, _), _). atm_of (last M) < length reasons \<and> M \<noteq> [])\<close>

definition atm_is_in_conflict_st_heur_pre
   :: \<open>nat literal \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>atm_is_in_conflict_st_heur_pre  = (\<lambda>(L, (M,N,(_, (_, D)), _)). atm_of L < length D)\<close>

definition skip_and_resolve_loop_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
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
                update_confl_tl_wl_heur L C S}
              else
                RETURN (True, S)
            }
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>



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
     apply (rule atm_in_conflict_lookup_pre)
     unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits[symmetric]
     apply assumption+
     done
  subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x1e x2d x2e
    apply (subst atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id, of \<open>all_atms_st x2\<close>  \<open>atm_of x1\<close> \<open>the (get_conflict_wl (snd y))\<close>])
    apply (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def)[]
    apply (auto simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def option_lookup_clause_rel_def)[]
    apply (simp add: atm_in_conflict_def atm_of_in_atms_of_iff)
    done
  done
qed

lemma skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D:
  \<open>(skip_and_resolve_loop_wl_D_heur, skip_and_resolve_loop_wl)
    \<in> twl_st_heur_conflict_ana' r \<rightarrow>\<^sub>f \<langle>twl_st_heur_conflict_ana' r\<rangle>nres_rel\<close>
proof -
  have H[refine0]: \<open>(x, y) \<in> twl_st_heur_conflict_ana \<Longrightarrow>
           ((False, x), False, y)
           \<in> bool_rel \<times>\<^sub>f
              twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x))\<close> for x y
    by auto

  show ?thesis
    supply [[goals_limit=1]]
    unfolding skip_and_resolve_loop_wl_D_heur_def skip_and_resolve_loop_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
        update_confl_tl_wl_heur_update_confl_tl_wl[THEN fref_to_Down_curry2, unfolded comp_def]
        maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec
          [THEN fref_to_Down_curry] lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st[THEN fref_to_Down]
       tl_state_wl_heur_tl_state_wl[THEN fref_to_Down]
       atm_is_in_conflict_st_heur_is_in_conflict_st[THEN fref_to_Down_curry])
   subgoal by fast
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
    subgoal by auto
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

definition (in -) get_count_max_lvls_code where
  \<open>get_count_max_lvls_code = (\<lambda>(_, _, _, _, _, _, _, clvls, _). clvls)\<close>


lemma is_decided_hd_trail_wl_heur_alt_def:
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>(M, _). is_None (snd (last_trail_pol M)))\<close>
  by (auto intro!: ext simp: is_decided_hd_trail_wl_heur_def)

lemma atm_of_in_atms_of: \<open>atm_of x \<in> atms_of C \<longleftrightarrow> x \<in># C \<or> -x \<in># C\<close>
  using atm_of_notin_atms_of_iff by blast

definition atm_is_in_conflict where
  \<open>atm_is_in_conflict L D \<longleftrightarrow> atm_of L \<in> atms_of (the D)\<close>

fun is_in_option_lookup_conflict where
  is_in_option_lookup_conflict_def[simp del]:
  \<open>is_in_option_lookup_conflict L (a, n, xs) \<longleftrightarrow> is_in_lookup_conflict (n, xs) L\<close>


lemma is_in_option_lookup_conflict_atm_is_in_conflict_iff:
  assumes
    \<open>ba \<noteq> None\<close> and aa: \<open>aa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and uaa: \<open>- aa \<notin># the ba\<close> and
    \<open>((b, c, d), ba) \<in> option_lookup_clause_rel \<A>\<close>
  shows \<open>is_in_option_lookup_conflict aa (b, c, d) =
         atm_is_in_conflict aa ba\<close>
proof -
  obtain yb where ba[simp]: \<open>ba = Some yb\<close>
    using assms by auto

  have map: \<open>mset_as_position d yb\<close> and le: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length d\<close> and [simp]: \<open>\<not>b\<close>
    using assms by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def)
  have aa_d: \<open>atm_of aa < length d\<close> and uaa_d: \<open>atm_of (-aa) < length d\<close>
    using le aa by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  from mset_as_position_in_iff_nth[OF map aa_d]
  have 1: \<open>(aa \<in># yb) = (d ! atm_of aa = Some (is_pos aa))\<close>
    .

  from mset_as_position_in_iff_nth[OF map uaa_d] have 2: \<open>(d ! atm_of aa \<noteq> Some (is_pos (-aa)))\<close>
    using uaa by simp

  then show ?thesis
    using uaa 1 2
    by (auto simp: is_in_lookup_conflict_def is_in_option_lookup_conflict_def atm_is_in_conflict_def
        atm_of_in_atms_of is_neg_neg_not_is_neg
        split: option.splits)
qed

lemma is_in_option_lookup_conflict_atm_is_in_conflict:
  \<open>(uncurry (RETURN oo is_in_option_lookup_conflict), uncurry (RETURN oo atm_is_in_conflict))
   \<in> [\<lambda>(L, D). D \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> -L \<notin># the D]\<^sub>f
      Id \<times>\<^sub>f option_lookup_clause_rel \<A> \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  by (simp add: is_in_option_lookup_conflict_atm_is_in_conflict_iff[of _ _ \<A>])

lemma is_in_option_lookup_conflict_alt_def:
  \<open>RETURN oo is_in_option_lookup_conflict =
     RETURN oo (\<lambda>L (_, n, xs). is_in_lookup_conflict (n, xs) L)\<close>
  by (auto intro!: ext simp: is_in_option_lookup_conflict_def)


lemma skip_and_resolve_loop_wl_DI:
  assumes
    \<open>skip_and_resolve_loop_wl_D_heur_inv S (b, T)\<close>
  shows \<open>is_decided_hd_trail_wl_heur_pre T\<close>
  using assms apply -
  unfolding skip_and_resolve_loop_wl_inv_def skip_and_resolve_loop_inv_l_def skip_and_resolve_loop_inv_def
     skip_and_resolve_loop_wl_D_heur_inv_def is_decided_hd_trail_wl_heur_pre_def
  apply (subst (asm) case_prod_beta)+
  unfolding prod.case
  apply normalize_goal+
  apply (clarsimp simp: twl_st_heur_def state_wl_l_def twl_st_l_def twl_st_heur_conflict_ana_def
    trail_pol_alt_def last_trail_pol_pre_def last_rev hd_map literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def simp flip: rev_map
    dest: multi_member_split)
  apply (case_tac x)
  apply (clarsimp_all dest!: multi_member_split simp: ann_lits_split_reasons_def)
  done

lemma isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv:
  \<open>isasat_fast x \<Longrightarrow>
       skip_and_resolve_loop_wl_D_heur_inv x
        (False, a2') \<Longrightarrow> isasat_fast a2'\<close>
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def isasat_fast_def
  by auto

end