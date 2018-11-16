theory IsaSAT_Conflict_Analysis
  imports IsaSAT_Setup IsaSAT_VMTF
begin


paragraph \<open>Skip and resolve\<close>

lemma get_maximum_level_remove_count_max_lvls:
  assumes L: \<open>L = -lit_of (hd M)\<close> and LD: \<open>L \<in># D\<close> and M_nempty: \<open>M \<noteq> []\<close>
  shows \<open>get_maximum_level_remove M D L = count_decided M \<longleftrightarrow>
       (count_decided M = 0 \<or> card_max_lvl M D > 1)\<close>
  (is \<open>?max \<longleftrightarrow> ?count\<close>)
proof
  assume H: ?max
  let ?D = \<open>remove1_mset L D\<close>
  have [simp]: \<open>get_level M L = count_decided M\<close>
    using M_nempty L by (cases M) auto
  define MD where \<open>MD \<equiv> {#L \<in># D. get_level M L = count_decided M#}\<close>
  show ?count
  proof (cases \<open>?D = {#}\<close>)
    case True
    then show ?thesis
      using LD H by (auto dest!: multi_member_split simp: get_maximum_level_remove_def)
  next
    case False
    then obtain L' where
      \<open>get_level M L' = get_maximum_level_remove M D L\<close> and L'_D: \<open>L' \<in># ?D\<close>
      using get_maximum_level_exists_lit_of_max_level[of \<open>remove1_mset L D\<close>]
      unfolding get_maximum_level_remove_def by blast
    then have \<open>L' \<in># {#L \<in># D. get_level M L = count_decided M#}\<close>
      using H by (auto dest: in_diffD simp: get_maximum_level_remove_def)
    moreover have \<open>L \<in># {#L \<in># D. get_level M L = count_decided M#}\<close>
      using LD by auto
    ultimately have \<open>{#L, L'#} \<subseteq># MD\<close>
      using L'_D LD by (cases \<open>L = L'\<close>)
        (auto dest!: multi_member_split simp: MD_def add_mset_eq_add_mset)
    from size_mset_mono[OF this] show ?thesis
      unfolding card_max_lvl_def H MD_def[symmetric]
      by auto
  qed
next
  let ?D = \<open>remove1_mset L D\<close>
  have [simp]: \<open>get_level M L = count_decided M\<close>
    using M_nempty L by (cases M) auto
  define MD where \<open>MD \<equiv> {#L \<in># D. get_level M L = count_decided M#}\<close>
  have L_MD: \<open>L \<in># MD\<close>
    using LD unfolding MD_def by auto
  assume ?count
  then consider
    (lev_0) \<open>count_decided M = 0\<close> |
    (count) \<open>card_max_lvl M D > 1\<close>
    by (cases \<open>D \<noteq> {#L#}\<close>) auto
  then show ?max
  proof cases
    case lev_0
    then show ?thesis
      using count_decided_ge_get_maximum_level[of M ?D]
      by (auto simp: get_maximum_level_remove_def)
  next
    case count
    then obtain L' where
      \<open>L' \<in># MD\<close> and
      LL': \<open>{#L, L'#} \<subseteq># MD\<close>
      using L_MD
      unfolding get_maximum_level_remove_def card_max_lvl_def MD_def[symmetric]
      by (force simp: nonempty_has_size[symmetric]
          dest!: multi_member_split multi_nonempty_split)
    then have \<open>get_level M L' = count_decided M\<close>
      unfolding MD_def by auto
    moreover have \<open>L' \<in># remove1_mset L D\<close>
    proof -
      have \<open>{#L, L'#} \<subseteq># D\<close>
        using LL' unfolding MD_def
        by (meson multiset_filter_subset subset_mset.dual_order.trans)
      then show ?thesis
        by (metis (no_types) LD insert_DiffM mset_subset_eq_add_mset_cancel single_subset_iff)
    qed
    ultimately have \<open>get_maximum_level M (remove1_mset L D) \<ge> count_decided M\<close>
      using get_maximum_level_ge_get_level[of L' ?D M]
      by simp
    then show ?thesis
      using count_decided_ge_get_maximum_level[of M ?D]
      by (auto simp: get_maximum_level_remove_def)
  qed
qed


definition maximum_level_removed_eq_count_dec where
  \<open>maximum_level_removed_eq_count_dec L S \<longleftrightarrow>
      get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L =
       count_decided (get_trail_wl S)\<close>

definition maximum_level_removed_eq_count_dec_heur where
  \<open>maximum_level_removed_eq_count_dec_heur L S \<longleftrightarrow>
      get_count_max_lvls_heur S > one_uint32_nat\<close>

definition maximum_level_removed_eq_count_dec_pre where
  \<open>maximum_level_removed_eq_count_dec_pre =
     (\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> count_decided (get_trail_wl S) \<ge> 1)\<close>

lemma maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec:
  \<open>(uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur),
      uncurry (RETURN oo maximum_level_removed_eq_count_dec)) \<in>
   [maximum_level_removed_eq_count_dec_pre]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur_conflict_ana \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using get_maximum_level_remove_count_max_lvls[of \<open>fst x\<close> \<open>get_trail_wl (snd y)\<close>
      \<open>the (get_conflict_wl (snd y))\<close>]
    by (cases x)
       (auto simp: count_decided_st_def counts_maximum_level_def twl_st_heur_conflict_ana_def
     maximum_level_removed_eq_count_dec_heur_def maximum_level_removed_eq_count_dec_def
     maximum_level_removed_eq_count_dec_pre_def)
  done

lemma get_trail_wl_heur_def: \<open>get_trail_wl_heur = (\<lambda>(M, S). M)\<close>
  by (intro ext, rename_tac S, case_tac S) auto

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition lit_and_ann_of_propagated_st_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<times> nat\<close>
where
  \<open>lit_and_ann_of_propagated_st_heur = (\<lambda>((M, _, _, reasons, _), _). (last M, reasons ! (atm_of (last M))))\<close>

lemma mark_of_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in>
    [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
  by (sep_auto simp: nat_ann_lit_rel_def)+


lemma mark_of_fast_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in>
    [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
proof -
  have 1: \<open>option_assn (\<lambda>a c. \<up> ((c, a) \<in> uint64_nat_rel)) = pure (\<langle>uint64_nat_rel\<rangle>option_rel)\<close>
    unfolding option_assn_pure_conv[symmetric]
    by (auto simp: pure_def)
  show ?thesis
    apply sepref_to_hoare
    unfolding 1
    apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
       apply (sep_auto simp: br_def)
      apply (sep_auto simp: nat_ann_lit_rel_def uint64_nat_rel_def br_def
        ann_lit_of_pair_if cong: )+
     apply (sep_auto simp: hr_comp_def)
    apply (sep_auto simp: hr_comp_def uint64_nat_rel_def br_def)
     apply (auto simp: nat_ann_lit_rel_def elim: option_relE)[]
    apply (auto simp: ent_refl_true)
    done
qed

lemma lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
   \<open>(RETURN o lit_and_ann_of_propagated_st_heur, RETURN o lit_and_ann_of_propagated_st) \<in>
   [\<lambda>S. is_proped (hd (get_trail_wl S)) \<and> get_trail_wl S \<noteq> []]\<^sub>f twl_st_heur_conflict_ana \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (rename_tac x y; case_tac x; case_tac y; case_tac \<open>hd (fst y)\<close>; case_tac \<open>fst y\<close>;
     case_tac \<open>fst (fst x)\<close> rule: rev_cases)
   (auto simp: twl_st_heur_conflict_ana_def lit_and_ann_of_propagated_st_heur_def
      lit_and_ann_of_propagated_st_def trail_pol_def ann_lits_split_reasons_def)

lemma twl_st_heur_conflict_ana_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
  \<open>(x, y) \<in> twl_st_heur_conflict_ana \<Longrightarrow> is_proped (hd (get_trail_wl y)) \<Longrightarrow> get_trail_wl y \<noteq> [] \<Longrightarrow>
    lit_and_ann_of_propagated_st_heur x = lit_and_ann_of_propagated_st y\<close>
  using lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st[THEN fref_to_Down_unRET,
    of y x]
  by auto

definition tl_state_wl_heur_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>tl_state_wl_heur_pre =
      (\<lambda>(M, N, D, WS, Q, ((A, m, fst_As, lst_As, next_search), to_remove), \<phi>, _). fst M \<noteq> [] \<and>
         tl_trailt_tr_pre M \<and>
	 vmtf_unset_pre (atm_of (last (fst M))) ((A, m, fst_As, lst_As, next_search), to_remove) \<and>
         atm_of (last (fst M)) < length \<phi> \<and>
         atm_of (last (fst M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow>  the next_search < length A))\<close>

definition tl_state_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, \<phi>, clvls).
       (tl_trailt_tr M, N, D, WS, Q, isa_vmtf_unset (atm_of (lit_of_last_trail_pol M)) vmtf, \<phi>, clvls))\<close>

lemma tl_state_wl_heur_alt_def:
    \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, \<phi>, clvls).
      (let L = lit_of_last_trail_pol M in
       (tl_trailt_tr M, N, D, WS, Q, isa_vmtf_unset (atm_of L) vmtf, \<phi>, clvls)))\<close>
  by (auto simp: tl_state_wl_heur_def Let_def)


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

lemma tl_state_wl_heur_tl_state_wl:
   \<open>(RETURN o tl_state_wl_heur, RETURN o tl_state_wl) \<in>
   [tl_state_wl_pre]\<^sub>f twl_st_heur_conflict_ana \<rightarrow> \<langle>twl_st_heur_conflict_ana\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: twl_st_heur_conflict_ana_def tl_state_wl_heur_def tl_state_wl_def vmtf_unset_vmtf_tl
       in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff phase_saving_def counts_maximum_level_def
       card_max_lvl_tl tl_state_wl_pre_def tl_state_out_learned neq_Nil_conv
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons all_atms_def[symmetric] card_max_lvl_Cons
     dest: no_dup_tlD
     intro!: tl_trail_tr[THEN fref_to_Down_unRET] isa_vmtf_tl_isa_vmtf
     simp: lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id]
     intro: tl_state_out_learned[THEN iffD2, of \<open>Cons _ _\<close>, simplified])
  apply (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id])
  apply (auto simp: lit_of_hd_trail_def)[3]
  apply (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id])
  apply (auto simp: lit_of_hd_trail_def)[3]
  done

definition (in -) get_max_lvl_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>get_max_lvl_st S L = get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L\<close>

definition update_confl_tl_wl_heur
  :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_confl_tl_wl_heur = (\<lambda>C L (M, N, (b, (n, xs)), Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats). do {
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(curry6 isa_set_lookup_conflict_aa_pre M N C (b, (n, xs)) clvls lbd outl);
      ((b, (n, xs)), clvls, lbd, outl) \<leftarrow> isa_resolve_merge_conflict M N C (b, (n, xs)) clvls lbd outl;
      ASSERT(curry lookup_conflict_remove1_pre L (n, xs) \<and> clvls \<ge> 1);
      let (n, xs) = lookup_conflict_remove1 L (n, xs);
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      RETURN (False, (tl_trailt_tr M, N, (b, (n, xs)), Q, W, isa_vmtf_unset L' vm,
          \<phi>, fast_minus clvls one_uint32_nat, cach, lbd, outl, stats))
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

definition update_confl_tl_wl_pre where
  \<open>update_confl_tl_wl_pre = (\<lambda>((C, L), S).
      C \<in># dom_m (get_clauses_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and>
      - L \<in># the (get_conflict_wl S) \<and>
      (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and>
      L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<and>
      is_proped (hd (get_trail_wl S)) \<and>
      C > 0 \<and>
      card_max_lvl (get_trail_wl S) (the (get_conflict_wl S)) \<ge> 1 \<and>
      distinct_mset (the (get_conflict_wl S)) \<and>
      - L \<notin> set (get_clauses_wl S \<propto> C) \<and>
      (length (get_clauses_wl S \<propto> C) > 2 \<longrightarrow> 
        L \<notin> set (tl (get_clauses_wl S \<propto> C))) \<and>
      L \<in> set (watched_l (get_clauses_wl S \<propto> C)) \<and>
      distinct (get_clauses_wl S \<propto> C) \<and>
      \<not>tautology (the (get_conflict_wl S)) \<and>
      \<not>tautology (mset (get_clauses_wl S \<propto> C)) \<and>
      \<not>tautology (remove1_mset L (remove1_mset (- L)
        ((the (get_conflict_wl S) \<union># mset (get_clauses_wl S \<propto> C))))) \<and>
      count_decided (get_trail_wl S) > 0 \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (the (get_conflict_wl S)) \<and>
      literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) (get_trail_wl S)
    )\<close>

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

abbreviation twl_st_heur_conflict_ana' where
  \<open>twl_st_heur_conflict_ana' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur_conflict_ana \<and>
     length (get_clauses_wl_heur S) = r}\<close>

lemma update_confl_tl_wl_heur_update_confl_tl_wl:
  \<open>(uncurry2 (update_confl_tl_wl_heur), uncurry2 (RETURN ooo update_confl_tl_wl)) \<in>
  [update_confl_tl_wl_pre]\<^sub>f
   nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur_conflict_ana' r \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r\<rangle>nres_rel\<close>
proof -
  have H: \<open>isa_resolve_merge_conflict ba c a (aa, ab, bb) i k ag
        \<le> SPEC
          (\<lambda>x. (case x of
                (x, xa) \<Rightarrow>
                  (case x of
                    (bb, n, xs) \<Rightarrow>
                      \<lambda>(clvls, lbd, outl). do {
                          _ \<leftarrow> ASSERT (curry lookup_conflict_remove1_pre b (n, xs) \<and>
                             1 \<le> clvls);
                          let (n, xs) = lookup_conflict_remove1 b (n, xs);
                          ASSERT(vmtf_unset_pre (atm_of b) ivmtf);
			  ASSERT(tl_trailt_tr_pre ba);
                          RETURN
                            (False, tl_trailt_tr ba, c, (bb, n, xs), e, f, isa_vmtf_unset (atm_of b) ivmtf,
                            h, fast_minus clvls one_uint32_nat, j,
                            lbd, outl, (ah, ai, aj, be), ak, al, am, an, bf)
                        })
                    xa)
                \<le> \<Down> (bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r)
                  (RETURN
                    (let D = resolve_cls_wl' (baa, ca, da, ea, fa, ga, ha) ao bg
                      in (False, tl baa, ca, Some D, ea, fa, ga, ha))))\<close>
    if
      inv: \<open>update_confl_tl_wl_pre ((ao, bg), baa, ca, da, ea, fa, ga, ha)\<close> and
      rel: \<open>(((a, b), ba, c, (aa, ab, bb), e, f, ivmtf, h, i, j,
        k, ag, (ah, ai, aj, be), ak, al, am, an, bf),
        (ao, bg), baa, ca, da, ea, fa, ga, ha)
      \<in> nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r\<close> and
      CLS[simp]: \<open>CLS = ((ao, bg), baa, ca, da, ea, fa, ga, ha)\<close> and
      \<open>CLS' = ((a, b), ba, c, (aa, ab, bb), e, f, ivmtf, h, i, j, k,
        ag, (ah, ai, aj, be), ak, al, am, an, bf)\<close>
    for a b ba c aa ab bb e f ac ad ae af bc bd h i j k ag ah ai aj be ak al am an
       bf ao bg baa ca da ea fa ga ha CLS CLS' ivmtf
  proof -
    let ?\<A> = \<open>all_atms_st (baa, ca, da, ea, fa, ga, ha)\<close>
   have
      ao: \<open>ao \<in># dom_m (get_clauses_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      conf: \<open>get_conflict_wl (baa, ca, da, ea, fa, ga, ha) \<noteq> None\<close> and
      nempty: \<open>get_trail_wl (baa, ca, da, ea, fa, ga, ha) \<noteq> []\<close> and
      uL_D: \<open>- bg \<in># the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      L_M: \<open>(bg, ao) = lit_and_ann_of_propagated
        (hd (get_trail_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      bg_D0: \<open>bg \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close> and
      proped: \<open>is_proped (hd (get_trail_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      \<open>0 < ao\<close> and
      card_max_lvl: \<open>1 \<le> card_max_lvl (get_trail_wl (baa, ca, da, ea, fa, ga, ha))
            (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      dist_D: \<open>distinct_mset (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      uL_NC: \<open>- bg \<notin> set (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> ao)\<close> and
      L_NC: \<open>length (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> ao) > 2 \<longrightarrow>
          bg \<notin> set (tl (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> ao))\<close> and
      dist_NC: \<open>distinct (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> ao)\<close> and
      tauto_D:  \<open>\<not> tautology (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      tauto_NC: \<open>\<not> tautology (mset (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> ao))\<close> and
      tauto_NC_D: \<open>\<not> tautology
          (remove1_mset (- bg)
            (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)) \<union>#
            mset (tl (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> ao))))\<close> and
      count_dec_ge: \<open>0 < count_decided (get_trail_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?\<A> (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n ?\<A> (baa, ca, da, ea, fa, ga, ha)\<close> and
      lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail ?\<A> (get_trail_wl (baa, ca, da, ea, fa, ga, ha))\<close>
      using inv unfolding CLS update_confl_tl_wl_pre_def prod.case
      by blast+
    have
      n_d: \<open>no_dup baa\<close> and
      outl: \<open>out_learned baa da ag\<close> and
      i: \<open>i \<in> counts_maximum_level baa da\<close>
      using rel unfolding twl_st_heur_conflict_ana_def
      by auto
    have
      [simp]: \<open>a = ao\<close> and
      [simp]: \<open>b = bg\<close> and
      n_d: \<open>no_dup baa\<close> and
      arena: \<open>valid_arena c ca (set an)\<close> and
      ocr: \<open>((aa, ab, bb), da) \<in> option_lookup_clause_rel ?\<A>\<close> and
      trail: \<open>(ba, baa) \<in> trail_pol ?\<A>\<close> and
      bounded: \<open>isasat_input_bounded ?\<A>\<close>
      using rel by (auto simp: CLS twl_st_heur_conflict_ana_def all_atms_def[symmetric])
    have lookup_remove1_uminus:
       \<open>lookup_conflict_remove1 (-bg) A = lookup_conflict_remove1 bg A\<close> for A
      by (auto simp: lookup_conflict_remove1_def)
    have [simp]: \<open>lit_of (hd baa) = bg\<close> and hd_M_L_C: \<open>hd baa = Propagated bg ao\<close>
      using L_M nempty proped by (cases baa; cases \<open>hd baa\<close>; auto; fail)+
    have bg_D[simp]: \<open>bg \<notin># the da\<close>
      using uL_D tauto_D by (auto simp: tautology_add_mset add_mset_eq_add_mset
      dest!: multi_member_split)
    have bg_\<A>: \<open>bg \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
      using  \<open>lit_of (hd baa) = bg\<close> lits_trail uL_D nempty
      by (cases baa)
        (auto simp del: \<open>lit_of (hd baa) = bg\<close> simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)

    have [simp]: \<open>length (ca \<propto> ao) > 2 \<Longrightarrow> bg \<notin> set (tl (ca \<propto> ao))\<close>
      using L_NC
      by (auto simp: resolve_cls_wl'_def split: if_splits)
    have mset_ge0_iff:  "0 < size M \<longleftrightarrow> M \<noteq> {#}" for M
     by (cases M) auto
    have no_dup: \<open>length (ca \<propto> ao) > 2 \<Longrightarrow> L \<in> set (tl (ca \<propto> ao)) \<Longrightarrow> - L \<in># the da \<Longrightarrow> False\<close> for L
      using tauto_NC_D tauto_NC \<open>length (ca \<propto> ao) > 2 \<Longrightarrow> bg \<notin> set (tl (ca \<propto> ao))\<close>
      apply (cases \<open>- L \<in># mset (tl (ca \<propto> ao))\<close>; cases \<open>bg = L\<close>)
      apply (auto dest!: multi_member_split
      simp: sup_union_left2 add_mset_remove_trivial_If tautology_add_mset split: if_splits)
      apply (metis in_set_tlD set_mset_mset tautology_minus)
      by (metis \<open>bg \<notin># the da\<close> in_remove1_mset_neq insert_DiffM set_mset_mset
        subset_mset.sup.right_idem subset_mset.sup_commute sup_union_left1 uminus_of_uminus_id
        union_single_eq_member)
    have size_union_ge1: \<open>Suc 0 \<le> size A \<Longrightarrow> Suc 0 \<le> size (A \<union># B)\<close> for A B
      apply (cases A)
      apply (simp; fail)
      apply (case_tac \<open>x \<in># B\<close>)
      by (auto dest!: multi_member_split simp: add_mset_union)
    have merge_conflict_m_pre: \<open>merge_conflict_m_pre ?\<A> ((((((baa, ca), ao), da), i), k), ag)\<close>
      using ao conf dist_D dist_NC tauto_NC n_d outl i no_dup lits lits_confl bounded
      unfolding merge_conflict_m_pre_def counts_maximum_level_def literals_are_\<L>\<^sub>i\<^sub>n_def
      is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
      by (auto simp: all_lits_of_mm_union all_lits_def)

    have arena_in_L: \<open>arena_lit c C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
      if \<open>Suc ao \<le> C\<close> \<open>C < ao + arena_length c ao\<close> for C
    proof -
      define D where \<open>D = C - ao\<close>
      with that have [simp]: \<open>C = ao + D\<close> and D_le: \<open>D < arena_length c ao\<close>
        by auto

      have is_in: \<open>ca \<propto> ao ! D \<in># mset (ca \<propto> ao)\<close>
        using arena that D_le ao
        by (auto intro!: nth_mem simp: arena_lifting(4))
      have \<open>set_mset (all_lits_of_m (mset (ca \<propto> ao))) \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>)\<close>
        using lits ao by (auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def ran_m_def all_lits_of_mm_add_mset
          is_\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_def
        dest!: multi_member_split)
      then have \<open>ca \<propto> ao ! D \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
        using multi_member_split[OF is_in]
        by (auto simp: all_lits_of_m_add_mset)

      then show ?thesis
        using arena ao D_le by (auto simp: arena_lifting)
    qed

    have [simp]: \<open>- bg \<notin># remove1_mset (- bg) (the da)\<close>
      using dist_D uL_D multi_member_split[of \<open>-bg\<close> \<open>the da\<close>]
      by auto
    moreover have [simp]: \<open>- bg \<notin> set (tl (ca \<propto> ao))\<close>
      using uL_D proped L_M nempty uL_NC
      by (cases \<open>ca \<propto> ao\<close>) (auto simp: resolve_cls_wl'_def split: if_splits)
    ultimately have [simp]: \<open>- bg \<notin># remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao)))\<close>
      by (metis \<open>a = ao\<close> diff_single_trivial in_multiset_in_set multi_drop_mem_not_eq
            remove1_mset_union_distrib)

    have \<open>vmtf_unset_pre (atm_of b) ivmtf\<close>
      if \<open>ivmtf \<in> isa_vmtf ?\<A> baa\<close>
      apply (rule vmtf_unset_pre'[OF that])
      using  that bg_\<A>
      by (auto simp: vmtf_unset_pre_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    moreover have \<open>isa_vmtf_unset (atm_of bg) ivmtf \<in> isa_vmtf ?\<A> (tl baa)\<close>
      if \<open>ivmtf \<in> isa_vmtf ?\<A> baa\<close>
      by (rule isa_vmtf_tl_isa_vmtf[OF that])
        (use inv rel that in \<open>auto simp: atms_of_def update_confl_tl_wl_pre_def
          twl_st_heur_conflict_ana_def
        intro!: isa_vmtf_unset_isa_vmtf\<close>)
    moreover have
      \<open>out_learned (tl baa) (Some (remove1_mset (- bg) ((the da) \<union># mset (tl (ca \<propto> ao))))) b\<close>
      if H: \<open>out_learned baa (Some ((the da) \<union># mset (tl (ca \<propto> ao)))) b\<close> for b
    proof -
      have \<open>(- bg) \<notin># {#bg \<in># (the da). get_level baa bg < count_decided baa#}\<close>
        using L_M nempty proped
        by (cases baa; cases \<open>hd baa\<close>) auto
      then have out:
        \<open>out_learned baa (Some (resolve_cls_wl' (baa, ca, Some (the da), ea, fa, ga, ha) ao bg)) b\<close>
        using uL_D H
        by (auto simp: resolve_cls_wl'_def out_learned_def ac_simps)
      have \<open>out_learned (tl baa)
        (Some (resolve_cls_wl' (baa, ca, Some (the da), ea, fa, ga, ha) ao bg)) b\<close>
        apply (rule out_learned_tl_Some_notin[THEN iffD1])
        using uL_D out proped L_M nempty proped nempty
        by (cases baa; cases \<open>hd baa\<close>; auto simp: resolve_cls_wl'_def split: if_splits; fail)+
    then show ?thesis
      using rel
      by (auto simp: twl_st_heur_conflict_ana_def merge_conflict_m_def update_confl_tl_wl_pre_def
          resolve_cls_wl'_def ac_simps)
    qed
    moreover have \<open>card_max_lvl baa (mset (tl (ca \<propto> ao)) \<union># (the da)) - Suc 0
      \<in> counts_maximum_level (tl baa)
        (Some (resolve_cls_wl' (baa, ca, da, ea, fa, ga, ha) ao bg))\<close>
    proof -
      have \<open>distinct_mset (remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao))))\<close>
        using dist_NC dist_D by (auto intro!: distinct_mset_minus)
      moreover have \<open>\<not>tautology (remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao))))\<close>
        using tauto_NC_D by simp
      moreover have \<open>card_max_lvl baa (mset (tl (ca \<propto> ao)) \<union># the da) - 1 =
        card_max_lvl baa (remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao))))\<close>
        unfolding \<open>lit_of (hd baa) = bg\<close> [symmetric]
        apply (subst card_max_lvl_remove1_mset_hd)
        using uL_D
        by (auto simp: hd_M_L_C ac_simps)
      ultimately show ?thesis
        unfolding counts_maximum_level_def
        using uL_D L_M proped nempty \<open>ao > 0\<close> n_d count_dec_ge
        by (auto simp del: simp: card_max_lvl_tl resolve_cls_wl'_def card_max_lvl_remove1_mset_hd)
    qed
    moreover have \<open>da = Some y \<Longrightarrow> ((a, aaa, b), Some (y \<union># mset (tl (ca \<propto> ao))))
       \<in> option_lookup_clause_rel ?\<A> \<Longrightarrow>
       ((a, lookup_conflict_remove1 (-bg) (aaa, b)),
        Some (remove1_mset (- bg) (y \<union># mset (tl (ca \<propto> ao)))))
       \<in> option_lookup_clause_rel ?\<A>\<close>
       for a aaa b ba y
       using uL_D bg_D0 bg_D
       using lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry, of ?\<A> \<open>-bg\<close>
          \<open>y \<union># mset (tl (ca \<propto> ao))\<close> \<open>-bg\<close> \<open>(aaa, b)\<close>]
       by (auto simp: option_lookup_clause_rel_def
         size_remove1_mset_If image_image uminus_\<A>\<^sub>i\<^sub>n_iff)
    moreover have \<open>1 \<le> card_max_lvl baa (the da \<union># mset (tl (ca \<propto> ao)))\<close>
      using card_max_lvl by (auto simp: card_max_lvl_def size_union_ge1)
    moreover have \<open>((a, aaa, b), Some (the da \<union># mset (tl (ca \<propto> ao))))
       \<in> option_lookup_clause_rel ?\<A> \<Longrightarrow>
       lookup_conflict_remove1_pre (bg, aaa, b)\<close>
       for a aaa b ba y
       using uL_D bg_D0 bg_D uL_D
       by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def atms_of_def
         lookup_conflict_remove1_pre_def mset_ge0_iff
         size_remove1_mset_If image_image uminus_\<A>\<^sub>i\<^sub>n_iff simp del: bg_D)
    moreover have \<open>tl_trailt_tr_pre ba\<close>
      by (rule tl_trailt_tr_pre[OF _ trail])
        (use nempty in auto)
    ultimately show ?thesis
       using rel inv
       apply -
       apply (rule order_trans)
       apply (rule isa_resolve_merge_conflict[of ?\<A> \<open>set an\<close>,
         THEN fref_to_Down_curry6, OF merge_conflict_m_pre])
       subgoal using arena ocr trail by (auto simp: all_atms_def[symmetric])
       subgoal unfolding merge_conflict_m_def conc_fun_SPEC
        by (auto simp: twl_st_heur_conflict_ana_def merge_conflict_m_def update_confl_tl_wl_pre_def
           resolve_cls_wl'_def ac_simps no_dup_tlD lookup_remove1_uminus arena_in_L
	   all_atms_def[symmetric]
           intro!: ASSERT_refine_left
	     tl_trail_tr[THEN fref_to_Down_unRET])
       done
  qed

  have \<open>isa_resolve_merge_conflict (aa, ab, ac, ad, ae, ba) c a (af, x1, x2) i k l
	\<le> SPEC
	   (\<lambda>x. (case x of
		 (x, xa) \<Rightarrow>
		   (case x of
		    (bb, n, xs) \<Rightarrow>
		      \<lambda>(clvls, lbd, outl). do {
			   _ \<leftarrow> ASSERT
				(curry lookup_conflict_remove1_pre b (n, xs) \<and>
				 1 \<le> clvls);
			   let (n, xs) = lookup_conflict_remove1 b (n, xs);
			   _ \<leftarrow> ASSERT
				(vmtf_unset_pre (atm_of b)
				  ((ah, ai, aj, ak, bc), al, bd));
			   _ \<leftarrow> ASSERT (tl_trailt_tr_pre (aa, ab, ac, ad, ae, ba));
			   RETURN
			    (False, tl_trailt_tr (aa, ab, ac, ad, ae, ba), c,
			     (bb, n, xs), e, f,
			     isa_vmtf_unset (atm_of b)
			      ((ah, ai, aj, ak, bc), al, bd),
			     h, fast_minus clvls one_uint32_nat, (am, be), lbd,
			     outl, (an, ao, ap, aq, ar, bf), (as, at, au, av, bg),
			     (aw, ax, ay, az, bh), (bi, bj), ra, s, t, u, v, w)
			 })
		    xa)
		\<le> \<Down> (bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r)
		   (RETURN
		     (let D = resolve_cls_wl' (baa, ca, da, ea, fa, ga, ha) bk bl
		      in (False, tl baa, ca, Some D, ea, fa, ga, ha))))\<close>
    if 
      inv: \<open>update_confl_tl_wl_pre ((bk, bl), baa, ca, da, ea, fa, ga, ha)\<close> and
      rel: \<open>(((a, b), (aa, ab, ac, ad, ae, ba), c, (af, ag, bb), e, f,
	 ((ah, ai, aj, ak, bc), al, bd), h, i, (am, be), k, l,
	 (an, ao, ap, aq, ar, bf), (as, at, au, av, bg), (aw, ax, ay, az, bh),
	 (bi, bj), ra, s, t, u, v, w),
	(bk, bl), baa, ca, da, ea, fa, ga, ha)
       \<in> nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r\<close> and
      CLS: \<open>CLS = ((bk, bl), baa, ca, da, ea, fa, ga, ha)\<close> and
      \<open>CLS' =
       ((a, b), (aa, ab, ac, ad, ae, ba), c, (af, ag, bb), e, f,
	((ah, ai, aj, ak, bc), al, bd), h, i, (am, be), k, l,
	(an, ao, ap, aq, ar, bf), (as, at, au, av, bg), (aw, ax, ay, az, bh),
	(bi, bj), ra, s, t, u, v, w)\<close> and
      \<open>1 \<le> i\<close> and
      \<open>lookup_conflict_remove1 b (ag, bb) = (x1, x2)\<close> and
      pre: \<open>curry6 isa_set_lookup_conflict_aa_pre
	(aa, ab, ac, ad, ae, ba) c a (af, x1, x2) i k l\<close>
    for a b aa ab ac ad ae ba c af ag bb e f ah ai aj ak bc al bd h i am be k l an
       ao ap aq ar bf as at au av bg aw ax ay az bh bi bj ra s t u v w bk bl baa
       ca da ea fa ga ha x1 x2
  proof -

    let ?\<A> = \<open>all_atms_st (baa, ca, da, ea, fa, ga, ha)\<close>
    have
      ao: \<open>bk \<in># dom_m (get_clauses_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      conf: \<open>get_conflict_wl (baa, ca, da, ea, fa, ga, ha) \<noteq> None\<close> and
      nempty: \<open>get_trail_wl (baa, ca, da, ea, fa, ga, ha) \<noteq> []\<close> and
      uL_D: \<open>- bl \<in># the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      L_M: \<open>(bl, bk) =
       lit_and_ann_of_propagated
	(hd (get_trail_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      bg_D0: \<open>bl \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (?\<A>)\<close> and
      proped: \<open>is_proped (hd (get_trail_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      \<open>0 < bk\<close> and
      card_max_lvl: \<open>1 \<le> card_max_lvl (get_trail_wl (baa, ca, da, ea, fa, ga, ha))
	    (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      dist_D: \<open>distinct_mset (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      uL_NC: \<open>- bl \<notin> set (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk)\<close> and
      L_NC: \<open>2 < length (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk) \<longrightarrow>
       bl \<notin> set (tl (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk))\<close> and
      L_watch: \<open>bl \<in> set (watched_l
		  (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk))\<close> and
      dist_NC: \<open>distinct (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk)\<close> and
      tauto_D: \<open>\<not> tautology (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      tauto_NC: \<open>\<not> tautology (mset (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk))\<close> and
      tauto_NC_D: \<open>\<not> tautology
	  (remove1_mset bl
	    (remove1_mset (- bl) (the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)) \<union>#
	     mset (get_clauses_wl (baa, ca, da, ea, fa, ga, ha) \<propto> bk))))\<close> and
      count_dec_ge: \<open>0 < count_decided (get_trail_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (?\<A>)
	(the (get_conflict_wl (baa, ca, da, ea, fa, ga, ha)))\<close> and
      lits_confl: \<open>literals_are_\<L>\<^sub>i\<^sub>n (?\<A>)
	(baa, ca, da, ea, fa, ga, ha)\<close> and
      lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (?\<A>)
	(get_trail_wl (baa, ca, da, ea, fa, ga, ha))\<close> 
      using inv unfolding CLS update_confl_tl_wl_pre_def prod.case apply -
      by blast+

    have
      n_d: \<open>no_dup baa\<close> and
      outl: \<open>out_learned baa da l\<close> and
      i: \<open>i \<in> counts_maximum_level baa da\<close>
      using rel unfolding twl_st_heur_conflict_ana_def
      by auto
    have
      [simp]: \<open>a = bk\<close> and
      [simp]: \<open>b = bl\<close> and
      n_d: \<open>no_dup baa\<close> and
      arena: \<open>valid_arena c ca (set ra)\<close> and
      ocr: \<open>((af, ag, bb), da) \<in> option_lookup_clause_rel ?\<A>\<close> and
      trail: \<open>((aa, ab, ac, ad, ae, ba), baa) \<in> trail_pol ?\<A>\<close> and
      bounded: \<open>isasat_input_bounded ?\<A>\<close>
      using rel by (auto simp: CLS twl_st_heur_conflict_ana_def all_atms_def[symmetric])

    have [simp]: \<open>lit_of (hd baa) = bl\<close> and hd_M_L_C: \<open>hd baa = Propagated bl bk\<close>
      using L_M nempty proped by (cases baa; cases \<open>hd baa\<close>; auto; fail)+

    have bg_D[simp]: \<open>bl \<notin># the da\<close>
      using uL_D tauto_D by (auto simp: tautology_add_mset add_mset_eq_add_mset
      dest!: multi_member_split)
    have bg_\<A>: \<open>bl \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
      using  \<open>lit_of (hd baa) = bl\<close> lits_trail uL_D nempty
      by (cases baa)
        (auto simp del: \<open>lit_of (hd baa) = bl\<close> simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)

    have [simp]: \<open>length (ca \<propto> bk) > 2 \<Longrightarrow> bl \<notin> set (tl (ca \<propto> bk))\<close>
      using L_NC
      by (auto simp: resolve_cls_wl'_def split: if_splits)
    have mset_ge0_iff:  "0 < size M \<longleftrightarrow> M \<noteq> {#}" for M
     by (cases M) auto
    have no_dup: \<open>L \<in> set ((ca \<propto> bk)) \<Longrightarrow>
       - L \<in># remove1_mset (-bl) (the da) \<Longrightarrow> False\<close> for L
      using tauto_NC_D tauto_NC \<open>length (ca \<propto> bk) > 2 \<Longrightarrow> bl \<notin> set (tl (ca \<propto> bk))\<close> uL_NC
        tauto_D uL_D dist_D L_watch dist_NC
      apply (cases \<open>- L \<in># mset (ca \<propto> bk)\<close>; cases \<open>bl = L\<close>)
      apply (auto dest!: multi_member_split
        simp: sup_union_left2 add_mset_remove_trivial_If tautology_add_mset in_set_tlD
          add_mset_eq_add_mset
        split: if_splits)
      apply (cases \<open>ca \<propto> bk\<close>;
        cases \<open>tl (ca \<propto> bk)\<close>)
	apply (auto simp: tautology_add_mset)
      done

    have size_union_ge1: \<open>Suc 0 \<le> size A \<Longrightarrow> Suc 0 \<le> size (A \<union># B)\<close> for A B
      apply (cases A)
      apply (simp; fail)
      apply (case_tac \<open>x \<in># B\<close>)
      by (auto dest!: multi_member_split simp: add_mset_union)

    let ?da = \<open>Some (remove1_mset (-bl) (the da))\<close>
    have merge_conflict_m_pre: \<open>merge_conflict_m_pre ?\<A> ((((((baa, ca), bk), ?da), i), k), l)\<close>
      using rel conf dist_D dist_NC tauto_NC n_d outl i lits lits_confl bounded ao no_dup
      multi_member_split[OF uL_D]
      (*no_dup*)
      unfolding merge_conflict_m_pre_def counts_maximum_level_def literals_are_\<L>\<^sub>i\<^sub>n_def
      is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
      apply (auto simp: all_lits_of_mm_union all_lits_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
      
      oops
      using ao conf dist_D dist_NC tauto_NC n_d outl i no_dup lits lits_confl bounded
      unfolding merge_conflict_m_pre_def counts_maximum_level_def literals_are_\<L>\<^sub>i\<^sub>n_def
      is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
      by (auto simp: all_lits_of_mm_union all_lits_def)

    have ?thesis
       using rel inv
       apply -
       apply (rule order_trans)
       apply (rule isa_resolve_merge_conflict[of ?\<A> \<open>set ra\<close>,
         THEN fref_to_Down_curry6, OF _])
       subgoal using arena ocr trail by (auto simp: all_atms_def[symmetric])
       subgoal unfolding merge_conflict_m_def conc_fun_SPEC
        by (auto simp: twl_st_heur_conflict_ana_def merge_conflict_m_def update_confl_tl_wl_pre_def
           resolve_cls_wl'_def ac_simps no_dup_tlD lookup_remove1_uminus arena_in_L
	   all_atms_def[symmetric]
           intro!: ASSERT_refine_left
	     tl_trail_tr[THEN fref_to_Down_unRET])
    have lookup_remove1_uminus:
       \<open>lookup_conflict_remove1 (-bg) A = lookup_conflict_remove1 bg A\<close> for A
      by (auto simp: lookup_conflict_remove1_def)
    have [simp]: \<open>lit_of (hd baa) = bg\<close> and hd_M_L_C: \<open>hd baa = Propagated bg ao\<close>
      using L_M nempty proped by (cases baa; cases \<open>hd baa\<close>; auto; fail)+
    have bg_D[simp]: \<open>bg \<notin># the da\<close>
      using uL_D tauto_D by (auto simp: tautology_add_mset add_mset_eq_add_mset
      dest!: multi_member_split)
    have bg_\<A>: \<open>bg \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
      using  \<open>lit_of (hd baa) = bg\<close> lits_trail uL_D nempty
      by (cases baa)
        (auto simp del: \<open>lit_of (hd baa) = bg\<close> simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)

    have [simp]: \<open>length (ca \<propto> ao) > 2 \<Longrightarrow> bg \<notin> set (tl (ca \<propto> ao))\<close>
      using L_NC
      by (auto simp: resolve_cls_wl'_def split: if_splits)
    have mset_ge0_iff:  "0 < size M \<longleftrightarrow> M \<noteq> {#}" for M
     by (cases M) auto
    have no_dup: \<open>length (ca \<propto> ao) > 2 \<Longrightarrow> L \<in> set (tl (ca \<propto> ao)) \<Longrightarrow> - L \<in># the da \<Longrightarrow> False\<close> for L
      using tauto_NC_D tauto_NC \<open>length (ca \<propto> ao) > 2 \<Longrightarrow> bg \<notin> set (tl (ca \<propto> ao))\<close>
      apply (cases \<open>- L \<in># mset (tl (ca \<propto> ao))\<close>; cases \<open>bg = L\<close>)
      apply (auto dest!: multi_member_split
      simp: sup_union_left2 add_mset_remove_trivial_If tautology_add_mset split: if_splits)
      apply (metis in_set_tlD set_mset_mset tautology_minus)
      by (metis \<open>bg \<notin># the da\<close> in_remove1_mset_neq insert_DiffM set_mset_mset
        subset_mset.sup.right_idem subset_mset.sup_commute sup_union_left1 uminus_of_uminus_id
        union_single_eq_member)
    have size_union_ge1: \<open>Suc 0 \<le> size A \<Longrightarrow> Suc 0 \<le> size (A \<union># B)\<close> for A B
      apply (cases A)
      apply (simp; fail)
      apply (case_tac \<open>x \<in># B\<close>)
      by (auto dest!: multi_member_split simp: add_mset_union)
    have merge_conflict_m_pre: \<open>merge_conflict_m_pre ?\<A> ((((((baa, ca), ao), da), i), k), ag)\<close>
      using ao conf dist_D dist_NC tauto_NC n_d outl i no_dup lits lits_confl bounded
      unfolding merge_conflict_m_pre_def counts_maximum_level_def literals_are_\<L>\<^sub>i\<^sub>n_def
      is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
      by (auto simp: all_lits_of_mm_union all_lits_def)

    have arena_in_L: \<open>arena_lit c C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
      if \<open>Suc ao \<le> C\<close> \<open>C < ao + arena_length c ao\<close> for C
    proof -
      define D where \<open>D = C - ao\<close>
      with that have [simp]: \<open>C = ao + D\<close> and D_le: \<open>D < arena_length c ao\<close>
        by auto

      have is_in: \<open>ca \<propto> ao ! D \<in># mset (ca \<propto> ao)\<close>
        using arena that D_le ao
        by (auto intro!: nth_mem simp: arena_lifting(4))
      have \<open>set_mset (all_lits_of_m (mset (ca \<propto> ao))) \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>)\<close>
        using lits ao by (auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def ran_m_def all_lits_of_mm_add_mset
          is_\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_def
        dest!: multi_member_split)
      then have \<open>ca \<propto> ao ! D \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
        using multi_member_split[OF is_in]
        by (auto simp: all_lits_of_m_add_mset)

      then show ?thesis
        using arena ao D_le by (auto simp: arena_lifting)
    qed

    have [simp]: \<open>- bg \<notin># remove1_mset (- bg) (the da)\<close>
      using dist_D uL_D multi_member_split[of \<open>-bg\<close> \<open>the da\<close>]
      by auto
    moreover have [simp]: \<open>- bg \<notin> set (tl (ca \<propto> ao))\<close>
      using uL_D proped L_M nempty uL_NC
      by (cases \<open>ca \<propto> ao\<close>) (auto simp: resolve_cls_wl'_def split: if_splits)
    ultimately have [simp]: \<open>- bg \<notin># remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao)))\<close>
      by (metis \<open>a = ao\<close> diff_single_trivial in_multiset_in_set multi_drop_mem_not_eq
            remove1_mset_union_distrib)

    have \<open>vmtf_unset_pre (atm_of b) ivmtf\<close>
      if \<open>ivmtf \<in> isa_vmtf ?\<A> baa\<close>
      apply (rule vmtf_unset_pre'[OF that])
      using  that bg_\<A>
      by (auto simp: vmtf_unset_pre_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    moreover have \<open>isa_vmtf_unset (atm_of bg) ivmtf \<in> isa_vmtf ?\<A> (tl baa)\<close>
      if \<open>ivmtf \<in> isa_vmtf ?\<A> baa\<close>
      by (rule isa_vmtf_tl_isa_vmtf[OF that])
        (use inv rel that in \<open>auto simp: atms_of_def update_confl_tl_wl_pre_def
          twl_st_heur_conflict_ana_def
        intro!: isa_vmtf_unset_isa_vmtf\<close>)
    moreover have
      \<open>out_learned (tl baa) (Some (remove1_mset (- bg) ((the da) \<union># mset (tl (ca \<propto> ao))))) b\<close>
      if H: \<open>out_learned baa (Some ((the da) \<union># mset (tl (ca \<propto> ao)))) b\<close> for b
    proof -
      have \<open>(- bg) \<notin># {#bg \<in># (the da). get_level baa bg < count_decided baa#}\<close>
        using L_M nempty proped
        by (cases baa; cases \<open>hd baa\<close>) auto
      then have out:
        \<open>out_learned baa (Some (resolve_cls_wl' (baa, ca, Some (the da), ea, fa, ga, ha) ao bg)) b\<close>
        using uL_D H
        by (auto simp: resolve_cls_wl'_def out_learned_def ac_simps)
      have \<open>out_learned (tl baa)
        (Some (resolve_cls_wl' (baa, ca, Some (the da), ea, fa, ga, ha) ao bg)) b\<close>
        apply (rule out_learned_tl_Some_notin[THEN iffD1])
        using uL_D out proped L_M nempty proped nempty
        by (cases baa; cases \<open>hd baa\<close>; auto simp: resolve_cls_wl'_def split: if_splits; fail)+
    then show ?thesis
      using rel
      by (auto simp: twl_st_heur_conflict_ana_def merge_conflict_m_def update_confl_tl_wl_pre_def
          resolve_cls_wl'_def ac_simps)
    qed
    moreover have \<open>card_max_lvl baa (mset (tl (ca \<propto> ao)) \<union># (the da)) - Suc 0
      \<in> counts_maximum_level (tl baa)
        (Some (resolve_cls_wl' (baa, ca, da, ea, fa, ga, ha) ao bg))\<close>
    proof -
      have \<open>distinct_mset (remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao))))\<close>
        using dist_NC dist_D by (auto intro!: distinct_mset_minus)
      moreover have \<open>\<not>tautology (remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao))))\<close>
        using tauto_NC_D by simp
      moreover have \<open>card_max_lvl baa (mset (tl (ca \<propto> ao)) \<union># the da) - 1 =
        card_max_lvl baa (remove1_mset (- bg) (the da \<union># mset (tl (ca \<propto> ao))))\<close>
        unfolding \<open>lit_of (hd baa) = bg\<close> [symmetric]
        apply (subst card_max_lvl_remove1_mset_hd)
        using uL_D
        by (auto simp: hd_M_L_C ac_simps)
      ultimately show ?thesis
        unfolding counts_maximum_level_def
        using uL_D L_M proped nempty \<open>ao > 0\<close> n_d count_dec_ge
        by (auto simp del: simp: card_max_lvl_tl resolve_cls_wl'_def card_max_lvl_remove1_mset_hd)
    qed
    moreover have \<open>da = Some y \<Longrightarrow> ((a, aaa, b), Some (y \<union># mset (tl (ca \<propto> ao))))
       \<in> option_lookup_clause_rel ?\<A> \<Longrightarrow>
       ((a, lookup_conflict_remove1 (-bg) (aaa, b)),
        Some (remove1_mset (- bg) (y \<union># mset (tl (ca \<propto> ao)))))
       \<in> option_lookup_clause_rel ?\<A>\<close>
       for a aaa b ba y
       using uL_D bg_D0 bg_D
       using lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry, of ?\<A> \<open>-bg\<close>
          \<open>y \<union># mset (tl (ca \<propto> ao))\<close> \<open>-bg\<close> \<open>(aaa, b)\<close>]
       by (auto simp: option_lookup_clause_rel_def
         size_remove1_mset_If image_image uminus_\<A>\<^sub>i\<^sub>n_iff)
    moreover have \<open>1 \<le> card_max_lvl baa (the da \<union># mset (tl (ca \<propto> ao)))\<close>
      using card_max_lvl by (auto simp: card_max_lvl_def size_union_ge1)
    moreover have \<open>((a, aaa, b), Some (the da \<union># mset (tl (ca \<propto> ao))))
       \<in> option_lookup_clause_rel ?\<A> \<Longrightarrow>
       lookup_conflict_remove1_pre (bg, aaa, b)\<close>
       for a aaa b ba y
       using uL_D bg_D0 bg_D uL_D
       by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def atms_of_def
         lookup_conflict_remove1_pre_def mset_ge0_iff
         size_remove1_mset_If image_image uminus_\<A>\<^sub>i\<^sub>n_iff simp del: bg_D)
    moreover have \<open>tl_trailt_tr_pre ba\<close>
      by (rule tl_trailt_tr_pre[OF _ trail])
        (use nempty in auto)
    ultimately show ?thesis
       using rel inv
       apply -
       apply (rule order_trans)
       apply (rule isa_resolve_merge_conflict[of ?\<A> \<open>set an\<close>,
         THEN fref_to_Down_curry6, OF merge_conflict_m_pre])
       subgoal using arena ocr trail by (auto simp: all_atms_def[symmetric])
       subgoal unfolding merge_conflict_m_def conc_fun_SPEC
        by (auto simp: twl_st_heur_conflict_ana_def merge_conflict_m_def update_confl_tl_wl_pre_def
           resolve_cls_wl'_def ac_simps no_dup_tlD lookup_remove1_uminus arena_in_L
	   all_atms_def[symmetric]
           intro!: ASSERT_refine_left
	     tl_trail_tr[THEN fref_to_Down_unRET])
       done  
    show ?thesis sorry
  qed

  have isa_set_lookup_conflict_aa_pre:
    \<open>curry6 isa_set_lookup_conflict_aa_pre
	 (aa, ab, ac, ad, ae, ba) c a (af, ia, ja) i k l\<close>
    if 
      inv: \<open>update_confl_tl_wl_pre ((bk, bl), baa, ca, da, ea, fa, ga, ha)\<close> and
      \<open>1 \<le> i\<close> and
      rem: \<open>lookup_conflict_remove1 b (ag, bb) = (ia, ja)\<close> and
      rel: \<open>(((a, b), (aa, ab, ac, ad, ae, ba), c, (af, ag, bb), e, f,
	 ((ah, ai, aj, ak, bc), al, bd), h, i, (am, be), k, l,
	 (an, ao, ap, aq, ar, bf), (as, at, au, av, bg), (aw, ax, ay, az, bh),
	 (bi, bj), ra, s, t, u, v, w),
	(bk, bl), baa, ca, da, ea, fa, ga, ha)
       \<in> nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_conflict_ana' r\<close> and
      CLS: \<open>CLS = ((bk, bl), baa, ca, da, ea, fa, ga, ha)\<close> and
      \<open>CLS' =
       ((a, b), (aa, ab, ac, ad, ae, ba), c, (af, ag, bb), e, f,
	((ah, ai, aj, ak, bc), al, bd), h, i, (am, be), k, l,
	(an, ao, ap, aq, ar, bf), (as, at, au, av, bg), (aw, ax, ay, az, bh),
	(bi, bj), ra, s, t, u, v, w)\<close>
    for a b aa ab ac ad ae ba c af ag bb e f ah ai aj ak bc al bd h i am be k l an
	 ao ap aq ar bf as at au av bg aw ax ay az bh bi bj ra s t u v w bk bl baa
	 ca da ea fa ga ha ia ja CLS CLS'
  proof -
    let ?\<A> = \<open>all_atms_st (baa, ca, da, ea, fa, ga, ha)\<close>

    have 
      ao: \<open>bk \<in># dom_m (get_clauses_wl (baa, ca, da, ea, fa, ga, ha))\<close> and
      lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail ?\<A>
	(get_trail_wl (baa, ca, da, ea, fa, ga, ha))\<close>
      using inv unfolding CLS update_confl_tl_wl_pre_def prod.case apply -
      by blast+
      
    have
      arena: \<open>valid_arena c ca (set ra)\<close> and
      ocr: \<open>((af, ag, bb), da) \<in> option_lookup_clause_rel ?\<A>\<close> and
      trail: \<open>((aa, ab, ac, ad, ae, ba), baa) \<in> trail_pol ?\<A>\<close> and
      [simp]: \<open>bk = a\<close>
      using rel by (auto simp: CLS twl_st_heur_conflict_ana_def all_atms_def[symmetric])
    show ?thesis
      using arena lits_trail ao
      unfolding isa_set_lookup_conflict_aa_pre_def
      by (auto simp: arena_lifting lookup_conflict_remove1_def)
  qed
  show ?thesis
    supply [[goals_limit = 2]]
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (intro frefI nres_relI)
    subgoal for CLS' CLS
      unfolding uncurry_def update_confl_tl_wl_heur_def comp_def
        update_confl_tl_wl_def
      apply (cases CLS'; cases CLS)
      apply clarify
      apply (refine_rcg lhs_step_If specify_left; remove_dummy_vars)
      subgoal
        by (auto simp: twl_st_heur_conflict_ana_def update_confl_tl_wl_pre_def
            RES_RETURN_RES RETURN_def counts_maximum_level_def)
      subgoal
        by (rule isa_set_lookup_conflict_aa_pre)
      subgoal for a b aa ab ac ad ae ba c af ag bb e f ah ai aj ak bc al bd h i am be k l an
       ao ap aq ar bf as at au av bg aw ax ay az bh bi bj ra s t u v w bk bl baa
       ca da ea fa ga ha x1 x2
       explore_have
      
      by (rule H)
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
      skip_and_resolve_loop_wl_D_inv S\<^sub>0 brk S \<and>
       length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S\<^sub>0') \<and>
       is_decided_hd_trail_wl_heur_pre S')\<close>

definition update_confl_tl_wl_heur_pre
   :: \<open>(nat \<times> nat literal) \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
\<open>update_confl_tl_wl_heur_pre =
  (\<lambda>((i, L), (M, N, D, W, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, clvls, cach, lbd,
        outl, _)).
      i > 0 \<and>
      (fst M) \<noteq> [] \<and>
      atm_of ((last (fst M))) < length \<phi> \<and>
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
	    ASSERT(lit_and_ann_of_propagated_st_heur_pre S);
            let (L, C) = lit_and_ann_of_propagated_st_heur S;
            ASSERT(atm_is_in_conflict_st_heur_pre (-L, S));
            if \<not>atm_is_in_conflict_st_heur (-L) S then
              do {
	      ASSERT (tl_state_wl_heur_pre S);
	      RETURN (False, tl_state_wl_heur S)}
            else
              if maximum_level_removed_eq_count_dec_heur (-L) S
              then do {
                ASSERT(update_confl_tl_wl_heur_pre ((C, L), S));
                update_confl_tl_wl_heur C L S}
              else
                RETURN (True, S)
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

context
  fixes x y xa x' x1 x2 x1b x2b r
  assumes
    xy:  \<open>(x, y) \<in> twl_st_heur_conflict_ana' r\<close> and
    confl:  \<open>get_conflict_wl y \<noteq> None\<close> and
    xa_x':  \<open>(xa, x') \<in> bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x))\<close> and
    x':  \<open>x' = (x1, x2)\<close> and
    xa:  \<open>xa = (x1b, x2b)\<close> and
    sor_inv: \<open>case x' of (x, xa) \<Rightarrow> skip_and_resolve_loop_wl_D_inv y x xa\<close>
begin


private lemma lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st x2) x2\<close> and
  confl_x2: \<open>get_conflict_wl x2 \<noteq> None\<close> and
  trail_nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
  not_tauto: \<open>\<not>tautology (the (get_conflict_wl x2))\<close> and
  dist_confl: \<open>distinct_mset (the (get_conflict_wl x2))\<close> and
  count_dec_not0: \<open>count_decided (get_trail_wl x2) \<noteq> 0\<close> and
  no_dup_x2: \<open>no_dup (get_trail_wl x2)\<close> and
  lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st x2) (get_trail_wl x2)\<close> and
  lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st x2) (the (get_conflict_wl x2))\<close>
proof -
  obtain x xa xb xc where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st x2) x2\<close> and
    x2_x: \<open>(x2, x) \<in> state_wl_l None\<close> and
    y_xa: \<open>(y, xa) \<in> state_wl_l None\<close> and
    \<open>correct_watching x2\<close> and
    x_xb: \<open>(x, xb) \<in> twl_st_l None\<close> and
    xa_xc: \<open>(xa, xc) \<in> twl_st_l None\<close> and
    \<open>cdcl_twl_o\<^sup>*\<^sup>* xc xb\<close> and
    list_invs: \<open>twl_list_invs x\<close> and
    struct: \<open>twl_struct_invs xb\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>\<not> is_decided (hd (get_trail_l x)) \<longrightarrow> 0 < mark_of (hd (get_trail_l x))\<close> and
    \<open>twl_stgy_invs xb\<close> and
    \<open>clauses_to_update xb = {#}\<close> and
    \<open>literals_to_update xb = {#}\<close> and
    confl: \<open>get_conflict xb \<noteq> None\<close> and
    count_dec: \<open>count_decided (get_trail xb) \<noteq> 0\<close> and
    trail_nempty: \<open>get_trail xb \<noteq> []\<close> and
    \<open>get_conflict xb \<noteq> Some {#}\<close> and
    \<open>x1 \<longrightarrow>
     (no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of xb)) \<and>
     (no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of xb))\<close>
    using sor_inv
    unfolding skip_and_resolve_loop_wl_D_inv_def prod.simps xa skip_and_resolve_loop_wl_D_heur_inv_def
    skip_and_resolve_loop_wl_inv_def x' skip_and_resolve_loop_inv_l_def
    skip_and_resolve_loop_inv_def by blast
  show \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st x2) x2\<close>
    using lits .
  show \<open>get_conflict_wl x2 \<noteq> None\<close>
    using x2_x y_xa confl x_xb
    by auto
  show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st x2) (get_trail_wl x2)\<close>
     using \<open>twl_struct_invs xb\<close> literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail lits x2_x x_xb
     by blast
  show trail_nempty_x2: \<open>get_trail_wl x2 \<noteq> []\<close>
    using x2_x y_xa confl x_xb trail_nempty
    by auto

  have cdcl_confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of xb)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of xb)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of xb)\<close>
    using struct
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by blast+
  then have confl': \<open>\<forall>T. conflicting (state\<^sub>W_of xb) = Some T \<longrightarrow>
       trail (state\<^sub>W_of xb) \<Turnstile>as CNot T\<close> and
    \<open>no_dup (trail (state\<^sub>W_of xb))\<close> and
    confl_annot: \<open>\<And>L mark a b.
        a @ Propagated L mark # b = trail (state\<^sub>W_of xb) \<longrightarrow>
        b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have conflicting: \<open>get_trail_wl x2 \<Turnstile>as CNot (the (get_conflict_wl x2))\<close> and
    \<open>no_dup (get_trail_wl x2)\<close>
    using x2_x y_xa confl x_xb trail_nempty
    by (auto simp: twl_st)

  show \<open>\<not>tautology (the (get_conflict_wl x2))\<close>
    using \<open>get_conflict_wl x2 \<noteq> None\<close> conflict_not_tautology
      struct x2_x x_xb by blast
  show dist_mset:  \<open>distinct_mset (the (get_conflict_wl x2))\<close> and
    \<open>count_decided (get_trail_wl x2) \<noteq> 0\<close>
    using dist x2_x x_xb \<open>get_conflict_wl x2 \<noteq> None\<close> count_dec
    by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        twl_st)
  show \<open>no_dup (get_trail_wl x2)\<close>
    using \<open>no_dup (get_trail_wl x2)\<close> .

  show lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st x2) (the (get_conflict_wl x2))\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict[OF x2_x struct x_xb lits])
      (use x2_x x_xb confl in auto)
qed

private lemma sor_heur_inv_heur1:
  \<open>fst (get_trail_wl_heur x2b) \<noteq> []\<close>
  using xa_x' trail_nempty unfolding xa x'
  by (auto simp: twl_st_heur_conflict_ana_def trail_pol_nempty last_trail_pol_pre_def
    dest!: neq_Nil_conv[THEN iffD1])

private lemma sor_heur_inv_heur2:
  \<open>last_trail_pol_pre (get_trail_wl_heur x2b)\<close>
  using xa_x' trail_nempty[THEN neq_Nil_conv[THEN iffD1]] sor_heur_inv_heur1 unfolding xa x'
  by (cases x2b; cases x2; cases \<open>get_trail_wl_heur x2b\<close>)
    (auto simp add: twl_st_heur_conflict_ana_def trail_pol_def last_trail_pol_pre_def
     ann_lits_split_reasons_def)

lemma sor_heur_inv:
  \<open>skip_and_resolve_loop_wl_D_heur_inv x xa\<close>
  using sor_inv xa_x' xy sor_heur_inv_heur1 sor_heur_inv_heur2 unfolding xa x'
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def prod.simps apply -
  apply (rule exI[of _ \<open>x2\<close>])
  apply (rule exI[of _ y])
  by (auto simp: is_decided_hd_trail_wl_heur_pre_def)

lemma conflict_ana_same_cond:
  \<open>(\<not> x1b \<and> \<not> is_decided_hd_trail_wl_heur x2b) =
    (\<not> x1 \<and> \<not> is_decided (hd (get_trail_wl x2)))\<close>
  apply (subst is_decided_hd_trail_wl_heur_hd_get_trail[THEN fref_to_Down_unRET_Id, OF trail_nempty,
    of _ \<open>length (get_clauses_wl_heur x)\<close>])
  using xa_x' unfolding xa x'
  by auto

context
  fixes x1a x2a x1c x2c
  assumes
    hd_xa:  \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1a, x2a)\<close> and
    cond_heur: \<open>case xa of (brk, S) \<Rightarrow> \<not> brk \<and> \<not> is_decided_hd_trail_wl_heur S\<close> and
    cond:  \<open>case x' of (brk, S) \<Rightarrow> \<not> brk \<and> \<not> is_decided (hd (get_trail_wl S))\<close> and
    xc:  \<open>lit_and_ann_of_propagated_st_heur x2b = (x1c, x2c)\<close> and
    assert: \<open>\<not> x1 \<and> \<not> is_decided (hd (get_trail_wl x2))\<close> and
    assert': \<open>\<not> x1b \<and> \<not> is_decided_hd_trail_wl_heur x2b\<close>
begin

lemma st[simp]: \<open>x1 = False\<close>  \<open>x1b = False\<close> and
  x2b_x2: \<open>(x2b, x2) \<in> twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x))\<close>
  using xy xa_x' x'
    twl_st_heur_conflict_ana_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st[of x2b x2]
   xa xc assert
  by (auto simp: is_decided_no_proped_iff xc
    lit_and_ann_of_propagated_st_def hd_xa)

private lemma
  x1c: \<open>x1c \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x2)\<close> and
  x1c_notin: \<open>x1c \<notin># the (get_conflict_wl x2)\<close> and
  not_dec_ge0: \<open>0 < mark_of (hd (get_trail_wl x2))\<close> and
  x2c_dom: \<open>x2c \<in># dom_m (get_clauses_wl x2)\<close> and
  hd_x2: \<open>hd (get_trail_wl x2) = Propagated x1c x2c\<close> and
  \<open>hd (get_clauses_wl x2 \<propto> x2c) = x1c\<close> and
  \<open>get_clauses_wl x2 \<propto> x2c \<noteq> []\<close> and
  ux1c_notin_tl: \<open>- x1c \<notin> set (tl (get_clauses_wl x2 \<propto> x2c))\<close> and
  x1c_notin_tl: \<open>x1c \<notin> set (tl (get_clauses_wl x2 \<propto> x2c))\<close> and
  not_tauto_x2c: \<open>\<not>tautology (mset (get_clauses_wl x2 \<propto> x2c))\<close> and
  dist_x2c: \<open>distinct (get_clauses_wl x2 \<propto> x2c)\<close> and
  not_tauto_resolved: \<open>\<not>tautology (remove1_mset (- x1c) (the (get_conflict_wl x2)
     \<union># mset (tl (get_clauses_wl x2 \<propto> x2c))))\<close> and
  st2[simp]: \<open>x1a = x1c\<close>\<open>x2a = x2c\<close>
proof -
  obtain x xa xb xc where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st x2) x2\<close> and
    x2_x: \<open>(x2, x) \<in> state_wl_l None\<close> and
    y_xa: \<open>(y, xa) \<in> state_wl_l None\<close> and
    \<open>correct_watching x2\<close> and
    x_xb: \<open>(x, xb) \<in> twl_st_l None\<close> and
    xa_xc: \<open>(xa, xc) \<in> twl_st_l None\<close> and
    \<open>cdcl_twl_o\<^sup>*\<^sup>* xc xb\<close> and
    list_invs: \<open>twl_list_invs x\<close> and
    struct: \<open>twl_struct_invs xb\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>\<not> is_decided (hd (get_trail_l x)) \<longrightarrow> 0 < mark_of (hd (get_trail_l x))\<close> and
    \<open>twl_stgy_invs xb\<close> and
    \<open>clauses_to_update xb = {#}\<close> and
    \<open>literals_to_update xb = {#}\<close> and
    confl: \<open>get_conflict xb \<noteq> None\<close> and
    count_dec: \<open>count_decided (get_trail xb) \<noteq> 0\<close> and
    trail_nempty: \<open>get_trail xb \<noteq> []\<close> and
    \<open>get_conflict xb \<noteq> Some {#}\<close> and
    \<open>x1 \<longrightarrow>
     (no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of xb)) \<and>
     (no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of xb))\<close>
    using sor_inv
    unfolding skip_and_resolve_loop_wl_D_inv_def prod.simps xa skip_and_resolve_loop_wl_D_heur_inv_def
    skip_and_resolve_loop_wl_inv_def x' skip_and_resolve_loop_inv_l_def
    skip_and_resolve_loop_inv_def by blast
  show st2[simp]: \<open>x1a = x1c\<close>\<open>x2a = x2c\<close>
    using trail_nempty xy xa_x' x' xc x_xb x2_x
      twl_st_heur_conflict_ana_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st[of x2b x2]
       assert xa
     by (auto simp: is_decided_no_proped_iff xc
       lit_and_ann_of_propagated_st_def hd_xa)
  have \<open>get_conflict_wl x2 \<noteq> None\<close>
    using x2_x y_xa confl x_xb
    by auto
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st x2) (get_trail_wl x2)\<close>
     using \<open>twl_struct_invs xb\<close> literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail lits x2_x x_xb
     by blast
  moreover have trail_nempty_x2: \<open>get_trail_wl x2 \<noteq> []\<close>
    using x2_x y_xa confl x_xb trail_nempty
    by auto
  ultimately show \<open>x1c \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x2)\<close>
    using hd_xa assert
    apply (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)

  have cdcl_confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of xb)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of xb)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of xb)\<close>
    using struct
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by blast+
  then have confl': \<open>\<forall>T. conflicting (state\<^sub>W_of xb) = Some T \<longrightarrow>
       trail (state\<^sub>W_of xb) \<Turnstile>as CNot T\<close> and
    \<open>no_dup (trail (state\<^sub>W_of xb))\<close> and
    confl_annot: \<open>\<And>L mark a b.
        a @ Propagated L mark # b = trail (state\<^sub>W_of xb) \<longrightarrow>
        b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have conflicting: \<open>get_trail_wl x2 \<Turnstile>as CNot (the (get_conflict_wl x2))\<close> and
    \<open>no_dup (get_trail_wl x2)\<close>
    using x2_x y_xa confl x_xb trail_nempty
    by (auto simp: twl_st)
  then show \<open>x1c \<notin># the (get_conflict_wl x2)\<close>
    using hd_xa assert
    by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>)
      (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons dest!: multi_member_split
      dest: in_lits_of_l_defined_litD)
  have \<open>\<not>tautology (the (get_conflict_wl x2))\<close>
    using \<open>get_conflict_wl x2 \<noteq> None\<close> conflict_not_tautology
      struct x2_x x_xb by blast
  have dist_mset:  \<open>distinct_mset (the (get_conflict_wl x2))\<close> and
    \<open>count_decided (get_trail_wl x2) \<noteq> 0\<close>
    using dist x2_x x_xb \<open>get_conflict_wl x2 \<noteq> None\<close> count_dec
    by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        twl_st)
  have \<open>no_dup (get_trail_wl x2)\<close>
    using \<open>no_dup (get_trail_wl x2)\<close> .
  show mark_ge0: \<open>0 < mark_of (hd (get_trail_wl x2))\<close>
    using \<open>\<not> is_decided (hd (get_trail_l x)) \<longrightarrow> 0 < mark_of (hd (get_trail_l x))\<close>
    x2_x assert by auto
  then show \<open>x2c \<in># dom_m (get_clauses_wl x2)\<close> and
    hd_x1c: \<open>hd (get_clauses_wl x2 \<propto> x2c) = x1c\<close> and
    x2c_nempty: \<open>get_clauses_wl x2 \<propto> x2c \<noteq> []\<close>
    using list_invs x2_x assert \<open>get_trail_wl x2 \<noteq> []\<close> hd_xa trail_nempty_x2
    by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
      cases \<open>get_clauses_wl x2 \<propto> x2c\<close>;
      auto simp: twl_list_invs_def all_conj_distrib hd_conv_nth)+

  have lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st x2) (the (get_conflict_wl x2))\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict[OF x2_x struct x_xb lits])
      (use x2_x x_xb confl in auto)
  show hd_x2: \<open>hd (get_trail_wl x2) = Propagated x1c x2c\<close>
    using trail_nempty assert hd_xa
    by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>) auto
  then have \<open>0 < x2c\<close>
    using mark_ge0 by auto
  have \<open>\<not>is_decided (hd (get_trail xb))\<close>
    using trail_nempty trail_nempty_x2 assert hd_xa x_xb x2b_x2 x2_x x_xb
    by (auto simp: twl_st_l_mark_of_is_decided state_wl_l_mark_of_is_decided)
  then have Neg:
    \<open>tl (get_trail_wl x2) \<Turnstile>as CNot (remove1_mset x1c (mset (get_clauses_wl x2 \<propto> x2c))) \<and>
      x1c \<in># mset (get_clauses_wl x2 \<propto> x2c)\<close>
    using confl_annot[of Nil] x2_x x_xb hd_get_trail_twl_st_of_get_trail_l[OF x_xb] trail_nempty
    hd_xa hd_x2 trail_nempty trail_nempty_x2 assert  \<open>0 < x2c\<close>
    twl_st_l_mark_of_hd[OF x_xb] twl_st_l_lits_of_tl[OF x_xb]
    by (cases \<open>get_trail xb\<close>; cases \<open>hd (get_trail xb)\<close>; cases \<open>get_trail_wl x2\<close>)
      (auto simp: twl_st true_annots_true_cls simp del: hd_get_trail_twl_st_of_get_trail_l)

  show \<open>- x1c \<notin> set (tl (get_clauses_wl x2 \<propto> x2c))\<close>
    using Neg hd_x1c x2c_nempty \<open>no_dup (get_trail_wl x2)\<close> hd_x2
    by (cases \<open>get_clauses_wl x2 \<propto> x2c\<close>; cases \<open>get_trail_wl x2\<close>)
      (auto simp: true_annots_true_cls_def_iff_negation_in_model
      dest: in_lits_of_l_defined_litD)
  show \<open>x1c \<notin> set (tl (get_clauses_wl x2 \<propto> x2c))\<close>
    using Neg hd_x1c x2c_nempty \<open>no_dup (get_trail_wl x2)\<close> hd_x2
    by (cases \<open>get_clauses_wl x2 \<propto> x2c\<close>; cases \<open>get_trail_wl x2\<close>)
      (auto simp: true_annots_true_cls_def_iff_negation_in_model
      dest: in_lits_of_l_defined_litD)
  have \<open>\<not>tautology (remove1_mset x1c (mset (get_clauses_wl x2 \<propto> x2c)))\<close>
    apply (rule consistent_CNot_not_tautology[of  \<open>lits_of_l (tl (get_trail_wl x2))\<close>])
    using Neg \<open>no_dup (get_trail_wl x2)\<close>
    by (auto simp: true_annots_true_cls intro!: distinct_consistent_interp
      dest: no_dup_tlD)
  then show \<open>\<not>tautology (mset (get_clauses_wl x2 \<propto> x2c))\<close>
    using Neg multi_member_split[of x1c \<open>mset (get_clauses_wl x2 \<propto> x2c)\<close>] hd_x1c
      \<open>x1c \<notin> set (tl (get_clauses_wl x2 \<propto> x2c))\<close> \<open>- x1c \<notin> set (tl (get_clauses_wl x2 \<propto> x2c))\<close>
    by (cases \<open>get_clauses_wl x2 \<propto> x2c\<close>)
      (auto simp: tautology_add_mset)
  show \<open>distinct (get_clauses_wl x2 \<propto> x2c)\<close>
    using dist x_xb x2_x \<open>x2c \<in># dom_m (get_clauses_wl x2)\<close>
    unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def
    by (auto simp: twl_st ran_m_def dest!: multi_member_split)
  then have \<open>distinct_mset (the (get_conflict_wl x2) \<union># mset (tl (get_clauses_wl x2 \<propto> x2c)))\<close>
    using dist dist_mset
    by (auto)
  then have H: \<open>get_trail_wl x2 \<Turnstile>as
      CNot ((remove1_mset (- x1c) (the (get_conflict_wl x2) \<union># mset (tl (get_clauses_wl x2 \<propto> x2c)))))\<close>
    using Neg hd_x1c trail_nempty_x2 hd_x2 conflicting
    apply (cases \<open>get_clauses_wl x2 \<propto> x2c\<close>; cases \<open>get_trail_wl x2\<close>)
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model distinct_mset_remove1_All)
  show \<open>\<not>tautology (remove1_mset (- x1c) (the (get_conflict_wl x2) \<union># mset (tl (get_clauses_wl x2 \<propto> x2c))))\<close>
    apply (rule consistent_CNot_not_tautology[OF _ H[unfolded true_annots_true_cls]])
    using \<open>no_dup (get_trail_wl x2)\<close>
    by (auto simp: true_annots_true_cls intro!: distinct_consistent_interp
      dest: no_dup_tlD)
qed


lemma atm_is_in_conflict_st_heur_ana_is_in_conflict_st:
  \<open>(uncurry (RETURN oo atm_is_in_conflict_st_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   [\<lambda>(L, S). -L \<notin># the (get_conflict_wl S) \<and> get_conflict_wl S \<noteq> None \<and>
     L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x)) \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using atm_is_in_conflict_st_heur_is_in_conflict_st_ana[THEN fref_to_Down, of y x]
    by (case_tac x, case_tac y)
      (auto simp: )
  done


lemma atm_is_in_conflict_st_heur_iff: \<open>(\<not> atm_is_in_conflict_st_heur (- x1c) x2b) =
        (- x1a \<notin># the (get_conflict_wl x2))\<close>
proof -
  show ?thesis
    unfolding is_in_conflict_st_def[symmetric] is_in_conflict_def[symmetric]
    apply (subst Not_eq_iff)
    apply (rule atm_is_in_conflict_st_heur_ana_is_in_conflict_st[THEN fref_to_Down_unRET_uncurry_Id])
    subgoal
      using confl_x2 x1c x1c_notin by (auto simp: uminus_\<A>\<^sub>i\<^sub>n_iff)
    subgoal
      using x2b_x2 by (auto simp: lit_and_ann_of_propagated_st_heur_def)
    done
qed

lemma ca_lit_and_ann_of_propagated_st_heur_pre:
  \<open>lit_and_ann_of_propagated_st_heur_pre x2b\<close>
  using x1c xa_x' confl_x2 trail_nempty[THEN neq_Nil_conv[THEN iffD1]]
  unfolding xa x' lit_and_ann_of_propagated_st_heur_pre_def
  by (cases x2b; cases x2)
   (auto simp add: twl_st_heur_conflict_ana_def
    trail_pol_def all_atms_def[symmetric] ann_lits_split_reasons_def)

lemma atm_is_in_conflict_st_heur_pre: \<open>atm_is_in_conflict_st_heur_pre (- x1c, x2b)\<close>
  using x1c xa_x' confl_x2
  unfolding atm_is_in_conflict_st_heur_pre_def xa x'
  by (cases x2b)
    (auto simp: twl_st_heur_conflict_ana_def option_lookup_clause_rel_def lookup_clause_rel_def
    atms_of_def all_atms_def)


context
  assumes x1a_notin: \<open>- x1a \<notin># the (get_conflict_wl x2)\<close>
begin

lemma tl_state_wl_heur_pre: \<open>tl_state_wl_heur_pre x2b\<close>
  using trail_nempty x2b_x2 xc x1c assert
  unfolding tl_state_wl_heur_pre_def
  by (cases x2b; cases \<open>get_trail_wl x2\<close>)
    (auto simp: twl_st_heur_conflict_ana_def lit_and_ann_of_propagated_st_heur_def
      is_decided_no_proped_iff trail_pol_nempty
      all_atms_def[symmetric]
    intro: isa_vmtf_le phase_saving_le isa_vmtf_next_search_le
    intro!: vmtf_unset_pre tl_trailt_tr_pre
    dest!: neq_Nil_conv[THEN iffD1]
    dest: multi_member_split)

private lemma tl_state_wl_pre: \<open>tl_state_wl_pre x2\<close>
  using trail_nempty x2b_x2 xc x1c assert hd_x2 x1c_notin x1a_notin not_tauto
    dist_confl count_dec_not0 lits_trail
  unfolding tl_state_wl_pre_def
  by (cases \<open>get_trail_wl x2\<close>)
    (auto simp:
      phase_saving_def atms_of_def vmtf_def is_decided_no_proped_iff
      neq_Nil_conv image_image st)

private lemma length_tl: \<open>length (get_clauses_wl_heur (tl_state_wl_heur x2b)) =
    length (get_clauses_wl_heur x2b)\<close>
  by (cases x2b) (auto simp: tl_state_wl_heur_def)

lemma tl_state_wl_heur_rel:
  \<open>((False, tl_state_wl_heur x2b), False, tl_state_wl x2)
    \<in> bool_rel \<times>\<^sub>f twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x))\<close>
  using x2b_x2 tl_state_wl_pre
  by (auto intro!: tl_state_wl_heur_tl_state_wl[THEN fref_to_Down_unRET] simp: length_tl)

end

context
  assumes x1a_notin: \<open>\<not> - x1a \<notin># the (get_conflict_wl x2)\<close>
begin
lemma maximum_level_removed_eq_count_dec_pre:
  \<open>maximum_level_removed_eq_count_dec_pre (- x1a, x2)\<close>
  using trail_nempty x2b_x2 xc x1c assert hd_x2 x1c_notin x1a_notin not_tauto
    dist_confl count_dec_not0 confl_x2
  unfolding maximum_level_removed_eq_count_dec_pre_def prod.simps
  apply -
  apply (intro conjI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma skip_rel:
  \<open>((- x1c, x2b), - x1a, x2) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_conflict_ana\<close>
  using x2b_x2
  by auto


context
  assumes \<open>maximum_level_removed_eq_count_dec_heur (- x1c) x2b\<close> and
    max_lvl: \<open>maximum_level_removed_eq_count_dec (- x1a) x2\<close>
begin

lemma update_confl_tl_wl_heur_pre:
  \<open>update_confl_tl_wl_heur_pre ((x2c, x1c), x2b)\<close>
  using trail_nempty x2b_x2 xc x1c assert hd_x2 x1c_notin x1a_notin not_tauto
    dist_confl count_dec_not0 confl_x2 no_dup_x2 x1c not_dec_ge0 lits_trail
  unfolding update_confl_tl_wl_heur_pre_def lit_and_ann_of_propagated_st_heur_def
  by (auto simp: twl_st_heur_conflict_ana_def trail_pol_nempty  atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n all_atms_def[symmetric]
     simp del: isasat_input_bounded_def
     dest!: neq_Nil_conv[THEN iffD1]
     intro: phase_saving_le isa_vmtf_le isa_vmtf_next_search_le)

private lemma counts_maximum_level:
  \<open>get_count_max_lvls_heur x2b \<in> counts_maximum_level (get_trail_wl x2) (get_conflict_wl x2)\<close>
  using x2b_x2 unfolding twl_st_heur_conflict_ana_def
  by auto

private lemma card_max_lvl_ge0:
   \<open>Suc 0 \<le> card_max_lvl (get_trail_wl x2) (the (get_conflict_wl x2))\<close>
  using counts_maximum_level confl_x2 max_lvl count_dec_not0
  get_maximum_level_exists_lit[of
      \<open>get_maximum_level (get_trail_wl x2) (remove1_mset (- x1c) (the (get_conflict_wl x2)))\<close>
     \<open>(get_trail_wl x2)\<close> \<open>remove1_mset (- x1c) (the (get_conflict_wl x2))\<close>]
  unfolding counts_maximum_level_def maximum_level_removed_eq_count_dec_def card_max_lvl_def
  get_maximum_level_remove_def
  by (auto dest!: in_diffD dest: multi_member_split)

lemma update_confl_tl_wl_pre:
  \<open>update_confl_tl_wl_pre ((x2a, x1a), x2)\<close>
  using trail_nempty x2b_x2 xc x1c assert hd_x2 x1c_notin x1a_notin not_tauto
    dist_confl count_dec_not0 confl_x2 no_dup_x2 x1c not_dec_ge0 lits_trail
    x2c_dom lits lits_confl card_max_lvl_ge0 x1c_notin_tl ux1c_notin_tl not_tauto_x2c
    dist_x2c not_tauto_resolved
  unfolding update_confl_tl_wl_pre_def prod.simps
  by (simp add: all_atms_def[symmetric])

lemma update_confl_tl_rel: \<open>(((x2c, x1c), x2b), (x2a, x1a), x2)
    \<in> nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x))\<close>
  using x2b_x2 by auto

end
end

declare st[simp del] st2[simp del]
end

end

lemma skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D:
  \<open>(skip_and_resolve_loop_wl_D_heur, skip_and_resolve_loop_wl_D)
    \<in> twl_st_heur_conflict_ana' r \<rightarrow>\<^sub>f \<langle>twl_st_heur_conflict_ana' r\<rangle>nres_rel\<close>
proof -
  have H[refine0]: \<open>(x, y) \<in> twl_st_heur_conflict_ana \<Longrightarrow>
           ((False, x), False, y)
           \<in> bool_rel \<times>\<^sub>f
              twl_st_heur_conflict_ana' (length (get_clauses_wl_heur x))\<close> for x y
    by auto

  show ?thesis
    supply [[goals_limit=1]]
    unfolding skip_and_resolve_loop_wl_D_heur_def skip_and_resolve_loop_wl_D_def
      Let_def
      maximum_level_removed_eq_count_dec_def[symmetric]
      get_maximum_level_remove_def[symmetric]
    apply (intro frefI nres_relI)
    apply (refine_vcg
        update_confl_tl_wl_heur_update_confl_tl_wl[THEN fref_to_Down_curry2, unfolded comp_def]
        maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec
          [THEN fref_to_Down_curry_no_nres_Id]
       tl_state_wl_heur_tl_state_wl[THEN fref_to_Down_no_nres])
    subgoal by auto
    subgoal for x y xa x'
      apply (cases x'; cases xa)
      by (rule sor_heur_inv)
    subgoal
      by (rule conflict_ana_same_cond)
    subgoal by (auto simp: )
    subgoal by (auto simp:)
    subgoal by (rule ca_lit_and_ann_of_propagated_st_heur_pre)
    subgoal
      by (rule atm_is_in_conflict_st_heur_pre)
    subgoal for x y xa x' x1 x2 x1a x2a x1b x2b x1c x2c
      by (rule atm_is_in_conflict_st_heur_iff)
    subgoal
      by (rule tl_state_wl_heur_pre)
    subgoal by (rule tl_state_wl_heur_rel)
    subgoal
      by (rule maximum_level_removed_eq_count_dec_pre)
    subgoal
      by (rule skip_rel)
    subgoal
      by (rule update_confl_tl_wl_heur_pre)
    subgoal
      by (rule update_confl_tl_wl_pre)
    subgoal
      by (rule update_confl_tl_rel)
    subgoal
      by auto
    subgoal
      by auto
    done
qed

definition (in -) get_count_max_lvls_code where
  \<open>get_count_max_lvls_code = (\<lambda>(_, _, _, _, _, _, _, clvls, _). clvls)\<close>

lemma get_count_max_lvls_heur_hnr[sepref_fr_rules]:
  \<open>(return o get_count_max_lvls_code, RETURN o get_count_max_lvls_heur) \<in>
     isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  subgoal for x x'
    by (cases x; cases x')
     (sep_auto simp: isasat_unbounded_assn_def get_count_max_lvls_code_def
        elim!: mod_starE)
  done

lemma get_count_max_lvls_heur_fast_hnr[sepref_fr_rules]:
  \<open>(return o get_count_max_lvls_code, RETURN o get_count_max_lvls_heur) \<in>
     isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  subgoal for x x'
    by (cases x; cases x')
     (sep_auto simp: isasat_bounded_assn_def get_count_max_lvls_code_def
        elim!: mod_starE)
  done

sepref_definition maximum_level_removed_eq_count_dec_code
  is \<open>uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  by sepref

sepref_definition maximum_level_removed_eq_count_dec_fast_code
  is \<open>uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  by sepref

declare maximum_level_removed_eq_count_dec_code.refine[sepref_fr_rules]
  maximum_level_removed_eq_count_dec_fast_code.refine[sepref_fr_rules]

lemma is_decided_hd_trail_wl_heur_alt_def:
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>(M, _). is_None (snd (last_trail_pol M)))\<close>
  by (auto intro!: ext simp: is_decided_hd_trail_wl_heur_def)

sepref_definition is_decided_hd_trail_wl_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[is_decided_hd_trail_wl_heur_pre]\<^sub>a
        isasat_unbounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_heur_alt_def isasat_unbounded_assn_def is_decided_hd_trail_wl_heur_pre_def
  by sepref

sepref_definition is_decided_hd_trail_wl_fast_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[is_decided_hd_trail_wl_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_heur_alt_def isasat_bounded_assn_def is_decided_hd_trail_wl_heur_pre_def
  by sepref

declare is_decided_hd_trail_wl_code.refine[sepref_fr_rules]
  is_decided_hd_trail_wl_fast_code.refine[sepref_fr_rules]

sepref_definition lit_and_ann_of_propagated_st_heur_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[lit_and_ann_of_propagated_st_heur_pre]\<^sub>a
       isasat_unbounded_assn\<^sup>k \<rightarrow> (unat_lit_assn *a nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def isasat_unbounded_assn_def lit_and_ann_of_propagated_st_heur_pre_def
  by sepref

sepref_definition lit_and_ann_of_propagated_st_heur_fast_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[lit_and_ann_of_propagated_st_heur_pre]\<^sub>a
       isasat_bounded_assn\<^sup>k \<rightarrow> (unat_lit_assn *a uint64_nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def isasat_bounded_assn_def lit_and_ann_of_propagated_st_heur_pre_def
  by sepref

declare lit_and_ann_of_propagated_st_heur_fast_code.refine[sepref_fr_rules]
  lit_and_ann_of_propagated_st_heur_code.refine[sepref_fr_rules]

declare isa_vmtf_unset_code.refine[sepref_fr_rules]

sepref_definition tl_state_wl_heur_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[tl_state_wl_heur_pre]\<^sub>a
      isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  supply [[goals_limit=1]] if_splits[split] lit_of_last_trail_pol_def[simp]
  unfolding tl_state_wl_heur_alt_def[abs_def] isasat_unbounded_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp] short_circuit_conv
  unfolding tl_state_wl_heur_pre_def
  by sepref

sepref_definition tl_state_wl_heur_fast_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[tl_state_wl_heur_pre]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] if_splits[split] lit_of_last_trail_pol_def[simp]
  unfolding tl_state_wl_heur_alt_def[abs_def] isasat_bounded_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp] short_circuit_conv lit_of_last_trail_pol_def
  unfolding tl_state_wl_heur_pre_def
  by sepref

declare
  tl_state_wl_heur_code.refine[sepref_fr_rules]
  tl_state_wl_heur_fast_code.refine[sepref_fr_rules]

(*
lemma option_lookup_clause_assn_the[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>C. C \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: lookup_clause_assn_def option_lookup_clause_assn_def lookup_clause_rel_def
       hr_comp_def option_lookup_clause_rel_def)

lemma option_lookup_clause_assn_Some[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. (False, C)), RETURN o Some) \<in> lookup_clause_assn\<^sup>d \<rightarrow>\<^sub>a option_lookup_clause_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: lookup_clause_assn_def option_lookup_clause_assn_def lookup_clause_rel_def
       hr_comp_def option_lookup_clause_rel_def bool_assn_alt_def)

lemma lookup_clause_assn_op_nset_is_emty[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, _). n = 0), RETURN o op_mset_is_empty) \<in> lookup_clause_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi, case_tac xi)
  by (sep_auto simp: lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    uint32_nat_assn_0_eq uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)+

*)

sepref_register update_confl_tl_wl_heur
sepref_definition update_confl_tl_wl_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[update_confl_tl_wl_heur_pre]\<^sub>a
  nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> bool_assn *a isasat_unbounded_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  unfolding update_confl_tl_wl_heur_def isasat_unbounded_assn_def
    update_confl_tl_wl_heur_pre_def PR_CONST_def
  by sepref

sepref_definition update_confl_tl_wl_fast_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), S). update_confl_tl_wl_heur_pre ((i, L), S) \<and> isasat_fast S]\<^sub>a
  uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool_assn *a isasat_bounded_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]] isasat_fast_length_leD[dest]
  unfolding update_confl_tl_wl_heur_def isasat_bounded_assn_def
    update_confl_tl_wl_heur_pre_def PR_CONST_def
  supply merge_conflict_m_def[simp]
  by sepref (* slow *)

declare update_confl_tl_wl_code.refine[sepref_fr_rules]
  update_confl_tl_wl_fast_code.refine[sepref_fr_rules]

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


sepref_definition is_in_option_lookup_conflict_code
  is \<open>uncurry (RETURN oo is_in_option_lookup_conflict)\<close>
  :: \<open>[\<lambda>(L, (c, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_in_option_lookup_conflict_alt_def is_in_lookup_conflict_def PROTECT_def
  by sepref


(*
context isasat_input_bounded
begin

sepref_register is_in_option_lookup_conflict

lemma conflict_remove1_code_op_nset_delete[sepref_fr_rules]:
  \<open>(uncurry is_in_option_lookup_conflict_code, uncurry (RETURN \<circ>\<circ> atm_is_in_conflict))
    \<in> [\<lambda>(L, D). D \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> -L \<notin># the D]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>k \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
            (\<lambda>(L, D). D \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> - L \<notin># the D)
            (\<lambda>_ (L, c, n, xs). atm_of L < length xs) (\<lambda>_. True)]\<^sub>a
           hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k)
               (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel) \<rightarrow>
           hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF is_in_option_lookup_conflict_code.refine
        is_in_option_lookup_conflict_atm_is_in_conflict]
    unfolding op_mset_delete_def
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that neq0_conv
    unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (fastforce simp: image_image twl_st_heur_conflict_ana_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def option_lookup_clause_assn_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep hr_comp_prod_conv
      lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_register atm_is_in_conflict_st_heur
sepref_thm atm_is_in_option_lookup_conflict_code
  is \<open>uncurry (RETURN oo atm_is_in_conflict_st_heur)\<close>
  :: \<open>[atm_is_in_conflict_st_heur_pre]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding atm_is_in_conflict_st_heur_alt_def atm_is_in_conflict_def[symmetric]
    atm_is_in_conflict_st_heur_pre_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) atm_is_in_option_lookup_conflict_code
  uses isasat_input_bounded.atm_is_in_option_lookup_conflict_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) atm_is_in_option_lookup_conflict_code_def

lemmas atm_is_in_option_lookup_conflict_code_def[sepref_fr_rules] =
   atm_is_in_option_lookup_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm atm_is_in_option_lookup_conflict_fast_code
  is \<open>uncurry (RETURN oo atm_is_in_conflict_st_heur)\<close>
  :: \<open>[atm_is_in_conflict_st_heur_pre]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding atm_is_in_conflict_st_heur_alt_def atm_is_in_conflict_def[symmetric]
    atm_is_in_conflict_st_heur_pre_def isasat_bounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) atm_is_in_option_lookup_conflict_fast_code
  uses isasat_input_bounded.atm_is_in_option_lookup_conflict_fast_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) atm_is_in_option_lookup_conflict_fast_code_def

lemmas atm_is_in_option_lookup_conflict_fast_code_def[sepref_fr_rules] =
   atm_is_in_option_lookup_conflict_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

end

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

lemma skip_and_resolve_loop_wl_D_heur_inv_nempty:
  \<open>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0 (brk, S) \<Longrightarrow> get_trail_wl_heur S \<noteq> []\<close>
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def skip_and_resolve_loop_inv_l_def
    skip_and_resolve_loop_inv_def skip_and_resolve_loop_wl_inv_def
    skip_and_resolve_loop_wl_D_inv_def prod.case
  apply -
  apply normalize_goal+
   by (auto simp: twl_st_heur_ana_state_simp)
*)
lemma skip_and_resolve_loop_wl_DI:
  assumes
    \<open>skip_and_resolve_loop_wl_D_heur_inv S (b, T)\<close>
  shows \<open>is_decided_hd_trail_wl_heur_pre T\<close>
  using assms unfolding skip_and_resolve_loop_wl_D_heur_inv_def prod.simps
  by blast

sepref_definition atm_is_in_conflict_st_heur_fast_code
  is \<open>uncurry (RETURN oo atm_is_in_conflict_st_heur)\<close>
  :: \<open>[atm_is_in_conflict_st_heur_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding atm_is_in_conflict_st_heur_def atm_is_in_conflict_st_heur_pre_def isasat_unbounded_assn_def
    atm_in_conflict_lookup_def
  by sepref

sepref_definition atm_is_in_conflict_st_heur_code
  is \<open>uncurry (RETURN oo atm_is_in_conflict_st_heur)\<close>
  :: \<open>[atm_is_in_conflict_st_heur_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding atm_is_in_conflict_st_heur_def atm_is_in_conflict_st_heur_pre_def isasat_bounded_assn_def
    atm_in_conflict_lookup_def
  by sepref

declare atm_is_in_conflict_st_heur_fast_code.refine[sepref_fr_rules]
  atm_is_in_conflict_st_heur_code.refine[sepref_fr_rules]

sepref_register skip_and_resolve_loop_wl_D is_in_conflict_st
sepref_definition skip_and_resolve_loop_wl_D
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref

lemma isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv:
  \<open>isasat_fast x \<Longrightarrow>
       skip_and_resolve_loop_wl_D_heur_inv x
        (False, a2') \<Longrightarrow> isasat_fast a2'\<close>
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def isasat_fast_def
  by auto

sepref_definition skip_and_resolve_loop_wl_D_fast
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
    isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref (* slow *)

declare skip_and_resolve_loop_wl_D_fast.refine[sepref_fr_rules]
  skip_and_resolve_loop_wl_D.refine[sepref_fr_rules]


end
