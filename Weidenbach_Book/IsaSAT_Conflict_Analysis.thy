theory IsaSAT_Conflict_Analysis
  imports IsaSAT_Setup Watched_Literals_Heuristics
begin

paragraph \<open>Skip and resolve\<close>

context isasat_input_bounded_nempty
begin


definition get_conflict_wll_is_Nil_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool nres\<close> where
  \<open>get_conflict_wll_is_Nil_heur = (\<lambda>(M, N, D, Q, W, _).
   do {
     if is_None D
     then RETURN False
     else do{ ASSERT(D \<noteq> None); RETURN (Multiset.is_empty (the D))}
   })\<close>


lemma get_conflict_wll_is_Nil_heur_get_conflict_wll_is_Nil:
  \<open>(PR_CONST get_conflict_wll_is_Nil_heur, get_conflict_wll_is_Nil) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: get_conflict_wll_is_Nil_heur_def get_conflict_wll_is_Nil_def twl_st_heur_def
      split: option.splits)


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


definition  (in isasat_input_ops) maximum_level_removed_eq_count_dec where
  \<open>maximum_level_removed_eq_count_dec L S \<longleftrightarrow>
      get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L =
       count_decided (get_trail_wl S)\<close>

definition  (in isasat_input_ops) maximum_level_removed_eq_count_dec_heur where
  \<open>maximum_level_removed_eq_count_dec_heur L S \<longleftrightarrow>
      count_decided_st S = zero_uint32_nat \<or> get_count_max_lvls_heur S > one_uint32_nat\<close>

definition maximum_level_removed_eq_count_dec_pre where
  \<open>maximum_level_removed_eq_count_dec_pre =
     (\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [])\<close>

lemma maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec:
  \<open>(uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur),
      uncurry (RETURN oo maximum_level_removed_eq_count_dec)) \<in>
   [maximum_level_removed_eq_count_dec_pre]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using get_maximum_level_remove_count_max_lvls[of \<open>fst x\<close> \<open>get_trail_wl (snd y)\<close>
      \<open>the (get_conflict_wl (snd y))\<close>]
    by (cases x)
       (auto simp: count_decided_st_def counts_maximum_level_def twl_st_heur_def
     maximum_level_removed_eq_count_dec_heur_def maximum_level_removed_eq_count_dec_def
     maximum_level_removed_eq_count_dec_pre_def)
  done

definition (in isasat_input_ops) is_decided_hd_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>S. is_decided (hd (get_trail_wl_heur S)))\<close>

lemma is_decided_hd_trail_wl_heur_alt_def:
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>(M, _). is_decided (hd M))\<close>
  unfolding is_decided_hd_trail_wl_heur_def by auto

lemma is_decided_hd_trail_wl_heur_is_decided_hd_trail_wl:
  \<open>(RETURN o is_decided_hd_trail_wl_heur, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>f twl_st_heur \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: is_decided_hd_trail_wl_heur_def is_decided_hd_trail_wl_def twl_st_heur_def)

lemma get_trail_wl_heur_def: \<open>get_trail_wl_heur = (\<lambda>(M, S). M)\<close>
  by (intro ext, rename_tac S, case_tac S) auto

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition (in isasat_input_ops) lit_and_ann_of_propagated_st_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<times> nat\<close>
where
  \<open>lit_and_ann_of_propagated_st_heur = (\<lambda>(M, _). (lit_of (hd M), mark_of (hd M)))\<close>

lemma mark_of_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in>
    [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
  by (sep_auto simp: nat_ann_lit_rel_def)+

lemma lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
   \<open>(RETURN o lit_and_ann_of_propagated_st_heur, RETURN o lit_and_ann_of_propagated_st) \<in>
   [\<lambda>S. is_proped (hd (get_trail_wl S))]\<^sub>f twl_st_heur \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y; case_tac x; case_tac y; case_tac \<open>hd (fst x)\<close>)
  by (auto simp: twl_st_heur_def lit_and_ann_of_propagated_st_heur_def
      lit_and_ann_of_propagated_st_def)

lemma twl_st_heur_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
  \<open>(x, y) \<in> twl_st_heur \<Longrightarrow> is_proped (hd (get_trail_wl y)) \<Longrightarrow>
    lit_and_ann_of_propagated_st_heur x = lit_and_ann_of_propagated_st y\<close>
  by (cases \<open>hd (get_trail_wl y)\<close>)
    (auto simp: twl_st_heur_def lit_and_ann_of_propagated_st_heur_def
      lit_and_ann_of_propagated_st_def)

definition (in isasat_input_ops) tl_state_wl_heur_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>tl_state_wl_heur_pre =
      (\<lambda>(M, N, D, WS, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, _). M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A))\<close>

definition (in isasat_input_ops) tl_state_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, \<phi>, clvls).
       (tl M, N, D, WS, Q, vmtf_unset (atm_of (lit_of (hd M))) vmtf, \<phi>, clvls))\<close>

lemma (in isasat_input_ops) tl_state_wl_heur_alt_def:
    \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, \<phi>, clvls).
      (let L = lit_of (hd M) in
       (tl M, N, D, WS, Q, vmtf_unset (atm_of L) vmtf, \<phi>, clvls)))\<close>
  by (auto simp: tl_state_wl_heur_def Let_def)

(* TODO remove
lemma literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0:
  assumes
    \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    nil: \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>lit_of (hd (get_trail_wl S)) \<in> snd ` D\<^sub>0\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then show ?thesis
     using nil \<L>\<^sub>a\<^sub>l\<^sub>l by (cases S; cases \<open>get_trail_wl S\<close>)
        (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def
          in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff image_image mset_take_mset_drop_mset' clauses_def
          is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def)
qed
*)

(* TODO: adapt this code to early breaks in skip_and_resolve! *)
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
  shows \<open>card_max_lvl (tl a) y =
      (if (lit_of(hd a) \<in># y \<or> -lit_of(hd a) \<in># y) \<and> count_decided a \<noteq> 0
       then card_max_lvl a y - 1 else card_max_lvl a y)\<close>
  using assms by (cases a) (auto simp: card_max_lvl_Cons)
end

context isasat_input_bounded_nempty
begin

definition (in isasat_input_ops) tl_state_wl_pre where
  \<open>tl_state_wl_pre = (\<lambda>S. get_trail_wl S \<noteq> [] \<and> lit_of(hd (get_trail_wl S)) \<in> snd ` D\<^sub>0 \<and>
     (lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
     -(lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
    \<not>tautology (the (get_conflict_wl S)) \<and>
    distinct_mset (the (get_conflict_wl S)) \<and>
    \<not>is_decided (hd (get_trail_wl S)))\<close>

lemma tl_state_out_learned:
   \<open>lit_of (hd a) \<notin># the at \<Longrightarrow>
       - lit_of (hd a) \<notin># the at \<Longrightarrow>
       \<not> is_decided (hd a) \<Longrightarrow>
       out_learned (tl a) at an \<longleftrightarrow> out_learned a at an\<close>
  by (cases a)  (auto simp: out_learned_def get_level_cons_if atm_of_eq_atm_of
      intro!: filter_mset_cong)

lemma tl_state_wl_heur_tl_state_wl:
  \<open>(RETURN o tl_state_wl_heur, RETURN o tl_state_wl) \<in>
  [tl_state_wl_pre]\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: twl_st_heur_def tl_state_wl_heur_def tl_state_wl_def vmtf_unset_vmtf_tl
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff phase_saving_def counts_maximum_level_def
    card_max_lvl_tl tl_state_wl_pre_def tl_state_out_learned
    dest: no_dup_tlD)

(* TODO KILL
lemma twl_struct_invs_confl:
  assumes
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close>
  shows
     \<open>\<not>tautology (the (get_conflict_wl S))\<close> and
     \<open>distinct_mset (the (get_conflict_wl S))\<close> and
     \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> -L \<in> lits_of_l (get_trail_wl S)\<close>
     \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> L \<notin> lits_of_l (get_trail_wl S)\<close>
proof -
  obtain M N U D NE UE Q W where
    S: \<open>S = (M, N, U, Some D, NE, UE, W, Q)\<close>
    using confl by (cases S; cases \<open>get_conflict_wl S\<close>; cases \<open>hd (get_trail_wl S)\<close>;
        cases \<open>get_trail_wl S\<close>) auto
  have
     confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     M_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using assms unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_struct_invs_def
    by auto
  have dist_D: \<open>distinct_mset D\<close>
    using dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  then show \<open>distinct_mset (the (get_conflict_wl S))\<close>
    by (auto simp: S)

  have M_D: \<open>convert_lits_l N M \<Turnstile>as CNot D\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: S true_annots_true_cls)

  have M_D': \<open>M \<Turnstile>as CNot D\<close>
    using M_D by (auto simp: true_annots_true_cls split: if_splits)

  have cons: \<open>consistent_interp (lits_of_l M)\<close> and n_d: \<open>no_dup M\<close>
    using M_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S)
  have tauto_D: \<open>\<not>tautology D\<close>
    using M_D' cons consistent_CNot_not_tautology[of \<open>lits_of_l M\<close> D]
    by (auto dest!: distinct_consistent_interp simp: true_annots_true_cls)
  then show \<open> \<not> tautology (the (get_conflict_wl S))\<close>
    by (auto simp: S)

  show H: \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> -L \<in> lits_of_l (get_trail_wl S)\<close>
    using M_D' unfolding S true_annots_true_cls_def_iff_negation_in_model
    by auto
  show \<open>L \<in># the (get_conflict_wl S) \<Longrightarrow> L \<notin> lits_of_l (get_trail_wl S)\<close> for L
    using H[of L] n_d
    unfolding S true_annots_true_cls_def_iff_negation_in_model
    by (auto dest: no_dup_consistentD)
qed
*)

definition (in -) get_max_lvl_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>get_max_lvl_st S L = get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L\<close>


definition (in -) lookup_conflict_remove1 :: \<open>nat literal \<Rightarrow> lookup_clause_rel \<Rightarrow> lookup_clause_rel\<close> where
  \<open>lookup_conflict_remove1 =
     (\<lambda>L (n,xs). if xs ! (atm_of L) = None then (n, xs) else (n-1, xs [atm_of L := None]))\<close>

lemma lookup_conflict_remove1:
  \<open>(uncurry (RETURN oo lookup_conflict_remove1), uncurry (RETURN oo remove1_mset)) \<in>
  [\<lambda>(L,C). L \<in># C \<and> -L \<notin># C \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f lookup_clause_rel \<rightarrow> \<langle>lookup_clause_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac y; case_tac x)
  subgoal for x y a b aa ab c
    using mset_as_position_remove[of c b \<open>atm_of aa\<close>]
    by (cases \<open>aa\<close>)
       (auto simp: lookup_clause_rel_def lookup_conflict_remove1_def  lookup_clause_rel_atm_in_iff minus_notin_trivial2
      size_remove1_mset_If in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff minus_notin_trivial mset_as_position_in_iff_nth)
   done
(* TODO port
lemma
  fixes S and C clvls :: nat
  defines [simp]:
     \<open>E \<equiv> (mset (tl ((get_clauses_wl S)!C)) \<union># the (get_conflict_wl S))\<close>
  assumes invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C < length (get_clauses_wl S)\<close> and
    L_confl: \<open>-L \<in># the (get_conflict_wl S)\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close> and
    twl_list: \<open>twl_list_invs (st_l_of_wl None S)\<close> and
    C': \<open>C > 0\<close>
  shows
    resolve_cls_wl'_union_uminus_positive_index:
      \<open>resolve_cls_wl' S C L = remove1_mset (-L) E\<close>
       (is \<open>?Res\<close>) and
    resolve_cls_wl'_not_tauto_confl: \<open>\<not>tautology (the (get_conflict_wl S))\<close> (is ?tauto) and
    resolve_cls_wl'_not_tauto_cls: \<open>\<not>tautology (mset (get_clauses_wl S ! C))\<close>
      (is \<open>?tauto_cls\<close>) and
    resolve_cls_wl'_L_in_cls: \<open>L \<in> set (get_clauses_wl S ! C)\<close> (is \<open>?L_in_cls\<close>) and
    resolve_cls_wl'_L_notin_cls: \<open>-L \<notin> set (get_clauses_wl S ! C)\<close> (is \<open>?uL_notin_cls\<close>) and
    resolve_cls_wl'_L_notin_tl_cls: \<open>L \<notin> set (tl (get_clauses_wl S ! C))\<close>
       (is \<open>?L_notin_tl_cls\<close>) and
    resolve_cls_wl'_in:
      \<open>-L \<in># E\<close>
      (is \<open>?L_in_union\<close>) and
    resolve_cls_wl'_notin:
      \<open>L \<notin># E\<close>
      (is \<open>?L_notin_union\<close>) and
    resolve_cls_wl'_not_tauto: \<open>\<not> tautology E\<close> and
    resolve_cls_wl'_card_max_lvl:
       \<open>card_max_lvl (get_trail_wl S) E = card_max_lvl (tl (get_trail_wl S))
         (E - {#-lit_of (hd (get_trail_wl S))#}) + 1\<close>(is \<open>?Max\<close>) and
    resolve_helper_notin_conflict:
       \<open>lit_of (hd (get_trail_wl S)) \<notin># the (get_conflict_wl S)\<close> and
    resolve_helper_seperated:
      \<open>La \<in> set (tl (get_clauses_wl S ! C)) \<Longrightarrow> - La \<in># the (get_conflict_wl S) \<Longrightarrow> False\<close>
proof -
  obtain M N U D NE UE Q W where
    S: \<open>S = (Propagated L C # M, N, U, Some D, NE, UE, W, Q)\<close>
    using confl tr by (cases S; cases \<open>get_conflict_wl S\<close>; cases \<open>hd (get_trail_wl S)\<close>;
        cases \<open>get_trail_wl S\<close>) auto
  obtain D' where
    D: \<open>D = add_mset (-L) D'\<close>
    using L_confl by (auto simp: S dest: multi_member_split)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding twl_struct_invs_def by fast
  then have
     confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     M_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>
     unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have dist_D: \<open>distinct_mset D\<close>
    using dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  have undef_L: \<open>undefined_lit M L\<close> and n_d: \<open>no_dup M\<close>
    using M_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S split: if_splits)
  have M_D: \<open>Propagated L (mset (N ! C)) # convert_lits_l N M \<Turnstile>as CNot D\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases C) (auto simp: S true_annots_true_cls)

  have M_D': \<open>Propagated L C # M \<Turnstile>as CNot D\<close>
    using M_D by (auto simp: true_annots_true_cls split: if_splits)
  have tauto_D: \<open>\<not>tautology D\<close>
    using M_D' n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l (Propagated L C # M)\<close> D]
    by (auto dest!: distinct_consistent_interp simp: true_annots_true_cls)
  then show ?tauto
    by (auto simp: S)
  have L_D': \<open>L \<notin># D'\<close>
    using M_D' undef_L by (auto simp: true_annots_true_cls_def_iff_negation_in_model
        Decided_Propagated_in_iff_in_lits_of_l D uminus_lit_swap)
 then show \<open>lit_of (hd (get_trail_wl S)) \<notin># the (get_conflict_wl S)\<close>
   by (auto simp: S D)

  have \<open>L = N ! C ! 0\<close>
    using C' twl_list by (auto simp: S twl_list_invs_def)
  moreover have \<open>length (N!C) \<ge> 2\<close>
    using twl_struct_invs_length_clause_ge_2'[OF assms(2) C'] C by (auto simp: S)
  ultimately have C'': \<open>mset (N!C) = add_mset L (mset (tl (N!C)))\<close>
    by (cases \<open>N!C\<close>) (auto simp: S twl_list_invs_def)
  have \<open>L \<in># mset (N ! C)\<close> and
    M_C: \<open>M \<Turnstile>as CNot (mset (N!C) - {#L#})\<close>
    using C C' confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (fastforce simp: S)+

  define C' where \<open>C' = mset (tl (N!C))\<close>
  have M_C': \<open>M \<Turnstile>as CNot C'\<close>
    using M_C unfolding C'_def C''
    by auto
  have uL_C': \<open>-L \<notin># C'\<close> \<open>L \<notin># C'\<close>
    using M_C undef_L by (auto simp: C'' true_annots_true_cls_def_iff_negation_in_model
        Decided_Propagated_in_iff_in_lits_of_l C'_def)
  then show tauto_C: ?tauto_cls
    using M_C n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l M\<close> \<open>C'\<close>]
    by (auto 5 5 dest!: distinct_consistent_interp
        simp: tautology_add_mset true_annots_true_cls C' C'' S C'_def[symmetric])
  have get_clss_S: \<open>get_clauses_wl S = N\<close>
    by (auto simp: S)
  show ?L_in_cls
    unfolding in_multiset_in_set[symmetric] get_clss_S C'' by simp

  have n_d_L: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> False\<close> for L
    using distinct_consistent_interp[OF n_d] by (auto simp: consistent_interp_def)
  have dist_C: \<open>distinct_mset (mset (N ! C))\<close>
    using C C' dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
   have \<open>L \<notin># D'\<close>
    using tauto_D by (auto simp: tautology_add_mset D S)
   moreover have [simp]: \<open>distinct_mset D'\<close> \<open>distinct_mset C'\<close>
    using dist_D dist_C unfolding D C'' C' C'_def by auto
   ultimately show ?Res
    using C C' uL_C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
         minus_notin_trivial S C'_def[symmetric])
  show ?L_in_union
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        S)
  show ?L_notin_union
    using C C' uL_C' dist_D L_D' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        S  C'_def[symmetric] dest: in_diffD)
  have [simp]: \<open>L \<notin># D'\<close>
    using undef_L n_d M_D' M_C
    by (auto 5 5 simp: C'' D true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l)
  have H: \<open>La \<in># C' \<Longrightarrow> - La \<in># D' \<Longrightarrow> False\<close> for La
    using M_D' M_C' undef_L L_D' n_d_L
    by (fastforce simp: true_annots_true_cls_def_iff_negation_in_model
        Decided_Propagated_in_iff_in_lits_of_l D uminus_lit_swap C'_def[symmetric]
        dest!: multi_member_split)

  then show \<open>\<not> tautology E\<close>
    using uL_C' dist_D tauto_C tauto_D L_D'
    by (fastforce simp: S C'' tautology_add_mset  C'_def[symmetric]
        distinct_mset_in_diff D minus_notin_trivial tautology_decomp')
  then have \<open>card_max_lvl (Propagated L C # M) (add_mset (-L) (C' \<union># D')) =
       card_max_lvl M (C' \<union># D') + 1\<close>
    apply (subst card_max_lvl_Cons)
    using undef_L n_d tauto_C dist_C uL_C' dist_D
    by (auto simp: S C'' D C'_def[symmetric] tautology_add_mset
        card_max_lvl_add_mset)
  then show ?Max
    using uL_C'
    by (auto simp: S resolve_cls_wl'_def C'' D C'_def[symmetric])
  show ?L_notin_tl_cls and ?uL_notin_cls
    using uL_C' unfolding set_mset_mset[symmetric] S get_clauses_wl.simps C'_def[symmetric] C''
    by (auto simp: S)
  fix La
  show \<open>La \<in> set (tl (get_clauses_wl S ! C)) \<Longrightarrow> - La \<in># the (get_conflict_wl S) \<Longrightarrow> False\<close>
    using H uL_C' by (auto simp: S C'_def D)
qed
*)

definition (in isasat_input_ops) update_confl_tl_wl_heur
  :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_confl_tl_wl_heur = (\<lambda>C L (M, N, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, outl, stats). do {
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      (D', clvls, lbd, outl) \<leftarrow> merge_conflict_m M N C D clvls lbd outl;
      let D' = remove1_mset (-L) (the D');
      RETURN (False, (tl M, N, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf,
          save_phase L \<phi>, fast_minus clvls one_uint32_nat, cach, lbd, outl, stats))
   })\<close>

lemma card_max_lvl_remove1_mset_hd:
  \<open>-lit_of (hd M) \<in># y \<Longrightarrow> is_proped (hd M) \<Longrightarrow>
     card_max_lvl M (remove1_mset (-lit_of (hd M)) y) = card_max_lvl M y - 1\<close>
  by (cases M)  (auto dest!: multi_member_split simp: card_max_lvl_add_mset)

lemma update_confl_tl_wl_heur_state_helper:
   \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<Longrightarrow> get_trail_wl S \<noteq> [] \<Longrightarrow>
    is_proped (hd (get_trail_wl S)) \<Longrightarrow> L = lit_of (hd (get_trail_wl S))\<close>
  by (cases S; cases \<open>hd (get_trail_wl S)\<close>) auto

lemma (in -) not_ge_Suc0: \<open>\<not>Suc 0 \<le> n \<longleftrightarrow> n = 0\<close> (* WTF *)
  by auto

(* TODO
lemma card_max_lvl_ge_1:
  assumes \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>get_conflict_wl S \<noteq> Some {#}\<close>
  shows
   \<open>card_max_lvl (get_trail_wl S) (the (get_conflict_wl S)) \<ge> Suc 0\<close>
  using assms unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
     cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
  by (cases S) (auto simp: card_max_lvl_def not_ge_Suc0 filter_mset_empty_conv)
*)
definition update_confl_tl_wl_pre where
  \<open>update_confl_tl_wl_pre = (\<lambda>((C, L), S). 
(*       twl_struct_invs (twl_st_of_wl None S) \<and>
      twl_stgy_invs (twl_st_of_wl None S) \<and>
      twl_list_invs (st_l_of_wl None S) \<and> *)
      C \<in># dom_m (get_clauses_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> - L \<in># the (get_conflict_wl S) \<and>
      (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and> L \<in> snd ` D\<^sub>0 \<and>
      is_proped (hd (get_trail_wl S)) \<and>
      C > 0)\<close>

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

lemma (in isasat_input_ops) phase_saving_save_phase[simp]: 
  \<open>phase_saving (save_phase L \<phi>) \<longleftrightarrow> phase_saving \<phi>\<close>
  by (auto simp: phase_saving_def save_phase_def)

lemma update_confl_tl_wl_heur_update_confl_tl_wl:
  \<open>(uncurry2 (update_confl_tl_wl_heur), uncurry2 (RETURN ooo update_confl_tl_wl)) \<in>
  [update_confl_tl_wl_pre]\<^sub>f
   nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
proof -
   have H2: \<open>merge_conflict_m M N clvls' D clvls lbd outl
      \<le> SPEC
          (\<lambda>x. (case x of (E, clvls, lbd, outl) \<Rightarrow> RETURN (False,
                     tl M, N, Some (remove1_mset (- L') (the E)), Q, W,
                     vmtf_mark_to_rescore_and_unset (atm_of L') ivmtf,
                     save_phase L' \<phi>, fast_minus clvls one_uint32_nat, cach, lbd, outl, stats))
                \<le> \<Down> (bool_rel \<times>\<^sub>f twl_st_heur)
                        (RETURN (False,
                    tl M', N', Some (resolve_cls_wl' (M', N', D', NE', UE', WS', Q') C
                       (snd (nat_of_lit L, L))), NE', UE', WS', Q')))\<close>
  if
    rel: \<open>(((clvls', L'), M, N, D, Q, W, ivmtf, \<phi>, clvls, cach, lbd, outl, stats),
      (C, snd (nat_of_lit L, L)), M', N', D', NE', UE', WS', Q')
     \<in> nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur\<close> and
    \<open>CLS = ((C, snd (nat_of_lit L, L)), M', N', D', NE', UE', WS', Q')\<close> and
    C_le: \<open>C \<in># dom_m (get_clauses_wl (M', N', D', NE', UE', WS', Q'))\<close> and
    confl: \<open>get_conflict_wl (M', N', D', NE', UE', WS', Q') = Some y\<close> and
    nempty: \<open>get_trail_wl (M', N', D', NE', UE', WS', Q') \<noteq> []\<close> and
    uL_y: \<open>- snd (nat_of_lit L, L) \<in># the (Some y)\<close> and
    L_M: \<open>(snd (nat_of_lit L, L), C) =
     lit_and_ann_of_propagated (hd (get_trail_wl (M', N', D', NE', UE', WS', Q')))\<close> and
    proped: \<open>is_proped (hd (get_trail_wl (M', N', D', NE', UE', WS', Q')))\<close> and
    \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>CLS' = ((clvls', L'), M, N, D, Q, W, ivmtf, \<phi>, clvls, cach, lbd, outl, stats)\<close> and
    \<open>C > 0\<close>
    for C M' N' D' NE' UE' WS' Q' y L L' M N D Q W \<phi> clvls cach lbd stats CLS CLS'
      ivmtf clvls' outl
  proof -
    have
      1: \<open>resolve_cls_wl' (M, N', Some y, NE', UE', WS', Q') C L =
          remove1_mset (- L) (y \<union># (mset (tl (N' \<propto> C))))\<close> and
       [simp]: \<open>L' = L\<close> and
       [simp]: \<open>M' = M\<close> and
       [simp]: \<open>N = N'\<close> and
       [simp]: \<open>D = D'\<close> and
       [simp]: \<open>D' = Some y\<close> and
       [simp]: \<open>Q = WS'\<close> and
       [simp]: \<open>(W, Q') \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
       vmtf: \<open>ivmtf \<in> vmtf M\<close> and
       \<phi>: \<open>phase_saving \<phi>\<close> and
       \<open>no_dup M\<close> and
       clvls: \<open>clvls \<in> counts_maximum_level M D'\<close> and
       cach[simp]: \<open>cach_refinement_empty cach\<close> and
       [simp]: \<open>clvls' = C\<close> and
       outl: \<open>out_learned M D outl\<close>
      using rel confl 
        C_le uL_y L_M proped nempty  \<open>C > 0\<close>
(* resolve_cls_wl'_union_uminus_positive_index[OF struct_invs, of clvls' L] list_invs*)
     by (auto simp: resolve_cls_wl'_def twl_st_heur_def ac_simps)
   have [simp]: \<open>lit_of (hd M) = L\<close>
     using L_M proped nempty
     by (cases \<open>hd M\<close>) (auto simp: atms_of_def)
   have  \<open>clvls' \<noteq> 0\<close>
     using \<open>C > 0\<close> by simp
   have 2[simp]: \<open>remove1_mset (- L) (mset (tl (N' \<propto> C)) \<union># y) =
    resolve_cls_wl' (M, N', Some y, NE', UE', WS', Q') C L\<close>
     unfolding 1 by (auto simp: ac_simps)

   have \<open>vmtf_mark_to_rescore_and_unset (atm_of L) ivmtf \<in> vmtf (tl M)\<close>
     using vmtf vmtf_mark_to_rescore_unset[where M = M] \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> L_M proped nempty
     apply (cases \<open>ivmtf\<close>; cases \<open>hd M\<close>)
     by (auto simp: atms_of_def)
   moreover have \<open>phase_saving (save_phase L \<phi>)\<close>
     using \<phi> by (auto simp: save_phase_def phase_saving_def)
   moreover have \<open>no_dup (tl M)\<close>
     using \<open>no_dup M\<close> by (simp add: no_dup_tlD)
   moreover have \<open>card_max_lvl M (mset (tl (N' \<propto> C)) \<union># y) - Suc 0
    \<in> counts_maximum_level (tl M)
        (Some (resolve_cls_wl' (M, N', Some y, NE', UE', WS', Q') C L))\<close>
     unfolding counts_maximum_level_def
     using resolve_cls_wl'_card_max_lvl[OF struct_invs, of C L] C_le uL_y L_M proped nempty
       list_invs clvls 2  \<open>C > 0\<close>
     by (auto simp del: 2)
   moreover {
     fix b
     assume \<open>out_learned M (Some (mset (tl (N' \<propto> clvls')) \<union># y)) b\<close>
     moreover have \<open>(- L) \<notin># {#L \<in># y. get_level M L < count_decided M#}\<close>
       using L_M nempty proped
       by (cases M; cases \<open>hd M\<close>) auto
     ultimately have out:
       \<open>out_learned M (Some (resolve_cls_wl' (M, N', Some y, NE', UE', WS', Q') clvls' L)) b\<close>
       using \<open>clvls' \<noteq> 0\<close>
       by (auto simp: resolve_cls_wl'_def out_learned_def ac_simps)
     have [simp]: \<open>- L \<notin># remove1_mset (- L) y\<close>
       using twl_struct_invs_confl(2)[OF struct_invs] confl
         uL_y multi_member_split[of \<open>-L\<close> y]
       by auto
     have [simp]: \<open>- L \<notin> set (tl (N' ! C))\<close>
       using uL_y out proped \<open>clvls' \<noteq> 0\<close> L_M C_le nempty list_invs
         resolve_cls_wl'_L_notin_cls[OF struct_invs, of C L, simplified]
       by (cases \<open>N' ! C\<close>) (auto simp: resolve_cls_wl'_def split: if_splits)
     have \<open>out_learned (tl M)
       (Some (resolve_cls_wl' (M, N', Some y, NE', UE', WS', Q') clvls' L)) b\<close>
       apply (rule out_learned_tl_Some_notin[THEN iffD1])
       using uL_y out proped \<open>clvls' \<noteq> 0\<close> L_M C_le nempty list_invs
         resolve_cls_wl'_notin[OF struct_invs, of C L]
       by (auto simp: resolve_cls_wl'_def split: if_splits)
    }
   ultimately show ?thesis
      by (auto simp: twl_st_heur_def merge_conflict_m_def)
  qed 
  show ?thesis
    supply [[goals_limit = 2]]
    apply (intro frefI nres_relI)
    subgoal for CLS' CLS
      unfolding uncurry_def update_confl_tl_wl_heur_def comp_def
        update_confl_tl_wl_def Let_def update_confl_tl_wl_pre_def merge_conflict_m_def
      apply (cases CLS'; cases CLS)
      apply clarify
      apply (refine_rcg lhs_step_If specify_left H2; remove_dummy_vars)
      subgoal
        using card_max_lvl_ge_1[of \<open>snd CLS\<close>]
        by  (auto simp: twl_st_heur_def
            RES_RETURN_RES RETURN_def counts_maximum_level_def
            in_multiset_nempty card_max_lvl_tl)
      subgoal
        apply (auto simp: twl_st_heur_def resolve_cls_wl'_def ac_simps no_dup_tlD
            counts_maximum_level_def
            intro!: )
        defer
        thm vmtf_mark_to_rescore_unset
        by fast
      subgoal by auto
      done
    done
qed

(* TODO Kill
lemma skip_and_resolve_hd_D\<^sub>0:
  assumes
    \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    \<open>get_trail_wl S = Propagated x21 x22 # xs\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>- x21 \<in> snd ` D\<^sub>0\<close>
  using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[of S None] assms
  by (cases S)
     (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons image_image
      uminus_\<A>\<^sub>i\<^sub>n_iff) *)

definition (in isasat_input_ops) skip_and_resolve_loop_wl_D_heur_inv where
 \<open>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0' =
    (\<lambda>(brk, S'). \<exists>S S\<^sub>0. (S', S) \<in> twl_st_heur \<and> (S\<^sub>0', S\<^sub>0) \<in> twl_st_heur \<and>
      skip_and_resolve_loop_wl_D_inv S\<^sub>0 brk S)\<close>

definition  (in isasat_input_ops) update_confl_tl_wl_heur_pre
   :: \<open>(nat \<times> nat literal) \<times> twl_st_wl_heur \<Rightarrow> bool\<close> 
where
\<open>update_confl_tl_wl_heur_pre =
  (\<lambda>((i, L), (M, N, D, W, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, clvls, cach, lbd,
        outl, _)).
      i > 0 \<and>
      (distinct (N \<propto> i)) \<and>
      (literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i))) \<and>
      (\<not> tautology (mset (N \<propto> i))) \<and>
      i \<in># dom_m N \<and> \<not> tautology (the D) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and>
      M \<noteq> [] \<and>
      L \<in> snd ` D\<^sub>0 \<and> -L \<in># the D \<and> L \<notin># the D \<and>
      ((L \<in> set (N \<propto> i) \<and> -L \<notin> set (N \<propto> i))) \<and>
      ((\<forall>L \<in> set (tl (N \<propto> i)). - L \<notin># the D)) \<and>
      (card_max_lvl M (mset (tl (N \<propto> i)) \<union># the D) \<ge> 1) \<and>
      atm_of (lit_of (hd M)) < length \<phi> \<and>
      atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = lit_of (hd M) \<and>
      clvls = card_max_lvl M (the D) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
      no_dup M \<and>
      out_learned M D outl)\<close>

definition (in isasat_input_ops) skip_and_resolve_loop_wl_D_heur
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
            let (L, C) = lit_and_ann_of_propagated_st_heur S;
            ASSERT(literal_is_in_conflict_heur_pre (-L, S));
            if \<not>literal_is_in_conflict_heur (-L) S then
              do {ASSERT (tl_state_wl_heur_pre S); RETURN (False, tl_state_wl_heur S)}
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

lemma skip_and_resolve_loop_wl_D_inv_skip_and_resolve_loop_wl_D_heur_inv:
  \<open>(x, y) \<in> twl_st_heur \<Longrightarrow>
       get_conflict_wl y \<noteq> None \<Longrightarrow>
       (xa, x') \<in> bool_rel \<times>\<^sub>f twl_st_heur \<Longrightarrow>
       skip_and_resolve_loop_wl_D_inv y (fst x') (snd x') \<Longrightarrow>
       skip_and_resolve_loop_wl_D_heur_inv x xa\<close>
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def
  apply (cases xa; cases x')
  apply clarify
  apply (rule exI[of _ \<open>snd x'\<close>])
  apply (rule exI[of _ y])
  by auto

lemma (in -)fref_to_Down_curry_no_nres_Id:
  \<open>(uncurry (RETURN oo f), uncurry (RETURN oo g)) \<in> [P]\<^sub>f A \<rightarrow> \<langle>Id\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y'. P (x', y') \<Longrightarrow> ((x, y), (x', y')) \<in> A \<Longrightarrow> f x y = g x' y')\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma (in -)fref_to_Down_no_nres:
  \<open>((RETURN o f), (RETURN o g)) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x'. P (x') \<Longrightarrow> (x, x') \<in> A \<Longrightarrow> (f x, g x') \<in> B)\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma (in -)fref_to_Down_curry_no_nres:
  \<open>(uncurry (RETURN oo f), uncurry (RETURN oo g)) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y'. P (x', y') \<Longrightarrow> ((x, y), (x', y')) \<in> A \<Longrightarrow> (f x y, g x' y') \<in> B)\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D:
  \<open>(skip_and_resolve_loop_wl_D_heur, skip_and_resolve_loop_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have tl_state_wl_pre: \<open>tl_state_wl_pre x2\<close>
    if
      \<open>skip_and_resolve_loop_wl_D_inv y False x2\<close> and
      hd_trail: \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1c, x2c)\<close> and
      notin: \<open>- x1c \<notin># the (get_conflict_wl x2)\<close> and
      is_dec: \<open>\<not> is_decided (hd (get_trail_wl x2))\<close>
    for x y xa x' x1 x2 x1a x2a x1b x2b x1c x2c ya
  proof -
    have
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None x2)\<close> and
      nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
      confl: \<open>get_conflict_wl x2 \<noteq> None\<close>
      using that
      by (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl get_trail_l_st_l_of_wl twl_st_of_sl_of_wl
          simp del: twl_st_of_wl.simps)

    from lits struct_invs have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)

    then have [simp]: \<open>lit_of (hd (get_trail_wl x2)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty by (cases \<open>get_trail_wl x2\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)
    have [simp]: \<open>lit_of (hd (get_trail_wl x2)) \<notin># the (get_conflict_wl x2)\<close>
      using notin nempty hd_trail is_dec twl_struct_invs_confl(4)[OF struct_invs confl]
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>)
        auto
    have [simp]: \<open>-lit_of (hd (get_trail_wl x2)) \<notin># the (get_conflict_wl x2)\<close>
      using notin nempty hd_trail is_dec
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>) auto
    show ?thesis
      using that twl_struct_invs_confl[OF struct_invs confl]
      by (auto simp: tl_state_wl_pre_def image_image twl_st_of_sl_of_wl
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          simp del: twl_st_of_wl.simps)
  qed
  have maximum_level_removed_eq_count_dec_pre: \<open>maximum_level_removed_eq_count_dec_pre (- x1a, x2)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur\<close> and
      \<open>skip_and_resolve_loop_wl_D_inv y x1 x2\<close> and
      hd_tr: \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      dec: \<open>\<not> x1 \<and> \<not> is_decided (hd (get_trail_wl x2))\<close> and
      in_confl: \<open>\<not> - x1a \<notin># the (get_conflict_wl x2)\<close>
 for x y xa x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    have
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None x2)\<close> and
      nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
      confl: \<open>get_conflict_wl x2 \<noteq> None\<close>
      using that
      by (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl
          simp del: twl_st_of_wl.simps)
    show ?thesis
      using nempty confl in_confl hd_tr dec
      unfolding maximum_level_removed_eq_count_dec_pre_def
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>) auto
  qed
  have update_confl_tl_wl_pre: \<open>update_confl_tl_wl_pre ((x2a, x1a), x2)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur\<close> and
      skip_inv: \<open>skip_and_resolve_loop_wl_D_inv y x1 x2\<close> and
      hd_tr: \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      dec: \<open>\<not> x1 \<and> \<not> is_decided (hd (get_trail_wl x2))\<close> and
      in_confl: \<open>\<not> - x1a \<notin># the (get_conflict_wl x2)\<close>
    for x y x' x1 x2 x1a x2a
  proof -
    have
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close> and
      invs:
        \<open>twl_struct_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_stgy_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_list_invs (st_l_of_wl None x2)\<close> and
      nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
      confl: \<open>get_conflict_wl x2 \<noteq> None\<close>
      using that
      by (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
          simp del: twl_st_of_wl.simps)
    have [simp]: \<open>x2a > 0\<close>
      using that
      by (cases x2; cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>)
        (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
          simp del: twl_st_of_wl.simps)

    from lits invs(1) have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)

    then have \<open>lit_of (hd (get_trail_wl x2)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty by (cases \<open>get_trail_wl x2\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)
    then have [simp]: \<open>x1a \<in> snd ` D\<^sub>0\<close> \<open>is_proped (hd (get_trail_wl x2))\<close>
      using nempty hd_tr dec
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
          auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons; fail)+
    have [simp]: \<open>x2a < length (get_clauses_wl x2)\<close>
      using invs(3) nempty hd_tr dec unfolding twl_list_invs_def
      by (cases x2; cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
          auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)

    show ?thesis
      using confl dec hd_tr nempty in_confl
      unfolding update_confl_tl_wl_pre_def
      by (auto simp del: twl_st_of_wl.simps simp: invs twl_st_of_sl_of_wl)
  qed
  have tl_state_wl_heur_pre: \<open>tl_state_wl_heur_pre x2b\<close>
    if
      rel: \<open>(xa, x') \<in> bool_rel \<times>\<^sub>f twl_st_heur\<close> and
      \<open>case x' of (brk, S) \<Rightarrow> \<not> brk \<and> \<not> is_decided (hd (get_trail_wl S))\<close> and
      \<open>skip_and_resolve_loop_wl_D_inv y x1 x2\<close> and
      \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1a, x2a)\<close> and
      st: \<open>x' = (x1, x2)\<close>
        \<open>xa = (x1b, x2b)\<close>
    for x y xa x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    obtain M N U D WS Q A m fst_As lst_As next_search \<phi> q g where
      x2b: \<open>x2b = (M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), q), \<phi>, g)\<close>
      by (cases x2b) auto
    have
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close> and
      invs:
        \<open>twl_struct_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_stgy_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_list_invs (st_l_of_wl None x2)\<close> and
      nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
      confl: \<open>get_conflict_wl x2 \<noteq> None\<close>
      using that
      by (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
          simp del: twl_st_of_wl.simps)
    from lits invs(1) have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
    then have lit_hd: \<open>lit_of (hd (get_trail_wl x2)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty by (cases \<open>get_trail_wl x2\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)
    have
      vmtf: \<open>((A, m, fst_As, lst_As, next_search), q) \<in> vmtf M\<close> and
      \<phi>: \<open>phase_saving \<phi>\<close> and
      [simp]: \<open>get_trail_wl x2 = M\<close>
      using rel unfolding x2b st twl_st_heur_def
      by auto
    have \<open>atm_of (lit_of (hd M)) < length \<phi>\<close>
      using \<phi> lit_hd unfolding phase_saving_def
      by (auto dest: atm_of_lit_in_atms_of)
    moreover have \<open>atm_of (lit_of (hd M)) < length A\<close>
      using vmtf lit_hd unfolding vmtf_def
      by (auto dest: atm_of_lit_in_atms_of)
    moreover have \<open>next_search = Some y \<Longrightarrow> y < length A\<close> for y
      using vmtf lit_hd unfolding vmtf_def
      by (auto dest: atm_of_lit_in_atms_of)
    ultimately show ?thesis
      using nempty unfolding tl_state_wl_heur_pre_def x2b
      by auto
  qed
  have literal_is_in_conflict_heur_pre: \<open>literal_is_in_conflict_heur_pre (- x1c, x2b)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur\<close> and
      \<open>(xa, x') \<in> bool_rel \<times>\<^sub>f twl_st_heur\<close> and
      \<open>skip_and_resolve_loop_wl_D_inv y x1 x2\<close> and
      hd_tr: \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      hd_tr': \<open>lit_and_ann_of_propagated_st_heur x2b = (x1c, x2c)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      dec: \<open>\<not> x1 \<and> \<not> is_decided (hd (get_trail_wl x2))\<close>
    for x y xa x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    have
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close> and
      invs:
        \<open>twl_struct_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_stgy_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_list_invs (st_l_of_wl None x2)\<close> and
      nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
      confl: \<open>get_conflict_wl x2 \<noteq> None\<close> and
      heur: \<open>(x2b, x2) \<in> twl_st_heur\<close>
      using that
      by (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
          simp del: twl_st_of_wl.simps)
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits confl invs(1)])
    then have lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur x2b))\<close>
      using confl heur by (auto simp: twl_st_heur_state_simp)

    from lits invs(1) have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
    then have lit_hd: \<open>lit_of (hd (get_trail_wl x2)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty by (cases \<open>get_trail_wl x2\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)
    then have [simp]: \<open>-x1a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty hd_tr dec
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
          auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons image_image
          lit_and_ann_of_propagated_st_heur_def uminus_\<A>\<^sub>i\<^sub>n_iff; fail)+
    then have \<open>x1c = x1a\<close>
      using nempty hd_tr dec hd_tr' heur
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
          auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons image_image
          lit_and_ann_of_propagated_st_heur_def twl_st_heur_def)
    then show ?thesis
      using confl heur lits_confl
      unfolding literal_is_in_conflict_heur_pre_def
      by (auto simp: image_image twl_st_heur_state_simp)
  qed

  have update_confl_tl_wl_heur_pre: \<open>update_confl_tl_wl_heur_pre ((x2c, x1c), x2b)\<close>
    if
      rel: \<open>(xa, x') \<in> bool_rel \<times>\<^sub>f twl_st_heur\<close> and
      \<open>skip_and_resolve_loop_wl_D_inv y x1 x2\<close> and
      hd_tr: \<open>lit_and_ann_of_propagated (hd (get_trail_wl x2)) = (x1a, x2a)\<close> and
      st: \<open>x' = (x1, x2)\<close>
        \<open>xa = (x1b, x2b)\<close> and
      hd_tr': \<open>lit_and_ann_of_propagated_st_heur x2b = (x1c, x2c)\<close> and
      dec: \<open>\<not> x1 \<and> \<not> is_decided (hd (get_trail_wl x2))\<close> and
      in_confl: \<open>\<not> - x1a \<notin># the (get_conflict_wl x2)\<close>
    for x y xa x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    obtain M N U D WS Q A m fst_As lst_As next_search \<phi> q clvls cach lbd outl stats where
      x2b: \<open>x2b = (M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), q), \<phi>, clvls, cach,
         lbd, outl, stats)\<close>
      by (cases x2b) auto
    have
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close> and
      invs:
        \<open>twl_struct_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_stgy_invs (twl_st_of_wl None x2)\<close>
        \<open>twl_list_invs (st_l_of_wl None x2)\<close> and
      nempty: \<open>get_trail_wl x2 \<noteq> []\<close> and
      confl: \<open>get_conflict_wl x2 \<noteq> None\<close> and
      heur: \<open>(x2b, x2) \<in> twl_st_heur\<close>
      using that
      by (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
          simp del: twl_st_of_wl.simps)
    have [simp]: \<open>x2a > 0\<close>
      using that
      by (cases x2; cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>)
        (auto simp: tl_state_wl_heur_pre_def image_image
          skip_and_resolve_loop_inv_def get_trail_twl_st_of_wl_get_trail_empty_iff
          get_conflict_twl_st_of_wl twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
          simp del: twl_st_of_wl.simps)
    from lits invs(1) have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
    then have lit_hd: \<open>lit_of (hd (get_trail_wl x2)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty by (cases \<open>get_trail_wl x2\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits confl invs(1)])
    then have lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur x2b))\<close>
      using confl heur by (auto simp: twl_st_heur_state_simp)

    from lits invs(1) have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
    then have lit_hd: \<open>lit_of (hd (get_trail_wl x2)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty by (cases \<open>get_trail_wl x2\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)
    then have [simp]: \<open>-x1a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> \<open>x1a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using nempty hd_tr dec
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
          auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons image_image
          lit_and_ann_of_propagated_st_heur_def uminus_\<A>\<^sub>i\<^sub>n_iff; fail)+
    have [simp]: \<open>x1c = x1a\<close> \<open>x2c = x2a\<close>
      using nempty hd_tr dec hd_tr' heur
      by (cases \<open>get_trail_wl x2\<close>; cases \<open>hd (get_trail_wl x2)\<close>;
          auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons image_image
          lit_and_ann_of_propagated_st_heur_def twl_st_heur_def; fail)+
    have
      vmtf: \<open>((A, m, fst_As, lst_As, next_search), q) \<in> vmtf M\<close> and
      \<phi>: \<open>phase_saving \<phi>\<close> and
      [simp]: \<open>get_trail_wl x2 = M\<close> and
      [simp]: \<open>M \<noteq> []\<close>
      using rel nempty unfolding x2b twl_st_heur_def st
      by auto

    have [simp]: \<open>get_conflict_wl x2 = D\<close> \<open>get_clauses_wl x2 = N\<close> \<open>get_trail_wl x2 = M\<close>
      using heur unfolding twl_list_invs_def
      by (auto simp: twl_st_heur_def x2b; fail)+

    have C_le: \<open>x2a < length N\<close>
      using nempty hd_tr dec invs(3) heur unfolding twl_list_invs_def
      by (cases M; cases \<open>hd M\<close>; auto simp: twl_st_heur_def x2b; fail)+
    have \<open>atm_of (lit_of (hd M)) < length \<phi>\<close>
      using \<phi> lit_hd unfolding phase_saving_def
      by (auto dest: atm_of_lit_in_atms_of)
    moreover have \<open>atm_of (lit_of (hd M)) < length A\<close>
      using vmtf lit_hd unfolding vmtf_def
      by (auto dest: atm_of_lit_in_atms_of)
    moreover have \<open>next_search = Some y \<Longrightarrow> y < length A\<close> for y
      using vmtf lit_hd unfolding vmtf_def
      by (auto dest: atm_of_lit_in_atms_of)
    moreover {
      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None x2))\<close>
      using invs unfolding twl_struct_invs_def by fast
    then have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None x2))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>distinct_mset_set (mset ` set (tl N))\<close>
      apply (subst append_take_drop_id[of U, symmetric])
      using heur unfolding set_append image_Un
      by (cases x2)
        (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def mset_take_mset_drop_mset drop_Suc
          x2b twl_st_heur_def)
    then have \<open>distinct (N ! x2c)\<close>
      using C_le nth_in_set_tl[of x2a N] by (auto simp: distinct_mset_set_def x2b)
    }
    moreover have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! x2c))\<close>
      apply (cases x2)
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth)
        (use C_le lits x2b heur in \<open>auto simp: clauses_def twl_st_heur_def\<close>)
    moreover have \<open>\<not>tautology (mset (N ! x2c))\<close>
      using resolve_cls_wl'_not_tauto_cls[of x2 x2c x1a] invs(1,3) confl in_confl C_le nempty
      dec hd_tr that
      by (auto simp: is_decided_no_proped_iff  twl_st_of_sl_of_wl get_trail_l_st_l_of_wl
        simp del: twl_st_of_wl.simps)
    moreover have \<open>x2c < length N\<close>
      using C_le by simp
    moreover have \<open>\<not>tautology (the D)\<close>
      using resolve_cls_wl'_not_tauto_confl[of x2 x2c x1a] invs(1) confl C_le nempty
      dec hd_tr invs(3) in_confl by (auto simp: is_decided_no_proped_iff)
    moreover {
      have lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close>
        by (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of _ None])
          (use lits confl invs in auto)
      then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the D)\<close>
        using heur by (auto simp: twl_st_heur_state_simp[symmetric] x2b)
    }
    moreover have \<open>D \<noteq> None\<close>
      using heur confl by (auto simp: twl_st_heur_state_simp[symmetric] x2b)
    moreover have \<open> - x1a \<in># the D\<close>
      using in_confl by auto
    moreover have \<open>0 < x2c \<Longrightarrow> x1a \<in> set (N ! x2c)\<close>
      using resolve_cls_wl'_L_in_cls[of x2 x2c x1a] invs(1) confl C_le nempty
      dec hd_tr invs(3) in_confl by (auto simp: is_decided_no_proped_iff)
    moreover have \<open>0 < x2c \<Longrightarrow> L \<in> set (tl (N ! x2c)) \<Longrightarrow> - L \<in># the D \<Longrightarrow> False\<close> for L
      using resolve_helper_seperated[of x2 x2c x1a L] invs(1) confl C_le nempty
      dec hd_tr invs(3) in_confl
      by (auto simp: is_decided_no_proped_iff counts_maximum_level_def)
    moreover have \<open>0 < x2c \<Longrightarrow> Suc 0 \<le> card_max_lvl M (mset (tl (N ! x2c)) \<union># the D)\<close>
      using resolve_cls_wl'_card_max_lvl[of x2 x2c x1a] invs(1) confl C_le nempty
      dec hd_tr invs(3) in_confl by (auto simp: is_decided_no_proped_iff counts_maximum_level_def)
    moreover have \<open>x1a = lit_of (hd M)\<close>
      using hd_tr nempty dec by (cases M; cases \<open>hd M\<close>) auto
    moreover have \<open>lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using lit_hd by simp
    moreover have \<open>no_dup M\<close>
      using heur confl unfolding twl_st_heur_def x2b
      by auto
    moreover have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close>
      using \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close> by simp
    moreover have \<open>clvls = card_max_lvl M (the D)\<close>
      using heur confl unfolding twl_st_heur_def x2b counts_maximum_level_def
      by auto
    moreover have \<open>out_learned M D outl\<close>
      using heur unfolding twl_st_heur_def x2b by blast
    ultimately show ?thesis
      unfolding update_confl_tl_wl_heur_pre_def x2b
      by (auto simp: image_image)
  qed

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
    subgoal by (auto simp: twl_st_heur_state_simp get_conflict_wl_is_Nil_heur_def)
    subgoal by (rule skip_and_resolve_loop_wl_D_inv_skip_and_resolve_loop_wl_D_heur_inv) auto
    subgoal by (auto simp: twl_st_heur_state_simp is_decided_hd_trail_wl_heur_def)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (rule literal_is_in_conflict_heur_pre) auto
    subgoal by (auto simp: twl_st_heur_state_simp is_decided_no_proped_iff
          lit_and_ann_of_propagated_st_def literal_is_in_conflict_heur_def
          twl_st_heur_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st)
    subgoal by (rule tl_state_wl_heur_pre) auto
    subgoal
      by (auto simp: twl_st_heur_state_simp
          intro: tl_state_wl_pre
          intro!: tl_state_wl_heur_tl_state_wl[THEN fref_to_Down_no_nres])
    subgoal by (rule maximum_level_removed_eq_count_dec_pre) auto
    subgoal by (auto simp: twl_st_heur_state_simp is_decided_no_proped_iff
          lit_and_ann_of_propagated_st_def
          twl_st_heur_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st)
    subgoal by (rule update_confl_tl_wl_heur_pre) auto
    subgoal by (rule update_confl_tl_wl_pre) auto
    subgoal by (auto simp: twl_st_heur_state_simp is_decided_no_proped_iff
          lit_and_ann_of_propagated_st_def
          twl_st_heur_lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
qed


sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil_heur)\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_heur_def twl_st_heur_assn_def
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses isasat_input_bounded_nempty.get_conflict_wll_is_Nil_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in -) get_count_max_lvls_code where
  \<open>get_count_max_lvls_code = (\<lambda>(_, _, _, _, _, _, _, _, clvls, _). clvls)\<close>

lemma get_count_max_lvls_heur_hnr[sepref_fr_rules]:
  \<open>(return o get_count_max_lvls_code, RETURN o get_count_max_lvls_heur) \<in>
     twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  subgoal for x x'
    by (cases x; cases x')
     (sep_auto simp: twl_st_heur_assn_def get_count_max_lvls_code_def
        elim!: mod_starE)
  done

sepref_thm maximum_level_removed_eq_count_dec_code
  is \<open>uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  by sepref

concrete_definition (in -) maximum_level_removed_eq_count_dec_code
   uses isasat_input_bounded_nempty.maximum_level_removed_eq_count_dec_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) maximum_level_removed_eq_count_dec_code_def

lemmas maximum_level_removed_eq_count_dec_code_hnr[sepref_fr_rules] =
   maximum_level_removed_eq_count_dec_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm is_decided_hd_trail_wl_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_heur_alt_def twl_st_heur_assn_def
  by sepref


concrete_definition (in -) is_decided_hd_trail_wl_code
   uses isasat_input_bounded_nempty.is_decided_hd_trail_wl_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms is_decided_hd_trail_wl_code_def

lemmas is_decided_hd_trail_wl_code[sepref_fr_rules] =
   is_decided_hd_trail_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm lit_and_ann_of_propagated_st_heur_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[\<lambda>S. is_proped (hd (get_trail_wl_heur S)) \<and> get_trail_wl_heur S \<noteq> []]\<^sub>a
       twl_st_heur_assn\<^sup>k \<rightarrow> (unat_lit_assn *a nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def twl_st_heur_assn_def
  by sepref

concrete_definition (in -) lit_and_ann_of_propagated_st_heur_code
   uses isasat_input_bounded_nempty.lit_and_ann_of_propagated_st_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_and_ann_of_propagated_st_heur_code_def

lemmas lit_and_ann_of_propagated_st_heur_code_refine[sepref_fr_rules] =
   lit_and_ann_of_propagated_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin

sepref_thm tl_state_wl_heur_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[tl_state_wl_heur_pre]\<^sub>a
      twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]] option.splits[split] if_splits[split]
  option.splits[split]
  supply [[goals_limit=1]] option.splits[split] literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0[intro]
  unfolding tl_state_wl_heur_alt_def[abs_def] twl_st_heur_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp] tl_state_wl_heur_pre_def
    short_circuit_conv
  by sepref


concrete_definition (in -) tl_state_wl_heur_code
  uses isasat_input_bounded_nempty.tl_state_wl_heur_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_state_wl_heur_code_def

lemmas tl_state_wl_heur_code_refine[sepref_fr_rules] =
   tl_state_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm conflict_remove1_code
  is \<open>uncurry (RETURN oo lookup_conflict_remove1)\<close>
  :: \<open>[\<lambda>(L, (n,xs)). n > 0 \<and> atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>
     lookup_clause_rel_assn\<close>
  supply [[goals_limit=2]] one_uint32_nat[sepref_fr_rules]
  unfolding lookup_conflict_remove1_def one_uint32_nat_def[symmetric] fast_minus_def[symmetric]
  by sepref

concrete_definition (in -) conflict_remove1_code
  uses isasat_input_bounded_nempty.conflict_remove1_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) conflict_remove1_code_def

lemmas conflict_remove1_code_refine[sepref_fr_rules] =
   conflict_remove1_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma conflict_remove1_code_op_nset_delete[sepref_fr_rules]:
  \<open>(uncurry conflict_remove1_code, uncurry (RETURN \<circ>\<circ> op_mset_delete))
    \<in> [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> L \<in># C \<and> -L \<notin># C]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (Id \<times>\<^sub>f lookup_clause_rel) (\<lambda>(L, C). L \<in># C \<and> - L \<notin># C \<and> L \<in> snd ` D\<^sub>0)
              (\<lambda>_ (L, n, xs). 0 < n \<and> atm_of L < length xs)
              (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d) (Id \<times>\<^sub>f lookup_clause_rel) \<rightarrow>
    hr_comp lookup_clause_rel_assn lookup_clause_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF conflict_remove1_code_refine lookup_conflict_remove1]
    unfolding op_mset_delete_def
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that neq0_conv
    unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (fastforce simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
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

lemma option_lookup_clause_assn_the[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>C. C \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_def option_lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    option_lookup_clause_rel_def)

lemma option_lookup_clause_assn_Some[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. (False, C)), RETURN o Some) \<in> lookup_clause_assn\<^sup>d \<rightarrow>\<^sub>a option_lookup_clause_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_def option_lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    option_lookup_clause_rel_def bool_assn_alt_def)


lemma lookup_clause_assn_op_nset_is_emty[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, _). n = 0), RETURN o op_mset_is_empty) \<in> lookup_clause_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi, case_tac xi)
  by (sep_auto simp: lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    uint32_nat_assn_0_eq uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)+

sepref_thm update_confl_tl_wl_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[update_confl_tl_wl_heur_pre]\<^sub>a
  nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> bool_assn *a twl_st_heur_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  unfolding update_confl_tl_wl_heur_def twl_st_heur_assn_def save_phase_def
    update_confl_tl_wl_heur_pre_def
  supply merge_conflict_m_def[simp]
  by sepref (* slow *)

concrete_definition (in -) update_confl_tl_wl_code
  uses isasat_input_bounded_nempty.update_confl_tl_wl_code.refine_raw
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_confl_tl_wl_code_def

lemmas update_confl_tl_wl_code_refine[sepref_fr_rules] =
   update_confl_tl_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end


setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

lemma skip_and_resolve_loop_wl_D_heur_inv_nempty:
  \<open>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0 (brk, S) \<Longrightarrow> get_trail_wl_heur S \<noteq> []\<close>
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def
    skip_and_resolve_loop_inv_def
   by (auto simp: twl_st_heur_def)

sepref_register skip_and_resolve_loop_wl_D is_in_conflict_st
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn\<close>
  supply [[goals_limit=1]] get_trail_twl_st_of_wl_get_trail_wl_empty_iff[simp]
    is_decided_hd_trail_wl_def[simp]
    is_decided_no_proped_iff[simp]
    literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of _ None, intro]
    get_conflict_l_st_l_of_wl[simp] is_in_conflict_st_def[simp]  neq_NilE[elim!]
    annotated_lit.splits[split] lit_and_ann_of_propagated_st_def[simp]
    annotated_lit.disc_eq_case(2)[simp]
    skip_and_resolve_hd_D\<^sub>0[simp]
    not_None_eq[simp del] maximum_level_removed_eq_count_dec_def[simp]
    skip_and_resolve_loop_wl_D_heur_inv_nempty[simp]
    is_decided_hd_trail_wl_heur_def[simp]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_heur_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref (* slow *)

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
  uses isasat_input_bounded_nempty.skip_and_resolve_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
end

setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

end
