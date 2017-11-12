theory IsaSAT_Conflict_Analysis
  imports IsaSAT_Setup
begin

paragraph \<open>Skip and resolve\<close>

context isasat_input_bounded_nempty
begin

definition get_conflict_wll_is_Nil_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool nres\<close> where
  \<open>get_conflict_wll_is_Nil_heur = (\<lambda>(M, N, U, D, Q, W, _).
   do {
     if is_None D
     then RETURN False
     else do{ ASSERT(D \<noteq> None); RETURN (Multiset.is_empty (the D))}
   })\<close>

sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil_heur)\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_heur_def twl_st_heur_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses isasat_input_bounded_nempty.get_conflict_wll_is_Nil_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma get_conflict_wll_is_Nil_heur_get_conflict_wll_is_Nil:
  \<open>(PR_CONST get_conflict_wll_is_Nil_heur, get_conflict_wll_is_Nil) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: get_conflict_wll_is_Nil_heur_def get_conflict_wll_is_Nil_def twl_st_heur_def
      split: option.splits)

lemma get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, get_conflict_wll_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code[FCOMP get_conflict_wll_is_Nil_heur_get_conflict_wll_is_Nil]
  unfolding twl_st_assn_def[symmetric] .

lemma get_conflict_wll_is_Nil_code_get_conflict_wl_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, RETURN \<circ> get_conflict_wl_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[FCOMP
   get_conflict_wll_is_Nil_get_conflict_wl_is_Nil[unfolded PR_CONST_def]]
  by auto

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
      have "{#L, L'#} \<subseteq># D"
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
      count_decided_st S = zero_uint32_nat \<or> get_count_max_lvls_heur S > one_uint32_nat\<close>

lemma maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec:
  \<open>(uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur),
      uncurry (RETURN oo maximum_level_removed_eq_count_dec)) \<in>
   [\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> []]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur\<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using get_maximum_level_remove_count_max_lvls[of \<open>fst x\<close> \<open>get_trail_wl (snd y)\<close>
      \<open>the (get_conflict_wl (snd y))\<close>]
    by (cases x)
       (auto simp: count_decided_st_def counts_maximum_level_def twl_st_heur_def
     maximum_level_removed_eq_count_dec_heur_def maximum_level_removed_eq_count_dec_def)
  done

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

lemma maximum_level_removed_eq_count_dec_hnr[sepref_fr_rules]:
  \<open>(uncurry maximum_level_removed_eq_count_dec_code,
      uncurry (RETURN oo maximum_level_removed_eq_count_dec)) \<in>
   [\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> []]\<^sub>a
    unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f twl_st_heur)
     (\<lambda>(L, S).
         L = -lit_of (hd (get_trail_wl S)) \<and>
         L \<in># the (get_conflict_wl S) \<and>
         get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [])
     (\<lambda>_ _. True)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    (unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k)
                    (Id \<times>\<^sub>f
                     twl_st_heur) \<rightarrow> hr_comp bool_assn bool_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF maximum_level_removed_eq_count_dec_code_hnr[unfolded PR_CONST_def]
      maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
      literals_to_update_wl_empty_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff lookup_clause_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric] lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition is_decided_hd_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>(M, _). is_decided (hd M))\<close>

lemma is_decided_hd_trail_wl_heur_is_decided_hd_trail_wl:
  \<open>(RETURN o is_decided_hd_trail_wl_heur, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>f twl_st_heur \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: is_decided_hd_trail_wl_heur_def is_decided_hd_trail_wl_def twl_st_heur_def)

lemma get_trail_wl_heur_def: \<open>get_trail_wl_heur = (\<lambda>(M, S). M)\<close>
  by (intro ext, rename_tac S, case_tac S) auto

sepref_thm is_decided_hd_trail_wl_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_heur_def twl_st_heur_assn_def
    supply get_trail_wl_heur_def[simp]
  by sepref


concrete_definition (in -) is_decided_hd_trail_wl_code
   uses isasat_input_bounded_nempty.is_decided_hd_trail_wl_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms is_decided_hd_trail_wl_code_def

lemmas is_decided_hd_trail_wl_code[sepref_fr_rules] =
   is_decided_hd_trail_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma is_decided_hd_trail_wl_code_is_decided_hd_trail_wl[sepref_fr_rules]:
  \<open>(is_decided_hd_trail_wl_code, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a twl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur (\<lambda>S. get_trail_wl S \<noteq> []) (\<lambda>_ S. get_trail_wl_heur S \<noteq> [])
        (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>k)
                     twl_st_heur \<rightarrow> hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_decided_hd_trail_wl_code
      is_decided_hd_trail_wl_heur_is_decided_hd_trail_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
      literals_to_update_wl_empty_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff lookup_clause_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma get_trail_twl_st_of_wl_get_trail_wl_empty_iff:
  \<open>get_trail (twl_st_of None (st_l_of_wl None S)) = [] \<longleftrightarrow> get_trail_wl S = []\<close>
  by (cases S) auto

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition lit_and_ann_of_propagated_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st_heur = (\<lambda>(M, _). (lit_of (hd M), mark_of (hd M)))\<close>

lemma mark_of_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in> [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
  by (sep_auto simp: nat_ann_lit_rel_def)+

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

lemma lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
   \<open>(RETURN o lit_and_ann_of_propagated_st_heur, RETURN o lit_and_ann_of_propagated_st) \<in>
   [\<lambda>S. is_proped (hd (get_trail_wl S))]\<^sub>f twl_st_heur \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y; case_tac x; case_tac y; case_tac \<open>hd (fst x)\<close>)
  by (auto simp: twl_st_heur_def lit_and_ann_of_propagated_st_heur_def lit_and_ann_of_propagated_st_def)

lemma lit_and_ann_of_propagated_st_refine[sepref_fr_rules]:
  \<open>(lit_and_ann_of_propagated_st_heur_code,
     (RETURN o lit_and_ann_of_propagated_st)) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> [] \<and> is_proped (hd (get_trail_wl S))]\<^sub>a
      twl_st_assn\<^sup>k  \<rightarrow> unat_lit_assn *a nat_assn \<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur (\<lambda>S. is_proped (hd (get_trail_wl S)))
         (\<lambda>_ S. is_proped (hd (get_trail_wl_heur S)) \<and> get_trail_wl_heur S \<noteq> [])
         (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k) twl_st_heur \<rightarrow>
    hr_comp (unat_lit_assn *a nat_assn) (Id \<times>\<^sub>f nat_rel)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF lit_and_ann_of_propagated_st_heur_code_refine lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: image_image twl_st_heur_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma skip_and_resolve_hd_in_D\<^sub>0:
  assumes
    L: "(L, a2'a) = lit_and_ann_of_propagated_st a2'" and
    is_proped: "is_proped (hd (get_trail_wl a2'))" and
    struct: "twl_struct_invs (twl_st_of None (st_l_of_wl None a2'))" and
    nempty: "get_trail_wl a2' \<noteq> []" and
    \<L>\<^sub>a\<^sub>l\<^sub>l: "is_\<L>\<^sub>a\<^sub>l\<^sub>l
      (all_lits_of_mm
        (cdcl\<^sub>W_restart_mset.clauses
          (state\<^sub>W_of (twl_st_of None (st_l_of_wl None a2')))))"
   shows "- L \<in> snd ` D\<^sub>0"
proof -
  obtain M' where
    M': \<open>get_trail_wl a2' = Propagated L a2'a # M'\<close>
    using is_proped L nempty by (cases \<open>get_trail_wl a2'\<close>; cases \<open>hd (get_trail_wl a2')\<close>)
      (auto simp: lit_and_ann_of_propagated_st_def)
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of None (st_l_of_wl None a2')))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then show ?thesis
    using \<L>\<^sub>a\<^sub>l\<^sub>l M' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases a2')
     (auto simp: image_image mset_take_mset_drop_mset'
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff clauses_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def)
qed


definition tl_state_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>tl_state_wl_heur = (\<lambda>(M, N, U, D, WS, Q, vmtf, \<phi>, clvls).
       (tl M, N, U, D, WS, Q, vmtf_unset (atm_of (lit_of (hd M))) vmtf, \<phi>, clvls))\<close>

lemma tl_state_wl_heur_alt_def:
    \<open>tl_state_wl_heur = (\<lambda>(M, N, U, D, WS, Q, vmtf, \<phi>, clvls).
      (let L = lit_of (hd M) in
       (tl M, N, U, D, WS, Q, vmtf_unset (atm_of L) vmtf, \<phi>, clvls)))\<close>
  by (auto simp: tl_state_wl_heur_def Let_def)


fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> _\<close> where
  \<open>get_vmtf_heur (M, N, U, D, WS, W, cvmtf, _) = cvmtf\<close>

end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin

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

sepref_thm tl_state_wl_heur_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[\<lambda>(M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, _). M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A)]\<^sub>a
      twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]] option.splits[split] if_splits[split]
  option.splits[split]
  supply [[goals_limit=1]] option.splits[split] literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0[intro]
  unfolding tl_state_wl_heur_alt_def[abs_def] twl_st_heur_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp]
    short_circuit_conv
  by sepref


concrete_definition (in -) tl_state_wl_heur_code
  uses isasat_input_bounded_nempty.tl_state_wl_heur_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_state_wl_heur_code_def

lemmas tl_state_wl_heur_code_refine[sepref_fr_rules] =
   tl_state_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* TODO: we need early breaks in skip_and_resolve! *)
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

lemma tl_state_wl_heur_tl_state_wl: \<open>(RETURN o tl_state_wl_heur, RETURN o tl_state_wl) \<in>
  [\<lambda>S. get_trail_wl S \<noteq> [] \<and> lit_of(hd (get_trail_wl S)) \<in> snd ` D\<^sub>0 \<and>
     (lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
     -(lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
    \<not>tautology (the (get_conflict_wl S)) \<and>
    distinct_mset (the (get_conflict_wl S)) \<and>
    \<not>is_decided (hd (get_trail_wl S))
  ]\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: twl_st_heur_def tl_state_wl_heur_def tl_state_wl_def vmtf_unset_vmtf_tl
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff phase_saving_def counts_maximum_level_def
    card_max_lvl_tl
    dest: no_dup_tlD)


lemma twl_struct_invs_confl:
  assumes
    \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close>
  shows
     \<open>\<not>tautology (the (get_conflict_wl S))\<close> and
     \<open>distinct_mset (the (get_conflict_wl S))\<close> and
     \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> -L \<in> lits_of_l (get_trail_wl S)\<close>
     \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> L \<notin> lits_of_l (get_trail_wl S)\<close>
proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (M, N, U, Some D, NP, UP, W, Q)\<close>
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

lemma tl_state_wl_refine[sepref_fr_rules]:
  \<open>(tl_state_wl_heur_code, RETURN o tl_state_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> [] \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        twl_struct_invs (twl_st_of None (st_l_of_wl None S)) \<and>
        -lit_of (hd (get_trail_wl S)) \<notin># the (get_conflict_wl S) \<and>
        \<not>is_decided (hd (get_trail_wl S)) \<and>
         get_conflict_wl S \<noteq> None]\<^sub>a
      twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
   \<in> [comp_PRE twl_st_heur
     (\<lambda>S. get_trail_wl S \<noteq> [] \<and>
          lit_of (hd (get_trail_wl S)) \<in> snd ` D\<^sub>0 \<and>
          lit_of (hd (get_trail_wl S))
          \<notin># the (get_conflict_wl S) \<and>
          - lit_of (hd (get_trail_wl S))
          \<notin># the (get_conflict_wl S) \<and>
          \<not> tautology (the (get_conflict_wl S)) \<and>
          distinct_mset (the (get_conflict_wl S)) \<and>
          \<not> is_decided (hd (get_trail_wl S)))
     (\<lambda>_ (M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, _).
         M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow> the next_search < length A))
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>d)
                    twl_st_heur \<rightarrow> hr_comp twl_st_heur_assn
    twl_st_heur\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF tl_state_wl_heur_code_refine tl_state_wl_heur_tl_state_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0[of x]
      twl_struct_invs_confl[of x]
    unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    apply (cases \<open>get_trail_wl x\<close>)
    by (auto simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

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
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
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

lemma resolve_cls_wl'_union_uminus_zero_index:
  assumes
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C = 0\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>resolve_cls_wl' S C L = remove1_mset (-L) (the (get_conflict_wl S))\<close>
  using assms by (auto simp: resolve_cls_wl'_def)


definition (in -) lookup_conflict_merge_abs_union'
  :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause option \<Rightarrow> nat \<Rightarrow> 'v cconflict\<close>
where
  \<open>lookup_conflict_merge_abs_union' M N i C _ =
      Some (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i))))\<close>

definition (in -) lookup_conflict_merge_abs_union
  :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause option \<Rightarrow> nat \<Rightarrow>
     ('v cconflict \<times> nat) nres\<close>
where
  \<open>lookup_conflict_merge_abs_union M N i C _ = RES {(Some (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i)))),
    card_max_lvl M (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i)))))}\<close>

lemma lookup_conflict_merge_abs_union_alt_def:
  \<open>lookup_conflict_merge_abs_union M N i C clvls = RES {(lookup_conflict_merge_abs_union' M N i C clvls,
    card_max_lvl M (the (lookup_conflict_merge_abs_union' M N i C clvls)))}\<close>
  unfolding lookup_conflict_merge_abs_union_def lookup_conflict_merge_abs_union'_def by auto

lemma
  fixes S and C clvls :: nat
  defines [simp]: \<open>E \<equiv> the (lookup_conflict_merge_abs_union' (get_trail_wl S)  (get_clauses_wl S) C (get_conflict_wl S) clvls)\<close>
  assumes invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C < length (get_clauses_wl S)\<close> and
    L_confl: \<open>-L \<in># the (get_conflict_wl S)\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close>
  shows
    resolve_cls_wl'_union_uminus_positive_index:
      \<open>C > 0 \<Longrightarrow> resolve_cls_wl' S C L =
          remove1_mset L E\<close>
       (is \<open>_ \<Longrightarrow> ?Res\<close>) and
    resolve_cls_wl'_not_tauto_confl: \<open>\<not>tautology (the (get_conflict_wl S))\<close> (is ?tauto) and
    resolve_cls_wl'_not_tauto_cls: \<open>C > 0 \<Longrightarrow> \<not>tautology (mset (get_clauses_wl S ! C))\<close>
      (is \<open>_ \<Longrightarrow> ?tauto_cls\<close>) and
    resolve_cls_wl'_L_in_cls: \<open>C > 0 \<Longrightarrow> L \<in> set (get_clauses_wl S ! C)\<close> (is \<open>_ \<Longrightarrow> ?L_in_cls\<close>) and
    resolve_cls_wl'_in:
      \<open>C > 0 \<Longrightarrow> L \<in># E\<close>
      (is \<open>_ \<Longrightarrow> ?L_in_union\<close>) and
    resolve_cls_wl'_notin:
      \<open>C > 0 \<Longrightarrow> -L \<notin># E\<close>
      (is \<open>_ \<Longrightarrow> ?L_notin_union\<close>) and
    resolve_cls_wl'_not_tauto: \<open>C > 0 \<Longrightarrow> \<not> tautology E\<close> and
    resolve_cls_wl'_card_max_lvl:
       \<open>C > 0 \<Longrightarrow> card_max_lvl (get_trail_wl S) E = card_max_lvl (tl (get_trail_wl S))
         (E - unmark (hd (get_trail_wl S))) + 1\<close>(is \<open>_ \<Longrightarrow> ?Max\<close>)
proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (Propagated L C # M, N, U, Some D, NP, UP, W, Q)\<close>
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

  assume C': \<open>C > 0\<close>
  have \<open>L \<in># mset (N ! C)\<close> and
    M_C: \<open>M \<Turnstile>as CNot (mset (N!C) - {#L#})\<close>
    using C C' confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (fastforce simp: S)+
  from multi_member_split[OF this(1)] obtain C' where
    C'': \<open>mset (N ! C) = add_mset L C'\<close>
    by auto
  moreover have uL_C': \<open>-L \<notin># C'\<close>
    using M_C undef_L by (auto simp: C'' true_annots_true_cls_def_iff_negation_in_model
        Decided_Propagated_in_iff_in_lits_of_l)
  ultimately show tauto_C: ?tauto_cls
    using M_C n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l M\<close> \<open>C'\<close>]
    by (auto 5 5 dest!: distinct_consistent_interp simp: tautology_add_mset true_annots_true_cls C' S)
  have get_clss_S: \<open>get_clauses_wl S = N\<close>
    by (auto simp: S)
  show ?L_in_cls
    unfolding in_multiset_in_set[symmetric] get_clss_S C'' by simp

  have n_d_L: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> False\<close> for L
    using distinct_consistent_interp[OF n_d] by (auto simp: consistent_interp_def)
  have dist_C: \<open>distinct_mset (mset (N ! C))\<close>
    using C C' dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  have uL_C'': \<open>-L \<notin># C' - uminus `# D'\<close>
    using uL_C' by (auto dest!: in_diffD)
  moreover have D'C'D': \<open>D' - uminus `# C' = D'\<close>
    apply (rule minus_eq_id_forall_notin_mset[THEN iffD2])
    unfolding Ball_def
    apply (rule impI conjI allI)
    subgoal for L'
      using undef_L n_d M_D' M_C n_d_L[of L']
      by (auto 5 5 simp: C'' D true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l)
    done

  moreover have \<open>L \<notin># D'\<close>
    using tauto_D by (auto simp: tautology_add_mset D S)
  moreover have [simp]: \<open>L \<notin># D' - add_mset L (C' + uminus `# C')\<close>
    using \<open>L \<notin># D'\<close> by (auto dest: in_diffD)
  moreover have [simp]: \<open>distinct_mset D'\<close> \<open>distinct_mset C'\<close>
    using dist_D dist_C unfolding D C'' C' by auto
  moreover have \<open>C' \<union># D' = C' \<union># (D' - (C' + uminus `# C'))\<close>
  proof -
    have \<open>D' - (C' + uminus `# C') = (D' -uminus `# C') - C'\<close>
      by (auto simp: ac_simps)
    also have \<open>\<dots> = D' - C'\<close>
      unfolding D'C'D' ..
    finally have A: \<open>C' \<union># (D' - (C' + uminus `# C')) = C' \<union># (D' - C')\<close> by simp
    show ?thesis
      unfolding A
      by (auto simp: ac_simps distinct_mset_rempdups_union_mset distinct_mset_in_diff
          intro!: distinct_set_mset_eq dest: in_diffD)
  qed
  ultimately show ?Res
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        lookup_conflict_merge_abs_union'_def minus_notin_trivial S)
  show ?L_in_union
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        lookup_conflict_merge_abs_union'_def S)
  show ?L_notin_union
    using C C' uL_C' uL_C'' dist_D unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        lookup_conflict_merge_abs_union'_def S dest: in_diffD)
  have [simp]: \<open>L \<notin># D'\<close>
    using undef_L n_d M_D' M_C
    by (auto 5 5 simp: C'' D true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l)

   have \<open>D' - (C' + uminus `# C') = (D' -uminus `# C') - C'\<close>
      by (auto simp: ac_simps)
    also have \<open>\<dots> = D' - C'\<close>
      unfolding D'C'D' ..
    finally show \<open>\<not> tautology E\<close>
    using uL_C' dist_D tauto_C tauto_D
    apply (auto simp: S lookup_conflict_merge_abs_union'_def C'' tautology_add_mset
        distinct_mset_in_diff D minus_notin_trivial
       )
    unfolding tautology_decomp'
    apply (auto simp: distinct_mset_in_diff)
    apply (metis D'C'D' image_eqI minus_eq_id_forall_notin_mset set_image_mset)
    by (metis (mono_tags, lifting) D'C'D' image_mset_add_mset insert_DiffM
        minus_eq_id_forall_notin_mset uminus_of_uminus_id union_single_eq_member)
  then have \<open>card_max_lvl (Propagated L C # M)
     (add_mset L (C' \<union># (D' - add_mset L (C' + uminus `# C')))) =
    card_max_lvl M (C' \<union># (D' - add_mset L (C' + uminus `# C'))) + 1\<close>
    apply (subst card_max_lvl_Cons)
    using undef_L n_d tauto_C dist_C uL_C'
    by (auto simp: S C'' lookup_conflict_merge_abs_union'_def D
        card_max_lvl_add_mset)
  then show ?Max
    by (auto simp: S resolve_cls_wl'_def lookup_conflict_merge_abs_union'_def C'' D)
qed

lemma lookup_conflict_merge_aa_lookup_conflict_merge_abs_union_aa:
  \<open>(uncurry4 (lookup_conflict_merge_aa), uncurry4 lookup_conflict_merge_abs_union) \<in>
     [\<lambda>((((M, N), i), C), clvls). distinct (N!i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i)) \<and>
          \<not> tautology (mset (N!i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None \<and>
         clvls = card_max_lvl M (the C)]\<^sub>f
    Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>option_lookup_clause_rel \<times>\<^sub>r nat_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for M N i b j xs clvls M' N' i' _ clvls' C
    using lookup_conflict_merge'_spec[of b j xs C \<open>N' ! i'\<close> clvls M]
    unfolding lookup_conflict_merge_abs_union_def lookup_conflict_merge_aa_def
    by auto
  done

lemma lookup_conflict_merge_code_lookup_conflict_merge_abs_union[sepref_fr_rules]:
  \<open>(uncurry4 lookup_conflict_merge_code, uncurry4 lookup_conflict_merge_abs_union) \<in>
    [\<lambda>((((M, N), i), C), clvls). distinct (N!i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i)) \<and> \<not> tautology (mset (N!i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None \<and> i < length N \<and> clvls = card_max_lvl M (the C)]\<^sub>a
    trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (option_lookup_clause_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     option_lookup_clause_assn *a uint32_nat_assn \<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
     \<in> [comp_PRE
     (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f
      nat_rel)
     (\<lambda>((((M, N), i), C), clvls).
         distinct (N ! i) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and>
         \<not> tautology (mset (N ! i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and>
         C \<noteq> None \<and> clvls = card_max_lvl M (the C))
     (\<lambda>_ ((((M, N), i), _, xs), _).
         i < length N \<and>
         (\<forall>j<length (N ! i).
             atm_of (N ! i ! j) < length (snd xs)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a
                     clauses_ll_assn\<^sup>k *\<^sub>a
                     nat_assn\<^sup>k *\<^sub>a
                     conflict_option_rel_assn\<^sup>d *\<^sub>a
                     uint32_nat_assn\<^sup>k)
                    (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                     option_lookup_clause_rel \<times>\<^sub>f
                     nat_rel) \<rightarrow> hr_comp
   (conflict_option_rel_assn *a uint32_nat_assn)
   (option_lookup_clause_rel \<times>\<^sub>f nat_rel)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lookup_conflict_merge_aa_hnr[unfolded PR_CONST_def]
      lookup_conflict_merge_aa_lookup_conflict_merge_abs_union_aa]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l
    unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep hr_comp_prod_conv option_lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition update_confl_tl_wl_heur
  :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_confl_tl_wl_heur = (\<lambda>C L (M, N, U, D, Q, W, vmtf, \<phi>, clvls, cach).
     (if C = 0 then do {
         let D' = remove1_mset (-L) (the D);
         let L' = atm_of L;
         ASSERT (clvls \<ge> 1);
         RETURN (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf,
            save_phase L \<phi>,
            fast_minus clvls one_uint32_nat,
            cach))
         }
      else do {
        let L' = atm_of L;
        (D', clvls) \<leftarrow> lookup_conflict_merge_abs_union M N C D clvls;
        let D' = remove1_mset L (the D');
        RETURN (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf,
           save_phase L \<phi>, fast_minus clvls one_uint32_nat, cach))
      }))\<close>

lemma card_max_lvl_remove1_mset_hd:
  \<open>-lit_of (hd M) \<in># y \<Longrightarrow> is_proped (hd M) \<Longrightarrow>
     card_max_lvl M (remove1_mset (-lit_of (hd M)) y) = card_max_lvl M y - 1\<close>
  by (cases M)  (auto dest!: multi_member_split simp: card_max_lvl_add_mset)


lemma resolve_cls_wl'_if_lookup_conflict_merge_abs_union:
  assumes
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>C < length (get_clauses_wl S)\<close> and
    \<open>- L \<in># the (get_conflict_wl S)\<close> and
    \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
    \<open>is_proped (hd (get_trail_wl S))\<close> and
    \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>resolve_cls_wl' S C L = (if C = 0 then remove1_mset (-L) (the (get_conflict_wl S))
               else remove1_mset L (the (lookup_conflict_merge_abs_union' (get_trail_wl S) (get_clauses_wl S) C (get_conflict_wl S) clvls)))\<close>
  using resolve_cls_wl'_union_uminus_positive_index[of \<open>S\<close> C L] assms
  unfolding lookup_conflict_merge_abs_union_def[symmetric]
  by (auto simp: resolve_cls_wl'_def)

lemma update_confl_tl_wl_heur_state_helper:
   \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<Longrightarrow> get_trail_wl S \<noteq> [] \<Longrightarrow>
    is_proped (hd (get_trail_wl S)) \<Longrightarrow> L = lit_of (hd (get_trail_wl S))\<close>
  by (cases S; cases \<open>hd (get_trail_wl S)\<close>) auto

lemma (in -) not_ge_Suc0: \<open>\<not>Suc 0 \<le> n \<longleftrightarrow> n = 0\<close> (* WTF *)
  by auto

lemma card_max_lvl_ge_1:
  assumes \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>get_conflict_wl S \<noteq> Some {#}\<close>
  shows
   \<open>card_max_lvl (get_trail_wl S) (the (get_conflict_wl S)) \<ge> Suc 0\<close>
  using assms unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
     cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
  by (cases S) (auto simp: card_max_lvl_def not_ge_Suc0 filter_mset_empty_conv)

lemma update_confl_tl_wl_heur_update_confl_tl_wl:
  \<open>(uncurry2 (update_confl_tl_wl_heur), uncurry2 (RETURN ooo update_confl_tl_wl)) \<in>
  [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and>
    twl_stgy_invs (twl_st_of_wl None S) \<and>
    C < length (get_clauses_wl S) \<and>
    get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> - L \<in># the (get_conflict_wl S) \<and>
     (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and> L \<in> snd ` D\<^sub>0 \<and>
    twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S))]\<^sub>f
   nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
  supply [[goals_limit = 2]]
  apply (intro frefI nres_relI)
  subgoal for CLS' CLS
    unfolding case_prod_beta uncurry_def update_confl_tl_wl_heur_def comp_def
    using resolve_cls_wl'_if_lookup_conflict_merge_abs_union[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close>
      \<open>snd (fst CLS)\<close> \<open>get_count_max_lvls_heur (snd CLS')\<close>, symmetric]
      twl_struct_invs_confl[of \<open>snd CLS\<close>]
      update_confl_tl_wl_heur_state_helper[of \<open>snd (fst CLS)\<close> \<open>fst (fst CLS)\<close>  \<open>snd CLS\<close>]
      card_max_lvl_ge_1[of \<open>snd CLS\<close>]
      resolve_cls_wl'_card_max_lvl[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close>]
      resolve_cls_wl'_not_tauto[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close>]
    by (cases \<open>CLS'\<close>; cases CLS)
       (auto simp: twl_st_heur_def update_confl_tl_wl_heur_def update_confl_tl_wl_def
        vmtf_unset_vmtf_tl Let_def save_phase_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff phase_saving_def vmtf_mark_to_rescore_unset
        lookup_conflict_merge_abs_union_alt_def
        RES_RETURN_RES RETURN_def no_dup_tlD counts_maximum_level_def
        RES_RES_RETURN_RES (* lookup_conflict_merge_abs_union'_def *)
        eq_commute[of \<open>remove1_mset _ _\<close> \<open>resolve_cls_wl' _ _ _\<close>]
        in_multiset_nempty card_max_lvl_tl
        distinct_mset_in_diff not_tautology_minus
          card_max_lvl_remove1_mset_hd is_decided_no_proped_iff
        intro!: RES_refine ASSERT_refine_left) (* slow *)
  done


lemma lookup_conflict_merge_abs_union_None: \<open>lookup_conflict_merge_abs_union' M a b c clvls \<noteq> None\<close>
  unfolding lookup_conflict_merge_abs_union'_def by auto


lemma lookup_clause_assn_op_nset_is_emty[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, _). n = 0), RETURN o op_mset_is_empty) \<in> lookup_clause_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi, case_tac xi)
  by (sep_auto simp: lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    uint32_nat_assn_0_eq uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)+


sepref_thm update_confl_tl_wl_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), (M, N, U, D, W, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, clvls, cach)).
      (i > 0 \<longrightarrow> distinct (N ! i)) \<and>
      (i > 0 \<longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N! i))) \<and>
      (i > 0 \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
      i < length N \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and>
      M \<noteq> [] \<and>
      L \<in> snd ` D\<^sub>0 \<and> -L \<in># the D \<and> L \<notin># the D \<and>
      (i > 0 \<longrightarrow> (L \<in> set (N ! i) \<and> -L \<notin> set (N ! i))) \<and>
      (i > 0 \<longrightarrow> (-L \<notin># the (lookup_conflict_merge_abs_union' M N i D clvls) \<and>
           L \<in># the (lookup_conflict_merge_abs_union' M N i D clvls))) \<and>
      (i > 0 \<longrightarrow> card_max_lvl M (the (lookup_conflict_merge_abs_union' M N i D clvls)) \<ge> 1) \<and>
      atm_of (lit_of (hd M)) < length \<phi> \<and>
      atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = lit_of (hd M) \<and>
      clvls = card_max_lvl M (the D)
         ]\<^sub>a
  nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> bool_assn *a twl_st_heur_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  supply lookup_conflict_merge_abs_union_None[simplified, simp]
  unfolding update_confl_tl_wl_heur_def twl_st_heur_assn_def save_phase_def
  supply lookup_conflict_merge_abs_union'_def[simp] lookup_conflict_merge_abs_union_def[simp]
  by sepref (* slow *)

concrete_definition (in -) update_confl_tl_wl_code
  uses isasat_input_bounded_nempty.update_confl_tl_wl_code.refine_raw
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_confl_tl_wl_code_def

lemmas update_confl_tl_wl_code_refine[sepref_fr_rules] =
   update_confl_tl_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma update_confl_tl_wl_code_update_confl_tl_wl[sepref_fr_rules]:
  \<open>(uncurry2 update_confl_tl_wl_code, uncurry2 (RETURN ooo update_confl_tl_wl))
    \<in> [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and>
        twl_stgy_invs (twl_st_of_wl None S) \<and>
        get_conflict_wl S \<noteq> None \<and>
        get_trail_wl S \<noteq> [] \<and>
        - L \<in># the (get_conflict_wl S) \<and>
        (L, C) = lit_and_ann_of_propagated_st S \<and>
        literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S)) \<and>
        additional_WS_invs (st_l_of_wl None S)]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> bool_assn *a twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in> [comp_PRE (nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur)
       (\<lambda>((C, L), S).
           twl_struct_invs (twl_st_of_wl None S) \<and>
           twl_stgy_invs (twl_st_of_wl None S) \<and>
           C < length (get_clauses_wl S) \<and>
           get_conflict_wl S \<noteq> None \<and>
           get_trail_wl S \<noteq> [] \<and>
           - L \<in># the (get_conflict_wl S) \<and>
           (L, C) =
           lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and>
           L \<in> snd ` D\<^sub>0 \<and>
           twl_struct_invs (twl_st_of_wl None S) \<and>
           is_proped (hd (get_trail_wl S)))
       (\<lambda>_ ((i, L), M, N, U, D, W, Q, ((A, m, fst_As, lst_As,
           next_search), _), \<phi>, clvls, cach).
           (0 < i \<longrightarrow> distinct (N ! i)) \<and>
           (0 < i \<longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i))) \<and>
           (0 < i \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
           i < length N \<and>
           literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and>
           D \<noteq> None \<and>
           M \<noteq> [] \<and>
           L \<in> snd ` D\<^sub>0 \<and>
           - L \<in># the D \<and>
           L \<notin># the D \<and>
           (0 < i \<longrightarrow> L \<in> set (N ! i) \<and> - L \<notin> set (N ! i)) \<and>
           (0 < i \<longrightarrow>
            - L
            \<notin># the (lookup_conflict_merge_abs_union' M N i D
                      clvls) \<and>
            L \<in># the (lookup_conflict_merge_abs_union' M N i D
                        clvls)) \<and>
           (0 < i \<longrightarrow>
            1 \<le> card_max_lvl M
                  (the (lookup_conflict_merge_abs_union' M N i D
                         clvls))) \<and>
           atm_of (lit_of (hd M)) < length \<phi> \<and>
           atm_of (lit_of (hd M)) < length A \<and>
           (next_search \<noteq> None \<longrightarrow>
            the next_search < length A) \<and>
           L = lit_of (hd M) \<and>
           clvls = card_max_lvl M (the D))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                      (nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
                       twl_st_heur_assn\<^sup>d)
                      (nat_rel \<times>\<^sub>f Id \<times>\<^sub>f
                       twl_st_heur) \<rightarrow> hr_comp
        (bool_assn *a twl_st_heur_assn)
        (bool_rel \<times>\<^sub>f twl_st_heur)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF update_confl_tl_wl_code_refine
       update_confl_tl_wl_heur_update_confl_tl_wl]
    .
  have pre: \<open>?pre' x\<close> (is \<open>comp_PRE ?rel ?\<Phi> ?\<Psi> _ x\<close>) if pre: \<open>?pre x\<close> for x
  unfolding comp_PRE_def
  proof (intro allI impI conjI)
    obtain C L S where
      [simp]: \<open>x = ((C,L), S)\<close>
      by (cases x) auto
    obtain M N U D W Q NP UP where
      [simp]: \<open>S = (M, N, U, D, NP, UP, W, Q)\<close>
      by (cases S) auto
    have LC: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
      lits_\<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
      trail_nempty: \<open>get_trail_wl S \<noteq> []\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
      proped: \<open>is_proped (hd (get_trail_wl S))\<close> and
      confl: \<open>get_conflict_wl S \<noteq> None\<close> and
      L_confl: \<open>-L \<in># the(get_conflict_wl S)\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)
    have lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n)
       (use lits_\<A>\<^sub>i\<^sub>n confl struct_invs in auto)
    have C_le: \<open>C < length (get_clauses_wl S)\<close>
      using trail_nempty LC proped add_invs trail_nempty unfolding additional_WS_invs_def
      by (cases M; cases \<open>hd M\<close>) auto
    moreover have L_D\<^sub>0: \<open>L \<in> snd ` D\<^sub>0\<close>
      using L_confl confl lits_D
      by (cases \<open>get_conflict_wl S\<close>)
        (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
            dest: multi_member_split)
    ultimately show \<open>?\<Phi> x\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)

    fix x'
    assume x'x: \<open>(x', x) \<in> nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur\<close>
    then obtain S' where
      [simp]: \<open>x' = ((C, L), S')\<close>
      by (cases x') auto
    obtain Q' A m fst_As lst_As next_search oth \<phi> clvls cach where
      [simp]: \<open>S' = (M, N, U, D, W, Q', ((A, m, fst_As, lst_As, next_search), oth), \<phi>, clvls, cach)\<close>
      using x'x by (cases S') (auto simp: twl_st_heur_def)
    have in_atms_le: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length A\<close> and \<phi>: \<open>phase_saving \<phi>\<close> and
      vmtf: \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m A \<and> fst_As = hd (ys' @ xs') \<and>
           lst_As = last (ys' @ xs') \<and> next_search = option_hd xs'\<close> and
      clvls: \<open>clvls \<in> counts_maximum_level M D\<close>
      using x'x unfolding twl_st_heur_def vmtf_def by auto
    then have atm_L_le_A: \<open>atm_of L < length A\<close>
      using L_D\<^sub>0 by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    have atm_L_le_\<phi>: \<open>atm_of L < length \<phi>\<close>
      using L_D\<^sub>0 \<phi> unfolding phase_saving_def by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    obtain xs' ys' where
      \<open>vmtf_ns (ys' @ xs') m A\<close> and \<open>fst_As = hd (ys' @ xs')\<close> and \<open>next_search = option_hd xs'\<close> and
      \<open>lst_As = last (ys' @ xs')\<close>
      using vmtf by blast
    then have next_search: \<open>the next_search < length A\<close> if \<open>next_search \<noteq> None\<close>
      apply - by (rule vmtf_ns_le_length[of \<open>ys' @ xs'\<close> m A]) (use that in auto)
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      using struct_invs unfolding twl_struct_invs_def by fast
    then have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>distinct_mset_set (mset ` set (tl N))\<close>
      apply (subst append_take_drop_id[of U, symmetric])
      unfolding set_append image_Un
      by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def mset_take_mset_drop_mset drop_Suc)
    then have dist_NC: \<open>distinct (N ! C)\<close> if \<open>C > 0\<close>
      using that C_le nth_in_set_tl[of C N] by (auto simp: distinct_mset_set_def)

    have lits_NC: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! C))\<close> if \<open>C > 0\<close>
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth) (use C_le that lits_\<A>\<^sub>i\<^sub>n in auto)
    have L_hd_M: \<open>L = lit_of (hd M)\<close>
      by (cases M; cases \<open>hd M\<close>) (use trail_nempty LC proped in auto)

    have \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC by auto
    have L_notin_D: \<open>L \<notin># the D\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC by auto
    have tauto: \<open>\<not>tautology (mset (N ! C))\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_not_tauto_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that
      by auto
    have L_NC: \<open>L \<in> set (N ! C)\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_L_in_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that by auto
    have L_NC': \<open>-L \<notin> set (N ! C)\<close> if \<open>C > 0\<close>
      using tauto that L_NC apply (auto simp: tautology_decomp)
      by (metis (full_types) nat_of_lit.cases uminus_Pos uminus_of_uminus_id)
    then have uL_lookup_conflict_merge: \<open>- L \<notin># the (lookup_conflict_merge_abs_union' M N C D clvls)\<close> if \<open>C > 0\<close>
      using confl L_notin_D that resolve_cls_wl'_notin[of S C L] struct_invs C_le LC proped
       trail_nempty
      by (auto simp: lookup_conflict_merge_abs_union'_def dest: in_diffD)
    then have L_lookup_conflict_merge: \<open>L \<in># the (lookup_conflict_merge_abs_union' M N C D clvls)\<close> if \<open>C > 0\<close>
      using confl L_notin_D that resolve_cls_wl'_in[of S C L] struct_invs C_le LC proped
       trail_nempty L_confl
      by (auto dest: in_diffD)
    have [simp]: \<open>Suc 0 \<le> card_max_lvl M (the (lookup_conflict_merge_abs_union' M N C D
                    (card_max_lvl M (the D))))\<close>
      if \<open>C > 0\<close>
      using resolve_cls_wl'_card_max_lvl[of S C L clvls] LC confl C_le L_D\<^sub>0 clvls that pre
      by (auto simp: counts_maximum_level_def)
    show \<open>?\<Psi> x x'\<close>
      using confl L_confl dist_NC lits_NC C_le trail_nempty L_D\<^sub>0 tauto lits_D L_notin_D L_NC
      uL_lookup_conflict_merge L_lookup_conflict_merge atm_L_le_A atm_L_le_\<phi> next_search clvls
      by (auto simp: L_hd_M[symmetric] counts_maximum_level_def)
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n:
  assumes
    \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl S))\<close> (is \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?M\<close>)
proof -
  have [simp]: \<open>lit_of ` set (convert_lits_l b a) =  lit_of ` set a\<close> for a b
    by (induction a) auto
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have N: \<open>atms_of ?M \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S)))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def lits_of_def atms_of_def
    by (cases S)
      (auto simp: mset_take_mset_drop_mset')

  have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S))))\<close>
    using twl_struct_invs_is_\<L>\<^sub>a\<^sub>l\<^sub>l_clauses_init_clss[OF struct] \<A>\<^sub>i\<^sub>n by fast
  then show ?thesis
    using N in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff
    by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def )
qed

lemma skip_and_resolde_hd_D\<^sub>0:
  assumes
    \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    \<open>get_trail_wl S = Propagated x21 x22 # xs\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>- x21 \<in> snd ` D\<^sub>0\<close>
  using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[of S] assms
  by (cases S)
     (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset image_image
      uminus_\<A>\<^sub>i\<^sub>n_iff)

end


setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

sepref_register skip_and_resolve_loop_wl_D is_in_conflict_st
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] get_trail_twl_st_of_wl_get_trail_wl_empty_iff[simp] is_decided_hd_trail_wl_def[simp]
    is_decided_no_proped_iff[simp] skip_and_resolve_hd_in_D\<^sub>0[intro]
    literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[intro]
    get_conflict_l_st_l_of_wl[simp] is_in_conflict_st_def[simp]  neq_NilE[elim!]
    annotated_lit.splits[split] lit_and_ann_of_propagated_st_def[simp]
    annotated_lit.disc_eq_case(2)[simp]
    skip_and_resolde_hd_D\<^sub>0[simp]
    not_None_eq[simp del] maximum_level_removed_eq_count_dec_def[simp]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>let _ = the _ in _\<close> Let_def)
  unfolding
    maximum_level_removed_eq_count_dec_def[unfolded get_maximum_level_remove_def, symmetric]
  unfolding
    literals_to_update_wl_literals_to_update_wl_empty
    get_conflict_wl.simps get_trail_wl.simps
    maximum_level_removed_eq_count_dec_def[symmetric]
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
    is_in_conflict_st_def[symmetric]
    lit_and_ann_of_propagated_st_def[symmetric]
    get_max_lvl_st_def[symmetric]
    count_decided_st_alt_def[symmetric]
    get_conflict_wl_get_conflict_wl_is_Nil
    is_in_conflict_def[symmetric]
  by sepref (* slow *)

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
  uses isasat_input_bounded_nempty.skip_and_resolve_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin

definition (in -) lit_of_hd_trail_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal\<close> where
  \<open>lit_of_hd_trail_st S = lit_of (hd (get_trail_wl S))\<close>

definition lit_of_hd_trail_st_heur :: \<open>twl_st_wl_heur_trail_ref \<Rightarrow> nat literal\<close> where
  \<open>lit_of_hd_trail_st_heur = (\<lambda>((M, _), _). hd M)\<close>

lemma lit_of_hd_trail_st_heur_lit_of_hd_trail_st:
   \<open>(RETURN o lit_of_hd_trail_st_heur, RETURN o lit_of_hd_trail_st) \<in>
       [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>f twl_st_heur_pol \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: lit_of_hd_trail_st_def twl_st_heur_pol_def trail_pol_def
       lit_of_hd_trail_st_heur_def ann_lits_split_reasons_def hd_map
      intro!: frefI nres_relI)

sepref_thm lit_of_hd_trail_st_code
  is \<open>RETURN o lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>((M, _), _). M \<noteq> []]\<^sub>a twl_st_heur_pol_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_def twl_st_heur_pol_assn_def
  by sepref

concrete_definition (in -) lit_of_hd_trail_st_code
   uses isasat_input_bounded_nempty.lit_of_hd_trail_st_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) lit_of_hd_trail_st_code_def

lemmas lit_of_hd_trail_st_code_refine_code[sepref_fr_rules] =
   lit_of_hd_trail_st_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem lit_of_hd_trail_st_code_lit_of_hd_trail_st[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_st_code, RETURN o lit_of_hd_trail_st)
    \<in> [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a
      twl_st_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur_pol (\<lambda>S. get_trail_wl S \<noteq> [])
        (\<lambda>_ ((M, _), _). M \<noteq> []) (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_heur_pol_assn\<^sup>k) twl_st_heur_pol \<rightarrow>
      hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_st_code_refine_code
    lit_of_hd_trail_st_heur_lit_of_hd_trail_st] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def
        ann_lits_split_reasons_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_heur_assn_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

term extract_shorter_conflict_l
definition (in -) extract_shorter_conflict_l_trivial
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>  'v cconflict \<Rightarrow> 'v cconflict nres\<close>
where
  \<open>extract_shorter_conflict_l_trivial M NU NP UP D =
    SPEC(\<lambda>D'. D' \<noteq> None \<and> the D' \<subseteq># the D \<and>
     clause `# twl_clause_of `# mset (tl NU) + NP + UP \<Turnstile>pm the D')\<close>
(*
definition (in -) extract_shorter_conflict_st_trivial
 :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> twl_st_wl_heur_lookup_conflict nres\<close>
where
\<open>extract_shorter_conflict_st_trivial = (\<lambda>(M, N, U, D, NP, UP, Q, W). do {
    D' \<leftarrow> minimize_and_extract_highest_lookup_conflict M N D;
    RETURN (M, N, U, D, NP, UP, Q, W)})\<close> *)

definition extract_shorter_conflict_st_trivial_heur
  :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow>
       (twl_st_wl_heur_lookup_conflict \<times> nat conflict_highest_conflict) nres\<close>
where
\<open>extract_shorter_conflict_st_trivial_heur = (\<lambda>(M, NU, U, (b, D), Q', W', vm, \<phi>, clvls, cach). do {
  (D', cach, L) \<leftarrow> minimize_and_extract_highest_lookup_conflict M NU D cach;
  RETURN ((M, NU, U, (b, D'), Q', W', vm, \<phi>, clvls, cach), L)})\<close>


definition extract_shorter_conflict_list where
  \<open>extract_shorter_conflict_list = (\<lambda>M NU C NP UP. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     C \<leftarrow> extract_shorter_conflict_l_trivial M NU NP UP C;
     RETURN (map_option (add_mset (-K)) C)
  })\<close>

definition extract_shorter_conflict_list_heur where
  \<open>extract_shorter_conflict_list_heur = (\<lambda>M NU cach (b, (n, xs)). do {
     let K = lit_of (hd M);
     ASSERT(atm_of K < length xs);
     ASSERT(n \<ge> 1);
     let xs = xs[atm_of K := None];
     ((n, xs), cach, L) \<leftarrow>
        minimize_and_extract_highest_lookup_conflict M NU (n - 1, xs) cach;
     ASSERT(atm_of K < length xs);
     ASSERT(n + 1 \<le> uint_max);
     RETURN ((b, (n + 1, xs[atm_of K := Some (is_neg K)])), cach, L)
  })\<close>

(*
lemma extract_shorter_conflict_list_heur_extract_shorter_conflict_list:
  \<open>(uncurry3 extract_shorter_conflict_list_heur, uncurry3 extract_shorter_conflict_list)
   \<in> [\<lambda>(((M', NU::nat clauses_l), cach), D). literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M = M' \<and> M \<noteq> [] \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>  - lit_of (hd M) \<in># the D \<and>
         lit_of (hd M) \<notin># the D \<and> distinct_mset (the D) \<and> get_level M (lit_of (hd M)) > 0 \<and>
          \<not>tautology (the D)]\<^sub>f
      Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel \<rightarrow>
       \<langle>{((D, cach, L), C). (D, C) \<in> option_lookup_clause_rel \<and> C \<noteq> None \<and>
          highest_lit M (remove1_mset (-lit_of (hd M)) (the C)) L \<and>
          (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}\<rangle>nres_rel\<close>
  supply extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial[refine_vcg]
  unfolding extract_shorter_conflict_list_def extract_shorter_conflict_list_heur_def uncurry_def
  apply (intro frefI nres_relI)
  apply clarify
  apply refine_rcg
  subgoal
    by (cases M)
      (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_lookup_clause_rel_def lookup_clause_rel_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_lookup_clause_rel_def lookup_clause_rel_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        dest: multi_member_split)
  unfolding conc_fun_RETURN[symmetric]
   apply (rule extract_shorter_conflict_list_extract_shorter_conflict_l_trivial_spec)
  subgoal for a aa ab b ac ba y
    using mset_as_position_remove[of b y \<open>atm_of (- lit_of (hd M))\<close>]
    apply (cases \<open>lit_of (hd M)\<close>)
    apply (auto intro!: ASSERT_refine_left
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_lookup_clause_rel_def lookup_clause_rel_def
        size_remove1_mset_If minus_notin_trivial2 minus_notin_trivial)
    done
  subgoal for M' b n zs ac ba D x' x1 x1a x2 x1b x2a L
    apply (auto intro!: ASSERT_refine_left)
    subgoal
      apply (cases M)
       apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_lookup_clause_rel_def lookup_clause_rel_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff is_pos_neg_not_is_pos
          extract_shorter_conflict_l_trivial_def
          intro!: mset_as_position.add
          dest!: multi_member_split[of _ D])
      done
    subgoal for D'
      using simple_clss_size_upper_div2[of D'] literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of D D']
        distinct_mset_mono[of D' D] not_tautology_mono[of D' D]
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_lookup_clause_rel_def lookup_clause_rel_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff uint_max_def
          dest!: extract_shorter_conflict_l_trivial_subset_msetD)
    subgoal
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_lookup_clause_rel_def lookup_clause_rel_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff is_pos_neg_not_is_pos
          extract_shorter_conflict_l_trivial_def
          intro!: mset_as_position.add
          dest!: multi_member_split[of _ D])
    done
  done
*)

abbreviation extract_shorter_conflict_l_trivial_pre where
\<open>extract_shorter_conflict_l_trivial_pre \<equiv> \<lambda>(M, D). literals_are_in_\<L>\<^sub>i\<^sub>n (mset (fst D))\<close>

sepref_register extract_shorter_conflict_l_trivial

type_synonym (in -) lookup_clause_rel_with_cls_with_highest =
  \<open>conflict_option_rel \<times> (nat literal \<times> nat)option\<close>

definition option_lookup_clause_rel_with_cls_with_highest2
  :: \<open>nat literal \<Rightarrow> (nat, 'a) ann_lits \<Rightarrow> (lookup_clause_rel_with_cls_with_highest \<times> nat clause option) set\<close> where
  \<open>option_lookup_clause_rel_with_cls_with_highest2 K M = {(((b, xs), L), D).
     D \<noteq> None \<and> ((b, xs), D) \<in> option_lookup_clause_rel \<and> highest_lit M (remove1_mset K (the D)) L \<and>
     (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd xs))}\<close>

abbreviation option_lookup_clause_rel_with_cls_with_highest where
  \<open>option_lookup_clause_rel_with_cls_with_highest M \<equiv> option_lookup_clause_rel_with_cls_with_highest2 (-lit_of (hd M)) M\<close>

lemmas option_lookup_clause_rel_with_cls_with_highest_def = option_lookup_clause_rel_with_cls_with_highest2_def

type_synonym (in -) conflict_with_cls_with_highest_assn =
   \<open>option_lookup_clause_assn \<times> (uint32 \<times> uint32) option\<close>

abbreviation conflict_with_cls_int_with_highest_assn
 :: \<open>lookup_clause_rel_with_cls_with_highest \<Rightarrow> conflict_with_cls_with_highest_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_with_highest_assn \<equiv>
    (bool_assn *a uint32_nat_assn *a array_assn (option_assn bool_assn)) *a option_assn (unat_lit_assn *a uint32_nat_assn)\<close>

definition conflict_with_cls_with_cls_with_highest_assn
  :: \<open>(nat, 'a) ann_lits \<Rightarrow> nat clause option \<Rightarrow> conflict_with_cls_with_highest_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_with_cls_with_highest_assn M \<equiv>
    hr_comp conflict_with_cls_int_with_highest_assn (option_lookup_clause_rel_with_cls_with_highest M)\<close>

(*)
lemma extract_shorter_conflict_list_extract_shorter_conflict_l_trivial:
  \<open>(uncurry extract_shorter_conflict_list, uncurry (RETURN oo extract_shorter_conflict_l_trivial)) \<in>
  [\<lambda>(M, D). M \<noteq> [] \<and> D \<noteq> None \<and> -lit_of (hd M) \<in># the D \<and> 0 < get_level M (lit_of (hd M))]\<^sub>f
   Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: extract_shorter_conflict_list_def extract_shorter_conflict_l_trivial_def
      Let_def)
*)

type_synonym (in -) twl_st_wl_confl_extracted_int =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    lookup_clause_rel_with_cls_with_highest \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times>
    bool list \<times> nat \<times> nat conflict_min_cach\<close>

definition twl_st_heur_confl_extracted2
  :: \<open>nat literal \<Rightarrow> (twl_st_wl_confl_extracted_int \<times> twl_st_wl_heur) set\<close> where
\<open>twl_st_heur_confl_extracted2 L =
  {((M', N', U', D', Q', W', vm', \<phi>', clvls', cach'), (M, N, U, D, Q, W, vm, \<phi>, clvls, cach)).
    M = M' \<and> N' = N \<and> U' = U \<and>
     (D', D) \<in> option_lookup_clause_rel_with_cls_with_highest2 L M \<and>
     Q' = Q \<and>
    W' = W \<and>
    vm = vm' \<and>
    \<phi>' = \<phi> \<and>
    clvls' = clvls \<and>
    cach' = cach
  }\<close>

definition twl_st_heur_confl_extracted
  :: \<open>(twl_st_wl_confl_extracted_int \<times> twl_st_wl_heur) set\<close>
where
\<open>twl_st_heur_confl_extracted =
  {((M', N', U', D', Q', W', vm', \<phi>', clvls', cach'), (M, N, U, D, Q, W, vm, \<phi>, clvls, cach)).
    M = M' \<and> N' = N \<and> U' = U \<and>
     (D', D) \<in> option_lookup_clause_rel_with_cls_with_highest M \<and>
     Q' = Q \<and>
    W' = W \<and>
    vm = vm' \<and>
    \<phi>' = \<phi> \<and>
    clvls' = clvls \<and>
    cach' = cach
  }\<close>

type_synonym (in -) twl_st_wll_trail_confl_extracted =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_with_highest_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times> uint32 \<times> minimize_assn\<close>


definition twl_st_confl_extracted_int_assn
  :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
where
  \<open>twl_st_confl_extracted_int_assn =
    trail_assn *a clauses_ll_assn *a nat_assn *a
    conflict_with_cls_int_with_highest_assn *a
    clause_l_assn *a
    arrayO_assn (arl_assn nat_assn) *a
    vmtf_remove_conc *a phase_saver_conc *a
    uint32_nat_assn *a
    cach_refinement_assn\<close>

definition (in isasat_input_ops) twl_st_heur_no_clvls
  :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_no_clvls =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach), (M, N, U, D, NP, UP, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach
  }\<close>

definition twl_st_confl_extracted_assn
  :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
  where
\<open>twl_st_confl_extracted_assn = hr_comp twl_st_confl_extracted_int_assn
  (twl_st_heur_confl_extracted O twl_st_heur_no_clvls)\<close>

definition twl_st_confl_extracted_assn2
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
  where
\<open>twl_st_confl_extracted_assn2 L = hr_comp twl_st_confl_extracted_int_assn
  (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls)\<close>

definition extract_shorter_conflict_list_st_int
  :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow>
       (twl_st_wl_heur_lookup_conflict \<times> nat conflict_highest_conflict) nres\<close>
where
  \<open>extract_shorter_conflict_list_st_int = (\<lambda>(M, N, U, D, Q', W', vm, \<phi>, clvls, cach). do {
     (D, cach, L) \<leftarrow> extract_shorter_conflict_list_heur M N cach D;
     RETURN ((M, N, U, D, Q', W', vm, \<phi>, clvls, cach), L)})
\<close>

definition extract_shorter_conflict_list_st where
  \<open>extract_shorter_conflict_list_st =
     (\<lambda>(M, N, U, D, NP, UP, WS, Q). do {
        D \<leftarrow> extract_shorter_conflict_list M N D NP UP;
        RETURN (M, N, U, D, NP, UP, WS, Q)})\<close>

term extract_shorter_conflict_wl

lemma extract_shorter_conflict_list_st_extract_shorter_conflict_st_trivial:
  \<open>(extract_shorter_conflict_list_st, extract_shorter_conflict_wl) \<in>
     [\<lambda>S. get_trail_wl S \<noteq> [] \<and> -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
         get_conflict_wl S \<noteq> None \<and> get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S))) > 0]\<^sub>f
     Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding extract_shorter_conflict_list_st_def
  extract_shorter_conflict_list_def
  by (intro frefI nres_relI)
    (auto simp: Let_def extract_shorter_conflict_l_trivial_def extract_shorter_conflict_wl_def
    RES_RETURN_RES dest!: multi_member_split)

lemma extract_shorter_conflict_list_st_int_extract_shorter_conflict_st_trivial_heur:
  \<open>(extract_shorter_conflict_list_st_int, extract_shorter_conflict_st_trivial_heur) \<in>
     [\<lambda>S. get_conflict_wl_heur S \<noteq> None \<and> get_trail_wl_heur S \<noteq> [] \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
        -lit_of (hd (get_trail_wl_heur S)) \<in># the (get_conflict_wl_heur S) \<and>
        0 < get_level (get_trail_wl_heur S) (lit_of (hd (get_trail_wl_heur S))) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl_heur S)) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
        distinct_mset (the (get_conflict_wl_heur S)) \<and> \<not>tautology (the (get_conflict_wl_heur S))]\<^sub>f
      (twl_st_wl_heur_lookup_lookup_clause_relqq) \<rightarrow> \<langle>twl_st_heur_confl_extractedgg \<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have H: \<open>a \<noteq> [] \<Longrightarrow>
   - lit_of (hd a) \<in># the ac \<Longrightarrow>
   (\<exists>y. ac = Some y) \<Longrightarrow> 0 < get_level a (lit_of (hd a)) \<Longrightarrow>
   extract_shorter_conflict_list_st (a, aa, ab, ac, ad, ae, af, b)
       \<le> \<Down> Id (RETURN (a, aa, ab, extract_shorter_conflict_l_trivial a ac, ad, ae, af, b))\<close>
    for a :: \<open>(nat, nat) ann_lits\<close> and aa :: \<open>nat clauses_l\<close> and
          ab :: nat and ac and ad ae :: \<open>nat clauses\<close> and af :: \<open>nat clause\<close> and
          b ::\<open>nat literal \<Rightarrow> nat list\<close>
    using extract_shorter_conflict_list_st_extract_shorter_conflict_st_trivial[unfolded fref_def
      extract_shorter_conflict_st_trivial_def nres_rel_def, simplified, rule_format,
      of a ac aa ab ad ae af b] by auto
  have H':
    \<open>M \<noteq> [] \<and>
     (\<exists>y. ba = Some y) \<and>
     - lit_of (hd M) \<in># the ba \<and>
     0 < get_level M (lit_of (hd M)) \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n (the ba) \<and>
     M \<noteq> [] \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
     - lit_of (hd M) \<in># the ba \<and>
     lit_of (hd M) \<notin># the ba \<and>
     distinct_mset (the ba) \<and>
     0 < get_level M (lit_of (hd M)) \<and>
     \<not> tautology (the ba) \<and>
     ((a, aa, b), ba) \<in> option_lookup_clause_rel \<Longrightarrow>
     extract_shorter_conflict_list_heur M (a, aa, b)
     \<le> \<Down> {((D, L), C).
           (D, C) \<in> option_lookup_clause_rel \<and>
           (\<exists>y. C = Some y) \<and>
           highest_lit M
            (remove1_mset (- lit_of (hd M)) (the C)) L \<and>
           (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}
         (RETURN (extract_shorter_conflict_l_trivial M ba))\<close> for a aa b ba M
    using extract_shorter_conflict_list_heur_extract_shorter_conflict_list
       [FCOMP extract_shorter_conflict_list_extract_shorter_conflict_l_trivial,
         unfolded fref_def
            extract_shorter_conflict_st_trivial_def nres_rel_def, of M] by auto
  show ?thesis
    apply (intro nres_relI frefI)
    subgoal for S' S
      apply (cases S; cases S')
      apply (auto simp: extract_shorter_conflict_list_st_int_def
          extract_shorter_conflict_st_trivial_heur_def twl_st_wl_heur_lookup_lookup_clause_rel_def)
    apply (rule intro_bind_refine[OF H', of _ \<open>get_conflict_wl_heur S\<close>])
    subgoal by auto
    subgoal
      by (auto simp: twl_st_heur_confl_extracted_def option_lookup_clause_rel_with_cls_with_highest_def)
    done
  done
qed


fun get_trail_wl_heur_conflict :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur_conflict (M, N, U, D, _) = M\<close>

lemma extract_shorter_conflict_st_trivial_extract_shorter_conflict_wl:
  \<open>(extract_shorter_conflict_st_trivial, extract_shorter_conflict_wl) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      get_conflict_wl S \<noteq> None \<and> no_skip S \<and> no_resolve S \<and> get_conflict_wl S \<noteq> Some {#}]\<^sub>f
    Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>extract_shorter_conflict_st_trivial S \<le>  (extract_shorter_conflict_wl S)\<close>
    if
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
      (is \<open>twl_struct_invs ?S\<close>) and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
      D: \<open>get_conflict_wl S \<noteq> None\<close> \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
      n_s_s: \<open>no_skip S\<close> and
      n_s_r: \<open>no_resolve S\<close>
    for S
  proof -
    obtain M N U D NP UP Q W where
      [simp]: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
      by (cases S)
    have
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of ?S)\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of ?S)\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>M \<Turnstile>as CNot (the D)\<close>
      using confl D unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto simp: clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    then have M_nempty: \<open>M ~= []\<close>
      using D by auto
    have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) \<Turnstile>p the D\<close>
      using that(2-) learned
      by (auto simp: clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of ?S) \<Turnstile>pm
        filter_mset (\<lambda>L. get_level (trail (state\<^sub>W_of ?S)) L > 0) (the (conflicting (state\<^sub>W_of ?S)))\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(1))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto)
      subgoal using D by (auto)
      subgoal using M_nempty by (cases M, auto)
      done
    moreover have \<open>- lit_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of ?S)) \<in>#
      {#L \<in># the (conflicting (state\<^sub>W_of ?S)). 0 < get_level (trail (state\<^sub>W_of ?S)) L#}\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto)
      subgoal using D by (auto)
      subgoal using M_nempty by (cases M, auto)
      done
    moreover have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) =
          mset ` set (tl N) \<union> set_mset NP \<union> set_mset UP\<close>
      apply (subst (2) append_take_drop_id[of U \<open>tl N\<close>, symmetric])
      unfolding set_append drop_Suc
      by auto
    ultimately show ?thesis
      using that(2-) D M_nempty
      by (auto simp: clauses_def mset_take_mset_drop_mset'
          extract_shorter_conflict_st_trivial_def extract_shorter_conflict_wl_def
          extract_shorter_conflict_l_trivial_def)
  qed
  show ?thesis
    by (intro frefI nres_relI) (auto intro!: H)
qed

definition find_decomp_wl_imp :: "(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> nat literal \<Rightarrow> vmtf_remove_int \<Rightarrow>
   ((nat, nat) ann_lits \<times> vmtf_remove_int) nres" where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 D L vm. do {
    let lev = get_maximum_level M\<^sub>0 (remove1_mset (-L) (the D));
    let k = count_decided M\<^sub>0;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j = count_decided M \<and> j \<ge> lev \<and>
           (M = [] \<longrightarrow> j = lev) \<and>
           (\<exists>M'. M\<^sub>0 = M' @ M \<and> (j = lev \<longrightarrow> M' \<noteq> [] \<and> is_decided (last M'))) \<and>
           vm' \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j > lev)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            if is_decided (hd M)
            then let L = atm_of (lit_of (hd M)) in RETURN (j-1, tl M, vmtf_unset L vm)
            else let L = atm_of (lit_of (hd M)) in RETURN (j, tl M, vmtf_unset L vm)}
         )
         (k, M\<^sub>0, vm);
    RETURN (M, vm')
  })\<close>


definition find_decomp_wl_imp_pre where
  \<open>find_decomp_wl_imp_pre = (\<lambda>(((M, D), L), vm). M \<noteq> [] \<and> D \<noteq> None \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> -L \<in># the D \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> vm \<in> vmtf M)\<close>

definition (in -) get_maximum_level_remove_int :: \<open>(nat, 'a) ann_lits \<Rightarrow>
    lookup_clause_rel_with_cls_with_highest \<Rightarrow> nat literal \<Rightarrow>  nat\<close> where
  \<open>get_maximum_level_remove_int = (\<lambda>_ (_, D) _.
    (case D of None \<Rightarrow> 0 | Some i \<Rightarrow> snd i))\<close>

sepref_thm get_maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo get_maximum_level_remove_int)\<close>
  :: \<open>trail_assn\<^sup>k  *\<^sub>a conflict_with_cls_int_with_highest_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a
       uint32_nat_assn\<close>
  supply uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
    snd_hnr_pure[sepref_fr_rules]
  unfolding get_maximum_level_remove_int_def zero_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) get_maximum_level_remove_code
   uses isasat_input_bounded_nempty.get_maximum_level_remove_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) get_maximum_level_remove_code_def

lemmas get_maximum_level_remove_code_hnr[sepref_fr_rules] =
   get_maximum_level_remove_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in -) get_maximum_level_remove' where
  \<open>get_maximum_level_remove' M D L = get_maximum_level_remove M (the D) L\<close>

lemma (in -)get_maximum_level_remove_single_removed[simp]: \<open>get_maximum_level_remove M {#L#} L = 0\<close>
  unfolding get_maximum_level_remove_def by auto

lemma (in -) get_maximum_level_remove_empty[simp]: \<open>get_maximum_level_remove M {#} = (\<lambda>_. 0)\<close>
 unfolding get_maximum_level_remove_def by auto

lemma get_maximum_level_remove_int_get_maximum_level_remove':
  \<open>(uncurry2 (RETURN ooo get_maximum_level_remove_int), uncurry2 (RETURN ooo get_maximum_level_remove')) \<in>
     [\<lambda>((M', D), L). M' = M \<and> L = -lit_of (hd M) \<and> M' \<noteq> [] \<and> D \<noteq> None]\<^sub>f Id \<times>\<^sub>f (option_lookup_clause_rel_with_cls_with_highest M) \<times>\<^sub>f Id \<rightarrow>
    \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: get_maximum_level_remove_int_def get_maximum_level_remove'_def
      option_lookup_clause_rel_with_cls_with_highest_def highest_lit_def
      get_maximum_level_remove_def[symmetric] remove1_mset_empty_iff
      split: option.splits)

lemma get_maximum_level_remove'_hnr[sepref_fr_rules]:
  \<open>(uncurry2 get_maximum_level_remove_code, uncurry2 (RETURN \<circ>\<circ>\<circ> get_maximum_level_remove'))
     \<in> [\<lambda>((a, b), ba). a = M \<and> ba = - lit_of (hd M) \<and> a \<noteq> [] \<and> b \<noteq> None]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
   uint32_nat_assn\<close>
  using get_maximum_level_remove_code_hnr[FCOMP get_maximum_level_remove_int_get_maximum_level_remove']
  unfolding conflict_with_cls_with_cls_with_highest_assn_def[symmetric] by simp

sepref_register find_decomp_wl_imp
sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry3 (PR_CONST find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>(((M', D), L), vm). M' = M \<and> L = lit_of (hd M') \<and> M' \<noteq> [] \<and> find_decomp_wl_imp_pre (((M', D), L), vm)]\<^sub>a
         trail_assn\<^sup>d *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_assn *a vmtf_remove_conc\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_decomp_wl_imp_pre_def get_maximum_level_remove'_def[symmetric]
  supply [[goals_limit=1]]   literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp_code.refine_raw
   is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition find_decomp_wvmtf_ns  where
  \<open>find_decomp_wvmtf_ns =
     (\<lambda>(M::(nat, nat) ann_lits) (D::nat clause option) (L::nat literal) _.
        SPEC(\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1 \<and> vm \<in> vmtf M1))\<close>


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, U, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, U, D, oth)
  })\<close>

definition find_decomp_wl_st_int :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>L (M, N, U, D, W, Q, vm, \<phi>).  do{
     (M', vm) \<leftarrow> find_decomp_wvmtf_ns M D L vm;
    RETURN (M', N, U, D, W, Q, vm, \<phi>)
  })\<close>


lemma
  assumes
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W))\<close> and
    D: \<open>D \<noteq> None\<close> \<open>E \<noteq> None\<close> \<open>the E \<noteq> {#}\<close> and M\<^sub>0: \<open>M\<^sub>0 \<noteq> []\<close> and ex_decomp: \<open>ex_decomp_of_max_lvl M\<^sub>0 D L\<close> and
    L: \<open>L = lit_of (hd M\<^sub>0)\<close> and
    E_D\<^sub>0: \<open>the E \<subseteq># the D\<close> and
    D\<^sub>0: \<open>D \<noteq> None\<close> and
   vm: \<open>vm \<in> vmtf M\<^sub>0\<close> and
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M\<^sub>0)\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp M\<^sub>0 E L vm \<le> find_decomp_wvmtf_ns M\<^sub>0 E L vm\<close>
     (is ?decomp)
proof -
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>'a list\<close>
    by (metis append.assoc append_Cons append_Nil list.exhaust list.sel(3) tl_Nil)
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that(1) zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2
  have [iff]: \<open>convert_lits_l N M = [] \<longleftrightarrow> M = []\<close> for M
    by (cases M) auto
  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>distinct_mset (the D)\<close>
    using D\<^sub>0 dist by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)
  then have dist_D: \<open>distinct_mset (the E)\<close>
    using distinct_mset_mono[OF E_D\<^sub>0] by fast
  have \<open>M\<^sub>0 \<Turnstile>as CNot (the D)\<close>
    using D\<^sub>0 confl by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  then have M\<^sub>0_CNot_D: \<open>M\<^sub>0 \<Turnstile>as CNot (the E)\<close>
    using E_D\<^sub>0 by (simp add: mset_subset_eqD true_annots_true_cls_def_iff_negation_in_model)

  have n_d: \<open>no_dup M\<^sub>0\<close>
    using lev_inv by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
  have \<open>atm_of L \<notin> atms_of (remove1_mset (- L) (the E))\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    moreover have \<open>-L \<notin># remove1_mset (- L) (the E)\<close>
      using dist_D by (meson distinct_mem_diff_mset multi_member_last)
    ultimately have \<open>L \<in># the E\<close>
      using D by (auto simp: atms_of_def atm_of_eq_atm_of dest: in_diffD)

    then have \<open>-L \<in> lits_of_l M\<^sub>0\<close>
      using M\<^sub>0_CNot_D by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then show False
      using n_d L M\<^sub>0 by (cases M\<^sub>0) (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  qed
  moreover have \<open>L \<in> set (N!C)\<close> if \<open> hd M\<^sub>0 = Propagated L C\<close> and \<open>C > 0\<close> for C
    using confl D M\<^sub>0 L that
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases M\<^sub>0; cases \<open>hd M\<^sub>0\<close>) (auto 5 5 split: if_splits)
  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply simp
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  thm WHILEIT_rule
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_wvmtf_ns_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal by simp
    subgoal by auto
    subgoal using M\<^sub>0 by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal
      using ex_decomp get_level_neq_Suc_count_decided E_D\<^sub>0 (*TODO Proof*)
      apply (auto simp: count_decided_butlast butlast_nil_iff eq_commute[of \<open>[_]\<close>] mset_le_subtract
          ex_decomp_of_max_lvl_def
          intro: butlast)
      using get_maximum_level_mono[of \<open>remove1_mset (-L) (the E)\<close> \<open>remove1_mset (-L) (the D)\<close>]
      by (metis E_D\<^sub>0 count_decided_ge_get_level mset_le_subtract
          not_less_eq_eq)
    subgoal using vm by auto
    subgoal using lits by auto
    subgoal using lits by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by (auto simp: count_decided_butlast count_decided_tl_if)[]
    subgoal for s a b aa ba x1 x2 x1a x2a by (cases aa) (auto simp: count_decided_ge_get_maximum_level)
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal for s D M
      apply (auto simp: count_decided_ge_get_maximum_level ex_decomp_get_ann_decomposition_iff
          get_lev_last)
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append simp del: append_butlast_last_id)
        apply (metis append_butlast_last_id)
       defer
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append snoc_eq_iff_butlast' count_decided_ge_get_maximum_level
          ex_decomp_get_ann_decomposition_iff get_lev_last)
      done
    done
qed


definition find_decomp_wvmtf_ns_pre where
  \<open>find_decomp_wvmtf_ns_pre = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NP UP Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
      vm \<in> vmtf M)\<close>

lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry3 find_decomp_wl_imp, uncurry3 find_decomp_wvmtf_ns) \<in>
    [find_decomp_wvmtf_ns_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: find_decomp_wvmtf_ns_pre_def simp del: twl_st_of_wl.simps
     intro!: find_decomp_wl_imp_le_find_decomp_wl')

definition find_decomp_wvmtf_ns_pre_full where
  \<open>find_decomp_wvmtf_ns_pre_full M' = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NP UP Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
      vm \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the E) \<and> -L \<in># the E \<and> M = M')\<close>

lemma find_decomp_wl_pre_full_alt_def:
  \<open>find_decomp_wvmtf_ns_pre_full M = (\<lambda>(((b, a), c), d). find_decomp_wvmtf_ns_pre (((b, a), c), d) \<and>
         b = M \<and>
         c = lit_of (hd b) \<and>
         b \<noteq> [] \<and>
              find_decomp_wl_imp_pre (((b, a), c), d))\<close>
  apply (intro ext)
  unfolding find_decomp_wvmtf_ns_pre_def find_decomp_wl_imp_pre_def find_decomp_wvmtf_ns_pre_full_def
  by fastforce

sepref_register find_decomp_wvmtf_ns
lemma find_decomp_wl_imp_code_find_decomp_wl'[sepref_fr_rules]:
  \<open>(uncurry3 find_decomp_wl_imp_code, uncurry3 (PR_CONST find_decomp_wvmtf_ns))
     \<in> [find_decomp_wvmtf_ns_pre_full M]\<^sub>a
     trail_assn\<^sup>d *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
    trail_assn *a vmtf_remove_conc\<close>
  using find_decomp_wl_imp_code[unfolded PR_CONST_def, FCOMP find_decomp_wl_imp_find_decomp_wl']
  unfolding PR_CONST_def find_decomp_wl_pre_full_alt_def[symmetric]
  .

lemma get_all_ann_decomposition_get_level:
  assumes
    L': \<open>L' = lit_of (hd M')\<close> and
    nd: \<open>no_dup M'\<close> and
    decomp: \<open>(Decided K # a, M2) \<in> set (get_all_ann_decomposition M')\<close> and
    lev_K: \<open>get_level M' K = Suc (get_maximum_level M' (remove1_mset (- L') y))\<close> and
    L: \<open>L \<in># remove1_mset (- lit_of (hd M')) y\<close>
  shows \<open>get_level a L = get_level M' L\<close>
proof -
  obtain M3 where M3: \<open>M' = M3 @ M2 @ Decided K # a\<close>
    using decomp by blast
  from lev_K have lev_L: \<open>get_level M' L < get_level M' K\<close>
    using get_maximum_level_ge_get_level[OF L, of M'] unfolding L'[symmetric] by auto
  have [simp]: \<open>get_level (M3 @ M2 @ Decided K # a) K = Suc (count_decided a)\<close>
    using nd unfolding M3 by auto
  have undef:\<open>undefined_lit (M3 @ M2) L\<close>
    using lev_L get_level_skip_end[of \<open>M3 @ M2\<close> L \<open>Decided K # a\<close>] unfolding M3
    by auto
  then have \<open>atm_of L \<noteq> atm_of K\<close>
    using lev_L unfolding M3 by auto
  then show ?thesis
    using undef unfolding M3 by (auto simp: get_level_cons_if)

qed

lemma find_decomp_wl_st_int_find_decomp_wl_st:
  \<open>(uncurry find_decomp_wl_st_int, uncurry find_decomp_wl_st) \<in>
   [\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> get_trail_wl S = M \<and>
       no_dup (get_trail_wl S) \<and> L = lit_of(hd M)]\<^sub>f
   nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_no_clvls \<rightarrow>
   \<langle>{(S', S). (S', S) \<in> twl_st_heur_no_clvls \<and>
     (\<forall>L \<in># remove1_mset (-lit_of (hd M)) (the (get_conflict_wl S)). get_level (get_trail_wl S) L = get_level M L)}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for L' M' N' U' D' K' W' Q' A' m'  _ _ _ _ _ \<phi> L M N U D NP UP W Q
    apply (auto simp: find_decomp_wl_st_int_def find_decomp_wl_st_def
        list_mset_rel_def br_def twl_st_heur_def twl_st_heur_no_clvls_def
        intro!: bind_refine[where R' =
          \<open>{((Ms', vm'), Ms). Ms = Ms' \<and> (\<exists>M''. M = M'' @ Ms) \<and> vm' \<in> vmtf Ms &
               (\<forall>L \<in># remove1_mset (-lit_of (hd M)) (the D). get_level Ms L = get_level M L)}\<close>]
          dest: no_dup_appendD)
    apply (auto simp: find_decomp_wvmtf_ns_def find_decomp_wl'_def intro:
        dest: no_dup_appendD)
    apply (rule RES_refine)
    apply (auto)
      apply (rule_tac x=K in exI; auto 5 5)
    by (auto intro: get_all_ann_decomposition_get_level)
  done

fun conflict_merge_wl where
  \<open>conflict_merge_wl D (M, N, U, _, oth) = (M, N, U, D, oth)\<close>

definition twl_st_confl_extracted_int_assn' where
 \<open>twl_st_confl_extracted_int_assn' M =
  (hr_comp trail_pol_assn trail_pol *a
      clauses_ll_assn *a
      nat_assn *a
      conflict_with_cls_with_cls_with_highest_assn M *a
      clause_l_assn *a
      arrayO_assn (arl_assn nat_assn) *a
      vmtf_remove_conc *a phase_saver_conc *a
      uint32_nat_assn *a
      cach_refinement_assn)\<close>

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry (PR_CONST find_decomp_wl_st_int)\<close>
  :: \<open>[\<lambda>(L, (M', N, U, D, W, Q, vm, \<phi>)). find_decomp_wvmtf_ns_pre_full M (((M', D), L), vm)]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a (twl_st_confl_extracted_int_assn' M)\<^sup>d \<rightarrow>
        (twl_st_confl_extracted_int_assn' M)\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def twl_st_heur_assn_def twl_st_confl_extracted_int_assn'_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp'_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_code_def

lemmas find_decomp_wl_imp'_code_hnr[sepref_fr_rules] =
  find_decomp_wl_imp'_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


lemma find_decomp_wl_st_find_decomp_wl:
  \<open>(uncurry find_decomp_wl_st, uncurry find_decomp_wl) \<in> [\<lambda>_. True]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  unfolding no_resolve_def no_skip_def
  apply (intro frefI nres_relI)
  subgoal premises p for S S'
    using p
    by (cases S, cases S')
        (auto intro!: find_decomp_wl_imp_le_find_decomp_wl'
        simp: find_decomp_wl_st_def find_decomp_wl'_def find_decomp_wl_def
        RES_RETURN_RES)
  done


lemma twl_st_heur_confl_extracted_twl_st_heur:
  \<open>twl_st_heur_confl_extracted O twl_st_heur =
    {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_lookup_clause_rel_with_cls_with_highest M \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     clvls \<in> counts_maximum_level M D \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M\<and>
     cach_refinement_empty cach}\<close>
  unfolding twl_st_heur_confl_extracted_def twl_st_heur_def
  by fast

lemma twl_st_heur_confl_extracted2_twl_st_heur:
  \<open>twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls =
    {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_lookup_clause_rel_with_cls_with_highest2 L M \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M\<and>
     cach_refinement_empty cach}\<close>
  unfolding twl_st_heur_confl_extracted2_def twl_st_heur_no_clvls_def
  by fast

definition find_decomp_wl_pre where
   \<open>find_decomp_wl_pre M = (\<lambda>(L, S). \<exists>D\<^sub>0. get_conflict_wl S \<noteq> None \<and>
               the (get_conflict_wl S) \<noteq> {#} \<and>
               get_trail_wl S \<noteq> [] \<and>
               ex_decomp_of_max_lvl (get_trail_wl S) D\<^sub>0 L \<and>
               L = lit_of (hd (get_trail_wl S)) \<and>
               twl_struct_invs (twl_st_of_wl None (conflict_merge_wl D\<^sub>0 S)) \<and>
               the (get_conflict_wl S) \<subseteq># the D\<^sub>0 \<and> D\<^sub>0 \<noteq> None \<and> get_trail_wl S = M \<and> L = lit_of (hd M) \<and>
               literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
               -L \<in># the (get_conflict_wl S) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the D\<^sub>0))\<close>

lemma find_decomp_wl_imp'_code_find_decomp_wl[sepref_fr_rules]:
  fixes M :: \<open>(nat, nat) ann_lits\<close>
  shows \<open>(uncurry find_decomp_wl_imp'_code, uncurry find_decomp_wl) \<in>
    [find_decomp_wl_pre M]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a twl_st_confl_extracted_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn2 (-lit_of (hd M))\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  define L where L: \<open>L \<equiv> -lit_of (hd M)\<close>
  have H: \<open>?c
       \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f Id) (\<lambda>_. True)
            (\<lambda>_. comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls)
              (\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and>
                  get_trail_wl S = M \<and> no_dup (get_trail_wl S) \<and> L = lit_of (hd M))
              (\<lambda>_ (L, M', N, U, D, W, Q, vm, \<phi>). find_decomp_wvmtf_ns_pre_full M (((M', D), L), vm))
              (\<lambda>_. True))
             (\<lambda>_. True)]\<^sub>a
        hrp_comp (hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a (twl_st_confl_extracted_int_assn' M)\<^sup>d)
                           (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls))
                 (nat_lit_lit_rel \<times>\<^sub>f Id) \<rightarrow>
        hr_comp (hr_comp (twl_st_confl_extracted_int_assn' M)
                                  {(S', S). (S', S) \<in> twl_st_heur_no_clvls \<and>
                                     (\<forall>L\<in>#remove1_mset (- lit_of (hd M)) (the (get_conflict_wl S)).
                                       get_level (get_trail_wl S) L = get_level M L)})
               Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[
      OF hfref_compI_PRE_aux[OF find_decomp_wl_imp'_code_hnr[unfolded PR_CONST_def]
            find_decomp_wl_st_int_find_decomp_wl_st]
         find_decomp_wl_st_find_decomp_wl]

    .
  have HH: \<open>H = H' \<Longrightarrow> unat_lit_assn *a H = unat_lit_assn *a H'\<close> for H H'
    by auto
  have 2: \<open>(a *a b *a c *a (hr_comp d d')*a e *a f*a g) =
       hr_comp (a *a b *a c *a d *a e *a f *a g)
           (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r d' \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id)\<close>
    for a :: \<open>'a \<Rightarrow> 'b \<Rightarrow> assn\<close> and  b c d d' e f g
    by auto

  define twl_st_heur' :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
    \<open>twl_st_heur' =
      {((M'', N', U', D', Q', W', vm, \<phi>, clvls, cach), (M', N, U, D, NP, UP, Q, W)).
        M' = M'' \<and> M' = M \<and> N' = N \<and> U' = U \<and> D = D' \<and>
         Q' = Q \<and>
        (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
        vm \<in> vmtf M \<and>
        phase_saving \<phi> \<and>
        no_dup M \<and>
        cach_refinement_empty cach
      }\<close>
  have decomp_1: \<open>hr_comp (twl_st_confl_extracted_int_assn' M) twl_st_heur_no_clvls
        (M, aa, ab, ac, ad, ae, af, b) =
        hr_comp (twl_st_confl_extracted_int_assn' M)
            (twl_st_heur')
       (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
    by (auto simp: hr_comp_def twl_st_heur_no_clvls_def twl_st_heur'_def ex_assn_pair_split
        eq_commute[of ac] intro!: ext)
  have decomp_2: \<open>hr_comp twl_st_confl_extracted_int_assn
     (twl_st_heur_confl_extracted O twl_st_heur_no_clvls) (M, aa, ab, ac, ad, ae, af, b) =
       hr_comp twl_st_confl_extracted_int_assn
     (twl_st_heur_confl_extracted O twl_st_heur') (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
  proof -
    have [simp]: \<open>(a, M, X) \<in> twl_st_heur_confl_extracted O twl_st_heur_no_clvls \<longleftrightarrow>
          (a, M, X) \<in> twl_st_heur_confl_extracted O twl_st_heur'\<close> for X a
      unfolding twl_st_heur_confl_extracted_def twl_st_heur_no_clvls_def twl_st_heur'_def
      by fastforce
    show ?thesis
      by (auto simp: hr_comp_def intro!: ext)
  qed
  have decomp: \<open>((Id \<times>\<^sub>f (Id \<times>\<^sub>f (nat_rel \<times>\<^sub>f (option_lookup_clause_rel_with_cls_with_highest M \<times>\<^sub>f
          (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id)))))) O twl_st_heur') =
     (twl_st_heur_confl_extracted O twl_st_heur')\<close>
    apply (auto simp: twl_st_heur_confl_extracted_def twl_st_heur'_def)
     apply fast
    apply force
    done
  have 1: \<open>hr_comp (twl_st_confl_extracted_int_assn' M) twl_st_heur_no_clvls
        (M, aa, ab, ac, ad, ae, af, b) =
        hr_comp twl_st_confl_extracted_int_assn
         (twl_st_heur_confl_extracted O twl_st_heur_no_clvls)
       (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
    apply (subst decomp_1)
    apply (subst decomp_2)

    unfolding twl_st_confl_extracted_int_assn'_def twl_st_heur_confl_extracted_twl_st_heur
    twl_st_confl_extracted_int_assn_def conflict_with_cls_with_cls_with_highest_assn_def
    apply (subst 2)
    apply (subst hr_comp_assoc)
    apply (subst decomp)
    ..
  have 0:
    \<open>twl_struct_invs
        (convert_lits_l aa M,
         {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take ab (tl aa))#},
         {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc ab) aa)#},
         Some ya, ad, ae, {#}, af) \<Longrightarrow>  no_dup M\<close> for aa ab ya ad ae af
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by simp
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def twl_st_heur_no_clvls_def find_decomp_wvmtf_ns_pre_full_def find_decomp_wl_pre_def
    apply (auto dest: 0)
    by (rule_tac x=aa in exI, rule_tac x=ab in exI, rule_tac x=\<open>Some ya\<close> in exI)
      (use literals_are_in_\<L>\<^sub>i\<^sub>n_mono in auto)

  have \<open>?c \<in> [?pre]\<^sub>a ?im' \<rightarrow> ?f'\<close>
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H apply assumption
    using pre ..
  then have \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f'\<close>
    apply (rule hfref_weaken_change_pre)
    subgoal
      unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
        twl_st_confl_extracted_assn_def hr_comp_assoc find_decomp_wl_pre_def
      by (auto simp: 1 intro!: ext)
    subgoal
      by auto
    done
  then have 3: \<open>(uncurry find_decomp_wl_imp'_code, uncurry find_decomp_wl)
    \<in> [?pre]\<^sub>a ?im \<rightarrow>
      hr_comp twl_st_confl_extracted_int_assn
         ((Id \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r option_lookup_clause_rel_with_cls_with_highest M \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O
          {(S', S). (S', S) \<in> twl_st_heur_no_clvls \<and>
             (\<forall>L\<in>#remove1_mset (- lit_of (hd M)) (the (get_conflict_wl S)).
               get_level (get_trail_wl S) L = get_level M L)})\<close>
    (is \<open>?c \<in> [_]\<^sub>a _ \<rightarrow> hr_comp _ ?ref\<close>)
    unfolding twl_st_confl_extracted_int_assn'_def hr_comp_Id2
      conflict_with_cls_with_cls_with_highest_assn_def
      twl_st_confl_extracted_assn_def
    apply (subst (asm) 2)
    unfolding twl_st_confl_extracted_int_assn_def[symmetric] hr_comp_assoc
    .
  have get_maximum_level_eq:
    \<open>\<forall>L\<in>#remove1_mset (- lit_of (hd M)) y. get_level bk L = get_level M L \<Longrightarrow>
       get_maximum_level M (remove1_mset (- lit_of (hd M)) y) =
       get_maximum_level bk (remove1_mset (- lit_of (hd M)) y)\<close> for bk y
    unfolding get_maximum_level_def by auto
  have incl: \<open>?ref
         \<subseteq> twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls\<close>
    unfolding twl_st_heur_confl_extracted2_twl_st_heur
    by (auto  simp: twl_st_heur_no_clvls_def option_lookup_clause_rel_with_cls_with_highest_def
        highest_lit_def L get_maximum_level_eq)

  show ?thesis
    unfolding twl_st_confl_extracted_assn2_def L
    apply (rule subsetD[OF hfref_imp_mono_result[OF incl, unfolded L]])
    apply (rule 3[unfolded L])
    done
qed

definition extract_shorter_conflict_wl_pre where
  \<open>extract_shorter_conflict_wl_pre S \<longleftrightarrow>
      twl_struct_invs (twl_st_of_wl None S) \<and>
            twl_stgy_invs (twl_st_of_wl None S) \<and>
            get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> no_skip S \<and> no_resolve S \<and>
            literals_are_\<L>\<^sub>i\<^sub>n S\<close>

lemma backtrack_wl_D_invD:
  assumes \<open>backtrack_wl_D_inv S\<close>
  shows \<open>get_trail_wl S \<noteq> []\<close> \<open>extract_shorter_conflict_wl_pre S\<close>
  using assms unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
  extract_shorter_conflict_wl_pre_def get_trail_l_st_l_of_wl
  apply (cases S; auto)
  using assms literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of S]
  unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
  extract_shorter_conflict_wl_pre_def get_trail_l_st_l_of_wl get_conflict_l_st_l_of_wl
  no_skip_def no_resolve_def
  by (auto simp del: split_paired_All)


lemma (in -) backtrack_l_inv_alt_def:
  \<open>backtrack_l_inv (st_l_of_wl None S) \<longleftrightarrow> get_trail_wl S \<noteq> [] \<and>
      no_skip S \<and>
      no_resolve S \<and>
      get_conflict_wl S \<noteq> None \<and>
      twl_struct_invs (twl_st_of_wl2 None S) \<and>
      twl_stgy_invs (twl_st_of_wl2 None S) \<and>
      additional_WS_invs (st_l_of_wl None S) \<and>
      get_conflict_wl S \<noteq> Some {#}
  \<close>
  unfolding backtrack_l_inv_def no_skip_def no_resolve_def
  by (cases S) auto

lemma backtrack_wl_D_inv_find_decomp_wl_preD:
  assumes
    inv: \<open>backtrack_wl_D_inv x\<close> and
    ext_c: \<open>RETURN xc \<le> extract_shorter_conflict_wl x\<close>
  shows \<open>find_decomp_wl_pre (get_trail_wl x) (lit_of_hd_trail_st x, xc)\<close>
proof -
  obtain M N U D NP UP W Q where
    x: \<open>x = (M, N, U, D, NP, UP, W, Q)\<close> by (cases x)
  have
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, U, D, NP, UP, W, Q)\<close> and
    \<open>correct_watching (M, N, U, D, NP, UP, W, Q)\<close> and
    \<open>no_skip (M, N, U, D, NP, UP, W, Q)\<close> and
    nr: \<open>no_resolve (M, N, U, D, NP, UP, W, Q)\<close> and
    D: \<open>D \<noteq> None\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q))\<close> and
    \<open>twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q))\<close> and
    \<open>additional_WS_invs (st_l_of_wl None (M, N, U, D, NP, UP, W, Q))\<close> and
    \<open>D \<noteq> Some {#}\<close> and
    [simp]: \<open>M \<noteq> []\<close>
    using inv
    unfolding extract_shorter_conflict_wl_def find_decomp_wl_pre_def backtrack_wl_D_inv_def
      backtrack_wl_inv_def x backtrack_l_inv_alt_def
    by auto
  obtain D' where D': \<open>D = Some D'\<close>
    using D by auto
  obtain E where
     xc: \<open>xc = (M, N, U, Some E, NP, UP, W, Q)\<close> and
     E_D': \<open>E \<subseteq># D'\<close> and
     uL_E: \<open>- lit_of (hd M) \<in># E\<close>
    using ext_c unfolding x D' extract_shorter_conflict_wl_def by auto
  then have [simp]: \<open>E \<noteq> {#}\<close> by auto
  have
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close> and
    conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have uL_D: \<open>- lit_of (hd M) \<in># D'\<close>
    using uL_E E_D' by auto
  have max: \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the (Some D')))
      < backtrack_lvl (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close>
  proof (cases \<open>is_proped (hd M)\<close>)
    case True
    then obtain K C M' where
       M: \<open>M = Propagated K C # M'\<close>
      by (cases M; cases \<open>hd M\<close>) auto
    have [simp]: \<open>get_maximum_level (Propagated K F # convert_lits_l N M') =
        get_maximum_level (Propagated K C # M')\<close> for F
      apply (rule ext)
      apply (rule get_maximum_level_cong)
      by (auto simp: get_level_cons_if)
    have \<open>0 < C \<Longrightarrow> K \<in> set (N ! C)\<close>
      using conf unfolding M by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
    then show ?thesis
      using nr uL_D count_decided_ge_get_maximum_level[of M \<open>remove1_mset (- K) D'\<close>]
      unfolding no_resolve_def D' M
      by (fastforce simp:  cdcl\<^sub>W_restart_mset.resolve.simps elim!: convert_lit.elims)
  next
    case False
    then obtain K M' where
       M: \<open>M = Decided K # M'\<close>
      by (cases M; cases \<open>hd M\<close>) auto
    have tr: \<open>M \<Turnstile>as CNot D'\<close>
      using conf confl by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def D')
    have cons: \<open>consistent_interp (lits_of_l M)\<close>
      using lev  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto dest!: distinct_consistent_interp)
    have tauto: \<open>\<not> tautology D'\<close>
      using consistent_CNot_not_tautology[OF cons tr[unfolded true_annots_true_cls]] .
    moreover have \<open>distinct_mset D'\<close>
      using dist unfolding D' cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by auto
    ultimately have \<open>atm_of K \<notin> atms_of (remove1_mset (- K) D')\<close>
      using uL_D unfolding M
      by (auto simp: atms_of_def tautology_add_mset atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      unfolding M
      apply (subst get_maximum_level_skip_first)
      using count_decided_ge_get_maximum_level[of M' \<open>remove1_mset (- K) D'\<close>]
      by auto
  qed
  moreover have \<open>Decided K # M1 = convert_lits_l N a \<longleftrightarrow> (a \<noteq> [] \<and> is_decided (hd a) \<and>
     M1 = convert_lits_l N (tl a) \<and> hd a = Decided K)\<close> for K M1 a
    by(cases a; cases \<open>hd a\<close>)  auto
  ultimately have ex_decomp[simp]: \<open>ex_decomp_of_max_lvl M (Some D') (lit_of (hd M))\<close>
    using cdcl\<^sub>W_restart_mset.backtrack_ex_decomp[OF lev max]
    unfolding ex_decomp_of_max_lvl_def
    by (auto 5 5 simp: get_all_ann_decomposition_convert_lits_l
        elim!: neq_NilE convert_lit.elims)
  show ?thesis
    unfolding extract_shorter_conflict_wl_def find_decomp_wl_pre_def backtrack_wl_D_inv_def
      backtrack_wl_inv_def backtrack_l_inv_alt_def
    using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct]
      literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits _ struct]
      uL_E E_D' struct
    unfolding x D' xc
    by (auto 5 5 simp: extract_shorter_conflict_wl_def backtrack_wl_D_inv_def backtrack_wl_inv_def
        backtrack_l_inv_alt_def lit_of_hd_trail_st_def no_skip_def[symmetric]
        intro: exI[of _ \<open>Some D'\<close>])
qed

definition size_conflict_wl where
  \<open>size_conflict_wl S = size (the (get_conflict_wl S))\<close>

sepref_thm size_conflict_wl_code
  is \<open>RETURN o size_conflict_wl_heur\<close>
  :: \<open>twl_st_confl_extracted_int_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_conflict_wl_heur_def twl_st_confl_extracted_int_assn_def
  by sepref

concrete_definition (in -) size_conflict_wl_code
   uses isasat_input_bounded_nempty.size_conflict_wl_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_wl_code_def

lemmas size_conflict_wl_code_hnr[sepref_fr_rules] =
   size_conflict_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma size_conflict_wl_heur_size_conflict_wl:
  \<open>(RETURN o size_conflict_wl_heur, RETURN o size_conflict_wl) \<in>
   [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>f twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<rightarrow>
    \<langle>nat_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_wl_heur_def size_conflict_wl_def
      twl_st_heur_confl_extracted2_twl_st_heur size_lookup_conflict_def
      option_lookup_clause_rel_with_cls_with_highest2_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

theorem size_conflict_wl_hnr[sepref_fr_rules]:
  \<open>(size_conflict_wl_code, RETURN o size_conflict_wl)
    \<in> [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>a
      (twl_st_confl_extracted_assn2 L)\<^sup>k  \<rightarrow> uint32_nat_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls)
     (\<lambda>S. get_conflict_wl S \<noteq> None) (\<lambda>_ _. True)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_confl_extracted_int_assn\<^sup>k)
                    (twl_st_heur_confl_extracted2 L O
                     twl_st_heur_no_clvls) \<rightarrow> hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF size_conflict_wl_code_hnr
    size_conflict_wl_heur_size_conflict_wl] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_confl_extracted_assn2_def ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma backtrack_get_conglit_wl_not_NoneD:
  \<open>RETURN xc \<le> extract_shorter_conflict_wl x \<Longrightarrow>
   RETURN xd \<le> find_decomp_wl (lit_of_hd_trail_st x) xc \<Longrightarrow>
   \<exists>y. get_conflict_wl xd = Some y\<close>
  by (cases xd; cases xc; cases x)
     (auto simp: find_decomp_wl_def extract_shorter_conflict_wl_def)

definition get_snd_highest_lit :: \<open>lookup_clause_rel_with_cls_with_highest \<Rightarrow> nat literal\<close> where
  \<open>get_snd_highest_lit = (\<lambda>((_, _, _), L). fst (the L))\<close>

definition find_lit_of_max_level_wl_int :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> nat literal \<Rightarrow> nat literal\<close> where
  \<open>find_lit_of_max_level_wl_int = (\<lambda>(M, N, U, D, _, _, _, _) _. get_snd_highest_lit D)\<close>

lemma get_snd_highest_lit[sepref_fr_rules]:
   \<open>(return o (\<lambda>((_, _, _), L). (fst (the L))), RETURN o get_snd_highest_lit) \<in>
    [\<lambda>S. snd S \<noteq> None]\<^sub>a (conflict_option_rel_assn *a
         option_assn (unat_lit_assn *a uint32_nat_assn))\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding get_snd_highest_lit_def
  apply sep_auto
  apply sepref_to_hoare
  subgoal for x xi
    apply (cases x; cases xi; cases \<open>snd x\<close>; cases \<open>snd xi\<close>)
    apply sep_auto+
    done
  done

sepref_thm find_lit_of_max_level_wl_code
  is \<open>uncurry (RETURN oo find_lit_of_max_level_wl_int)\<close>
  :: \<open>[\<lambda>((M, N, U, (_, L), _), _). L \<noteq> None]\<^sub>a  twl_st_confl_extracted_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
           unat_lit_assn\<close>
  unfolding find_lit_of_max_level_wl_int_def twl_st_confl_extracted_int_assn_def
  by sepref

concrete_definition (in -) find_lit_of_max_level_wl_code
   uses isasat_input_bounded_nempty.find_lit_of_max_level_wl_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) find_lit_of_max_level_wl_code_def

lemmas find_lit_of_max_level_wl_code_hnr[sepref_fr_rules] =
   find_lit_of_max_level_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma find_lit_of_max_level_wl_int_find_lit_of_max_level_wl:
  \<open>(uncurry (RETURN oo find_lit_of_max_level_wl_int), uncurry find_lit_of_max_level_wl) \<in>
    [\<lambda>(S, L'). L' = -L \<and> get_conflict_wl S \<noteq> None \<and> size (the (get_conflict_wl S)) > 1]\<^sub>f
     twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<times>\<^sub>r nat_lit_lit_rel \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: find_lit_of_max_level_wl_int_def find_lit_of_max_level_wl_def
      twl_st_heur_confl_extracted2_twl_st_heur get_snd_highest_lit_def
      option_lookup_clause_rel_with_cls_with_highest2_def highest_lit_def
      remove1_mset_empty_iff)

theorem find_lit_of_max_level_wl_hnr[sepref_fr_rules]:
  \<open>(uncurry find_lit_of_max_level_wl_code, uncurry find_lit_of_max_level_wl)
    \<in> [\<lambda>(S, L'). L' = -L \<and> get_conflict_wl S \<noteq> None \<and> size (the (get_conflict_wl S)) > 1]\<^sub>a
      (twl_st_confl_extracted_assn2 L)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<times>\<^sub>f nat_lit_lit_rel)
     (\<lambda>(S, L'). L' = - L \<and> get_conflict_wl S \<noteq> None \<and> 1 < size (the (get_conflict_wl S)))
     (\<lambda>_ ((M, N, U, (_, L), _), _). L \<noteq> None)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_confl_extracted_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                    (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<times>\<^sub>f
                     nat_lit_lit_rel) \<rightarrow> hr_comp unat_lit_assn nat_lit_lit_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_lit_of_max_level_wl_code_hnr
    find_lit_of_max_level_wl_int_find_lit_of_max_level_wl] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def highest_lit_def remove1_mset_empty_iff
        twl_st_heur_confl_extracted2_def option_lookup_clause_rel_with_cls_with_highest2_def
        option_lookup_clause_rel_def lookup_clause_rel_def twl_st_heur_no_clvls_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_confl_extracted_assn2_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition list_of_mset2_None where
  \<open>list_of_mset2_None L L' D = SPEC(\<lambda>(E, F). mset E = the D \<and> E!0 = L \<and> E!1 = L' \<and>
     F = None \<and> length E \<ge> 2)\<close>

lemma propagate_bt_wl_D_alt_def:
  \<open>propagate_bt_wl_D = (\<lambda>L L' (M, N, U, D, NP, UP, Q, W).
    list_of_mset2_None (- L) L' D \<bind>
    (\<lambda>(D'', E). RETURN
             (Propagated (- L) (length N) # M, N @ [D''], U, E, NP, UP, {#L#},
              W(- L := W (- L) @ [length N], L' := W L' @ [length N]))))\<close>
  unfolding propagate_bt_wl_D_def list_of_mset2_def list_of_mset2_None_def
  by (auto simp: RES_RETURN_RES RES_RETURN_RES2 uncurry_def intro!: ext)


lemma extract_shorter_conflict_l_trivial_int_extract_shorter_conflict_l_trivial:
  \<open>(extract_shorter_conflict_st_trivial_heur, extract_shorter_conflict_st_trivial) \<in>
    [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur_no_clvls\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: extract_shorter_conflict_st_trivial_heur_def twl_st_heur_no_clvls_def
        extract_shorter_conflict_st_trivial_def twl_st_heur_def RETURN_def
     intro!: RES_refine)


type_synonym (in -) lookup_clause_rel_with_cls = \<open>nat clause_l \<times> bool option list\<close>
type_synonym (in -) conflict_with_cls_assn = \<open>uint32 array \<times> bool option array\<close>

type_synonym twl_st_wll_confl_with_cls =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn\<close>

definition option_lookup_clause_rel_with_cls_removed
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> (lookup_clause_rel_with_cls \<times> nat clause option) set\<close>
where
  \<open>option_lookup_clause_rel_with_cls_removed L L' = {((C, xs), D). D \<noteq> None \<and> (drop 2 C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs) \<and> C!0 = L \<and> C!1 = L' \<and> length C \<ge> 2}\<close>


definition option_lookup_clause_rel_with_cls
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> (lookup_clause_rel_with_cls \<times> nat clause option) set\<close>
where
  \<open>option_lookup_clause_rel_with_cls L L' = {((C, xs), D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs) \<and> C!0 = L \<and> C!1 = L' \<and> length C \<ge> 2}\<close>

definition option_lookup_clause_rel_with_cls_removed1 :: \<open>(nat clause_l \<times> nat clause option) set\<close> where
  \<open>option_lookup_clause_rel_with_cls_removed1 = {(C, D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel}\<close>

abbreviation (in -) conflict_with_cls_int_assn :: \<open>lookup_clause_rel_with_cls \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_assn \<equiv>
    (array_assn unat_lit_assn *a array_assn (option_assn bool_assn))\<close>

definition conflict_with_cls_assn_removed
 :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause option \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_with_cls_assn_removed L L' \<equiv>
   hr_comp conflict_with_cls_int_assn (option_lookup_clause_rel_with_cls_removed L L')\<close>

definition conflict_with_cls_assn :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause option \<Rightarrow>
   conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_assn L L' \<equiv> hr_comp conflict_with_cls_int_assn (option_lookup_clause_rel_with_cls L L')\<close>

definition option_lookup_clause_rel_removed :: \<open>_ set\<close> where
  \<open>option_lookup_clause_rel_removed =
   {((b, n, xs), C). C \<noteq> None \<and> n \<ge> 2 \<and> n \<le> length xs \<and>
      ((b, n - 2, xs), C) \<in> option_lookup_clause_rel}\<close>


type_synonym (in -) twl_st_wl_heur_W_confl_with_cls =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    lookup_clause_rel_with_cls \<times> nat clause \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

text \<open>
  \<^item> We are filling D starting from the end (index \<^term>\<open>n\<close>)
  \<^item> We are changing position one and two.
\<close>
definition conflict_to_conflict_with_cls
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat literal list \<Rightarrow> conflict_option_rel \<Rightarrow> (nat literal list \<times> conflict_option_rel) nres\<close>
where
  \<open>conflict_to_conflict_with_cls = (\<lambda>_ _ D (_, n, xs). do {
     (_, _, C, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, m, C, zs). i \<le> length zs \<and> length zs = length xs \<and>
          length C = n \<and> m \<le> length C \<and> C!0 = D!0 \<and> C!1 = D!1\<^esup>
       (\<lambda>(i, m, C, zs). m > 2)
       (\<lambda>(i, m, C, zs). do {
           ASSERT(i < length xs);
           ASSERT(i \<le> uint_max div 2);
           ASSERT(m > 2);
           ASSERT(zs ! i \<noteq> None \<longrightarrow> Pos i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
           case zs ! i of
             None \<Rightarrow> RETURN (i+1, m, C, zs)
           | Some b \<Rightarrow> RETURN (i+1, m-1, C[m-1 := (if b then Pos i else Neg i)], zs[i := None])
       })
       (0, n, D, xs);
     RETURN (C, (True, zero_uint32_nat, zs))
  }
  )\<close>

definition conflict_to_conflict_with_cls_spec where
  \<open>conflict_to_conflict_with_cls_spec _ D = D\<close>

definition list_of_mset2_None_droped where
  \<open>list_of_mset2_None_droped L L' _ D = SPEC(\<lambda>(E, F). mset (drop 2 E) = the D \<and> E!0 = L \<and> E!1 = L' \<and>
     F = None \<and> length E \<ge> 2)\<close>

lemma (in -) bind_rule_complete_RES: \<open>(M \<bind> f \<le> RES \<Phi>) = (M \<le> SPEC (\<lambda>x. f x \<le> RES \<Phi>))\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

lemma WHILEIT_rule_stronger_inv_RES:
  assumes
    \<open>wf R\<close> and
    \<open>I s\<close> and
    \<open>I' s\<close>
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> and
   \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> \<not> b s \<Longrightarrow> s \<in> \<Phi>\<close>
 shows \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> RES \<Phi>\<close>
proof -
  have RES_SPEC: \<open>RES \<Phi> = SPEC(\<lambda>s. s \<in> \<Phi>)\<close>
    by auto
  have \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s\<close>
    by (metis (mono_tags, lifting) WHILEIT_weaken)
  also have \<open>WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s \<le> RES \<Phi>\<close>
    unfolding RES_SPEC
    by (rule WHILEIT_rule) (use assms in \<open>auto simp: \<close>)
  finally show ?thesis .
qed

lemma conflict_to_conflict_with_cls_id:
  \<open>(uncurry3 conflict_to_conflict_with_cls, uncurry3 list_of_mset2_None_droped) \<in>
    [\<lambda>(((L, L'),D), C). C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> length D = size (the C) + 2 \<and>
      L = D!0 \<and> L' = D!1]\<^sub>f
      Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel_removed  \<rightarrow>
       \<langle>Id \<times>\<^sub>f option_lookup_clause_rel\<rangle> nres_rel\<close>
   (is \<open>_ \<in> [_]\<^sub>f _ \<rightarrow> \<langle>?R\<rangle>nres_rel\<close>)
proof -
  have H: \<open>conflict_to_conflict_with_cls L L' D (b, n, xs) \<le> \<Down> ?R (list_of_mset2_None_droped L L' D (Some C))\<close>
    if
      ocr: \<open>((b, n, xs), Some C) \<in> option_lookup_clause_rel_removed\<close> and
      lits_\<A>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
      len_D: \<open>length D = size C + 2\<close> and
      [simp]: \<open>D!0 = L\<close>\<open>D!Suc 0 = L'\<close>
    for b n xs C D L L'
  proof -
    define I' where
      [simp]: \<open>I' = (\<lambda>(i, m, D, zs).
              ((b, m, zs), Some (filter_mset (\<lambda>L. atm_of L \<ge> i) C)) \<in> option_lookup_clause_rel_removed \<and>
               m - 2 = length (filter (op \<noteq> None) zs) \<and>
               i + (m - 2) + length (filter (op = None) (drop i zs)) = length zs \<and> (\<forall>k < i. zs ! k = None) \<and>
               mset (drop m D) = filter_mset (\<lambda>L. atm_of L < i) C \<and>
               length D \<ge> 2 \<and>
               m \<ge> 2)\<close>
    let ?I' = I'
    let ?C = \<open>C\<close>
    let ?I = \<open>\<lambda>xs n (i, m, E, zs). i \<le> length zs \<and> length zs = length xs \<and> length E = n \<and>
          m \<le> length E \<and> E!0 = D!0 \<and> E!1 = D!1\<close>
    let ?cond = \<open>\<lambda>s. case s of (i, m, C, zs) \<Rightarrow> 2 < m\<close>
    have n_le: \<open>n \<le> length xs\<close> and b: \<open>b = False\<close> and
       dist_C: \<open>distinct_mset C\<close> and
       tauto_C: \<open>\<not> tautology C\<close> and
       atms_le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close> and
       n_size: \<open>n = 2 + size C\<close> and
       map: \<open>mset_as_position xs C\<close>
      using mset_as_position_length_not_None[of xs ?C] that  mset_as_position_distinct_mset[of xs ?C]
        mset_as_position_tautology[of xs ?C] len_D
      by (auto simp: option_lookup_clause_rel_def option_lookup_clause_rel_removed_def lookup_clause_rel_def
          tautology_add_mset)
    have size_C: \<open>size C \<le> 1 + uint_max div 2\<close>
      using simple_clss_size_upper_div2[OF lits_\<A>\<^sub>i\<^sub>n dist_C tauto_C] .

    have final: "\<not> (case s of (i, m, C, zs) \<Rightarrow> 2 < m) \<Longrightarrow>
    s \<in> {x. (case x of (_, _, C, zs) \<Rightarrow> RETURN (C, True, zero_uint32_nat, zs))
              \<le> RES ((Id \<times>\<^sub>f option_lookup_clause_rel)\<inverse> ``
                      {(E, F).
                       mset (drop 2 E) = the (Some C) \<and>
                       E ! 0 = L \<and> E ! 1 = L' \<and> F = None \<and> 2 \<le> length E})}"
      if
        s0: "?I baa aa s" and
        s1: "?I' s" and
        s:
          "\<not> ?cond s"
(*           "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)" *)
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
      for a ba aa baa s (* ab bb ac bc ad bd *)
    proof -
      obtain ab bb ac bc ad bd where
        s': "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
        by (cases s) auto
      then have [simp]: \<open>ac = 2\<close> \<open>s = (ab, 2, ad, bd)\<close> \<open>bb = (2, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close>
        \<open>n = aa\<close>\<open>xs = baa\<close>
        using s s1 by auto
      have \<open>((b, 2, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close> and
         le_ad: \<open>length ad \<ge> 2\<close>
        using s1 by auto
      then have [simp]: \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close> and map': \<open>mset_as_position bd {#}\<close>
        unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def by auto
      have [simp]: \<open>length bd = length xs\<close>
        using s0 by auto
      have [iff]: \<open>\<not>x < ab \<longleftrightarrow> ab \<le> x\<close> for x
        by auto
      have \<open>{#L \<in># C. atm_of L < ab#} = C\<close>
        using multiset_partition[of C \<open>\<lambda>L. atm_of L < ab\<close>] by auto
      then have [simp]: \<open>mset (drop 2 ad) = C\<close>
        using s1 by auto
      have [simp]: \<open>ad ! 0 = L\<close> \<open>ad ! Suc 0 = L'\<close>
        using s0 unfolding s by auto
      show ?thesis
        using map' atms_le_xs le_ad by (auto simp: option_lookup_clause_rel_with_cls_removed_def
            list_mset_rel_def br_def Image_iff option_lookup_clause_rel_def lookup_clause_rel_def)
    qed
    have init: "I' (0, aa, D, baa)"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)"
      for a ba aa baa
      using ocr that n_le n_size size_C len_D mset_as_position_length_not_None[OF map]
      sum_length_filter_compl[of \<open>op = None\<close> xs]
      by auto

    have in_\<L>\<^sub>a\<^sub>l\<^sub>l: "Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        cond: "?cond s" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_baa: "ab < length baa" and
        bd_ab: "bd ! ab \<noteq> None"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close>
        using b unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def
        by auto
      have \<open>ab < length bd\<close>
        using I I' cond s unfolding I' by auto
      then have ab_in_C: \<open>Pos ab \<in># C \<or> Neg ab \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_\<A>\<^sub>i\<^sub>n by auto
      then show ?thesis
        using lits_\<A>\<^sub>i\<^sub>n
        by (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    qed
    have le_uint_max_div2: "ab \<le> uint_max div 2"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)" and
        "?I baa aa s" and
        I': "I' s" and
        m: "?cond s" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)" and
        "ab < length baa"
      for a ba aa baa s ab bb ac bc ad bd
    proof (rule ccontr)
      assume le: \<open>\<not> ?thesis\<close>
      have \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using I' s unfolding I'_def by auto
      have \<open>L \<in># C \<Longrightarrow> atm_of L \<le> uint_max div 2\<close> for L
        using lits_\<A>\<^sub>i\<^sub>n in_N1_less_than_uint_max
        by (cases L)  (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset uint_max_def)
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close>
        using le by (force simp: filter_mset_empty_conv)
      then show False
        using m s ocr unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def by auto
    qed
    have IH_I': "I' (ab + 1, ac, ad, bd)"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        m: "?cond s" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_le: "ab < length baa" and
        "ab \<le> uint_max div 2" and
        "2 < ac" and
        "bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        bd_ab: "bd ! ab = None"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have [simp]: \<open>s = (ab, ac, ad, bd)\<close> \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close>
        \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa \<close> \<open>length bd = length baa\<close>
        using s I by auto
      have
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close> and
        eq: \<open>ab + length (filter (op \<noteq> None) bd) + length (filter (op = None) (drop ab bd)) = length baa\<close> and
        le_ab_None: \<open>\<forall>k<ab. bd ! k = None\<close> and
        ac: \<open>ac - 2 = length (filter (op \<noteq> None) bd)\<close> and
        ac2: \<open>ac \<ge> 2\<close> and
        le_ad: \<open>length ad \<ge> 2\<close>
        using I' unfolding I'_def by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close>
        using b unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>Pos ab \<notin># C\<close> \<open>Neg ab \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_\<A>\<^sub>i\<^sub>n by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        unfolding less_Suc_eq_le unfolding le_eq_less_or_eq
        using ab_in_C dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      then have mset_drop: \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using I' by auto

      have \<open>x \<in>#C \<Longrightarrow> atm_of x \<noteq> ab\<close> for x
        using bd_ab ocr
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> x]
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> \<open>-x\<close>]
        unfolding option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
        by force
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using s by (force intro!: filter_mset_cong2)
      then have ocr': \<open>((b, ac, bd), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using I' s by auto

      have
        x1a: \<open>ac - 2 = size {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>ac \<ge> 2\<close> and
        map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close>
        using ocr unfolding option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
        by auto

      have [iff]: \<open>ab + length (filter (op \<noteq> None) x2b) = length x2b \<longleftrightarrow> ab = length (filter (op = None) x2b)\<close> for x2b
        using sum_length_filter_compl[of \<open>op \<noteq> None\<close> x2b] by auto
      have filter_take_ab: \<open>filter (op = None) (take ab bd) = take ab bd\<close>
        apply (rule filter_id_conv[THEN iffD2])
        using le_ab_None by (auto simp: nth_append take_set split: if_splits)
      have Suc_le_bd: \<open>Suc ab + length (filter (op \<noteq> None) bd) + length (filter (op = None) (drop (Suc ab )bd)) =
          length baa\<close>
        using b ac Cons_nth_drop_Suc[of ab bd, symmetric] ab_le eq bd_ab by auto
      have le_Suc_None: \<open>k < Suc ab \<Longrightarrow> bd ! k = None\<close> for k
        using le_ab_None bd_ab  by (auto simp: less_Suc_eq)

      show ?thesis using le_ad mset_drop ocr' Suc_le_bd le_Suc_None ac ac2 unfolding I'_def by auto
    qed
    have IH_I'_notin: "I' (ab + 1, ac - 1, ad[ac - 1 := if x then Pos ab else Neg ab],
          bd[ab := None])"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        m: "?cond s" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_le: "ab < length baa" and
        "ab \<le> uint_max div 2" and
        "2 < ac" and
        "bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        bd_ab_x: "bd ! ab = Some x"
      for a ba aa baa s ab bb ac bc ad bd x
    proof -
      have [simp]: \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa\<close>
        \<open>s = (ab, (ac, (ad, bd)))\<close>
        \<open>length baa = length bd\<close>
        using I s by auto
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close> and
        ac: \<open>ac - 2 = length (filter (op \<noteq> None) bd)\<close> and
        eq: \<open>ab + (ac - 2) + length (filter (op = None) (drop ab bd)) = length bd\<close> and
        ac2: \<open>ac \<ge> 2\<close> and
        le_ad: \<open>length ad \<ge> 2\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using b unfolding option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
        by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>(if x then Pos ab else Neg ab) \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab_x lits_\<A>\<^sub>i\<^sub>n by auto
      have \<open>distinct_mset {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>\<not> tautology {#L \<in># C. ab \<le> atm_of L#}\<close>
        using mset_as_position_distinct_mset[OF map] mset_as_position_tautology[OF map] by fast+
      have [iff]: \<open>\<not> ab < atm_of a \<and> ab = atm_of a \<longleftrightarrow>  (ab = atm_of a)\<close> for a :: \<open>nat literal\<close> and ab
        by auto
      have H1: \<open>{#L \<in># C.  ab \<le> atm_of L#} = (if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv)
      have H2: \<open>{#L \<in># C. Suc ab \<le> atm_of L#} = remove1_mset (Pos ab) (remove1_mset (Neg ab) {#L \<in># C. ab \<le> atm_of L#})\<close>
        by (auto simp: H1)
      have map': \<open>mset_as_position (bd[ab := None]) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        unfolding H2
        apply (rule mset_as_position_remove)
        using map ab_le by auto
      have c_r: \<open>((b, ac - Suc 0, bd[ab := None]), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using ocr b map' m ac by (cases x) (auto simp: option_lookup_clause_rel_removed_def
            option_lookup_clause_rel_def lookup_clause_rel_def H1)
      have H3: \<open>(if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      have ac_ge0: \<open>ac > 0\<close>
        using m by auto
      then have \<open>ac - Suc 0 < length ad\<close> and \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close>
        using I' I m by auto
      then have 3: \<open>mset (drop (ac - Suc 0) (ad[ac - Suc 0 := (if x then Pos ab else Neg ab)])) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using Cons_nth_drop_Suc[symmetric, of \<open>ac - 1\<close> \<open>ad\<close>] ac_ge0
        by (auto simp: drop_update_swap H3[symmetric])
      have ac_filter: \<open>ac - Suc (Suc (Suc 0)) = length (filter (op \<noteq> None) (bd[ab := None]))\<close>
        apply (subst length_filter_update_true)
        using ac bd_ab_x ab_le by auto
      have \<open>length (filter (op \<noteq> None) bd) \<ge> Suc 0\<close>
        using bd_ab_x ab_le nth_mem by (fastforce simp: filter_empty_conv)
      then have eq': \<open>Suc ab + length (filter (op \<noteq> None) (bd[ab := None])) + length (filter (op = None) (drop (Suc ab) bd)) = length bd\<close>
        using b ac Cons_nth_drop_Suc[of ab bd, symmetric] ab_le eq bd_ab_x ac2
        by (auto simp: length_filter_update_true)
      show ?thesis
        using b c_r that s ac_filter 3 eq' le_ad unfolding I'_def by auto
    qed
    show ?thesis
      supply WHILEIT_rule[refine_vcg del]
      unfolding conflict_to_conflict_with_cls_def Let_def list_of_mset2_None_droped_def conc_fun_RES
      apply refine_rcg
      unfolding bind_rule_complete_RES
      apply (refine_vcg WHILEIT_rule_stronger_inv_RES[where
            R = \<open>measure (\<lambda>(i :: nat, m :: nat, D :: nat clause_l, zs :: bool option list). length zs - i)\<close> and
            I' = \<open>I'\<close>] bind_rule_complete_RES)
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal using len_D n_size by auto
      subgoal using len_D n_size by auto
      subgoal by simp
      subgoal by simp
      subgoal by (rule init)
      subgoal using n_le by auto
      subgoal by (rule le_uint_max_div2)
      subgoal by auto
      subgoal by (rule in_\<L>\<^sub>a\<^sub>l\<^sub>l) assumption+
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I')
      subgoal by auto
      subgoal using b by (auto simp: less_Suc_eq)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I'_notin)
      subgoal by auto
      subgoal by (rule final) assumption+
      done
    qed

  show ?thesis
    apply (intro frefI nres_relI)
    apply clarify
    subgoal for a aa ab b ac ba y
      using H by (auto simp: conflict_to_conflict_with_cls_spec_def)
    done
qed


lemma conflict_to_conflict_with_cls_code_helper:
  \<open>a1'b \<le> uint_max div 2 \<Longrightarrow> Suc a1'b \<le> uint_max\<close>
  \<open> 0 < a1'c \<Longrightarrow> one_uint32_nat \<le> a1'c\<close>
  \<open>fast_minus a1'c one_uint32_nat  = a1'c - 1\<close>
  by (auto simp: uint_max_def)

sepref_register conflict_to_conflict_with_cls
sepref_thm conflict_to_conflict_with_cls_code
  is \<open>uncurry3 (PR_CONST conflict_to_conflict_with_cls)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a(array_assn unat_lit_assn)\<^sup>d *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a
      array_assn unat_lit_assn *a conflict_option_rel_assn\<close>
  supply uint32_nat_assn_zero_uint32_nat[sepref_fr_rules] [[goals_limit=1]]
   Pos_unat_lit_assn'[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
   conflict_to_conflict_with_cls_code_helper[simp] uint32_2_hnr[sepref_fr_rules]
  unfolding conflict_to_conflict_with_cls_def array_fold_custom_replicate
    fast_minus_def[of \<open>_ :: nat\<close>, symmetric] PR_CONST_def
  apply (rewrite at "\<hole> < length _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at "_ ! \<hole> \<noteq> None" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at "\<hole> < _" two_uint32_nat_def[symmetric])
  apply (rewrite at "\<hole> < _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>(\<hole>, _, _, _)\<close> zero_uint32_nat_def[symmetric])
  apply (rewrite at "(zero_uint32_nat, \<hole>, _, _)" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>_ + \<hole>\<close> one_uint32_nat_def[symmetric])+
  apply (rewrite at \<open>fast_minus _ \<hole>\<close> one_uint32_nat_def[symmetric])+
  by sepref

concrete_definition (in -) conflict_to_conflict_with_cls_code
   uses isasat_input_bounded_nempty.conflict_to_conflict_with_cls_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_to_conflict_with_cls_code_def

lemmas conflict_to_conflict_with_cls_code_refine[sepref_fr_rules] =
   conflict_to_conflict_with_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma extract_shorter_conflict_with_cls_code_conflict_to_conflict_with_cls_spec[sepref_fr_rules]:
  \<open>(uncurry3 conflict_to_conflict_with_cls_code, uncurry3 list_of_mset2_None_droped)
    \<in> [\<lambda>(((L, L'), D), C). C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and>
           length D = size (the C) + 2 \<and> L = D ! 0 \<and> L' = D ! 1]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a
     (hr_comp conflict_option_rel_assn option_lookup_clause_rel_removed)\<^sup>d \<rightarrow>
     clause_ll_assn *a option_lookup_clause_assn\<close>
  using conflict_to_conflict_with_cls_code_refine[unfolded PR_CONST_def,
    FCOMP conflict_to_conflict_with_cls_id]
  unfolding option_lookup_clause_assn_def
  by simp

definition remove2_from_conflict :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat cconflict \<Rightarrow> nat cconflict\<close> where
  \<open>remove2_from_conflict L L' C = Some (remove1_mset L (remove1_mset L' (the C)))\<close>

definition remove2_from_conflict_int
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> conflict_option_rel \<Rightarrow> conflict_option_rel\<close>
where
  \<open>remove2_from_conflict_int L L' = (\<lambda>(b, n, xs). (b, n, xs[atm_of L := None, atm_of L' := None]))\<close>

lemma remove2_from_conflict_int_remove2_from_conflict:
  \<open>(uncurry2 (RETURN ooo remove2_from_conflict_int), uncurry2 (RETURN ooo remove2_from_conflict)) \<in>
   [\<lambda>((L, L'), C). L \<in># the C \<and> L' \<in># the C \<and> C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L']\<^sub>f
    Id \<times>\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel \<rightarrow> \<langle>option_lookup_clause_rel_removed\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for K K' b n xs L L' bc C
    using mset_as_position_length_not_None[of xs C] mset_as_position_tautology[of xs C]
      mset_as_position_remove[of xs C \<open>atm_of L\<close>]
      mset_as_position_remove[of \<open>xs[atm_of L := None]\<close> \<open>remove1_mset L C\<close> \<open>atm_of L'\<close>]
    apply (cases L; cases L')
    by (auto simp: remove2_from_conflict_int_def remove2_from_conflict_def
      option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
      add_mset_eq_add_mset tautology_add_mset
      dest!: multi_member_split)
  done

sepref_thm remove2_from_conflict_code
  is \<open>uncurry2 (RETURN ooo remove2_from_conflict_int)\<close>
  :: \<open>[\<lambda>((L, L'), (b, n, xs)). atm_of L < length xs \<and> atm_of L' < length xs]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn\<close>
  unfolding remove2_from_conflict_int_def
  by sepref

concrete_definition (in -) remove2_from_conflict_code
   uses isasat_input_bounded_nempty.remove2_from_conflict_code.refine_raw
   is \<open>(uncurry2 ?f, _)\<in>_\<close>

prepare_code_thms (in -) remove2_from_conflict_code_def

lemmas remove2_from_conflict_code_hnr[sepref_fr_rules] =
   remove2_from_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem remove2_from_conflict_hnr[sepref_fr_rules]:
  \<open>(uncurry2 remove2_from_conflict_code, uncurry2 (RETURN ooo remove2_from_conflict))
    \<in> [\<lambda>((L, L'), C). L \<in># the C \<and> L' \<in># the C \<and> C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L']\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow>
      hr_comp conflict_option_rel_assn option_lookup_clause_rel_removed\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
          (\<lambda>((L, L'), C).
              L \<in># the C \<and>
              L' \<in># the C \<and>
              C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L')
          (\<lambda>_ ((L, L'), b, n, xs).
              atm_of L < length xs \<and> atm_of L' < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel) \<rightarrow>
      hr_comp conflict_option_rel_assn option_lookup_clause_rel_removed\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF remove2_from_conflict_code_hnr
    remove2_from_conflict_int_remove2_from_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def option_lookup_clause_rel_def
        lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    using pre ..
qed

definition list_of_mset2_None_int where
  \<open>list_of_mset2_None_int L L' C\<^sub>0 =  do {
     let n = size (the C\<^sub>0);
     ASSERT(n \<ge> 2);
     let D = replicate n L;
     let D = D[1 := L'];
     let C = remove2_from_conflict L L' C\<^sub>0;
     ASSERT(C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> size (the C\<^sub>0) = size (the C) + 2 \<and>
       D!0 = L \<and> D!1 = L');
(*      let D = ASSN_ANNOT (conflict_with_cls_assn_removed L L') (conflict_to_conflict_with_cls_spec D C); *)
(*      ASSERT(D \<noteq> None \<and> L \<notin># the D \<and> L' \<notin># the D); *)
(*      let D = add2_from_conflict L L' D;
     ASSERT(D \<noteq> None); *)
     list_of_mset2_None_droped L L' D C}\<close>

lemma (in -) list_length2E:
  \<open>length xs \<ge> 2 \<Longrightarrow> (\<And>x y zs. xs = x # y # zs \<Longrightarrow> zs = tl (tl xs) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases xs; cases \<open>tl xs\<close>) auto

lemma list_of_mset2_None_int_list_of_mset2_None:
  \<open>(uncurry2 (list_of_mset2_None_int), uncurry2 list_of_mset2_None) \<in>
     [\<lambda>((L, L'), C). C \<noteq> None \<and> L \<in># the C \<and> L' \<in># the C \<and> L \<noteq> L' \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> distinct_mset (the C)]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: list_of_mset2_None_int_def list_of_mset2_None_def
      list_of_mset2_def conflict_to_conflict_with_cls_spec_def
      remove2_from_conflict_def add_mset_eq_add_mset RES_RETURN_RES
      literals_are_in_\<L>\<^sub>i\<^sub>n_sub literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset list_of_mset2_None_droped_def
      dest!: multi_member_split
      elim!: list_length2E)

definition size_conflict :: \<open>nat clause option \<Rightarrow> nat\<close> where
  \<open>size_conflict D = size (the D)\<close>

definition size_conflict_int :: \<open>conflict_option_rel \<Rightarrow> nat\<close> where
  \<open>size_conflict_int = (\<lambda>(_, n, _). n)\<close>

lemma size_conflict_code_refine_raw:
  \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_conflict_int) \<in> conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: size_conflict_int_def)

concrete_definition (in -) size_conflict_code
   uses isasat_input_bounded_nempty.size_conflict_code_refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_code_def

lemmas size_conflict_code_hnr[sepref_fr_rules] =
   size_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma size_conflict_int_size_conflict:
  \<open>(RETURN o size_conflict_int, RETURN o size_conflict) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<rightarrow>
     \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_int_def size_conflict_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

lemma size_conflict_hnr[sepref_fr_rules]:
  \<open>(size_conflict_code, RETURN \<circ> size_conflict) \<in> [\<lambda>x. x \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using size_conflict_code_hnr[FCOMP size_conflict_int_size_conflict]
  unfolding option_lookup_clause_assn_def[symmetric]
  by simp

lemma two_different_multiset_sizeD:
  assumes \<open>a \<in># y\<close> and \<open>ba \<in># y\<close> \<open>a \<noteq> ba\<close>
  shows \<open>Suc 0 < size y\<close> \<open>size y = Suc (Suc (size (y - {#a, ba#})))\<close>
  using assms by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
sepref_thm list_of_mset2_None_code
  is \<open>uncurry2 (PR_CONST list_of_mset2_None_int)\<close>
  :: \<open>[\<lambda>((L, L'), C). C \<noteq> None \<and> L \<in># the C \<and> L' \<in># the C \<and> L \<noteq> L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the C)]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         option_lookup_clause_assn\<^sup>d \<rightarrow> clause_ll_assn *a option_lookup_clause_assn\<close>
  supply [[goals_limit=1]] size_conflict_def[simp]
  unfolding list_of_mset2_None_int_def size_conflict_def[symmetric]
    array_fold_custom_replicate PR_CONST_def
  by sepref

concrete_definition (in -) list_of_mset2_None_code
   uses isasat_input_bounded_nempty.list_of_mset2_None_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) list_of_mset2_None_code_def

lemmas list_of_mset2_None_int_hnr[sepref_fr_rules] =
  list_of_mset2_None_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma list_of_mset2_None_hnr[sepref_fr_rules]:
  \<open>(uncurry2 list_of_mset2_None_code, uncurry2 list_of_mset2_None)
   \<in> [\<lambda>((a, b), ba). ba \<noteq> None \<and> a \<in># the ba \<and> b \<in># the ba \<and> a \<noteq> b \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the ba) \<and> distinct_mset (the ba) \<and> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> b \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow>
      clause_ll_assn *a option_lookup_clause_assn\<close>
  using list_of_mset2_None_int_hnr[unfolded PR_CONST_def, FCOMP list_of_mset2_None_int_list_of_mset2_None]
  by simp

sepref_thm extract_shorter_conflict_list_removed_code
  is \<open>uncurry (PR_CONST extract_shorter_conflict_list_removed)\<close>
  :: \<open>[\<lambda>(M, (b, n, xs)). M \<noteq> []]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn *a
       option_assn (unat_lit_assn *a uint32_nat_assn)\<close>
  supply [[goals_limit = 1]] uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
    Pos_unat_lit_assn[sepref_fr_rules]
    Neg_unat_lit_assn[sepref_fr_rules]
  unfolding extract_shorter_conflict_list_removed_def PR_CONST_def
  extract_shorter_conflict_list_heur_def
  lit_of_hd_trail_def[symmetric] Let_def
  zero_uint32_nat_def[symmetric]
  fast_minus_def[symmetric] one_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_removed_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_removed_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_removed_code_def

lemmas extract_shorter_conflict_list_removed_code_extract_shorter_conflict_list_removed[sepref_fr_rules] =
  extract_shorter_conflict_list_removed_code.refine[of \<A>\<^sub>i\<^sub>n,
      OF isasat_input_bounded_nempty_axioms]

sepref_thm extract_shorter_conflict_l_trivial'
  is \<open>uncurry (PR_CONST extract_shorter_conflict_list_heur)\<close>
  :: \<open>[\<lambda>(M, (b, n, xs)). M \<noteq> []]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn *a
       option_assn (unat_lit_assn *a uint32_nat_assn)\<close>
  supply [[goals_limit = 1]]
  unfolding extract_shorter_conflict_list_def PR_CONST_def
  extract_shorter_conflict_list_heur_def
  lit_of_hd_trail_def[symmetric] Let_def one_uint32_nat_def[symmetric]
  fast_minus_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_l_trivial_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_l_trivial'.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_def

lemmas extract_shorter_conflict_l_trivial_code_wl_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code.refine[of \<A>\<^sub>i\<^sub>n,
      OF isasat_input_bounded_nempty_axioms]

text \<open>
  This is the \<^emph>\<open>direct\<close> composition of the refinement theorems. Only the version lifted to
  state should be used (to get rid of the \<^term>\<open>M\<close> that appears in the refinement relation).
\<close>
lemma extract_shorter_conflict_l_trivial_code_extract_shorter_conflict_l_trivial:
  \<open>(uncurry extract_shorter_conflict_l_trivial_code,
     uncurry (RETURN \<circ>\<circ> extract_shorter_conflict_l_trivial))
    \<in> [\<lambda>(M', D). M' \<noteq> [] \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M' = M \<and>
         -lit_of (hd M) \<in># the D \<and>  0 < get_level M (lit_of (hd M)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and>
         distinct_mset (the D) \<and> \<not>tautology (the D)]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> (conflict_with_cls_with_cls_with_highest_assn M)\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel)
       (\<lambda>(M, D). M \<noteq> [] \<and> D \<noteq> None \<and> - lit_of (hd M) \<in># the D \<and> 0 < get_level M (lit_of (hd M)))
       (\<lambda>_. comp_PRE (Id \<times>\<^sub>f option_lookup_clause_rel)
              (\<lambda>(M', D). literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M = M' \<and> M \<noteq> [] \<and>
                  literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> - lit_of (hd M) \<in># the D \<and>
                  lit_of (hd M) \<notin># the D \<and> distinct_mset (the D) \<and>
                  0 < get_level M (lit_of (hd M)) \<and> \<not> tautology (the D))
              (\<lambda>_ (M, b, n, xs). M \<noteq> [])
              (\<lambda>_. True))
       (\<lambda>_. True)]\<^sub>a
    hrp_comp (hrp_comp ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a (bool_assn *a lookup_clause_rel_assn)\<^sup>d)
                       (Id \<times>\<^sub>f option_lookup_clause_rel))
              (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel) \<rightarrow>
    hr_comp (hr_comp ((bool_assn *a lookup_clause_rel_assn) *a
                        option_assn (unat_lit_assn *a uint32_nat_assn))
                     {((D, L), C). (D, C) \<in> option_lookup_clause_rel \<and> C \<noteq> None \<and>
                      highest_lit M (remove1_mset (- lit_of (hd M)) (the C)) L \<and>
                       (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))})
             Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
       hfref_compI_PRE_aux[OF extract_shorter_conflict_l_trivial_code_wl_D[unfolded PR_CONST_def]
          extract_shorter_conflict_list_heur_extract_shorter_conflict_list, of M]
       extract_shorter_conflict_list_extract_shorter_conflict_l_trivial] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
    by (auto simp: comp_PRE_def option_lookup_clause_rel_with_cls_def list_mset_rel_def br_def
        map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def[symmetric]
       conflict_with_cls_with_cls_with_highest_assn_def option_lookup_clause_rel_with_cls_with_highest_def
       hr_comp_Id2
    apply (rule arg_cong[of _ _ \<open>hr_comp _\<close>])
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed


sepref_register extract_shorter_conflict_list_heur
sepref_thm extract_shorter_conflict_list_st_int_code
  is \<open>PR_CONST extract_shorter_conflict_list_st_int\<close>
  :: \<open>[\<lambda>(M,_). M \<noteq> []]\<^sub>a
      twl_st_heur_lookup_lookup_clause_assn\<^sup>d \<rightarrow>
        trail_assn *a clauses_ll_assn *a
       nat_assn *a
       ((bool_assn *a lookup_clause_rel_assn) *a option_assn (unat_lit_assn *a uint32_nat_assn)) *a
       clause_l_assn *a
       arrayO_assn (arl_assn nat_assn) *a
       vmtf_remove_conc *a phase_saver_conc *a uint32_nat_assn *a cach_refinement_assn\<close>
  supply [[goals_limit = 1]]
  unfolding extract_shorter_conflict_list_st_int_def twl_st_heur_lookup_lookup_clause_assn_def
    PR_CONST_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_st_int_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_st_int_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_st_int_code_def

lemmas extract_shorter_conflict_list_st_int_code[sepref_fr_rules] =
  extract_shorter_conflict_list_st_int_code.refine[of \<A>\<^sub>i\<^sub>n,
      OF isasat_input_bounded_nempty_axioms]

sepref_register extract_shorter_conflict_list_st_int
sepref_thm extract_shorter_conflict_st_trivial_code
  is \<open>PR_CONST extract_shorter_conflict_list_st_int\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur_conflict S \<noteq> []]\<^sub>a twl_st_heur_lookup_lookup_clause_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding  twl_st_confl_extracted_int_assn_def PR_CONST_def
    extract_shorter_conflict_list_st_int_def twl_st_heur_lookup_lookup_clause_assn_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_st_trivial_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_st_trivial_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) extract_shorter_conflict_st_trivial_code_def

lemmas extract_shorter_conflict_st_code_refine[sepref_fr_rules] =
   extract_shorter_conflict_st_trivial_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition extract_shorter_conflict_st_trivial_pre where
  \<open>extract_shorter_conflict_st_trivial_pre S \<longleftrightarrow> (get_conflict_wl S \<noteq> None \<and>
          get_trail_wl S \<noteq> [] \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
          - lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
          0 < get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S))) \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl S)) \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
          distinct_mset (the (get_conflict_wl S)) \<and> \<not> tautology (the (get_conflict_wl S)))\<close>

lemma extract_shorter_conflict_st_trivial_hnr[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_st_trivial_code, extract_shorter_conflict_st_trivial) \<in>
    [extract_shorter_conflict_st_trivial_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
       \<in> [comp_PRE twl_st_heur (\<lambda>S. get_conflict_wl S \<noteq> None)
               (\<lambda>_. comp_PRE twl_st_wl_heur_lookup_lookup_clause_rel
                  (\<lambda>S. get_conflict_wl_heur S \<noteq> None \<and>
                     get_trail_wl_heur S \<noteq> [] \<and>
                     literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
                     - lit_of (hd (get_trail_wl_heur S)) \<in># the (get_conflict_wl_heur S) \<and>
                     0 < get_level (get_trail_wl_heur S) (lit_of (hd (get_trail_wl_heur S))) \<and>
                     literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl_heur S)) \<and>
                     literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and> distinct_mset (the (get_conflict_wl_heur S)) \<and> \<not> tautology (the (get_conflict_wl_heur S)))
                 (\<lambda>_ S. get_trail_wl_heur_conflict S \<noteq> [])
              (\<lambda>_. True))
       (\<lambda>_. True)]\<^sub>a
      hrp_comp (hrp_comp (twl_st_heur_lookup_lookup_clause_assn\<^sup>d) twl_st_wl_heur_lookup_lookup_clause_rel) twl_st_heur \<rightarrow>
     hr_comp (hr_comp twl_st_confl_extracted_int_assn twl_st_heur_confl_extracted) twl_st_heur_no_clvls\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
        hfref_compI_PRE_aux[OF extract_shorter_conflict_st_code_refine[unfolded PR_CONST_def]
           extract_shorter_conflict_list_st_int_extract_shorter_conflict_st_trivial_heur]
         extract_shorter_conflict_l_trivial_int_extract_shorter_conflict_l_trivial] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def twl_st_wl_heur_lookup_lookup_clause_rel_def extract_shorter_conflict_st_trivial_pre_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
      map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn ..
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

lemma extract_shorter_conflict_wl_pre_extract_shorter_conflict_st_trivial_pre:
  assumes \<open>extract_shorter_conflict_wl_pre S\<close>
  shows \<open>extract_shorter_conflict_st_trivial_pre S\<close>
proof -
  have
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    confl_nempty: \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
    n_s: \<open>no_skip S\<close> and
    n_r: \<open>no_resolve S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using assms unfolding extract_shorter_conflict_wl_pre_def by fast+

  have invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  have
    conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have lits_conf: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits confl struct_invs] .

  have trail: \<open>get_trail_wl S \<noteq> []\<close>
    using conf confl confl_nempty unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def apply (cases S)
    by auto
  have uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># {#L \<in># the (get_conflict_wl S).
         0 < get_level (get_trail_wl S) L#}\<close>
    using cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2)[of \<open>state\<^sub>W_of (twl_st_of_wl None S)\<close>]
     n_s n_r confl invs stgy_invs trail confl_nempty unfolding no_skip_def no_resolve_def twl_stgy_invs_def
    by (cases S) simp
  have lev_L: \<open>0 < get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S)))\<close> and
    uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)\<close>
    using uL_D by auto

  have lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl S))\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct_invs] .
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl S))\<close>
    using dist confl by (cases S) (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)

  have tr: \<open>get_trail_wl S \<Turnstile>as CNot (the (get_conflict_wl S))\<close>
    using conf confl by (cases S) (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    using lev_inv  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (cases S) (auto dest!: distinct_consistent_interp)
  have tauto: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
    using consistent_CNot_not_tautology[OF cons tr[unfolded true_annots_true_cls]] .
  show ?thesis
    using lits_conf confl trail lits_trail uL_D lev_L dist_confl tauto
    unfolding extract_shorter_conflict_st_trivial_pre_def
    by (intro conjI) fast+
qed

lemma extract_shorter_conflict_wl_code_extract_shorter_conflict_wl[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_st_trivial_code, extract_shorter_conflict_wl)
    \<in> [extract_shorter_conflict_wl_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE Id
     (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and>
          twl_stgy_invs (twl_st_of_wl None S) \<and>
          get_conflict_wl S \<noteq> None \<and>
          no_skip S \<and>
          no_resolve S \<and> get_conflict_wl S \<noteq> Some {#})
     (\<lambda>_. extract_shorter_conflict_st_trivial_pre)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_assn\<^sup>d)
                    Id \<rightarrow> hr_comp twl_st_confl_extracted_assn
                           Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_shorter_conflict_st_trivial_hnr[unfolded PR_CONST_def]
        extract_shorter_conflict_st_trivial_extract_shorter_conflict_wl] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    using extract_shorter_conflict_wl_pre_extract_shorter_conflict_st_trivial_pre[of x]
    unfolding comp_PRE_def extract_shorter_conflict_wl_pre_def
    by (auto simp: comp_PRE_def twl_st_heur_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by auto
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by auto

  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed


definition rescore_clause :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (vmtf_remove_int \<times> phase_saver) nres\<close> where
\<open>rescore_clause C M vm \<phi> = SPEC (\<lambda>(vm', \<phi>' :: bool list). vm' \<in> vmtf M \<and> phase_saving \<phi>')\<close>

definition (in isasat_input_ops) vmtf_rescore_body
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (nat \<times> vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore_body C _ vm \<phi> = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm, \<phi>). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length \<phi> \<and> atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm, \<phi>). i < length C)
           (\<lambda>(i, vm, \<phi>). do {
               ASSERT(i < length C);
               let vm' = vmtf_mark_to_rescore (atm_of (C!i)) vm;
               let \<phi>' = save_phase_inv (C!i) \<phi>;
               RETURN(i+1, vm', \<phi>')
             })
           (0, vm, \<phi>)
    }\<close>

definition (in isasat_input_ops) vmtf_rescore
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
       (vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore C M vm \<phi> = do {
      (_, vm, \<phi>) \<leftarrow> vmtf_rescore_body C M vm \<phi>;
      RETURN (vm, \<phi>)
    }\<close>

sepref_thm vmtf_rescore_code
  is \<open>uncurry3 vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *a phase_saver_conc\<close>
  unfolding vmtf_rescore_def vmtf_mark_to_rescore_and_unset_def save_phase_inv_def vmtf_mark_to_rescore_def vmtf_unset_def
  vmtf_rescore_body_def
  supply [[goals_limit = 1]] is_None_def[simp] fold_is_None[simp]
  by sepref

concrete_definition (in -) vmtf_rescore_code
   uses isasat_input_bounded_nempty.vmtf_rescore_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescore_code_def

lemmas vmtf_rescore_code_refine[sepref_fr_rules] =
   vmtf_rescore_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* TODO Move *)
lemma vmtf_append_remove_iff':
  \<open>(vm, b @ [L]) \<in> vmtf M \<longleftrightarrow>
     L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<and> (vm, b) \<in> vmtf M\<close>
  by (cases vm) (auto simp: vmtf_append_remove_iff)
(* ENd Move *)
lemma vmtf_rescore_score_clause:
  \<open>(uncurry3 vmtf_rescore, uncurry3 rescore_clause) \<in>
     [\<lambda>(((C, M), vm), \<phi>). literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> vm \<in> vmtf M \<and> phase_saving \<phi>]\<^sub>f
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body C M vm \<phi> \<le>
        SPEC (\<lambda>(n :: nat, vm', \<phi>' :: bool list). phase_saving \<phi>' \<and> vm' \<in> vmtf M)\<close>
    if M: \<open>vm \<in> vmtf M\<close>\<open>phase_saving \<phi>\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for C vm \<phi> M
    unfolding vmtf_rescore_body_def vmtf_mark_to_rescore_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm', \<phi>'). phase_saving \<phi>' \<and> vm' \<in> vmtf M\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using C M by (auto simp: vmtf_def phase_saving_def)
    subgoal using C M by auto
    subgoal using M by auto
    subgoal by auto
    subgoal unfolding save_phase_inv_def by auto
    subgoal using C unfolding phase_saving_def save_phase_inv_def by auto
    subgoal unfolding save_phase_inv_def phase_saving_def by auto
    subgoal using C by (auto simp: vmtf_append_remove_iff')
    subgoal by auto
    done
  have K: \<open>((a, b),(a', b')) \<in> A \<times>\<^sub>f B \<longleftrightarrow> (a, a') \<in> A \<and> (b, b') \<in> B\<close> for a b a' b' A B
    by auto
  show ?thesis
    unfolding vmtf_rescore_def rescore_clause_def uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule bind_refine_spec)
     prefer 2
     apply (subst (asm) K)
     apply (rule H; auto)
    subgoal
      by (meson atm_of_lit_in_atms_of contra_subsetD in_all_lits_of_m_ain_atms_of_iff
          in_multiset_in_set literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by auto
    done
qed

lemma vmtf_rescore_code_rescore_clause[sepref_fr_rules]:
  \<open>(uncurry3 vmtf_rescore_code, uncurry3 (PR_CONST rescore_clause))
     \<in> [\<lambda>(((b, a), c), d). literals_are_in_\<L>\<^sub>i\<^sub>n (mset b) \<and> c \<in> vmtf a \<and>
         phase_saving d]\<^sub>a
       clause_ll_assn\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>
        vmtf_remove_conc *a phase_saver_conc\<close>
  using vmtf_rescore_code_refine[FCOMP vmtf_rescore_score_clause]
  by auto

definition vmtf_flush' where
   \<open>vmtf_flush' _ = vmtf_flush\<close>

sepref_thm vmtf_flush_all_code
  is \<open>uncurry vmtf_flush'\<close>
  :: \<open>[\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] trail_dump_code_refine[sepref_fr_rules]
  unfolding vmtf_flush'_def
  by sepref

concrete_definition (in -) vmtf_flush_all_code
   uses isasat_input_bounded_nempty.vmtf_flush_all_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_all_code_def

lemmas vmtf_flush_all_code_hnr[sepref_fr_rules] =
   vmtf_flush_all_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition flush :: \<open>(nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int nres\<close> where
\<open>flush M _ = SPEC (\<lambda>vm'. vm' \<in> vmtf M)\<close>

lemma trail_bump_rescore:
  \<open>(uncurry vmtf_flush', uncurry flush) \<in> [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>f Id \<times>\<^sub>r Id  \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding vmtf_flush'_def flush_def
  apply (intro nres_relI frefI)
  apply clarify
  subgoal for a aa ab ac b ba ad ae af ag bb bc
    using vmtf_change_to_remove_order
    by auto
  done

lemma trail_dump_code_rescore[sepref_fr_rules]:
   \<open>(uncurry vmtf_flush_all_code, uncurry (PR_CONST flush)) \<in> [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>a
        trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
   (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
  using vmtf_flush_all_code_hnr[FCOMP trail_bump_rescore] by simp

definition st_remove_highest_lvl_from_confl :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
   \<open>st_remove_highest_lvl_from_confl S = S\<close>

definition st_remove_highest_lvl_from_confl_heur :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> twl_st_wl_heur_lookup_conflict\<close> where
  \<open>st_remove_highest_lvl_from_confl_heur = (\<lambda>(M, N, U, (D, _), oth). (M, N, U, D, oth))\<close>


type_synonym (in -) twl_st_wl_W_int =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat clause option \<times> nat clauses \<times> nat clauses \<times> nat clause \<times> (nat literal \<Rightarrow> nat list)\<close>

definition twl_st_wl_W_conflict
  :: \<open>(twl_st_wl_heur_lookup_conflict \<times> twl_st_wl_W_int) set\<close>
where
  \<open>twl_st_wl_W_conflict =
   {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_lookup_clause_rel \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M\<and>
     cach_refinement_empty cach}\<close>

lemma twl_st_wl_W_conflict_alt_def:
  \<open>twl_st_wl_W_conflict =
     (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r option_lookup_clause_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O
     twl_st_heur_no_clvls\<close>
  unfolding twl_st_wl_W_conflict_def twl_st_heur_no_clvls_def
  by force

definition twl_st_W_conflict_int_assn
  :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close>
where
\<open>twl_st_W_conflict_int_assn =
  trail_assn *a clauses_ll_assn *a nat_assn *a
  conflict_option_rel_assn *a
  clause_l_assn *a
  arrayO_assn (arl_assn nat_assn) *a
  vmtf_remove_conc *a phase_saver_conc *a uint32_nat_assn *a
  cach_refinement_assn
  \<close>

lemma st_remove_highest_lvl_from_confl_heur_st_remove_highest_lvl_from_confl:
  \<open>(RETURN o st_remove_highest_lvl_from_confl_heur, RETURN o st_remove_highest_lvl_from_confl) \<in>
   (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls) \<rightarrow>\<^sub>f \<langle>twl_st_wl_W_conflict\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: st_remove_highest_lvl_from_confl_heur_def st_remove_highest_lvl_from_confl_def
      twl_st_wl_W_conflict_def twl_st_heur_confl_extracted2_def twl_st_heur_no_clvls_def
      option_lookup_clause_rel_with_cls_with_highest2_def)


sepref_thm st_remove_highest_lvl_from_confl_code
  is \<open>RETURN o st_remove_highest_lvl_from_confl_heur\<close>
  :: \<open>twl_st_confl_extracted_int_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_W_conflict_int_assn\<close>
  unfolding st_remove_highest_lvl_from_confl_heur_def twl_st_confl_extracted_int_assn_def
  twl_st_W_conflict_int_assn_def
  by sepref


concrete_definition (in -) st_remove_highest_lvl_from_confl_code
   uses isasat_input_bounded_nempty.st_remove_highest_lvl_from_confl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) st_remove_highest_lvl_from_confl_code_def

lemmas st_remove_highest_lvl_from_confl_heur_hnr[sepref_fr_rules] =
   st_remove_highest_lvl_from_confl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) twl_st_assn_no_clvls :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_assn_no_clvls = hr_comp twl_st_heur_assn twl_st_heur_no_clvls\<close>

lemma twl_st_assn_twl_st_wl_W_conflict:
  \<open>twl_st_assn_no_clvls = hr_comp twl_st_W_conflict_int_assn twl_st_wl_W_conflict\<close>
  unfolding twl_st_assn_no_clvls_def twl_st_wl_W_conflict_alt_def twl_st_W_conflict_int_assn_def
    twl_st_heur_assn_def hr_comp_assoc[symmetric] option_lookup_clause_assn_def
  by simp

lemma st_remove_highest_lvl_from_confl_hnr[sepref_fr_rules]:
  \<open>(st_remove_highest_lvl_from_confl_code, RETURN \<circ> st_remove_highest_lvl_from_confl)
   \<in> (twl_st_confl_extracted_assn2 L)\<^sup>d \<rightarrow>\<^sub>a twl_st_assn_no_clvls\<close>
  using st_remove_highest_lvl_from_confl_heur_hnr[FCOMP st_remove_highest_lvl_from_confl_heur_st_remove_highest_lvl_from_confl]
  unfolding twl_st_confl_extracted_assn2_def[symmetric] twl_st_assn_twl_st_wl_W_conflict[symmetric]
  by simp

definition propagate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propagate_bt_wl_D_heur = (\<lambda>L L' (M, N, U, D, Q, W, vm, \<phi>, _, cach). do {
      (D'', C) \<leftarrow> list_of_mset2_None (- L) L' D;
      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset D''));
      (vm, \<phi>) \<leftarrow> rescore_clause D'' M vm \<phi>;
      vm \<leftarrow> flush M vm;
      let W = W[nat_of_lit (- L) := W ! nat_of_lit (- L) @ [length N]];
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [length N]];
      RETURN (Propagated (- L) (length N) # M, N @ [D''], U, C, {#L#}, W, vm, \<phi>, zero_uint32_nat,
         cach)
    })\<close>

sepref_register list_of_mset2_None rescore_clause flush
sepref_thm propagate_bt_wl_D_code
  is \<open>uncurry2 (PR_CONST propagate_bt_wl_D_heur)\<close>
  :: \<open>[\<lambda>((L, L'), S). get_conflict_wl_heur S \<noteq> None \<and> -L \<in># the (get_conflict_wl_heur S) \<and>
         L' \<in># the (get_conflict_wl_heur S) \<and> -L \<noteq> L' \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
       distinct_mset (the (get_conflict_wl_heur S)) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       undefined_lit (get_trail_wl_heur S) L \<and>
     nat_of_lit (-L) < length (get_watched_list_heur S) \<and>
     nat_of_lit L' < length (get_watched_list_heur S) \<and>
     get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S) \<and>
     phase_saving (get_phase_saver_heur S)]\<^sub>a
   unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit = 1]] uminus_\<A>\<^sub>i\<^sub>n_iff[simp] image_image[simp] append_ll_def[simp]
  rescore_clause_def[simp] flush_def[simp]
  unfolding propagate_bt_wl_D_heur_def twl_st_heur_assn_def cons_trail_Propagated_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric]
    cons_trail_Propagated_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_bt_wl_D_code
  uses isasat_input_bounded_nempty.propagate_bt_wl_D_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_bt_wl_D_code_def

lemmas propagate_bt_wl_D_heur_hnr[sepref_fr_rules] =
  propagate_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma propagate_bt_wl_D_heur_propagate_bt_wl_D:
  \<open>(uncurry2 propagate_bt_wl_D_heur, uncurry2 propagate_bt_wl_D) \<in>
     [\<lambda>((L, L'), S). get_conflict_wl S \<noteq> None \<and> -L \<noteq> L' \<and> undefined_lit (get_trail_wl S) L \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))]\<^sub>f
     Id \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur_no_clvls \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding propagate_bt_wl_D_heur_def propagate_bt_wl_D_alt_def twl_st_heur_def list_of_mset2_None_def
    twl_st_heur_no_clvls_def uncurry_def
  apply clarify
  apply refine_vcg
  apply
    (auto simp: propagate_bt_wl_D_heur_def propagate_bt_wl_D_def Let_def
      list_of_mset2_def list_of_mset2_None_def RES_RETURN_RES2 RES_RETURN_RES twl_st_heur_def
      map_fun_rel_def rescore_clause_def flush_def
      intro!: RES_refine vmtf_consD)
  done

definition propagate_bt_wl_D_pre :: \<open>(nat literal \<times> nat literal) \<times> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>propagate_bt_wl_D_pre = (\<lambda>((L, L'), S).
         get_conflict_wl S \<noteq> None \<and>
         - L \<in># the (get_conflict_wl S) \<and>
         L' \<in># the (get_conflict_wl S) \<and>
         - L \<noteq> L' \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
         distinct_mset (the (get_conflict_wl S)) \<and>
         L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         undefined_lit (get_trail_wl S) L)\<close>

lemma propagate_bt_wl_D_hnr[sepref_fr_rules]:
  \<open>(uncurry2 propagate_bt_wl_D_code, uncurry2 propagate_bt_wl_D) \<in>
    [propagate_bt_wl_D_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn_no_clvls\<^sup>d \<rightarrow>
        twl_st_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun \<in>
     [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls)
     (\<lambda>((L, L'), S).
         get_conflict_wl S \<noteq> None \<and>
         - L \<noteq> L' \<and>
         undefined_lit (get_trail_wl S) L \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)))
     (\<lambda>_ ((L, L'), S).
         get_conflict_wl_heur S \<noteq> None \<and>
         - L \<in># the (get_conflict_wl_heur S) \<and>
         L' \<in># the (get_conflict_wl_heur S) \<and>
         - L \<noteq> L' \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
         distinct_mset (the (get_conflict_wl_heur S)) \<and>
         L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         undefined_lit (get_trail_wl_heur S) L \<and>
         nat_of_lit (- L) < length (get_watched_list_heur S) \<and>
         nat_of_lit L' < length (get_watched_list_heur S) \<and>
         local.get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S) \<and>
         phase_saving (get_phase_saver_heur S))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
                      twl_st_heur_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f
                      twl_st_heur_no_clvls) \<rightarrow> hr_comp twl_st_heur_assn twl_st_heur
\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propagate_bt_wl_D_heur_hnr[unfolded PR_CONST_def]
       propagate_bt_wl_D_heur_propagate_bt_wl_D]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def map_fun_rel_def propagate_bt_wl_D_pre_def
    twl_st_heur_no_clvls_def
    by (auto simp: image_image uminus_\<A>\<^sub>i\<^sub>n_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_no_clvls_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


lemma backtrack_wl_D_alt_def:
  \<open>backtrack_wl_D S =
    do {
      ASSERT(backtrack_wl_D_inv S);
      let L = lit_of (hd (get_trail_wl S));
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propagate_bt_wl_D L L' (st_remove_highest_lvl_from_confl S)
      }
      else do {
        let S = st_remove_highest_lvl_from_confl S;
        propagate_unit_bt_wl_D L S
     }
  }\<close>
  unfolding backtrack_wl_D_def st_remove_highest_lvl_from_confl_def
    st_remove_highest_lvl_from_confl_def Let_def
  by auto

lemma backtrack_wl_D_helper3:
  assumes
    invs: \<open>backtrack_wl_D_inv x\<close> and
    extract_shorter: \<open>RETURN xc \<le> extract_shorter_conflict_wl x\<close> and
    decomp: \<open>RETURN xd \<le> find_decomp_wl (lit_of_hd_trail_st x) xc\<close> and
    \<open>Suc 0 < size (the (get_conflict_wl xd))\<close> and
    lit2: \<open>RETURN xf \<le> find_lit_of_max_level_wl xd (lit_of_hd_trail_st x)\<close> and
    \<open>(a, lit_of_hd_trail_st x) \<in> unat_lit_rel\<close> and
    \<open>(aa, xf) \<in> unat_lit_rel\<close>
  shows \<open>propagate_bt_wl_D_pre
          ((lit_of_hd_trail_st x, xf), xd)\<close>
proof -
  obtain M N U D NP UP W Q where
    x: \<open>x = (M, N, U, D, NP, UP, W, Q)\<close>
    by (cases x)
  obtain D' where
    xc: \<open>xc = (M, N, U, Some D', NP, UP, W, Q)\<close> and
    D'_D: \<open>D' \<subseteq># the D\<close> and
    \<open>clause `# twl_clause_of `# mset (tl N) + NP + UP \<Turnstile>pm D'\<close> and
    uM_D': \<open>- lit_of (hd M) \<in># D'\<close>
    using extract_shorter unfolding x extract_shorter_conflict_wl_def
    by (cases xc) (auto simp: x extract_shorter_conflict_wl_def)

  obtain K M1 M2 where
     xd: \<open>xd = (M1, N, U, Some D', NP, UP, W, Q)\<close> and
     decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
     \<open>get_level M K = get_maximum_level M (remove1_mset (- lit_of_hd_trail_st x) D') + 1\<close>
    using decomp unfolding xc find_decomp_wl_def by auto
  have
    xf: \<open>xf \<in># remove1_mset (- lit_of_hd_trail_st x) D'\<close> and
    lev_xf: \<open>get_level M1 xf = get_maximum_level M1 (remove1_mset (- lit_of_hd_trail_st x) D')\<close>
    using lit2 unfolding find_lit_of_max_level_wl_def xd by simp_all
  have
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x\<close> and
    D: \<open>D \<noteq> None\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None x)\<close> and
    M_nempty: \<open>M \<noteq> []\<close>
    using invs unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def x
    by auto
  have lits_D': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D'\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits _ struct_invs] D
      literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF _ D'_D] unfolding xd x by auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None x))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None x))\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>no_dup M\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: x)
  then have undef: \<open>undefined_lit M1 (lit_of_hd_trail_st x)\<close>
    using decomp M_nempty unfolding x lit_of_hd_trail_st_def
    apply (cases M)
     apply (auto dest!: get_all_ann_decomposition_exists_prepend)
    apply (case_tac c; case_tac M2)
       apply auto
    done
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl xd))\<close>
    using dist D distinct_mset_mono[OF D'_D] unfolding x xd cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by auto
  then have diff: \<open>- lit_of_hd_trail_st x \<noteq> xf\<close>
    using lev_xf M_nempty uM_D' xf unfolding x lit_of_hd_trail_st_def xd
    by (cases M) (auto dest!: multi_member_split)
  show ?thesis
    unfolding propagate_bt_wl_D_pre_def
    apply clarify
    apply (intro conjI)
    subgoal
      unfolding xd by simp
    subgoal using uM_D' unfolding xd x lit_of_hd_trail_st_def by auto
    subgoal using xf by (auto simp: x xd dest!: in_diffD)
    subgoal using diff .
    subgoal using lits_D' unfolding xd by auto
    subgoal using dist_confl .
    subgoal
      using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct_invs] M_nempty
      unfolding x by (cases M) (auto simp: lit_of_hd_trail_st_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal
      using xf lits_D' by (auto dest!: multi_member_split in_diffD simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal using undef unfolding x xd by auto
    done
qed

definition remove_last :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option nres\<close> where
  \<open>remove_last _ _  = SPEC(op = None)\<close>

definition propagate_unit_bt_wl_D_int :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propagate_unit_bt_wl_D_int = (\<lambda>L (M, N, U, D, Q, W, vm, \<phi>). do {
      D \<leftarrow> remove_last L D;
      vm \<leftarrow> flush M vm;
      RETURN (Propagated (- L) 0 # M, N, U, D, {#L#}, W, vm, \<phi>)})\<close>

lemma propagate_unit_bt_wl_D_int_propagate_unit_bt_wl_D:
  \<open>(uncurry propagate_unit_bt_wl_D_int, uncurry propagate_unit_bt_wl_D) \<in>
     [\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> undefined_lit (get_trail_wl S) L \<and>
        size(the (get_conflict_wl S)) = 1]\<^sub>f
     Id \<times>\<^sub>f twl_st_heur_no_clvls \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: propagate_unit_bt_wl_D_int_def propagate_unit_bt_wl_D_def RES_RETURN_RES
      twl_st_heur_def flush_def RES_RES_RETURN_RES single_of_mset_def remove_last_def
      twl_st_heur_no_clvls_def
      intro!: RES_refine vmtf_consD size_1_singleton_mset)

definition remove_last_int :: \<open>nat literal \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>remove_last_int = (\<lambda>L (b, n, xs). (True, 0, xs[atm_of L := None]))\<close>

lemma remove_last_int_remove_last:
  \<open>(uncurry (RETURN oo remove_last_int), uncurry remove_last) \<in>
    [\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f Id \<times>\<^sub>r option_lookup_clause_rel \<rightarrow>
      \<langle>option_lookup_clause_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (clarify dest!: size_1_singleton_mset)
  subgoal for a aa ab b ac ba y L
    using mset_as_position_remove[of b \<open>{#L#}\<close> \<open>atm_of L\<close>]
    by (cases L)
     (auto simp: remove_last_int_def remove_last_def option_lookup_clause_rel_def
        RETURN_RES_refine_iff lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       uminus_lit_swap)
  done

sepref_thm remove_last_code
  is \<open>uncurry (RETURN oo (PR_CONST remove_last_int))\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>
     conflict_option_rel_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
  unfolding remove_last_int_def PR_CONST_def zero_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) remove_last_code
   uses isasat_input_bounded_nempty.remove_last_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) remove_last_code_def

lemmas remove_last_int_hnr[sepref_fr_rules] =
   remove_last_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem remove_last_hnr[sepref_fr_rules]:
  \<open>(uncurry remove_last_code, uncurry remove_last)
    \<in> [\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> option_lookup_clause_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
       (\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)
       (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d)
              (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel) \<rightarrow>
    hr_comp conflict_option_rel_assn option_lookup_clause_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF remove_last_int_hnr[unfolded PR_CONST_def]
    remove_last_int_remove_last] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm propagate_unit_bt_wl_D_code
  is \<open>uncurry (PR_CONST propagate_unit_bt_wl_D_int)\<close>
  :: \<open>[\<lambda>(L, S). get_conflict_wl_heur S \<noteq> None \<and> size (the (get_conflict_wl_heur S)) = 1 \<and>
        undefined_lit (get_trail_wl_heur S) L \<and>
         -L \<in># the (get_conflict_wl_heur S) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S)]\<^sub>a
   unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit = 1]] flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propagate_unit_bt_wl_D_int_def cons_trail_Propagated_def[symmetric] twl_st_heur_assn_def
  PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_unit_bt_wl_D_code
  uses isasat_input_bounded_nempty.propagate_unit_bt_wl_D_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_unit_bt_wl_D_code_def

lemmas propagate_unit_bt_wl_D_int_hnr[sepref_fr_rules] =
  propagate_unit_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]

definition propagate_unit_bt_wl_D_pre :: \<open>nat literal \<times> nat twl_st_wl \<Rightarrow> bool\<close> where
   \<open>propagate_unit_bt_wl_D_pre =
      (\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> undefined_lit (get_trail_wl S) L \<and>
        size(the (get_conflict_wl S)) = 1 \<and> -L \<in># the (get_conflict_wl S) \<and>
        L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>

theorem propagate_unit_bt_wl_D_hnr[sepref_fr_rules]:
  \<open>(uncurry propagate_unit_bt_wl_D_code, uncurry propagate_unit_bt_wl_D)
    \<in> [propagate_unit_bt_wl_D_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn_no_clvls\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls)
       (\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> undefined_lit (get_trail_wl S) L \<and>
           size (the (get_conflict_wl S)) = 1)
       (\<lambda>_ (L, S). get_conflict_wl_heur S \<noteq> None \<and> size (the (get_conflict_wl_heur S)) = 1 \<and>
           undefined_lit (get_trail_wl_heur S) L \<and> -L \<in># the (get_conflict_wl_heur S) \<and>
           L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> local.get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S))
       (\<lambda>_. True)]\<^sub>a
   hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d) (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls) \<rightarrow>
   hr_comp twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propagate_unit_bt_wl_D_int_hnr[unfolded PR_CONST_def]
    propagate_unit_bt_wl_D_int_propagate_unit_bt_wl_D]  .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_def  twl_st_heur_no_clvls_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff propagate_unit_bt_wl_D_pre_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def twl_st_assn_no_clvls_def
    by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma backtrack_wl_D_helper4[simp]:
  assumes
    invs: \<open>backtrack_wl_D_inv x\<close> and
    extract_shorter: \<open>RETURN xc \<le> extract_shorter_conflict_wl x\<close> and
    decomp: \<open>RETURN xd \<le> find_decomp_wl (lit_of_hd_trail_st x) xc\<close> and
    size: \<open>\<not> Suc 0 < size (the (get_conflict_wl xd))\<close>
  shows \<open>propagate_unit_bt_wl_D_pre
          (lit_of_hd_trail_st x, xd)\<close>
proof -
  obtain M N U D NP UP W Q where
    x: \<open>x = (M, N, U, D, NP, UP, W, Q)\<close>
    by (cases x)
  obtain D' where
    xc: \<open>xc = (M, N, U, Some D', NP, UP, W, Q)\<close> and
    D'_D: \<open>D' \<subseteq># the D\<close> and
    \<open>clause `# twl_clause_of `# mset (tl N) + NP + UP \<Turnstile>pm D'\<close> and
    uM_D': \<open>- lit_of (hd M) \<in># D'\<close>
    using extract_shorter unfolding x extract_shorter_conflict_wl_def
    by (cases xc) (auto simp: x extract_shorter_conflict_wl_def)

  obtain K M1 M2 where
     xd: \<open>xd = (M1, N, U, Some D', NP, UP, W, Q)\<close> and
     decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
     \<open>get_level M K = get_maximum_level M (remove1_mset (- lit_of_hd_trail_st x) D') + 1\<close>
    using decomp unfolding xc find_decomp_wl_def by auto

  have
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x\<close> and
    D: \<open>D \<noteq> None\<close> \<open>D \<noteq> Some {#}\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None x)\<close> and
    M_nempty: \<open>M \<noteq> []\<close>
    using invs unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def x
    by auto
  have lits_D': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D'\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits _ struct_invs] D
      literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF _ D'_D] unfolding xd x by auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None x))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None x))\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>no_dup M\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: x)
  then have undef: \<open>undefined_lit M1 (lit_of_hd_trail_st x)\<close>
    using decomp M_nempty unfolding x lit_of_hd_trail_st_def
    apply (cases M)
     apply (auto dest!: get_all_ann_decomposition_exists_prepend)
    apply (case_tac c; case_tac M2)
       apply auto
    done
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl xd))\<close>
    using dist D distinct_mset_mono[OF D'_D] unfolding x xd cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by auto
  show ?thesis
    unfolding propagate_unit_bt_wl_D_pre_def
    apply clarify
    apply (intro conjI)
    subgoal unfolding xd by simp
    subgoal using undef unfolding x xd by auto
    subgoal using size uM_D' by (cases D') (auto simp: x xd)
    subgoal using uM_D' unfolding xd by (auto simp: lit_of_hd_trail_st_def x)
    subgoal
      using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct_invs] M_nempty
      unfolding x by (cases M) (auto simp: lit_of_hd_trail_st_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    done
qed
end

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

sepref_register find_lit_of_max_level_wl propagate_bt_wl_D propagate_unit_bt_wl_D
sepref_register backtrack_wl_D
sepref_thm backtrack_wl_D
  is \<open>PR_CONST backtrack_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] backtrack_wl_D_invD[simp] backtrack_wl_D_inv_find_decomp_wl_preD[intro!, dest]
  backtrack_get_conglit_wl_not_NoneD[dest] lit_of_hd_trail_st_def[symmetric, simp]
  size_conflict_wl_def[simp] st_remove_highest_lvl_from_confl_def[simp]
  backtrack_wl_D_helper3[simp]
  unfolding backtrack_wl_D_alt_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lit_of_hd_trail_st_def[symmetric]
    cons_trail_Propagated_def[symmetric]
    size_conflict_wl_def[symmetric] one_uint32_nat_def[symmetric]
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
  text \<open>We need an \<^term>\<open>ASSN_ANNOT\<close> for type \<^typ>\<open>'a nres\<close>, but this does not exist and
   it is not clear how to do it.\<close>
           apply sepref_dbg_side_unfold apply (auto simp: )[]
          apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
                apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
         apply sepref_dbg_trans_step_keep
        apply sepref_dbg_trans_step_keep
       apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
     apply (solves \<open>simp\<close>)
    apply sepref_dbg_trans_step_keep
   apply sepref_dbg_trans_step_keep
  apply sepref_dbg_constraints
  done

concrete_definition (in -) backtrack_wl_D_code
   uses isasat_input_bounded_nempty.backtrack_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_code_def

lemmas backtrack_wl_D_code_refine[sepref_fr_rules] =
   backtrack_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>


end