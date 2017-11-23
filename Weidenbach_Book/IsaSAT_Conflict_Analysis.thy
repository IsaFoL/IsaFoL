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
  :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause option \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
     ('v cconflict \<times> nat \<times> lbd) nres\<close>
where
  \<open>lookup_conflict_merge_abs_union M N i C _ _ =
     SPEC (\<lambda>c. fst c = Some (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i)))) \<and>
        fst (snd c) = card_max_lvl M (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i))))
      )\<close>

lemma lookup_conflict_merge_abs_union_alt_def:
  \<open>lookup_conflict_merge_abs_union M N i C clvls lbd =
      SPEC (\<lambda>c. fst c = lookup_conflict_merge_abs_union' M N i C clvls  \<and>
         fst (snd c) = card_max_lvl M (the (lookup_conflict_merge_abs_union' M N i C clvls)))
     \<close>
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
  \<open>(uncurry5 (lookup_conflict_merge_aa), uncurry5 lookup_conflict_merge_abs_union) \<in>
     [\<lambda>(((((M, N), i), C), clvls), lbd). distinct (N!i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i)) \<and>
          \<not> tautology (mset (N!i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None \<and>
         clvls = card_max_lvl M (the C)]\<^sub>f
    Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<rightarrow>
        \<langle>option_lookup_clause_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for M N i b j xs clvls lbd M' N' i' _ clvls' lbd' C
    using lookup_conflict_merge'_spec[of b j xs C \<open>N' ! i'\<close> clvls M]
    unfolding lookup_conflict_merge_abs_union_def lookup_conflict_merge_aa_def
    by auto
  done

lemma lookup_conflict_merge_code_lookup_conflict_merge_abs_union[sepref_fr_rules]:
  \<open>(uncurry5 lookup_conflict_merge_code, uncurry5 lookup_conflict_merge_abs_union) \<in>
    [\<lambda>(((((M, N), i), C), clvls), lbd).
      distinct (N!i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i)) \<and> \<not> tautology (mset (N!i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None \<and> i < length N \<and> clvls = card_max_lvl M (the C) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> no_dup M]\<^sub>a
    trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (option_lookup_clause_assn)\<^sup>d *\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d \<rightarrow>
     option_lookup_clause_assn *a uint32_nat_assn *a lbd_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
     \<in> [comp_PRE
     (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
      option_lookup_clause_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      Id)
     (\<lambda>(((((M, N), i), C), clvls), lbd).
         distinct (N ! i) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n
          (mset (N ! i)) \<and>
         \<not> tautology (mset (N ! i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and>
         C \<noteq> None \<and>
         clvls = card_max_lvl M (the C))
     (\<lambda>_ (((((M, N), i), _, xs), _), _).
         i < length N \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
         (\<forall>j<length (N ! i).
             atm_of (N ! i ! j)
             < length (snd xs)) \<and>
         no_dup M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n
          (mset (N ! i)))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((hr_comp
  trail_pol_assn trail_pol)\<^sup>k *\<^sub>a
clauses_ll_assn\<^sup>k *\<^sub>a
nat_assn\<^sup>k *\<^sub>a
conflict_option_rel_assn\<^sup>d *\<^sub>a
uint32_nat_assn\<^sup>k *\<^sub>a
lbd_assn\<^sup>d)
                     (Id \<times>\<^sub>f Id \<times>\<^sub>f
nat_rel \<times>\<^sub>f
option_lookup_clause_rel \<times>\<^sub>f
nat_rel \<times>\<^sub>f
Id) \<rightarrow> hr_comp
        (conflict_option_rel_assn *a
         uint32_nat_assn *a lbd_assn)
        (option_lookup_clause_rel \<times>\<^sub>f
         (nat_rel \<times>\<^sub>f Id))\<close>
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
  \<open>update_confl_tl_wl_heur = (\<lambda>C L (M, N, U, D, Q, W, vmtf, \<phi>, clvls, cach, lbd).
     (if C = 0 then do {
         let D' = remove1_mset (-L) (the D);
         let L' = atm_of L;
         ASSERT (clvls \<ge> 1);
         RETURN (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf,
            save_phase L \<phi>,
            fast_minus clvls one_uint32_nat,
            cach, lbd))
         }
      else do {
        let L' = atm_of L;
        (D', clvls, lbd) \<leftarrow> lookup_conflict_merge_abs_union M N C D clvls lbd;
        let D' = remove1_mset L (the D');
        RETURN (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf,
           save_phase L \<phi>, fast_minus clvls one_uint32_nat, cach, lbd))
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
      clvls = card_max_lvl M (the D) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
      no_dup M
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
        is_proped (hd (get_trail_wl S)) \<and>
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
           clvls = card_max_lvl M (the D) \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
           no_dup M)
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
    have
      trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail( get_trail_wl S)\<close>
      using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits_\<A>\<^sub>i\<^sub>n, of None ] struct_invs
      by auto

    fix x'
    assume x'x: \<open>(x', x) \<in> nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur\<close>
    then obtain S' where
      [simp]: \<open>x' = ((C, L), S')\<close>
      by (cases x') auto
    obtain Q' A m fst_As lst_As next_search oth \<phi> clvls cach where
      [simp]: \<open>S' = (M, N, U, D, W, Q', ((A, m, fst_As, lst_As, next_search), oth), \<phi>, clvls, cach)\<close> and
      n_d: \<open>no_dup (get_trail_wl S)\<close>
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
      trail n_d
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

(* TODO rename to literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail + Move *)
lemma literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n:
  assumes
    \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)\<close> (is \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail ?M\<close>)
proof -
  let ?M = \<open>lit_of `# mset ?M\<close>
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
    using N
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_def image_image)
qed

(* TODO Move *)
lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (L # M) \<longleftrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)
(* End Move *)

lemma skip_and_resolde_hd_D\<^sub>0:
  assumes
    \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    \<open>get_trail_wl S = Propagated x21 x22 # xs\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>- x21 \<in> snd ` D\<^sub>0\<close>
  using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[of S] assms
  by (cases S)
     (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons image_image
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

end