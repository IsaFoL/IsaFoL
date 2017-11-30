theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup
begin

subsubsection \<open>Refining Propagate And Conflict\<close>

paragraph \<open>Propagation, Inner Loop\<close>

context isasat_input_bounded
begin

lemma unit_prop_body_wl_invD:
  fixes S w K
  defines \<open>C \<equiv> (watched_by S K) ! w\<close>
  assumes inv: \<open>unit_prop_body_wl_inv S w K\<close>
  shows \<open>distinct((get_clauses_wl S)!C)\<close> and \<open>get_conflict_wl S = None\<close>
proof -
  obtain M N U D' NP UP Q W where
     S: \<open>S = (M, N, U, D', NP, UP, Q, W)\<close>
    by (cases S)
  have
     struct_invs: \<open>twl_struct_invs (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))\<close> and
     \<open>twl_list_invs (st_l_of_wl (Some (K, w)) S)\<close> and
     corr: \<open>correct_watching S\<close> and
     \<open>w < length (watched_by S K)\<close> and
     confl: \<open>get_conflict_wl S = None\<close> and
     w_ge_0: \<open>0 < watched_by S K ! w\<close> and
     w_le_length: \<open>w < length (watched_by S K)\<close> and
     w_le_length_S: \<open>watched_by S K ! w < length (get_clauses_wl S)\<close>
    using inv unfolding unit_prop_body_wl_inv_def by fast+

  show \<open>get_conflict_wl S = None\<close>
    using confl .
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
       (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S)))\<close> and
      \<open>\<forall>D\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))).
      \<not> tautology D\<close>
      and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
    (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S)))\<close>
    using struct_invs unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have \<open>distinct_mset_set (mset ` set (tl N))\<close>
    apply (subst append_take_drop_id[of \<open>U\<close> \<open>tl N\<close>, symmetric])
    apply (subst set_append)
    apply (subst image_Un)
    apply (subst distinct_mset_set_union)
    using dist
    by (auto simp: C_def S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        mset_take_mset_drop_mset drop_Suc)
  moreover have NC: \<open>N!C \<in> set (tl N)\<close>
     using w_ge_0 w_le_length_S unfolding C_def S
     by (auto intro!: nth_in_set_tl)
  ultimately show \<open>distinct((get_clauses_wl S)!C)\<close>
     unfolding distinct_mset_set_def S by simp
qed

lemma (in -)[sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def
      lit_of_natP_def)

fun watched_by_int:: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> watched\<close> where
  \<open>watched_by_int (M, N, U, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat literal \<Rightarrow> nat list)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, _, W) = W\<close>

fun (in -) get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat list list\<close> where
  \<open>get_watched_wl_heur (_, _, _, _, _, W, _) = W\<close>

definition (in -) watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app_heur = (\<lambda>(M, N, U, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>

definition (in -) watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

lemma watched_by_app_watched_by_app_heur:
  \<open>(uncurry2 (RETURN ooo watched_by_app_heur), uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L)]\<^sub>f
     twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: watched_by_app_heur_def watched_by_app_def twl_st_heur_def map_fun_rel_def)

sepref_thm watched_by_app_heur_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and> K < length (watched_by_int S L)]\<^sub>a
        twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_heur_def twl_st_heur_assn_def nth_rll_def[symmetric]
  by sepref

concrete_definition (in -) watched_by_app_heur_code
   uses isasat_input_bounded.watched_by_app_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_code_def

lemmas watched_by_app_heur_code_refine[sepref_fr_rules] =
   watched_by_app_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma watched_by_app_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 watched_by_app_heur_code, uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K).  L \<in> snd ` D\<^sub>0 \<and> K < length (watched_by S L)]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 watched_by_app_heur_code, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_by_app))
  \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f nat_rel)
      (\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L))
      (\<lambda>_ ((S, L), K).
          nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF watched_by_app_heur_code_refine[unfolded PR_CONST_def]
        watched_by_app_watched_by_app_heur[unfolded PR_CONST_def]] .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

(* TODO Move *)
lemma (in -) twl_struct_invs_length_clause_ge_2:
  assumes
    struct: \<open>twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close> and
    i: \<open>i > 0\<close> \<open>i < length (get_clauses_wl S)\<close>
 shows \<open>length (get_clauses_wl S ! i) \<ge> 2\<close>
proof -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S)
  have \<open>twl_st_inv (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) (M, N, U, D, NP, UP, WS, Q)))\<close>
    using struct unfolding S twl_struct_invs_def by fast
  then have \<open>\<forall>x\<in>set (tl N). 2 \<le> length x \<and> distinct x\<close>
    by (auto simp: twl_st_inv.simps mset_take_mset_drop_mset')
  then show ?thesis
    using i by (auto simp: nth_in_set_tl S)
qed
(* End Move *)


lemma unit_prop_body_wl_D_invD:
  assumes \<open>unit_prop_body_wl_D_inv S w L\<close>
  shows
    \<open>w < length (watched_by S L)\<close> and
    \<open>watched_by_app S L w < length (get_clauses_wl S)\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w \<noteq> []\<close> and
    \<open>Suc 0 < length (get_clauses_wl S ! watched_by_app S L w)\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    \<open>watched_by_app S L w > 0\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>get_conflict_wl S = None\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! watched_by_app S L w))\<close> and
    \<open>distinct (get_clauses_wl S ! watched_by_app S L w)\<close>
proof -
  show \<open>L \<in> snd ` D\<^sub>0\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def by fast
  show \<open>w < length (watched_by S L)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by fast
  show S_L_W_le_S: \<open>watched_by_app S L w < length (get_clauses_wl S)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast
  show \<open>get_clauses_wl S ! watched_by_app S L w \<noteq> []\<close>
    using assms twl_struct_invs_length_clause_ge_2[of L w S \<open>watched_by S L ! w\<close>]
    unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      twl_list_invs_def by force
  show le: \<open>Suc 0 < length (get_clauses_wl S ! watched_by_app S L w)\<close>
    using assms twl_struct_invs_length_clause_ge_2[of L w S \<open>watched_by S L ! w\<close>]
    unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      twl_list_invs_def by force
  have nempty: \<open>get_clauses_wl S \<noteq> []\<close> and S_L_w_ge_0: \<open>0 < watched_by_app S L w\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    twl_list_invs_def watched_by_app_def by auto
  obtain M N U D NP UP W Q where
    S: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
    by (cases S)
  show lits_N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! watched_by_app S L w))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def apply -
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of _ _ M U D NP UP Q W])
    apply (rule S_L_W_le_S)
    apply (rule S_L_w_ge_0)
    using S by (auto simp del: twl_st_of.simps)
  then show \<open>get_clauses_wl S ! watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close>
    using le apply (cases \<open>get_clauses_wl S ! watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S ! watched_by_app S L w)\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show \<open>get_clauses_wl S ! watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close>
    using lits_N le apply (cases \<open>get_clauses_wl S ! watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S ! watched_by_app S L w)\<close>;
        cases \<open>tl (tl (get_clauses_wl S ! watched_by_app S L w))\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show S_L_W_ge_0: \<open>watched_by_app S L w > 0\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and \<open>get_conflict_wl S = None\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    struct: \<open>twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close> and
    stgy: \<open>twl_stgy_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    all_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
          (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding twl_struct_invs_def by fast+
  then have
     learned_tauto:
       \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))). \<not> tautology s\<close> and
     dist:
        \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L)
            (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>\<forall>D\<in>mset ` set (tl (get_clauses_wl S)). distinct_mset D\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    unfolding set_append
    using dist
    apply (cases S)
    by (auto simp: drop_Suc clauses_def mset_take_mset_drop_mset
        watched_by_app_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct)
  then show \<open>distinct (get_clauses_wl S ! watched_by_app S L w)\<close>
    using S_L_W_le_S S_L_W_ge_0 nempty
    by (cases S; cases \<open>get_clauses_wl S\<close>)
       (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct
         clauses_def mset_take_mset_drop_mset watched_by_app_def)
qed

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) ! i ! j\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j.  N ! i ! j)\<close>


sepref_thm access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>(((_,N,_), i), j). i < length N \<and> j < length_rll N i]\<^sub>a
      twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp]
  unfolding twl_st_heur_assn_def access_lit_in_clauses_heur_def
    nth_rll_def[symmetric]
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_code_def

lemmas access_lit_in_clauses_heur_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma access_lit_in_clauses_heur_access_lit_in_clauses:
  \<open>(uncurry2 (RETURN ooo access_lit_in_clauses_heur), uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
   twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: access_lit_in_clauses_heur_def twl_st_heur_def access_lit_in_clauses_def)

lemma access_lit_in_clauses_refine[sepref_fr_rules]:
  \<open>(uncurry2 access_lit_in_clauses_heur_code, uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
    [\<lambda>((S, i), j). i < length (get_clauses_wl S) \<and> j < length_rll (get_clauses_wl S) i]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    unat_lit_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 access_lit_in_clauses_heur_code, uncurry2 (RETURN \<circ>\<circ>\<circ> access_lit_in_clauses))
  \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) (\<lambda>_. True)
      (\<lambda>_ (((_, N, _), i), j). i < length N \<and> j < length_rll N i) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF access_lit_in_clauses_heur_code_refine[unfolded PR_CONST_def]
        access_lit_in_clauses_heur_access_lit_in_clauses[unfolded PR_CONST_def]] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
          map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

definition (in -) find_unwatched_wl_st  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st = (\<lambda>(M, N, U, D, NP, UP, Q, W) i. do {
    find_unwatched_l M (N ! i)
  })\<close>

lemma find_unwatched_l_find_unwatched_wl_s:
  \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S ! C) = find_unwatched_wl_st S C\<close>
  by (cases S) (auto simp: find_unwatched_wl_st_def)

definition (in -) find_unwatched :: "('a, 'b) ann_lits \<Rightarrow> 'a clause_l \<Rightarrow> (nat option) nres" where
\<open>find_unwatched M C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
    (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and> j < length C \<and> j \<ge> 2))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      ASSERT(i < length C);
      case polarity M (C!i) of
        None \<Rightarrow> do { RETURN (Some i, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some i, i)} else do { RETURN (None, i+1)})
    })
    (None, 2::nat);
  RETURN (fst S)
  }
\<close>

definition find_unwatched_wl_st_heur  :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st_heur = (\<lambda>(M, N, U, D, Q, W, vm, \<phi>) i. do {
    find_unwatched M (N ! i)
  })\<close>

end

lemma case_tri_bool_If:
  \<open>(case a of
       None \<Rightarrow> f1
     | Some v \<Rightarrow>
        (if v then f2 else f3)) =
   (let b = a in if b = UNSET
    then f1
    else if b = SET_TRUE then f2 else f3)\<close>
  by (auto split: option.splits)

context isasat_input_bounded_nempty
begin

sepref_thm find_unwatched_wl_st_heur_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_st_heur))\<close>
  :: \<open>[\<lambda>(S, i). i < length (get_clauses_wl_heur S) \<and> i > 0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S]\<^sub>a
         twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0'[intro] nth_rll_def[simp]
    length_rll_def[simp]
  unfolding find_unwatched_wl_st_heur_def twl_st_heur_assn_def PR_CONST_def
  find_unwatched_def nth_rll_def[symmetric] length_rll_def[symmetric]
  case_tri_bool_If
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma (in -) find_unwatched:
  assumes \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close>
  shows \<open>find_unwatched M C \<le> find_unwatched_l M C\<close>
  unfolding find_unwatched_def find_unwatched_l_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq polarity_def
        split: if_splits intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq polarity_def
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal by (auto simp: polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using distinct_consistent_interp[OF assms(1)]
    apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth
       polarity_def split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
    by (metis atLeastLessThan_iff less_antisym)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using no_dup_consistentD[OF assms(1)]
    by (cases s, cases \<open>fst s\<close>)
      (auto simp: Decided_Propagated_in_iff_in_lits_of_l all_set_conv_nth
        intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal by auto
  subgoal for s j by auto
  subgoal by auto
  done

theorem find_unwatched_wl_st_heur_find_unwatched_wl_s:
  \<open>(uncurry find_unwatched_wl_st_heur, uncurry find_unwatched_wl_st)
    \<in> [\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
      length (get_clauses_wl S ! i) \<ge> 2]\<^sub>f
      twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: find_unwatched_wl_st_def find_unwatched_wl_st_heur_def twl_st_heur_def
    find_unwatched)

theorem find_unwatched_wl_st_heur_code_find_unwatched_wl_s[sepref_fr_rules]:
  \<open>(uncurry find_unwatched_wl_st_heur_code, uncurry find_unwatched_wl_st)
    \<in> [\<lambda>(S, i). \<exists>w L. unit_prop_body_wl_D_inv S w L \<and> i = watched_by_app S L w]\<^sub>a
      twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry find_unwatched_wl_st_heur_code, uncurry find_unwatched_wl_st)
    \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f nat_rel)
         (\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
            2 \<le> length (get_clauses_wl S ! i))
         (\<lambda>_ (S, i). i < length (get_clauses_wl_heur S) \<and> 0 < i \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (twl_st_heur \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp (option_assn nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[unfolded PR_CONST_def]
    find_unwatched_wl_st_heur_find_unwatched_wl_s] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
  proof -
    have [simp]: \<open>mset `# mset (take ai (tl ah)) + ak + (mset `# mset (drop (Suc ai) ah) + al) =
      mset `# mset (tl ah) + ak + al\<close> for ai ah ak al
      apply (subst (6) append_take_drop_id[of ai, symmetric])
      unfolding mset_append drop_Suc
      by auto
    have [intro]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur T\<close> and \<open>get_clauses_wl_heur T = get_clauses_wl S\<close> if
       \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))))\<close> and
       \<open>(T, S) \<in> twl_st_heur\<close>
      for S and T
      using that apply (auto simp: twl_st_heur_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' clauses_def literals_are_in_\<L>\<^sub>i\<^sub>n_heur_def)
      apply (auto simp add: all_lits_of_mm_union literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
      done
    show ?thesis
      unfolding comp_PRE_def
      apply (intro ext impI conjI)
      subgoal
        using that by (auto dest: simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
            unit_propagation_inner_loop_body_l_inv_def watched_by_app_def)
      subgoal
        by (use that in \<open>auto simp: comp_PRE_def unit_prop_body_wl_D_inv_def
            mset_take_mset_drop_mset clauses_def mset_take_mset_drop_mset' drop_Suc
            unit_prop_body_wl_inv_def watched_by_app_def
            unit_propagation_inner_loop_body_l_inv_def twl_st_heur_def
          simp del: twl_st_of.simps st_l_of_wl.simps\<close>)
      done
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemmas unit_prop_body_wl_D_invD' =
  unit_prop_body_wl_D_invD[of \<open>(M, N, U, D, NP, UP, WS, Q)\<close> for M N U D NP UP WS Q,
   unfolded watched_by_app_def,
    simplified] unit_prop_body_wl_D_invD(7)

definition set_conflict_wl' :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl' = (\<lambda>C (M, N, U, D, NP, UP, Q, W). (M, N, U, Some (mset (N!C)), NP, UP, {#}, W))\<close>

lemma set_conflict_wl'_alt_def:
  \<open>set_conflict_wl' i S = set_conflict_wl (get_clauses_wl S ! i) S\<close>
  by (cases S) (auto simp: set_conflict_wl'_def set_conflict_wl_def)

definition set_conflict_wl'_int :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>set_conflict_wl'_int = (\<lambda>C (M, N, U, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, stats). do {
    let n = zero_uint32_nat;
    (D, clvls, lbd) \<leftarrow> conflict_merge M N C D n lbd;
    RETURN (M, N, U, D, {#}, W, vmtf, \<phi>, clvls, cach, lbd, incr_conflict stats)})\<close>

sepref_thm set_conflict_wl'_int_code
  is \<open>uncurry set_conflict_wl'_int\<close>
  :: \<open>[\<lambda>(C, S). get_conflict_wl_heur S = None \<and> C < length (get_clauses_wl_heur S) \<and>
      distinct (get_clauses_wl_heur S ! C) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl_heur S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl_heur S ! C)) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl_heur S) \<and>
      no_dup (get_trail_wl_heur S)]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]]
    lookup_conflict_merge_code_set_conflict[unfolded twl_st_heur_assn_def, sepref_fr_rules]
  unfolding set_conflict_wl'_int_def twl_st_heur_assn_def IICF_List_Mset.lms_fold_custom_empty
  by sepref

concrete_definition (in -) set_conflict_wl'_int_code
  uses isasat_input_bounded_nempty.set_conflict_wl'_int_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl'_int_code_def

lemmas set_conflict_wl'_int_code[sepref_fr_rules] =
  set_conflict_wl'_int_code.refine[OF isasat_input_bounded_nempty_axioms]


lemma set_conflict_wl'_int_set_conflict_wl':
  \<open>(uncurry set_conflict_wl'_int, uncurry (RETURN oo set_conflict_wl')) \<in>
    nat_rel \<times>\<^sub>r twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
    (auto simp: twl_st_heur_def set_conflict_wl'_int_def set_conflict_wl'_def
        conflict_merge_def bind_RES_RETURN2_eq RETURN_def RES_RES2_RETURN_RES
        counts_maximum_level_def RES_RETURN_RES3 RES_RES_RETURN_RES RES_RES3_RETURN_RES
      intro!: RES_refine)

lemma set_conflict_wl'_int_code_set_conflict_wl'[sepref_fr_rules]:
  \<open>(uncurry set_conflict_wl'_int_code, uncurry (RETURN oo set_conflict_wl')) \<in>
    [\<lambda>(C, S). get_conflict_wl S = None \<and> C < length (get_clauses_wl S) \<and>
      distinct (get_clauses_wl S ! C) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl S ! C)) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)]\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
    twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry set_conflict_wl'_int_code, uncurry (RETURN \<circ>\<circ> set_conflict_wl'))
  \<in> [comp_PRE (nat_rel \<times>\<^sub>f twl_st_heur) (\<lambda>_. True)
       (\<lambda>_ (C, S).
           get_conflict_wl_heur S = None \<and>
           C < length (get_clauses_wl_heur S) \<and>
           distinct (get_clauses_wl_heur S ! C) \<and>
           literals_are_in_\<L>\<^sub>i\<^sub>n
            (mset (get_clauses_wl_heur S ! C)) \<and>
           \<not> tautology (mset (get_clauses_wl_heur S ! C)) \<and>
           literals_are_in_\<L>\<^sub>i\<^sub>n_trail
            (get_trail_wl_heur S) \<and>
           no_dup (get_trail_wl_heur S))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d)
                       (nat_rel \<times>\<^sub>f
                        twl_st_heur) \<rightarrow> hr_comp
           twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_conflict_wl'_int_code set_conflict_wl'_int_set_conflict_wl']
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def by auto
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
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


definition update_clause_wl_heur :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    (nat \<times> twl_st_wl_heur) nres\<close> where
  \<open>update_clause_wl_heur = (\<lambda>(L::nat literal) C w i f (M, N, U, D, Q, W, vm). do {
     let K' = (N!C) ! f;
     let N' = list_update N C (swap (N!C) i f);
     let W = W[nat_of_lit L := delete_index_and_swap (W ! nat_of_lit L) w];
     RETURN (w, (M, N', U, D, Q,
            W[nat_of_lit K':= W ! nat_of_lit K' @ [C]],
            vm))
  })\<close>

lemma update_clause_wl_heur_update_clause_wl:
  \<open>(uncurry5 update_clause_wl_heur, uncurry5 (update_clause_wl)) \<in>
   [\<lambda>(((((L, C), w), i), f), S). (get_clauses_wl S ! C) ! f \<noteq> L]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>nat_rel \<times>\<^sub>r twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def)

lemma length_delete_index_and_swap_ll[simp]: \<open>length (delete_index_and_swap_ll s i j) = length s\<close>
  by (auto simp: delete_index_and_swap_ll_def)

sepref_thm update_clause_wl_code
  is \<open>uncurry5 update_clause_wl_heur\<close>
  :: \<open>
    [\<lambda>(((((L, C), w), i), f), S).
      C < length (get_clauses_wl_heur S) \<and>
      f < length (get_clauses_wl_heur S ! C) \<and>
      i < length (get_clauses_wl_heur S ! C) \<and>
      nat_of_lit L < length (get_watched_wl_heur S) \<and>
      nat_of_lit ((get_clauses_wl_heur S ! C) ! f)  < length (get_watched_wl_heur S) \<and>
      w < length (get_watched_wl_heur S ! nat_of_lit L)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>
       nat_assn *a twl_st_heur_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric] delete_index_and_swap_ll_def[symmetric]
   append_ll_def[symmetric]
  by sepref


concrete_definition (in -) update_clause_wl_code
  uses isasat_input_bounded_nempty.update_clause_wl_code.refine_raw
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_code_def

lemmas update_clause_wl_code[sepref_fr_rules] =
  update_clause_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma
  find_unwatched_not_tauto:
    \<open>\<not>tautology(mset (get_clauses_wl S ! watched_by_app S L C))\<close>
    (is ?tauto is \<open>\<not>tautology (?D)\<close> is \<open>\<not>tautology (mset ?C)\<close>)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv None (watched_by_app S L C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    val: \<open>polarity_st S (get_clauses_wl S ! watched_by_app S L C !
         (1 - (if access_lit_in_clauses S (watched_by_app S L C) 0 = L then 0 else 1))) = Some False\<close>
      (is \<open>polarity_st _ (_ ! _ ! ?i) = Some False\<close>)
  for S C xj L
proof  -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S)

  have \<open>consistent_interp (lits_of_l (trail (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))))\<close>
    \<open>no_dup (trail (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))))\<close> and
    valid: \<open>valid_enqueued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    by (cases S) (auto)

  have \<open>twl_list_invs (st_l_of_wl (Some (L, C)) S)\<close> and C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and \<open>no_duplicate_queued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
  have \<open>\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S ! (watched_by S L ! C))).
         - L \<in> lits_of_l (get_trail_wl S)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def watched_by_app_def
    by auto
  moreover {
    have \<open>twl_list_invs (st_l_of_wl (Some (L, C)) S)\<close> and \<open>C < length (watched_by S L)\<close> and
      \<open>get_conflict_wl S = None\<close> and \<open>no_duplicate_queued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
    then have \<open>add_mset L WS \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
      apply (cases \<open>drop C (watched_by S L)\<close>)
      apply (simp add: S image_image split: if_splits)
      apply (simp add: S image_image split: if_splits)
      unfolding ex_disj_distrib
      by blast
    from mset_subset_eq_insertD[OF this] have \<open>- L \<in> lits_of_l (convert_lits_l N M)\<close>
      by (auto simp: lits_of_def)
  }
  moreover have \<open>- ?C ! ?i \<in> lits_of_l (convert_lits_l N M)\<close>
    using val by (auto simp: S polarity_st_def watched_by_app_def polarity_def
        access_lit_in_clauses_def Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  moreover have length_C: \<open>length ?C \<ge> 2\<close>
    apply (rule twl_struct_invs_length_clause_ge_2)
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by (auto simp: watched_by_app_def)
  moreover {
    have QL: \<open>Q L ! C = hd (drop C (Q L))\<close>
      using confl C_le length_C by (auto simp: S hd_drop_conv_nth split: )
    have \<open>L \<in># mset (watched_l ?C)\<close>
      using valid confl C_le length_C by (auto simp: QL S take_2_if watched_by_app_def)
    then have \<open>N ! (Q L ! C) ! 0 = L \<or> N ! (Q L ! C) ! 1 = L\<close>
      using confl C_le length_C by (auto simp: S take_2_if watched_by_app_def QL split: if_splits)
  }
  ultimately have Not: \<open>lits_of_l (get_trail_wl S) \<Turnstile>s CNot ?D\<close>
    unfolding true_clss_def_iff_negation_in_model
    apply (subst (2) append_take_drop_id[symmetric, of _ 2])
    unfolding mset_append watched_by_app_def access_lit_in_clauses_def
    by (auto simp: S take_2_if hd_conv_nth split: if_splits)
  show ?thesis
    using consistent_CNot_not_tautology[OF cons Not] .
qed

lemma
  find_unwatched_get_clause_neq_L:
    \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<noteq> L\<close> (is ?neq)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv (Some xj) (watched_by S L ! C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof (rule ccontr)
  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm A) \<longleftrightarrow> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = atms_of_mm A\<close> for A
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def by metis
  assume eq[simplified, simp]: \<open>\<not> ?neq\<close>
  let ?C = \<open>get_clauses_wl S ! watched_by_app S L C\<close>
  let ?L = \<open>get_clauses_wl S ! watched_by_app S L C ! xj\<close>
  have corr: \<open>correct_watching S\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    unfolding correct_watching.simps twl_struct_invs_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
  moreover have \<open>watched_by_app S L C < length (get_clauses_wl S)\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover have \<open>watched_by_app S L C > 0\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  ultimately have in_watched: \<open>watched_by_app S L C \<in># mset (watched_by S L)\<close>
    using inv by (auto simp: watched_by_app_def dest: unit_prop_body_wl_D_invD)

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover have \<open>L \<in> snd ` D\<^sub>0\<close>
    using inv by (auto intro: unit_prop_body_wl_D_invD)
  ultimately have \<open>L \<in># all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)) + get_unit_init_clss S)\<close>
    using alien
    by (cases S)
        (auto 5 5 simp: get_unit_init_clss_def clauses_def mset_take_mset_drop_mset drop_Suc
        mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset.no_strange_atm_def
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym in_all_lits_of_mm_ain_atms_of_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        dest: in_atms_of_mset_takeD)
    then have H: \<open>mset (watched_by S L) =
      mset_set {x. Suc 0 \<le> x \<and> x < length (get_clauses_wl S) \<and> L \<in> set (watched_l (get_clauses_wl S ! x))}\<close>
      using corr by (cases S)
          (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
          get_unit_init_clss_def)
  have L_in_watched: \<open>L \<in> set (watched_l ?C)\<close>
    using in_watched unfolding H
    by (cases S)
        (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
        get_unit_init_clss_def)
  have \<open>xj \<ge> 2\<close> and \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def unit_prop_body_wl_find_unwatched_inv_def
    by (cases S; auto simp: watched_by_app_def)+

  then have L_in_unwatched: \<open>L \<in> set (unwatched_l ?C)\<close>
    by (auto simp: in_set_drop_conv_nth intro!: exI[of _ xj])
  have \<open>distinct_mset_set (mset ` set (tl (get_clauses_wl S)))\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    using dist unfolding  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def set_append
    by (cases S)
        (auto simp: mset_take_mset_drop_mset image_Un drop_Suc)
  then have dist_C: \<open>distinct ?C\<close>
    using inv by (auto simp: mset_take_mset_drop_mset intro: unit_prop_body_wl_D_invD)
  then show False
    using L_in_watched L_in_unwatched by (cases ?C; cases \<open>tl ?C\<close>; cases \<open>tl (tl ?C)\<close>) auto
qed

lemma update_clause_wl_code_update_clause_wl[sepref_fr_rules]:
  \<open>(uncurry5 update_clause_wl_code, uncurry5 update_clause_wl) \<in>
    [\<lambda>(((((L, C), w), i), f), S).
      unit_prop_body_wl_D_inv S w L \<and>
      unit_prop_body_wl_D_find_unwatched_inv (Some f) C S \<and>
      C = watched_by S L ! w \<and>
      i = (if get_clauses_wl S ! C ! 0 = L then 0 else 1)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
       nat_assn *a twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry5 update_clause_wl_code, uncurry5 update_clause_wl) \<in>
    [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(((((L, C), w), i), f), S). get_clauses_wl S ! C ! f \<noteq> L)
       (\<lambda>_ (((((L, C), w), i), f), S).
           C < length (get_clauses_wl_heur S) \<and>
           f < length (get_clauses_wl_heur S ! C) \<and>
           i < length (get_clauses_wl_heur S ! C) \<and>
           nat_of_lit L < length (get_watched_wl_heur S) \<and>
           nat_of_lit (get_clauses_wl_heur S ! C ! f)
           < length (get_watched_wl_heur S) \<and>
           w < length (get_watched_wl_heur S ! nat_of_lit L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
        twl_st_heur_assn\<^sup>d)
      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow>
    hr_comp (nat_assn *a twl_st_heur_assn) (nat_rel \<times>\<^sub>f twl_st_heur)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF update_clause_wl_code update_clause_wl_heur_update_clause_wl]
    .
  have [dest]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
    if \<open>unit_prop_body_wl_D_inv S w L\<close>
    for S w L
  proof -
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
      using that unfolding twl_st_heur_def  map_fun_rel_def unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def by fast
    then  have \<open> set_mset (all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))) \<subseteq>
       set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>get_learned_wl S\<close>])
      unfolding mset_append all_lits_of_mm_union
      apply (cases S)
      by (auto simp:  mset_take_mset_drop_mset' literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def clauses_def
           drop_Suc all_lits_of_mm_union is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    then show ?thesis
      unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def by blast
  qed
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    unfolding comp_PRE_def
    apply (cases x)
    apply (clarify)
    apply (intro conjI impI allI)
    subgoal for L C w i f M N U D NP UP Q W
      using that find_unwatched_get_clause_neq_L[of f \<open>(M, N, U, D, NP, UP, Q, W)\<close> L w]
      by (auto simp add: watched_by_app_def)
    subgoal for L C w i f M N U D NP UP Q W y
      apply (subgoal_tac \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl N))\<close>)
      subgoal
        using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>tl N\<close> \<open>(W L ! w - 1)\<close> f]
        using that unfolding comp_PRE_def twl_st_heur_def  map_fun_rel_def unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def
        by (auto dest: simp: nth_tl)[]
      subgoal
        using that by auto
      done
    done
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
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


definition propagate_lit_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close>
where
  \<open>propagate_lit_wl_heur = (\<lambda>L' C i (M, N, U, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats).
      let N' = list_update N C (swap (N!C) 0 (fast_minus 1 i)) in
      (Propagated L' C # M, N', U, D, add_mset (-L') Q, W, vm, \<phi>, clvls, cach, lbd,
         incr_propagation stats))\<close>

lemma propagate_lit_wl_heur_propagate_lit_wl:
  \<open>(uncurry3 (RETURN oooo propagate_lit_wl_heur), uncurry3 (RETURN oooo propagate_lit_wl)) \<in>
  [\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None]\<^sub>f
  Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
      vmtf_consD)

sepref_thm propagate_lit_wl_code
  is \<open>uncurry3 (RETURN oooo (PR_CONST propagate_lit_wl_heur))\<close>
  :: \<open>[\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
       1 - i < length (get_clauses_wl_heur S ! C) \<and> i \<le> 1 \<and>
       C < length (get_clauses_wl_heur S)]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def twl_st_heur_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
  by sepref


concrete_definition (in -) propagate_lit_wl_code
  uses isasat_input_bounded_nempty.propagate_lit_wl_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_lit_wl_code_def

lemmas propagate_lit_wl_code[sepref_fr_rules] =
  propagate_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma propagate_lit_wl_code_propagate_lit_wl[sepref_fr_rules]:
  \<open>(uncurry3 propagate_lit_wl_code, uncurry3 (RETURN oooo propagate_lit_wl)) \<in>
    [\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> L \<in> snd ` D\<^sub>0 \<and> get_conflict_wl S = None \<and>
          1 - i < length (get_clauses_wl S ! C) \<and> i \<le> 1 \<and> C < length (get_clauses_wl S)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun \<in>
     [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None)
       (\<lambda>_ (((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
          1 - i < length (get_clauses_wl_heur S ! C) \<and> i \<le> 1 \<and> C < length (get_clauses_wl_heur S))
       (\<lambda>_. True)]\<^sub>a hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d)
                      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow> hr_comp twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propagate_lit_wl_code[unfolded PR_CONST_def]
       propagate_lit_wl_heur_propagate_lit_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
    by (auto simp: image_image)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
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

lemma undefined_lit_polarity_st_iff:
   \<open>undefined_lit (get_trail_wl S) L \<longleftrightarrow> polarity_st S L \<noteq> Some True \<and> polarity_st S L \<noteq> Some False\<close>
  by (auto simp: polarity_st_def polarity_def)

lemma find_unwatched_le_length:
  \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_st S (watched_by_app S L C)\<close>
  for S L C xj
  using that unfolding find_unwatched_wl_st_def find_unwatched_l_def
  by (cases S) auto

lemma find_unwatched_in_D\<^sub>0: \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in> snd ` D\<^sub>0\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_st S (watched_by_app S L C)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof -
  have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover {
    have xj: \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
      using find_unw by (cases S) (auto simp: find_unwatched_wl_st_def find_unwatched_l_def)
    have \<open>watched_by_app S L C < length (get_clauses_wl S)\<close> \<open>watched_by_app S L C > 0\<close>
      using inv by (blast intro: unit_prop_body_wl_D_invD)+
    then have \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
      using xj
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset
          in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def nth_in_set_tl
          intro!: bexI[of _ \<open>get_clauses_wl S ! watched_by_app S L C\<close>])
    then have \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))\<close>
      apply (subst (asm)(3) append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
      unfolding mset_append
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset'
          all_lits_of_mm_union drop_Suc) }
  ultimately show ?thesis
    by (auto simp: image_image is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
qed

end

text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

context isasat_input_bounded_nempty
begin

context
begin

lemma unit_propagation_inner_loop_body_wl_D_helper:
  \<open>unit_prop_body_wl_D_inv b ba a \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl b)\<close>
  unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
  by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[of _ \<open>Some (a, ba)\<close>])
    auto


sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_assn\<close>
  supply
    if_splits[split] unit_prop_body_wl_D_invD[intro,dest]
    watched_by_app_def[symmetric,simp]
    access_lit_in_clauses_def[simp] unit_prop_body_wl_D_invD'[intro]
    length_rll_def[simp] find_unwatched_not_tauto[dest]
    unit_propagation_inner_loop_body_wl_D_helper[intro]
  supply undefined_lit_polarity_st_iff[iff]
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_app_def[symmetric] access_lit_in_clauses_def[symmetric]
    find_unwatched_l_find_unwatched_wl_s
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    find_unwatched_wl_st_heur_def[symmetric] polarity_st_def[symmetric]
    set_conflict_wl'_alt_def[symmetric] fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

end

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_D.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

sepref_register unit_propagation_inner_loop_body_wl_D

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit Propagation, Inner Loop\<close>

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur = (\<lambda>(M, N, U, D, Q, W, _) L. length (W ! nat_of_lit L))\<close>

lemma length_ll_fs_heur_length_ll_fs:
    \<open>(uncurry (RETURN oo length_ll_fs_heur), uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_heur \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: length_ll_fs_def length_ll_fs_heur_def twl_st_heur_def map_fun_rel_def)

lemma (in -) get_watched_wl_heur_def: \<open>get_watched_wl_heur = (\<lambda>(M, N, U, D, Q, W, _). W)\<close>
  by (intro ext, rename_tac x, case_tac x) (auto intro!: ext)

sepref_thm length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_def get_watched_wl_heur_def twl_st_heur_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) length_ll_fs_heur_code
   uses isasat_input_bounded_nempty.length_ll_fs_heur_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_heur_code_def

lemmas length_ll_fs_heur_code_refine[sepref_fr_rules] =
   length_ll_fs_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma length_ll_fs_heur_code_length_ll_fs[sepref_fr_rules]:
  \<open>(uncurry length_ll_fs_heur_code, uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
thm hfref_compI_PRE_aux[OF length_ll_fs_heur_code_refine length_ll_fs_heur_length_ll_fs]
  have H: \<open>?fun \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f Id) (\<lambda>(S, L). L \<in> snd ` D\<^sub>0)
    (\<lambda>_ (S, L). nat_of_lit L < length (get_watched_wl_heur S))
    (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                   (twl_st_heur \<times>\<^sub>f Id) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_ll_fs_heur_code_refine length_ll_fs_heur_length_ll_fs]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
    by (auto simp: image_image map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
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

lemma length_ll_fs_alt_def: \<open>length_ll_fs S L = length_ll_f (watched_by S) L\<close>
  by (cases S) (auto simp: length_ll_fs_def length_ll_f_def)

sepref_register unit_propagation_inner_loop_wl_loop_D

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric] length_ll_fs_alt_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None length_ll_fs_def[symmetric]
  supply [[goals_limit=1]]
  by sepref


concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit propagation, Outer Loop\<close>

definition (in -) select_and_remove_from_literals_to_update_wl_heur
  :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wl_heur_W_list \<times> _\<close> where
  \<open>select_and_remove_from_literals_to_update_wl_heur =
     (\<lambda>(M, N, U, D, Q, W, other).  ((M, N, U, D, tl Q, W, other), hd Q))\<close>

definition get_literals_to_update_wl where
   \<open>get_literals_to_update_wl = (\<lambda>(M, N, U, D, NP, UP, Q, W). Q)\<close>

definition get_literals_to_update_wl_heur_W_list where
   \<open>get_literals_to_update_wl_heur_W_list = (\<lambda>(M, N, U, D, Q, W, _). Q)\<close>

definition literals_to_update_wl_empty_heur :: \<open>twl_st_wl_heur_W_list \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty_heur = (\<lambda>(M, N, U, D, Q, W, oth). Q = [])\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>(RETURN o select_and_remove_from_literals_to_update_wl_heur,
    select_and_remove_from_literals_to_update_wl) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty S]\<^sub>f
      (twl_st_wl_heur_W_list_rel O twl_st_heur) \<rightarrow>
       \<langle>(twl_st_wl_heur_W_list_rel O twl_st_heur) \<times>\<^sub>r Id\<rangle>nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
  select_and_remove_from_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  twl_st_wl_heur_W_list_rel_twl_st_rel get_literals_to_update_wl_def
  literals_to_update_wl_empty_def
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y,
      case_tac \<open>get_literals_to_update_wl_heur_W_list y\<close>)
  unfolding get_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  by (auto intro!: RETURN_SPEC_refine simp: nempty_list_mset_rel_iff)

sepref_thm select_and_remove_from_literals_to_update_wl_code
  is \<open>RETURN o select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>[\<lambda>S. \<not>literals_to_update_wl_empty_heur S]\<^sub>a twl_st_heur_W_list_assn\<^sup>d \<rightarrow> twl_st_heur_W_list_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) select_and_remove_from_literals_to_update_wl_code
   uses isasat_input_bounded_nempty.select_and_remove_from_literals_to_update_wl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_code_def

lemmas select_and_remove_from_literals_to_update_wl_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem select_and_remove_from_literals_to_update_wl_code_select_and_remove_from_literals_to_update_wl
  [sepref_fr_rules]:
  \<open>(select_and_remove_from_literals_to_update_wl_code,
     select_and_remove_from_literals_to_update_wl)
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty S]\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *a
          unat_lit_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun
    \<in> [comp_PRE (twl_st_wl_heur_W_list_rel O twl_st_heur)
         (\<lambda>S. \<not> literals_to_update_wl_empty S)
         (\<lambda>_ S. \<not> literals_to_update_wl_empty_heur S)
         (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_heur_W_list_assn\<^sup>d) (twl_st_wl_heur_W_list_rel O twl_st_heur) \<rightarrow>
      hr_comp (twl_st_heur_W_list_assn *a unat_lit_assn)
           ((twl_st_wl_heur_W_list_rel O twl_st_heur) \<times>\<^sub>f Id)\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl_code_refine
      select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def literals_to_update_wl_empty_heur_def
      literals_to_update_wl_empty_def twl_st_wl_heur_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm literals_to_update_wl_empty_heur_code
  is \<open>RETURN o literals_to_update_wl_empty_heur\<close>
  :: \<open>twl_st_heur_W_list_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) literals_to_update_wl_empty_heur_code
   uses isasat_input_bounded_nempty.literals_to_update_wl_empty_heur_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_empty_heur_code_def

lemmas literals_to_update_wl_empty_heur_code_refine[sepref_fr_rules] =
   literals_to_update_wl_empty_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma literals_to_update_wl_empty_heur_literals_to_update_wl_empty:
  \<open>(RETURN o literals_to_update_wl_empty_heur, RETURN o literals_to_update_wl_empty) \<in>
    twl_st_wl_heur_W_list_rel O twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding literals_to_update_wl_empty_heur_def literals_to_update_wl_empty_def
    twl_st_wl_heur_W_list_rel_twl_st_rel
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: Nil_list_mset_rel_iff empty_list_mset_rel_iff)

lemma literals_to_update_wl_empty_heur_code_literals_to_update_wl_empty[sepref_fr_rules]:
  \<open>(literals_to_update_wl_empty_heur_code, RETURN \<circ> literals_to_update_wl_empty)
     \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_empty_heur_code_refine[FCOMP
      literals_to_update_wl_empty_heur_literals_to_update_wl_empty]
  unfolding twl_st_assn_W_list[symmetric]
  .

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def
    literals_to_update_wl_literals_to_update_wl_empty
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D
   uses isasat_input_bounded_nempty.unit_propagation_outer_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_def

lemmas unit_propagation_outer_loop_wl_D[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end

end