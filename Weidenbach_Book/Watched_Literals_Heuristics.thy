theory Watched_Literals_Heuristics
  imports Watched_Literals_Watch_List_Code_Common IsaSAT_Setup
begin

fun watched_by_int :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> watched\<close> where
  \<open>watched_by_int (M, N, U, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat literal \<Rightarrow> nat list)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, _, W) = W\<close>

fun (in -) get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat list list\<close> where
  \<open>get_watched_wl_heur (_, _, _, _, _, W, _) = W\<close>


definition watched_by_app_heur_pre where
  \<open>watched_by_app_heur_pre = (\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L))\<close>

definition (in -) watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app_heur S L K = watched_by_int S L ! K\<close>

lemma watched_by_app_heur_alt_def:
  \<open>watched_by_app_heur = (\<lambda>(M, N, U, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>
  by (auto simp: watched_by_app_heur_def intro!: ext)

definition (in -) watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>


(* TODO Move *)
definition polarity_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st_heur S = polarity (get_trail_wl_heur S)\<close>

abbreviation (in isasat_input_ops) polarity_st_pre where
\<open>polarity_st_pre \<equiv> \<lambda>(M, L). L \<in> snd ` D\<^sub>0\<close>

context isasat_input_bounded
begin
(* TODO Move *)
lemma polarity_st_heur_pol_polarity_st_refine[sepref_fr_rules]:
  \<open>(uncurry polarity_st_heur_pol_code, uncurry (RETURN oo polarity_st_heur)) \<in>
     [polarity_st_pre]\<^sub>a twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
proof -
  have [simp]: \<open>polarity_atm M (atm_of L) =
      (if is_pos L then polarity M L else map_option uminus (polarity M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: polarity_atm_def polarity_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry polarity_st_heur_pol, uncurry (RETURN oo polarity_st_heur)) \<in>
     [\<lambda>(_, L). L \<in> snd ` D\<^sub>0]\<^sub>f
     (trail_pol \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
       (auto simp: trail_pol_def polarity_st_def polarity_pol_def invert_pol_def
        polarity_def polarity_st_heur_def polarity_st_heur_pol_def)
  show ?thesis
    using polarity_st_heur_pol_code.refine[FCOMP 2, OF isasat_input_bounded_axioms,
      unfolded twl_st_heur_pol_assn_twl_st_heur_assn] by simp
qed
(* End Move *)

lemma unit_prop_body_wl_invD:
  fixes S w K
  defines \<open>C \<equiv> (watched_by S K) ! w\<close>
  assumes inv: \<open>unit_prop_body_wl_inv S w K\<close>
  shows \<open>distinct((get_clauses_wl S)!C)\<close> and \<open>get_conflict_wl S = None\<close>
proof -
  obtain M N U D' NE UE Q W where
     S: \<open>S = (M, N, U, D', NE, UE, Q, W)\<close>
    by (cases S)
  have
     struct_invs: \<open>twl_struct_invs (twl_st_of_wl (Some (K, w)) S)\<close> and
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
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl (Some (K, w)) S))\<close> and
      \<open>\<forall>D\<in>#learned_clss (state\<^sub>W_of (twl_st_of_wl (Some (K, w)) S)).
      \<not> tautology D\<close>
      and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl (Some (K, w)) S))\<close>
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
  obtain M N U D NE UE W Q where
    S: \<open>S = (M, N, U, D, NE, UE, Q, W)\<close>
    by (cases S)
  show lits_N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! watched_by_app S L w))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def apply -
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of _ _ M U D NE UE Q W])
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

  show S_L_W_ge_0: \<open>watched_by_app S L w > 0\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>get_conflict_wl S = None\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    struct: \<open>twl_struct_invs (twl_st_of_wl (Some (L, w)) S)\<close> and
    stgy: \<open>twl_stgy_invs (twl_st_of_wl (Some (L, w)) S)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    all_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
          (state\<^sub>W_of (twl_st_of_wl (Some (L, w)) S))\<close>
    using struct unfolding twl_struct_invs_def by fast+
  then have
     learned_tauto:
       \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of (twl_st_of_wl (Some (L, w)) S)).
           \<not> tautology s\<close> and
     dist:
        \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl (Some (L, w)) S))\<close>
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


definition (in -) find_unwatched_wl_st  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st = (\<lambda>(M, N, U, D, NE, UE, Q, W) i. do {
    find_unwatched_l M (N ! i)
  })\<close>

lemma find_unwatched_l_find_unwatched_wl_s:
  \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S ! C) = find_unwatched_wl_st S C\<close>
  by (cases S) (auto simp: find_unwatched_wl_st_def)

definition (in -) find_unwatched :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a clause_l \<Rightarrow> (nat option) nres\<close> where
\<open>find_unwatched M C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
      (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and>
       j < length C \<and> j \<ge> 2))\<^esup>
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

definition (in isasat_input_ops) find_unwatched_wl_st_heur_pre where
  \<open>find_unwatched_wl_st_heur_pre =
     (\<lambda>(S, i). i < length (get_clauses_wl_heur S) \<and> i > 0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S)\<close>

definition (in isasat_input_ops) find_unwatched_wl_st_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st_heur = (\<lambda>(M, N, U, D, Q, W, vm, \<phi>) i. do {
    find_unwatched M (N ! i)
  })\<close>


lemma (in -) find_unwatched:
  assumes \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close>
  shows \<open>find_unwatched M C \<le> \<Down> Id (find_unwatched_l M C)\<close>
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
    find_unwatched[simplified])


lemmas unit_prop_body_wl_D_invD' =
  unit_prop_body_wl_D_invD[of \<open>(M, N, U, D, NE, UE, WS, Q)\<close> for M N U D NE UE WS Q,
   unfolded watched_by_app_def,
    simplified] unit_prop_body_wl_D_invD(7)


definition (in isasat_input_ops) set_conflict_wl' :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl' =
      (\<lambda>C (M, N, U, D, NE, UE, Q, W). (M, N, U, Some (mset (N!C)), NE, UE, {#}, W))\<close>

lemma set_conflict_wl'_alt_def:
  \<open>set_conflict_wl' i S = set_conflict_wl (get_clauses_wl S ! i) S\<close>
  by (cases S) (auto simp: set_conflict_wl'_def set_conflict_wl_def)

definition (in isasat_input_ops) set_conflict_wl_heur_pre where
  \<open>set_conflict_wl_heur_pre =
     (\<lambda>(C, S). get_conflict_wl_heur S = None \<and> C < length (get_clauses_wl_heur S) \<and>
        distinct (get_clauses_wl_heur S ! C) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl_heur S ! C)) \<and>
        \<not> tautology (mset (get_clauses_wl_heur S ! C)) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl_heur S) \<and>
        no_dup (get_trail_wl_heur S))\<close>

definition (in isasat_input_ops) set_conflict_wl_heur
  :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>set_conflict_wl_heur = (\<lambda>C (M, N, U, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, stats). do {
    let n = zero_uint32_nat;
    (D, clvls, lbd) \<leftarrow> set_conflict_m M N C D n lbd;
    RETURN (M, N, U, D, {#}, W, vmtf, \<phi>, clvls, cach, lbd, incr_conflict stats)})\<close>


definition (in isasat_input_ops) update_clause_wl_code_pre where
  \<open>update_clause_wl_code_pre = (\<lambda>(((((L, C), w), i), f), S).
      C < length (get_clauses_wl_heur S) \<and>
      f < length (get_clauses_wl_heur S ! C) \<and>
      i < length (get_clauses_wl_heur S ! C) \<and>
      nat_of_lit L < length (get_watched_wl_heur S) \<and>
      nat_of_lit ((get_clauses_wl_heur S ! C) ! f)  < length (get_watched_wl_heur S) \<and>
      w < length (get_watched_wl_heur S ! nat_of_lit L))\<close>

definition (in isasat_input_ops) update_clause_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    (nat \<times> twl_st_wl_heur) nres\<close>
where
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
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<rightarrow>
  \<langle>nat_rel \<times>\<^sub>r twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def)

lemma length_delete_index_and_swap_ll[simp]: \<open>length (delete_index_and_swap_ll s i j) = length s\<close>
  by (auto simp: delete_index_and_swap_ll_def)

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) ! i ! j\<close>

definition (in -) access_lit_in_clauses_heur_pre where
  \<open>access_lit_in_clauses_heur_pre =
      (\<lambda>((S, i), j). i < length (get_clauses_wl_heur S) \<and> j < length_rll (get_clauses_wl_heur S) i)\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur S i j = get_clauses_wl_heur S ! i ! j\<close>

lemma access_lit_in_clauses_heur_alt_def:
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j.  N ! i ! j)\<close>
  by (auto simp: access_lit_in_clauses_heur_def intro!: ext)

lemma
  find_unwatched_not_tauto:
    \<open>\<not>tautology(mset (get_clauses_wl S ! watched_by_app S L C))\<close>
    (is ?tauto is \<open>\<not>tautology (?D)\<close> is \<open>\<not>tautology (mset ?C)\<close>)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv None (watched_by_app S L C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    val: \<open>polarity_st S (get_clauses_wl S ! watched_by_app S L C !
         (1 - (if access_lit_in_clauses S (watched_by_app S L C) 0 = L then 0 else 1))) =
          Some False\<close>
      (is \<open>polarity_st _ (_ ! _ ! ?i) = Some False\<close>)
  for S C xj L
proof  -
  obtain M N U D NE UE WS Q where
    S: \<open>S = (M, N, U, D, NE, UE, WS, Q)\<close>
    by (cases S)

  have \<open>consistent_interp
       (lits_of_l (trail (state\<^sub>W_of (twl_st_of_wl (Some (L, C)) S))))\<close>
    \<open>no_dup (trail (state\<^sub>W_of (twl_st_of_wl (Some (L, C)) S)))\<close> and
    valid: \<open>valid_enqueued (twl_st_of_wl (Some (L, C)) S)\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    by (cases S) (auto)

  have
    \<open>twl_list_invs (st_l_of_wl (Some (L, C)) S)\<close> and
    C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    \<open>no_duplicate_queued (twl_st_of_wl (Some (L, C)) S)\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
  have \<open>\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S ! (watched_by S L ! C))).
         - L \<in> lits_of_l (get_trail_wl S)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def watched_by_app_def
    by auto
  moreover {
    have
      \<open>twl_list_invs (st_l_of_wl (Some (L, C)) S)\<close> and
      \<open>C < length (watched_by S L)\<close> and
      \<open>get_conflict_wl S = None\<close> and
      \<open>no_duplicate_queued (twl_st_of_wl (Some (L, C)) S)\<close>
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
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    by (auto simp: watched_by_app_def)
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
    \<open>False\<close> (is ?neq)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv (Some xj) (watched_by S L ! C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    eq: \<open>get_clauses_wl S ! watched_by_app S L C ! xj = L\<close>
  for S C xj L
proof -
  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm A) \<longleftrightarrow> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = atms_of_mm A\<close> for A
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def by metis

  let ?C = \<open>get_clauses_wl S ! watched_by_app S L C\<close>
  let ?L = \<open>get_clauses_wl S ! watched_by_app S L C ! xj\<close>
  have corr: \<open>correct_watching S\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm
      (state\<^sub>W_of (twl_st_of_wl (Some (L, C)) S))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
       (state\<^sub>W_of (twl_st_of_wl (Some (L, C)) S))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    unfolding correct_watching.simps twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
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
  ultimately have
    \<open>L \<in># all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)) + get_unit_init_clss S)\<close>
    using alien
    by (cases S)
        (auto 5 5 simp: get_unit_init_clss_def clauses_def mset_take_mset_drop_mset drop_Suc
        mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset.no_strange_atm_def
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym in_all_lits_of_mm_ain_atms_of_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        dest: in_atms_of_mset_takeD)
    then have H: \<open>mset (watched_by S L) =
      mset_set {x. Suc 0 \<le> x \<and> x < length (get_clauses_wl S) \<and>
         L \<in> set (watched_l (get_clauses_wl S ! x))}\<close>
      using corr by (cases S)
          (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
          get_unit_init_clss_def)
  have L_in_watched: \<open>L \<in> set (watched_l ?C)\<close>
    using in_watched unfolding H
    by (cases S)
        (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
        get_unit_init_clss_def)
  have \<open>xj \<ge> 2\<close> and \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def
    by (cases S; auto simp: watched_by_app_def)+

  then have L_in_unwatched: \<open>L \<in> set (unwatched_l ?C)\<close>
    using eq by (auto simp: in_set_drop_conv_nth intro!: exI[of _ xj])
  have \<open>distinct_mset_set (mset ` set (tl (get_clauses_wl S)))\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    using dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def set_append
    by (cases S)
        (auto simp: mset_take_mset_drop_mset image_Un drop_Suc)
  then have dist_C: \<open>distinct ?C\<close>
    using inv by (auto simp: mset_take_mset_drop_mset intro: unit_prop_body_wl_D_invD)
  then show False
    using L_in_watched L_in_unwatched by (cases ?C; cases \<open>tl ?C\<close>; cases \<open>tl (tl ?C)\<close>) auto
qed


definition (in isasat_input_ops) propagate_lit_wl_heur_pre where
  \<open>propagate_lit_wl_heur_pre =
     (\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
       1 - i < length (get_clauses_wl_heur S ! C) \<and> i \<le> 1 \<and>
       C < length (get_clauses_wl_heur S))\<close>

definition (in isasat_input_ops) propagate_lit_wl_heur
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


lemma undefined_lit_polarity_st_iff:
   \<open>undefined_lit (get_trail_wl S) L \<longleftrightarrow>
      polarity_st S L \<noteq> Some True \<and> polarity_st S L \<noteq> Some False\<close>
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

definition (in isasat_input_ops) unit_prop_body_wl_heur_inv where
  \<open>unit_prop_body_wl_heur_inv S w L \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_D_inv S' w L)\<close>

definition (in isasat_input_ops) unit_prop_body_wl_D_find_unwatched_heur_inv where
  \<open>unit_prop_body_wl_D_find_unwatched_heur_inv f C S \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_D_find_unwatched_inv f C S')\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_body_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> twl_st_wl_heur) nres\<close>
where
  \<open>unit_propagation_inner_loop_body_wl_heur L w S = do {
      ASSERT(unit_prop_body_wl_heur_inv S w L);
      ASSERT(watched_by_app_heur_pre ((S, L), w));
      let C = watched_by_app_heur S L w;
      ASSERT(access_lit_in_clauses_heur_pre ((S, C), 0));
      let i = (if access_lit_in_clauses_heur S C 0 = L then 0 else 1);
      ASSERT(access_lit_in_clauses_heur_pre ((S, C), 1 - i));
      let L' = access_lit_in_clauses_heur S C (1 - i);
      ASSERT(polarity_st_pre (S, L'));
      let val_L' = polarity_st_heur S L';
      if val_L' = Some True
      then RETURN (w+1, S)
      else do {
        ASSERT(find_unwatched_wl_st_heur_pre (S, C));
        f \<leftarrow> find_unwatched_wl_st_heur S C;
        ASSERT (unit_prop_body_wl_D_find_unwatched_heur_inv f C S);
        case f of
          None \<Rightarrow>
            if val_L' = Some False
            then do {
              ASSERT(set_conflict_wl_heur_pre (C, S));
              S \<leftarrow> set_conflict_wl_heur C S;
              RETURN (w+1, S)}
            else do {
              ASSERT(propagate_lit_wl_heur_pre (((L', C), i), S));
              let S = propagate_lit_wl_heur L' C i S;
              RETURN (w+1, S)}
        | Some f \<Rightarrow> do {
            ASSERT(update_clause_wl_code_pre (((((L, C), w), i), f), S));
            update_clause_wl_heur L C w i f S
          }
      }
   }\<close>

lemma twl_st_heur_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows
     \<open>get_clauses_wl_heur S = get_clauses_wl S'\<close>
     \<open>get_trail_wl_heur S = get_trail_wl S'\<close>
     \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> watched_by_int S C = watched_by S' C\<close>
  using assms unfolding twl_st_heur_def by (auto simp: map_fun_rel_def)



ML \<open>
signature MORE_REFINEMENT = sig
  val down_converse: Proof.context -> thm -> thm
end

structure More_Refinement: MORE_REFINEMENT = struct
  val unfold_refine = (fn context => Local_Defs.unfold (context)
   @{thms refine_rel_defs nres_rel_def in_pair_collect_simp fref_def})
  val unfold_Ball = (fn context => Local_Defs.unfold (context)
    @{thms Ball2_split_def all_to_meta})
  val replace_ALL_by_meta = (fn context => fn thm => Object_Logic.rulify context thm)
  val down_converse = (fn context =>
    replace_ALL_by_meta context o (unfold_Ball context) o (unfold_refine context))
end
\<close>
attribute_setup "to_\<Down>" = \<open>
    Scan.succeed (Thm.rule_attribute [] (More_Refinement.down_converse o Context.proof_of))
  \<close> "convert theorem from @{text \<rightarrow>}-form to @{text \<Down>}-form."

method "to_\<Down>" =
   (unfold refine_rel_defs nres_rel_def in_pair_collect_simp fref_def uncurry_def;
   unfold Ball2_split_def all_to_meta fref_def uncurry_def;
   intro allI impI)


lemma set_conflict_wl_heur_set_conflict_wl':
  \<open>(uncurry set_conflict_wl_heur, uncurry (RETURN oo set_conflict_wl')) \<in>
    nat_rel \<times>\<^sub>r twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
    (auto simp: twl_st_heur_def set_conflict_wl_heur_def set_conflict_wl'_def
        bind_RES_RETURN2_eq RETURN_def RES_RES2_RETURN_RES
        counts_maximum_level_def RES_RETURN_RES3 RES_RES_RETURN_RES RES_RES3_RETURN_RES
        set_conflict_m_def
      intro!: RES_refine)

lemma (in -)split_in_curry:
  \<open>(uncurry f, uncurry g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y'. P (x', y') \<Longrightarrow> ((x, y), (x', y')) \<in> A \<Longrightarrow> f x y \<le> \<Down> B (g x' y'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma (in -)split_in_curry2:
  \<open>(uncurry2 f, uncurry2 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z'. P ((x', y'), z') \<Longrightarrow> (((x, y), z), ((x', y'), z')) \<in> A\<Longrightarrow>
         f x y z \<le> \<Down> B (g x' y' z'))\<close>
  for f g :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd nres\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma (in -)split_in_curry3:
  \<open>(uncurry3 f, uncurry3 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z' a a'. P (((x', y'), z'), a') \<Longrightarrow>
        ((((x, y), z), a), (((x', y'), z'), a')) \<in> A \<Longrightarrow>
         f x y z a \<le> \<Down> B (g x' y' z' a'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma (in -)split_in_curry4:
  \<open>(uncurry4 f, uncurry4 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z' a a' b b'. P ((((x', y'), z'), a'), b') \<Longrightarrow>
        (((((x, y), z), a), b), ((((x', y'), z'), a'), b')) \<in> A \<Longrightarrow>
         f x y z a b \<le> \<Down> B (g x' y' z' a' b'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma (in -)split_in_curry5:
  \<open>(uncurry5 f, uncurry5 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z' a a' b b' c c'. P (((((x', y'), z'), a'), b'), c') \<Longrightarrow>
        ((((((x, y), z), a), b), c), (((((x', y'), z'), a'), b'), c')) \<in> A \<Longrightarrow>
         f x y z a b c \<le> \<Down> B (g x' y' z' a' b' c'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

declare RETURN_as_SPEC_refine[refine2 del]
lemma in_Id_in_Id_option_rel[refine]:
  \<open>(f, f') \<in> Id \<Longrightarrow> (f, f') \<in> \<langle>Id\<rangle> option_rel\<close>
  by auto

lemma unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry2 unit_propagation_inner_loop_body_wl_heur, uncurry2 unit_propagation_inner_loop_body_wl_D)
   \<in> Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>unit_prop_body_wl_D_inv T i L \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for T i L
    unfolding unit_prop_body_wl_D_inv_def by auto
  have pol_undef: \<open>polarity M L \<noteq> Some True \<Longrightarrow> polarity M L \<noteq> Some False \<Longrightarrow> defined_lit M L \<Longrightarrow>
     False\<close>
    for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (auto simp: polarity_def split: if_splits)
  have 1: \<open>RETURN (w + 1, f S') = do {S \<leftarrow> RETURN (f S'); RETURN (w + 1, S)}\<close>
    for w :: nat and S' and f
    by auto
  have watched_by_app_heur_pre: \<open>unit_prop_body_wl_heur_inv x2c x2b x1c \<Longrightarrow>
      watched_by_app_heur_pre ((x2c, x1c), x2b)\<close>
    for x2c x2b x1c
    by (auto simp: unit_prop_body_wl_heur_inv_def watched_by_app_heur_pre_def
        unit_prop_body_wl_D_inv_def twl_st_heur_def unit_prop_body_wl_inv_def
        map_fun_rel_def)
  have access_lit_in_clauses_heur_pre: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<Longrightarrow>
    x1 = (x1a, x2) \<Longrightarrow>
    y = (x1, x2a) \<Longrightarrow>
    x1b = (x1c, x2b) \<Longrightarrow>
    x = (x1b, x2c) \<Longrightarrow>
    unit_prop_body_wl_D_inv x2a x2 x1a \<Longrightarrow>
       access_lit_in_clauses_heur_pre ((x2c, watched_by_int x2c x1c ! x2b), 0)\<close>
    for x2c x2b x1c x y x1 x1a x2 x2a x1b
    using twl_struct_invs_length_clause_ge_2'[of \<open>(Some (x1c, x2))\<close> x2a \<open>(watched_by x2a x1c ! x2)\<close>]
    by (auto simp: unit_prop_body_wl_heur_inv_def access_lit_in_clauses_heur_pre_def
        unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        twl_st_heur_state_simp twl_list_invs_def length_rll_def
        simp del: twl_st_of_wl.simps get_clauses_wl.simps)
  have access_lit_in_clauses_heur_pre2: \<open>(x, y)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
       twl_st_heur \<Longrightarrow>
    x1 = (x1a, x2) \<Longrightarrow>
    y = (x1, x2a) \<Longrightarrow>
    x1b = (x1c, x2b) \<Longrightarrow>
    x = (x1b, x2c) \<Longrightarrow>
    unit_prop_body_wl_D_inv x2a x2 x1a \<Longrightarrow>
    access_lit_in_clauses_heur_pre
     ((x2c, watched_by_int x2c x1c ! x2b),
      1 -
      (if get_clauses_wl_heur x2c !
          (watched_by_int x2c x1c ! x2b) !
          0 =
          x1c
       then 0 else 1))\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c 
    using twl_struct_invs_length_clause_ge_2'[of \<open>(Some (x1c, x2))\<close> x2a \<open>(watched_by x2a x1c ! x2)\<close>]
    by (auto simp: access_lit_in_clauses_heur_pre_def
        unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        twl_st_heur_state_simp twl_list_invs_def length_rll_def
        simp del: twl_st_of_wl.simps get_clauses_wl.simps)
  note find_unw = find_unwatched_wl_st_heur_find_unwatched_wl_s[THEN split_in_curry]
      set_conflict_wl_heur_set_conflict_wl'[THEN split_in_curry, unfolded comp_def]
      propagate_lit_wl_heur_propagate_lit_wl[THEN split_in_curry3, unfolded comp_def]
      update_clause_wl_heur_update_clause_wl[THEN split_in_curry5, unfolded comp_def]
  show ?thesis
    supply [[goals_limit=1]]
    apply (intro frefI nres_relI)
    unfolding unit_propagation_inner_loop_body_wl_heur_def unit_propagation_inner_loop_body_wl_D_def
      uncurry_def find_unwatched_l_find_unwatched_wl_s 1 polarity_st_heur_def
      watched_by_app_heur_def access_lit_in_clauses_heur_def
    unfolding set_conflict_wl'_alt_def[symmetric]
    apply (refine_rcg find_unw)
    subgoal
      unfolding unit_prop_body_wl_heur_inv_def by fastforce
    subgoal by (rule watched_by_app_heur_pre)
    subgoal by (rule access_lit_in_clauses_heur_pre)
    subgoal by (rule access_lit_in_clauses_heur_pre2)
    subgoal sorry
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by auto
    subgoal sorry
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal
      by (rule twl_struct_invs_length_clause_ge_2)
        (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c f fa
      unfolding unit_prop_body_wl_D_find_unwatched_heur_inv_def
      by (rule exI[of _ x2a])
         (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal sorry
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal sorry
    subgoal by (auto simp: twl_st_heur_state_simp split: if_splits dest!: pol_undef)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal sorry
    subgoal by (auto simp: twl_st_heur_state_simp watched_by_app_def
          intro!: find_unwatched_get_clause_neq_L)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
qed

end

end