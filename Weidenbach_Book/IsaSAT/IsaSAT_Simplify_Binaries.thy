theory IsaSAT_Simplify_Binaries
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Simplify_Binaries_Defs
    IsaSAT_Simplify_Units
    IsaSAT_Restart
begin

section \<open>Simplification of binary clauses\<close>

text \<open>Special handling of binary clauses is required to avoid special cases of units in the general
forward subsumption algorithm (which, as of writing, does not exist).\<close>



 lemma all_atms_st_add_remove[simp]:
   \<open>C \<in># dom_m N \<Longrightarrow> all_atms_st (M, fmdrop C N, D, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C)) NS, US,  N0, U0, Q, W) =
      all_atms_st  (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
   \<open>C \<in># dom_m N \<Longrightarrow> all_atms_st (M, fmdrop C N, D, NE, UE, NEk, UEk, NS,  add_mset (mset (N \<propto> C)) US,  N0, U0, Q, W) =
      all_atms_st  (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
   \<open>C \<in># dom_m N \<Longrightarrow> all_atms_st (M, fmdrop C N, D, NE, UE, add_mset (mset (N \<propto> C)) NEk, UEk, NS, US,  N0, U0, Q, W) =
      all_atms_st  (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
   \<open>C \<in># dom_m N \<Longrightarrow> all_atms_st (M, fmdrop C N, D, NE, UE, NEk, UEk, add_mset (mset (N \<propto> C)) NS,  US,  N0, U0, Q, W) =
      all_atms_st  (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
   \<open>all_atms_st (L # M, N, D, NE, UE, NEk, UEk, NS,  US,  N0, U0, Q, W) = all_atms_st  (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
   \<open>all_atms_st (M, N, D, NE, UE, NEk, UEk, NS,  US,  N0, U0, add_mset K Q, W) = all_atms_st  (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)\<close>
  apply (auto simp: all_atms_st_def all_atms_def all_lits_def all_lits_of_mm_union all_lits_of_mm_add_mset
      distinct_mset_remove1_All dest!: multi_member_split
    simp del: all_atms_def[symmetric])
    by (metis (no_types, lifting) Watched_Literals_Clauses.ran_m_fmdrop Watched_Literals_Clauses.ran_m_mapsto_upd all_lits_of_mm_add_mset
      fmupd_same image_mset_add_mset image_mset_union union_single_eq_member)+

lemma all_atms_st_add_kep[simp]:
  \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)) \<Longrightarrow>
    set_mset (all_atms_st (M, N, D, NE, UE, add_mset {#L#} NEk, UEk, NS, US, N0, U0, Q, W)) = set_mset (all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W))\<close>
  \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W)) \<Longrightarrow>
    set_mset (all_atms_st (M, N, D, NE, UE, NEk, add_mset {#L#} UEk, NS, US, N0, U0, Q, W)) = set_mset (all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US,  N0, U0, Q, W))\<close>
  by (auto simp: all_atms_st_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n all_atms_def all_lits_def all_lits_of_mm_union all_lits_of_mm_add_mset
      all_lits_of_m_add_mset
    simp del: all_atms_def[symmetric])

lemma clss_size_corr_in_dom_red_clss_size_lcount_ge0:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow> clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<Longrightarrow> clss_size_lcount lcount \<ge> Suc 0\<close>
  apply (auto dest!: multi_member_split simp: clss_size_corr_def clss_size_def)
  by (metis member_add_mset red_in_dom_number_of_learned_ge1)


abbreviation twl_st_heur_restart_ana'' :: \<open>_\<close> where
  \<open>twl_st_heur_restart_ana'' r u ns lw  \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> learned_clss_count S \<le> u \<and> get_vmtf_heur S = ns \<and> length (get_watched_wl_heur S) = lw}\<close>

lemma isa_clause_remove_duplicate_clause_wl_clause_remove_duplicate_clause_wl:
  \<open>(uncurry isa_clause_remove_duplicate_clause_wl, uncurry clause_remove_duplicate_clause_wl) \<in> [\<lambda>(C, S). C \<in># dom_m (get_clauses_wl S)]\<^sub>f
  nat_rel \<times>\<^sub>ftwl_st_heur_restart_ana'' r u ns lw \<rightarrow>
  \<langle>twl_st_heur_restart_ana'' r u ns lw\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding isa_clause_remove_duplicate_clause_wl_def clause_remove_duplicate_clause_wl_def uncurry_def
      mop_arena_status_def nres_monad3
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k a b c d e
      unfolding arena_is_valid_clause_vdom_def
      apply (rule exI[of _ \<open>get_clauses_wl x2\<close>], rule exI[of _ \<open>set (get_vdom e)\<close>])
      by (simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k a b c d e
      unfolding mark_garbage_pre_def arena_is_valid_clause_idx_def prod.simps
      apply (rule exI[of _ \<open>get_clauses_wl x2\<close>], rule exI[of _ \<open>set (get_vdom e)\<close>])
      by (simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k
      x2k x1l x2l x1m x2m
      by (auto simp: clause_remove_duplicate_clause_wl_pre_def clause_remove_duplicate_clause_pre_def state_wl_l_def red_in_dom_number_of_learned_ge1
        twl_st_heur_restart_def twl_st_heur_restart_ana_def clss_size_corr_in_dom_red_clss_size_lcount_ge0 arena_lifting clss_size_corr_restart_def)
    subgoal
       by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def valid_arena_extra_information_mark_to_delete' aivdom_inv_dec_remove_clause arena_lifting
         all_init_atms_fmdrop_add_mset_unit learned_clss_count_def
      dest!: in_vdom_m_fmdropD)
    done
qed


(*TODO Move*)
lemma [simp]: \<open>(S, x) \<in> state_wl_l None \<Longrightarrow>
    defined_lit (get_trail_l x) L \<longleftrightarrow> defined_lit (get_trail_wl S) L\<close>
  by (auto simp: state_wl_l_def)
(*END Move*)
 
lemma binary_clause_subres_wl_alt_def:
  \<open>binary_clause_subres_wl C L L' = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
   ASSERT (binary_clause_subres_lits_wl_pre C L L' (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
   ASSERT (L' \<in>#  \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)));
   ASSERT (L \<in>#  \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)));
   ASSERT (get_conflict_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) = None \<and> undefined_lit M L \<and> C \<in># dom_m N);
   M' \<leftarrow> cons_trail_propagate_l L 0 M;
   ASSERT (M' = Propagated L 0 # M);
   let S = (M', fmdrop C N, D, NE, UE,
      (if irred N C then add_mset {#L#} else id) NEk, (if irred N C then id else add_mset {#L#}) UEk,
      (if irred N C then add_mset (mset (N \<propto> C)) else id) NS, (if irred N C then id else add_mset (mset (N \<propto> C))) US,
       N0, U0, add_mset (-L) Q, W);
   ASSERT (set_mset (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)) = set_mset (all_init_atms_st S));
   RETURN S
 })\<close> (is \<open>?A = ?B\<close>)
 proof -
  have H: \<open>binary_clause_subres_lits_wl_pre C L L' S \<Longrightarrow> set_mset (all_atms_st S) = set_mset (all_init_atms_st S)\<close> for S
    unfolding binary_clause_subres_lits_wl_pre_def binary_clause_subres_lits_pre_def
    apply normalize_goal+
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3) by fast
  have H: \<open>binary_clause_subres_lits_wl_pre C L L' S \<longleftrightarrow> binary_clause_subres_lits_wl_pre C L L' S \<and> L' \<in>#  \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S) \<and> L \<in>#  \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S) \<and>
    undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None \<and> C \<in># dom_m (get_clauses_wl S)\<close> for S
    apply (rule iffI)
    apply simp_all
    apply (frule \<L>\<^sub>a\<^sub>l\<^sub>l_cong[OF H, symmetric])
    unfolding binary_clause_subres_lits_wl_pre_def binary_clause_subres_lits_pre_def binary_clause_subres_lits_pre_def
    apply normalize_goal+
    apply (simp add: )
    by (cases S; auto simp: all_atms_st_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits all_lits_def ran_m_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      dest!: multi_member_split)
  have [simp]: \<open>L \<in># all_init_lits x1a (x1c + x1e + x1g + x1i) \<Longrightarrow>
    set_mset (all_init_atms x1a (add_mset {#L#} (x1c + x1e + x1g + x1i))) = set_mset (all_init_atms x1a ((x1c + x1e + x1g + x1i)))\<close> for x1a x1c x1e x1g x1i
    by (auto simp: all_init_atms_def all_init_lits_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      simp del: all_init_atms_def[symmetric])
  have \<open>?A S \<le> \<Down>Id (?B S)\<close> for S
    unfolding binary_clause_subres_wl_def summarize_ASSERT_conv cons_trail_propagate_l_def nres_monad3 Let_def bind_to_let_conv
    apply (subst (2) H)
    by refine_vcg auto
  moreover have \<open>?B S \<le> \<Down>Id (?A S)\<close> for S
    unfolding binary_clause_subres_wl_def summarize_ASSERT_conv cons_trail_propagate_l_def nres_monad3 Let_def bind_to_let_conv
    apply (subst (2) H)
    by refine_vcg
     (auto simp: all_init_atms_st_def all_init_atms_fmdrop_add_mset_unit \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms)
  ultimately show ?thesis
    unfolding Down_id_eq
    by (intro ext, rule antisym)
qed

lemma isa_binary_clause_subres_isa_binary_clause_subres_wl:
  \<open>(uncurry3 isa_binary_clause_subres_wl, uncurry3 binary_clause_subres_wl)
  \<in> nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_restart_ana'' r u ns lw \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart_ana'' r u ns lw\<rangle>nres_rel\<close>
proof -
  have A: \<open>A \<in> twl_st_heur_restart_ana'' r u ns lw \<Longrightarrow> A \<in> twl_st_heur_restart_ana'' r u ns lw\<close> for A
    by auto
  note cong = trail_pol_cong option_lookup_clause_rel_cong map_fun_rel_D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
    cach_refinement_empty_cong' vdom_m_cong' vdom_m_cong'' isasat_input_bounded_cong[THEN iffD1] isasat_input_nempty_cong[THEN iffD1]
    heuristic_rel_cong empty_occs_list_cong'
  show ?thesis
    unfolding isa_binary_clause_subres_wl_def binary_clause_subres_wl_alt_def uncurry_def Let_def
      mop_arena_status_def nres_monad3
    apply (intro frefI nres_relI)
    subgoal for S T
    apply (refine_vcg cons_trail_Propagated_tr[of \<open>all_init_atms_st (snd T)\<close>, THEN fref_to_Down_curry2])
    subgoal unfolding isa_binary_clause_subres_lits_wl_pre_def twl_st_heur_restart_ana_def  by force
    subgoal by auto
    subgoal by (auto simp: DECISION_REASON_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def all_init_atms_st_def)
    subgoal for x1 x1a x1b x2 x2a x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i
    x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x1p x1q x2o x2p x2q M M'
      unfolding arena_is_valid_clause_vdom_def
      apply (rule exI[of _ \<open>get_clauses_wl x2b\<close>], rule exI[of _ \<open>set (get_vdom x2q)\<close>])
      by (simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    subgoal for x1 x1a x1b x2 x2a x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i
    x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x1p x1q x2o x2p x2q M M'
      unfolding mark_garbage_pre_def arena_is_valid_clause_idx_def prod.simps
      by (rule exI[of _ \<open>get_clauses_wl x2b\<close>], rule exI[of _ \<open>set (get_vdom x2q)\<close>])
        (simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    subgoal H
      by (auto simp: clause_remove_duplicate_clause_wl_pre_def clause_remove_duplicate_clause_pre_def state_wl_l_def red_in_dom_number_of_learned_ge1
        twl_st_heur_restart_def twl_st_heur_restart_ana_def clss_size_corr_in_dom_red_clss_size_lcount_ge0 arena_lifting
        clss_size_corr_restart_def)
    subgoal by (frule H; assumption?) (auto simp: learned_clss_count_def)
    apply (rule A)
    subgoal premises p
      using p
      apply (simp only:  twl_st_heur_restart_alt_def2 Let_def twl_st_heur_restart_ana_def in_pair_collect_simp prod.simps prod_rel_fst_snd_iff get_trail_wl.simps fst_conv snd_conv)
      apply normalize_goal+
      apply (drule cong[OF p(28)])+
      apply (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def valid_arena_extra_information_mark_to_delete' aivdom_inv_dec_remove_clause
        arena_lifting isa_vmtf_consD2 all_init_atms_st_def
      dest!: in_vdom_m_fmdropD)
      apply (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def valid_arena_extra_information_mark_to_delete' aivdom_inv_dec_remove_clause
        arena_lifting isa_vmtf_consD2 clss_size_corr_restart_def clss_size_def learned_clss_count_def
      dest!: in_vdom_m_fmdropD)
      done
     done
  done
qed


lemma deduplicate_binary_clauses_inv_wl_strengthen_def:
  \<open>deduplicate_binary_clauses_inv_wl S L (abort, i, a, T) \<longleftrightarrow> deduplicate_binary_clauses_inv_wl S L (abort, i, a, T) \<and>
  set_mset (all_init_atms_st T) = set_mset (all_init_atms_st S)\<close>
  apply (rule iffI)
  subgoal
    apply (intro conjI)
    apply (solves simp)
    unfolding deduplicate_binary_clauses_inv_wl_def prod.simps
      deduplicate_binary_clauses_inv_def
    apply normalize_goal+
    apply simp
    subgoal for xa xb xc
      apply - unfolding mem_Collect_eq prod.simps deduplicate_binary_clauses_inv_def
      using rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l[of xa xb]
        rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[of xa xb]
      by (auto simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms all_init_atms_st_alt_def)
    done
  subgoal by simp
  done

lemma deduplicate_binary_clauses_inv_wl_strengthen_def2:
  \<open>deduplicate_binary_clauses_inv_wl S L = (\<lambda>(abort, i, a, T). deduplicate_binary_clauses_inv_wl S L (abort, i, a, T) \<and>
  set_mset (all_init_atms_st T) = set_mset (all_init_atms_st S) \<and>
  set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S)))\<close>
  apply (intro ext, clarsimp simp only:)
  apply (subst deduplicate_binary_clauses_inv_wl_strengthen_def)
  apply auto
    using \<L>\<^sub>a\<^sub>l\<^sub>l_cong apply blast+
  done

definition mop_watched_by_at_init :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> 'v watcher nres\<close> where
\<open>mop_watched_by_at_init = (\<lambda>S L w. do {
   ASSERT(L \<in># all_init_lits_of_wl S);
   ASSERT(w < length (watched_by S L));
  RETURN (watched_by S L ! w)
})\<close>
lemma mop_watched_by_app_heur_mop_watched_by_at_init_ana:
   \<open>(uncurry2 mop_watched_by_app_heur, uncurry2 mop_watched_by_at_init) \<in>
    twl_st_heur_restart_ana u \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding mop_watched_by_app_heur_def mop_watched_by_at_init_def uncurry_def all_lits_def[symmetric]
    all_lits_alt_def[symmetric] twl_st_heur_restart_ana_def twl_st_heur_restart_alt_def2 Let_def
  by (intro frefI nres_relI, refine_rcg)
  (simp_all add: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) watched_by_alt_def)

lemma deduplicate_binary_clauses_wl_alt_def:
\<open>deduplicate_binary_clauses_wl L S = do {
    ASSERT (deduplicate_binary_clauses_pre_wl L S);
    ASSERT (L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S));
    let CS = (\<lambda>_::nat literal. None);
    let l = length (watched_by S L);
    let val = polarity (get_trail_wl S) L;
    (_, _, _, S) \<leftarrow> WHILE\<^sub>T\<^bsup>deduplicate_binary_clauses_inv_wl S L\<^esup> (\<lambda>(abort, i, CS, S). \<not>abort \<and> i < l \<and> get_conflict_wl S = None)
      (\<lambda>(abort, i, CS, S).
      do {
         (C,L', b) \<leftarrow> mop_watched_by_at_init S L i;
         ASSERT (L'  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S));
         let st = C \<in># dom_m (get_clauses_wl S);
         if \<not>st \<or> \<not>b then
           RETURN (abort, i+1, CS, S)
         else do {
           let _ = polarity (get_trail_wl S) L';
           if defined_lit (get_trail_wl S) L' then do {
             U \<leftarrow> simplify_clause_with_unit_st_wl C S;
             ASSERT (set_mset (all_init_atms_st U) = set_mset (all_init_atms_st S));
             ASSERT (L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st U));
             let _ = polarity (get_trail_wl U) L;
             RETURN (defined_lit (get_trail_wl U) L, i+1, CS, U)
           }
           else do {
             let c = CS L';
             let _ = CS L';
             if c \<noteq> None then do {
               let C' = (if \<not>snd (the c) \<longrightarrow> \<not>irred (get_clauses_wl S) C then C else fst (the c));
               let CS = (if \<not>snd (the c) \<longrightarrow> \<not>irred (get_clauses_wl S) C then CS else CS (L' := Some (C, irred (get_clauses_wl S) C)));
               ASSERT (C' \<in># dom_m (get_clauses_wl S));
               S \<leftarrow> clause_remove_duplicate_clause_wl C' S;
               RETURN (abort, i+1, CS, S)
             } else do {
               let c = CS (-L');
               if CS (-L') \<noteq> None then do {
                 S \<leftarrow> binary_clause_subres_wl C L (-L') S;
                 RETURN (True, i+1, CS, S)
               } else do {
                 let CS' = CS (L' := Some (C, irred (get_clauses_wl S) C));
                 RETURN (abort, i+1, CS', S)
               }
             }
          }
        }
      })
      (defined_lit (get_trail_wl S) L, 0, CS, S);
   let CS = (\<lambda>_::nat literal. None);
   RETURN S
}\<close> (is \<open>?A = ?B\<close>)
proof -
  have H: \<open>a = b \<Longrightarrow> (a, b) \<in> Id\<close> \<open>x =y \<Longrightarrow> x \<le> \<Down>Id y\<close> for a b x y
    by auto
  have \<open>?A \<le> \<Down> Id ?B\<close>
    supply [[goals_limit=1]]
    unfolding Let_def deduplicate_binary_clauses_wl_def bind_to_let_conv mop_watched_by_at_init_def
      nres_monad3
    by (refine_vcg H(1); (rule H refl)?; simp)
  moreover have \<open>?B \<le> \<Down>Id ?A\<close>
    unfolding Let_def deduplicate_binary_clauses_wl_def bind_to_let_conv mop_watched_by_at_init_def
      nres_monad3
    apply (refine_vcg H(1); (rule H)?)
    subgoal
      unfolding deduplicate_binary_clauses_pre_wl_def deduplicate_binary_clauses_pre_def
      apply normalize_goal+
      by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits all_init_lits_of_wl_def all_init_lits_def
        IsaSAT_Setup.get_unit_init_clss_wl_alt_def ac_simps \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i
      apply (subst (asm) deduplicate_binary_clauses_inv_wl_def)
      unfolding  deduplicate_binary_clauses_inv_alt_def case_prod_beta
      apply normalize_goal+
      apply simp
      subgoal for xa xb xc xd
      apply - unfolding mem_Collect_eq prod.simps
      apply normalize_goal+
      using rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l[of xa xb]
        rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[of xa xb]
      by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4))
      done
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i
      apply (subst (asm) deduplicate_binary_clauses_inv_wl_def)
      unfolding  deduplicate_binary_clauses_inv_alt_def case_prod_beta
      apply normalize_goal+
      apply simp
      subgoal for xa xb xc xd
      apply - unfolding mem_Collect_eq prod.simps
      apply normalize_goal+
      using rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l[of xa xb]
        rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[of xa xb]
      by (auto simp add: literals_are_\<L>\<^sub>i\<^sub>n'_def  blits_in_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms dest!: multi_member_split nth_mem)
      done
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i
      apply (subst (asm) deduplicate_binary_clauses_inv_wl_def)
      unfolding  deduplicate_binary_clauses_inv_alt_def case_prod_beta
      apply normalize_goal+
      apply simp
      subgoal for xa xb xc xd
      apply - unfolding mem_Collect_eq prod.simps
      apply normalize_goal+
      using rtranclp_cdcl_twl_inprocessing_l_all_init_lits_of_l[of xa xb]
        rtranclp_cdcl_twl_inprocessing_l_all_learned_lits_of_l[of xa xb]
      by (auto simp add: literals_are_\<L>\<^sub>i\<^sub>n'_def  blits_in_\<L>\<^sub>i\<^sub>n'_def watched_by_alt_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms dest!: multi_member_split nth_mem)
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      apply (subst (asm) deduplicate_binary_clauses_inv_wl_strengthen_def2)
      apply (clarsimp dest!: )
      apply (drule \<L>\<^sub>a\<^sub>l\<^sub>l_cong)
      by presburger
    subgoal by auto
    subgoal by auto
    subgoal
      unfolding case_prod_beta deduplicate_binary_clauses_inv_wl_def
      deduplicate_binary_clauses_inv_def deduplicate_binary_clauses_correctly_marked_def
      by normalize_goal+
         (auto split: if_splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  ultimately show ?thesis unfolding Down_id_eq by (rule antisym)
qed



lemma deduplicate_binary_clauses_pre_wl_in_all_atmsD:
  \<open>deduplicate_binary_clauses_pre_wl L S \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S)\<close>
   \<open>deduplicate_binary_clauses_pre_wl L S \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close>
proof -
  assume \<open>deduplicate_binary_clauses_pre_wl L S\<close>
  then show \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S)\<close>
    unfolding deduplicate_binary_clauses_pre_wl_def deduplicate_binary_clauses_pre_def apply -
    apply normalize_goal+
    by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits all_init_lits_of_wl_def all_init_lits_def
      IsaSAT_Setup.get_unit_init_clss_wl_alt_def ac_simps \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms)
  then show \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close>
    using \<L>\<^sub>a\<^sub>l\<^sub>l_init_all by blast
qed


lemma isa_deduplicate_binary_clauses_mark_duplicated_binary_clauses_as_garbage_wl:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana'' r u ns lw\<close> \<open>(L,L')\<in> nat_lit_lit_rel\<close> and
    \<open>(CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = (length (get_watched_wl_heur S))}\<close> (is \<open>_ \<in> ?CS\<close>)
  shows \<open>isa_deduplicate_binary_clauses_wl L CS S \<le>
    \<Down>{((CS, T), T'). (T,T') \<in> twl_st_heur_restart_ana'' r u ns lw \<and> (CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = (length (get_watched_wl_heur S))}}
      (deduplicate_binary_clauses_wl L' S')\<close>
proof -
  have [simp]: \<open>L' = L\<close>
    using assms by auto
  have [simp]: \<open>all_init_atms (get_clauses_wl S')
        (IsaSAT_Setup.get_unkept_unit_init_clss_wl S' + IsaSAT_Setup.get_kept_unit_init_clss_wl S' + get_subsumed_init_clauses_wl S' +
      get_init_clauses0_wl S') = all_init_atms_st S'\<close>
    by (auto simp: all_init_atms_st_def IsaSAT_Setup.get_unit_init_clss_wl_alt_def)

  have [refine0]: \<open>(CS, Map.empty) \<in>?CS \<Longrightarrow>
    (val, polarity (get_trail_wl S') L') \<in> \<langle>bool_rel\<rangle>option_rel \<Longrightarrow>
    deduplicate_binary_clauses_inv_wl S' L' (defined_lit (get_trail_wl S') L', 0, Map.empty, S') \<Longrightarrow>
    ((val \<noteq> UNSET, 0, CS, S), defined_lit (get_trail_wl S') L', 0, Map.empty, S') \<in> bool_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r ?CS \<times>\<^sub>r
    ({(a, b). (a,b)\<in> twl_st_heur_restart_ana'' r u ns lw \<and> learned_clss_count a \<le> learned_clss_count S})\<close> (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _\<Longrightarrow> _ \<in> ?loop\<close>)
    for CS val
    using assms by (auto simp: polarity_def)
  have [refine0]: \<open>isa_simplify_clause_with_unit_st2 C S
    \<le> \<Down> {(a, b). (a, b) \<in> twl_st_heur_restart \<and> get_avdom a = get_avdom S \<and>
  get_vdom a = get_vdom S \<and>
  get_ivdom a = get_ivdom S \<and>
    length (get_clauses_wl_heur a) = r \<and> learned_clss_count a \<le> u \<and> learned_clss_count a \<le> learned_clss_count S  \<and> get_vmtf_heur a = get_vmtf_heur S \<and>
    length (get_watched_wl_heur a) = lw}
    (simplify_clause_with_unit_st_wl C' T)\<close>
    if \<open>(S,T) \<in> {(a, b).
    (a, b) \<in> twl_st_heur_restart \<and>
    get_avdom a = get_avdom S \<and>
      get_vdom a = get_vdom S \<and>  get_ivdom a = get_ivdom S \<and> length (get_clauses_wl_heur a) = r
      \<and> learned_clss_count a \<le> u \<and> get_vmtf_heur a = get_vmtf_heur S \<and>
      length (get_watched_wl_heur a) = lw}\<close>
      \<open>(C,C') \<in> Id\<close>
    for S T C C'
    apply (rule isa_simplify_clause_with_unit_st2_simplify_clause_with_unit_st2[THEN order_trans])
    apply (rule that)
    apply (rule that)
    apply (rule ref_two_step'')
    defer
    apply (rule simplify_clause_with_unit_st2_simplify_clause_with_unit_st[THEN order_trans, of _ C' T T])
    apply auto
    done
  have [simp]: \<open>(Sa, U) \<in> twl_st_heur_restart_ana (length (get_clauses_wl_heur Sa)) \<longleftrightarrow> (Sa, U) \<in> twl_st_heur_restart\<close>  for Sa U
    by (auto simp: twl_st_heur_restart_ana_def)
  have KK: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S')) \<longleftrightarrow>
    set_mset ((all_init_atms_st T)) = set_mset ((all_init_atms_st S'))\<close> for S' T
    apply (auto simp:  \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2))
    apply (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_cong_set_mset)
    apply (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_cong_set_mset)
    apply (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) \<L>\<^sub>a\<^sub>l\<^sub>l_cong)+
    done


  have get_watched_wl_heur: \<open>mop_watched_by_app_heur x2e L x1d \<le> \<Down>
    {(a,b). a = b \<and> a = get_watched_wl_heur x2e ! nat_of_lit L ! x1d \<and> b = watched_by x2b L' ! x1a \<and>
        fst a \<in> set (get_vdom x2e)} (mop_watched_by_at_init x2b L' x1a)\<close>
    (is \<open>_ \<le>\<Down> ?watched _\<close>)
  if 
    \<open>(S, S') \<in> twl_st_heur_restart_ana'' r u ns lw\<close> and
    \<open>(L, L') \<in> nat_lit_lit_rel\<close> and
    \<open>deduplicate_binary_clauses_pre_wl L' S'\<close> and
    \<open>L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S')\<close> and
    \<open>(CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur S)}\<close> and
    \<open>polarity_pol_pre (get_trail_wl_heur S) L\<close> and
    \<open>inres (RETURN (polarity_pol (get_trail_wl_heur S) L)) val\<close> and
    \<open>(val, polarity (get_trail_wl S') L') \<in> \<langle>bool_rel\<rangle>option_rel\<close> and
    \<open>(x, x') \<in> ?loop\<close> and
    \<open>case x of (abort, i, CS, Sa) \<Rightarrow> \<not> abort \<and> i < l \<and> get_conflict_wl_is_None_heur Sa\<close> and
    \<open>case x' of (abort, i, CS, S) \<Rightarrow> \<not> abort \<and> i < length (watched_by S' L') \<and> get_conflict_wl S = None\<close> and
    \<open>case x' of
  (abort, i, a, T) \<Rightarrow>
    deduplicate_binary_clauses_inv_wl S' L' (abort, i, a, T) \<and>
    set_mset (all_init_atms_st T) = set_mset (all_init_atms_st S') \<and>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S'))\<close> and
    \<open>x2a = (x1b, x2b)\<close> and
    \<open>x2 = (x1a, x2a)\<close> and
    \<open>x' = (x1, x2)\<close> and
    \<open>x2d = (x1e, x2e)\<close> and
    \<open>x2c = (x1d, x2d)\<close> and
    \<open>x = (x1c, x2c)\<close> and
    \<open>(l, length (watched_by S' L')) \<in> {(l, l'). (l, l') \<in> nat_rel \<and> l' = length (watched_by S' L')}\<close>
    for CS val x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e l
  proof -
    show ?thesis
      apply (rule order_trans)
      apply (rule mop_watched_by_app_heur_mop_watched_by_at_init_ana[of r, THEN fref_to_Down_curry2,
        of _ _ _ x2b L' x1a])
      subgoal by fast
      subgoal using that by auto
      unfolding Down_id_eq mop_watched_by_at_init_def
      apply (refine_rcg)
      using that twl_st_heur_restart_ana_watchlist_in_vdom[where L=L and x2e=x2e and x2f=x2b and x1d = x1d
        and a=\<open>fst (get_watched_wl_heur x2e ! nat_of_lit L ! x1d)\<close> and b=\<open>snd(get_watched_wl_heur x2e ! nat_of_lit L ! x1d)\<close>
        and r=r]
      by (auto simp: twl_st_heur_restart_ana_state_simp watched_by_alt_def
        deduplicate_binary_clauses_inv_wl_def mop_watched_by_at_init_def)
  qed
  have watched_in_vdom:
    \<open>x1h \<in> set (get_vdom x2e)\<close> \<open>(x1h, x1f) \<in> nat_rel\<close>
    if \<open>(xa, x'a) \<in> ?watched x1d x1a x2b x2e\<close>
      \<open>x'a = (x1f, x2f)\<close>
      \<open>x2f = (x3f, x3f')\<close>
      \<open>xa = (x1h, x2h)\<close>
      \<open>x2h = (x3h, x3h')\<close>
    for x2e xa x'a x1h x2h x1f x2f x1d x1a x2b x3f x3f' x3h x3h'
    using that
    by auto
  have irred_status: \<open>\<not> (x1f \<notin># dom_m (get_clauses_wl x2b) \<or> \<not> x2g) \<Longrightarrow>
    (xb, x1f \<in># dom_m (get_clauses_wl x2b))
    \<in> {(a, b). (a \<noteq> DELETED) = b \<and>
    (a = IRRED) = (irred (get_clauses_wl x2b) x1f \<and> b) \<and> (a = LEARNED) = (\<not> irred (get_clauses_wl x2b) x1f \<and> b)} \<Longrightarrow>
    (xb, irred (get_clauses_wl x2b) x1f) \<in> {(a,b). a \<noteq> DELETED \<and> ((a=IRRED) \<longleftrightarrow> b) \<and> ((a=LEARNED) \<longleftrightarrow> \<not>b)}\<close>
    for xb x2b x1f x2g
    by (cases xb) auto
  have twl_st_heur_restart_ana_stateD:  \<open>valid_arena (get_clauses_wl_heur x2e) (get_clauses_wl x2b) (set (get_vdom x2e))\<close>
    if \<open>(x2e, x2b) \<in> twl_st_heur_restart_ana r\<close>
      for x2e x2b
    using that unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_def
    by simp
  have is_markedI: \<open>(x1e, x1e') \<in> ?CS \<Longrightarrow> (x1i, x1i') \<in> nat_lit_lit_rel \<Longrightarrow> x1i' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
    is_marked x1e x1i \<le> SPEC (\<lambda>c. (c, x1e' x1i') \<in> {(a,b). a \<longleftrightarrow> b\<noteq>None})\<close>
    \<open>(x1e, x1e') \<in> ?CS \<Longrightarrow> (x1i, x1i') \<in> nat_lit_lit_rel \<Longrightarrow> (m, x1e' x1i') \<in> {(a,b). a \<longleftrightarrow> b\<noteq>None} \<Longrightarrow>x1i' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
    (if m then get_marked x1e x1i else RETURN (1, True))
    \<le> SPEC
    (\<lambda>c. (c, x1e' x1i') \<in> {(a,b). b \<noteq> None \<longrightarrow> a = the b})\<close>
    \<open>(x1e, x1e') \<in> ?CS \<Longrightarrow> (x1i, x1i') \<in> nat_lit_lit_rel \<Longrightarrow> x1i' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow> (x, x') \<in> Id \<Longrightarrow>
    (m, x1e' x1i') \<in> {(a,b). a \<longleftrightarrow> b\<noteq>None} \<Longrightarrow> \<not>m \<Longrightarrow>
    set_marked x1e x1i x \<le> SPEC (\<lambda>c. (c, x1e'(x1i' \<mapsto> x')) \<in> ?CS)\<close>
    for x1e x1e' x1i x1i' m x x'
    using assms(1)
    unfolding is_marked_def get_marked_def set_marked_def
    by (auto intro!: ASSERT_leI simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
      map_fun_rel_def)
  have length_watchlist:
    \<open>(S, S') \<in> twl_st_heur_restart_ana'' r u ns lw \<Longrightarrow>
      (L, L') \<in> nat_lit_lit_rel \<Longrightarrow>
      L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
      mop_length_watched_by_int S L \<le> SPEC (\<lambda>c. (c, length (watched_by S' L')) \<in> {(l,l'). (l,l') \<in> nat_rel \<and> l' = length (watched_by S' L')})\<close>
    by (auto simp: mop_length_watched_by_int_def twl_st_heur_restart_ana_def
      twl_st_heur_restart_def map_fun_rel_def watched_by_alt_def intro!: ASSERT_leI)
  have [refine0]: \<open>(CS, a) \<in> ?CS \<Longrightarrow> empty CS \<le> SPEC (\<lambda>u. (u, Map.empty) \<in> ?CS)\<close> for a CS
    by (auto simp: empty_def)

  have update_marked: \<open>(if \<not> snd n \<longrightarrow> st = LEARNED then RETURN x1e else update_marked x1e x1i (x1h, st = IRRED))
     \<le> SPEC
        (\<lambda>c. (c, if \<not> snd (the (x1b x1g)) \<longrightarrow> \<not> irred (get_clauses_wl x2b) x1f then x1b
           else x1b(x1g \<mapsto> (x1f, irred (get_clauses_wl x2b) x1f)))
          \<in> ?CS)\<close>
    if
      loop: \<open>(x, x') \<in> ?loop\<close> and
      \<open>case x' of
    (abort, i, a, T) \<Rightarrow>
      deduplicate_binary_clauses_inv_wl S' L' (abort, i, a, T) \<and>
      set_mset (all_init_atms_st T) = set_mset (all_init_atms_st S') \<and>
      set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S'))\<close> and
      st: \<open>x2a = (x1b, x2b)\<close>
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1c, x2c)\<close> 
        \<open>x2f = (x1g, x2g)\<close>
        \<open>x'a = (x1f, x2f)\<close>
        \<open>x2h = (x1i, x2i)\<close>
        \<open>xa = (x1h, x2h)\<close> and
      \<open>x1d < l\<close> and
      \<open>(xa, x'a)
    \<in> {(a, b).
       a = b \<and>
       a = get_watched_wl_heur x2e ! nat_of_lit L ! x1d \<and>
       b = watched_by x2b L' ! x1a \<and> fst a \<in> set (get_vdom x2e)}\<close> and
      \<open>x1g \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x2b)\<close> and
      \<open>0 < x1h \<and> x1h < length (get_clauses_wl_heur x2e)\<close> and
      \<open>(st, x1f \<in># dom_m (get_clauses_wl x2b))
    \<in> {(a, b).
       (a \<noteq> DELETED) = b \<and>
       (a = IRRED) = (irred (get_clauses_wl x2b) x1f \<and> b) \<and>
       (a = LEARNED) = (\<not> irred (get_clauses_wl x2b) x1f \<and> b)}\<close> and
      \<open>\<not> (st = DELETED \<or> \<not> x2i)\<close> and
      \<open>\<not> (x1f \<notin># dom_m (get_clauses_wl x2b) \<or> \<not> x2g)\<close> and
      m: \<open>(m, x1b x1g) \<in> {a. case a of (a, b) \<Rightarrow> a = (b \<noteq> None)}\<close> m and
      \<open>(n, x1b x1g) \<in> {a. case a of (a, b) \<Rightarrow> b \<noteq> None \<longrightarrow> a = the b}\<close> and
      \<open>x1b x1g \<noteq> None\<close>
      for l val x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e xa x'a x1f x2f x1g x2g x1h x2h x1i x2i st
    vala m n
  proof -
    have \<open>(get_watched_wl_heur S, get_watched_wl S') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S'))\<close>
      using assms
      by (auto intro!: ASSERT_leI simp: st twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    then show ?thesis
      using that
      unfolding update_marked_def
      by (auto intro!: ASSERT_leI simp: st map_fun_rel_def)
  qed
  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding isa_deduplicate_binary_clauses_wl_def deduplicate_binary_clauses_wl_alt_def mop_polarity_pol_def nres_monad3 apply -
    apply (subst deduplicate_binary_clauses_wl_alt_def)
    apply (subst deduplicate_binary_clauses_inv_wl_strengthen_def2)
    apply (refine_rcg polarity_pol_polarity[of \<open>all_init_atms_st S'\<close>, THEN fref_to_Down_unRET_uncurry]
      mop_arena_status_vdom isa_clause_remove_duplicate_clause_wl_clause_remove_duplicate_clause_wl[of r \<open>learned_clss_count S\<close> ns lw for S,
          THEN fref_to_Down_curry, of _ _ _ S S for S]
      isa_binary_clause_subres_isa_binary_clause_subres_wl[of r \<open>learned_clss_count S\<close> ns lw for S, THEN fref_to_Down_curry3, of _ _ _ S _ _ _ _ S for S]
      length_watchlist)
    subgoal
      using length_watched_le_ana[of S' S \<open>length (get_clauses_wl_heur S)\<close> L]
      by (auto simp add: deduplicate_binary_clauses_pre_wl_def watched_by_alt_def
        deduplicate_binary_clauses_pre_wl_in_all_atmsD  \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2)
        twl_st_heur_restart_ana_state_simp twl_st_heur_restart_ana_def)
    subgoal
      by (rule polarity_pol_pre)
       (use assms in \<open>auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def\<close>)[2]
   subgoal
      by auto
   subgoal
     by (use assms in \<open>auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def\<close>)
    subgoal by auto
    subgoal for CS val
      by (auto simp: watched_by_alt_def deduplicate_binary_clauses_pre_wl_in_all_atmsD get_conflict_wl_is_None_def
        twl_st_heur_restart_ana_state_simp get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id])
    subgoal by auto
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    apply (rule get_watched_wl_heur; assumption)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
       (metis (no_types, lifting) arena_dom_status_iff(3) bot_nat_0.extremum gr0I le_antisym numeral_le_iff semiring_norm(69))+

    subgoal by  (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
      intro!: valid_arena_in_vdom_le_arena)
    apply (solves auto)
    subgoal for CS val x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      by auto
    subgoal
      by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    subgoal by auto
    subgoal
      by (simp add: deduplicate_binary_clauses_pre_wl_in_all_atmsD \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2))
    subgoal
      apply (rule polarity_pol_pre)
      apply (use assms in \<open>auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_alt_def2 Let_def\<close>)[]
      apply (clarsimp simp add: watched_by_alt_def twl_st_heur_restart_ana_state_simp)
      done
    subgoal by auto
    subgoal
      unfolding prod_rel_iff
      apply (intro conjI impI)
      subgoal
        unfolding twl_st_heur_restart_alt_def2 twl_st_heur_restart_ana_def Let_def KK prod.simps
        apply (simp only: in_pair_collect_simp prod_rel_iff prod.simps)
        apply normalize_goal+
        apply (rule trail_pol_cong, assumption, assumption)
        done
      subgoal
        by (clarsimp simp: watched_by_alt_def twl_st_heur_restart_ana_state_simp dest: trail_pol_cong)
      done
    subgoal
      by (auto simp: polarity_def)
    subgoal
      by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (clarsimp simp add: watched_by_alt_def twl_st_heur_restart_ana_state_simp)
    subgoal
      apply (rule polarity_pol_pre)
      apply (use assms in \<open>auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_alt_def2 Let_def\<close>)[]
      apply (clarsimp simp add: watched_by_alt_def twl_st_heur_restart_ana_state_simp)
      done
    subgoal by (clarsimp simp add: twl_st_heur_restart_ana_def)
    subgoal
        unfolding twl_st_heur_restart_alt_def2 twl_st_heur_restart_ana_def Let_def KK prod.simps
        apply (simp only: in_pair_collect_simp prod_rel_iff prod.simps)
        apply normalize_goal+
        by (metis (no_types, lifting) trail_pol_cong)
    subgoal
      by (auto simp: twl_st_heur_restart_ana_state_simp polarity_def)
    apply (rule is_markedI)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    apply (rule is_markedI)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    apply (rule update_marked; assumption)
    subgoal by (auto split: if_splits)
    subgoal by simp
    subgoal by simp
    apply (rule is_markedI)
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: uminus_\<A>\<^sub>i\<^sub>n_iff)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    apply (rule is_markedI)
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: uminus_\<A>\<^sub>i\<^sub>n_iff)
    subgoal by simp
    apply assumption
    subgoal by auto
    apply (solves auto)
    apply (solves auto)
    subgoal by auto
    done
qed


lemma lambda_split_second: \<open>(\<lambda>(a, x). f a x) = (\<lambda>(a,b,c:: isasat). f a (b,c))\<close>
  by (auto intro!: ext)

lemma isa_mark_duplicated_binary_clauses_as_garbage_wl_alt_def:
  \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl S\<^sub>0 = do {
  ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S\<^sub>0);
  let skip = should_eliminate_pure_st S\<^sub>0;
  CS \<leftarrow> create (length (get_watched_wl_heur S\<^sub>0));
  (CS, S) \<leftarrow> iterate_over_VMTFC
    (\<lambda>A (CS, S). do {ASSERT (get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S));
        skip_lit \<leftarrow> mop_is_marked_added_heur_st S A;
        if \<not>skip \<or> \<not>skip_lit then RETURN (CS, S)
        else do {
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Pos A) CS S;
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Neg A) CS S;
          ASSERT (get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S));
          RETURN (CS, S)
          }})
       (\<lambda>(CS, S). get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S))
       (\<lambda>(CS, S). get_conflict_wl_is_None_heur S)
          (get_vmtf_heur_array S\<^sub>0, Some (get_vmtf_heur_fst S\<^sub>0)) (CS, S\<^sub>0);
   RETURN S
   }\<close>
  unfolding iterate_over_VMTFC_def prod.simps nres_monad3 Let_def
  apply (rewrite  at  \<open>WHILE\<^sub>T\<^bsup>_\<^esup> _ \<hole>\<close> lambda_split_second)
  unfolding isa_mark_duplicated_binary_clauses_as_garbage_wl_def
  apply (rewrite at \<open>WHILE\<^sub>T\<^bsup>_\<^esup> _ \<hole> _\<close> lambda_split_second)
  apply (auto intro!: bind_cong simp: Let_def)
  done

definition mark_duplicated_binary_clauses_as_garbage_wl2 :: \<open>_ \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_wl2 S = do {
     ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl S);
     Ls \<leftarrow> SPEC (\<lambda>Ls:: 'v multiset. set_mset Ls =  set_mset (atm_of `# all_init_lits_of_wl S) \<and> distinct_mset Ls);
     (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(L, T). mark_duplicated_binary_clauses_as_garbage_wl_inv Ls S (T, L)\<^esup>(\<lambda>(Ls, S). Ls \<noteq> {#} \<and> get_conflict_wl S = None)
     (\<lambda>(Ls, S). do {
        ASSERT (Ls \<noteq> {#});
        L \<leftarrow> SPEC (\<lambda>L. L \<in># Ls);
        ASSERT (L \<in># atm_of `# all_init_lits_of_wl S);
        skip \<leftarrow> RES (UNIV :: bool set);
        if skip then RETURN (remove1_mset L Ls, S)
        else do {
          S \<leftarrow> deduplicate_binary_clauses_wl (Pos L) S;
          S \<leftarrow> deduplicate_binary_clauses_wl (Neg L) S;
          RETURN (remove1_mset L Ls, S)
        }
     })
     (Ls, S);
    RETURN S
  }\<close>

lemma mark_duplicated_binary_clauses_as_garbage_wl2_alt_def:
  \<open>mark_duplicated_binary_clauses_as_garbage_wl2 S = do {
     ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl S);
     Ls \<leftarrow> SPEC (\<lambda>Ls:: 'v multiset. set_mset Ls =  set_mset (atm_of `# all_init_lits_of_wl S) \<and> distinct_mset Ls);
     (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(L, T). mark_duplicated_binary_clauses_as_garbage_wl_inv Ls S (T, L)\<^esup>(\<lambda>(Ls, S). Ls \<noteq> {#} \<and> get_conflict_wl S = None)
     (\<lambda>(Ls, S). do {
        ASSERT (Ls \<noteq> {#});
        L \<leftarrow> SPEC (\<lambda>L. L \<in># Ls);
        S \<leftarrow> do {
          ASSERT (L \<in># atm_of `# all_init_lits_of_wl S);
          skip \<leftarrow> RES (UNIV :: bool set);
          if skip then RETURN (S)
          else do {
            S \<leftarrow> deduplicate_binary_clauses_wl (Pos L) S;
            S \<leftarrow> deduplicate_binary_clauses_wl (Neg L) S;
            RETURN (S)
          }
       };
       RETURN (remove1_mset L Ls, S)
     })
     (Ls, S);
    RETURN S
  }\<close>
  unfolding nres_monad_laws mark_duplicated_binary_clauses_as_garbage_wl2_def bind_to_let_conv Let_def
  apply (auto intro!: bind_cong[OF refl] simp: bind_to_let_conv)
  apply (subst bind_to_let_conv Let_def)+
  apply (auto simp: Let_def nres_monad_laws intro!: bind_cong)
  apply (subst nres_monad_laws)+
  apply auto
  done

lemma mark_duplicated_binary_clauses_as_garbage_wl2_ge_\<L>\<^sub>a\<^sub>l\<^sub>l:
  \<open>\<Down> Id (mark_duplicated_binary_clauses_as_garbage_wl2 S) \<ge> do {
     ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl S);
   iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC
  (\<lambda>L S. do {
          ASSERT (L \<in># atm_of `# all_init_lits_of_wl S);
          skip \<leftarrow> RES (UNIV :: bool set);
          if skip then RETURN (S)
          else do {
            S \<leftarrow> deduplicate_binary_clauses_wl (Pos L) S;
            S \<leftarrow> deduplicate_binary_clauses_wl (Neg L) S;
            RETURN (S)
          }
       })
        (atm_of `# all_init_lits_of_wl S)
        (\<lambda>\<A> T. mark_duplicated_binary_clauses_as_garbage_wl_inv (all_init_atms_st S) S (T, \<A>))
        (\<lambda>S. get_conflict_wl S = None) S}\<close>
proof -
  have H: \<open>a=b \<Longrightarrow> (a,b) \<in> Id\<close> for a b
    by auto
  have H': \<open>a=b \<Longrightarrow> a \<le>\<Down>Id b\<close> for a b
    by auto
  have HH: \<open>mark_duplicated_binary_clauses_as_garbage_wl_inv Ls S (x2, x1) \<Longrightarrow>
    set_mset Ls = set_mset (all_init_atms_st S) \<Longrightarrow>
    distinct_mset Ls \<Longrightarrow> mark_duplicated_binary_clauses_as_garbage_wl_inv (all_init_atms_st S) S (x2, x1)\<close>
    for Ls x2 x1
    unfolding mark_duplicated_binary_clauses_as_garbage_wl_inv_def
      mark_duplicated_binary_clauses_as_garbage_inv_def prod.simps
    apply normalize_goal+
    apply (rule_tac x=x in exI, rule_tac x=xa in exI)
    apply simp
    by (metis Duplicate_Free_Multiset.distinct_mset_mono distinct_subseteq_iff)

  show ?thesis
    unfolding iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC_def mark_duplicated_binary_clauses_as_garbage_wl2_alt_def
    apply refine_vcg
    apply (rule H)
    subgoal by auto
    subgoal by (auto simp flip: all_init_atms_st_alt_def intro: HH)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    apply (rule H')
    subgoal by auto
    apply (rule H')
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma mark_duplicated_binary_clauses_as_garbage_wl2_mark_duplicated_binary_clauses_as_garbage_wl:
  \<open>mark_duplicated_binary_clauses_as_garbage_wl2 S \<le> \<Down>Id (mark_duplicated_binary_clauses_as_garbage_wl S)\<close>
proof -
  have H: \<open>fst a = snd b \<and> snd a = fst b \<Longrightarrow> (a,b) \<in> {((s,t), (u, v)). (s=v) \<and> (t=u)}\<close> for a b
    by (cases a; cases b) simp
  have H': \<open>a = b \<Longrightarrow> a \<le> \<Down>Id b\<close> for a b
    by auto
  show ?thesis
    unfolding mark_duplicated_binary_clauses_as_garbage_wl2_def
      mark_duplicated_binary_clauses_as_garbage_wl_def
    apply (refine_vcg)
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H')
    subgoal by auto
    apply (rule H')
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma isa_mark_duplicated_binary_clauses_as_garbage_wl_mark_duplicated_binary_clauses_as_garbage_wl:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (mark_duplicated_binary_clauses_as_garbage_wl S')\<close>
proof -
  obtain ns m fst_As lst_As next_search to_remove where
    vm: \<open>get_vmtf_heur S = ((ns, m, fst_As, lst_As, next_search), to_remove)\<close>
    by (cases \<open>get_vmtf_heur S\<close>) auto
  have 1: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> isa_vmtf (atm_of `# all_init_lits_of_wl S') (get_trail_wl S')\<close> and
    2: \<open>isasat_input_nempty (all_init_atms_st S')\<close> and
    3: \<open>isasat_input_bounded (all_init_atms_st S')\<close>
     using assms unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_alt_def2 Let_def vm
     by (simp_all add: vm all_init_atms_st_alt_def)
   then obtain ba where
     1: \<open>((ns, m, fst_As, lst_As, next_search), ba) \<in> vmtf (atm_of `# all_init_lits_of_wl S') (get_trail_wl S')\<close>
     unfolding isa_vmtf_def
     by auto
  have [refine0]: \<open>RETURN False \<le> \<Down> {(a,b). a = b \<and> \<not>b} (RES UNIV)\<close>
    by (auto intro!: RETURN_RES_refine)
  have create: \<open>create (length (get_watched_wl_heur S)) \<le> SPEC (\<lambda>c. (c, Map.empty) \<in> {((c :: nat literal \<Rightarrow> (nat \<times> bool) option, m::nat), c'). c = c' \<and> m =  (length (get_watched_wl_heur S))})\<close> (is \<open>_ _\<le> SPEC(\<lambda>_. _ \<in> ?CS)\<close>)
    by (auto simp: create_def)
   have init: \<open>(x2a, x2) \<in> \<langle>nat_rel\<rangle>option_rel \<Longrightarrow> (CS, Map.empty) \<in> ?CS \<Longrightarrow>
     ((x2a, CS, S), x2, S') \<in> {((a,CS,T), (b,T')). ((a,T), b,T') \<in> \<langle>nat_rel\<rangle>option_rel \<times>\<^sub>r {(a,b). (a,b)\<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S))
        (learned_clss_count S) (get_vmtf_heur S) (length (get_watched_wl_heur S)) \<and> ns = get_vmtf_heur_array S} \<and>
     (CS, Map.empty) \<in> {((c :: nat literal \<Rightarrow> (nat \<times> bool) option, m::nat), c'). c = c' \<and> m =  (length (get_watched_wl_heur T))}}\<close>
     (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?loop\<close>)
    for x2a x2 CS
    using vm assms
    by (auto simp: get_vmtf_heur_array_def twl_st_heur_restart_ana_def)
  have rel: \<open>(xa, Sa)
    \<in> {((CS, T), T').
    (T, T')
    \<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S) (get_vmtf_heur S)
       (length (get_watched_wl_heur S)) \<and>
    (CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur x2d)}} \<Longrightarrow>
    xa = (x1e, x2e) \<Longrightarrow>
    length (get_clauses_wl_heur x2e) \<le> length (get_clauses_wl_heur S) \<and>
    learned_clss_count x2e \<le> learned_clss_count S \<Longrightarrow>
    (xb, x'a)
    \<in> {((CS, T), T').
    (T, T')
    \<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S) (get_vmtf_heur S)
       (length (get_watched_wl_heur S)) \<and>
    (CS, Map.empty) \<in> {((c, m), c'::nat literal \<Rightarrow> (nat \<times> bool) option). c = c' \<and> m = length (get_watched_wl_heur x2e)}} \<Longrightarrow>
    xb = (a, b) \<Longrightarrow>
    get_vmtf_heur_array S = get_vmtf_heur_array b \<Longrightarrow>
    ((a, b), x'a) \<in> {((CS, T), T'). (T,T')\<in>twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S) (get_vmtf_heur S)
       (length (get_watched_wl_heur S)) \<and>
    (CS, Map.empty) \<in> {((c, m), c'::nat literal \<Rightarrow> (nat \<times> bool) option). c = c' \<and> m = length (get_watched_wl_heur S)}}\<close> for A Sa x1d x2d skip xa x1e x2e xb x'a a b
    by auto
  have rel2:
    \<open>(x, x')
    \<in> {((a, CS, T), b, T').
    ((a, T), b, T')
    \<in> \<langle>nat_rel\<rangle>option_rel \<times>\<^sub>f
      {(a, b).
       (a, b)
       \<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S)
       (get_vmtf_heur S) (length (get_watched_wl_heur S)) \<and>
       ns = get_vmtf_heur_array S} \<and>
    (CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur T)}} \<Longrightarrow>
    x' = (x1b, x2b) \<Longrightarrow> x = (x1c, x2c) \<Longrightarrow> (x2c, x2b) \<in> {((CS, T), T').
    ((T), T')
    \<in> 
      {(a, b).
       (a, b)
       \<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S)
       (get_vmtf_heur S) (length (get_watched_wl_heur S)) \<and>
       ns = get_vmtf_heur_array S} \<and>
    (CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur T)}}\<close> for x' x1b x2b x1c x2c x
    by auto
  have rel0: \<open>((x1d, x2d), x2b) \<in> {((CS, T), T'). (T,T')\<in>twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S) (get_vmtf_heur S)
       (length (get_watched_wl_heur S)) \<and>
    (CS, Map.empty) \<in> {((c, m), c'::nat literal \<Rightarrow> (nat \<times> bool) option). c = c' \<and> m = length (get_watched_wl_heur S)}}\<close>
  if 
    \<open>mark_duplicated_binary_clauses_as_garbage_pre_wl S'\<close> and
    \<open>mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S\<close> and
    \<open>inres (create (length (get_watched_wl_heur S))) CS\<close> and
    \<open>(CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur S)}\<close> and
    \<open>(ns, Some fst_As) = (x1, x2)\<close> and
    \<open>(get_vmtf_heur_array S, Some (get_vmtf_heur_fst S)) = (x1a, x2a)\<close> and
    \<open>(x, x')
  \<in> {((a, CS, T), b, T').
     ((a, T), b, T')
     \<in> \<langle>nat_rel\<rangle>option_rel \<times>\<^sub>f
    {(a, b).
     (a, b)
     \<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S)) (learned_clss_count S)
        (get_vmtf_heur S) (length (get_watched_wl_heur S)) \<and>
     ns = get_vmtf_heur_array S} \<and>
     (CS, Map.empty) \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur T)}}\<close> and
    \<open>case x of (n, x) \<Rightarrow> \<forall>x1 x2. x = (x1, x2) \<longrightarrow> n \<noteq> None \<and> get_conflict_wl_is_None_heur x2\<close> and
    \<open>case x' of (n, x) \<Rightarrow> n \<noteq> None \<and> get_conflict_wl x = None\<close> and
    \<open>case x of (n, CS, Sa) \<Rightarrow> get_vmtf_heur_array S = get_vmtf_heur_array Sa\<close> and
    \<open>case x' of
  (n, x) \<Rightarrow>
    \<exists>\<B>'. mark_duplicated_binary_clauses_as_garbage_wl_inv (all_init_atms_st S') S'
       (x, \<B>')\<close> and
    \<open>x' = (x1b, x2b)\<close> and
    \<open>x = (x1c, x2c)\<close> and
    \<open>x1b \<noteq> None\<close> and
    \<open>x1c \<noteq> None\<close> and
    \<open>the x1b < length x1\<close> and
    \<open>the x1b \<le> uint32_max div 2\<close> and
    \<open>the x1c < length x1a\<close> and
    \<open>the x1c \<le> uint32_max div 2\<close> and
    \<open>x2c = (x1d, x2d)\<close> and
    \<open>get_vmtf_heur_array S = get_vmtf_heur_array x2d\<close> and
    \<open>the x1b \<in># atm_of `# all_init_lits_of_wl x2b\<close>
  for skip CS x1 x2 x1a x2a x x' x1b x2b x1c x2c x1d x2d skipa
    using that by auto
  have binary_deduplicate_required: \<open>(should_eliminate_pure_st S, True) \<in> UNIV\<close>
   for S skip v
    by (auto simp: should_eliminate_pure_st_def)
  have GC_required_skip: \<open>mop_is_marked_added_heur_st x2d (the x1c)
     \<le> \<Down> {(a,b). (\<not>skip \<or> \<not>a,b)\<in>bool_rel}
        (RES UNIV)\<close>
    if
      \<open>mark_duplicated_binary_clauses_as_garbage_pre_wl S'\<close> and
      \<open>mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S\<close> and
      \<open>inres (create (length (get_watched_wl_heur S))) CS\<close> and
      \<open>(CS, Map.empty)
    \<in> {((c, m), c'). c = c' \<and> m = length (get_watched_wl_heur S)}\<close> and
      \<open>(ns, Some fst_As) = (x1, x2)\<close> and
      \<open>(get_vmtf_heur_array S, Some (get_vmtf_heur_fst S)) =
    (x1a, x2a)\<close> and
      \<open>(x, x')
    \<in> {((a, CS, T), b, T').
       ((a, T), b, T')
       \<in> \<langle>nat_rel\<rangle>option_rel \<times>\<^sub>f
      {(a, b).
       (a, b)
       \<in> twl_st_heur_restart_ana'' (length (get_clauses_wl_heur S))
          (learned_clss_count S) (get_vmtf_heur S)
          (length (get_watched_wl_heur S)) \<and>
       ns = get_vmtf_heur_array S} \<and>
       (CS, Map.empty)
       \<in> {((c, m), c').
       c = c' \<and> m = length (get_watched_wl_heur T)}}\<close> and
      \<open>case x of
    (n, x) \<Rightarrow>
      \<forall>x1 x2.
      x = (x1, x2) \<longrightarrow> n \<noteq> None \<and> get_conflict_wl_is_None_heur x2\<close> and
      \<open>case x' of (n, x) \<Rightarrow> n \<noteq> None \<and> get_conflict_wl x = None\<close> and
      \<open>case x of
    (n, CS, Sa) \<Rightarrow> get_vmtf_heur_array S = get_vmtf_heur_array Sa\<close> and
      \<open>case x' of
    (n, x) \<Rightarrow>
      \<exists>\<B>'. mark_duplicated_binary_clauses_as_garbage_wl_inv
         (all_init_atms_st S') S' (x, \<B>')\<close> and
      \<open>x' = (x1b, x2b)\<close> and
      \<open>x = (x1c, x2c)\<close> and
      \<open>x1b \<noteq> None\<close> and
      \<open>x1c \<noteq> None\<close> and
      \<open>the x1b < length x1\<close> and
      \<open>the x1b \<le> uint32_max div 2\<close> and
      \<open>the x1c < length x1a\<close> and
      \<open>the x1c \<le> uint32_max div 2\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>get_vmtf_heur_array S = get_vmtf_heur_array x2d\<close> and
      \<open>the x1b \<in># atm_of `# all_init_lits_of_wl x2b\<close>
    for skip CS x1 x2 x1a x2a x x' x1b x2b x1c x2c x1d x2d
  proof -
    term ?thesis
    have heur: \<open>heuristic_rel (all_init_atms_st x2b) (get_heur x2d)\<close>
      using that
      by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
        all_init_atms_st_def get_unit_init_clss_wl_alt_def)
    moreover have \<open>the x1c \<in># all_init_atms_st x2b\<close>
      using that by (auto simp: all_init_atms_st_alt_def)
    ultimately have \<open>is_marked_added_heur_pre (get_heur x2d) (the x1c)\<close>
      unfolding is_marked_added_heur_pre_def
      by (auto simp: heuristic_rel_def is_marked_added_heur_pre_stats_def
        heuristic_rel_stats_def phase_saving_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    then show ?thesis
      unfolding mop_is_marked_added_heur_st_def mop_is_marked_added_heur_def
      by (auto intro!: RETURN_RES_refine)
  qed
  have skip: \<open>(skip_lit, skip)
    ∈ {(a, b). (¬should_eliminate_pure_st S  ∨ ¬ a, b) ∈ bool_rel} ⟹
    skip ∈ UNIV ⟹ (¬ should_eliminate_pure_st S ∨ ¬ skip_lit) = skip\<close> for skip_lit skip
   by auto
  have last_step: \<open>do {
   _ \<leftarrow> ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S);
     let skip = should_eliminate_pure_st S;
    (CS::(nat literal \<Rightarrow> (nat \<times> bool) option)\<times> nat) \<leftarrow> create (length (get_watched_wl_heur S));
    (CS, S) \<leftarrow> iterate_over_VMTFC
    (\<lambda>A (CS, Sa). do {
       _ \<leftarrow> ASSERT (get_vmtf_heur_array S = get_vmtf_heur_array Sa);
        skip_lit \<leftarrow> mop_is_marked_added_heur_st Sa A;
       if \<not>skip \<or> \<not>skip_lit then RETURN (CS, Sa)
       else do {
        ASSERT (length (get_clauses_wl_heur Sa) \<le> length (get_clauses_wl_heur S) \<and> learned_clss_count Sa \<le> learned_clss_count S);
        (CS, Sa) \<leftarrow> isa_deduplicate_binary_clauses_wl (Pos A) CS Sa;
        ASSERT (length (get_clauses_wl_heur Sa) \<le> length (get_clauses_wl_heur S) \<and> learned_clss_count Sa \<le> learned_clss_count S);
        (CS, Sa) \<leftarrow> isa_deduplicate_binary_clauses_wl (Neg A) CS Sa;
        _ \<leftarrow> ASSERT (get_vmtf_heur_array S = get_vmtf_heur_array Sa);
        RETURN (CS, Sa)
         }
     })
    (\<lambda>(CS, Sa). get_vmtf_heur_array S = get_vmtf_heur_array Sa)
    (\<lambda>(CS, S). get_conflict_wl_is_None_heur S)
    (get_vmtf_heur_array S, Some (get_vmtf_heur_fst S)) (CS, S);
    RETURN S
    } \<le> \<Down> (twl_st_heur_restart_ana' r u)
     (do {
      x \<leftarrow> ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl S');
      let _ = True;
      let _ = (\<lambda>_::nat literal. None :: (nat \<times> bool) option);
      x \<leftarrow> iterate_over_VMTFC
       (\<lambda>L (S). do {
          _ \<leftarrow> ASSERT (L \<in># atm_of `# all_init_lits_of_wl S);
          skip \<leftarrow> RES UNIV;
          if skip then RETURN (S)
          else do {
           (S) \<leftarrow> deduplicate_binary_clauses_wl (Pos L) S;
           (S) \<leftarrow> deduplicate_binary_clauses_wl (Neg L) S;
           RETURN (S)
          }
        })
       (\<lambda>(x). \<exists>\<B>'. mark_duplicated_binary_clauses_as_garbage_wl_inv
            (all_init_atms_st S') S' (x, \<B>'))
       (\<lambda>(x). get_conflict_wl x = None) (ns, Some fst_As) (S');
      RETURN x
            })\<close> for CS
    supply [[goals_limit=1]]
    unfolding iterate_over_VMTFC_def
    apply (refine_vcg
      isa_deduplicate_binary_clauses_mark_duplicated_binary_clauses_as_garbage_wl[where r=\<open>length (get_clauses_wl_heur S)\<close> and u=\<open>learned_clss_count S\<close> and
      ns = \<open>get_vmtf_heur S\<close> and lw=\<open>length (get_watched_wl_heur S)\<close>])
    subgoal using assms unfolding mark_duplicated_binary_clauses_as_garbage_pre_wl_heur_def
      by fast
    apply (rule create)
    apply (rule init)
    subgoal by (use vm in \<open>auto simp: get_vmtf_heur_fst_def\<close>)
    subgoal by auto
    subgoal using vm by (auto simp: get_vmtf_heur_array_def)
    subgoal
      apply auto
      apply (subst (asm) get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id])
      apply (auto simp: get_conflict_wl_is_None_def)
      apply (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id])
      apply (auto simp: get_conflict_wl_is_None_def)
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule GC_required_skip; assumption)
    apply (rule skip; assumption)
    apply (rule rel0; assumption)
    subgoal by (auto simp add: twl_st_heur_restart_ana_def)
    subgoal by (auto simp add: twl_st_heur_restart_ana_def)
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by (auto simp add: twl_st_heur_restart_ana_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp
    subgoal premises p
      using p(26-) unfolding get_vmtf_heur_array_def by simp
    apply (rule rel; assumption?)
    subgoal by auto
    apply (rule rel2; assumption)
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    done

  show ?thesis
    unfolding isa_mark_duplicated_binary_clauses_as_garbage_wl_alt_def
    apply (rule order_trans)
    defer
    apply (rule ref_two_step'')
    apply (rule subset_refl)
    apply (rule mark_duplicated_binary_clauses_as_garbage_wl2_mark_duplicated_binary_clauses_as_garbage_wl[unfolded Down_id_eq])
    apply (rule order_trans)
    defer
    apply (rule ref_two_step'')
    apply (rule subset_refl)
    apply (rule mark_duplicated_binary_clauses_as_garbage_wl2_ge_\<L>\<^sub>a\<^sub>l\<^sub>l[unfolded Down_id_eq])
    defer
    apply (rule order_trans)
    defer
    apply (rule ref_two_step'')
    apply (rule subset_refl)
    apply (rule bind_refine[of _ _ _ _ Id, unfolded Down_id_eq])
    apply (rule Id_refine)
    apply (rule iterate_over_VMTFC_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC[unfolded Down_id_eq,
      where I = \<open>\<lambda>x. \<exists>\<B>'. mark_duplicated_binary_clauses_as_garbage_wl_inv (all_init_atms_st S') S' (x, \<B>')\<close> and
       P = \<open>\<lambda>x. get_conflict_wl x = None\<close> for \<B>])
    apply (rule 1)
    apply (solves \<open>use 2 in \<open>auto simp: all_init_atms_st_alt_def\<close>\<close>)
    apply (solves \<open>use 3 in \<open>auto simp: all_init_atms_st_alt_def\<close>\<close>)
    apply (solves auto)
    apply (solves auto)
    apply (rule last_step[THEN order_trans])
    by auto (*getting rid of the last RETURN*)
qed


lemma isa_mark_duplicated_binary_clauses_as_garbage_wl2_isa_mark_duplicated_binary_clauses_as_garbage_wl:
  \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl2 S \<le>
  \<Down>Id (isa_mark_duplicated_binary_clauses_as_garbage_wl S)\<close>
proof -
  have H: \<open>a=b\<Longrightarrow> (a,b)\<in>Id\<close> \<open>c=d \<Longrightarrow> c \<le>\<Down>Id d\<close> for a b c d
    by auto
  have K: \<open>(Sb, Sc) \<in> Id \<Longrightarrow>(CSb, CSc) \<in> Id \<Longrightarrow>
    get_vmtf_heur_array S = get_vmtf_heur_array Sb \<Longrightarrow>
    ((CSb, Sb), (CSc, Sc)) \<in> {((CSa, a), (CSb, b)). (CSa, CSb)\<in>Id \<and> (a,b)\<in>Id \<and> get_vmtf_heur_array S = get_vmtf_heur_array a}\<close> for Sb Sc CSb CSc
    by auto
  show ?thesis
    unfolding isa_mark_duplicated_binary_clauses_as_garbage_wl2_def
      isa_mark_duplicated_binary_clauses_as_garbage_wl_def nres_monad3 Let_def
    apply refine_rcg
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    apply (rule K)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    apply (rule K; assumption?)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma isa_mark_duplicated_binary_clauses_as_garbage_wl_mark_duplicated_binary_clauses_as_garbage_wl2:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl2 S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (mark_duplicated_binary_clauses_as_garbage_wl S')\<close>
  apply (rule order_trans)
  apply (rule isa_mark_duplicated_binary_clauses_as_garbage_wl2_isa_mark_duplicated_binary_clauses_as_garbage_wl)
  unfolding Down_id_eq
  apply (rule isa_mark_duplicated_binary_clauses_as_garbage_wl_mark_duplicated_binary_clauses_as_garbage_wl)
  apply (rule assms)+
  done

end
