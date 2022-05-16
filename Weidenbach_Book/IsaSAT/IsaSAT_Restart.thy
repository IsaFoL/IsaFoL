theory IsaSAT_Restart
  imports
    Watched_Literals.WB_Sort Watched_Literals.Watched_Literals_Watch_List_Simp IsaSAT_Rephase_State
    IsaSAT_Setup IsaSAT_VMTF IsaSAT_Sorting IsaSAT_Proofs
begin

chapter \<open>Restarts\<close>

lemma twl_st_heur_change_subsumed_clauses:
  fixes lcount lcount' :: clss_size
  assumes \<open>(S,
     (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)) \<in> twl_st_heur\<close>
    \<open>set_mset (all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)) = set_mset (all_atms_st (M, N, D, NE, UE, NEk, UEk, NS', US', N0, U0, Q, W))\<close>and
    \<open>clss_size_corr N NE UE NEk UEk NS' US' N0 U0 lcount'\<close>
  shows \<open>(set_learned_count_wl_heur lcount' S,
     (M, N, D, NE, UE, NEk, UEk, NS', US', N0, U0, Q, W)) \<in> twl_st_heur\<close>
proof -
  note cong = trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong isa_vmtf_cong heuristic_rel_cong
  note cong2 = D\<^sub>0_cong phase_saving_cong cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
    isasat_input_bounded_cong
  show ?thesis
    supply[[goals_limit=1]]
    supply [dest!] = cong[OF assms(2)]
    using assms(1) assms(3) apply -
    unfolding twl_st_heur_def in_pair_collect_simp prod.simps get_trail_wl.simps get_clauses_wl.simps
      get_conflict_wl.simps literals_to_update_wl.simps get_watched_wl.simps
      IsaSAT_Setup.get_unkept_unit_learned_clss_wl.simps
      IsaSAT_Setup.get_kept_unit_init_clss_wl.simps
      IsaSAT_Setup.get_kept_unit_learned_clss_wl.simps get_subsumed_init_clauses_wl.simps
      get_subsumed_learned_clauses_wl.simps get_init_clauses0_wl.simps isasat_state_simp
       get_learned_clauses0_wl.simps IsaSAT_Setup.get_unkept_unit_init_clss_wl.simps
    apply normalize_goal+
    apply (subst (asm) cong2[OF assms(2)])+
    apply (intro conjI)
    apply ((drule cong[OF assms(2)])+; assumption)+
    done
qed


text \<open>
  This is a list of comments (how does it work for glucose and cadical) to prepare the future
  refinement:
  \<^enum> Reduction
     \<^item> every 2000+300*n (rougly since inprocessing changes the real number, cadical)
           (split over initialisation file); don't restart if level < 2 or if the level is less
       than the fast average
     \<^item> curRestart * nbclausesbeforereduce;
          curRestart = (conflicts / nbclausesbeforereduce) + 1 (glucose)
  \<^enum> Killed
     \<^item> half of the clauses that \<^bold>\<open>can\<close> be deleted (i.e., not used since last restart), not strictly
       LBD, but a probability of being useful.
     \<^item> half of the clauses
  \<^enum> Restarts:
     \<^item> EMA-14, aka restart if enough clauses and slow\_glue\_avg * opts.restartmargin > fast\_glue (file ema.cpp)
     \<^item> (lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts),
       \<^text>\<open>conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()\<close>
\<close>
declare all_atms_def[symmetric,simp]

definition twl_st_heur_restart :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_restart =
  {(S,T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_init_atms N (NE+NEk+NS+N0)) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_init_atms N (NE+NEk+NS+N0)) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N (NE+NEk+NS+N0))) \<and>
    vm \<in> isa_vmtf (all_init_atms N (NE+NEk+NS+N0)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms N (NE+NEk+NS+N0)) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} lcount \<and>
    vdom_m (all_init_atms N (NE+NEk+NS+N0)) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_init_atms N (NE+NEk+NS+N0)) \<and>
    isasat_input_nempty (all_init_atms N (NE+NEk+NS+N0)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_init_atms N (NE+NEk+NS+N0)) heur
  }\<close>


abbreviation twl_st_heur'''' where
  \<open>twl_st_heur'''' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r}\<close>

abbreviation twl_st_heur''''uu where
  \<open>twl_st_heur''''uu r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r \<and>
    learned_clss_count S \<le> u}\<close>

abbreviation twl_st_heur_restart''' where
  \<open>twl_st_heur_restart''' r \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur_restart'''' where
  \<open>twl_st_heur_restart'''' r \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) \<le> r}\<close>

definition twl_st_heur_restart_ana :: \<open>nat \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_restart_ana r =
  {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur_restart_ana' :: \<open>_\<close> where
  \<open>twl_st_heur_restart_ana' r u \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> learned_clss_count S \<le> u}\<close>

lemma twl_st_heur_restart_anaD: \<open>x \<in> twl_st_heur_restart_ana r \<Longrightarrow> x \<in> twl_st_heur_restart\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)

lemma twl_st_heur_restartD:
  \<open>x \<in> twl_st_heur_restart \<Longrightarrow> x \<in> twl_st_heur_restart_ana (length (get_clauses_wl_heur (fst x)))\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)

definition clause_score_ordering2 where
  \<open>clause_score_ordering2 = (\<lambda>(lbd, act) (lbd', act'). lbd < lbd' \<or> (lbd = lbd' \<and> act \<le> act'))\<close>

lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

global_interpretation twl_restart_ops id
  by unfold_locales

global_interpretation twl_restart id
  by standard (rule unbounded_id)

definition empty_Q :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>empty_Q = (\<lambda>S. do{
  j \<leftarrow> mop_isa_length_trail (get_trail_wl_heur S);
  RETURN (set_heur_wl_heur (restart_info_restart_done_heur (get_heur S)) (set_literals_to_update_wl_heur j S))
  })\<close>

definition restart_abs_wl_heur_pre  :: \<open>isasat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_heur_pre S brk  \<longleftrightarrow> (\<exists>T last_GC last_Restart. (S, T) \<in> twl_st_heur \<and> restart_abs_wl_pre T last_GC last_Restart brk)\<close>


named_theorems twl_st_heur_restart

lemma [twl_st_heur_restart]:
  assumes \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>(get_trail_wl_heur S, get_trail_wl T) \<in> trail_pol (all_init_atms_st T)\<close>
  using assms by (cases S; cases T)
   (simp only: twl_st_heur_restart_def get_trail_wl.simps
    mem_Collect_eq prod.case get_clauses_wl.simps get_unit_init_clss_wl.simps all_init_atms_st_def
    all_init_atms_def get_init_clauses0_wl.simps isasat_int.inject get_unkept_unit_init_clss_wl.simps
    get_kept_unit_init_clss_wl.simps
    get_subsumed_init_clauses_wl.simps split: isasat_int.splits)

lemma trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail:
  \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def trail_pol_def
  by auto

lemma refine_generalise1: \<open>A \<le> B \<Longrightarrow> do {x \<leftarrow> B; C x} \<le> D \<Longrightarrow> do {x \<leftarrow> A; C x} \<le> (D:: 'a nres)\<close>
  using Refine_Basic.bind_mono(1) dual_order.trans by blast

lemma refine_generalise2: "A \<le> B \<Longrightarrow> do {x \<leftarrow> do {x \<leftarrow> B; A' x}; C x} \<le> D \<Longrightarrow>
  do {x \<leftarrow> do {x \<leftarrow> A; A' x}; C x} \<le> (D:: 'a nres)"
  by (simp add: refine_generalise1)


lemma trail_pol_no_dup: \<open>(M, M') \<in> trail_pol \<A> \<Longrightarrow> no_dup M'\<close>
  by (auto simp: trail_pol_def)

definition remove_all_annot_true_clause_one_imp_heur
  :: \<open>nat \<times> clss_size \<times> arena \<Rightarrow> (clss_size \<times> arena) nres\<close>
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, j, N). do {
      case arena_status N C of
        DELETED \<Rightarrow> RETURN (j, N)
      | IRRED \<Rightarrow> RETURN (j, extra_information_mark_to_delete N C)
      | LEARNED \<Rightarrow> RETURN (clss_size_decr_lcount j, extra_information_mark_to_delete N C)
  })\<close>

definition remove_all_annot_true_clause_imp_wl_D_pre
  :: \<open>nat multiset \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_pre \<A> L S \<longleftrightarrow> (L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>

definition remove_all_annot_true_clause_imp_wl_D_heur_pre where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur_restart
      \<and> remove_all_annot_true_clause_imp_wl_D_pre (all_init_atms_st S') L S')\<close>

definition minimum_number_between_restarts :: \<open>64 word\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

definition five_uint64 :: \<open>64 word\<close> where
  \<open>five_uint64 = 5\<close>

definition upper_restart_bound_not_reached :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>upper_restart_bound_not_reached = (\<lambda>S.
  of_nat (clss_size_lcount (get_learned_count S)) < 3000 + 1000 * (get_restart_count (get_stats_heur S)))\<close>

definition (in -) lower_restart_bound_not_reached :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>lower_restart_bound_not_reached = (\<lambda>S.
  \<not>opts_reduce (get_opts S) \<or>
   (opts_restart (get_opts S) \<and> 
    (of_nat (clss_size_lcount (get_learned_count S)) < 2000 + 1000 * (get_restart_count (get_stats_heur S)))))\<close>

definition div2 where [simp]: \<open>div2 n = n div 2\<close>

definition safe_minus where \<open>safe_minus a b = (if b \<ge> a then 0 else a - b)\<close>

definition max_restart_decision_lvl :: nat where
  \<open>max_restart_decision_lvl = 300\<close>

definition max_restart_decision_lvl_code :: \<open>32 word\<close> where
  \<open>max_restart_decision_lvl_code = 300\<close>

fun (in -) get_reductions_count :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>get_reductions_count S
  = get_lrestart_count (get_stats_heur S)\<close>

definition GC_required_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>GC_required_heur S n = do {
    n \<leftarrow> RETURN (full_arena_length_st S);
    wasted \<leftarrow> RETURN (wasted_bytes_st S);
    RETURN (3*wasted > ((of_nat n)>>2))
 }\<close>


definition FLAG_no_restart :: \<open>8 word\<close> where
  \<open>FLAG_no_restart = 0\<close>

definition FLAG_restart :: \<open>8 word\<close> where
  \<open>FLAG_restart = 1\<close>

definition FLAG_Reduce_restart :: \<open>8 word\<close> where
  \<open>FLAG_Reduce_restart = 3\<close>

definition FLAG_GC_restart :: \<open>8 word\<close> where
  \<open>FLAG_GC_restart = 2\<close>

definition FLAG_Inprocess_restart :: \<open>8 word\<close> where
  \<open>FLAG_Inprocess_restart = 4\<close>

definition restart_flag_rel :: \<open>(8 word \<times> restart_type) set\<close> where
  \<open>restart_flag_rel = {(FLAG_no_restart, NO_RESTART), (FLAG_restart, RESTART), (FLAG_GC_restart, GC),
  (FLAG_Reduce_restart, GC), (FLAG_Inprocess_restart, INPROCESS)}\<close>

definition GC_units_required :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>GC_units_required T \<longleftrightarrow> units_since_last_GC_st T \<ge> get_GC_units_opt T\<close>

lemma clss_size_corr_restart_simp2:
  \<open>NO_MATCH {#} UE \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c =
  clss_size_corr_restart N NE {#} NEk UEk NS US N0 U0 c\<close>
  \<open>NO_MATCH {#} US \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c =
   clss_size_corr_restart N NE UE NEk UEk NS {#} N0 U0 c\<close>
  \<open>NO_MATCH {#} U0 \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c =
  clss_size_corr_restart N NE UE NEk UEk NS US N0 {#} c\<close> and
  clss_size_corr_restart_intro:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow>
  clss_size_corr_restart (fmdrop C N) NE UE NEk UEk NS US' N0 U0' (clss_size_decr_lcount c)\<close>
  by (auto simp: clss_size_corr_restart_def)

lemma mark_garbage_heur_wl:
  assumes
    ST: \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>\<not> irred (get_clauses_wl T) C\<close> and \<open>i < length (get_tvdom S)\<close> and
    iC: \<open>get_tvdom S ! i = C\<close>
  shows \<open>(mark_garbage_heur3 C i S, mark_garbage_wl C T) \<in> twl_st_heur_restart\<close>
proof -
  show ?thesis
    using assms distinct_mset_dom[of \<open>get_clauses_wl T\<close>]
      distinct_mset_mono[of \<open>mset (get_avdom S)\<close> \<open>mset (get_vdom S)\<close>]
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_def mark_garbage_heur3_def mark_garbage_wl_def)
  by (auto simp: twl_st_heur_restart_def mark_garbage_heur3_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If clss_size_corr_restart_intro
    simp: all_init_atms_def all_init_lits_def aivdom_inv_dec_remove_clause
     simp del: all_init_atms_def[symmetric]
    intro: valid_arena_extra_information_mark_to_delete'
    intro!: aivdom_inv_dec_remove_and_swap_inactive_tvdom
    aivdom_inv_dec_remove_and_swap_inactive
      dest!: in_set_butlastD in_vdom_m_fmdropD
    elim!: in_set_upd_cases)
qed

lemma mark_garbage_heur_wl_ana:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>\<not> irred (get_clauses_wl T) C\<close> \<open>C = get_tvdom S ! i\<close> \<open>i < length (get_tvdom S)\<close>
  shows \<open>(mark_garbage_heur3 C i S, mark_garbage_wl C T) \<in> twl_st_heur_restart_ana r\<close>
proof -
  have [intro!]: \<open>distinct n \<Longrightarrow> mset n \<subseteq># mset m \<Longrightarrow> mset (removeAll (n ! i) n) \<subseteq># mset m\<close> for n A m
    by (metis filter_mset_eq_conv mset_filter removeAll_filter_not_eq subset_mset.dual_order.trans)

  show ?thesis
    using assms
    using assms distinct_mset_dom[of \<open>get_clauses_wl T\<close>]
      distinct_mset_mono[of \<open>mset (get_avdom S)\<close> \<open>mset (get_vdom S)\<close>]
    apply (cases S; cases T)
    apply (simp add: twl_st_heur_restart_ana_def mark_garbage_heur3_def mark_garbage_wl_def)
    by (auto simp: twl_st_heur_restart_def mark_garbage_heur3_def mark_garbage_wl_def
      learned_clss_l_l_fmdrop size_remove1_mset_If init_clss_l_fmdrop_irrelev aivdom_inv_dec_remove_clause
      valid_arena_extra_information_mark_to_delete' clss_size_corr_restart_intro
      simp: all_init_atms_def all_init_lits_def clss_size_corr_restart_simp2
      simp del: all_init_atms_def[symmetric] clss_size_corr_restart_simp
      intro: valid_arena_extra_information_mark_to_delete'
      intro!: aivdom_inv_dec_remove_and_swap_inactive
      aivdom_inv_dec_remove_and_swap_inactive_tvdom
      dest!: in_set_butlastD in_vdom_m_fmdropD
      elim!: in_set_upd_cases)
qed

lemma mark_unused_st_heur_ana:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>(mark_unused_st_heur C S, T) \<in> twl_st_heur_restart_ana r\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_ana_def mark_unused_st_heur_def)
  apply (auto simp: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If
     simp: all_init_atms_def all_init_lits_def
     simp del: all_init_atms_def[symmetric]
     intro!: valid_arena_mark_unused
     dest!: in_set_butlastD in_vdom_m_fmdropD
     elim!: in_set_upd_cases)
  done

lemma twl_st_heur_restart_valid_arena[twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
  using assms by (auto simp: twl_st_heur_restart_def)

lemma twl_st_heur_restart_get_avdom_nth_get_vdom[twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> \<open>i < length (get_avdom S)\<close>
  shows \<open>get_avdom S ! i \<in> set (get_vdom S)\<close>
  using assms by (auto 5 3 simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
    dest!: set_mset_mono)

lemma twl_st_heur_restart_get_tvdom_nth_get_vdom[twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> \<open>i < length (get_tvdom S)\<close>
  shows \<open>get_tvdom S ! i \<in> set (get_vdom S)\<close>
  using assms by (auto 5 3 simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
    dest!: set_mset_mono)

lemma [twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in> set (get_avdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
proof -
  show \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close>
    using assms
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_dom_status_iff(1) aivdom_inv_dec_alt_def
        split: prod.splits)
  assume C: \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  show \<open>arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
qed


lemma [twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>C \<in> set (get_avdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
    using assms
    by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart)

lemma [twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in> set (get_tvdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
proof -
  show \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close>
    using assms
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_dom_status_iff(1) aivdom_inv_dec_alt_def
        split: prod.splits)
  assume C: \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  show \<open>arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
qed

lemma [twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>C \<in> set (get_tvdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
    using assms
    by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart)

definition number_clss_to_keep :: \<open>isasat \<Rightarrow> nat nres\<close> where
  \<open>number_clss_to_keep = (\<lambda>S.
    RES UNIV)\<close>

definition number_clss_to_keep_impl :: \<open>isasat \<Rightarrow> nat nres\<close> where
  \<open>number_clss_to_keep_impl = (\<lambda>S.
    RETURN (length_tvdom_aivdom (get_aivdom S) >> 1))\<close>

lemma number_clss_to_keep_impl_number_clss_to_keep:
  \<open>(number_clss_to_keep_impl, number_clss_to_keep) \<in> Id \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (auto simp: number_clss_to_keep_impl_def number_clss_to_keep_def Let_def intro!: frefI nres_relI)

(* TODO Missing : The sorting function + definition of l should depend on the number of initial
  clauses *)
definition (in -) MINIMUM_DELETION_LBD :: nat where
  \<open>MINIMUM_DELETION_LBD = 3\<close>

lemma in_set_delete_index_and_swapD:
  \<open>x \<in> set (delete_index_and_swap xs i) \<Longrightarrow> x \<in> set xs\<close>
  apply (cases \<open>i < length xs\<close>)
  apply (auto dest!: in_set_butlastD)
  by (metis List.last_in_set in_set_upd_cases list.size(3) not_less_zero)

lemma delete_index_vdom_heur_twl_st_heur_restart_ana:
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> i < length (get_tvdom S) \<Longrightarrow>
  get_tvdom S ! i \<notin># dom_m (get_clauses_wl T) \<Longrightarrow>
    (delete_index_vdom_heur i S, T) \<in> twl_st_heur_restart_ana r\<close>
  using in_set_delete_index_and_swapD[of _ \<open>get_tvdom S\<close> i]
    distinct_mset_mono[of \<open>mset (get_tvdom S)\<close> \<open>mset (get_vdom S)\<close>]
  supply [[goals_limit=1]]
  by (clarsimp simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def delete_index_vdom_heur_def)
    (auto intro!: aivdom_inv_dec_removed_inactive_tvdom)


lemma incr_wasted_st:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close>
  shows \<open>(incr_wasted_st C S, T) \<in> twl_st_heur_restart_ana r\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_ana_def incr_wasted_st_def)
   apply (auto simp: twl_st_heur_restart_def heuristic_rel_stats_def
     learned_clss_l_l_fmdrop size_remove1_mset_If phase_save_heur_rel_def
     simp: all_init_atms_def all_init_lits_def 
     simp del: all_init_atms_def[symmetric]
     intro!: valid_arena_mark_unused
     dest!: in_set_butlastD in_vdom_m_fmdropD
     elim!: in_set_upd_cases)
  done


lemma twl_st_heur_restart_same_annotD:
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> Propagated L C \<in> set (get_trail_wl T) \<Longrightarrow>
     Propagated L C' \<in> set (get_trail_wl T) \<Longrightarrow> C = C'\<close>
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> Propagated L C \<in> set (get_trail_wl T) \<Longrightarrow>
     Decided L \<in> set (get_trail_wl T) \<Longrightarrow> False\<close>
  by (auto simp: twl_st_heur_restart_def dest: no_dup_no_propa_and_dec
    no_dup_same_annotD)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_mono:
  \<open>set_mset \<A> \<subseteq> set_mset \<B> \<Longrightarrow> L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<B>\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma all_lits_of_mm_mono2:
  \<open>x \<in># (all_lits_of_mm A) \<Longrightarrow> set_mset A \<subseteq> set_mset B \<Longrightarrow> x \<in># (all_lits_of_mm B)\<close>
  by (auto simp: all_lits_of_mm_def)


lemma \<L>\<^sub>a\<^sub>l\<^sub>l_init_all:
  \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a) \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1a)\<close>
  using all_init_lits_of_wl_all_lits_st \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms
    \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) by blast



lemma twl_st_heur_restartD2:
  \<open>x \<in> twl_st_heur_restart \<Longrightarrow> x \<in> twl_st_heur_restart_ana' (length (get_clauses_wl_heur (fst x)))
  (learned_clss_count (fst x))\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_init_lits_of_mm:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_init_lits N NUE)) = set_mset (all_init_lits N NUE)\<close>
  by (auto simp: all_init_lits_def \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm)
abbreviation trail_get_reason :: \<open>trail_pol \<Rightarrow> _\<close> where
  \<open>trail_get_reason \<equiv> (\<lambda>(M, val, lvls, reason, k). reason)\<close>
definition trail_update_reason_at :: \<open>_ \<Rightarrow> _ \<Rightarrow> trail_pol \<Rightarrow> _\<close> where
  \<open>trail_update_reason_at \<equiv> (\<lambda>L C (M, val, lvls, reason, k). (M, val, lvls, reason[atm_of L := C], k))\<close>

definition replace_reason_in_trail :: \<open>nat literal \<Rightarrow> _\<close> where
  \<open>replace_reason_in_trail L C = (\<lambda>M. do {
    ASSERT(atm_of L < length (trail_get_reason M));
    RETURN (trail_update_reason_at L 0 M)
  })\<close>

definition isasat_replace_annot_in_trail
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
  where
  \<open>isasat_replace_annot_in_trail L C = (\<lambda>S. do {
    let lcount = clss_size_resetUS0 (get_learned_count S);
    M \<leftarrow> replace_reason_in_trail L C (get_trail_wl_heur S);
    RETURN (set_trail_wl_heur M (set_learned_count_wl_heur lcount S))
  })\<close>

lemma trail_pol_replace_annot_in_trail_spec:
  assumes
    \<open>atm_of x2 < length (trail_get_reason (get_trail_wl_heur S))\<close> and
    x2: \<open>atm_of x2 \<in># all_init_atms_st (ys @ Propagated x2 C # zs, x2n')\<close> and
    \<open>(S, (ys @ Propagated x2 C # zs, x2n'))
    \<in> twl_st_heur_restart_ana r\<close> and
    M: \<open>M = get_trail_wl_heur S\<close>
  shows
    \<open>(set_trail_wl_heur (trail_update_reason_at x2 0 M) S,
        (ys @ Propagated x2 0 # zs, x2n'))
       \<in> twl_st_heur_restart_ana r\<close>
proof -
  let ?S = \<open>(ys @ Propagated x2 C # zs, x2n')\<close>
  let ?\<A> = \<open>all_init_atms_st ?S\<close>
  have pol: \<open>(get_trail_wl_heur S, ys @ Propagated x2 C # zs)
         \<in> trail_pol (all_init_atms_st ?S)\<close>
    using assms(3) unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_def all_init_atms_st_def
    by (cases x2n') auto
  obtain x y x1b x1c x1d x1e x2d where
    tr: \<open>get_trail_wl_heur S = (x1b, x1c, x1d, x1e, x2d)\<close> and
    x2d: \<open>x2d = (count_decided (ys @ Propagated x2 C # zs), y)\<close> and
    reasons: \<open>((map lit_of (rev (ys @ Propagated x2 C # zs)), x1e),
      ys @ Propagated x2 C # zs)
     \<in> ann_lits_split_reasons ?\<A>\<close> and
    pol: \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>.        nat_of_lit L < length x1c \<and>
        x1c ! nat_of_lit L = polarity (ys @ Propagated x2 C # zs) L\<close> and
    n_d: \<open>no_dup (ys @ Propagated x2 C # zs)\<close> and
    lvls: \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>. atm_of L < length x1d \<and>
        x1d ! atm_of L = get_level (ys @ Propagated x2 C # zs) L\<close> and
    \<open>undefined_lit ys (lit_of (Propagated x2 C))\<close> and
    \<open>undefined_lit zs (lit_of (Propagated x2 C))\<close> and
    inA:\<open>\<forall>L\<in>set (ys @ Propagated x2 C # zs). lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close> and
    cs: \<open>control_stack y (ys @ Propagated x2 C # zs)\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail ?\<A> (ys @ Propagated x2 C # zs)\<close> and
    \<open>length (ys @ Propagated x2 C # zs) < uint32_max\<close> and
    \<open>length (ys @ Propagated x2 C # zs) \<le> uint32_max div 2 + 1\<close> and
    \<open>count_decided (ys @ Propagated x2 C # zs) < uint32_max\<close> and
    \<open>length (map lit_of (rev (ys @ Propagated x2 C # zs))) =
     length (ys @ Propagated x2 C # zs)\<close> and
    bounded: \<open>isasat_input_bounded ?\<A>\<close> and
    x1b: \<open>x1b = map lit_of (rev (ys @ Propagated x2 C # zs))\<close>
    using pol unfolding trail_pol_alt_def
    apply (cases \<open>get_trail_wl_heur S\<close>)
    by blast
  have lev_eq: \<open>get_level (ys @ Propagated x2 C # zs) =
    get_level (ys @ Propagated x2 0 # zs)\<close>
    \<open>count_decided (ys @ Propagated x2 C # zs) =
      count_decided (ys @ Propagated x2 0 # zs)\<close>
    by (auto simp: get_level_cons_if get_level_append_if)
  have [simp]: \<open>atm_of x2 < length x1e\<close>
    using reasons x2 assms(1) unfolding tr by auto

  have \<open>((x1b, x1e[atm_of x2 := 0]), ys @ Propagated x2 0 # zs)
       \<in> ann_lits_split_reasons ?\<A>\<close>
    using reasons n_d undefined_notin
    by (auto simp: ann_lits_split_reasons_def x1b
      DECISION_REASON_def atm_of_eq_atm_of)
  moreover have n_d': \<open>no_dup (ys @ Propagated x2 0 # zs)\<close>
    using n_d by auto
  moreover have \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>.
     nat_of_lit L < length x1c \<and>
        x1c ! nat_of_lit L = polarity (ys @ Propagated x2 0 # zs) L\<close>
    using pol by (auto simp: polarity_def)
  moreover have \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>.
    atm_of L < length x1d \<and>
           x1d ! atm_of L = get_level (ys @ Propagated x2 0 # zs) L\<close>
    using lvls by (auto simp: get_level_append_if get_level_cons_if)
  moreover have \<open>control_stack y (ys @ Propagated x2 0 # zs)\<close>
    using cs apply -
    apply (subst control_stack_alt_def[symmetric, OF n_d'])
    apply (subst (asm) control_stack_alt_def[symmetric, OF n_d])
    unfolding control_stack'_def lev_eq
    apply normalize_goal
    apply (intro ballI conjI)
    apply (solves auto)
    unfolding set_append list.set(2) Un_iff insert_iff
    apply (rule disjE, assumption)
    subgoal for L
      by (drule_tac x = L in bspec)
        (auto simp: nth_append nth_Cons split: nat.splits)
    apply (rule disjE[of \<open>_ = _\<close>], assumption)
    subgoal for L
      by (auto simp: nth_append nth_Cons split: nat.splits)
    subgoal for L
      by (drule_tac x = L in bspec)
        (auto simp: nth_append nth_Cons split: nat.splits)
    done
  ultimately have
    \<open>((x1b, x1c, x1d, x1e[atm_of x2 := 0], x2d), ys @ Propagated x2 0 # zs)
         \<in> trail_pol ?\<A>\<close>
    using n_d x2 inA bounded
    unfolding trail_pol_def x2d
    by simp
  moreover { fix aaa ca
    have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms aaa ca) (ys @ Propagated x2 C # zs) =
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms aaa ca) (ys @ Propagated x2 0 # zs)\<close>
       by (auto simp: vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    then have \<open>isa_vmtf (all_init_atms aaa ca) (ys @ Propagated x2 C # zs) =
      isa_vmtf (all_init_atms aaa ca) (ys @ Propagated x2 0 # zs)\<close>
      by (auto simp: isa_vmtf_def vmtf_def
	image_iff)
  }
  moreover { fix D
    have \<open>get_level (ys @ Propagated x2 C # zs) = get_level (ys @ Propagated x2 0 # zs)\<close>
      by (auto simp: get_level_append_if get_level_cons_if)
    then have \<open>counts_maximum_level (ys @ Propagated x2 C # zs) D =
      counts_maximum_level (ys @ Propagated x2 0 # zs) D\<close> and
      \<open>out_learned (ys @ Propagated x2 C # zs) = out_learned (ys @ Propagated x2 0 # zs)\<close>
      by (auto simp: counts_maximum_level_def card_max_lvl_def
        out_learned_def intro!: ext)
  }
  ultimately show ?thesis
    using assms(3) unfolding twl_st_heur_restart_ana_def M
    by (cases x2n')
      (auto simp: twl_st_heur_restart_def all_init_atms_st_def tr trail_update_reason_at_def
        simp flip: mset_map drop_map)
qed

lemmas trail_pol_replace_annot_in_trail_spec2 =
  trail_pol_replace_annot_in_trail_spec[of \<open>- _\<close>, simplified]

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_ball_all:
  \<open>(\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NUE). P L) = (\<forall>L \<in># all_lits N NUE. P L)\<close>
  \<open>(\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NUE). P L) = (\<forall>L \<in># all_init_lits N NUE. P L)\<close>
  by (simp_all add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits  \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms)

lemma clss_size_corr_restart_intro3[intro]:
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 lcount \<Longrightarrow>
  clss_size_corr_restart N NE UE NEk UEk NS {#} N0 {#} (clss_size_resetUS0 lcount)\<close>
  by (auto simp: clss_size_corr_restart_def clss_size_resetUS_def clss_size_def
    clss_size_resetU0_def clss_size_resetUE_def)

lemma twl_st_heur_restart_ana_US_empty:
  \<open>NO_MATCH {#} US \<Longrightarrow> NO_MATCH {#} U0 \<Longrightarrow>  NO_MATCH {#} UE \<Longrightarrow> (S, M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, W, Q) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
   (set_learned_count_wl_heur (clss_size_resetUS0 (get_learned_count S)) S, M, N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, W, Q)
       \<in> twl_st_heur_restart_ana r\<close>
  by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
    intro: clss_size_corr_simp)

fun equality_except_trail_empty_US_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>equality_except_trail_empty_US_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, WS, Q)
     (M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', WS', Q') \<longleftrightarrow>
  N = N' \<and> D = D' \<and> NE = NE' \<and> NEk = NEk' \<and> UEk = UEk' \<and> NS = NS' \<and> US = {#} \<and> UE = {#} \<and>
  N0' = N0 \<and> U0 = {#} \<and> WS = WS' \<and> Q = Q'\<close>

lemma equality_except_conflict_wl_get_clauses_wl:
    \<open>equality_except_conflict_wl S Y \<Longrightarrow> get_clauses_wl S = get_clauses_wl Y\<close> and
  equality_except_conflict_wl_get_trail_wl:
    \<open>equality_except_conflict_wl S Y \<Longrightarrow> get_trail_wl S = get_trail_wl Y\<close> and
  equality_except_trail_empty_US_wl_get_conflict_wl:
    \<open>equality_except_trail_empty_US_wl S Y \<Longrightarrow> get_conflict_wl S = get_conflict_wl Y\<close> and
  equality_except_trail_empty_US_wl_get_clauses_wl:
    \<open>equality_except_trail_empty_US_wl S Y\<Longrightarrow> get_clauses_wl S = get_clauses_wl Y\<close>
 by (cases S; cases Y; solves auto)+

lemma isasat_replace_annot_in_trail_replace_annot_in_trail_spec:
  \<open>(((L, C), S), ((L', C'), S')) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur_restart_ana' r u \<Longrightarrow>
  isasat_replace_annot_in_trail L C S \<le>
    \<Down>{(U, U'). (U, U') \<in> twl_st_heur_restart_ana' r u \<and>
        get_clauses_wl_heur U = get_clauses_wl_heur S \<and>
        get_learned_count U = clss_size_resetUS0 (get_learned_count S) \<and>
       get_vdom U = get_vdom S \<and>
       equality_except_trail_empty_US_wl U' S'}
    (replace_annot_wl L' C' S')\<close>
  unfolding isasat_replace_annot_in_trail_def replace_annot_wl_def
    uncurry_def replace_reason_in_trail_def nres_monad3
  apply (cases S', hypsubst, unfold prod.case)
  apply refine_rcg
  subgoal
    by (auto simp: trail_pol_alt_def ann_lits_split_reasons_def \<L>\<^sub>a\<^sub>l\<^sub>l_ball_all all_init_lits_of_wl_def
      twl_st_heur_restart_def twl_st_heur_restart_ana_def replace_annot_wl_pre_def
      all_init_lits_alt_def(2))
  subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
    unfolding replace_annot_wl_pre_def replace_annot_l_pre_def bind_to_let_conv Let_def
    apply (clarify dest!: split_list[of \<open>Propagated _ _\<close>])
    apply (rule RETURN_SPEC_refine)
    apply (rule_tac x = \<open>(ys @ Propagated L 0 # zs, x2, x1a, x2a, {#}, x2b, x1c, x2c, {#}, x2d, {#}, x2e, x1f)\<close> in exI)
    apply (intro conjI)
    prefer 2
    apply (rule_tac x = \<open>ys @ Propagated L 0 # zs\<close> in exI)
    apply (intro conjI)
    apply blast
    by (auto intro!: trail_pol_replace_annot_in_trail_spec[where C=C]
        trail_pol_replace_annot_in_trail_spec2
      simp: atm_of_eq_atm_of all_init_atms_def replace_annot_wl_pre_def
      \<L>\<^sub>a\<^sub>l\<^sub>l_ball_all replace_annot_l_pre_def state_wl_l_def all_init_lits_of_wl_def
      all_init_lits_def ac_simps
        twl_st_heur_restart_ana_US_empty learned_clss_count_def  all_init_atms_st_def
      simp del: all_init_atms_def[symmetric]; fail)+
  done

definition remove_one_annot_true_clause_one_imp_wl_D_heur
  :: \<open>nat \<Rightarrow> isasat \<Rightarrow> (nat \<times> isasat) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl_D_heur = (\<lambda>i S\<^sub>0. do {
      (L, C) \<leftarrow> do {
        L \<leftarrow> isa_trail_nth (get_trail_wl_heur S\<^sub>0) i;
	C \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur S\<^sub>0) L;
	RETURN (L, C)};
      ASSERT(C \<noteq> None \<and> i + 1 \<le> Suc (uint32_max div 2));
      if the C = 0 then RETURN (i+1, S\<^sub>0)
      else do {
        ASSERT(C \<noteq> None);
        S \<leftarrow> isasat_replace_annot_in_trail L (the C) S\<^sub>0;
        log_del_clause_heur S (the C);
	ASSERT(mark_garbage_pre (get_clauses_wl_heur S, the C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) (the C) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
        S \<leftarrow> mark_garbage_heur4 (the C) S;
        \<comment> \<open>\<^text>\<open>S \<leftarrow> remove_all_annot_true_clause_imp_wl_D_heur L S;\<close>\<close>
        RETURN (i+1, S)
      }
  })\<close>

definition cdcl_twl_full_restart_wl_D_GC_prog_heur_post :: \<open>isasat \<Rightarrow> isasat \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_D_GC_prog_heur_post S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
    cdcl_twl_full_restart_wl_GC_prog_post S' T')\<close>

definition remove_one_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>isasat \<Rightarrow> (nat \<times> isasat) \<Rightarrow> bool\<close> where
  \<open>remove_one_annot_true_clause_imp_wl_D_heur_inv S = (\<lambda>(i, T).
    (\<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
     remove_one_annot_true_clause_imp_wl_inv S' (i, T') \<and>
     learned_clss_count T \<le> learned_clss_count S))\<close>

definition empty_US  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>empty_US = (\<lambda>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
  (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))\<close>


definition remove_one_annot_true_clause_imp_wl_D_heur :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl_D_heur = (\<lambda>S. do {
    ASSERT((isa_length_trail_pre o get_trail_wl_heur) S);
    k \<leftarrow> (if count_decided_st_heur S = 0
      then RETURN (isa_length_trail (get_trail_wl_heur S))
      else get_pos_of_level_in_trail_imp (get_trail_wl_heur S) 0);
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_D_heur_inv S\<^esup>
      (\<lambda>(i, S). i < k)
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl_D_heur i S)
      (0, S);
    RETURN (empty_US_heur S)
  })\<close>

lemma get_pos_of_level_in_trail_le_decomp:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>get_pos_of_level_in_trail (get_trail_wl T) 0
         \<le> SPEC
            (\<lambda>k. \<exists>M1. (\<exists>M2 K.
                          (Decided K # M1, M2)
                          \<in> set (get_all_ann_decomposition (get_trail_wl T))) \<and>
                      count_decided M1 = 0 \<and> k = length M1)\<close>
  unfolding get_pos_of_level_in_trail_def
proof (rule SPEC_rule)
  fix x
  assume H: \<open>x < length (get_trail_wl T) \<and>
        is_decided (rev (get_trail_wl T) ! x) \<and>
        get_level (get_trail_wl T) (lit_of (rev (get_trail_wl T) ! x)) = 0 + 1\<close>
  let ?M1 = \<open>rev (take x (rev (get_trail_wl T)))\<close>
  let ?K =  \<open>Decided ((lit_of(rev (get_trail_wl T) ! x)))\<close>
  let ?M2 = \<open>rev (drop  (Suc x) (rev (get_trail_wl T)))\<close>
  have T: \<open>(get_trail_wl T) = ?M2 @ ?K # ?M1\<close> and
     K: \<open>Decided (lit_of ?K) = ?K\<close>
    apply (subst append_take_drop_id[symmetric, of _ \<open>length (get_trail_wl T) - Suc x\<close>])
    apply (subst Cons_nth_drop_Suc[symmetric])
    using H
    apply (auto simp: rev_take rev_drop rev_nth)
    apply (cases \<open>rev (get_trail_wl T) ! x\<close>)
    apply (auto simp: rev_take rev_drop rev_nth)
    done
  have n_d: \<open>no_dup (get_trail_wl T)\<close>
    using assms(1)
    by (auto simp: twl_st_heur_restart_def)
  obtain M2 where
    \<open>(?K # ?M1, M2) \<in> set (get_all_ann_decomposition (get_trail_wl T))\<close>
    using get_all_ann_decomposition_ex[of \<open>lit_of ?K\<close> ?M1 ?M2]
    apply (subst (asm) K)
    apply (subst (asm) K)
    apply (subst (asm) T[symmetric])
    by blast
  moreover have \<open>count_decided ?M1 = 0\<close>
    using n_d H
    by (subst (asm)(1) T, subst (asm)(11)T, subst T) auto
  moreover have \<open>x = length ?M1\<close>
    using n_d H by auto
  ultimately show \<open>\<exists>M1. (\<exists>M2 K. (Decided K # M1, M2)
                 \<in> set (get_all_ann_decomposition (get_trail_wl T))) \<and>
             count_decided M1 = 0 \<and> x = length M1 \<close>
    by blast
qed

lemma twl_st_heur_restart_isa_length_trail_get_trail_wl:
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> mop_isa_length_trail (get_trail_wl_heur S) = RETURN (length (get_trail_wl T))\<close>
  unfolding isa_length_trail_def twl_st_heur_restart_ana_def twl_st_heur_restart_def trail_pol_alt_def
    mop_isa_length_trail_def isa_length_trail_pre_def
  by (subgoal_tac \<open>(case get_trail_wl_heur S of
            (M', xs, lvls, reasons, k, cs) \<Rightarrow> length M' \<le> uint32_max)\<close>)
    (cases S;auto dest: ann_lits_split_reasons_map_lit_of intro!: ASSERT_leI; fail)+

lemma twl_st_heur_restart_count_decided_st_alt_def:
  fixes S :: isasat
  shows \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> count_decided_st_heur S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_restart_ana_def trail_pol_def twl_st_heur_restart_def
  by (cases T) (auto simp: count_decided_st_heur_def count_decided_pol_def)

lemma twl_st_heur_restart_trailD:
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
    (get_trail_wl_heur S, get_trail_wl T) \<in> trail_pol (all_init_atms_st T)\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def all_init_atms_st_def
    get_unit_init_clss_wl_alt_def)

lemma no_dup_nth_proped_dec_notin:
  \<open>no_dup M \<Longrightarrow> k < length M \<Longrightarrow> M ! k = Propagated L C \<Longrightarrow> Decided L \<notin> set M\<close>
  apply (auto dest!: split_list simp: nth_append nth_Cons defined_lit_def in_set_conv_nth
    split: if_splits nat.splits)
  by (metis no_dup_no_propa_and_dec nth_mem)

lemma get_literal_and_reason:
  assumes
    \<open>((k, S), k', T) \<in> nat_rel \<times>\<^sub>f twl_st_heur_restart_ana r\<close> and
    \<open>remove_one_annot_true_clause_one_imp_wl_pre k' T\<close> and
    proped: \<open>is_proped (rev (get_trail_wl T) ! k')\<close>
  shows \<open>do {
           L \<leftarrow> isa_trail_nth (get_trail_wl_heur S) k;
           C \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur S) L;
           RETURN (L, C)
         } \<le> \<Down> {((L, C), L', C'). L = L' \<and> C' = the C \<and> C \<noteq> None}
              (SPEC (\<lambda>p. rev (get_trail_wl T) ! k' = Propagated (fst p) (snd p)))\<close>
proof -
  have n_d: \<open>no_dup (get_trail_wl T)\<close> and
   res: \<open>((k, S), k', T) \<in> nat_rel \<times>\<^sub>f twl_st_heur_restart\<close>
    using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
  from no_dup_nth_proped_dec_notin[OF this(1), of \<open>length (get_trail_wl T) - Suc k'\<close>]
  have dec_notin: \<open>Decided (lit_of (rev (fst T) ! k')) \<notin> set (fst T)\<close>
    using proped assms(2) by (cases T; cases \<open>rev (get_trail_wl T) ! k'\<close>)
     (auto simp: twl_st_heur_restart_def state_wl_l_def
      remove_one_annot_true_clause_one_imp_wl_pre_def twl_st_l_def
      remove_one_annot_true_clause_one_imp_pre_def rev_nth
      dest: no_dup_nth_proped_dec_notin)
  have k': \<open>k' < length (get_trail_wl T)\<close> and [simp]: \<open>fst T = get_trail_wl T\<close>
    using proped assms(2)
    by (cases T; auto simp: twl_st_heur_restart_def state_wl_l_def
      remove_one_annot_true_clause_one_imp_wl_pre_def twl_st_l_def
      remove_one_annot_true_clause_one_imp_pre_def; fail)+
  define k'' where \<open>k'' \<equiv> length (get_trail_wl T) - Suc k'\<close>
  have k'': \<open>k'' < length (get_trail_wl T)\<close>
    using k' by (auto simp: k''_def)
  have \<open>rev (get_trail_wl T) ! k' = get_trail_wl T ! k''\<close>
    using k' k'' by (auto simp: k''_def nth_rev)
  then have \<open>rev_trail_nth (fst T) k' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T)\<close>
    using k'' assms nth_mem[OF k']
    by (auto simp: twl_st_heur_restart_ana_def rev_trail_nth_def get_unit_init_clss_wl_alt_def
      trail_pol_alt_def twl_st_heur_restart_def all_init_atms_st_def)
  then have 1: \<open>(SPEC (\<lambda>p. rev (get_trail_wl T) ! k' = Propagated (fst p) (snd p))) =
    do {
      L \<leftarrow> RETURN (rev_trail_nth (fst T) k');
      ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
      C \<leftarrow> (get_the_propagation_reason (fst T) L);
      ASSERT(C \<noteq> None);
      RETURN (L, the C)
    }\<close>
    using proped dec_notin k' nth_mem[OF k''] no_dup_same_annotD[OF n_d]
    apply (subst dual_order.eq_iff)
    apply (rule conjI)
    subgoal
      unfolding get_the_propagation_reason_def
      apply (cases \<open>rev (get_trail_wl T) ! k'\<close>)
      apply (auto simp: RES_RES_RETURN_RES rev_trail_nth_def
            get_the_propagation_reason_def lits_of_def rev_nth
  	    RES_RETURN_RES
           dest: split_list
	    simp flip: k''_def
	    intro!: le_SPEC_bindI[of _ \<open>Some (mark_of (get_trail_wl T ! k''))\<close>])
      apply (cases \<open>rev (get_trail_wl T) ! k'\<close>) (*TODO proof*)
      apply  (auto simp: RES_RES_RETURN_RES rev_trail_nth_def RES_ASSERT_moveout
          get_the_propagation_reason_def lits_of_def rev_nth
	  RES_RETURN_RES
        simp flip: k''_def
        dest: split_list
        intro!: exI[of _ \<open>Some (mark_of (rev (get_trail_wl T) ! k'))\<close>])
	  apply (subst RES_ASSERT_moveout)
	    by (auto 4 3 simp: RES_RETURN_RES image_iff
        dest: split_list
        intro!: exI[of _ \<open>Some (mark_of ((get_trail_wl T) ! k''))\<close>])
    subgoal
      apply (cases \<open>rev (get_trail_wl T) ! k'\<close>) (*TODO proof*)
      apply  (auto simp: RES_RES_RETURN_RES rev_trail_nth_def RES_ASSERT_moveout
          get_the_propagation_reason_def lits_of_def rev_nth
	  RES_RETURN_RES
        simp flip: k''_def
        dest: split_list
        intro!: exI[of _ \<open>Some (mark_of (rev (get_trail_wl T) ! k'))\<close>])
	  apply (subst RES_ASSERT_moveout)
	    by (auto 4 3 simp: RES_RETURN_RES image_iff
        dest: split_list
        intro!: exI[of _ \<open>Some (mark_of ((get_trail_wl T) ! k''))\<close>])
    done

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (subst 1)
    apply (refine_rcg
      isa_trail_nth_rev_trail_nth[THEN fref_to_Down_curry, unfolded comp_def,
        of _ _ _ _ \<open>all_init_atms_st T\<close>]
      get_the_propagation_reason_pol[THEN fref_to_Down_curry, unfolded comp_def,
        of \<open>all_init_atms_st T\<close>])
    subgoal using k' by auto
    subgoal using assms by (cases S; auto dest: twl_st_heur_restart_trailD)
    subgoal by auto
    subgoal for K K'
      using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
        all_init_atms_st_def get_unit_init_clss_wl_alt_def)
    subgoal
      by auto
    done
qed


lemma red_in_dom_number_of_learned_ge1: \<open>C' \<in># dom_m baa \<Longrightarrow> \<not> irred baa C' \<Longrightarrow> Suc 0 \<le> size (learned_clss_l baa)\<close>
  by (auto simp: ran_m_def dest!: multi_member_split)


definition find_decomp_wl0 :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>find_decomp_wl0 = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) (M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q', W').
  (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
  count_decided M' = 0) \<and>
  (N', D', NE', UE', NEk', UEk', NS', US, N0, U0, Q', W') = (N, D, NE, UE, NEk, UEk, NS, US', N0', U0', Q, W))\<close>
lemma cdcl_twl_local_restart_wl_spec0_alt_def:
  \<open>cdcl_twl_local_restart_wl_spec0 = (\<lambda>S. do {
    ASSERT(restart_abs_wl_pre2 S False);
    if count_decided (get_trail_wl S) > 0
    then do {
      T \<leftarrow> SPEC(find_decomp_wl0 S);
      RETURN (empty_Q_wl T)
    } else RETURN (empty_US_heur_wl S)})\<close>
  by (intro ext; case_tac S)
   (auto 6 4 simp: cdcl_twl_local_restart_wl_spec0_def
	RES_RETURN_RES2 image_iff RES_RETURN_RES empty_US_heur_wl_def
	find_decomp_wl0_def empty_Q_wl_def uncurry_def
       intro!: bind_cong[OF refl]
      dest: get_all_ann_decomposition_exists_prepend)


lemma cdcl_twl_local_restart_wl_spec0:
  assumes Sy:  \<open>(S, y) \<in> twl_st_heur_restart_ana' r u\<close> and
    \<open>get_conflict_wl y = None\<close>
  shows \<open>do {
      if count_decided_st_heur S > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S;
        empty_Q (empty_US_heur S)
      } else RETURN (empty_US_heur S)
    }
         \<le> \<Down> (twl_st_heur_restart_ana' r u) (cdcl_twl_local_restart_wl_spec0 y)\<close>
proof -
  define upd :: \<open>_ \<Rightarrow> _ \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
    \<open>upd M' vm = (\<lambda> S. set_vmtf_wl_heur vm (set_trail_wl_heur M' S))\<close>
     for M' :: trail_pol and vm

  have find_decomp_wl_st_int_alt_def:
    \<open>find_decomp_wl_st_int = (\<lambda>highest S. do{
      (M', vm) \<leftarrow> isa_find_decomp_wl_imp (get_trail_wl_heur S) highest (get_vmtf_heur S);
      RETURN (upd M' vm S)
    })\<close>
    unfolding upd_def find_decomp_wl_st_int_def
    by (auto intro!: ext)

  have [refine0]: \<open>do {
	  (M', vm) \<leftarrow>
	    isa_find_decomp_wl_imp (get_trail_wl_heur S) 0 (get_vmtf_heur S);
	  RETURN (upd M' vm S)
    } \<le> \<Down> {(S,
     T).
    (set_literals_to_update_wl_heur (isa_length_trail (get_trail_wl_heur S))
     (set_heur_wl_heur (restart_info_restart_done_heur (get_heur S)) S),
	  (empty_Q_wl2 T)) \<in> twl_st_heur_restart_ana' r u \<and>
	  isa_length_trail_pre (get_trail_wl_heur S)} (SPEC (find_decomp_wl0 y))\<close>
     (is \<open>_ \<le> \<Down> ?A _\<close>)
    if
      \<open>0 < count_decided_st_heur S\<close> and
      \<open>0 < count_decided (get_trail_wl y)\<close>
  proof -
    have A:\<open> ?A = {(S,
     T).
    (set_literals_to_update_wl_heur (length (get_trail_wl T))
     (set_heur_wl_heur (restart_info_restart_done_heur (get_heur S)) S),
	  (empty_Q_wl2 T)) \<in> twl_st_heur_restart_ana' r u \<and>
	  isa_length_trail_pre (get_trail_wl_heur S)}\<close>
	  supply[[goals_limit=1]]
      apply (rule ; rule)
      subgoal for x
        apply clarify
	apply (frule twl_st_heur_restart_isa_length_trail_get_trail_wl)
        by (auto simp:  trail_pol_def empty_Q_wl2_def mop_isa_length_trail_def)
      subgoal for x
        apply clarify
	apply (frule twl_st_heur_restart_isa_length_trail_get_trail_wl)
        by (auto simp:  trail_pol_def empty_Q_wl2_def
            mop_isa_length_trail_def learned_clss_count_def)
      done

    let ?\<A> = \<open>all_init_atms_st y\<close>
    have \<open>get_vmtf_heur S \<in> isa_vmtf ?\<A> (get_trail_wl y)\<close>and
      n_d: \<open>no_dup (get_trail_wl y)\<close>
      using Sy
      by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
        all_init_atms_st_def get_unit_init_clss_wl_alt_def)
    then obtain vm' where
      vm': \<open>(get_vmtf_heur S, vm') \<in> Id \<times>\<^sub>f distinct_atoms_rel ?\<A>\<close> and
      vm: \<open>vm' \<in> vmtf (all_init_atms_st y) (get_trail_wl y)\<close>
      unfolding isa_vmtf_def
      by force

    have find_decomp_w_ns_pre:
      \<open>find_decomp_w_ns_pre (all_init_atms_st y) ((get_trail_wl y, 0), vm')\<close>
      using that assms vm' vm unfolding find_decomp_w_ns_pre_def
      by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
        all_init_atms_st_def get_unit_init_clss_wl_alt_def
        dest: trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
    have 1: \<open>isa_find_decomp_wl_imp (get_trail_wl_heur S) 0 (get_vmtf_heur S) \<le>
       \<Down> ({(M, M'). (M, M') \<in> trail_pol ?\<A> \<and> count_decided M' = 0} \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel ?\<A>))
         (find_decomp_w_ns ?\<A> (get_trail_wl y) 0 vm')\<close>
      apply (rule  order_trans)
      apply (rule isa_find_decomp_wl_imp_find_decomp_wl_imp[THEN fref_to_Down_curry2,
        of \<open>get_trail_wl y\<close> 0 vm' _ _ _ ?\<A>])
      subgoal using that by auto
      subgoal
        using Sy vm'
	by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def get_unit_init_clss_wl_alt_def
          all_init_atms_st_def)
      apply (rule order_trans, rule ref_two_step')
      apply (rule find_decomp_wl_imp_find_decomp_wl'[THEN fref_to_Down_curry2,
        of ?\<A> \<open>get_trail_wl y\<close> 0 vm'])
      subgoal by (rule find_decomp_w_ns_pre)
      subgoal by auto
      subgoal
        using n_d
        by (fastforce simp: find_decomp_w_ns_def conc_fun_RES Image_iff)
      done

  show ?thesis
      supply [[goals_limit=1]] unfolding A
      apply (rule bind_refine_res[OF _ 1[unfolded find_decomp_w_ns_def conc_fun_RES]])
      apply (case_tac y, cases S)
      apply clarify
      apply (rule RETURN_SPEC_refine)
      using assms
      by (auto simp: upd_def find_decomp_wl0_def
        intro!: RETURN_SPEC_refine clss_size_corr_simp simp: twl_st_heur_restart_def out_learned_def
	    empty_Q_wl2_def twl_st_heur_restart_ana_def learned_clss_count_def
            all_init_atms_st_def
	intro: isa_vmtfI isa_length_trail_pre dest: no_dup_appendD)
  qed
  have [simp]: \<open>clss_size_corr_restart x1a x1c x1d NEk UEk x1e x1f x1g x1h (ck, cl, cd, cm, cn) \<Longrightarrow>
    clss_size_corr_restart x1a x1c x1d NEk UEk x1e {#} x1g {#} (ck, 0, cd, 0, 0)\<close>
    for  x1a x1c x1d x1e x1f x1g x1h ck cl cm cn NEk UEk cd
    by (auto simp: clss_size_corr_restart_def clss_size_def)

  have Sy': \<open>(empty_US_heur S, empty_US_heur_wl y) \<in> twl_st_heur_restart_ana' r u\<close>
    using Sy by (cases y; cases S; auto simp: twl_st_heur_restart_ana_def
      empty_US_heur_wl_def twl_st_heur_restart_def empty_US_heur_def clss_size_resetUE_def
      clss_size_lcountUEk_def
      clss_size_resetUS_def clss_size_lcount_def clss_size_lcountU0_def clss_size_resetU0_def
      learned_clss_count_def clss_size_def clss_size_lcountUS_def clss_size_lcountUE_def)
  show ?thesis
    unfolding find_decomp_wl_st_int_alt_def
      cdcl_twl_local_restart_wl_spec0_alt_def
    apply refine_vcg
    subgoal
      using Sy by (auto simp: twl_st_heur_restart_count_decided_st_alt_def)
    subgoal for Sa T
      unfolding empty_Q_def empty_Q_wl_def empty_US_heur_def empty_Q_wl2_def
      apply clarify
      apply (frule twl_st_heur_restart_isa_length_trail_get_trail_wl)
      by refine_vcg
       (cases \<open>get_learned_count Sa\<close>, auto simp add: mop_isa_length_trail_def twl_st_heur_restart_ana_def get_unit_init_clss_wl_alt_def
        twl_st_heur_restart_def learned_clss_count_def clss_size_resetUS_def clss_size_lcountUEk_def Let_def
        clss_size_lcount_def clss_size_lcountU0_def clss_size_resetU0_def clss_size_resetUE_def
      learned_clss_count_def clss_size_def clss_size_lcountUS_def clss_size_lcountUE_def)
    subgoal
      using Sy' .
    done
qed

lemma no_get_all_ann_decomposition_count_dec0:
  \<open>(\<forall>M1. (\<forall>M2 K. (Decided K # M1, M2) \<notin> set (get_all_ann_decomposition M))) \<longleftrightarrow>
  count_decided M = 0\<close>
  apply (induction M rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M
    by auto
  subgoal for L C M
    by (cases \<open>get_all_ann_decomposition M\<close>) fastforce+
  done

lemma get_pos_of_level_in_trail_decomp_iff:
  assumes \<open>no_dup M\<close>
  shows \<open>((\<exists>M1 M2 K.
                (Decided K # M1, M2)
                \<in> set (get_all_ann_decomposition M) \<and>
                count_decided M1 = 0 \<and> k = length M1)) \<longleftrightarrow>
    k < length M \<and> count_decided M > 0 \<and> is_decided (rev M ! k) \<and> get_level M (lit_of (rev M ! k)) = 1\<close>
  (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then obtain K M1 M2 where
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    [simp]: \<open>count_decided M1 = 0\<close> and
    k_M1: \<open>length M1 = k\<close>
    by auto
  then have \<open>k < length M\<close>
    by auto
  moreover have \<open>rev M ! k = Decided K\<close>
    using decomp
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: nth_append
      simp flip: k_M1)
  moreover have \<open>get_level M (lit_of (rev M ! k)) = 1\<close>
    using assms decomp
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: get_level_append_if nth_append
      simp flip: k_M1)
  ultimately show ?B
    using decomp by auto
next
  assume ?B
  define K where \<open>K = lit_of (rev M ! k)\<close>
  obtain M1 M2 where
    M: \<open>M = M2 @ Decided K # M1\<close> and
    k_M1: \<open>length M1 = k\<close>
    apply (subst (asm) append_take_drop_id[of \<open>length M - Suc k\<close>, symmetric])
    apply (subst (asm) Cons_nth_drop_Suc[symmetric])
    unfolding K_def
    subgoal using \<open>?B\<close> by auto
    subgoal using \<open>?B\<close> K_def by (cases \<open>rev M ! k\<close>) (auto simp: rev_nth)
    done
  moreover have \<open>count_decided M1 = 0\<close>
    using assms \<open>?B\<close> unfolding M
    by (auto simp: nth_append k_M1)
  ultimately show ?A
    using get_all_ann_decomposition_ex[of K M1 M2]
    unfolding M
    by auto
qed

lemma remove_all_learned_subsumed_clauses_wl_id:
  \<open>(x2a, x2) \<in> twl_st_heur_restart_ana' r u \<Longrightarrow>
   RETURN (empty_US_heur x2a)
    \<le> \<Down> (twl_st_heur_restart_ana' r u)
       (remove_all_learned_subsumed_clauses_wl x2)\<close>
   by (cases x2a; cases x2)
    (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def learned_clss_count_def
     remove_all_learned_subsumed_clauses_wl_def empty_US_heur_def
     intro: clss_size_corr_simp)

lemma mark_garbage_heur4_remove_and_add_cls_l:
  \<open>(S, T) \<in> {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> learned_clss_count S \<le> u} \<Longrightarrow> (C, C') \<in> Id \<Longrightarrow>
    mark_garbage_heur4 C S
       \<le> \<Down> {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> learned_clss_count S \<le> u}
            (remove_and_add_cls_wl C' T)\<close>
  unfolding mark_garbage_heur4_def remove_and_add_cls_wl_def Let_def
  apply (cases T, hypsubst, unfold prod.case)
  apply refine_rcg
  subgoal
    by (auto simp add: twl_st_heur_restart_def twl_st_heur_restart_ana_def arena_lifting get_unit_init_clss_wl_alt_def
      dest!: clss_size_corr_restart_rew multi_member_split simp: ran_m_def)
  subgoal
    supply [[goals_limit=1]]
    apply (auto simp: learned_clss_count_def)
    apply (clarsimp simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def
        arena_lifting
     valid_arena_extra_information_mark_to_delete'
      all_init_atms_fmdrop_add_mset_unit learned_clss_l_l_fmdrop
      learned_clss_l_l_fmdrop_irrelev aivdom_inv_dec_remove_clause
      size_Diff_singleton red_in_dom_number_of_learned_ge1 learned_clss_count_def
      clss_size_corr_restart_intro clss_size_corr_restart_simp3
      dest: in_vdom_m_fmdropD dest: in_diffD
      intro: clss_size_corr_restart_intro)
    apply (auto simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def
        arena_lifting
     valid_arena_extra_information_mark_to_delete'
      all_init_atms_fmdrop_add_mset_unit learned_clss_l_l_fmdrop
      learned_clss_l_l_fmdrop_irrelev aivdom_inv_dec_remove_clause
      size_Diff_singleton red_in_dom_number_of_learned_ge1 learned_clss_count_def
      clss_size_corr_restart_intro clss_size_corr_restart_simp3
      dest: in_vdom_m_fmdropD dest: in_diffD
      intro: clss_size_corr_restart_intro)
    done
  done

lemma remove_one_annot_true_clause_one_imp_wl_pre_fst_le_uint32:
  assumes \<open>(x, y) \<in> nat_rel \<times>\<^sub>f {p. (fst p, snd p) \<in> twl_st_heur_restart_ana r \<and>
          learned_clss_count (fst p) \<le> u}\<close> and
    \<open>remove_one_annot_true_clause_one_imp_wl_pre (fst y) (snd y)\<close>
  shows \<open>fst x + 1 \<le> Suc (uint32_max div 2)\<close>
proof -
  have [simp]: \<open>fst y = fst x\<close>
    using assms by (cases x, cases y) auto
  have \<open>fst x < length (get_trail_wl (snd y))\<close>
    using assms apply -
    unfolding
     remove_one_annot_true_clause_one_imp_wl_pre_def
     remove_one_annot_true_clause_one_imp_pre_def
   by normalize_goal+ auto
  moreover have \<open>(get_trail_wl_heur (snd x), get_trail_wl (snd y)) \<in> trail_pol (all_init_atms_st (snd y))\<close>
    using assms
    by (cases x, cases y) (simp add: twl_st_heur_restart_ana_def
      twl_st_heur_restart_def all_init_atms_st_def)
  ultimately show \<open>?thesis\<close>
    by (auto simp add: trail_pol_alt_def)
qed

lemma remove_one_annot_true_clause_one_imp_wl_alt_def:
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i S. do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_pre i S);
      ASSERT(is_proped (rev (get_trail_wl S) ! i));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev (get_trail_wl S))!i = Propagated L C);
      ASSERT(Propagated L C \<in> set (get_trail_wl S));
      ASSERT(L \<in># all_init_lits_of_wl S);
      if C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<in># dom_m (get_clauses_wl S));
	S \<leftarrow> replace_annot_wl L C S;
        _ \<leftarrow> RETURN (log_clause S C);
	S \<leftarrow> remove_and_add_cls_wl C S;
        RETURN (i+1, S)
      }
  })\<close>
  by (auto simp: remove_one_annot_true_clause_one_imp_wl_def log_clause_def cong: if_cong)


lemma log_clause_heur_log_clause2_ana:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_ana' r u\<close> \<open>(C,C') \<in> nat_rel\<close>
  shows \<open>log_clause_heur S C \<le>\<Down>unit_rel (log_clause2 T C')\<close>
proof -
  have [refine0]: \<open>(0,0)\<in>nat_rel\<close>
    by auto
  have length: \<open>\<Down> nat_rel ((RETURN \<circ> (\<lambda>c. length (get_clauses_wl T \<propto> c))) C') \<le> SPEC (\<lambda>c. (c, length (get_clauses_wl T \<propto> C')) \<in> {(a,b). a=b \<and> a = length (get_clauses_wl T \<propto> C)})\<close>
    by (use assms in auto)
  show ?thesis
    unfolding log_clause_heur_def log_clause2_def comp_def uncurry_def mop_arena_length_st_def
      mop_access_lit_in_clauses_heur_def
    apply (refine_vcg mop_arena_lit[where vdom = \<open>set (get_vdom S)\<close> and N = \<open>get_clauses_wl T\<close>, THEN order_trans] 
      mop_arena_length[where vdom = \<open>set (get_vdom S)\<close>, THEN fref_to_Down_curry, THEN order_trans, unfolded prod.simps])
    apply assumption
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    apply (rule length)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest: arena_lifting(10)\<close>)
    subgoal by auto
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    apply assumption
    subgoal by (use assms in auto)
    apply (rule refl)
    subgoal by auto
    by auto
qed

lemma log_del_clause_heur_log_clause:
  assumes \<open>(S,T) \<in> twl_st_heur_restart_ana' r u\<close> \<open>(C,C') \<in> nat_rel\<close> \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>log_del_clause_heur S C \<le> SPEC (\<lambda>c. (c, log_clause T C') \<in> unit_rel)\<close>
    unfolding log_del_clause_heur_alt_def
    apply (rule log_clause_heur_log_clause2_ana[THEN order_trans, OF assms(1,2)])
    apply (rule order_trans)
    apply (rule ref_two_step')
    apply (rule log_clause2_log_clause[THEN fref_to_Down_curry])
    using assms by auto

lemma remove_one_annot_true_clause_one_imp_wl_D_heur_remove_one_annot_true_clause_one_imp_wl_D:
  \<open>(uncurry remove_one_annot_true_clause_one_imp_wl_D_heur,
    uncurry remove_one_annot_true_clause_one_imp_wl) \<in>
    nat_rel \<times>\<^sub>f twl_st_heur_restart_ana' r u \<rightarrow>\<^sub>f
    \<langle>nat_rel \<times>\<^sub>f twl_st_heur_restart_ana' r u\<rangle>nres_rel\<close>
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    remove_one_annot_true_clause_one_imp_wl_alt_def case_prod_beta uncurry_def
  apply (intro frefI nres_relI)
  subgoal for x y
  apply (refine_rcg get_literal_and_reason[where r=r]
    isasat_replace_annot_in_trail_replace_annot_in_trail_spec
      [where r=r and u=u] log_del_clause_heur_log_clause
    mark_garbage_heur4_remove_and_add_cls_l[where r=r and u=u])
  subgoal
    by (auto simp: prod_rel_fst_snd_iff)
  subgoal unfolding remove_one_annot_true_clause_one_imp_wl_pre_def
    by auto
  subgoal
    by (rule remove_one_annot_true_clause_one_imp_wl_pre_fst_le_uint32)
  subgoal for p pa
    by (cases pa)
      (auto simp: all_init_atms_def simp del: all_init_atms_def[symmetric])
  subgoal
    by (cases x, cases y)
     (fastforce simp: twl_st_heur_restart_def
       trail_pol_alt_def)+
  subgoal by auto
  subgoal for p pa
    by (cases pa; cases p; cases x; cases y)
      (auto simp: all_init_atms_def learned_clss_count_def simp del: all_init_atms_def[symmetric])
  apply (solves auto)
  subgoal by auto
  subgoal in_dom_m for p pa S Sa
    unfolding mark_garbage_pre_def
      arena_is_valid_clause_idx_def
      prod.case
    apply (case_tac Sa; cases y)
    apply (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    done
  subgoal for p pa S Sa
    using in_dom_m
    unfolding mark_garbage_pre_def
      arena_is_valid_clause_idx_def
      prod.case
    apply (rule_tac x = \<open>get_clauses_wl Sa\<close> in exI)
    apply (rule_tac x = \<open>set (get_vdom S)\<close> in exI)
    apply (case_tac Sa; cases y)
    apply (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    done
  subgoal for p pa S Sa
    unfolding arena_is_valid_clause_vdom_def
    apply (rule_tac x = \<open>get_clauses_wl Sa\<close> in exI)
    apply (rule_tac x = \<open>set (get_vdom S)\<close> in exI)
    apply (case_tac Sa; cases y)
    apply (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    done
  subgoal
    by (auto simp: prod_rel_fst_snd_iff dest: get_learned_count_learned_clss_countD)
  subgoal
    by (auto simp: prod_rel_fst_snd_iff dest: get_learned_count_learned_clss_countD)
  subgoal
    by auto
  subgoal
    by (cases x, cases y) fastforce
  done
  done
 
lemma remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D:
  \<open>(remove_one_annot_true_clause_imp_wl_D_heur, remove_one_annot_true_clause_imp_wl) \<in>
  twl_st_heur_restart_ana' r u \<rightarrow>\<^sub>f
  \<langle>twl_st_heur_restart_ana' r u\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?A \<rightarrow>\<^sub>f _\<close>)
  unfolding remove_one_annot_true_clause_imp_wl_def
    remove_one_annot_true_clause_imp_wl_D_heur_def
  apply (intro frefI nres_relI)
  subgoal for x y
  apply (refine_vcg
    WHILEIT_refine[where R = \<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> learned_clss_count S \<le> learned_clss_count x}\<close>]
    remove_one_annot_true_clause_one_imp_wl_D_heur_remove_one_annot_true_clause_one_imp_wl_D[
       THEN fref_to_Down_curry])
  subgoal by (auto simp: trail_pol_alt_def isa_length_trail_pre_def
    twl_st_heur_restart_def twl_st_heur_restart_ana_def)
  subgoal by (auto dest: twl_st_heur_restart_isa_length_trail_get_trail_wl
   simp: twl_st_heur_restart_count_decided_st_alt_def mop_isa_length_trail_def)
  subgoal
    apply (rule order_trans)
    apply (rule get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail_CS[THEN fref_to_Down_curry,
        of \<open>get_trail_wl y\<close> 0 _ _ \<open>all_init_atms_st y\<close>])
    subgoal by (auto simp: get_pos_of_level_in_trail_pre_def
      twl_st_heur_restart_count_decided_st_alt_def)
    subgoal by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
        all_init_atms_st_def get_unit_init_clss_wl_alt_def)
    subgoal
      apply (subst get_pos_of_level_in_trail_decomp_iff)
      apply (solves \<open>auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def\<close>)
      apply (auto simp: get_pos_of_level_in_trail_def
        twl_st_heur_restart_count_decided_st_alt_def)
      done
    done
    subgoal by auto
    subgoal for  k k' T T'
      apply (subst (asm)(16) surjective_pairing)
      apply (subst (asm)(14) surjective_pairing)
      unfolding remove_one_annot_true_clause_imp_wl_D_heur_inv_def
        prod_rel_iff
      apply (subst (7) surjective_pairing, subst prod.case)
        apply (rule_tac x=y in exI)
        apply (rule_tac x= \<open>snd T'\<close> in exI)
      by (auto intro: twl_st_heur_restart_anaD simp: prod_rel_fst_snd_iff twl_st_heur_restart_anaD)
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: remove_all_learned_subsumed_clauses_wl_id)
  done
  done

definition iterate_over_VMTFC where
  \<open>iterate_over_VMTFC = (\<lambda>f (I :: 'a \<Rightarrow> bool) P (ns :: (nat, nat) vmtf_node list, n) x. do {
      (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). I x\<^esup>
        (\<lambda>(n, x). n \<noteq> None \<and> P x)
        (\<lambda>(n, x). do {
          ASSERT(n \<noteq> None);
          let A = the n;
          ASSERT(A < length ns);
          ASSERT(A \<le> uint32_max div 2);
          x \<leftarrow> f A x;
          RETURN (get_next ((ns ! A)), x)
        })
        (n, x);
      RETURN x
    })\<close>

definition iterate_over_VMTF :: \<open>_\<close> where
  iterate_over_VMTF_alt_def: \<open>iterate_over_VMTF f I  = iterate_over_VMTFC f I (\<lambda>_. True)\<close>

lemmas iterate_over_VMTF_def =
  iterate_over_VMTF_alt_def[unfolded iterate_over_VMTFC_def simp_thms]

definition iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC where
  \<open>iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC = (\<lambda>f \<A>\<^sub>0 I P x. do {
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset \<A>\<^sub>0 \<and> distinct_mset \<A>);
    (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(\<A>, x). I \<A> x\<^esup>
      (\<lambda>(\<B>, x). \<B> \<noteq> {#} \<and> P x)
      (\<lambda>(\<B>, x). do {
        ASSERT(\<B> \<noteq> {#});
        A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
        x \<leftarrow> f A x;
        RETURN (remove1_mset A \<B>, x)
      })
      (\<A>, x);
    RETURN x
  })\<close>

definition iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l :: \<open>_\<close> where
  iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def: \<open>iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l f \<A> I  = iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC f \<A> I (\<lambda>_. True)\<close>

lemmas iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_def =
  iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def[unfolded iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC_def simp_thms]


lemma iterate_over_VMTFC_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC:
  fixes x :: 'a
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    nempty: \<open>\<A> \<noteq> {#}\<close> \<open>isasat_input_bounded \<A>\<close> and
    II': \<open>\<And>x \<B>. set_mset \<B> \<subseteq> set_mset \<A> \<Longrightarrow> I' \<B> x \<Longrightarrow> I x\<close> and
    \<open>\<And>x. I x \<Longrightarrow> P x = Q x\<close>
  shows \<open>iterate_over_VMTFC f I P (ns, Some fst_As) x \<le> \<Down> Id (iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC f \<A> I' Q x)\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    \<open>fst_As = hd (ys' @ xs')\<close> and
    \<open>lst_As = last (ys' @ xs')\<close> and
    vmtf_\<L>: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    le: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close>
    using vmtf unfolding vmtf_def
    by blast
  define zs where \<open>zs = ys' @ xs'\<close>
  define is_lasts where
    \<open>is_lasts \<B> n m \<longleftrightarrow> set_mset \<B> = set (drop m zs) \<and> set_mset \<B> \<subseteq> set_mset \<A> \<and>
        distinct_mset \<B> \<and>
        card (set_mset \<B>) \<le> length zs \<and>
        card (set_mset \<B>) + m = length zs \<and>
        (n = option_hd (drop m zs)) \<and>
        m \<le> length zs\<close> for \<B> and n :: \<open>nat option\<close> and m
  have card_\<A>: \<open>card (set_mset \<A>) = length zs\<close>
    \<open>set_mset \<A> = set zs\<close> and
    nempty': \<open>zs \<noteq> []\<close> and
    dist_zs: \<open>distinct zs\<close>
    using vmtf_\<L> vmtf_ns_distinct[OF vmtf_ns] nempty
    unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def eq_commute[of _ \<open>atms_of _\<close>] zs_def
    by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n card_Un_disjoint distinct_card)
  have hd_zs_le: \<open>hd zs < length ns\<close>
    using vmtf_ns_le_length[OF vmtf_ns, of \<open>hd zs\<close>] nempty'
    unfolding zs_def[symmetric]
    by auto
  have [refine0]: \<open>
       (the x1a, A) \<in> nat_rel \<Longrightarrow>
       x = x2b \<Longrightarrow>
       f (the x1a) x2b \<le> \<Down> Id (f A x)\<close> for x1a A x x2b
      by auto
  define iterate_over_VMTF2 where
    \<open>iterate_over_VMTF2 \<equiv> (\<lambda>f (I :: 'a \<Rightarrow> bool) (vm :: (nat, nat) vmtf_node list, n) x. do {
      let _ = remdups_mset \<A>;
      (_, _, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n,m, x). I x\<^esup>
        (\<lambda>(n, _, x). n \<noteq> None \<and> P x)
        (\<lambda>(n, m, x). do {
          ASSERT(n \<noteq> None);
          let A = the n;
          ASSERT(A < length ns);
          ASSERT(A \<le> uint32_max div 2);
          x \<leftarrow> f A x;
          RETURN (get_next ((ns ! A)), Suc m, x)
        })
        (n, 0, x);
      RETURN x
    })\<close>
  have iterate_over_VMTF2_alt_def:
    \<open>iterate_over_VMTF2 \<equiv> (\<lambda>f (I :: 'a \<Rightarrow> bool) (vm :: (nat, nat) vmtf_node list, n) x. do {
      (_, _, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n,m, x). I x\<^esup>
        (\<lambda>(n, _, x). n \<noteq> None \<and> P x)
        (\<lambda>(n, m, x). do {
          ASSERT(n \<noteq> None);
          let A = the n;
          ASSERT(A < length ns);
          ASSERT(A \<le> uint32_max div 2);
          x \<leftarrow> f A x;
          RETURN (get_next ((ns ! A)), Suc m, x)
        })
        (n, 0, x);
      RETURN x
    })\<close>
    unfolding iterate_over_VMTF2_def by force
  have nempty_iff: \<open>(x1 \<noteq> None \<and> P x2a) = (x1b \<noteq> {#} \<and> Q xb)\<close> (is \<open>?A = ?B\<close>)
  if
    \<open>(remdups_mset \<A>, \<A>') \<in> Id\<close> and
    H: \<open>(x, x') \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close> and
    \<open>case x of (n, m, xa) \<Rightarrow> I xa\<close> and
    \<open>case x' of (\<A>', x) \<Rightarrow> I' \<A>' x\<close> and
    st[simp]:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x = (x1, x2)\<close>
      \<open>x' = (x1b, xb)\<close>
    for \<A>' x x' x1 x2 x1a x2a x1b xb
  proof
    have KK: \<open>P x2a = Q xb\<close>
      by (subst assms) (use that in auto)
    show ?A if ?B
      using that H unfolding KK
      by (auto simp: is_lasts_def)
    show ?B if ?A
      using that H unfolding KK
      by (auto simp: is_lasts_def)
  qed
  have IH: \<open>((get_next (ns ! the x1a), Suc x1b, xa), remove1_mset A x1, xb)
        \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close>
     if
      \<open>(remdups_mset \<A>, \<A>') \<in> Id\<close> and
      H: \<open>(x, x') \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close> and
      \<open>case x of (n, uu_, x) \<Rightarrow> n \<noteq> None \<and> P x\<close> and
      nempty: \<open>case x' of (\<B>, x) \<Rightarrow> \<B> \<noteq> {#} \<and> Q x\<close> and
      \<open>case x of (n, m, xa) \<Rightarrow> I xa\<close> and
      \<open>case x' of (\<A>', x) \<Rightarrow> I' \<A>' x\<close> and
      st:
        \<open>x' = (x1, x2)\<close>
        \<open>x2a = (x1b, x2b)\<close>
        \<open>x = (x1a, x2a)\<close>
        \<open>(xa, xb) \<in> Id\<close> and
      \<open>x1 \<noteq> {#}\<close> and
      \<open>x1a \<noteq> None\<close> and
      A: \<open>(the x1a, A) \<in> nat_rel\<close> and
      \<open>the x1a < length ns\<close>
      for \<A>' x x' x1 x2 x1a x2a x1b x2b A xa xb
  proof -
    have [simp]: \<open>distinct_mset x1\<close> \<open>x1b < length zs\<close>
      using H A nempty
      apply (auto simp: st is_lasts_def simp flip: Cons_nth_drop_Suc)
      apply (cases \<open>x1b = length zs\<close>)
      apply auto
      done
    then have [simp]: \<open>zs ! x1b \<notin> set (drop (Suc x1b) zs)\<close>
      by (auto simp: in_set_drop_conv_nth nth_eq_iff_index_eq dist_zs)
    have [simp]: \<open>length zs - Suc x1b + x1b = length zs \<longleftrightarrow> False\<close>
      using \<open>x1b < length zs\<close> by presburger
    have \<open>vmtf_ns (take x1b zs @ zs ! x1b # drop (Suc x1b) zs) m ns\<close>
      using vmtf_ns
      by (auto simp: Cons_nth_drop_Suc simp flip: zs_def)
    from vmtf_ns_last_mid_get_next_option_hd[OF this]
    show ?thesis
      using H A st
      by (auto simp: st is_lasts_def dist_zs distinct_card distinct_mset_set_mset_remove1_mset
           simp flip: Cons_nth_drop_Suc)
  qed
  have WTF[simp]: \<open>length zs - Suc 0 = length zs \<longleftrightarrow> zs = []\<close>
    by (cases zs) auto
  have zs2: \<open>set (xs' @ ys') = set zs\<close>
    by (auto simp: zs_def)
  have is_lasts_le:  \<open>is_lasts x1 (Some A) x1b \<Longrightarrow> A < length ns\<close> for x2 xb x1b x1 A
    using vmtf_\<L> le nth_mem[of \<open>x1b\<close> zs] unfolding is_lasts_def prod.case vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      set_append[symmetric]zs_def[symmetric] zs2
    by (auto simp: eq_commute[of \<open>set zs\<close> \<open>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>] hd_drop_conv_nth
      simp del: nth_mem)
  have le_uint32_max: \<open>the x1a \<le> uint32_max div 2\<close>
    if
      \<open>(remdups_mset \<A>, \<A>') \<in> Id\<close> and
      \<open>(x, x') \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close> and
      \<open>case x of (n, uu_, x) \<Rightarrow> n \<noteq> None \<and> P x\<close> and
      \<open>case x' of (\<B>, x) \<Rightarrow> \<B> \<noteq> {#} \<and> Q x\<close> and
      \<open>case x of (n, m, xa) \<Rightarrow> I xa\<close> and
      \<open>case x' of (\<A>', x) \<Rightarrow> I' \<A>' x\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2a = (x1b, xb)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>x1 \<noteq> {#}\<close> and
      \<open>x1a \<noteq> None\<close> and
      \<open>(the x1a, A) \<in> nat_rel\<close> and
      \<open>the x1a < length ns\<close>
    for \<A>' x x' x1 x2 x1a x2a x1b xb A
  proof -
    have \<open>the x1a \<in># \<A>\<close>
      using that unfolding is_lasts_def
      by clarsimp (auto simp: is_lasts_def)
    then show ?thesis
      using nempty by (auto dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
  qed
  have  \<open>iterate_over_VMTF2 f I (ns, Some fst_As) x \<le> \<Down> Id (iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC f \<A> I' Q x)\<close>
    unfolding iterate_over_VMTF2_def iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC_def prod.case
    apply (refine_vcg WHILEIT_refine[where R = \<open>{((n :: nat option, m::nat, x::'a), (\<A>' :: nat multiset, y)).
        is_lasts \<A>' n m \<and> x = y}\<close>])
    subgoal by simp
    subgoal by simp
    subgoal
      using card_\<A> fst_As nempty nempty' hd_conv_nth[OF nempty'] hd_zs_le unfolding zs_def[symmetric]
        is_lasts_def
      by (simp_all add:  eq_commute[of \<open>remdups_mset _\<close>])
    subgoal for \<A>' x x' x1 x2 x1a xaa using II'[of \<open>_\<close> xaa] unfolding is_lasts_def by auto
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b xb
      by (rule nempty_iff)
    subgoal by auto
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b xb
      by (simp add: is_lasts_def in_set_dropI)
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b xb
      by (auto simp: is_lasts_le)
    subgoal by (rule le_uint32_max)
    subgoal by auto
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b x2b A xa xb
      by (rule IH)
    subgoal by auto
    done
  moreover have \<open>iterate_over_VMTFC f I P (ns, Some fst_As) x  \<le> \<Down> Id (iterate_over_VMTF2 f I (ns, Some fst_As) x)\<close>
    unfolding iterate_over_VMTF2_alt_def iterate_over_VMTFC_def prod.case
    by (refine_vcg WHILEIT_refine[where R = \<open>{((n :: nat option, x::'a), (n' :: nat option, m'::nat, x'::'a)).
        n = n' \<and> x = x'}\<close>]) auto
  ultimately show ?thesis
    by simp
qed


lemma iterate_over_VMTF_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l:
  fixes x :: 'a
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    nempty: \<open>\<A> \<noteq> {#}\<close> \<open>isasat_input_bounded \<A>\<close> \<open>\<And>x \<B>. set_mset \<B> \<subseteq> set_mset \<A> \<Longrightarrow> I' \<B> x \<Longrightarrow> I x\<close>
  shows \<open>iterate_over_VMTF f I (ns, Some fst_As) x \<le> \<Down> Id (iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l f \<A> I' x)\<close>
  unfolding iterate_over_VMTF_alt_def iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
  apply (rule iterate_over_VMTFC_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC[OF assms])
  by auto


definition arena_is_packed :: \<open>arena \<Rightarrow> nat clauses_l \<Rightarrow> bool\<close> where
\<open>arena_is_packed arena N \<longleftrightarrow> length arena = (\<Sum>C \<in># dom_m N. length (N \<propto> C) + header_size (N \<propto> C))\<close>

lemma arena_is_packed_empty[simp]: \<open>arena_is_packed [] fmempty\<close>
  by (auto simp: arena_is_packed_def)

lemma arena_is_packed_append:
  assumes \<open>arena_is_packed (arena) N\<close> and
    [simp]: \<open>length C = length (fst C') + header_size (fst C')\<close> and
    [simp]: \<open>a \<notin># dom_m N\<close>
  shows \<open>arena_is_packed (arena @ C) (fmupd a C' N)\<close>
  using assms(1) by (auto simp: arena_is_packed_def
    intro!: sum_mset_cong)

lemma arena_is_packed_append_valid:
  assumes
    in_dom: \<open>fst C \<in># dom_m x1a\<close> and
    valid0: \<open>valid_arena x1c x1a vdom0\<close> and
    valid: \<open>valid_arena x1d x2a (set x2d)\<close> and
    packed: \<open>arena_is_packed x1d x2a\<close> and
    n: \<open>n = header_size  (x1a \<propto> (fst C))\<close>
  shows \<open>arena_is_packed
          (x1d @
           Misc.slice (fst C - n)
            (fst C + arena_length x1c (fst C)) x1c)
          (fmupd (length x1d + n) (the (fmlookup x1a (fst C))) x2a)\<close>
proof -
  have [simp]: \<open>length x1d + n \<notin># dom_m x2a\<close>
  using valid by (auto dest: arena_lifting(2) valid_arena_in_vdom_le_arena
    simp: arena_is_valid_clause_vdom_def header_size_def)
  have [simp]: \<open>arena_length x1c (fst C) = length (x1a \<propto> (fst C))\<close> \<open>fst C \<ge> n\<close>
      \<open>fst C - n < length x1c\<close>  \<open>fst C < length x1c\<close>
    using valid0 valid in_dom by (auto simp: arena_lifting n less_imp_diff_less)
  have [simp]: \<open>length
     (Misc.slice (fst C - n)
       (fst C + length (x1a \<propto> (fst C))) x1c) =
     length (x1a \<propto> fst C) + header_size (x1a \<propto> fst C)\<close>
     using valid in_dom arena_lifting(10)[OF valid0]
     by (fastforce simp: slice_len_min_If min_def arena_lifting(4) simp flip: n)
  show ?thesis
    by (rule arena_is_packed_append[OF packed]) auto
qed

definition move_is_packed :: \<open>arena \<Rightarrow> _ \<Rightarrow> arena \<Rightarrow> _ \<Rightarrow> bool\<close> where
\<open>move_is_packed arena\<^sub>o N\<^sub>o arena N \<longleftrightarrow>
   ((\<Sum>C\<in>#dom_m N\<^sub>o. length (N\<^sub>o \<propto> C) + header_size (N\<^sub>o \<propto> C)) +
   (\<Sum>C\<in>#dom_m N. length (N \<propto> C) + header_size (N \<propto> C)) \<le> length arena\<^sub>o)\<close>

definition arena_header_size :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>arena_header_size arena C =
  (if arena_length arena C > 4 then MAX_HEADER_SIZE else MIN_HEADER_SIZE)\<close>

lemma valid_arena_header_size:
  \<open>valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> arena_header_size arena C = header_size (N \<propto> C)\<close>
  by (auto simp: arena_header_size_def header_size_def arena_lifting)
(*TODO Move*)
lemma WHILEIT_refine_with_invariant_and_break:
  assumes R0: \<open>I' x' \<Longrightarrow> (x,x')\<in>R\<close>
  assumes IREF: \<open>\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x\<close>
  assumes COND_REF: \<open>\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'\<close>
  assumes STEP_REF:
    \<open>\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')\<close>
  shows \<open>WHILEIT I b f x \<le>\<Down>{(x, x'). (x, x') \<in> R \<and> I x \<and>  I' x' \<and> \<not>b' x'} (WHILEIT I' b' f' x')\<close>
    (is \<open>_ \<le> \<Down>?R' _\<close>)
  apply (subst (2)WHILEIT_add_post_condition)
  apply (refine_vcg WHILEIT_refine_genR[where R'=R and R = ?R'])
  subgoal by (auto intro: assms)[]
  subgoal by (auto intro: assms)[]
  subgoal using COND_REF by (auto)
  subgoal by (auto intro: assms)[]
  subgoal by (auto intro: assms)[]
  done

definition rewatch_spec :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>rewatch_spec = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS).
  SPEC (\<lambda>(M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q', WS').
     (M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q') = (M, N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q) \<and>
     correct_watching' (M, N', D, NE, UE, NEk', UEk', NS', US, N0, U0, Q', WS') \<and>
     literals_are_\<L>\<^sub>i\<^sub>n' (M, N', D, NE, UE, NEk', UEk', NS', US, N0, U0, Q', WS')))\<close>

lemma blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0':
  \<open>literals_are_\<L>\<^sub>i\<^sub>n' (a, aq, ab, ac, ad, NEk, UEk, ae, af, N0, U0, Q, b) \<Longrightarrow>
       literals_are_\<L>\<^sub>i\<^sub>n' (a, aq, ab, ac, ad, NEk, UEk, ae, af, N0, U0, {#}, b)\<close>
  by (auto simp: literals_are_\<L>\<^sub>i\<^sub>n'_empty blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0)

lemma RES_RES11_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(a, b, c, d, e, g, h, i, j, k, l). RES (f a b c d e g h i j k l)) =
   RES (\<Union>((\<lambda>(a, b, c, d, e, g, h, i, j, k, l). f a b c d e g h i j k l) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def Bex_def
    split: prod.splits)

lemma RES_RES13_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(a, b, c, d, e, g, h, i, j, k, l, m, n). RES (f a b c d e g h i j k l m n)) =
   RES (\<Union>((\<lambda>(a, b, c, d, e, g, h, i, j, k, l, m, n). f a b c d e g h i j k l m n) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def Bex_def
    split: prod.splits)

lemma ref_two_step'': \<open>R \<subseteq> R' \<Longrightarrow> A \<le> B \<Longrightarrow> \<Down> R A \<le>  \<Down> R' B\<close>
  by (simp add: "weaken_\<Down>" ref_two_step')

abbreviation twl_st_heur_restart'''u where
  \<open>twl_st_heur_restart'''u r u \<equiv>
  {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) = r \<and>
  learned_clss_count S \<le> u}\<close>

abbreviation twl_st_heur_restart''''u where
  \<open>twl_st_heur_restart''''u r u \<equiv>
  {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) \<le> r  \<and>
  learned_clss_count S \<le> u}\<close>


fun correct_watching''' :: \<open>_ \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching''' \<A> (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm \<A>.
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<and> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
             correctly_marked_as_binary N (i, K, b)) \<and>
        fst `# mset (W L) = clause_to_update L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}))\<close>

declare correct_watching'''.simps[simp del]

lemma correct_watching'''_add_clause:
  assumes
    corr: \<open>correct_watching''' \<A> ((a, aa, CD, ac, ad, NEk, UEk, NS, US, N0, U0, Q, b))\<close> and
    leC: \<open>2 \<le> length C\<close> and
    i_notin[simp]: \<open>i \<notin># dom_m aa\<close> and
    dist[iff]: \<open>C ! 0 \<noteq> C ! Suc 0\<close>
  shows \<open>correct_watching''' \<A>
          ((a, fmupd i (C, red) aa, CD, ac, ad, NEk, UEk, NS, US, N0, U0, Q, b
            (C ! 0 := b (C ! 0) @ [(i, C ! Suc 0, length C = 2)],
             C ! Suc 0 := b (C ! Suc 0) @ [(i, C ! 0, length C = 2)])))\<close>
proof -
  have [iff]: \<open>C ! Suc 0 \<noteq> C ! 0\<close>
    using  \<open>C ! 0 \<noteq> C ! Suc 0\<close> by argo
  have [iff]: \<open>C ! Suc 0 \<in># all_lits_of_m (mset C)\<close> \<open>C ! 0 \<in># all_lits_of_m (mset C)\<close>
    \<open>C ! Suc 0 \<in> set C\<close> \<open> C ! 0 \<in> set C\<close> \<open>C ! 0 \<in> set (watched_l C)\<close> \<open>C ! Suc 0 \<in> set (watched_l C)\<close>
    using leC by (force intro!: in_clause_in_all_lits_of_m nth_mem simp: in_set_conv_iff
        intro: exI[of _ 0] exI[of _ \<open>Suc 0\<close>])+
  have [dest!]: \<open>\<And>L. L \<noteq> C ! 0 \<Longrightarrow> L \<noteq> C ! Suc 0 \<Longrightarrow> L \<in> set (watched_l C) \<Longrightarrow> False\<close>
     by (cases C; cases \<open>tl C\<close>; auto)+
  have i: \<open>i \<notin> fst ` set (b L)\<close> if \<open>L\<in>#all_lits_of_mm \<A>\<close>for L
    using corr i_notin that unfolding correct_watching'''.simps
    by force
  have [iff]: \<open>(i,c, d) \<notin> set (b L)\<close> if \<open>L\<in>#all_lits_of_mm \<A>\<close> for L c d
    using i[of L, OF that] by (auto simp: image_iff)
  then show ?thesis
    using corr
    by (force simp: correct_watching'''.simps ran_m_mapsto_upd_notin
        all_lits_of_mm_add_mset all_lits_of_mm_union clause_to_update_mapsto_upd_notin correctly_marked_as_binary.simps
        split: if_splits)
qed


lemma rewatch_correctness:
  assumes empty: \<open>\<And>L. L \<in># all_lits_of_mm \<A> \<Longrightarrow> W L = []\<close> and
    H[dest]: \<open>\<And>x. x \<in># dom_m N \<Longrightarrow> distinct (N \<propto> x) \<and> length (N \<propto> x) \<ge> 2\<close> and
    incl: \<open>set_mset (all_lits_of_mm (mset `# ran_mf N)) \<subseteq> set_mset (all_lits_of_mm \<A>)\<close>
  shows
    \<open>rewatch N W \<le> SPEC(\<lambda>W. correct_watching''' \<A> (M, N, C, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W))\<close>
proof -
  define I where
    \<open>I \<equiv> \<lambda>(a :: nat list) (b :: nat list) W.
        correct_watching''' \<A> ((M, fmrestrict_set (set a) N, C, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W))\<close>
  have I0: \<open>set_mset (dom_m N) \<subseteq> set x \<and> distinct x \<Longrightarrow> I [] x W\<close> for x
    using empty unfolding I_def by (auto simp: correct_watching'''.simps
       all_blits_are_in_problem_init.simps clause_to_update_def
       all_lits_of_mm_union)
  have le: \<open>length (\<sigma> L) < size (dom_m N)\<close>
     if \<open>correct_watching''' \<A> (M, fmrestrict_set (set l1) N, C, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, \<sigma>)\<close> and
      \<open>set_mset (dom_m N) \<subseteq> set x \<and> distinct x\<close> and
     \<open>x = l1 @ xa # l2\<close> \<open>xa \<in># dom_m N\<close> \<open>L \<in> set (N \<propto> xa)\<close>
     for L l1 \<sigma> xa l2 x
  proof -
    have 1: \<open>card (set l1) \<le> length l1\<close>
      by (auto simp: card_length)
    have \<open>L \<in># all_lits_of_mm \<A>\<close>
      using that incl in_clause_in_all_lits_of_m[of L \<open>mset (N \<propto> xa)\<close>]
      by (auto simp: correct_watching'''.simps dom_m_fmrestrict_set' ran_m_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset atm_of_all_lits_of_m
          in_all_lits_of_mm_ain_atms_of_iff
        dest!: multi_member_split)
    then have \<open>distinct_watched (\<sigma> L)\<close> and \<open>fst ` set (\<sigma> L) \<subseteq> set l1 \<inter> set_mset (dom_m N)\<close>
      using that incl
      by (auto simp: correct_watching'''.simps dom_m_fmrestrict_set' dest!: multi_member_split)
    then have \<open>length (map fst (\<sigma> L)) \<le> card (set l1 \<inter> set_mset (dom_m N))\<close>
      using 1 by (subst distinct_card[symmetric])
       (auto simp: distinct_watched_alt_def intro!: card_mono intro: order_trans)
    also have \<open>... < card (set_mset (dom_m N))\<close>
      using that by (auto intro!: psubset_card_mono)
    also have \<open>... = size (dom_m N)\<close>
      by (simp add: distinct_mset_dom distinct_mset_size_eq_card)
    finally show ?thesis by simp
  qed
  show ?thesis
    unfolding rewatch_def
    apply (refine_vcg
      nfoldli_rule[where I = \<open>I\<close>])
    subgoal by (rule I0)
    subgoal using assms unfolding I_def by auto
    subgoal for x xa l1 l2 \<sigma>  using H[of xa] unfolding I_def apply -
      by (rule, subst (asm)nth_eq_iff_index_eq)
        linarith+
    subgoal for x xa l1 l2 \<sigma> unfolding I_def by (rule le) (auto intro!: nth_mem)
    subgoal for x xa l1 l2 \<sigma> unfolding I_def by (drule le[where L = \<open>N \<propto> xa ! 1\<close>]) (auto simp: I_def dest!: le)
    subgoal for x xa l1 l2 \<sigma>
      unfolding I_def
      by (cases \<open>the (fmlookup N xa)\<close>)
       (auto intro!: correct_watching'''_add_clause simp: dom_m_fmrestrict_set')
    subgoal
      unfolding I_def
      by auto
    subgoal by auto
    subgoal unfolding I_def
      by (auto simp: fmlookup_restrict_set_id')
    done
qed

definition update_restart_phases :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>update_restart_phases = (\<lambda>S. do {
     let heur = get_heur S;
     heur \<leftarrow> RETURN (incr_restart_phase heur);
     heur \<leftarrow> RETURN (incr_restart_phase_end heur);
     heur \<leftarrow> RETURN (if current_restart_phase heur = QUIET_PHASE then heuristic_reluctant_enable heur else heuristic_reluctant_disable heur);
     RETURN (set_heur_wl_heur heur S)
  })\<close>


lemma heuristic_rel_incr_restartI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase_end heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def incr_restart_phase_end_def)

definition rewatch_heur_st_pre :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>rewatch_heur_st_pre S \<longleftrightarrow> (\<forall>i < length (get_tvdom S). get_tvdom S ! i \<le> sint64_max)\<close>

lemma isasat_GC_clauses_wl_D_rewatch_pre:
  assumes
    \<open>length (get_clauses_wl_heur x) \<le> sint64_max\<close> and
    \<open>length (get_clauses_wl_heur xc) \<le> length (get_clauses_wl_heur x)\<close> and
    \<open>\<forall>i \<in> set (get_tvdom xc). i \<le> length (get_clauses_wl_heur x)\<close>
  shows \<open>rewatch_heur_st_pre xc\<close>
  using assms
  unfolding rewatch_heur_st_pre_def all_set_conv_all_nth
  by auto

(*TODO Move*)
definition should_inprocess_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>should_inprocess_st S \<longleftrightarrow>
      (get_global_conflict_count S > next_inprocessing_schedule_st S)\<close>
(*TODO Move*)
lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_restart_ana' r (u) \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro WB_More_Refinement.frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_restart_ana_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def twl_st_heur_restart_def
     split: option.splits)
lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_restart:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro WB_More_Refinement.frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_restart_ana_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def twl_st_heur_restart_def
     split: option.splits)
(*TODO Move*)
lemma mop_arena_status2:
  assumes \<open>(C,C')\<in>nat_rel\<close> \<open>C \<in> vdom\<close>
    \<open>valid_arena arena N vdom\<close>
  shows
    \<open>mop_arena_status arena C
    \<le> SPEC
    (\<lambda>c. (c, C \<in># dom_m N)
    \<in> {(a,b). (b \<longrightarrow> (a = IRRED \<longleftrightarrow> irred N C) \<and> (a = LEARNED \<longleftrightarrow> \<not>irred N C)) \<and>  (a = DELETED \<longleftrightarrow> \<not>b)})\<close>
  using assms arena_dom_status_iff[of arena N vdom C] unfolding mop_arena_status_def
  by (cases \<open>C \<in># dom_m N\<close>)
    (auto intro!: ASSERT_leI simp: arena_is_valid_clause_vdom_def
     arena_lifting)

(*END Move*)
(*TODO Move*)
lemma mop_arena_status_vdom:
  assumes \<open>C \<in> vdom\<close> and \<open>(C,C')\<in>nat_rel\<close>
    \<open>valid_arena arena N vdom\<close>
  shows
    \<open>mop_arena_status arena C
    \<le> SPEC
    (\<lambda>c. (c, C' \<in># dom_m N)
    \<in> {(a,b). (a \<noteq> DELETED \<longleftrightarrow> b) \<and> (((a = IRRED \<longleftrightarrow> (irred N C' \<and> b)) \<and> (a = LEARNED \<longleftrightarrow> (\<not>irred N C' \<and> b))))})\<close>
   using assms arena_lifting(24,25)[of arena N vdom C] arena_dom_status_iff(1)[of arena N vdom C]
   unfolding mop_arena_status_def
   by (cases \<open>arena_status arena C'\<close>)
    (auto intro!: ASSERT_leI simp: arena_is_valid_clause_vdom_def)
(*TODO rename*)
lemma all_init_atms_alt_def:
  \<open>all_init_atms (get_clauses_wl S')
        (IsaSAT_Setup.get_unkept_unit_init_clss_wl S' + IsaSAT_Setup.get_kept_unit_init_clss_wl S' + get_subsumed_init_clauses_wl S' +
  get_init_clauses0_wl S') = all_init_atms_st S'\<close>
  by (auto simp: all_init_atms_st_def IsaSAT_Setup.get_unit_init_clss_wl_alt_def)

lemma twl_st_heur_restart_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_restart\<close>
  shows
     twl_st_heur_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
       watched_by_int S C = watched_by S' C\<close>
      \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
       get_watched_wl_heur S ! (nat_of_lit C) =  get_watched_wl S' C\<close>and
     \<open>literals_to_update_wl S' =
         uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev (get_trail_wl S')))\<close> and
     twl_st_heur_state_simp_watched2: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
       nat_of_lit C < length(get_watched_wl_heur S)\<close>
  using assms unfolding twl_st_heur_restart_def
  by (solves \<open>cases S; cases S'; auto simp add: Let_def map_fun_rel_def ac_simps all_init_atms_st_def\<close>)+

lemma twl_st_heur_restart_ana_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana u\<close>
  shows
     twl_st_heur_restart_ana_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
       watched_by_int S C = watched_by S' C\<close>
      \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
       get_watched_wl_heur S ! (nat_of_lit C) =  get_watched_wl S' C\<close>and
     \<open>literals_to_update_wl S' =
         uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev (get_trail_wl S')))\<close> and
     twl_st_heur_restart_ana_state_simp_watched2: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st S') \<Longrightarrow>
       nat_of_lit C < length(get_watched_wl_heur S)\<close>
  using assms twl_st_heur_restart_state_simp[of S S'] unfolding twl_st_heur_restart_ana_def
  by (auto simp: )

lemma twl_st_heur_restart_ana_watchlist_in_vdom:
  \<open>get_watched_wl_heur x2e ! nat_of_lit L ! x1d = (a, b) \<Longrightarrow>
  (x2e, x2f) \<in> twl_st_heur_restart_ana r \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x2f) \<Longrightarrow>
  x1d < length (get_watched_wl_heur x2e ! nat_of_lit L) \<Longrightarrow>
    a \<in> set (get_vdom x2e)\<close>
  apply (drule nth_mem)
  by (subst (asm) twl_st_heur_restart_ana_state_simp, assumption, assumption)+
   (auto 5 3 simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def vdom_m_def
    all_init_atms_alt_def
    dest!: multi_member_split)

lemma twl_st_heur_restart_alt_def2:
  \<open>twl_st_heur_restart =
  {(S,T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_init_atms_st T) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_init_atms_st T) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st T)) \<and>
    vm \<in> isa_vmtf (all_init_atms_st T) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms_st T) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} lcount \<and>
    vdom_m (all_init_atms_st T) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_init_atms_st T) \<and>
    isasat_input_nempty (all_init_atms_st T) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_init_atms_st T) heur
  }\<close>
  unfolding twl_st_heur_restart_def Let_def
  by (auto simp: all_init_atms_st_def )

lemma length_watched_le_ana:
  assumes
    prop_inv: \<open>correct_watching'_leaking_bin x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur_restart_ana r\<close> and
    x2': \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1)\<close>
  shows \<open>length (watched_by x1 x2) \<le> r - MIN_HEADER_SIZE\<close>
proof -
  have x2: \<open>x2 \<in># all_init_lits_of_wl x1\<close>
    using \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) x2' by blast
  have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using prop_inv x2 unfolding all_atms_def all_lits_def
    by (cases x1; auto simp: correct_watching'_leaking_bin.simps ac_simps all_lits_st_alt_def[symmetric])
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def twl_st_heur'_def aivdom_inv_dec_alt_def Let_def)

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def Let_def)

  have \<open>vdom_m (all_init_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_alt_def2 ac_simps Let_def)

  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2' unfolding vdom_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a) - MIN_HEADER_SIZE\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show ?thesis
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>]
      simp: twl_st_heur_restart_ana_def)
qed

lemma D\<^sub>0_cong': \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> x \<in> D\<^sub>0 \<A> \<Longrightarrow> x \<in> D\<^sub>0 \<B>\<close>
  by (subst (asm) D\<^sub>0_cong, assumption)
lemma map_fun_rel_D\<^sub>0_cong: \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow>x \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<Longrightarrow> x \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<B>)\<close>
  by (subst (asm) D\<^sub>0_cong, assumption)

lemma vdom_m_cong': "set_mset \<A> = set_mset \<B> \<Longrightarrow> x \<in> vdom_m \<A> a b \<Longrightarrow> x \<in> vdom_m \<B> a b"
  by (subst (asm) vdom_m_cong, assumption)
lemma vdom_m_cong'': "set_mset \<A> = set_mset \<B> \<Longrightarrow> vdom_m \<A> a b \<subseteq> A \<Longrightarrow> vdom_m \<B> a b \<subseteq> A"
  by (subst (asm) vdom_m_cong, assumption)
lemma cach_refinement_empty_cong': "set_mset \<A> = set_mset \<B> \<Longrightarrow> cach_refinement_empty \<A> x \<Longrightarrow> cach_refinement_empty \<B> x"
  by (subst (asm) cach_refinement_empty_cong, assumption)

end
