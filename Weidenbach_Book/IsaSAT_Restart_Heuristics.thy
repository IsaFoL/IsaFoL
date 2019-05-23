theory IsaSAT_Restart_Heuristics
  imports Watched_Literals.WB_Sort Watched_Literals_Watch_List_Domain_Restart IsaSAT_Setup IsaSAT_VMTF
begin

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


definition twl_st_heur_restart :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_restart =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts),
     (M, N, D, NE, UE, Q, W)).
    (M', M) \<in> trail_pol (all_init_atms N NE) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_init_atms N NE) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N NE)) \<and>
    vm \<in> isa_vmtf (all_init_atms N NE) M \<and>
    phase_saving (all_init_atms N NE) \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms N NE) cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m (all_init_atms N NE)  W N \<subseteq> set vdom \<and>
    set avdom \<subseteq> set vdom \<and>
    isasat_input_bounded (all_init_atms N NE) \<and>
    isasat_input_nempty (all_init_atms N NE) \<and>
    distinct vdom
  }\<close>


definition clause_score_ordering where
  \<open>clause_score_ordering = (\<lambda>(lbd, act) (lbd', act'). lbd < lbd' \<or> (lbd = lbd' \<and> act = act'))\<close>

lemma clause_score_ordering_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo clause_score_ordering), uncurry (RETURN oo clause_score_ordering)) \<in>
    (uint32_nat_assn *a uint32_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn *a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: clause_score_ordering_def uint32_nat_rel_def br_def
      nat_of_uint32_less_iff)

lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

global_interpretation twl_restart_ops id
  by unfold_locales

global_interpretation twl_restart id
  by standard (rule unbounded_id)

text \<open>
  We first fix the function that proves termination. We don't take the ``smallest'' function
  possible (other possibilites that are growing slower include \<^term>\<open>\<lambda>(n::nat). n >> 50\<close>).
  Remark that this scheme is not compatible with Luby (TODO: use Luby restart scheme every once
  in a while like CryptoMinisat?)
\<close>

lemma get_slow_ema_heur_alt_def:
   \<open>RETURN o get_slow_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN sema)\<close>
  by auto

sepref_definition get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_slow_ema_heur_slow_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_slow_ema_heur_fast_code.refine[sepref_fr_rules]
  get_slow_ema_heur_slow_code.refine[sepref_fr_rules]


lemma get_fast_ema_heur_alt_def:
   \<open>RETURN o get_fast_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, lcount). RETURN fema)\<close>
  by auto

sepref_definition get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_fast_ema_heur_slow_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_fast_ema_heur_slow_code.refine[sepref_fr_rules]
  get_fast_ema_heur_fast_code.refine[sepref_fr_rules]


fun (in -) get_conflict_count_since_last_restart_heur :: \<open>twl_st_wl_heur \<Rightarrow> uint64\<close> where
  \<open>get_conflict_count_since_last_restart_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, _, (ccount, _), _)
      = ccount\<close>

lemma (in -) get_counflict_count_heur_alt_def:
   \<open>RETURN o get_conflict_count_since_last_restart_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN ccount)\<close>
  by auto

sepref_definition get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_conflict_count_since_last_restart_heur_slow_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_conflict_count_since_last_restart_heur_fast_code.refine[sepref_fr_rules]
  get_conflict_count_since_last_restart_heur_slow_code.refine[sepref_fr_rules]

lemma get_learned_count_alt_def:
   \<open>RETURN o get_learned_count = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). RETURN lcount)\<close>
  by auto

sepref_definition get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_learned_count_slow_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_unbounded_assn_def
  by sepref

declare get_learned_count_fast_code.refine[sepref_fr_rules]
  get_learned_count_slow_code.refine[sepref_fr_rules]

definition (in -) find_local_restart_target_level_int_inv where
  \<open>find_local_restart_target_level_int_inv ns cs =
     (\<lambda>(brk, i). i \<le> length cs \<and> length cs < uint32_max)\<close>

definition find_local_restart_target_level_int
   :: \<open>trail_pol \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> nat nres\<close>
where
  \<open>find_local_restart_target_level_int =
     (\<lambda>(M, xs, lvls, reasons, k, cs) ((ns :: nat_vmtf_node list, m :: nat, fst_As::nat, lst_As::nat,
        next_search::nat option), _). do {
     (brk, i) \<leftarrow> WHILE\<^sub>T\<^bsup>find_local_restart_target_level_int_inv ns cs\<^esup>
        (\<lambda>(brk, i). \<not>brk \<and> i < length_uint32_nat cs)
        (\<lambda>(brk, i). do {
           ASSERT(i < length cs);
           let t = (cs  ! i);
	   ASSERT(t < length M);
	   let L = atm_of (M ! t);
           ASSERT(L < length ns);
           let brk = stamp (ns ! L) < m;
           RETURN (brk, if brk then i else i+one_uint32_nat)
         })
        (False, zero_uint32_nat);
    RETURN i
   })\<close>

sepref_definition find_local_restart_target_level_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

sepref_definition find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

declare find_local_restart_target_level_code.refine[sepref_fr_rules]
  find_local_restart_target_level_fast_code.refine[sepref_fr_rules]

definition find_local_restart_target_level where
  \<open>find_local_restart_target_level M _ = SPEC(\<lambda>i. i \<le> count_decided M)\<close>

lemma find_local_restart_target_level_alt_def:
  \<open>find_local_restart_target_level M vm = do {
      (b, i) \<leftarrow> SPEC(\<lambda>(b::bool, i). i \<le> count_decided M);
       RETURN i
    }\<close>
  unfolding find_local_restart_target_level_def by (auto simp: RES_RETURN_RES2 uncurry_def)


lemma find_local_restart_target_level_int_find_local_restart_target_level:
   \<open>(uncurry find_local_restart_target_level_int, uncurry find_local_restart_target_level) \<in>
     [\<lambda>(M, vm). vm \<in> isa_vmtf \<A> M]\<^sub>f trail_pol \<A> \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_alt_def
    uncurry_def Let_def
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for a aa ab ac ad b ae af ag ah ba bb ai aj ak al am bc bd
    apply (refine_rcg WHILEIT_rule[where R = \<open>measure (\<lambda>(brk, i). (If brk 0 1) + length b - i)\<close>]
        assert.ASSERT_leI)
    subgoal by auto
    subgoal
      unfolding find_local_restart_target_level_int_inv_def
      by (auto simp: trail_pol_alt_def control_stack_length_count_dec)
    subgoal by auto
    subgoal by (auto simp: trail_pol_alt_def intro: control_stack_le_length_M)
    subgoal for s x1 x2
      by (subgoal_tac \<open>a ! (b ! x2) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>)
        (auto simp: trail_pol_alt_def rev_map lits_of_def rev_nth
            vmtf_def atms_of_def isa_vmtf_def
          intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l)
    subgoal by (auto simp: find_local_restart_target_level_int_inv_def)
    subgoal by (auto simp: trail_pol_alt_def control_stack_length_count_dec
          find_local_restart_target_level_int_inv_def)
    subgoal by auto
    done
  done

definition empty_Q :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>empty_Q = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount). do{
    ASSERT(isa_length_trail_pre M);
    let j = isa_length_trail M;
    RETURN (M, N, D, j, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
       restart_info_restart_done ccount, vdom, lcount)
  })\<close>

definition incr_restart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_restart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
       res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_restart stats,
       ema_reinit fast_ema, ema_reinit slow_ema,
       restart_info_restart_done res_info, vdom, avdom, lcount)
  })\<close>

sepref_definition incr_restart_stat_slow_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_register incr_restart_stat

sepref_definition incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare incr_restart_stat_slow_code.refine[sepref_fr_rules]
  incr_restart_stat_fast_code.refine[sepref_fr_rules]

definition incr_lrestart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_lrestart stats,
       fast_ema, slow_ema,
       restart_info_restart_done res_info,
       vdom, avdom, lcount)
  })\<close>

sepref_definition incr_lrestart_stat_slow_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_register incr_lrestart_stat

sepref_definition incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare incr_lrestart_stat_slow_code.refine[sepref_fr_rules]
  incr_lrestart_stat_fast_code.refine[sepref_fr_rules]

definition restart_abs_wl_heur_pre  :: \<open>twl_st_wl_heur \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_heur_pre S brk  \<longleftrightarrow> (\<exists>T. (S, T) \<in> twl_st_heur \<and> restart_abs_wl_D_pre T brk)\<close>

text \<open>\<^term>\<open>find_decomp_wl_st_int\<close> is the wrong function here, because unlike in the backtrack case,
  we also have to update the queue of literals to update. This is done in the function \<^term>\<open>empty_Q\<close>.
\<close>

definition find_local_restart_target_level_st :: \<open>twl_st_wl_heur \<Rightarrow> nat nres\<close> where
  \<open>find_local_restart_target_level_st S = do {
    find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S)
  }\<close>

lemma find_local_restart_target_level_st_alt_def:
  \<open>find_local_restart_target_level_st = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats). do {
      find_local_restart_target_level_int M vm})\<close>
 apply (intro ext)
  apply (case_tac x)
  by (auto simp: find_local_restart_target_level_st_def)

sepref_definition find_local_restart_target_level_st_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_definition find_local_restart_target_level_st_fast_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare find_local_restart_target_level_st_code.refine[sepref_fr_rules]
  find_local_restart_target_level_st_fast_code.refine[sepref_fr_rules]

definition cdcl_twl_local_restart_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_local_restart_wl_D_heur = (\<lambda>S. do {
      ASSERT(restart_abs_wl_heur_pre S False);
      lvl \<leftarrow> find_local_restart_target_level_st S;
      if lvl = count_decided_st_heur S
      then RETURN S
      else do {
        S \<leftarrow> find_decomp_wl_st_int lvl S;
        S \<leftarrow> empty_Q S;
        incr_lrestart_stat S
      }
   })\<close>


sepref_definition empty_Q_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_unbounded_assn_def
  by sepref

sepref_definition empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def
  by sepref

declare empty_Q_code.refine[sepref_fr_rules]
  empty_Q_fast_code.refine[sepref_fr_rules]

sepref_register cdcl_twl_local_restart_wl_D_heur
  empty_Q find_decomp_wl_st_int

sepref_definition cdcl_twl_local_restart_wl_D_heur_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_local_restart_wl_D_heur_code.refine[sepref_fr_rules]
  cdcl_twl_local_restart_wl_D_heur_fast_code.refine[sepref_fr_rules]


named_theorems twl_st_heur_restart

lemma [twl_st_heur_restart]:
  assumes \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>(get_trail_wl_heur S, get_trail_wl T) \<in> trail_pol (all_init_atms_st T)\<close>
  using assms by (cases S; cases T; auto simp: twl_st_heur_restart_def)

lemma trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail:
  \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def trail_pol_def
  by auto

lemma refine_generalise1: "A \<le> B \<Longrightarrow> do {x \<leftarrow> B; C x} \<le> D \<Longrightarrow> do {x \<leftarrow> A; C x} \<le> (D:: 'a nres)"
  using Refine_Basic.bind_mono(1) dual_order.trans by blast

lemma refine_generalise2: "A \<le> B \<Longrightarrow> do {x \<leftarrow> do {x \<leftarrow> B; A' x}; C x} \<le> D \<Longrightarrow>
  do {x \<leftarrow> do {x \<leftarrow> A; A' x}; C x} \<le> (D:: 'a nres)"
  by (simp add: refine_generalise1)

lemma cdcl_twl_local_restart_wl_D_spec_int:
  \<open>cdcl_twl_local_restart_wl_D_spec (M, N, D, NE, UE, Q, W) \<ge> ( do {
      ASSERT(restart_abs_wl_D_pre (M, N, D, NE, UE, Q, W) False);
      i \<leftarrow> SPEC(\<lambda>_. True);
      if i
      then RETURN (M, N, D, NE, UE, Q, W)
      else do {
        (M, Q') \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
              Q' = {#}) \<or> (M' = M \<and> Q' = Q));
        RETURN (M, N, D, NE, UE, Q', W)
     }
   })\<close>
proof -
  have If_Res: \<open>(if i then (RETURN f) else (RES g)) = (RES (if i then {f} else g))\<close> for i f g
    by auto
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_D_spec_def prod.case RES_RETURN_RES2 If_Res
    by refine_vcg
      (auto simp: If_Res RES_RETURN_RES2 RES_RES_RETURN_RES uncurry_def
        image_iff split:if_splits)
qed

lemma trail_pol_no_dup: \<open>(M, M') \<in> trail_pol \<A> \<Longrightarrow> no_dup M'\<close>
  by (auto simp: trail_pol_def)

lemma cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec:
  \<open>(cdcl_twl_local_restart_wl_D_heur, cdcl_twl_local_restart_wl_D_spec) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have K: \<open>( (case S of
               (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
                ccount, vdom, lcount) \<Rightarrow>
                 ASSERT (isa_length_trail_pre M) \<bind>
                 (\<lambda>_. RES {(M, N, D, isa_length_trail M, W, vm, \<phi>, clvls, cach,
                            lbd, outl, stats, fema, sema,
                            restart_info_restart_done ccount, vdom, lcount)}))) =
        ((ASSERT (case S of (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
                ccount, vdom, lcount) \<Rightarrow> isa_length_trail_pre M)) \<bind>
         (\<lambda> _. (case S of
               (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
                ccount, vdom, lcount) \<Rightarrow> RES {(M, N, D, isa_length_trail M, W, vm, \<phi>, clvls, cach,
                            lbd, outl, stats, fema, sema,
                            restart_info_restart_done ccount, vdom, lcount)})))\<close> for S
  by (cases S) auto

  have K2: \<open>(case S of
               (a, b) \<Rightarrow> RES (\<Phi> a b)) =
        (RES (case S of (a, b) \<Rightarrow> \<Phi> a b))\<close> for S
  by (cases S) auto

  have [dest]: \<open>av = None\<close> \<open>out_learned a av am \<Longrightarrow> out_learned x1 av am\<close>
    if \<open>restart_abs_wl_D_pre (a, au, av, aw, ax, ay, bd) False\<close>
    for a au av aw ax ay bd x1 am
    using that
    unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by (auto simp: twl_st_l_def state_wl_l_def out_learned_def)
  have [refine0]:
    \<open>find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S) \<le>
      \<Down> {(i, b). b = (i = count_decided (get_trail_wl T)) \<and>
          i \<le> count_decided (get_trail_wl T)} (SPEC (\<lambda>_. True))\<close>
    if \<open>(S, T) \<in> twl_st_heur\<close> for S T
    apply (rule find_local_restart_target_level_int_find_local_restart_target_level[THEN fref_to_Down_curry,
       THEN order_trans, of \<open>all_atms_st T\<close> \<open>get_trail_wl T\<close> \<open>get_vmtf_heur S\<close>])
    subgoal using that unfolding twl_st_heur_def by auto
    subgoal using that unfolding twl_st_heur_def by auto
    subgoal by (auto simp: find_local_restart_target_level_def conc_fun_RES)
    done
  have P: \<open>P\<close>
    if
      ST: \<open>(((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs),
	bt, bu, bv, bw, bx, by, bz)
       \<in> twl_st_heur\<close> and
      \<open>restart_abs_wl_D_pre (bt, bu, bv, bw, bx, by, bz) False\<close> and
      \<open>restart_abs_wl_heur_pre
	((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs)
	False\<close> and
      lvl: \<open>(lvl, i)
       \<in> {(i, b).
	  b = (i = count_decided (get_trail_wl (bt, bu, bv, bw, bx, by, bz))) \<and>
	  i \<le> count_decided (get_trail_wl (bt, bu, bv, bw, bx, by, bz))}\<close> and
      \<open>i \<in> {_. True}\<close> and
      \<open>lvl \<noteq>
       count_decided_st_heur
	((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs)\<close> and
      i: \<open>\<not> i\<close> and
    H: \<open>(\<And>vm0. ((an, bc), vm0) \<in> distinct_atoms_rel (all_atms_st (bt, bu, bv, bw, bx, by, bz)) \<Longrightarrow>
           ((aj, ak, al, am, bb), vm0) \<in> vmtf (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt \<Longrightarrow>
      isa_find_decomp_wl_imp (a, aa, ab, ac, ad, b) lvl
        ((aj, ak, al, am, bb), an, bc)
	\<le> \<Down> {(a, b). (a,b) \<in> trail_pol (all_atms_st (bt, bu, bv, bw, bx, by, bz)) \<times>\<^sub>f
               (Id \<times>\<^sub>f distinct_atoms_rel (all_atms_st (bt, bu, bv, bw, bx, by, bz)))}
	    (find_decomp_w_ns (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt lvl vm0) \<Longrightarrow> P)\<close>
    for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
       bw bx "by" bz lvl i x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
       x1g x2g x1h x2h x1i x2i P
  proof -
    have
      tr: \<open>((a, aa, ab, ac, ad, b), bt) \<in> trail_pol (all_atms bu (bw + bx))\<close> and
      \<open>valid_arena ae bu (set bo)\<close> and
      \<open>((af, ag, ba), bv)
       \<in> option_lookup_clause_rel (all_atms bu (bw + bx))\<close> and
      \<open>by = {#- lit_of x. x \<in># mset (drop ah (rev bt))#}\<close> and
      \<open>(ai, bz) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms bu (bw + bx)))\<close> and
      vm: \<open>((aj, ak, al, am, bb), an, bc) \<in> isa_vmtf (all_atms bu (bw + bx)) bt\<close> and
      \<open>phase_saving (all_atms bu (bw + bx)) ao\<close> and
      \<open>no_dup bt\<close> and
      \<open>ap \<in> counts_maximum_level bt bv\<close> and
      \<open>cach_refinement_empty (all_atms bu (bw + bx)) (aq, bd)\<close> and
      \<open>out_learned bt bv as\<close> and
      \<open>bq = size (learned_clss_l bu)\<close> and
      \<open>vdom_m (all_atms bu (bw + bx)) bz bu \<subseteq> set bo\<close> and
      \<open>set bp \<subseteq> set bo\<close> and
      \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms bu (bw + bx)). nat_of_lit L \<le> uint_max\<close> and
      \<open>all_atms bu (bw + bx) \<noteq> {#}\<close> and
      bounded: \<open>isasat_input_bounded (all_atms bu (bw + bx))\<close>
      using ST unfolding twl_st_heur_def all_atms_def[symmetric]
      by (auto)

    obtain vm0 where
      vm: \<open>((aj, ak, al, am, bb), vm0) \<in> vmtf (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt\<close> and
      vm0: \<open>((an, bc), vm0) \<in> distinct_atoms_rel (all_atms_st (bt, bu, bv, bw, bx, by, bz))\<close>
      using vm
      by (auto simp: isa_vmtf_def)
    have n_d: \<open>no_dup bt\<close>
      using tr by (auto simp: trail_pol_def)
    show ?thesis
      apply (rule H)
      apply (rule vm0)
      apply (rule vm)
      apply (rule isa_find_decomp_wl_imp_find_decomp_wl_imp[THEN fref_to_Down_curry2, THEN order_trans,
        of bt lvl \<open>((aj, ak, al, am, bb), vm0)\<close> _ _ _ \<open>all_atms_st (bt, bu, bv, bw, bx, by, bz)\<close>])
      subgoal using lvl i by auto
      subgoal using vm0 tr by auto
      apply (subst (3) Down_id_eq[symmetric])
      apply (rule order_trans)
      apply (rule ref_two_step')
      apply (rule find_decomp_wl_imp_find_decomp_wl'[THEN fref_to_Down_curry2, of _ bt lvl
        \<open>((aj, ak, al, am, bb), vm0)\<close>])
      subgoal
        using that(1-8) vm vm0 bounded n_d tr
	by (auto simp: find_decomp_w_ns_pre_def dest: trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
      subgoal by auto
        using ST
        by (auto simp: find_decomp_w_ns_def conc_fun_RES twl_st_heur_def)
  qed

  show ?thesis
    supply [[goals_limit=1]]
    unfolding cdcl_twl_local_restart_wl_D_heur_def
    unfolding
      find_decomp_wl_st_int_def find_local_restart_target_level_def incr_lrestart_stat_def
       empty_Q_def find_local_restart_target_level_st_def nres_monad_laws
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_local_restart_wl_D_spec_int)
    unfolding bind_to_let_conv Let_def RES_RETURN_RES2 nres_monad_laws
    apply (refine_vcg)
    subgoal unfolding restart_abs_wl_heur_pre_def by blast
    apply assumption
    subgoal by (auto simp: twl_st_heur_def count_decided_st_heur_def trail_pol_def)
    apply (rule P)
    apply assumption+
      apply (rule refine_generalise1)
      apply assumption
    subgoal for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
       bw bx "by" bz lvl i vm0
      unfolding RETURN_def RES_RES2_RETURN_RES RES_RES13_RETURN_RES find_decomp_w_ns_def conc_fun_RES
        RES_RES13_RETURN_RES K K2
	apply (auto simp: intro_spec_iff intro!: ASSERT_leI isa_length_trail_pre)
	apply (auto simp: isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
	  intro: isa_vmtfI trail_pol_no_dup)
	apply (clarsimp simp: twl_st_heur_def)
	apply (rule_tac x=aja in exI)
	apply (auto simp: isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
	  intro: isa_vmtfI trail_pol_no_dup)
	done
    done
qed


definition remove_all_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> nat watcher list \<Rightarrow> nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_inv S xs = (\<lambda>(i, T).
       \<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
         remove_all_annot_true_clause_imp_wl_D_inv S' (map fst xs) (i, T'))
     \<close>

definition remove_all_annot_true_clause_one_imp_heur
  :: \<open>nat \<times> nat \<times> arena \<Rightarrow> (nat \<times> arena) nres\<close>
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, j, N). do {
      case arena_status N C of
        DELETED \<Rightarrow> RETURN (j, N)
      | IRRED \<Rightarrow> RETURN (j, extra_information_mark_to_delete N C)
      | LEARNED \<Rightarrow> RETURN (j-1, extra_information_mark_to_delete N C)
  })\<close>

definition remove_all_annot_true_clause_imp_wl_D_heur_pre where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur_restart
      \<and> remove_all_annot_true_clause_imp_wl_D_pre (all_init_atms_st S') L S')\<close>


(* TODO: unfold Let when generating code! *)
definition remove_all_annot_true_clause_imp_wl_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl_D_heur = (\<lambda>L (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fast_ema, slow_ema, ccount, vdom, avdom, lcount, opts). do {
    ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_pre L (M, N0, D, Q, W, vm, \<phi>, clvls,
       cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts));
    let xs = W!(nat_of_lit L);
    (_, lcount', N) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, j, N).
        remove_all_annot_true_clause_imp_wl_D_heur_inv
           (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
	  fast_ema, slow_ema, ccount, vdom, avdom, lcount, opts) xs
           (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
	  fast_ema, slow_ema, ccount, vdom, avdom, j, opts)\<^esup>
      (\<lambda>(i, j, N). i < length xs)
      (\<lambda>(i, j, N). do {
        ASSERT(i < length xs);
        if clause_not_marked_to_delete_heur (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
	  fast_ema, slow_ema, ccount, vdom, avdom, lcount, opts) i
        then do {
          (j, N) \<leftarrow> remove_all_annot_true_clause_one_imp_heur (fst (xs!i), j, N);
          ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_inv
             (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
	       fast_ema, slow_ema, ccount, vdom, avdom, lcount, opts) xs
             (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
	       fast_ema, slow_ema, ccount, vdom, avdom, j, opts));
          RETURN (i+1, j, N)
        }
        else
          RETURN (i+1, j, N)
      })
      (0, lcount, N0);
    RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
	  fast_ema, slow_ema, ccount, vdom, avdom, lcount', opts)
  })\<close>


definition minimum_number_between_restarts :: \<open>uint64\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

lemma minimum_number_between_restarts[sepref_fr_rules]:
 \<open>(uncurry0 (return minimum_number_between_restarts), uncurry0 (RETURN minimum_number_between_restarts))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition five_uint64 :: \<open>uint64\<close> where
  \<open>five_uint64 = 5\<close>

lemma five_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return five_uint64), uncurry0 (RETURN five_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition two_uint64 :: \<open>uint64\<close> where
  \<open>two_uint64 = 2\<close>

lemma two_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return two_uint64), uncurry0 (RETURN two_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto


definition upper_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>upper_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    lcount < 3000 + 1000 * nat_of_uint64 restarts)\<close>

sepref_register upper_restart_bound_not_reached
sepref_definition upper_restart_bound_not_reached_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition upper_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare upper_restart_bound_not_reached_impl.refine[sepref_fr_rules]
  upper_restart_bound_not_reached_fast_impl.refine[sepref_fr_rules]


definition (in -) lower_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>lower_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
        (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
     (\<not>opts_reduce opts \<or> (opts_restart opts \<and> (lcount < 2000 + 1000 * nat_of_uint64 restarts))))\<close>

sepref_register lower_restart_bound_not_reached
sepref_definition lower_restart_bound_not_reached_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition lower_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare lower_restart_bound_not_reached_impl.refine[sepref_fr_rules]
  lower_restart_bound_not_reached_fast_impl.refine[sepref_fr_rules]


definition (in -) clause_score_extract :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>clause_score_extract arena C = (
     if arena_status arena C = DELETED
     then (uint32_max, zero_uint32_nat) \<comment> \<open>deleted elements are the
        largest possible\<close>
     else
       let lbd = get_clause_LBD arena C in
       let act = arena_act arena C in
       (lbd, act)
  )\<close>
sepref_register clause_score_extract

definition (in -)valid_sort_clause_score_pre_at where
  \<open>valid_sort_clause_score_pre_at arena C \<longleftrightarrow>
    (\<exists>i vdom. C = vdom ! i \<and> arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)))
          \<and> i < length vdom)\<close>

sepref_definition (in -) clause_score_extract_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply uint32_max_uint32_nat_assn[sepref_fr_rules]
  unfolding clause_score_extract_def insert_sort_inner_def valid_sort_clause_score_pre_at_def
  by sepref

declare clause_score_extract_code.refine[sepref_fr_rules]

definition (in -)valid_sort_clause_score_pre where
  \<open>valid_sort_clause_score_pre arena vdom \<longleftrightarrow>
    (\<forall>C \<in> set vdom. arena_is_valid_clause_vdom arena C \<and>
        (arena_status arena C \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena C \<and> arena_act_pre arena C)))\<close>

definition reorder_vdom_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>reorder_vdom_wl S = RETURN S\<close>

definition (in -) quicksort_clauses_by_score :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>quicksort_clauses_by_score arena =
    full_quicksort_ref clause_score_ordering (clause_score_extract arena)\<close>

definition (in -) sort_vdom_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>sort_vdom_heur = (\<lambda>(M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount). do {
    ASSERT(valid_sort_clause_score_pre arena avdom);
    avdom \<leftarrow> quicksort_clauses_by_score arena avdom;
    RETURN (M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount)
    })\<close>

lemma sort_clauses_by_score_reorder:
  \<open>quicksort_clauses_by_score arena vdom \<le> SPEC(\<lambda>vdom'. mset vdom = mset vdom')\<close>
  unfolding quicksort_clauses_by_score_def
  by (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down, THEN order_trans])
    (auto simp add: reorder_remove_def
     intro: full_quicksort[THEN order_trans])

lemma sort_vdom_heur_reorder_vdom_wl:
  \<open>(sort_vdom_heur, reorder_vdom_wl) \<in> twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding  reorder_vdom_wl_def sort_vdom_heur_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
        intro!: exI[of _ \<open>get_clauses_wl y\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_def dest: mset_eq_setD)
    done
qed

lemma (in -) insort_inner_clauses_by_score_invI:
   \<open>valid_sort_clause_score_pre a ba \<Longrightarrow>
       mset ba = mset a2' \<Longrightarrow>
       a1' < length a2' \<Longrightarrow>
       valid_sort_clause_score_pre_at a (a2' ! a1')\<close>
  unfolding valid_sort_clause_score_pre_def all_set_conv_nth valid_sort_clause_score_pre_at_def
  by (metis in_mset_conv_nth)+


lemma sort_clauses_by_score_invI:
  \<open>valid_sort_clause_score_pre a b \<Longrightarrow>
       mset b = mset a2' \<Longrightarrow> valid_sort_clause_score_pre a a2'\<close>
  using mset_eq_setD unfolding valid_sort_clause_score_pre_def by blast

definition partition_clause where
  \<open>partition_clause arena = partition_between_ref clause_score_ordering  (clause_score_extract arena)\<close>


sepref_definition (in -) partition_clause_code
  is \<open>uncurry3 partition_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn *a nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro]
  unfolding partition_clause_def partition_between_ref_def
    choose_pivot3_def
  by sepref

declare partition_clause_code.refine[sepref_fr_rules]

sepref_definition (in -) sort_clauses_by_score_code
  is \<open>uncurry quicksort_clauses_by_score\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding insert_sort_def
    quicksort_clauses_by_score_def
    full_quicksort_ref_def
    quicksort_ref_def
    partition_clause_def[symmetric]
    List.null_def
  by sepref


declare sort_clauses_by_score_code.refine[sepref_fr_rules]


sepref_definition sort_vdom_heur_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding sort_vdom_heur_def isasat_unbounded_assn_def
  by sepref

declare sort_vdom_heur_code.refine[sepref_fr_rules]

definition opts_restart_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_restart_st = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts). (opts_restart opts))\<close>

sepref_definition opts_restart_st_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_unbounded_assn_def
  by sepref

sepref_definition opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref

declare opts_restart_st_code.refine[sepref_fr_rules]
  opts_restart_st_fast_code.refine[sepref_fr_rules]

definition opts_reduction_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_reduction_st = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). (opts_reduce opts))\<close>

sepref_definition opts_reduction_st_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_unbounded_assn_def
  by sepref

sepref_definition opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

declare opts_reduction_st_code.refine[sepref_fr_rules]
  opts_reduction_st_fast_code.refine[sepref_fr_rules]

sepref_register opts_reduction_st opts_restart_st

definition max_restart_decision_lvl :: nat where
  \<open>max_restart_decision_lvl = 300\<close>

definition max_restart_decision_lvl_code :: uint32 where
  \<open>max_restart_decision_lvl_code = 300\<close>

sepref_register max_restart_decision_lvl

lemma max_restart_decision_lvl_code_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return max_restart_decision_lvl_code), uncurry0 (RETURN max_restart_decision_lvl)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def max_restart_decision_lvl_def
    max_restart_decision_lvl_code_def)

(* TODO Move*)

definition nat_of_uint64_id_conv :: \<open>uint64 \<Rightarrow> nat\<close> where
\<open>nat_of_uint64_id_conv = nat_of_uint64\<close>

lemma nat_of_uint64_id_conv_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o nat_of_uint64_id_conv) \<in> uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: nat_of_uint64_id_conv_def uint64_nat_rel_def br_def)

definition restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n = do {
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let sema = ema_get_value (get_slow_ema_heur S);
    let limit = (11 * sema) >> 4;
       \<comment>\<open>roughly speaking 125/100 with hopefully no overflow (there is currently no division
         on \<^typ>\<open>uint64\<close>\<close>
    let fema = ema_get_value (get_fast_ema_heur S);
    let ccount = get_conflict_count_since_last_restart_heur S;
    let lcount = get_learned_count S;
    let can_res = (lcount > n);
    let min_reached = (ccount > minimum_number_between_restarts);
    let level = count_decided_st_heur S;
    let should_not_reduce = (\<not>opt_red \<or> upper_restart_bound_not_reached S);
    RETURN ((opt_res \<or> opt_red) \<and>
       (should_not_reduce \<longrightarrow> limit > fema) \<and> min_reached \<and> can_res \<and>
      level > two_uint32_nat \<and> \<^cancel>\<open>This comment from Marijn Heule seems not to help: 
         \<^term>\<open>level < max_restart_decision_lvl\<close>\<close>
      uint64_of_uint32_conv level > nat_of_uint64_id_conv (fema >> 32))}
  \<close>


sepref_definition restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  bit_lshift_uint64_assn[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

sepref_definition restart_required_heur_slow_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  bit_lshift_uint64_assn[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

declare restart_required_heur_fast_code.refine[sepref_fr_rules]
  restart_required_heur_slow_code.refine[sepref_fr_rules]

definition mark_to_delete_clauses_wl_D_heur_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>mark_to_delete_clauses_wl_D_heur_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur_restart \<and> mark_to_delete_clauses_wl_D_pre S')\<close>

lemma mark_to_delete_clauses_wl_post_alt_def:
  \<open>mark_to_delete_clauses_wl_post S0 S \<longleftrightarrow>
    (\<exists>T0 T.
        (S0, T0) \<in> state_wl_l None \<and>
        (S, T) \<in> state_wl_l None \<and>
        (\<exists>U0 U. (T0, U0) \<in> twl_st_l None \<and>
               (T, U) \<in> twl_st_l None \<and>
               remove_one_annot_true_clause\<^sup>*\<^sup>* T0 T \<and>
               twl_list_invs T0 \<and>
               twl_struct_invs U0 \<and>
               twl_list_invs T \<and>
               twl_struct_invs U \<and>
               get_conflict_l T0 = None \<and>
	       clauses_to_update_l T0 = {#}) \<and>
        correct_watching S0 \<and> correct_watching S)\<close>
  unfolding mark_to_delete_clauses_wl_post_def mark_to_delete_clauses_l_post_def
    mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_D_pre_def
  apply (rule iffI; normalize_goal+)
  subgoal for T0 T U0
    apply (rule exI[of _ T0])
    apply (rule exI[of _ T])
    apply (intro conjI)
    apply auto[2]
    apply (rule exI[of _ U0])
    apply auto
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[of T0 T U0]
      rtranclp_cdcl_twl_restart_l_list_invs[of T0]
    apply (auto dest: )
     using rtranclp_cdcl_twl_restart_l_list_invs by blast
  subgoal for T0 T U0 U
    apply (rule exI[of _ T0])
    apply (rule exI[of _ T])
    apply (intro conjI)
    apply auto[2]
    apply (rule exI[of _ U0])
    apply auto
    done
  done

lemma mark_to_delete_clauses_wl_D_heur_pre_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur_pre S \<longleftrightarrow>
      (\<exists>S'. (S, S') \<in> twl_st_heur \<and> mark_to_delete_clauses_wl_D_pre S')\<close> (is ?A) and
    mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur:
      \<open>mark_to_delete_clauses_wl_D_pre T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close> (is \<open>_ \<Longrightarrow> _ ?B\<close>) and
    mark_to_delete_clauses_wl_post_twl_st_heur:
      \<open>mark_to_delete_clauses_wl_post T0 T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close> (is \<open>_ \<Longrightarrow> _ ?C\<close>)
proof -
  note cong =  trail_pol_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong

  show ?A
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def mark_to_delete_clauses_wl_pre_def
      mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_D_pre_def
    apply (rule iffI)
    apply normalize_goal+
    subgoal for T U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (rule exI[of _ T])
      apply (intro conjI) defer
      apply (rule exI[of _ U])
      apply (intro conjI) defer
      apply (rule exI[of _ V])
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    apply normalize_goal+
    subgoal for T U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (rule exI[of _ T])
      apply (intro conjI) defer
      apply (rule exI[of _ U])
      apply (intro conjI) defer
      apply (rule exI[of _ V])
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    done
  show \<open>mark_to_delete_clauses_wl_D_pre T \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def mark_to_delete_clauses_wl_pre_def
      mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_D_pre_def
    apply normalize_goal+
    apply (rule iffI)
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    done
  show  \<open>mark_to_delete_clauses_wl_post T0 T \<Longrightarrow> ?C\<close>
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_post_alt_def
    apply normalize_goal+
    apply (rule iffI)
    subgoal for U0 U V0 V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      apply (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
      done
    subgoal for U0 U V0 V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    done

qed

definition mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts))\<close>

lemma get_vdom_mark_garbage[simp]:
  \<open>get_vdom (mark_garbage_heur C i S) = get_vdom S\<close>
  \<open>get_avdom (mark_garbage_heur C i S) = delete_index_and_swap (get_avdom S) i\<close>
  by (cases S; auto simp: mark_garbage_heur_def; fail)+


lemma mark_garbage_heur_wl:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>\<not> irred (get_clauses_wl T) C\<close>
  shows \<open>(mark_garbage_heur C i S, mark_garbage_wl C T) \<in> twl_st_heur_restart\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
	all_init_atms_def[symmetric])
  apply (auto simp: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If
     simp: all_init_atms_def all_init_lits_def
     simp del: all_init_atms_def[symmetric]
     intro: valid_arena_extra_information_mark_to_delete'
      dest!: in_set_butlastD in_vdom_m_fmdropD
      elim!: in_set_upd_cases)
  done

definition mark_unused_st_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_unused_st_heur C = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
      stats, fast_ema, slow_ema, ccount, vdom, avdom, lcount, opts).
    (M', arena_decr_act (mark_unused N' C) C, D', j, W', vm, \<phi>, clvls, cach,
      lbd, outl, stats, fast_ema, slow_ema, ccount,
      vdom, avdom, lcount, opts))\<close>

lemma mark_unused_st_heur_simp[simp]:
  \<open>get_avdom (mark_unused_st_heur C T) = get_avdom T\<close>
  \<open>get_vdom (mark_unused_st_heur C T) = get_vdom T\<close>
  by (cases T; auto simp: mark_unused_st_heur_def; fail)+

lemma mark_unused_st_heur:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>(mark_unused_st_heur C S, T) \<in> twl_st_heur_restart\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_def mark_unused_st_heur_def
	all_init_atms_def[symmetric])
  apply (auto simp: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If
     simp: all_init_atms_def all_init_lits_def
     simp del: all_init_atms_def[symmetric]
     intro!: valid_arena_mark_unused valid_arena_arena_decr_act
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
  using assms by (fastforce simp: twl_st_heur_restart_def)

lemma [twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in> set (get_avdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow>
         (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
proof -
  show \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close>
    using assms
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_dom_status_iff(1)
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

definition number_clss_to_keep :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>number_clss_to_keep = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
      (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount).
    1000 + 150 * nat_of_uint64 restarts)\<close>


definition access_vdom_at :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_vdom_at S i = get_avdom S ! i\<close>

lemma access_vdom_at_alt_def:
  \<open>access_vdom_at = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount) i. avdom ! i)\<close>
  by (intro ext) (auto simp: access_vdom_at_def)

definition access_vdom_at_pre where
  \<open>access_vdom_at_pre S i \<longleftrightarrow> i < length (get_avdom S)\<close>

(* TODO Missing : The sorting function + definition of l should depend on the number of initial
  clauses *)
definition (in -) MINIMUM_DELETION_LBD :: nat where
  \<open>MINIMUM_DELETION_LBD = 3\<close>

lemma (in -) MINIMUM_DELETION_LBD_hnr[sepref_fr_rules]:
 \<open>(uncurry0 (return 3), uncurry0 (RETURN MINIMUM_DELETION_LBD)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: MINIMUM_DELETION_LBD_def uint32_nat_rel_def br_def)

definition delete_index_vdom_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close>where
  \<open>delete_index_vdom_heur = (\<lambda>i (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount).
     (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
       ccount, vdom, delete_index_and_swap avdom i, lcount))\<close>

lemma in_set_delete_index_and_swapD:
  \<open>x \<in> set (delete_index_and_swap xs i) \<Longrightarrow> x \<in> set xs\<close>
  apply (cases \<open>i < length xs\<close>)
  apply (auto dest!: in_set_butlastD)
  by (metis List.last_in_set in_set_upd_cases list.size(3) not_less_zero)


lemma delete_index_vdom_heur_twl_st_heur_restart:
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow>
    (delete_index_vdom_heur i S, T) \<in> twl_st_heur_restart\<close>
  by (auto simp: twl_st_heur_restart_def delete_index_vdom_heur_def
    dest: in_set_delete_index_and_swapD simp del: delete_index_and_swap.simps)

definition mark_clauses_as_unused_wl_D_heur
  :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>mark_clauses_as_unused_wl_D_heur  = (\<lambda>i S. do {
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, S). i < length (get_avdom S))
      (\<lambda>(i, T). do {
        ASSERT(i < length (get_avdom T));
        ASSERT(access_vdom_at_pre T i);
        let C = get_avdom T ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
        if \<not>clause_not_marked_to_delete_heur T C then RETURN (i, delete_index_vdom_heur i T)
        else do {
          ASSERT(arena_act_pre (get_clauses_wl_heur T) C);
          RETURN (i+1, mark_unused_st_heur C T)
        }
      })
      (i, S);
    RETURN T
  })\<close>

lemma avdom_delete_index_vdom_heur[simp]:
  \<open>get_avdom (delete_index_vdom_heur i S) =
     delete_index_and_swap (get_avdom S) i\<close>
  by (cases S) (auto simp: delete_index_vdom_heur_def)

lemma mark_clauses_as_unused_wl_D_heur:
  assumes \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>mark_clauses_as_unused_wl_D_heur i S \<le> \<Down> twl_st_heur_restart (SPEC ( (=) T))\<close>
proof -
  have 1: \<open> \<Down> twl_st_heur_restart (SPEC ( (=) T)) = do {
      (i, T) \<leftarrow> SPEC (\<lambda>(i::nat, T'). (T', T) \<in> twl_st_heur_restart);
      RETURN T
    }\<close>
    by (auto simp: RES_RETURN_RES2 uncurry_def conc_fun_RES)
  show ?thesis
    unfolding mark_clauses_as_unused_wl_D_heur_def 1
    apply (rule Refine_Basic.bind_mono)
    subgoal
      apply (refine_vcg
         WHILET_rule[where R = \<open>measure (\<lambda>(i, T). length (get_avdom T) - i)\<close> and
	   I = \<open>\<lambda>(_, S). (S, T) \<in> twl_st_heur_restart\<close>])
      subgoal by auto
      subgoal using assms by auto
      subgoal by auto
      subgoal unfolding access_vdom_at_pre_def by auto
      subgoal
        unfolding clause_not_marked_to_delete_heur_pre_def
	  arena_is_valid_clause_vdom_def
	by (fastforce simp: twl_st_heur_restart_def)
      subgoal
        by (auto intro: delete_index_vdom_heur_twl_st_heur_restart)
      subgoal by auto
      subgoal
        unfolding arena_is_valid_clause_idx_def
	  arena_is_valid_clause_vdom_def arena_act_pre_def
	by (fastforce simp: twl_st_heur_restart_def twl_st_heur_restart)
      subgoal by (auto intro!: mark_unused_st_heur simp: twl_st_heur_restart)
      subgoal by auto
      done
    subgoal
      by auto
    done
qed

definition mark_to_delete_clauses_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
    S \<leftarrow> sort_vdom_heur S;
    let l = number_clss_to_keep S;
    (i, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(i, S). i < length (get_avdom S))
      (\<lambda>(i, T). do {
        ASSERT(i < length (get_avdom T));
        ASSERT(access_vdom_at_pre T i);
        let C = get_avdom T ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
        if \<not>clause_not_marked_to_delete_heur T C then RETURN (i, delete_index_vdom_heur i T)
        else do {
          ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
          let L = access_lit_in_clauses_heur T C 0;
          D \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur T) L;
          ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
          ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
          ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
            arena_is_valid_clause_idx (get_clauses_wl_heur T) C);
          ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
	    marked_as_used_pre (get_clauses_wl_heur T) C);
          let can_del = (D \<noteq> Some C) \<and>
	     arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
             arena_status (get_clauses_wl_heur T) C = LEARNED \<and>
             arena_length (get_clauses_wl_heur T) C \<noteq> two_uint64_nat \<and>
	     \<not>marked_as_used (get_clauses_wl_heur T) C;
          if can_del
          then
            do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
          else do {
	    ASSERT(arena_act_pre (get_clauses_wl_heur T) C);
            RETURN (i+1, mark_unused_st_heur C T)
	  }
        }
      })
      (l, S);
    T \<leftarrow> mark_clauses_as_unused_wl_D_heur i T;
    incr_restart_stat T
  })\<close>

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

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_init_all:
  \<open>L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a) \<Longrightarrow> L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1a)\<close>
  apply (rule \<L>\<^sub>a\<^sub>l\<^sub>l_mono)
  defer
  apply assumption
  apply (cases x1a)
  apply (auto simp: all_init_atms_def all_lits_def all_init_lits_def
      all_lits_of_mm_union
    simp del: all_init_atms_def[symmetric])
  by (metis all_clss_l_ran_m all_lits_of_mm_union imageI image_mset_union union_iff)


lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D:
  \<open>(mark_to_delete_clauses_wl_D_heur, mark_to_delete_clauses_wl_D) \<in>
     twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
proof -
  have mark_to_delete_clauses_wl_D_alt_def:
    \<open>mark_to_delete_clauses_wl_D  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_pre S);
      S \<leftarrow> reorder_vdom_wl S;
      xs \<leftarrow> collect_valid_indices_wl S;
      l \<leftarrow> SPEC(\<lambda>_::nat. True);
      (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_D_inv S xs\<^esup>
        (\<lambda>(i, T, xs). i < length xs)
        (\<lambda>(i, T, xs). do {
          if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
          else do {
            ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	    ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
              (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
               \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2);
            ASSERT(i < length xs);
            if can_del
            then
              RETURN (i, mark_garbage_wl (xs!i) T, delete_index_and_swap xs i)
            else
              RETURN (i+1, T, xs)
          }
        })
        (l, S, xs);
      RETURN S
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_def reorder_vdom_wl_def
    by (auto intro!: ext)

  have mark_to_delete_clauses_wl_D_heur_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
      S \<leftarrow> sort_vdom_heur S;
      _ \<leftarrow> RETURN (get_avdom S);
      l \<leftarrow> RETURN (number_clss_to_keep S);
      (i, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
        (\<lambda>(i, S). i < length (get_avdom S))
        (\<lambda>(i, T). do {
          ASSERT(i < length (get_avdom T));
          ASSERT(access_vdom_at_pre T i);
          let C = get_avdom T ! i;
          ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
          if(\<not>clause_not_marked_to_delete_heur T C) then RETURN (i, delete_index_vdom_heur i T)
          else do {
            ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
            let L = access_lit_in_clauses_heur T C 0;
            D \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur T) L;
            ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
            ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
            ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
                arena_is_valid_clause_idx (get_clauses_wl_heur T) C);
            ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
	        marked_as_used_pre (get_clauses_wl_heur T) C);
            let can_del = (D \<noteq> Some C) \<and>
	       arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur T) C = LEARNED \<and>
               arena_length (get_clauses_wl_heur T) C \<noteq> two_uint64_nat \<and>
	       \<not>marked_as_used (get_clauses_wl_heur T) C;
            if can_del
            then do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
            else do {
  	      ASSERT(arena_act_pre (get_clauses_wl_heur T) C);
              RETURN (i+1, mark_unused_st_heur C T)
	    }
          }
        })
        (l, S);
      T \<leftarrow> mark_clauses_as_unused_wl_D_heur i T;
      incr_restart_stat T
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_heur_def
    by (auto intro!: ext)

  have [refine0]: \<open>RETURN (get_avdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_avdom x} (collect_valid_indices_wl y)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y
  proof -
    show ?thesis by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed
  have init_rel[refine0]: \<open>(x, y) \<in> twl_st_heur_restart \<Longrightarrow>
       (l, la) \<in> nat_rel \<Longrightarrow>
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur_restart \<and> get_avdom S = get_avdom x}\<close>
    for x y l la
    by auto

  have get_the_propagation_reason:
    \<open>get_the_propagation_reason_pol (get_trail_wl_heur x2b)
       (arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0))
        \<le> \<Down> {(D, b). b \<longleftrightarrow> ((D \<noteq> Some (get_avdom x2b ! x1b)) \<and>
               arena_lbd (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) = LEARNED) \<and>
               arena_length (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) \<noteq> two_uint32_nat \<and>
	       \<not>marked_as_used (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b)}
       (SPEC
           (\<lambda>b. b \<longrightarrow>
                Propagated (get_clauses_wl x1a \<propto> (x2a ! x1) ! 0) (x2a ! x1)
                \<notin> set (get_trail_wl x1a) \<and>
                \<not> irred (get_clauses_wl x1a) (x2a ! x1) \<and>
                length (get_clauses_wl x1a \<propto> (x2a ! x1)) \<noteq> 2 ))\<close>
  if
    \<open>(x, y) \<in> twl_st_heur_restart\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
    \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    xa_x': \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close> and
    \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
    \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
    \<open>x1b < length (get_avdom x2b)\<close> and
    \<open>access_vdom_at_pre x2b x1b\<close> and
    \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
    \<open>\<not> \<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
    \<open>\<not> x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close> and
    \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
    \<open>access_lit_in_clauses_heur_pre ((x2b, get_avdom x2b ! x1b), 0)\<close> and
    st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
    L: \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
    for x y S Sa xs' xs l la xa x' x1 x2 x1a x2a x1' x2' x3 x1b ys x2b
  proof -
    have L: \<open>arena_lit (get_clauses_wl_heur x2b) (x2a ! x1) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      using L that by (auto simp: twl_st_heur_restart st arena_lifting dest: \<L>\<^sub>a\<^sub>l\<^sub>l_init_all)

    show ?thesis
      apply (rule order.trans)
      apply (rule get_the_propagation_reason_pol[THEN fref_to_Down_curry,
        of \<open>all_init_atms_st x1a\<close> \<open>get_trail_wl x1a\<close>
	  \<open>arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0)\<close>])
      subgoal
        using xa_x' L by (auto simp add: twl_st_heur_restart_def st)
      subgoal
        using xa_x' by (auto simp add: twl_st_heur_restart_def st)
      using that unfolding get_the_propagation_reason_def apply -
      by (auto simp: twl_st_heur_restart lits_of_def get_the_propagation_reason_def
          conc_fun_RES
        dest: twl_st_heur_restart_same_annotD imageI[of _ _ lit_of])
  qed
  have \<open>((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom, lcount),
           S')
          \<in> twl_st_heur_restart \<longleftrightarrow>
    ((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom', lcount),
           S')
          \<in> twl_st_heur_restart\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema
      ccount vdom lcount S' avdom' avdom
    using that unfolding twl_st_heur_restart_def
    by auto
  then have mark_to_delete_clauses_wl_D_heur_pre_vdom':
    \<open>mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, vdom, avdom, lcount) \<longleftrightarrow>
      mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
        fast_ema, slow_ema, ccount, vdom, avdom', lcount)\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount vdom lcount
    using that
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def
    by metis
  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart \<and> V = T \<and>
         (mark_to_delete_clauses_wl_D_pre T \<longrightarrow> mark_to_delete_clauses_wl_D_pre V) \<and>
         (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U)}
         (reorder_vdom_wl T)\<close>
    if \<open>(S, T) \<in> twl_st_heur_restart\<close> for S T
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply (refine_rcg ASSERT_leI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_def
         intro: mark_to_delete_clauses_wl_D_heur_pre_vdom'[THEN iffD1]
         dest: mset_eq_setD)
    done
  have already_deleted:
    \<open>((x1b, delete_index_vdom_heur x1b x2b), x1, x1a,
       delete_index_and_swap x2a x1)
      \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
      \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv Sa xs x'\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      \<open>x1b < length (get_avdom x2b)\<close> and
      \<open>access_vdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
      \<open>\<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
      \<open>x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa
  proof -
    show ?thesis
      using xx unfolding st
      by (auto simp: twl_st_heur_restart_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If
          intro: valid_arena_extra_information_mark_to_delete'
          dest!: in_set_butlastD in_vdom_m_fmdropD
          elim!: in_set_upd_cases)
  qed

  have init:
    \<open>(u, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S} \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart \<Longrightarrow>
    mark_to_delete_clauses_wl_D_inv Sa xs (la, Sa, xs) \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
       {(Sa, (T, xs)). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close>
       for x y S Sa xs l la u
    by auto
  have [refine0]: \<open>mark_clauses_as_unused_wl_D_heur i T
    \<le> SPEC
       (\<lambda>x. incr_restart_stat x \<le> SPEC (\<lambda>c. (c, S) \<in> twl_st_heur_restart))\<close>
    if \<open>(T, S) \<in> twl_st_heur_restart\<close> for S T i
    by (rule order_trans, rule mark_clauses_as_unused_wl_D_heur[OF that, of i])
      (auto simp: conc_fun_RES incr_restart_stat_def
        twl_st_heur_restart_def)
  show ?thesis
    supply sort_vdom_heur_def[simp]
    unfolding mark_to_delete_clauses_wl_D_heur_alt_def mark_to_delete_clauses_wl_D_alt_def
      access_lit_in_clauses_heur_def Let_def
    apply (intro frefI nres_relI)
    apply (refine_vcg sort_vdom_heur_reorder_vdom_wl[THEN fref_to_Down])
    subgoal
      unfolding mark_to_delete_clauses_wl_D_heur_pre_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule init; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_vdom_at_pre_def)
    subgoal for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d
      unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
        prod.simps
      by (rule exI[of _ \<open>get_clauses_wl x2a\<close>], rule exI[of _ \<open>set (get_vdom x2d)\<close>])
         (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal
      by (auto simp: twl_st_heur_restart)
    subgoal
      by (rule already_deleted)
    subgoal for x y _ _ _ _ _ xs l la xa x' x1 x2 x1a x2a
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_avdom x2a ! x1a\<close>], simp, rule exI[of _ \<open>get_clauses_wl x1\<close>])
        (auto simp: twl_st_heur_restart_def)
    apply (rule get_the_propagation_reason; assumption)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena
	  twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart arena_dom_status_iff
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal unfolding marked_as_used_pre_def by fast
    subgoal
      by (auto simp: twl_st_heur_restart)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_garbage_heur_wl)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def arena_act_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_unused_st_heur)
    subgoal
      by (auto simp:)
    done
qed

definition cdcl_twl_full_restart_wl_prog_heur where
\<open>cdcl_twl_full_restart_wl_prog_heur S = do {
  _ \<leftarrow> ASSERT (mark_to_delete_clauses_wl_D_heur_pre S);
  T \<leftarrow> mark_to_delete_clauses_wl_D_heur S;
  RETURN T
}\<close>

lemma cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D:
  \<open>(cdcl_twl_full_restart_wl_prog_heur, cdcl_twl_full_restart_wl_prog_D) \<in>
     twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def cdcl_twl_full_restart_wl_prog_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D[THEN fref_to_Down])
  subgoal
    unfolding mark_to_delete_clauses_wl_D_heur_pre_alt_def
    by fast
  subgoal
    by (subst mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur[symmetric])
  subgoal
    by (subst mark_to_delete_clauses_wl_post_twl_st_heur)
  done

definition cdcl_twl_restart_wl_heur where
\<open>cdcl_twl_restart_wl_heur S = do {
    let b = lower_restart_bound_not_reached S;
    if b then cdcl_twl_local_restart_wl_D_heur S
    else cdcl_twl_full_restart_wl_prog_heur S
  }\<close>


lemma cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog:
  \<open>(cdcl_twl_restart_wl_heur, cdcl_twl_restart_wl_D_prog) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_D_prog_def cdcl_twl_restart_wl_heur_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
    cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec[THEN fref_to_Down]
    cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D[THEN fref_to_Down])
  subgoal by auto
  subgoal by auto
  done


definition restart_prog_wl_D_heur
  :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur \<times> nat) nres"
where
  \<open>restart_prog_wl_D_heur S n brk = do {
    b \<leftarrow> restart_required_heur S n;
    if \<not>brk \<and> b
    then do {
       T \<leftarrow> cdcl_twl_restart_wl_heur S;
       RETURN (T, n+1)
    }
    else RETURN (S, n)
  }\<close>

lemma restart_required_heur_restart_required_wl:
  \<open>(uncurry restart_required_heur, uncurry restart_required_wl) \<in>
    twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding restart_required_heur_def restart_required_wl_def uncurry_def Let_def
    by (intro frefI nres_relI)
     (auto simp: twl_st_heur_def get_learned_clss_wl_def)

lemma restart_prog_wl_D_heur_restart_prog_wl_D:
  \<open>(uncurry2 restart_prog_wl_D_heur, uncurry2 restart_prog_wl_D) \<in>
    twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel  \<rightarrow>\<^sub>f \<langle>twl_st_heur \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  unfolding restart_prog_wl_D_heur_def restart_prog_wl_D_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
      restart_required_heur_restart_required_wl[THEN fref_to_Down_curry]
      cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog[THEN fref_to_Down])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition isasat_replace_annot_in_trail
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>isasat_replace_annot_in_trail L C = (\<lambda>((M, val, lvls, reason, k), oth). do {
      ASSERT(atm_of L < length reason);
      RETURN ((M, val, lvls, reason[atm_of L := 0], k), oth)
    })\<close>

lemma trail_pol_replace_annot_in_trail_spec:
  assumes
    \<open>atm_of x2 < length x1e\<close> and
    x2: \<open>atm_of x2 \<in># all_init_atms_st (ys @ Propagated x2 C # zs, x2n')\<close> and
    \<open>(((x1b, x1c, x1d, x1e, x2d), x2n),
        (ys @ Propagated x2 C # zs, x2n'))
       \<in> twl_st_heur_restart\<close>
  shows
    \<open>(((x1b, x1c, x1d, x1e[atm_of x2 := 0], x2d), x2n),
        (ys @ Propagated x2 0 # zs, x2n'))
       \<in> twl_st_heur_restart\<close>
proof -
  let ?S = \<open>(ys @ Propagated x2 C # zs, x2n')\<close>
  let ?\<A> = \<open>all_init_atms_st ?S\<close>
  have pol: \<open>((x1b, x1c, x1d, x1e, x2d), ys @ Propagated x2 C # zs)
         \<in> trail_pol (all_init_atms_st ?S)\<close>
    using assms(3) unfolding twl_st_heur_restart_def
    by auto
  obtain x y where
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
    \<open>length (ys @ Propagated x2 C # zs) < uint_max\<close> and
    \<open>length (ys @ Propagated x2 C # zs) \<le> uint_max div 2 + 1\<close> and
    \<open>count_decided (ys @ Propagated x2 C # zs) < uint_max\<close> and
    \<open>length (map lit_of (rev (ys @ Propagated x2 C # zs))) =
     length (ys @ Propagated x2 C # zs)\<close> and
    bounded: \<open>isasat_input_bounded ?\<A>\<close> and
    x1b: \<open>x1b = map lit_of (rev (ys @ Propagated x2 C # zs))\<close>
    using pol unfolding trail_pol_alt_def
    by blast
  have lev_eq: \<open>get_level (ys @ Propagated x2 C # zs) =
    get_level (ys @ Propagated x2 0 # zs)\<close>
    \<open>count_decided (ys @ Propagated x2 C # zs) =
      count_decided (ys @ Propagated x2 0 # zs)\<close>
    by (auto simp: get_level_cons_if get_level_append_if)
  have [simp]: \<open>atm_of x2 < length x1e\<close>
    using reasons x2 in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
    by (auto simp: ann_lits_split_reasons_def
      dest: multi_member_split)
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
    using assms(3) unfolding twl_st_heur_restart_def
    by (cases x2n; cases x2n')
      (auto simp: twl_st_heur_restart_def
        simp flip: mset_map drop_map)
qed

lemmas trail_pol_replace_annot_in_trail_spec2 =
  trail_pol_replace_annot_in_trail_spec[of \<open>- _\<close>, simplified]

lemma isasat_replace_annot_in_trail_replace_annot_in_trail_spec:
  \<open>(uncurry2 isasat_replace_annot_in_trail,
    uncurry2 replace_annot_l) \<in>
    [\<lambda>((L, C), S).
       Propagated L C \<in> set (get_trail_wl S) \<and> atm_of L \<in># all_init_atms_st S]\<^sub>f
       Id \<times>\<^sub>f Id\<times>\<^sub>f twl_st_heur_restart \<rightarrow> \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
  unfolding isasat_replace_annot_in_trail_def replace_annot_l_def
    uncurry_def
  apply (intro frefI nres_relI)
  apply refine_rcg
  subgoal
    using in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
    by (auto simp: trail_pol_alt_def ann_lits_split_reasons_def
      twl_st_heur_restart_def)
  subgoal for x y x1 x1a x2 x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
      x2f x1g x2g x1h x1i
      x2h x2i x1j x1k x2j x1l x2k x1m x2l x1n x2m x2n
    apply (clarify dest!: split_list[of \<open>Propagated _ _\<close>])
    apply (rule RETURN_SPEC_refine)
    apply (rule_tac x = \<open>(ys @ Propagated x1a 0 # zs, x1c, x1d,
      x1e, x1f, x1g, x2g)\<close> in exI)
    apply (intro conjI)
    prefer 2
    apply (rule_tac x = \<open>ys @ Propagated x1a 0 # zs\<close> in exI)
    apply (intro conjI)
    apply blast
    by (auto intro!: trail_pol_replace_annot_in_trail_spec
        trail_pol_replace_annot_in_trail_spec2
      simp: atm_of_eq_atm_of all_init_atms_def
      simp del: all_init_atms_def[symmetric])
  done

definition mark_garbage_heur2 :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur2 C = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, if arena_status N' C = IRRED then lcount else lcount - 1, opts))\<close>

definition remove_one_annot_true_clause_one_imp_wl_D_heur
  :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> twl_st_wl_heur) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl_D_heur = (\<lambda>i S. do {
      (L, C) \<leftarrow> do {
        L \<leftarrow> isa_trail_nth (get_trail_wl_heur S) i;
	C \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur S) L;
	RETURN (L, C)};
      ASSERT(C \<noteq> None);
      if the C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<noteq> None);
        S \<leftarrow> isasat_replace_annot_in_trail L (the C) S;
	ASSERT(mark_garbage_pre (get_clauses_wl_heur S, the C));
        let S = mark_garbage_heur2 (the C) S;
        \<comment> \<open>\<^text>\<open>S \<leftarrow> remove_all_annot_true_clause_imp_wl_D_heur L S;\<close>\<close>
        RETURN (i+1, S)
      }
  })\<close>

definition cdcl_twl_full_restart_wl_D_GC_prog_heur_post :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_D_GC_prog_heur_post S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
    cdcl_twl_full_restart_wl_D_GC_prog_post S' T')\<close>

definition remove_one_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> (nat \<times> twl_st_wl_heur) \<Rightarrow> bool\<close> where
  \<open>remove_one_annot_true_clause_imp_wl_D_heur_inv S = (\<lambda>(i, T).
    (\<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
     remove_one_annot_true_clause_imp_wl_D_inv S' (i, T')))\<close>

definition remove_one_annot_true_clause_imp_wl_D_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl_D_heur = (\<lambda>S. do {
    k \<leftarrow> (if count_decided_st_heur S = 0
      then RETURN (isa_length_trail (get_trail_wl_heur S))
      else get_pos_of_level_in_trail_imp (get_trail_wl_heur S) 0);
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_D_heur_inv S\<^esup>
      (\<lambda>(i, S). i < k)
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl_D_heur i S)
      (0, S);
    RETURN S
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
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> isa_length_trail (get_trail_wl_heur S) = length (get_trail_wl T)\<close>
  unfolding isa_length_trail_def twl_st_heur_restart_def trail_pol_def
  by (cases S) (auto dest: ann_lits_split_reasons_map_lit_of)

lemma twl_st_heur_restart_count_decided_st_alt_def:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> count_decided_st_heur S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_restart_def trail_pol_def
  by (cases S) (auto simp: count_decided_st_heur_def)

lemma twl_st_heur_restart_trailD:
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow>
    (get_trail_wl_heur S, get_trail_wl T)
    \<in> trail_pol (all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T))\<close>
  by (auto simp: twl_st_heur_restart_def)

lemma no_dup_nth_proped_dec_notin:
  \<open>no_dup M \<Longrightarrow> k < length M \<Longrightarrow> M ! k = Propagated L C \<Longrightarrow> Decided L \<notin> set M\<close>
  apply (auto dest!: split_list simp: nth_append nth_Cons defined_lit_def in_set_conv_nth
    split: if_splits nat.splits)
  by (metis no_dup_no_propa_and_dec nth_mem)


(*TODO Move*)
lemma RES_ASSERT_moveout:
  "(\<And>a. a \<in> P \<Longrightarrow> Q a) \<Longrightarrow> do {a \<leftarrow> RES P; ASSERT(Q a); (f a)} =
   do {a\<leftarrow> RES P; (f a)}"
  apply (subst order_class.eq_iff)
  apply (rule conjI)
  subgoal
    by (refine_rcg bind_refine_RES[where R=Id, unfolded Down_id_eq])
      auto
  subgoal
    by (refine_rcg bind_refine_RES[where R=Id, unfolded Down_id_eq])
      auto
  done

lemma remove_all_annot_true_clause_imp_wl_inv_length_cong:
  \<open>remove_all_annot_true_clause_imp_wl_inv S xs T \<Longrightarrow>
    length xs = length ys \<Longrightarrow> remove_all_annot_true_clause_imp_wl_inv S ys T\<close>
  by (auto simp: remove_all_annot_true_clause_imp_wl_inv_def
    remove_all_annot_true_clause_imp_inv_def)

lemma get_literal_and_reason:
  assumes
    \<open>((k, S), k', T) \<in> nat_rel \<times>\<^sub>f twl_st_heur_restart\<close> and
    \<open>remove_one_annot_true_clause_one_imp_wl_D_pre k' T\<close> and
    proped: \<open>is_proped (rev (get_trail_wl T) ! k')\<close>
  shows \<open>do {
           L \<leftarrow> isa_trail_nth (get_trail_wl_heur S) k;
           C \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur S) L;
           RETURN (L, C)
         } \<le> \<Down> {((L, C), L', C'). L = L' \<and> C' = the C \<and> C \<noteq> None}
              (SPEC (\<lambda>p. rev (get_trail_wl T) ! k' = Propagated (fst p) (snd p)))\<close>
proof -
  have n_d: \<open>no_dup (get_trail_wl T)\<close>
    using assms by (auto simp: twl_st_heur_restart_def)
  from no_dup_nth_proped_dec_notin[OF this, of \<open>length (get_trail_wl T) - Suc k'\<close>]
  have dec_notin: \<open>Decided (lit_of (rev (fst T) ! k')) \<notin> set (fst T)\<close>
    using proped assms(2) by (cases T; cases \<open>rev (get_trail_wl T) ! k'\<close>)
     (auto simp: twl_st_heur_restart_def
      remove_one_annot_true_clause_one_imp_wl_D_pre_def state_wl_l_def
      remove_one_annot_true_clause_one_imp_wl_pre_def twl_st_l_def
      remove_one_annot_true_clause_one_imp_pre_def rev_nth
      dest: no_dup_nth_proped_dec_notin)
  have k': \<open>k' < length (get_trail_wl T)\<close> and [simp]: \<open>fst T = get_trail_wl T\<close>
    using proped assms(2)
    by (cases T; auto simp: twl_st_heur_restart_def
      remove_one_annot_true_clause_one_imp_wl_D_pre_def state_wl_l_def
      remove_one_annot_true_clause_one_imp_wl_pre_def twl_st_l_def
      remove_one_annot_true_clause_one_imp_pre_def; fail)+
  define k'' where \<open>k'' \<equiv> length (get_trail_wl T) - Suc k'\<close>
  have k'': \<open>k'' < length (get_trail_wl T)\<close>
    using k' by (auto simp: k''_def)
  have \<open>rev (get_trail_wl T) ! k' = get_trail_wl T ! k''\<close>
    using k' k'' by (auto simp: k''_def nth_rev)
  then have \<open>rev_trail_nth (fst T) k' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T))\<close>
    using k'' assms nth_mem[OF k']
    by (auto simp: twl_st_heur_restart_def rev_trail_nth_def
      trail_pol_alt_def)
  then have 1: \<open>(SPEC (\<lambda>p. rev (get_trail_wl T) ! k' = Propagated (fst p) (snd p))) =
    do {
      L \<leftarrow> RETURN (rev_trail_nth (fst T) k');
      ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T)));
      C \<leftarrow> (get_the_propagation_reason (fst T) L);
      ASSERT(C \<noteq> None);
      RETURN (L, the C)
    }\<close>
    using proped dec_notin k' nth_mem[OF k''] no_dup_same_annotD[OF n_d]
    apply (subst order_class.eq_iff)
    apply (rule conjI)
    subgoal
      unfolding get_the_propagation_reason_def
      by (cases \<open>rev (get_trail_wl T) ! k'\<close>)
        (auto simp: RES_RES_RETURN_RES rev_trail_nth_def
            get_the_propagation_reason_def lits_of_def rev_nth
  	    RES_RETURN_RES
          dest: split_list
	  simp flip: k''_def
	  intro!: le_SPEC_bindI[of _ \<open>Some (mark_of (get_trail_wl T ! k''))\<close>])
    subgoal
      apply (cases \<open>rev (get_trail_wl T) ! k'\<close>) (*TODO proof*)
      apply  (auto simp: RES_RES_RETURN_RES rev_trail_nth_def
          get_the_propagation_reason_def lits_of_def rev_nth
	  RES_RETURN_RES
        simp flip: k''_def
        dest: split_list
        intro!: exI[of _ \<open>Some (mark_of (rev (fst T) ! k'))\<close>])
	  apply (subst RES_ASSERT_moveout)
	  apply (auto simp: RES_RETURN_RES
        dest: split_list)
	done
    done

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (subst 1)
    apply (refine_rcg
      isa_trail_nth_rev_trail_nth[THEN fref_to_Down_curry, unfolded comp_def,
        of _ _ _ _ \<open>(all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T))\<close>]
      get_the_propagation_reason_pol[THEN fref_to_Down_curry, unfolded comp_def,
        of \<open>(all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T))\<close>])
    subgoal using k' by auto
    subgoal using assms by (cases S; auto dest: twl_st_heur_restart_trailD)
    subgoal by auto
    subgoal for K K'
      using assms by (auto simp: twl_st_heur_restart_def)
    subgoal
      by auto
    done
qed
(*
lemma extra_information_mark_to_delete_extract_and_remove:
  \<open>valid_arena N N' vdom \<Longrightarrow> C \<in># dom_m N' \<Longrightarrow> C = C' \<Longrightarrow>
  RETURN (extra_information_mark_to_delete N C)
    \<le> \<Down> {(N, (N', C, b)). valid_arena N N' vdom} (extract_and_remove N' C')\<close>
  by (auto simp: extract_and_remove_def RETURN_RES_refine_iff
    intro: valid_arena_extra_information_mark_to_delete')
*)

lemma all_init_atms_fmdrop_add_mset_unit:
  \<open>C \<in># dom_m baa \<Longrightarrow> irred baa C \<Longrightarrow>
    all_init_atms (fmdrop C baa) (add_mset (mset (baa \<propto> C)) da) =
   all_init_atms baa da\<close>
  \<open>C \<in># dom_m baa \<Longrightarrow> \<not>irred baa C \<Longrightarrow>
    all_init_atms (fmdrop C baa) da =
   all_init_atms baa da\<close>
  by (auto simp del: all_init_atms_def[symmetric]
    simp: all_init_atms_def all_init_lits_def
      init_clss_l_fmdrop_irrelev image_mset_remove1_mset_if)


lemma learned_clss_l_l_fmdrop_irrelev: \<open>irred N C \<Longrightarrow>
  learned_clss_l (fmdrop C N) = learned_clss_l N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma mark_garbage_heur2_remove_and_add_cls_l:
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> (C, C') \<in> Id \<Longrightarrow>
    C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
    RETURN (mark_garbage_heur2 C S)
       \<le> \<Down> twl_st_heur_restart (remove_and_add_cls_l C' T)\<close>
  unfolding mark_garbage_heur2_def remove_and_add_cls_l_def
  by (cases S; cases T)
    (auto simp: twl_st_heur_restart_def arena_lifting
      valid_arena_extra_information_mark_to_delete'
      all_init_atms_fmdrop_add_mset_unit learned_clss_l_l_fmdrop
      learned_clss_l_l_fmdrop_irrelev
      size_Diff_singleton
    dest: in_vdom_m_fmdropD)

lemma remove_one_annot_true_clause_one_imp_wl_D_heur_remove_one_annot_true_clause_one_imp_wl_D:
  \<open>(uncurry remove_one_annot_true_clause_one_imp_wl_D_heur,
    uncurry remove_one_annot_true_clause_one_imp_wl_D) \<in>
    nat_rel \<times>\<^sub>f twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>f twl_st_heur_restart\<rangle>nres_rel\<close>
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    remove_one_annot_true_clause_one_imp_wl_D_def case_prod_beta uncurry_def
  apply (intro frefI nres_relI)
  subgoal for x y
  apply (refine_rcg get_literal_and_reason
    isasat_replace_annot_in_trail_replace_annot_in_trail_spec
      [THEN fref_to_Down_curry2]
    mark_garbage_heur2_remove_and_add_cls_l)
  subgoal by auto
  subgoal unfolding remove_one_annot_true_clause_one_imp_wl_D_pre_def
    by auto
  subgoal by auto
  subgoal by (cases x, cases y) auto
  subgoal by auto
  subgoal
    by (cases x, cases y)
     (fastforce simp: twl_st_heur_restart_def
       trail_pol_alt_def)+
  subgoal
    by (cases x, cases y)
     (fastforce simp: twl_st_heur_restart_def
       trail_pol_alt_def)+
  subgoal for p pa S Sa
    unfolding mark_garbage_pre_def
      arena_is_valid_clause_idx_def
      prod.case
    apply (rule_tac x = \<open>get_clauses_wl Sa\<close> in exI)
    apply (rule_tac x = \<open>set (get_vdom S)\<close> in exI)
    apply (case_tac S, case_tac Sa)
    apply (auto simp: twl_st_heur_restart_def)
    done
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by (cases x, cases y) fastforce
  done
  done

(*
lemma remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D:
  \<open>(remove_one_annot_true_clause_imp_wl_D_heur, remove_one_annot_true_clause_imp_wl_D) \<in>
    twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
  unfolding remove_one_annot_true_clause_imp_wl_D_heur_def
    remove_one_annot_true_clause_imp_wl_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg WHILEIT_refine[where R = \<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> twl_st_heur_restart \<and> 
     literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T}\<close>])
  subgoal by (auto simp: twl_st_heur_restart_count_decided_st_alt_def
    twl_st_heur_restart_isa_length_trail_get_trail_wl)
  subgoal for S T
    apply (rule order_trans)
      apply (rule get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail_CS[THEN fref_to_Down_curry,
        of \<open>get_trail_wl T\<close> \<open>0::nat\<close> \<open>get_trail_wl_heur S\<close> _ \<open>all_init_atms_st T\<close>])
    apply (auto simp: get_pos_of_level_in_trail_pre_def twl_st_heur_restart_count_decided_st_alt_def
      dest: twl_st_heur_restart_trailD
      intro!: get_pos_of_level_in_trail_le_decomp)
    done
  subgoal
    by (auto simp: remove_one_annot_true_clause_imp_wl_D_inv_def)
  subgoal for x y k ka xa x'
    unfolding remove_one_annot_true_clause_imp_wl_D_heur_inv_def
    apply (subst case_prod_beta)
    apply (subst (asm)(11) surjective_pairing)
    apply (subst (asm)(9) surjective_pairing)
    unfolding prod_rel_iff
    apply (rule_tac x=y in exI)
    apply (rule_tac x= \<open>snd x'\<close> in exI)
    apply auto
    done
  subgoal by auto
  subgoal sorry
  subgoal by auto
  done


    *)


definition cdcl_twl_full_restart_wl_D_GC_heur_prog where
\<open>cdcl_twl_full_restart_wl_D_GC_heur_prog S = do {
    S \<leftarrow> do {
      if count_decided_st_heur S > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S;
        empty_Q S
      } else RETURN S
    };
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    U \<leftarrow> mark_to_delete_clauses_wl_D_heur T;
    V \<leftarrow> RETURN U;
    RETURN V
  }\<close>


lemma RES_RETURN_RES5:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T1, T2, T3, T4, T5). RETURN (f T1 T2 T3 T4 T5)) =
    RES ((\<lambda>(a, b, c, d, e). f a b c d e) ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c, d, e). f a b c d e\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  apply (subst (asm)(4) split_prod_bound)
  apply (subst (asm)(5) split_prod_bound)
  by simp

lemma RES_RETURN_RES6:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T1, T2, T3, T4, T5, T6). RETURN (f T1 T2 T3 T4 T5 T6)) =
    RES ((\<lambda>(a, b, c, d, e, f'). f a b c d e f') ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c, d, e, f'). f a b c d e f'\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  apply (subst (asm)(4) split_prod_bound)
  apply (subst (asm)(5) split_prod_bound)
  apply (subst (asm)(6) split_prod_bound)
  by simp

lemma RES_RETURN_RES7:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T1, T2, T3, T4, T5, T6, T7). RETURN (f T1 T2 T3 T4 T5 T6 T7)) =
    RES ((\<lambda>(a, b, c, d, e, f', g). f a b c d e f' g) ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c, d, e, f', g). f a b c d e f' g\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  apply (subst (asm)(4) split_prod_bound)
  apply (subst (asm)(5) split_prod_bound)
  apply (subst (asm)(6) split_prod_bound)
  apply (subst (asm)(7) split_prod_bound)
  by simp

definition find_decomp_wl0 where
  \<open>find_decomp_wl0 = (\<lambda>(M, N, D, NE, UE, Q, W) (M', N', D', NE', UE', Q', W').
	 (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
	    count_decided M' = 0) \<and>
	  (N', D', NE', UE', Q', W') = (N, D, NE, UE, Q, W))\<close>

definition empty_Q_wl :: \<open>_\<close> where
\<open>empty_Q_wl = (\<lambda>(M', N, D, NE, UE, _, W). (M', N, D, NE, UE, {#}, W))\<close>

lemma cdcl_twl_local_restart_wl_spec0_alt_def:
  \<open>cdcl_twl_local_restart_wl_spec0 = (\<lambda>S.
    if count_decided (get_trail_wl S) > 0
    then do {
      T \<leftarrow> SPEC(find_decomp_wl0 S);
      RETURN (empty_Q_wl T)
    } else RETURN S)\<close>
  by (intro ext; case_tac S)
    (fastforce simp: cdcl_twl_local_restart_wl_spec0_def
	RES_RETURN_RES2 image_iff RES_RETURN_RES
	find_decomp_wl0_def empty_Q_wl_def
      dest: get_all_ann_decomposition_exists_prepend)

lemma cdcl_twl_local_restart_wl_spec0:
  assumes Sy:  \<open>(S, y) \<in> twl_st_heur_restart\<close> and
    \<open>get_conflict_wl y = None\<close>
  shows \<open>do {
      if count_decided_st_heur S > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S;
        empty_Q S
      } else RETURN S
    }
         \<le> \<Down> twl_st_heur_restart (cdcl_twl_local_restart_wl_spec0 y)\<close>
proof -
  define upd :: \<open>_ \<Rightarrow> _ \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
    \<open>upd M' vm = (\<lambda> (_, N, D, Q, W, _, \<phi>, clvls, cach, lbd, stats).
       (M', N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats))\<close>
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
	} \<le> \<Down> {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
	  ccount,
       vdom, avdom, lcount, opts),
     T).
       ((M', N', D', isa_length_trail M', W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
         slow_ema, restart_info_restart_done ccount, vdom, avdom, lcount, opts),
	  (empty_Q_wl T)) \<in> twl_st_heur_restart \<and>
	  isa_length_trail_pre M'} (SPEC (find_decomp_wl0 y))\<close>
     (is \<open>_ \<le> \<Down> ?A _\<close>)
    if
      \<open>0 < count_decided_st_heur S\<close> and
      \<open>0 < count_decided (get_trail_wl y)\<close>
  proof -
    have A:
      \<open>?A = {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
	  ccount,
       vdom, avdom, lcount, opts),
     T).
       ((M', N', D', length (get_trail_wl T), W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
         slow_ema, restart_info_restart_done ccount, vdom, avdom, lcount, opts),
	  (empty_Q_wl T)) \<in> twl_st_heur_restart \<and>
	  isa_length_trail_pre M'}\<close>
	  supply[[goals_limit=1]]
      apply (rule ; rule)
      subgoal for x
        apply clarify
	apply (frule twl_st_heur_restart_isa_length_trail_get_trail_wl)
        by (auto simp:  trail_pol_def empty_Q_wl_def
            isa_length_trail_def
          dest!: ann_lits_split_reasons_map_lit_of)
      subgoal for x
        apply clarify
	apply (frule twl_st_heur_restart_isa_length_trail_get_trail_wl)
        by (auto simp:  trail_pol_def empty_Q_wl_def
            isa_length_trail_def
          dest!: ann_lits_split_reasons_map_lit_of)
      done

    let ?\<A> = \<open>all_init_atms_st y\<close>
    have \<open>get_vmtf_heur S \<in> isa_vmtf ?\<A> (get_trail_wl y)\<close>and
      n_d: \<open>no_dup (get_trail_wl y)\<close>
      using Sy
      by (auto simp: twl_st_heur_restart_def)
    then obtain vm' where
      vm': \<open>(get_vmtf_heur S, vm') \<in> Id \<times>\<^sub>f distinct_atoms_rel ?\<A>\<close> and
      vm: \<open>vm' \<in> vmtf (all_init_atms_st y) (get_trail_wl y)\<close>
      unfolding isa_vmtf_def
      by force

    have find_decomp_w_ns_pre:
      \<open>find_decomp_w_ns_pre (all_init_atms_st y) ((get_trail_wl y, 0), vm')\<close>
      using that assms vm' vm unfolding find_decomp_w_ns_pre_def
      by (auto simp: twl_st_heur_restart_def
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
	by (auto simp: twl_st_heur_restart_def)
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
      apply (auto simp: upd_def find_decomp_wl0_def
        intro!: RETURN_SPEC_refine)
	apply (rule_tac x=bx in exI)
	using assms
	apply auto
	by (auto simp: twl_st_heur_restart_def out_learned_def
	    empty_Q_wl_def
	  intro: isa_vmtfI isa_length_trail_pre dest: no_dup_appendD)
  qed

  show ?thesis
    unfolding find_decomp_wl_st_int_alt_def
      cdcl_twl_local_restart_wl_spec0_alt_def
    apply refine_vcg
    subgoal
      using Sy by (auto simp: twl_st_heur_restart_count_decided_st_alt_def)
    subgoal
      unfolding empty_Q_def empty_Q_wl_def
      by refine_vcg
        (simp_all add: twl_st_heur_restart_isa_length_trail_get_trail_wl)
    subgoal
      using Sy .
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

lemma remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D:
  \<open>(remove_one_annot_true_clause_imp_wl_D_heur, remove_one_annot_true_clause_imp_wl_D) \<in>
    twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
  unfolding remove_one_annot_true_clause_imp_wl_D_def
    remove_one_annot_true_clause_imp_wl_D_heur_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    WHILEIT_refine[where R = \<open>nat_rel \<times>\<^sub>r twl_st_heur_restart\<close>]
    remove_one_annot_true_clause_one_imp_wl_D_heur_remove_one_annot_true_clause_one_imp_wl_D[THEN
      fref_to_Down_curry])
  subgoal by (auto simp: twl_st_heur_restart_isa_length_trail_get_trail_wl
    twl_st_heur_restart_count_decided_st_alt_def)
  subgoal for x y
    apply (rule order_trans)
    apply (rule get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail_CS[THEN fref_to_Down_curry,
        of \<open>get_trail_wl y\<close> 0 _ _ \<open>all_init_atms_st y\<close>])
    subgoal by (auto simp: get_pos_of_level_in_trail_pre_def
      twl_st_heur_restart_count_decided_st_alt_def)
    subgoal by (auto simp: twl_st_heur_restart_def)
    subgoal
      apply (subst get_pos_of_level_in_trail_decomp_iff)
      apply (solves \<open>auto simp: twl_st_heur_restart_def\<close>)
      apply (auto simp: get_pos_of_level_in_trail_def
        twl_st_heur_restart_count_decided_st_alt_def)
      done
    done
    subgoal by auto
    subgoal for x y k k' T T'
      apply (subst (asm)(11) surjective_pairing)
      apply (subst (asm)(9) surjective_pairing)
      unfolding remove_one_annot_true_clause_imp_wl_D_heur_inv_def
        prod_rel_iff
      apply (subst (10) surjective_pairing, subst prod.case)
      by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
  done


lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl2_D:
  \<open>(mark_to_delete_clauses_wl_D_heur, mark_to_delete_clauses_wl2_D) \<in>
     twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
proof -
  have mark_to_delete_clauses_wl_D_alt_def:
    \<open>mark_to_delete_clauses_wl2_D  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_pre S);
      S \<leftarrow> reorder_vdom_wl S;
      xs \<leftarrow> collect_valid_indices_wl S;
      l \<leftarrow> SPEC(\<lambda>_::nat. True);
      (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl2_D_inv S xs\<^esup>
        (\<lambda>(i, T, xs). i < length xs)
        (\<lambda>(i, T, xs). do {
          if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
          else do {
            ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	    ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
              (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
               \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2);
            ASSERT(i < length xs);
            if can_del
            then
              RETURN (i, mark_garbage_wl (xs!i) T, delete_index_and_swap xs i)
            else
              RETURN (i+1, T, xs)
          }
        })
        (l, S, xs);
      RETURN S
    })\<close>
    unfolding mark_to_delete_clauses_wl2_D_def reorder_vdom_wl_def
    by (auto intro!: ext)

  have mark_to_delete_clauses_wl_D_heur_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
      S \<leftarrow> sort_vdom_heur S;
      _ \<leftarrow> RETURN (get_avdom S);
      l \<leftarrow> RETURN (number_clss_to_keep S);
      (i, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
        (\<lambda>(i, S). i < length (get_avdom S))
        (\<lambda>(i, T). do {
          ASSERT(i < length (get_avdom T));
          ASSERT(access_vdom_at_pre T i);
          let C = get_avdom T ! i;
          ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
          if(\<not>clause_not_marked_to_delete_heur T C) then RETURN (i, delete_index_vdom_heur i T)
          else do {
            ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
            let L = access_lit_in_clauses_heur T C 0;
            D \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur T) L;
            ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
            ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
            ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
                arena_is_valid_clause_idx (get_clauses_wl_heur T) C); 
            ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
	        marked_as_used_pre (get_clauses_wl_heur T) C);
            let can_del = (D \<noteq> Some C) \<and> arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur T) C = LEARNED \<and>
               arena_length (get_clauses_wl_heur T) C \<noteq> two_uint64_nat \<and>
	       \<not>marked_as_used (get_clauses_wl_heur T) C;
            if can_del
            then do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
            else do {
  	      ASSERT(arena_act_pre (get_clauses_wl_heur T) C);
              RETURN (i+1, mark_unused_st_heur C T)
	    }
          }
        })
        (l, S);
      T \<leftarrow> mark_clauses_as_unused_wl_D_heur i T;
      incr_restart_stat T
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_heur_def
    by (auto intro!: ext)

  have [refine0]: \<open>RETURN (get_avdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_avdom x} (collect_valid_indices_wl y)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y
  proof -
    show ?thesis by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed
  have init_rel[refine0]: \<open>(x, y) \<in> twl_st_heur_restart \<Longrightarrow>
       (l, la) \<in> nat_rel \<Longrightarrow>
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur_restart \<and> get_avdom S = get_avdom x}\<close>
    for x y l la
    by auto

  have get_the_propagation_reason:
    \<open>get_the_propagation_reason_pol (get_trail_wl_heur x2b)
       (arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0))
        \<le> \<Down> {(D, b). b \<longleftrightarrow> ((D \<noteq> Some (get_avdom x2b ! x1b)) \<and>
               arena_lbd (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) = LEARNED) \<and>
               arena_length (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) \<noteq> two_uint32_nat \<and>
	       \<not>marked_as_used (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b)}
       (SPEC
           (\<lambda>b. b \<longrightarrow>
                Propagated (get_clauses_wl x1a \<propto> (x2a ! x1) ! 0) (x2a ! x1)
                \<notin> set (get_trail_wl x1a) \<and>
                \<not> irred (get_clauses_wl x1a) (x2a ! x1) \<and>
                length (get_clauses_wl x1a \<propto> (x2a ! x1)) \<noteq> 2 ))\<close>
  if
    \<open>(x, y) \<in> twl_st_heur_restart\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
    \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    xa_x': \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close> and
    \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
    \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
    \<open>x1b < length (get_avdom x2b)\<close> and
    \<open>access_vdom_at_pre x2b x1b\<close> and
    \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
    \<open>\<not> \<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
    \<open>\<not> x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close> and
    \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
    \<open>access_lit_in_clauses_heur_pre ((x2b, get_avdom x2b ! x1b), 0)\<close> and
    st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
    L: \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
    for x y S Sa xs' xs l la xa x' x1 x2 x1a x2a x1' x2' x3 x1b ys x2b
  proof -
    have L: \<open>arena_lit (get_clauses_wl_heur x2b) (x2a ! x1) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      using L that by (auto simp: twl_st_heur_restart st arena_lifting dest: \<L>\<^sub>a\<^sub>l\<^sub>l_init_all)

    show ?thesis
      apply (rule order.trans)
      apply (rule get_the_propagation_reason_pol[THEN fref_to_Down_curry,
        of \<open>all_init_atms_st x1a\<close> \<open>get_trail_wl x1a\<close>
	  \<open>arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0)\<close>])
      subgoal
        using xa_x' L by (auto simp add: twl_st_heur_restart_def st)
      subgoal
        using xa_x' by (auto simp add: twl_st_heur_restart_def st)
      using that unfolding get_the_propagation_reason_def apply -
      by (auto simp: twl_st_heur_restart lits_of_def get_the_propagation_reason_def
          conc_fun_RES
        dest: twl_st_heur_restart_same_annotD imageI[of _ _ lit_of])
  qed
  have \<open>((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom, lcount),
           S')
          \<in> twl_st_heur_restart \<longleftrightarrow>
    ((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom', lcount),
           S')
          \<in> twl_st_heur_restart\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema
      ccount vdom lcount S' avdom' avdom
    using that unfolding twl_st_heur_restart_def
    by auto
  then have mark_to_delete_clauses_wl_D_heur_pre_vdom':
    \<open>mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, vdom, avdom, lcount) \<longleftrightarrow>
      mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
        fast_ema, slow_ema, ccount, vdom, avdom', lcount)\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount vdom lcount
    using that
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def
    by metis
  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart \<and> V = T \<and>
         (mark_to_delete_clauses_wl_D_pre T \<longrightarrow> mark_to_delete_clauses_wl_D_pre V) \<and>
         (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U)}
         (reorder_vdom_wl T)\<close>
    if \<open>(S, T) \<in> twl_st_heur_restart\<close> for S T
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply (refine_rcg ASSERT_leI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_def
         intro: mark_to_delete_clauses_wl_D_heur_pre_vdom'[THEN iffD1]
         dest: mset_eq_setD)
    done
  have already_deleted:
    \<open>((x1b, delete_index_vdom_heur x1b x2b), x1, x1a,
       delete_index_and_swap x2a x1)
      \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
      \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl2_D_inv Sa xs x'\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      \<open>x1b < length (get_avdom x2b)\<close> and
      \<open>access_vdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
      \<open>\<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
      \<open>x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa
  proof -
    show ?thesis
      using xx unfolding st
      by (auto simp: twl_st_heur_restart_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If
          intro: valid_arena_extra_information_mark_to_delete'
          dest!: in_set_butlastD in_vdom_m_fmdropD
          elim!: in_set_upd_cases)
  qed

  have init:
    \<open>(u, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S} \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart \<Longrightarrow>
    mark_to_delete_clauses_wl2_D_inv Sa xs (la, Sa, xs) \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
       {(Sa, (T, xs)). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close>
       for x y S Sa xs l la u
    by auto
  have [refine0]: \<open>mark_clauses_as_unused_wl_D_heur i T
    \<le> SPEC
       (\<lambda>x. incr_restart_stat x \<le> SPEC (\<lambda>c. (c, S) \<in> twl_st_heur_restart))\<close>
    if \<open>(T, S) \<in> twl_st_heur_restart\<close> for S T i
    by (rule order_trans, rule mark_clauses_as_unused_wl_D_heur[OF that, of i])
      (auto simp: conc_fun_RES incr_restart_stat_def
        twl_st_heur_restart_def)
  show ?thesis
    supply sort_vdom_heur_def[simp]
    unfolding mark_to_delete_clauses_wl_D_heur_alt_def mark_to_delete_clauses_wl_D_alt_def
      access_lit_in_clauses_heur_def Let_def
    apply (intro frefI nres_relI)
    apply (refine_vcg sort_vdom_heur_reorder_vdom_wl[THEN fref_to_Down])
    subgoal
      unfolding mark_to_delete_clauses_wl_D_heur_pre_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule init; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_vdom_at_pre_def)
    subgoal for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d
      unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
        prod.simps
      by (rule exI[of _ \<open>get_clauses_wl x2a\<close>], rule exI[of _ \<open>set (get_vdom x2d)\<close>])
         (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal
      by (auto simp: twl_st_heur_restart)
    subgoal
      by (rule already_deleted)
    subgoal for x y _ _ _ _ _ xs l la xa x' x1 x2 x1a x2a
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_avdom x2a ! x1a\<close>], simp, rule exI[of _ \<open>get_clauses_wl x1\<close>])
        (auto simp: twl_st_heur_restart_def)
    apply (rule get_the_propagation_reason; assumption)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena
	  twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart arena_dom_status_iff
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal unfolding marked_as_used_pre_def by fast
    subgoal
      by (auto simp: twl_st_heur_restart)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_garbage_heur_wl)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def arena_act_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_unused_st_heur)
    subgoal
      by (auto simp:)
    done
qed

lemma restart_prog_wl_D_heur_restart_prog_wl_D:
  \<open>(cdcl_twl_full_restart_wl_D_GC_heur_prog, cdcl_twl_full_restart_wl_D_GC_prog) \<in>
    [\<lambda>y.  get_conflict_wl y = None]\<^sub>f twl_st_heur_restart \<rightarrow> \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def
    cdcl_twl_full_restart_wl_D_GC_prog_def
  apply (intro frefI nres_relI)
  apply (refine_rcg cdcl_twl_local_restart_wl_spec0
    remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D[THEN fref_to_Down]
    mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl2_D[THEN fref_to_Down])
  subgoal by fast
  subgoal by fast
  oops


definition iterate_over_VMTF where
  \<open>iterate_over_VMTF = (\<lambda>(vm, n) I f x. do {
    (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). n < length vm \<and> I x\<^esup>
      (\<lambda>(n, _). get_next (vm ! n) \<noteq> None)
      (\<lambda>(n, x). do {
        let A = the (get_next (vm ! n));
        x \<leftarrow> f A x;
        RETURN (A, x)
      })
      (n, x);
    RETURN x
  })\<close>

definition iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l where
  \<open>iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l = (\<lambda>\<A>\<^sub>0 I f x. do {
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset \<A>\<^sub>0);
    (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, x). I x\<^esup>
      (\<lambda>(\<B>, _). \<B> \<noteq> {#})
      (\<lambda>(\<B>, x). do {
        ASSERT(\<B> \<noteq> {#});
        A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
        x \<leftarrow> f A x;
        RETURN (remove1_mset A \<B>, x)
      })
      (\<A>, x);
    RETURN x
  })\<close>

lemma
  fixes x :: 'a
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
  shows \<open>iterate_over_VMTF (ns, fast_As) I f x \<le> \<Down> Id (iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> I f x)\<close>
proof -
thm wf_vmtf_get_next
  obtain xs' ys' where
    \<open>vmtf_ns (ys' @ xs') m ns\<close>
    \<open>fst_As = hd (ys' @ xs')\<close>
    \<open>lst_As = last (ys' @ xs')\<close> and
    \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close>
    using vmtf unfolding vmtf_def
    by blast
  define is_lasts where
    \<open>is_lasts \<A> n \<longleftrightarrow> \<A> = mset (drop (length (ys' @ xs') - size \<A>) (ys' @ xs')) \<and>
         (ys' @ xs') ! (length (ys' @ xs') - size \<A>) = n\<close> for \<A> n
  have iterate_over_VMTF_alt_def:
    \<open>iterate_over_VMTF = (\<lambda>(vm, n) I f x. do {
      let _= \<A>;
      (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). n < length vm \<and> I x\<^esup>
        (\<lambda>(n, _). get_next (vm ! n) \<noteq> None)
        (\<lambda>(n, x). do {
          let A = the (get_next (vm ! n));
          x \<leftarrow> f A x;
          RETURN (A, x)
        })
        (n, x);
      RETURN x
    })\<close>
    unfolding iterate_over_VMTF_def
    by auto
  show ?thesis
    unfolding iterate_over_VMTF_alt_def iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    apply (refine_vcg WHILEIT_refine[where R = \<open>{((n :: nat, x::'a), (\<A>' :: nat multiset, y)). is_lasts \<A> n \<and> x = y}\<close>])
    subgoal by auto
    subgoal apply (auto simp: is_lasts_def)
  oops

end
