theory IsaSAT_Restart_Heuristics
  imports Watched_Literals_Watch_List_Domain_Restart IsaSAT_Setup IsaSAT_VMTF
    IsaSAT_Inner_Propagation (* TODO remove dependency *)
begin

locale isasat_restart_bounded =
  twl_restart + isasat_input_bounded

sublocale isasat_restart_bounded \<subseteq> isasat_restart_ops
 .

instantiation prod :: (ord, ord) ord
begin
  definition less_prod where
    \<open>less_prod = (\<lambda>(a, b) (c,d). a < c \<or> (a = c \<and> b < d)) \<close>

  definition less_eq_prod where
    \<open>less_eq_prod = (\<lambda>(a, b) (c,d). (a < c) \<or> (a = c \<and> b \<le> d)) \<close>

instance
  by standard
end

instance prod :: (preorder, preorder) preorder
  apply standard
  subgoal for x y
    by (auto simp: less_prod_def less_eq_prod_def less_le_not_le)
  subgoal for x
    by (auto simp: less_prod_def less_eq_prod_def less_le_not_le)
  subgoal
    using less_trans order_trans by (fastforce simp: less_prod_def less_eq_prod_def intro: less_trans)
  done

 instance prod :: (order, order) order
  apply standard
  subgoal for x y
    by (auto simp: less_prod_def less_eq_prod_def)
  done

instance prod :: (linorder, linorder) linorder
  by standard
   (auto simp: less_prod_def less_eq_prod_def)


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

lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

global_interpretation twl_restart_ops id
  by unfold_locales

sublocale isasat_input_ops \<subseteq> isasat_restart_ops id
  .

context isasat_input_bounded_nempty
begin

text \<open>
  We first fix the function that proves termination. We don't take the ``smallest'' function
  possible (other possibilites that are growing slower include \<^term>\<open>\<lambda>(n::nat). n >> 50\<close>).
  Remark that this scheme is not compatible with Luby (TODO: use Luby restart scheme every once
  in a while like CryptoMinisat?)
\<close>

sublocale isasat_restart_bounded id
  by standard (rule unbounded_id)


lemma get_slow_ema_heur_alt_def:
   \<open>RETURN o get_slow_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN sema)\<close>
  by auto

sepref_thm get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

concrete_definition (in -) get_slow_ema_heur_fast_code
   uses isasat_input_bounded_nempty.get_slow_ema_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_slow_ema_heur_fast_code_def

lemmas get_slow_ema_heur_fast_code_hnr[sepref_fr_rules] =
   get_slow_ema_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm get_slow_ema_heur_slow_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) get_slow_ema_heur_slow_code
   uses isasat_input_bounded_nempty.get_slow_ema_heur_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_slow_ema_heur_slow_code_def

lemmas get_slow_ema_heur_slow_code_hnr[sepref_fr_rules] =
   get_slow_ema_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


lemma get_fast_ema_heur_alt_def:
   \<open>RETURN o get_fast_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, lcount). RETURN fema)\<close>
  by auto

sepref_thm get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

concrete_definition (in -) get_fast_ema_heur_fast_code
   uses isasat_input_bounded_nempty.get_fast_ema_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_fast_ema_heur_fast_code_def

lemmas get_fast_ema_heur_fast_code_hnr[sepref_fr_rules] =
   get_fast_ema_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm get_fast_ema_heur_slow_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) get_fast_ema_heur_slow_code
   uses isasat_input_bounded_nempty.get_fast_ema_heur_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_fast_ema_heur_slow_code_def

lemmas get_fast_ema_heur_slow_code_hnr[sepref_fr_rules] =
   get_fast_ema_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

fun (in -) get_conflict_count_since_last_restart_heur :: \<open>twl_st_wl_heur \<Rightarrow> uint64\<close> where
  \<open>get_conflict_count_since_last_restart_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, _, (ccount, _), _)
      = ccount\<close>

lemma (in -) get_counflict_count_heur_alt_def:
   \<open>RETURN o get_conflict_count_since_last_restart_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN ccount)\<close>
  by auto

sepref_thm get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def
  by sepref

concrete_definition (in -) get_conflict_count_since_last_restart_heur_fast_code
   uses isasat_input_bounded_nempty.get_conflict_count_since_last_restart_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_count_since_last_restart_heur_fast_code_def

lemmas get_conflict_count_since_last_restart_heur_code_hnr[sepref_fr_rules] =
   get_conflict_count_since_last_restart_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm get_conflict_count_since_last_restart_heur_slow_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) get_conflict_count_since_last_restart_heur_slow_code
   uses isasat_input_bounded_nempty.get_conflict_count_since_last_restart_heur_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_count_since_last_restart_heur_slow_code_def

lemmas get_conflict_count_since_last_restart_heur_slow_code_hnr[sepref_fr_rules] =
   get_conflict_count_since_last_restart_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma get_learned_count_alt_def:
   \<open>RETURN o get_learned_count = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). RETURN lcount)\<close>
  by auto

sepref_thm get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def
  by sepref

concrete_definition (in -) get_learned_count_fast_code
   uses isasat_input_bounded_nempty.get_learned_count_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_learned_count_fast_code_def

lemmas get_learned_count_code_hnr[sepref_fr_rules] =
   get_learned_count_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm get_learned_count_slow_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) get_learned_count_slow_code
   uses isasat_input_bounded_nempty.get_learned_count_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_learned_count_slow_code_def

lemmas get_learned_count_slow_code_hnr[sepref_fr_rules] =
   get_learned_count_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition (in -) find_local_restart_target_level_int_inv where
  \<open>find_local_restart_target_level_int_inv ns cs =
     (\<lambda>(brk, i). i \<le> length cs \<and> length cs < uint32_max)\<close>

definition (in isasat_input_ops) find_local_restart_target_level_int
   :: \<open>trail_pol \<Rightarrow> vmtf_remove_int \<Rightarrow> nat nres\<close>
where
  \<open>find_local_restart_target_level_int =
     (\<lambda>(M, xs, lvls, reasons, k, cs) ((ns, m, fst_As, lst_As, next_search), to_remove). do {
     (brk, i) \<leftarrow> WHILE\<^sub>T\<^bsup>find_local_restart_target_level_int_inv ns cs\<^esup>
        (\<lambda>(brk, i). \<not>brk \<and> i < length_u cs)
        (\<lambda>(brk, i). do {
           ASSERT(i < length cs);
           let t = (cs  ! i);
           ASSERT(t < length M);
           ASSERT(M ! t \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
           let L = atm_of (M ! t);
           ASSERT(L < length ns);
           let brk = stamp (ns ! L) < m;
           RETURN (brk, if brk then i else i+one_uint32_nat)
         })
        (False, zero_uint32_nat);
    RETURN i
   })\<close>

sepref_thm find_local_restart_target_level_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

concrete_definition (in -) find_local_restart_target_level_code
   uses isasat_input_bounded_nempty.find_local_restart_target_level_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) find_local_restart_target_level_code_def

lemmas find_local_restart_target_level_code_def_hnr (*[sepref_fr_rules]*) =
   find_local_restart_target_level_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

concrete_definition (in -) find_local_restart_target_level_fast_code
   uses isasat_input_bounded_nempty.find_local_restart_target_level_fast_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) find_local_restart_target_level_fast_code_def

lemmas find_local_restart_target_level_fast_code_def_hnr (*[sepref_fr_rules]*) =
   find_local_restart_target_level_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition (in isasat_input_ops) find_local_restart_target_level where
  \<open>find_local_restart_target_level M _ = SPEC(\<lambda>i. i \<le> count_decided M)\<close>

lemma find_local_restart_target_level_alt_def:
  \<open>find_local_restart_target_level M vm = do {
      (b, i) \<leftarrow> SPEC(\<lambda>(b::bool, i). i \<le> count_decided M);
       RETURN i
    }\<close>
  unfolding find_local_restart_target_level_def by (auto simp: RES_RETURN_RES2 uncurry_def)


lemma find_local_restart_target_level_int_find_local_restart_target_level:
   \<open>(uncurry find_local_restart_target_level_int, uncurry find_local_restart_target_level) \<in>
     [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>f trail_pol \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
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
    subgoal by (auto simp: trail_pol_alt_def rev_map lits_of_def rev_nth
          intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l)
    subgoal by (auto simp: vmtf_def atms_of_def)
    subgoal by (auto simp: find_local_restart_target_level_int_inv_def)
    subgoal by (auto simp: trail_pol_alt_def control_stack_length_count_dec
          find_local_restart_target_level_int_inv_def)
    subgoal by auto
    done
  done

lemma find_local_restart_target_level_hnr[sepref_fr_rules]:
  \<open>(uncurry find_local_restart_target_level_code, uncurry find_local_restart_target_level)
    \<in> [\<lambda>(b, a). a \<in> vmtf b]\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using find_local_restart_target_level_code_def_hnr[FCOMP
       find_local_restart_target_level_int_find_local_restart_target_level] .

lemma find_local_restart_target_level_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry find_local_restart_target_level_fast_code, uncurry find_local_restart_target_level)
    \<in> [\<lambda>(b, a). a \<in> vmtf b]\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using find_local_restart_target_level_fast_code_def_hnr[FCOMP
       find_local_restart_target_level_int_find_local_restart_target_level] .

definition (in isasat_input_ops) find_local_restart_target_level_st :: \<open>twl_st_wl_heur \<Rightarrow> nat nres\<close> where
  \<open>find_local_restart_target_level_st S = do {
     ASSERT(get_vmtf_heur S \<in>  vmtf (get_trail_wl_heur S));
     find_local_restart_target_level (get_trail_wl_heur S) (get_vmtf_heur S)
  }\<close>

lemma find_local_restart_target_level_st_alt_def:
  \<open>find_local_restart_target_level_st = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats). do {
      ASSERT(vm \<in>  vmtf M);
      find_local_restart_target_level M vm})\<close>
  apply (intro ext)
  apply (case_tac x)
  by (auto simp: find_local_restart_target_level_st_def)


sepref_thm find_local_restart_target_level_st_code
  is \<open>PR_CONST find_local_restart_target_level_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) find_local_restart_target_level_st_code
   uses isasat_input_bounded_nempty.find_local_restart_target_level_st_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) find_local_restart_target_level_st_code_def

sepref_register find_local_restart_target_level_st
lemmas find_local_restart_target_level_st_hnr [sepref_fr_rules] =
   find_local_restart_target_level_st_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm find_local_restart_target_level_st_fast_code
  is \<open>PR_CONST find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) find_local_restart_target_level_st_fast_code
   uses isasat_input_bounded_nempty.find_local_restart_target_level_st_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) find_local_restart_target_level_st_fast_code_def
lemmas find_local_restart_target_level_st_fast_hnr [sepref_fr_rules] =
   find_local_restart_target_level_st_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) empty_Q :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>empty_Q = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount). do{
    let j = length_u M;
    RETURN (M, N, D, j, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
       restart_info_restart_done ccount, vdom, lcount)
  })\<close>

definition (in isasat_input_ops) incr_restart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_restart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
       res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_restart stats,
       ema_reinit fast_ema, ema_reinit slow_ema,
       restart_info_restart_done res_info, vdom, avdom, lcount)
  })\<close>

sepref_thm incr_restart_stat_slow_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) incr_restart_stat_slow_code
   uses isasat_input_bounded_nempty.incr_restart_stat_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) incr_restart_stat_slow_code_def

sepref_register incr_restart_stat
lemmas incr_restart_stat_slow_code_hnr [sepref_fr_rules] =
   incr_restart_stat_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) incr_restart_stat_fast_code
   uses isasat_input_bounded_nempty.incr_restart_stat_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) incr_restart_stat_fast_code_def
lemmas incr_restart_stat_fast_code_hnr [sepref_fr_rules] =
   incr_restart_stat_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) incr_lrestart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_lrestart stats,
       ema_reinit fast_ema, ema_reinit slow_ema,
       restart_info_restart_done res_info,
       vdom, avdom, lcount)
  })\<close>

sepref_thm incr_lrestart_stat_slow_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) incr_lrestart_stat_slow_code
   uses isasat_input_bounded_nempty.incr_lrestart_stat_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) incr_lrestart_stat_slow_code_def

sepref_register incr_lrestart_stat
lemmas incr_lrestart_stat_slow_code_hnr [sepref_fr_rules] =
   incr_lrestart_stat_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) incr_lrestart_stat_fast_code
   uses isasat_input_bounded_nempty.incr_lrestart_stat_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) incr_lrestart_stat_fast_code_def
lemmas incr_lrestart_stat_fast_code_hnr [sepref_fr_rules] =
   incr_lrestart_stat_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition (in isasat_input_ops) restart_abs_wl_heur_pre  :: \<open>twl_st_wl_heur \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_heur_pre S brk  \<longleftrightarrow> (\<exists>T. (S, T) \<in> twl_st_heur \<and> restart_abs_wl_D_pre T brk)\<close>

text \<open>\<^term>\<open>find_decomp_wl_st_int\<close> is the wrong function here, because unlike in the backtrack case,
  we also have to update the queue of literals to update. This is done in the function \<^term>\<open>empty_Q\<close>.
\<close>


definition (in isasat_input_ops) cdcl_twl_local_restart_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_local_restart_wl_D_heur = (\<lambda>S. do {
      ASSERT(restart_abs_wl_heur_pre S False);
      lvl \<leftarrow> find_local_restart_target_level_st S;
      if lvl = count_decided_st S
      then RETURN S
      else do {
        S \<leftarrow> empty_Q S;
        ASSERT(find_decomp_w_ns_pre ((get_trail_wl_heur S, lvl), get_vmtf_heur S));
        S \<leftarrow> find_decomp_wl_st_int lvl S;
        S \<leftarrow> empty_Q S;
        incr_lrestart_stat S
      }
   })\<close>


sepref_thm empty_Q_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) empty_Q_code
   uses isasat_input_bounded_nempty.empty_Q_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) empty_Q_code_def

lemmas empty_Q_hnr [sepref_fr_rules] =
   empty_Q_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(*
sepref_thm empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold apply (auto simp: )[]
  by sepref

concrete_definition (in -) empty_Q_fast_code
   uses isasat_input_bounded_nempty.empty_Q_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) empty_Q_fast_code_def

lemmas empty_Q_fast_hnr [sepref_fr_rules] =
   empty_Q_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
*)

sepref_register cdcl_twl_local_restart_wl_D_heur
  empty_Q find_decomp_wl_st_int

sepref_thm cdcl_twl_local_restart_wl_D_heur_code
  is \<open>PR_CONST cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_local_restart_wl_D_heur_code
   uses isasat_input_bounded_nempty.cdcl_twl_local_restart_wl_D_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

lemmas cdcl_twl_local_restart_wl_D_heur_hnr [sepref_fr_rules] =
   cdcl_twl_local_restart_wl_D_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(*
sepref_thm cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>PR_CONST cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_local_restart_wl_D_heur_fast_code
   uses isasat_input_bounded_nempty.cdcl_twl_local_restart_wl_D_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

lemmas cdcl_twl_local_restart_wl_D_heur_fast_hnr [sepref_fr_rules] =
   cdcl_twl_local_restart_wl_D_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
*)

named_theorems (in isasat_input_ops) twl_st_heur

lemma (in isasat_input_ops) [twl_st_heur]:
  assumes \<open>(S, T) \<in> twl_st_heur\<close>
  shows \<open>get_trail_wl T = get_trail_wl_heur S\<close>
  using assms by (cases S; cases T; auto simp: twl_st_heur_def; fail)


lemma restart_abs_wl_D_pre_find_decomp_w_ns_pre:
  assumes
    pre: \<open>restart_abs_wl_D_pre T False\<close> and
    ST: \<open>(S, T) \<in> twl_st_heur\<close> and
    \<open>lvl < count_decided (get_trail_wl_heur S)\<close>
  shows \<open>find_decomp_w_ns_pre ((get_trail_wl_heur S, lvl), get_vmtf_heur S)\<close>
proof -
  obtain x xa where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' T\<close> and
    Tx: \<open>(T, x) \<in> state_wl_l None\<close> and
    \<open>correct_watching T\<close> and
    xxa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs xa\<close> and
    \<open>twl_list_invs x\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>twl_stgy_invs xa\<close> and
    \<open>get_conflict xa = None\<close>
    using pre unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by blast
  have lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[OF Tx xxa struct] lits by blast
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl_heur S)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail[OF Tx struct xxa lits] ST
    by (auto simp add: twl_st_heur)
  moreover have \<open> get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S)\<close>
    using ST by (auto simp add: twl_st_heur_def)
  moreover have \<open>no_dup (get_trail_wl_heur S)\<close>
    using struct ST Tx xxa unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: twl_st twl_st_l twl_st_heur)
  ultimately show ?thesis
    using assms unfolding find_decomp_w_ns_pre_def prod.case
    by blast
qed

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
  have H: \<open>g = g' \<Longrightarrow> (f \<bind> g) = (f \<bind> g')\<close> for f :: \<open>_ nres\<close> and g g' by auto
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_D_spec_def prod.case RES_RETURN_RES2 If_Res
    by refine_vcg
      (auto simp: If_Res RES_RETURN_RES2 RES_RES_RETURN_RES uncurry_def
        image_iff split:if_splits)
qed

lemma count_decided_st_alt_def':
  \<open>count_decided_st S = count_decided (get_trail_wl_heur S)\<close>
  by (cases S) (auto simp: count_decided_st_def)

lemma cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec:
  \<open>(cdcl_twl_local_restart_wl_D_heur, cdcl_twl_local_restart_wl_D_spec) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have [dest]: \<open>av = None\<close> \<open>out_learned a av am \<Longrightarrow> out_learned x1 av am\<close>
    if \<open>restart_abs_wl_D_pre (a, au, av, aw, ax, ay, bd) False\<close>
    for a au av aw ax ay bd x1 am
    using that
    unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by (auto simp: twl_st_l_def state_wl_l_def out_learned_def)
  have [dest]: \<open>find_decomp_w_ns_pre ((a, lvl), (ae, af, ag, ah, b), ba) \<Longrightarrow>
       (Decided K # x1, M2) \<in> set (get_all_ann_decomposition a) \<Longrightarrow>
        no_dup x1\<close>
    for a lvl ae ab ag ah b ba x1 M2 af K
    unfolding find_decomp_w_ns_pre_def prod.case
    by (auto dest!: distinct_get_all_ann_decomposition_no_dup no_dup_appendD1)
  have [refine0]:
    \<open>SPEC (\<lambda>i. i \<le> count_decided a) \<le> \<Down> {(i, b). b = (i = count_decided a) \<and>
          i \<le> count_decided a} (SPEC (\<lambda>_. True))\<close> for a
    by (auto intro: RES_refine)
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_D_heur_def count_decided_st_alt_def'
      find_decomp_wl_st_int_def find_local_restart_target_level_def incr_lrestart_stat_def
      find_decomp_w_ns_def empty_Q_def find_local_restart_target_level_st_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_local_restart_wl_D_spec_int)
    unfolding bind_to_let_conv Let_def RES_RETURN_RES2
    apply (refine_vcg)
    subgoal unfolding restart_abs_wl_heur_pre_def by blast
    subgoal by (force simp: twl_st_heur_def)
    subgoal by auto
    subgoal
      by (force dest: restart_abs_wl_D_pre_find_decomp_w_ns_pre)
    subgoal for a aa ab ac b ad ae af ag ah ai ba bb aj ak al am
       an ao ap aq ar bc as at au av bd aw ax ay az be
       bf bg bh bi bj bk bl bm bn bo bp bq br bs lvl i
       x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
       x1f x2f x1g x2g x1h x2h x1i x2i S x1j x2j x1k
       x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w
       x2w x1x x2x x1y x2y
      unfolding RETURN_def RES_RES2_RETURN_RES RES_RES13_RETURN_RES
      apply (rule RES_refine, rule bexI[of _ \<open>(get_trail_wl_heur S, bn, bo, bp, bq, {#}, bs)\<close>];
         ((subst uncurry_def image_iff)+)?; (rule bexI[of _ \<open>(get_trail_wl_heur S, {#})\<close>])?)
      subgoal
         by (clarsimp simp add: twl_st_heur_def)
           (auto simp: twl_st_heur_def)[]
      by ((fastforce simp: twl_st_heur_def))+
        \<comment> \<open>This proof is very slow: a direct call to auto takes around 60s. This is faster,
          but not that much actually.\<close>
    done
qed

definition(in isasat_input_ops)  remove_all_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> nat watcher list \<Rightarrow> nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_inv S xs = (\<lambda>(i, T).
       \<exists>S' T'. (S, S') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
         remove_all_annot_true_clause_imp_wl_D_inv S' (map fst xs) (i, T'))
     \<close>

definition (in isasat_input_ops) remove_all_annot_true_clause_one_imp_heur
  :: \<open>nat \<times> arena \<Rightarrow> arena nres\<close>
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, N). do {
      if arena_status N C = DELETED
         then RETURN (extra_information_mark_to_delete N C)
      else do {
        RETURN N
      }
  })\<close>

definition(in isasat_input_ops) remove_all_annot_true_clause_imp_wl_D_heur_pre where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur \<and> remove_all_annot_true_clause_imp_wl_D_pre L S')\<close>


(* TODO: unfold Let when generating code! *)
definition(in isasat_input_ops) remove_all_annot_true_clause_imp_wl_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl_D_heur = (\<lambda>L (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats). do {
    ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_pre L (M, N0, D, Q, W, vm, \<phi>, clvls,
       cach, lbd, outl, stats));
    let xs = W!(nat_of_lit L);
    (_, N) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N).
        remove_all_annot_true_clause_imp_wl_D_heur_inv
           (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) xs
           (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats)\<^esup>
      (\<lambda>(i, N). i < length xs)
      (\<lambda>(i, N). do {
        ASSERT(i < length xs);
        if clause_not_marked_to_delete_heur (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) i
        then do {
          N \<leftarrow> remove_all_annot_true_clause_one_imp_heur (fst (xs!i), N);
          ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_inv
             (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) xs
             (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats));
          RETURN (i+1, N)
        }
        else
          RETURN (i+1, N)
      })
      (0, N0);
    RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats)
  })\<close>


definition (in -) minimum_number_between_restarts :: \<open>uint64\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

lemma (in -) minimum_number_between_restarts[sepref_fr_rules]:
 \<open>(uncurry0 (return minimum_number_between_restarts), uncurry0 (RETURN minimum_number_between_restarts))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition (in -) five_uint64 :: \<open>uint64\<close> where
  \<open>five_uint64 = 5\<close>

lemma (in -) five_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return five_uint64), uncurry0 (RETURN five_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition (in -) two_uint64 :: \<open>uint64\<close> where
  \<open>two_uint64 = 2\<close>

lemma (in -) two_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return two_uint64), uncurry0 (RETURN two_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto


definition (in -) upper_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>upper_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    lcount < 3000 + 500 * nat_of_uint64 restarts)\<close>

sepref_register upper_restart_bound_not_reached
sepref_thm upper_restart_bound_not_reached_impl
  is \<open>PR_CONST (RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) upper_restart_bound_not_reached_impl
   uses isasat_input_bounded_nempty.upper_restart_bound_not_reached_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) upper_restart_bound_not_reached_impl_def

lemmas upper_restart_bound_not_reached_impl[sepref_fr_rules] =
   upper_restart_bound_not_reached_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_thm upper_restart_bound_not_reached_fast_impl
  is \<open>PR_CONST (RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) upper_restart_bound_not_reached_fast_impl
   uses isasat_input_bounded_nempty.upper_restart_bound_not_reached_fast_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) upper_restart_bound_not_reached_fast_impl_def

lemmas upper_restart_bound_not_reached_fast_impl[sepref_fr_rules] =
   upper_restart_bound_not_reached_fast_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]


definition (in -) lower_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>lower_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
        (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    opts_reduce opts \<or> opts_restart opts \<and> lcount < 2000 + 300 * nat_of_uint64 restarts)\<close>

sepref_register lower_restart_bound_not_reached
sepref_thm lower_restart_bound_not_reached_impl
  is \<open>PR_CONST (RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) lower_restart_bound_not_reached_impl
   uses isasat_input_bounded_nempty.lower_restart_bound_not_reached_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lower_restart_bound_not_reached_impl_def

lemmas lower_restart_bound_not_reached_impl[sepref_fr_rules] =
   lower_restart_bound_not_reached_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_thm lower_restart_bound_not_reached_fast_impl
  is \<open>PR_CONST (RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) lower_restart_bound_not_reached_fast_impl
   uses isasat_input_bounded_nempty.lower_restart_bound_not_reached_fast_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lower_restart_bound_not_reached_fast_impl_def

lemmas lower_restart_bound_not_reached_fast_impl[sepref_fr_rules] =
   lower_restart_bound_not_reached_fast_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

end

definition (in -) clause_score_extract :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>clause_score_extract arena xs C = (
     let C = (xs ! C) in
     if arena_status arena C = DELETED then (uint32_max, uint32_max) \<comment> \<open>deleted elements are the
        smallest possible\<close>
     else
       let lbd = get_clause_LBD arena C in
       let act = arena_act arena C in
       (lbd, act)
  )\<close>
sepref_register clause_score_extract

lemma uint32_max_uint32_nat_assn:
  \<open>(uncurry0 (return 4294967295), uncurry0 (RETURN uint32_max)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_max_def uint32_max_def uint32_nat_rel_def br_def)

definition (in -)valid_sort_clause_score_pre_at where
  \<open>valid_sort_clause_score_pre_at arena vdom i \<longleftrightarrow>
    arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)))
          \<and> i < length vdom\<close>

sepref_definition (in -) clause_score_extract_code
  is \<open>uncurry2 (RETURN ooo clause_score_extract)\<close>
  :: \<open>[uncurry2 valid_sort_clause_score_pre_at]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply uint32_max_uint32_nat_assn[sepref_fr_rules]
  unfolding clause_score_extract_def insert_sort_inner_def valid_sort_clause_score_pre_at_def
  by sepref

declare clause_score_extract_code.refine[sepref_fr_rules]

definition (in -)valid_sort_clause_score_pre where
  \<open>valid_sort_clause_score_pre arena vdom \<longleftrightarrow>
    (\<forall>C \<in> set vdom. arena_is_valid_clause_vdom arena C \<and>
        (arena_status arena C \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena C \<and> arena_act_pre arena C)))\<close>

definition (in -)insort_inner_clauses_by_score :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>insort_inner_clauses_by_score arena = insert_sort_inner (clause_score_extract arena)\<close>

definition (in -) sort_clauses_by_score :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>sort_clauses_by_score arena = insert_sort (clause_score_extract arena)\<close>

definition reorder_vdom_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>reorder_vdom_wl S = RETURN S\<close>

definition (in -) sort_vdom_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>sort_vdom_heur = (\<lambda>(M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount). do {
    ASSERT(valid_sort_clause_score_pre arena avdom);
    avdom \<leftarrow> sort_clauses_by_score arena avdom;
    RETURN (M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount)
    })\<close>

lemma sort_clauses_by_score_reorder:
  \<open>sort_clauses_by_score arena vdom \<le> SPEC(\<lambda>vdom'. mset vdom = mset vdom')\<close>
  unfolding sort_clauses_by_score_def
  by (rule order.trans, rule insert_sort_reorder_remove[THEN fref_to_Down, of _ vdom])
     (auto simp add: reorder_remove_def)

lemma (in isasat_input_ops) sort_vdom_heur_reorder_vdom_wl:
  \<open>(sort_vdom_heur, reorder_vdom_wl) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding  reorder_vdom_wl_def sort_vdom_heur_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
        intro!: exI[of _ \<open>get_clauses_wl y\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_def dest: mset_eq_setD)
    done
qed

lemma (in -) less_pair_uint32_nat_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (<)), uncurry (RETURN oo (<))) \<in> (uint32_nat_assn *a uint32_nat_assn)\<^sup>d *\<^sub>a (uint32_nat_assn *a uint32_nat_assn)\<^sup>d \<rightarrow>\<^sub>a bool_assn\<close>
   by sepref_to_hoare
     (sep_auto simp: less_prod_def uint32_nat_rel_def br_def nat_of_uint32_less_iff)

lemma (in -) insort_inner_clauses_by_score_invI:
   \<open>valid_sort_clause_score_pre a ba \<Longrightarrow>
       mset ba = mset a2' \<Longrightarrow>
       a1' < length a2' \<Longrightarrow>
       valid_sort_clause_score_pre_at a a2' a1'\<close>
  unfolding valid_sort_clause_score_pre_def all_set_conv_nth valid_sort_clause_score_pre_at_def
  by (metis in_mset_conv_nth)+

sepref_definition (in -) insort_inner_clauses_by_score_code
  is \<open>uncurry2 insort_inner_clauses_by_score\<close>
  :: \<open>[\<lambda>((arena, vdom), _). valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> vdom_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro]
  unfolding insort_inner_clauses_by_score_def insert_sort_inner_def
  by sepref

declare insort_inner_clauses_by_score_code.refine[sepref_fr_rules]

lemma sort_clauses_by_score_invI:
  \<open>valid_sort_clause_score_pre a b \<Longrightarrow>
       mset b = mset a2' \<Longrightarrow> valid_sort_clause_score_pre a a2'\<close>
  using mset_eq_setD unfolding valid_sort_clause_score_pre_def by blast

sepref_definition (in -) sort_clauses_by_score_code
  is \<open>uncurry sort_clauses_by_score\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding insert_sort_def insort_inner_clauses_by_score_def[symmetric]
    sort_clauses_by_score_def
  by sepref

declare sort_clauses_by_score_code.refine[sepref_fr_rules]


context isasat_input_ops
begin

sepref_thm (in isasat_input_ops) sort_vdom_heur_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding sort_vdom_heur_def isasat_unbounded_assn_def
  by sepref


concrete_definition (in -) sort_vdom_heur_code
   uses isasat_input_ops.sort_vdom_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) sort_vdom_heur_code_def

lemmas sort_vdom_heur_code_hnr[sepref_fr_rules] =
   sort_vdom_heur_code.refine[of \<A>\<^sub>i\<^sub>n]

definition opts_restart_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_restart_st = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts). (opts_restart opts))\<close>

sepref_thm opts_restart_st_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) opts_restart_st_code
   uses isasat_input_ops.opts_restart_st_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) opts_restart_st_code_def

lemmas opts_restart_st_hnr[sepref_fr_rules] =
   opts_restart_st_code.refine[of \<A>\<^sub>i\<^sub>n]

sepref_thm opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref

concrete_definition (in -) opts_restart_st_fast_code
   uses isasat_input_ops.opts_restart_st_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) opts_restart_st_fast_code_def

lemmas opts_restart_st_fast_hnr[sepref_fr_rules] =
   opts_restart_st_fast_code.refine[of \<A>\<^sub>i\<^sub>n]

definition opts_reduction_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_reduction_st = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). (opts_reduce opts))\<close>

sepref_thm opts_reduction_st_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_unbounded_assn_def
  by sepref

concrete_definition (in -) opts_reduction_st_code
   uses isasat_input_ops.opts_reduction_st_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) opts_reduction_st_code_def

lemmas opts_reduction_st_hnr[sepref_fr_rules] =
   opts_reduction_st_code.refine[of \<A>\<^sub>i\<^sub>n]

sepref_thm opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

concrete_definition (in -) opts_reduction_st_fast_code
   uses isasat_input_ops.opts_reduction_st_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) opts_reduction_st_fast_code_def

lemmas opts_reduction_st_fast_hnr[sepref_fr_rules] =
   opts_reduction_st_fast_code.refine[of \<A>\<^sub>i\<^sub>n]
end

context isasat_input_bounded_nempty
begin
sepref_register opts_reduction_st opts_restart_st

definition (in isasat_input_ops) restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n = do {
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let sema = ema_get_value (get_slow_ema_heur S);
    let limit = (18 * sema) >> 4;
       \<comment>\<open>roughly speaking 125/100 with hopefully no overflow (there is currently no division
         on \<^typ>\<open>uint64\<close>\<close>
    let fema = ema_get_value (get_fast_ema_heur S);
    let ccount = get_conflict_count_since_last_restart_heur S;
    let lcount = get_learned_count S;
    let can_res = (lcount > n);
    let min_reached = (ccount > minimum_number_between_restarts);
    let level = count_decided_st S;
    let should_not_reduce = (\<not>opt_red \<or> upper_restart_bound_not_reached S);
    RETURN ((opt_res \<or> opt_red) \<and>
       (should_not_reduce \<longrightarrow> limit > fema) \<and> min_reached \<and> can_res \<and>
      level > two_uint32_nat \<and> nat_of_uint32_conv level > nat_of_uint64 (fema >> 48))}
  \<close>

lemma uint64_max_ge_48: \<open>48 \<le> uint64_max\<close>
  by (auto simp: uint64_max_def)


sepref_thm restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]] uint64_max_ge_48[simp]
  bit_lshift_uint64_assn[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

concrete_definition (in -) restart_required_heur_fast_code
   uses isasat_input_bounded_nempty.restart_required_heur_fast_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) restart_required_heur_fast_code_def

lemmas restart_required_heur_fast_code_hnr[sepref_fr_rules] =
   restart_required_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm restart_required_heur_slow_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]] uint64_max_ge_48[simp]
  bit_lshift_uint64_assn[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

concrete_definition (in -) restart_required_heur_slow_code
   uses isasat_input_bounded_nempty.restart_required_heur_slow_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) restart_required_heur_slow_code_def

lemmas restart_required_heur_slow_code_hnr[sepref_fr_rules] =
   restart_required_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) mark_to_delete_clauses_wl_D_heur_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>mark_to_delete_clauses_wl_D_heur_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur \<and> mark_to_delete_clauses_wl_D_pre S')\<close>

definition (in isasat_input_ops) mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts))\<close>

lemma (in isasat_input_ops) get_vdom_mark_garbage[simp]:
  \<open>get_vdom (mark_garbage_heur C i S) = get_vdom S\<close>
  \<open>get_avdom (mark_garbage_heur C i S) = delete_index_and_swap (get_avdom S) i\<close>
  by (cases S; auto simp: mark_garbage_heur_def; fail)+

lemma (in isasat_input_ops) mark_garbage_heur_wl:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
  \<not>irred (get_clauses_wl T) C \<Longrightarrow>
 (mark_garbage_heur C i S, mark_garbage_wl C T) \<in> twl_st_heur\<close>
  by (cases S; cases T)
     (auto simp: twl_st_heur_def mark_garbage_heur_def mark_garbage_wl_def
      learned_clss_l_l_fmdrop size_remove1_mset_If
    intro: valid_arena_extra_information_mark_to_delete'
    dest!: in_set_butlastD in_vdom_m_fmdropD
    elim!: in_set_upd_cases)

lemma (in isasat_input_ops) twl_st_heur_valid_arena[twl_st_heur]:
  assumes
    \<open>(S, T) \<in> twl_st_heur\<close>
  shows \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
  using assms by (auto simp: twl_st_heur_def)

lemma (in isasat_input_ops) twl_st_heur_get_avdom_nth_get_vdom[twl_st_heur]:
  assumes
    \<open>(S, T) \<in> twl_st_heur\<close> \<open>i < length (get_avdom S)\<close>
  shows \<open>get_avdom S ! i \<in> set (get_vdom S)\<close>
  using assms by (fastforce simp: twl_st_heur_def)

lemma (in isasat_input_ops) [twl_st_heur]:
  assumes
    \<open>(S, T) \<in> twl_st_heur\<close> and
    \<open>C \<in> set (get_avdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow>
         (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
proof -
  show \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close>
    using assms
    by (cases S; cases T)
      (auto simp add: twl_st_heur_def clause_not_marked_to_delete_heur_def
          arena_dom_status_iff(1)
        split: prod.splits)
  assume C: \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  show \<open>arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
qed

definition (in isasat_input_ops) number_clss_to_keep :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>number_clss_to_keep = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
      (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount).
    1000 + 150 * nat_of_uint64 restarts)\<close>


definition (in isasat_input_ops) access_vdom_at :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_vdom_at S i = get_avdom S ! i\<close>

lemma access_vdom_at_alt_def:
  \<open>access_vdom_at = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount) i. avdom ! i)\<close>
  by (intro ext) (auto simp: access_vdom_at_def)

definition (in isasat_input_ops) access_vdom_at_pre where
  \<open>access_vdom_at_pre S i \<longleftrightarrow> i < length (get_avdom S)\<close>

(* TODO Missing : The sorting function + definition of l should depend on the number of initial
  clauses *)
definition (in -) MINIMUM_DELETION_LBD :: nat where
  \<open>MINIMUM_DELETION_LBD = 3\<close>

lemma (in -) MINIMUM_DELETION_LBD_hnr[sepref_fr_rules]:
 \<open>(uncurry0 (return 3), uncurry0 (RETURN MINIMUM_DELETION_LBD)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: MINIMUM_DELETION_LBD_def uint32_nat_rel_def br_def)

definition (in isasat_input_ops)  delete_index_vdom_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close>where
  \<open>delete_index_vdom_heur = (\<lambda>i (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount).
     (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
       ccount, vdom, delete_index_and_swap avdom i, lcount))\<close>

definition (in isasat_input_ops) mark_to_delete_clauses_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
    S \<leftarrow> sort_vdom_heur S;
    let l = number_clss_to_keep S;
    (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
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
          ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
          D \<leftarrow> get_the_propagation_reason (get_trail_wl_heur T) L;
          ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
          ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
          let can_del = (D \<noteq> Some C) \<and> arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
             arena_status (get_clauses_wl_heur T) C = LEARNED;
          if can_del
          then
            do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
          else
            RETURN (i+1, T)
        }
      })
      (l, S);
    incr_restart_stat T
  })\<close>

lemma (in isasat_input_ops) twl_st_heur_same_annotD:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> Propagated L C \<in> set (get_trail_wl_heur S) \<Longrightarrow>
     Propagated L C' \<in> set (get_trail_wl_heur S) \<Longrightarrow> C = C'\<close>
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> Propagated L C \<in> set (get_trail_wl_heur S) \<Longrightarrow>
     Decided L \<in> set (get_trail_wl_heur S) \<Longrightarrow> False\<close>
  by (auto simp: twl_st_heur_def dest: no_dup_no_propa_and_dec
    no_dup_same_annotD)


lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D:
  \<open>(mark_to_delete_clauses_wl_D_heur, mark_to_delete_clauses_wl_D) \<in>
     twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
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
            ASSERT(get_clauses_wl T\<propto>(xs!i)!0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
              (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
               \<not>irred (get_clauses_wl T) (xs!i));
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
      (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
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
            ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
            D \<leftarrow> get_the_propagation_reason (get_trail_wl_heur T) L;
            ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
            ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
            let can_del = (D \<noteq> Some C) \<and> arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur T) C = LEARNED;
            if can_del
            then do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
            else
              RETURN (i+1, T)
          }
        })
        (l, S);
      incr_restart_stat T
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_heur_def
    by (auto intro!: ext)

  have [refine0]: \<open>RETURN (get_avdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_avdom x} (collect_valid_indices_wl y)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y
  proof -
    show ?thesis by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed
  have init_rel[refine0]: \<open>(x, y) \<in> twl_st_heur \<Longrightarrow>
       (l, la) \<in> nat_rel \<Longrightarrow>
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur \<and> get_avdom S = get_avdom x}\<close>
    for x y l la
    by auto
  have get_the_propagation_reason:
    \<open>get_the_propagation_reason (get_trail_wl_heur x2b)
       (arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0))
        \<le> \<Down> {(D, b). b \<longleftrightarrow> ((D \<noteq> Some (get_avdom x2b ! x1b)) \<and>
               arena_lbd (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) = LEARNED)}
       (SPEC
           (\<lambda>b. b \<longrightarrow>
                Propagated (get_clauses_wl x1a \<propto> (x2a ! x1) ! 0) (x2a ! x1)
                \<notin> set (get_trail_wl x1a) \<and>
                \<not> irred (get_clauses_wl x1a) (x2a ! x1)))\<close>
  if
    \<open>(x, y) \<in> twl_st_heur\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
    \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur \<and> xs = get_avdom Sa}\<close> and
    \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
    \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
    \<open>x1b < length (get_avdom x2b)\<close> and
    \<open>access_vdom_at_pre x2b x1b\<close> and
    \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
    \<open>\<not> \<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
    \<open>\<not> x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close> and
    \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
    \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>access_lit_in_clauses_heur_pre ((x2b, get_avdom x2b ! x1b), 0)\<close> and
    \<open>x2 = (x1a, x2a)\<close> and
    \<open>x' = (x1, x2)\<close> and
    \<open>xa = (x1b, x2b)\<close> and
    \<open>arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for x y S Sa xs' xs l la xa x' x1 x2 x1a x2a x1' x2' x3 x1b ys x2b
  proof -
    show ?thesis
      using that unfolding get_the_propagation_reason_def apply -
      by (rule RES_refine)
        (auto simp: twl_st_heur lits_of_def
        dest: twl_st_heur_same_annotD imageI[of _ _ lit_of])
  qed
  have \<open>((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom, lcount),
           S')
          \<in> twl_st_heur \<longleftrightarrow>
    ((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom', lcount),
           S')
          \<in> twl_st_heur\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema
      ccount vdom lcount S' avdom' avdom
    using that unfolding twl_st_heur_def
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
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur \<and> V = T \<and>
         (mark_to_delete_clauses_wl_D_pre T \<longrightarrow> mark_to_delete_clauses_wl_D_pre V) \<and>
         (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U)}
         (reorder_vdom_wl T)\<close>
    if \<open>(S, T) \<in> twl_st_heur\<close> for S T
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply refine_rcg
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_def
         intro: mark_to_delete_clauses_wl_D_heur_pre_vdom'[THEN iffD1]
         dest: mset_eq_setD)
    done
  have already_deleted:
    \<open>((x1b, delete_index_vdom_heur x1b x2b), x1, x1a,
       delete_index_and_swap x2a x1)
      \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur \<and> xs = get_avdom Sa}\<close>
    if
      \<open>(x, y) \<in> twl_st_heur\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
      \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur \<and> xs = get_avdom Sa}\<close> and
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
      by (auto simp: twl_st_heur_def delete_index_vdom_heur_def
          twl_st_heur_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If
          intro: valid_arena_extra_information_mark_to_delete'
          dest!: in_set_butlastD in_vdom_m_fmdropD
          elim!: in_set_upd_cases)
  qed

  have init:
    \<open>(u, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S} \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur \<Longrightarrow>
    mark_to_delete_clauses_wl_D_inv Sa xs (la, Sa, xs) \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
       {(Sa, (T, xs)). (Sa, T) \<in> twl_st_heur \<and> xs = get_avdom Sa}\<close>
       for x y S Sa xs l la u
    by auto
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
         (auto simp: twl_st_heur dest: twl_st_heur_get_avdom_nth_get_vdom)
    subgoal
      by (auto simp: twl_st_heur)
    subgoal
      by (rule already_deleted)
    subgoal for x y _ _ _ _ _ xs l la xa x' x1 x2 x1a x2a
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_avdom x2a ! x1a\<close>], simp, rule exI[of _ \<open>get_clauses_wl x1\<close>])
        (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur)
    apply (rule get_the_propagation_reason; assumption)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur dest: twl_st_heur_valid_arena)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur dest: twl_st_heur_valid_arena twl_st_heur_get_avdom_nth_get_vdom)
    subgoal
      by (auto simp: twl_st_heur)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur dest: twl_st_heur_valid_arena)
    subgoal
      by (auto simp: mark_garbage_heur_wl)
    subgoal
      by auto
    subgoal
      by (auto simp: incr_restart_stat_def twl_st_heur_def)
    done
qed

definition (in isasat_input_ops) cdcl_twl_full_restart_wl_prog_heur where
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
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def by fast
  done

definition (in isasat_input_ops) cdcl_twl_restart_wl_heur where
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


definition (in isasat_input_ops) restart_prog_wl_D_heur
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
      cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
      cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D[THEN fref_to_Down]
      cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog[THEN fref_to_Down])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end