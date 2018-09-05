theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart
     IsaSAT_CDCL
begin

locale isasat_restart_bounded =
  twl_restart + isasat_input_bounded

sublocale isasat_restart_bounded \<subseteq> isasat_restart_ops
 .


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
     \<^item> EMA-14, aka restart if enough clauses and slow_glue_avg * opts.restartmargin > fast_glue (file ema.cpp)
     \<^item> (lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts),
       \<^text>\<open>conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()\<close>
\<close>

definition tight_domain where
  \<open>tight_domain NU NU' \<longleftrightarrow>  Suc (Max_mset (add_mset 0 (dom_m NU))) = length NU'\<close>

lemma Max_insert_remove1_is_Max_insert:
  fixes x :: \<open>nat\<close>
  assumes \<open>0 < x\<close> \<open>finite A\<close>
  shows \<open>Max (insert x A - {0}) = Max (insert x A)\<close>
proof -
  show ?thesis
    apply (rule Max_eq_if)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal
      apply (intro ballI)
      subgoal for b
        apply (cases \<open>b = 0\<close>)
         apply (rule_tac x = x in bexI)
        using assms apply auto[2]
        apply (rule_tac x = b in bexI)
        using assms apply auto[2]
        done
      done
    done
qed

lemma Max_mset_eq: \<open>((\<forall>m\<in>#M. m \<le> a) \<and> a\<in>#M) \<Longrightarrow> Max_mset M = a\<close>
  by (subst Max_eq_iff) auto

lemma Suc_eq_minus_iff: \<open>b \<noteq> 0 \<Longrightarrow> Suc a = b \<longleftrightarrow> a = b - 1\<close>
  by auto

lemma tight_domain_alt_def: \<open>0 \<notin># dom_m NU \<Longrightarrow> tight_domain NU NU' \<longleftrightarrow>
      (\<forall>j \<in>#dom_m NU. j < length NU') \<and> NU' \<noteq> [] \<and>
      ((NU = fmempty \<and> length NU' = 1) \<or> (NU \<noteq> fmempty \<and> length NU' \<ge> 1 \<and> length NU' - 1 \<in># dom_m NU))\<close>
  apply (intro iffI conjI impI)
  subgoal
    using distinct_mset_dom[of \<open>NU\<close>]
    by (auto simp: tight_domain_def Max.insert_remove Max_insert_remove1_is_Max_insert
        add_mset_eq_add_mset
        split: if_splits
        dest!: multi_member_split[of _ \<open>dom_m NU\<close>])
  subgoal
    using distinct_mset_dom[of \<open>NU\<close>]
    by (auto simp: tight_domain_def Max.insert_remove Max_insert_remove1_is_Max_insert
        add_mset_eq_add_mset
        split: if_splits
        dest!: multi_member_split[of _ \<open>dom_m NU\<close>])
  subgoal
    using distinct_mset_dom[of \<open>NU\<close>]
    apply (auto simp: tight_domain_def Max.insert_remove Max_insert_remove1_is_Max_insert
        add_mset_eq_add_mset dom_m_empty_iff
        split: if_splits
        dest: multi_member_split[of _ \<open>dom_m NU\<close>] Max_dom_empty)
    using Max_in_lits Suc_to_right dom_m_empty_iff by auto
  subgoal
    using distinct_mset_dom[of \<open>NU\<close>]
    by (auto simp: tight_domain_def Max.insert_remove Max_insert_remove1_is_Max_insert
        add_mset_eq_add_mset Suc_eq_minus_iff max_def
        split: if_splits
        dest: multi_member_split[of _ \<open>dom_m NU\<close>]
        intro!: Max_mset_eq)
  done


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
       stats, fema, sema, ccount, lcount). RETURN sema)\<close>
  by auto

sepref_thm get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_fast_assn_def
  by sepref

concrete_definition (in -) get_slow_ema_heur_fast_code
   uses isasat_input_bounded_nempty.get_slow_ema_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_slow_ema_heur_fast_code_def

lemmas get_slow_ema_heur_fast_code_hnr[sepref_fr_rules] =
   get_slow_ema_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm get_slow_ema_heur_slow_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_assn_def
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
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_fast_assn_def
  by sepref

concrete_definition (in -) get_fast_ema_heur_fast_code
   uses isasat_input_bounded_nempty.get_fast_ema_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_fast_ema_heur_fast_code_def

lemmas get_fast_ema_heur_fast_code_hnr[sepref_fr_rules] =
   get_fast_ema_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm get_fast_ema_heur_slow_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_assn_def
  by sepref

concrete_definition (in -) get_fast_ema_heur_slow_code
   uses isasat_input_bounded_nempty.get_fast_ema_heur_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_fast_ema_heur_slow_code_def

lemmas get_fast_ema_heur_slow_code_hnr[sepref_fr_rules] =
   get_fast_ema_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma get_counflict_count_heur_alt_def:
   \<open>RETURN o get_conflict_count_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, lcount). RETURN ccount)\<close>
  by auto

sepref_thm get_conflict_count_heur_fast_code
  is \<open>RETURN o get_conflict_count_heur\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_fast_assn_def
  by sepref

concrete_definition (in -) get_conflict_count_heur_fast_code
   uses isasat_input_bounded_nempty.get_conflict_count_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_count_heur_fast_code_def

lemmas get_conflict_count_heur_code_hnr[sepref_fr_rules] =
   get_conflict_count_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm get_conflict_count_heur_slow_code
  is \<open>RETURN o get_conflict_count_heur\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_assn_def
  by sepref

concrete_definition (in -) get_conflict_count_heur_slow_code
   uses isasat_input_bounded_nempty.get_conflict_count_heur_slow_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_count_heur_slow_code_def

lemmas get_conflict_count_heur_slow_code_hnr[sepref_fr_rules] =
   get_conflict_count_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma get_learned_count_alt_def:
   \<open>RETURN o get_learned_count = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, lcount). RETURN lcount)\<close>
  by auto

sepref_thm get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_fast_assn_def
  by sepref

concrete_definition (in -) get_learned_count_fast_code
   uses isasat_input_bounded_nempty.get_learned_count_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_learned_count_fast_code_def

lemmas get_learned_count_code_hnr[sepref_fr_rules] =
   get_learned_count_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm get_learned_count_slow_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_assn_def
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
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_assn_def PR_CONST_def
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
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_fast_assn_def PR_CONST_def
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
    RETURN (M, N, D, j, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, 0, vdom, lcount)
  })\<close>

definition (in isasat_input_ops) incr_restart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_restart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, oth). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_restart stats, oth)
  })\<close>

sepref_thm incr_restart_stat_slow_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_assn_def PR_CONST_def
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
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_fast_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) incr_restart_stat_fast_code
   uses isasat_input_bounded_nempty.incr_restart_stat_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) incr_restart_stat_fast_code_def
lemmas incr_restart_stat_fast_code_hnr [sepref_fr_rules] =
   incr_restart_stat_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


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
        incr_restart_stat S
      }
   })\<close>


sepref_thm empty_Q_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_assn_def
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
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_fast_assn_def
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
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
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
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn\<close>
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

(* TODO Move *)
lemma RES_RES13_RETURN_RES: \<open>do {
  (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, oth) \<leftarrow> RES A;
  RES (f M N D Q W vm \<phi> clvls cach lbd outl stats oth)
} = RES (\<Union>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, oth)\<in>A. f M N D Q W vm \<phi> clvls cach lbd outl stats oth)\<close>
  by (force simp:  pw_eq_iff refine_pw_simps uncurry_def)
(* End Move *)

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
      find_decomp_wl_st_int_def find_local_restart_target_level_def incr_restart_stat_def
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
    subgoal for a aa ab ac b ad ae af ag ah ai ba bb aj ak al am an ao ap aq bc ar as at au
       bd av aw ax ay az be bf lvl i x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e
       x2e x1f x2f x1g x2g x1h x2h x1i x2i S x1j x2j x1k x2k x1l x2l x1m x2m x1n
       x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w
       x2w x1x x2x x1y x2y
      unfolding RETURN_def RES_RES2_RETURN_RES RES_RES13_RETURN_RES
      apply (rule RES_refine, rule bexI[of _ \<open>(get_trail_wl_heur S, aw, ax, ay, az, {#}, bf)\<close>];
         ((subst uncurry_def image_iff)+)?; (rule bexI[of _ \<open>(get_trail_wl_heur S, {#})\<close>])?)
      by ((fastforce simp: twl_st_heur_def)+)[2]
        (auto simp: twl_st_heur_def)
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


definition (in -) minimum_number_between_restarts :: \<open>uint32\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

lemma (in -) minimum_number_between_restarts[sepref_fr_rules]:
 \<open>(uncurry0 (return minimum_number_between_restarts), uncurry0 (RETURN minimum_number_between_restarts))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
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


definition (in -) local_restart_only :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>local_restart_only = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, (props, decs, confl, restarts), fast_ema, slow_ema, ccount,
       vdom, lcount).
    lcount < 2000 + 300 * nat_of_uint64 restarts)\<close>

sepref_register local_restart_only
sepref_thm local_restart_only_impl
  is \<open>PR_CONST (RETURN o local_restart_only)\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding local_restart_only_def PR_CONST_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) local_restart_only_impl
   uses isasat_input_bounded_nempty.local_restart_only_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) local_restart_only_impl_def

lemmas local_restart_only_impl[sepref_fr_rules] =
   local_restart_only_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_thm local_restart_only_fast_impl
  is \<open>PR_CONST (RETURN o local_restart_only)\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding local_restart_only_def PR_CONST_def isasat_fast_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) local_restart_only_fast_impl
   uses isasat_input_bounded_nempty.local_restart_only_fast_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) local_restart_only_fast_impl_def

lemmas local_restart_only_fast_impl[sepref_fr_rules] =
   local_restart_only_fast_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

definition (in -) restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n = do {
    let sema = get_slow_ema_heur S;
    let sema' = (5 * get_slow_ema_heur S) >> 2;
       \<comment>\<open>roughly speaking 125/100 with hopefully no overflow (there is currently no division
         on \<^typ>\<open>uint64\<close>\<close>
    let fema = get_fast_ema_heur S;
    let ccount = get_conflict_count_heur S;
    let lcount = get_learned_count S;
    let can_res = (lcount > n);
    let min_reached = (ccount > minimum_number_between_restarts);
    RETURN ((local_restart_only S \<longrightarrow> sema' > fema) \<and> min_reached \<and> can_res)}
  \<close>

sepref_thm restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
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
  :: \<open>isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
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

definition (in isasat_input_ops) mark_garbage_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur C = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount - 1))\<close>

lemma (in isasat_input_ops) get_vdom_mark_garbage[simp]:
  \<open>get_vdom (mark_garbage_heur C S) = get_vdom S\<close>
  by (cases S) (auto simp: mark_garbage_heur_def)

lemma (in isasat_input_ops) mark_garbage_heur_wl:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
  \<not>irred (get_clauses_wl T) C \<Longrightarrow>
 (mark_garbage_heur C S, mark_garbage_wl C T) \<in> twl_st_heur\<close>
  by (cases S; cases T)
    (auto simp: twl_st_heur_def mark_garbage_heur_def mark_garbage_wl_def
      learned_clss_l_l_fmdrop size_remove1_mset_If
    intro: valid_arena_extra_information_mark_to_delete'
    dest: in_vdom_m_fmdropD)

lemma (in isasat_input_ops) twl_st_heur_valid_arena[twl_st_heur]:
  assumes
    \<open>(S, T) \<in> twl_st_heur\<close>
  shows \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
  using assms by (auto simp: twl_st_heur_def)

lemma (in isasat_input_ops) [twl_st_heur]:
  assumes
    \<open>(S, T) \<in> twl_st_heur\<close> and
    \<open>i < length (get_vdom S)\<close> and
    \<open>C \<in> set (get_vdom S)\<close>
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
  \<open>number_clss_to_keep = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, (props, decs, confl, restarts), fast_ema, slow_ema, ccount,
       vdom, lcount).
    2000 + 300 * nat_of_uint64 restarts)\<close>


definition (in isasat_input_ops) access_vdom_at :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_vdom_at S i = get_vdom S ! i\<close>

lemma access_vdom_at_alt_def:
  \<open>access_vdom_at = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) i. vdom ! i)\<close>
  by (intro ext) (auto simp: access_vdom_at_def)

definition (in isasat_input_ops) access_vdom_at_pre where
  \<open>access_vdom_at_pre S i \<longleftrightarrow> i < length (get_vdom S)\<close>

(* TODO Missing : The sorting function + definition of l should depend on the number of initial
  clauses *)
definition (in -) MINIMUM_DELETION_LBD :: nat where
  \<open>MINIMUM_DELETION_LBD = 3\<close>

lemma (in -) MINIMUM_DELETION_LBD_hnr[sepref_fr_rules]:
 \<open>(uncurry0 (return 3), uncurry0 (RETURN MINIMUM_DELETION_LBD)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: MINIMUM_DELETION_LBD_def uint32_nat_rel_def br_def)

definition (in isasat_input_ops) mark_to_delete_clauses_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
    let l = number_clss_to_keep S;
    (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(i, S). i < length (get_vdom S))
      (\<lambda>(i, T). do {
        ASSERT(i < length (get_vdom T));
        ASSERT(access_vdom_at_pre T i);
        let C = get_vdom T ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
        if \<not>clause_not_marked_to_delete_heur T C then RETURN (i+1, T)
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
              RETURN (i+1, mark_garbage_heur C T)
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
      xs \<leftarrow> collect_valid_indices_wl S;
      l \<leftarrow> SPEC(\<lambda>_::nat. True);
      (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_D_inv S xs\<^esup>
        (\<lambda>(i, T). i < length xs)
        (\<lambda>(i, T). do {
          if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i+1, T)
          else do {
            ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
            ASSERT(get_clauses_wl T\<propto>(xs!i)!0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and> \<not>irred (get_clauses_wl T) (xs!i));
            ASSERT(i < length xs);
            if can_del
            then
              RETURN (i+1, mark_garbage_wl (xs!i) T)
            else
              RETURN (i+1, T)
          }
        })
        (l, S);
      RETURN S
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_def
    by (auto intro!: ext)

  have mark_to_delete_clauses_wl_D_heur_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
      _ \<leftarrow> RETURN (get_vdom S);
      l \<leftarrow> RETURN (number_clss_to_keep S);
      (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
        (\<lambda>(i, S). i < length (get_vdom S))
        (\<lambda>(i, T). do {
          ASSERT(i < length (get_vdom T));
          ASSERT(access_vdom_at_pre T i);
          let C = get_vdom T ! i;
          ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
          if(\<not>clause_not_marked_to_delete_heur T C) then RETURN (i+1, T)
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
              RETURN (i+1, mark_garbage_heur C T)
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

  have [refine0]: \<open>RETURN (get_vdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_vdom x} (collect_valid_indices_wl y)\<close>
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
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur \<and> get_vdom S = get_vdom x}\<close>
    for x y l la
    by auto
  have get_the_propagation_reason: \<open>get_the_propagation_reason (get_trail_wl_heur x2a)
        (arena_lit (get_clauses_wl_heur x2a) (get_vdom x2a ! x1a + 0))
        \<le> \<Down> {(D, b). b \<longleftrightarrow> ((D \<noteq> Some (get_vdom x2a ! x1a)) \<and>
               arena_lbd (get_clauses_wl_heur x2a) (get_vdom x2a ! x1a) > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur x2a) (get_vdom x2a ! x1a) = LEARNED)}
          (SPEC
            (\<lambda>b. b \<longrightarrow>
                  Propagated (get_clauses_wl x2 \<propto> (xs ! x1) ! 0) (xs ! x1)
                  \<notin> set (get_trail_wl x2) \<and>
                  \<not> irred (get_clauses_wl x2) (xs ! x1)))\<close>
    if
      \<open>(x, y) \<in> twl_st_heur\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(xs', xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_vdom x}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>(xa, x')
      \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur \<and> get_vdom S = get_vdom x}\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_vdom S)\<close> and
      \<open>case x' of (i, T) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv y xs x'\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>xa = (x1a, x2a)\<close> and
      \<open>x1a < length (get_vdom x2a)\<close> and
      \<open>\<not> \<not> clause_not_marked_to_delete_heur x2a (get_vdom x2a ! x1a)\<close> and
      \<open>\<not> xs ! x1 \<notin># dom_m (get_clauses_wl x2)\<close> and
      \<open>0 < length (get_clauses_wl x2 \<propto> (xs ! x1))\<close> and
      \<open>get_clauses_wl x2 \<propto> (xs ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for x y xs xs' l la xa x' x1 x2 x1a x2a
  proof -
    show ?thesis
      using that unfolding get_the_propagation_reason_def apply -
      by (rule RES_refine)
        (auto simp: twl_st_heur lits_of_def intro!: 
        dest: twl_st_heur_same_annotD imageI[of _ _ lit_of])
  qed

  show ?thesis
    unfolding mark_to_delete_clauses_wl_D_heur_alt_def mark_to_delete_clauses_wl_D_def Let_def
      access_lit_in_clauses_heur_def
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal
      unfolding mark_to_delete_clauses_wl_D_heur_pre_def by fast
    subgoal
      by auto
    subgoal
      by auto
    subgoal by (auto simp: access_vdom_at_pre_def)
    subgoal for x y _ xs l la xa x' x1 x2 x1a x2a
      unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
        prod.simps
      by (rule exI[of _ \<open>get_clauses_wl x2\<close>], rule exI[of _ \<open>set (get_vdom x2a)\<close>])
        (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur)
    subgoal
      by auto
    subgoal for x y _ xs l la xa x' x1 x2 x1a x2a
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_vdom x2a ! x1a\<close>], simp, rule exI[of _ \<open>get_clauses_wl x2\<close>])
        (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur)
    apply (rule get_the_propagation_reason; assumption)
    subgoal for x y _ xs l la xa x' x1 x2 x1a x2a
      unfolding prod.simps
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x2\<close>], rule exI[of _ \<open>set (get_vdom x2a)\<close>])
        (auto simp: twl_st_heur dest: twl_st_heur_valid_arena)
    subgoal for x y _ xs l la xa x' x1 x2 x1a x2a
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x2\<close>], rule exI[of _ \<open>set (get_vdom x2a)\<close>])
        (auto simp: twl_st_heur dest: twl_st_heur_valid_arena)
    subgoal
      by (auto simp: twl_st_heur)
    subgoal for x y _ xs l la xa x' x1 x2 x1a x2a
      unfolding prod.simps mark_garbage_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x2\<close>], rule exI[of _ \<open>set (get_vdom x2a)\<close>])
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
    let b = local_restart_only S;
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

definition (in isasat_input_ops) cdcl_twl_stgy_restart_abs_wl_heur_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n \<longleftrightarrow>
    (\<exists>S\<^sub>0' T'. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
      cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0' brk T' n)\<close>

definition (in isasat_input_ops) cdcl_twl_stgy_restart_prog_wl_heur
   :: "twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres"
where
  \<open>cdcl_twl_stgy_restart_prog_wl_heur S\<^sub>0 = do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        (T, n) \<leftarrow> restart_prog_wl_D_heur T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0::twl_st_wl_heur, 0);
    RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_wl_heur_cdcl_twl_stgy_restart_prog_wl_D:
  \<open>(cdcl_twl_stgy_restart_prog_wl_heur, cdcl_twl_stgy_restart_prog_wl_D) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_heur_def cdcl_twl_stgy_restart_prog_wl_D_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry2]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r twl_st_heur \<times>\<^sub>r nat_rel\<close>])
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


sepref_register number_clss_to_keep

sepref_thm number_clss_to_keep_impl
  is \<open>PR_CONST (RETURN o number_clss_to_keep)\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding number_clss_to_keep_def PR_CONST_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) number_clss_to_keep_impl
   uses isasat_input_bounded_nempty.number_clss_to_keep_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) number_clss_to_keep_impl_def

lemmas number_clss_to_keep_impl[sepref_fr_rules] =
   number_clss_to_keep_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_register access_vdom_at
sepref_thm access_vdom_at_code
  is \<open>uncurry (PR_CONST (RETURN oo access_vdom_at))\<close>
  :: \<open>[uncurry access_vdom_at_pre]\<^sub>a isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding access_vdom_at_alt_def PR_CONST_def access_vdom_at_pre_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) access_vdom_at_code
   uses isasat_input_bounded_nempty.access_vdom_at_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) access_vdom_at_code_def

lemmas access_vdom_at_code[sepref_fr_rules] =
   access_vdom_at_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]


definition length_vdom :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>length_vdom S = length (get_vdom S)\<close>

lemma length_vdom_alt_def:
  \<open>length_vdom = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount). length vdom)\<close>
  by (intro ext) (auto simp: length_vdom_def)

sepref_register length_vdom
sepref_thm length_vdom_code
  is \<open>PR_CONST (RETURN o length_vdom)\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding length_vdom_alt_def PR_CONST_def access_vdom_at_pre_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) length_vdom_code
   uses isasat_input_bounded_nempty.length_vdom_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) length_vdom_code_def

lemmas length_vdom_code[sepref_fr_rules] =
   length_vdom_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]


definition (in isasat_input_ops) get_the_propagation_reason_heur 
 :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close>
where
  \<open>get_the_propagation_reason_heur S = get_the_propagation_reason (get_trail_wl_heur S)\<close>

lemma get_the_propagation_reason_heur_alt_def:
  \<open>get_the_propagation_reason_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) L . get_the_propagation_reason M' L)\<close>
  by (intro ext) (auto simp: get_the_propagation_reason_heur_def)

sepref_register get_the_propagation_reason_heur
sepref_thm get_the_propagation_reason_heur_code
  is \<open>uncurry (PR_CONST get_the_propagation_reason_heur)\<close>
  :: \<open>[\<lambda>(S, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>aisasat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  unfolding get_the_propagation_reason_heur_alt_def PR_CONST_def access_vdom_at_pre_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_the_propagation_reason_heur_code
   uses isasat_input_bounded_nempty.get_the_propagation_reason_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) get_the_propagation_reason_heur_code_def

lemmas get_the_propagation_reason_heur[sepref_fr_rules] =
   get_the_propagation_reason_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

definition (in isasat_input_ops) clause_is_learned_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool"
where
  \<open>clause_is_learned_heur S C \<longleftrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED\<close>

lemma clause_is_learned_heur_alt_def:
  \<open>clause_is_learned_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . arena_status N' C = LEARNED)\<close>
  by (intro ext) (auto simp: clause_is_learned_heur_def)

sepref_register clause_is_learned_heur
sepref_thm clause_is_learned_heur_code
  is \<open>uncurry (RETURN oo (PR_CONST clause_is_learned_heur))\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding clause_is_learned_heur_alt_def PR_CONST_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) clause_is_learned_heur_code
   uses isasat_input_bounded_nempty.clause_is_learned_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) clause_is_learned_heur_code_def

lemmas clause_is_learned_heur_code[sepref_fr_rules] =
   clause_is_learned_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

(* TODO deduplicate arena_lbd = get_clause_LBD *)
definition (in isasat_input_ops) clause_lbd_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat"
where
  \<open>clause_lbd_heur S C = arena_lbd (get_clauses_wl_heur S) C\<close>

lemma clause_lbd_heur_alt_def:
  \<open>clause_lbd_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . get_clause_LBD N' C)\<close>
  by (intro ext) (auto simp: clause_lbd_heur_def get_clause_LBD_def arena_lbd_def)

sepref_register clause_lbd_heur
sepref_thm clause_lbd_heur_code
  is \<open>uncurry (RETURN oo (PR_CONST clause_lbd_heur))\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding clause_lbd_heur_alt_def PR_CONST_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) clause_lbd_heur_code
   uses isasat_input_bounded_nempty.clause_lbd_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) clause_lbd_heur_code_def

lemmas clause_lbd_heur_code[sepref_fr_rules] =
   clause_lbd_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_register mark_garbage_heur
sepref_thm mark_garbage_heur_code
  is \<open>uncurry (RETURN oo (PR_CONST mark_garbage_heur))\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C)]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  unfolding mark_garbage_heur_def PR_CONST_def isasat_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) mark_garbage_heur_code
   uses isasat_input_bounded_nempty.mark_garbage_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) mark_garbage_heur_code_def

lemmas mark_garbage_heur_code[sepref_fr_rules] =
   mark_garbage_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]


sepref_register mark_to_delete_clauses_wl_D_heur
sepref_thm mark_to_delete_clauses_wl_D_heur_impl
  is \<open>PR_CONST mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def PR_CONST_def
    access_vdom_at_def[symmetric] length_vdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) mark_to_delete_clauses_wl_D_heur_impl
   uses isasat_input_bounded_nempty.mark_to_delete_clauses_wl_D_heur_impl.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) mark_to_delete_clauses_wl_D_heur_impl_def

lemmas mark_to_delete_clauses_wl_D_heur_impl[sepref_fr_rules] =
   mark_to_delete_clauses_wl_D_heur_impl.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register cdcl_twl_full_restart_wl_prog_heur
sepref_thm cdcl_twl_full_restart_wl_prog_heur_code
  is \<open>PR_CONST cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_full_restart_wl_prog_heur_code
   uses isasat_input_bounded_nempty.cdcl_twl_full_restart_wl_prog_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_full_restart_wl_prog_heur_code_def

lemmas cdcl_twl_full_restart_wl_prog_heur_code[sepref_fr_rules] =
   cdcl_twl_full_restart_wl_prog_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm cdcl_twl_restart_wl_heur_code
  is \<open>PR_CONST cdcl_twl_restart_wl_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_restart_wl_heur_code
   uses isasat_input_bounded_nempty.cdcl_twl_restart_wl_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_restart_wl_heur_code_def

lemmas cdcl_twl_restart_wl_heur_code[sepref_fr_rules] =
   cdcl_twl_restart_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(*
sepref_thm cdcl_twl_restart_wl_heur_fast_code
  is \<open>PR_CONST cdcl_twl_restart_wl_heur\<close>
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_restart_wl_heur_fast_code
   uses isasat_input_bounded_nempty.cdcl_twl_restart_wl_heur_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_restart_wl_heur_fast_code_def

lemmas cdcl_twl_restart_wl_heur_fast_code[sepref_fr_rules] =
   cdcl_twl_restart_wl_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
*)

sepref_register restart_required_heur cdcl_twl_restart_wl_heur
sepref_thm restart_wl_D_heur_slow_code
  is \<open>uncurry2 (PR_CONST restart_prog_wl_D_heur)\<close>
  :: \<open>isasat_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_assn *a nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) restart_wl_D_heur_slow_code
   uses isasat_input_bounded_nempty.restart_wl_D_heur_slow_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) restart_wl_D_heur_slow_code_def

lemmas restart_wl_D_heur_slow_code[sepref_fr_rules] =
   restart_wl_D_heur_slow_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(*
sepref_thm restart_prog_wl_D_heur_fast_code
  is \<open>uncurry2 (PR_CONST restart_prog_wl_D_heur)\<close>
  :: \<open>isasat_fast_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_fast_assn *a nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) restart_prog_wl_D_heur_fast_code
   uses isasat_input_bounded_nempty.restart_prog_wl_D_heur_fast_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) restart_prog_wl_D_heur_fast_code_def

lemmas restart_prog_wl_D_heur_fast_code[sepref_fr_rules] =
   restart_prog_wl_D_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
*)
sepref_register unit_propagation_outer_loop_wl_D_heur cdcl_twl_o_prog_wl_D_heur
  restart_prog_wl_D_heur

sepref_thm cdcl_twl_stgy_restart_prog_wl_heur_code
  is \<open>PR_CONST cdcl_twl_stgy_restart_prog_wl_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) cdcl_twl_stgy_restart_prog_wl_heur_code
   uses isasat_input_bounded_nempty.cdcl_twl_stgy_restart_prog_wl_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_restart_prog_wl_heur_code_def

lemmas cdcl_twl_stgy_restart_prog_wl_heur_hnr[sepref_fr_rules] =
   cdcl_twl_stgy_restart_prog_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

text \<open>TODO There is no fast mode yet!\<close>
(* sepref_thm cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>PR_CONST cdcl_twl_stgy_restart_prog_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>aisasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
    apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
           apply sepref_dbg_side_unfold apply (auto simp: )[]

  by sepref *)


end

export_code cdcl_twl_stgy_restart_prog_wl_heur_code in SML_imp module_name Test


end