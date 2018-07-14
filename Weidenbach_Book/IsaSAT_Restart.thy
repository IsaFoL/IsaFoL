theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart
     IsaSAT_CDCL
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
     \<^item> EMA-14, aka restart if enough clauses and slow_glue_avg * opts.restartmargin > fast_glue (file ema.cpp)
     \<^item> (lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts),
       \<^text>\<open>conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()\<close>
\<close>

declare dom_m_fmdrop[simp del]
lemma dom_m_fmdrop[simp]: \<open>dom_m (fmdrop C N) = removeAll_mset C (dom_m N)\<close>
  unfolding dom_m_def
  by (cases \<open>C |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq)

lemma butlast_Nil_iff: \<open>butlast xs = [] \<longleftrightarrow> length xs = 1 \<or> length xs = 0\<close>
  by (cases xs) auto

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

lemma (in -)mset_fset_empty_iff: \<open>mset_fset a = {#} \<longleftrightarrow> a = fempty\<close>
  by (cases a) (auto simp: mset_set_empty_iff)

lemma (in -) dom_m_empty_iff:
  \<open>dom_m NU = {#} \<longleftrightarrow> NU = fmempty\<close>
  by (cases NU) (auto simp: dom_m_def mset_fset_empty_iff)

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

lemma tight_domain_fmdrop: 
  \<open>0 \<notin># dom_m ba \<Longrightarrow> aa < length NU' - 1 \<Longrightarrow> tight_domain (fmdrop aa ba) NU' \<longleftrightarrow> tight_domain ba NU'\<close>
  by (auto simp: tight_domain_alt_def)

lemma tight_domain_fmdrop_last:
  \<open>0 \<notin># dom_m ba \<Longrightarrow> length NU' > 1 \<Longrightarrow> tight_domain ba NU' \<Longrightarrow> tight_domain (fmdrop (length NU' - 1) ba) (butlast NU')\<close>
  apply (auto simp: tight_domain_alt_def butlast_Nil_iff)
  oops

lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

global_interpretation twl_restart_ops id
  by unfold_locales

sublocale isasat_input_ops \<subseteq> isasat_restart_ops id
  .

context isasat_input_bounded_nempty
begin

definition (in -)butlast_if_last_removed where
  \<open>butlast_if_last_removed i N = (if i = length N-1 then butlast N else N)\<close>
definition (in -) fmdrop_ref where
  \<open>fmdrop_ref i = (\<lambda>(N, N'). do {
     ASSERT(i < length N \<and> i < length N' \<and> i > 0);
     let N = N[i := []];
     let N' = N'[i := (DELETED, 0, 0)];
     let N = butlast_if_last_removed i N;
     let N' = butlast_if_last_removed i N';
     RETURN (N, N')
  })\<close>
lemma (in -) butlast_if_last_removed_simps[simp]:
  \<open>aa = length b - 1 \<Longrightarrow> length (butlast_if_last_removed aa b) = length b -1\<close>
  \<open>aa \<noteq> length b - 1 \<Longrightarrow> length (butlast_if_last_removed aa b) = length b\<close>
  unfolding butlast_if_last_removed_def
  by auto

lemma
  \<open>(uncurry fmdrop_ref, uncurry (RETURN oo fmdrop)) \<in>
     [\<lambda>(i, xs). i \<in># dom_m xs \<and> i > 0 \<and> 0 \<notin># dom_m xs]\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  unfolding fmdrop_ref_def list_fmap_rel_def Let_def tight_domain_def[symmetric]
  apply (intro frefI nres_relI)
  apply (case_tac x; case_tac y)
  apply (simp only: prod.case in_pair_collect_simp prod_rel_iff uncurry_def
      RETURN_refine_iff comp_def)
  apply (intro conjI impI ballI ASSERT_refine_left)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply (subst RETURN_refine_iff)
  apply (simp only: prod.case in_pair_collect_simp prod_rel_iff uncurry_def
      RETURN_refine_iff comp_def)
  apply (intro conjI impI ballI ASSERT_refine_left allI)
  subgoal by (force simp: distinct_mset_remove1_All distinct_mset_dom butlast_if_last_removed_def)
  subgoal for x y a b c aa ba i
    by (auto simp: distinct_mset_remove1_All distinct_mset_dom nth_butlast butlast_if_last_removed_def
        dest!: multi_member_split[of i])
  subgoal for x y a b c aa ba i
    apply (cases \<open>aa = length c - Suc 0\<close>; cases \<open>i \<in># dom_m ba\<close>)
    subgoal
      by (clarsimp simp: )
    subgoal
      apply (clarsimp simp: butlast_if_last_removed_def)
      by (smt One_nat_def diff_is_0_eq diff_le_self le_trans length_butlast length_list_update
          neq0_conv nth_butlast nth_list_update_neq zero_less_diff)
    subgoal
      by (clarsimp simp: butlast_if_last_removed_def)
    subgoal
      apply (clarsimp simp: butlast_if_last_removed_def)
      by (smt One_nat_def diff_is_0_eq diff_le_self le_trans length_butlast length_list_update
          neq0_conv nth_butlast nth_list_update_neq zero_less_diff)
    done
  subgoal
    by (clarsimp simp add: butlast_Nil_iff butlast_if_last_removed_def)
  subgoal for x y a b c aa ba
    apply (cases \<open>aa = length c - Suc 0\<close>)
    apply (clarsimp_all simp add: tight_domain_fmdrop)
    sorry
  subgoal for x y a b c aa ba i
    by (auto simp: butlast_if_last_removed_def nth_butlast dest!: multi_member_split[of i])
  subgoal for x y a b c aa ba i
    by (auto simp: butlast_if_last_removed_def nth_butlast dest!: multi_member_split[of i])
  subgoal
    by (auto simp: butlast_if_last_removed_def)

    sorry
  oops
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x y a b c aa ba
    by (force simp add: distinct_mset_remove1_All distinct_mset_dom
        dest!: multi_member_split[of aa])
  subgoal for x y a b c aa ba i
    by (clarsimp simp add: distinct_mset_remove1_All distinct_mset_dom nth_butlast
        dest!: multi_member_split[of i])
  subgoal for x y a b c aa ba
    apply (clarsimp simp add: distinct_mset_remove1_All distinct_mset_dom nth_butlast
        dest!: multi_member_split[of aa])
    try0
    oops
    sorry

text \<open>
  We first fix the function that proves termination. We don't take the ``smallest'' function
  possible (other possibilites that are growing slower include \<^term>\<open>\<lambda>(n::nat). n >> 50\<close>).
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
     RETURN (M, N, D, {#}, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, 0, vdom, lcount)
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
        incr_restart_stat S
      }
   })\<close>


sepref_thm empty_Q_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_assn_def IICF_List_Mset.lms_fold_custom_empty
  by sepref

concrete_definition (in -) empty_Q_code
   uses isasat_input_bounded_nempty.empty_Q_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) empty_Q_code_def

lemmas empty_Q_hnr [sepref_fr_rules] =
   empty_Q_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_fast_assn_def IICF_List_Mset.lms_fold_custom_empty
  by sepref

concrete_definition (in -) empty_Q_fast_code
   uses isasat_input_bounded_nempty.empty_Q_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) empty_Q_fast_code_def
lemmas empty_Q_fast_hnr [sepref_fr_rules] =
   empty_Q_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

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

named_theorems twl_st_heur

lemma [twl_st_heur]:
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
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close> and
    Tx: \<open>(T, x) \<in> state_wl_l None\<close> and
    \<open>partial_correct_watching T\<close> and
    xxa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs xa\<close> and
    \<open>twl_list_invs x\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>twl_stgy_invs xa\<close> and
    \<open>get_conflict xa = None\<close>
    using pre unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by blast
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl_heur S)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail[OF Tx struct xxa lits] ST
    by (auto simp add: twl_st_heur)
  moreover have \<open> get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S)\<close>
    using ST by (auto simp add: twl_st_heur_def)
  moreover have \<open>no_dup (get_trail_wl_heur S)\<close>
    using struct ST Tx xxa unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
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
      find_decomp_wl_st_int_def find_local_restart_target_level_def incr_restart_stat_def
      find_decomp_w_ns_def empty_Q_def find_local_restart_target_level_st_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_local_restart_wl_D_spec_int)
    unfolding bind_to_let_conv Let_def RES_RETURN_RES2
    apply (refine_vcg )
    subgoal unfolding restart_abs_wl_heur_pre_def by blast
    subgoal by (force simp: twl_st_heur_def)
    subgoal by auto
    subgoal
      by (force dest: restart_abs_wl_D_pre_find_decomp_w_ns_pre)
    subgoal
      unfolding RETURN_def
      by (rule RES_refine) (auto 5 5 simp: twl_st_heur_def)
    done
qed

definition(in isasat_input_ops)  remove_all_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> nat list \<Rightarrow> nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_inv S xs = (\<lambda>(i, T).
       \<exists>S' T'. (S, S') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
         remove_all_annot_true_clause_imp_wl_D_inv S' xs (i, T'))
     \<close>

definition (in isasat_input_ops) remove_all_annot_true_clause_one_imp_heur
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, N). do {
      if C \<in># dom_m N then RETURN (fmdrop C N)
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
        if xs!i \<in># dom_m N
        then do {
          N \<leftarrow> remove_all_annot_true_clause_one_imp_heur (xs!i, N);
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


definition (in -) restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n = do {
    let sema = get_slow_ema_heur S;
    let sema' = (five_uint64 * get_slow_ema_heur S) >> 2;
       \<comment>\<open>roughly speaking 125/100 with hopefully no overflow\<close>
    let fema = get_fast_ema_heur S;
    
    let ccount = get_conflict_count_heur S ;
    let lcount = get_learned_count S;
    let can_res = (lcount > n );
    let min_reached = (ccount > minimum_number_between_restarts);
    RETURN (sema' > fema \<and> min_reached \<and> can_res)}
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

definition (in isasat_input_ops) cdcl_twl_restart_wl_heur where
\<open>cdcl_twl_restart_wl_heur S = do {
   cdcl_twl_local_restart_wl_D_heur S
  }\<close>

lemma cdcl_twl_restart_wl_heur_alt_def:
  \<open>cdcl_twl_restart_wl_heur S = do {
   let b = True;
   if b then cdcl_twl_local_restart_wl_D_heur S else cdcl_twl_local_restart_wl_D_heur S
  }\<close>
  unfolding cdcl_twl_restart_wl_heur_def by auto

lemma cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog:
  \<open>(cdcl_twl_restart_wl_heur, cdcl_twl_restart_wl_D_prog) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_D_prog_def cdcl_twl_restart_wl_heur_alt_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
    cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec[THEN fref_to_Down])
  subgoal by auto
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