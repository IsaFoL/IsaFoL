theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart IsaSAT_Setup IsaSAT_VMTF
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

lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

context isasat_input_bounded
begin
text \<open>
  We first fix the function that proves termination. We don't take the ``smallest'' function
  possible (other possibilites that are growing slower include \<^term>\<open>\<lambda>(n::nat). n >> 50\<close>).
\<close>
sublocale isasat_restart_bounded id
  by standard (rule unbounded_id)

definition find_local_restart_target_level_int_inv where
  \<open>find_local_restart_target_level_int_inv ns cs =
     (\<lambda>(brk, i). i \<le> length cs \<and> length cs < uint32_max)\<close>

definition find_local_restart_target_level_int :: \<open>trail_pol \<Rightarrow> vmtf_remove_int \<Rightarrow> nat nres\<close> where
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
   uses isasat_input_bounded.find_local_restart_target_level_code
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) find_local_restart_target_level_code_def

lemmas find_local_restart_target_level_code_def_hnr[sepref_fr_rules] =
   find_local_restart_target_level_code_def.refine

definition (in isasat_input_ops) find_local_restart_target_level where
  \<open>find_local_restart_target_level M _ = SPEC(\<lambda>i. i \<le> count_decided M)\<close>

lemma find_local_restart_target_level_alt_def:
  \<open>find_local_restart_target_level M vm = do {
      (b, i) \<leftarrow> SPEC(\<lambda>(b::bool, i). i \<le> count_decided M);
       RETURN i
    }\<close>
  unfolding find_local_restart_target_level_def by (auto simp: RES_RETURN_RES2 uncurry_def)

(* TODO Move and use! *)
lemma trail_pol_alt_def:
  \<open>trail_pol = {((M', xs, lvls, reasons, k, cs), M). ((M', reasons), M) \<in> ann_lits_split_reasons \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<and>
    control_stack cs M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
   length M < uint32_max \<and>
   length M \<le> uint32_max div 2 + 1 \<and>
   count_decided M < uint32_max \<and>
   length M' = length M \<and>
   M' = map lit_of (rev M)
   }\<close>
proof -
  have [intro!]: \<open>length M < n \<Longrightarrow> count_decided M < n\<close> for M n
    using length_filter_le[of is_decided M]
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def uint_max_def count_decided_def
        simp del: length_filter_le
        dest: length_trail_uint_max_div2)
  show ?thesis
    unfolding trail_pol_def
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def uint_max_def ann_lits_split_reasons_def
        dest: length_trail_uint_max_div2)
qed

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

definition (in isasat_input_ops) find_local_restart_target_level_st :: \<open>twl_st_wl_heur \<Rightarrow> nat nres\<close> where
  \<open>find_local_restart_target_level_st S =
     find_local_restart_target_level (get_trail_wl_heur S) (get_vmtf_heur S)\<close>

lemma find_local_restart_target_level_st_alt_def:
  \<open>find_local_restart_target_level_st = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats).
      find_local_restart_target_level M vm)\<close>
  apply (intro ext)
  apply (case_tac x)
  by (auto simp: find_local_restart_target_level_st_def)

definition (in isasat_input_ops) empty_Q :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>empty_Q = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats). do{
     RETURN (M, N, D, {#}, W, vm, \<phi>, clvls, cach, lbd, stats)
  })\<close>

definition (in isasat_input_ops) restart_abs_wl_heur_pre  :: \<open>twl_st_wl_heur \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_heur_pre S brk  \<longleftrightarrow> (\<exists>T. (S, T) \<in> twl_st_heur \<and> restart_abs_wl_D_pre T brk)\<close>


definition (in isasat_input_ops) cdcl_twl_local_restart_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_local_restart_wl_D_heur = (\<lambda>S. do {
      ASSERT(restart_abs_wl_heur_pre S False);
      lvl \<leftarrow> find_local_restart_target_level_st S;
      if lvl = count_decided (get_trail_wl_heur S)
      then RETURN S
      else do {
        S \<leftarrow> empty_Q S;
        ASSERT(find_decomp_w_ns_pre ((get_trail_wl_heur S, lvl), get_vmtf_heur S));
        find_decomp_wl_st_int lvl S
      }
   })\<close>

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

(* TODO Move *)
lemma no_dup_appendD1:
  \<open>no_dup (a @ b) \<Longrightarrow> no_dup a\<close>
  by (auto simp: no_dup_def)
(* End Move *)

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
    unfolding cdcl_twl_local_restart_wl_D_heur_def
      find_decomp_wl_st_int_def find_local_restart_target_level_def
      find_decomp_w_ns_def empty_Q_def find_local_restart_target_level_st_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_local_restart_wl_D_spec_int)
    unfolding bind_to_let_conv Let_def RES_RETURN_RES2
    apply (refine_vcg )
    subgoal unfolding restart_abs_wl_heur_pre_def by blast
    subgoal by auto
    subgoal
      by (force dest: restart_abs_wl_D_pre_find_decomp_w_ns_pre)
    subgoal
      by (rule RES_refine) (force simp: twl_st_heur_def intro!: )
    done
qed

definition remove_all_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> nat list \<Rightarrow> nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_inv S xs = (\<lambda>(i, T).
       \<exists>S' T'. (S, S') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
         remove_all_annot_true_clause_imp_wl_D_inv S' xs (i, T'))
     \<close>
definition remove_all_annot_true_clause_one_imp_heur
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, N). do {
      if C \<in># dom_m N then RETURN (fmdrop C N)
      else do {
        RETURN N
      }
  })\<close>

definition remove_all_annot_true_clause_imp_wl_D_heur_pre where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur \<and> remove_all_annot_true_clause_imp_wl_D_pre L S')\<close>

(* TODO: unfold Let when generating code! *)
definition remove_all_annot_true_clause_imp_wl_D_heur
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

definition minimum_number_between_restarts :: \<open>uint32\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

definition restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n =
    RETURN (
       ((get_slow_ema_heur S * 5) >> 2) > get_fast_ema_heur S \<and>
        get_conflict_count_heur S > minimum_number_between_restarts \<and>
        size (get_clauses_wl_heur S) > n)\<close>

definition cdcl_twl_restart_wl_heur where
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

end

end