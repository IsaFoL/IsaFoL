theory IsaSAT_Restart_Reduce
imports IsaSAT_Restart IsaSAT_Restart_Reduce_Defs
begin

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
     [\<lambda>(M, vm). vm \<in> bump_heur \<A> M]\<^sub>f trail_pol \<A> \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_alt_def
    uncurry_def Let_def
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for a aa ab ac ad b ba ae bb
    unfolding access_focused_vmtf_array_def nres_monad3 bind_to_let_conv Let_def
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
            vmtf_def atms_of_def isa_vmtf_def bump_heur_def bump_get_heuristics_def
          intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l)
    subgoal by (auto simp: find_local_restart_target_level_int_inv_def)
    subgoal by (auto simp: trail_pol_alt_def control_stack_length_count_dec
          find_local_restart_target_level_int_inv_def)
    subgoal by auto
    done
  done

lemma find_local_restart_target_level_st_alt_def:
  \<open>find_local_restart_target_level_st = (\<lambda>S. do {
      find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S)})\<close>
 apply (intro ext)
  by (auto simp: find_local_restart_target_level_st_def)

lemma cdcl_twl_local_restart_wl_D_spec_int:
  \<open>cdcl_twl_local_restart_wl_spec (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<ge> ( do {
      ASSERT(\<exists>last_GC last_Restart. restart_abs_wl_pre (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) last_GC last_Restart False);
      i \<leftarrow> SPEC(\<lambda>_. True);
      if i
      then RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)
      else do {
        (M, Q') \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
              Q' = {#}) \<or> (M' = M \<and> Q' = Q));
        RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q', W)
     }
   })\<close>
proof -
  have If_Res: \<open>(if i then (RETURN f) else (RES g)) = (RES (if i then {f} else g))\<close> for i f g
    by auto
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_spec_def prod.case RES_RETURN_RES2 If_Res
    by refine_vcg
      (auto simp: If_Res RES_RETURN_RES2 RES_RES_RETURN_RES uncurry_def
        image_iff split:if_splits)
qed

lemma cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec:
  \<open>(cdcl_twl_local_restart_wl_D_heur, cdcl_twl_local_restart_wl_spec) \<in>
    twl_st_heur''''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur''''u r u\<rangle>nres_rel\<close>
proof -
  have K: \<open>(do {
    j \<leftarrow> mop_isa_length_trail (get_trail_wl_heur S);
    RES {f j}
    }) = (do {
    ASSERT (isa_length_trail_pre (get_trail_wl_heur S));
    RES {f (isa_length_trail (get_trail_wl_heur S))}})\<close> for S :: isasat and f
    by (cases S) (auto simp: mop_isa_length_trail_def)
  have K2: \<open>(case S of
               (a, b) \<Rightarrow> RES (\<Phi> a b)) =
        (RES (case S of (a, b) \<Rightarrow> \<Phi> a b))\<close> for S
  by (cases S) auto

  have [dest]: \<open>av = None\<close> \<open>out_learned a av am \<Longrightarrow> out_learned x1 av am\<close>
    if \<open>restart_abs_wl_pre (a, au, av, aw, ax, NEk, UEk, NS, US, N0, U0, ay, bd) last_GC last_Restart False\<close>
    for a au av aw ax ay bd x1 am NEk UEk NS US last_GC last_Restart N0 U0
    using that
    unfolding restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by (auto simp: twl_st_l_def state_wl_l_def out_learned_def)
  have [refine0]:
    \<open>find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S) \<le>
      \<Down> {(i, b). b = (i = count_decided (get_trail_wl T)) \<and>
          i \<le> count_decided (get_trail_wl T)} (SPEC (\<lambda>_. True))\<close>
    if \<open>(S, T) \<in> twl_st_heur\<close> for S T
    apply (rule find_local_restart_target_level_int_find_local_restart_target_level[THEN
         fref_to_Down_curry, THEN order_trans, of \<open>all_atms_st T\<close> \<open>get_trail_wl T\<close> \<open>get_vmtf_heur S\<close>])
    subgoal using that unfolding twl_st_heur_def by auto
    subgoal using that unfolding twl_st_heur_def by auto
    subgoal by (auto simp: find_local_restart_target_level_def conc_fun_RES)
    done
  have H:
      \<open>set_mset (all_atms_st S) =
           set_mset (all_init_atms_st S)\<close> (is ?A)
      \<open>set_mset (all_atms_st S) =
           set_mset (all_atms (get_clauses_wl S) (get_unit_clauses_wl S + get_subsumed_init_clauses_wl S + get_init_clauses0_wl S))\<close>
           (is ?B)
      \<open>get_conflict_wl S = None\<close> (is ?C)
     if pre: \<open>restart_abs_wl_pre S last_GC last_Restart False\<close>
       for S last_GC last_Restart
  proof -
    obtain T U where
      ST: \<open>(S, T) \<in> state_wl_l None\<close> and
      \<open>correct_watching S\<close> and
      \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
      TU: \<open>(T, U) \<in> twl_st_l None\<close> and
      struct: \<open>twl_struct_invs U\<close> and
      \<open>twl_list_invs T\<close> and
      \<open>clauses_to_update_l T = {#}\<close> and
      \<open>twl_stgy_invs U\<close> and
      confl: \<open>get_conflict U = None\<close>
      using pre unfolding restart_abs_wl_pre_def restart_abs_l_pre_def restart_prog_pre_def apply -
      by blast

   show ?C
     using ST TU confl by auto

   have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
     using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       pcdcl_all_struct_invs_def state\<^sub>W_of_def
     by fast+
   then show ?A and ?B
      subgoal A
        using ST TU unfolding set_eq_iff in_set_all_atms_iff
          in_set_all_atms_iff in_set_all_init_atms_iff get_unit_clauses_wl_alt_def
          using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3) struct by blast
      subgoal
        using ST TU alien unfolding set_eq_iff in_set_all_atms_iff all_atms_st_def
          in_set_all_atms_iff in_set_all_init_atms_iff get_unit_clauses_wl_alt_def
        apply (subst all_clss_lf_ran_m[symmetric])
        apply (subst all_clss_lf_ran_m[symmetric])
        unfolding image_mset_union
        by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def twl_st twl_st_l in_set_all_atms_iff
          in_set_all_init_atms_iff)
     done
  qed
  have P: \<open>P\<close>
    if
      ST: \<open>(S, bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz)
       \<in> twl_st_heur\<close> and
      \<open>\<exists>last_GC last_Restart. restart_abs_wl_pre (bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz) last_GC last_Restart False\<close> and
      \<open>restart_abs_wl_heur_pre
	S
	False\<close> and
      lvl: \<open>(lvl, i)
       \<in> {(i, b).
	  b = (i = count_decided (get_trail_wl (bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz))) \<and>
	  i \<le> count_decided (get_trail_wl (bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz))}\<close> and
      \<open>i \<in> {_. True}\<close> and
      \<open>lvl \<noteq> count_decided_st_heur S\<close> and
      i: \<open>\<not> i\<close> and
    H: \<open>
      isa_find_decomp_wl_imp (get_trail_wl_heur S) lvl (get_vmtf_heur S)
	\<le> \<Down> {(a, b). (a,b) \<in> trail_pol (all_atms_st (bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz)) \<times>\<^sub>f Id}
	    (find_decomp_w_ns (all_atms_st (bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz)) bt lvl vm0) \<Longrightarrow> P\<close>
    for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao aq bd ar as at'
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq bt bu bv aqbd
       bw bx "by" bz lvl i x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f S
       x1g x2g x1h x2h x1i x2i P NS US last_GC last_Restart N0 U0 NEk UEk heur heur2 stats M' stats42
  proof -
    let ?\<A> = \<open>all_atms_st (bt, bu, bv, bw, bx, NEk, UEk, NS, US, N0, U0, by, bz)\<close>
    let ?bo = \<open>get_vdom_aivdom (get_aivdom S)\<close>
    let ?ae = \<open>get_clauses_wl_heur S\<close>
    let ?heur = \<open>get_heur S\<close>
    let ?vm = \<open>get_vmtf_heur S\<close>
    have
      tr: \<open>(get_trail_wl_heur S, bt) \<in> trail_pol ?\<A>\<close> and
      \<open>valid_arena ?ae bu (set ?bo)\<close> and
      vm: \<open>?vm \<in> bump_heur ?\<A> bt\<close> and (*
      \<open>(heur, bv)
       \<in> option_lookup_clause_rel ?\<A>\<close> and
      \<open>by = {#- lit_of x. x \<in># mset (drop ah (rev bt))#}\<close> and
      \<open>(ai, bz) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 ?\<A>)\<close> and
      \<open>no_dup bt\<close> and
      \<open>ao \<in> counts_maximum_level bt bv\<close> and
      \<open>cach_refinement_empty ?\<A> aqbd\<close> and
      \<open>out_learned bt bv as\<close> and
      \<open>clss_size_corr bu bw bx NEk UEk NS US N0 U0 bp\<close> and
      \<open>vdom_m ?\<A> bz bu \<subseteq> set ?bo\<close> and
      \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>. nat_of_lit L \<le> unat32_max\<close> and
      \<open>?\<A> \<noteq> {#}\<close> and*)
      bounded: \<open>isasat_input_bounded ?\<A>\<close> and
      heur: \<open>heuristic_rel ?\<A> ?heur\<close>
      using ST unfolding twl_st_heur_def all_atms_def
      by (auto)

    have n_d: \<open>no_dup bt\<close>
      using tr by (auto simp: trail_pol_def)
    show ?thesis
      apply (rule H)
      apply (rule isa_find_decomp_wl_imp_find_decomp_wl_imp[THEN fref_to_Down_curry2, THEN order_trans,
        of bt lvl \<open>get_vmtf_heur S\<close> _ _ _ \<open>?\<A>\<close>])
      subgoal using lvl i by auto
      subgoal using vm tr by auto
      apply (subst (3) Down_id_eq[symmetric])
      apply (rule order_trans)
      apply (rule ref_two_step')
      apply (rule find_decomp_wl_imp_find_decomp_wl'[THEN fref_to_Down_curry2, of _ bt lvl \<open>get_vmtf_heur S\<close>])
      subgoal
        using that(1-8) vm bounded n_d tr
	by (auto simp: find_decomp_w_ns_pre_def dest: trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
      subgoal by auto
        using ST
        by (auto simp: find_decomp_w_ns_def conc_fun_RES twl_st_heur_def)
  qed
  note cong =  trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong heuristic_rel_cong

  show ?thesis
    supply [[goals_limit=1]]
    unfolding cdcl_twl_local_restart_wl_D_heur_def
    unfolding
      find_decomp_wl_st_int_def find_local_restart_target_level_def incr_restart_stat_def
       empty_Q_def find_local_restart_target_level_st_def nres_monad_laws
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule ref_two_step)
    prefer 2
     apply (rule cdcl_twl_local_restart_wl_D_spec_int)
    unfolding bind_to_let_conv RES_RETURN_RES2 nres_monad_laws Let_def
    apply (refine_vcg)
    subgoal unfolding restart_abs_wl_heur_pre_def by blast
    apply assumption
    subgoal by (simp add: twl_st_heur_count_decided_st_alt_def)
    subgoal by (auto simp: twl_st_heur_def count_decided_st_heur_def trail_pol_def)

    apply (rule P)
    apply assumption+
      apply (rule refine_generalise1)
      apply assumption
    subgoal for a aa ab ac ad b ae af ag ba ah ai aj ak al az
      unfolding RETURN_def RES_RES2_RETURN_RES RES_RES13_RETURN_RES find_decomp_w_ns_def conc_fun_RES
        RES_RES13_RETURN_RES K2 K
      apply (auto simp: intro_spec_iff intro!: ASSERT_leI isa_length_trail_pre)
      apply (auto simp: isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
        intro: trail_pol_no_dup)
      apply (frule twl_st_heur_change_subsumed_clauses[where US' = ba and NS' = ag and
        lcount' = \<open>get_learned_count a\<close>])
      apply (solves \<open>auto dest: H(2)\<close>)[]
      apply (solves \<open>auto simp: twl_st_heur_def\<close>)[]
      apply (frule H(2))
      apply (frule H(3))
	apply (clarsimp simp: twl_st_heur_def)
	apply (rule_tac x=aea in exI)
	apply (auto simp: isa_length_trail_length_u[THEN fref_to_Down_unRET_Id] learned_clss_count_def
          all_atms_st_def
	  intro: trail_pol_no_dup)
      done
    done
qed



lemma distinct_mset_union_iff:
  \<open>distinct_mset (xs + ys) = (distinct_mset xs \<and> distinct_mset ys \<and> set_mset xs \<inter> set_mset ys = {})\<close>
  by (induction xs) (auto)

lemma aivdom_inv_dec_remove_deleted_clauses_from_avdom:
  \<open>aivdom_inv_dec avdom0 (dom_m N) \<Longrightarrow>
  mset (take a (get_avdom_aivdom ba)) \<subseteq># mset (get_avdom_aivdom avdom0) \<Longrightarrow>
    mset (take a (get_avdom_aivdom ba)) \<inter># dom_m N = mset (get_avdom_aivdom avdom0) \<inter># dom_m N \<Longrightarrow>
    get_vdom_aivdom ba = get_vdom_aivdom avdom0 \<Longrightarrow>
    get_ivdom_aivdom ba = get_ivdom_aivdom avdom0 \<Longrightarrow>
  mset (get_tvdom_aivdom ba) \<subseteq># mset (get_avdom_aivdom avdom0) \<Longrightarrow>
  mset (take a (get_avdom_aivdom ba)) \<inter># dom_m N = mset (get_avdom_aivdom avdom0) \<inter># dom_m N \<Longrightarrow>
  aivdom_inv_dec (take_avdom_aivdom a ba) (dom_m N)\<close>
 supply [simp del] = distinct_finite_set_mset_subseteq_iff
 using distinct_mset_mono[of \<open>mset (take a (get_avdom_aivdom ba))\<close> \<open>mset (get_avdom_aivdom avdom0)\<close>]
 apply (auto simp: aivdom_inv_dec_alt_def2 distinct_mset_mono intro: distinct_take
   simp flip: distinct_subseteq_iff)
 apply auto
 apply (metis UnE comp_apply in_mono inter_iff set_mset_comp_mset)
 apply (subst distinct_subseteq_iff[symmetric])
 apply (auto dest: distinct_mset_mono)
 by (metis mset_subset_eqD set_mset_mset subsetD)

lemma remove_deleted_clauses_from_avdom:
  assumes \<open>aivdom_inv_dec avdom0 (dom_m N)\<close>
  shows \<open>remove_deleted_clauses_from_avdom N avdom0 \<le> SPEC(\<lambda>aivdom. aivdom_inv_dec aivdom (dom_m N) \<and>
     get_vdom_aivdom aivdom = get_vdom_aivdom avdom0\<and>
     get_ivdom_aivdom aivdom = get_ivdom_aivdom avdom0\<and>
    mset (get_tvdom_aivdom aivdom) \<subseteq># mset (get_avdom_aivdom avdom0) \<and>
   (\<forall>C \<in> set (get_tvdom_aivdom aivdom). C \<in># dom_m N \<and> \<not>irred N C \<and> length (N \<propto> C) \<noteq> 2))\<close>
proof -
  have dist_avdom: \<open>distinct (get_avdom_aivdom avdom0)\<close>
    using assms by (auto simp: aivdom_inv_dec_alt_def2)
  have I0: \<open>remove_deleted_clauses_from_avdom_inv N avdom0 (0, 0, empty_tvdom avdom0)\<close>
    unfolding remove_deleted_clauses_from_avdom_inv_def by auto
  have ISuc_keep:
    \<open>x \<Longrightarrow> remove_deleted_clauses_from_avdom_inv N avdom0
    (a+1, aa + 1, push_to_tvdom (get_avdom_aivdom ba ! aa) (swap_avdom_aivdom ba a aa))\<close> (is \<open>_ \<Longrightarrow> ?A\<close>) and
    ISuc_keep_no:
    \<open>remove_deleted_clauses_from_avdom_inv N avdom0
    (a+1, aa + 1,  (swap_avdom_aivdom ba a aa))\<close> (is ?B)
    if
      \<open>remove_deleted_clauses_from_avdom_inv N avdom0 s\<close> and
      \<open>case s of (i, j, avdom) \<Rightarrow> j < length (get_avdom_aivdom avdom0)\<close> and
      \<open>s = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>get_avdom_aivdom ba ! aa \<in># dom_m N\<close> and
      irred: \<open>x \<longrightarrow> \<not> irred N (get_avdom_aivdom ba ! aa) \<and> length (N \<propto> (get_avdom_aivdom ba ! aa)) \<noteq> 2\<close>
    for ba aa s a b x
  proof -
    have [simp]: \<open>aa < length (get_avdom_aivdom ba) \<Longrightarrow>
      add_mset (get_avdom_aivdom ba ! aa) (mset (take aa (get_avdom_aivdom ba)) + mset (drop (Suc aa) (get_avdom_aivdom ba))) =
      mset (get_avdom_aivdom ba)\<close>
      using that apply -
      apply (subst (4)append_take_drop_id[symmetric, of \<open>get_avdom_aivdom ba\<close> aa])
      apply (subst mset_append)
      by (auto simp flip: Cons_nth_drop_Suc)
    have 1: \<open>distinct (take a (get_avdom_aivdom ba) @ drop aa (get_avdom_aivdom ba))\<close>
      using assms that
        distinct_mset_mono[of \<open>mset (take a (get_avdom_aivdom ba) @ drop aa (get_avdom_aivdom ba))\<close>
        \<open>mset (get_avdom_aivdom avdom0)\<close>]
      by (auto simp: aivdom_inv_dec_alt_def2 remove_deleted_clauses_from_avdom_inv_def distinct_mset_union_iff)
    have 2: \<open>a = aa  \<Longrightarrow>distinct (get_avdom_aivdom ba)\<close>
      by (metis \<open>distinct (take a (get_avdom_aivdom ba) @ drop aa (get_avdom_aivdom ba))\<close> append_take_drop_id)

    show \<open>x \<Longrightarrow> ?A\<close>
      using assms that dist_avdom 1 2 apply -
      apply (cases \<open>Suc a \<le> aa\<close>)
      unfolding remove_deleted_clauses_from_avdom_inv_def prod.simps
      apply (auto simp: drop_swap_irrelevant swap_only_first_relevant Suc_le_eq take_update_last remove_deleted_clauses_from_avdom_inv_def
        intro: subset_mset.dual_order.trans 
        simp flip:  take_Suc_conv_app_nth Cons_nth_drop_Suc)
      apply (auto simp: take_Suc_conv_app_nth)
      done
    show ?B
      using 1 2  assms that dist_avdom 
      apply (cases \<open>Suc a \<le> aa\<close>)
      unfolding remove_deleted_clauses_from_avdom_inv_def prod.simps
      apply (auto simp: drop_swap_irrelevant swap_only_first_relevant Suc_le_eq take_update_last remove_deleted_clauses_from_avdom_inv_def
        intro: subset_mset.dual_order.trans 
        simp flip:  take_Suc_conv_app_nth Cons_nth_drop_Suc)
      apply (auto simp: take_Suc_conv_app_nth)
      done
qed
  have ISuc_nokeep:
    \<open>remove_deleted_clauses_from_avdom_inv N avdom0
    (a, aa + 1, ba)\<close> (is ?A)
    if
      \<open>remove_deleted_clauses_from_avdom_inv N avdom0 s\<close> and
      \<open>case s of (i, j, avdom) \<Rightarrow> j < length (get_avdom_aivdom avdom0)\<close> and
      \<open>s = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>get_avdom_aivdom ba ! aa \<notin># dom_m N\<close>
    for ba aa s a b
  proof -
    have \<open>aa < length (get_avdom_aivdom ba) \<Longrightarrow>
      add_mset (get_avdom_aivdom ba ! aa) (mset (take aa (get_avdom_aivdom ba)) + mset (drop (Suc aa) (get_avdom_aivdom ba))) =
      mset (get_avdom_aivdom ba)\<close>
      using that apply -
      apply (subst (4)append_take_drop_id[symmetric, of \<open>get_avdom_aivdom ba\<close> aa])
      apply (subst mset_append)
      by (auto simp flip: Cons_nth_drop_Suc)
    have \<open>distinct (take a (get_avdom_aivdom ba) @ drop aa (get_avdom_aivdom ba))\<close>
      using assms that
        distinct_mset_mono[of \<open>mset (take a (get_avdom_aivdom ba) @ drop aa (get_avdom_aivdom ba))\<close>
        \<open>mset (get_avdom_aivdom avdom0)\<close>]
      by (auto simp: aivdom_inv_dec_alt_def2 remove_deleted_clauses_from_avdom_inv_def distinct_mset_union_iff)
    moreover have \<open>a = aa  \<Longrightarrow>distinct (get_avdom_aivdom ba)\<close>
      by (metis \<open>distinct (take a (get_avdom_aivdom ba) @ drop aa (get_avdom_aivdom ba))\<close> append_take_drop_id)

    ultimately show ?A
      using assms that dist_avdom apply -
      apply (cases \<open>Suc a \<le> aa\<close>)
      unfolding remove_deleted_clauses_from_avdom_inv_def prod.simps
      by (auto simp: drop_swap_irrelevant swap_only_first_relevant Suc_le_eq take_update_last remove_deleted_clauses_from_avdom_inv_def
        intro: subset_mset.dual_order.trans subset_mset_trans_add_mset
        simp flip:  take_Suc_conv_app_nth Cons_nth_drop_Suc)
  qed

  show ?thesis
    using assms
    unfolding remove_deleted_clauses_from_avdom_def Let_def is_candidate_for_removal_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, j, avdom). length (get_avdom_aivdom avdom) - j)\<close>])
    subgoal by auto
    subgoal by (rule I0)
    subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
    subgoal supply [[unify_trace_failure]] by (rule ISuc_keep)
    subgoal by auto
    subgoal by (rule ISuc_keep_no)
    subgoal by auto
    subgoal by (rule ISuc_nokeep)
    subgoal by (auto simp: aivdom_inv_dec_alt_def)
    subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
    subgoal by (force intro!: aivdom_inv_dec_remove_deleted_clauses_from_avdom
      simp: remove_deleted_clauses_from_avdom_inv_def simp flip: distinct_subseteq_iff)
    subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
    subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
    subgoal by (force simp: remove_deleted_clauses_from_avdom_inv_def simp flip: distinct_subseteq_iff)
    subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
    done
qed

(*TODO Move*)
lemma arena_status_mark_unused[simp]:
  \<open>arena_status (mark_unused arena C) D = arena_status arena D\<close>
  by (auto simp: arena_status_def mark_unused_def LBD_SHIFT_def
    nth_list_update')


lemma isa_is_candidate_for_removal_is_candidate_for_removal:
  assumes
    valid: \<open>valid_arena arena N vdom\<close> and
    C: \<open>(C, C') \<in> nat_rel\<close> and
    MM': \<open>(M, M') \<in> trail_pol \<A>\<close> and
    \<A>: \<open>set_mset (all_atms N NUE) = set_mset \<A>\<close>
  shows \<open>isa_is_candidate_for_removal M C arena \<le> \<Down> bool_rel (is_candidate_for_removal C' N)\<close>
proof -
  have [simp]: \<open>C \<in># dom_m N \<Longrightarrow> N \<propto> C \<noteq> []\<close> and
    C'[simp]: \<open>C' = C\<close>
    using valid C by (auto simp: valid_arena_nempty)
  have 1: \<open>C \<in># dom_m N \<Longrightarrow> atm_of (arena_lit arena C) \<in># \<A>\<close>
    using valid \<A>
    by (cases \<open>N \<propto> C\<close>)
     (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def
      arena_lifting arena_dom_status_iff(1)
      arena_lit_pre_def all_atms_def all_lits_def
      ran_m_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
      simp flip: arena_lifting
      dest: valid_arena_nempty
      dest!: multi_member_split)
  have 2: \<open>C \<in># dom_m N \<Longrightarrow>  (arena_lit arena C) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    using 1 by (cases \<open>arena_lit arena C\<close>) (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset dest!: multi_member_split)
  have [simp]: \<open>get_clause_LBD_pre arena C\<close>  \<open>arena_act_pre arena C\<close>
    \<open>arena_is_valid_clause_vdom arena C\<close> \<open>marked_as_used_pre arena C\<close>
    if \<open>C \<in># dom_m N\<close>
    using valid that by (auto simp: get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      arena_act_pre_def arena_is_valid_clause_vdom_def marked_as_used_pre_def)
  show ?thesis
    using 1 2 valid MM'
    unfolding isa_is_candidate_for_removal_def is_candidate_for_removal_def
      get_the_propagation_reason_pol_def mop_arena_lbd_def
      mop_arena_status_def mop_marked_as_used_def Let_def
    by (refine_vcg mop_arena_lit(1)
      mop_arena_length[THEN fref_to_Down_curry, THEN order_trans,of N C _ C vdom])
     (auto simp:
      arena_lifting arena_dom_status_iff(1) trail_pol_alt_def
      ann_lits_split_reasons_def
      intro: exI[of _ \<open>C::nat\<close>] exI[of _ vdom]
      dest: valid_arena_nempty)
qed


lemma isa_gather_candidates_for_reduction_remove_deleted_clauses_from_avdom:
  \<open>valid_arena arena N (set vdom) \<Longrightarrow> mset (get_avdom_aivdom avdom0) \<subseteq># mset vdom \<Longrightarrow>
  (M, M') \<in> trail_pol \<A> \<Longrightarrow> set_mset (all_atms N NUE) = set_mset \<A> \<Longrightarrow>
  length (get_avdom_aivdom avdom0) \<le> length (get_vdom_aivdom avdom0) \<Longrightarrow>
  distinct vdom \<Longrightarrow>
  isa_gather_candidates_for_reduction M arena avdom0 \<le>
  \<Down>{((arena', st), st'). (st, st') \<in> Id \<and> length arena' = length arena \<and> valid_arena arena' N (set vdom)}
  (remove_deleted_clauses_from_avdom N avdom0)\<close>
  unfolding isa_gather_candidates_for_reduction_def remove_deleted_clauses_from_avdom_def Let_def
  apply (refine_vcg WHILEIT_refine[where R= \<open>{((arena', st), st'). (st, st') \<in> Id \<and> length arena' = length arena \<and> valid_arena arena' N (set vdom)}\<close>]
    )
  subgoal by (auto dest!: valid_arena_vdom_le(2) size_mset_mono simp: distinct_card)
  subgoal by auto
  subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
  subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
  subgoal by auto
  subgoal by auto
  subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c unfolding arena_is_valid_clause_vdom_def
    apply (auto intro!: exI[of _ N] exI[of _ \<open>set vdom\<close>] dest!: mset_eq_setD dest: mset_le_add_mset
      simp: Cons_nth_drop_Suc[symmetric] remove_deleted_clauses_from_avdom_inv_def)
    by (meson in_multiset_in_set mset_subset_eqD union_single_eq_member)
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: remove_deleted_clauses_from_avdom_inv_def)
  subgoal
    apply (auto simp: arena_lifting arena_dom_status_iff(1) Cons_nth_drop_Suc[symmetric] remove_deleted_clauses_from_avdom_inv_def
      dest!: mset_eq_setD dest: mset_le_add_mset)
    by (metis arena_dom_status_iff(1) mset_subset_eqD set_mset_mset union_single_eq_member)
  subgoal by (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def)
    apply (rule isa_is_candidate_for_removal_is_candidate_for_removal; assumption?; auto intro!: valid_arena_mark_unused; fail)
  subgoal by auto
  subgoal by (auto intro!: valid_arena_mark_unused)
  subgoal by (auto intro!: valid_arena_mark_unused)
  subgoal by (auto intro!: valid_arena_mark_unused)
  subgoal by (auto intro!: valid_arena_mark_unused)
  subgoal by (auto intro!: valid_arena_mark_unused)
  done

(*TODO Move*)
lemma bind_result_subst_iff:
  \<open>P \<le> \<Down> {(a,b). (f a, b) \<in> R} g \<longleftrightarrow>
  do {
  a \<leftarrow> P;
  RETURN (f a)
  } \<le> \<Down> R g\<close>
  by (cases P; cases g)
   (auto simp: RETURN_def RES_RES_RETURN_RES conc_fun_RES)

lemma isa_isa_gather_candidates_for_reduction_remove_deleted_clauses_from_avdom2:
  assumes \<open>valid_arena arena N (set (get_vdom_aivdom avdom))\<close>
    \<open>aivdom_inv_dec avdom (dom_m N)\<close> and
    MM': \<open>(M, M') \<in> trail_pol \<A>\<close> and
    \<A>: \<open>set_mset (all_atms N NUE) = set_mset \<A>\<close>
 shows
  \<open>isa_gather_candidates_for_reduction M arena avdom \<le>
   (SPEC (\<lambda>(arena', aivdom). aivdom_inv_dec aivdom (dom_m N) \<and>
     get_vdom_aivdom aivdom = get_vdom_aivdom avdom\<and>
     get_ivdom_aivdom aivdom = get_ivdom_aivdom avdom\<and>
     mset (get_tvdom_aivdom aivdom) \<subseteq># mset (get_avdom_aivdom avdom) \<and>
   valid_arena arena' N (set (get_vdom_aivdom avdom)) \<and>
   length arena' = length arena \<and>
   (\<forall>C \<in> set (get_tvdom_aivdom aivdom). C \<in># dom_m N \<and> \<not>irred N C \<and> length (N \<propto> C) \<noteq> 2)))\<close>
proof -
  have i: \<open>mset (get_avdom_aivdom avdom) \<subseteq># mset (get_vdom_aivdom avdom)\<close>
    \<open>distinct (get_vdom_aivdom avdom)\<close>
    \<open>length (get_avdom_aivdom avdom) \<le> length (get_vdom_aivdom avdom)\<close>
    using assms(2) by (auto simp: aivdom_inv_dec_alt_def dest: size_mset_mono)
  have H: \<open>aivdom_inv (get_vdom_aivdom avdom, get_avdom_aivdom avdom, get_ivdom_aivdom avdom, get_tvdom_aivdom avdom) (dom_m N)\<close>
    using assms(2) by (cases avdom) (auto simp: aivdom_inv_dec_def simp del: aivdom_inv.simps)
  show ?thesis
    apply (rule order_trans)
    apply (rule isa_gather_candidates_for_reduction_remove_deleted_clauses_from_avdom)
    apply (rule assms i)+
    apply (rule order_trans)
    apply (rule ref_two_step'[OF remove_deleted_clauses_from_avdom])
    apply (rule assms)
    apply (auto simp: conc_fun_RES)
    done
qed

lemma mset_inter_eqD: \<open>x1m \<inter># af = xa \<inter># af \<Longrightarrow>
    set_mset x1m \<inter> set_mset (af) = set_mset xa \<inter> set_mset af\<close> for x1m af xa
    by auto
      (metis Int_iff comp_apply set_mset_comp_mset set_mset_inter)+

lemma aivdom_inv_cong2:
  \<open>mset vdom = mset vdom' \<Longrightarrow> mset avdom = mset avdom' \<Longrightarrow> mset ivdom = mset ivdom' \<Longrightarrow> mset tvdom = mset tvdom' \<Longrightarrow>
    aivdom_inv (vdom, avdom, ivdom, tvdom) b \<Longrightarrow> aivdom_inv (vdom', avdom', ivdom', tvdom') b\<close>
  by (auto 3 3 simp: dest: same_mset_distinct_iff mset_eq_setD)

lemma aivdom_inv_dec_cong2:
  \<open>aivdom_inv_dec aivdom b \<Longrightarrow> mset (get_vdom_aivdom aivdom) = mset (get_vdom_aivdom aivdom') \<Longrightarrow>
  mset (get_avdom_aivdom aivdom) = mset (get_avdom_aivdom aivdom') \<Longrightarrow>
  mset (get_ivdom_aivdom aivdom) = mset (get_ivdom_aivdom aivdom') \<Longrightarrow> 
  mset (get_tvdom_aivdom aivdom) = mset (get_tvdom_aivdom aivdom') \<Longrightarrow> aivdom_inv_dec aivdom' b\<close>
  using aivdom_inv_cong2[of \<open>get_vdom_aivdom aivdom\<close> \<open>get_vdom_aivdom aivdom'\<close>
    \<open>get_avdom_aivdom aivdom\<close> \<open>get_avdom_aivdom aivdom'\<close>
     \<open>get_ivdom_aivdom aivdom\<close> \<open>get_ivdom_aivdom aivdom'\<close> 
     \<open>get_tvdom_aivdom aivdom\<close> \<open>get_tvdom_aivdom aivdom'\<close> b]
  by (cases aivdom; cases aivdom') (auto simp: aivdom_inv_dec_def simp del: aivdom_inv.simps)

lemma sort_clauses_by_score_reorder:
  assumes
    \<open>valid_arena arena N (set (get_vdom_aivdom vdom))\<close> and
    \<open>aivdom_inv_dec vdom (dom_m N)\<close>
  shows \<open>sort_clauses_by_score arena vdom
      \<le> SPEC
      (\<lambda>vdom'.
       mset (get_avdom_aivdom vdom) = mset (get_avdom_aivdom vdom') \<and>
       mset (get_vdom_aivdom vdom) = mset (get_vdom_aivdom vdom') \<and>
       mset (get_ivdom_aivdom vdom) = mset (get_ivdom_aivdom vdom') \<and>
       mset (get_tvdom_aivdom vdom) = mset (get_tvdom_aivdom vdom') \<and>
    aivdom_inv_dec vdom' (dom_m N))\<close>
proof -
  have \<open>set (get_avdom_aivdom vdom) \<subseteq> set (get_vdom_aivdom vdom)\<close>
    using assms(2)
    by (auto simp: aivdom_inv_dec_alt_def)
  then show ?thesis
    using assms
    unfolding sort_clauses_by_score_def
    apply refine_vcg
    unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
      get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      valid_sort_clause_score_pre_at_def
    apply (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff(2-)
      arena_dom_status_iff(1)[symmetric] in_set_conv_nth
      arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def
      intro:  aivdom_inv_dec_cong2 dest!: set_mset_mono mset_subset_eqD)
    using arena_dom_status_iff(1) apply force
    using arena_dom_status_iff(1) by (smt (verit, best) aivdom_inv_dec_alt_def mset_subset_eqD nth_mem set_mset_mset)
qed

lemma specify_left_RES:
  assumes "m \<le> RES \<Phi>"
  assumes "\<And>x. x \<in> \<Phi> \<Longrightarrow> f x \<le> M"  
  shows "do { x \<leftarrow> m; f x } \<le> M"
  using assms by (auto simp: pw_le_iff refine_pw_simps)  

lemma sort_vdom_heur_reorder_vdom_wl:
  \<open>(sort_vdom_heur, reorder_vdom_wl) \<in> twl_st_heur_restart_ana r \<rightarrow>\<^sub>f \<langle>{(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and>
  (\<forall>C \<in> set (get_tvdom S). C \<in># dom_m (get_clauses_wl T) \<and> \<not>irred (get_clauses_wl T) C \<and>
    length (get_clauses_wl T \<propto> C) \<noteq> 2)}\<rangle>nres_rel\<close>
proof -
   have mark_to_delete_clauses_wl_pre_same_atms: \<open>set_mset (all_atms_st T) = set_mset (all_init_atms_st T)\<close>
    if \<open>mark_to_delete_clauses_wl_pre T\<close> for T
    using that unfolding mark_to_delete_clauses_wl_pre_def mark_to_delete_clauses_l_pre_def apply -
    apply normalize_goal+
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[symmetric]) assumption+

  show ?thesis
    unfolding reorder_vdom_wl_def sort_vdom_heur_def Let_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
      apply (rule specify_left_RES)
      apply (rule_tac  N = \<open>get_clauses_wl y\<close> and M' = \<open>get_trail_wl y\<close> and
        \<A> = \<open>all_init_atms_st y\<close> and
        NUE = \<open>get_unit_clauses_wl y + get_subsumed_clauses_wl y + get_clauses0_wl y\<close> in
        isa_isa_gather_candidates_for_reduction_remove_deleted_clauses_from_avdom2[unfolded conc_fun_RES])
    subgoal for x y
      by (case_tac y; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case)
    subgoal for x y
      by (case_tac y; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
        mem_Collect_eq prod.case)
    subgoal for x y
      by (case_tac y; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case all_init_atms_st_def)
    subgoal for x y
      unfolding all_atms_st_def[symmetric]
      by (rule mark_to_delete_clauses_wl_pre_same_atms)
    apply (subst case_prod_beta)
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (intro impI ballI)
       (auto intro!: exI[of _ \<open>get_clauses_wl y\<close>] exI[of _ \<open>set (get_vdom x)\<close>]
         simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff(2-)
        arena_dom_status_iff(1)[symmetric]
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def)
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal by auto
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal for x y x1
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder[of _  \<open>get_clauses_wl y\<close>])
      subgoal
       by (clarsimp simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest: mset_eq_setD)
     subgoal
       by (case_tac \<open>x1\<close>; case_tac \<open>get_content (snd x1)\<close>) simp
      subgoal
        by (auto 5 3 simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def intro: aivdom_inv_dec_cong2
          dest: mset_eq_setD)
      done
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


lemma valid_sort_clause_score_pre_swap:
  \<open>valid_sort_clause_score_pre a b \<Longrightarrow> x < length b \<Longrightarrow>
       ba < length b \<Longrightarrow> valid_sort_clause_score_pre a (swap b x ba)\<close>
  by (auto simp: valid_sort_clause_score_pre_def)


lemma mark_to_delete_clauses_wl_post_alt_def:
  \<open>mark_to_delete_clauses_wl_post S0 S \<longleftrightarrow>
    (\<exists>T0 T.
        (S0, T0) \<in> state_wl_l None \<and>
        (S, T) \<in> state_wl_l None \<and>
        blits_in_\<L>\<^sub>i\<^sub>n S0 \<and>
        blits_in_\<L>\<^sub>i\<^sub>n S \<and>
       get_unkept_learned_clss_wl S = {#} \<and>
       get_subsumed_learned_clauses_wl S = {#} \<and>
       get_learned_clauses0_wl S = {#} \<and>
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
    mark_to_delete_clauses_l_pre_def
  apply (rule iffI; normalize_goal+)
  subgoal for T0 T U0
    apply (rule exI[of _ T0])
    apply (rule exI[of _ T])
    apply (intro conjI)
    apply auto[7]
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
    apply auto[3]
    apply (rule exI[of _ U0])
    apply auto
    done
  done

lemma mark_to_delete_clauses_wl_D_heur_pre_alt_def:
  \<open>(\<exists>S'. (S, S') \<in> twl_st_heur \<and> mark_to_delete_clauses_wl_pre S') \<Longrightarrow>
  mark_to_delete_clauses_wl_D_heur_pre S\<close> (is \<open>?pre \<Longrightarrow> ?A\<close>) and
    mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur:
      \<open>mark_to_delete_clauses_wl_pre T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_restart\<close> (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> ?B\<close>) and
    mark_to_delete_clauses_wl_post_twl_st_heur:
      \<open>mark_to_delete_clauses_wl_post T0 T \<Longrightarrow>
        (S, T) \<in> twl_st_heur_restart \<Longrightarrow> (clss_size_resetUS0_st S, T) \<in> twl_st_heur\<close> (is \<open>_ \<Longrightarrow> ?Cpre \<Longrightarrow> ?C\<close>)
proof -
  note cong = trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong empty_occs_list_cong

  show ?A if ?pre
    using that apply -
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def mark_to_delete_clauses_wl_pre_def
      mark_to_delete_clauses_l_pre_def
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
      by (auto simp add: twl_st_heur_def twl_st_heur_restart_def all_init_atms_st_def
        intro: clss_size_corr_restart_clss_size_corr(1)
        simp del: isasat_input_nempty_def)
    done
  show \<open>mark_to_delete_clauses_wl_pre T \<Longrightarrow> (S, T) \<in> twl_st_heur \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def mark_to_delete_clauses_wl_pre_def
      mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_pre_def
    apply normalize_goal+
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (auto simp add: twl_st_heur_def twl_st_heur_restart_def all_init_atms_st_def all_atms_st_def
        intro: clss_size_corr_restart_clss_size_corr(1)
        simp del: isasat_input_nempty_def)
    done
  show  \<open>mark_to_delete_clauses_wl_post T0 T \<Longrightarrow> ?Cpre \<Longrightarrow> ?C\<close>
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_post_alt_def
    apply normalize_goal+
    subgoal for U0 U V0 V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (auto simp add: twl_st_heur_def twl_st_heur_restart_def all_init_atms_st_def all_atms_st_def
        clss_size_resetUS0_st_def
        simp del: isasat_input_nempty_def
        intro: clss_size_corr_restart_clss_size_corr(2))
    done
qed


lemma find_largest_lbd_and_size:
  assumes
    \<open>(S,T) \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>find_largest_lbd_and_size l S \<le>SPEC (\<lambda>_. True)\<close>
proof -
  have arena: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close> and
    avdom: \<open>aivdom_inv_dec (get_aivdom S) (dom_m (get_clauses_wl T))\<close>
    using assms unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_def by auto

  have [intro!]: \<open>clause_not_marked_to_delete_heur_pre (S, get_tvdom S ! i)\<close>
    \<open>\<not> \<not> clause_not_marked_to_delete_heur S (get_tvdom S ! i) \<Longrightarrow> get_clause_LBD_pre (get_clauses_wl_heur S) (get_tvdom S ! i)\<close>
    \<open>\<not> \<not> clause_not_marked_to_delete_heur S (get_tvdom S ! i) \<Longrightarrow> arena_is_valid_clause_idx (get_clauses_wl_heur S) (get_tvdom S ! i)\<close>
    if \<open>i < length (get_tvdom S)\<close>
    for i
    using arena avdom multi_member_split[of \<open>get_tvdom S ! i\<close> \<open>mset (get_tvdom S)\<close>] that
      arena_dom_status_iff(1)[OF arena, of \<open>get_tvdom S ! i\<close>]
    unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
      aivdom_inv_dec_alt_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      clause_not_marked_to_delete_heur_def
    by (auto intro!: exI[of _ \<open>get_clauses_wl T\<close>] exI[of _ \<open>set (get_vdom S)\<close>]
      simp: arena_lifting)
  have le: \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur S)\<close>
    using avdom valid_arena_vdom_le[OF arena] unfolding aivdom_inv_dec_alt_def by (auto simp: distinct_card dest: size_mset_mono)

  show ?thesis
    unfolding find_largest_lbd_and_size_def mop_clause_not_marked_to_delete_heur_def nres_monad3
      mop_arena_lbd_st_def mop_arena_lbd_def mop_arena_length_st_def mop_arena_length_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, _, _). length (get_tvdom S) - i)\<close>])
    subgoal by (rule le)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_tvdom_at_pre_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma mark_to_delete_clauses_wl_D_heur_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S0. do {
          ASSERT (mark_to_delete_clauses_wl_D_heur_pre S0);
          S \<leftarrow> sort_vdom_heur S0;
          _ \<leftarrow> RETURN (get_tvdom S);
          l \<leftarrow> number_clss_to_keep S;
          (lbd, sze) \<leftarrow> find_largest_lbd_and_size l S;
          ASSERT
               (length (get_tvdom S) \<le> length (get_clauses_wl_heur S0));
          (i, T) \<leftarrow>
            WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup> (\<lambda>(i, S). i < length (get_tvdom S))
             (\<lambda>(i, T). do {
                   ASSERT (i < length (get_tvdom T));
                   ASSERT (access_tvdom_at_pre T i);
                   ASSERT
                        (clause_not_marked_to_delete_heur_pre
                          (T, get_tvdom T ! i));
                   b \<leftarrow> mop_clause_not_marked_to_delete_heur T
                        (get_tvdom T ! i);
                   if \<not>b then RETURN (i, delete_index_vdom_heur i T)
                   else do {
                          ASSERT
                               (access_lit_in_clauses_heur_pre
                                 ((T, get_tvdom T ! i), 0));
                          ASSERT
                               (length (get_clauses_wl_heur T)
                                \<le> length (get_clauses_wl_heur S0));
                          ASSERT
                               (length (get_tvdom T)
                                \<le> length (get_clauses_wl_heur T));
                          L \<leftarrow> mop_access_lit_in_clauses_heur T
                               (get_tvdom T ! i) 0;
                          D \<leftarrow> get_the_propagation_reason_pol
                               (get_trail_wl_heur T) L;
                          ASSERT
                               (arena_is_valid_clause_idx
                                 (get_clauses_wl_heur T) (get_tvdom T ! i));
                          let can_del = (D \<noteq> Some (get_tvdom T ! i) \<and>
                             arena_length (get_clauses_wl_heur T) (get_tvdom T ! i) \<noteq> 2);
                          if can_del
                          then do {
                                wasted \<leftarrow> mop_arena_length_st T (get_tvdom T ! i);
                                _ \<leftarrow> log_del_clause_heur T (get_tvdom T ! i);
                                 ASSERT(mark_garbage_pre
                                   (get_clauses_wl_heur T, get_tvdom T ! i) \<and>
                                   1 \<le> clss_size_lcount (get_learned_count T) \<and> i < length (get_tvdom T));
                                 RETURN
                                  (i, mark_garbage_heur3 (get_tvdom T ! i) i (incr_wasted_st (of_nat wasted) T))
                               }
                          else do {
                                 RETURN (i + 1, T)
                               }
                        }
                 })
             (l, S);
          ASSERT
               (length (get_tvdom T) \<le> length (get_clauses_wl_heur S0));
         incr_reduction_stat (set_stats_size_limit_st lbd sze T)
        })\<close>
    unfolding mark_to_delete_clauses_wl_D_heur_def
      mop_arena_lbd_def mop_arena_status_def mop_arena_length_def
      mop_marked_as_used_def bind_to_let_conv Let_def
      nres_monad3 mop_mark_garbage_heur3_def mop_mark_unused_st_heur_def
      incr_wasted_st_twl_st
    by (auto intro!: ext bind_cong[OF refl])


lemma mark_to_delete_clauses_GC_wl_D_heur_alt_def:
    \<open>mark_to_delete_clauses_GC_wl_D_heur  = (\<lambda>S0. do {
          ASSERT (mark_to_delete_clauses_GC_wl_D_heur_pre S0);
          S \<leftarrow> sort_vdom_heur S0;
          _ \<leftarrow> RETURN (get_tvdom S);
          l \<leftarrow> number_clss_to_keep S;
          (lbd, sze) \<leftarrow> find_largest_lbd_and_size l S;
          ASSERT
               (length (get_tvdom S) \<le> length (get_clauses_wl_heur S0));
          (i, T) \<leftarrow>
            WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup> (\<lambda>(i, S). i < length (get_tvdom S))
             (\<lambda>(i, T). do {
                   ASSERT (i < length (get_tvdom T));
                   ASSERT (access_tvdom_at_pre T i);
                   ASSERT
                        (clause_not_marked_to_delete_heur_pre
                          (T, get_tvdom T ! i));
                   b \<leftarrow> mop_clause_not_marked_to_delete_heur T
                        (get_tvdom T ! i);
                   if \<not>b then RETURN (i, delete_index_vdom_heur i T)
                   else do {
                          ASSERT
                               (access_lit_in_clauses_heur_pre
                                 ((T, get_tvdom T ! i), 0));
                          ASSERT
                               (length (get_clauses_wl_heur T)
                                \<le> length (get_clauses_wl_heur S0));
                          ASSERT
                               (length (get_tvdom T)
                                \<le> length (get_clauses_wl_heur T));
                          ASSERT
                               (arena_is_valid_clause_idx
                                 (get_clauses_wl_heur T) (get_tvdom T ! i));
                          let can_del = (arena_length (get_clauses_wl_heur T) (get_tvdom T ! i) \<noteq> 2);
                          if can_del
                          then do {
                                wasted \<leftarrow> mop_arena_length_st T (get_tvdom T ! i);
                                _ \<leftarrow> log_del_clause_heur T (get_tvdom T ! i);
                                 ASSERT(mark_garbage_pre
                                   (get_clauses_wl_heur T, get_tvdom T ! i) \<and>
                                   1 \<le> clss_size_lcount (get_learned_count T)\<and> i < length (get_tvdom T));
                                 RETURN
                                  (i, mark_garbage_heur3 (get_tvdom T ! i) i (incr_wasted_st (of_nat wasted) T))
                               }
                          else do {
                                 RETURN
                                  (i + 1, T)
                               }
                        }
                 })
             (l, S);
          ASSERT
               (length (get_tvdom T) \<le> length (get_clauses_wl_heur S0));
          incr_restart_stat (set_stats_size_limit_st lbd sze T)
        })\<close>
    unfolding mark_to_delete_clauses_GC_wl_D_heur_def
      mop_arena_lbd_def mop_arena_status_def mop_arena_length_def
      mop_marked_as_used_def bind_to_let_conv Let_def
      nres_monad3 mop_mark_garbage_heur3_def mop_mark_unused_st_heur_def
      incr_wasted_st_twl_st
    by (auto intro!: ext intro!: bind_cong[OF refl])

lemma learned_clss_count_mark_garbage_heur3:
  \<open>clss_size_lcount (get_learned_count xs) \<ge> Suc 0 \<Longrightarrow> learned_clss_count (mark_garbage_heur3 C i xs) = (learned_clss_count xs) - 1\<close> and
  learned_clss_count_incr_st[simp]:
  \<open>learned_clss_count (incr_wasted_st b xs) = learned_clss_count xs\<close>
  by (cases xs; auto simp: mark_garbage_heur3_def incr_wasted_st_def learned_clss_count_def; fail)+

lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D:
  \<open>(mark_to_delete_clauses_wl_D_heur, mark_to_delete_clauses_wl) \<in>
     twl_st_heur_restart_ana' r u \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart_ana' r u\<rangle>nres_rel\<close>
proof -
  have mark_to_delete_clauses_wl_D_alt_def:
    \<open>mark_to_delete_clauses_wl  = (\<lambda>S0. do {
      ASSERT(mark_to_delete_clauses_wl_pre S0);
      S \<leftarrow> reorder_vdom_wl S0;
      xs \<leftarrow> collect_valid_indices_wl S;
      l \<leftarrow> SPEC(\<lambda>_::nat. True);
      _ \<leftarrow> SPEC(\<lambda>_::nat\<times>nat. True);
      (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_inv S xs\<^esup>
        (\<lambda>(i, T, xs). i < length xs)
        (\<lambda>(i, T, xs). do {
          b \<leftarrow> RETURN (xs!i \<in># dom_m (get_clauses_wl T));
          if \<not>b then RETURN (i, T, delete_index_and_swap xs i)
          else do {
            ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	    ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
            K \<leftarrow> RETURN (get_clauses_wl T \<propto> (xs ! i) ! 0);
            b \<leftarrow> RETURN (); \<comment> \<open>propagation reason\<close>
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
              (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
               \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2);
            ASSERT(i < length xs);
            if can_del
            then do{
              _  \<leftarrow> RETURN (length (get_clauses_wl T \<propto> (xs!i)));
              _ \<leftarrow> RETURN (log_clause T (xs!i));
              RETURN (i, mark_garbage_wl (xs!i) T, delete_index_and_swap xs i)}
            else
              RETURN (i+1, T, xs)
          }
        })
        (l, S, xs);
      remove_all_learned_subsumed_clauses_wl S
    })\<close>
    unfolding mark_to_delete_clauses_wl_def reorder_vdom_wl_def bind_to_let_conv Let_def nres_monad3
      summarize_ASSERT_conv
    by (force intro!: ext)

  have mono: \<open>g = g' \<Longrightarrow> do {f; g} = do {f; g'}\<close>
     \<open>(\<And>x. h x = h' x) \<Longrightarrow> do {x \<leftarrow> f; h x} = do {x \<leftarrow> f; h' x}\<close> for f f' :: \<open>_ nres\<close> and g g' and h h'
    by auto
  have mark_to_delete_clauses_wl_pre_same_atms: \<open>set_mset (all_atms_st T) = set_mset (all_init_atms_st T)\<close>
    if \<open>mark_to_delete_clauses_wl_pre T\<close> for T
    using that unfolding mark_to_delete_clauses_wl_pre_def mark_to_delete_clauses_l_pre_def apply -
    apply normalize_goal+
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[symmetric]) assumption+
  have mark_to_delete_clauses_wl_D_heur_pre_cong:
    \<open>aivdom_inv_dec vdom' (dom_m (get_clauses_wl S')) \<Longrightarrow>
    mset (get_vdom_aivdom (get_aivdom T)) = mset (get_vdom_aivdom vdom') \<Longrightarrow>
     (T, S') \<in> twl_st_heur_restart \<Longrightarrow>
    mark_to_delete_clauses_wl_pre S' \<Longrightarrow>
    mark_to_delete_clauses_wl_D_heur_pre T \<Longrightarrow>
    valid_arena N'' (get_clauses_wl S') (set (get_vdom_aivdom (get_aivdom T))) \<Longrightarrow>
    mark_to_delete_clauses_wl_D_heur_pre (set_clauses_wl_heur N'' (set_aivdom_wl_heur vdom' T))\<close>
    for M' N' D' j W' vm clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount lcount heur old_arena ivdom opts S' vdom' N'' T
    using mset_eq_setD[of \<open>get_vdom_aivdom (get_aivdom T)\<close> \<open>get_vdom_aivdom vdom'\<close>, symmetric] apply -
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def apply normalize_goal+
    by (rule_tac x=S' in exI)
     (clarsimp simp: twl_st_heur_restart_def dest: mset_eq_setD intro: )

  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart_ana' r u \<and> V = T \<and>
         (mark_to_delete_clauses_wl_pre T \<longrightarrow> mark_to_delete_clauses_wl_pre V) \<and>
          (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U) \<and>
         (\<forall>C\<in>set (get_tvdom U). \<not>irred (get_clauses_wl V) C \<and> length (get_clauses_wl V \<propto> C) \<noteq> 2)}
         (reorder_vdom_wl T)\<close> (is \<open>_ \<le> \<Down>?sort _\<close>)
    if \<open>(S, T) \<in> twl_st_heur_restart_ana' r u\<close> and \<open>mark_to_delete_clauses_wl_pre T\<close> for S T
    supply [simp del] = EQ_def
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def Let_def
    apply (refine_rcg ASSERT_leI)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
      apply (rule specify_left_RES)
      apply (rule_tac  N = \<open>get_clauses_wl T\<close> and M' = \<open>get_trail_wl T\<close> and
        \<A> = \<open>all_init_atms_st T\<close> and
        NUE = \<open>get_unit_clauses_wl T + get_subsumed_clauses_wl T + get_clauses0_wl T\<close> in
     isa_isa_gather_candidates_for_reduction_remove_deleted_clauses_from_avdom2[unfolded conc_fun_RES])
    subgoal
      by (case_tac T; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case)
    subgoal
      by (case_tac T; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case)
    subgoal
      by (case_tac T; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case
        all_init_atms_st_def)
    subgoal
      unfolding all_atms_st_def[symmetric]
      by (rule mark_to_delete_clauses_wl_pre_same_atms)
    apply (subst case_prod_beta)
    apply (intro ASSERT_leI)
    subgoal
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff(1)[symmetric]
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
        intro!: exI[of _ \<open>get_clauses_wl T\<close>] exI[of _ \<open>set (get_vdom S)\<close>]
        dest: set_mset_mono mset_subset_eqD)
    subgoal by (auto simp: EQ_def)
    subgoal
      by (cases T)
       (clarsimp simp add: twl_st_heur_restart_ana_def valid_arena_vdom_subset twl_st_heur_restart_def aivdom_inv_dec_alt_def case_prod_beta split: 
        dest!: size_mset_mono valid_arena_vdom_subset)
    subgoal  for arena_aivdom
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder[of _ \<open>get_clauses_wl T\<close>])
      subgoal
        by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest: mset_eq_setD)
      subgoal
        by (cases \<open>arena_aivdom\<close>; cases \<open>get_content (snd arena_aivdom)\<close>)
         (simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
      subgoal
        apply auto
        apply (auto simp: learned_clss_count_def (* twl_st_heur_restart_ana_def twl_st_heur_restart_def *)
          intro: mark_to_delete_clauses_wl_D_heur_pre_cong
          intro: aivdom_inv_cong2
          dest: mset_eq_setD)
          apply (auto 4 3 simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def 
            intro: aivdom_inv_cong2 dest: mset_eq_setD; fail)[]
          apply (rule mark_to_delete_clauses_wl_D_heur_pre_cong)
          apply assumption+
          apply (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
          done
          done
        done

  have [refine0]: \<open>RETURN (get_tvdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_tvdom x \<and>
    (\<forall>C\<in>set (get_tvdom x). \<not>irred (get_clauses_wl y) C \<and> length (get_clauses_wl y \<propto> C) \<noteq> 2)}
    (collect_valid_indices_wl y)\<close>
    (is \<open>_ \<le> \<Down> ?indices _\<close>)
    if
      \<open>(x, y) \<in> ?sort S T\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y S T
  proof -
    show ?thesis using that by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed

  have init:
    \<open>(u', xs) \<in> ?indices S Sa \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart_ana' r u \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
    {(Sa', (T, xs)). (Sa', T) \<in> twl_st_heur_restart_ana' r u \<and> xs = get_tvdom Sa' \<and>
    set (get_tvdom Sa') \<subseteq> set (get_tvdom S) \<and>
      (\<forall>C\<in>set (get_tvdom Sa'). \<not>irred (get_clauses_wl T) C \<and> length (get_clauses_wl T \<propto> C) \<noteq> 2)}\<close>
    (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?R\<close>)
    for x y S Sa xs l la u'
    by auto

  define reason_rel where
    \<open>reason_rel K x1a \<equiv> {(C, _ :: unit).
          (C \<noteq> None) = (Propagated K (the C) \<in> set (get_trail_wl x1a)) \<and>
          (C = None) = (Decided K \<in> set (get_trail_wl x1a) \<or>
             K \<notin> lits_of_l (get_trail_wl x1a)) \<and>
         (\<forall>C1. (Propagated K C1 \<in> set (get_trail_wl x1a) \<longrightarrow> C1 = the C))}\<close> for K :: \<open>nat literal\<close> and x1a
  have get_the_propagation_reason:
    \<open>get_the_propagation_reason_pol (get_trail_wl_heur x2b) L
        \<le> SPEC (\<lambda>D. (D, ()) \<in> reason_rel K x1a)\<close>
  if
    \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close> and
    \<open>mark_to_delete_clauses_wl_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa) \<in> ?sort x y\<close> and
    \<open>(ys, xs) \<in> ?indices S Sa\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    xa_x': \<open>(xa, x') \<in> ?R S\<close> and
    \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
    \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
    \<open>x1b < length (get_tvdom x2b)\<close> and
    \<open>access_tvdom_at_pre x2b x1b\<close> and
    dom: \<open>(b, ba)
       \<in> {(b, b').
          (b, b') \<in> bool_rel \<and>
          b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
      \<open>\<not> \<not> b\<close>
      \<open>\<not> \<not> ba\<close> and
    \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
    \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close> and
    st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
    L: \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close> and
    L': \<open>(L, K)
    \<in> {(L, L').
       (L, L') \<in> nat_lit_lit_rel \<and>
       L' = get_clauses_wl x1a \<propto> (x2a ! x1) ! 0}\<close>
    for x y S Sa xs' xs l la xa x' x1 x2 x1a x2a x1' x2' x3 x1b ys x2b L K b ba
  proof -
    have L: \<open>arena_lit (get_clauses_wl_heur x2b) (x2a ! x1) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      using L that by (auto dest!: twl_st_heur_restart(2) simp: st arena_lifting dest: twl_st_heur_restart_anaD)

    show ?thesis
      apply (rule order.trans)
      apply (rule get_the_propagation_reason_pol[THEN fref_to_Down_curry,
        of \<open>all_init_atms_st x1a\<close> \<open>get_trail_wl x1a\<close>
	  \<open>arena_lit (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b + 0)\<close>])
      subgoal
        using xa_x' L L' by (auto simp add: twl_st_heur_restart_def st)
      subgoal
        using xa_x' L' dom by (auto simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def st arena_lifting
          all_init_atms_st_def get_unit_init_clss_wl_alt_def)
      using that unfolding get_the_propagation_reason_def reason_rel_def apply -
      by (auto simp: twl_st_heur_restart lits_of_def get_the_propagation_reason_def
          conc_fun_RES
        dest!: twl_st_heur_restart_anaD dest: twl_st_heur_restart(2)  twl_st_heur_restart_same_annotD imageI[of _ _ lit_of])
  qed

  have already_deleted:
    \<open>((x1b,  delete_index_vdom_heur x1b x2b), x1, x1a, delete_index_and_swap x2a x1) \<in> ?R S\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa) \<in> ?sort x y\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x') \<in> ?R S\<close> and
      nempty: \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      le: \<open>x1b < length (get_tvdom x2b)\<close> and
      \<open>access_tvdom_at_pre x2b x1b\<close> and
      ba: \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
        \<open>\<not>ba\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa ba b
  proof -
    show ?thesis
      using xx nempty le ba unfolding st
      by (cases \<open>get_tvdom x2b\<close> rule: rev_cases)
       (auto 4 3 simp: twl_st_heur_restart_ana_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If learned_clss_count_def
          aivdom_inv_removed_inactive
        intro: valid_arena_extra_information_mark_to_delete'
        intro!: aivdom_inv_dec_removed_inactive_tvdom
        dest!: in_set_butlastD in_vdom_m_fmdropD
        elim!: in_set_upd_cases)
  qed

  have mop_clause_not_marked_to_delete_heur:
    \<open>mop_clause_not_marked_to_delete_heur x2b (get_tvdom x2b ! x1b)
        \<le> SPEC
           (\<lambda>c. (c, x2a ! x1 \<in># dom_m (get_clauses_wl x1a))
                \<in> {(b, b'). (b,b') \<in> bool_rel \<and> (b \<longleftrightarrow> x2a ! x1 \<in># dom_m (get_clauses_wl x1a))})\<close>
    if
      \<open>(xa, x') \<in> ?R S\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_inv Sa xs x'\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close>
    for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b
    unfolding mop_clause_not_marked_to_delete_heur_def
    apply refine_vcg
    subgoal
      using that by blast
    subgoal
      using that by (auto simp: twl_st_heur_restart arena_lifting dest: twl_st_heur_restart(2) dest!: twl_st_heur_restart_anaD)
    done

  have mop_access_lit_in_clauses_heur:
    \<open>mop_access_lit_in_clauses_heur x2b (get_tvdom x2b ! x1b) 0
        \<le> SPEC
           (\<lambda>c. (c, get_clauses_wl x1a \<propto> (x2a ! x1) ! 0)
                \<in> {(L, L'). (L, L') \<in> nat_lit_lit_rel \<and> L' = get_clauses_wl x1a \<propto> (x2a ! x1) ! 0})\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close> and
      \<open>mark_to_delete_clauses_wl_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa) \<in> ?sort x y\<close> and
      \<open>(uu, xs) \<in> ?indices S Sa\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {uu. True}\<close> and
      \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur x)\<close> and
      \<open>(xa, x') \<in> ?R S\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_inv Sa xs x'\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      \<open>x1b < length (get_tvdom x2b)\<close> and
      \<open>access_tvdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close> and
      \<open>(b, ba)
       \<in> {(b, b').
          (b, b') \<in> bool_rel \<and>
          b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close> and
      \<open>\<not> \<not> b\<close> and
      \<open>\<not> \<not> ba\<close> and
      \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
      \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0
       \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close> and
      pre: \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close>
     for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b b ba
  unfolding mop_access_lit_in_clauses_heur_def mop_arena_lit2_def
  apply refine_vcg
  subgoal using pre unfolding access_lit_in_clauses_heur_pre_def by simp
  subgoal using that by (auto dest!: twl_st_heur_restart_anaD twl_st_heur_restart_valid_arena simp: arena_lifting)
  done

  have incr_restart_stat: \<open>incr_reduction_stat (set_stats_size_limit_st lbd sze T)
    \<le> \<Down> (twl_st_heur_restart_ana' r u) (remove_all_learned_subsumed_clauses_wl S)\<close>
    if \<open>(T, S) \<in> twl_st_heur_restart_ana' r u\<close> for S T i u  lbd sze
    using that
    by (cases S; cases T)
      (auto simp: conc_fun_RES incr_restart_stat_def learned_clss_count_def set_stats_size_limit_st_def
        twl_st_heur_restart_ana_def twl_st_heur_restart_def
      remove_all_learned_subsumed_clauses_wl_def clss_size_corr_def incr_reduction_stat_def
      clss_size_lcountUE_def clss_size_lcountUS_def clss_size_def
      clss_size_resetUS_def clss_size_lcount_def clss_size_lcountU0_def 
        RES_RETURN_RES)

  have only_irred: \<open>\<not> irred (get_clauses_wl x1a) (x2a ! x1)\<close> (is ?A) and
    get_learned_count_ge: \<open>Suc 0 \<le> clss_size_lcount (get_learned_count x2b)\<close> (is ?B)
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close> and
      \<open>mark_to_delete_clauses_wl_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa) \<in> ?sort x y\<close> and
      indices: \<open>(uu, xs) \<in> ?indices S Sa\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur x)\<close> and
      xx: \<open>(xa, x') \<in> ?R S\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_inv Sa xs x'\<close> and
      st: \<open>x2 = (x1a, x2a)\<close> \<open>x' = (x1, x2)\<close> \<open>xa = (x1b, x2b)\<close> and
      \<open>x1b < length (get_tvdom x2b)\<close> and
      \<open>access_tvdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close> and
      dom: \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
        \<open>\<not> \<not> b\<close>
        \<open>\<not> \<not> ba\<close> and
      \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
      \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close> and
      \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close> and
      \<open>length (get_clauses_wl_heur x2b) \<le> length (get_clauses_wl_heur x)\<close> and
      \<open>length (get_tvdom x2b) \<le> length (get_clauses_wl_heur x2b)\<close> and
      \<open>(L, K) \<in> {(L, L'). (L, L') \<in> nat_lit_lit_rel \<and> L' = get_clauses_wl x1a \<propto> (x2a ! x1) ! 0}\<close> and
      \<open>(D, bb) \<in> reason_rel K x1a\<close> and
      \<open>arena_is_valid_clause_idx (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b)\<close> and
      \<open>D \<noteq> Some (get_tvdom x2b ! x1b) \<and> arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2\<close>
      for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b b ba L K D bb
    proof -
      have \<open>get_tvdom x2b ! x1 \<in> set (get_tvdom x2b)\<close> and
        x: \<open>(x2b, x1a) \<in> twl_st_heur_restart_ana r\<close>
      using that by (auto dest: simp: arena_lifting twl_st_heur_restart)
    then show ?A
      using indices xx
      by (auto dest: twl_st_heur_restart_anaD twl_st_heur_restart_valid_arena
        simp: arena_lifting twl_st_heur_restart st)
    then show ?B
      using dom x by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def ran_m_def
        dest!: multi_member_split
        dest!: clss_size_corr_restart_rew)
  qed
  have length_filter_le: \<open>((x1b, mark_garbage_heur3 (get_tvdom x2b ! x1b) x1b (incr_wasted_st (word_of_nat wasted) x2b)), x1,
  mark_garbage_wl (x2a ! x1) x1a, delete_index_and_swap x2a x1)
    \<in> ?R S\<close>
    if H:
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close>
      \<open>mark_to_delete_clauses_wl_pre y\<close>
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
      \<open>(S, Sa) \<in> ?sort x y\<close>
      \<open>(uu, xs) \<in> ?indices S Sa\<close>
      \<open>(l, la) \<in> nat_rel\<close>
      \<open>la \<in> {_. True}\<close>
      \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur x)\<close>
      \<open>(xa, x') \<in> ?R S\<close>
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close>
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close>
      \<open>mark_to_delete_clauses_wl_inv Sa xs x'\<close>
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close>
      \<open>x1b < length (get_tvdom x2b)\<close>
      \<open>access_tvdom_at_pre x2b x1b\<close>
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close>
      \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
      \<open>\<not> \<not> b\<close>
      \<open>\<not> \<not> ba\<close>
      \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close>
      \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close>
      \<open>length (get_clauses_wl_heur x2b) \<le> length (get_clauses_wl_heur x)\<close>
      \<open>length (get_tvdom x2b) \<le> length (get_clauses_wl_heur x2b)\<close>
      \<open>(L, K) \<in> {(L, L'). (L, L') \<in> nat_lit_lit_rel \<and> L' = get_clauses_wl x1a \<propto> (x2a ! x1) ! 0}\<close>
      \<open>(D, bb) \<in> reason_rel K x1a\<close>
      \<open>arena_is_valid_clause_idx (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b)\<close>
      \<open>(D \<noteq> Some (get_tvdom x2b ! x1b) \<and> arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2, can_del)
    \<in> bool_rel\<close>
      \<open>x1 < length x2a\<close>
      \<open>D \<noteq> Some (get_tvdom x2b ! x1b) \<and> arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2\<close>
      can_del
    for x y S Sa xs l la xa x' x1 x2 x1a x2a x1b x2b b ba can_del D L K bb uu wasted
  proof -
      have [simp]: \<open>mark_garbage_heur3 i C (incr_wasted_st b S) = incr_wasted_st b (mark_garbage_heur3 i C S)\<close> for i C S b
        by (cases S; auto simp: mark_garbage_heur3_def incr_wasted_st_def)
      have \<open>mark_garbage_pre (get_clauses_wl_heur x2b, get_tvdom x2b ! x1b)\<close>
        \<open>x1b < length (get_tvdom x2b)\<close>
        using that
        unfolding prod.simps mark_garbage_pre_def
          arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def apply -
        by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
         (auto simp: twl_st_heur_restart twl_st_heur_restart_ana_def dest: twl_st_heur_restart_valid_arena)
      moreover have 0: \<open>Suc 0 \<le> clss_size_lcount (get_learned_count x2b)\<close>
         \<open>\<not> irred (get_clauses_wl x1a) (x2a ! x1)\<close> 
        using get_learned_count_ge[OF that(1-29,32)] only_irred[OF that(1-29,32)] by auto
      moreover have \<open>(mark_garbage_heur3 (get_tvdom x2b ! x1) x1
        (incr_wasted_st (word_of_nat wasted) x2b),
        mark_garbage_wl (get_tvdom x2b ! x1) x1a)
        \<in> twl_st_heur_restart_ana r\<close>
        by (use that 0 in
          \<open>auto intro!: incr_wasted_st mark_garbage_heur_wl_ana simp: twl_st_heur_restart
          learned_clss_count_mark_garbage_heur3
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_anaD\<close>)
      moreover have \<open>learned_clss_count
        (mark_garbage_heur3 (get_tvdom x2b ! x1) x1
        (incr_wasted_st (word_of_nat wasted) x2b))
        \<le> u\<close>
        by (use that 0 in
          \<open>auto intro!: incr_wasted_st mark_garbage_heur_wl_ana simp: twl_st_heur_restart
          learned_clss_count_mark_garbage_heur3
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_anaD\<close>)
      moreover have \<open>xb \<in> set (get_tvdom S)\<close>
        if \<open>xb \<in> set (butlast ((get_tvdom x2b)[x1 := last (get_tvdom x2b)]))\<close> for xb
      proof -
        have \<open>xb \<in> set (get_tvdom x2b)\<close>
          using that H by (auto dest!: in_set_butlastD)
            (metis Misc.last_in_set in_set_upd_eq len_greater_imp_nonempty)
        then show ?thesis
          using H by auto
      qed
      moreover have K: \<open>\<not>irred (get_clauses_wl (mark_garbage_wl (get_tvdom x2b ! x1) x1a)) C\<close>  \<open>C \<noteq> get_tvdom x2b ! x1\<close>
        if \<open>C \<in> set (butlast ((get_tvdom x2b)[x1 := last (get_tvdom x2b)]))\<close> for C
      proof -
        have a: \<open>distinct (get_tvdom x2b)\<close> \<open>x1 < length (get_tvdom x2b)\<close>
          using  H(9-15) by (auto simp: twl_st_heur_restart_ana_def
            twl_st_heur_restart_def aivdom_inv_dec_alt_def)
        then have 1: \<open>get_tvdom x2b = take x1 (get_tvdom x2b) @ get_tvdom x2b ! x1 # drop (Suc x1) (get_tvdom x2b)\<close>
          by (subst append_take_drop_id[of x1, symmetric], subst Cons_nth_drop_Suc[symmetric])
           auto
        have \<open>set (delete_index_and_swap (get_tvdom x2b) x1) =
          set (get_tvdom x2b) - {get_tvdom x2b!x1}\<close>
          using a
          apply (subst (asm) (2)1, subst (asm) (1)1)
          apply (subst (2)1, subst (1)1)
          apply (cases \<open>drop (Suc x1) (get_tvdom x2b)\<close> rule: rev_cases)
          by (auto simp: nth_append list_update_append1 list_update_append2 butlast_append
            dest: in_set_butlastD)
        then show [simp]: \<open>C \<noteq> get_tvdom x2b ! x1\<close>
          using that by auto
        show  \<open>\<not>irred (get_clauses_wl (mark_garbage_wl (get_tvdom x2b ! x1) x1a)) C\<close>
          using that H
          apply (cases x1a)
          apply (auto simp: mark_garbage_wl_def)
          by (metis Misc.last_in_set in_set_butlastD in_set_upd_cases len_greater_imp_nonempty)
      qed
      moreover have \<open>length (get_clauses_wl (mark_garbage_wl (get_tvdom x2b ! x1) x1a) \<propto> C) \<noteq> 2\<close>
        if \<open>C \<in> set (butlast ((get_tvdom x2b)[x1 := last (get_tvdom x2b)]))\<close> for C
      proof -
        have \<open>C \<in> set (get_tvdom x2b)\<close> \<open>C \<noteq> get_tvdom x2b ! x1\<close>
          using K(2)[OF that] that
          apply (auto simp: mark_garbage_wl_def)
          using in_set_delete_index_and_swapD by fastforce
        then show ?thesis
          using H
          by (cases x1a)
           (auto simp: mark_garbage_wl_def)
      qed
      ultimately show ?thesis
        using that supply [[goals_limit=1]]
        by (auto intro!: )
  qed
  have mop_arena_length_st: \<open>mop_arena_length_st x2b (get_tvdom x2b ! x1b)
    \<le> SPEC
    (\<lambda>c. (c, length (get_clauses_wl x1a \<propto> (x2a ! x1))) \<in> nat_rel)\<close> 
    if H:
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close>
      \<open>mark_to_delete_clauses_wl_pre y\<close>
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
      \<open>(S, Sa) \<in> ?sort x y\<close>
      \<open>(uu, xs) \<in> ?indices S Sa\<close>
      \<open>(l, la) \<in> nat_rel\<close>
      \<open>la \<in> {_. True}\<close>
      \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur x)\<close>
      \<open>(xa, x') \<in> ?R S\<close>
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close>
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close>
      \<open>mark_to_delete_clauses_wl_inv Sa xs x'\<close>
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close>
      \<open>x1b < length (get_tvdom x2b)\<close>
      \<open>access_tvdom_at_pre x2b x1b\<close>
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close>
      \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
      \<open>\<not> \<not> b\<close>
      \<open>\<not> \<not> ba\<close>
      \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close>
      \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close>
      \<open>length (get_clauses_wl_heur x2b) \<le> length (get_clauses_wl_heur x)\<close>
      \<open>length (get_tvdom x2b) \<le> length (get_clauses_wl_heur x2b)\<close>
      \<open>(L, K) \<in> {(L, L'). (L, L') \<in> nat_lit_lit_rel \<and> L' = get_clauses_wl x1a \<propto> (x2a ! x1) ! 0}\<close>
      \<open>(D, bb) \<in> reason_rel K x1a\<close>
      \<open>arena_is_valid_clause_idx (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b)\<close>
      \<open>(D \<noteq> Some (get_tvdom x2b ! x1b) \<and> arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2, can_del)
    \<in> bool_rel\<close>
      \<open>x1 < length x2a\<close>
      \<open>D \<noteq> Some (get_tvdom x2b ! x1b) \<and> arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2\<close>
      can_del
    for x y S Sa xs l la xa x' x1 x2 x1a x2a x1b x2b b ba can_del D L K bb uu
    unfolding mop_arena_length_st_def
    apply (rule mop_arena_length[THEN fref_to_Down_curry, THEN order_trans,
      of \<open>get_clauses_wl x1a\<close> \<open>get_tvdom x2b ! x1b\<close> _ _ \<open>set (get_vdom x2b)\<close>])
    using that by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
  show ?thesis
    supply sort_vdom_heur_def[simp] twl_st_heur_restart_anaD[dest] [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_alt_def mark_to_delete_clauses_wl_D_alt_def
      access_lit_in_clauses_heur_def
    apply (intro frefI nres_relI)
    apply (refine_vcg sort_vdom_heur_reorder_vdom_wl[THEN fref_to_Down] incr_restart_stat find_largest_lbd_and_size)
    subgoal
      unfolding mark_to_delete_clauses_wl_D_heur_pre_def by fast
    apply assumption
    subgoal by auto
    subgoal for x y S T unfolding number_clss_to_keep_def by (cases S) (auto)
    apply (solves auto)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
       dest!: valid_arena_vdom_subset size_mset_mono)
    apply (rule init; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_tvdom_at_pre_def)
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
        prod.simps
      by (rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
         (auto simp: twl_st_heur_restart
        intro!: twl_st_heur_restart_valid_arena[simplified]
        dest: twl_st_heur_restart_get_tvdom_nth_get_vdom[simplified])
    apply (rule mop_clause_not_marked_to_delete_heur; assumption)
    subgoal for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b
      by (auto simp: twl_st_heur_restart)
    subgoal
      by (rule already_deleted)
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_tvdom x2b ! x1b\<close>], simp add: aivdom_inv_dec_alt_def,
        rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>])
        (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal premises p using p(7-)
      by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
        dest!: valid_arena_vdom_subset size_mset_mono)
      apply (rule mop_access_lit_in_clauses_heur; assumption)
      apply (rule get_the_propagation_reason; assumption)
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest:twl_st_heur_restart_get_avdom_nth_get_vdom
        intro!: twl_st_heur_restart_valid_arena[simplified])
    subgoal
      unfolding marked_as_used_pre_def
      by (auto simp: twl_st_heur_restart reason_rel_def)
    subgoal for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b b ba L K D bb
      by (rule only_irred)
    subgoal
      by (auto dest!: twl_st_heur_restart_anaD twl_st_heur_restart_valid_arena simp: arena_lifting)
    subgoal by fast
    apply (rule mop_arena_length_st; assumption)
    apply (rule log_del_clause_heur_log_clause[where r=r and u=u])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def apply -
      by (rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
       (auto simp: twl_st_heur_restart twl_st_heur_restart_ana_def dest: twl_st_heur_restart_valid_arena)
    subgoal premises that
      using get_learned_count_ge[OF that(2-8,12-15,17-33)] that(32-)
      using only_irred[OF that(2-8,12-15,17-33)]
      by auto
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      by (rule length_filter_le)
   subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (force simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>] dest!: set_mset_mono mset_subset_eqD)
    subgoal for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1c x2c b ba L x2b
      using size_mset_mono[of \<open>mset (get_tvdom x2b)\<close> \<open>mset (get_vdom x2b)\<close>]
      by (clarsimp simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
        dest!: valid_arena_vdom_subset)
    subgoal
      by auto
    done
qed

lemma cdcl_twl_mark_clauses_to_delete_alt_def:
  \<open>cdcl_twl_mark_clauses_to_delete S = do {
  _ \<leftarrow> ASSERT (mark_to_delete_clauses_wl_D_heur_pre S);
  T \<leftarrow> mark_to_delete_clauses_wl_D_heur S;
  RETURN (schedule_next_reduction_st (clss_size_resetUS0_st T))
  }\<close>
  unfolding cdcl_twl_mark_clauses_to_delete_def IsaSAT_Profile.start_def IsaSAT_Profile.stop_def
  by auto

lemma learned_clss_count_clss_size_resetUS0_st_le:
  \<open>learned_clss_count (clss_size_resetUS0_st T) \<le> learned_clss_count T\<close> and
  clss_size_resetUS0_st_simp[simp]:
  \<open>get_clauses_wl_heur (clss_size_resetUS0_st T) = get_clauses_wl_heur T\<close>
  by (cases T;clarsimp simp: clss_size_resetUS0_st_def learned_clss_count_def
    clss_size_lcountUS_def clss_size_lcountU0_def clss_size_lcountUE_def
    clss_size_resetUS_def clss_size_resetU0_def clss_size_resetUE_def clss_size_lcountUEk_def
    clss_size_lcount_def
    split: prod.splits)+

lemma learned_clss_count_schedule_next_reduction_st_le:
  \<open>learned_clss_count (schedule_next_reduction_st T) = learned_clss_count T\<close> and
  schedule_next_reduction_st_simp[simp]:
  \<open>get_clauses_wl_heur (schedule_next_reduction_st T) = get_clauses_wl_heur T\<close>
  by (solves \<open>cases T;clarsimp simp: schedule_next_reduction_st_def learned_clss_count_def Let_def
     schedule_next_reduce_st_def\<close>)+

lemma schedule_next_reduction_sttwl_st_heur:
   \<open>(S,T)\<in>twl_st_heur \<Longrightarrow> (schedule_next_reduction_st S, T) \<in> twl_st_heur\<close>
  by (auto simp: twl_st_heur_def schedule_next_reduction_st_def Let_def
    schedule_next_reduce_st_def)

lemma cdcl_twl_mark_clauses_to_delete_cdcl_twl_full_restart_wl_prog_D:
  \<open>(cdcl_twl_mark_clauses_to_delete, cdcl_twl_full_restart_wl_prog) \<in>
     twl_st_heur''''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur''''u r u\<rangle>nres_rel\<close>
  unfolding cdcl_twl_mark_clauses_to_delete_alt_def cdcl_twl_full_restart_wl_prog_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D[THEN fref_to_Down])
  subgoal
    by (rule mark_to_delete_clauses_wl_D_heur_pre_alt_def) fast
  apply (rule twl_st_heur_restartD2)
  subgoal
    by (rule mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur) auto
  subgoal for x y T Ta
    using learned_clss_count_clss_size_resetUS0_st_le[of T]
      learned_clss_count_schedule_next_reduction_st_le[of \<open>clss_size_resetUS0_st T\<close>]
    by (auto simp: mark_to_delete_clauses_wl_post_twl_st_heur twl_st_heur_restart_anaD
        schedule_next_reduction_sttwl_st_heur)
     (auto simp: twl_st_heur_restart_ana_def)
  done

lemma cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog:
  \<open>(cdcl_twl_restart_wl_heur, cdcl_twl_restart_wl_prog) \<in>
    twl_st_heur''''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur''''u r u\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_prog_def cdcl_twl_restart_wl_heur_def
  by (intro frefI nres_relI)
    (refine_rcg lhs_step_If
    cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec[THEN fref_to_Down]
    cdcl_twl_mark_clauses_to_delete_cdcl_twl_full_restart_wl_prog_D[THEN fref_to_Down])

lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_GC_wl_D:
  \<open>(mark_to_delete_clauses_GC_wl_D_heur, mark_to_delete_clauses_GC_wl) \<in>
     twl_st_heur_restart_ana' r u \<rightarrow>\<^sub>f
      \<langle>twl_st_heur_restart_ana' r u\<rangle>nres_rel\<close>
proof -
  have H: \<open>mark_to_delete_clauses_GC_wl_pre S \<and> mark_to_delete_clauses_wl_pre S \<longleftrightarrow>
    mark_to_delete_clauses_GC_wl_pre S\<close> for S
   unfolding mark_to_delete_clauses_GC_wl_pre_def mark_to_delete_clauses_wl_pre_def
   mark_to_delete_clauses_l_GC_pre_def mark_to_delete_clauses_l_pre_def
   by blast
  have mark_to_delete_clauses_GC_wl_D_alt_def:
    \<open>mark_to_delete_clauses_GC_wl  = (\<lambda>S0. do {
      ASSERT(mark_to_delete_clauses_GC_wl_pre S0);
      S \<leftarrow> reorder_vdom_wl S0;
      xs \<leftarrow> collect_valid_indices_wl S;
      l \<leftarrow> SPEC (\<lambda>_::nat. True);
      _ \<leftarrow> SPEC (\<lambda>_::nat\<times>nat. True);
      (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_GC_wl_inv S xs\<^esup>
        (\<lambda>(i, T, xs). i < length xs)
        (\<lambda>(i, T, xs). do {
          b \<leftarrow> RETURN (xs!i \<in># dom_m (get_clauses_wl T));
          if \<not>b then RETURN (i, T, delete_index_and_swap xs i)
          else do {
            ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	    ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
              (\<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2));
            ASSERT(i < length xs);
            if can_del
            then
              RETURN (i, mark_garbage_wl (xs!i) T, delete_index_and_swap xs i)
            else
              RETURN (i+1, T, xs)
          }
        })
        (l, S, xs);
      remove_all_learned_subsumed_clauses_wl S
    })\<close>
   unfolding mark_to_delete_clauses_GC_wl_def reorder_vdom_wl_def bind_to_let_conv Let_def
     nres_monad3 summarize_ASSERT_conv H
   by (auto intro!: ext bind_cong[OF refl])


  have mono: \<open>g = g' \<Longrightarrow> do {f; g} = do {f; g'}\<close>
     \<open>(\<And>x. h x = h' x) \<Longrightarrow> do {x \<leftarrow> f; h x} = do {x \<leftarrow> f; h' x}\<close> for f f' :: \<open>_ nres\<close> and g g' and h h'
    by auto
  have mark_to_delete_clauses_wl_pre_same_atms: \<open>set_mset (all_atms_st T) = set_mset (all_init_atms_st T)\<close>
    if \<open>mark_to_delete_clauses_wl_pre T\<close> for T
    using that unfolding mark_to_delete_clauses_wl_pre_def mark_to_delete_clauses_l_pre_def apply -
    apply normalize_goal+
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[symmetric]) assumption+

  have mark_to_delete_clauses_wl_D_heur_pre_cong:
    \<open>aivdom_inv_dec vdom' (dom_m (get_clauses_wl S')) \<Longrightarrow>
    mset (get_vdom_aivdom (get_aivdom T)) = mset (get_vdom_aivdom vdom') \<Longrightarrow>
     (T, S') \<in> twl_st_heur_restart \<Longrightarrow>
    mark_to_delete_clauses_GC_wl_pre S' \<Longrightarrow>
    mark_to_delete_clauses_GC_wl_D_heur_pre T \<Longrightarrow>
    valid_arena N'' (get_clauses_wl S') (set (get_vdom_aivdom (get_aivdom T))) \<Longrightarrow>
    mark_to_delete_clauses_GC_wl_D_heur_pre (set_clauses_wl_heur N'' (set_aivdom_wl_heur vdom' T))\<close>
    for M' N' D' j W' vm clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount lcount heur old_arena ivdom opts S' vdom' N'' T
    using mset_eq_setD[of \<open>get_vdom_aivdom (get_aivdom T)\<close> \<open>get_vdom_aivdom vdom'\<close>, symmetric] apply -
    unfolding mark_to_delete_clauses_GC_wl_D_heur_pre_def
    by (rule_tac x=S' in exI)
     (clarsimp simp: twl_st_heur_restart_def dest: mset_eq_setD intro: )

   have mark_to_delete_clauses_wl_pre_same_atms: \<open>set_mset (all_atms_st T) = set_mset (all_init_atms_st T)\<close>
    if \<open>mark_to_delete_clauses_GC_wl_pre T\<close> for T
    using that unfolding mark_to_delete_clauses_GC_wl_pre_def mark_to_delete_clauses_l_pre_def
      mark_to_delete_clauses_l_GC_pre_def apply -
    apply normalize_goal+
    by (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[symmetric]) assumption+

  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart_ana' r u \<and> V = T \<and>
         (mark_to_delete_clauses_GC_wl_pre T \<longrightarrow> mark_to_delete_clauses_GC_wl_pre V) \<and>
          (mark_to_delete_clauses_GC_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_GC_wl_D_heur_pre U) \<and>
         (\<forall>C\<in>set (get_tvdom U). \<not>irred (get_clauses_wl V) C)}
         (reorder_vdom_wl T)\<close> (is \<open>_ \<le> \<Down>?sort _\<close>)
    if \<open>(S, T) \<in> twl_st_heur_restart_ana' r u\<close> and \<open>mark_to_delete_clauses_GC_wl_pre T\<close> for S T
    supply [simp del] = EQ_def
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def Let_def
    apply (refine_rcg ASSERT_leI)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
      dest!: valid_arena_vdom_subset size_mset_mono)
      apply (rule specify_left_RES)
      apply (rule_tac  N = \<open>get_clauses_wl T\<close> and M' = \<open>get_trail_wl T\<close> and
        \<A> = \<open>all_init_atms_st T\<close> and
        NUE = \<open>get_unit_clauses_wl T + get_subsumed_clauses_wl T + get_clauses0_wl T\<close> in
     isa_isa_gather_candidates_for_reduction_remove_deleted_clauses_from_avdom2[unfolded conc_fun_RES])
    subgoal
      by (case_tac T; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case)
    subgoal
      by (case_tac T; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case)
    subgoal
      by (case_tac T; auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def mem_Collect_eq prod.case
        all_init_atms_st_def)
    subgoal
      unfolding all_atms_st_def[symmetric]
      by (rule mark_to_delete_clauses_wl_pre_same_atms)
    apply (subst case_prod_beta)
    apply (intro ASSERT_leI)
    subgoal for arena_aivdom
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff(1)[symmetric]
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
        intro!: exI[of _ \<open>get_clauses_wl T\<close>] exI[of _ \<open>set (get_vdom S)\<close>]
        dest: set_mset_mono mset_subset_eqD)
    subgoal by (auto simp: EQ_def)
    subgoal
      by (cases T)
       (clarsimp simp add: twl_st_heur_restart_ana_def valid_arena_vdom_subset twl_st_heur_restart_def aivdom_inv_dec_alt_def case_prod_beta split: 
        dest!: size_mset_mono valid_arena_vdom_subset)
    subgoal for arena_aivdom
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder[of _ \<open>get_clauses_wl T\<close>])
      subgoal
        by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest: mset_eq_setD)
      subgoal
        by (cases \<open>arena_aivdom\<close>; cases \<open>get_content (snd arena_aivdom)\<close>)
         (simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
      subgoal
        apply auto
        apply (auto simp: learned_clss_count_def (* twl_st_heur_restart_ana_def twl_st_heur_restart_def *)
          intro: mark_to_delete_clauses_wl_D_heur_pre_cong
          intro: aivdom_inv_cong2
          dest: mset_eq_setD)
          apply (auto 4 3 simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def 
            intro: aivdom_inv_cong2 dest: mset_eq_setD; fail)[]
          apply (rule mark_to_delete_clauses_wl_D_heur_pre_cong)
          apply assumption+
          apply (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
          done
          done
        done

  have [refine0]: \<open>RETURN (get_tvdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_tvdom x \<and>
       (\<forall>C\<in>set (get_tvdom x). \<not>irred (get_clauses_wl y) C)} (collect_valid_indices_wl y)\<close>
    (is \<open>_ \<le> \<Down> ?indices _\<close>)
    if
      \<open>(x, y) \<in> ?sort S T\<close> and
      \<open>mark_to_delete_clauses_GC_wl_D_heur_pre x\<close>
    for x y S T
  proof -
    show ?thesis using that by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed

  have init:
    \<open>(u', xs) \<in> ?indices S Sa \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart_ana' r u \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
    {(Sa', (T, xs)). (Sa', T) \<in> twl_st_heur_restart_ana' r u \<and> xs = get_tvdom Sa' \<and>
    set (get_tvdom Sa') \<subseteq> set (get_tvdom S) \<and> (\<forall>C\<in>set (get_tvdom Sa'). \<not>irred (get_clauses_wl T) C)}\<close>
    (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<in> ?R\<close>)
       for x y S Sa xs l la u'
    by auto

  define reason_rel where
    \<open>reason_rel K x1a \<equiv> {(C, _ :: unit).
          (C \<noteq> None) = (Propagated K (the C) \<in> set (get_trail_wl x1a)) \<and>
          (C = None) = (Decided K \<in> set (get_trail_wl x1a) \<or>
             K \<notin> lits_of_l (get_trail_wl x1a)) \<and>
         (\<forall>C1. (Propagated K C1 \<in> set (get_trail_wl x1a) \<longrightarrow> C1 = the C))}\<close> for K :: \<open>nat literal\<close> and x1a


  have already_deleted:
    \<open>((x1b,  delete_index_vdom_heur x1b x2b), x1, x1a, delete_index_and_swap x2a x1) \<in> ?R S\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close> and
      \<open>mark_to_delete_clauses_GC_wl_D_heur_pre x\<close> and
      \<open>(S, Sa) \<in> ?sort x y\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x') \<in> ?R S\<close> and
      nempty: \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      le: \<open>x1b < length (get_tvdom x2b)\<close> and
      \<open>access_tvdom_at_pre x2b x1b\<close> and
      ba: \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
        \<open>\<not>ba\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa ba b
  proof -
    show ?thesis
      using xx nempty le ba unfolding st
      by (cases \<open>get_tvdom x2b\<close> rule: rev_cases)
       (auto 4 3 simp: twl_st_heur_restart_ana_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If learned_clss_count_def
          aivdom_inv_removed_inactive
        intro: valid_arena_extra_information_mark_to_delete'
        intro!: aivdom_inv_dec_removed_inactive_tvdom
        dest!: in_set_butlastD in_vdom_m_fmdropD
        elim!: in_set_upd_cases)
  qed

  have mop_clause_not_marked_to_delete_heur:
    \<open>mop_clause_not_marked_to_delete_heur x2b (get_tvdom x2b ! x1b)
        \<le> SPEC
           (\<lambda>c. (c, x2a ! x1 \<in># dom_m (get_clauses_wl x1a))
                \<in> {(b, b'). (b,b') \<in> bool_rel \<and> (b \<longleftrightarrow> x2a ! x1 \<in># dom_m (get_clauses_wl x1a))})\<close>
    if
      \<open>(xa, x') \<in> ?R S\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_GC_wl_inv Sa xs x'\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close>
    for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b
    unfolding mop_clause_not_marked_to_delete_heur_def
    apply refine_vcg
    subgoal
      using that by blast
    subgoal
      using that by (auto simp: twl_st_heur_restart arena_lifting dest: twl_st_heur_restart(2) dest!: twl_st_heur_restart_anaD)
    done
  have incr_reduction_stat: \<open>incr_restart_stat (set_stats_size_limit_st lbd sze T)
    \<le> \<Down> (twl_st_heur_restart_ana' r u) (remove_all_learned_subsumed_clauses_wl S)\<close>
    if \<open>(T, S) \<in> twl_st_heur_restart_ana' r u\<close> for S T i u lbd sze
    using that
    by (cases S; cases T)
      (auto simp: conc_fun_RES incr_restart_stat_def learned_clss_count_def set_stats_size_limit_st_def
        twl_st_heur_restart_ana_def twl_st_heur_restart_def
      remove_all_learned_subsumed_clauses_wl_def clss_size_corr_def
      clss_size_lcountUE_def clss_size_lcountUS_def clss_size_def
      clss_size_resetUS_def clss_size_lcount_def clss_size_lcountU0_def incr_reduction_stat_def
        RES_RETURN_RES)

  have only_irred: \<open>\<not> irred (get_clauses_wl x1a) (x2a ! x1)\<close> (is ?A) and
    get_learned_count_ge: \<open>Suc 0 \<le> clss_size_lcount (get_learned_count x2b)\<close> (is ?B)
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close> and
      \<open>mark_to_delete_clauses_GC_wl_pre y\<close> and
      \<open>mark_to_delete_clauses_GC_wl_D_heur_pre x\<close> and
      \<open>(S, Sa) \<in> ?sort x y\<close> and
      indices: \<open>(uu, xs) \<in> ?indices S Sa\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur x)\<close> and
      xx: \<open>(xa, x') \<in> ?R S\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_GC_wl_inv Sa xs x'\<close> and
      st: \<open>x2 = (x1a, x2a)\<close> \<open>x' = (x1, x2)\<close> \<open>xa = (x1b, x2b)\<close> and
      \<open>x1b < length (get_tvdom x2b)\<close> and
      \<open>access_tvdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close> and
      dom: \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
        \<open>\<not> \<not> b\<close>
        \<open>\<not> \<not> ba\<close> and
      \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
      \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close> and
      \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close> and
      \<open>length (get_clauses_wl_heur x2b) \<le> length (get_clauses_wl_heur x)\<close> and
      \<open>length (get_tvdom x2b) \<le> length (get_clauses_wl_heur x2b)\<close> and
      \<open>arena_is_valid_clause_idx (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b)\<close>
      for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b b ba L K D bb
    proof -
      have \<open>get_tvdom x2b ! x1 \<in> set (get_tvdom x2b)\<close> and
        x: \<open>(x2b, x1a) \<in> twl_st_heur_restart_ana r\<close>
      using that by (auto dest: simp: arena_lifting twl_st_heur_restart)
    then show ?A
      using indices xx
      by (auto dest: twl_st_heur_restart_anaD twl_st_heur_restart_valid_arena
        simp: arena_lifting twl_st_heur_restart st)
    then show ?B
      using dom x by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def ran_m_def
        dest!: multi_member_split
        dest!: clss_size_corr_restart_rew)
  qed
  have length_filter_le: \<open>\<Down> nat_rel ((RETURN \<circ> (\<lambda>c. length (get_clauses_wl x1a \<propto> c))) (get_tvdom x2b ! x1b))
     \<le> SPEC
        (\<lambda>wasted.
         do {
        _ \<leftarrow> log_del_clause_heur x2b (get_tvdom x2b ! x1b);
        _ \<leftarrow> ASSERT
          (mark_garbage_pre (get_clauses_wl_heur x2b, get_tvdom x2b ! x1b) \<and>
           1 \<le> clss_size_lcount (get_learned_count x2b) \<and> x1b < length (get_tvdom x2b));
        RETURN (x1b, mark_garbage_heur3 (get_tvdom x2b ! x1b) x1b (incr_wasted_st (word_of_nat wasted) x2b))
         } \<le> SPEC
           (\<lambda>c. (c, x1, mark_garbage_wl (x2a ! x1) x1a, delete_index_and_swap x2a x1) \<in> ?R S))\<close>
    if H:
      \<open>(x, y) \<in> twl_st_heur_restart_ana' r u\<close>
      \<open>mark_to_delete_clauses_GC_wl_pre y\<close>
      \<open>mark_to_delete_clauses_GC_wl_D_heur_pre x\<close>
      \<open>(S, Sa) \<in> ?sort x y\<close>
      \<open>(uu, xs) \<in> ?indices S Sa\<close>
      \<open>(l, la) \<in> nat_rel\<close>
      \<open>la \<in> {_. True}\<close>
      \<open>length (get_tvdom S) \<le> length (get_clauses_wl_heur x)\<close>
      \<open>(xa, x') \<in> ?R S\<close>
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_tvdom S)\<close>
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close>
      \<open>mark_to_delete_clauses_GC_wl_inv Sa xs x'\<close>
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close>
      \<open>x1b < length (get_tvdom x2b)\<close>
      \<open>access_tvdom_at_pre x2b x1b\<close>
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_tvdom x2b ! x1b)\<close>
      \<open>(b, ba) \<in> {(b, b'). (b, b') \<in> bool_rel \<and> b = (x2a ! x1 \<in># dom_m (get_clauses_wl x1a))}\<close>
      \<open>\<not> \<not> b\<close>
      \<open>\<not> \<not> ba\<close>
      \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close>
      \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      \<open>access_lit_in_clauses_heur_pre ((x2b, get_tvdom x2b ! x1b), 0)\<close>
      \<open>length (get_clauses_wl_heur x2b) \<le> length (get_clauses_wl_heur x)\<close>
      \<open>length (get_tvdom x2b) \<le> length (get_clauses_wl_heur x2b)\<close>
      \<open>arena_is_valid_clause_idx (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b)\<close>
      \<open>(arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2, can_del)
    \<in> bool_rel\<close>
      \<open>x1 < length x2a\<close>
      \<open>arena_length (get_clauses_wl_heur x2b) (get_tvdom x2b ! x1b) \<noteq> 2\<close>
      can_del
    for x y S Sa xs l la xa x' x1 x2 x1a x2a x1b x2b b ba can_del D L K bb uu
  proof -
      have [simp]: \<open>mark_garbage_heur3 i C (incr_wasted_st b S) = incr_wasted_st b (mark_garbage_heur3 i C S)\<close> for i C S b
        by (cases S; auto simp: mark_garbage_heur3_def incr_wasted_st_def)
      have \<open>mark_garbage_pre (get_clauses_wl_heur x2b, get_tvdom x2b ! x1b)\<close>
        \<open>x1b < length (get_tvdom x2b)\<close>
        using that
        unfolding prod.simps mark_garbage_pre_def
          arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def apply -
        by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
         (auto simp: twl_st_heur_restart twl_st_heur_restart_ana_def dest: twl_st_heur_restart_valid_arena)
      moreover have 0: \<open>Suc 0 \<le> clss_size_lcount (get_learned_count x2b)\<close>
         \<open>\<not> irred (get_clauses_wl x1a) (x2a ! x1)\<close> 
        using get_learned_count_ge[OF that(1-27)] only_irred[OF that(1-27)] by auto
      moreover have \<open>(mark_garbage_heur3 (get_tvdom x2b ! x1) x1
        (incr_wasted_st (word_of_nat (length (get_clauses_wl x1a \<propto> (get_tvdom x2b ! x1)))) x2b),
        mark_garbage_wl (get_tvdom x2b ! x1) x1a)
        \<in> twl_st_heur_restart_ana r\<close>
        by (use that 0 in
          \<open>auto intro!: incr_wasted_st mark_garbage_heur_wl_ana simp: twl_st_heur_restart
          learned_clss_count_mark_garbage_heur3
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_anaD\<close>)
      moreover have \<open>learned_clss_count
        (mark_garbage_heur3 (get_tvdom x2b ! x1) x1
        (incr_wasted_st (word_of_nat (length (get_clauses_wl x1a \<propto> (get_tvdom x2b ! x1)))) x2b))
        \<le> u\<close>
        by (use that 0 in
          \<open>auto intro!: incr_wasted_st mark_garbage_heur_wl_ana simp: twl_st_heur_restart
          learned_clss_count_mark_garbage_heur3
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_anaD\<close>)
      moreover have \<open>xb \<in> set (get_tvdom S)\<close>
        if \<open>xb \<in> set (butlast ((get_tvdom x2b)[x1 := last (get_tvdom x2b)]))\<close> for xb
      proof -
        have \<open>xb \<in> set (get_tvdom x2b)\<close>
          using that H by (auto dest!: in_set_butlastD)
            (metis Misc.last_in_set in_set_upd_eq len_greater_imp_nonempty)
        then show ?thesis
          using H by auto
      qed
      moreover have \<open>\<not>irred (get_clauses_wl (mark_garbage_wl (get_tvdom x2b ! x1) x1a)) C\<close>
        if \<open>C \<in> set (butlast ((get_tvdom x2b)[x1 := last (get_tvdom x2b)]))\<close> for C
      proof -
        have a: \<open>distinct (get_tvdom x2b)\<close> \<open>x1 < length (get_tvdom x2b)\<close>
          using  H(9-15) by (auto simp: twl_st_heur_restart_ana_def
            twl_st_heur_restart_def aivdom_inv_dec_alt_def)
        then have 1: \<open>get_tvdom x2b = take x1 (get_tvdom x2b) @ get_tvdom x2b ! x1 # drop (Suc x1) (get_tvdom x2b)\<close>
          by (subst append_take_drop_id[of x1, symmetric], subst Cons_nth_drop_Suc[symmetric])
           auto
        have \<open>set (delete_index_and_swap (get_tvdom x2b) x1) =
          set (get_tvdom x2b) - {get_tvdom x2b!x1}\<close>
          using a
          apply (subst (asm) (2)1, subst (asm) (1)1)
          apply (subst (2)1, subst (1)1)
          apply (cases \<open>drop (Suc x1) (get_tvdom x2b)\<close> rule: rev_cases)
          by (auto simp: nth_append list_update_append1 list_update_append2 butlast_append
            dest: in_set_butlastD)
        then have [simp]: \<open>C \<noteq> get_tvdom x2b ! x1\<close>
          using that by auto
        show ?thesis
          using that H
          apply (cases x1a)
          apply (auto simp: mark_garbage_wl_def)
          by (metis Misc.last_in_set in_set_butlastD in_set_upd_cases len_greater_imp_nonempty)
      qed
      ultimately show ?thesis apply -
        using that
        apply (auto intro!: ASSERT_leI)
        apply (subst bind_rule_complete)
        apply (rule order_trans)
        apply (rule log_del_clause_heur_log_clause[where r=r and u=u])
        by auto
  qed
  show ?thesis
    supply sort_vdom_heur_def[simp] twl_st_heur_restart_anaD[dest] [[goals_limit=1]]
    unfolding mark_to_delete_clauses_GC_wl_D_heur_alt_def mark_to_delete_clauses_GC_wl_D_alt_def
      access_lit_in_clauses_heur_def
    apply (intro frefI nres_relI)
    apply (refine_vcg sort_vdom_heur_reorder_vdom_wl[THEN fref_to_Down] incr_reduction_stat find_largest_lbd_and_size)
    subgoal
      unfolding mark_to_delete_clauses_GC_wl_D_heur_pre_def by fast
    apply assumption
    subgoal by auto
    subgoal for x y S T unfolding number_clss_to_keep_def by (cases S) (auto)
    apply (solves auto)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
       dest!: valid_arena_vdom_subset size_mset_mono)
    apply (rule init; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_tvdom_at_pre_def)
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
        prod.simps
      by (rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
         (auto simp: twl_st_heur_restart
          intro!: twl_st_heur_restart_valid_arena[simplified]
          dest: twl_st_heur_restart_get_tvdom_nth_get_vdom[simplified])
    apply (rule mop_clause_not_marked_to_delete_heur; assumption)
    subgoal for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b
      by (auto simp: twl_st_heur_restart)
    subgoal
      by (rule already_deleted)
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_tvdom x2b ! x1b\<close>], simp add: aivdom_inv_dec_alt_def,
        rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>])
        (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal premises p using p(7-)
      by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
        dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl (fst x2c)\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart intro!: twl_st_heur_restart_valid_arena[simplified]
        dest: twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal
      unfolding marked_as_used_pre_def
      by (auto simp: twl_st_heur_restart reason_rel_def)
    subgoal
      by (auto dest!: twl_st_heur_restart_anaD twl_st_heur_restart_valid_arena[simplified]
        simp: arena_lifting)
    subgoal by fast
    subgoal for x y S Sa u xs l la _ _ x1 x2 xb x' x1c x2c x1a x2a x1b x2b
      unfolding mop_arena_length_st_def
      apply (rule mop_arena_length[THEN fref_to_Down_curry, THEN order_trans,
        of \<open>get_clauses_wl x1a\<close> \<open>get_tvdom x2b ! x1b\<close> _ _ \<open>set (get_vdom x2b)\<close>])
      subgoal
        by auto
      subgoal
        by (auto simp: twl_st_heur_restart_valid_arena[simplified])
      subgoal
        by (rule length_filter_le)
     done
   subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (force simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>] dest!: set_mset_mono mset_subset_eqD)
    subgoal for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1c x2c b ba L x2b
      using size_mset_mono[of \<open>mset (get_tvdom x2b)\<close> \<open>mset (get_vdom x2b)\<close>]
      by (clarsimp simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def aivdom_inv_dec_alt_def
        dest!: valid_arena_vdom_subset)
    subgoal
      by auto
    done
qed



definition isasat_GC_entry :: \<open>_\<close> where
\<open>isasat_GC_entry \<A> vdom0 arena_old W'  = {((arena\<^sub>o, (arena, aivdom)), (N\<^sub>o, N)). valid_arena arena\<^sub>o N\<^sub>o vdom0 \<and> valid_arena arena N (set (get_vdom_aivdom aivdom)) \<and> vdom_m \<A> W' N\<^sub>o \<subseteq> vdom0 \<and> dom_m N = mset (get_vdom_aivdom aivdom) \<and>
  arena_is_packed arena N \<and>
  aivdom_inv_strong_dec aivdom (dom_m N) \<and>
  length arena\<^sub>o = length arena_old \<and>
    move_is_packed arena\<^sub>o N\<^sub>o arena N}\<close>

definition isasat_GC_refl :: \<open>_\<close> where
\<open>isasat_GC_refl \<A> vdom0 arena_old = {((arena\<^sub>o, (arena, aivdom), W), (N\<^sub>o, N, W')). valid_arena arena\<^sub>o N\<^sub>o vdom0 \<and> valid_arena arena N (set (get_vdom_aivdom aivdom)) \<and>
     (W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N\<^sub>o \<subseteq> vdom0 \<and> dom_m N = mset (get_vdom_aivdom aivdom) \<and>
  arena_is_packed arena N \<and> aivdom_inv_strong_dec aivdom (dom_m N) \<and>
  length arena\<^sub>o = length arena_old \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. length (W' L) \<le> length arena\<^sub>o) \<and>move_is_packed arena\<^sub>o N\<^sub>o arena N}\<close>

lemma move_is_packed_empty[simp]: \<open>valid_arena arena N vdom \<Longrightarrow> move_is_packed arena N [] fmempty\<close>
  by (auto simp: move_is_packed_def valid_arena_ge_length_clauses)

lemma move_is_packed_append:
  assumes
    dom: \<open>C \<in># dom_m x1a\<close> and
    E: \<open>length E = length (x1a \<propto> C) + header_size (x1a \<propto> C)\<close> \<open>(fst E') = (x1a \<propto> C)\<close>
     \<open>n = header_size (x1a \<propto> C)\<close> and
    valid: \<open>valid_arena x1d x2a D'\<close> and
    packed: \<open>move_is_packed x1c x1a x1d x2a\<close>
  shows \<open>move_is_packed (extra_information_mark_to_delete x1c C)
          (fmdrop C x1a)
          (x1d @ E)
          (fmupd (length x1d + n) E' x2a)\<close>
proof -
  have [simp]: \<open>(\<Sum>x\<in>#remove1_mset C
          (dom_m
            x1a). length
                   (fst (the (if x = C then None
                              else fmlookup x1a x))) +
                  header_size
                   (fst (the (if x = C then None
                              else fmlookup x1a x)))) =
     (\<Sum>x\<in>#remove1_mset C
          (dom_m
            x1a). length
                   (x1a \<propto> x) +
                  header_size
                   (x1a \<propto> x))\<close>
   by (rule sum_mset_cong)
    (use distinct_mset_dom[of x1a] in \<open>auto dest!: simp: distinct_mset_remove1_All\<close>)
  have [simp]: \<open>(length x1d + header_size (x1a \<propto> C)) \<notin># (dom_m x2a)\<close>
    using valid arena_lifting(2) by blast
  have [simp]: \<open>(\<Sum>x\<in>#(dom_m x2a). length
                    (fst (the (if length x1d + header_size (x1a \<propto> C) = x
                               then Some E'
                               else fmlookup x2a x))) +
                   header_size
                    (fst (the (if length x1d + header_size (x1a \<propto> C) = x
                               then Some E'
                               else fmlookup x2a x)))) =
    (\<Sum>x\<in>#dom_m x2a. length
                    (x2a \<propto> x) +
                   header_size
                    (x2a \<propto> x))\<close>
   by (rule sum_mset_cong)
    (use distinct_mset_dom[of x2a] in \<open>auto dest!: simp: distinct_mset_remove1_All\<close>)
  show ?thesis
    using packed dom E
    by (auto simp: move_is_packed_def split: if_splits dest!: multi_member_split)
qed
(*
lemma aivdom_inv_intro_add_mset_irred:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set vdom \<Longrightarrow> aivdom_inv (vdom, avdom, ivdom, tvdom) d \<Longrightarrow> aivdom_inv (vdom @ [C], avdom, ivdom @ [C], tvdom) (add_mset C d)\<close>
  unfolding aivdom_inv_alt_def
  by (cases \<open>C \<in> (set avdom \<union> set ivdom)\<close>)
   (auto dest: subset_mset_imp_subset_add_mset)
*)
lemma isasat_GC_clauses_prog_copy_wl_entry:
  assumes \<open>valid_arena arena N vdom0\<close> and
    \<open>valid_arena arena' N' (set (get_vdom_aivdom aivdom))\<close> and
    vdom: \<open>vdom_m \<A> W N \<subseteq> vdom0\<close> and
    L: \<open>atm_of A \<in># \<A>\<close> and
    L'_L: \<open>(A', A) \<in> nat_lit_lit_rel\<close> and
    W: \<open>(W' , W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    \<open>dom_m N' = mset (get_vdom_aivdom aivdom)\<close> and
   \<open>arena_is_packed arena' N'\<close> and
    ivdom: \<open>aivdom_inv_strong_dec aivdom (dom_m N')\<close> and
    r: \<open>length arena = r\<close> and
    le: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. length (W L) \<le> length arena\<close> and
    packed: \<open>move_is_packed arena N arena' N'\<close>
  shows \<open>isasat_GC_clauses_prog_copy_wl_entry arena W' A' (arena', aivdom)
     \<le> \<Down> (isasat_GC_entry \<A> vdom0 arena W)
         (cdcl_GC_clauses_prog_copy_wl_entry N (W A) A N')\<close>
     (is \<open>_ \<le> \<Down> (?R) _\<close>)
proof -
  have A: \<open>A' = A\<close> and K[simp]: \<open>W' ! nat_of_lit A = W A\<close>
    using L'_L L W apply auto
    by (cases A) (auto simp: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset dest!: multi_member_split)
  have A_le: \<open>nat_of_lit A < length W'\<close>
    using W L by (cases A; auto simp: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset dest!: multi_member_split)
  have length_slice: \<open>C \<in># dom_m x1a \<Longrightarrow> valid_arena x1c x1a vdom' \<Longrightarrow>
      length
     (Misc.slice (C - header_size (x1a \<propto> C))
       (C + arena_length x1c C) x1c) =
    arena_length x1c C + header_size (x1a \<propto> C)\<close> for x1c x1a C vdom'
     using arena_lifting(1-4,10)[of x1c x1a vdom' C]
    by (auto simp: header_size_def slice_len_min_If min_def split: if_splits)
  show ?thesis
    unfolding isasat_GC_clauses_prog_copy_wl_entry_def cdcl_GC_clauses_prog_copy_wl_entry_def prod.case A
    arena_header_size_def[symmetric]
    apply (refine_vcg ASSERT_leI WHILET_refine[where R = \<open>nat_rel \<times>\<^sub>r ?R\<close>])
    subgoal using A_le by (auto simp: isasat_GC_entry_def)
    subgoal using le L K by (cases A) (auto dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using assms by (auto simp: isasat_GC_entry_def)
    subgoal using W L by auto
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      using vdom L
      unfolding arena_is_valid_clause_vdom_def K isasat_GC_entry_def
      by (cases A)
        (force dest!: multi_member_split simp: vdom_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)+
    subgoal
      using vdom L
      unfolding arena_is_valid_clause_vdom_def K isasat_GC_entry_def
      by (subst arena_dom_status_iff)
        (cases A ; auto dest!: multi_member_split simp: arena_lifting arena_dom_status_iff
            vdom_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset; fail)+
   subgoal
     unfolding arena_is_valid_clause_idx_def isasat_GC_entry_def
     by auto
   subgoal unfolding isasat_GC_entry_def move_is_packed_def arena_is_packed_def
       by (auto simp: valid_arena_header_size arena_lifting dest!: multi_member_split)
   subgoal using r by (auto simp: isasat_GC_entry_def)
   subgoal by (auto dest: valid_arena_header_size simp: arena_lifting dest!: valid_arena_vdom_subset multi_member_split simp: arena_header_size_def isasat_GC_entry_def aivdom_inv_strong_dec_alt_def
    split: if_splits)
   subgoal by (auto simp: isasat_GC_entry_def aivdom_inv_strong_dec_alt_def dest!: size_mset_mono)
   subgoal by (auto simp: isasat_GC_entry_def aivdom_inv_strong_dec_alt_def dest!: size_mset_mono)
   subgoal by (auto simp: isasat_GC_entry_def aivdom_inv_strong_dec_alt_def dest!: size_mset_mono)
   subgoal 
     by (force simp: isasat_GC_entry_def dest: arena_lifting(2))
   subgoal by (auto simp: arena_header_size_def)
   subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d D
     using valid_arena_in_vdom_le_arena(1)[of x1d x2a \<open>set (get_vdom_aivdom x2d)\<close> D] apply -
(*TODO slow*)
     by (rule order_trans[OF fm_mv_clause_to_new_arena])
      (force intro: valid_arena_extra_information_mark_to_delete'
         simp: arena_lifting remove_1_mset_id_iff_notin
            mark_garbage_pre_def isasat_GC_entry_def min_def
            valid_arena_header_size
       simp del: aivdom_inv.simps
       dest: in_vdom_m_fmdropD arena_lifting(2)
       intro!: arena_is_packed_append_valid subset_mset_trans_add_mset
       aivdom_inv_dec_intro_init_strong_add_mset aivdom_inv_dec_intro_learned_strong_add_mset
       move_is_packed_append length_slice aivdom_inv_intro_add_mset)+
   subgoal
     by auto
   subgoal
     by auto
   done
 qed

lemma isasat_GC_clauses_prog_single_wl:
  assumes
    \<open>(X, X') \<in> isasat_GC_refl \<A> vdom0 arena0\<close> and
    X: \<open>X = (arena, (arena', aivdom), W)\<close> \<open>X' = (N, N', W')\<close> and
    L: \<open>A \<in># \<A>\<close> and
    st: \<open>(A, A') \<in> Id\<close> and
    st': \<open>narena = (arena', aivdom)\<close> and
    ae: \<open>length arena0 = length arena\<close> and
    le_all: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. length (W' L) \<le> length arena\<close>
  shows \<open>isasat_GC_clauses_prog_single_wl arena narena  W A
     \<le> \<Down> (isasat_GC_refl \<A> vdom0 arena0)
         (cdcl_GC_clauses_prog_single_wl N W' A' N')\<close>
     (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  let ?vdom = \<open>get_vdom_aivdom aivdom\<close>
  have H:
    \<open>valid_arena arena N vdom0\<close>
    \<open>valid_arena arena' N' (set ?vdom)\<close> and
    vdom: \<open>vdom_m \<A> W' N \<subseteq> vdom0\<close> and
    L: \<open>A \<in># \<A>\<close> and
    eq: \<open>A' = A\<close> and
    WW': \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    vdom_dom: \<open>dom_m N' = mset ?vdom\<close> and
    packed: \<open>arena_is_packed arena' N'\<close> and
    aivdom: \<open>aivdom_inv_strong_dec aivdom (dom_m N')\<close> and
    packed2: \<open>move_is_packed arena N arena' N'\<close> and
    incl: \<open>vdom_m \<A> W' N \<subseteq> vdom0\<close>
    using assms X st by (auto simp: isasat_GC_refl_def)

  have vdom2: \<open>vdom_m \<A> W' x1 \<subseteq> vdom0 \<Longrightarrow> vdom_m \<A> (W'(L := [])) x1 \<subseteq> vdom0\<close> for x1 L
    by (force simp: vdom_m_def dest!: multi_member_split)
  have vdom_m_upd: \<open>x \<in> vdom_m \<A> (W(Pos A := [], Neg A := [])) N \<Longrightarrow> x \<in> vdom_m \<A> W N\<close> for x W A N
    by (auto simp: image_iff vdom_m_def dest: multi_member_split)
  have vdom_m3: \<open>x \<in> vdom_m \<A> W a \<Longrightarrow> dom_m a \<subseteq># dom_m b \<Longrightarrow> dom_m b \<subseteq># dom_m c \<Longrightarrow>x \<in> vdom_m \<A> W c\<close> for a b c W x
    unfolding vdom_m_def by auto
  have W: \<open>(W[2 * A := [], Suc (2 * A) := []], W'(Pos A := [], Neg A := []))
       \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> for A
    using WW' unfolding map_fun_rel_def
    apply clarify
    apply (intro conjI)
    apply auto[]
    apply (drule multi_member_split)
    apply (case_tac L)
    apply (auto dest!: multi_member_split)
    done
  have le: \<open>nat_of_lit (Pos A) < length W\<close> \<open>nat_of_lit (Neg A) < length W\<close>
    using WW' L by (auto dest!: multi_member_split simp: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
  have [refine0]: \<open>RETURN (Pos A) \<le> \<Down> Id (RES {Pos A, Neg A})\<close> by auto
  have vdom_upD:\<open> x \<in> vdom_m \<A> (W'(Pos A := [], Neg A := [])) xd \<Longrightarrow> x \<in>  vdom_m \<A> (\<lambda>a. if a = Pos A then [] else W' a) xd\<close>
    for W' a A x xd
    by (auto simp: vdom_m_def)
  show ?thesis
    unfolding isasat_GC_clauses_prog_single_wl_def
      cdcl_GC_clauses_prog_single_wl_def eq st' isasat_GC_refl_def
    apply (refine_vcg
      isasat_GC_clauses_prog_copy_wl_entry[where r= \<open>length arena\<close> and \<A> = \<A>])
    subgoal using le by auto
    subgoal using le by auto
    apply (rule H(1); fail)
    apply (rule H(2); fail)
    subgoal using incl by auto
    subgoal using L by auto
    subgoal using WW' by auto
    subgoal using vdom_dom by blast
    subgoal using packed by blast
    subgoal using aivdom by blast
    subgoal by blast
    subgoal using le_all by auto
    subgoal using packed2 by auto
    subgoal using ae by (auto simp: isasat_GC_entry_def)
    apply (solves \<open>auto simp: isasat_GC_entry_def\<close>)
    apply (solves \<open>auto simp: isasat_GC_entry_def\<close>)
    apply (rule vdom2; auto)
    supply isasat_GC_entry_def[simp]
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using L by auto
    subgoal using L by auto
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' le_all by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' le_all by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' le_all by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' le_all by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using W ae le_all aivdom by (auto simp: dest!: vdom_upD)
    done
qed

definition cdcl_GC_clauses_prog_wl2  where
  \<open>cdcl_GC_clauses_prog_wl2 = (\<lambda>N0 \<A>0 WS. do {
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset \<A>0);
    (_, (N, N', WS)) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_GC_clauses_prog_wl_inv \<A> N0\<^esup>
      (\<lambda>(\<B>, _). \<B> \<noteq> {#})
      (\<lambda>(\<B>, (N, N', WS)). do {
        ASSERT(\<B> \<noteq> {#});
        A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
        (N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_single_wl N WS A N';
        RETURN (remove1_mset A \<B>, (N, N', WS))
      })
      (\<A>, (N0, fmempty, WS));
    RETURN (N, N', WS)
  })\<close>


lemma cdcl_GC_clauses_prog_wl_inv_cong_empty:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow>
  cdcl_GC_clauses_prog_wl_inv \<A> N ({#}, x) \<Longrightarrow> cdcl_GC_clauses_prog_wl_inv \<B> N ({#}, x)\<close>
  by (auto simp: cdcl_GC_clauses_prog_wl_inv_def)

lemma isasat_GC_clauses_prog_wl2:
  assumes \<open>valid_arena arena\<^sub>o N\<^sub>o vdom0\<close> and
    \<open>valid_arena arena N (set vdom)\<close> and
    vdom: \<open>vdom_m \<A> W' N\<^sub>o \<subseteq> vdom0\<close> and
    vmtf: \<open>ns \<in> bump_heur \<A> M\<close> and
    nempty: \<open>\<A> \<noteq> {#}\<close> and
    W_W': \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close> and old: \<open>old_arena = []\<close> and
    le_all: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. length (W' L) \<le> length arena\<^sub>o\<close>
 shows
    \<open>isasat_GC_clauses_prog_wl2 ns (arena\<^sub>o, (old_arena, empty_aivdom aivdom), W)
        \<le> \<Down> ({((arena\<^sub>o', (arena, aivdom), W), (N\<^sub>o', N, W')). valid_arena arena\<^sub>o' N\<^sub>o' vdom0 \<and>
                valid_arena arena N (set (get_vdom_aivdom aivdom)) \<and>
       (W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N\<^sub>o' \<subseteq> vdom0 \<and>
        cdcl_GC_clauses_prog_wl_inv \<A> N\<^sub>o ({#}, N\<^sub>o', N, W') \<and> dom_m N = mset (get_vdom_aivdom aivdom) \<and>
         arena_is_packed arena N \<and> aivdom_inv_strong_dec aivdom (dom_m N) \<and>
       length arena\<^sub>o' = length arena\<^sub>o})
         (cdcl_GC_clauses_prog_wl2 N\<^sub>o \<A> W')\<close>
proof -
  define f where
    \<open>f A \<equiv> (\<lambda>(arena\<^sub>o, arena, W). isasat_GC_clauses_prog_single_wl arena\<^sub>o arena W A)\<close> for A :: nat
  let ?R = \<open>{((\<A>', arena\<^sub>o', (arena, vdom), W), (\<A>'', N\<^sub>o', N, W')). \<A>' = \<A>'' \<and>
      ((arena\<^sub>o', (arena, vdom), W), (N\<^sub>o', N, W')) \<in> isasat_GC_refl \<A> vdom0 arena\<^sub>o \<and>
      length arena\<^sub>o' = length arena\<^sub>o}\<close>
  have H: \<open>(X, X') \<in> ?R \<Longrightarrow> X = (x1, x2) \<Longrightarrow> x2 = (x3, x4) \<Longrightarrow> x4 = (x5, x6) \<Longrightarrow>
     X' = (x1', x2') \<Longrightarrow> x2' = (x3', x4') \<Longrightarrow> x4' = (x5', x6') \<Longrightarrow>
     ((x3, (fst x5, (snd x5)), x6), (x3', x5', x6')) \<in> isasat_GC_refl \<A> vdom0 arena\<^sub>o\<close>
    for X X' A B x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x0 x0' x x'
     supply [[show_types]]
    by auto
  have isasat_GC_clauses_prog_wl_alt_def:
    \<open>isasat_GC_clauses_prog_wl2 n x0 = iterate_over_VMTF f (\<lambda>x. length (fst x) = length (fst x0)) (fst (bump_get_heuristics n), Some (bumped_vmtf_array_fst n)) x0\<close>
    (is \<open>?A = ?B\<close>)
    for n x0
  proof -
    have [refine0]: \<open>((Some (fst (snd (snd (bump_get_heuristics n)))), x0),
      snd (fst (bump_get_heuristics n), Some (fst ((snd (snd (bump_get_heuristics n)))))), x0) \<in> Id\<close>
      \<open>((snd (fst (bump_get_heuristics n), Some (fst ((snd (snd (bump_get_heuristics n)))))), x0),
         Some (fst (snd ((snd (bump_get_heuristics n))))), x0) \<in> Id\<close>
      \<open>a=a' \<Longrightarrow> b=b' \<Longrightarrow> c=c' \<Longrightarrow> d=d' \<Longrightarrow> isasat_GC_clauses_prog_single_wl a b c d \<le> \<Down>Id (isasat_GC_clauses_prog_single_wl a' b' c' d')\<close>
      for a' b' c' d' a b c d
      by auto
    have \<open>?A \<le> \<Down>Id ?B\<close>
      unfolding f_def isasat_GC_clauses_prog_wl2_def iterate_over_VMTF_def
        bumped_vmtf_array_fst_def access_focused_vmtf_array_def nres_monad3
        case_prod_beta
      by refine_rcg (solves \<open>(auto simp: length_bumped_vmtf_array_def)\<close>)+
    moreover have \<open>?B \<le> \<Down>Id ?A\<close>
      unfolding f_def isasat_GC_clauses_prog_wl2_def iterate_over_VMTF_def
        bumped_vmtf_array_fst_def access_focused_vmtf_array_def nres_monad3
        case_prod_beta
      by refine_vcg (solves \<open>(auto simp: length_bumped_vmtf_array_def)\<close>)+
    ultimately show ?thesis
      by auto
  qed
  have empty[simp]: \<open>aivdom_inv_dec (AIvdom ([], [], [], [])) {#}\<close>
    by (auto simp: aivdom_inv_dec_alt_def)
  have vmtf': \<open>(fst (bump_get_heuristics ns), fst (snd (bump_get_heuristics ns)),
    bumped_vmtf_array_fst  ns, fst (snd (snd (snd (bump_get_heuristics ns)))), snd (snd (snd (snd (bump_get_heuristics ns))))) \<in> vmtf \<A> M\<close>
    using vmtf unfolding bump_heur_def
    by (cases \<open>bump_get_heuristics ns\<close>) (auto simp: bump_get_heuristics_def bumped_vmtf_array_fst_def
      split: if_splits)
  show ?thesis
    unfolding isasat_GC_clauses_prog_wl_alt_def prod.case f_def[symmetric] old
    apply (rule order_trans[OF iterate_over_VMTF_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l[OF vmtf' nempty bounded, 
      where I' = \<open>\<lambda>_ x. length (fst x) = length (fst (arena\<^sub>o, ([], empty_aivdom aivdom), W))\<close>]])
    subgoal by auto
    unfolding Down_id_eq iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_def cdcl_GC_clauses_prog_wl2_def f_def
    apply (refine_vcg WHILEIT_refine_with_invariant_and_break[where R = ?R]
            isasat_GC_clauses_prog_single_wl)
    subgoal by fast
    subgoal using assms by (auto simp: valid_arena_empty isasat_GC_refl_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H; assumption; fail)
    apply (rule refl)+
    subgoal by (auto simp add: cdcl_GC_clauses_prog_wl_inv_def)
    subgoal by auto
    subgoal by auto
    subgoal using le_all by (auto simp: isasat_GC_refl_def split: prod.splits)
    subgoal by (auto simp: isasat_GC_refl_def)
    subgoal by (auto simp: isasat_GC_refl_def
      dest: cdcl_GC_clauses_prog_wl_inv_cong_empty)
    done
qed


lemma cdcl_GC_clauses_prog_wl_alt_def:
  \<open>cdcl_GC_clauses_prog_wl = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS). do {
    ASSERT(cdcl_GC_clauses_pre_wl (M, N, D, NE, UE, NEk, UEk,NS, US, N0, U0, Q, WS));
    (N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_wl2 N (all_init_atms N (NE+NEk+NS+N0)) WS;
    RETURN (M, N', D, NE, UE, NEk, UEk,NS, US, N0, U0, Q, WS)
  })\<close>
proof -
   have [refine0]: \<open>(x1c, x1) \<in> Id \<Longrightarrow> RES (set_mset x1c)
       \<le> \<Down> Id  (RES (set_mset x1))\<close> for x1 x1c
     by auto
   have [refine0]: \<open>(xa, x') \<in> Id \<Longrightarrow>
       x2a = (x1b, x2b) \<Longrightarrow>
       x2 = (x1a, x2a) \<Longrightarrow>
       x' = (x1, x2) \<Longrightarrow>
       x2d = (x1e, x2e) \<Longrightarrow>
       x2c = (x1d, x2d) \<Longrightarrow>
       xa = (x1c, x2c) \<Longrightarrow>
       (A, Aa) \<in> Id \<Longrightarrow>
       cdcl_GC_clauses_prog_single_wl x1d x2e A x1e
       \<le> \<Down> Id
          (cdcl_GC_clauses_prog_single_wl x1a x2b Aa x1b)\<close>
      for \<A> x xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e A aaa Aa
      by auto
   show ?thesis
     unfolding cdcl_GC_clauses_prog_wl_def cdcl_GC_clauses_prog_wl2_def
       while.imonad3

     apply (intro ext)
     apply (clarsimp simp add: while.imonad3)
     apply (subst dual_order.eq_iff[of \<open>(_ :: _ nres)\<close>])
     apply (intro conjI)
     subgoal
       by (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
        (refine_rcg WHILEIT_refine[where R = Id], auto simp add: all_init_atms_st_def)
     subgoal
       by (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
        (refine_rcg WHILEIT_refine[where R = Id], auto simp add: all_init_atms_st_def)
     done
qed


lemma length_watched_le'':
  assumes
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur_restart\<close> and
    prop_inv: \<open>correct_watching'_nobin x1\<close>
  shows \<open>\<forall>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1). length (watched_by x1 x2) \<le> length (get_clauses_wl_heur x1a)\<close>
proof
  fix x2
  assume x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1)\<close>
  have \<open>correct_watching'_nobin x1\<close>
    using prop_inv unfolding unit_propagation_outer_loop_wl_inv_def
      unit_propagation_outer_loop_wl_inv_def
    by auto
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using x2
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms correct_watching'_nobin.simps
      simp flip: all_init_lits_def all_init_lits_alt_def)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_restart_def aivdom_inv_dec_alt_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1)\<close>
    using x2 xb_x'a unfolding all_init_atms_def all_init_lits_def
    by auto

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur_restart_def)

  have \<open>vdom_m (all_init_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_restart_def all_atms_def[symmetric] all_init_atms_st_def)
  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur_restart_def simp flip: all_init_atms_def
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a)\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show \<open>length (watched_by x1 x2) \<le> length (get_clauses_wl_heur x1a)\<close>
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

lemma length_watched_le''':
  assumes
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur_restart\<close> and
    prop_inv: \<open>no_lost_clause_in_WL x1\<close>
  shows \<open>\<forall>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1). length (watched_by x1 x2) \<le> length (get_clauses_wl_heur x1a)\<close>
proof
  fix x2
  assume x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1)\<close>
  have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using x2 prop_inv
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms no_lost_clause_in_WL_def
      simp flip: all_init_lits_def all_init_lits_alt_def)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_restart_def aivdom_inv_dec_alt_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1)\<close>
    using x2 xb_x'a unfolding all_init_atms_def all_init_lits_def
    by auto

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur_restart_def)

  have \<open>vdom_m (all_init_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_restart_def all_atms_def[symmetric] all_init_atms_st_def)
  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur_restart_def simp flip: all_init_atms_def
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a)\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show \<open>length (watched_by x1 x2) \<le> length (get_clauses_wl_heur x1a)\<close>
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

definition twl_st_heur_restart_strong_aivdom :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_restart_strong_aivdom =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S; occs = get_occs S in
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
    vm \<in> bump_heur (all_init_atms N (NE+NEk+NS+N0)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms N (NE+NEk+NS+N0)) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} lcount \<and>
    vdom_m (all_init_atms N (NE+NEk+NS+N0)) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_strong_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_init_atms N (NE+NEk+NS+N0)) \<and>
    isasat_input_nempty (all_init_atms N (NE+NEk+NS+N0)) \<and>
    old_arena = [] \<and>
      heuristic_rel (all_init_atms N (NE+NEk+NS+N0)) heur \<and>
    (occs, empty_occs_list (all_init_atms N (NE+NEk+NS+N0))) \<in> occurrence_list_ref
  }\<close>

lemma isasat_GC_clauses_prog_wl:
  \<open>(isasat_GC_clauses_prog_wl, cdcl_GC_clauses_prog_wl) \<in>
   {(S, T). (S, T) \<in> twl_st_heur_restart \<and> learned_clss_count S \<le> u} \<rightarrow>\<^sub>f
   \<langle>{(S, T). (S, T) \<in> twl_st_heur_restart_strong_aivdom \<and> arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T) \<and>
      learned_clss_count S \<le> u}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?T \<rightarrow>\<^sub>f _\<close>)
proof-
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab NS US NEk UEk stats S.
       (S,
        x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       valid_arena (get_clauses_wl_heur S) (x1a) (set (get_vdom S))\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab NS US N0 U0 NEk UEk S.
       (S,
        x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       isasat_input_bounded (all_init_atms x1a (x1c + NEk + NS + N0))\<close>
     unfolding twl_st_heur_restart_def
     by (auto simp: all_init_atms_st_def)
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab NS US N0 U0 NEk UEk S.
       (S,
        x1, x1a, x1b, x1c, x1d, NEk, UEk,NS, US, N0, U0, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       vdom_m (all_init_atms x1a (x1c+NEk+NS+N0)) x2e x1a \<subseteq> set (get_vdom S)\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab NS US N0 U0 NEk UEk S.
       (S,
        x1, x1a, x1b, x1c, x1d, NEk, UEk,NS, US, N0, U0, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       all_init_atms x1a (x1c+NEk+NS+N0) \<noteq> {#}\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>a b c x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab NS US N0 U0 NEk UEk S.
       (S, x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e) \<in> ?T \<Longrightarrow>
       get_vmtf_heur S \<in> bump_heur (all_init_atms x1a (x1c+NEk+NS+N0)) x1\<close>
       \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab NS US N0 U0 NEk UEk S.
       (S,
        x1, x1a, x1b, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e, x2e)
       \<in> ?T \<Longrightarrow> (get_watched_wl_heur S, x2e) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms x1a (x1c+NEk+NS+N0)))\<close>
    unfolding twl_st_heur_restart_def isa_vmtf_def distinct_atoms_rel_def distinct_hash_atoms_rel_def
      all_init_atms_st_def
    by (case_tac \<open>get_vmtf_heur S\<close>; auto; fail)+
  have H: \<open>vdom_m (all_init_atms x1a x1c) x2ad x1ad \<subseteq> set x2af\<close>
    if
       empty: \<open>\<forall>A\<in>#all_init_atms x1a x1c. x2ad (Pos A) = [] \<and> x2ad (Neg A) = []\<close> and
      rem: \<open>GC_remap\<^sup>*\<^sup>* (x1a, Map.empty, fmempty) (fmempty, m, x1ad)\<close> and
      \<open>dom_m x1ad = mset x2af\<close>
    for m :: \<open>nat \<Rightarrow> nat option\<close> and y :: \<open>nat literal multiset\<close> and x :: \<open>nat\<close> and
      x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
         x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab x1ac x1ad x2ad x1ae
         x1ag x2af x2ag
  proof -
    have \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms x1a x1c) \<Longrightarrow> x2ad xa = []\<close> for xa
      using empty by (cases xa) (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    then show ?thesis
      using \<open>dom_m x1ad = mset x2af\<close>
      by (auto simp: vdom_m_def)
  qed
  have H': \<open>mset x2ag \<subseteq># mset x1ah \<Longrightarrow> x \<in> set x2ag \<Longrightarrow> x \<in> set x1ah\<close> for x2ag x1ah x
    by (auto dest: mset_eq_setD)
  have [iff]: \<open> (\<exists>UEa :: 'v clauses. size UE = size UEa)\<close> for UE :: \<open>'v clauses\<close>
    by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isasat_GC_clauses_prog_wl_def cdcl_GC_clauses_prog_wl_alt_def take_0 Let_def
    apply (intro frefI nres_relI)
    apply (refine_vcg isasat_GC_clauses_prog_wl2[where \<A> = \<open>all_init_atms _ _\<close>]; remove_dummy_vars)
    subgoal
      by (clarsimp simp add: twl_st_heur_restart_def
        cdcl_GC_clauses_prog_wl_inv_def H H'
        rtranclp_GC_remap_all_init_atms
        rtranclp_GC_remap_learned_clss_l)
    subgoal
      unfolding cdcl_GC_clauses_pre_wl_def mem_Collect_eq prod.simps
        no_lost_clause_in_WL_alt_def
      apply normalize_goal+
      by (drule length_watched_le''')
        (clarsimp_all simp add: twl_st_heur_restart_def
          cdcl_GC_clauses_prog_wl_inv_def H H'
          rtranclp_GC_remap_all_init_atms all_init_atms_st_def
        rtranclp_GC_remap_learned_clss_l
        dest!: )
    subgoal
      by (clarsimp simp add: twl_st_heur_restart_def twl_st_heur_restart_strong_aivdom_def clss_size_corr_restart_def
        cdcl_GC_clauses_prog_wl_inv_def H H' clss_size_def
        rtranclp_GC_remap_all_init_atms learned_clss_count_def aivdom_inv_dec_def
        rtranclp_GC_remap_learned_clss_l)
    done
qed

definition cdcl_remap_st :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_remap_st = (\<lambda>(M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS).
  SPEC (\<lambda>(M', N', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q', WS').
         (M', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q') = (M, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N\<^sub>0, (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N'))\<close>

lemma cdcl_GC_clauses_wl_D_alt_def:
  \<open>cdcl_GC_clauses_wl = (\<lambda>S. do {
    ASSERT(cdcl_GC_clauses_pre_wl S);
    let b = True;
    if b then do {
      S \<leftarrow> cdcl_remap_st S;
      S \<leftarrow> rewatch_spec S;
      RETURN S
    }
    else remove_all_learned_subsumed_clauses_wl S})\<close>
  supply [[goals_limit=1]]
  unfolding cdcl_GC_clauses_wl_def
  by (fastforce intro!: ext simp: RES_RES_RETURN_RES2 cdcl_remap_st_def RES_RES13_RETURN_RES
      RES_RES11_RETURN_RES uncurry_def image_iff
      RES_RETURN_RES_RES2 RES_RETURN_RES RES_RES2_RETURN_RES rewatch_spec_def
      rewatch_spec_def remove_all_learned_subsumed_clauses_wl_def
      literals_are_\<L>\<^sub>i\<^sub>n'_empty blits_in_\<L>\<^sub>i\<^sub>n'_restart_wl_spec0'
      all_init_lits_alt_def[symmetric]
    intro!: bind_cong_nres intro: literals_are_\<L>\<^sub>i\<^sub>n'_empty)

lemma cdcl_GC_clauses_prog_wl2_st:
  assumes \<open>(T, S) \<in> state_wl_l None\<close>
  \<open>cdcl_GC_clauses_pre S \<and>
    no_lost_clause_in_WL T \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' T\<close> and
    \<open>get_clauses_wl T = N\<^sub>0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl T \<le>
       \<Down> {((M', N'', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q', WS'), (N, N')).
       (M', D', NE', UE', NEk', UEk', NS', US', N0', U0', Q') = (get_trail_wl T, get_conflict_wl T, get_unkept_unit_init_clss_wl T,
           get_unkept_unit_learned_clss_wl T, get_kept_unit_init_clss_wl T,
           get_kept_unit_learned_clss_wl T, get_subsumed_init_clauses_wl T, get_subsumed_learned_clauses_wl T,
           get_init_clauses0_wl T, get_learned_clauses0_wl T,
           literals_to_update_wl T) \<and> N'' = N \<and>
           (\<forall>L\<in>#all_init_lits_of_wl T. WS' L = []) \<and>
           all_init_lits_of_wl T = all_init_lits N (NE'+NEk'+NS'+N0') \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (get_clauses_wl T, Map.empty, fmempty)
               (fmempty, m, N))}
      (SPEC(\<lambda>(N'::(nat, 'a literal list \<times> bool) fmap, m).
         GC_remap\<^sup>*\<^sup>* (N\<^sub>0', (\<lambda>_. None), fmempty) (fmempty, m, N') \<and>
    0 \<notin># dom_m N'))\<close>
  using assms apply -
  apply (rule order_trans)
  apply (rule order_trans)
    prefer 2
  apply (rule cdcl_GC_clauses_prog_wl2[of \<open>get_trail_wl T\<close> \<open>get_clauses_wl T\<close> \<open>get_conflict_wl T\<close>
    \<open>get_unkept_unit_init_clss_wl T\<close> \<open>get_unkept_unit_learned_clss_wl T\<close>
    \<open>get_kept_unit_init_clss_wl T\<close> \<open>get_kept_unit_learned_clss_wl T\<close>  \<open>get_subsumed_init_clauses_wl T\<close>
    \<open>get_subsumed_learned_clauses_wl T\<close> \<open>get_init_clauses0_wl T\<close> \<open>get_learned_clauses0_wl T\<close> \<open>literals_to_update_wl T\<close>
    \<open>get_watched_wl T\<close> S N\<^sub>0'])
  apply (cases T; auto simp: all_init_atms_st_def; fail)+
  apply (auto 5 3 simp: all_init_lits_of_wl_def all_init_lits_def ac_simps
      get_unit_init_clss_wl_alt_def
    dest: rtranclp_GC_remap_init_clss_l_old_new intro!: RES_refine)
  done

abbreviation isasat_GC_clauses_rel where
  \<open>isasat_GC_clauses_rel y u \<equiv> {(S, T). (S, T) \<in> twl_st_heur_restart_strong_aivdom \<and>
           (\<forall>L\<in>#all_init_lits_of_wl y. get_watched_wl T L = [])\<and>
           get_trail_wl T = get_trail_wl y \<and>
           get_conflict_wl T = get_conflict_wl y \<and>
           get_unkept_unit_init_clss_wl T = get_unkept_unit_init_clss_wl y \<and>
           get_kept_unit_init_clss_wl T = get_kept_unit_init_clss_wl y \<and>
           get_unkept_unit_learned_clss_wl T = get_unkept_unit_learned_clss_wl y \<and>
           get_kept_unit_learned_clss_wl T = get_kept_unit_learned_clss_wl y \<and>
           get_subsumed_init_clauses_wl T = get_subsumed_init_clauses_wl y \<and>
           get_subsumed_learned_clauses_wl T = get_subsumed_learned_clauses_wl y \<and>
           get_init_clauses0_wl T = get_init_clauses0_wl y \<and>
           get_learned_clauses0_wl T = get_learned_clauses0_wl y \<and>
           learned_clss_count S \<le> u \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, (\<lambda>_. None), fmempty) (fmempty, m, get_clauses_wl T)) \<and>
           arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T)}\<close>


lemma isasat_GC_clauses_prog_wl_cdcl_remap_st:
  assumes
    \<open>(x, y) \<in> twl_st_heur_restart'''u r u\<close> and
    \<open>cdcl_GC_clauses_pre_wl y\<close>
  shows \<open>isasat_GC_clauses_prog_wl x \<le> \<Down> (isasat_GC_clauses_rel y u) (cdcl_remap_st y)\<close>
proof -
  have xy: \<open>(x, y) \<in> {(S, T). (S, T) \<in> twl_st_heur_restart \<and> learned_clss_count S \<le> u}\<close>
    using assms(1) by auto
  have H: \<open>isasat_GC_clauses_rel y u=
    {(S, T). (S, T) \<in> twl_st_heur_restart_strong_aivdom \<and> arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T) \<and> 
           learned_clss_count S \<le> u} O
    {(S, T). S = T \<and> (\<forall>L\<in>#all_init_lits_of_wl y. get_watched_wl T L = [])\<and>
           get_trail_wl T = get_trail_wl y \<and>
           get_conflict_wl T = get_conflict_wl y \<and>
           get_unkept_unit_init_clss_wl T = get_unkept_unit_init_clss_wl y \<and>
           get_kept_unit_init_clss_wl T = get_kept_unit_init_clss_wl y \<and>
           get_unkept_unit_learned_clss_wl T = get_unkept_unit_learned_clss_wl y \<and>
           get_kept_unit_learned_clss_wl T = get_kept_unit_learned_clss_wl y \<and>
           get_subsumed_init_clauses_wl T = get_subsumed_init_clauses_wl y \<and>
           get_subsumed_learned_clauses_wl T = get_subsumed_learned_clauses_wl y \<and>
           get_init_clauses0_wl T = get_init_clauses0_wl y \<and>
           get_learned_clauses0_wl T = get_learned_clauses0_wl y \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, (\<lambda>_. None), fmempty) (fmempty, m, get_clauses_wl T))}\<close>
    by blast
  show ?thesis
    using assms apply -
    apply (rule order_trans[OF isasat_GC_clauses_prog_wl[THEN fref_to_Down]])
    subgoal by fast
    apply (rule xy)
    unfolding conc_fun_chain[symmetric] H
    apply (rule ref_two_step')
    unfolding cdcl_GC_clauses_pre_wl_def
    apply normalize_goal+
    apply (rule order_trans[OF cdcl_GC_clauses_prog_wl2_st])
    apply assumption
    subgoal for xa
      using assms(2) by (simp add: correct_watching'_nobin_clauses_pointed_to
        cdcl_GC_clauses_pre_wl_def)
    apply (rule refl)
    subgoal by (auto simp: cdcl_remap_st_def conc_fun_RES split: prod.splits)
    done
qed

inductive_cases GC_remapE: \<open>GC_remap (a, aa, b) (ab, ac, ba)\<close>
lemma rtranclp_GC_remap_ran_m_remap:
  \<open>GC_remap\<^sup>*\<^sup>* (old, m, new) (old', m', new')  \<Longrightarrow> C \<in># dom_m old \<Longrightarrow> C \<notin># dom_m old' \<Longrightarrow>
         m' C \<noteq> None \<and>
         fmlookup new' (the (m' C)) = fmlookup old C\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for a aa b ab ac ba
    apply (cases \<open>C \<notin># dom_m a\<close>)
    apply (auto dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite_map
       GC_remap_ran_m_no_rewrite)
    apply (metis GC_remap_ran_m_no_rewrite_fmap GC_remap_ran_m_no_rewrite_map in_dom_m_lookup_iff option.sel)
    using GC_remap_ran_m_remap rtranclp_GC_remap_ran_m_no_rewrite by fastforce
  done

lemma GC_remap_ran_m_exists_earlier:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> C \<in># dom_m new' \<Longrightarrow> C \<notin># dom_m new \<Longrightarrow>
         \<exists>D. m' D = Some C \<and> D \<in># dom_m old \<and>
         fmlookup new' C = fmlookup old D\<close>
  by (induction rule: GC_remap.induct[split_format(complete)]) auto


lemma rtranclp_GC_remap_ran_m_exists_earlier:
  \<open>GC_remap\<^sup>*\<^sup>* (old, m, new) (old', m', new')  \<Longrightarrow> C \<in># dom_m new' \<Longrightarrow> C \<notin># dom_m new \<Longrightarrow>
         \<exists>D. m' D = Some C \<and> D \<in># dom_m old \<and>
         fmlookup new' C = fmlookup old D\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  apply (auto dest: GC_remap_ran_m_exists_earlier)
  apply (case_tac \<open>C \<in># dom_m b\<close>)
  apply (auto elim!: GC_remapE split: if_splits)
  apply blast
  using rtranclp_GC_remap_ran_m_no_new_map rtranclp_GC_remap_ran_m_no_rewrite
  by (metis fst_conv)


lemma watchlist_put_binaries_first_one_correct_watching:
  assumes \<open>\<exists>W'. correct_watching''' \<B> (M, N, D, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W') \<and> (W,W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> \<open>L < length W\<close>
  shows \<open>watchlist_put_binaries_first_one W L \<le> \<Down>{(a,b). (a,b)\<in>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> length a = length W \<and> (\<forall>K. mset (a ! K) = mset (W ! K))} (SPEC (\<lambda>W. correct_watching''' \<B> (M, N, D, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W)))\<close>
proof -
  obtain W' where W': \<open>correct_watching''' \<B>(M, N, D, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W') \<and> (W,W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close>
    using assms by fast
  let ?R = \<open>measure (\<lambda>(i, j, _). length (W ! L) - i)\<close>
  have R[refine]: \<open>wf ?R\<close>
    by auto
  have H: \<open>(\<forall>K. mset (Wa ! K) = mset (W ! K)) \<longleftrightarrow> (\<forall>K. mset (Wa ! K) = mset (W ! K)) \<and> (\<forall>K. set (Wa ! K) = set (W ! K)) \<and> 
   (\<forall>K. distinct_watched (Wa ! K) \<longleftrightarrow> distinct_watched (W ! K))\<close> for W Wa
   by (auto dest: mset_eq_setD simp del: distinct_mset_mset_distinct
    simp flip: distinct_mset_mset_distinct)

  show ?thesis
    using assms(2) W'
    unfolding watchlist_put_binaries_first_one_def conc_fun_SPEC apply -
    apply (refine_vcg )
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: nth_list_update)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for s a b aa ba
      apply (subst (asm) H)
      apply (rule_tac x= \<open>\<lambda>L. if L \<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A> then ba ! nat_of_lit L else W' L\<close> in exI)
      apply (auto simp: correct_watching'''.simps all_blits_are_in_problem_init.simps 
        map_fun_rel_def dest: mset_eq_setD split: if_splits)
      done
    done
qed

lemma watchlist_put_binaries_first:
  assumes \<open>correct_watching''' \<B> (M, N, D, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W')\<close>
    \<open>(W,W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close>
  shows \<open>watchlist_put_binaries_first W \<le> \<Down>(\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)) (SPEC (\<lambda>W. correct_watching''' \<B> (M, N, D, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W)))\<close>
proof -
  let ?R = \<open>measure (\<lambda>(i, _). length W - i)\<close>
  have [refine]: \<open>wf ?R\<close>
    by auto
  note [refine_vcg del] = WHILEIT_rule
  show ?thesis
    unfolding watchlist_put_binaries_first_def conc_fun_SPEC apply -
    apply (refine_vcg
          watchlist_put_binaries_first_one_correct_watching[where \<A>=\<A> and \<B>=\<B> and M=M and
          N=N and D=D and NE=NE and UE=UE and NEk=NEk and UEk=UEk and NS=NS and US=US
          and N\<^sub>0=N\<^sub>0 and U\<^sub>0=U\<^sub>0 and Q=Q, THEN order_trans]
      WHILEIT_rule_stronger_inv[where
      I' = \<open>\<lambda>(i, W). \<exists>W'. (W,W')\<in>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<and>
        correct_watching''' \<B> (M, N, D, NE, UE, NEk, UEk, NS, US, N\<^sub>0, U\<^sub>0, Q, W')\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using assms by fast
    subgoal by auto
    subgoal by fast
    subgoal by (auto simp: conc_fun_RES)
    subgoal by fast
    done
qed

lemma rewatch_heur_st_correct_watching:
  assumes
    pre: \<open>cdcl_GC_clauses_pre_wl y\<close> and
    S_T: \<open>(S, T) \<in> isasat_GC_clauses_rel y u\<close>
  shows \<open>rewatch_heur_and_reorder_st (empty_US_heur S) \<le> \<Down> (twl_st_heur_restart'''u (length (get_clauses_wl_heur S)) u)
    (rewatch_spec (T))\<close>
proof -
  obtain M N D NE UE NEk UEk NS US N0 U0 Q W where
    T: \<open>T = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
    by (cases T) auto
  let ?vdom = \<open>get_aivdom S\<close>
  let ?N' = \<open>get_clauses_wl_heur S\<close>
  let ?W' = \<open>get_watched_wl_heur S\<close>

  have
    valid: \<open>valid_arena ?N' N (set (get_vdom_aivdom ?vdom))\<close> and
    W: \<open>(?W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st T))\<close> and
    empty: \<open>\<And>L. L \<in># all_init_lits_of_wl y \<Longrightarrow> W L = []\<close> and
    NUE:\<open>get_unkept_unit_init_clss_wl y = NE \<close>
      \<open>get_unkept_unit_learned_clss_wl y = UE\<close>
      \<open>get_kept_unit_init_clss_wl y = NEk\<close>
      \<open>get_kept_unit_learned_clss_wl y = UEk\<close>
      \<open>get_trail_wl y = M\<close>
      \<open>get_subsumed_init_clauses_wl y = NS\<close>
      \<open>get_subsumed_learned_clauses_wl y = US\<close>
      \<open>get_init_clauses0_wl y = N0\<close>
      \<open>get_learned_clauses0_wl y = U0\<close> and
    avdom:  \<open>aivdom_inv_strong_dec (?vdom) (dom_m N)\<close> and
    tvdom: \<open>get_tvdom_aivdom ?vdom = get_vdom_aivdom ?vdom\<close>
    using assms by (auto simp: twl_st_heur_restart_strong_aivdom_def T all_init_atms_st_def
      aivdom_inv_strong_dec_alt_def)
  have
    dist: \<open>distinct (get_vdom_aivdom ?vdom)\<close> and
    dom_m_vdom: \<open>set_mset (dom_m N) \<subseteq> set (get_vdom_aivdom ?vdom)\<close>
    using avdom valid unfolding aivdom_inv_strong_dec_alt_def
      apply (cases ?vdom; cases \<open>IsaSAT_VDom.get_aivdom ?vdom\<close>; use avdom in auto)
      apply (cases ?vdom; cases \<open>IsaSAT_VDom.get_aivdom ?vdom\<close>; use avdom valid in \<open>auto simp: aivdom_inv_strong_dec_alt_def
        simp del: distinct_finite_set_mset_subseteq_iff\<close>)
      by (metis (no_types, opaque_lifting) UnE mset_subset_eqD set_mset_mset subsetD)

  obtain m where
    m: \<open>GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, Map.empty, fmempty)
             (fmempty, m, N)\<close>
    using assms by (auto simp: twl_st_heur_restart_def T)
  obtain x xa xb where
    y_x: \<open>(y, x) \<in> Id\<close> \<open>x = y\<close> and
    lits_y: \<open>literals_are_\<L>\<^sub>i\<^sub>n' y\<close> and
    x_xa: \<open>(x, xa) \<in> state_wl_l None\<close> and
    \<open>no_lost_clause_in_WL x\<close> and
    xa_xb: \<open>(xa, xb) \<in> twl_st_l None\<close> and
    \<open>twl_list_invs xa\<close> and
    struct_invs: \<open>twl_struct_invs xb\<close> and
    \<open>get_conflict_l xa = None\<close> and
    \<open>clauses_to_update_l xa = {#}\<close> and
    \<open>count_decided (get_trail_l xa) = 0\<close> and
    \<open>\<forall>L\<in>set (get_trail_l xa). mark_of L = 0\<close>
    using pre
    unfolding cdcl_GC_clauses_pre_wl_def
      cdcl_GC_clauses_pre_def
    by blast
  have [iff]:
    \<open>distinct_mset (mset (watched_l C) + mset (unwatched_l C)) \<longleftrightarrow> distinct C\<close> for C
    unfolding mset_append[symmetric]
    by auto

  have \<open>twl_st_inv xb\<close>
    using xa_xb struct_invs
    by (auto simp: twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
  then have A:
    \<open>\<And>C. C \<in># dom_m (get_clauses_wl x) \<Longrightarrow> distinct (get_clauses_wl x \<propto> C) \<and> 2 \<le> length (get_clauses_wl x \<propto> C)\<close>
    using xa_xb x_xa
    by (cases x; cases \<open>irred (get_clauses_wl x) C\<close>)
      (auto simp: twl_struct_invs_def twl_st_inv.simps
        twl_st_l_def state_wl_l_def ran_m_def conj_disj_distribR
        Collect_disj_eq Collect_conv_if
      dest!: multi_member_split
      split: if_splits)
  have struct_wf:
    \<open>C \<in># dom_m N \<Longrightarrow> distinct (N \<propto> C) \<and> 2 \<le> length (N \<propto> C)\<close> for C
    using rtranclp_GC_remap_ran_m_exists_earlier[OF m, of \<open>C\<close>] A y_x
    by (auto simp: T dest: )

  have eq_UnD: \<open>A = A' \<union> A'' \<Longrightarrow> A' \<subseteq> A\<close> for A A' A''
      by blast

  have eq3: \<open>all_init_lits_of_wl y = all_init_lits N (NE+NEk+NS+N0)\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m] NUE
    by (auto simp: all_init_lits_def all_init_lits_of_wl_def ac_simps
      get_unit_init_clss_wl_alt_def)
  moreover have \<open>all_lits_st y = all_lits_st T\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m] rtranclp_GC_remap_learned_clss_l_old_new[OF m]
      NUE
      apply (cases y)
    apply (auto simp: all_init_lits_def T NUE all_lits_def all_lits_st_def)
    by (metis all_clss_l_ran_m all_lits_def)
  moreover have \<open>set_mset (all_init_lits_of_wl y) = set_mset (all_lits_st T)\<close>
    by (smt \<open>\<And>thesis. (\<And>x xa xb. \<lbrakk>(y, x) \<in> Id; x = y; literals_are_\<L>\<^sub>i\<^sub>n' y; (x, xa) \<in> state_wl_l None; no_lost_clause_in_WL x; (xa, xb) \<in> twl_st_l None; twl_list_invs xa; twl_struct_invs xb; get_conflict_l xa = None; clauses_to_update_l xa = {#}; count_decided (get_trail_l xa) = 0; \<forall>L\<in>set (get_trail_l xa). mark_of L = 0\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> calculation(2) literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4))
  ultimately have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))
    (mset `# ran_mf N)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[OF x_xa xa_xb struct_invs] lits_y
      rtranclp_GC_remap_init_clss_l_old_new[OF m]
      rtranclp_GC_remap_learned_clss_l_old_new[OF m]
    unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_init_lits_alt_def[symmetric] \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits
     all_init_atms_st_def
    by (auto simp: T all_lits_st_def all_lits_def all_lits_of_mm_union)

  have eq: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N (NE+NEk+NS+N0))) = set_mset (all_init_lits_of_wl y)\<close>
    unfolding eq3 \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits ..
  then have vd: \<open>vdom_m (all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)) W N \<subseteq> set_mset (dom_m N)\<close>
    using empty dom_m_vdom
    by (auto simp: vdom_m_def all_init_atms_st_def)
  have \<open>{#i \<in># clause_to_update L (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}).
         i \<in># dom_m N#} =
       {#i \<in># clause_to_update L (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, {#}).
         True#}\<close> for L
       by (rule filter_mset_cong2)  (auto simp: clause_to_update_def)
  then have corr2: \<open>correct_watching'''
        ({#mset (fst x). x \<in># init_clss_l (get_clauses_wl y)#} + NE+NEk + NS+N0)
        (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W'a) \<Longrightarrow>
       correct_watching' (M, N, get_conflict_wl y, NE, UE,NEk, UEk, NS, US, N0, U0, Q, W'a)\<close> for W'a
     using rtranclp_GC_remap_init_clss_l_old_new[OF m]
     by (auto simp: correct_watching'''.simps correct_watching'.simps all_init_lits_of_wl_def
       ac_simps)
  have eq2: \<open>all_init_lits (get_clauses_wl y) (NE+NEk+NS+N0) = all_init_lits N (NE+NEk+NS+N0)\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m]
    by (auto simp: T all_init_lits_def NUE
      \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits)
  have \<open>i \<in># dom_m N \<Longrightarrow> set (N \<propto> i) \<subseteq> set_mset (all_init_lits N (NE+NEk+NS+N0))\<close> for i
    using lits by (auto dest!: multi_member_split split_list
      simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def ran_m_def all_init_atms_st_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits)
  then have blit2: \<open>correct_watching'''
        ({#mset x. x \<in># init_clss_lf (get_clauses_wl y)#} + NE + NEk + NS + N0)
        (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W'a) \<Longrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n' (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W'a)\<close> for W'a
      using rtranclp_GC_remap_init_clss_l_old_new[OF m]
      unfolding  correct_watching'''.simps  blits_in_\<L>\<^sub>i\<^sub>n'_def eq2
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits all_init_lits_alt_def[symmetric] all_init_lits_of_wl_def
      by (fastforce simp add: all_init_lits_def blits_in_\<L>\<^sub>i\<^sub>n'_def ac_simps
        get_unit_init_clss_wl_alt_def NUE dest!: multi_member_split)
  have \<open>correct_watching'''
        ({#mset x. x \<in># init_clss_lf (get_clauses_wl y)#} + (NE+NEk + NS+N0))
        (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W'a) \<Longrightarrow>
        vdom_m (all_init_atms N (NE+NEk+NS+N0)) W'a N \<subseteq> set_mset (dom_m N)\<close> for W'a
      using rtranclp_GC_remap_init_clss_l_old_new[OF m]
      unfolding  correct_watching'''.simps  blits_in_\<L>\<^sub>i\<^sub>n'_def eq2
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits all_init_lits_alt_def[symmetric]
      by (auto simp add: all_init_lits_def blits_in_\<L>\<^sub>i\<^sub>n'_def vdom_m_def NUE all_init_atms_def
          \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm
        simp flip: all_lits_st_alt_def
        dest!: multi_member_split)
    then have st:
      \<open>(x, W'a) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))) \<Longrightarrow>
     correct_watching'''
         ({#mset x. x \<in># init_clss_lf (get_clauses_wl y)#} +  (NE + (NEk + (NS + N0))))
        (M, N, get_conflict_wl y, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W'a) \<Longrightarrow>
      (set_watched_wl_heur x 
       (set_learned_count_wl_heur (clss_size_resetUS0 (get_learned_count S)) S),
        M, N, get_conflict_wl y, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W'a)
       \<in> twl_st_heur_restart\<close> for W'a m x
      using S_T dom_m_vdom
      by (auto simp: T twl_st_heur_restart_def all_init_atms_st_def y_x NUE ac_simps
        twl_st_heur_restart_strong_aivdom_def aivdom_inv_strong_dec_def2)
  have Su: \<open>learned_clss_count S \<le> u\<close>
    using S_T by auto
  have truc: \<open>xa \<in># all_learned_lits_of_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W'a) \<Longrightarrow>
       xa \<in># all_init_lits_of_wl (M, N, D, NE, {#}, NEk, UEk, NS, {#}, N0, {#}, Q, W'a)\<close> for W'a M D xa
    using lits_y eq3 rtranclp_GC_remap_learned_clss_l[OF m]
    unfolding literals_are_\<L>\<^sub>i\<^sub>n'_def all_init_lits_def NUE all_learned_lits_of_wl_def
      all_learned_lits_of_wl_def all_init_lits_of_wl_def
      all_lits_of_mm_union all_init_lits_def  \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits
    by (auto simp: ac_simps all_lits_of_mm_union get_unit_init_clss_wl_alt_def
      NUE get_unit_learned_clss_wl_alt_def)

  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding rewatch_heur_st_def T empty_US_heur_def rewatch_heur_and_reorder_st_def rewatch_heur_and_reorder_def
      Let_def prod.case tvdom isasat_state_simp nres_monad3
    apply clarify
    apply (rule ASSERT_leI)
    subgoal by (auto dest!: valid_arena_vdom_subset simp: twl_st_heur_restart_strong_aivdom_def aivdom_inv_strong_dec_alt_def)
    apply (rule bind_refine_res)
    prefer 2
    apply (rule order.trans)
    apply (rule rewatch_heur_rewatch[OF valid _ dist dom_m_vdom W[unfolded T, simplified] lits])
    apply (solves simp)
    apply (rule vd)
    apply (rule order_trans[OF ref_two_step'])
    apply (rule rewatch_correctness[where M=M and N=N and NE=NE and UE=UE and C=D and Q=Q and
        NS=NS and US=US and N\<^sub>0=N0 and U\<^sub>0=U0 and UEk=UEk and NEk=NEk and W=W])
    apply (rule empty[unfolded all_init_lits_of_wl_def]; assumption)
    apply (rule struct_wf; assumption)
    subgoal using lits eq2 by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_init_atms_def all_init_lits_def
      \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_init_atms_st_def ac_simps get_unit_init_clss_wl_alt_def
       simp del: all_init_atms_def[symmetric])
    apply (subst conc_fun_RES)
    apply (rule order.refl)
    subgoal for m x
      apply clarify
      subgoal for W'
      apply (rule bind_refine_res)
        prefer 2
      apply (rule order.trans)
      apply (rule watchlist_put_binaries_first[where M=M and N=N and NE=NE and UE=UE and Q=Q and
        NS=NS and US=US and N\<^sub>0=N0 and U\<^sub>0=U0 and UEk=UEk and NEk=NEk and D=D and W= \<open>x\<close> and W'=W'
        and \<B> = \<open>(mset `# get_init_clss_wl y + get_unit_init_clss_wl y +
        get_subsumed_init_clauses_wl y +
        get_init_clauses0_wl y)\<close>])
      apply auto[2]
      apply (subst conc_fun_RES)
      apply (rule order.refl)
      apply clarify
      using Su
      apply (auto simp: rewatch_spec_def RETURN_RES_refine_iff NUE learned_clss_count_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def literals_are_\<L>\<^sub>i\<^sub>n'_def add.assoc get_unit_init_clss_wl_alt_def
        intro: corr2 blit2 st dest: truc intro!: )
      apply (rule_tac x=xa in exI)
      apply (auto simp: rewatch_spec_def RETURN_RES_refine_iff NUE learned_clss_count_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def literals_are_\<L>\<^sub>i\<^sub>n'_def add.assoc get_unit_init_clss_wl_alt_def
        intro: corr2 blit2 st dest: truc intro!: )
      done
    done
  done
qed

lemma GC_remap_dom_m_subset:
  \<open>GC_remap (old, m, new) (old', m', new') \<Longrightarrow> dom_m old' \<subseteq># dom_m old\<close>
  by (induction rule: GC_remap.induct[split_format(complete)]) (auto dest!: multi_member_split)

lemma rtranclp_GC_remap_dom_m_subset:
  \<open>rtranclp GC_remap (old, m, new) (old', m', new') \<Longrightarrow> dom_m old' \<subseteq># dom_m old\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for old1 m1 new1 old2 m2 new2
    using GC_remap_dom_m_subset[of old1 m1 new1 old2 m2 new2] by auto
  done

lemma GC_remap_mapping_unchanged:
  \<open>GC_remap (old, m, new) (old', m', new') \<Longrightarrow> C \<in> dom m \<Longrightarrow> m' C = m C\<close>
  by (induction rule: GC_remap.induct[split_format(complete)]) auto

lemma rtranclp_GC_remap_mapping_unchanged:
  \<open>GC_remap\<^sup>*\<^sup>* (old, m, new) (old', m', new') \<Longrightarrow> C \<in> dom m \<Longrightarrow> m' C = m C\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for old1 m1 new1 old2 m2 new2
    using GC_remap_mapping_unchanged[of old1 m1 new1 old2 m2 new2, of C]
    by (auto dest: GC_remap_mapping_unchanged simp: dom_def intro!: image_mset_cong2)
  done


lemma GC_remap_mapping_dom_extended:
  \<open>GC_remap (old, m, new) (old', m', new') \<Longrightarrow> dom m' = dom m \<union> set_mset (dom_m old - dom_m old')\<close>
  by (induction rule: GC_remap.induct[split_format(complete)]) (auto dest!: multi_member_split)

lemma rtranclp_GC_remap_mapping_dom_extended:
  \<open>GC_remap\<^sup>*\<^sup>* (old, m, new) (old', m', new') \<Longrightarrow> dom m' = dom m \<union> set_mset (dom_m old - dom_m old')\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for old1 m1 new1 old2 m2 new2
    using GC_remap_mapping_dom_extended[of old1 m1 new1 old2 m2 new2]
    GC_remap_dom_m_subset[of old1 m1 new1 old2 m2 new2]
    rtranclp_GC_remap_dom_m_subset[of old m new old1 m1 new1]
    by (auto dest: GC_remap_mapping_dom_extended simp: dom_def mset_subset_eq_exists_conv)
  done

lemma GC_remap_dom_m:
  \<open>GC_remap (old, m, new) (old', m', new') \<Longrightarrow> dom_m new' = dom_m new + the `# m' `# (dom_m old - dom_m old')\<close>
  by (induction rule: GC_remap.induct[split_format(complete)]) (auto dest!: multi_member_split)

lemma rtranclp_GC_remap_dom_m:
  \<open>rtranclp GC_remap (old, m, new) (old', m', new') \<Longrightarrow> dom_m new' = dom_m new + the `# m' `# (dom_m old - dom_m old')\<close>
  apply (induction rule: rtranclp_induct[of r \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  subgoal for old1 m1 new1 old2 m2 new2
    using GC_remap_dom_m[of old1 m1 new1 old2 m2 new2] GC_remap_dom_m_subset[of old1 m1 new1 old2 m2 new2]
    rtranclp_GC_remap_dom_m_subset[of old m new old1 m1 new1]
    GC_remap_mapping_unchanged[of old1 m1 new1 old2 m2 new2]
    rtranclp_GC_remap_mapping_dom_extended[of old m new old1 m1 new1]
    by (auto dest: simp: mset_subset_eq_exists_conv intro!: image_mset_cong2)
  done

lemma isasat_GC_clauses_rel_packed_le:
  assumes
    xy: \<open>(x, y) \<in> twl_st_heur_restart''' r\<close> and
    ST: \<open>(S, T) \<in> isasat_GC_clauses_rel y u\<close>
  shows \<open>length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur x)\<close> and
     \<open>\<forall>C \<in> set (get_tvdom S). C < length (get_clauses_wl_heur x)\<close>
proof -
  obtain m where
    \<open>(S, T) \<in> twl_st_heur_restart_strong_aivdom\<close> and
    \<open>\<forall>L\<in>#all_init_lits_of_wl y. get_watched_wl T L = []\<close> and
    \<open>get_trail_wl T = get_trail_wl y\<close> and
    \<open>get_conflict_wl T = get_conflict_wl y\<close> and
    \<open>get_kept_unit_init_clss_wl T = get_kept_unit_init_clss_wl y\<close> and
    \<open>get_kept_unit_learned_clss_wl T = get_kept_unit_learned_clss_wl y\<close> and
    \<open>get_unkept_unit_init_clss_wl T = get_unkept_unit_init_clss_wl y\<close> and
    \<open>get_unkept_unit_learned_clss_wl T = get_unkept_unit_learned_clss_wl y\<close> and
    remap: \<open>GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, Map.empty, fmempty)
      (fmempty, m, get_clauses_wl T)\<close> and
    packed: \<open>arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T)\<close>
     using ST by auto
  have \<open>valid_arena (get_clauses_wl_heur x) (get_clauses_wl y) (set (get_vdom x))\<close>
    using xy unfolding twl_st_heur_restart_def by (cases x; cases y) auto
  from valid_arena_ge_length_clauses[OF this]
  have \<open>(\<Sum>C\<in>#dom_m (get_clauses_wl  y). length (get_clauses_wl y \<propto> C) +
              header_size (get_clauses_wl y \<propto> C)) \<le> length (get_clauses_wl_heur x)\<close>
   (is \<open>?A \<le> _\<close>) .
  moreover have \<open>?A = (\<Sum>C\<in>#dom_m (get_clauses_wl T). length (get_clauses_wl T \<propto> C) +
              header_size (get_clauses_wl T \<propto> C))\<close>
    using rtranclp_GC_remap_ran_m_remap[OF remap]
    by (auto simp: rtranclp_GC_remap_dom_m[OF remap] intro!: sum_mset_cong)
  ultimately show le: \<open>length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur x)\<close>
    using packed unfolding arena_is_packed_def by simp

  have \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
    using ST unfolding twl_st_heur_restart_strong_aivdom_def by (cases S; cases T) auto
  moreover have \<open>set (get_tvdom S) \<subseteq> set (get_vdom S)\<close>
    using ST by (auto simp: twl_st_heur_restart_strong_aivdom_def
      aivdom_inv_strong_dec_alt_def)
  ultimately show \<open>\<forall>C \<in> set (get_tvdom S). C < length (get_clauses_wl_heur x)\<close>
    using le
    by (auto dest: valid_arena_in_vdom_le_arena)
qed

lemma isasat_GC_clauses_wl_D:
  \<open>(isasat_GC_clauses_wl_D b, cdcl_GC_clauses_wl)
    \<in> twl_st_heur_restart'''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart''''u r u\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding prod_rel_fst_snd_iff
    isasat_GC_clauses_wl_D_def cdcl_GC_clauses_wl_D_alt_def uncurry_def
  apply (refine_vcg isasat_GC_clauses_prog_wl_cdcl_remap_st[where r=r]
    rewatch_heur_st_correct_watching)
  subgoal unfolding isasat_GC_clauses_pre_wl_D_def by blast
  subgoal by fast
  apply assumption
  subgoal by (rule isasat_GC_clauses_rel_packed_le) fast+
  subgoal by (rule isasat_GC_clauses_rel_packed_le(2)) fast+
  apply assumption+
  subgoal by (auto)
  subgoal by (auto)
  done

end
