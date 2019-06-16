theory IsaSAT_Restart_Heuristics
imports Watched_Literals.WB_Sort Watched_Literals.Watched_Literals_Watch_List_Domain_Restart
  IsaSAT_Setup IsaSAT_VMTF
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
       vdom, avdom, lcount, opts, old_arena),
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
    mset avdom \<subseteq># mset vdom \<and>
    isasat_input_bounded (all_init_atms N NE) \<and>
    isasat_input_nempty (all_init_atms N NE) \<and>
    distinct vdom \<and> old_arena = []
  }\<close>

definition twl_st_heur_restart_ana :: \<open>nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_restart_ana r = {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) = r}\<close>

lemma twl_st_heur_restart_anaD: \<open>x \<in> twl_st_heur_restart_ana r \<Longrightarrow> x \<in> twl_st_heur_restart\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)

lemma twl_st_heur_restartD: \<open>x \<in> twl_st_heur_restart \<Longrightarrow> x \<in> twl_st_heur_restart_ana (length (get_clauses_wl_heur (fst x)))\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)

definition clause_score_ordering where
  \<open>clause_score_ordering = (\<lambda>(lbd, act) (lbd', act'). lbd < lbd' \<or> (lbd = lbd' \<and> act \<le> act'))\<close>

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


lemma get_fast_ema_heur_alt_def:
   \<open>RETURN o get_fast_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, lcount). RETURN fema)\<close>
  by auto


fun (in -) get_conflict_count_since_last_restart_heur :: \<open>twl_st_wl_heur \<Rightarrow> uint64\<close> where
  \<open>get_conflict_count_since_last_restart_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, _, (ccount, _), _)
      = ccount\<close>

lemma (in -) get_counflict_count_heur_alt_def:
   \<open>RETURN o get_conflict_count_since_last_restart_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN ccount)\<close>
  by auto

lemma get_learned_count_alt_def:
   \<open>RETURN o get_learned_count = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). RETURN lcount)\<close>
  by auto

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

definition incr_lrestart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_lrestart stats,
       fast_ema, slow_ema,
       restart_info_restart_done res_info,
       vdom, avdom, lcount)
  })\<close>

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

definition five_uint64 :: \<open>uint64\<close> where
  \<open>five_uint64 = 5\<close>


definition upper_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>upper_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    lcount < 3000 + 1000 * nat_of_uint64 restarts)\<close>

definition (in -) lower_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>lower_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
        (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts, old).
     (\<not>opts_reduce opts \<or> (opts_restart opts \<and> (lcount < 2000 + 1000 * nat_of_uint64 restarts))))\<close>

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

definition valid_sort_clause_score_pre_at where
  \<open>valid_sort_clause_score_pre_at arena C \<longleftrightarrow>
    (\<exists>i vdom. C = vdom ! i \<and> arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)))
          \<and> i < length vdom)\<close>

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
    ASSERT(length avdom \<le> length arena);
    avdom \<leftarrow> quicksort_clauses_by_score arena avdom;
    RETURN (M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount)
    })\<close>

lemma sort_clauses_by_score_reorder:
  \<open>quicksort_clauses_by_score arena vdom \<le> SPEC(\<lambda>vdom'. mset vdom = mset vdom')\<close>
  unfolding quicksort_clauses_by_score_def
  by (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down, THEN order_trans])
    (auto simp add: reorder_list_def clause_score_ordering_def
     intro!: full_quicksort_correct[THEN order_trans])

lemma valid_arena_vdom_subset:
  assumes \<open>valid_arena arena N (set vdom)\<close> and \<open>distinct vdom\<close>
  shows \<open>length vdom \<le> length arena\<close>
proof -
  have \<open>set vdom \<subseteq> {0 ..< length arena}\<close>
    using assms by (auto simp: valid_arena_def)
  from card_mono[OF _ this] show ?thesis using assms by (auto simp: distinct_card)
qed

lemma sort_vdom_heur_reorder_vdom_wl:
  \<open>(sort_vdom_heur, reorder_vdom_wl) \<in> twl_st_heur_restart_ana r \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart_ana r\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (fastforce simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def
        intro!: exI[of _ \<open>get_clauses_wl y\<close>])
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest!: valid_arena_vdom_subset size_mset_mono)
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest: mset_eq_setD)
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

definition partition_main_clause where
  \<open>partition_main_clause arena = partition_main clause_score_ordering (clause_score_extract arena)\<close>

definition partition_clause where
  \<open>partition_clause arena = partition_between_ref clause_score_ordering  (clause_score_extract arena)\<close>

lemma valid_sort_clause_score_pre_swap:
  \<open>valid_sort_clause_score_pre a b \<Longrightarrow> x < length b \<Longrightarrow>
       ba < length b \<Longrightarrow> valid_sort_clause_score_pre a (swap b x ba)\<close>
  by (auto simp: valid_sort_clause_score_pre_def)

definition div2 where [simp]: \<open>div2 n = n div 2\<close>

definition safe_minus where \<open>safe_minus a b = (if b \<ge> a then 0 else a - b)\<close>

definition opts_restart_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_restart_st = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts, _). (opts_restart opts))\<close>

definition opts_reduction_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_reduction_st = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts, _). (opts_reduce opts))\<close>

definition max_restart_decision_lvl :: nat where
  \<open>max_restart_decision_lvl = 300\<close>

definition max_restart_decision_lvl_code :: uint32 where
  \<open>max_restart_decision_lvl_code = 300\<close>

definition restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n = do {
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let sema = ema_get_value (get_slow_ema_heur S);
    let limit = (11 * sema) >> 4;
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


fun (in -) get_reductions_count :: \<open>twl_st_wl_heur \<Rightarrow> uint64\<close> where
  \<open>get_reductions_count (_, _, _, _, _, _, _,_,_,_,_,
       (_, _, _, lres, _, _), _)
      = lres\<close>

lemma (in -) get_reduction_count_alt_def:
   \<open>RETURN o get_reductions_count = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       (_, _, _, lres, _, _), fema, sema, _, lcount). RETURN lres)\<close>
  by auto


definition GC_EVERY :: uint64 where
  \<open>GC_EVERY = 15\<close> \<comment>\<open>hard-coded limit\<close>

definition GC_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>GC_required_heur S n = do {
    let lres = get_reductions_count S;
    RETURN (lres AND GC_EVERY = GC_EVERY)} \<^cancel>\<open>Temporary measure\<close>
  \<close>

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
       vdom, avdom, lcount, opts, old_arena).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts, old_arena))\<close>

lemma get_vdom_mark_garbage[simp]:
  \<open>get_vdom (mark_garbage_heur C i S) = get_vdom S\<close>
  \<open>get_avdom (mark_garbage_heur C i S) = delete_index_and_swap (get_avdom S) i\<close>
  by (cases S; auto simp: mark_garbage_heur_def; fail)+


lemma mark_garbage_heur_wl:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>\<not> irred (get_clauses_wl T) C\<close> and \<open>i < length (get_avdom S)\<close>
  shows \<open>(mark_garbage_heur C i S, mark_garbage_wl C T) \<in> twl_st_heur_restart\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def)
  apply (auto simp: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If
     simp: all_init_atms_def all_init_lits_def mset_butlast_remove1_mset
     simp del: all_init_atms_def[symmetric]
     intro: valid_arena_extra_information_mark_to_delete'
      dest!: in_set_butlastD in_vdom_m_fmdropD
      elim!: in_set_upd_cases)
  done

lemma mark_garbage_heur_wl_ana:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>\<not> irred (get_clauses_wl T) C\<close> and \<open>i < length (get_avdom S)\<close>
  shows \<open>(mark_garbage_heur C i S, mark_garbage_wl C T) \<in> twl_st_heur_restart_ana r\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_ana_def mark_garbage_heur_def mark_garbage_wl_def)
  apply (auto simp: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If init_clss_l_fmdrop_irrelev
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
  using assms by (fastforce simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest!: set_mset_mono)

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
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> i < length (get_avdom S) \<Longrightarrow>
    (delete_index_vdom_heur i S, T) \<in> twl_st_heur_restart\<close>
  by (auto simp: twl_st_heur_restart_def delete_index_vdom_heur_def
    dest: in_set_delete_index_and_swapD)


lemma delete_index_vdom_heur_twl_st_heur_restart_ana:
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> i < length (get_avdom S) \<Longrightarrow>
    (delete_index_vdom_heur i S, T) \<in> twl_st_heur_restart_ana r\<close>
  by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def delete_index_vdom_heur_def
    dest: in_set_delete_index_and_swapD)

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
  assumes \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close>
  shows \<open>mark_clauses_as_unused_wl_D_heur i S \<le> \<Down> (twl_st_heur_restart_ana r) (SPEC ( (=) T))\<close>
proof -
  have 1: \<open> \<Down> (twl_st_heur_restart_ana r) (SPEC ( (=) T)) = do {
      (i, T) \<leftarrow> SPEC (\<lambda>(i::nat, T'). (T', T) \<in> twl_st_heur_restart_ana r);
      RETURN T
    }\<close>
    by (auto simp: RES_RETURN_RES2 uncurry_def conc_fun_RES)
  show ?thesis
    unfolding mark_clauses_as_unused_wl_D_heur_def 1
    apply (rule Refine_Basic.bind_mono)
    subgoal
      apply (refine_vcg
         WHILET_rule[where R = \<open>measure (\<lambda>(i, T). length (get_avdom T) - i)\<close> and
	   I = \<open>\<lambda>(_, S). (S, T) \<in> twl_st_heur_restart_ana r\<close>])
      subgoal by auto
      subgoal using assms by auto
      subgoal by auto
      subgoal unfolding access_vdom_at_pre_def by auto
      subgoal for st a S'
        unfolding clause_not_marked_to_delete_heur_pre_def
	  arena_is_valid_clause_vdom_def
        by (fastforce simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def dest!: set_mset_mono
          intro!: exI[of _ \<open>get_clauses_wl T\<close>]  exI[of _ \<open>set (get_vdom S')\<close>])
      subgoal
        by (auto intro: delete_index_vdom_heur_twl_st_heur_restart_ana)
      subgoal by auto
      subgoal
        unfolding arena_is_valid_clause_idx_def
	  arena_is_valid_clause_vdom_def arena_act_pre_def
       by (fastforce simp: twl_st_heur_restart_def twl_st_heur_restart
            dest!: twl_st_heur_restart_anaD)
      subgoal by (auto intro!: mark_unused_st_heur_ana simp: twl_st_heur_restart
        dest: twl_st_heur_restart_anaD)
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
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C) \<and> get_learned_count T \<ge> 1);
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
     twl_st_heur_restart_ana r \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart_ana r\<rangle>nres_rel\<close>
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
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C) \<and> get_learned_count T \<ge> 1);
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
      \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y
  proof -
    show ?thesis by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed
  have init_rel[refine0]: \<open>(x, y) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
       (l, la) \<in> nat_rel \<Longrightarrow>
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> get_avdom S = get_avdom x}\<close>
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
    \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart_ana r \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
    \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    xa_x': \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close> and
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
      using L that by (auto simp: twl_st_heur_restart st arena_lifting dest: \<L>\<^sub>a\<^sub>l\<^sub>l_init_all twl_st_heur_restart_anaD)

    show ?thesis
      apply (rule order.trans)
      apply (rule get_the_propagation_reason_pol[THEN fref_to_Down_curry,
        of \<open>all_init_atms_st x1a\<close> \<open>get_trail_wl x1a\<close>
	  \<open>arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0)\<close>])
      subgoal
        using xa_x' L by (auto simp add: twl_st_heur_restart_def st)
      subgoal
        using xa_x' by (auto simp add: twl_st_heur_restart_ana_def twl_st_heur_restart_def st)
      using that unfolding get_the_propagation_reason_def apply -
      by (auto simp: twl_st_heur_restart lits_of_def get_the_propagation_reason_def
          conc_fun_RES
        dest!: twl_st_heur_restart_anaD dest: twl_st_heur_restart_same_annotD imageI[of _ _ lit_of])
  qed
  have \<open>((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom, lcount),
           S')
          \<in> twl_st_heur_restart \<longleftrightarrow>
    ((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom', lcount),
           S')
          \<in> twl_st_heur_restart\<close>
    if \<open>mset avdom = mset avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema
      ccount vdom lcount S' avdom' avdom
    using that unfolding twl_st_heur_restart_def
    by auto
  then have mark_to_delete_clauses_wl_D_heur_pre_vdom':
    \<open>mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, vdom, avdom, lcount) \<longleftrightarrow>
      mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
        fast_ema, slow_ema, ccount, vdom, avdom', lcount)\<close>
    if \<open>mset avdom = mset avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount vdom lcount
    using that
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def
    by metis
  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart_ana r \<and> V = T \<and>
         (mark_to_delete_clauses_wl_D_pre T \<longrightarrow> mark_to_delete_clauses_wl_D_pre V) \<and>
         (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U)}
         (reorder_vdom_wl T)\<close>
    if \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> for S T
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply (refine_rcg ASSERT_leI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (fastforce simp: valid_sort_clause_score_pre_def twl_st_heur_restart_ana_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>])
    subgoal
     by (auto simp: twl_st_heur_restart_ana_def valid_arena_vdom_subset twl_st_heur_restart_def
        dest!: size_mset_mono valid_arena_vdom_subset)
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
         intro: mark_to_delete_clauses_wl_D_heur_pre_vdom'[THEN iffD1]
         dest: mset_eq_setD)
    done
  have already_deleted:
    \<open>((x1b, delete_index_vdom_heur x1b x2b), x1, x1a,
       delete_index_and_swap x2a x1)
      \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart_ana r \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
      \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv Sa xs x'\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      le: \<open>x1b < length (get_avdom x2b)\<close> and
      \<open>access_vdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
      \<open>\<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
      \<open>x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa
  proof -
    show ?thesis
      using xx le unfolding st
      by (auto simp: twl_st_heur_restart_ana_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If
          intro: valid_arena_extra_information_mark_to_delete'
          dest!: in_set_butlastD in_vdom_m_fmdropD
          elim!: in_set_upd_cases)
  qed
  have get_learned_count_ge: \<open>1 \<le> get_learned_count x2b\<close>
    if
      xy: \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
      \<open>(xa, x')
       \<in> nat_rel \<times>\<^sub>f
         {(Sa, T, xs).
          (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv Sa xs x'\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      dom: \<open>\<not> x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close> and
      \<open>can_del
       \<in> {b. b \<longrightarrow>
             Propagated (get_clauses_wl x1a \<propto> (x2a ! x1) ! 0) (x2a ! x1)
             \<notin> set (get_trail_wl x1a) \<and>
             \<not> irred (get_clauses_wl x1a) (x2a ! x1) \<and>
             length (get_clauses_wl x1a \<propto> (x2a ! x1)) \<noteq> 2}\<close> and
      \<open>can_del\<close> for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b D can_del
  proof -
    have \<open>\<not>irred (get_clauses_wl x1a) (x2a ! x1)\<close> and \<open>(x2b, x1a) \<in> twl_st_heur_restart_ana r\<close>
      using that by (auto simp: )
    then show ?thesis
     using dom by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def ran_m_def
       dest!: multi_member_split)
  qed
  have init:
    \<open>(u, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S} \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
    mark_to_delete_clauses_wl_D_inv Sa xs (la, Sa, xs) \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
       {(Sa, (T, xs)). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close>
       for x y S Sa xs l la u
    by auto
  have [refine0]: \<open>mark_clauses_as_unused_wl_D_heur i T
    \<le> SPEC
       (\<lambda>x. incr_restart_stat x \<le> SPEC (\<lambda>c. (c, S) \<in> twl_st_heur_restart_ana r))\<close>
    if \<open>(T, S) \<in> twl_st_heur_restart_ana r\<close> for S T i
    by (rule order_trans, rule mark_clauses_as_unused_wl_D_heur[OF that, of i])
      (auto simp: conc_fun_RES incr_restart_stat_def
        twl_st_heur_restart_ana_def twl_st_heur_restart_def)
  show ?thesis
    supply sort_vdom_heur_def[simp] twl_st_heur_restart_anaD[dest]
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
        (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
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
    subgoal for x y S Sa uu_ xs l la xa x' x1 x2 x1a x2a x1b x2b D can_del
        by (rule get_learned_count_ge)
    subgoal
      by (auto intro!: mark_garbage_heur_wl_ana)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def arena_act_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_unused_st_heur_ana)
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
  apply (rule twl_st_heur_restartD)
  subgoal
    by (subst mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur[symmetric])
  subgoal
    by (subst mark_to_delete_clauses_wl_post_twl_st_heur, assumption, rule twl_st_heur_restart_anaD)
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
       \<in> twl_st_heur_restart_ana r\<close>
  shows
    \<open>(((x1b, x1c, x1d, x1e[atm_of x2 := 0], x2d), x2n),
        (ys @ Propagated x2 0 # zs, x2n'))
       \<in> twl_st_heur_restart_ana r\<close>
proof -
  let ?S = \<open>(ys @ Propagated x2 C # zs, x2n')\<close>
  let ?\<A> = \<open>all_init_atms_st ?S\<close>
  have pol: \<open>((x1b, x1c, x1d, x1e, x2d), ys @ Propagated x2 C # zs)
         \<in> trail_pol (all_init_atms_st ?S)\<close>
    using assms(3) unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_def
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
    using assms(3) unfolding twl_st_heur_restart_ana_def
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
       Id \<times>\<^sub>f Id\<times>\<^sub>f twl_st_heur_restart_ana r \<rightarrow> \<langle>twl_st_heur_restart_ana r\<rangle>nres_rel\<close>
  unfolding isasat_replace_annot_in_trail_def replace_annot_l_def
    uncurry_def
  apply (intro frefI nres_relI)
  apply refine_rcg
  subgoal
    using in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
    by (auto simp: trail_pol_alt_def ann_lits_split_reasons_def
      twl_st_heur_restart_def twl_st_heur_restart_ana_def)
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

definition mark_garbage_heur2 :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mark_garbage_heur2 C = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts). do{
    let st = arena_status N' C = IRRED;
    ASSERT(\<not>st \<longrightarrow> lcount \<ge> 1);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, if st then lcount else lcount - 1, opts) })\<close>

definition remove_one_annot_true_clause_one_imp_wl_D_heur
  :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> twl_st_wl_heur) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl_D_heur = (\<lambda>i S. do {
      (L, C) \<leftarrow> do {
        L \<leftarrow> isa_trail_nth (get_trail_wl_heur S) i;
	C \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur S) L;
	RETURN (L, C)};
      ASSERT(C \<noteq> None \<and> i + 1 \<le> uint32_max);
      if the C = 0 then RETURN (i+1, S)
      else do {
        ASSERT(C \<noteq> None);
        S \<leftarrow> isasat_replace_annot_in_trail L (the C) S;
	ASSERT(mark_garbage_pre (get_clauses_wl_heur S, the C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) (the C));
        S \<leftarrow> mark_garbage_heur2 (the C) S;
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
    ASSERT((isa_length_trail_pre o get_trail_wl_heur) S);
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
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> isa_length_trail (get_trail_wl_heur S) = length (get_trail_wl T)\<close>
  unfolding isa_length_trail_def twl_st_heur_restart_ana_def twl_st_heur_restart_def trail_pol_def
  by (cases S) (auto dest: ann_lits_split_reasons_map_lit_of)

lemma twl_st_heur_restart_count_decided_st_alt_def:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> count_decided_st_heur S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_restart_ana_def trail_pol_def twl_st_heur_restart_def
  by (cases S) (auto simp: count_decided_st_heur_def)

lemma twl_st_heur_restart_trailD:
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
    (get_trail_wl_heur S, get_trail_wl T)
    \<in> trail_pol (all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T))\<close>
  by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)

lemma no_dup_nth_proped_dec_notin:
  \<open>no_dup M \<Longrightarrow> k < length M \<Longrightarrow> M ! k = Propagated L C \<Longrightarrow> Decided L \<notin> set M\<close>
  apply (auto dest!: split_list simp: nth_append nth_Cons defined_lit_def in_set_conv_nth
    split: if_splits nat.splits)
  by (metis no_dup_no_propa_and_dec nth_mem)

lemma remove_all_annot_true_clause_imp_wl_inv_length_cong:
  \<open>remove_all_annot_true_clause_imp_wl_inv S xs T \<Longrightarrow>
    length xs = length ys \<Longrightarrow> remove_all_annot_true_clause_imp_wl_inv S ys T\<close>
  by (auto simp: remove_all_annot_true_clause_imp_wl_inv_def
    remove_all_annot_true_clause_imp_inv_def)

lemma get_literal_and_reason:
  assumes
    \<open>((k, S), k', T) \<in> nat_rel \<times>\<^sub>f twl_st_heur_restart_ana r\<close> and
    \<open>remove_one_annot_true_clause_one_imp_wl_D_pre k' T\<close> and
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
    by (auto simp: twl_st_heur_restart_ana_def rev_trail_nth_def
      trail_pol_alt_def twl_st_heur_restart_def)
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
      using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    subgoal
      by auto
    done
qed


lemma red_in_dom_number_of_learned_ge1: \<open>C' \<in># dom_m baa \<Longrightarrow> \<not> irred baa C' \<Longrightarrow> Suc 0 \<le> size (learned_clss_l baa)\<close>
  by (auto simp: ran_m_def dest!: multi_member_split)

lemma mark_garbage_heur2_remove_and_add_cls_l:
  \<open>(S, T) \<in> twl_st_heur_restart_ana r \<Longrightarrow> (C, C') \<in> Id \<Longrightarrow>
    C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
    mark_garbage_heur2 C S
       \<le> \<Down> (twl_st_heur_restart_ana r) (remove_and_add_cls_l C' T)\<close>
  unfolding mark_garbage_heur2_def remove_and_add_cls_l_def
  apply (cases S; cases T)
  by  (auto simp: twl_st_heur_restart_def arena_lifting
      valid_arena_extra_information_mark_to_delete'
      all_init_atms_fmdrop_add_mset_unit learned_clss_l_l_fmdrop
      learned_clss_l_l_fmdrop_irrelev twl_st_heur_restart_ana_def
      size_Diff_singleton red_in_dom_number_of_learned_ge1 intro!: ASSERT_leI
    dest: in_vdom_m_fmdropD)

lemma remove_one_annot_true_clause_one_imp_wl_D_heur_remove_one_annot_true_clause_one_imp_wl_D:
  \<open>(uncurry remove_one_annot_true_clause_one_imp_wl_D_heur,
    uncurry remove_one_annot_true_clause_one_imp_wl_D) \<in>
    nat_rel \<times>\<^sub>f twl_st_heur_restart_ana r \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>f twl_st_heur_restart_ana r\<rangle>nres_rel\<close>
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    remove_one_annot_true_clause_one_imp_wl_D_def case_prod_beta uncurry_def
  apply (intro frefI nres_relI)
  subgoal for x y
  apply (refine_rcg get_literal_and_reason[where r=r]
    isasat_replace_annot_in_trail_replace_annot_in_trail_spec
      [where r=r, THEN fref_to_Down_curry2]
    mark_garbage_heur2_remove_and_add_cls_l[where r=r])
  subgoal by auto
  subgoal unfolding remove_one_annot_true_clause_one_imp_wl_D_pre_def
    by auto
  subgoal unfolding remove_one_annot_true_clause_one_imp_wl_D_pre_def
     remove_one_annot_true_clause_one_imp_wl_pre_def
     remove_one_annot_true_clause_one_imp_pre_def
     by (cases x; cases y)
       (auto simp: uint32_max_def twl_st_heur_restart_def twl_st_heur_restart_ana_def
          state_wl_l_def trail_pol_alt_def)
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
    apply (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
    done
  subgoal for p pa S Sa
    unfolding arena_is_valid_clause_vdom_def
    apply (rule_tac x = \<open>get_clauses_wl Sa\<close> in exI)
    apply (rule_tac x = \<open>set (get_vdom S)\<close> in exI)
    apply (case_tac S, case_tac Sa)
    apply (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
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
(*TODO Move*)
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
  assumes Sy:  \<open>(S, y) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>get_conflict_wl y = None\<close>
  shows \<open>do {
      if count_decided_st_heur S > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S;
        empty_Q S
      } else RETURN S
    }
         \<le> \<Down> (twl_st_heur_restart_ana r) (cdcl_twl_local_restart_wl_spec0 y)\<close>
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
	  (empty_Q_wl T)) \<in> twl_st_heur_restart_ana r \<and>
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
	  (empty_Q_wl T)) \<in> twl_st_heur_restart_ana r \<and>
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
      by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    then obtain vm' where
      vm': \<open>(get_vmtf_heur S, vm') \<in> Id \<times>\<^sub>f distinct_atoms_rel ?\<A>\<close> and
      vm: \<open>vm' \<in> vmtf (all_init_atms_st y) (get_trail_wl y)\<close>
      unfolding isa_vmtf_def
      by force

    have find_decomp_w_ns_pre:
      \<open>find_decomp_w_ns_pre (all_init_atms_st y) ((get_trail_wl y, 0), vm')\<close>
      using that assms vm' vm unfolding find_decomp_w_ns_pre_def
      by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
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
	by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
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
        intro!: RETURN_SPEC_refine simp: twl_st_heur_restart_def out_learned_def
	    empty_Q_wl_def twl_st_heur_restart_ana_def
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
    twl_st_heur_restart_ana r \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart_ana r\<rangle>nres_rel\<close>
  unfolding remove_one_annot_true_clause_imp_wl_D_def
    remove_one_annot_true_clause_imp_wl_D_heur_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    WHILEIT_refine[where R = \<open>nat_rel \<times>\<^sub>r twl_st_heur_restart_ana r\<close>]
    remove_one_annot_true_clause_one_imp_wl_D_heur_remove_one_annot_true_clause_one_imp_wl_D[THEN
      fref_to_Down_curry])
  subgoal by (auto simp: trail_pol_alt_def isa_length_trail_pre_def
    twl_st_heur_restart_def twl_st_heur_restart_ana_def)
  subgoal by (auto simp: twl_st_heur_restart_isa_length_trail_get_trail_wl
    twl_st_heur_restart_count_decided_st_alt_def)
  subgoal for x y
    apply (rule order_trans)
    apply (rule get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail_CS[THEN fref_to_Down_curry,
        of \<open>get_trail_wl y\<close> 0 _ _ \<open>all_init_atms_st y\<close>])
    subgoal by (auto simp: get_pos_of_level_in_trail_pre_def
      twl_st_heur_restart_count_decided_st_alt_def)
    subgoal by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    subgoal
      apply (subst get_pos_of_level_in_trail_decomp_iff)
      apply (solves \<open>auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def\<close>)
      apply (auto simp: get_pos_of_level_in_trail_def
        twl_st_heur_restart_count_decided_st_alt_def)
      done
    done
    subgoal by auto
    subgoal for x y k k' T T'
      apply (subst (asm)(12) surjective_pairing)
      apply (subst (asm)(10) surjective_pairing)
      unfolding remove_one_annot_true_clause_imp_wl_D_heur_inv_def
        prod_rel_iff
      apply (subst (10) surjective_pairing, subst prod.case)
      by (fastforce intro: twl_st_heur_restart_anaD simp: twl_st_heur_restart_anaD)
    subgoal by auto
    subgoal by auto
    subgoal by auto
  done


lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl2_D:
  \<open>(mark_to_delete_clauses_wl_D_heur, mark_to_delete_clauses_wl2_D) \<in>
     twl_st_heur_restart_ana r \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart_ana r\<rangle>nres_rel\<close>
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
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C) \<and> get_learned_count T \<ge> 1);
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
      \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y
  proof -
    show ?thesis by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed
  have init_rel[refine0]: \<open>(x, y) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
       (l, la) \<in> nat_rel \<Longrightarrow>
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> get_avdom S = get_avdom x}\<close>
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
    \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart_ana r \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
    \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    xa_x': \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close> and
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
      using L that by (auto simp: twl_st_heur_restart st arena_lifting dest: \<L>\<^sub>a\<^sub>l\<^sub>l_init_all twl_st_heur_restart_anaD)

    show ?thesis
      apply (rule order.trans)
      apply (rule get_the_propagation_reason_pol[THEN fref_to_Down_curry,
        of \<open>all_init_atms_st x1a\<close> \<open>get_trail_wl x1a\<close>
	  \<open>arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0)\<close>])
      subgoal
        using xa_x' L by (auto simp add: twl_st_heur_restart_def st)
      subgoal
        using xa_x' by (auto simp add: twl_st_heur_restart_def twl_st_heur_restart_ana_def st)
      using that unfolding get_the_propagation_reason_def apply -
      by (auto simp: twl_st_heur_restart lits_of_def get_the_propagation_reason_def
          conc_fun_RES
        dest: twl_st_heur_restart_same_annotD imageI[of _ _ lit_of]
          dest!: twl_st_heur_restart_anaD)
  qed
  have \<open>((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom, lcount),
           S')
          \<in> twl_st_heur_restart \<longleftrightarrow>
    ((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom', lcount),
           S')
          \<in> twl_st_heur_restart\<close>
    if \<open>mset avdom = mset avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema
      ccount vdom lcount S' avdom' avdom
    using that unfolding twl_st_heur_restart_def twl_st_heur_restart_ana_def
    by auto
  then have mark_to_delete_clauses_wl_D_heur_pre_vdom':
    \<open>mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, vdom, avdom, lcount) \<longleftrightarrow>
      mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
        fast_ema, slow_ema, ccount, vdom, avdom', lcount)\<close>
    if \<open>mset avdom = mset avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount vdom lcount
    using that twl_st_heur_restart_anaD
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def
    by metis
  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart_ana r \<and> V = T \<and>
         (mark_to_delete_clauses_wl_D_pre T \<longrightarrow> mark_to_delete_clauses_wl_D_pre V) \<and>
         (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U)}
         (reorder_vdom_wl T)\<close>
    if \<open>(S, T) \<in> twl_st_heur_restart_ana r\<close> for S T
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply (refine_rcg ASSERT_leI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def twl_st_heur_restart_ana_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>] exI[of _ \<open>set (get_vdom S)\<close>])
    subgoal by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
       dest!: size_mset_mono valid_arena_vdom_subset)
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
         intro: mark_to_delete_clauses_wl_D_heur_pre_vdom'[THEN iffD1]
         dest: mset_eq_setD)
    done
  have already_deleted:
    \<open>((x1b, delete_index_vdom_heur x1b x2b), x1, x1a,
       delete_index_and_swap x2a x1)
      \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart_ana r \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
      \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl2_D_inv Sa xs x'\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      x1b: \<open>x1b < length (get_avdom x2b)\<close> and
      \<open>access_vdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
      \<open>\<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
      \<open>x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa
  proof -
    show ?thesis
      using xx x1b unfolding st
      by (auto simp: twl_st_heur_restart_ana_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If
          intro: valid_arena_extra_information_mark_to_delete'
          dest!: in_set_butlastD in_vdom_m_fmdropD
          elim!: in_set_upd_cases)
  qed

  have get_learned_count_ge: \<open>1 \<le> get_learned_count x2b\<close>
    if
      xy: \<open>(x, y) \<in> twl_st_heur_restart_ana r\<close> and
      \<open>(xa, x')
       \<in> nat_rel \<times>\<^sub>f
         {(Sa, T, xs).
          (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      dom: \<open>\<not> x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close> and
      \<open>can_del
       \<in> {b. b \<longrightarrow>
             Propagated (get_clauses_wl x1a \<propto> (x2a ! x1) ! 0) (x2a ! x1)
             \<notin> set (get_trail_wl x1a) \<and>
             \<not> irred (get_clauses_wl x1a) (x2a ! x1) \<and>
             length (get_clauses_wl x1a \<propto> (x2a ! x1)) \<noteq> 2}\<close> and
      \<open>can_del\<close> for x y S Sa uu xs l la xa x' x1 x2 x1a x2a x1b x2b D can_del
  proof -
    have \<open>\<not>irred (get_clauses_wl x1a) (x2a ! x1)\<close> and \<open>(x2b, x1a) \<in> twl_st_heur_restart_ana r\<close>
      using that by (auto simp: )
    then show ?thesis
     using dom by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def ran_m_def
       dest!: multi_member_split)
  qed
  have init:
    \<open>(u, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S} \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
    mark_to_delete_clauses_wl2_D_inv Sa xs (la, Sa, xs) \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
       {(Sa, (T, xs)). (Sa, T) \<in> twl_st_heur_restart_ana r \<and> xs = get_avdom Sa}\<close>
       for x y S Sa xs l la u
    by auto
  have [refine0]: \<open>mark_clauses_as_unused_wl_D_heur i T
    \<le> SPEC
       (\<lambda>x. incr_restart_stat x \<le> SPEC (\<lambda>c. (c, S) \<in> twl_st_heur_restart_ana r))\<close>
    if \<open>(T, S) \<in> twl_st_heur_restart_ana r\<close> for S T i
      by (rule order_trans, rule mark_clauses_as_unused_wl_D_heur[OF that, of i])
      (use that in \<open>auto simp: conc_fun_RES incr_restart_stat_def
        twl_st_heur_restart_ana_def twl_st_heur_restart_def\<close>)
  show ?thesis
    supply sort_vdom_heur_def[simp] twl_st_heur_restart_anaD[dest]
    unfolding mark_to_delete_clauses_wl_D_heur_alt_def mark_to_delete_clauses_wl_D_alt_def
      access_lit_in_clauses_heur_def Let_def
    apply (intro frefI nres_relI)
    apply (refine_vcg sort_vdom_heur_reorder_vdom_wl[THEN fref_to_Down])
    subgoal
      unfolding mark_to_delete_clauses_wl_D_heur_pre_def by (fast dest: twl_st_heur_restart_anaD)
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
         (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_get_avdom_nth_get_vdom twl_st_heur_restart_anaD)
    subgoal
      by (auto simp: twl_st_heur_restart dest!: twl_st_heur_restart_anaD)
    subgoal
      by (rule already_deleted)
    subgoal for x y _ _ _ _ _ xs l la xa x' x1 x2 x1a x2a
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_avdom x2a ! x1a\<close>], simp, rule exI[of _ \<open>get_clauses_wl x1\<close>])
        (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
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
    subgoal by (rule get_learned_count_ge)
    subgoal
      by (auto intro!: mark_garbage_heur_wl_ana)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def arena_act_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_unused_st_heur_ana)
    subgoal
      by (auto simp:)
    done
qed

definition iterate_over_VMTF where
  \<open>iterate_over_VMTF \<equiv> (\<lambda>f (I :: 'a \<Rightarrow> bool) (ns :: (nat, nat) vmtf_node list, n) x. do {
      (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). I x\<^esup>
        (\<lambda>(n, _). n \<noteq> None)
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

definition iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l where
  \<open>iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l = (\<lambda>f \<A>\<^sub>0 I x. do {
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset \<A>\<^sub>0 \<and> distinct_mset \<A>);
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

lemma iterate_over_VMTF_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l:
  fixes x :: 'a
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    nempty: \<open>\<A> \<noteq> {#}\<close> \<open>isasat_input_bounded \<A>\<close>
  shows \<open>iterate_over_VMTF f I (ns, Some fst_As) x \<le> \<Down> Id (iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l f \<A> I x)\<close>
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
        (\<lambda>(n, _, _). n \<noteq> None)
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
        (\<lambda>(n, _, _). n \<noteq> None)
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
  have nempty_iff: \<open>(x1 \<noteq> None) = (x1b \<noteq> {#})\<close>
  if
    \<open>(remdups_mset \<A>, \<A>') \<in> Id\<close> and
    H: \<open>(x, x') \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close> and
    \<open>case x of (n, m, xa) \<Rightarrow> I xa\<close> and
    \<open>case x' of (uu_, x) \<Rightarrow> I x\<close> and
    st[simp]:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x = (x1, x2)\<close>
      \<open>x' = (x1b, xb)\<close>
    for \<A>' x x' x1 x2 x1a x2a x1b xb
  proof
    show \<open>x1b \<noteq> {#}\<close> if \<open>x1 \<noteq> None\<close>
      using that H
      by (auto simp: is_lasts_def)
    show \<open>x1 \<noteq> None\<close> if  \<open>x1b \<noteq> {#}\<close>
      using that H
      by (auto simp: is_lasts_def)
  qed
  have IH: \<open>((get_next (ns ! the x1a), Suc x1b, xa), remove1_mset A x1, xb)
        \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close>
     if
      \<open>(remdups_mset \<A>, \<A>') \<in> Id\<close> and
      H: \<open>(x, x') \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close> and
      \<open>case x of (n, uu_, uua_) \<Rightarrow> n \<noteq> None\<close> and
      nempty: \<open>case x' of (\<B>, uu_) \<Rightarrow> \<B> \<noteq> {#}\<close> and
      \<open>case x of (n, m, xa) \<Rightarrow> I xa\<close> and
      \<open>case x' of (uu_, x) \<Rightarrow> I x\<close> and
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
  have le_uint_max: \<open>the x1a \<le> uint_max div 2\<close>
    if 
      \<open>(remdups_mset \<A>, \<A>') \<in> Id\<close> and
      \<open>(x, x') \<in> {((n, m, x), \<A>', y). is_lasts \<A>' n m \<and> x = y}\<close> and
      \<open>case x of (n, uu_, uua_) \<Rightarrow> n \<noteq> None\<close> and
      \<open>case x' of (\<B>, uu_) \<Rightarrow> \<B> \<noteq> {#}\<close> and
      \<open>case x of (n, m, xa) \<Rightarrow> I xa\<close> and
      \<open>case x' of (uu_, x) \<Rightarrow> I x\<close> and
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
      using that by (auto simp: is_lasts_def)
    then show ?thesis
      using nempty by (auto dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
  qed
  have  \<open>iterate_over_VMTF2 f I (ns, Some fst_As) x \<le> \<Down> Id (iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l f \<A> I x)\<close>
    unfolding iterate_over_VMTF2_def iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_def prod.case
    apply (refine_vcg WHILEIT_refine[where R = \<open>{((n :: nat option, m::nat, x::'a), (\<A>' :: nat multiset, y)).
        is_lasts \<A>' n m \<and> x = y}\<close>])
    subgoal by simp
    subgoal by simp
    subgoal
      using card_\<A> fst_As nempty nempty' hd_conv_nth[OF nempty'] hd_zs_le unfolding zs_def[symmetric]
        is_lasts_def
      by (simp_all add:  eq_commute[of \<open>remdups_mset _\<close>])
    subgoal by auto
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b xb
      by (rule nempty_iff)
    subgoal by auto
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b xb
      by (simp add: is_lasts_def in_set_dropI)
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b xb
      by (auto simp: is_lasts_le)
    subgoal by (rule le_uint_max)
    subgoal by auto
    subgoal for \<A>' x x' x1 x2 x1a x2a x1b x2b A xa xb
      by (rule IH)
    subgoal by auto
    done
  moreover have \<open>iterate_over_VMTF f I (ns, Some fst_As) x  \<le> \<Down> Id (iterate_over_VMTF2 f I (ns, Some fst_As) x)\<close>
    unfolding iterate_over_VMTF2_alt_def iterate_over_VMTF_def prod.case
    by (refine_vcg WHILEIT_refine[where R = \<open>{((n :: nat option, x::'a), (n' :: nat option, m'::nat, x'::'a)).
        n = n' \<and> x = x'}\<close>]) auto
  ultimately show ?thesis
    by simp
qed


definition arena_is_packed :: \<open>arena \<Rightarrow> nat clauses_l \<Rightarrow> bool\<close> where
\<open>arena_is_packed arena N \<longleftrightarrow> length arena = (\<Sum>C \<in># dom_m N. length (N \<propto> C) + header_size (N \<propto> C))\<close>

lemma arena_is_packed_empty[simp]: \<open>arena_is_packed [] fmempty\<close>
  by (auto simp: arena_is_packed_def)

lemma sum_mset_cong:
  \<open>(\<And>A. A \<in># M \<Longrightarrow> f A = g A) \<Longrightarrow> (\<Sum> A \<in># M. f A) = (\<Sum> A \<in># M. g A)\<close>
  by (induction M) auto
lemma arena_is_packed_append:
  assumes \<open>arena_is_packed (arena) N\<close> and
    [simp]: \<open>length C = length (fst C') + header_size (fst C')\<close> and
    [simp]: \<open>a \<notin># dom_m N\<close>
  shows \<open>arena_is_packed (arena @ C) (fmupd a C' N)\<close>
proof -
  show ?thesis
    using assms(1) by (auto simp: arena_is_packed_def
     intro!: sum_mset_cong)
qed

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

definition isasat_GC_clauses_prog_copy_wl_entry
  :: \<open>arena \<Rightarrow> (nat watcher) list list \<Rightarrow> nat literal \<Rightarrow>
         (arena \<times> _ \<times> _) \<Rightarrow> (arena \<times> (arena \<times> _ \<times> _)) nres\<close>
where
\<open>isasat_GC_clauses_prog_copy_wl_entry = (\<lambda>N W A (N', vdm, avdm). do {
    ASSERT(nat_of_lit A < length W);
    let le = length (W ! nat_of_lit A);
    (i, N, N', vdm, avdm) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, N', vdm, avdm). i < le)
      (\<lambda>(i, N, (N', vdm, avdm)). do {
        ASSERT(i < length (W ! nat_of_lit A));
        let C = fst (W ! nat_of_lit A ! i);
        ASSERT(arena_is_valid_clause_vdom N C);
        let st = arena_status N C;
        if st \<noteq> DELETED then do {
          ASSERT(arena_is_valid_clause_idx N C);
          let D = length N' + (if arena_length N C > 4 then 5 else 4);
          N' \<leftarrow> fm_mv_clause_to_new_arena C N N';
          ASSERT(mark_garbage_pre (N, C));
	  RETURN (i+1, extra_information_mark_to_delete N C, N', vdm @ [D],
             (if st = LEARNED then avdm @ [D] else avdm))
        } else RETURN (i+1, N, (N', vdm, avdm))
      }) (0, N, (N', vdm, avdm));
    RETURN (N, (N', vdm, avdm))
  })\<close>

lemma isasat_GC_clauses_prog_copy_wl_entry:
  assumes \<open>valid_arena arena N vdom0\<close> and
    \<open>valid_arena arena' N' (set vdom)\<close> and
    vdom: \<open>vdom_m \<A> W N \<subseteq> vdom0\<close> and
    L: \<open>atm_of A \<in># \<A>\<close> and
    L'_L: \<open>(A', A) \<in> nat_lit_lit_rel\<close> and
    W: \<open>(W' , W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    \<open>dom_m N' = mset vdom\<close> \<open>distinct vdom\<close> and
   \<open>arena_is_packed arena' N'\<close> and
   avdom: \<open>mset avdom \<subseteq># mset vdom\<close>
  shows \<open>isasat_GC_clauses_prog_copy_wl_entry arena W' A' (arena', vdom, avdom)
     \<le> \<Down> ({(arena, N'). valid_arena arena N' vdom0 \<and> vdom_m \<A> W N' \<subseteq> vdom0 \<and> dom_m N' \<subseteq># dom_m N} \<times>\<^sub>f
    {((arena, vdom, avdom), N). valid_arena arena N (set vdom) \<and> dom_m N = mset vdom \<and> distinct vdom \<and>
     arena_is_packed arena N \<and> mset avdom \<subseteq># mset vdom})
         (cdcl_GC_clauses_prog_copy_wl_entry N (W A) A N')\<close>
     (is \<open>_ \<le> \<Down> (?R\<^sub>1 \<times>\<^sub>f ?R\<^sub>2) _\<close>)
proof -
  have A: \<open>A' = A\<close> and K[simp]: \<open>W' ! nat_of_lit A = W A\<close>
    using L'_L L W apply auto
    by (cases A) (auto simp: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset dest!: multi_member_split)
  have A_le: \<open>nat_of_lit A < length W'\<close>
    using W L by (cases A; auto simp: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset dest!: multi_member_split)
  show ?thesis
    unfolding isasat_GC_clauses_prog_copy_wl_entry_def cdcl_GC_clauses_prog_copy_wl_entry_def prod.case A
    apply (refine_vcg WHILET_refine[where R = \<open>nat_rel \<times>\<^sub>r ?R\<^sub>1 \<times>\<^sub>r ?R\<^sub>2\<close>])
    subgoal using A_le by auto
    subgoal using assms by auto
    subgoal using W L by auto
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      using vdom L
      unfolding arena_is_valid_clause_vdom_def K
      by (cases A)
        (force dest!: multi_member_split simp: vdom_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)+
    subgoal
      using vdom L
      unfolding arena_is_valid_clause_vdom_def K
      by (subst arena_dom_status_iff)
        (cases A ; auto dest!: multi_member_split simp: arena_lifting arena_dom_status_iff
            vdom_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset; fail)+
   subgoal
     unfolding arena_is_valid_clause_idx_def
     by auto
   subgoal
     by (force dest: arena_lifting(2))
   subgoal by auto
   subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d D
     by (rule order_trans[OF fm_mv_clause_to_new_arena])
      (auto intro: valid_arena_extra_information_mark_to_delete'
         simp: header_size_def arena_lifting remove_1_mset_id_iff_notin
            mark_garbage_pre_def slice_len_min_If
       dest: in_vdom_m_fmdropD arena_lifting(2)
       intro!: arena_is_packed_append_valid subset_mset_trans_add_mset)
   subgoal
     by auto
   subgoal
     by auto
   done
 qed

definition isasat_GC_clauses_prog_single_wl
  :: \<open>arena \<Rightarrow>  (arena \<times> _ \<times> _) \<Rightarrow> (nat watcher) list list \<Rightarrow> nat \<Rightarrow>
        (arena \<times> (arena \<times> _ \<times> _) \<times> (nat watcher) list list) nres\<close>
where
\<open>isasat_GC_clauses_prog_single_wl = (\<lambda>N N' WS A. do {
    let L = Pos A; \<^cancel>\<open>use phase saving instead\<close>
    ASSERT(nat_of_lit L < length WS);
    ASSERT(nat_of_lit (-L) < length WS);
    (N, (N', vdom, avdom)) \<leftarrow> isasat_GC_clauses_prog_copy_wl_entry N WS L N';
    let WS = WS[nat_of_lit L := []];
    (N, N') \<leftarrow> isasat_GC_clauses_prog_copy_wl_entry N WS (-L) (N', vdom, avdom);
    let WS = WS[nat_of_lit (-L) := []];
    RETURN (N, N', WS)
  })\<close>

definition isasat_GC_refl :: \<open>_\<close> where
\<open>isasat_GC_refl \<A> vdom0 = {((arena\<^sub>o, (arena, vdom, avdom), W), (N\<^sub>o, N, W')). valid_arena arena\<^sub>o N\<^sub>o vdom0 \<and> valid_arena arena N (set vdom) \<and>
     (W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N\<^sub>o \<subseteq> vdom0 \<and> dom_m N = mset vdom \<and> distinct vdom \<and>
    arena_is_packed arena N \<and> mset avdom \<subseteq># mset vdom}\<close>

lemma isasat_GC_clauses_prog_single_wl:
  assumes
    \<open>(X, X') \<in> isasat_GC_refl \<A> vdom0\<close> and
    X: \<open>X = (arena, (arena', vdom, avdom), W)\<close> \<open>X' = (N, N', W')\<close> and
    L: \<open>A \<in># \<A>\<close> and
    st: \<open>(A, A') \<in> Id\<close> and st': \<open>narena = (arena', vdom, avdom)\<close>
  shows \<open>isasat_GC_clauses_prog_single_wl arena narena  W A
     \<le> \<Down> (isasat_GC_refl \<A> vdom0)
         (cdcl_GC_clauses_prog_single_wl N W' A' N')\<close>
     (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  have H:
    \<open>valid_arena arena N vdom0\<close>
    \<open>valid_arena arena' N' (set vdom)\<close> and
    vdom: \<open>vdom_m \<A> W' N \<subseteq> vdom0\<close> and
    L: \<open>A \<in># \<A>\<close> and
    eq: \<open>A' = A\<close> and
    WW': \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    vdom_dom: \<open>dom_m N' = mset vdom\<close> and
    dist: \<open>distinct vdom\<close> and
    packed: \<open>arena_is_packed arena' N'\<close> and
    avdom: \<open>mset avdom \<subseteq># mset vdom\<close>
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
  show ?thesis
    unfolding isasat_GC_clauses_prog_single_wl_def
      cdcl_GC_clauses_prog_single_wl_def eq st' isasat_GC_refl_def
    apply (refine_vcg
      isasat_GC_clauses_prog_copy_wl_entry)
    subgoal using le by auto
    subgoal using le by auto
    apply (rule H(1); fail)
    apply (rule H(2); fail)
    apply (rule vdom; fail)
    subgoal
      using L by auto
    subgoal using WW'
      by auto
    subgoal using vdom_dom by blast
    subgoal using dist by blast
    subgoal using packed by blast
    subgoal using avdom by blast
    apply (solves auto)
    apply (solves auto)
    apply (rule vdom2; auto)
    subgoal
      using L by auto
    subgoal by auto
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using WW' by (auto simp: map_fun_rel_def dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    subgoal using W vdom by auto (blast dest: vdom_m_upd vdom_m3)
    done
qed

definition isasat_GC_clauses_prog_wl2 where
  \<open>isasat_GC_clauses_prog_wl2 \<equiv> (\<lambda>(ns :: (nat, nat) vmtf_node list, n) x. do {
      (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). True\<^esup>
        (\<lambda>(n, _). n \<noteq> None)
        (\<lambda>(n, x). do {
          ASSERT(n \<noteq> None);
          let A = the n;
          ASSERT(A < length ns);
          ASSERT(A \<le> uint32_max div 2);
          x \<leftarrow> (\<lambda>(arena\<^sub>o, arena, W). isasat_GC_clauses_prog_single_wl arena\<^sub>o arena W A) x;
          RETURN (get_next ((ns ! A)), x)
        })
        (n, x);
      RETURN x
    })\<close>

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


lemma WHILEIT_refine_with_invariant_and_break:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF:
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>{(x, x'). (x, x') \<in> R \<and> I x \<and>  I' x' \<and> \<not>b' x'} (WHILEIT I' b' f' x')"
  (is \<open>_ \<le> \<Down>?R' _\<close>)
    apply (subst (2)WHILEIT_add_post_condition)
    apply (refine_vcg WHILEIT_refine_genR[where R'=R and R = ?R'])
    subgoal by (auto intro: assms)[]
    subgoal by (auto intro: assms)[]
    subgoal using COND_REF by (auto)
    subgoal by (auto intro: assms)[]
    subgoal by (auto intro: assms)[]
    done

lemma cdcl_GC_clauses_prog_wl_inv_cong_empty:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow>
  cdcl_GC_clauses_prog_wl_inv \<A> N ({#}, x) \<Longrightarrow> cdcl_GC_clauses_prog_wl_inv \<B> N ({#}, x)\<close>
  by (auto simp: cdcl_GC_clauses_prog_wl_inv_def)

lemma isasat_GC_clauses_prog_wl2:
  assumes \<open>valid_arena arena\<^sub>o N\<^sub>o vdom0\<close> and
    \<open>valid_arena arena N (set vdom)\<close> and
    vdom: \<open>vdom_m \<A> W' N\<^sub>o \<subseteq> vdom0\<close> and
    vmtf: \<open>((ns, m, n, lst_As1, next_search1), to_remove1) \<in> vmtf \<A> M\<close> and
    nempty: \<open>\<A> \<noteq> {#}\<close> and
    W_W': \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close> and old: \<open>old_arena = []\<close>
 shows
    \<open>isasat_GC_clauses_prog_wl2 (ns, Some n) (arena\<^sub>o, (old_arena, [], []), W)
        \<le> \<Down> ({((arena\<^sub>o, (arena, vdom, avdom), W), (N\<^sub>o', N, W')). valid_arena arena\<^sub>o N\<^sub>o' vdom0 \<and> valid_arena arena N (set vdom) \<and>
       (W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N\<^sub>o' \<subseteq> vdom0 \<and>
        cdcl_GC_clauses_prog_wl_inv \<A> N\<^sub>o ({#}, N\<^sub>o', N, W') \<and> dom_m N = mset vdom \<and> distinct vdom \<and>
        arena_is_packed arena N \<and> mset avdom \<subseteq># mset vdom})
         (cdcl_GC_clauses_prog_wl2 N\<^sub>o \<A> W')\<close>
proof -
  define f where
    \<open>f A \<equiv> (\<lambda>(arena\<^sub>o, arena, W). isasat_GC_clauses_prog_single_wl arena\<^sub>o arena W A)\<close> for A :: nat
  let ?R = \<open>{((\<A>', arena\<^sub>o, (arena, vdom), W), (\<A>'', N\<^sub>o', N, W')). \<A>' = \<A>'' \<and>
      ((arena\<^sub>o, (arena, vdom), W), (N\<^sub>o', N, W')) \<in> isasat_GC_refl \<A> vdom0}\<close>
  let ?S = \<open>{((\<A>', arena\<^sub>o, (arena, vdom), W), (\<A>'', N\<^sub>o', N, W')). \<A>' = \<A>'' \<and>
      ((arena\<^sub>o, (arena, vdom), W), (N\<^sub>o', N, W')) \<in> isasat_GC_refl \<A> vdom0 \<and>
            cdcl_GC_clauses_prog_wl_inv \<A> N\<^sub>o (\<A>'', N\<^sub>o', N, W')}\<close>
  have H: \<open>(X, X') \<in> ?R \<Longrightarrow> X = (x1, x2) \<Longrightarrow> x2 = (x3, x4) \<Longrightarrow> x4 = (x5, x6) \<Longrightarrow>
     X' = (x1', x2') \<Longrightarrow> x2' = (x3', x4') \<Longrightarrow> x4' = (x5', x6') \<Longrightarrow>
     ((x3, (fst x5, fst (snd x5), snd (snd x5)), x6), (x3', x5', x6')) \<in> isasat_GC_refl \<A> vdom0\<close>
    for X X' A B x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x0 x0' x x'
     supply [[show_types]]
    by auto
  have isasat_GC_clauses_prog_wl_alt_def:
    \<open>isasat_GC_clauses_prog_wl2 = iterate_over_VMTF f (\<lambda>_. True)\<close>
    unfolding f_def isasat_GC_clauses_prog_wl2_def iterate_over_VMTF_def by (auto intro!: ext)
  show ?thesis
    unfolding isasat_GC_clauses_prog_wl_alt_def prod.case f_def[symmetric] old
    apply (rule order_trans[OF iterate_over_VMTF_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l[OF vmtf nempty bounded]])
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
    subgoal by (auto simp: isasat_GC_refl_def
      dest: cdcl_GC_clauses_prog_wl_inv_cong_empty)
    done
qed


lemma cdcl_GC_clauses_prog_wl_alt_def:
  \<open>cdcl_GC_clauses_prog_wl = (\<lambda>(M, N0, D, NE, UE, Q, WS). do {
    ASSERT(cdcl_GC_clauses_pre_wl (M, N0, D, NE, UE, Q, WS));
    (N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_wl2 N0 (all_init_atms N0 NE) WS;
    RETURN (M, N', D, NE, UE, Q, WS)
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
     apply (subst order_class.eq_iff[of \<open>(_ :: _ nres)\<close>])
     apply (intro conjI)
     subgoal
       by (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric]) (refine_rcg WHILEIT_refine[where R = Id], auto)
     subgoal
       by (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric]) (refine_rcg WHILEIT_refine[where R = Id], auto)
     done
qed

definition isasat_GC_clauses_prog_wl :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>isasat_GC_clauses_prog_wl = (\<lambda>(M', N', D', j, W', ((ns, st, fst_As, lst_As, nxt), to_remove), \<phi>, clvls, cach, lbd, outl, stats,
    fast_ema, slow_ema, ccount,  vdom, avdom, lcount, opts, old_arena). do {
    ASSERT(old_arena = []);
    (N, (N', vdom, avdom), WS) \<leftarrow> isasat_GC_clauses_prog_wl2 (ns, Some fst_As) (N', (old_arena, take 0 vdom, take 0 avdom), W');
    RETURN (M', N', D', j, WS, ((ns, st, fst_As, lst_As, nxt), to_remove), \<phi>, clvls, cach, lbd, outl, incr_GC stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts, take 0 N)
  })\<close>


lemma isasat_GC_clauses_prog_wl:
  \<open>(isasat_GC_clauses_prog_wl, cdcl_GC_clauses_prog_wl) \<in>
   twl_st_heur_restart \<rightarrow>\<^sub>f
   \<langle>{(S, T). (S, T) \<in> twl_st_heur_restart \<and> arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T)}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?T \<rightarrow>\<^sub>f _\<close>)
proof-
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab.
       ((x1f, x1g, x1h, x1i, x1j, ((x1m, x1n, x1o, x1p, x2n), x2o), x1q, x1r,
         x1s, x1t, x1u, x1v, x1w, x1x, x1y, x1z, x1aa, x1ab, x2ab),
        x1, x1a, x1b, x1c, x1d, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       valid_arena x1g x1a (set x1z)\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab.
       ((x1f, x1g, x1h, x1i, x1j, ((x1m, x1n, x1o, x1p, x2n), x2o), x1q, x1r,
         x1s, x1t, x1u, x1v, x1w, x1x, x1y, x1z, x1aa, x1ab, x2ab),
        x1, x1a, x1b, x1c, x1d, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       isasat_input_bounded (all_init_atms x1a x1c)\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab.
       ((x1f, x1g, x1h, x1i, x1j, ((x1m, x1n, x1o, x1p, x2n), x2o), x1q, x1r,
         x1s, x1t, x1u, x1v, x1w, x1x, x1y, x1z, x1aa, x1ab, x2ab),
        x1, x1a, x1b, x1c, x1d, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       vdom_m (all_init_atms x1a x1c) x2e x1a \<subseteq> set x1z\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab.
       ((x1f, x1g, x1h, x1i, x1j, ((x1m, x1n, x1o, x1p, x2n), x2o), x1q, x1r,
         x1s, x1t, x1u, x1v, x1w, x1x, x1y, x1z, x1aa, x1ab, x2ab),
        x1, x1a, x1b, x1c, x1d, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       all_init_atms x1a x1c \<noteq> {#}\<close>
     unfolding twl_st_heur_restart_def
     by auto
  have [refine0]: \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab.
       ((x1f, x1g, x1h, x1i, x1j, ((x1m, x1n, x1o, x1p, x2n), x2o), x1q, x1r,
         x1s, x1t, x1u, x1v, x1w, x1x, x1y, x1z, x1aa, x1ab, x2ab),
        x1, x1a, x1b, x1c, x1d, x1e, x2e)
       \<in> ?T \<Longrightarrow>
       ((x1m, x1n, x1o, x1p, x2n), set (fst x2o)) \<in> vmtf (all_init_atms x1a x1c) x1\<close>
       \<open>\<And>x1 x1a x1b x1c x1d x1e x2e x1f x1g x1h x1i x1j x1m x1n x1o x1p x2n x2o x1q
       x1r x1s x1t x1u x1v x1w x1x x1y x1z x1aa x1ab x2ab.
       ((x1f, x1g, x1h, x1i, x1j, ((x1m, x1n, x1o, x1p, x2n), x2o), x1q, x1r,
         x1s, x1t, x1u, x1v, x1w, x1x, x1y, x1z, x1aa, x1ab, x2ab),
        x1, x1a, x1b, x1c, x1d, x1e, x2e)
       \<in> ?T \<Longrightarrow> (x1j, x2e) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms x1a x1c))\<close>
     unfolding twl_st_heur_restart_def isa_vmtf_def distinct_atoms_rel_def distinct_hash_atoms_rel_def
     by auto
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
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isasat_GC_clauses_prog_wl_def cdcl_GC_clauses_prog_wl_alt_def take_0
    apply (intro frefI nres_relI)
    apply (refine_vcg isasat_GC_clauses_prog_wl2[where \<A> = \<open>all_init_atms _ _\<close>]; remove_dummy_vars)
    subgoal
      by (clarsimp simp add: twl_st_heur_restart_def
        cdcl_GC_clauses_prog_wl_inv_def H H'
        rtranclp_GC_remap_all_init_atms
        rtranclp_GC_remap_learned_clss_l)
    subgoal
      by (clarsimp simp add: twl_st_heur_restart_def
        cdcl_GC_clauses_prog_wl_inv_def H H'
        rtranclp_GC_remap_all_init_atms
        rtranclp_GC_remap_learned_clss_l)
    done
qed

definition cdcl_remap_st :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>cdcl_remap_st = (\<lambda>(M, N0, D, NE, UE, Q, WS).
  SPEC (\<lambda>(M', N', D', NE', UE', Q', WS'). (M', D', NE', UE', Q') = (M, D, NE, UE, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N'))\<close>

definition rewatch_spec :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>rewatch_spec = (\<lambda>(M, N, D, NE, UE, Q, WS).
  SPEC (\<lambda>(M', N', D', NE', UE', Q', WS'). (M', N', D', NE', UE', Q') = (M, N, D, NE, UE, Q) \<and>
     correct_watching' (M, N', D, NE, UE, Q', WS') \<and>
     blits_in_\<L>\<^sub>i\<^sub>n' (M, N', D, NE, UE, Q', WS')))\<close>

lemma RES_RES7_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(a, b, c, d, e, g, h). RES (f a b c d e g h)) = RES (\<Union>((\<lambda>(a, b, c, d, e, g, h). f a b c d e g h) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def Bex_def split: prod.splits)

lemma cdcl_GC_clauses_wl_D_alt_def:
  \<open>cdcl_GC_clauses_wl_D = (\<lambda>S. do {
    ASSERT(cdcl_GC_clauses_pre_wl_D S);
    let b = True;
    if b then do {
      S \<leftarrow> cdcl_remap_st S;
      S \<leftarrow> rewatch_spec S;
      RETURN S
    }
    else RETURN S})\<close>
  supply [[goals_limit=1]]
  unfolding cdcl_GC_clauses_wl_D_def
  by (fastforce intro!: ext simp: RES_RES_RETURN_RES2 cdcl_remap_st_def
    RES_RES7_RETURN_RES uncurry_def image_iff
    RES_RETURN_RES_RES2 RES_RETURN_RES RES_RES2_RETURN_RES rewatch_spec_def
    intro!: bind_cong_nres)


definition isasat_GC_clauses_pre_wl_D :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
\<open>isasat_GC_clauses_pre_wl_D S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> twl_st_heur_restart \<and> cdcl_GC_clauses_pre_wl_D T
  )\<close>


definition isasat_GC_clauses_wl_D :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
\<open>isasat_GC_clauses_wl_D = (\<lambda>S. do {
  ASSERT(isasat_GC_clauses_pre_wl_D S);
  let b = True;
  if b then do {
    T \<leftarrow> isasat_GC_clauses_prog_wl S;
    ASSERT(length (get_clauses_wl_heur T) \<le> length (get_clauses_wl_heur S));
    ASSERT(\<forall>i \<in> set (get_vdom T). i < length (get_clauses_wl_heur S));
    U \<leftarrow> rewatch_heur_st T;
    RETURN U
  }
  else RETURN S})\<close>


lemma cdcl_GC_clauses_prog_wl2_st:
  assumes \<open>(T, S) \<in> state_wl_l None\<close>
  \<open>correct_watching'' T \<and> cdcl_GC_clauses_pre S \<and>
   set_mset (dom_m (get_clauses_wl T)) \<subseteq> clauses_pointed_to
      (Neg ` set_mset (all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T)) \<union>
       Pos ` set_mset (all_init_atms (get_clauses_wl T) (get_unit_init_clss_wl T)))
       (get_watched_wl T)\<close> and
    \<open>get_clauses_wl T = N0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl T \<le>
       \<Down> {((M', N'', D', NE', UE', Q', WS'), (N, N')).
       (M', D', NE', UE', Q') = (get_trail_wl T, get_conflict_wl T, get_unit_init_clss_wl T,
           get_unit_learned_clss_wl T, literals_to_update_wl T) \<and> N'' = N \<and>
           (\<forall>L\<in>#all_init_lits (get_clauses_wl T) (get_unit_init_clss_wl T). WS' L = []) \<and>
           all_init_lits (get_clauses_wl T) (get_unit_init_clss_wl T) = all_init_lits N NE' \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (get_clauses_wl T, Map.empty, fmempty)
               (fmempty, m, N))}
      (SPEC(\<lambda>(N'::(nat, 'a literal list \<times> bool) fmap, m).
         GC_remap\<^sup>*\<^sup>* (N0', (\<lambda>_. None), fmempty) (fmempty, m, N') \<and>
	  0 \<notin># dom_m N'))\<close>
   using cdcl_GC_clauses_prog_wl2[of \<open>get_trail_wl T\<close> \<open>get_clauses_wl T\<close> \<open>get_conflict_wl T\<close>
     \<open>get_unit_init_clss_wl T\<close> \<open>get_unit_learned_clss_wl T\<close> \<open>literals_to_update_wl T\<close>
     \<open>get_watched_wl T\<close> S] assms
   by (cases T) auto

lemma correct_watching''_clauses_pointed_to:
  assumes
    xa_xb: \<open>(xa, xb) \<in> state_wl_l None\<close> and
    corr: \<open>correct_watching'' xa\<close> and
    pre: \<open>cdcl_GC_clauses_pre xb\<close> and
    L: \<open>literals_are_\<L>\<^sub>i\<^sub>n'
      (all_init_atms (get_clauses_wl xa) (get_unit_init_clss_wl xa)) xa\<close>
  shows \<open>set_mset (dom_m (get_clauses_wl xa))
         \<subseteq> clauses_pointed_to
            (Neg `
             set_mset
              (all_init_atms (get_clauses_wl xa) (get_unit_init_clss_wl xa)) \<union>
             Pos `
             set_mset
              (all_init_atms (get_clauses_wl xa) (get_unit_init_clss_wl xa)))
            (get_watched_wl xa)\<close>
        (is \<open>_ \<subseteq> ?A\<close>)
proof
  let ?\<A> = \<open>all_init_atms (get_clauses_wl xa) (get_unit_init_clss_wl xa)\<close>
  fix C
  assume C: \<open>C \<in># dom_m (get_clauses_wl xa)\<close>
  obtain M N D NE UE Q W where
    xa: \<open>xa = (M, N, D, NE, UE, Q, W)\<close>
    by (cases xa)
  obtain x where
    xb_x: \<open>(xb, x) \<in> twl_st_l None\<close> and
    \<open>twl_list_invs xb\<close> and
    struct_invs: \<open>twl_struct_invs x\<close> and
    \<open>get_conflict_l xb = None\<close> and
    \<open>clauses_to_update_l xb = {#}\<close> and
    \<open>count_decided (get_trail_l xb) = 0\<close> and
    \<open>\<forall>L\<in>set (get_trail_l xb). mark_of L = 0\<close>
    using pre unfolding cdcl_GC_clauses_pre_def by fast
  have \<open>twl_st_inv x\<close>
    using xb_x C struct_invs
    by (auto simp: twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
  then have le0: \<open>get_clauses_wl xa \<propto> C \<noteq> []\<close>
    using xb_x C xa_xb
    by (cases x; cases \<open>irred N C\<close>)
      (auto simp: twl_struct_invs_def twl_st_inv.simps
        twl_st_l_def state_wl_l_def xa ran_m_def conj_disj_distribR
        Collect_disj_eq Collect_conv_if
      dest!: multi_member_split)
  then have le: \<open>N \<propto> C ! 0 \<in> set (watched_l (N \<propto> C))\<close>
    by (cases \<open>N \<propto> C\<close>) (auto simp: xa)
  have eq: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NE)) =
        set_mset (all_lits_of_mm (mset `# init_clss_lf N + NE))\<close>
     by (auto simp del: all_init_atms_def[symmetric]
        simp: all_init_atms_def xa \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm[symmetric]
          all_init_lits_def)
  have H: \<open>get_clauses_wl xa \<propto> C ! 0 \<in># all_lits_of_mm (mset `# init_clss_lf (get_clauses_wl xa) + get_unit_init_clss_wl xa)\<close>
    using L C le0 apply -
    by (subst (asm) literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[OF xa_xb xb_x struct_invs])
      (cases \<open>N \<propto> C\<close>; auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def ran_m_def eq
          all_lits_of_mm_add_mset is_\<L>\<^sub>a\<^sub>l\<^sub>l_def xa all_lits_of_m_add_mset
        dest!: multi_member_split)
  moreover {
    have \<open>{#i \<in># fst `# mset (W (N \<propto> C ! 0)). i \<in># dom_m N#} =
           add_mset C {#Ca \<in># remove1_mset C (dom_m N). N \<propto> C ! 0 \<in> set (watched_l (N \<propto> Ca))#}\<close>
      using corr H C le unfolding xa
      by (auto simp: clauses_pointed_to_def correct_watching''.simps xa
        simp: all_init_atms_def all_init_lits_def clause_to_update_def
        simp del: all_init_atms_def[symmetric]
        dest!: multi_member_split)
    from arg_cong[OF this, of set_mset] have \<open>C \<in> fst ` set (W (N \<propto> C ! 0))\<close>
      using corr H C le unfolding xa
      by (auto simp: clauses_pointed_to_def correct_watching''.simps xa
        simp: all_init_atms_def all_init_lits_def clause_to_update_def
        simp del: all_init_atms_def[symmetric]
        dest!: multi_member_split) }
  ultimately show \<open>C \<in> ?A\<close>
    by (cases \<open>N \<propto> C ! 0\<close>)
      (auto simp: clauses_pointed_to_def correct_watching''.simps xa
      simp: all_init_atms_def all_init_lits_def clause_to_update_def
      simp del: all_init_atms_def[symmetric]
      dest!: multi_member_split)
qed

abbreviation isasat_GC_clauses_rel where
  \<open>isasat_GC_clauses_rel y \<equiv> {(S, T). (S, T) \<in> twl_st_heur_restart \<and>
           (\<forall>L\<in>#all_init_lits (get_clauses_wl y) (get_unit_init_clss_wl y). get_watched_wl T L = [])\<and>
           all_init_lits_st y = all_init_lits (get_clauses_wl y) (get_unit_init_clss_wl y) \<and>
           get_trail_wl T = get_trail_wl y \<and>
           get_conflict_wl T = get_conflict_wl y \<and>
           get_unit_init_clss_wl T = get_unit_init_clss_wl y \<and>
           get_unit_learned_clss_wl T = get_unit_learned_clss_wl y \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, (\<lambda>_. None), fmempty) (fmempty, m, get_clauses_wl T)) \<and>
           arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T)}\<close>

lemma ref_two_step'': \<open>R \<subseteq> R' \<Longrightarrow> A \<le> B \<Longrightarrow> \<Down> R A \<le>  \<Down> R' B\<close>
  by (simp add: "weaken_\<Down>" ref_two_step')

lemma isasat_GC_clauses_prog_wl_cdcl_remap_st:
  assumes
    \<open>(x, y) \<in> twl_st_heur_restart\<close> and
    \<open>cdcl_GC_clauses_pre_wl_D y\<close>
  shows \<open>isasat_GC_clauses_prog_wl x \<le> \<Down> (isasat_GC_clauses_rel y) (cdcl_remap_st y)\<close>
proof -
  have H: \<open>isasat_GC_clauses_rel y =
    {(S, T). (S, T) \<in> twl_st_heur_restart \<and> arena_is_packed (get_clauses_wl_heur S) (get_clauses_wl T)} O
    {(S, T). S = T \<and> (\<forall>L\<in>#all_init_lits_st y. get_watched_wl T L = [])\<and>
           all_init_lits_st y = all_init_lits (get_clauses_wl y) (get_unit_init_clss_wl y) \<and>
           get_trail_wl T = get_trail_wl y \<and>
           get_conflict_wl T = get_conflict_wl y \<and>
           get_unit_init_clss_wl T = get_unit_init_clss_wl y \<and>
           get_unit_learned_clss_wl T = get_unit_learned_clss_wl y \<and>
           (\<exists>m. GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, (\<lambda>_. None), fmempty) (fmempty, m, get_clauses_wl T))}\<close>
    by blast
  show ?thesis
    using assms apply -
    apply (rule order_trans[OF isasat_GC_clauses_prog_wl[THEN fref_to_Down]])
    subgoal by fast
    apply assumption
    unfolding conc_fun_chain[symmetric] H
    apply (rule ref_two_step')
    unfolding cdcl_GC_clauses_pre_wl_D_def cdcl_GC_clauses_pre_wl_def
    apply normalize_goal+
    apply (rule order_trans[OF cdcl_GC_clauses_prog_wl2_st])
    apply (solves auto)
    subgoal for xa xb by (simp add: correct_watching''_clauses_pointed_to)
    apply (rule refl)
    subgoal by (auto simp: cdcl_remap_st_def conc_fun_RES split: prod.splits)
    done
qed

fun correct_watching''' :: \<open>_ \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching''' \<A> (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_mm \<A>.
       distinct_watched (W L) \<and>
       (\<forall>(i, K, b)\<in>#mset (W L).
             i \<in># dom_m N \<and> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
             correctly_marked_as_binary N (i, K, b)) \<and>
        fst `# mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

declare correct_watching'''.simps[simp del]

lemma correct_watching'''_add_clause:
  assumes
    corr: \<open>correct_watching''' \<A> ((a, aa, CD, ac, ad, Q, b))\<close> and
    leC: \<open>2 \<le> length C\<close> and
    i_notin[simp]: \<open>i \<notin># dom_m aa\<close> and
    dist[iff]: \<open>C ! 0 \<noteq> C ! Suc 0\<close>
  shows \<open>correct_watching''' \<A>
          ((a, fmupd i (C, red) aa, CD, ac, ad, Q, b
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
    H[dest]: \<open>\<And>x. x \<in># dom_m N \<Longrightarrow> distinct (N \<propto> x) \<and> length (N \<propto> x) \<ge> 2\<close>
  shows
    \<open>rewatch N W \<le> SPEC(\<lambda>W. correct_watching''' \<A> (M, N, C, NE, UE, Q, W))\<close>
proof -
  define I where
    \<open>I \<equiv> \<lambda>(a :: nat list) (b :: nat list) W.
        correct_watching''' \<A> ((M, fmrestrict_set (set a) N, C, NE, UE, Q, W))\<close>
  have I0: \<open>set_mset (dom_m N) \<subseteq> set x \<and> distinct x \<Longrightarrow> I [] x W\<close> for x
    using empty unfolding I_def by (auto simp: correct_watching'''.simps
       all_blits_are_in_problem_init.simps clause_to_update_def
       all_lits_of_mm_union)

  show ?thesis
    unfolding rewatch_def
    apply (refine_vcg
      nfoldli_rule[where I = \<open>I\<close>])
    subgoal by (rule I0)
    subgoal using assms unfolding I_def by auto
    subgoal for x xa l1 l2 \<sigma>
      unfolding I_def
      apply (cases \<open>the (fmlookup N xa)\<close>)
      apply auto
      defer
       apply (rule correct_watching'''_add_clause)
          apply (auto simp: dom_m_fmrestrict_set')
      apply (auto dest!: H simp: nth_eq_iff_index_eq)
      apply (subst (asm) nth_eq_iff_index_eq)
      apply simp
      apply simp
       apply auto[]
      by linarith
    subgoal
      unfolding I_def
      by auto
    subgoal by auto
    subgoal unfolding I_def
      by (auto simp: fmlookup_restrict_set_id')
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
  using rtranclp_GC_remap_ran_m_no_new_map rtranclp_GC_remap_ran_m_no_rewrite by fastforce

lemma rewatch_heur_st_correct_watching:
  assumes
    pre: \<open>cdcl_GC_clauses_pre_wl_D y\<close> and
    S_T: \<open>(S, T) \<in> isasat_GC_clauses_rel y\<close>
  shows \<open>rewatch_heur_st S \<le> \<Down> (twl_st_heur_restart)
    (rewatch_spec T)\<close>
proof -
  obtain M N D NE UE Q W where
    T: \<open>T = (M, N, D, NE, UE, Q, W)\<close>
    by (cases T) auto

  obtain M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema ccount
       vdom avdom lcount opts where
    S: \<open>S = (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts)\<close>
    by (cases S) auto

  have
    valid: \<open>valid_arena N' N (set vdom)\<close> and
    dist: \<open>distinct vdom\<close> and
    dom_m_vdom: \<open>set_mset (dom_m N) \<subseteq> set vdom\<close> and
    W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N NE))\<close> and
    empty: \<open>\<And>L. L \<in># all_init_lits_st y \<Longrightarrow> W L = []\<close> and
    NUE:\<open>get_unit_init_clss_wl y = NE \<close>
      \<open>get_unit_learned_clss_wl y = UE\<close>
      \<open>get_trail_wl y = M\<close>
    using assms by (auto simp: twl_st_heur_restart_def S T)
  obtain m where
    m: \<open>GC_remap\<^sup>*\<^sup>* (get_clauses_wl y, Map.empty, fmempty)
             (fmempty, m, N)\<close>
    using assms by (auto simp: twl_st_heur_restart_def S T)
  obtain x xa xb where
    y_x: \<open>(y, x) \<in> Id\<close> \<open>x = y\<close> and
    lits_y: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st y) y\<close> and
    x_xa: \<open>(x, xa) \<in> state_wl_l None\<close> and
    \<open>correct_watching'' x\<close> and
    xa_xb: \<open>(xa, xb) \<in> twl_st_l None\<close> and
    \<open>twl_list_invs xa\<close> and
    struct_invs: \<open>twl_struct_invs xb\<close> and
    \<open>get_conflict_l xa = None\<close> and
    \<open>clauses_to_update_l xa = {#}\<close> and
    \<open>count_decided (get_trail_l xa) = 0\<close> and
    \<open>\<forall>L\<in>set (get_trail_l xa). mark_of L = 0\<close>
    using pre
    unfolding cdcl_GC_clauses_pre_wl_D_def cdcl_GC_clauses_pre_wl_def
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

  have eq3: \<open>all_init_lits (get_clauses_wl y) NE = all_init_lits N NE\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m]
    by (auto simp: all_init_lits_def)
  moreover have \<open>all_lits_st y = all_lits_st T\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m] rtranclp_GC_remap_learned_clss_l_old_new[OF m]
    apply (auto simp: all_init_lits_def T NUE all_lits_def)
    by (metis NUE(1) NUE(2) all_clss_l_ran_m all_lits_def get_unit_clauses_wl_alt_def)
  ultimately have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_init_atms N NE) (mset `# ran_mf N)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[OF x_xa xa_xb struct_invs] lits_y
      rtranclp_GC_remap_init_clss_l_old_new[OF m]
      rtranclp_GC_remap_learned_clss_l_old_new[OF m]
    apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits
      y_x literals_are_\<L>\<^sub>i\<^sub>n'_def literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def[of N] T
      get_unit_clauses_wl_alt_def all_lits_of_mm_union all_lits_def atm_of_eq_atm_of
      is_\<L>\<^sub>a\<^sub>l\<^sub>l_def NUE all_init_atms_def all_init_lits_def all_atms_def conj_disj_distribR
      in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def atm_of_all_lits_of_mm
      ex_disj_distrib Collect_disj_eq atms_of_def
      dest!: multi_member_split[of _ \<open>ran_m _\<close>]
      split: if_splits
      simp del: all_init_atms_def[symmetric] all_atms_def[symmetric])
      apply (auto dest!: eq_UnD dest!: split_list)
      done
  have eq: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms N NE)) = set_mset (all_init_lits_st y)\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m]
    by (auto simp: T all_init_lits_def NUE
      \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits)
  then have vd: \<open>vdom_m (all_init_atms N NE) W N \<subseteq> set_mset (dom_m N)\<close>
    using empty dom_m_vdom
    by (auto simp: vdom_m_def)
  have \<open>{#i \<in># clause_to_update L (M, N, get_conflict_wl y, NE, UE, {#}, {#}).
         i \<in># dom_m N#} =
       {#i \<in># clause_to_update L (M, N, get_conflict_wl y, NE, UE, {#}, {#}).
         True#}\<close> for L
       by (rule filter_mset_cong2)  (auto simp: clause_to_update_def)
  then have corr2: \<open>correct_watching'''
        ({#mset (fst x). x \<in># init_clss_l (get_clauses_wl y)#} + NE)
        (M, N, get_conflict_wl y, NE, UE, Q, W'a) \<Longrightarrow>
       correct_watching' (M, N, get_conflict_wl y, NE, UE, Q, W'a)\<close> for W'a
     using rtranclp_GC_remap_init_clss_l_old_new[OF m]
     by (auto simp: correct_watching'''.simps correct_watching'.simps)
  have eq2: \<open>all_init_lits (get_clauses_wl y) NE = all_init_lits N NE\<close>
    using rtranclp_GC_remap_init_clss_l_old_new[OF m]
    by (auto simp: T all_init_lits_def NUE
      \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits)
  have \<open>i \<in># dom_m N \<Longrightarrow> set (N \<propto> i) \<subseteq> set_mset (all_init_lits N NE)\<close> for i
    using lits by (auto dest!: multi_member_split split_list simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def ran_m_def
      all_lits_of_mm_add_mset all_lits_of_m_add_mset
      \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits)
  then have blit2: \<open>correct_watching'''
        ({#mset x. x \<in># init_clss_lf (get_clauses_wl y)#} + NE)
        (M, N, get_conflict_wl y, NE, UE, Q, W'a) \<Longrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n' (M, N, get_conflict_wl y, NE, UE, Q, W'a)\<close> for W'a
      using rtranclp_GC_remap_init_clss_l_old_new[OF m]
      unfolding  correct_watching'''.simps  blits_in_\<L>\<^sub>i\<^sub>n'_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits all_init_lits_def[symmetric]
      by (fastforce simp: correct_watching'''.simps  blits_in_\<L>\<^sub>i\<^sub>n'_def
        simp: eq \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits eq2
        dest!: multi_member_split[of _ \<open>all_init_lits N NE\<close>]
        dest: mset_eq_setD)
  have \<open>correct_watching'''
        ({#mset x. x \<in># init_clss_lf (get_clauses_wl y)#} + NE)
        (M, N, get_conflict_wl y, NE, UE, Q, W'a) \<Longrightarrow>
        vdom_m (all_init_atms N NE) W'a N \<subseteq> set_mset (dom_m N)\<close> for W'a
      unfolding  correct_watching'''.simps  blits_in_\<L>\<^sub>i\<^sub>n'_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms_all_init_lits all_init_lits_def[symmetric]
      using eq eq3
      by (force simp: correct_watching'''.simps vdom_m_def NUE)
  then have st: \<open>(x, W'a) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N NE)) \<Longrightarrow>
     correct_watching'''
        ({#mset x. x \<in># init_clss_lf (get_clauses_wl y)#} + NE)
        (M, N, get_conflict_wl y, NE, UE, Q, W'a) \<Longrightarrow>
      ((M', N', D', j, x, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
         slow_ema, ccount, vdom, avdom, lcount, opts),
        M, N, get_conflict_wl y, NE, UE, Q, W'a)
       \<in> twl_st_heur_restart\<close> for W'a m x
       using S_T dom_m_vdom
       by (auto simp: S T twl_st_heur_restart_def y_x NUE)

  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding rewatch_heur_st_def T S
    apply clarify
    apply (rule bind_refine_res)
    prefer 2
    apply (rule order.trans)
    apply (rule rewatch_heur_rewatch[OF valid _ dist dom_m_vdom W lits])
    apply (solves simp)
    apply (rule vd)
    apply (rule order_trans[OF ref_two_step'])
    apply (rule rewatch_correctness[where M=M and N=N and NE=NE and UE=UE and C=D and Q=Q])
    apply (rule empty[unfolded all_init_lits_def]; assumption)
    apply (rule struct_wf; assumption)
    apply (subst conc_fun_RES)
    apply (rule order.refl)
   apply (fastforce simp: rewatch_spec_def RETURN_RES_refine_iff NUE
      intro: corr2 blit2 st)
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
    xy: \<open>(x, y) \<in> twl_st_heur_restart\<close> and
    ST: \<open>(S, T) \<in> isasat_GC_clauses_rel y\<close>
  shows \<open>length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur x)\<close> and
     \<open>\<forall>C \<in> set (get_vdom S). C < length (get_clauses_wl_heur x)\<close>
proof -
  obtain m where
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>\<forall>L\<in>#all_init_lits_st y. get_watched_wl T L = []\<close> and
    \<open>get_trail_wl T = get_trail_wl y\<close> and
    \<open>get_conflict_wl T = get_conflict_wl y\<close> and
    \<open>get_unit_init_clss_wl T = get_unit_init_clss_wl y\<close> and
    \<open>get_unit_learned_clss_wl T = get_unit_learned_clss_wl y\<close> and
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
    using ST unfolding twl_st_heur_restart_def by (cases S; cases T) auto
  then show \<open>\<forall>C \<in> set (get_vdom S). C < length (get_clauses_wl_heur x)\<close>
    using le
    by (auto dest: valid_arena_in_vdom_le_arena)
qed

lemma isasat_GC_clauses_wl_D:
  \<open>(isasat_GC_clauses_wl_D, cdcl_GC_clauses_wl_D)
    \<in> twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
  unfolding isasat_GC_clauses_wl_D_def cdcl_GC_clauses_wl_D_alt_def
  apply (intro frefI nres_relI)
  apply (refine_vcg isasat_GC_clauses_prog_wl_cdcl_remap_st
    rewatch_heur_st_correct_watching)
  subgoal unfolding isasat_GC_clauses_pre_wl_D_def by blast
  subgoal by fast
  subgoal by (rule isasat_GC_clauses_rel_packed_le)
  subgoal by (rule isasat_GC_clauses_rel_packed_le(2))
  apply assumption+
  done



definition cdcl_twl_full_restart_wl_D_GC_heur_prog where
\<open>cdcl_twl_full_restart_wl_D_GC_heur_prog S0 = do {
    S \<leftarrow> do {
      if count_decided_st_heur S0 > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S0;
        empty_Q S
      } else RETURN S0
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    U \<leftarrow> mark_to_delete_clauses_wl_D_heur T;
    ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
    V \<leftarrow> isasat_GC_clauses_wl_D U;
    RETURN V
  }\<close>

lemma
    cdcl_twl_full_restart_wl_GC_prog_pre_heur:
      \<open>cdcl_twl_full_restart_wl_GC_prog_pre T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close> (is \<open>_ \<Longrightarrow> _ ?B\<close>) and
     cdcl_twl_full_restart_wl_D_GC_prog_post_heur:
       \<open>cdcl_twl_full_restart_wl_D_GC_prog_post S0 T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close>
proof -
  note cong =  trail_pol_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong

  show \<open>cdcl_twl_full_restart_wl_GC_prog_pre T \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def cdcl_twl_full_restart_l_GC_prog_pre_def
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
  show \<open>cdcl_twl_full_restart_wl_D_GC_prog_post S0 T \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_D_GC_prog_post_def
       cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    subgoal for S0' T' S0'' U S0'''
    apply (rule iffI)
    subgoal
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
        cdcl_twl_restart_l_invs[of S0'' S0''' U]
      apply -
      apply (clarsimp simp del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T')
      apply (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
      using isa_vmtf_cong option_lookup_clause_rel_cong trail_pol_cong by presburger
    subgoal
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
        cdcl_twl_restart_l_invs[of S0'' S0''' U]
      apply -
      apply (cases S; cases T)
      by (clarsimp simp add: twl_st_heur_def twl_st_heur_restart_def
        simp del: isasat_input_nempty_def)
    done
    done

qed

lemma cdcl_twl_full_restart_wl_D_GC_heur_prog:
  \<open>(cdcl_twl_full_restart_wl_D_GC_heur_prog, cdcl_twl_full_restart_wl_D_GC_prog) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def
    cdcl_twl_full_restart_wl_D_GC_prog_def
  apply (intro frefI nres_relI)
  apply (refine_rcg cdcl_twl_local_restart_wl_spec0
    remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D[THEN fref_to_Down]
    mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl2_D[THEN fref_to_Down]
    isasat_GC_clauses_wl_D[THEN fref_to_Down])
  apply (subst (asm) cdcl_twl_full_restart_wl_GC_prog_pre_heur, assumption)
  apply (rule twl_st_heur_restartD, assumption)
  subgoal
    unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def
      cdcl_twl_full_restart_l_GC_prog_pre_def
    by normalize_goal+ auto
  subgoal by (auto simp: twl_st_heur_restart_ana_def)
  apply assumption
  subgoal by (auto simp: twl_st_heur_restart_ana_def)
  apply assumption
  subgoal by (auto simp: twl_st_heur_restart_ana_def)
  subgoal for x y
    by (blast dest: twl_st_heur_restart_anaD)
  subgoal for x y
    by (blast dest: cdcl_twl_full_restart_wl_D_GC_prog_post_heur)
  done


definition restart_prog_wl_D_heur
  :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur \<times> nat) nres"
where
  \<open>restart_prog_wl_D_heur S n brk = do {
    b \<leftarrow> restart_required_heur S n;
    b2 \<leftarrow> GC_required_heur S n;
    if \<not>brk \<and> b \<and> b2
    then do {
       T \<leftarrow> cdcl_twl_full_restart_wl_D_GC_heur_prog S;
       RETURN (T, n+1)
    }
    else if \<not>brk \<and> b
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
proof -
  have [refine0]: \<open>GC_required_heur S n \<le> SPEC (\<lambda>_. True)\<close> for S n
    by (auto simp: GC_required_heur_def)
  show ?thesis
    unfolding restart_prog_wl_D_heur_def restart_prog_wl_D_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_required_heur_restart_required_wl[THEN fref_to_Down_curry]
        cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog[THEN fref_to_Down]
        cdcl_twl_full_restart_wl_D_GC_heur_prog[THEN fref_to_Down])
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

definition isasat_trail_nth_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat literal nres\<close> where
\<open>isasat_trail_nth_st S i = isa_trail_nth (get_trail_wl_heur S) i\<close>

lemma isasat_trail_nth_st_alt_def:
  \<open>isasat_trail_nth_st = (\<lambda>(M, _) i.  isa_trail_nth M i)\<close>
  by (auto simp: isasat_trail_nth_st_def intro!: ext)

definition get_the_propagation_reason_pol_st :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close> where
\<open>get_the_propagation_reason_pol_st S i = get_the_propagation_reason_pol (get_trail_wl_heur S) i\<close>

lemma get_the_propagation_reason_pol_st_alt_def:
  \<open>get_the_propagation_reason_pol_st = (\<lambda>(M, _) i.  get_the_propagation_reason_pol M i)\<close>
  by (auto simp: get_the_propagation_reason_pol_st_def intro!: ext)

definition isasat_length_trail_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
\<open>isasat_length_trail_st S = isa_length_trail (get_trail_wl_heur S)\<close>

lemma isasat_length_trail_st_alt_def:
  \<open>isasat_length_trail_st = (\<lambda>(M, _).  isa_length_trail M)\<close>
  by (auto simp: isasat_length_trail_st_def intro!: ext)

definition get_pos_of_level_in_trail_imp_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
\<open>get_pos_of_level_in_trail_imp_st S = get_pos_of_level_in_trail_imp (get_trail_wl_heur S)\<close>

lemma get_pos_of_level_in_trail_imp_alt_def:
  \<open>get_pos_of_level_in_trail_imp_st = (\<lambda>(M, _).  get_pos_of_level_in_trail_imp M)\<close>
  by (auto simp: get_pos_of_level_in_trail_imp_st_def intro!: ext)

sepref_de

lemma shorten_take_ll_0: \<open>shorten_take_ll L 0 W = W[L := []]\<close>
  by (auto simp: shorten_take_ll_def)

lemma length_shorten_take_ll[simp]: \<open>length (shorten_take_ll a j W) = length W\<close>
  by (auto simp: shorten_take_ll_def)

definition rewatch_heur_st_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
\<open>rewatch_heur_st_pre S \<longleftrightarrow> (\<forall>i < length (get_vdom S). get_vdom S ! i \<le> uint64_max)\<close>

lemma isasat_GC_clauses_wl_D_rewatch_pre:
  assumes
    \<open>length (get_clauses_wl_heur x) \<le> uint64_max\<close> and
    \<open>length (get_clauses_wl_heur xc) \<le> length (get_clauses_wl_heur x)\<close> and
    \<open>\<forall>i \<in> set (get_vdom xc). i \<le> length (get_clauses_wl_heur x)\<close>
  shows \<open>rewatch_heur_st_pre xc\<close>
  using assms
  unfolding rewatch_heur_st_pre_def all_set_conv_all_nth
  by auto

lemma li_uint32_maxdiv2_le_unit32_max: \<open>a \<le> uint32_max div 2 + 1 \<Longrightarrow> a \<le> uint32_max\<close>
  by (auto simp: uint32_max_def)
end
