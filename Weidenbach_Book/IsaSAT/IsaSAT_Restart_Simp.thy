theory IsaSAT_Restart_Simp
  imports IsaSAT_Restart_Heuristics IsaSAT_Other IsaSAT_Propagate_Conflict IsaSAT_Restart_Inprocessing
begin

chapter \<open>Full CDCL with Restarts\<close>

definition cdcl_twl_stgy_restart_abs_wl_heur_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 = (\<lambda>(brk, T, last_GC, last_Rephase).
    (\<exists>S\<^sub>0' T'. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
      cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0' (brk, T', last_GC, last_Rephase)))\<close>

(*TODO FIX rephasing probably does not work after GC*)
definition update_all_phases :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur) nres\<close> where
  \<open>update_all_phases = (\<lambda>S. do {
     let lcount = get_global_conflict_count S;
     end_of_restart_phase \<leftarrow> RETURN (end_of_restart_phase_st S);
     S \<leftarrow> (if end_of_restart_phase > lcount then RETURN S else update_restart_phases S);
     S \<leftarrow> (if end_of_rephasing_phase_st S > lcount then RETURN S else rephase_heur_st S);
     RETURN S
  })\<close>

definition cdcl_twl_stgy_restart_prog_wl_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_wl_heur S\<^sub>0 = do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, last_GC, last_Rephase, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        (T, last_GC, last_Rephase, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Rephase n brk;
        RETURN (brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Rephase, n)
      })
      (False, S\<^sub>0::twl_st_wl_heur, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0, 0);
    RETURN T
  }\<close>

fun Pair4 :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd\<close> where
  \<open>Pair4 a b c d = (a, b, c, d)\<close>

lemma update_all_phases_Pair:
  \<open>(update_all_phases, (RETURN o id)) \<in>
  twl_st_heur''''uu r  u  \<rightarrow>\<^sub>f \<langle>twl_st_heur''''uu r u\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>(S, S') \<in> twl_st_heur''''uu r u \<Longrightarrow> update_restart_phases S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur''''uu r u)\<close>
    for S :: twl_st_wl_heur and S' :: \<open>nat twl_st_wl\<close>
    unfolding update_all_phases_def update_restart_phases_def
    by (auto simp: twl_st_heur'_def twl_st_heur_def learned_clss_count_def
        intro!: rephase_heur_st_spec[THEN order_trans]
        simp del: incr_restart_phase_end.simps incr_restart_phase.simps)
  have [refine0]: \<open>(S, S') \<in> twl_st_heur''''uu r u \<Longrightarrow> rephase_heur_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur''''uu r u)\<close>
    for S :: twl_st_wl_heur and S' :: \<open>nat twl_st_wl\<close>
    unfolding update_all_phases_def rephase_heur_st_def
    apply (cases S')
    apply (refine_vcg rephase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
    apply (clarsimp simp: twl_st_heur'_def twl_st_heur_def learned_clss_count_def)
    apply (simp add: learned_clss_count_def)
    apply (clarsimp simp add: twl_st_heur_def learned_clss_count_def)
    done

  show ?thesis
    supply[[goals_limit=1]]
    unfolding update_all_phases_def
    apply (subst (1) bind_to_let_conv)
    apply (subst (1) Let_def)
    apply (subst (1) Let_def)
    apply (intro frefI nres_relI)
    apply (case_tac x rule:prod.exhaust)
    apply (simp only: uncurry_def prod.case comp_def)
    apply refine_vcg
    subgoal by simp
    apply assumption
    subgoal by simp
    apply assumption
    subgoal by simp
    apply assumption
    subgoal by simp
    done
qed


lemma cdcl_twl_stgy_restart_prog_wl_heur_cdcl_twl_stgy_restart_prog_wl_D:
  \<open>(cdcl_twl_stgy_restart_prog_wl_heur, cdcl_twl_stgy_restart_prog_wl) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>(x1e, x1a) \<in> twl_st_heur \<Longrightarrow> (x1e, x1a)
       \<in> {(S, T).
          (S, T) \<in> twl_st_heur \<and>
          get_learned_count S = get_learned_count x1e}\<close> for x1e x1a
    by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_heur_def cdcl_twl_stgy_restart_prog_wl_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D2[THEN fref_to_Down_curry4]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D2[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r twl_st_heur \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>])
    subgoal by (auto simp: learned_clss_count_twl_st_heur)
    subgoal for x y xa x'
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod_rel_fst_snd_iff case_prod_beta
      apply (rule_tac x = \<open>y\<close>  in exI)
      apply (rule_tac x = \<open>fst (snd x')\<close>  in exI)
      apply (cases x')
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding get_conflict_wl_is_None
      by (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    subgoal by auto
    done
qed

definition fast_number_of_iterations :: \<open>_ \<Rightarrow> bool\<close> where
\<open>fast_number_of_iterations n \<longleftrightarrow> n < uint64_max >> 1\<close>

definition isasat_fast_slow :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
   [simp]: \<open>isasat_fast_slow S = RETURN S\<close>

definition cdcl_twl_stgy_restart_prog_early_wl_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, last_GC, last_Restart, n).
       cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 (brk, T, last_GC, last_Restart, n) \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T) \<and> length (get_clauses_wl_heur T) \<le> uint64_max\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(length (get_clauses_wl_heur S) \<le> uint64_max);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max);
        ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S));
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max);
        (T, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
	ebrk \<leftarrow> RETURN (\<not>isasat_fast T);
        RETURN (ebrk, brk \<or> \<not>get_conflict_wl_is_None_heur T, T, n)
      })
      (ebrk, False, S\<^sub>0::twl_st_wl_heur, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0,  0);
    ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max \<and>
        get_old_arena T = []);
    if \<not>brk then do {
       T \<leftarrow> isasat_fast_slow T;
       (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_heur_inv T\<^esup>
	         (\<lambda>(brk, _). \<not>brk)
	         (\<lambda>(brk, S, last_GC, last_Restart, n).
	         do {
	           T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
	           (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
	           (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
	           RETURN (brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Restart, n)
	         })
	         (False, T, n);
       RETURN T
    }
    else isasat_fast_slow T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_wl_heur_cdcl_twl_stgy_restart_prog_early_wl_D:
  assumes r: \<open>r \<le> uint64_max\<close>
  shows \<open>(cdcl_twl_stgy_restart_prog_early_wl_heur, cdcl_twl_stgy_restart_prog_early_wl) \<in>
   twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
thm cdcl_twl_stgy_restart_prog_early_wl_def
  have cdcl_twl_stgy_restart_prog_early_wl_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_early_wl S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, last_GC, last_Res, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 o snd\<^esup>
	        (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
	        (\<lambda>(_, brk, S, last_GC, last_Res, n).
	        do {
	          T \<leftarrow> unit_propagation_outer_loop_wl S;
	          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
	          (T, last_GC, last_Res, n) \<leftarrow> restart_prog_wl T last_GC last_Res n brk;
	          ebrk \<leftarrow> RES UNIV;
	          RETURN (ebrk, brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Res, n)
	        })
          (ebrk, False, S\<^sub>0::nat twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0),
            size (get_all_learned_clss_wl S\<^sub>0),0);
      if \<not>brk then do {
        T \<leftarrow> RETURN T;
	(brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv T\<^esup>
	  (\<lambda>(brk, _). \<not>brk)
	  (\<lambda>(brk, S, last_GC, last_Res, n).
	  do {
	    T \<leftarrow> unit_propagation_outer_loop_wl S;
	    (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
	    (T, last_GC, last_Res, n) \<leftarrow> restart_prog_wl T last_GC last_Res n brk;
	    RETURN (brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Res, n)
	  })
	  (False, T::nat twl_st_wl, last_GC, last_Res, n);
	RETURN T
      }
      else RETURN T
    }\<close> for S\<^sub>0
      unfolding cdcl_twl_stgy_restart_prog_early_wl_def nres_monad1
      by (auto intro!: bind_cong)
  have [refine0]: \<open>RETURN (\<not>isasat_fast x) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (\<not>isasat_fast x))} (RES UNIV)\<close>
    for x
    by (auto intro: RETURN_RES_refine)
  have [refine0]: \<open>isasat_fast_slow x1e
      \<le> \<Down> {(S, S'). S = x1e \<and> S' = x1b}
	   (RETURN x1b)\<close>
    for x1e x1b
  proof -
    show ?thesis
      unfolding isasat_fast_slow_def by auto
  qed
  have twl_st_heur'': \<open>(x1e, x1b) \<in> twl_st_heur \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''
        (dom_m (get_clauses_wl x1b))
        (length (get_clauses_wl_heur x1e))
        (get_learned_count x1e)\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)
  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r lcount \<Longrightarrow>
    (x1e, x1b)
    \<in> {(S, Taa).
          (S, Taa) \<in> twl_st_heur \<and>
          length (get_clauses_wl_heur S) = r \<and>
          learned_clss_count S = clss_size_allcount lcount}\<close>
    for x1e x1b r \<D> lcount
    by (auto simp: twl_st_heur'_def clss_size_allcount_def learned_clss_count_def clss_size_lcountU0_def
      clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def split: prod.splits)
  have H: \<open>(xb, x'a)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur'''' (length (get_clauses_wl_heur x1e) + MAX_HEADER_SIZE+1 + uint32_max div 2) \<Longrightarrow>
    x'a = (x1f, x2f) \<Longrightarrow>
    xb = (x1g, x2g) \<Longrightarrow>
    (x1g, x1f) \<in> bool_rel \<Longrightarrow>
    (x2e, x2b) \<in> nat_rel \<Longrightarrow>
    (((x2g, x2e), x1g), (x2f, x2b), x1f)
    \<in> twl_st_heur''' (length (get_clauses_wl_heur x2g)) \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      bool_rel\<close> for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e T Ta xb
       x'a x1f x2f x1g x2g
    by auto
  (* have abs_inv: \<open>(x, y) \<in> twl_st_heur''' r \<Longrightarrow>
   *   (ebrk, ebrka) \<in> {(b, b'). b = b' \<and> b = (\<not> isasat_fast x)} \<Longrightarrow>
   *   (xb, x'a) \<in> bool_rel \<times>\<^sub>f (twl_st_heur \<times>\<^sub>f nat_rel) \<Longrightarrow>
   *   case x'a of
   *   (brk, xa, xb) \<Rightarrow>
   *     cdcl_twl_stgy_restart_abs_wl_inv y brk xa xb \<Longrightarrow>
   *   x2f = (x1g, x2g) \<Longrightarrow>
   *   xb = (x1f, x2f) \<Longrightarrow>
   *   cdcl_twl_stgy_restart_abs_wl_heur_inv x x1f x1g x2g\<close>
   *  for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
   *      x1e x2e T Ta xb x'a x1f x2f x1g x2g
   *   unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fastforce *)
  have H''': \<open>(((((x2k, x1h), x1i), x2i), x1k), (((x2j, x1c), x1d), x2d), x1j)
        \<in> twl_st_heur''''u (length (get_clauses_wl_heur x2k)) (learned_clss_count x2k) \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          bool_rel\<close>
    if 
      \<open>(x, y) \<in> twl_st_heur''' r\<close> and
      \<open>(ebrk, ebrka) \<in> {(b, b'). b = b' \<and> b = (\<not> isasat_fast x)}\<close> and
      \<open>ebrka \<in> UNIV\<close> and
      \<open>(xa, x')
       \<in> {((ebrk, brk, T, last_GC, last_Rephase, n), ebrk', brk', T',
          last_GC', last_Rephase', n').
          ebrk = ebrk' \<and>
          brk = brk' \<and>
          (T, T') \<in> twl_st_heur \<and>
          n = n' \<and>
          last_GC' = last_GC \<and>
          last_Rephase' = last_Rephase \<and>
          (\<not> ebrk \<longrightarrow> isasat_fast T) \<and>
          length (get_clauses_wl_heur T) \<le> uint64_max}\<close> and
      \<open>(cdcl_twl_stgy_restart_abs_wl_inv y \<circ> snd) x'\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x2g = (x1h, x2h)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>xa = (x1e, x2e)\<close> and
      \<open>\<not> x1f \<and> \<not> x1e\<close> and
      \<open>length (get_clauses_wl_heur x1g) \<le> uint64_max\<close> and
      \<open>(T, Ta)
       \<in> twl_st_heur'' (dom_m (get_clauses_wl x1b))
          (length (get_clauses_wl_heur x1g)) lcount\<close> and
      \<open>length (get_clauses_wl_heur T) \<le> uint64_max\<close> and
      \<open>length (get_clauses_wl_heur T) = length (get_clauses_wl_heur x1g)\<close> and
      \<open>(xb, x'a)
       \<in> bool_rel \<times>\<^sub>f
         twl_st_heur''''uu
          (length (get_clauses_wl_heur x1g) + 3 + 1 + uint32_max div 2)
          lcount'\<close> and
      \<open>x'a = (x1j, x2j)\<close> and
      \<open>xb = (x1k, x2k)\<close> and
      \<open>length (get_clauses_wl_heur x2k) \<le> uint64_max\<close>
    for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
      x2f x1g x2g x1h x2h x1i x2i T Ta xb x'a x1j x2j x1k x2k lcount lcount'
    using that by auto

  have H4: \<open>(((((x2q, x1n), x1o), x2o), x1q), (((x2p, x1j), x1k), x2k), x1p)
        \<in> twl_st_heur''''u (length (get_clauses_wl_heur x2q)) (learned_clss_count x2q) \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          bool_rel\<close>
    if
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>xa = (x1e, x2e)\<close> and
      \<open>(xb, x'a)
       \<in> bool_rel \<times>\<^sub>f (twl_st_heur \<times>\<^sub>f (nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f nat_rel)))\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x2i = (x1j, x2j)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x'a = (x1h, x2h)\<close> and
      \<open>x2n = (x1o, x2o)\<close> and
      \<open>x2m = (x1n, x2n)\<close> and
      \<open>x2l = (x1m, x2m)\<close> and
      \<open>xb = (x1l, x2l)\<close> and
      \<open>(xc, x'b)
       \<in> bool_rel \<times>\<^sub>f
         twl_st_heur''''uu
          (length (get_clauses_wl_heur x1m) + 3 + 1 + uint32_max div 2)
          (Suc (clss_size_allcount (get_learned_count x1m)))\<close> and
      \<open>x'b = (x1p, x2p)\<close> and
      \<open>xc = (x1q, x2q)\<close>
      for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
         x1g x2g T Ta xb x'a x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n
        x2n x1o x2o Tb Tc xc x'b x1p x2p x1q x2q
      using that by auto

  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp] learned_clss_count_twl_st_heur[simp]
    unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def
      cdcl_twl_stgy_restart_prog_early_wl_alt_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry4]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r twl_st_heur \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
      WHILEIT_refine[where R = \<open>{((ebrk, brk, T, last_GC, last_Rephase, n),
         (ebrk', brk', T', last_GC', last_Rephase', n')).
	    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur \<and> n = n' \<and>
              last_GC' = last_GC \<and>  last_Rephase' = last_Rephase \<and>
	      (\<not>ebrk \<longrightarrow> isasat_fast T) \<and> length (get_clauses_wl_heur T) \<le> uint64_max}\<close>])
    subgoal using r by auto
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod.case prod_rel_fst_snd_iff
      apply (rule_tac x=y in exI)
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close> in exI)
      apply (case_tac xa; case_tac x')
      by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by auto
    subgoal by auto
    apply (rule twl_st_heur'''; assumption)
    subgoal by (auto simp: isasat_fast_def uint64_max_def sint64_max_def uint32_max_def)
    apply (rule H'''; assumption)
    subgoal unfolding get_conflict_wl_is_None
      by (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    subgoal by auto
    subgoal by (subst (asm)(2) twl_st_heur_def) force
    subgoal by auto
    subgoal by auto
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
      x2f x1g x2g T Ta xb x'a
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod.case prod_rel_fst_snd_iff
        case_prod_beta
      apply (rule_tac x= \<open>x1b\<close> in exI)
      apply (rule_tac x= \<open>fst (snd x'a)\<close> in exI)
      apply (case_tac xb; case_tac x'a)
      by simp
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    apply (rule twl_st_heur'''; assumption)
    apply (rule H4; assumption)
    subgoal unfolding get_conflict_wl_is_None
      by (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    subgoal by auto
    subgoal by auto
    done
qed

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
     intro!: valid_arena_mark_unused
     dest!: in_set_butlastD in_vdom_m_fmdropD
     elim!: in_set_upd_cases)
  done

lemma mark_to_delete_clauses_wl_D_heur_is_Some_iff:
  \<open>D = Some C \<longleftrightarrow> D \<noteq> None \<and> ((the D) = C)\<close>
  by auto

lemma (in -) isasat_fast_alt_def:
  \<open>RETURN o isasat_fast = (\<lambda>(M, N, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). RETURN (length N \<le> sint64_max - (uint32_max div 2 + MAX_HEADER_SIZE + 1) \<and>
     clss_size_allcount lcount < uint64_max))\<close>
  unfolding isasat_fast_def
  by (auto intro!: ext simp: learned_clss_count_def clss_size_allcount_def clss_size_lcount_def
    clss_size_lcountUS_def clss_size_lcountUE_def clss_size_lcountU0_def)

definition isasat_fast_relaxed :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast_relaxed S \<longleftrightarrow> length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max\<close>

definition isasat_fast_relaxed2 :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isasat_fast_relaxed2 S n  \<longleftrightarrow> isasat_fast_relaxed S \<and> n < uint64_max\<close>

definition cdcl_twl_stgy_restart_prog_bounded_wl_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, last_GC, last_Restart, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 (brk, T, last_GC, last_Restart, n) \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T \<and> n < uint64_max) \<and>
        (\<not>ebrk \<longrightarrow>length (get_clauses_wl_heur T) \<le> sint64_max)\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(isasat_fast S);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(isasat_fast T);
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(isasat_fast_relaxed2 T n);
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
        T \<leftarrow> update_all_phases T;
        ASSERT(isasat_fast_relaxed T);
	ebrk \<leftarrow> RETURN (\<not>(isasat_fast T \<and> n < uint64_max));
        RETURN (ebrk, brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0::twl_st_wl_heur, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0, 0);
    RETURN (ebrk, T)
  }\<close>

(*TODO Move*)
lemma all_count_learned[simp]: \<open>clss_size_allcount (get_learned_count S) = learned_clss_count S\<close>
    by (auto simp: twl_st_heur'_def clss_size_allcount_def learned_clss_count_def clss_size_lcountU0_def
      clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def split: prod.splits)

lemma cdcl_twl_stgy_restart_prog_bounded_wl_heur_cdcl_twl_stgy_restart_prog_bounded_wl_D:
  assumes r: \<open>r \<le> uint64_max\<close>
  shows \<open>(cdcl_twl_stgy_restart_prog_bounded_wl_heur, cdcl_twl_stgy_restart_prog_bounded_wl) \<in>
   twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>r twl_st_heur\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_stgy_restart_prog_bounded_wl_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 o snd\<^esup>
	        (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
	        (\<lambda>(_, brk, S, last_GC, last_Restart,n).
                do {
                  ASSERT (\<not> brk);
	          T \<leftarrow> unit_propagation_outer_loop_wl S;
	          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
	          (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl T last_GC last_Restart n brk;
                  T \<leftarrow> RETURN (id T);
	          ebrk \<leftarrow> RES UNIV;
	          RETURN (ebrk, brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Restart, n)
	        })
	        (ebrk, False, S\<^sub>0::nat twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0),
                    size (get_all_learned_clss_wl S\<^sub>0), 0);
      RETURN (ebrk, T)
    }\<close> for S\<^sub>0
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_def nres_monad1 Let_def
    by (auto intro!: bind_cong[OF refl])

  have [refine0]: \<open>RETURN (\<not>(isasat_fast x \<and> n < uint64_max)) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (\<not>(isasat_fast x \<and> n < uint64_max)))} (RES UNIV)\<close>
       \<open>RETURN (\<not>isasat_fast x) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (\<not>(isasat_fast x \<and> 0 < uint64_max)))} (RES UNIV)\<close>
    for x n
    by (auto intro: RETURN_RES_refine simp: uint64_max_def)
  have [refine0]: \<open>isasat_fast_slow x1e
      \<le> \<Down> {(S, S'). S = x1e \<and> S' = x1b}
	   (RETURN x1b)\<close>
    for x1e x1b
  proof -
    show ?thesis
      unfolding isasat_fast_slow_def by auto
  qed
  have twl_st_heur'': \<open>(x1e, x1b) \<in> twl_st_heur \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''
        (dom_m (get_clauses_wl x1b))
        (length (get_clauses_wl_heur x1e))
         (get_learned_count x1e)\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)

  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r lcount \<Longrightarrow>
    (x1e, x1b)
    \<in> {(S, Taa).
          (S, Taa) \<in> twl_st_heur \<and>
          length (get_clauses_wl_heur S) = r \<and>
          learned_clss_count S = clss_size_allcount lcount}\<close>
    for x1e x1b r \<D> lcount
    by (auto simp: twl_st_heur'_def clss_size_allcount_def learned_clss_count_def clss_size_lcountU0_def
      clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def split: prod.splits)
  have H: \<open>(xb, x'a)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur'''' (length (get_clauses_wl_heur x1e) + MAX_HEADER_SIZE+1 + uint32_max div 2) \<Longrightarrow>
    x'a = (x1f, x2f) \<Longrightarrow>
    xb = (x1g, x2g) \<Longrightarrow>
    (x1g, x1f) \<in> bool_rel \<Longrightarrow>
    (x2e, x2b) \<in> nat_rel \<Longrightarrow>
    (((x2g, x2e), x1g), (x2f, x2b), x1f)
    \<in> twl_st_heur''' (length (get_clauses_wl_heur x2g)) \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      bool_rel\<close> for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e T Ta xb
       x'a x1f x2f x1g x2g
    by auto
  let ?R = \<open>{((ebrk, brk, T, last_GC, last_Rephase, n), ebrk', brk', T',
          last_GC', last_Rephase', n').
          ebrk = ebrk' \<and>
          brk = brk' \<and>
          (T, T') \<in> twl_st_heur \<and>
          n = n' \<and>
          last_GC' = last_GC \<and>
          last_Rephase' = last_Rephase \<and>
          (\<not> ebrk \<longrightarrow> isasat_fast T \<and> n < uint64_max) \<and>
          length (get_clauses_wl_heur T) \<le> uint64_max}\<close>
 have H''': \<open>(((((x2k, x1h), x1i), x2i), x1k), (((x2j, x1c), x1d), x2d), x1j)
        \<in> twl_st_heur''' (length (get_clauses_wl_heur x2k)) \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          bool_rel\<close>
    if
      \<open>(xa, x') \<in> ?R\<close> and
      \<open>(cdcl_twl_stgy_restart_abs_wl_inv y \<circ> snd) x'\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x2g = (x1h, x2h)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>xa = (x1e, x2e)\<close> and
      \<open>(xb, x'a)
       \<in> bool_rel \<times>\<^sub>f
         twl_st_heur''''
          (length (get_clauses_wl_heur x1g) + 3 + 1 + uint32_max div 2)\<close> and
      \<open>x'a = (x1j, x2j)\<close> and
      \<open>xb = (x1k, x2k)\<close>
    for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
      x2f x1g x2g x1h x2h x1i x2i T Ta xb x'a x1j x2j x1k x2k
    using that by auto
  have H4: \<open>(((((x2q, x1n), x1o), x2o), x1q), (((x2p, x1j), x1k), x2k), x1p)
        \<in> twl_st_heur''' (length (get_clauses_wl_heur x2q)) \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          bool_rel\<close>
    if 
      \<open>(xb, x'a)
       \<in> bool_rel \<times>\<^sub>f
         (twl_st_heur \<times>\<^sub>f (nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f nat_rel)))\<close> and
      \<open>case xb of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
      \<open>case x'a of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
      \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv x xb\<close> and
      \<open>cdcl_twl_stgy_restart_abs_wl_inv y x'a\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x2i = (x1j, x2j)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x'a = (x1h, x2h)\<close> and
      \<open>x2n = (x1o, x2o)\<close> and
      \<open>x2m = (x1n, x2n)\<close> and
      \<open>x2l = (x1m, x2m)\<close> and
      \<open>xb = (x1l, x2l)\<close> and
      \<open>(Tb, Tc)
       \<in> twl_st_heur'' (dom_m (get_clauses_wl x1i))
          (length (get_clauses_wl_heur x1m)) lcount\<close> and
      \<open>(xc, x'b)
       \<in> bool_rel \<times>\<^sub>f
         twl_st_heur''''
          (length (get_clauses_wl_heur x1m) + 3 + 1 + uint32_max div 2)\<close> and
      \<open>x'b = (x1p, x2p)\<close> and
      \<open>xc = (x1q, x2q)\<close>
    for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
       x2f x1g x2g T Ta xb x'a x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m
       x2m x1n x2n x1o x2o Tb Tc xc x'b x1p x2p x1q x2q lcount
    using that by auto
  have H4: \<open>(((((x2k, x1h), x1i), x2i), x1k), (((x2j, x1c), x1d), x2d), x1j)
        \<in> twl_st_heur''''u (length (get_clauses_wl_heur x2k)) (learned_clss_count x2k)  \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          nat_rel \<times>\<^sub>f
          bool_rel\<close>
    if
      \<open>(x, y) \<in> twl_st_heur''' r\<close> and
      \<open>(ebrk, ebrka)
       \<in> {(b, b'). b = b' \<and> b = (\<not> (isasat_fast x \<and> 0 < uint64_max))}\<close> and
      \<open>ebrka \<in> UNIV\<close> and
      \<open>(xa, x')
       \<in> {((ebrk, brk, T, last_GC, last_Rephase, n), ebrk', brk', T', last_GC',
          last_Rephase', n').
          ebrk = ebrk' \<and>
          brk = brk' \<and>
          (T, T') \<in> twl_st_heur \<and>
          n = n' \<and>
          last_GC' = last_GC \<and>
          last_Rephase' = last_Rephase \<and>
          (\<not> ebrk \<longrightarrow> isasat_fast T \<and> n < uint64_max) \<and>
          length (get_clauses_wl_heur T) \<le> uint64_max}\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x2g = (x1h, x2h)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>xa = (x1e, x2e)\<close> and
      \<open>\<not> x1f \<and> \<not> x1e\<close> and
      \<open>(xb, x'a)
       \<in> bool_rel \<times>\<^sub>f
         twl_st_heur''''uu
          (length (get_clauses_wl_heur x1g) + 3 + 1 + uint32_max div 2)
          (Suc (clss_size_allcount (get_learned_count x1g)))\<close> and
      \<open>x'a = (x1j, x2j)\<close> and
      \<open>xb = (x1k, x2k)\<close>
    for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
          x1g x2g x1h x2h x1i x2i T Ta xb x'a x1j x2j x1k x2k
      using that by auto
    have H5:
      \<open>       (xc, x'b)
       \<in> twl_st_heur''''uu r u \<times>\<^sub>f
         (nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f nat_rel)) \<Longrightarrow>
       x'b = (x1l, x2l) \<Longrightarrow>
       xc = (x1o, x2o) \<Longrightarrow>
       (x1o, x1l)
       \<in> twl_st_heur''''uu r u
      \<close> for xc x'b u r x1o x1l x2o x2l
      by auto
  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp] learned_clss_count_twl_st_heur[simp]
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def
      cdcl_twl_stgy_restart_prog_bounded_wl_alt_def
    apply (intro frefI nres_relI)

    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry4]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        update_all_phases_Pair[THEN fref_to_Down, unfolded comp_def]
        WHILEIT_refine[where R = \<open>?R\<close>])
    subgoal using r by (auto simp: sint64_max_def isasat_fast_def uint32_max_def)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod.case prod_rel_fst_snd_iff
      apply (rule_tac x=y in exI)
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close> in exI)
      apply (case_tac xa; case_tac x')
      by simp
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: sint64_max_def isasat_fast_def uint32_max_def)
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by (auto dest: get_learned_count_learned_clss_countD simp: isasat_fast_def)
    apply (rule twl_st_heur'''; assumption)
    subgoal by (auto simp: isasat_fast_def uint64_max_def uint32_max_def sint64_max_def
      isasat_fast_relaxed_def isasat_fast_relaxed2_def)
    apply (rule H4; assumption)
    apply (rule H5; assumption)
    subgoal
      by (auto simp: isasat_fast_def uint64_max_def uint32_max_def sint64_max_def
        isasat_fast_relaxed_def)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i T Ta xb x'a x1j x2j x1k x2k xc x'b x1l x2l
       x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q Tb Tc ebrkb ebrkc
      unfolding get_conflict_wl_is_None (*auto with the simp rules also works, but takes forever*)
      apply (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id, of _ Tc])
        apply fast
      by (auto simp: isasat_fast_def uint64_max_def uint32_max_def sint64_max_def)
    subgoal by auto
    done
qed

end