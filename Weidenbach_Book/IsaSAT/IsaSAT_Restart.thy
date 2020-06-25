theory IsaSAT_Restart
  imports IsaSAT_Restart_Heuristics IsaSAT_CDCL
begin

chapter \<open>Full CDCL with Restarts\<close>

definition cdcl_twl_stgy_restart_abs_wl_heur_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 = (\<lambda>(brk, T, last_GC, last_Rephase).
    (\<exists>S\<^sub>0' T'. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
      cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0' (brk, T', last_GC, last_Rephase)))\<close>

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
        RETURN (brk, T, last_GC, last_Rephase, n)
      })
      (False, S\<^sub>0::twl_st_wl_heur, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0, 0);
    RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_wl_heur_cdcl_twl_stgy_restart_prog_wl_D:
  \<open>(cdcl_twl_stgy_restart_prog_wl_heur, cdcl_twl_stgy_restart_prog_wl) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_heur_def cdcl_twl_stgy_restart_prog_wl_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D2[THEN fref_to_Down_curry4]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D2[THEN fref_to_Down]
        cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D[THEN fref_to_Down]
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
    subgoal by auto
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
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0::twl_st_wl_heur, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0,  0);
    ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max \<and>
        get_old_arena T = []);
    if \<not>brk then do {
       T \<leftarrow> isasat_fast_slow T;
       (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0\<^esup>
	         (\<lambda>(brk, _). \<not>brk)
	         (\<lambda>(brk, S, last_GC, last_Restart, n).
	         do {
	           T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
	           (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
	           (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
	           RETURN (brk, T, last_GC, last_Restart, n)
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
	          RETURN (ebrk, brk, T, last_GC, last_Res, n)
	        })
          (ebrk, False, S\<^sub>0::nat twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0),
            size (get_all_learned_clss_wl S\<^sub>0),0);
      if \<not>brk then do {
        T \<leftarrow> RETURN T;
	(brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0\<^esup>
	  (\<lambda>(brk, _). \<not>brk)
	  (\<lambda>(brk, S, last_GC, last_Res, n).
	  do {
	    T \<leftarrow> unit_propagation_outer_loop_wl S;
	    (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
	    (T, last_GC, last_Res, n) \<leftarrow> restart_prog_wl T last_GC last_Res n brk;
	    RETURN (brk, T, last_GC, last_Res, n)
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
        (length (get_clauses_wl_heur x1e))\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)
  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''' r\<close>
    for x1e x1b r \<D>
    by (auto simp: twl_st_heur'_def)
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
        \<in> twl_st_heur''' (length (get_clauses_wl_heur x2k)) \<times>\<^sub>f
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
          (length (get_clauses_wl_heur x1g))\<close> and
      \<open>length (get_clauses_wl_heur T) \<le> uint64_max\<close> and
      \<open>length (get_clauses_wl_heur T) = length (get_clauses_wl_heur x1g)\<close> and
      \<open>(xb, x'a)
       \<in> bool_rel \<times>\<^sub>f
         twl_st_heur''''
          (length (get_clauses_wl_heur x1g) + 3 + 1 + uint32_max div 2)\<close> and
      \<open>x'a = (x1j, x2j)\<close> and
      \<open>xb = (x1k, x2k)\<close> and
      \<open>length (get_clauses_wl_heur x2k) \<le> uint64_max\<close>
    for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
      x2f x1g x2g x1h x2h x1i x2i T Ta xb x'a x1j x2j x1k x2k
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
    subgoal by auto
    subgoal by auto
    subgoal by (subst (asm)(2) twl_st_heur_def) force
    subgoal by auto
    subgoal by auto
    subgoal sorry
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    apply (rule twl_st_heur'''; assumption)
    apply (rule H'''; assumption?)
oops
    apply (rule H; assumption?)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: isasat_fast_slow_def)
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
  \<open>RETURN o isasat_fast = (\<lambda>(M, N, _). RETURN (length N \<le> sint64_max - (uint32_max div 2 + MAX_HEADER_SIZE + 1)))\<close>
  unfolding isasat_fast_def
  by (auto intro!:ext)

definition cdcl_twl_stgy_restart_prog_bounded_wl_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T \<and> n < uint64_max) \<and>
        (\<not>ebrk \<longrightarrow>length (get_clauses_wl_heur T) \<le> sint64_max)\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(length (get_clauses_wl_heur S) \<le> sint64_max);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(length (get_clauses_wl_heur T) \<le> sint64_max);
        ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S));
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(length (get_clauses_wl_heur T) \<le> sint64_max);
        (T, n) \<leftarrow> restart_prog_wl_D_heur T n brk;
	ebrk \<leftarrow> RETURN (\<not>(isasat_fast T \<and> n < uint64_max));
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0::twl_st_wl_heur, 0);
    RETURN (brk, T)
  }\<close>


lemma cdcl_twl_stgy_restart_prog_bounded_wl_heur_cdcl_twl_stgy_restart_prog_bounded_wl_D:
  assumes r: \<open>r \<le> uint64_max\<close>
  shows \<open>(cdcl_twl_stgy_restart_prog_bounded_wl_heur, cdcl_twl_stgy_restart_prog_bounded_wl) \<in>
   twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>r twl_st_heur\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_stgy_restart_prog_bounded_wl_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
	        (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
	        (\<lambda>(_, brk, S, n).
	        do {
	          T \<leftarrow> unit_propagation_outer_loop_wl S;
	          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
	          (T, n) \<leftarrow> restart_prog_wl T n brk;
	          ebrk \<leftarrow> RES UNIV;
	          RETURN (ebrk, brk, T, n)
	        })
	        (ebrk, False, S\<^sub>0::nat twl_st_wl, 0);
      RETURN (brk, T)
    }\<close> for S\<^sub>0
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_def nres_monad1 by auto
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
        (length (get_clauses_wl_heur x1e))\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)
  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''' r\<close>
    for x1e x1b r \<D>
    by (auto simp: twl_st_heur'_def)
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
  have abs_inv: \<open>(x, y) \<in> twl_st_heur''' r \<Longrightarrow>
    (ebrk, ebrka) \<in> {(b, b'). b = b' \<and> b = (\<not> isasat_fast x \<and> x2g < uint64_max)} \<Longrightarrow>
    (xb, x'a) \<in> bool_rel \<times>\<^sub>f (twl_st_heur \<times>\<^sub>f nat_rel) \<Longrightarrow>
    case x'a of
    (brk, xa, xb) \<Rightarrow>
      cdcl_twl_stgy_restart_abs_wl_inv y brk xa xb \<Longrightarrow>
    x2f = (x1g, x2g) \<Longrightarrow>
    xb = (x1f, x2f) \<Longrightarrow>
    cdcl_twl_stgy_restart_abs_wl_heur_inv x x1f x1g x2g\<close>
   for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
       x1e x2e T Ta xb x'a x1f x2f x1g x2g
    unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def
    apply (rule_tac x=y in exI)
    by fastforce
  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp]
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def
      cdcl_twl_stgy_restart_prog_bounded_wl_alt_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry2]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>{((ebrk, brk, T,n), (ebrk', brk', T', n')).
	    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur \<and> n = n' \<and>
	      (\<not>ebrk \<longrightarrow> isasat_fast T \<and> n < uint64_max) \<and>
              (\<not>ebrk \<longrightarrow> length (get_clauses_wl_heur T) \<le> sint64_max)}\<close>])
    subgoal using r by (auto simp: sint64_max_def isasat_fast_def uint32_max_def)
    subgoal
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: sint64_max_def isasat_fast_def uint32_max_def)
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by auto
    subgoal by auto
    apply (rule twl_st_heur'''; assumption)
    subgoal by (auto simp: isasat_fast_def uint64_max_def uint32_max_def sint64_max_def)
    apply (rule H; assumption?)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end