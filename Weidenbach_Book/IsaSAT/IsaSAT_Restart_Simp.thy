theory IsaSAT_Restart_Simp
  imports IsaSAT_Restart_Heuristics IsaSAT_Other IsaSAT_Propagate_Conflict IsaSAT_Restart_Inprocessing
    IsaSAT_Restart_Simp_Defs
begin

fun Pair4 :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd\<close> where
  \<open>Pair4 a b c d = (a, b, c, d)\<close>

lemma rephase_heur_st_spec:
  \<open>(S, S') \<in> twl_st_heur_loop \<Longrightarrow> rephase_heur_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur_loop)\<close>
  unfolding rephase_heur_st_def
  apply (cases S')
  apply (refine_vcg rephase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_loop_def all_atms_st_def)
  done

lemma update_all_phases_Pair:
  \<open>(S, S') \<in> twl_st_heur_loop''''uu r u\<Longrightarrow>
     update_all_phases S \<le> \<Down> ({(T, T'). (T,T')\<in>twl_st_heur_loop''''uu r u \<and> T' = S'}) (RETURN (id S'))\<close>
proof -
  have [refine0]: \<open>(S, S') \<in> twl_st_heur_loop''''uu r u \<Longrightarrow> count_decided (get_trail_wl S') = 0 \<Longrightarrow>
    update_restart_mode S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur_loop''''uu r u)\<close>
    for S :: isasat and S' :: \<open>nat twl_st_wl\<close>
    unfolding update_all_phases_def update_restart_mode_def Let_def
    by (auto simp: twl_st_heur'_def twl_st_heur_loop_def learned_clss_count_def
        intro!: rephase_heur_st_spec[THEN order_trans] switch_bump_heur
        simp del: incr_restart_phase_end_stats.simps incr_restart_phase_stats.simps)
  have [refine0]: \<open>(S, S') \<in> twl_st_heur_loop''''uu r u \<Longrightarrow> rephase_heur_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur_loop''''uu r u)\<close>
    for S :: isasat and S' :: \<open>nat twl_st_wl\<close>
    unfolding update_all_phases_def rephase_heur_st_def
    apply (cases S')
    apply (refine_vcg rephase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
    apply (clarsimp simp: twl_st_heur'_def twl_st_heur_loop_def learned_clss_count_def)
    apply (simp add: learned_clss_count_def)
    apply (clarsimp simp add: twl_st_heur_loop_def learned_clss_count_def)
    done

   show \<open>(S, S') \<in> twl_st_heur_loop''''uu r u\<Longrightarrow>
     update_all_phases S \<le> \<Down> ({(T, T'). (T,T')\<in>twl_st_heur_loop''''uu r u \<and> T' = S'}) (RETURN (id S'))\<close> for S S'
    unfolding update_all_phases_def
    apply (subst (1) bind_to_let_conv)
    apply (subst (1) Let_def)
    apply (subst (1) Let_def)
    apply refine_vcg
    apply assumption
    subgoal 
      using count_decided_trail_ref[THEN fref_to_Down_unRET_Id, of \<open>get_trail_wl_heur S\<close>
          \<open>get_trail_wl S'\<close> \<open>all_atms_st S'\<close>]
      by (simp add: count_decided_st_def twl_st_heur_loop_def count_decided_st_heur_def Let_def)
    apply assumption
    subgoal by simp
    subgoal by simp
    apply assumption
    subgoal by simp
    subgoal by simp
    subgoal by simp
    done
qed

lemma cdcl_twl_stgy_restart_abs_wl_inv_NoneD:
  \<open>cdcl_twl_stgy_restart_abs_wl_inv y (False, x1a, x1b, x1c, x2c) \<Longrightarrow>
  get_conflict_wl x1a = None\<close>
  unfolding cdcl_twl_stgy_restart_abs_wl_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
    prod.simps cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_prog_int_inv_def
  unfolding not_False_eq_True simp_thms
  apply normalize_goal+
  by simp

(*TODO Move*)
lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_loop \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_loop_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def
     split: option.splits)

lemma cdcl_twl_stgy_restart_prog_wl_heur_cdcl_twl_stgy_restart_prog_wl_D:
  \<open>(cdcl_twl_stgy_restart_prog_wl_heur, cdcl_twl_stgy_restart_prog_wl) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur_loop\<rangle>nres_rel\<close>
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
        WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r restart_prog_wl_heur_rel2\<close>])
    subgoal by (auto simp: learned_clss_count_twl_st_heur intro!: twl_st_heur_twl_st_heur_loopD)
    subgoal for x y xa x'
      using cdcl_twl_stgy_restart_abs_wl_inv_NoneD[of y \<open>fst (snd x')\<close>
        \<open>fst (snd (snd x'))\<close> \<open>fst (snd (snd (snd x')))\<close> \<open>snd (snd (snd (snd x')))\<close>] apply -
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod_rel_fst_snd_iff case_prod_beta
      apply (rule_tac x = \<open>y\<close>  in exI)
      apply (rule_tac x = \<open>fst (snd x')\<close>  in exI)
      apply (cases x', cases xa)
      by auto
    subgoal by auto
    subgoal
      by (rule twl_st_heur_loop_twl_st_heurD)
       (auto dest: cdcl_twl_stgy_restart_abs_wl_inv_NoneD)
    subgoal by auto
    subgoal by (auto dest!: cdcl_twl_stgy_restart_abs_wl_inv_NoneD)
    subgoal unfolding get_conflict_wl_is_None
      by (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    subgoal by auto
    done
qed

definition fast_number_of_iterations :: \<open>_ \<Rightarrow> bool\<close> where
\<open>fast_number_of_iterations n \<longleftrightarrow> n < unat64_max >> 1\<close>


definition convert_to_full_state_wl_heur :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  [simp]: \<open>convert_to_full_state_wl_heur S = RETURN S\<close>
definition convert_to_full_state_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  [simp]: \<open>convert_to_full_state_wl S = RETURN S\<close>

lemma convert_to_full_state_wl_heur:
  \<open>(S, T) \<in> twl_st_heur_loop \<Longrightarrow> get_conflict_wl T = None \<Longrightarrow>
  convert_to_full_state_wl_heur S \<le> \<Down>(twl_st_heur''
        (dom_m (get_clauses_wl T))
        (length (get_clauses_wl_heur S))
         (get_learned_count S)) (convert_to_full_state_wl T)\<close>
  by (auto intro!: nres_relI frefI twl_st_heur_loop_twl_st_heurD simp: twl_st_heur'_def)


lemma cdcl_twl_stgy_restart_prog_early_wl_heur_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_early_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, last_GC, last_Restart, n).
       cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 (brk, T, last_GC, last_Restart, n) \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T) \<and> length (get_clauses_wl_heur T) \<le> unat64_max\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(length (get_clauses_wl_heur S) \<le> unat64_max);
        S \<leftarrow> convert_to_full_state_wl_heur S;
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(length (get_clauses_wl_heur T) \<le> unat64_max);
        ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S));
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(length (get_clauses_wl_heur T) \<le> unat64_max);
        (T, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
	ebrk \<leftarrow> RETURN (\<not>isasat_fast T);
        RETURN (ebrk, brk \<or> \<not>get_conflict_wl_is_None_heur T, T, n)
      })
      (ebrk, False, S\<^sub>0::isasat, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0,  0);
    ASSERT(length (get_clauses_wl_heur T) \<le> unat64_max \<and>
        get_old_arena T = []);
    if \<not>brk then do {
       T \<leftarrow> isasat_fast_slow T;
       (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_heur_inv2 T\<^esup>
	         (\<lambda>(brk, _). \<not>brk)
	         (\<lambda>(brk, S, last_GC, last_Restart, n).
	         do {
                   S \<leftarrow> convert_to_full_state_wl_heur S;
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
    unfolding convert_to_full_state_wl_heur_def Let_def cdcl_twl_stgy_restart_prog_early_wl_heur_def
      bind_to_let_conv
   by auto

lemma cdcl_twl_stgy_restart_prog_early_wl_heur_cdcl_twl_stgy_restart_prog_early_wl_D:
  assumes r: \<open>r \<le> unat64_max\<close>
  shows \<open>(cdcl_twl_stgy_restart_prog_early_wl_heur, cdcl_twl_stgy_restart_prog_early_wl) \<in>
   twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>twl_st_heur_loop\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_stgy_restart_prog_early_wl_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_early_wl S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, last_GC, last_Res, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 o snd\<^esup>
	        (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
	        (\<lambda>(_, brk, S, last_GC, last_Res, n).
	        do {
                  S \<leftarrow> convert_to_full_state_wl S;
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
            S \<leftarrow> convert_to_full_state_wl S;
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
      unfolding cdcl_twl_stgy_restart_prog_early_wl_def nres_monad1 bind_to_let_conv
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

  let ?R = \<open>{((ebrk, brk, T, last_GC, last_Rephase, n),
         (ebrk', brk', T', last_GC', last_Rephase', n')).
    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur_loop \<and>
    (\<not>brk \<longrightarrow> (n = n' \<and> last_GC' = last_GC \<and>  last_Rephase' = last_Rephase)) \<and>
	      (\<not>ebrk \<longrightarrow> isasat_fast T) \<and> length (get_clauses_wl_heur T) \<le> unat64_max}\<close>
  let ?S = \<open>{((brk, T, last_GC, last_Rephase, n),
         (brk', T', last_GC', last_Rephase', n')).
     (brk = brk') \<and> (T, T')  \<in> twl_st_heur_loop \<and>
    (\<not>brk \<longrightarrow> (n = n' \<and> last_GC' = last_GC \<and>  last_Rephase' = last_Rephase))}\<close>
  have twl_st_heur'': \<open>(x1e, x1b) \<in> twl_st_heur_loop \<Longrightarrow> get_conflict_wl x1b = None \<Longrightarrow>
    (convert_to_full_state_wl_heur x1e) \<le>\<Down>
    (twl_st_heur''
        (dom_m (get_clauses_wl x1b))
        (length (get_clauses_wl_heur x1e))
        (get_learned_count x1e)) (convert_to_full_state_wl x1b)\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def intro!: nres_relI twl_st_heur_loop_twl_st_heurD)
  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r lcount \<Longrightarrow>
    (x1e, x1b)
    \<in> {(S, Taa).
          (S, Taa) \<in> twl_st_heur \<and>
          length (get_clauses_wl_heur S) = r \<and>
          learned_clss_count S = clss_size_allcount lcount}\<close>
    for x1e x1b r \<D> lcount
    by (auto simp: twl_st_heur'_def clss_size_allcount_def learned_clss_count_def clss_size_lcountU0_def
      clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def clss_size_lcountUEk_def
      split: prod.splits)
  have H: \<open>(xb, x'a)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur'''' (length (get_clauses_wl_heur x1e) + MAX_HEADER_SIZE+1 + unat32_max div 2) \<Longrightarrow>
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

  have H''':
    \<open>\<And>x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i S Sa T Ta
    xb x'a x1j x2j x1k x2k.
    (xa, x') \<in> ?R \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    x2a = (x1b, x2b) \<Longrightarrow>
    x2 = (x1a, x2a) \<Longrightarrow>
    x' = (x1, x2) \<Longrightarrow>
    x2h = (x1i, x2i) \<Longrightarrow>
    x2g = (x1h, x2h) \<Longrightarrow>
    x2f = (x1g, x2g) \<Longrightarrow>
    x2e = (x1f, x2f) \<Longrightarrow>
    xa = (x1e, x2e) \<Longrightarrow>
    \<not> x1f \<and> \<not> x1e \<Longrightarrow>
    length (get_clauses_wl_heur x1g) \<le> unat64_max \<Longrightarrow>
    (xb, x'a)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur''''uu (length (get_clauses_wl_heur x1g) + 3 + 1 + unat32_max div 2)
    (Suc (clss_size_allcount (get_learned_count x1g))) \<Longrightarrow>
    x'a = (x1j, x2j) \<Longrightarrow>
    xb = (x1k, x2k) \<Longrightarrow>
    (((((x2k, x1h), x1i), x2i), x1k), (((x2j, x1c), x1d), x2d), x1j)
    \<in> twl_st_heur''''u (length (get_clauses_wl_heur x2k))
      (Suc (clss_size_allcount (get_learned_count x1g))) \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel\<close>
    by simp

have H4: \<open>\<And>x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g T Ta xb x'a x1h x2h
    x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o S Sa Tb Tc xc x'b x1p x2p x1q x2q.
    (xb, x'a) \<in> ?S \<Longrightarrow>
    case xb of (brk, uu_) \<Rightarrow> \<not> brk \<Longrightarrow>
    case x'a of (brk, uu_) \<Rightarrow> \<not> brk \<Longrightarrow>
    cdcl_twl_stgy_restart_abs_wl_heur_inv2 T xb \<Longrightarrow>
    cdcl_twl_stgy_restart_abs_wl_inv Ta x'a \<Longrightarrow>
    x2j = (x1k, x2k) \<Longrightarrow>
    x2i = (x1j, x2j) \<Longrightarrow>
    x2h = (x1i, x2i) \<Longrightarrow>
    x'a = (x1h, x2h) \<Longrightarrow>
    x2n = (x1o, x2o) \<Longrightarrow>
    x2m = (x1n, x2n) \<Longrightarrow>
    x2l = (x1m, x2m) \<Longrightarrow>
    xb = (x1l, x2l) \<Longrightarrow>
    (S, Sa)
    \<in> twl_st_heur'' (dom_m (get_clauses_wl x1i)) (length (get_clauses_wl_heur x1m))
    (get_learned_count x1m) \<Longrightarrow>
    (Tb, Tc)
    \<in> twl_st_heur'' (dom_m (get_clauses_wl x1i)) (length (get_clauses_wl_heur x1m))
    (get_learned_count x1m) \<Longrightarrow>
    (xc, x'b)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur''''uu (length (get_clauses_wl_heur x1m) + 3 + 1 + unat32_max div 2)
    (Suc (clss_size_allcount (get_learned_count x1m))) \<Longrightarrow>
    x'b = (x1p, x2p) \<Longrightarrow>
    xc = (x1q, x2q) \<Longrightarrow>
    (((((x2q, x1n), x1o), x2o), x1q), (((x2p, x1j), x1k), x2k), x1p)
    \<in> twl_st_heur''''u (length (get_clauses_wl_heur x2q)) (learned_clss_count x2q)  \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      bool_rel\<close>
      by auto
 
  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp] learned_clss_count_twl_st_heur[simp]
    unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_alt_def
      cdcl_twl_stgy_restart_prog_early_wl_alt_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry4]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
      unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        WHILEIT_refine[where R = ?S]
      WHILEIT_refine[where R = \<open>?R\<close>])
    subgoal using r by (auto intro!: twl_st_heur_twl_st_heur_loopD)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      using cdcl_twl_stgy_restart_abs_wl_inv_NoneD[of y \<open>fst (snd (snd x'))\<close>
        \<open>fst (snd (snd (snd x')))\<close> \<open>fst (snd (snd (snd (snd x'))))\<close> \<open>snd (snd (snd (snd (snd x'))))\<close>] 
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod.case prod_rel_fst_snd_iff
      apply (rule_tac x=y in exI)
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close> in exI)
      apply (case_tac xa; case_tac x')
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
      apply (rule twl_st_heur''; auto dest!: cdcl_twl_stgy_restart_abs_wl_inv_NoneD; fail)
    apply assumption
    subgoal by auto
    subgoal by auto
    apply (rule twl_st_heur'''; assumption)
    subgoal by (auto simp: isasat_fast_def unat64_max_def snat64_max_def unat32_max_def)
    apply (rule H'''; assumption)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i S Sa
      T Ta xb x'a x1j x2j x1k x2k xc x'b x1l x2l x1m x2m x1n x2n x1o x2o ebrkb ebrkc
      unfolding get_conflict_wl_is_None
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id, of _ \<open>x1l\<close>])
         clarsimp_all
    subgoal by auto
    subgoal by (subst (asm)twl_st_heur_loop_def) force
    subgoal by auto
    subgoal by auto
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f
      x2f x1g x2g T Ta xb x'a
      using cdcl_twl_stgy_restart_abs_wl_inv_NoneD[of y \<open>fst (snd x'a)\<close>
        \<open>fst (snd (snd x'a))\<close> \<open>fst (snd (snd (snd x'a)))\<close> \<open>snd (snd (snd (snd x'a)))\<close>] 
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv2_def prod.case prod_rel_fst_snd_iff
        case_prod_beta
      apply (rule_tac x= \<open>x1b\<close> in exI)
      apply (rule_tac x= \<open>fst (snd x'a)\<close> in exI)
      apply (case_tac xb; case_tac x'a)
      by auto
    subgoal by auto
      apply (rule twl_st_heur'')
    subgoal by (auto dest!: cdcl_twl_stgy_restart_abs_wl_inv_NoneD)
    subgoal by (auto dest!: cdcl_twl_stgy_restart_abs_wl_inv_NoneD)
      apply assumption
    apply (rule twl_st_heur'''; assumption)
    apply (rule H4; assumption)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g T Ta xb x'a x1h x2h
    x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o S Sa Tb Tc xc x'b x1p x2p x1q x2q xd x'c x1r
      x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w
      unfolding get_conflict_wl_is_None
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id, of _ x1r])
       clarsimp_all
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

lemma cdcl_twl_stgy_restart_prog_bounded_wl_heur_alt_def:
    \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, last_GC, last_Restart, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 (brk, T, last_GC, last_Restart, n) \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T \<and> n < unat64_max) \<and>
        (\<not>ebrk \<longrightarrow>length (get_clauses_wl_heur T) \<le> snat64_max)\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(isasat_fast S);
        S \<leftarrow> convert_to_full_state_wl_heur S;
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(isasat_fast T);
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(isasat_fast_relaxed2 T n);
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
        T \<leftarrow> update_all_phases T;
        ASSERT(isasat_fast_relaxed T);
	ebrk \<leftarrow> RETURN (\<not>(isasat_fast T \<and> n < unat64_max));
        RETURN (ebrk, brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0::isasat, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0, 0);
    RETURN (ebrk, T)
  }\<close>
  unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def bind_to_let_conv Let_def
  convert_to_full_state_wl_heur_def by auto


lemma cdcl_twl_stgy_restart_prog_bounded_wl_heur_cdcl_twl_stgy_restart_prog_bounded_wl_D:
  assumes r: \<open>r \<le> unat64_max\<close>
  shows \<open>(cdcl_twl_stgy_restart_prog_bounded_wl_heur, cdcl_twl_stgy_restart_prog_bounded_wl) \<in>
   twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>r twl_st_heur_loop\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_stgy_restart_prog_bounded_wl_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 o snd\<^esup>
	        (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
	        (\<lambda>(_, brk, S, last_GC, last_Restart,n).
                do {
                  ASSERT (\<not> brk);
                  S \<leftarrow> convert_to_full_state_wl S;
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
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_def nres_monad1 Let_def bind_to_let_conv
  convert_to_full_state_wl_def
    by (auto intro!: bind_cong[OF refl])

  have [refine0]: \<open>RETURN (\<not>(isasat_fast x \<and> n < unat64_max)) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (\<not>(isasat_fast x \<and> n < unat64_max)))} (RES UNIV)\<close>
       \<open>RETURN (\<not>isasat_fast x) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (\<not>(isasat_fast x \<and> 0 < unat64_max)))} (RES UNIV)\<close>
    for x n
    by (auto intro: RETURN_RES_refine simp: unat64_max_def)
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
      clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def clss_size_lcountUEk_def
      split: prod.splits)
  have H: \<open>(xb, x'a)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur'''' (length (get_clauses_wl_heur x1e) + MAX_HEADER_SIZE+1 + unat32_max div 2) \<Longrightarrow>
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
          (T, T') \<in> twl_st_heur_loop \<and>
          (\<not>brk \<longrightarrow> (n = n' \<and> last_GC' = last_GC \<and> last_Rephase' = last_Rephase)) \<and>
          (\<not> ebrk \<longrightarrow> isasat_fast T \<and> n < unat64_max) \<and>
          length (get_clauses_wl_heur T) \<le> unat64_max}\<close>

  have H4: \<open>\<And>x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i S Sa
    T Ta xb x'a x1j x2j x1k x2k.
    (x, y) \<in> twl_st_heur''' r \<Longrightarrow>
    (xa, x') \<in> ?R \<Longrightarrow>
    x2c = (x1d, x2d) \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    x2a = (x1b, x2b) \<Longrightarrow>
    x2 = (x1a, x2a) \<Longrightarrow>
    x' = (x1, x2) \<Longrightarrow>
    x2h = (x1i, x2i) \<Longrightarrow>
    x2g = (x1h, x2h) \<Longrightarrow>
    x2f = (x1g, x2g) \<Longrightarrow>
    x2e = (x1f, x2f) \<Longrightarrow>
    xa = (x1e, x2e) \<Longrightarrow>
    \<not> x1a \<Longrightarrow>
    \<not> x1f \<and> \<not> x1e \<Longrightarrow>
    isasat_fast x1g \<Longrightarrow>
    (S, Sa)
    \<in> twl_st_heur'' (dom_m (get_clauses_wl x1b)) (length (get_clauses_wl_heur x1g))
    (get_learned_count x1g) \<Longrightarrow>
    (T, Ta)
    \<in> twl_st_heur'' (dom_m (get_clauses_wl Sa)) (length (get_clauses_wl_heur S)) (get_learned_count S) \<Longrightarrow>
    isasat_fast T \<Longrightarrow>
    (xb, x'a)
    \<in> bool_rel \<times>\<^sub>f
      twl_st_heur''''uu (length (get_clauses_wl_heur S) + 3 + 1 + unat32_max div 2)
    (Suc (clss_size_allcount (get_learned_count S))) \<Longrightarrow>
    x'a = (x1j, x2j) \<Longrightarrow>
    xb = (x1k, x2k) \<Longrightarrow>
    isasat_fast_relaxed2 x2k x2i \<Longrightarrow>
    (((((x2k, x1h), x1i), x2i), x1k), (((x2j, x1c), x1d), x2d), x1j)
    \<in> twl_st_heur''''u (length (get_clauses_wl_heur x2k)) (learned_clss_count x2k) \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      bool_rel\<close>
   by simp

    have H5:
      \<open>(xc, x'b) \<in> restart_prog_wl_heur_rel (length (get_clauses_wl_heur x2k)) (learned_clss_count x2k) \<Longrightarrow>
    x2m = (x1n, x2n) \<Longrightarrow>
    x2l = (x1m, x2m) \<Longrightarrow>
    x'b = (x1l, x2l) \<Longrightarrow>
    x2p = (x1q, x2q) \<Longrightarrow>
    x2o = (x1p, x2p) \<Longrightarrow>
    xc = (x1o, x2o) \<Longrightarrow>
    (x1o, x1l)
      \<in> twl_st_heur_loop''''uu  (length (get_clauses_wl_heur x2k)) (learned_clss_count x2k)\<close>
    for x2k x2m x1n x2n x2l x1m x'b x1l x2p x1q x2q x2o x1o xc x1p
    by auto

  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp] learned_clss_count_twl_st_heur[simp]
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_alt_def
      cdcl_twl_stgy_restart_prog_bounded_wl_alt_def
    apply (intro frefI nres_relI)

    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry4]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        update_all_phases_Pair
        convert_to_full_state_wl_heur
        WHILEIT_refine[where R = \<open>?R\<close>])
    subgoal using r by (auto simp: snat64_max_def isasat_fast_def unat32_max_def
      dest: twl_st_heur_twl_st_heur_loopD)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      using cdcl_twl_stgy_restart_abs_wl_inv_NoneD[of y \<open>fst (snd (snd x'))\<close>
        \<open>fst (snd (snd (snd x')))\<close> \<open>fst (snd (snd (snd (snd x'))))\<close> \<open>snd (snd (snd (snd (snd x'))))\<close>] 
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def prod.case prod_rel_fst_snd_iff
      apply (rule_tac x=y in exI)
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close> in exI)
      apply (case_tac xa; case_tac x')
      by (auto intro!: twl_st_heur_twl_st_heur_loopD)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: snat64_max_def isasat_fast_def unat32_max_def)
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest!: cdcl_twl_stgy_restart_abs_wl_inv_NoneD)
    apply (rule twl_st_heur'')
    subgoal by simp
    subgoal by (auto dest: get_learned_count_learned_clss_countD simp: isasat_fast_def)
    apply (rule twl_st_heur'''; assumption)
    subgoal by (auto simp: isasat_fast_def unat64_max_def unat32_max_def snat64_max_def
      isasat_fast_relaxed_def isasat_fast_relaxed2_def)
    apply (rule H4; assumption)
    apply (rule H5; assumption)
    subgoal
      by (auto simp: isasat_fast_def unat64_max_def unat32_max_def snat64_max_def
        isasat_fast_relaxed_def)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i S Sa
    T Ta xb x'a x1j x2j x1k x2k xc x'b x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q Tb Tc
      unfolding get_conflict_wl_is_None (*auto with the simp rules also works, but takes forever*)
      apply (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id, of _ Tc])
      apply fast
      by (auto simp: isasat_fast_def unat64_max_def unat32_max_def snat64_max_def
        dest!: twl_st_heur_twl_st_heur_loopD)
    subgoal by auto
    done
qed

end
