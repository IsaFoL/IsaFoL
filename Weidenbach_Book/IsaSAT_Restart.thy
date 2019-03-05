theory IsaSAT_Restart
  imports IsaSAT_Restart_Heuristics IsaSAT_CDCL
begin

definition cdcl_twl_stgy_restart_abs_wl_heur_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n \<longleftrightarrow>
    (\<exists>S\<^sub>0' T'. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
      cdcl_twl_stgy_restart_abs_wl_D_inv S\<^sub>0' brk T' n)\<close>

definition cdcl_twl_stgy_restart_prog_wl_heur
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

definition cdcl_twl_stgy_restart_prog_early_wl_heur
   :: "twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres"
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T)\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(length (get_clauses_wl_heur S) \<le> uint64_max);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max);
        ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S));
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        (T, n) \<leftarrow> restart_prog_wl_D_heur T n brk;
	      ebrk \<leftarrow> RETURN (\<not>isasat_fast T);
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0::twl_st_wl_heur, 0);
    if \<not>brk then do {
       T \<leftarrow> isasat_fast_slow T;
       (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n\<^esup>
	         (\<lambda>(brk, _). \<not>brk)
	         (\<lambda>(brk, S, n).
	         do {
	           T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
	           (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
	           (T, n) \<leftarrow> restart_prog_wl_D_heur T n brk;
	           RETURN (brk, T, n)
	         })
	         (False, T, n);
       RETURN T
    }
    else isasat_fast_slow T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_wl_heur_cdcl_twl_stgy_restart_prog_early_wl_D:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl_heur, cdcl_twl_stgy_restart_prog_early_wl_D) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_stgy_restart_prog_early_wl_D_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_early_wl_D S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, brk, T, n). cdcl_twl_stgy_restart_abs_wl_D_inv S\<^sub>0 brk T n\<^esup>
	        (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
	        (\<lambda>(_, brk, S, n).
	        do {
	          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
	          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
	          (T, n) \<leftarrow> restart_prog_wl_D T n brk;
	          ebrk \<leftarrow> RES UNIV;
	          RETURN (ebrk, brk, T, n)
	        })
	        (ebrk, False, S\<^sub>0::nat twl_st_wl, 0);
      if \<not>brk then do {
        T \<leftarrow> RETURN T;
	(brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_D_inv S\<^sub>0 brk T n\<^esup>
	  (\<lambda>(brk, _). \<not>brk)
	  (\<lambda>(brk, S, n).
	  do {
	    T \<leftarrow> unit_propagation_outer_loop_wl_D S;
	    (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
	    (T, n) \<leftarrow> restart_prog_wl_D T n brk;
	    RETURN (brk, T, n)
	  })
	  (False, T::nat twl_st_wl, n);
	RETURN T
      }
      else RETURN T
    }\<close> for S\<^sub>0
    unfolding cdcl_twl_stgy_restart_prog_early_wl_D_def nres_monad1 by auto
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
      unfolding isasat_fast_slow_alt_def by auto
  qed
  have twl_st_heur'': \<open>(x1e, x1b) \<in> twl_st_heur \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''
        (dom_m (get_clauses_wl x1b))
        (length (get_clauses_wl_heur x1e))\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)
  have abs_inv: \<open>(x, y) \<in> twl_st_heur \<Longrightarrow>
    (ebrk, ebrka) \<in> {(b, b'). b = b' \<and> b = (\<not> isasat_fast x)} \<Longrightarrow>
    (xb, x'a) \<in> bool_rel \<times>\<^sub>f (twl_st_heur \<times>\<^sub>f nat_rel) \<Longrightarrow>
    case x'a of
    (brk, xa, xb) \<Rightarrow>
      cdcl_twl_stgy_restart_abs_wl_D_inv y brk xa xb \<Longrightarrow>
    x2f = (x1g, x2g) \<Longrightarrow>
    xb = (x1f, x2f) \<Longrightarrow>
    cdcl_twl_stgy_restart_abs_wl_heur_inv x x1f x1g x2g\<close>
   for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
       x1e x2e T Ta xb x'a x1f x2f x1g x2g
    unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fastforce
  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp]
    unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def
      cdcl_twl_stgy_restart_prog_early_wl_D_alt_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry2]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r twl_st_heur \<times>\<^sub>r nat_rel\<close>]
        WHILEIT_refine[where R = \<open>{((ebrk, brk, T,n), (ebrk', brk', T', n')).
	    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur \<and> n = n' \<and>
	      (\<not>ebrk \<longrightarrow> isasat_fast T)}\<close>])
    subgoal by auto
    subgoal
      unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule abs_inv)
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: isasat_fast_slow_alt_def)
    done
qed

sepref_register number_clss_to_keep

sepref_definition number_clss_to_keep_impl
  is \<open> (RETURN o number_clss_to_keep)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding number_clss_to_keep_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition number_clss_to_keep_fast_impl
  is \<open> (RETURN o number_clss_to_keep)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding number_clss_to_keep_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare number_clss_to_keep_impl.refine[sepref_fr_rules]
   number_clss_to_keep_fast_impl.refine[sepref_fr_rules]

sepref_register access_vdom_at
sepref_definition access_vdom_at_code
  is \<open>uncurry ( (RETURN oo access_vdom_at))\<close>
  :: \<open>[uncurry access_vdom_at_pre]\<^sub>a isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding access_vdom_at_alt_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition access_vdom_at_fast_code
  is \<open>uncurry ( (RETURN oo access_vdom_at))\<close>
  :: \<open>[uncurry access_vdom_at_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding access_vdom_at_alt_def access_vdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref


declare access_vdom_at_fast_code.refine[sepref_fr_rules]
   access_vdom_at_code.refine[sepref_fr_rules]

definition length_avdom :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>length_avdom S = length (get_avdom S)\<close>

lemma length_avdom_alt_def:
  \<open>length_avdom = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount). length avdom)\<close>
  by (intro ext) (auto simp: length_avdom_def)

sepref_register length_avdom
sepref_definition length_avdom_code
  is \<open> (RETURN o length_avdom)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding length_avdom_alt_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition length_avdom_fast_code
  is \<open> (RETURN o length_avdom)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding length_avdom_alt_def access_vdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare  length_avdom_code.refine[sepref_fr_rules]
    length_avdom_fast_code.refine[sepref_fr_rules]

definition get_the_propagation_reason_heur
 :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close>
where
  \<open>get_the_propagation_reason_heur S = get_the_propagation_reason_pol (get_trail_wl_heur S)\<close>

lemma get_the_propagation_reason_heur_alt_def:
  \<open>get_the_propagation_reason_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) L . get_the_propagation_reason_pol M' L)\<close>
  by (intro ext) (auto simp: get_the_propagation_reason_heur_def)

sepref_register get_the_propagation_reason_heur
sepref_definition get_the_propagation_reason_heur_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  unfolding get_the_propagation_reason_heur_alt_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint64_nat_assn\<close>
  unfolding get_the_propagation_reason_heur_alt_def access_vdom_at_pre_def
     isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare get_the_propagation_reason_heur_fast_code.refine[sepref_fr_rules]
    get_the_propagation_reason_heur_code.refine[sepref_fr_rules]

definition clause_is_learned_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool"
where
  \<open>clause_is_learned_heur S C \<longleftrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED\<close>

lemma clause_is_learned_heur_alt_def:
  \<open>clause_is_learned_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . arena_status N' C = LEARNED)\<close>
  by (intro ext) (auto simp: clause_is_learned_heur_def)

sepref_register clause_is_learned_heur
sepref_definition clause_is_learned_heur_code
  is \<open>uncurry (RETURN oo ( clause_is_learned_heur))\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding clause_is_learned_heur_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo ( clause_is_learned_heur))\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare clause_is_learned_heur_code.refine[sepref_fr_rules]
    clause_is_learned_heur_code2.refine[sepref_fr_rules]


(* TODO deduplicate arena_lbd = get_clause_LBD *)
definition clause_lbd_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat"
where
  \<open>clause_lbd_heur S C = arena_lbd (get_clauses_wl_heur S) C\<close>

lemma clause_lbd_heur_alt_def:
  \<open>clause_lbd_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . get_clause_LBD N' C)\<close>
  by (intro ext) (auto simp: clause_lbd_heur_def get_clause_LBD_def arena_lbd_def)

sepref_register clause_lbd_heur
sepref_definition clause_lbd_heur_code
  is \<open>uncurry (RETURN oo ( clause_lbd_heur))\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding clause_lbd_heur_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding clause_lbd_heur_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare  clause_lbd_heur_code2.refine[sepref_fr_rules]
    clause_lbd_heur_code.refine[sepref_fr_rules]

sepref_register mark_garbage_heur
sepref_definition mark_garbage_heur_code
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding mark_garbage_heur_def isasat_unbounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def
  supply [[goals_limit = 1]]
  by sepref

declare  mark_garbage_heur_code.refine[sepref_fr_rules]
    mark_garbage_heur_code2.refine[sepref_fr_rules]

sepref_register delete_index_vdom_heur
sepref_definition delete_index_vdom_heur_code
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding delete_index_vdom_heur_def isasat_unbounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def butlast_nonresizing_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition delete_index_vdom_heur_fast_code2
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding delete_index_vdom_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def butlast_nonresizing_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare delete_index_vdom_heur_code.refine[sepref_fr_rules]
  delete_index_vdom_heur_fast_code2.refine[sepref_fr_rules]

definition (in -) access_length_heur where
  \<open>access_length_heur S i = arena_length (get_clauses_wl_heur S) i\<close>

lemma access_length_heur_alt_def:
  \<open>access_length_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . arena_length N' C)\<close>
  by (intro ext) (auto simp: access_length_heur_def arena_lbd_def)

sepref_register access_length_heur
sepref_definition access_length_heur_code
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding access_length_heur_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition access_length_heur_fast_code2
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding access_length_heur_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare access_length_heur_code.refine[sepref_fr_rules]
  access_length_heur_fast_code2.refine[sepref_fr_rules]

definition marked_as_used_st where
  \<open>marked_as_used_st T C =
    marked_as_used (get_clauses_wl_heur T) C\<close>

lemma marked_as_used_st_alt_def:
  \<open>marked_as_used_st = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . marked_as_used N' C)\<close>
  by (intro ext) (auto simp: marked_as_used_st_def)

(*TODO Move*)

sepref_definition isa_marked_as_used_fast_code
  is \<open>uncurry isa_marked_as_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply op_eq_uint32[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_marked_as_used_def
  by sepref

lemma isa_marked_as_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_marked_as_used_fast_code, uncurry (RETURN \<circ>\<circ> marked_as_used))
     \<in> [uncurry marked_as_used_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using isa_marked_as_used_fast_code.refine[FCOMP isa_marked_as_used_marked_as_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

(*END Move*)
sepref_register marked_as_used_st
sepref_definition marked_as_used_st_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding marked_as_used_st_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition marked_as_used_st_fast_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition marked_as_used_st_fast_code2
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare marked_as_used_st_code.refine[sepref_fr_rules]
  marked_as_used_st_fast_code.refine[sepref_fr_rules]
  marked_as_used_st_fast_code2.refine[sepref_fr_rules]

sepref_definition mark_unused_st_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_register mark_unused_st_heur
sepref_definition mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition mark_unused_st_fast_code2
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare mark_unused_st_code.refine[sepref_fr_rules]
  mark_unused_st_fast_code.refine[sepref_fr_rules]
  mark_unused_st_fast_code2.refine[sepref_fr_rules]

sepref_register mark_to_delete_clauses_wl_D_heur
sepref_definition mark_to_delete_clauses_wl_D_heur_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    short_circuit_conv
    marked_as_used_st_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

(* TODO Move *)
sepref_definition sort_vdom_heur_fast_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding sort_vdom_heur_def isasat_bounded_assn_def
  by sepref

declare sort_vdom_heur_fast_code.refine[sepref_fr_rules]

sepref_definition clause_not_marked_to_delete_heur_fast_code2
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref


declare clause_not_marked_to_delete_heur_fast_code.refine[sepref_fr_rules]
  clause_not_marked_to_delete_heur_fast_code2.refine[sepref_fr_rules]

sepref_definition access_lit_in_clauses_heur_fast_code2
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j)]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]] arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isasat_bounded_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric] arena_is_valid_clause_idx_le_uint64_max2[intro]
  by sepref

declare access_lit_in_clauses_heur_fast_code.refine[sepref_fr_rules]
  access_lit_in_clauses_heur_fast_code2.refine[sepref_fr_rules]

(* END Move *)

lemma mark_to_delete_clauses_wl_D_heur_is_Some_iff:
  \<open>D = Some C \<longleftrightarrow> D \<noteq> None \<and> (nat_of_uint64_conv (the D) = C)\<close>
  by auto

sepref_definition mark_to_delete_clauses_wl_D_heur_fast_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>[\<lambda>S. True]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    short_circuit_conv mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric]
  supply [[goals_limit = 1]] option.splits[split]
  by sepref

declare mark_to_delete_clauses_wl_D_heur_fast_impl.refine[sepref_fr_rules]
  mark_to_delete_clauses_wl_D_heur_impl.refine[sepref_fr_rules]

sepref_register cdcl_twl_full_restart_wl_prog_heur
sepref_definition cdcl_twl_full_restart_wl_prog_heur_code
  is \<open> cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_full_restart_wl_prog_heur_fast_code
  is \<open> cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_full_restart_wl_prog_heur_fast_code.refine[sepref_fr_rules]
   cdcl_twl_full_restart_wl_prog_heur_code.refine[sepref_fr_rules]

sepref_definition cdcl_twl_restart_wl_heur_code
  is \<open> cdcl_twl_restart_wl_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_restart_wl_heur_fast_code
  is \<open> cdcl_twl_restart_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_restart_wl_heur_fast_code.refine[sepref_fr_rules]
   cdcl_twl_restart_wl_heur_code.refine[sepref_fr_rules]

sepref_register restart_required_heur cdcl_twl_restart_wl_heur
sepref_definition restart_wl_D_heur_slow_code
  is \<open>uncurry2 ( restart_prog_wl_D_heur)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_unbounded_assn *a nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition restart_prog_wl_D_heur_fast_code
  is \<open>uncurry2 ( restart_prog_wl_D_heur)\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn *a nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare restart_wl_D_heur_slow_code.refine[sepref_fr_rules]
   restart_prog_wl_D_heur_fast_code.refine[sepref_fr_rules]


sepref_definition cdcl_twl_stgy_restart_prog_wl_heur_code
  is \<open>cdcl_twl_stgy_restart_prog_wl_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_stgy_restart_prog_wl_heur_code.refine[sepref_fr_rules]

lemma (in -) isasat_fast_alt_def:
  \<open>RETURN o isasat_fast = (\<lambda>(M, N, _). RETURN (length N \<le> uint64_max - (uint32_max div 2 + 6)))\<close>
  unfolding isasat_fast_def
  by (auto intro!:ext)

lemma (in -) uint32_max_nat_hnr:
  \<open>(uncurry0 (return uint32_max), uncurry0 (RETURN uint32_max)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

sepref_register isasat_fast
sepref_definition isasat_fast_code
  is \<open>RETURN o ( isasat_fast)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding isasat_fast_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]] uint32_max_nat_hnr[sepref_fr_rules]
  by sepref

declare isasat_fast_code.refine[sepref_fr_rules]

sepref_definition cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_early_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  by sepref

declare cdcl_twl_stgy_restart_prog_wl_heur_fast_code.refine[sepref_fr_rules]

export_code cdcl_twl_stgy_restart_prog_wl_heur_code in SML_imp module_name Test

end