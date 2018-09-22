theory IsaSAT_Restart
  imports IsaSAT_Restart_Heuristics IsaSAT_CDCL
begin

context isasat_input_bounded_nempty
begin

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

definition (in isasat_input_ops) cdcl_twl_stgy_restart_prog_early_wl_heur
   :: "twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres"
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 brk T n \<and> (\<not>ebrk \<longrightarrow>isasat_fast T)\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, n).
      do {
        ASSERT(isasat_fast S);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
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
    else RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_wl_heur_cdcl_twl_stgy_restart_prog_early_wl_D:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl_heur, cdcl_twl_stgy_restart_prog_early_wl_D) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have cdcl_twl_stgy_restart_prog_early_wl_D_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_early_wl_D S\<^sub>0 = do {
      ebrk \<leftarrow> RES UNIV;
      (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
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
	(brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
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
  have [refine0]: \<open> RETURN (\<not>isasat_fast x) \<le> \<Down>
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
  show ?thesis
    supply[[goals_limit=1]]
    unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def
      cdcl_twl_stgy_restart_prog_early_wl_D_alt_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down_curry2]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r twl_st_heur \<times>\<^sub>r nat_rel\<close>]
        WHILEIT_refine[where R = \<open>{((ebrk, brk, T,n), (ebrk', brk', T', n')).
	    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur \<and> n = n' \<and>
	      (\<not>ebrk \<longrightarrow> isasat_fast T)}\<close>])
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_heur_inv_def by fastforce
    subgoal by auto
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
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding number_clss_to_keep_def PR_CONST_def isasat_unbounded_assn_def
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
  :: \<open>[uncurry access_vdom_at_pre]\<^sub>a isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding access_vdom_at_alt_def PR_CONST_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) access_vdom_at_code
   uses isasat_input_bounded_nempty.access_vdom_at_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) access_vdom_at_code_def

lemmas access_vdom_at_code[sepref_fr_rules] =
   access_vdom_at_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]


definition length_avdom :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>length_avdom S = length (get_avdom S)\<close>

lemma length_avdom_alt_def:
  \<open>length_avdom = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount). length avdom)\<close>
  by (intro ext) (auto simp: length_avdom_def)

sepref_register length_avdom
sepref_thm length_avdom_code
  is \<open>PR_CONST (RETURN o length_avdom)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding length_avdom_alt_def PR_CONST_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) length_avdom_code
   uses isasat_input_bounded_nempty.length_avdom_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) length_avdom_code_def

lemmas length_avdom_code[sepref_fr_rules] =
   length_avdom_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
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
  :: \<open>[\<lambda>(S, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>aisasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  unfolding get_the_propagation_reason_heur_alt_def PR_CONST_def access_vdom_at_pre_def isasat_unbounded_assn_def
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
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding clause_is_learned_heur_alt_def PR_CONST_def isasat_unbounded_assn_def
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
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding clause_lbd_heur_alt_def PR_CONST_def isasat_unbounded_assn_def
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
  is \<open>uncurry2 (RETURN ooo (PR_CONST mark_garbage_heur))\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding mark_garbage_heur_def PR_CONST_def isasat_unbounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) mark_garbage_heur_code
   uses isasat_input_bounded_nempty.mark_garbage_heur_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) mark_garbage_heur_code_def

lemmas mark_garbage_heur_code[sepref_fr_rules] =
   mark_garbage_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_register delete_index_vdom_heur
sepref_thm delete_index_vdom_heur_code
  is \<open>uncurry (RETURN oo (PR_CONST delete_index_vdom_heur))\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding delete_index_vdom_heur_def PR_CONST_def isasat_unbounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def butlast_nonresizing_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) delete_index_vdom_heur_code
   uses isasat_input_bounded_nempty.delete_index_vdom_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) delete_index_vdom_heur_code_def

lemmas delete_index_vdom_heur_code[sepref_fr_rules] =
   delete_index_vdom_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

definition (in -) access_length_heur where
  \<open>access_length_heur S i = arena_length (get_clauses_wl_heur S) i\<close>

lemma access_length_heur_alt_def:
  \<open>access_length_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, lcount) C . arena_length N' C)\<close>
  by (intro ext) (auto simp: access_length_heur_def arena_lbd_def)

sepref_register access_length_heur
sepref_thm access_length_heur_code
  is \<open>uncurry (RETURN oo (PR_CONST access_length_heur))\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding access_length_heur_alt_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) access_length_heur_code
   uses isasat_input_bounded_nempty.access_length_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) access_length_heur_code_def

lemmas access_length_heur_code_hnr[sepref_fr_rules] =
   access_length_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]


sepref_register mark_to_delete_clauses_wl_D_heur
sepref_thm mark_to_delete_clauses_wl_D_heur_impl
  is \<open>PR_CONST mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def PR_CONST_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    short_circuit_conv
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
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
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
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
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
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
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
  :: \<open>isasat_unbounded_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_unbounded_assn *a nat_assn\<close>
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
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn *a nat_assn\<close>
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
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) cdcl_twl_stgy_restart_prog_wl_heur_code
   uses isasat_input_bounded_nempty.cdcl_twl_stgy_restart_prog_wl_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_restart_prog_wl_heur_code_def

lemmas cdcl_twl_stgy_restart_prog_wl_heur_hnr[sepref_fr_rules] =
   cdcl_twl_stgy_restart_prog_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma (in -) isasat_fast_alt_def:
  \<open>RETURN o isasat_fast = (\<lambda>(M, N, _). RETURN (length N \<le> uint64_max - (uint32_max + 5)))\<close>
  unfolding isasat_fast_def
  by (auto intro!:ext)

lemma (in -) uint32_max_nat_hnr:
  \<open>(uncurry0 (return uint32_max), uncurry0 (RETURN uint32_max)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

sepref_register isasat_fast
sepref_thm (in isasat_input_ops) isasat_fast_code
  is \<open>RETURN o (PR_CONST isasat_fast)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding isasat_fast_alt_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]] uint32_max_nat_hnr[sepref_fr_rules]
  by sepref


concrete_definition (in -) isasat_fast_code
   uses isasat_input_ops.isasat_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) isasat_fast_code_def

lemmas isasat_fast_hnr[sepref_fr_rules] =
   isasat_fast_code.refine[of \<A>\<^sub>i\<^sub>n, unfolded PR_CONST_def]

text \<open>TODO There is no fast mode yet!\<close>
sepref_thm cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>PR_CONST cdcl_twl_stgy_restart_prog_early_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
    apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
           apply sepref_dbg_side_unfold apply (auto simp: )[]

  by sepref


end

export_code cdcl_twl_stgy_restart_prog_wl_heur_code in SML_imp module_name Test


end