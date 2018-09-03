theory IsaSAT_CDCL
  imports IsaSAT_Propagate_Conflict IsaSAT_Conflict_Analysis IsaSAT_Backtrack
    IsaSAT_Decide IsaSAT_Show
begin

context isasat_input_bounded_nempty
begin

paragraph \<open>Combining Together: the Other Rules\<close>

definition (in isasat_input_ops) cdcl_twl_o_prog_wl_D_heur
 :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>cdcl_twl_o_prog_wl_D_heur S =
    do {
      if get_conflict_wl_is_None_heur S
      then decide_wl_or_skip_D_heur S
      else do {
        if count_decided_st S > zero_uint32_nat
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D_heur S;
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

lemma cdcl_twl_o_prog_wl_D_heur_alt_def:
  \<open>cdcl_twl_o_prog_wl_D_heur S =
    do {
      if get_conflict_wl_is_None_heur S
      then decide_wl_or_skip_D_heur S
      else do {
        if count_decided_st S > zero_uint32_nat
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D_heur S;
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          _ \<leftarrow> isasat_current_status U; \<comment> \<open>Print some information every once in a while\<close>
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def isasat_current_status_def
  by auto

sepref_register get_conflict_wl_is_None decide_wl_or_skip_D_heur skip_and_resolve_loop_wl_D_heur
  backtrack_wl_D_nlit_heur

sepref_register cdcl_twl_o_prog_wl_D

sepref_thm cdcl_twl_o_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_alt_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_o_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_code_def

lemmas cdcl_twl_o_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(*
sepref_thm cdcl_twl_o_prog_wl_D_fast_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> bool_assn *a isasat_fast_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_fast_code
   uses isasat_input_bounded_nempty.cdcl_twl_o_prog_wl_D_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_fast_code_def

lemmas cdcl_twl_o_prog_wl_D_fast_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms] *)

lemma (in isasat_input_ops) twl_st_heur_count_decided_st_alt_def:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> count_decided_st S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_def
  by (cases S) auto

lemma cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D:
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f
     \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def cdcl_twl_o_prog_wl_D_def
    get_conflict_wl_is_None
  apply (intro frefI nres_relI)
  apply (refine_vcg
      decide_wl_or_skip_D_heur_decide_wl_or_skip_D[THEN fref_to_Down]
      skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D[THEN fref_to_Down]
      backtrack_wl_D_nlit_backtrack_wl_D[THEN fref_to_Down])
  subgoal
   by (auto simp: twl_st_heur_state_simp
     get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_count_decided_st_alt_def)
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  done


paragraph \<open>Combining Together: Full Strategy\<close>

definition (in isasat_input_ops) cdcl_twl_stgy_prog_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_prog_wl_D_heur S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          cdcl_twl_o_prog_wl_D_heur T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>


lemma cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D:
  \<open>(cdcl_twl_stgy_prog_wl_D_heur, cdcl_twl_stgy_prog_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def cdcl_twl_stgy_prog_wl_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down])
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  done

sepref_register cdcl_twl_stgy_prog_wl_D unit_propagation_outer_loop_wl_D_heur
  cdcl_twl_o_prog_wl_D_heur

sepref_thm cdcl_twl_stgy_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_stgy_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_prog_wl_D_code_def

lemmas cdcl_twl_stgy_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n]
end
(*
definition (in -)isasat_fast2 where
  \<open>isasat_fast2 = isasat_fast\<close>


definition (in -) isasat_fast_clss :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>isasat_fast_clss = (\<lambda>(_, N). length N \<le> uint32_max)\<close>

definition (in -) isasat_fast_clss_dom :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>isasat_fast_clss_dom = (\<lambda>N. \<forall>i\<in>#dom_m N. i < uint32_max)\<close>


lemma (in -) isasat_fast_clss_dom:
  \<open>(RETURN o isasat_fast_clss, RETURN o isasat_fast_clss_dom) \<in>
      \<langle>Id\<rangle>clauses_l_fmat \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp:  clauses_ll_assn_def list_fmap_rel_def isasat_fast_clss_dom_def
      isasat_fast_clss_def)
  apply (subst (asm)(4) eq_commute)
  apply auto
  apply (case_tac \<open>dom_m y\<close>)
   apply (auto simp: uint_max_def)
  apply (subst (asm)(4) eq_commute)
  apply auto
  done

definition (in -) isasat_fast_code :: \<open>twl_st_wll_trail_fast \<Rightarrow> bool\<close> where
  \<open>isasat_fast_code = (\<lambda>(M', (N', _, n), _). n < uint32_max)\<close>


lemma (in -)isasat_fast_clss_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>(N, _, n). n \<le> uint32_max), RETURN o isasat_fast_clss) \<in>
       isasat_clauses_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: isasat_fast_clss_def min_def
      isasat_fast2_def isasat_fast_code_def clauses_ll_assn_def
      hr_comp_def list_fmap_rel_def arlO_assn_def arl_assn_def
      is_array_list_def list_rel_imp_same_length[symmetric]
      dest: heap_list_add_same_length
      elim!: mod_starE
      split: if_splits)

lemma isasat_fast_clss_dom_hnr [sepref_fr_rules]:
\<open>((return \<circ>\<circ> case_prod) (\<lambda>N (_, n). n \<le> uint_max),
     RETURN \<circ> isasat_fast_clss_dom)
    \<in> (clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using isasat_fast_clss_hnr[FCOMP isasat_fast_clss_dom] unfolding clauses_ll_assn_def[symmetric]
  .

lemma (in -)isasat_fast2_alt_def:
  \<open>isasat_fast2 = (\<lambda>(M,N,_). isasat_fast_clss_dom N)\<close>
  by (auto simp: isasat_fast2_def isasat_fast_clss_dom_def) *)


context isasat_input_bounded_nempty
begin

(* declare isasat_fast_slow_code.refine[sepref_fr_rules] *)

(* sepref_register isasat_fast2
sepref_thm isasat_fast2_code
  is \<open>RETURN o isasat_fast2\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_fast2_alt_def isasat_fast_assn_def
  by sepref

concrete_definition (in -) isasat_fast2_code
  uses isasat_input_bounded_nempty.isasat_fast2_code.refine_raw
  is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) isasat_fast2_code_def

lemmas isasat_fast2_code[sepref_fr_rules] =
   isasat_fast2_code.refine[OF isasat_input_bounded_nempty_axioms] *)

sepref_register cdcl_twl_stgy_prog_wl_D_heur

(* definition (in isasat_input_ops) cdcl_twl_stgy_prog_break_wl_D_heur_break
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_prog_break_wl_D_heur_break S\<^sub>0 =
  do {
    let b = isasat_fast2 S\<^sub>0;
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, S). (b \<longrightarrow> \<not>brk \<longrightarrow>isasat_fast2 S)\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT (b \<and> \<not>brk);
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          ASSERT(isasat_fast2 T);
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
          b \<leftarrow> RETURN (isasat_fast2 T);
          RETURN (b, brk, T)
        })
        (b, False, S\<^sub>0);
    if brk then isasat_fast_slow T
    else do {
        T' \<leftarrow> isasat_fast_slow T;
        cdcl_twl_stgy_prog_wl_D_heur T'
    }
  }\<close> *)
(*
sepref_register isasat_fast_slow
sepref_thm cdcl_twl_stgy_prog_wl_D_fast_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_break_wl_D_heur_break\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  unfolding cdcl_twl_stgy_prog_break_wl_D_heur_break_def PR_CONST_def
  supply [[goals_limit = 1]] isasat_input_bounded_nempty_axioms[intro] isasat_fast2_def[simp]
  by sepref

concrete_definition (in -) cdcl_twl_stgy_prog_wl_D_fast_code
   uses isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_prog_wl_D_fast_code_def

lemmas cdcl_twl_stgy_prog_wl_D_fast_code[sepref_fr_rules] =
   cdcl_twl_stgy_prog_wl_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n] *)

(* definition  (in -)isasat_fast_wl where
  \<open>isasat_fast_wl S = (\<forall>L\<in>#dom_m (get_clauses_wl S). L < uint_max)\<close>

lemma twl_st_heur_isasat_fast_wl:
   \<open>(x, y) \<in> twl_st_heur \<Longrightarrow> isasat_fast_wl y = isasat_fast2 x\<close>
  by (auto simp: isasat_fast2_def twl_st_heur_state_simp twl_st_heur_def isasat_fast_wl_def)
term isasat_fast_slow

lemma cdcl_twl_stgy_prog_break_wl_D_alt_def:
  \<open>cdcl_twl_stgy_prog_break_wl_D S\<^sub>0 =
  do {
    b \<leftarrow> SPEC (\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 (brk, T) \<and>
          literals_are_\<L>\<^sub>i\<^sub>n T\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(b);
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
          b \<leftarrow>  SPEC (\<lambda>_. True);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    if brk then RETURN (isasat_fast_slow_wl_D T)
    else do {
        let T' = isasat_fast_slow_wl_D T;
        cdcl_twl_stgy_prog_wl_D T'
     }
  }\<close>
  unfolding Let_def cdcl_twl_stgy_prog_break_wl_D_def isasat_fast_slow_wl_D_def id_apply
  by (auto simp: Let_def)

lemma cdcl_twl_stgy_prog_wl_D_heur_break_cdcl_twl_stgy_prog_wl_D:
  \<open>(cdcl_twl_stgy_prog_break_wl_D_heur_break,
     cdcl_twl_stgy_prog_break_wl_D) \<in>
         twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have H1: \<open>
    (isasat_fast2 x, b) \<in> bool_rel \<Longrightarrow>
    (x, y) \<in> twl_st_heur \<Longrightarrow>
    ((isasat_fast2 x, False, x), b, False, y) \<in> {(b, b'). b = b' \<and>
       (b \<longrightarrow> isasat_fast2 x)} \<times>\<^sub>r bool_rel \<times>\<^sub>r twl_st_heur\<close> for b x y
    by auto
  have H2:
    \<open>(x, y) \<in> twl_st_heur \<Longrightarrow>
    (isasat_fast2 x, isasat_fast_wl y) \<in> {(b, b'). b = b' \<and>
       (b \<longrightarrow> isasat_fast2 x)}\<close> for x y
    by (auto simp: twl_st_heur_state_simp twl_st_heur_isasat_fast_wl)
  have H3:
    \<open>RETURN (isasat_fast2 x) \<le> \<Down> {(b, b'). b = b' \<and> (b \<longrightarrow> isasat_fast2 x)} (SPEC (\<lambda>_. True))\<close>
    for x
     by (auto simp: RETURN_RES_refine_iff)
  let ?R = \<open>{((b, brk, S), (b', brk', S')). b = b' \<and>
       (b \<longrightarrow> isasat_fast2 S) \<and> brk = brk' \<and> (S, S') \<in> twl_st_heur}\<close>

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del] twl_st_heur'_def[simp]
    unfolding cdcl_twl_stgy_prog_break_wl_D_heur_break_def cdcl_twl_stgy_prog_break_wl_D_alt_def
      isasat_fast2_def[symmetric]
  apply (intro frefI nres_relI)
  apply (refine_vcg H1 H2 H3
      WHILEIT_refine[where R= ?R]
      unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down,
        of x y \<open>dom_m (get_clauses_wl_heur x)\<close> for x y]
      cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
      cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D[THEN fref_to_Down]
      isasat_fast_slow_isasat_fast_slow_wl_D[THEN fref_to_Down, unfolded comp_def, simplified])
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_isasat_fast_wl)
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_isasat_fast_wl)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp isasat_fast2_def)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_isasat_fast_wl)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_isasat_fast_wl)
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_isasat_fast_wl)
  done

qed *)

end

(* export_code cdcl_twl_stgy_prog_wl_D_fast_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail_Fast.sml" *)

export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.sml"


end
