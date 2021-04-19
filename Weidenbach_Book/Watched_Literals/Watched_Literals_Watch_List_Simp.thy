theory Watched_Literals_Watch_List_Simp
  imports Watched_Literals_Watch_List_Reduce Watched_Literals_Watch_List
    Watched_Literals_Watch_List_Inprocessing
begin

no_notation funcset (infixr "\<rightarrow>" 60)


definition cdcl_twl_full_restart_wl_GC_prog where
  \<open>cdcl_twl_full_restart_wl_GC_prog S = do {
  ASSERT(cdcl_twl_full_restart_wl_GC_prog_pre S);
  S' \<leftarrow> cdcl_twl_local_restart_wl_spec0 S;
  T \<leftarrow> remove_one_annot_true_clause_imp_wl S';
  ASSERT(mark_to_delete_clauses_GC_wl_pre T);
  U \<leftarrow> mark_to_delete_clauses_GC_wl T;
  V \<leftarrow> cdcl_GC_clauses_wl U;
  ASSERT(cdcl_twl_full_restart_wl_GC_prog_post S V);
  RETURN V
  }\<close>

lemma cdcl_twl_full_restart_wl_GC_prog:
  \<open>(cdcl_twl_full_restart_wl_GC_prog, cdcl_twl_full_restart_l_GC_prog) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_GC_prog_def cdcl_twl_full_restart_l_GC_prog_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp[THEN fref_to_Down]
    mark_to_delete_clauses_wl_mark_to_delete_clauses_l2[THEN fref_to_Down]
    cdcl_GC_clauses_wl_cdcl_GC_clauses[THEN fref_to_Down]
    cdcl_twl_local_restart_wl_spec0_cdcl_twl_local_restart_l_spec0)
  subgoal unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def by blast
  subgoal by (auto dest: correct_watching'_correct_watching'')
  subgoal unfolding mark_to_delete_clauses_GC_wl_pre_def by fast
  subgoal
    by (auto dest: correct_watching''_clauses_pointed_to2)
  subgoal for x y S S' T Ta U Ua V Va
    using cdcl_twl_full_restart_wl_GC_prog_post_correct_watching[of y Va V]
      cdcl_twl_restart_l_inp.intros(1)
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
    by blast
  subgoal for x y S S' T Ta U Ua V Va
    using cdcl_twl_full_restart_wl_GC_prog_post_correct_watching[of y Va V]
    by (auto dest!: cdcl_twl_restart_l_inp.intros(1))
  done


definition cdcl_twl_full_restart_inprocess_wl_prog where
  \<open>cdcl_twl_full_restart_inprocess_wl_prog S = do {
  ASSERT(cdcl_twl_full_restart_wl_GC_prog_pre S);
  S' \<leftarrow> cdcl_twl_local_restart_wl_spec0 S;
  S' \<leftarrow> remove_one_annot_true_clause_imp_wl S';
  T \<leftarrow> simplify_clauses_with_unit_st_wl S';
  if get_conflict_wl T \<noteq> None then RETURN T
  else do {
    ASSERT(mark_to_delete_clauses_GC_wl_pre T);
    U \<leftarrow> mark_to_delete_clauses_GC_wl T;
    V \<leftarrow> cdcl_GC_clauses_wl U;
    ASSERT(cdcl_twl_full_restart_wl_GC_prog_post S V);
    RETURN V
  }
  }\<close>

lemma cdcl_twl_full_restart_inprocess_wl_prog:
  \<open>(cdcl_twl_full_restart_inprocess_wl_prog, cdcl_twl_full_restart_inprocess_l) \<in>
    {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching' S \<and> literals_are_\<L>\<^sub>i\<^sub>n' S} \<rightarrow>\<^sub>f
     \<langle>{(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> (get_conflict_wl S = None \<longrightarrow> correct_watching S \<and>
       blits_in_\<L>\<^sub>i\<^sub>n S)}\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_inprocess_wl_prog_def cdcl_twl_full_restart_inprocess_l_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    remove_one_annot_true_clause_imp_wl_remove_one_annot_true_clause_imp[THEN fref_to_Down]
    cdcl_twl_local_restart_wl_spec0_cdcl_twl_local_restart_l_spec0
    simplify_clauses_with_unit_st_wl_simplify_clause_with_unit_st
    mark_to_delete_clauses_wl_mark_to_delete_clauses_l2[THEN fref_to_Down]
    cdcl_GC_clauses_wl_cdcl_GC_clauses[THEN fref_to_Down]
    )
  subgoal unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def by blast
  subgoal by (auto dest: correct_watching'_correct_watching'')
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    unfolding mark_to_delete_clauses_GC_wl_pre_def
    by fast
  subgoal for x y S S' T Ta U Ua
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
    by fast
  subgoal for x y S S' T Ta U Ua V Va W Wa
    using cdcl_twl_full_restart_wl_GC_prog_post_correct_watching[of y Wa W]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
    by fast
  subgoal for x y S' S'a T Ta U Ua V Va W Wa
    using cdcl_twl_full_restart_wl_GC_prog_post_correct_watching[of y Wa W]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
    by fast
  done


context twl_restart_ops
begin

definition restart_prog_wl
  :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_wl \<times> nat \<times> nat \<times> nat) nres"
  where
  \<open>restart_prog_wl S last_GC last_Restart n brk = do {
    ASSERT(restart_abs_wl_pre S last_GC last_Restart brk);
    b \<leftarrow> restart_required_wl S last_GC last_Restart n;
    if b = RESTART \<and> \<not>brk then do {
      T \<leftarrow> cdcl_twl_restart_wl_prog S;
      RETURN (T, last_GC, size (get_all_learned_clss_wl T), n)
    }
    else if b = GC \<and> \<not>brk then do {
      b \<leftarrow> SPEC(\<lambda>_. True);
      T \<leftarrow> (if b then cdcl_twl_full_restart_wl_prog S else cdcl_twl_full_restart_wl_GC_prog S);
      RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
    }
    else
      RETURN (S, last_GC, last_Restart, n)
    }\<close>

lemma restart_prog_wl_alt_def:
 \<open>restart_prog_wl S last_GC last_Restart n brk = do {
     ASSERT(restart_abs_wl_pre S last_GC last_Restart brk);
     b \<leftarrow> restart_required_wl S last_GC last_Restart n;
     let _ = (b = RESTART);
      if b = RESTART \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog S;
       RETURN (T, last_GC, size (get_all_learned_clss_wl T), n)
     }
     else if b = GC \<and> \<not>brk then do {
       b \<leftarrow> SPEC(\<lambda>_. True);
       T \<leftarrow> (if b then cdcl_twl_full_restart_wl_prog S else cdcl_twl_full_restart_wl_GC_prog S);
       RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
     }
     else
       RETURN (S, last_GC, last_Restart, n)
   }\<close>
  unfolding restart_prog_wl_def
  by auto

lemma restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n:
  assumes pre: \<open>restart_abs_wl_pre x1c last_GC last_Restart b\<close> and
    \<open>blits_in_\<L>\<^sub>i\<^sub>n x1c\<close>
  shows \<open>literals_are_\<L>\<^sub>i\<^sub>n' x1c\<close>
proof -

  obtain y x where
    y_x: \<open>(y, x) \<in> twl_st_l None\<close> and
    x1c_y: \<open>(x1c, y) \<in> state_wl_l None\<close> and
    struct_invs: \<open>twl_struct_invs x\<close> and
    list_invs: \<open>twl_list_invs y\<close>
    using pre unfolding restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def apply - apply normalize_goal+
    by blast
  then have eq:
    \<open>set_mset (all_init_lits_of_wl x1c) = set_mset (all_lits_st x1c)\<close>
    using y_x x1c_y literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(4) by blast
  moreover have eq: \<open>set_mset (all_learned_lits_of_wl x1c) \<subseteq> set_mset (all_lits_st x1c)\<close>
    using y_x x1c_y
    unfolding all_lits_st_init_learned by auto
  ultimately show \<open>literals_are_\<L>\<^sub>i\<^sub>n' x1c\<close>
    using eq assms by (cases x1c)
      (clarsimp simp: blits_in_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n'_def all_lits_def literals_are_\<L>\<^sub>i\<^sub>n'_def
         all_init_lits_def ac_simps)
qed

lemma cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog:
  \<open>(uncurry4 restart_prog_wl, uncurry4 restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>f nat_rel\<times>\<^sub>f nat_rel\<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>r nat_rel\<times>\<^sub>r nat_rel\<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<times>\<^sub>f _ \<times>\<^sub>f _ \<times>\<^sub>f _ \<times>\<^sub>f _  \<rightarrow>\<^sub>f \<langle>?R'\<rangle>nres_rel\<close>)
proof -
  have [simp]: \<open>size (learned_clss_l (get_clauses_wl a)) = size ((get_learned_clss_wl a))\<close> for a
    by (cases a, auto simp: get_learned_clss_wl_def)
  have [refine0]:
    \<open>restart_required_wl a b c d \<le> \<Down> {(b, b'). (b' = (b = GC)) \<and>
    (b = RESTART \<longrightarrow> size (get_all_learned_clss_wl a) > c)} (GC_required_l a' b' d')\<close>
    (is \<open>_ \<le> \<Down> ?GC _\<close>)
    if \<open>(a, a') \<in> ?R\<close> and \<open>(b, b') \<in> nat_rel\<close> \<open>(d, d') \<in> nat_rel\<close>
      \<open>restart_abs_wl_pre a b c brk\<close>
    for a a' b b' c c' d d' e e' brk
    using that unfolding restart_abs_wl_pre_def GC_required_l_def restart_abs_l_pre_def
      restart_required_wl_def restart_prog_pre_def apply -
    apply (refine_rcg)
    subgoal by auto
    subgoal by normalize_goal+ simp
    by (rule RES_refine, rule_tac x= \<open>s = GC\<close> in bexI)
     auto
  have [refine0]: \<open>RETURN (b = RESTART) \<le> \<Down>bool_rel (restart_required_l a' c d)\<close>
    if \<open>(b, b') \<in> ?GC a c'\<close> \<open>(a, a') \<in> ?R\<close> \<open>(c, c') \<in> nat_rel\<close>
    for a a' b b' c c' d d' e e'
    using that
    unfolding restart_required_l_def
    by refine_rcg auto
  show ?thesis
    unfolding uncurry_def restart_prog_wl_alt_def restart_prog_l_def rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_GC_prog[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_full_twl_restart_l_prog[THEN fref_to_Down])
    subgoal unfolding restart_abs_wl_pre_def
       by (fastforce simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption+
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by (auto)
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    done
qed


definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_wl
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_wl (S\<^sub>0::'v twl_st_wl) =
  do {
    (brk, T, _, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl T last_GC last_Restart n brk;
        RETURN (brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (False, S\<^sub>0::'v twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0), size (get_all_learned_clss_wl S\<^sub>0), 0);
    RETURN T
  }\<close>

end


definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_early_wl
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl (S\<^sub>0::'v twl_st_wl) = do {
    ebrk \<leftarrow> RES UNIV;
    (_, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0::'v twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0), size (get_all_learned_clss_wl S\<^sub>0), 0);
    if \<not> brk then do {
      (brk, T, _, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv T\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S, last_GC, last_Restart, n).
          do {
            T \<leftarrow> unit_propagation_outer_loop_wl S;
            (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
            (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl T last_GC last_Restart  n brk;
            RETURN (brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Restart, n)
          })
         (False, T::'v twl_st_wl, last_GC, last_Restart, n);
      RETURN T
    }
    else RETURN T
  }\<close>

context twl_restart_ops
begin


definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_bounded_wl
  :: \<open>'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl (S\<^sub>0::'v twl_st_wl) = do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0::'v twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0), size (get_all_learned_clss_wl S\<^sub>0), 0);
    RETURN (ebrk, T)
  }\<close>


lemma cdcl_twl_stgy_restart_prog_bounded_wl_cdcl_twl_stgy_restart_prog_bounded_l:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_wl, cdcl_twl_stgy_restart_prog_bounded_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>bool_rel \<times>\<^sub>r {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_def cdcl_twl_stgy_restart_prog_bounded_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry4]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def comp_def
      by (fastforce simp: prod_rel_fst_snd_iff)
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    done
qed

theorem cdcl_twl_stgy_restart_prog_bounded_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_wl, cdcl_twl_stgy_restart_prog_bounded_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>bool_rel \<times>\<^sub>r state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_bounded_wl_cdcl_twl_stgy_restart_prog_bounded_l[where 'a='v]
  unfolding fref_param1 apply -
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?; match_fun_rel?)
    auto

definition cdcl_GC_clauses_prog_copy_wl_entry
  :: \<open>'v clauses_l \<Rightarrow> 'v watched \<Rightarrow> 'v literal \<Rightarrow>
         'v clauses_l \<Rightarrow> ('v clauses_l \<times> 'v clauses_l) nres\<close>
where
\<open>cdcl_GC_clauses_prog_copy_wl_entry = (\<lambda>N W A N'. do {
    let le = length W;
    (i, N, N') \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, N'). i < le)
      (\<lambda>(i, N, N'). do {
        ASSERT(i < length W);
        let C = fst (W ! i);
        if C \<in># dom_m N then do {
          D \<leftarrow> SPEC(\<lambda>D. D \<notin># dom_m N' \<and> D \<noteq> 0);
	  RETURN (i+1, fmdrop C N, fmupd D (N \<propto> C, irred N C) N')
        } else RETURN (i+1, N, N')
      }) (0, N, N');
    RETURN (N, N')
  })\<close>

lemma cdcl_GC_clauses_prog_copy_wl_entry:
  fixes A :: \<open>'v literal\<close> and WS :: \<open>'v literal \<Rightarrow> 'v watched\<close>
  defines [simp]: \<open>W \<equiv> WS A\<close>
  assumes \<open>
	  ran m0 \<subseteq> set_mset (dom_m N0') \<and>
	  (\<forall>L\<in>dom m0. L \<notin># (dom_m N0)) \<and>
	  set_mset (dom_m N0) \<subseteq> clauses_pointed_to (set_mset \<A>) WS \<and>
          0 \<notin># dom_m N0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_copy_wl_entry N0 W A N0' \<le>
      SPEC(\<lambda>(N, N'). (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, m0, N0') (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  (\<forall>L\<in>dom m. L \<notin># (dom_m N)) \<and>
	  set_mset (dom_m N) \<subseteq> clauses_pointed_to (set_mset (remove1_mset A \<A>)) WS) \<and>
	  (\<forall>L \<in> set W. fst L \<notin># dom_m N) \<and>
          0 \<notin># dom_m N')\<close>
proof -
  have [simp]:
    \<open>x \<in># remove1_mset a (dom_m aaa) \<longleftrightarrow> x \<noteq> a \<and> x \<in># dom_m aaa\<close> for x a aaa
    using distinct_mset_dom[of aaa]
    by (cases \<open>a \<in># dom_m aaa\<close>)
      (auto dest!: multi_member_split simp: add_mset_eq_add_mset)

  show ?thesis
    unfolding cdcl_GC_clauses_prog_copy_wl_entry_def
    apply (refine_vcg
      WHILET_rule[where I = \<open>\<lambda>(i, N, N'). \<exists>m. GC_remap\<^sup>*\<^sup>* (N0, m0, N0') (N, m, N') \<and>
	  ran m \<subseteq> set_mset (dom_m N') \<and>
	  (\<forall>L\<in>dom m. L \<notin># (dom_m N)) \<and>
	  set_mset (dom_m N) \<subseteq> clauses_pointed_to (set_mset (remove1_mset A \<A>)) WS \<union>
	    (fst) ` set (drop i W) \<and>
	  (\<forall>L \<in> set (take i W). fst L \<notin># dom_m N) \<and>
          0 \<notin># dom_m N'\<close> and
	R = \<open>measure (\<lambda>(i, N, N'). length W -i)\<close>])
    subgoal by auto
    subgoal
      using assms
      by (cases \<open>A \<in># \<A>\<close>) (auto dest!: multi_member_split)
    subgoal by auto
    subgoal for s aa ba aaa baa x x1 x2 x1a x2a
      apply clarify
      apply (subgoal_tac \<open>(\<exists>m'. GC_remap (aaa, m, baa) (fmdrop (fst (W ! aa)) aaa, m',
		fmupd x (the (fmlookup aaa (fst (W ! aa)))) baa) \<and>
	  ran m' \<subseteq> set_mset (dom_m (fmupd x (the (fmlookup aaa (fst (W ! aa)))) baa)) \<and>
    (\<forall>L\<in>dom m'. L \<notin># (dom_m (fmdrop (fst (W ! aa)) aaa)))) \<and>
	  set_mset (dom_m (fmdrop (fst (W ! aa)) aaa)) \<subseteq>
	    clauses_pointed_to (set_mset (remove1_mset A \<A>)) WS \<union>
	     fst ` set (drop (Suc aa) W) \<and>
	  (\<forall>L \<in> set (take (Suc aa) W). fst L \<notin># dom_m (fmdrop (fst (W ! aa)) aaa))\<close>)
      apply (auto intro: rtranclp.rtrancl_into_rtrancl)[]
      apply (auto simp: GC_remap.simps Cons_nth_drop_Suc[symmetric]
          take_Suc_conv_app_nth
        dest: multi_member_split)
      apply (rule_tac x= \<open>m(fst (W ! aa) \<mapsto> x)\<close> in exI)
      apply (intro conjI)
      apply (rule_tac x=x in exI)
        apply (rule_tac x= \<open>fst (W ! aa)\<close> in exI)
        apply (force dest: rtranclp_GC_remap_ran_m_no_lost)
       apply auto
      by (smt basic_trans_rules(31) fun_upd_apply mem_Collect_eq option.simps(1) ran_def)
    subgoal by auto
    subgoal by (auto 5 5 simp: GC_remap.simps Cons_nth_drop_Suc[symmetric]
          take_Suc_conv_app_nth
        dest: multi_member_split)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition cdcl_GC_clauses_prog_single_wl
  :: \<open>'v clauses_l \<Rightarrow> ('v literal \<Rightarrow> 'v watched) \<Rightarrow> 'v \<Rightarrow>
         'v clauses_l \<Rightarrow> ('v clauses_l \<times> 'v clauses_l \<times> ('v literal \<Rightarrow> 'v watched)) nres\<close>
where
\<open>cdcl_GC_clauses_prog_single_wl = (\<lambda>N WS A N'. do {
    L \<leftarrow> RES {Pos A, Neg A};
    (N, N') \<leftarrow> cdcl_GC_clauses_prog_copy_wl_entry N (WS L) L N';
    let WS = WS(L := []);
    (N, N') \<leftarrow> cdcl_GC_clauses_prog_copy_wl_entry N (WS (-L)) (-L) N';
    let WS = WS(-L := []);
    RETURN (N, N', WS)
  })\<close>

lemma cdcl_GC_clauses_prog_single_wl_removed:
  \<open>\<forall>L\<in>set (W (Pos A)). fst L \<notin># dom_m aaa \<Longrightarrow>
       \<forall>L\<in>set (W (Neg A)). fst L \<notin># dom_m a \<Longrightarrow>
       GC_remap\<^sup>*\<^sup>* (aaa, ma, baa) (a, mb, b) \<Longrightarrow>
       set_mset (dom_m a) \<subseteq> clauses_pointed_to (set_mset (negs \<A> + poss \<A> - {#Neg A, Pos A#})) W \<Longrightarrow>
       xa \<in># dom_m a \<Longrightarrow>
       xa \<in> clauses_pointed_to (Neg ` set_mset (remove1_mset A \<A>) \<union> Pos ` set_mset (remove1_mset A \<A>))
              (W(Pos A := [], Neg A := []))\<close>
  \<open>\<forall>L\<in>set (W (Neg A)). fst L \<notin># dom_m aaa \<Longrightarrow>
       \<forall>L\<in>set (W (Pos A)). fst L \<notin># dom_m a \<Longrightarrow>
       GC_remap\<^sup>*\<^sup>* (aaa, ma, baa) (a, mb, b) \<Longrightarrow>
       set_mset (dom_m a) \<subseteq> clauses_pointed_to (set_mset (negs \<A> + poss \<A> - {#Pos A, Neg A#})) W \<Longrightarrow>
       xa \<in># dom_m a \<Longrightarrow>
       xa \<in> clauses_pointed_to
              (Neg ` set_mset (remove1_mset A \<A>) \<union> Pos ` set_mset (remove1_mset A \<A>))
              (W(Neg A := [], Pos A := []))\<close>
  supply poss_remove_Pos[simp] negs_remove_Neg[simp]
  by (case_tac [!] \<open>A \<in># \<A>\<close>)
    (fastforce simp: clauses_pointed_to_def
      dest!: multi_member_split
      dest: rtranclp_GC_remap_ran_m_no_lost)+

lemma cdcl_GC_clauses_prog_single_wl:
  fixes A :: \<open>'v\<close> and WS :: \<open>'v literal \<Rightarrow> 'v watched\<close> and
    N0 :: \<open>'v clauses_l\<close>
  assumes \<open>ran m \<subseteq> set_mset (dom_m N0') \<and>
	  (\<forall>L\<in>dom m. L \<notin># (dom_m N0)) \<and>
	  set_mset (dom_m N0) \<subseteq>
	    clauses_pointed_to (set_mset (negs \<A> + poss \<A>)) W \<and>
          0 \<notin># dom_m N0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_single_wl N0 W A N0' \<le>
      SPEC(\<lambda>(N, N', WS'). \<exists>m'. GC_remap\<^sup>*\<^sup>* (N0, m, N0') (N, m', N') \<and>
	  ran m' \<subseteq> set_mset (dom_m N') \<and>
	  (\<forall>L\<in>dom m'. L \<notin># dom_m N) \<and>
	  WS' (Pos A) = [] \<and> WS' (Neg A) = [] \<and>
	  (\<forall>L. L \<noteq> Pos A \<longrightarrow> L \<noteq> Neg A \<longrightarrow> W L = WS' L) \<and>
	  set_mset (dom_m N) \<subseteq>
	    clauses_pointed_to
	      (set_mset (negs (remove1_mset A \<A>) + poss (remove1_mset A \<A>))) WS' \<and>
          0 \<notin># dom_m N'
	  )\<close>
proof -
  have [simp]: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Neg A, Pos A#} =
   negs \<A> + poss \<A>\<close>
    by (induction \<A>) auto
  have [simp]: \<open>A \<notin># \<A> \<Longrightarrow> negs \<A> + poss \<A> - {#Pos A, Neg A#} =
   negs \<A> + poss \<A>\<close>
    by (induction \<A>)  auto
  show ?thesis
    unfolding cdcl_GC_clauses_prog_single_wl_def
    apply (refine_vcg)
    subgoal for x (*TODO proof*)
      apply (rule order_trans, rule cdcl_GC_clauses_prog_copy_wl_entry[of _ _ _
            \<open>negs \<A> + poss \<A>\<close>])
       apply(solves \<open>use assms in auto\<close>)
      apply (rule RES_rule)
      apply (refine_vcg)
      apply clarify
      subgoal for aa ba aaa baa ma
        apply (rule order_trans,
            rule cdcl_GC_clauses_prog_copy_wl_entry[of ma _ _
              \<open>remove1_mset x (negs \<A> + poss \<A>)\<close>])
         apply (solves \<open>auto simp: clauses_pointed_to_remove1_if\<close>)[]
        unfolding Let_def
        apply (rule RES_rule)
        apply clarsimp
        apply (simp add: eq_commute[of \<open>Neg _\<close>]
            uminus_lit_swap clauses_pointed_to_remove1_if)
        apply auto
         apply (rule_tac x=mb in exI)
         apply (auto dest!:
            simp: clauses_pointed_to_remove1_if
            clauses_pointed_to_remove1_if2
            clauses_pointed_to_remove1_if2_eq)
         apply (subst (asm) clauses_pointed_to_remove1_if2_eq)
          apply (force dest: rtranclp_GC_remap_ran_m_no_lost)
         apply (auto intro!: cdcl_GC_clauses_prog_single_wl_removed)[]
         apply (rule_tac x=mb in exI)
         apply (auto dest: multi_member_split[of A]
            simp: clauses_pointed_to_remove1_if
            clauses_pointed_to_remove1_if2
            clauses_pointed_to_remove1_if2_eq)
         apply (subst (asm) clauses_pointed_to_remove1_if2_eq)
          apply (force dest: rtranclp_GC_remap_ran_m_no_lost)
        apply (auto intro!: cdcl_GC_clauses_prog_single_wl_removed)[]
        done
    done
    done
qed


definition (in -)cdcl_GC_clauses_prog_wl_inv
  :: \<open>'v multiset \<Rightarrow> 'v clauses_l \<Rightarrow>
    'v multiset \<times> ('v clauses_l \<times> 'v clauses_l \<times> ('v literal \<Rightarrow> 'v watched)) \<Rightarrow> bool\<close>
where
\<open>cdcl_GC_clauses_prog_wl_inv \<A> N0 = (\<lambda>(\<B>, (N, N', WS)). \<B> \<subseteq># \<A> \<and>
  (\<forall>A \<in> set_mset \<A> - set_mset \<B>. (WS (Pos A) = []) \<and> WS (Neg A) = []) \<and>
  0 \<notin># dom_m N' \<and>
  (\<exists>m. GC_remap\<^sup>*\<^sup>* (N0, (\<lambda>_. None), fmempty) (N, m, N')\<and>
      ran m \<subseteq> set_mset (dom_m N') \<and>
      (\<forall>L\<in>dom m. L \<notin># dom_m N) \<and>
      set_mset (dom_m N) \<subseteq> clauses_pointed_to (Neg ` set_mset \<B> \<union> Pos ` set_mset \<B>) WS))\<close>

definition cdcl_GC_clauses_prog_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>cdcl_GC_clauses_prog_wl = (\<lambda>(M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS). do {
    ASSERT(cdcl_GC_clauses_pre_wl (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS));
    \<A> \<leftarrow> SPEC(\<lambda>\<A>. set_mset \<A> = set_mset (all_init_atms_st (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS)));
    (_, (N, N', WS)) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_GC_clauses_prog_wl_inv \<A> N\<^sub>0\<^esup>
      (\<lambda>(\<B>, _). \<B> \<noteq> {#})
      (\<lambda>(\<B>, (N, N', WS)). do {
        ASSERT(\<B> \<noteq> {#});
        A \<leftarrow> SPEC (\<lambda>A. A \<in># \<B>);
        (N, N', WS) \<leftarrow> cdcl_GC_clauses_prog_single_wl N WS A N';
        RETURN (remove1_mset A \<B>, (N, N', WS))
      })
      (\<A>, (N\<^sub>0, fmempty, WS));
    RETURN (M, N', D, NE, UE, NS, US, N0, U0, Q, WS)
  })\<close>


lemma cdcl_GC_clauses_prog_wl:
  assumes \<open>((M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS), S) \<in> state_wl_l None \<and>
    correct_watching'' (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS) \<and> cdcl_GC_clauses_pre S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS) \<and>
   set_mset (dom_m N\<^sub>0) \<subseteq> clauses_pointed_to
      (Neg ` set_mset (all_init_atms N\<^sub>0 (NE+NS+N0)) \<union> Pos ` set_mset (all_init_atms N\<^sub>0 (NE+NS+N0))) WS\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS) \<le>
      (SPEC(\<lambda>(M', N', D', NE', UE', NS', US', N0', U0', Q', WS').
         (M', D', NE', UE', NS', US', N0', U0', Q') = (M, D, NE, UE, NS, US, N0, U0, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N\<^sub>0, (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N' \<and> (\<forall>L \<in># all_init_lits N\<^sub>0 (NE+NS+N0). WS' L = [])))\<close>
proof -
  show ?thesis
    supply[[goals_limit=1]]
    unfolding cdcl_GC_clauses_prog_wl_def
    apply (refine_vcg
      WHILEIT_rule[where R = \<open>measure (\<lambda>(\<A>::'v multiset, (_::'v clauses_l, _ ::'v clauses_l,
          _:: 'v literal \<Rightarrow> 'v watched)). size \<A>)\<close>])
    subgoal
      using assms
      unfolding cdcl_GC_clauses_pre_wl_def
      by blast
    subgoal by auto
    subgoal using assms unfolding cdcl_GC_clauses_prog_wl_inv_def by (auto simp: all_init_atms_st_def)
    subgoal by auto
    subgoal for a b aa ba ab bb ac bc ad bd ae be af bf ag bg ah bh ai bi x s aj bj ak bk al bl xa
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      apply clarify
      apply (rule order_trans,
         rule_tac m=m and \<A>=aj in cdcl_GC_clauses_prog_single_wl)
      subgoal by (auto simp: all_init_atms_st_def)
      subgoal
        apply (rule RES_rule)
        apply clarify
        apply (rule RETURN_rule)
        apply clarify
        apply (intro conjI)
             apply (solves auto)
            apply (solves \<open>auto dest!: multi_member_split\<close>)
           apply (solves auto)
          apply (rule_tac x=m' in exI)
          apply (solves \<open>auto\<close>)[]
         apply (simp_all add: size_Diff1_less)[]
        done
      done
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by auto
    subgoal
      unfolding cdcl_GC_clauses_prog_wl_inv_def
      by (intro ballI, rename_tac L, case_tac L)
        (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_init_atms_def all_init_atms_st_def
          simp del: all_init_atms_def[symmetric]
          dest!: multi_member_split)
  done
qed


lemma cdcl_GC_clauses_prog_wl2:
  assumes \<open>((M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS), S) \<in> state_wl_l None \<and>
    correct_watching'' (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS) \<and> cdcl_GC_clauses_pre S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n' (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS) \<and>
   set_mset (dom_m N\<^sub>0) \<subseteq> clauses_pointed_to
    (Neg ` set_mset (all_init_atms N\<^sub>0 (NE+NS+N0)) \<union> Pos ` set_mset (all_init_atms N\<^sub>0 (NE+NS+N0))) WS\<close>
  \<open>N\<^sub>0 = N\<^sub>0'\<close>
  shows
    \<open>cdcl_GC_clauses_prog_wl (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, WS) \<le> \<Down> Id
      (SPEC(\<lambda>(M', N', D', NE', UE', NS', US', N0', U0', Q', WS').
         (M', D', NE', UE', NS', US', N0', U0', Q') = (M, D, NE, UE, NS, US, N0, U0, Q) \<and>
         (\<exists>m. GC_remap\<^sup>*\<^sup>* (N\<^sub>0', (\<lambda>_. None), fmempty) (fmempty, m, N')) \<and>
         0 \<notin># dom_m N' \<and> (\<forall>L \<in># all_init_lits N\<^sub>0 (NE+NS+N0). WS' L = [])))\<close>
proof -
  show ?thesis
    unfolding \<open>N\<^sub>0 = N\<^sub>0'\<close>[symmetric]
    apply (rule order_trans[OF cdcl_GC_clauses_prog_wl[OF assms(1)]])
    apply (rule RES_refine)
    apply (fastforce dest: rtranclp_GC_remap_all_init_lits)
    done
qed

lemma cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  have [refine0]:
    \<open>(x, y) \<in> ?R \<Longrightarrow> ((False, x, 0), False, y, 0) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close> for x y
    by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where
      R=\<open>bool_rel \<times>\<^sub>r {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry4]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
   subgoal by auto
    subgoal for S T U V
      unfolding cdcl_twl_stgy_restart_abs_wl_inv_def case_prod_beta
      by (fastforce simp: prod_rel_fst_snd_iff)
    subgoal by auto
    subgoal by auto
    subgoal by auto
   subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    done
qed
lemma cdcl_twl_stgy_restart_prog_early_wl_cdcl_twl_stgy_restart_prog_early_l:
    \<open>(cdcl_twl_stgy_restart_prog_early_wl, cdcl_twl_stgy_restart_prog_early_l)
  \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
  \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
   show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_wl_def cdcl_twl_stgy_restart_prog_early_l_def
     apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
        WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
       unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
       cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry4]
       cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
     subgoal by auto
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def comp_def
       by (fastforce simp: prod_rel_fst_snd_iff)
     subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
     subgoal by auto
     subgoal by auto
     subgoal by (auto simp: correct_watching_correct_watching)
    subgoal unfolding cdcl_twl_stgy_restart_abs_wl_inv_def comp_def
      by (fastforce simp: prod_rel_fst_snd_iff)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
     subgoal by auto
     done
qed


theorem cdcl_twl_stgy_restart_prog_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l[where 'a='v]
  unfolding fref_param1 apply -
  apply (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?)
  by (metis (no_types, lifting) in_pair_collect_simp nres_rel_mono subrelI)

theorem cdcl_twl_stgy_restart_prog_early_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl, cdcl_twl_stgy_restart_prog_early_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_early_wl_cdcl_twl_stgy_restart_prog_early_l[where 'a='v]
  unfolding fref_param1 apply -
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?; match_fun_rel?)
    auto


end

end
