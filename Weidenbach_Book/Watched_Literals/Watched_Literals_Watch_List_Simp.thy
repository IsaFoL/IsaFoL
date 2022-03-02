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
      cdcl_twl_restart_l_inp.intros(1)[of y Va] apply -
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
  T \<leftarrow> simplify_clauses_with_units_st_wl S';
  T \<leftarrow> mark_duplicated_binary_clauses_as_garbage_wl T;
  if get_conflict_wl T \<noteq> None then do {
    ASSERT(cdcl_twl_full_restart_wl_GC_prog_post_confl S T);
    RETURN T
  }
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
    simplify_clauses_with_units_st_wl_simplify_clause_with_units_st
    mark_to_delete_clauses_wl_mark_to_delete_clauses_l2[THEN fref_to_Down]
    cdcl_GC_clauses_wl_cdcl_GC_clauses[THEN fref_to_Down]
    )
  subgoal unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def by blast
  subgoal by (auto dest: correct_watching'_correct_watching'')
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x y S' S'a T Ta U Ua
    using cdcl_twl_full_restart_wl_GC_prog_post_correct_watching[of y Ua U]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_confl_def apply -
    by (rule exI[of _ y], rule exI[of _ Ua])
      (smt (verit, best) all_lits_st_alt_def basic_trans_rules(31) in_pair_collect_simp
         literals_are_\<L>\<^sub>i\<^sub>n'_def set_mset_set_mset_eq_iff union_iff)
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
    else if (b = GC \<or> b = INPROCESS) \<and> \<not>brk then do {
      if b \<noteq> INPROCESS then do {
        b \<leftarrow> SPEC(\<lambda>_. True);
        T \<leftarrow> (if b then cdcl_twl_full_restart_wl_prog S else cdcl_twl_full_restart_wl_GC_prog S);
        RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
      } else do {
        T \<leftarrow> cdcl_twl_full_restart_inprocess_wl_prog S;
        RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
      }
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
     else if (b = GC \<or> b = INPROCESS) \<and> \<not>brk then do {
      let _ = (b = INPROCESS);
      if b \<noteq> INPROCESS then do {
         b \<leftarrow> SPEC(\<lambda>_. True);
         T \<leftarrow> (if b then cdcl_twl_full_restart_wl_prog S else cdcl_twl_full_restart_wl_GC_prog S);
         RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
        } else do {
          T \<leftarrow> cdcl_twl_full_restart_inprocess_wl_prog S;
          RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
       }
    }
    else
       RETURN (S, last_GC, last_Restart, n)
   }\<close>
  unfolding restart_prog_wl_def Let_def
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
  \<langle>{(S, T).  (S, T) \<in> state_wl_l None \<and> (get_conflict_wl S = None \<longrightarrow> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S)} \<times>\<^sub>r nat_rel\<times>\<^sub>r nat_rel\<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<times>\<^sub>f _ \<times>\<^sub>f _ \<times>\<^sub>f _ \<times>\<^sub>f _  \<rightarrow>\<^sub>f \<langle>?R'\<rangle>nres_rel\<close>)
proof -
  have [simp]: \<open>size (learned_clss_l (get_clauses_wl a)) = size ((get_learned_clss_wl a))\<close> for a
    by (cases a, auto simp: get_learned_clss_wl_def)
  have [refine0]:
    \<open>restart_required_wl a b c d \<le> \<Down> {(b, b'). (b' = (b = GC \<or> b = INPROCESS)) \<and>
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
    by (rule RES_refine)
     auto
  have [refine0]: \<open>RETURN (b = RESTART) \<le> \<Down>bool_rel (restart_required_l a' c d)\<close>
    if \<open>(b, b') \<in> ?GC a c'\<close> \<open>(a, a') \<in> ?R\<close> \<open>(c, c') \<in> nat_rel\<close>
    for a a' b b' c c' d d' e e'
    using that
    unfolding restart_required_l_def
    by refine_rcg auto
  have [refine0]: \<open>RETURN (b = INPROCESS) \<le> \<Down> bool_rel (inprocessing_required_l x1c)\<close> for b x1c
    by (auto simp: inprocessing_required_l_def)
  show ?thesis
    supply [[goals_limit=1]]
    unfolding uncurry_def restart_prog_wl_alt_def restart_prog_l_def rewatch_clauses_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_GC_prog[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_full_twl_restart_l_prog[THEN fref_to_Down]
      cdcl_twl_full_restart_inprocess_wl_prog[THEN fref_to_Down])
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
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by (auto simp: correct_watching_correct_watching restart_abs_wl_pre_blits_in_\<L>\<^sub>i\<^sub>n)
    subgoal by auto
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
        ASSERT(\<not>brk);
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_wl T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0::'v twl_st_wl, size (get_all_learned_clss_wl S\<^sub>0), size (get_all_learned_clss_wl S\<^sub>0), 0);
    RETURN (ebrk, T)
  }\<close>

lemma cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>state_wl_l None\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  let ?S = \<open>{((brk, S), (brk', T)). (brk,brk') \<in> bool_rel \<and> (S, T) \<in> state_wl_l None \<and>
      (\<not>brk \<longrightarrow> (correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S))}\<close>
  let ?T = \<open> {((brk, S, l, m, n), ( brk', T, l', m', n')).
     ((l, m, n), (l', m', n')) \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<and>
     ((brk, S), (brk', T)) \<in> ?S}\<close>

  have [refine0]:
    \<open>(x, y) \<in> ?R \<Longrightarrow> ((False, x, 0), False, y, 0) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close> for x y
    by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R=\<open>?T\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry4]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
   subgoal by auto
    subgoal for S T U V
      unfolding cdcl_twl_stgy_restart_abs_wl_inv_def case_prod_beta
      apply (rule_tac x= \<open>T\<close>in exI)
      apply (rule_tac x= \<open>fst (snd V)\<close>in exI)
      by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_restart_prog_bounded_wl_cdcl_twl_stgy_restart_prog_bounded_l:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_wl, cdcl_twl_stgy_restart_prog_bounded_l)
    \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
       \<langle>bool_rel \<times>\<^sub>r state_wl_l None\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>_\<rangle>nres_rel\<close>)
proof -
  let ?S = \<open>{((brk, S), (brk', T)). (brk,brk') \<in> bool_rel \<and> (S, T) \<in> state_wl_l None \<and>
    (\<not>brk \<longrightarrow> (correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S))}\<close>
  let ?T = \<open> {((ebrk, brk, S, l, m, n), (ebrk', brk', T, l', m', n')).
    ((ebrk, l, m, n), (ebrk', l', m', n')) \<in> bool_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<and>
    ((brk, S), (brk', T)) \<in> ?S}\<close>
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_bounded_wl_def cdcl_twl_stgy_restart_prog_bounded_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
        WHILEIT_refine[where R=\<open>?T\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry4]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
    subgoal by auto
    subgoal for x y ebrk ebrka xa x'
      unfolding cdcl_twl_stgy_restart_abs_wl_inv_def comp_def case_prod_beta
      apply (rule_tac x= \<open>y\<close>in exI)
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close>in exI)
      by simp
    subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

theorem cdcl_twl_stgy_restart_prog_bounded_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_wl, cdcl_twl_stgy_restart_prog_bounded_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>bool_rel \<times>\<^sub>r state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_bounded_wl_cdcl_twl_stgy_restart_prog_bounded_l[where 'a='v]
  unfolding fref_param1 apply -
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?; match_fun_rel?)


lemma cdcl_twl_stgy_restart_prog_early_wl_cdcl_twl_stgy_restart_prog_early_l:
    \<open>(cdcl_twl_stgy_restart_prog_early_wl, cdcl_twl_stgy_restart_prog_early_l)
  \<in> {(S, T).  (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
  \<langle>state_wl_l None\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  let ?S = \<open>{((brk, S), (brk', T)). (brk,brk') \<in> bool_rel \<and> (S, T) \<in> state_wl_l None \<and>
    (\<not>brk \<longrightarrow> (correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S))}\<close>
  let ?T = \<open> {((ebrk, brk, S, l, m, n), (ebrk', brk', T, l', m', n')).
    ((ebrk, l, m, n), (ebrk', l', m', n')) \<in> bool_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<and>
    ((brk, S), (brk', T)) \<in> ?S}\<close>
  let ?U = \<open> {((brk, S, l, m, n), (brk', T, l', m', n')).
    ((l, m, n), (l', m', n')) \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<and>
    ((brk, S), (brk', T)) \<in> ?S}\<close>
   show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_wl_def cdcl_twl_stgy_restart_prog_early_l_def
     apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R=\<open>?U\<close>]
        WHILEIT_refine[where R=\<open>?T\<close>]
       unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
       cdcl_twl_full_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry4]
       cdcl_twl_o_prog_wl_spec[THEN fref_to_Down])
     subgoal by auto
    subgoal for x y ebrk ebrka xa x'
      unfolding cdcl_twl_stgy_restart_abs_wl_inv_def comp_def case_prod_beta
      apply (rule_tac x= \<open>y\<close>in exI)
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close>in exI)
      by simp
     subgoal by auto
    subgoal by (auto simp: correct_watching_correct_watching)
    subgoal by auto
     subgoal by auto
     subgoal by auto
     subgoal by (auto simp: correct_watching_correct_watching)
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
    x1f x2f x1g x2g x1h x2h x1i x2i xb x'a
      unfolding cdcl_twl_stgy_restart_abs_wl_inv_def comp_def case_prod_beta
      apply (rule_tac x= \<open>fst (snd (snd x'))\<close>in exI)
      apply (rule_tac x= \<open>(fst (snd x'a))\<close>in exI)
      by simp
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
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?)

theorem cdcl_twl_stgy_restart_prog_early_wl_spec:
  \<open>(cdcl_twl_stgy_restart_prog_early_wl, cdcl_twl_stgy_restart_prog_early_l) \<in> {(S::'v twl_st_wl, S').
       (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S} \<rightarrow> \<langle>state_wl_l None\<rangle>nres_rel\<close>
   (is \<open>?o \<in> ?A \<rightarrow> \<langle>?B\<rangle> nres_rel\<close>)
  using cdcl_twl_stgy_restart_prog_early_wl_cdcl_twl_stgy_restart_prog_early_l[where 'a='v]
  unfolding fref_param1 apply -
  by (match_spec; match_fun_rel+; (fast intro: nres_rel_mono)?; match_fun_rel?)


end

end
