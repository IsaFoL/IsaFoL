theory Watched_Literals_Watch_List_Restart
  imports Watched_Literals_List_Restart Watched_Literals_Watch_List
begin

fun (in -) partial_correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE + UE).
        (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (watched_l (N\<propto>i))))\<close>

lemma (in -) \<open>correct_watching S \<Longrightarrow> partial_correct_watching S\<close>
  by (cases S)
    (auto simp: correct_watching.simps partial_correct_watching.simps clause_to_update_def
    simp del: set_mset_mset dest: in_set_mset_eq_in)

term remove_all_annot_true_clause_imp
definition remove_all_annot_true_clause_imp_wl
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl = (\<lambda>L (M, N, D, NE, UE, Q, W). do {
    let xs = W L;
    (_, N, NE) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, NE). i < length xs)
      (\<lambda>(i, N, NE). do {
          ASSERT(i < length xs);
          if xs!i \<in># dom_m N
          then do {
            (N, NE) \<leftarrow> remove_all_annot_true_clause_one_imp (xs!i, N, NE);
            RETURN (i+1, N, NE)
          }
          else
            RETURN (i+1, N, NE)
      })
      (0, N, NE);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

lemma reduce_dom_clauses_fmdrop:
  \<open>reduce_dom_clauses N0 N \<Longrightarrow> reduce_dom_clauses N0 (fmdrop C N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: reduce_dom_clauses_def distinct_mset_remove1_All)

lemma \<open>(uncurry remove_all_annot_true_clause_imp_wl, uncurry remove_all_annot_true_clause_imp) \<in>
   Id \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
proof -
  have H: \<open>((0, x1i, x1k), 0, x1b, x1d) \<in> nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    if \<open>(x1i, x1b) \<in> Id\<close> and  \<open>(x1k, x1d) \<in> Id\<close>
    for x1i x1k x1b x1d
    using that by auto
  have [refine0]: \<open>remove_all_annot_true_clause_one_imp (C, N0, NE) \<le>
        \<Down> {((N, NE), (N', NE')). N = N' \<and> NE = NE' \<and>
            (C \<in># dom_m N \<longrightarrow> N = fmdrop C N0)}
          (remove_all_annot_true_clause_one_imp (C', N', NE'))\<close>
    if \<open>(C, C') \<in> Id\<close> and \<open>(N0, N') \<in> Id\<close> and \<open>(NE, NE') \<in> Id\<close>
    for C C' N N' NE NE' N0
    using that unfolding remove_all_annot_true_clause_one_imp_def by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding uncurry_def remove_all_annot_true_clause_imp_wl_def
      remove_all_annot_true_clause_imp_def
    subgoal for LS LT
      apply (cases LS; cases LT)
      subgoal for L M N0 D NE UE Q W L' M' N' D' NE' UE' Q' W'
      apply (refine_rcg H
        WHILET_refine[where R=\<open>
          {((i, N, NE), (i', N', NE')). i = i' \<and> N = N' \<and> NE = NE' \<and>
            partial_correct_watching (M, N, D, NE, UE, Q, W) \<and>
            reduce_dom_clauses N0 N}\<close>])
    subgoal apply (auto simp: state_wl_l_def partial_correct_watching.simps) sorry
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    subgoal apply (auto simp: state_wl_l_def reduce_dom_clauses_fmdrop) sorry
    subgoal by (auto simp: state_wl_l_def)
    subgoal by (auto simp: state_wl_l_def)
    oops

definition remove_one_annot_true_clause_one_imp_wl
  :: \<open>nat \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl = (\<lambda>i (M, N, D, NE, UE, Q, W). do {
      ASSERT(i < length M);
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev M)!i = Propagated L C);
      if C = 0 then RETURN (i+1, M, N, D, NE, UE, Q, W)
      else do {
        ASSERT(C \<in># dom_m N);
        M \<leftarrow> replace_annot_in_trail_spec M L;
        (N', C, b) \<leftarrow> extract_and_remove N C;
        let S = (if b then (M, N', D, add_mset (mset C) NE, UE, Q, W)
                      else (M, N', D, NE, add_mset (mset C) UE, Q, W));
        S \<leftarrow> remove_all_annot_true_clause_imp_wl L S;
        RETURN (i+1, S)
      }
  })\<close>

definition remove_one_annot_true_clause_imp_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl = (\<lambda>S. do {
    (_, S) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, S). i < length (get_trail_wl S) \<and> \<not>is_decided (get_trail_wl S!i))
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl i S)
      (0, S);
    RETURN S
  })\<close>

definition collect_valid_indices_wl where
  \<open>collect_valid_indices_wl S = SPEC (\<lambda>N. mset N \<subseteq># dom_m (get_clauses_wl S) \<and> distinct N)\<close>

definition mark_to_delete_clauses_wl :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl  = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    xs \<leftarrow> collect_valid_indices_wl (M, N, D, NE, UE, Q, W);
    (_, _, N) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(brk, i, N). \<not>brk \<and> i < length xs)
      (\<lambda>(brk, i, N). do {
        can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> (Propagated (N\<propto>(xs!i)!0) (xs!i) \<notin> set M) \<and> \<not>irred N (xs!i));
        brk \<leftarrow> SPEC(\<lambda>_. True);
        ASSERT(i < length xs);
        if can_del
        then
          RETURN (brk, i+1, fmdrop (xs!i) N)
        else
          RETURN (brk, i+1, N)
      })
      (False, 0, N);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

  

lemma \<open>(uncurry remove_all_annot_true_clause_imp_wl, uncurry remove_all_annot_true_clause_imp) \<in>
   Id \<times>\<^sub>f {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding uncurry_def remove_all_annot_true_clause_imp_wl_def
    remove_all_annot_true_clause_imp_def
  apply (refine_vcg
    WHILET_refine[where R=\<open>bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
       {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<close>])
  
thm WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
       {(S, T). (S, T) \<in> state_wl_l None \<and> partial_correct_watching S}\<close>]
  oops

text \<open>Most important point: We assume that the new watch list is correct.\<close>
inductive cdcl_twl_restart_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
restart_trail:
   \<open>cdcl_twl_restart_wl (M, N, None, NE, UE, Q, W)
       (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
  if
    \<open>valid_trail_reduction M M'\<close> and
    \<open>init_clss_lf N = init_clss_lf N' + NE'\<close> and
    \<open>learned_clss_lf N' + UE' \<subseteq># learned_clss_lf N\<close> and
    \<open>\<forall>E\<in># (NE'+UE'). \<exists>L\<in>set E. L \<in> lits_of_l M \<and> get_level M L = 0\<close> and
    \<open>\<forall>L E E' . Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E > 0  \<longrightarrow> E' > 0 \<longrightarrow>
        E \<in># dom_m N' \<and> N' \<propto> E = N \<propto> E'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E = 0 \<longrightarrow> E' \<noteq> 0 \<longrightarrow>
       mset (N \<propto> E') \<in># NE + mset `# NE' + UE + mset `# UE'\<close> and
    \<open>\<forall>L E E'. Propagated L E \<in> set M' \<longrightarrow> Propagated L E' \<in> set M \<longrightarrow> E' = 0 \<longrightarrow> E = 0\<close> and
    \<open>0 \<notin># dom_m N'\<close> and
    \<open>if length M = length M' then Q = Q' else Q' = {#}\<close> and
    \<open>correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>

lemma cdcl_twl_restart_wl_cdcl_twl_restart_l_spec:
  assumes
    \<open>cdcl_twl_restart_wl S S'\<close> and
    \<open>(S, T) \<in> state_wl_l None\<close> and
    \<open>correct_watching S\<close>
  shows \<open>\<exists>T'. (S' , T') \<in> state_wl_l None \<and> cdcl_twl_restart_l T T' \<and> correct_watching S'\<close>
  using assms
proof (induction rule: cdcl_twl_restart_wl.induct)
  case (restart_trail M M' N N' NE' UE' NE UE Q Q' W' W)
  let ?T' = \<open>(M', N', None, NE + mset `# NE', UE + mset `# UE', {#}, Q')\<close>
  have \<open>cdcl_twl_restart_l T ?T'\<close>
    using restart_trail
    by (auto simp: cdcl_twl_restart_l.simps state_wl_l_def)
  moreover have \<open>((M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W') , ?T') \<in> state_wl_l None\<close>
    using restart_trail
    by (auto simp: cdcl_twl_restart_l.simps state_wl_l_def)
  moreover have \<open>correct_watching (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
    using restart_trail
    by fast
  ultimately show ?case
    by blast
qed

lemma restart_prog_wl_restart_prog_l:
  \<open>(\<lambda>S. SPEC (cdcl_twl_restart_wl S), \<lambda>S. SPEC (cdcl_twl_restart_l S)) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule RES_refine)
  using cdcl_twl_restart_wl_cdcl_twl_restart_l_spec by blast

definition (in -) get_learned_clss_wl where
  \<open>get_learned_clss_wl S = learned_clss_lf (get_clauses_wl S)\<close>

context twl_restart
begin

definition restart_required_wl :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_wl S n = SPEC (\<lambda>b. b \<longrightarrow> size (get_learned_clss_wl S) > f n)\<close>

definition restart_prog_wl_pre :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>restart_prog_wl_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> restart_prog_l_pre S'
      \<and> correct_watching S)\<close>

definition restart_prog_wl :: "'v twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_wl \<times> nat) nres" where
  \<open>restart_prog_wl S n brk = do {
     ASSERT(restart_prog_wl_pre S);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_wl S T);
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>


lemma (in -)[twl_st_l]:
  \<open>(S, S') \<in> state_wl_l None \<Longrightarrow> get_learned_clss_l S' = get_learned_clss_wl S\<close>
  by (auto simp: get_learned_clss_wl_def get_learned_clss_l_def state_wl_l_def)

lemma restart_required_wl_restart_required_l:
  \<open>(uncurry restart_required_wl, uncurry restart_required_l) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None} \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f
    \<langle>bool_rel\<rangle> nres_rel\<close>
  unfolding restart_required_wl_def restart_required_l_def uncurry_def
  by (intro frefI nres_relI)
   (auto simp: state_wl_l_def get_learned_clss_l_def get_learned_clss_wl_def)


lemma restart_prog_wl_restart_prog_l:
  \<open>(uncurry2 restart_prog_wl, uncurry2 restart_prog_l) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}
        \<times>\<^sub>f  nat_rel  \<times>\<^sub>f  bool_rel \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}
        \<times>\<^sub>f nat_rel\<rangle> nres_rel\<close>
    unfolding restart_prog_wl_def restart_prog_l_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      restart_required_wl_restart_required_l[THEN fref_to_Down_curry]
      restart_prog_wl_restart_prog_l[THEN fref_to_Down])
    subgoal for Snb Snb'
     unfolding restart_prog_wl_pre_def
     by (rule exI[of _ \<open>fst (fst (Snb'))\<close>]) simp
    subgoal by simp
    subgoal by simp -- \<open>If condition\<close>
    subgoal by simp
    subgoal by simp
    subgoal by auto
    done


definition cdcl_twl_stgy_restart_prog_wl_inv where
  \<open>cdcl_twl_stgy_restart_prog_wl_inv S\<^sub>0 brk T n \<equiv>
    (\<exists>S\<^sub>0' T'.
       (S\<^sub>0, S\<^sub>0') \<in> state_wl_l None \<and>
       (T, T') \<in> state_wl_l None \<and>
       cdcl_twl_stgy_restart_prog_l_inv S\<^sub>0' brk T' n \<and>
       correct_watching T)\<close>

definition cdcl_twl_stgy_restart_prog_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>cdcl_twl_stgy_restart_prog_wl S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_prog_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl T;
        (T, n) \<leftarrow> restart_prog_wl T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0, 0);
    RETURN T
  }\<close>

lemma cdcl_twl_stgy_restart_prog_wl_cdcl_twl_stgy_restart_prog_l:
  \<open>(cdcl_twl_stgy_restart_prog_wl, cdcl_twl_stgy_restart_prog_l) \<in>
     {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_def cdcl_twl_stgy_restart_prog_l_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
      (S, S') \<in> state_wl_l None \<and> correct_watching S \<and> brk = brk' \<and> n = n'}\<close>]
      unit_propagation_outer_loop_wl_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_spec[THEN fref_to_Down]
      restart_prog_wl_restart_prog_l[THEN fref_to_Down_curry2])
  subgoal by simp
  subgoal for x y xa x' x1 x2 x1a x2a
    unfolding cdcl_twl_stgy_restart_prog_wl_inv_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd x')\<close> in exI)
    by auto
  subgoal by fast
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_l_inv_def
      cdcl_twl_stgy_restart_prog_wl_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st twl_st_wl)
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by auto
  subgoal by auto
  done

end

end
