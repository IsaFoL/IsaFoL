theory Watched_Literals_Algorithm
  imports
    Watched_Literals_Transition_System
    WB_More_Refinement
begin


section \<open>First Refinement: Deterministic Rule Application\<close>

subsection \<open>Unit Propagation Loops\<close>

definition set_conflicting :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_conflicting = (\<lambda>C (M, N, U, D, NE, UE, WS, Q). (M, N, U, Some (clause C), NE, UE, {#}, {#}))\<close>

definition propagate_lit :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_lit = (\<lambda>L' C (M, N, U, D, NE, UE, WS, Q).
      (Propagated L' (clause C) # M, N, U, D, NE, UE, WS, add_mset (-L') Q))\<close>

definition update_clauseS :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>update_clauseS = (\<lambda>L C (M, N, U, D, NE, UE, WS, Q). do {
        K \<leftarrow> SPEC (\<lambda>L. L \<in># unwatched C \<and> -L \<notin> lits_of_l M);
        if K \<in> lits_of_l M
        then RETURN (M, N, U, D, NE, UE, WS, Q)
        else do {
          (N', U') \<leftarrow> SPEC (\<lambda>(N', U'). update_clauses (N, U) C L K (N', U'));
          RETURN (M, N', U', D, NE, UE, WS, Q)
        }
  })\<close>

definition unit_propagation_inner_loop_body :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow>
  'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>unit_propagation_inner_loop_body = (\<lambda>L C S. do {
    do {
      bL' \<leftarrow> SPEC (\<lambda>K. K \<in># clause C);
      if bL' \<in> lits_of_l (get_trail S)
      then RETURN S
      else do {
        L' \<leftarrow> SPEC (\<lambda>K. K \<in># watched C - {#L#});
        ASSERT (watched C = {#L, L'#});
        if L' \<in> lits_of_l (get_trail S)
        then RETURN S
        else
          if \<forall>L \<in># unwatched C. -L \<in> lits_of_l (get_trail S)
          then
            if -L' \<in> lits_of_l (get_trail S)
            then do {RETURN (set_conflicting C S)}
            else do {RETURN (propagate_lit L' C S)}
          else do {
            update_clauseS L C S
        }
        }
    }
  })
\<close>

definition unit_propagation_inner_loop :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>unit_propagation_inner_loop S\<^sub>0 = do {
    n \<leftarrow> SPEC(\<lambda>_::nat. True);
    (S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(S, n). twl_struct_invs S \<and> twl_stgy_invs S \<and> cdcl_twl_cp\<^sup>*\<^sup>* S\<^sub>0 S \<and>
          (clauses_to_update S \<noteq> {#} \<or> n > 0 \<longrightarrow> get_conflict S = None)\<^esup>
      (\<lambda>(S, n). clauses_to_update S \<noteq> {#} \<or> n > 0)
      (\<lambda>(S, n). do {
        b \<leftarrow> SPEC(\<lambda>b. (b \<longrightarrow> n > 0) \<and> (\<not>b \<longrightarrow> clauses_to_update S \<noteq> {#}));
        if \<not>b then do {
          ASSERT(clauses_to_update S \<noteq> {#});
          (L, C) \<leftarrow> SPEC (\<lambda>C. C \<in># clauses_to_update S);
          let S' = set_clauses_to_update (clauses_to_update S - {#(L, C)#}) S;
          T \<leftarrow> unit_propagation_inner_loop_body L C S';
          RETURN (T, if get_conflict T = None then n else 0)
        } else do { \<^cancel>\<open>This branch allows us to do skip some clauses.\<close>
          RETURN (S, n - 1)
        }
      })
      (S\<^sub>0, n);
    RETURN S
  }
\<close>

lemma unit_propagation_inner_loop_body:
  fixes S :: \<open>'v twl_st\<close>
  assumes
    \<open>clauses_to_update S \<noteq> {#}\<close> and
    x_WS: \<open>(L, C) \<in># clauses_to_update S\<close> and
    inv: \<open>twl_struct_invs S\<close> and
    inv_s: \<open>twl_stgy_invs S\<close> and
    confl: \<open>get_conflict S = None\<close>
  shows
     \<open>unit_propagation_inner_loop_body L C
          (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)
        \<le> (SPEC (\<lambda>T'.  twl_struct_invs T' \<and> twl_stgy_invs T' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S T' \<and>
           (T', S) \<in> measure (size \<circ> clauses_to_update)))\<close> (is ?spec) and
    \<open>nofail (unit_propagation_inner_loop_body L C
       (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S))\<close> (is ?fail)
proof -
  obtain M N U D NE UE WS Q where
    S: \<open>S = (M, N, U, D, NE, UE, WS, Q)\<close>
    by (cases S) auto

  have \<open>C \<in># N + U\<close> and struct: \<open>struct_wf_twl_cls C\<close> and L_C: \<open>L \<in># watched C\<close>
    using inv multi_member_split[OF x_WS]
    unfolding twl_struct_invs_def twl_st_inv.simps S
    by force+
  show ?fail
    unfolding unit_propagation_inner_loop_body_def Let_def S
    by (cases C) (use struct L_C in \<open>auto simp: refine_pw_simps S size_2_iff update_clauseS_def\<close>)
  note [[goals_limit=15]]
  show ?spec
    using assms unfolding unit_propagation_inner_loop_body_def update_clause.simps
  proof (refine_vcg; (unfold prod.inject clauses_to_update.simps set_clauses_to_update.simps
        ball_simps)?;  clarify?; (unfold triv_forall_equality)?)
    fix L' :: \<open>'v literal\<close>
    assume
      \<open>clauses_to_update S \<noteq> {#}\<close> and
      WS: \<open>(L, C) \<in># clauses_to_update S\<close> and
      twl_inv: \<open>twl_struct_invs S\<close>
    have \<open>C \<in># N + U\<close> and struct: \<open>struct_wf_twl_cls C\<close> and L_C: \<open>L \<in># watched C\<close>
      using twl_inv WS unfolding twl_struct_invs_def twl_st_inv.simps S by (auto; fail)+

    define WS' where \<open>WS' = WS - {#(L, C)#}\<close>
    have WS_WS': \<open>WS = add_mset (L, C) WS'\<close>
      using WS unfolding WS'_def S by auto

    have D: \<open>D = None\<close>
      using confl S by auto

    let ?S' = \<open>(M, N, U, None, NE, UE, add_mset (L, C) WS', Q)\<close>
    let ?T = \<open>(set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
    let ?T' = \<open>(M, N, U, None, NE, UE, WS', Q)\<close>

    { \<comment> \<open>blocking literal\<close>
      fix K'
      assume
          K': \<open>K' \<in># clause C\<close> and
          L': \<open>K' \<in> lits_of_l (get_trail ?T)\<close>

      have \<open>cdcl_twl_cp ?S' ?T'\<close>
        by (rule cdcl_twl_cp.delete_from_working) (use L' K' S in simp_all)

      then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
        using L' D by (simp add: S WS_WS')
      show \<open>twl_struct_invs ?T\<close>
        using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

      show \<open>twl_stgy_invs ?T\<close>
        using cdcl inv_s inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)

      show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
        using D WS_WS' cdcl by auto

      show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
        by (simp add: WS'_def[symmetric] WS_WS' S)

    }

    assume L': \<open>L' \<in># remove1_mset L (watched C)\<close>
    show watched: \<open>watched C = {#L, L'#}\<close>
      by (cases C) (use struct L_C L' in \<open>auto simp: size_2_iff\<close>)
    then have L_C': \<open>L \<in># clause C\<close> and L'_C': \<open>L' \<in># clause C\<close>
      by (cases C; auto; fail)+

    { \<comment> \<open>if \<^term>\<open>L' \<in> lits_of_l M\<close>, then:\<close>
      assume L': \<open>L' \<in> lits_of_l (get_trail ?T)\<close>

      have \<open>cdcl_twl_cp ?S' ?T'\<close>
        by (rule cdcl_twl_cp.delete_from_working) (use L' L'_C' watched S in simp_all)

      then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
        using L' watched D by (simp add: S WS_WS')
      show \<open>twl_struct_invs ?T\<close>
        using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

      show \<open>twl_stgy_invs ?T\<close>
        using cdcl inv_s inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)

      show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
        using D WS_WS' cdcl by auto

      show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
        by (simp add: WS'_def[symmetric] WS_WS' S)

    }
      \<comment> \<open>if \<^term>\<open>L' \<in> lits_of_l M\<close>, else:\<close>
    let ?M = \<open>get_trail ?T\<close>
    assume L': \<open>L' \<notin> lits_of_l ?M\<close>
    {
      { \<comment> \<open>if \<^term>\<open>\<forall>L \<in># unwatched C. -L \<in> lits_of_l ?M\<close>, then\<close>
        assume unwatched: \<open>\<forall>L\<in>#unwatched C. - L \<in> lits_of_l ?M\<close>

        { \<comment> \<open>if \<^term>\<open>-L' \<in> lits_of_l ?M\<close> then\<close>
          let ?T' = \<open>(M, N, U, Some (clause C), NE, UE, {#}, {#})\<close>
          let ?T = \<open>set_conflicting C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
          assume uL': \<open>-L' \<in> lits_of_l ?M\<close>
          have cdcl: \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.conflict) (use uL' L' watched unwatched S in simp_all)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            using uL' L' watched unwatched by (simp add: set_conflicting_def WS_WS' S D)

          show \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding WS_WS'
            by (force intro: cdcl_twl_cp_twl_struct_invs)
          show \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding WS_WS'
            by (force intro: cdcl_twl_cp_twl_stgy_invs)
          show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using D WS_WS' cdcl S by auto
          show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
            by (simp add: S WS'_def[symmetric] WS_WS' set_conflicting_def)
        }


        { \<comment> \<open>if \<^term>\<open>-L' \<in> lits_of_l M \<close> else\<close>
          let ?S = \<open>(M, N, U, D, NE, UE, WS, Q)\<close>
          let ?T' = \<open>(Propagated L' (clause C) # M, N, U, None, NE, UE, WS', add_mset (- L') Q)\<close>
          let ?S' = \<open>(M, N, U, None, NE, UE, add_mset (L, C) WS', Q)\<close>
          let ?T = \<open>propagate_lit L' C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
          assume uL': \<open>- L' \<notin> lits_of_l ?M\<close>

          have undef: \<open>undefined_lit M L'\<close>
            using uL' L' by (auto simp: S defined_lit_map lits_of_def atm_of_eq_atm_of)

          have cdcl: \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.propagate) (use uL' L' undef watched unwatched D S in simp_all)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            using uL' L' undef watched unwatched D S WS_WS' by (simp add: propagate_lit_def)

          show \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

          show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using cdcl D WS_WS' by force
          show \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)
          show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
            by (simp add: WS'_def[symmetric] WS_WS' S propagate_lit_def)
        }
      }

      fix La
\<comment> \<open>if \<^term>\<open>\<forall>L \<in># unwatched C. -L \<in> lits_of_l M\<close>, else\<close>
      {
        let ?S = \<open>(M, N, U, D, NE, UE, WS, Q)\<close>
        let ?S' = \<open>(M, N, U, None, NE, UE, add_mset (L, C) WS', Q)\<close>
        let ?T = \<open>set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S\<close>
        fix K M' N' U' D' WS'' NE' UE' Q' N'' U''
        have \<open>update_clauseS L C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)
              \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> twl_stgy_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and>
              (S', S) \<in> measure (size \<circ> clauses_to_update))\<close> (is ?upd)
          apply (rewrite at \<open>set_clauses_to_update _ \<hole>\<close> S)
          apply (rewrite at \<open>clauses_to_update \<hole>\<close> S)
          unfolding update_clauseS_def clauses_to_update.simps set_clauses_to_update.simps
          apply clarify
        proof refine_vcg
          fix x xa a b
          assume K: \<open>x \<in># unwatched C \<and> - x \<notin> lits_of_l M\<close>
          have uL: \<open>- L \<in> lits_of_l M\<close>
            using inv unfolding twl_struct_invs_def S WS_WS' by auto
          { \<comment> \<open>BLIT\<close>
            let ?T = \<open>(M, N, U, D, NE, UE, remove1_mset (L, C) WS, Q)\<close>
            let ?T' = \<open>(M, N, U, None, NE, UE, WS', Q)\<close>

            assume \<open>x \<in> lits_of_l M\<close>
            have uL: \<open>- L \<in> lits_of_l M\<close>
              using inv unfolding twl_struct_invs_def S WS_WS' by auto
            have \<open>L \<in># clause C\<close> \<open>x \<in># clause C\<close>
              using watched K by (cases C; simp; fail)+
            have \<open>cdcl_twl_cp ?S' ?T'\<close>
              by (rule cdcl_twl_cp.delete_from_working[OF \<open>x \<in># clause C\<close> \<open>x \<in> lits_of_l M\<close>])
            then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
              by (auto simp: S D WS_WS')

            show \<open>twl_struct_invs ?T\<close>
              using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

            have uL: \<open>- L \<in> lits_of_l M\<close>
              using inv unfolding twl_struct_invs_def S WS_WS' by auto

            show \<open>twl_stgy_invs ?T\<close>
              using cdcl inv inv_s D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)
            show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
              using D WS_WS' cdcl by auto
            show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
              by (simp add: WS'_def[symmetric] WS_WS' S)
          }
          assume
            update: \<open>case xa of (N', U') \<Rightarrow> update_clauses (N, U) C L x (N', U')\<close> and
            [simp]: \<open>xa = (a, b)\<close>
          let ?T' = \<open>(M, a, b, None, NE, UE, WS', Q)\<close>
          let ?T = \<open>(M, a, b, D, NE, UE, remove1_mset (L, C) WS, Q)\<close>
          have \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.update_clause)
              (use uL L' K update watched S in \<open>simp_all add: true_annot_iff_decided_or_true_lit\<close>)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            by (auto simp: S D WS_WS')

          show \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

          have uL: \<open>- L \<in> lits_of_l M\<close>
            using inv unfolding twl_struct_invs_def S WS_WS' by auto

          show \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)
          show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using D WS_WS' cdcl by auto
          show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
            by (simp add: WS'_def[symmetric] WS_WS' S)

        qed
        moreover assume \<open>\<not>?upd\<close>
        ultimately show \<open>- La \<in>
          lits_of_l (get_trail (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S))\<close>
          by fast
      }
    }
  qed
qed

declare unit_propagation_inner_loop_body(1)[THEN order_trans, refine_vcg]

lemma unit_propagation_inner_loop:
  assumes \<open>twl_struct_invs S\<close> and inv: \<open>twl_stgy_invs S\<close> and \<open>get_conflict S = None\<close>
  shows \<open>unit_propagation_inner_loop S \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
    cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and> clauses_to_update S' = {#})\<close>
  unfolding unit_propagation_inner_loop_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(S, n). (size o clauses_to_update) S + n)\<close>])
  subgoal by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp add: twl_struct_invs_def)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

declare unit_propagation_inner_loop[THEN order_trans, refine_vcg]

definition unit_propagation_outer_loop :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>unit_propagation_outer_loop S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs S \<and> twl_stgy_invs S \<and> cdcl_twl_cp\<^sup>*\<^sup>* S\<^sub>0 S \<and> clauses_to_update S = {#}\<^esup>
      (\<lambda>S. literals_to_update S \<noteq> {#})
      (\<lambda>S. do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># literals_to_update S);
        let S' = set_clauses_to_update {#(L, C)|C \<in># get_clauses S. L \<in># watched C#}
           (set_literals_to_update (literals_to_update S - {#L#}) S);
        ASSERT(cdcl_twl_cp S S');
        unit_propagation_inner_loop S'
      })
      S\<^sub>0
\<close>

(* don't use no_step here to allow the abbreviation to fold by default *)
abbreviation unit_propagation_outer_loop_spec where
  \<open>unit_propagation_outer_loop_spec S S' \<equiv> twl_struct_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and>
    literals_to_update S' = {#} \<and>  (\<forall>S'a. \<not> cdcl_twl_cp S' S'a) \<and> twl_stgy_invs S'\<close>

lemma unit_propagation_outer_loop:
  assumes \<open>twl_struct_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and confl: \<open>get_conflict S = None\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>unit_propagation_outer_loop S \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and>
    literals_to_update S' = {#} \<and> no_step cdcl_twl_cp S' \<and> twl_stgy_invs S')\<close>
proof -

  have assert_twl_cp: \<open>cdcl_twl_cp T
     (set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
        (set_literals_to_update (remove1_mset L (literals_to_update T)) T))\<close> (is ?twl) and
    assert_twl_struct_invs:
      \<open>twl_struct_invs (set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
      (set_literals_to_update (remove1_mset L (literals_to_update T)) T))\<close>
           (is \<open>twl_struct_invs ?T'\<close>) and
    assert_stgy_invs:
      \<open>twl_stgy_invs  (set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
      (set_literals_to_update (remove1_mset L (literals_to_update T)) T))\<close> (is ?stgy)
     if
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      invs: \<open>twl_struct_invs T \<and> twl_stgy_invs T \<and>cdcl_twl_cp\<^sup>*\<^sup>* S T \<and> clauses_to_update T = {#}\<close>
      for L T
  proof -
    from that have
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      \<open>cdcl_twl_cp\<^sup>*\<^sup>* S T\<close> and
      w_q: \<open>clauses_to_update T = {#}\<close>
      by fast+
    have \<open>get_conflict T = None\<close>
      using w_q p invs unfolding twl_struct_invs_def by auto
    then obtain M N U NE UE Q where
      T: \<open>T = (M, N, U, None, NE, UE, {#}, Q)\<close>
      using w_q p by (cases T) auto
    define Q' where \<open>Q' = remove1_mset L Q\<close>
    have Q: \<open>Q = add_mset L Q'\<close>
      using L_T unfolding Q'_def T by auto

      \<comment> \<open>Show assertion that one step has been done\<close>
    show twl: ?twl
      unfolding T set_clauses_to_update.simps set_literals_to_update.simps literals_to_update.simps Q'_def[symmetric]
      unfolding Q get_clauses.simps
      by (rule cdcl_twl_cp.pop)
    then show \<open>twl_struct_invs ?T'\<close>
      using cdcl_twl_cp_twl_struct_invs struct_invs by blast


    then show ?stgy
      using twl cdcl_twl_cp_twl_stgy_invs[OF twl] invs by blast
  qed

  show ?thesis
    unfolding unit_propagation_outer_loop_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>{(T, S). twl_struct_invs S \<and> cdcl_twl_cp\<^sup>+\<^sup>+ S T}\<close>])
                apply ((simp_all add: assms tranclp_wf_cdcl_twl_cp; fail)+)[6]
    subgoal by (rule assert_twl_cp) \<comment> \<open>Assertion\<close>
    subgoal by (rule assert_twl_struct_invs) \<comment> \<open>WHILE-loop invariants\<close>
    subgoal by (rule assert_stgy_invs)
    subgoal for S L
      by (cases S)
       (auto simp: twl_st twl_struct_invs_def)
    subgoal by (simp; fail)
    subgoal by auto
    subgoal by auto
    subgoal by simp
    subgoal by auto \<comment> \<open>Termination\<close>
    subgoal \<comment> \<open>Final invariants\<close>
      by simp
    subgoal by simp
    subgoal by auto
    subgoal by (auto simp: cdcl_twl_cp.simps)
    subgoal by simp
    done
qed
declare unit_propagation_outer_loop[THEN order_trans, refine_vcg]


subsection \<open>Other Rules\<close>

subsubsection \<open>Decide\<close>

definition find_unassigned_lit :: \<open>'v twl_st \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit = (\<lambda>S.
      SPEC (\<lambda>L.
        (L \<noteq> None \<longrightarrow> undefined_lit (get_trail S) (the L) \<and>
          atm_of (the L) \<in> atms_of_mm (get_all_init_clss S)) \<and>
        (L = None \<longrightarrow> (\<nexists>L. undefined_lit (get_trail S) L \<and>
         atm_of L \<in> atms_of_mm (get_all_init_clss S)))))\<close>

definition propagate_dec where
  \<open>propagate_dec = (\<lambda>L (M, N, U, D, NE, UE, WS, Q). (Decided L # M, N, U, D, NE, UE, WS, {#-L#}))\<close>

definition decide_or_skip :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>decide_or_skip S = do {
     L \<leftarrow> find_unassigned_lit S;
     case L of
       None \<Rightarrow> RETURN (True, S)
     | Some L \<Rightarrow> RETURN (False, propagate_dec L S)
  }
\<close>

lemma decide_or_skip_spec:
  assumes \<open>clauses_to_update S = {#}\<close> and \<open>literals_to_update S = {#}\<close> and \<open>get_conflict S = None\<close> and
    twl: \<open>twl_struct_invs S\<close> and twl_s: \<open>twl_stgy_invs S\<close>
  shows \<open>decide_or_skip S \<le> SPEC(\<lambda>(brk, T). cdcl_twl_o\<^sup>*\<^sup>* S T \<and>
       get_conflict T = None \<and>
       no_step cdcl_twl_o T \<and> (brk \<longrightarrow> no_step cdcl_twl_stgy T) \<and> twl_struct_invs T \<and>
       twl_stgy_invs T \<and> clauses_to_update T = {#} \<and>
       (\<not>brk \<longrightarrow> literals_to_update T \<noteq> {#}) \<and>
       (\<not>no_step cdcl_twl_o S \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ S T))\<close>
proof -
  obtain M N U NE UE where S: \<open>S = (M, N, U, None, NE, UE, {#}, {#})\<close>
    using assms by (cases S) auto
  have atm_N_U:
    \<open>atm_of L \<in> atms_of_mm (clauses N + NE)\<close>
    if U: \<open>atm_of L \<in> atms_of_ms (clause ` set_mset U)\<close> and
       undef: \<open>undefined_lit M L\<close>
    for L
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close> and unit: \<open>entailed_clss_inv S\<close>
      using twl unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then show ?thesis
      using that
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def S cdcl\<^sub>W_restart_mset_state image_Un)
  qed
  {
    fix L
    assume undef: \<open>undefined_lit M L\<close> and L: \<open>atm_of L \<in> atms_of_mm (clauses N + NE)\<close>
    let ?T = \<open>(Decided L # M, N, U, None, NE, UE, {#}, {#- L#})\<close>
    have o: \<open>cdcl_twl_o (M, N, U, None, NE, UE, {#}, {#}) ?T\<close>
      by (rule cdcl_twl_o.decide) (use undef L in auto)
    have twl': \<open>twl_struct_invs ?T\<close>
      using S cdcl_twl_o_twl_struct_invs o twl by blast
    have twl_s': \<open>twl_stgy_invs ?T\<close>
      using S cdcl_twl_o_twl_stgy_invs o twl twl_s by blast
    note o twl' twl_s'
  } note H = this
  show ?thesis
    using assms unfolding S find_unassigned_lit_def propagate_dec_def decide_or_skip_def
    apply (refine_vcg)
    subgoal by fast
    subgoal by blast
    subgoal by (force simp: H elim!: cdcl_twl_oE cdcl_twl_stgyE cdcl_twl_cpE dest!: atm_N_U)
    subgoal by (force elim!: cdcl_twl_oE cdcl_twl_stgyE cdcl_twl_cpE)
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (auto elim!: cdcl_twl_oE)
    subgoal using atm_N_U by (auto simp: cdcl_twl_o.simps decide)
    subgoal by auto
    subgoal by (auto elim!: cdcl_twl_oE)
    subgoal by auto
    subgoal using atm_N_U H by auto
    subgoal using H atm_N_U by auto
    subgoal by auto
    subgoal by auto
    subgoal using H atm_N_U by auto
    done
qed

declare decide_or_skip_spec[THEN order_trans, refine_vcg]

subsubsection \<open>Skip and Resolve Loop\<close>

definition skip_and_resolve_loop_inv where
  \<open>skip_and_resolve_loop_inv S\<^sub>0 =
    (\<lambda>(brk, S). cdcl_twl_o\<^sup>*\<^sup>* S\<^sub>0 S \<and> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and>
          get_conflict S \<noteq> None \<and>
          count_decided (get_trail S) \<noteq> 0 \<and>
          get_trail S \<noteq> [] \<and>
          get_conflict S \<noteq> Some {#} \<and>
          (brk \<longrightarrow> no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S) \<and>
            no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S)))\<close>

definition tl_state :: \<open>'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>tl_state = (\<lambda>(M, N, U, D, NE, UE, WS, Q). (tl M, N, U, D, NE, UE, WS, Q))\<close>

definition update_confl_tl :: \<open>'v clause option \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>update_confl_tl = (\<lambda>D (M, N, U, _, NE, UE, WS, Q). (tl M, N, U, D, NE, UE, WS, Q))\<close>

definition skip_and_resolve_loop :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>skip_and_resolve_loop S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>skip_and_resolve_loop_inv S\<^sub>0\<^esup>
        (\<lambda>(uip, S). \<not>uip \<and> \<not>is_decided (hd (get_trail S)))
        (\<lambda>(_, S).
          do {
            ASSERT(get_trail S \<noteq> []);
            let D' = the (get_conflict S);
            (L, C) \<leftarrow> SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail S));
            if -L \<notin># D' then
              do {RETURN (False, tl_state S)}
            else
              if get_maximum_level (get_trail S) (remove1_mset (-L) D') = count_decided (get_trail S)
              then
                do {RETURN (False, update_confl_tl (Some (cdcl\<^sub>W_restart_mset.resolve_cls L D' C)) S)}
              else
                do {RETURN (True, S)}
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma skip_and_resolve_loop_spec:
  assumes struct_S: \<open>twl_struct_invs S\<close> and stgy_S: \<open>twl_stgy_invs S\<close> and
    \<open>clauses_to_update S = {#}\<close> and \<open>literals_to_update S = {#}\<close> and
    \<open>get_conflict S \<noteq> None\<close> and count_dec: \<open>count_decided (get_trail S) > 0\<close>
  shows \<open>skip_and_resolve_loop S \<le> SPEC(\<lambda>T. cdcl_twl_o\<^sup>*\<^sup>* S T \<and> twl_struct_invs T \<and> twl_stgy_invs T \<and>
      no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of T) \<and>
      no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of T) \<and>
      get_conflict T \<noteq> None \<and> clauses_to_update T = {#} \<and> literals_to_update T = {#})\<close>
  unfolding skip_and_resolve_loop_def
proof (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(brk, S). Suc (length (get_trail S) - If brk 1 0))\<close>];
      remove_dummy_vars)
  show \<open>wf (measure (\<lambda>(brk, S). Suc (length (get_trail S) - (if brk then 1 else 0))))\<close>
    by auto

  have \<open>get_trail S \<Turnstile>as CNot (the (get_conflict S))\<close> if \<open>get_conflict S \<noteq> None\<close>
      using assms that unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by (cases S, auto simp add: cdcl\<^sub>W_restart_mset_state)
  then have \<open>get_trail S \<noteq> []\<close> if \<open>get_conflict S \<noteq> Some {#}\<close>
    using that assms by auto
  then show \<open>skip_and_resolve_loop_inv S (False, S)\<close>
    using assms by (cases S) (auto simp: skip_and_resolve_loop_inv_def cdcl\<^sub>W_restart_mset.skip.simps
          cdcl\<^sub>W_restart_mset.resolve.simps cdcl\<^sub>W_restart_mset_state
          twl_stgy_invs_def cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)

  fix brk :: bool and T :: \<open>'a twl_st\<close>
  assume
    inv: \<open>skip_and_resolve_loop_inv S (brk, T)\<close> and
    brk: \<open>case (brk, T) of (brk, S) \<Rightarrow> \<not> brk \<and> \<not> is_decided (hd (get_trail S))\<close>
  have [simp]: \<open>brk = False\<close>
    using brk by auto
  show M_not_empty: \<open>get_trail T \<noteq> []\<close>
    using brk inv unfolding skip_and_resolve_loop_inv_def by auto

  fix L :: \<open>'a literal\<close> and C
  assume
    LC: \<open>case (L, C) of (L, C) \<Rightarrow> Propagated L C = hd (get_trail T)\<close>

  obtain M N U D NE UE WS Q where
    T: \<open>T = (M, N, U, D, NE, UE, WS, Q)\<close>
    by (cases T)

  obtain M' :: \<open>('a, 'a clause) ann_lits\<close> and D' where
    M: \<open>get_trail T = Propagated L C # M'\<close> and WS: \<open>WS = {#}\<close> and Q: \<open>Q = {#}\<close> and D: \<open>D = Some D'\<close> and
    st: \<open>cdcl_twl_o\<^sup>*\<^sup>* S T\<close> and twl: \<open>twl_struct_invs T\<close> and D': \<open>D' \<noteq> {#}\<close> and
    twl_stgy_S: \<open>twl_stgy_invs T\<close> and
    [simp]: \<open>count_decided (tl M) > 0\<close> \<open>count_decided (tl M) \<noteq> 0\<close>
    using brk inv LC unfolding skip_and_resolve_loop_inv_def
    by (cases \<open>get_trail T\<close>; cases \<open>hd (get_trail T)\<close>) (auto simp: T)

  { \<comment> \<open>skip\<close>
    assume LD: \<open>- L \<notin># the (get_conflict T)\<close>
    let ?T = \<open>tl_state T\<close>
    have o_S_T: \<open>cdcl_twl_o T ?T\<close>
      using cdcl_twl_o.skip[of L \<open>the D\<close> C M' N U NE UE]
      using LD D inv M unfolding skip_and_resolve_loop_inv_def T WS Q D by (auto simp: tl_state_def)
    have st_T: \<open>cdcl_twl_o\<^sup>*\<^sup>* S ?T\<close>
      using st o_S_T by auto
    moreover have twl_T: \<open>twl_struct_invs ?T\<close>
      using struct_S twl o_S_T cdcl_twl_o_twl_struct_invs by blast
    moreover have twl_stgy_T: \<open>twl_stgy_invs ?T\<close>
      using twl o_S_T stgy_S twl_stgy_S cdcl_twl_o_twl_stgy_invs by blast
    moreover have \<open>tl M \<noteq> []\<close>
      using twl_T D D' unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state T tl_state_def)
    ultimately show \<open>skip_and_resolve_loop_inv S (False, tl_state T)\<close>
      using WS Q D D' unfolding skip_and_resolve_loop_inv_def tl_state_def T
      by simp

    show \<open>((False, ?T), (brk, T))
        \<in> measure (\<lambda>(brk, S). Suc (length (get_trail S) - (if brk then 1 else 0)))\<close>
      using M_not_empty by (simp add: tl_state_def T M)

  }
  { \<comment> \<open>resolve\<close>
    assume
      LD: \<open>\<not>- L \<notin># the (get_conflict T)\<close> and
      max: \<open>get_maximum_level (get_trail T) (remove1_mset (- L) (the (get_conflict T)))
        = count_decided (get_trail T)\<close>
    let ?D = \<open>remove1_mset (- L) (the (get_conflict T)) \<union># remove1_mset L C\<close>
    let ?T = \<open>update_confl_tl (Some ?D) T\<close>
    have count_dec: \<open>count_decided M' = count_decided M\<close>
      using M unfolding T by auto
    then have o_S_T: \<open>cdcl_twl_o T ?T\<close>
      using cdcl_twl_o.resolve[of L \<open>the D\<close> C M' N U NE UE] LD D max M WS Q D
      by (auto simp: T D update_confl_tl_def)
    then have st_T: \<open>cdcl_twl_o\<^sup>*\<^sup>* S ?T\<close>
      using st by auto
    moreover have twl_T: \<open>twl_struct_invs ?T\<close>
      using st_T twl o_S_T cdcl_twl_o_twl_struct_invs by blast
    moreover have twl_stgy_T: \<open>twl_stgy_invs ?T\<close>
      using twl o_S_T twl_stgy_S cdcl_twl_o_twl_stgy_invs by blast
    moreover {
      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of ?T)\<close>
      using twl_T D D' M unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       by fast
      then have \<open>tl M \<Turnstile>as CNot ?D\<close>
        using M unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp add: cdcl\<^sub>W_restart_mset_state T update_confl_tl_def)
    }
    moreover have \<open>get_conflict ?T \<noteq> Some {#}\<close>
      using twl_stgy_T count_dec unfolding twl_stgy_invs_def update_confl_tl_def
        cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def T
        by (auto simp: trail.simps conflicting.simps)
    ultimately show \<open>skip_and_resolve_loop_inv S (False, ?T)\<close>
      using WS Q D D' unfolding skip_and_resolve_loop_inv_def
      by (auto simp add: cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
          cdcl\<^sub>W_restart_mset_state update_confl_tl_def T)

    show \<open>((False, ?T), (brk, T)) \<in> measure (\<lambda>(brk, S). Suc (length (get_trail S)
        - (if brk then 1 else 0)))\<close>
      using M_not_empty by (simp add: T update_confl_tl_def)
  }
  { \<comment> \<open>No step\<close>
    assume
      LD: \<open>\<not>- L \<notin># the (get_conflict T)\<close> and
      max: \<open>get_maximum_level (get_trail T) (remove1_mset (- L) (the (get_conflict T)))
         \<noteq> count_decided (get_trail T)\<close>

    show \<open>skip_and_resolve_loop_inv S (True, T)\<close>
      using inv max LD D M unfolding skip_and_resolve_loop_inv_def
      by (auto simp add: cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
          cdcl\<^sub>W_restart_mset_state T)
    show \<open>((True, T), (brk, T)) \<in> measure (\<lambda>(brk, S). Suc (length (get_trail S) - (if brk then 1 else 0)))\<close>
      using M_not_empty by simp
  }
next \<comment> \<open>Final properties\<close>
  fix brk T U
  assume
    inv: \<open>skip_and_resolve_loop_inv S (brk, T)\<close> and
    brk: \<open>\<not>(case (brk, T) of (brk, S) \<Rightarrow> \<not> brk \<and> \<not> is_decided (hd (get_trail S)))\<close>
  show \<open>cdcl_twl_o\<^sup>*\<^sup>* S T\<close>
    using inv by (auto simp add: skip_and_resolve_loop_inv_def)

  { assume \<open>is_decided (hd (get_trail T))\<close>
    then have \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of T)\<close> and
      \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of T)\<close>
      by (cases T;  auto simp add: cdcl\<^sub>W_restart_mset.skip.simps
          cdcl\<^sub>W_restart_mset.resolve.simps cdcl\<^sub>W_restart_mset_state)+
  }
  moreover
  { assume \<open>brk\<close>
    then have \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of T)\<close> and
      \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of T)\<close>
      using inv by (auto simp: skip_and_resolve_loop_inv_def)
  }
  ultimately show \<open>\<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of T) U\<close> and
    \<open>\<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of T) U\<close>
    using brk unfolding prod.case by blast+

  show \<open>twl_struct_invs T\<close>
    using inv unfolding skip_and_resolve_loop_inv_def by auto
  show \<open>twl_stgy_invs T\<close>
    using inv unfolding skip_and_resolve_loop_inv_def by auto

  show \<open>get_conflict T \<noteq> None\<close>
    using inv by (auto simp: skip_and_resolve_loop_inv_def)

  show \<open>clauses_to_update T = {#}\<close>
    using inv by (auto simp: skip_and_resolve_loop_inv_def)

  show \<open>literals_to_update T = {#}\<close>
    using inv by (auto simp: skip_and_resolve_loop_inv_def)
qed

declare skip_and_resolve_loop_spec[THEN order_trans, refine_vcg]


subsubsection \<open>Backtrack\<close>

definition extract_shorter_conflict :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>extract_shorter_conflict = (\<lambda>(M, N, U, D, NE, UE, WS, Q).
    SPEC(\<lambda>S'. \<exists>D'. S' = (M, N, U, Some D', NE, UE, WS, Q) \<and>
       D' \<subseteq># the D \<and> clause `# (N + U) + NE + UE \<Turnstile>pm D' \<and> -lit_of (hd M) \<in># D'))\<close>

fun equality_except_conflict :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
\<open>equality_except_conflict (M, N, U, D, NE, UE, WS, Q) (M', N', U', D', NE', UE', WS', Q') \<longleftrightarrow>
    M = M' \<and> N = N' \<and> U = U' \<and> NE = NE' \<and> UE = UE' \<and> WS = WS' \<and> Q = Q'\<close>

lemma extract_shorter_conflict_alt_def:
  \<open>extract_shorter_conflict S =
    SPEC(\<lambda>S'. \<exists>D'. equality_except_conflict S S' \<and> Some D' = get_conflict S' \<and>
       D' \<subseteq># the (get_conflict S) \<and> clause `# (get_clauses S) + unit_clss S \<Turnstile>pm D' \<and>
       -lit_of (hd (get_trail S)) \<in># D')\<close>
  unfolding extract_shorter_conflict_def
  by (cases S) (auto simp: ac_simps)

definition reduce_trail_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>reduce_trail_bt = (\<lambda>L (M, N, U, D', NE, UE, WS, Q). do {
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
              get_level M K = get_maximum_level M (the D' - {#-L#}) + 1);
        RETURN (M1, N, U, D', NE, UE, WS, Q)
  })\<close>

definition propagate_bt :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_bt = (\<lambda>L L' (M, N, U, D, NE, UE, WS, Q).
    (Propagated (-L) (the D) # M, N, add_mset (TWL_Clause {#-L, L'#} (the D - {#-L, L'#})) U, None,
      NE, UE, WS, {#L#}))\<close>

definition propagate_unit_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_unit_bt = (\<lambda>L (M, N, U, D, NE, UE, WS, Q).
    (Propagated (-L) (the D) # M, N, U, None, NE, add_mset (the D) UE, WS, {#L#}))\<close>

definition backtrack_inv where
  \<open>backtrack_inv S \<longleftrightarrow> get_trail S \<noteq> [] \<and> get_conflict S \<noteq> Some {#}\<close>

definition backtrack :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>backtrack S =
    do {
      ASSERT(backtrack_inv S);
      let L = lit_of (hd (get_trail S));
      S \<leftarrow> extract_shorter_conflict S;
      S \<leftarrow> reduce_trail_bt L S;

      if size (the (get_conflict S)) > 1
      then do {
        L' \<leftarrow> SPEC(\<lambda>L'. L' \<in># the (get_conflict S) - {#-L#} \<and> L \<noteq> -L' \<and>
          get_level (get_trail S) L' = get_maximum_level (get_trail S) (the (get_conflict S) - {#-L#}));
        RETURN (propagate_bt L L' S)
      }
      else do {
        RETURN (propagate_unit_bt L S)
      }
    }
  \<close>


lemma
  assumes confl: \<open>get_conflict S \<noteq> None\<close> \<open>get_conflict S \<noteq> Some {#}\<close> and
    w_q: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close> and
    ns_s: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S)\<close> and
    ns_r: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S)\<close> and
    twl_struct: \<open>twl_struct_invs S\<close> and twl_stgy: \<open>twl_stgy_invs S\<close>
  shows
    backtrack_spec:
    \<open>backtrack S \<le> SPEC (\<lambda>T. cdcl_twl_o S T \<and> get_conflict T = None \<and> no_step cdcl_twl_o T \<and>
      twl_struct_invs T \<and> twl_stgy_invs T \<and> clauses_to_update T = {#} \<and>
      literals_to_update T \<noteq> {#})\<close> (is ?spec) and
    backtrack_nofail:
      \<open>nofail (backtrack S)\<close> (is ?fail)
proof -
  let ?S = \<open>state\<^sub>W_of S\<close>
  have inv_s: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant ?S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ?S\<close>
    using twl_struct twl_stgy unfolding twl_struct_invs_def twl_stgy_invs_def by fast+
  let ?D' = \<open>the (conflicting ?S)\<close>
  have M_CNot_D': \<open>trail ?S \<Turnstile>as CNot ?D'\<close>
    using inv confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases \<open>conflicting ?S\<close>; cases S) (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have trail: \<open>get_trail S \<noteq> []\<close>
    using confl unfolding true_annots_true_cls_def_iff_negation_in_model
    by (cases S) (auto simp: cdcl\<^sub>W_restart_mset_state)
  show ?spec
    unfolding backtrack_def extract_shorter_conflict_def reduce_trail_bt_def
  proof (refine_vcg; remove_dummy_vars; clarify?)
    show \<open>backtrack_inv S\<close>
      using trail confl unfolding backtrack_inv_def by fast

    fix M M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and
      N U :: \<open>'a twl_clss\<close> and
      D :: \<open>'a clause option\<close> and D' :: \<open>'a clause\<close> and NE UE :: \<open>'a clauses\<close> and
      WS :: \<open>'a clauses_to_update\<close> and Q :: \<open>'a lit_queue\<close> and K K' :: \<open>'a literal\<close>
    let ?S = \<open>(M, N, U, D, NE, UE, WS, Q)\<close>
    let ?T = \<open>(M, N, U, Some D', NE, UE, WS, Q)\<close>
    let ?U = \<open>(M1, N, U, Some D', NE, UE, WS, Q)\<close>
    let ?MS = \<open>get_trail ?S\<close>
    let ?MT = \<open>get_trail ?T\<close>
    assume
      S: \<open>S = (M, N, U, D, NE, UE, WS, Q)\<close> and
      D'_D: \<open>D' \<subseteq># the D\<close> and
      L_D': \<open>-lit_of (hd M) \<in># D'\<close> and
      N_U_NE_UE_D': \<open>clause `# (N + U) + NE + UE \<Turnstile>pm D'\<close> and
      decomp: \<open>(Decided K' # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
      lev_K': \<open>get_level M K' = get_maximum_level M (remove1_mset (- lit_of (hd ?MS))
               (the (Some D'))) + 1\<close>
    have WS: \<open>WS = {#}\<close> and Q: \<open>Q = {#}\<close>
      using w_q p unfolding S by auto

    have uL_D: \<open>- lit_of (hd M) \<in># the D\<close>
      using decomp N_U_NE_UE_D' D'_D L_D' lev_K'
      unfolding WS Q
      by auto

    have D_Some_the: \<open>D = Some (the D)\<close>
      using confl S by auto
    let ?S' = \<open>state\<^sub>W_of S\<close>
    have inv_s: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant ?S'\<close> and
      inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ?S'\<close>
      using twl_struct twl_stgy unfolding twl_struct_invs_def twl_stgy_invs_def by fast+
    have Q: \<open>Q = {#}\<close> and WS: \<open>WS = {#}\<close>
      using w_q p unfolding S by auto
    have M_CNot_D': \<open>M \<Turnstile>as CNot D'\<close>
      using M_CNot_D' S D'_D
      by (auto simp: cdcl\<^sub>W_restart_mset_state true_annots_true_cls_def_iff_negation_in_model)
    obtain L'' M' where M: \<open>M = L'' # M'\<close>
      using trail S by (cases M) auto
    have D'_empty: \<open>D' \<noteq> {#}\<close>
      using L_D' by auto
    have L'_D: \<open>-lit_of L'' \<in># D'\<close>
      using L_D' by (auto simp: cdcl\<^sub>W_restart_mset_state M)
    have lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ?S'\<close>
      using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
    then have n_d: \<open>no_dup M\<close> and dec: \<open>backtrack_lvl ?S' = count_decided M\<close>
      using S unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state)
    then have uL''_M: \<open>-lit_of L'' \<notin> lits_of_l M\<close>
      by (auto simp: Decided_Propagated_in_iff_in_lits_of_l M)
    have \<open>get_maximum_level M (remove1_mset (-lit_of (hd M)) D') < count_decided M\<close>
    proof (cases L'')
      case (Decided x1) note L'' = this(1)
      have \<open>distinct_mset (the D)\<close>
        using inv S confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        by (auto simp: cdcl\<^sub>W_restart_mset_state)
      then have \<open>distinct_mset D'\<close>
        using D'_D by (blast intro: distinct_mset_mono)
      then have \<open>- x1 \<notin># remove1_mset (- x1) D'\<close>
        using L'_D L'' D'_D by (auto dest: distinct_mem_diff_mset)
      then have H: \<open>\<forall>x\<in>#remove1_mset (- lit_of (hd M)) D'. undefined_lit [L''] x\<close>
        using L'' M_CNot_D' uL''_M
        by (fastforce simp: atms_of_def atm_of_eq_atm_of M true_annots_true_cls_def_iff_negation_in_model
            dest: in_diffD)
      have \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) D') =
        get_maximum_level M' (remove1_mset (- lit_of (hd M)) D')\<close>
        using get_maximum_level_skip_beginning[OF H, of M'] M
        by auto
      then show ?thesis
        using count_decided_ge_get_maximum_level[of M' \<open>remove1_mset (-lit_of (hd M)) D'\<close>] M L''
        by simp
    next
      case (Propagated L C) note L'' = this(1)
      moreover {
        have \<open>\<forall>L mark a b. a @ Propagated L mark # b = trail (state\<^sub>W_of S) \<longrightarrow>
          b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
          using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          by blast
        then have \<open>L \<in># C\<close>
          by (force simp: S M cdcl\<^sub>W_restart_mset_state L'') }
      moreover have D_empty: \<open>the D \<noteq> {#}\<close>
        using D'_D D'_empty by auto
      moreover have \<open>-L \<in># the D\<close>
        using ns_s L'' confl D_empty
        by (force simp: cdcl\<^sub>W_restart_mset.skip.simps S M cdcl\<^sub>W_restart_mset_state)
      ultimately have \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D)) < count_decided M\<close>
        using ns_r confl count_decided_ge_get_maximum_level[of M \<open>remove1_mset (-lit_of (hd M)) (the D)\<close>]
        by (fastforce simp add: cdcl\<^sub>W_restart_mset.resolve.simps S M
            cdcl\<^sub>W_restart_mset_state)

      moreover have \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) D') \<le>
              get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D))\<close>
        by (rule get_maximum_level_mono) (use D'_D in \<open>auto intro: mset_le_subtract\<close>)
      ultimately show ?thesis
        by simp
    qed

    then have \<open>\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
      get_level M K = get_maximum_level M (remove1_mset (-lit_of (hd M)) D') + 1\<close>
      using cdcl\<^sub>W_restart_mset.backtrack_ex_decomp[OF lev_inv]
      by (auto simp: cdcl\<^sub>W_restart_mset_state S)

    define i where \<open>i = get_maximum_level M (remove1_mset (- lit_of (hd M)) D')\<close>

    let ?T =  \<open>(Propagated (-lit_of (hd M)) D' # M1, N,
      add_mset (TWL_Clause {#-lit_of (hd M), K#} (D' - {#-lit_of (hd M), K#})) U,
      None, NE, UE, WS, {#lit_of (hd M)#})\<close>
    let ?T' = \<open>(Propagated (-lit_of (hd M)) D' # M1, N,
      add_mset (TWL_Clause {#-lit_of (hd M), K#} (D' - {#-lit_of (hd M), K#})) U,
      None, NE, UE, WS, {#- (-lit_of (hd M))#})\<close>

    have lev_D': \<open>count_decided M = get_maximum_level (L'' # M') D'\<close>
      using count_decided_ge_get_maximum_level[of M D'] L'_D
        get_maximum_level_ge_get_level[of \<open>-lit_of L''\<close> D' M] unfolding M
      by (auto split: if_splits)

    { \<comment> \<open>conflict clause > 1 literal\<close>
      assume size_D: \<open>1 < size (the (get_conflict ?U))\<close> and
      K_D: \<open>K \<in># remove1_mset (- lit_of (hd ?MS)) (the (get_conflict ?U))\<close> and
      lev_K: \<open>get_level (get_trail ?U) K = get_maximum_level (get_trail ?U)
          (remove1_mset (- lit_of (hd (get_trail ?S))) (the (get_conflict ?U)))\<close>

      have \<open>\<forall>L' \<in># D'. -L' \<in> lits_of_l M\<close>
        using M_CNot_D' uL''_M
        by (fastforce simp: atms_of_def atm_of_eq_atm_of M true_annots_true_cls_def_iff_negation_in_model
            dest: in_diffD)
      obtain c where c: \<open>M = c @ M2 @ Decided K' # M1\<close>
        using get_all_ann_decomposition_exists_prepend[OF decomp] by blast
      have \<open>get_level M K' = Suc (count_decided M1)\<close>
        using n_d unfolding c by auto
      then have i: \<open>i = count_decided M1\<close>
        using lev_K' unfolding i_def by auto
      have lev_M_M1: \<open>\<forall>L' \<in># D' - {#-lit_of (hd M)#}. get_level M L' = get_level M1 L'\<close>
      proof
        fix L'
        assume L': \<open>L' \<in># D' - {#-lit_of (hd M)#}\<close>
        have \<open>get_level M L' > count_decided M1\<close> if \<open>defined_lit (c @ M2 @ Decided K' # []) L'\<close>
          using get_level_skip_end[OF that, of M1] n_d that get_level_last_decided_ge[of \<open>c @ M2\<close>]
          by (auto simp: c)
        moreover have \<open>get_level M L' \<le> i\<close>
          using get_maximum_level_ge_get_level[OF L', of M] unfolding i_def by auto
        ultimately show \<open>get_level M L' = get_level M1 L'\<close>
          using n_d c L' i by (cases \<open>defined_lit (c @ M2 @ Decided K' # []) L'\<close>) auto
      qed
      have \<open>get_level M1 `# remove1_mset (- lit_of (hd M)) D' = get_level M `# remove1_mset (- lit_of (hd M)) D'\<close>
        by (rule image_mset_cong) (use lev_M_M1 in auto)
      then have max_M1_M1_D: \<open>get_maximum_level M1 (remove1_mset (- lit_of (hd M)) D') =
        get_maximum_level M (remove1_mset (- lit_of (hd M)) D')\<close>
        unfolding get_maximum_level_def by argo


      have \<open>\<exists>L' \<in># remove1_mset (-lit_of (hd M)) D'.
           get_level M L' = get_maximum_level M (remove1_mset (- lit_of (hd M)) D')\<close>
        by (rule get_maximum_level_exists_lit_of_max_level)
          (use size_D in \<open>auto simp: remove1_mset_empty_iff\<close>)
      have D'_ne_single: \<open>D' \<noteq> {#- lit_of (hd M)#}\<close>
        using size_D apply (cases D', simp)
        apply (rename_tac L D'')
        apply (case_tac D'')
        by simp_all
      have \<open>cdcl_twl_o (M, N, U, D, NE, UE, WS, Q) ?T'\<close>
        unfolding Q WS option.sel list.sel
        apply (subst D_Some_the)
        apply (rule cdcl_twl_o.backtrack_nonunit_clause[of \<open>-lit_of (hd M)\<close> _ K' M1 M2 _ _ i])
        subgoal using D'_D L_D' by blast
        subgoal using L'_D decomp M by auto
        subgoal using L'_D decomp M by auto
        subgoal using L'_D M lev_D' by auto
        subgoal using i lev_D' i_def by auto
        subgoal using lev_K' i_def by auto
        subgoal using D'_ne_single .
        subgoal using D'_D .
        subgoal using N_U_NE_UE_D' .
        subgoal using L_D' .
        subgoal using K_D by (auto dest: in_diffD)
        subgoal using lev_K lev_M_M1 K_D by (simp add: i_def max_M1_M1_D)
        done
    then show cdcl: \<open>cdcl_twl_o ?S (propagate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
      unfolding WS Q by (auto simp: propagate_bt_def)

      show \<open>get_conflict (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) = None\<close>
        by (auto simp: propagate_bt_def)

      show \<open>twl_struct_invs (propagate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
        using S cdcl cdcl_twl_o_twl_struct_invs twl_struct by (auto simp: propagate_bt_def)
      show \<open>twl_stgy_invs (propagate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
        using S cdcl cdcl_twl_o_twl_stgy_invs twl_struct twl_stgy by blast
      show \<open>clauses_to_update (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) = {#}\<close>
        using WS by (auto simp: propagate_bt_def)

      show False if \<open>cdcl_twl_o (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) (an, ao, ap, aq, ar, as, at, b)\<close>
        for an ao ap aq ar as at b
        using that by (auto simp: cdcl_twl_o.simps propagate_bt_def)

      show False if \<open>literals_to_update (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) = {#}\<close>
        using that by (auto simp: propagate_bt_def)

    }

    { \<comment> \<open>conflict clause has 1 literal\<close>
      assume \<open>\<not> 1 < size (the (get_conflict ?U))\<close>
      then have D': \<open>D' = {#-lit_of (hd M)#}\<close>
        using L'_D by (cases D') (auto simp: M)
      let ?T = \<open>(Propagated (- lit_of (hd M)) D' # M1, N, U, None, NE, add_mset D' UE, WS,
        unmark (hd M))\<close>
      let ?T' = \<open>(Propagated (- lit_of (hd M)) D' # M1, N, U, None, NE, add_mset D' UE, WS,
        {#- (-lit_of (hd M))#})\<close>

      have i_0: \<open>i = 0\<close>
        using i_def by (auto simp: D')

      have \<open>cdcl_twl_o (M, N, U, D, NE, UE, WS, Q) ?T'\<close>
        unfolding D' option.sel WS Q apply (subst D_Some_the)
        apply (rule cdcl_twl_o.backtrack_unit_clause[of _ \<open>the D\<close> K' M1 M2 _ D' i])
        subgoal using D'_D D' by auto
        subgoal using decomp by simp
        subgoal by (simp add: M)
        subgoal using D' by (auto simp: get_maximum_level_add_mset)
        subgoal using i_def by simp
        subgoal using lev_K' i_def[symmetric] by auto
        subgoal using D' .
        subgoal using D'_D .
        subgoal using N_U_NE_UE_D' .
        done
      then show cdcl: \<open>cdcl_twl_o (M, N, U, D, NE, UE, WS, Q)
             (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
        by (auto simp add: propagate_unit_bt_def)
      show \<open>get_conflict (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = None\<close>
        by (auto simp add: propagate_unit_bt_def)

      show \<open>twl_struct_invs (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
        using S cdcl cdcl_twl_o_twl_struct_invs twl_struct by blast

      show \<open>twl_stgy_invs (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
        using S cdcl cdcl_twl_o_twl_stgy_invs twl_struct twl_stgy by blast
      show \<open>clauses_to_update (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = {#}\<close>
        using WS by (auto simp add: propagate_unit_bt_def)
      show False if \<open>literals_to_update (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = {#}\<close>
        using that by (auto simp add: propagate_unit_bt_def)
      fix an ao ap aq ar as at b
      show False if \<open>cdcl_twl_o (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) (an, ao, ap, aq, ar, as, at, b) \<close>
        using that by (auto simp: cdcl_twl_o.simps propagate_unit_bt_def)
    }
  qed
  then show ?fail
    using nofail_simps(2) pwD1 by blast
qed

declare backtrack_spec[THEN order_trans, refine_vcg]


subsubsection \<open>Full loop\<close>

definition cdcl_twl_o_prog :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>cdcl_twl_o_prog S =
    do {
      if get_conflict S = None
      then decide_or_skip S
      else do {
        if count_decided (get_trail S) > 0
        then do {
          T \<leftarrow> skip_and_resolve_loop S;
          ASSERT(get_conflict T \<noteq> None \<and> get_conflict T \<noteq> Some {#});
          U \<leftarrow> backtrack T;
          RETURN (False, U)
        }
        else
          RETURN (True, S)
      }
    }
  \<close>

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>
declare split_paired_All[simp del]

lemma skip_and_resolve_same_decision_level:
  assumes \<open>cdcl_twl_o S T\<close>  \<open>get_conflict T \<noteq> None\<close>
  shows  \<open>count_decided (get_trail T) = count_decided (get_trail S)\<close>
  using assms by (induction rule: cdcl_twl_o.induct) auto


lemma skip_and_resolve_conflict_before:
  assumes \<open>cdcl_twl_o S T\<close> \<open>get_conflict T \<noteq> None\<close>
  shows  \<open>get_conflict S \<noteq> None\<close>
  using assms by (induction rule: cdcl_twl_o.induct) auto

lemma rtranclp_skip_and_resolve_same_decision_level:
  \<open>cdcl_twl_o\<^sup>*\<^sup>* S T \<Longrightarrow> get_conflict S \<noteq> None \<Longrightarrow> get_conflict T \<noteq> None \<Longrightarrow>
    count_decided (get_trail T) = count_decided (get_trail S)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using skip_and_resolve_conflict_before[of T U]
    by (auto simp: skip_and_resolve_same_decision_level)
  done

lemma empty_conflict_lvl0:
  \<open>twl_stgy_invs T \<Longrightarrow> get_conflict T = Some {#} \<Longrightarrow> count_decided (get_trail T) = 0\<close>
  by (cases T) (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
      trail.simps conflicting.simps)

abbreviation cdcl_twl_o_prog_spec where
  \<open>cdcl_twl_o_prog_spec S \<equiv> \<lambda>(brk, T).
       cdcl_twl_o\<^sup>*\<^sup>* S T \<and>
       (get_conflict T \<noteq> None \<longrightarrow> count_decided (get_trail T) = 0) \<and>
       (\<not> brk \<longrightarrow> get_conflict T = None \<and> (\<forall>S'. \<not> cdcl_twl_o T S')) \<and>
       (brk \<longrightarrow> get_conflict T \<noteq> None \<or> (\<forall>S'. \<not> cdcl_twl_stgy T S')) \<and>
       twl_struct_invs T \<and> twl_stgy_invs T \<and> clauses_to_update T = {#} \<and>
       (\<not> brk \<longrightarrow> literals_to_update T \<noteq> {#}) \<and>
       (\<not>brk \<longrightarrow> \<not> (\<forall>S'. \<not> cdcl_twl_o S S') \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ S T)\<close>

lemma cdcl_twl_o_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close> and
    ns_cp: \<open>no_step cdcl_twl_cp S\<close>
  shows
    \<open>cdcl_twl_o_prog S \<le> SPEC(cdcl_twl_o_prog_spec S)\<close>
    (is \<open>_ \<le> ?S\<close>)
proof -
  have [iff]: \<open>\<not> cdcl_twl_cp S T\<close> for T
    using ns_cp by fast

  show ?thesis
    unfolding cdcl_twl_o_prog_def
    apply (refine_vcg decide_or_skip_spec[THEN order_trans]; remove_dummy_vars)
    \<comment> \<open>initial invariants\<close>
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by simp
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal for T using assms empty_conflict_lvl0[of T]
      rtranclp_skip_and_resolve_same_decision_level[of S T] by auto
    subgoal using assms by auto
    subgoal using assms by (auto elim!: cdcl_twl_oE simp: image_Un)
    subgoal by (auto elim!: cdcl_twl_stgyE cdcl_twl_oE cdcl_twl_cpE)
    subgoal by (auto simp: rtranclp_unfold elim!: cdcl_twl_oE)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal for uip by auto
    done
qed

declare cdcl_twl_o_prog_spec[THEN order_trans, refine_vcg]


subsection \<open>Full Strategy\<close>

abbreviation cdcl_twl_stgy_prog_inv where
  \<open>cdcl_twl_stgy_prog_inv S\<^sub>0 \<equiv> \<lambda>(brk, T). twl_struct_invs T \<and> twl_stgy_invs T \<and>
        (brk \<longrightarrow> final_twl_state T) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* S\<^sub>0 T \<and> clauses_to_update T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict T = None)\<close>

definition cdcl_twl_stgy_prog :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>cdcl_twl_stgy_prog S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_prog_inv S\<^sub>0\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop S;
          cdcl_twl_o_prog T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

lemma wf_cdcl_twl_stgy_measure:
   \<open>wf ({((brkT, T), (brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T}
        \<union> {((brkT, T), (brkS, S)). S = T \<and> brkT \<and> \<not>brkS})\<close>
  (is \<open>wf (?TWL \<union> ?BOOL)\<close>)
proof (rule wf_union_compatible)
  show \<open>wf ?TWL\<close>
    using tranclp_wf_cdcl_twl_stgy wf_snd_wf_pair by blast
  show \<open>?TWL O ?BOOL \<subseteq> ?TWL\<close>
    by auto

  show \<open>wf ?BOOL\<close>
    unfolding wf_iff_no_infinite_down_chain
  proof clarify
    fix f :: \<open>nat \<Rightarrow> bool \<times> 'b\<close>
    assume H: \<open>\<forall>i. (f (Suc i), f i) \<in> {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>
    then have \<open>(f (Suc 0), f 0) \<in> {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close> and
      \<open>(f (Suc 1), f 1) \<in> {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>
      by presburger+
    then show False
      by auto
  qed
qed

lemma cdcl_twl_o_final_twl_state:
  assumes
    \<open>cdcl_twl_stgy_prog_inv S (brk, T)\<close> and
    \<open>case (brk, T) of (brk, _) \<Rightarrow> \<not> brk\<close> and
    twl_o: \<open>cdcl_twl_o_prog_spec U (True, V)\<close>
  shows \<open>final_twl_state V\<close>
proof -
  have \<open>cdcl_twl_o\<^sup>*\<^sup>* U V\<close> and
    confl_lev: \<open>get_conflict V \<noteq> None \<longrightarrow> count_decided (get_trail V) = 0\<close> and
    final: \<open>get_conflict V \<noteq> None \<or> (\<forall>S'. \<not> cdcl_twl_stgy V S')\<close>
    \<open>twl_struct_invs V\<close>
    \<open>twl_stgy_invs V\<close>
    \<open>clauses_to_update V = {#}\<close>
    using twl_o
    by force+

  show ?thesis
    unfolding final_twl_state_def
    using confl_lev final
    by auto
qed

lemma cdcl_twl_stgy_in_measure:
  assumes
    twl_stgy: \<open>cdcl_twl_stgy_prog_inv S (brk0, T)\<close> and
    brk0: \<open>case (brk0, T) of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
    twl_o: \<open>cdcl_twl_o_prog_spec U V\<close> and
    [simp]: \<open>twl_struct_invs U\<close> and
    TU: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T U\<close> and
    \<open>literals_to_update U = {#}\<close>
  shows \<open>(V, brk0, T)
         \<in> {((brkT, T), brkS, S). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union>
            {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>
proof -
  have [simp]: \<open>twl_struct_invs T\<close>
    using twl_stgy by fast+
  obtain brk' V' where
    V: \<open>V = (brk', V')\<close>
    by (cases V)
  have
    UV: \<open>cdcl_twl_o\<^sup>*\<^sup>* U V'\<close> and
    \<open>(get_conflict V' \<noteq> None \<longrightarrow> count_decided (get_trail V') = 0)\<close> and
    not_brk': \<open>(\<not> brk' \<longrightarrow> get_conflict V' = None \<and> (\<forall>S'. \<not> cdcl_twl_o V' S'))\<close> and
    brk': \<open>(brk' \<longrightarrow> get_conflict V' \<noteq> None \<or> (\<forall>S'. \<not> cdcl_twl_stgy V' S'))\<close> and
    [simp]: \<open>twl_struct_invs V'\<close>
    \<open>twl_stgy_invs V'\<close>
    \<open>clauses_to_update V' = {#}\<close> and
    no_lits_to_upd: \<open>(0 < count_decided (get_trail V') \<longrightarrow> \<not> brk' \<longrightarrow> literals_to_update V' \<noteq> {#})\<close>
    \<open>(\<not>brk' \<longrightarrow> \<not> (\<forall>S'. \<not> cdcl_twl_o U S') \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ U V')\<close>
    using twl_o unfolding V
    by fast+
    have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T V'\<close>
      using TU UV by (auto dest!: rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD)
    then have TV_or_tranclp_TV: \<open>T = V' \<or> cdcl_twl_stgy\<^sup>+\<^sup>+ T V'\<close>
      unfolding rtranclp_unfold by auto
    have [simp]: \<open>\<not> cdcl_twl_stgy\<^sup>+\<^sup>+ V' V'\<close>
      using wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of V'] by auto
    have [simp]: \<open>brk0 = False\<close>
      using brk0 by auto

    have \<open>brk'\<close> if \<open>T = V'\<close>
    proof -
      have ns_TV: \<open>\<not>cdcl_twl_stgy\<^sup>+\<^sup>+ T V'\<close>
        using that[symmetric] wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of T] by auto

      have ns_T_T: \<open>\<not>cdcl_twl_o\<^sup>+\<^sup>+ T T\<close>
        using wf_not_refl[OF tranclp_wf_cdcl_twl_o, of T] by auto
      have \<open>T = U\<close>
        by (metis (no_types, hide_lams) TU UV ns_TV rtranclp_cdcl_twl_cp_stgyD
            rtranclp_cdcl_twl_o_stgyD rtranclp_tranclp_tranclp rtranclp_unfold)
      show ?thesis
        using assms \<open>literals_to_update U = {#}\<close> unfolding V that[symmetric] \<open>T = U\<close>[symmetric]
        by (auto simp: ns_T_T)
    qed

    then show ?thesis
      using TV_or_tranclp_TV
      unfolding V
      by auto
qed

lemma cdcl_twl_o_prog_cdcl_twl_stgy:
  assumes
    twl_stgy: \<open>cdcl_twl_stgy_prog_inv S (brk, S')\<close> and
    \<open>case (brk, S') of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
    twl_o: \<open>cdcl_twl_o_prog_spec T (brk', U)\<close> and
    \<open>twl_struct_invs T\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* S' T\<close> and
    \<open>literals_to_update T = {#}\<close> and
    \<open>\<forall>S'. \<not> cdcl_twl_cp T S'\<close> and
    \<open>twl_stgy_invs T\<close>
  shows \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S U\<close>
proof -
  have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S S'\<close>
    using twl_stgy by fast
  moreover {
    have \<open>cdcl_twl_o\<^sup>*\<^sup>* T U\<close>
      using twl_o by fast
    then have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' U\<close>
      using cp by (auto dest!: rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD)
  }
  ultimately show ?thesis by auto
qed

lemma cdcl_twl_stgy_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_prog S \<le> conclusive_TWL_run S\<close>
  unfolding cdcl_twl_stgy_prog_def full_def conclusive_TWL_run_def
  apply (refine_vcg WHILEIT_rule[where
     R = \<open>{((brkT, T), (brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union>
          {((brkT, T), (brkS, S)). S = T \<and> brkT \<and> \<not>brkS}\<close>];
      remove_dummy_vars)
  \<comment> \<open>Well foundedness of the relation\<close>
  subgoal using wf_cdcl_twl_stgy_measure .

  \<comment> \<open>initial invariants:\<close>
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp

\<comment> \<open>loop invariants:\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (rule cdcl_twl_o_final_twl_state)
  subgoal by (rule cdcl_twl_o_prog_cdcl_twl_stgy)
  subgoal by simp
  subgoal for brk0 T U brl V
    by clarsimp

  \<comment> \<open>Final properties\<close>
  subgoal for brk0 T U V  \<comment> \<open>termination\<close>
    by (rule cdcl_twl_stgy_in_measure)
  subgoal by simp
  subgoal by fast
  done


definition cdcl_twl_stgy_prog_break :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>cdcl_twl_stgy_prog_break S\<^sub>0 =
  do {
    b \<leftarrow> SPEC(\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, S). cdcl_twl_stgy_prog_inv S\<^sub>0 S\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(_, brk, S). do {
          T \<leftarrow> unit_propagation_outer_loop S;
          T \<leftarrow> cdcl_twl_o_prog T;
          b \<leftarrow> SPEC(\<lambda>_. True);
          RETURN (b, T)
        })
        (b, False, S\<^sub>0);
    if brk then RETURN T
    else \<comment>\<open>finish iteration is required only\<close>
      cdcl_twl_stgy_prog T
  }
  \<close>

lemma wf_cdcl_twl_stgy_measure_break:
  \<open>wf ({((bT, brkT, T), (bS, brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union>
          {((bT, brkT, T), (bS, brkS, S)). S = T \<and> brkT \<and> \<not>brkS}
          )\<close>
    (is \<open>?wf ?R\<close>)
proof -
  have 1: \<open>wf ({((brkT, T), brkS, S). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union>
    {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS})\<close>
    (is \<open>wf ?S\<close>)
    by (rule wf_cdcl_twl_stgy_measure)
  have \<open>wf {((bT, T), (bS, S)). (T, S) \<in> ?S}\<close>
    apply (rule wf_snd_wf_pair)
    apply (rule wf_subset)
    apply (rule 1)
    apply auto
    done
  then show ?thesis
    apply (rule wf_subset)
    apply auto
    done
qed

lemma cdcl_twl_stgy_prog_break_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_prog_break S \<le> conclusive_TWL_run S\<close>
  unfolding cdcl_twl_stgy_prog_break_def full_def conclusive_TWL_run_def
  apply (refine_vcg cdcl_twl_stgy_prog_spec[unfolded conclusive_TWL_run_def]
       WHILEIT_rule[where
     R = \<open>{((bT, brkT, T), (bS, brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union>
          {((bT, brkT, T), (bS, brkS, S)). S = T \<and> brkT \<and> \<not>brkS}\<close>];
      remove_dummy_vars)
  \<comment> \<open>Well foundedness of the relation\<close>
  subgoal using wf_cdcl_twl_stgy_measure_break .

  \<comment> \<open>initial invariants:\<close>
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp

  \<comment> \<open>loop invariants:\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal for x a aa ba xa x1a
    by (rule cdcl_twl_o_final_twl_state[of S a aa ba]) simp_all
  subgoal for x a aa ba xa x1a
    by (rule cdcl_twl_o_prog_cdcl_twl_stgy[of S a aa ba xa x1a]) fast+
  subgoal by simp
  subgoal for brk0 T U brl V
    by clarsimp

  \<comment> \<open>Final properties\<close>
  subgoal for x a aa ba xa xb  \<comment> \<open>termination\<close>
    using cdcl_twl_stgy_in_measure[of S a aa ba xa] by fast
  subgoal by simp
  subgoal by fast

  \<comment> \<open>second loop\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal using assms by auto
  done

end