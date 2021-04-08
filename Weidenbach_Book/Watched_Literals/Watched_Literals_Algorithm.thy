theory Watched_Literals_Algorithm
  imports
    More_Sepref.WB_More_Refinement
    Watched_Literals_Transition_System
    Watched_Literals_All_Literals
begin

chapter \<open>First Refinement: Deterministic Rule Application\<close>

section \<open>Unit Propagation Loops\<close>

definition set_conflict_pre :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
  \<open>set_conflict_pre C S \<longleftrightarrow>
    (\<exists>L C'. let S' = (set_clauses_to_update (add_mset (L, C') (clauses_to_update S)) S) in
    twl_struct_invs S' \<and> twl_stgy_invs S' \<and> get_trail S' \<Turnstile>as CNot (clause C))\<close>

definition set_conflicting :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_conflicting = (\<lambda>C (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q).
    (M, N, U, Some (clause C), NE, UE, NS, US, N0, U0, {#}, {#}))\<close>

definition mop_set_conflicting :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>mop_set_conflicting = (\<lambda>C S. do {
     ASSERT (set_conflict_pre C S);
     RETURN (set_conflicting C S)})\<close>

definition propagate_lit_pre :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
\<open>propagate_lit_pre L' C S \<longleftrightarrow>
  (\<exists>L C'. let S' = (set_clauses_to_update (add_mset (L, C') (clauses_to_update S)) S) in
   twl_struct_invs S' \<and> twl_stgy_invs S' \<and> undefined_lit (get_trail S) L' \<and>
   L' \<in># all_lits_of_mm (clauses (get_clauses S) + unit_clss S))\<close>

definition propagate_lit :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_lit = (\<lambda>L' C (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q). do {
      (Propagated L' (clause C) # M, N, U, D, NE, UE, NS, US, N0, U0, WS, add_mset (-L') Q)})\<close>

definition mop_propagate_lit :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>mop_propagate_lit = (\<lambda>L' C S. do {
      ASSERT(propagate_lit_pre L' C S);
      RETURN (propagate_lit L' C S)})\<close>

definition update_clauseS_pre  :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
  \<open>update_clauseS_pre L C S \<longleftrightarrow>
   (let S = (set_clauses_to_update (add_mset (L, C) (clauses_to_update S)) S) in
     L \<in># watched C \<and> C \<in># get_clauses S \<and> twl_struct_invs S \<and> twl_stgy_invs S)\<close>

definition update_clauseS :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>update_clauseS = (\<lambda>L C (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q). do {
        ASSERT(update_clauseS_pre L C (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q));
        K \<leftarrow> SPEC (\<lambda>L. L \<in># unwatched C \<and> -L \<notin> lits_of_l M);
        if K \<in> lits_of_l M
        then RETURN (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)
        else do {
          (N', U') \<leftarrow> SPEC (\<lambda>(N', U'). update_clauses (N, U) C L K (N', U'));
          RETURN (M, N', U', D, NE, UE, NS, US, N0, U0, WS, Q)
        }
  })\<close>

definition all_lits_of_st :: \<open>'v twl_st \<Rightarrow> 'v literal multiset\<close> where
\<open>all_lits_of_st S \<equiv> all_lits_of_mm (clauses (get_clauses S) + unit_clss S + subsumed_clauses S +
    get_all_clauses0 S)\<close>

definition mop_lit_is_pos where
  \<open>mop_lit_is_pos L S = do {
     ASSERT(L \<in># all_lits_of_st S \<and>
        no_dup (get_trail S));
     RETURN (L \<in> lits_of_l (get_trail S))
  }\<close>

definition unit_propagation_inner_loop_body :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow>
  'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>unit_propagation_inner_loop_body = (\<lambda>L C S. do {
    do {
      bL' \<leftarrow> SPEC (\<lambda>K. K \<in># clause C);
      val_bL' \<leftarrow> mop_lit_is_pos bL' S;
      if val_bL'
      then RETURN S
      else do {
        L' \<leftarrow> SPEC (\<lambda>K. K \<in># watched C - {#L#});
        ASSERT (watched C = {#L, L'#});
        val_L' \<leftarrow> mop_lit_is_pos L' S;
        if val_L'
        then RETURN S
        else
          if \<forall>L \<in># unwatched C. -L \<in> lits_of_l (get_trail S)
          then
            if -L' \<in> lits_of_l (get_trail S)
            then do {mop_set_conflicting C S}
            else do {mop_propagate_lit L' C S}
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

lemma unit_propagation_inner_loop_body: (* \htmllink{unit_propagation_inner_loop_body} *)
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
           (T', S) \<in> measure (size \<circ> clauses_to_update)))\<close> (is ?spec is \<open>_ \<le> ?R\<close>) and
    \<open>nofail (unit_propagation_inner_loop_body L C
       (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S))\<close> (is ?fail)
proof -
  obtain M N U D NE UE NS US N0 U0 WS Q where
    S: \<open>S = (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    by (cases S) auto

  have \<open>C \<in># N + U\<close> and struct: \<open>struct_wf_twl_cls C\<close> and L_C: \<open>L \<in># watched C\<close> and
    uL_M: \<open>-L \<in> lits_of_l M\<close>
    using inv multi_member_split[OF x_WS]
    unfolding twl_struct_invs_def twl_st_inv.simps S
    by force+

  have uL: \<open>- L \<in> lits_of_l M\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
    using inv x_WS unfolding twl_struct_invs_def S pcdcl_all_struct_invs_def by auto

  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have alien_L: \<open>L \<in># all_lits_of_mm (clauses N + clauses U + (NE + NS + UE + US + N0 + U0))\<close> and
    n_d: \<open>no_dup M\<close>
    using uL unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S cdcl\<^sub>W_restart_mset_state in_all_lits_of_mm_ain_atms_of_iff)
  have \<open>C \<in># N + U \<Longrightarrow> b \<in># clause C \<Longrightarrow>
    b \<in># all_lits_of_mm (clauses N + clauses U + (NE + NS + UE + US + N0 + U0))\<close> for b C
    by (auto dest!: multi_member_split simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset)

  note [[goals_limit=15]]
  show ?spec
    using assms unfolding unit_propagation_inner_loop_body_def update_clause.simps
      mop_lit_is_pos_def nres_monad3
  proof (refine_vcg; (unfold prod.inject clauses_to_update.simps set_clauses_to_update.simps
        ball_simps)?;  clarify?; (unfold triv_forall_equality)?)
    fix L' :: \<open>'v literal\<close>
    assume
      \<open>clauses_to_update S \<noteq> {#}\<close> and
      twl_inv: \<open>twl_struct_invs S\<close>
    have \<open>C \<in># N + U\<close> and struct: \<open>struct_wf_twl_cls C\<close> and L_C: \<open>L \<in># watched C\<close>
      using twl_inv x_WS unfolding twl_struct_invs_def twl_st_inv.simps S by (auto; fail)+

    define WS' where \<open>WS' = WS - {#(L, C)#}\<close>
    have WS_WS': \<open>WS = add_mset (L, C) WS'\<close>
      using x_WS unfolding WS'_def S by auto

    have D: \<open>D = None\<close>
      using confl S by auto

    let ?S' = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, C) WS', Q)\<close>
    let ?T = \<open>(set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
    let ?T' = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, WS', Q)\<close>

    { \<comment> \<open>blocking literal\<close>
      fix K'
      assume
          K': \<open>K' \<in># clause C\<close>
      show \<open>K' \<in># all_lits_of_st (set_clauses_to_update
                      (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
        using K' \<open>C \<in># N + U\<close> by (auto dest!: multi_member_split
            simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset clauses_def S all_lits_of_st_def)

      show \<open>no_dup (get_trail
                    (set_clauses_to_update
                      (remove1_mset (L, C)
                        (clauses_to_update S))
                      S))\<close>
        using n_d by (auto simp: S)
      assume
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

      show \<open>L' \<in># all_lits_of_st (set_clauses_to_update
                      (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
        using L'_C' \<open>C \<in># N + U\<close> by (auto dest!: multi_member_split
            simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset clauses_def S all_lits_of_st_def)


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
          let ?T' = \<open>(M, N, U, Some (clause C), NE, UE, NS, US, N0, U0, {#}, {#})\<close>
          let ?T = \<open>set_conflicting C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
          assume uL': \<open>-L' \<in> lits_of_l ?M\<close>
          have cdcl: \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.conflict) (use uL' L' watched unwatched S in simp_all)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            using uL' L' watched unwatched by (simp add: set_conflicting_def WS_WS' S D)

          have \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding WS_WS'
            by (force intro: cdcl_twl_cp_twl_struct_invs)
          moreover have \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding WS_WS'
            by (force intro: cdcl_twl_cp_twl_stgy_invs)
          moreover have \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using D WS_WS' cdcl S by auto
          moreover have \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
            by (simp add: S WS'_def[symmetric] WS_WS' set_conflicting_def)

          moreover have \<open>get_trail (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S))
             S) \<Turnstile>as CNot (clause C)\<close>
             using unwatched uL' watched L' uL_M by (cases C; auto simp: true_annots_true_cls_def_iff_negation_in_model S)
         ultimately show \<open>mop_set_conflicting C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)
           \<le> ?R\<close>
           using assms
           by (auto simp: mop_set_conflicting_def set_conflict_pre_def Let_def S
              intro!: ASSERT_leI exI[of _ L] exI[of _ C])

        }


        { \<comment> \<open>if \<^term>\<open>-L' \<in> lits_of_l M \<close> else\<close>
           let ?S = \<open>(M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
          let ?T' = \<open>(Propagated L' (clause C) # M, N, U, None, NE, UE, NS, US, N0, U0, WS', add_mset (- L') Q)\<close>
          let ?S' = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, C) WS', Q)\<close>
          let ?T = \<open>propagate_lit L' C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
          assume uL': \<open>- L' \<notin> lits_of_l ?M\<close>

          have undef: \<open>undefined_lit M L'\<close>
            using uL' L' by (auto simp: S defined_lit_map lits_of_def atm_of_eq_atm_of)

          have cdcl: \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.propagate) (use uL' L' undef watched unwatched D S in simp_all)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            using uL' L' undef watched unwatched D S WS_WS' by (simp add: propagate_lit_def)

          moreover have  \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

          moreover have  \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using cdcl D WS_WS' by force
          moreover have  \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)
          moreover have \<open>L' \<in># all_lits_of_mm (clauses N + clauses U + (NE + UE))\<close>
            using L'_C' \<open>C \<in># N + U\<close> by (auto simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset
               dest!: multi_member_split)
          ultimately show \<open>mop_propagate_lit L' C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)
           \<le> ?R\<close>
           using x_WS inv inv_s undef
           by (auto simp: mop_propagate_lit_def propagate_lit_pre_def propagate_lit_def Let_def S
              intro!: ASSERT_leI exI[of _ L] exI[of _ C] dest: multi_member_split)
        }
      }

      fix La
\<comment> \<open>if \<^term>\<open>\<forall>L \<in># unwatched C. -L \<in> lits_of_l M\<close>, else\<close>
      {
        let ?S = \<open>(M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
        let ?S' = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, C) WS', Q)\<close>
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
          show \<open>update_clauseS_pre L C (M, N, U, D, NE, UE, NS, US, N0, U0, remove1_mset (L, C) WS, Q)\<close>
            using assms L_C \<open>C \<in># N + U\<close> unfolding update_clauseS_pre_def S Let_def
            by auto
          assume K: \<open>x \<in># unwatched C \<and> - x \<notin> lits_of_l M\<close>
          have uL: \<open>- L \<in> lits_of_l M\<close>
            using inv unfolding twl_struct_invs_def S WS_WS' by auto
          { \<comment> \<open>BLIT\<close>
            let ?T = \<open>(M, N, U, D, NE, UE, NS, US, N0, U0, remove1_mset (L, C) WS, Q)\<close>
            let ?T' = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, WS', Q)\<close>

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
          let ?T' = \<open>(M, a, b, None, NE, UE, NS, US, N0, U0, WS', Q)\<close>
          let ?T = \<open>(M, a, b, D, NE, UE, NS, US, N0, U0, remove1_mset (L, C) WS, Q)\<close>
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
  from SPEC_nofail[OF this] show ?fail .
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

definition pop_literal_to_update_pre where
  \<open>pop_literal_to_update_pre S \<longleftrightarrow>
     twl_struct_invs S \<and> twl_stgy_invs S \<and> clauses_to_update S = {#} \<and>
     literals_to_update S \<noteq> {#}\<close>

definition mop_pop_literal_to_update :: \<open>'v twl_st \<Rightarrow> ('v literal \<times> 'v twl_st) nres\<close> where
  \<open>mop_pop_literal_to_update S = do {
      ASSERT(pop_literal_to_update_pre S);
      L \<leftarrow> SPEC (\<lambda>L. L \<in># literals_to_update S);
      let S' = set_clauses_to_update {#(L, C)|C \<in># get_clauses S. L \<in># watched C#}
           (set_literals_to_update (literals_to_update S - {#L#}) S);
      RETURN (L, S')
   }\<close>

definition unit_propagation_outer_loop :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>unit_propagation_outer_loop S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs S \<and> twl_stgy_invs S \<and> cdcl_twl_cp\<^sup>*\<^sup>* S\<^sub>0 S \<and> clauses_to_update S = {#}\<^esup>
      (\<lambda>S. literals_to_update S \<noteq> {#})
      (\<lambda>S. do {
        (L, S') \<leftarrow> mop_pop_literal_to_update S;
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
  have assert_twl_cp: \<open>cdcl_twl_cp T T'\<close> (is ?twl) and
    assert_twl_struct_invs:
      \<open>twl_struct_invs T'\<close>
           (is \<open>twl_struct_invs ?T'\<close>) and
    assert_stgy_invs:
      \<open>twl_stgy_invs T'\<close> (is ?stgy)
     if
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      invs: \<open>twl_struct_invs T \<and> twl_stgy_invs T \<and>cdcl_twl_cp\<^sup>*\<^sup>* S T \<and> clauses_to_update T = {#}\<close> and
      eq: \<open>(L, set_clauses_to_update (Pair L `# {#C \<in># get_clauses T. L \<in># watched C#})
            (set_literals_to_update (remove1_mset L (literals_to_update T)) T)) =
       (L', T')\<close>
      for L T L' T'
  proof -
    from that have
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      \<open>cdcl_twl_cp\<^sup>*\<^sup>* S T\<close> and
      w_q: \<open>clauses_to_update T = {#}\<close> and
      eq[simp]: \<open>L' = L\<close> \<open>T' = (set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
        (set_literals_to_update (remove1_mset L (literals_to_update T)) T))\<close>
      by fast+
    have \<open>get_conflict T = None\<close>
      using w_q p invs unfolding twl_struct_invs_def by auto
    then obtain M N U NE UE NS US N0 U0 Q where
      T: \<open>T = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, Q)\<close>
      using w_q p by (cases T) auto
    define Q' where \<open>Q' = remove1_mset L Q\<close>
    have Q: \<open>Q = add_mset L Q'\<close>
      using L_T unfolding Q'_def T by auto

      \<comment> \<open>Show assertion that one step has been done\<close>
    show twl: ?twl
      unfolding eq T set_clauses_to_update.simps set_literals_to_update.simps literals_to_update.simps Q'_def[symmetric]
      unfolding Q get_clauses.simps
      by (rule cdcl_twl_cp.pop)
    then show \<open>twl_struct_invs ?T'\<close>
      using cdcl_twl_cp_twl_struct_invs struct_invs by blast


    then show ?stgy
      using twl cdcl_twl_cp_twl_stgy_invs[OF twl] invs by blast
  qed

  show ?thesis
    unfolding unit_propagation_outer_loop_def mop_pop_literal_to_update_def nres_monad3
    apply (refine_vcg WHILEIT_rule[where R = \<open>{(T, S). twl_struct_invs S \<and> cdcl_twl_cp\<^sup>+\<^sup>+ S T}\<close>])
                apply ((simp_all add: assms tranclp_wf_cdcl_twl_cp; fail)+)[6]
    subgoal unfolding pop_literal_to_update_pre_def by blast
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


section \<open>Other Rules\<close>

subsection \<open>Decide\<close>

definition find_unassigned_lit :: \<open>'v twl_st \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit = (\<lambda>S.
      SPEC (\<lambda>L.
        (L \<noteq> None \<longrightarrow> undefined_lit (get_trail S) (the L) \<and>
           (the L) \<in># all_lits_of_st S) \<and>
        (L = None \<longrightarrow> (\<nexists>L. undefined_lit (get_trail S) L \<and>
         L \<in># all_lits_of_st S))))\<close>

definition propagate_dec where
  \<open>propagate_dec = (\<lambda>L (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q).
     (Decided L # M, N, U, D, NE, UE, NS, US, N0, U0, WS, {#-L#}))\<close>

definition decide_or_skip_pre :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>decide_or_skip_pre S \<longleftrightarrow>
    clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and> get_conflict S = None \<and>
    twl_struct_invs S \<and> twl_stgy_invs S\<close>

definition decide_or_skip :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>decide_or_skip S = do {
     ASSERT(decide_or_skip_pre S);
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
  obtain M N U NE UE NS US N0 U0 where S: \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using assms by (cases S) auto
  have atm_N_U:
    \<open>atm_of L \<in> atms_of_ms (clause ` set_mset U) \<Longrightarrow>
       atm_of L \<in> atms_of_mm (clauses N + NE + NS + N0)\<close>
    \<open>atms_of_mm (get_all_clss (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})) = atms_of_mm (clauses N + NE + NS + N0)\<close>
    for L
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close> and unit: \<open>entailed_clss_inv (pstate\<^sub>W_of S)\<close>
      using twl unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        pcdcl_all_struct_invs_def
      by auto
    then show
      \<open>atm_of L \<in> atms_of_ms (clause ` set_mset U) \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses N + NE + NS + N0)\<close>
      \<open>atms_of_mm (get_all_clss (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})) = atms_of_mm (clauses N + NE + NS + N0)\<close>
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def S cdcl\<^sub>W_restart_mset_state image_Un)
  qed
  {
    fix L
    assume undef: \<open>undefined_lit M L\<close> and L: \<open>atm_of L \<in> atms_of_mm (clauses N + NE + NS + N0)\<close>
    let ?T = \<open>(Decided L # M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#- L#})\<close>
    have o: \<open>cdcl_twl_o (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) ?T\<close>
      by (rule cdcl_twl_o.decide) (use undef L in auto)
    have twl': \<open>twl_struct_invs ?T\<close>
      using S cdcl_twl_o_twl_struct_invs o twl by blast
    have twl_s': \<open>twl_stgy_invs ?T\<close>
      using S cdcl_twl_o_twl_stgy_invs o twl twl_s by blast
    note o twl' twl_s'
  } note H = this
  have H'[unfolded S, simp]:
    \<open>L \<in># all_lits_of_st S \<longleftrightarrow> atm_of L \<in> atms_of_mm (clauses N + NE + NS + N0)\<close> for L
    using atm_N_U(2)
    by (auto simp: S all_lits_of_st_def all_lits_def in_all_lits_of_mm_ain_atms_of_iff)
  show ?thesis
    using assms unfolding S find_unassigned_lit_def propagate_dec_def decide_or_skip_def
      atm_N_U
    apply (refine_vcg)
    subgoal unfolding decide_or_skip_pre_def by blast
    subgoal by fast
    subgoal by blast
    subgoal by (force simp: H elim!: cdcl_twl_oE cdcl_twl_stgyE cdcl_twl_cpE dest!: atm_N_U(1))
    subgoal by (force elim!: cdcl_twl_oE cdcl_twl_stgyE cdcl_twl_cpE)
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (auto elim!: cdcl_twl_oE)
    subgoal using atm_N_U(1) H' by (auto simp: cdcl_twl_o.simps decide)
    subgoal by auto
    subgoal by (auto elim!: cdcl_twl_oE)
    subgoal using atm_N_U H by auto
    subgoal using H H' atm_N_U by auto
    subgoal using H H' atm_N_U by auto
    subgoal by auto
    subgoal by auto
    subgoal using H H' atm_N_U by auto
    done
qed

declare decide_or_skip_spec[THEN order_trans, refine_vcg]


subsection \<open>Skip and Resolve Loop\<close>

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

definition tl_state :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st)\<close> where
  \<open>tl_state = (\<lambda>(M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q). do {
      (False, (tl M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q))})\<close>

definition mop_tl_state_pre :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>mop_tl_state_pre S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and>
          get_conflict S \<noteq> None \<and>
          count_decided (get_trail S) \<noteq> 0 \<and>
          get_trail S \<noteq> [] \<and>
          get_conflict S \<noteq> Some {#} \<and>
          is_proped (hd (get_trail S)) \<and>
          lit_of (hd (get_trail S)) \<in># all_lits_of_st S \<and>
          lit_of (hd (get_trail S)) \<notin># the (get_conflict S) \<and>
          -lit_of (hd (get_trail S)) \<notin># the (get_conflict S)\<close>

definition mop_tl_state :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>mop_tl_state = (\<lambda>S. do {
    ASSERT(mop_tl_state_pre S);
    RETURN(tl_state S)})\<close>

definition update_confl_tl_pre :: \<open>'v literal \<Rightarrow> 'v clause \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
\<open>update_confl_tl_pre L D S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and>
          get_conflict S \<noteq> None \<and>
          count_decided (get_trail S) \<noteq> 0 \<and>
          get_trail S \<noteq> [] \<and>
          get_conflict S \<noteq> Some {#} \<and>
          L \<in># D \<and>
          -L \<in># the (get_conflict S) \<and>
          hd (get_trail S) = Propagated L D \<and>
          L \<in># all_lits_of_st S\<close>

definition update_confl_tl :: \<open>'v literal \<Rightarrow> 'v clause \<Rightarrow> 'v twl_st \<Rightarrow> (bool \<times> 'v twl_st)\<close> where
  \<open>update_confl_tl = (\<lambda>L C (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q).
     (False, (tl M, N, U, Some (remove1_mset L (remove1_mset (-L) ((the D) \<union># C))), NE, UE, NS, US, N0, U0, WS, Q)))\<close>

definition mop_update_confl_tl :: \<open>'v literal \<Rightarrow> 'v clause \<Rightarrow> 'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>mop_update_confl_tl = (\<lambda>L C S. do {
     ASSERT(update_confl_tl_pre L C S);
     RETURN (update_confl_tl L C S)})\<close>

definition mop_lit_notin_conflict :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> bool nres\<close> where
  \<open>mop_lit_notin_conflict L S = do {
    ASSERT(get_conflict S \<noteq> None \<and> -L \<notin># the (get_conflict S) \<and> L \<in># all_lits_of_st S);
    RETURN (L \<notin># the (get_conflict S))
  }\<close>

definition mop_maximum_level_removed_pre :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
\<open>mop_maximum_level_removed_pre L S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and>
          get_conflict S \<noteq> None \<and>
          count_decided (get_trail S) \<noteq> 0 \<and>
          get_trail S \<noteq> [] \<and>
          get_conflict S \<noteq> Some {#} \<and>
          -L \<in># the (get_conflict S) \<and>
          L = lit_of (hd (get_trail S))\<close>

definition mop_maximum_level_removed :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> bool nres\<close> where
\<open>mop_maximum_level_removed L S = do {
   ASSERT (mop_maximum_level_removed_pre L S);
   RETURN (get_maximum_level (get_trail S) (remove1_mset (-L) (the (get_conflict S))) = count_decided (get_trail S))
}\<close>

definition mop_hd_trail_pre :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>mop_hd_trail_pre S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and>
      get_conflict S \<noteq> None \<and>
      get_trail S \<noteq> [] \<and> is_proped (hd (get_trail S)) \<and>
      get_conflict S \<noteq> Some {#}\<close>

definition mop_hd_trail :: \<open>'v twl_st \<Rightarrow> ('v literal \<times> 'v clause) nres\<close> where
  \<open>mop_hd_trail S = do{
     ASSERT(mop_hd_trail_pre S);
     SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail S))
  }\<close>

definition skip_and_resolve_loop :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>skip_and_resolve_loop S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>skip_and_resolve_loop_inv S\<^sub>0\<^esup>
        (\<lambda>(uip, S). \<not>uip \<and> \<not>is_decided (hd (get_trail S)))
        (\<lambda>(_, S).
          do {
            (L, C) \<leftarrow> mop_hd_trail S;
            b \<leftarrow> mop_lit_notin_conflict (-L) S;
            if b then
              do {mop_tl_state S}
            else do {
                b \<leftarrow> mop_maximum_level_removed L S;
                if b
                then
                  do {mop_update_confl_tl L C S}
                else
                  do {RETURN (True, S)}}
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
     (is \<open>_ \<le> ?R\<close>)
  unfolding skip_and_resolve_loop_def mop_hd_trail_def nres_monad3 mop_lit_notin_conflict_def
    mop_maximum_level_removed_def
proof (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(brk, S). Suc (length (get_trail S) - If brk 1 0))\<close>];
      remove_dummy_vars)
  let ?R = \<open>(\<lambda>a b. SPEC
          (\<lambda>s'. skip_and_resolve_loop_inv S s' \<and>
                (s', a, b)
                \<in> measure
                   (\<lambda>(brk, S).
                       Suc (length (get_trail S) - (if brk then 1 else 0)))))\<close>
  show \<open>wf (measure (\<lambda>(brk, S). Suc (length (get_trail S) - (if brk then 1 else 0))))\<close>
    by auto

  have neg: \<open>get_trail S \<Turnstile>as CNot (the (get_conflict S))\<close> if \<open>get_conflict S \<noteq> None\<close>
      using assms that unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def pcdcl_all_struct_invs_def
      by (cases S, auto simp add: cdcl\<^sub>W_restart_mset_state)
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
  have M_not_empty: \<open>get_trail T \<noteq> []\<close>
    using brk inv unfolding skip_and_resolve_loop_inv_def by auto
  then show \<open>mop_hd_trail_pre T\<close>
    using brk inv unfolding skip_and_resolve_loop_inv_def mop_hd_trail_pre_def
    by (cases \<open>get_trail T\<close>; cases \<open>hd (get_trail T)\<close>)  auto

  fix L :: \<open>'a literal\<close> and C
  assume
    LC: \<open>case (L, C) of (L, C) \<Rightarrow> Propagated L C = hd (get_trail T)\<close>

  obtain M N U D NE UE NS US N0 U0 WS Q where
    T: \<open>T = (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    by (cases T)


  obtain M' :: \<open>('a, 'a clause) ann_lits\<close> and D' where
    M: \<open>get_trail T = Propagated L C # M'\<close> and WS: \<open>WS = {#}\<close> and Q: \<open>Q = {#}\<close> and D: \<open>D = Some D'\<close> and
    st: \<open>cdcl_twl_o\<^sup>*\<^sup>* S T\<close> and twl: \<open>twl_struct_invs T\<close> and D': \<open>D' \<noteq> {#}\<close> and
    twl_stgy_S: \<open>twl_stgy_invs T\<close> and
    count_dec[simp]: \<open>count_decided (tl M) > 0\<close> \<open>count_decided (tl M) \<noteq> 0\<close> \<open>count_decided M \<noteq> 0\<close>
    using brk inv LC unfolding skip_and_resolve_loop_inv_def
    by (cases \<open>get_trail T\<close>; cases \<open>hd (get_trail T)\<close>) (auto simp: T)

  show \<open>get_conflict T \<noteq> None\<close>
     by (auto simp: T D)

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of T)\<close> and
       \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T)\<close> and
       alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close>
    using twl D D' M unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      pcdcl_all_struct_invs_def by auto
  then have \<open>M \<Turnstile>as CNot D'\<close> and n_d: \<open>no_dup M\<close> and
    confl_proped: \<open>\<And>L mark a b.
        a @ Propagated L mark # b = trail (state\<^sub>W_of T) \<longrightarrow>
        b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
    using M unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp add: cdcl\<^sub>W_restart_mset_state T D)
  then show \<open>- (- L) \<notin># the (get_conflict T)\<close>
    using M by (auto simp: T D dest!: multi_member_split uminus_lits_of_l_definedD)
  show alien_L: \<open>- L  \<in># all_lits_of_st T\<close>
    using alien M
    by (cases T)
      (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_st_def
        cdcl\<^sub>W_restart_mset_state in_all_lits_of_mm_ain_atms_of_iff)

  have LD': \<open>L \<notin># D'\<close>
    using \<open>M \<Turnstile>as CNot D'\<close> M n_d
    by (auto dest!: multi_member_split dest: uminus_lits_of_l_definedD simp: T)

  { \<comment> \<open>skip\<close>
    assume LD: \<open>- L \<notin># the (get_conflict T)\<close>
    let ?T = \<open>snd (tl_state T)\<close>
    have o_S_T: \<open>cdcl_twl_o T ?T\<close>
      using cdcl_twl_o.skip[of L \<open>the D\<close> C M' N U NE UE NS US N0 U0]
      using LD D inv M unfolding skip_and_resolve_loop_inv_def T WS Q D by (auto simp: tl_state_def)
    have st_T: \<open>cdcl_twl_o\<^sup>*\<^sup>* S ?T\<close>
      using st o_S_T by auto
    moreover have twl_T: \<open>twl_struct_invs ?T\<close>
      using struct_S twl o_S_T cdcl_twl_o_twl_struct_invs by blast
    moreover have twl_stgy_T: \<open>twl_stgy_invs ?T\<close>
      using twl o_S_T stgy_S twl_stgy_S cdcl_twl_o_twl_stgy_invs by blast
    moreover have \<open>tl M \<noteq> []\<close>
      using twl_T D D' unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def pcdcl_all_struct_invs_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state T tl_state_def)
    moreover have \<open>- lit_of (hd M) \<in># all_lits_of_st T\<close> \<open>is_proped (hd M)\<close>
       \<open>- lit_of (hd M) \<notin># the (get_conflict T)\<close>  \<open>lit_of (hd M) \<notin># the (get_conflict T)\<close>
      using M alien_L LD LD' D
      by (auto intro!: ASSERT_leI simp: T tl_state_def in_all_lits_of_mm_uminus_iff)
    ultimately show \<open>mop_tl_state T \<le> ?R brk T\<close>
      using WS Q D D' twl_stgy_S twl alien_L LD
      unfolding skip_and_resolve_loop_inv_def mop_tl_state_pre_def mop_tl_state_def all_lits_of_st_def
      by (auto intro!: ASSERT_leI simp: T tl_state_def in_all_lits_of_mm_uminus_iff)
  }

  { \<comment> \<open>resolve\<close>
    assume
      LD: \<open>\<not>- L \<notin># the (get_conflict T)\<close>

    have count_dec': \<open>count_decided M' = count_decided M\<close>
      using M unfolding T by auto
    then show mop_maximum_level_removed_pre: \<open>mop_maximum_level_removed_pre L T\<close>
      using count_dec twl_stgy_S twl D' LD M unfolding mop_maximum_level_removed_pre_def
      by (auto simp: T D WS Q simp del: count_dec)

    assume
      max: \<open>get_maximum_level (get_trail T) (remove1_mset (-L) (the (get_conflict T)))
        = count_decided (get_trail T)\<close>

    let ?D = \<open>remove1_mset (- L) (the (get_conflict T)) \<union># remove1_mset L C\<close>
    let ?T = \<open>snd (update_confl_tl L C T)\<close>

    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of T)\<close>
      using twl D D' M unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        pcdcl_all_struct_invs_def by auto
    then have \<open>L \<in># C\<close> \<open>M' \<Turnstile>as CNot (remove1_mset L C)\<close> \<open>M \<Turnstile>as CNot D'\<close>
      using M
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (force simp: T cdcl\<^sub>W_restart_mset_state D)+
    then have \<open>-L \<notin># C\<close>
      using n_d M by (auto simp: T add_mset_eq_add_mset Decided_Propagated_in_iff_in_lits_of_l
         dest!: multi_member_split)
    have \<open>L \<notin># D'\<close>
      using \<open>M \<Turnstile>as CNot D'\<close> M n_d
      by (auto simp: T Decided_Propagated_in_iff_in_lits_of_l
         dest!: multi_member_split)
    then have D_alt[simp]: \<open>D' \<union># C - {#L, - L#} = ?D\<close>
      \<open>the D \<union># C - {#L, - L#} = ?D\<close>
      using LD \<open>L \<in># C\<close> \<open>-L \<notin># C\<close>
      by (auto simp: T D sup_union_right1 dest!: multi_member_split)
    have o_S_T: \<open>cdcl_twl_o T ?T\<close>
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
      pcdcl_all_struct_invs_def by auto
      then have \<open>tl M \<Turnstile>as CNot ?D\<close>
        using M unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp add: cdcl\<^sub>W_restart_mset_state T update_confl_tl_def)
    }
    moreover have \<open>get_conflict ?T \<noteq> Some {#}\<close>
      using twl_stgy_T count_dec unfolding twl_stgy_invs_def update_confl_tl_def
        cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def T
        by (auto simp: trail.simps conflicting.simps)
    moreover have \<open>update_confl_tl_pre L C T\<close>
      using WS Q D D' mop_maximum_level_removed_pre twl_stgy_T twl twl_stgy_S M LD count_dec
        confl_proped[of \<open>[]\<close> L C \<open>M'\<close>] alien_L
      unfolding skip_and_resolve_loop_inv_def
      by (auto simp add: cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps all_lits_of_st_def
          cdcl\<^sub>W_restart_mset_state update_confl_tl_def T update_confl_tl_pre_def in_all_lits_of_mm_uminus_iff)
    ultimately show  \<open>mop_update_confl_tl L C T \<le> ?R brk T\<close>
      using WS Q D D' mop_maximum_level_removed_pre M count_dec unfolding skip_and_resolve_loop_inv_def
      by (auto simp add: cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
          cdcl\<^sub>W_restart_mset_state update_confl_tl_def T mop_update_confl_tl_def)
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


subsection \<open>Backtrack\<close>

definition extract_shorter_conflict_pre :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>extract_shorter_conflict_pre S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and> get_trail S \<noteq> []\<close>

definition extract_shorter_conflict :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>extract_shorter_conflict = (\<lambda>(M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q). do {
    ASSERT(extract_shorter_conflict_pre (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q));
    SPEC(\<lambda>S'. \<exists>D'. S' = (M, N, U, Some D', NE, UE, NS, US, N0, U0, WS, Q) \<and>
       D' \<subseteq># the D \<and> clause `# (N + U) + NE + NS + UE + US + N0 + U0 \<Turnstile>pm D' \<and> -lit_of (hd M) \<in># D')
  })\<close>

fun equality_except_conflict :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
\<open>equality_except_conflict (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)
    (M', N', U', D', NE', UE', NS', US', N0', U0', WS', Q') \<longleftrightarrow>
  M = M' \<and> N = N' \<and> U = U' \<and> NE = NE' \<and> UE = UE' \<and> NS = NS' \<and> US = US' \<and> N0 = N0' \<and> U0 = U0' \<and>
      WS = WS' \<and> Q = Q'\<close>

lemma extract_shorter_conflict_alt_def:
  \<open>extract_shorter_conflict S = do {
   ASSERT(extract_shorter_conflict_pre S);
    SPEC(\<lambda>S'. \<exists>D'. equality_except_conflict S S' \<and> Some D' = get_conflict S' \<and>
       D' \<subseteq># the (get_conflict S) \<and> clause `# (get_clauses S) + unit_clss S + subsumed_clauses S + get_all_clauses0 S \<Turnstile>pm D' \<and>
       -lit_of (hd (get_trail S)) \<in># D')}\<close>
  unfolding extract_shorter_conflict_def
  by (cases S) (auto simp: ac_simps intro!: bind_cong[OF refl])

definition reduce_trail_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>reduce_trail_bt = (\<lambda>L (M, N, U, D', NE, UE, WS, Q). do {
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
              get_level M K = get_maximum_level M (the D' - {#-L#}) + 1);
        RETURN (M1, N, U, D', NE, UE, WS, Q)
  })\<close>

definition propagate_bt_pre :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
  \<open>propagate_bt_pre L L' S \<longleftrightarrow> (\<exists>M N U D NE UE NS US WS Q M' D'.
    S = (M, N, U, Some D, NE, UE,NS, US,  WS, Q) \<and>
    twl_stgy_invs (M' @ M, N, U, Some D', NE, UE, NS, US, WS, Q) \<and>
    twl_struct_invs (M' @ M, N, U, Some D', NE, UE, NS, US, WS, Q) \<and>
    D \<subseteq># D' \<and>
    -L \<in># D \<and>
    get_conflict S \<noteq> None \<and>
    L' \<in># D - {#-L#} \<and>
    L \<noteq> -L' \<and>
    get_level (M) L' = get_maximum_level (M) (D - {#-L#}) \<and>
    undefined_lit M L \<and>
    L \<in># all_lits_of_st  (M, N, U, Some D, NE, UE, NS, US, WS, Q)\<and>
    L' \<in># all_lits_of_st  (M, N, U, Some D, NE, UE, NS, US, WS, Q) \<and>
    (set_mset (all_lits_of_m D) \<subseteq>
       set_mset (all_lits_of_st  (M, N, U, Some D, NE, UE, NS, US, WS, Q))))\<close>

definition propagate_bt :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_bt = (\<lambda>L L' (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q). do {
      (Propagated (-L) (the D) # M, N, add_mset (TWL_Clause {#-L, L'#} (the D - {#-L, L'#})) U,
      None, NE, UE, NS, US, N0, U0, WS, {#L#})
   })\<close>

definition mop_propagate_bt :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>mop_propagate_bt = (\<lambda>L L' S. do {
     ASSERT(propagate_bt_pre L L' S);
     RETURN (propagate_bt L L' S)
   })\<close>


definition propagate_unit_bt_pre :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
  \<open>propagate_unit_bt_pre L S \<longleftrightarrow> (\<exists>M N U NE UE NS US N0 U0 WS Q M' D'.
    S = (M, N, U, Some {#-L#}, NE, UE, NS, US, N0, U0, WS, Q) \<and>
    twl_stgy_invs (M' @ M, N, U, Some D', NE, UE, NS, US, N0, U0, WS, Q) \<and>
    twl_struct_invs (M' @ M, N, U, Some D', NE, UE, NS, US, N0, U0, WS, Q) \<and>
    {#-L#} \<subseteq># D' \<and>
    undefined_lit M L \<and>
    L \<in># all_lits_of_st (M, N, U, Some D', NE, UE, NS, US, N0, U0, WS, Q))\<close>

definition propagate_unit_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_unit_bt = (\<lambda>L (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q).
     (Propagated (-L) (the D) # M, N, U, None, NE, add_mset (the D) UE, NS, US, N0, U0, WS, {#L#}))\<close>


definition mop_propagate_unit_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>mop_propagate_unit_bt = (\<lambda>L S. do {
    ASSERT (propagate_unit_bt_pre L S);
    RETURN (propagate_unit_bt L S)
  })\<close>


definition mop_lit_hd_trail_pre :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>mop_lit_hd_trail_pre S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
      clauses_to_update S = {#} \<and> literals_to_update S = {#} \<and>
      get_conflict S \<noteq> None \<and>
      get_trail S \<noteq> [] \<and>
      get_conflict S \<noteq> Some {#}\<close>

definition mop_lit_hd_trail :: \<open>'v twl_st \<Rightarrow> ('v literal) nres\<close> where
  \<open>mop_lit_hd_trail S = do {
     ASSERT(mop_lit_hd_trail_pre S);
     SPEC(\<lambda>L. L = lit_of (hd (get_trail S)))
  }\<close>

definition backtrack_inv where
  \<open>backtrack_inv S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and> get_trail S \<noteq> [] \<and>
    get_conflict S \<noteq> None \<and> get_conflict S \<noteq> Some {#} \<and> -lit_of (hd (get_trail S)) \<in># the (get_conflict S) \<and>
    no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S) \<and> no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S)\<close>

definition find_lit_of_max_level where
   \<open>find_lit_of_max_level =  (\<lambda>S L. do {
    ASSERT(distinct_mset (the (get_conflict S)) \<and> -L \<in># the (get_conflict S));
    SPEC(\<lambda>L'. L' \<in># the (get_conflict S) - {#-L#} \<and>
      get_level (get_trail S) L' = get_maximum_level (get_trail S) (the (get_conflict S) - {#-L#}))
   })\<close>



definition backtrack :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>backtrack S =
    do {
      ASSERT(backtrack_inv S);
      L \<leftarrow> mop_lit_hd_trail S;
      S \<leftarrow> extract_shorter_conflict S;
      S \<leftarrow> reduce_trail_bt L S;

      if size (the (get_conflict S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level S L;
        mop_propagate_bt L L' S
      }
      else do {
        mop_propagate_unit_bt L S
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
    using twl_struct twl_stgy unfolding pcdcl_all_struct_invs_def twl_struct_invs_def
      twl_stgy_invs_def by auto
  let ?D' = \<open>the (conflicting ?S)\<close>
  have M_CNot_D': \<open>trail ?S \<Turnstile>as CNot ?D'\<close> and
     dist: \<open>distinct_mset ?D'\<close>
    using inv confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (cases \<open>conflicting ?S\<close>; cases S; auto simp: cdcl\<^sub>W_restart_mset_state; fail)+
  then have trail: \<open>get_trail S \<noteq> []\<close>
    using confl unfolding true_annots_true_cls_def_iff_negation_in_model
    by (cases S) (auto simp: cdcl\<^sub>W_restart_mset_state)
   have all_struct:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
      using twl_struct
      by (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def)
    then have uL_D: \<open>- lit_of (hd (get_trail S)) \<in># the (get_conflict S)\<close>
      using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
          \<open>state\<^sub>W_of S\<close>] ns_s ns_r confl twl_stgy
      by (auto simp: twl_st twl_stgy_invs_def pcdcl_all_struct_invs_def)

  show ?spec
    unfolding backtrack_def extract_shorter_conflict_def reduce_trail_bt_def
     mop_lit_hd_trail_def mop_propagate_bt_def mop_propagate_unit_bt_def
     find_lit_of_max_level_def
  proof (refine_vcg; remove_dummy_vars; clarify?)
    show \<open>backtrack_inv S\<close>
      using uL_D trail confl assms unfolding backtrack_inv_def by fast
    show \<open>mop_lit_hd_trail_pre S\<close>
      using trail confl assms unfolding mop_lit_hd_trail_pre_def
      by auto
    fix M M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and
      N U :: \<open>'a twl_clss\<close> and
      D :: \<open>'a clause option\<close> and D' :: \<open>'a clause\<close> and NE UE NS US N0 U0 :: \<open>'a clauses\<close> and
      WS :: \<open>'a clauses_to_update\<close> and Q :: \<open>'a lit_queue\<close> and K K' :: \<open>'a literal\<close>
    let ?S = \<open>(M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    let ?T = \<open>(M, N, U, Some D', NE, UE, NS, US, N0, U0, WS, Q)\<close>
    let ?U = \<open>(M1, N, U, Some D', NE, UE, NS, US, N0, U0, WS, Q)\<close>
    let ?MS = \<open>get_trail ?S\<close>
    let ?MT = \<open>get_trail ?T\<close>
    assume
      S: \<open>S = (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    show \<open>extract_shorter_conflict_pre ?S\<close>
      using assms trail unfolding S extract_shorter_conflict_pre_def by auto
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have alien_L: \<open>lit_of (hd M) \<in># all_lits_of_st ?S\<close>
    using trail unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def all_lits_of_st_def
    by (cases M) (auto simp: S cdcl\<^sub>W_restart_mset_state in_all_lits_of_mm_ain_atms_of_iff)

    assume
      D'_D: \<open>D' \<subseteq># the D\<close> and
      L_D': \<open>-lit_of (hd M) \<in># D'\<close>
    show \<open>distinct_mset (the (get_conflict ?U))\<close>
      using dist distinct_mset_mono[OF D'_D] by (auto simp: S cdcl\<^sub>W_restart_mset_state)
    show \<open>- lit_of (hd (get_trail ?S)) \<in># the (get_conflict ?U)\<close>
      using L_D' by (auto simp: S)

    assume
      N_U_NE_UE_D': \<open>clauses (N + U) + NE + NS + UE + US + N0 + U0 \<Turnstile>pm D'\<close> and
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
      using twl_struct twl_stgy unfolding twl_struct_invs_def twl_stgy_invs_def
        pcdcl_all_struct_invs_def by auto
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
      ultimately have \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D))
          < count_decided M\<close>
        using ns_r confl count_decided_ge_get_maximum_level[of M
	  \<open>remove1_mset (-lit_of (hd M)) (the D)\<close>]
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
      using cdcl\<^sub>W_restart_mset.backtrack_ex_decomp n_d
      by (auto simp: cdcl\<^sub>W_restart_mset_state S)

    define i where \<open>i = get_maximum_level M (remove1_mset (- lit_of (hd M)) D')\<close>

    let ?T =  \<open>(Propagated (-lit_of (hd M)) D' # M1, N,
      add_mset (TWL_Clause {#-lit_of (hd M), K#} (D' - {#-lit_of (hd M), K#})) U,
      None, NE, UE, NS, US, N0, U0, WS, {#lit_of (hd M)#})\<close>
    let ?T' = \<open>(Propagated (-lit_of (hd M)) D' # M1, N,
      add_mset (TWL_Clause {#-lit_of (hd M), K#} (D' - {#-lit_of (hd M), K#})) U,
      None, NE, UE, NS, US, N0, U0, WS, {#- (-lit_of (hd M))#})\<close>

    have lev_D': \<open>count_decided M = get_maximum_level (L'' # M') D'\<close>
      using count_decided_ge_get_maximum_level[of M D'] L'_D
        get_maximum_level_ge_get_level[of \<open>-lit_of L''\<close> D' M] unfolding M
      by (auto split: if_splits)

    have \<open>the D \<noteq> {#}\<close>
      using D'_D D'_empty L'_D by (auto)
    have uL'_D: \<open>lit_of L'' \<notin># D'\<close>
      using L_D' n_d M_CNot_D' by (auto simp: cdcl\<^sub>W_restart_mset_state M add_mset_eq_add_mset
          Decided_Propagated_in_iff_in_lits_of_l
        dest!: multi_member_split)

    { \<comment> \<open>conflict clause > 1 literal\<close>
      assume size_D: \<open>1 < size (the (get_conflict ?U))\<close> and
      K_D: \<open>K \<in># remove1_mset (- lit_of (hd ?MS)) (the (get_conflict ?U))\<close> and
      lev_K: \<open>get_level (get_trail ?U) K = get_maximum_level (get_trail ?U)
          (remove1_mset (- lit_of (hd (get_trail ?S))) (the (get_conflict ?U)))\<close>
      have neq: \<open>lit_of (hd M) \<noteq> - K\<close>
        using dist K_D D'_D L_D' distinct_mset_mono[OF D'_D]
        by (auto simp: S conflicting.simps M distinct_mset_remove1_All)
      moreover have \<open>undefined_lit M1 (lit_of (hd (get_trail ?S)))\<close>
        using decomp n_d M
        apply (auto simp: dest!: get_all_ann_decomposition_exists_prepend)
        apply (case_tac c; case_tac M2)
        apply auto
        done
      moreover have \<open>lit_of (hd (get_trail ?S)) \<in># all_lits_of_st ?S\<close>
        using alien_L by (auto simp: M)
      moreover have \<open>K \<in># all_lits_of_st ?S\<close>
        using alien  neq  mset_subset_eqD[OF D'_D in_diffD[OF K_D,
            unfolded get_conflict.simps option.sel]] assms(1)
        unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_st_def all_lits_of_st_def
        by (auto simp: S cdcl\<^sub>W_restart_mset_state in_all_lits_of_mm_ain_atms_of_iff
          dest!: multi_member_split)
      moreover have \<open>set_mset (all_lits_of_m D') \<subseteq> set_mset (all_lits_of_st ?S)\<close>
        using alien assms(1) atms_of_subset_mset_mono[OF D'_D]
        unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def all_lits_of_st_def
        by (fastforce simp: S cdcl\<^sub>W_restart_mset_state in_all_lits_of_mm_ain_atms_of_iff
             in_all_lits_of_m_ain_atms_of_iff)
      ultimately show \<open>propagate_bt_pre (lit_of (hd (get_trail ?S))) K ?U\<close>
        using \<open>the D \<noteq> {#}\<close> assms D'_D D'_empty L'_D K_D uL'_D lev_K
           get_all_ann_decomposition_exists_prepend[OF decomp] uL_D
        unfolding propagate_bt_pre_def S all_lits_of_st_def
        by (auto simp: L_D' intro!: exI[of _ \<open>take (length M - length M1) M\<close>]
           exI[of _ \<open>the D\<close>])
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
      have cdcl: \<open>cdcl_twl_o (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) ?T'\<close>
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
        subgoal using N_U_NE_UE_D' by (auto simp: ac_simps)
        subgoal using L_D' .
        subgoal using K_D by (auto dest: in_diffD)
        subgoal using lev_K lev_M_M1 K_D by (simp add: i_def max_M1_M1_D)
        done
    moreover have \<open>get_conflict ?T' = None \<and> clauses_to_update ?T' = {#} \<and> literals_to_update ?T' \<noteq> {#}\<close>
      unfolding WS Q
        using S cdcl_twl_o_twl_struct_invs twl_struct by (auto simp: propagate_bt_def)
    moreover have \<open>(\<forall>S'. \<not> cdcl_twl_o ?T' S')\<close> by (auto simp: cdcl_twl_o.simps)
    moreover have \<open>twl_struct_invs ?T'\<close>
        using S cdcl cdcl_twl_o_twl_struct_invs[OF cdcl] twl_struct twl_stgy by auto
    moreover have \<open>twl_stgy_invs ?T'\<close>
        using S cdcl cdcl_twl_o_twl_stgy_invs[OF cdcl] twl_struct twl_stgy by auto
    moreover have \<open>clauses_to_update ?T' = {#}\<close>
        using WS by (auto simp: propagate_bt_def)

    moreover have False if \<open>cdcl_twl_o ?T' (an, ao, ap, aq, ar, as, at, b)\<close>
        for an ao ap aq ar as at b
        using that by (auto simp: cdcl_twl_o.simps propagate_bt_def)
    ultimately show cdcl:
       \<open>cdcl_twl_o ?S (propagate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
       \<open>get_conflict (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) = None\<close>
       \<open>twl_struct_invs (propagate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
       \<open>twl_stgy_invs (propagate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
       \<open>clauses_to_update (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) = {#}\<close>
       \<open>\<And>S'. cdcl_twl_o (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) S' \<Longrightarrow> False\<close>
       \<open>literals_to_update (propagate_bt (lit_of (hd (get_trail ?S))) K ?U) = {#} \<Longrightarrow> False\<close>
      unfolding propagate_bt_def by auto
    }

    { \<comment> \<open>conflict clause has 1 literal\<close>
      assume \<open>\<not> 1 < size (the (get_conflict ?U))\<close>
      then have D': \<open>D' = {#-lit_of (hd M)#}\<close>
        using L'_D by (cases D') (auto simp: M)
      let ?T = \<open>(Propagated (- lit_of (hd M)) D' # M1, N, U, None, NE, add_mset D' UE, NS, US, N0, U0, WS,
        unmark (hd M))\<close>
      let ?T' = \<open>(Propagated (- lit_of (hd M)) D' # M1, N, U, None, NE, add_mset D' UE, NS, US, N0, U0, WS,
        {#- (-lit_of (hd M))#})\<close>

      have i_0: \<open>i = 0\<close>
        using i_def by (auto simp: D')

      have cdcl: \<open>cdcl_twl_o (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) ?T'\<close>
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
        subgoal using N_U_NE_UE_D' by (auto simp: ac_simps)
        done
      moreover have \<open>get_conflict ?T' = None\<close>
        by (auto simp add: propagate_unit_bt_def)

      moreover have \<open>twl_struct_invs ?T'\<close>
        using S cdcl cdcl_twl_o_twl_struct_invs twl_struct by blast

      moreover have \<open>twl_stgy_invs ?T'\<close>
        using S cdcl cdcl_twl_o_twl_stgy_invs twl_struct twl_stgy by blast
      moreover have \<open>clauses_to_update ?T' = {#}\<close>
        using WS by (auto simp add: propagate_unit_bt_def)
      ultimately show cdcl:
       \<open>cdcl_twl_o ?S (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
       \<open>get_conflict (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = None\<close>
       \<open>twl_struct_invs (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
       \<open>twl_stgy_invs (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
       \<open>clauses_to_update (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = {#}\<close>
      unfolding propagate_unit_bt_def by auto
      show False if \<open>literals_to_update (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = {#}\<close>
        using that by (auto simp add: propagate_unit_bt_def)
      fix an ao ap aq ar as at b
      show False if \<open>cdcl_twl_o (propagate_unit_bt (lit_of (hd (get_trail ?S))) ?U) (an, ao, ap, aq, ar, as, at, b)\<close>
        using that by (auto simp: cdcl_twl_o.simps propagate_unit_bt_def)
      have \<open>undefined_lit M1 (lit_of (hd (get_trail ?S)))\<close>
        using decomp n_d M
        apply (auto simp: dest!: get_all_ann_decomposition_exists_prepend)
        apply (case_tac c; case_tac M2)
        apply auto
        done
      then show \<open>propagate_unit_bt_pre (lit_of (hd (get_trail ?S))) ?U\<close>
        using \<open>the D \<noteq> {#}\<close> assms D'_D D'_empty L'_D uL'_D alien_L cdcl
           get_all_ann_decomposition_exists_prepend[OF decomp] uL_D
        unfolding propagate_unit_bt_pre_def S all_lits_of_st_def
        by (auto simp: L_D' D' intro!: exI[of _ \<open>take (length M - length M1) M\<close>]
           exI[of _ \<open>the D\<close>])
    }
  qed
  then show ?fail
    using nofail_simps(2) pwD1 by blast
qed

declare backtrack_spec[THEN order_trans, refine_vcg]


subsection \<open>Full loop\<close>

definition cdcl_twl_o_prog_pre :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_o_prog_pre S' \<longleftrightarrow>
     no_step cdcl_twl_cp S' \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      clauses_to_update S' = {#} \<and> literals_to_update S' = {#}\<close>

definition cdcl_twl_o_prog :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>cdcl_twl_o_prog S =
    do {
      ASSERT(cdcl_twl_o_prog_pre S);
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
       (\<not>brk \<longrightarrow> \<not> (\<forall>S'. \<not> cdcl_twl_o S S') \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ S T) \<and>
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>

lemma cdcl_twl_o_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close> and
    ns_cp: \<open>no_step cdcl_twl_cp S\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
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
    subgoal using assms unfolding cdcl_twl_o_prog_pre_def by auto
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
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    done
qed

declare cdcl_twl_o_prog_spec[THEN order_trans, refine_vcg]


section \<open>Full Strategy\<close>

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

lemma cdcl_twl_stgy_prog_spec: (* \htmllink{cdcl_twl_stgy_prog_spec} *)
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_prog S \<le> conclusive_TWL_norestart_run S\<close>
  unfolding cdcl_twl_stgy_prog_def full_def conclusive_TWL_norestart_run_def
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
  subgoal using assms by simp

\<comment> \<open>loop invariants:\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
  subgoal by simp
  subgoal for brk b x
    apply (subgoal_tac \<open>pcdcl\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of x)\<close>)
    subgoal
      using assms
        rtranclp_pcdcl_entailed_by_init[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of x\<close>]
      by (auto simp: twl_struct_invs_def)
    subgoal (*TODO Proof*)
      apply (auto simp: twl_struct_invs_def)
      apply (meson assms(1) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_trans)+
      done
    done
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
    \<open>get_conflict S = None\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_prog_break S \<le> conclusive_TWL_norestart_run S\<close>
  unfolding cdcl_twl_stgy_prog_break_def full_def conclusive_TWL_norestart_run_def
  apply (refine_vcg cdcl_twl_stgy_prog_spec[unfolded conclusive_TWL_norestart_run_def]
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
  subgoal using assms by simp

  \<comment> \<open>loop invariants:\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
  subgoal by simp+
  subgoal for brk b x xa
    apply (subgoal_tac \<open>pcdcl\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of xa)\<close>)
    subgoal
      using assms
        rtranclp_pcdcl_entailed_by_init[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of xa\<close>]
      by (auto simp: twl_struct_invs_def)
    subgoal (*TODO Proof*)
      apply (auto simp: twl_struct_invs_def)
      apply (meson assms(1) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_trans)+
      done
    done

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
  subgoal for brk b x
    apply (subgoal_tac \<open>pcdcl\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of x)\<close>)
    subgoal
      using assms
        rtranclp_pcdcl_entailed_by_init[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of x\<close>]
      by (auto simp: twl_struct_invs_def)
    subgoal (*TODO Proof*)
      apply (auto simp: twl_struct_invs_def)
      apply (meson assms(1) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_trans)+
      done
    done
  subgoal using assms by auto
  done

definition cdcl_twl_stgy_prog_early :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>cdcl_twl_stgy_prog_early S\<^sub>0 =
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
    RETURN (brk , T)
  }
  \<close>

lemma cdcl_twl_stgy_prog_early_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_prog_early S \<le> partial_conclusive_TWL_norestart_run S\<close>
  unfolding cdcl_twl_stgy_prog_early_def full_def partial_conclusive_TWL_norestart_run_def
  apply (refine_vcg
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
  subgoal using assms by simp

  \<comment> \<open>loop invariants:\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
  subgoal by simp
  subgoal for brk b x xa
    apply (subgoal_tac \<open>pcdcl\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of xa)\<close>)
    subgoal
      using assms
        rtranclp_pcdcl_entailed_by_init[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of xa\<close>]
      by (auto simp: twl_struct_invs_def)
    subgoal (*TODO Proof*)
      apply (auto simp: twl_struct_invs_def)
      apply (meson assms(1) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_trans)+
      done
    done
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
  done

end
