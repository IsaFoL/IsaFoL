theory CDCL_Two_Watched_Literals_Algorithm
  imports
    CDCL_Two_Watched_Literals_Transition_System
    WB_More_Refinement
begin

section \<open>First Refinement: Deterministic Rule Application\<close>

subsection \<open>Unit Propagation Loops\<close>

definition mark_conflict :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>mark_conflict = (\<lambda>C (M, N, U, D, NP, UP, WS, Q). (M, N, U, Some (clause C), NP, UP, {#}, {#}))\<close>

definition propgate_lit :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propgate_lit = (\<lambda>L' C (M, N, U, D, NP, UP, WS, Q).
      (Propagated L' (clause C) # M, N, U, D, NP, UP, WS, add_mset (-L') Q))\<close>

definition update_clauseS :: \<open>'v literal \<Rightarrow> 'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>update_clauseS = (\<lambda>L C (M, N, U, D, NP, UP, WS, Q). do {
        K \<leftarrow> SPEC (\<lambda>L. L \<in># unwatched C \<and> -L \<notin> lits_of_l M);
        (N', U') \<leftarrow> SPEC (\<lambda>(N', U'). update_clauses (N, U) C L K (N', U'));
        RETURN (M, N', U', D, NP, UP, WS, Q)
  })\<close>

definition unit_propagation_inner_loop_body :: "'v literal \<times> 'v twl_cls \<Rightarrow>
  'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>unit_propagation_inner_loop_body = (\<lambda>(L, C) (S::'v twl_st). do {
    L' \<leftarrow> SPEC (\<lambda>K. K \<in># watched C - {#L#});
    ASSERT (watched C = {#L, L'#});
    if L' \<in> lits_of_l (get_trail S)
    then RETURN S
    else
      if \<forall>L \<in># unwatched C. -L \<in> lits_of_l (get_trail S)
      then
        if -L' \<in> lits_of_l (get_trail S)
        then do {RETURN (mark_conflict C S)}
        else do {RETURN (propgate_lit L' C S)}
      else do {
        update_clauseS L C S
     }
  })
\<close>

definition unit_propagation_inner_loop :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>unit_propagation_inner_loop S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs S \<and> twl_stgy_invs S \<and> cdcl_twl_cp\<^sup>*\<^sup>* S\<^sub>0 S\<^esup>
      (\<lambda>S. clauses_to_update S \<noteq> {#})
      (\<lambda>S. do {
        C \<leftarrow> SPEC (\<lambda>C. C \<in># clauses_to_update S);
        let S' = set_clauses_to_update (clauses_to_update S - {#C#}) S;
        unit_propagation_inner_loop_body C S'
      })
      S\<^sub>0
\<close>

lemma unit_propagation_inner_loop_body:
  fixes S :: \<open>'v twl_st\<close>
  assumes
    \<open>clauses_to_update S \<noteq> {#}\<close> and
    WS: \<open>x \<in># clauses_to_update S\<close> and
    inv: \<open>twl_struct_invs S\<close> and
    inv_s: \<open>twl_stgy_invs S\<close> and
    confl: \<open>get_conflict S = None\<close>
  shows \<open>unit_propagation_inner_loop_body x (set_clauses_to_update (remove1_mset x (clauses_to_update S)) S)
    \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> twl_stgy_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and> (S', S) \<in> measure (size \<circ> clauses_to_update))\<close> (is ?spec) and
    \<open>nofail (unit_propagation_inner_loop_body x (set_clauses_to_update (remove1_mset x (clauses_to_update S)) S))\<close> (is ?fail)
proof -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S) auto
  obtain L C where x: \<open>x = (L, C)\<close> by (cases x)
  have \<open>C \<in># N + U\<close> and struct: \<open>struct_wf_twl_cls C\<close> and L_C: \<open>L \<in># watched C\<close>
    using inv WS unfolding twl_struct_invs_def twl_st_inv.simps S x by auto
  show ?fail
    unfolding unit_propagation_inner_loop_body_def Let_def x S
    by (cases C) (use struct L_C in \<open>auto simp: refine_pw_simps S x size_2_iff update_clauseS_def\<close>)
  note [[goals_limit=15]]
  show ?spec
    using assms unfolding unit_propagation_inner_loop_body_def x update_clause.simps
  proof (refine_vcg; (unfold prod.inject clauses_to_update.simps set_clauses_to_update.simps
        ball_simps)?; clarify?; unfold triv_forall_equality)
    fix L' :: \<open>'v literal\<close>
    assume
      \<open>clauses_to_update S \<noteq> {#}\<close> and
      WS: \<open>(L, C) \<in># clauses_to_update S\<close> and
      twl_inv: \<open>twl_struct_invs S\<close> and
      L': \<open>L' \<in># remove1_mset L (watched C)\<close>
    have \<open>C \<in># N + U\<close> and struct: \<open>struct_wf_twl_cls C\<close> and L_C: \<open>L \<in># watched C\<close>
      using twl_inv WS unfolding twl_struct_invs_def twl_st_inv.simps S by auto
    show watched: \<open>watched C = {#L, L'#}\<close>
      by (cases C) (use struct L_C L' in \<open>auto simp: size_2_iff\<close>)

    define WS' where \<open>WS' = WS - {#(L, C)#}\<close>
    have WS_WS': \<open>WS = add_mset (L, C) WS'\<close>
      using WS unfolding WS'_def S by auto
    have D: \<open>D = None\<close>
      using confl S by auto

    let ?S' = \<open>(M, N, U, None, NP, UP, add_mset (L, C) WS', Q)\<close>
    let ?T = \<open>(set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
    let ?T' = \<open>(M, N, U, None, NP, UP, WS', Q)\<close>

    { \<comment> \<open>if \<^term>\<open>L' \<in> lits_of_l M\<close>, then:\<close>
      assume L': \<open>L' \<in> lits_of_l (get_trail ?T)\<close>

      have \<open>cdcl_twl_cp ?S' ?T'\<close>
        by (rule cdcl_twl_cp.delete_from_working) (use L' watched S in simp_all)

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
          let ?T' = \<open>(M, N, U, Some (clause C), NP, UP, {#}, {#})\<close>
          let ?T = \<open>mark_conflict C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
          assume uL': \<open>-L' \<in> lits_of_l ?M\<close>
          have cdcl: \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.conflict) (use uL' L' watched unwatched S in simp_all)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            using uL' L' watched unwatched by (simp add: mark_conflict_def WS_WS' S D)

          show \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding WS_WS' mark_conflict_def
            by (force intro: cdcl_twl_cp_twl_struct_invs)
          show \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding WS_WS' mark_conflict_def
            by (force intro: cdcl_twl_cp_twl_stgy_invs)
          show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using D WS_WS' cdcl S mark_conflict_def by auto
          show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
            by (simp add: S WS'_def[symmetric] WS_WS' mark_conflict_def)
        }


        { \<comment> \<open>if \<^term>\<open>-L' \<in> lits_of_l M \<close> else\<close>
          let ?S = \<open>(M, N, U, D, NP, UP, WS, Q)\<close>
          let ?T' = \<open>(Propagated L' (clause C) # M, N, U, None, NP, UP, WS', add_mset (- L') Q)\<close>
          let ?S' = \<open>(M, N, U, None, NP, UP, add_mset (L, C) WS', Q)\<close>
          let ?T = \<open>propgate_lit L' C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)\<close>
          assume uL': \<open>- L' \<notin> lits_of_l ?M\<close>

          have undef: \<open>undefined_lit M L'\<close>
            using uL' L' by (auto simp: S defined_lit_map lits_of_def atm_of_eq_atm_of)

          have cdcl: \<open>cdcl_twl_cp ?S' ?T'\<close>
            by (rule cdcl_twl_cp.propagate) (use uL' L' undef watched unwatched D S in simp_all)
          then have cdcl: \<open>cdcl_twl_cp S ?T\<close>
            using uL' L' undef watched unwatched D S WS_WS' by (simp add: propgate_lit_def)

          show \<open>twl_struct_invs ?T\<close>
            using cdcl inv D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_struct_invs)

          show \<open>cdcl_twl_cp\<^sup>*\<^sup>* S ?T\<close>
            using cdcl D WS_WS' by force
          show \<open>twl_stgy_invs ?T\<close>
            using cdcl inv inv_s D unfolding S WS_WS' by (force intro: cdcl_twl_cp_twl_stgy_invs)
          show \<open>(?T, S) \<in> measure (size \<circ> clauses_to_update)\<close>
            by (simp add: WS'_def[symmetric] WS_WS' S propgate_lit_def)
        }
      }
      fix La

      \<comment> \<open>if \<^term>\<open>\<forall>L \<in># unwatched C. -L \<in> lits_of_l M\<close>, else\<close>
      {
        let ?S = \<open>(M, N, U, D, NP, UP, WS, Q)\<close>
        let ?S' = \<open>(M, N, U, None, NP, UP, add_mset (L, C) WS', Q)\<close>
        let ?T = \<open>set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S\<close>
        fix K M' N' U' D' WS'' NP' UP' Q' N'' U''
(*         assume \<open>?T = (M', N', U', D', NP', UP', WS'', Q')\<close> *)
        have \<open>update_clauseS L C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)
               \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> twl_stgy_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and> (S', S) \<in> measure (size \<circ> clauses_to_update))\<close>
          apply (rewrite at \<open>set_clauses_to_update _ \<hole>\<close> S)
          apply (rewrite at \<open>clauses_to_update \<hole>\<close> S)
          unfolding update_clauseS_def clauses_to_update.simps set_clauses_to_update.simps
          apply clarify
        proof refine_vcg
          fix x xa a b
          assume K: \<open>x \<in># unwatched C \<and> - x \<notin> lits_of_l M\<close> and
            update: \<open>case xa of (N', U') \<Rightarrow> update_clauses (N, U) C L x (N', U')\<close> and
            [simp]: \<open>xa = (a, b)\<close>
          let ?T' = \<open>(M, a, b, None, NP, UP, WS', Q)\<close>
          let ?T = \<open>(M, a, b, D, NP, UP, remove1_mset (L, C) WS, Q)\<close>
          have uL: \<open>- L \<in> lits_of_l M\<close>
            using inv unfolding twl_struct_invs_def S WS_WS' by auto
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
        moreover
          assume \<open>\<not>update_clauseS L C (set_clauses_to_update (remove1_mset (L, C) (clauses_to_update S)) S)
               \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> twl_stgy_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and> (S', S) \<in> measure (size \<circ> clauses_to_update))\<close>
          ultimately have False by fast
        then show \<open>- La \<in> lits_of_l (get_trail ?T)\<close>
          ..
      }
    }
  qed

qed

declare unit_propagation_inner_loop_body(1)[THEN order_trans, refine_vcg]

lemma unit_propagation_inner_loop:
  assumes \<open>twl_struct_invs S\<close> and inv: \<open>twl_stgy_invs S\<close>
  shows \<open>unit_propagation_inner_loop S \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
    cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and> clauses_to_update S' = {#})\<close>
  unfolding unit_propagation_inner_loop_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (size o clauses_to_update)\<close>])
          apply (auto simp: assms)
  apply (simp add: twl_struct_invs_def)
  done

declare unit_propagation_inner_loop[THEN order_trans, refine_vcg]

definition unit_propagation_outer_loop :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
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

lemma unit_propagation_outer_loop:
  assumes \<open>twl_struct_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and confl: \<open>get_conflict S = None\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>unit_propagation_outer_loop S \<le> SPEC (\<lambda>S'. twl_struct_invs S' \<and> cdcl_twl_cp\<^sup>*\<^sup>* S S' \<and>
    literals_to_update S' = {#} \<and> no_step cdcl_twl_cp S' \<and> twl_stgy_invs S')\<close>
  unfolding unit_propagation_outer_loop_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>{(T, S). twl_struct_invs S \<and> cdcl_twl_cp\<^sup>+\<^sup>+ S T}\<close>])
              apply ((simp_all add: assms tranclp_wf_cdcl_twl_cp; fail)+)[6]
  subgoal \<comment> \<open>Assertion\<close>
  proof -
    fix L T
    assume
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      twl: \<open>twl_struct_invs T \<and> twl_stgy_invs T \<and>cdcl_twl_cp\<^sup>*\<^sup>* S T \<and> clauses_to_update T = {#}\<close>
    then have
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      twl: \<open>twl_struct_invs T\<close> and
      \<open>cdcl_twl_cp\<^sup>*\<^sup>* S T\<close> and
      w_q: \<open>clauses_to_update T = {#}\<close>
      by fast+
    have \<open>get_conflict T = None\<close>
      using w_q p twl unfolding twl_struct_invs_def by auto
    then obtain M N U NP UP Q where
      T: \<open>T = (M, N, U, None, NP, UP, {#}, Q)\<close>
      using w_q p by (cases T) auto
    define Q' where \<open>Q' = remove1_mset L Q\<close>
    have Q: \<open>Q = add_mset L Q'\<close>
      using L_T unfolding Q'_def T by auto

    let ?T' = \<open>set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
      (set_literals_to_update (remove1_mset L (literals_to_update T)) T)\<close>
      \<comment> \<open>Show assertion that one step has been done\<close>
    show
      \<open>cdcl_twl_cp T ?T'\<close>
      unfolding T set_clauses_to_update.simps set_literals_to_update.simps literals_to_update.simps Q'_def[symmetric]
      unfolding Q get_clauses.simps
      by (rule cdcl_twl_cp.pop)
  qed
  subgoal \<comment> \<open>WHILE-loop invariants\<close>
  proof -
    fix L T
    assume
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      twl: \<open>twl_struct_invs T \<and> twl_stgy_invs T \<and> cdcl_twl_cp\<^sup>*\<^sup>* S T \<and> clauses_to_update T = {#}\<close>
    then have
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      twl: \<open>twl_struct_invs T\<close> and
      \<open>cdcl_twl_cp\<^sup>*\<^sup>* S T\<close> and
      w_q: \<open>clauses_to_update T = {#}\<close>
      by fast+
    have \<open>get_conflict T = None\<close>
      using w_q p twl unfolding twl_struct_invs_def by auto
    then obtain M N U NP UP Q where
      T: \<open>T = (M, N, U, None, NP, UP, {#}, Q)\<close>
      using w_q p by (cases T) auto
    define Q' where \<open>Q' = remove1_mset L Q\<close>
    have Q: \<open>Q = add_mset L Q'\<close>
      using L_T unfolding Q'_def T by auto

    let ?T' = \<open>set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
      (set_literals_to_update (remove1_mset L (literals_to_update T)) T)\<close>
      \<comment> \<open>Show assertion that one step has been done\<close>
    assume
      \<open>cdcl_twl_cp T ?T'\<close>

      \<comment> \<open>Show that the invariant still holds\<close>
    then show \<open>twl_struct_invs ?T'\<close>
      using cdcl_twl_cp_twl_struct_invs twl by blast

  qed
  subgoal
  proof -
    fix L T
    assume
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      twl: \<open>twl_struct_invs T \<and> twl_stgy_invs T \<and> cdcl_twl_cp\<^sup>*\<^sup>* S T \<and>clauses_to_update T = {#}\<close>
    then have
      p: \<open>literals_to_update T \<noteq> {#}\<close> and
      L_T: \<open>L \<in># literals_to_update T\<close> and
      twl: \<open>twl_struct_invs T\<close> and
      twl_s: \<open>twl_stgy_invs T\<close> and
      \<open>cdcl_twl_cp\<^sup>*\<^sup>* S T\<close> and
      w_q: \<open>clauses_to_update T = {#}\<close>
      by fast+
    have \<open>get_conflict T = None\<close>
      using w_q p twl unfolding twl_struct_invs_def by auto
    then obtain M N U NP UP Q where
      T: \<open>T = (M, N, U, None, NP, UP, {#}, Q)\<close>
      using w_q p by (cases T) auto
    define Q' where \<open>Q' = remove1_mset L Q\<close>
    have Q: \<open>Q = add_mset L Q'\<close>
      using L_T unfolding Q'_def T by auto

    let ?T' = \<open>set_clauses_to_update (Pair L `# {#Ca \<in># get_clauses T. L \<in># watched Ca#})
      (set_literals_to_update (remove1_mset L (literals_to_update T)) T)\<close>
      \<comment> \<open>Show assertion that one step has been done\<close>
    assume
      cdcl: \<open>cdcl_twl_cp T ?T'\<close>

    then show \<open>twl_stgy_invs ?T'\<close>
      using twl cdcl_twl_cp_twl_stgy_invs[OF cdcl] twl_s by blast

  qed
  subgoal by (simp; fail)
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal for T L U \<comment> \<open>Termination\<close>
    by auto
  subgoal \<comment> \<open>Final invariants\<close>
    by simp
  subgoal by simp
  subgoal by auto
  subgoal by (auto simp: cdcl_twl_cp.simps)
  subgoal by simp
  done

declare unit_propagation_outer_loop[THEN order_trans, refine_vcg]


subsection \<open>Other Rules\<close>

subsubsection \<open>Decide\<close>

definition find_unassigned_lit :: \<open>'v twl_st \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit = (\<lambda>S.
      SPEC (\<lambda>L.
        (L \<noteq> None \<longrightarrow> undefined_lit (get_trail S) (the L) \<and>
          atm_of (the L) \<in> atms_of_mm (clause `# get_clauses S)) \<and>
        (L = None \<longrightarrow> (\<nexists>L. undefined_lit (get_trail S) L \<and>
         atm_of L \<in> atms_of_mm (clause `# get_clauses S)))))\<close>

definition propagate_dec where
  \<open>propagate_dec = (\<lambda>L (M, N, U, D, NP, UP, WS, Q). (Decided L # M, N, U, D, NP, UP, WS, {#-L#}))\<close>

definition decide_or_skip :: "'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres" where
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
       (get_conflict T \<noteq> None \<longrightarrow> get_conflict T = Some {#}) \<and>
       no_step cdcl_twl_o T \<and> (brk \<longrightarrow> no_step cdcl_twl_stgy T) \<and> twl_struct_invs T \<and>
       twl_stgy_invs T \<and> clauses_to_update T = {#} \<and>
       (\<not>brk \<longrightarrow> literals_to_update T \<noteq> {#}) \<and>
       (\<not>no_step cdcl_twl_o S \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ S T))\<close>
proof -
  obtain M N U NP UP where S: \<open>S = (M, N, U, None, NP, UP, {#}, {#})\<close>
    using assms by (cases S) auto
  have atm_N_U:
    \<open>atm_of L \<in> atms_of_ms (clause ` set_mset N)\<close>
    if U: \<open>atm_of L \<in> atms_of_ms (clause ` set_mset U)\<close> and
       undef: \<open>undefined_lit M L\<close>
    for L
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close> and unit: \<open>unit_clss_inv S\<close>
      using twl unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    moreover have \<open>atm_of L \<notin> atms_of_mm NP\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain C where C: \<open>C \<in># NP\<close> and LC: \<open>atm_of L \<in> atms_of C\<close>
        by (auto  simp: S atms_of_ms_def atms_of_def)
      then obtain L' where \<open>C = {#L'#}\<close> and \<open>defined_lit M L'\<close>
        using unit by (auto simp: S Decided_Propagated_in_iff_in_lits_of_l)
      then show False
        using LC undef by (auto simp: atm_of_eq_atm_of)
    qed
    ultimately show ?thesis
      using that
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def S cdcl\<^sub>W_restart_mset_state image_Un)
  qed
  {
    fix L
    assume undef: \<open>undefined_lit M L\<close> and L: \<open>atm_of L \<in> atms_of_mm (clause `# N)\<close>
    let ?T = \<open>(Decided L # M, N, U, None, NP, UP, {#}, {#- L#})\<close>
    have o: \<open>cdcl_twl_o (M, N, U, None, NP, UP, {#}, {#}) ?T\<close>
      by (rule cdcl_twl_o.decide) (use undef L in \<open>auto\<close>)
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
          (\<not>brk \<longrightarrow> get_trail S \<noteq> [] \<and> get_conflict S \<noteq> Some {#}) \<and>
          (brk \<longrightarrow> no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S) \<and>
            no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S)))\<close>

definition tl_state :: \<open>'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>tl_state = (\<lambda>(M, N, U, D, NP, UP, WS, Q). (tl M, N, U, D, NP, UP, WS, Q))\<close>

definition update_confl_tl :: \<open>'v clause option \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>update_confl_tl = (\<lambda>D (M, N, U, _, NP, UP, WS, Q). (tl M, N, U, D, NP, UP, WS, Q))\<close>

definition skip_and_resolve_loop :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>skip_and_resolve_loop S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>skip_and_resolve_loop_inv S\<^sub>0\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail S)))
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
                do {RETURN (cdcl\<^sub>W_restart_mset.resolve_cls L D' C = {#},
                    update_confl_tl (Some (cdcl\<^sub>W_restart_mset.resolve_cls L D' C)) S)}
              else
                do {RETURN (True, S)}
          }
        )
        (get_conflict S\<^sub>0 = Some {#}, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma skip_and_resolve_loop_spec:
  assumes struct_S: \<open>twl_struct_invs S\<close> and stgy_S: \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and \<open>literals_to_update S = {#}\<close> and
    \<open>get_conflict S \<noteq> None\<close>
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
  then show \<open>skip_and_resolve_loop_inv S (get_conflict S = Some {#}, S)\<close>
    using assms by (cases S) (auto simp: skip_and_resolve_loop_inv_def cdcl\<^sub>W_restart_mset.skip.simps
          cdcl\<^sub>W_restart_mset.resolve.simps cdcl\<^sub>W_restart_mset_state)

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

  obtain M N U D NP UP WS Q where
    T: \<open>T = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases T)

  obtain M' :: \<open>('a, 'a clause) ann_lits\<close> and D' where
    M: \<open>get_trail T = Propagated L C # M'\<close> and WS: \<open>WS = {#}\<close> and Q: \<open>Q = {#}\<close> and D: \<open>D = Some D'\<close> and
    st: \<open>cdcl_twl_o\<^sup>*\<^sup>* S T\<close> and twl: \<open>twl_struct_invs T\<close> and D': \<open>D' \<noteq> {#}\<close> and
    twl_stgy_S: \<open>twl_stgy_invs T\<close>
    using brk inv LC unfolding skip_and_resolve_loop_inv_def
    by (cases \<open>get_trail T\<close>; cases \<open>hd (get_trail T)\<close>) (auto simp: T)

  { \<comment> \<open>skip\<close>
    assume
      LD: \<open>- L \<notin># the (get_conflict T)\<close>
    let ?T = \<open>tl_state T\<close>
    have o_S_T: \<open>cdcl_twl_o T ?T\<close>
      using cdcl_twl_o.skip[of L \<open>the D\<close> C M' N U NP UP]
      using LD D inv M  unfolding skip_and_resolve_loop_inv_def T WS Q D by (auto simp: tl_state_def)
    have st_T: \<open>cdcl_twl_o\<^sup>*\<^sup>* S ?T\<close>
      using st o_S_T by auto
    moreover have twl_T: \<open>twl_struct_invs ?T\<close>
      using struct_S twl o_S_T cdcl_twl_o_twl_struct_invs by blast
    moreover have twl_stgy_T: \<open>twl_stgy_invs ?T\<close>
      using twl o_S_T stgy_S twl_stgy_S cdcl_twl_o_twl_stgy_invs by blast
    moreover have \<open>tl M \<noteq> []\<close>
      using twl_T D D' unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by (auto simp add: cdcl\<^sub>W_restart_mset_state T tl_state_def)
    ultimately show \<open>skip_and_resolve_loop_inv S (False, tl_state T)\<close>
      using WS Q D D' unfolding skip_and_resolve_loop_inv_def tl_state_def T
      by simp

    show \<open>((False, ?T), (brk, T)) \<in> measure (\<lambda>(brk, S). Suc (length (get_trail S) - (if brk then 1 else 0)))\<close>
      using M_not_empty by (simp add: tl_state_def T M)

  }
  { \<comment> \<open>resolve\<close>
    assume
      LD: \<open>\<not>- L \<notin># the (get_conflict T)\<close> and
      max: \<open>get_maximum_level (get_trail T) (remove1_mset (- L) (the (get_conflict T))) = count_decided (get_trail T)\<close>
    let ?D = \<open>remove1_mset (- L) (the (get_conflict T)) \<union># remove1_mset L C\<close>
    let ?T = \<open>update_confl_tl (Some ?D) T\<close>
    have count_dec: \<open>count_decided M' = count_decided M\<close>
      using M unfolding T by auto
    then have o_S_T: \<open>cdcl_twl_o T ?T\<close>
      using cdcl_twl_o.resolve[of L \<open>the D\<close> C M' N U NP UP] LD D max M WS Q D
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
        using  M unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp add: cdcl\<^sub>W_restart_mset_state T update_confl_tl_def)
    }
    ultimately show \<open>skip_and_resolve_loop_inv S (?D = {#}, ?T)\<close>
      using WS Q D D' unfolding skip_and_resolve_loop_inv_def
      by (auto simp add: cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
          cdcl\<^sub>W_restart_mset_state update_confl_tl_def T)

    show \<open>((?D = {#}, ?T), (brk, T)) \<in> measure (\<lambda>(brk, S). Suc (length (get_trail S)
        - (if brk then 1 else 0)))\<close>
      using M_not_empty by (simp add: T update_confl_tl_def)
  }
  { \<comment> \<open>No step\<close>
    assume
      LD: \<open>\<not>- L \<notin># the (get_conflict T)\<close> and
      max: \<open>get_maximum_level (get_trail T) (remove1_mset (- L) (the (get_conflict T))) \<noteq> count_decided (get_trail T)\<close>

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
  \<open>extract_shorter_conflict = (\<lambda>(M, N, U, D, NP, UP, WS, Q).
    SPEC(\<lambda>S'. \<exists>D'. S' = (M, N, U, Some D', NP, UP, WS, Q) \<and>
       D' \<subseteq># the D \<and> clause `# (N + U) + NP + UP \<Turnstile>pm D' \<and> -lit_of (hd M) \<in># D'))\<close>


definition reduce_trail_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>reduce_trail_bt = (\<lambda>L (M, N, U, D', NP, UP, WS, Q). do {
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
              get_level M K = get_maximum_level M (the D' - {#-L#}) + 1);
        RETURN (M1, N, U, D', NP, UP, WS, Q)
  })\<close>

definition propgate_bt :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propgate_bt = (\<lambda>L L' (M, N, U, D, NP, UP, WS, Q).
    (Propagated (-L) (the D) # M, N, add_mset (TWL_Clause {#-L, L'#} (the D - {#-L, L'#})) U, None,
      NP, UP, WS, {#L#}))\<close>

definition propgate_unit_bt :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propgate_unit_bt = (\<lambda>L (M, N, U, D, NP, UP, WS, Q).
    (Propagated (-L) (the D) # M, N, U, None, NP, add_mset (the D) UP, WS, {#L#}))\<close>

definition backtrack_inv where
  \<open>backtrack_inv S \<longleftrightarrow> get_trail S \<noteq> []\<close>

definition backtrack :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>backtrack S =
    do {
      do {
        ASSERT(backtrack_inv S);
        let L = lit_of (hd (get_trail S));
        S \<leftarrow> extract_shorter_conflict S;
        S \<leftarrow> reduce_trail_bt L S;

        if size (the (get_conflict S)) > 1
        then do {
          L' \<leftarrow> SPEC(\<lambda>L'. L' \<in># the (get_conflict S) - {#-L#} \<and> L \<noteq> -L' \<and>
            get_level (get_trail S) L' = get_maximum_level (get_trail S) (the (get_conflict S) - {#-L#}));
          RETURN (propgate_bt L L' S)
        }
        else do {
          RETURN (propgate_unit_bt L S)
        }
      }
    }
  \<close>


context conflict_driven_clause_learning\<^sub>W
begin

lemma no_step_skip_hd_in_conflicting:
  assumes
    inv_s: "cdcl\<^sub>W_stgy_invariant S" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    ns: \<open>no_step skip S\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> \<open>conflicting S \<noteq> Some {#}\<close>
  shows \<open>-lit_of (hd (trail S)) \<in># the (conflicting S)\<close>
proof -
  let
    ?M = \<open>trail S\<close> and
    ?N = \<open>init_clss S\<close> and
    ?U = \<open>learned_clss S\<close> and
    ?k = \<open>backtrack_lvl S\<close> and
    ?D = \<open>conflicting S\<close>
  obtain D where D: \<open>?D = Some D\<close>
    using confl by (cases ?D) auto
  have M_D: \<open>?M \<Turnstile>as CNot D\<close>
    using inv D unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by auto
  then have tr: \<open>trail S \<noteq> []\<close>
    using confl D by auto
  obtain L M where M: \<open>?M = L # M\<close>
    using tr by (cases \<open>?M\<close>) auto
  have conlf_k: \<open>conflict_is_false_with_level S\<close>
    using inv_s unfolding cdcl\<^sub>W_stgy_invariant_def by simp
  then obtain L_k where
    L_k: \<open>L_k \<in># D\<close> and lev_L_k: \<open>get_level ?M L_k = ?k\<close>
    using confl D by auto
  have dec: \<open>?k = count_decided ?M\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  moreover {
    have \<open>no_dup ?M\<close>
      using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
    then have \<open>-lit_of L \<notin> lits_of_l M\<close>
      unfolding M by (auto simp: defined_lit_map lits_of_def uminus_lit_swap)
    }
  ultimately have L_D: \<open>lit_of L \<notin># D\<close>
    using M_D unfolding M by (auto simp add: true_annots_true_cls_def_iff_negation_in_model
        uminus_lit_swap)
  show ?thesis
  proof (cases L)
    case (Decided L') note L' = this(1)
    moreover have \<open>atm_of L' = atm_of L_k\<close>
      using lev_L_k count_decided_ge_get_level[of M L_k] unfolding M dec L'
      by (auto simp: get_level_cons_if split: if_splits)
    then have \<open>L' = -L_k\<close>
      using L_k L_D L' by (auto simp: atm_of_eq_atm_of)
    then show ?thesis using L_k unfolding D M L' by simp
  next
    case (Propagated L' C)
    then show ?thesis
      using ns confl by (auto simp: skip.simps M D)
  qed
qed

end


lemma backtrack_spec:
  assumes confl: \<open>get_conflict S \<noteq> None\<close> \<open>get_conflict S \<noteq> Some {#}\<close> and
    w_q: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close> and
    ns_s: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S)\<close> and
    ns_r: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S)\<close> and
    twl_struct: \<open>twl_struct_invs S\<close> and twl_stgy: \<open>twl_stgy_invs S\<close>
  shows \<open>backtrack S \<le> SPEC (\<lambda>T. cdcl_twl_o S T \<and> get_conflict T = None \<and> no_step cdcl_twl_o T \<and>
    twl_struct_invs T \<and> twl_stgy_invs T \<and> clauses_to_update T = {#} \<and>
    literals_to_update T \<noteq> {#})\<close>
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
  show ?thesis
    unfolding backtrack_def extract_shorter_conflict_def reduce_trail_bt_def
     (*  propgate_bt_def propgate_unit_bt_def *)
  proof (refine_vcg; remove_dummy_vars; clarify?)
    show \<open>backtrack_inv S\<close>
      using trail unfolding backtrack_inv_def .


    fix M M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and
      N U :: \<open>'a twl_clss\<close> and
      D :: \<open>'a clause option\<close> and D' :: \<open>'a clause\<close> and NP UP :: \<open>'a clauses\<close> and
      WS :: \<open>'a clauses_to_update\<close> and Q :: \<open>'a lit_queue\<close> and K K' :: \<open>'a literal\<close>
    let ?S = \<open>(M, N, U, D, NP, UP, WS, Q)\<close>
    let ?T = \<open>(M, N, U, Some D', NP, UP, WS, Q)\<close>
    let ?U = \<open>(M1, N, U, Some D', NP, UP, WS, Q)\<close>
    let ?MS = \<open>get_trail ?S\<close>
    let ?MT = \<open>get_trail ?T\<close>
    assume
      S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close> and
      D'_D: \<open>D' \<subseteq># the D\<close> and
      L_D': \<open>-lit_of (hd M) \<in># D'\<close> and
      N_U_NP_UP_D': \<open>clause `# (N + U) + NP + UP \<Turnstile>pm D'\<close> and
      decomp: \<open>(Decided K' # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
      lev_K': \<open>get_level M K' = get_maximum_level M (remove1_mset (- lit_of (hd ?MS))
               (the (Some D'))) + 1\<close>
    have WS: \<open>WS = {#}\<close> and Q: \<open>Q = {#}\<close>
      using w_q p unfolding S by auto

(*     assume \<open>1 < size (get_conflict ?U)\<close> and
      \<open>K \<in># remove1_mset (- lit_of (hd (get_trail ?S))) (the (get_conflict ?U))\<close> *)
    have uL_D: \<open>- lit_of (hd M) \<in># the D\<close>
      using decomp N_U_NP_UP_D' D'_D L_D' lev_K'
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
      None, NP, UP, WS, {#lit_of (hd M)#})\<close>
    let ?T' = \<open>(Propagated (-lit_of (hd M)) D' # M1, N,
      add_mset (TWL_Clause {#-lit_of (hd M), K#} (D' - {#-lit_of (hd M), K#})) U,
      None, NP, UP, WS, {#- (-lit_of (hd M))#})\<close>

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
(*       assume L'_D': \<open>L' \<in># remove1_mset (-lit_of (hd M)) D'\<close> and
        lev_L: \<open>get_level M1 L' = get_maximum_level M (remove1_mset (- lit_of (hd M)) D')\<close> *)
      have D'_ne_single: \<open>D' \<noteq> {#- lit_of (hd M)#}\<close>
        using size_D apply (cases D', simp)
        apply (rename_tac L D'')
        apply (case_tac D'')
        by simp_all
      have \<open>cdcl_twl_o (M, N, U, D, NP, UP, WS, Q) ?T'\<close>
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
        subgoal using N_U_NP_UP_D' .
        subgoal using L_D' .
        subgoal using K_D by (auto dest: in_diffD)
        subgoal using lev_K lev_M_M1 K_D by (simp add: i_def max_M1_M1_D)
        done
    then show cdcl: \<open>cdcl_twl_o ?S (propgate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
      unfolding WS Q by (auto simp: propgate_bt_def)

      show \<open>get_conflict (propgate_bt (lit_of (hd (get_trail ?S))) K ?U) = None\<close>
        by (auto simp: propgate_bt_def)

      show \<open>twl_struct_invs (propgate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
        using S cdcl cdcl_twl_o_twl_struct_invs twl_struct by (auto simp: propgate_bt_def)
      show \<open>twl_stgy_invs (propgate_bt (lit_of (hd (get_trail ?S))) K ?U)\<close>
        using S cdcl cdcl_twl_o_twl_stgy_invs twl_struct twl_stgy by blast
      show \<open>clauses_to_update (propgate_bt (lit_of (hd (get_trail ?S))) K ?U) = {#}\<close>
        using WS by (auto simp: propgate_bt_def)

      show False if \<open>cdcl_twl_o (propgate_bt (lit_of (hd (get_trail ?S))) K ?U) (an, ao, ap, aq, ar, as, at, b)\<close>
        for  an ao ap aq ar as at b
        using that by (auto simp: cdcl_twl_o.simps propgate_bt_def)

      show False if \<open>literals_to_update (propgate_bt (lit_of (hd (get_trail ?S))) K ?U) = {#}\<close>
        using that by (auto simp: propgate_bt_def)

    }

    { \<comment> \<open>conflict clause has 1 literal\<close>
      assume \<open>\<not> 1 < size (the (get_conflict ?U))\<close>
      then have D': \<open>D' = {#-lit_of (hd M)#}\<close>
        using L'_D by (cases D') (auto simp: M)
      let ?T = \<open>(Propagated (- lit_of (hd M)) D' # M1, N, U, None, NP, add_mset D' UP, WS,
        unmark (hd M))\<close>
      let ?T' = \<open>(Propagated (- lit_of (hd M)) D' # M1, N, U, None, NP, add_mset D' UP, WS,
        {#- (-lit_of (hd M))#})\<close>

      have i_0: \<open>i = 0\<close>
        using i_def by (auto simp: D')

      have \<open>cdcl_twl_o (M, N, U, D, NP, UP, WS, Q) ?T'\<close>
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
        subgoal using N_U_NP_UP_D' .
        done
      then show cdcl: \<open>cdcl_twl_o (M, N, U, D, NP, UP, WS, Q)
             (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
        by (auto simp add: propgate_unit_bt_def)
      show \<open>get_conflict (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = None\<close>
        by (auto simp add: propgate_unit_bt_def)

      show \<open>twl_struct_invs (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
        using S cdcl cdcl_twl_o_twl_struct_invs twl_struct by blast

      show \<open>twl_stgy_invs (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U)\<close>
        using S cdcl cdcl_twl_o_twl_stgy_invs twl_struct twl_stgy by blast
      show \<open>clauses_to_update (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = {#}\<close>
        using WS by (auto simp add: propgate_unit_bt_def)
      show False if \<open>literals_to_update (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U) = {#}\<close>
        using that by (auto simp add: propgate_unit_bt_def)
      fix an ao ap aq ar as at b
      show False if \<open>cdcl_twl_o (propgate_unit_bt (lit_of (hd (get_trail ?S))) ?U) (an, ao, ap, aq, ar, as, at, b) \<close>
        using that by (auto simp: cdcl_twl_o.simps propgate_unit_bt_def)
    }
  qed
qed

declare backtrack_spec[THEN order_trans, refine_vcg]


subsubsection \<open>Full loop\<close>

definition cdcl_twl_o_prog :: "'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres" where
  \<open>cdcl_twl_o_prog S =
    do {
      if get_conflict S = None
      then decide_or_skip S
      else do {
        T \<leftarrow> skip_and_resolve_loop S;
        if get_conflict T \<noteq> Some {#}
        then do {U \<leftarrow> backtrack T; RETURN (False, U)}
        else do {RETURN (True, T)}
      }
    }
  \<close>

lemma cdcl_twl_o_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close> and
    ns_cp: \<open>no_step cdcl_twl_cp S\<close>
  shows
    \<open>cdcl_twl_o_prog S \<le> SPEC(\<lambda>(brk, T). cdcl_twl_o\<^sup>*\<^sup>* S T \<and>
       (get_conflict T \<noteq> None \<longrightarrow> get_conflict T = Some {#}) \<and>
       no_step cdcl_twl_o T \<and> (brk \<longrightarrow> no_step cdcl_twl_stgy T) \<and> twl_struct_invs T \<and>
       twl_stgy_invs T \<and> clauses_to_update T = {#} \<and>
       (\<not>brk \<longrightarrow> literals_to_update T \<noteq> {#}) \<and>
       (\<not>no_step cdcl_twl_o S \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ S T))\<close>
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
    subgoal using assms by (auto elim!: cdcl_twl_oE simp: image_Un)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by (auto elim!: cdcl_twl_oE simp: image_Un)
    subgoal for x T using assms
      by (cases T) (auto elim!: cdcl_twl_stgyE cdcl_twl_oE cdcl_twl_cpE)

    \<comment> \<open>decision, if false\<close>
    subgoal using assms by (auto elim!: cdcl_twl_oE)
    subgoal by (auto simp: rtranclp_unfold elim!: cdcl_twl_oE)
    done
qed

declare cdcl_twl_o_prog_spec[THEN order_trans, refine_vcg]


subsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>cdcl_twl_stgy_prog S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs T \<and> twl_stgy_invs T \<and>
        (brk \<longrightarrow> no_step cdcl_twl_stgy T) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* S\<^sub>0 T \<and> clauses_to_update T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict T = None)\<^esup>
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

lemma wf_cdcl_twl_stgy_measure: \<open>wf ({((brkT, T), (brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union> {((brkT, T), (brkS, S)). S = T \<and> brkT \<and> \<not>brkS})\<close>
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

lemma cdcl_twl_stgy_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_prog S \<le> SPEC(\<lambda>T. full cdcl_twl_stgy S T)\<close>
  unfolding cdcl_twl_stgy_prog_def full_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>{((brkT, T), (brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union> {((brkT, T), (brkS, S)). S = T \<and> brkT \<and> \<not>brkS}\<close>];
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
  subgoal by blast
  subgoal for brk S' T brk' U
  proof -
    assume a1: "cdcl_twl_cp\<^sup>*\<^sup>* S' T"
    assume a2: "case (brk', U) of (brk, S') \<Rightarrow> cdcl_twl_o\<^sup>*\<^sup>* T S' \<and>
      (get_conflict S' \<noteq> None \<longrightarrow> get_conflict S' = Some {#}) \<and> no_step cdcl_twl_o S' \<and>
      (brk \<longrightarrow> no_step cdcl_twl_stgy S') \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      clauses_to_update S' = {#} \<and> (\<not> brk \<longrightarrow> literals_to_update S' \<noteq> {#}) \<and>
      (\<not> no_step cdcl_twl_o T \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ T S')"
    assume a3: "case (brk, S') of (brk, S') \<Rightarrow> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      (brk \<longrightarrow> no_step cdcl_twl_stgy S') \<and> cdcl_twl_stgy\<^sup>*\<^sup>* S S' \<and> clauses_to_update S' = {#} \<and>
      (\<not> brk \<longrightarrow> get_conflict S' = None)"
    have f4: "cdcl_twl_o\<^sup>*\<^sup>* T U \<and> (get_conflict U \<noteq> None \<longrightarrow> get_conflict U = Some {#}) \<and>
      no_step cdcl_twl_o U \<and> (brk' \<longrightarrow> no_step cdcl_twl_stgy U) \<and> twl_struct_invs U \<and>
      twl_stgy_invs U \<and> clauses_to_update U = {#} \<and> (\<not> brk' \<longrightarrow> literals_to_update U \<noteq> {#})"
      using a2 by fastforce
    have f5: "cdcl_twl_stgy\<^sup>*\<^sup>* S' T"
      using a1 by (metis cp mono_rtranclp)
    have "cdcl_twl_stgy\<^sup>*\<^sup>* T U"
      using f4 rtranclp_cdcl_twl_o_stgyD by blast
    then show ?thesis
      using f5 a3 by force
  qed
  subgoal by simp
  subgoal by (force simp: twl_struct_invs_def)
  \<comment> \<open>Final properties\<close>
  subgoal for brkT T U V'  \<comment> \<open>termination\<close>
  proof -
    assume
      T: \<open>case (brkT, T) of (brk, T) \<Rightarrow> twl_struct_invs T \<and> twl_stgy_invs T \<and>
        (brk \<longrightarrow> no_step cdcl_twl_stgy T) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* S T \<and> clauses_to_update T = {#} \<and>
        (\<not> brk \<longrightarrow> get_conflict T = None)\<close> and
      brkT: \<open>case (brkT, T) of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
      V': \<open>case V' of (brk, T) \<Rightarrow> cdcl_twl_o\<^sup>*\<^sup>* U T \<and>
      (get_conflict T \<noteq> None \<longrightarrow> get_conflict T = Some {#}) \<and>
      no_step cdcl_twl_o T \<and> (brk \<longrightarrow> no_step cdcl_twl_stgy T) \<and> twl_struct_invs T \<and>
      twl_stgy_invs T \<and> clauses_to_update T = {#} \<and> (\<not> brk \<longrightarrow> literals_to_update T \<noteq> {#}) \<and>
      (\<not> no_step cdcl_twl_o U \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ U T)\<close> and
      [simp]: \<open>twl_struct_invs U\<close> and
      TU: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T U\<close> and
      \<open>literals_to_update U = {#}\<close> and
      \<open>no_step cdcl_twl_cp U\<close> and
      [simp]: \<open>twl_stgy_invs U\<close>
    obtain brkV V where
      V'_V: \<open>V' = (brkV, V)\<close>
      by (cases V') auto
    then have
      UV: \<open>cdcl_twl_o\<^sup>*\<^sup>* U V\<close> and
      confl_V: \<open>get_conflict V \<noteq> None \<longrightarrow> get_conflict V = Some {#}\<close> and
      ns_o_V: \<open>no_step cdcl_twl_o V\<close> and
      brkV: \<open>brkV \<longrightarrow> no_step cdcl_twl_stgy V\<close> and
      \<open>\<not> brkV \<longrightarrow> literals_to_update V \<noteq> {#}\<close> and
      \<open>\<not> no_step cdcl_twl_o U \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ U V\<close> and
      [simp]: \<open>twl_struct_invs V\<close>
      using V' by auto

    have [simp]: \<open>twl_struct_invs T\<close>
      using T by auto
    have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T V\<close>
      using TU UV by (auto dest!: rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD)
    then have TV_or_tranclp_TV: \<open>T = V \<or> cdcl_twl_stgy\<^sup>+\<^sup>+ T V\<close>
      unfolding rtranclp_unfold by auto

    have [simp]: \<open>\<not>brkT\<close>
      using brkT by auto

    have \<open>brkV\<close> if \<open>T = V\<close>
    proof -
      have ns_TV: \<open>\<not>cdcl_twl_stgy\<^sup>+\<^sup>+ T V\<close>
        using that wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of T] by auto

      have ns_U_U: \<open>\<not>cdcl_twl_o\<^sup>+\<^sup>+ U U\<close>
        using wf_not_refl[OF tranclp_wf_cdcl_twl_o, of U] by auto
      have \<open>T = U\<close>
        by (metis (no_types, hide_lams) TU UV ns_TV rtranclp_cdcl_twl_cp_stgyD
            rtranclp_cdcl_twl_o_stgyD rtranclp_tranclp_tranclp rtranclp_unfold)
      then show brkV
        using T V' \<open>literals_to_update U = {#}\<close>  unfolding V'_V that[symmetric] by (auto simp: ns_U_U)
    qed
    then show \<open>(V', (brkT, T)) \<in> {((brkT, T), (brkS, S)). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<union>
      {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>
      using TV_or_tranclp_TV unfolding V'_V by auto
  qed
  subgoal by simp
  subgoal by fast
  done

end