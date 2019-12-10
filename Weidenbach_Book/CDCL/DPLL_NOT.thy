theory DPLL_NOT
imports CDCL_NOT
begin

chapter \<open>DPLL\<close>

text \<open>
  We have developed two variants of DPLL: the first one is based on NOT's CDCL, instantiated
  with specific conditions. Then we have also formalised Weidenbach's chapter about DPLL. We
  have also showed the equivalence between both.
  \<close>


section \<open>DPLL as an Instance of NOT\<close>

subsection \<open>DPLL with Backtracking\<close>

text \<open>We are using a concrete pair instead of an abstract state.\<close>

locale dpll_with_backtrack
begin

inductive backtrack :: \<open>('v, unit) ann_lits \<times> 'v clauses
  \<Rightarrow> ('v, unit) ann_lits \<times> 'v clauses \<Rightarrow> bool\<close> where
\<open>backtrack_split (fst S) = (M', L # M) \<Longrightarrow> is_decided L \<Longrightarrow> D \<in># snd S \<Longrightarrow>
  fst S \<Turnstile>as CNot D \<Longrightarrow> backtrack S (Propagated (- lit_of L) () # M, snd S)\<close>

inductive_cases backtrackE[elim]: \<open>backtrack (M, N) (M', N')\<close>

lemma backtrack_is_backjump: (* \htmllink{backtrack_is_backjump} *)
  fixes M M' :: \<open>('v, unit) ann_lits\<close>
  assumes
    backtrack: \<open>backtrack (M, N) (M', N')\<close> and
    no_dup: \<open>(no_dup \<circ> fst) (M, N)\<close> and
    decomp: \<open>all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
    shows \<open>
       \<exists>C F' K F L l C'.
          M = F' @ Decided K # F \<and>
          M' = Propagated L l # F \<and> N = N' \<and> C \<in># N \<and> F' @ Decided K # F \<Turnstile>as CNot C \<and>
          undefined_lit F L \<and> atm_of L \<in> atms_of_mm N \<union> atm_of ` lits_of_l (F' @ Decided K # F) \<and>
          N \<Turnstile>pm C' + {#L#} \<and> F \<Turnstile>as CNot C'\<close>
proof -
  let ?S = \<open>(M, N)\<close>
  let ?T = \<open>(M', N')\<close>
  obtain F F' P L D where
    b_sp: \<open>backtrack_split M = (F', L # F)\<close>  and
    \<open>is_decided L\<close> and
    \<open>D \<in># snd ?S\<close> and
    \<open>M \<Turnstile>as CNot D\<close> and
    bt: \<open>backtrack ?S (Propagated (- (lit_of L)) P # F, N)\<close> and
    M': \<open>M' = Propagated (- (lit_of L)) P # F\<close> and
    [simp]: \<open>N' = N\<close>
  using backtrackE[OF backtrack] by (metis backtrack fstI sndI)
  let ?K = \<open>lit_of L\<close>
  let ?C = \<open>image_mset lit_of {#K\<in>#mset M. is_decided K \<and> K\<noteq>L#} :: 'v clause\<close>
  let ?C' = \<open>set_mset (image_mset (\<lambda>C. add_mset C {#}) (?C+{#?K#}))\<close>
  obtain K where L: \<open>L = Decided K\<close> using \<open>is_decided L\<close> by (cases L) auto

  have M: \<open>M = F' @ Decided K # F\<close>
    using b_sp by (metis L backtrack_split_list_eq fst_conv snd_conv)
  moreover have CNot_D: \<open>F' @ Decided K # F \<Turnstile>as CNot D\<close>
    using \<open>M\<Turnstile>as CNot D\<close> unfolding M .
  moreover have undef: \<open>undefined_lit F (-?K)\<close>
    using no_dup unfolding M L by (simp add: defined_lit_map image_Un)
  moreover have atm_K: \<open>atm_of (-K) \<in> atms_of_mm N \<union> atm_of ` lits_of_l (F' @ Decided K # F)\<close>
    by auto
  moreover {
    have \<open>set_mset N \<union> ?C' \<Turnstile>ps {{#}}\<close>
    proof -
      have A: \<open>set_mset N \<union> ?C' \<union> unmark_l M = set_mset N \<union> unmark_l M\<close>
        unfolding M L by auto
      have \<open>set_mset N \<union> {{#lit_of L#} |L. is_decided L \<and> L \<in> set M}
        \<Turnstile>ps unmark_l M\<close>
        using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
      moreover have C': \<open>?C' = {{#lit_of L#} |L. is_decided L \<and> L \<in> set M}\<close>
        unfolding M L by standard (force intro: IntI)+
      ultimately have N_C_M: \<open>set_mset N \<union> ?C' \<Turnstile>ps unmark_l M\<close>
        by auto
      have \<open>set_mset N \<union> (\<lambda>L. {#lit_of L#}) ` (set M) \<Turnstile>ps {{#}}\<close>
        unfolding true_clss_clss_def
      proof (intro allI impI, goal_cases)
        case (1 I) note tot = this(1) and cons = this(2) and I_N_M = this(3)
        have \<open>I \<Turnstile> D\<close>
          using I_N_M \<open>D \<in># snd ?S\<close> unfolding true_clss_def by auto
        moreover {
          have "lits_of_l (F' @ Decided K # F) \<subseteq> I"
            using I_N_M M true_clss_singleton_lit_of_implies_incl by blast
          then have \<open>I \<Turnstile>s CNot D\<close>
            by (meson CNot_D true_annots_true_cls true_cls_mono_set_mset_l true_clss_def) }
        ultimately show ?case using cons consistent_CNot_not by blast
      qed
      then show ?thesis
        using true_clss_clss_left_right[OF N_C_M, of \<open>{{#}}\<close>] unfolding A by auto
    qed
    have \<open>N \<Turnstile>pm image_mset uminus ?C + {#-?K#}\<close>
      unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
      proof (intro allI impI)
        fix I
        assume
          tot: \<open>total_over_set I (atms_of_ms (set_mset N \<union> {image_mset uminus ?C + {#- ?K#}})) \<close> and
          cons: \<open>consistent_interp I\<close> and
          \<open>I \<Turnstile>sm N\<close>
        have \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
          using cons tot unfolding consistent_interp_def L by (cases K) auto
        have \<open>{a \<in> set M. is_decided a \<and> a \<noteq> Decided K} =
          set M \<inter> {L. is_decided L \<and> L \<noteq> Decided K}\<close>
          by auto
        then have
          tI: \<open>total_over_set I (atm_of ` lit_of ` (set M \<inter> {L. is_decided L \<and> L \<noteq> Decided K}))\<close>
          using tot by (auto simp add: L atms_of_uminus_lit_atm_of_lit_of)

        then have H: \<open>-lit_of L \<in> I\<close> if L_I: \<open>lit_of L \<notin> I\<close> and L_M: \<open>L \<in> set M\<close> and
          dec_L: \<open>is_decided L\<close> and not_K: \<open>L \<noteq> Decided K\<close> for L
          proof -
            have \<open>atm_of (lit_of L) \<in> atm_of ` lit_of ` (set M \<inter> {m. is_decided m \<and> m \<noteq> Decided K})\<close>
              using L_M dec_L not_K by blast
            then have \<open>Pos (atm_of (lit_of L)) \<in> I \<or> Neg (atm_of (lit_of L)) \<in> I\<close>
              using tI unfolding total_over_set_def by blast
            then show \<open>- lit_of L \<in> I\<close>
              using L_I by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                literal.sel(1,2))
          qed
        have \<open>\<not>I \<Turnstile>s ?C'\<close>
          using \<open>set_mset N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>sm N\<close>
          unfolding true_clss_clss_def total_over_m_def
          by (simp add: atms_of_uminus_lit_atm_of_lit_of atms_of_ms_single_image_atm_of_lit_of)
        then show \<open>I \<Turnstile> image_mset uminus ?C + {#- lit_of L#}\<close>
          unfolding true_clss_def true_cls_def
          using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
          unfolding L by (auto dest!: H)
      qed }
  moreover
    have \<open>set F' \<inter> {K. is_decided K \<and> K \<noteq> L} = {}\<close>
      using backtrack_split_fst_not_decided[of _ M] b_sp by auto
    then have \<open>F \<Turnstile>as CNot (image_mset uminus ?C)\<close>
       unfolding M CNot_def true_annots_def by (auto simp add: L lits_of_def)
  ultimately show ?thesis
    using M' \<open>D \<in># snd ?S\<close> L by force
qed

lemma backtrack_is_backjump':
  fixes M M' :: \<open>('v, unit) ann_lits\<close>
  assumes
    backtrack: \<open>backtrack S T\<close> and
    no_dup: \<open>(no_dup \<circ> fst) S\<close> and
    decomp: \<open>all_decomposition_implies_m (snd S) (get_all_ann_decomposition (fst S))\<close>
    shows \<open>
        \<exists>C F' K F L l C'.
          fst S = F' @ Decided K # F \<and>
          T = (Propagated L l # F, snd S) \<and> C \<in># snd S \<and> fst S \<Turnstile>as CNot C
          \<and> undefined_lit F L \<and> atm_of L \<in> atms_of_mm (snd S) \<union> atm_of ` lits_of_l (fst S) \<and>
          snd S \<Turnstile>pm C' + {#L#} \<and> F \<Turnstile>as CNot C'\<close>
  apply (cases S, cases T)
  using backtrack_is_backjump[of \<open>fst S\<close> \<open>snd S\<close> \<open>fst T\<close> \<open>snd T\<close>] assms by fastforce

sublocale dpll_state
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close> \<open>\<lambda>(M, N). (tl M, N)\<close>
  \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close>
  by unfold_locales (auto simp: ac_simps)

sublocale backjumping_ops
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close> \<open>\<lambda>(M, N). (tl M, N)\<close>
  \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close> \<open>\<lambda>_ _ _ S T. backtrack S T\<close>
  by unfold_locales

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T:
  \<open>reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S =
    (if length (fst S) \<ge> length F
    then drop (length (fst S) - length F) (fst S)
    else [],
    snd S)\<close> (is \<open>?R = ?C\<close>)
proof -
  have \<open>?R = (fst ?R, snd ?R)\<close>
    by (cases \<open>reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S\<close>) auto
  also have \<open>(fst ?R, snd ?R) = ?C\<close>
    by (auto simp: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop)
  finally show ?thesis .
qed

lemma backtrack_is_backjump'':
  fixes M M' :: \<open>('v, unit) ann_lits\<close>
  assumes
    backtrack: \<open>backtrack S T\<close> and
    no_dup: \<open>(no_dup \<circ> fst) S\<close> and
    decomp: \<open>all_decomposition_implies_m (snd S) (get_all_ann_decomposition (fst S))\<close>
    shows \<open>backjump S T\<close>
proof -
  obtain C F' K F L l C' where
    1: \<open>fst S = F' @ Decided K # F\<close> and
    2: \<open>T = (Propagated L l # F, snd S)\<close> and
    3: \<open>C \<in># snd S\<close> and
    4: \<open>fst S \<Turnstile>as CNot C\<close> and
    5: \<open>undefined_lit F L\<close> and
    6: \<open>atm_of L \<in> atms_of_mm (snd S) \<union> atm_of ` lits_of_l (fst S)\<close> and
    7: \<open>snd S \<Turnstile>pm C' + {#L#}\<close> and
    8: \<open>F \<Turnstile>as CNot C'\<close>
  using backtrack_is_backjump'[OF assms] by force
  show ?thesis
    apply (cases S)
    using backjump.intros[OF 1 _ _ 4 5 _ _ 8, of T] 2 backtrack 1 5 3 6 7
    by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop
      reduce_trail_to\<^sub>N\<^sub>O\<^sub>T simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
qed

lemma can_do_bt_step:
   assumes
     M: \<open>fst S = F' @ Decided K # F\<close> and
     \<open>C \<in># snd S\<close> and
     C: \<open>fst S \<Turnstile>as CNot C\<close>
   shows \<open>\<not> no_step backtrack S\<close>
proof -
  obtain L G' G where
    \<open>backtrack_split (fst S) = (G', L # G)\<close>
    unfolding M by (induction F' rule: ann_lit_list_induct) auto
  moreover then have \<open>is_decided L\<close>
     by (metis backtrack_split_snd_hd_decided list.distinct(1) list.sel(1) snd_conv)
  ultimately show ?thesis
     using backtrack.intros[of S G' L G C] \<open>C \<in># snd S\<close> C unfolding M by auto
qed

end


sublocale dpll_with_backtrack \<subseteq> decide_ops
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close>
  \<open>\<lambda>(M, N). (tl M, N)\<close> \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close>
  \<open>\<lambda>_ _. True\<close>
  by unfold_locales

context dpll_with_backtrack
begin
lemma undefined_lit_ex_decide\<^sub>N\<^sub>O\<^sub>T:
  \<open>atm_of L \<in> atms_of_mm (snd S) \<Longrightarrow> undefined_lit (fst S) L \<Longrightarrow> Ex (decide\<^sub>N\<^sub>O\<^sub>T S)\<close>
  using decide\<^sub>N\<^sub>O\<^sub>T.intros[of S L] state_eq\<^sub>N\<^sub>O\<^sub>T_ref by blast
end

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping_ops
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close>
  \<open>\<lambda>(M, N). (tl M, N)\<close> \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close>
  \<open>\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_ _ _ S T. backtrack S T\<close>
  \<open>\<lambda>_ _ _. True\<close>
  apply unfold_locales
   apply (metis (mono_tags, lifting) case_prod_beta comp_def dpll_with_backtrack.backtrack_is_backjump''
     dpll_with_backtrack.can_do_bt_step)
  using undefined_lit_ex_decide\<^sub>N\<^sub>O\<^sub>T by blast

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close>
  \<open>\<lambda>(M, N). (tl M, N)\<close> \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close>
  \<open>\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_ _ _ S T. backtrack S T\<close>
  \<open>\<lambda>_ _ _. True\<close>
  apply unfold_locales
  using dpll_bj_no_dup dpll_bj_all_decomposition_implies_inv apply fastforce
  done

context dpll_with_backtrack
begin
lemma wf_tranclp_dpll_inital_state:
  assumes fin: \<open>finite A\<close>
  shows \<open>wf {((M'::('v, unit) ann_lits, N'::'v clauses), ([], N))|M' N' N.
    dpll_bj\<^sup>+\<^sup>+ ([], N) (M', N') \<and> atms_of_mm N \<subseteq> atms_of_ms A}\<close>
  using wf_tranclp_dpll_bj[OF assms(1)] by (rule wf_subset) auto

corollary full_dpll_final_state_conclusive:
  fixes M M' :: \<open>('v, unit) ann_lits\<close>
  assumes
    full: \<open>full dpll_bj ([], N) (M', N')\<close>
  shows \<open>unsatisfiable (set_mset N) \<or> (M' \<Turnstile>asm N \<and> satisfiable (set_mset N))\<close>
  using assms full_dpll_backjump_final_state[of \<open>([],N)\<close> \<open>(M', N')\<close> \<open>set_mset N\<close>] by auto

corollary full_dpll_normal_form_from_init_state:
  fixes M M' :: \<open>('v, unit) ann_lits\<close>
  assumes
    full: \<open>full dpll_bj ([], N) (M', N')\<close>
  shows \<open>M' \<Turnstile>asm N \<longleftrightarrow> satisfiable (set_mset N)\<close>
proof -
  have \<open>no_dup M'\<close>
    using rtranclp_dpll_bj_no_dup[of \<open>([], N)\<close> \<open>(M', N')\<close>]
    full unfolding full_def by auto
  then have \<open>M' \<Turnstile>asm N \<Longrightarrow> satisfiable (set_mset N)\<close>
    using distinct_consistent_interp satisfiable_carac' true_annots_true_cls by blast
  then show ?thesis
  using full_dpll_final_state_conclusive[OF full] by auto
qed

interpretation conflict_driven_clause_learning_ops
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close>
  \<open>\<lambda>(M, N). (tl M, N)\<close> \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close>
  \<open>\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_ _ _ S T. backtrack S T\<close>
  \<open>\<lambda>_ _ _. True\<close> \<open>\<lambda>_ _. False\<close> \<open>\<lambda>_ _. False\<close>
  by unfold_locales

interpretation conflict_driven_clause_learning
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close>
  \<open>\<lambda>(M, N). (tl M, N)\<close> \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close>
  \<open>\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_ _ _ S T. backtrack S T\<close>
  \<open>\<lambda>_ _ _. True\<close> \<open>\<lambda>_ _. False\<close> \<open>\<lambda>_ _. False\<close>
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup by fastforce

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_is_dpll:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> dpll_bj S T\<close>
  by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T.simps learn.simps forget\<^sub>N\<^sub>O\<^sub>T.simps)

text \<open>Another proof of termination:\<close>
lemma \<open>wf {(T, S). dpll_bj S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}\<close>
  unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_is_dpll[symmetric]
  by (rule wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain) (auto simp: learn.simps forget\<^sub>N\<^sub>O\<^sub>T.simps)
end


subsection \<open>Adding Restarts\<close>

text \<open>This was mainly a test whether it was possible to instantiate the assumption of the locale.\<close>
locale dpll_withbacktrack_and_restarts =
  dpll_with_backtrack +
  fixes f :: \<open>nat \<Rightarrow> nat\<close>
  assumes unbounded: \<open>unbounded f\<close> and f_ge_1:\<open>\<And>n. n \<ge> 1 \<Longrightarrow> f n \<ge> 1\<close>
begin
  sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts
  fst snd \<open>\<lambda>L (M, N). (L # M, N)\<close> \<open>\<lambda>(M, N). (tl M, N)\<close>
  \<open>\<lambda>C (M, N). (M, add_mset C N)\<close> \<open>\<lambda>C (M, N). (M, removeAll_mset C N)\<close> f \<open>\<lambda>(_, N) S. S = ([], N)\<close>
  \<open>\<lambda>A (M, N). atms_of_mm N \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l M \<subseteq> atms_of_ms A \<and> finite A
    \<and> all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
  \<open>\<lambda>A T. (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)\<close> dpll_bj
  \<open>\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_ann_decomposition M)\<close>
  \<open>\<lambda>A _.  (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))\<close>
  apply unfold_locales
          apply (rule unbounded)
         using f_ge_1 apply fastforce
        apply (smt dpll_bj_all_decomposition_implies_inv dpll_bj_atms_in_trail_in_set
          dpll_bj_clauses id_apply prod.case_eq_if)
       apply (rule dpll_bj_trail_mes_decreasing_prop; auto; fail)
      apply (rename_tac A T U, case_tac T, simp; fail)
     apply (rename_tac A T U, case_tac U, simp; fail)
    using dpll_bj_clauses dpll_bj_all_decomposition_implies_inv dpll_bj_no_dup by fastforce+
end

end
