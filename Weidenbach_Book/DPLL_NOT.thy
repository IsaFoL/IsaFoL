theory DPLL_NOT
imports CDCL_NOT
begin

section \<open>DPLL as an instance of NOT\<close>
subsection \<open>DPLL with simple backtrack\<close>
locale dpll_with_backtrack
begin
inductive backtrack :: "('v, dpll_marked_level, dpll_mark) marked_lit list \<times> 'v clauses
  \<Rightarrow> ('v, dpll_marked_level, dpll_mark) marked_lit list \<times> 'v clauses \<Rightarrow> bool" where
"backtrack_split (fst S)  = (M', L # M) \<Longrightarrow> is_marked L \<Longrightarrow> D \<in># snd S
  \<Longrightarrow> fst S \<Turnstile>as CNot D \<Longrightarrow> backtrack S (Propagated (- (lit_of L)) Proped # M, snd S)"

inductive_cases backtrackE[elim]: "backtrack (M, N) (M', N')"
lemma backtrack_is_backjump:
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
  assumes
    backtrack: "backtrack (M, N) (M', N')" and
    no_dup: "(no_dup \<circ> fst) (M, N)" and
    decomp: "all_decomposition_implies_m N (get_all_marked_decomposition M)"
    shows "
       \<exists>C F' K d F L l C'.
          M = F' @ Marked K d # F \<and>
          M' = Propagated L l # F \<and> N = N' \<and> C \<in># N \<and> F' @ Marked K d # F \<Turnstile>as CNot C \<and>
          undefined_lit L F \<and> atm_of L \<in> atms_of_mu N \<union> atm_of ` lits_of (F' @ Marked K d # F) \<and>
          N \<Turnstile>pm C' + {#L#} \<and> F \<Turnstile>as CNot C'"
proof -
  let ?S = "(M, N)"
  let ?T = "(M', N')"
  obtain F F' P L D where
    b_sp: "backtrack_split M = (F', L # F)"  and
    "is_marked L" and
    "D \<in># snd ?S" and
    "M \<Turnstile>as CNot D" and
    bt: "backtrack ?S (Propagated (- (lit_of L)) P # F, N)" and
    M': "M' = Propagated (- (lit_of L)) P # F" and
    [simp]: "N' = N"
  using backtrackE[OF backtrack] by (metis backtrack fstI sndI)
  let ?K = "lit_of L"
  let ?C = "image_mset lit_of {#K\<in>#mset M. is_marked K \<and> K\<noteq>L#} :: 'v literal multiset"
  let ?C' = "set_mset (image_mset single (?C+{#?K#}))"
  obtain K d where L: "L = Marked K d" using \<open>is_marked L\<close> by (cases L) auto

  have M: "M = F' @ Marked K d # F"
    using b_sp  by (metis L backtrack_split_list_eq fst_conv snd_conv)
  moreover have "F' @ Marked K d # F \<Turnstile>as CNot D"
    using \<open>M\<Turnstile>as CNot D\<close> unfolding M .
  moreover have "undefined_lit (-?K) F"
    using no_dup unfolding M L by (simp add: defined_lit_map)
  moreover have "atm_of (-K) \<in> atms_of_mu N \<union> atm_of ` lits_of (F' @ Marked K d # F)"
    by auto
  moreover
    have "set_mset N \<union> ?C' \<Turnstile>ps {{#}}"
      proof -
        have A: "set_mset N \<union> ?C' \<union> (\<lambda>a. {#lit_of a#}) ` set M  =
          set_mset  N \<union> (\<lambda>a. {#lit_of a#}) ` set M"
          unfolding M L by auto
        have "set_mset  N \<union> {{#lit_of L#} |L. is_marked L \<and> L \<in> set M}
            \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
          using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
        moreover have C': "?C' = {{#lit_of L#} |L. is_marked L \<and> L \<in> set M}"
          unfolding M L apply standard
            apply force
          using IntI by auto
        ultimately have N_C_M: "set_mset N \<union> ?C' \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
          by auto
        have "set_mset N \<union> (\<lambda>L. {#lit_of L#}) ` (set M) \<Turnstile>ps {{#}}"
          unfolding true_clss_clss_def
          proof (intro allI impI, goal_cases)
            case (1 I) note tot = this(1) and cons = this(2) and I_N_M = this(3)
            have "I \<Turnstile> D"
              using I_N_M \<open>D \<in># snd ?S\<close> unfolding true_clss_def by auto
            moreover have "I \<Turnstile>s CNot D"
              using \<open>M \<Turnstile>as CNot D\<close> unfolding M by (metis "1"(3) \<open>M \<Turnstile>as CNot D\<close>
                true_annots_true_cls true_cls_mono_set_mset_l true_clss_def
                true_clss_singleton_lit_of_implies_incl true_clss_union)
            ultimately show ?case using cons consistent_CNot_not by blast
          qed
        thus ?thesis
          using true_clss_clss_left_right[OF N_C_M, of "{{#}}"] unfolding A by auto
      qed
    have "N \<Turnstile>pm image_mset uminus ?C + {#-?K#}"
      unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
      proof (intro allI impI)
        fix I
        assume
          tot: "total_over_set I (atms_of_m (set_mset N \<union> {image_mset uminus ?C + {#- ?K#}})) " and
          cons: "consistent_interp I" and
          "I \<Turnstile>sm N"
        have "(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)"
          using cons tot unfolding consistent_interp_def L by (cases K) auto
        have "total_over_set I (atm_of ` lit_of ` (set M \<inter> {L. is_marked L \<and> L \<noteq> Marked K d}))"
          using tot by (auto simp add: L atms_of_uminus_lit_atm_of_lit_of)

        hence H: "\<And>x.
            lit_of x \<notin> I \<Longrightarrow> x \<in> set M \<Longrightarrow>is_marked x
            \<Longrightarrow> x \<noteq> Marked K d \<Longrightarrow> -lit_of x \<in> I"
            (* TODO one-liner? *)
          unfolding total_over_set_def atms_of_s_def
          proof -
            fix x :: "('v, dpll_marked_level, dpll_mark) marked_lit"
            assume a1: "x \<in> set M"
            assume a2: "\<forall>l\<in>atm_of ` lit_of ` (set M \<inter> {L. is_marked L \<and> L \<noteq> Marked K d}).
              Pos l \<in> I \<or> Neg l \<in> I"
            assume a3: "lit_of x \<notin> I"
            assume a4: "is_marked x"
            assume a5: "x \<noteq> Marked K d"
            have f6: "Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))"
              by simp
            have "Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I"
              using a5 a4 a2 a1 by blast
            thus "- lit_of x \<in> I"
              using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                literal.sel(1))
          qed
        have "\<not>I \<Turnstile>s ?C'"
          using \<open>set_mset N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>sm N\<close>
          unfolding true_clss_clss_def total_over_m_def
          by (simp add: atms_of_uminus_lit_atm_of_lit_of atms_of_m_single_image_atm_of_lit_of)
        then show "I \<Turnstile> image_mset uminus ?C + {#- lit_of L#}"
          unfolding true_clss_def true_cls_def Bex_mset_def
          using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
          unfolding L by (auto dest!: H)
      qed
  moreover
    have "set F' \<inter> {K. is_marked K \<and> K \<noteq> L} = {}"
      using backtrack_split_fst_not_marked[of _ M] b_sp by auto
    hence "F \<Turnstile>as CNot (image_mset uminus ?C)"
       unfolding M CNot_def true_annots_def by (auto simp add: L lits_of_def)
  ultimately show ?thesis
    using M' \<open>D \<in># snd ?S\<close> L by auto
qed

lemma backtrack_is_backjump':
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
  assumes
    backtrack: "backtrack S T" and
    no_dup: "(no_dup \<circ> fst) S" and
    decomp: "all_decomposition_implies_m (snd S) (get_all_marked_decomposition (fst S))"
    shows "
        \<exists>C F' K d F L l C'.
          fst S = F' @ Marked K d # F \<and>
          T = (Propagated L l # F, snd S) \<and> C \<in># snd S \<and> fst S \<Turnstile>as CNot C
          \<and> undefined_lit L F \<and> atm_of L \<in> atms_of_mu (snd S) \<union> atm_of ` lits_of (fst S) \<and>
          snd S \<Turnstile>pm C' + {#L#} \<and> F \<Turnstile>as CNot C'"
  apply (cases S, cases T)
  using backtrack_is_backjump[of "fst S" "snd S" "fst T" "snd T"] assms by fastforce

sublocale dpll_state fst snd "\<lambda>L (M, N). (L # M, N)" "\<lambda>(M, N). (tl M, N)"
  "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)"
  by unfold_locales auto

sublocale backjumping_ops fst snd "\<lambda>L (M, N). (L # M, N)" "\<lambda>(M, N). (tl M, N)"
  "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)" "\<lambda>_ _ S T. backtrack S T"
  by unfold_locales

lemma backtrack_is_backjump'':
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
  assumes
    backtrack: "backtrack S T" and
    no_dup: "(no_dup \<circ> fst) S" and
    decomp: "all_decomposition_implies_m (snd S) (get_all_marked_decomposition (fst S))"
    shows "backjump S T"
proof -
  obtain C F' K d F L l C' where
    1: "fst S = F' @ Marked K d # F" and
    2: "T = (Propagated L l # F, snd S)" and
    3: "C \<in># snd S" and
    4: "fst S \<Turnstile>as CNot C" and
    5: "undefined_lit L F" and
    6: "atm_of L \<in> atms_of_mu (snd S) \<union> atm_of ` lits_of (fst S)" and
    7: "snd S \<Turnstile>pm C' + {#L#}" and
    8: "F \<Turnstile>as CNot C'"
  using backtrack_is_backjump'[OF assms] by blast
  show ?thesis
    using backjump.intros[OF 1 _ 3 4 5 6 7 8] 2 backtrack 1
    by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
qed

lemma can_do_bt_step:
   assumes
     M: "fst S = F' @ Marked K d # F" and
     "C \<in># snd S" and
     C: "fst S \<Turnstile>as CNot C"
   shows "\<not> no_step backtrack S"
proof -
  obtain L G' G where
    "backtrack_split (fst S) = (G', L # G)"
    unfolding M by (induction F' rule: marked_lit_list_induct) auto
  moreover hence "is_marked L"
     by (metis backtrack_split_snd_hd_marked list.distinct(1) list.sel(1) snd_conv)
  ultimately show ?thesis
     using backtrack.intros[of S G' L G C] \<open>C \<in># snd S\<close> C unfolding M by auto
qed

end

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping_ops fst snd "\<lambda>L (M, N). (L # M, N)"
  "\<lambda>(M, N). (tl M, N)" "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)" "\<lambda>_. True"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_marked_decomposition M)"
  "(\<lambda>_ _ S T. backtrack S T)"
  by unfold_locales (metis (mono_tags, lifting) dpll_with_backtrack.backtrack_is_backjump''
   dpll_with_backtrack.can_do_bt_step prod.case_eq_if comp_apply)

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping fst snd "\<lambda>L (M, N). (L # M, N)"
  "\<lambda>(M, N). (tl M, N)" "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)" "\<lambda>_. True"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_marked_decomposition M)"
  "(\<lambda>_ _ S T. backtrack S T)"
  apply unfold_locales
  using dpll_bj_no_dup dpll_bj_all_decomposition_implies_inv apply fastforce
  done

sublocale dpll_with_backtrack \<subseteq> conflict_driven_clause_learning_ops
  fst snd "\<lambda>L (M, N). (L # M, N)"
  "\<lambda>(M, N). (tl M, N)" "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)" "\<lambda>_. True"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_marked_decomposition M)"
  "(\<lambda>_ _ S T. backtrack S T)" "\<lambda>_ _. False" "\<lambda>_ _. False"
  by unfold_locales

sublocale dpll_with_backtrack \<subseteq> conflict_driven_clause_learning
  fst snd "\<lambda>L (M, N). (L # M, N)"
  "\<lambda>(M, N). (tl M, N)" "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)" "\<lambda>_. True"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_marked_decomposition M)"
  "(\<lambda>_ _ S T. backtrack S T)" "\<lambda>_ _. False" "\<lambda>_ _. False"
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps dpll_bj_inv forgetE learnE by blast

context dpll_with_backtrack
begin
lemma tranclp_dpll_wf_inital_state:
  assumes fin: "finite A"
  shows "wf {((M'::('v, dpll_marked_level, dpll_mark) marked_lits, N'::'v clauses), ([], N))|M' N' N.
    dpll_bj\<^sup>+\<^sup>+ ([], N) (M', N') \<and> atms_of_mu N \<subseteq> atms_of_m A}"
  using tranclp_dpll_bj_wf[OF assms(1)] by (rule wf_subset) auto

theorem full0_dpll_normal_forms:
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
  assumes
    full: "full0 dpll_bj ([], N) (M', N')"
  shows "unsatisfiable (set_mset N) \<or> (M' \<Turnstile>asm N \<and> satisfiable (set_mset N))"
  using assms full0_dpll_backjump_normal_forms[of "([],N)" "(M', N')" "set_mset N"] by auto

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_is_dpll:
  "cdcl\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> dpll_bj S T"
  by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T.simps learn.simps forget\<^sub>N\<^sub>O\<^sub>T.simps)

text \<open>Another proof of termination:\<close>
lemma "wf {(T, S). dpll_bj S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}"
  unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_is_dpll[symmetric]
  by (rule wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain)
  (auto simp: learn.simps forget\<^sub>N\<^sub>O\<^sub>T.simps)
end

subsection \<open>Adding restarts\<close>
locale dpll_withbacktrack_and_restarts =
  dpll_with_backtrack +
  fixes f :: "nat \<Rightarrow> nat"
  assumes strict_mono: "strict_mono f"
begin
  sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts  fst snd "\<lambda>L (M, N). (L # M, N)" "\<lambda>(M, N). (tl M, N)"
    "\<lambda>C (M, N). (M, {#C#} + N)" "\<lambda>C (M, N). (M, remove_mset N C)" f "\<lambda>(_, N) S. S = ([], N)"
  "\<lambda>A (M, N). atms_of_mu N \<subseteq> atms_of_m A \<and> atm_of ` lits_of M \<subseteq> atms_of_m A \<and> finite A
    \<and> all_decomposition_implies_m N (get_all_marked_decomposition M)"
  "\<lambda>A T. (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)" dpll_bj
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies_m N (get_all_marked_decomposition M)"
  "\<lambda>A _.  (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))"
  apply unfold_locales
         apply (rule strict_mono)
        apply (smt dpll_bj_all_decomposition_implies_inv dpll_bj_atms_in_trail_in_set
          dpll_bj_clauses dpll_bj_no_dup prod.case_eq_if)
       apply (rule dpll_bj_trail_mes_decreasing_prop; auto)
      apply (case_tac T, simp)
     apply (case_tac U, simp)
    using dpll_bj_clauses dpll_bj_all_decomposition_implies_inv dpll_bj_no_dup by fastforce+
end

end