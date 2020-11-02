(*
  File:         PAC_Checker_Specification.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory EPAC_Checker_Specification
  imports EPAC_Specification
    Refine_Imperative_HOL.IICF
    PAC_Checker.Finite_Map_Multiset
    PAC_Checker.PAC_Checker_Specification
begin

section \<open>Checker Algorithm\<close>


text \<open>

In this level of refinement, we define the first level of the
implementation of the checker, both with the specification as
on ideals and the first version of the loop.

\<close>

subsection \<open>Algorithm\<close>

definition PAC_checker_step
  ::  \<open>int_poly \<Rightarrow> (status \<times> fpac_step) \<Rightarrow> (int_poly, nat, nat) pac_step \<Rightarrow>
    (status \<times> fpac_step) nres\<close>
where
  \<open>PAC_checker_step = (\<lambda>spec (stat, (\<V>, A)) st. case st of
     Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_add A \<V> (pac_src1 st) (pac_src2 st) (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. (\<not>is_failed st' \<and> is_found st' \<longrightarrow> r - spec \<in> ideal polynomial_bool));
        if eq
        then RETURN (merge_status stat st', \<V>, fmupd (new_id st) r A)
        else RETURN (FAILED, (\<V>, A))
   }
   | Del _ \<Rightarrow>
       do {
        eq \<leftarrow> check_del A (pac_src1 st);
        if eq
        then RETURN (stat, (\<V>, fmdrop (pac_src1 st) A))
        else RETURN (FAILED, (\<V>, A))
   }
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
         q \<leftarrow> normalize_poly_spec (pac_mult st);
        eq \<leftarrow> check_mult A \<V> (pac_src1 st) q (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. (\<not>is_failed st' \<and> is_found st' \<longrightarrow> r - spec \<in> ideal polynomial_bool));
        if eq
        then RETURN (merge_status stat st',
          \<V>, fmupd (new_id st) r A)
        else RETURN (FAILED, (\<V>, A))
   }
   | Extension _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st - Var (new_var st));
        (eq) \<leftarrow> check_extension A \<V> (new_id st) (new_var st) r;
        if eq
        then do {
         RETURN (stat,
          insert (new_var st) \<V>, fmupd (new_id st) (r) A)}
        else RETURN (FAILED, (\<V>, A))
   }
 )\<close>
lemma PAC_checker_step_PAC_checker_specification2:
  fixes a :: \<open>status\<close>
  assumes AB: \<open>((\<V>, A),(\<V>\<^sub>B, B)) \<in> polys_rel_full\<close> and
    \<open>\<not>is_failed a\<close> and
    [simp,intro]: \<open>a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> and
    A\<^sub>0B: \<open>PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (\<V>, B)\<close> and
    spec\<^sub>0: \<open>vars spec \<subseteq> \<V>\<^sub>0\<close>  and
    vars_A\<^sub>0: \<open>\<Union> (vars ` set_mset A\<^sub>0) \<subseteq> \<V>\<^sub>0\<close>
  shows \<open>PAC_checker_step spec (a, (\<V>, A)) st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification_step2 (\<V>\<^sub>0, A\<^sub>0) spec (\<V>, B))\<close>
proof -
  have
    \<open>\<V>\<^sub>B = \<V>\<close>and
    [simp, intro]:\<open>(A, B) \<in> polys_rel\<close>
    using AB
    by (auto simp: polys_rel_full_def)
  have H0: \<open>2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r \<in> pac_ideal
                (insert (the (fmlookup A x12))
                  ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close> for x12 r Aa
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult.commute 
         diff_in_polynomial_bool_pac_idealI
       ideal.span_base pac_idealI3 set_image_mset set_mset_add_mset_insert union_single_eq_member)+
  then have H0': \<open>\<And>Aa. 2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          spec \<in> pac_ideal (insert (the (fmlookup A x12)) ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close>
    for r x12
    by (metis (no_types, lifting) diff_in_polynomial_bool_pac_idealI)

  have H1: \<open> x12 \<in># dom_m A \<Longrightarrow>
       2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       vars spec \<subseteq> vars r \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close> for x12 r
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x12)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynomial_bool\<close> \<open>2 * the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     by (auto dest!: multi_member_split simp: ran_m_def 
         intro: H0')
   have H2': \<open>the (fmlookup A x11) + the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       B = add_mset (the (fmlookup A x11)) {#the (fmlookup A x). x \<in># Aa#} \<Longrightarrow>
       (the (fmlookup A x11) + the (fmlookup A x12) - r
        \<in> More_Modules.ideal
            (insert (the (fmlookup A x11))
              ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa \<union> polynomial_bool)) \<Longrightarrow>
        - r
        \<in> More_Modules.ideal
            (insert (the (fmlookup A x11))
              ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa \<union> polynomial_bool))) \<Longrightarrow>
       r \<in> pac_ideal (insert (the (fmlookup A x11)) ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close>
     for r x12 x11 A Aa
     by (metis (mono_tags, lifting) Un_insert_left diff_diff_eq2 diff_in_polynomial_bool_pac_idealI diff_zero
       ideal.span_diff ideal.span_neg minus_diff_eq pac_idealI1 pac_ideal_def set_image_mset
       set_mset_add_mset_insert union_single_eq_member)
   have H2: \<open>x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r
       \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close>  for x12 r x11
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x11)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynomial_bool\<close> \<open>the (fmlookup A x11) + the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     by (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
       (auto dest!: multi_member_split simp: ran_m_def ideal.span_base 
         intro: diff_in_polynomial_bool_pac_idealI simp: H2')

   have H3': \<open>the (fmlookup A x12) * q - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r \<in> pac_ideal (insert (the (fmlookup A x12)) ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close>
     for Aa x12 r q
     by (metis (no_types, lifting) ab_semigroup_mult_class.mult.commute diff_in_polynomial_bool_pac_idealI
       ideal.span_base pac_idealI3 set_image_mset set_mset_add_mset_insert union_single_eq_member)

  have H3: \<open>x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x12) * q - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close> for x12 r q
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x12)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynomial_bool\<close> \<open>2 * the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     by (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
       (auto dest!: multi_member_split simp: ran_m_def H3'
         intro: diff_in_polynomial_bool_pac_idealI)

  have [intro]: \<open>spec \<in> pac_ideal (set_mset B) \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> and
    vars_B: \<open>\<Union> (vars ` set_mset B) \<subseteq> \<V>\<close>and
    vars_B: \<open>\<Union> (vars ` set_mset (ran_m A)) \<subseteq> \<V>\<close>
    using rtranclp_PAC_Format_subset_ideal[OF A\<^sub>0B  vars_A\<^sub>0] spec\<^sub>0 \<open>(A, B) \<in> polys_rel\<close>[unfolded polys_rel_def, simplified]
    by (smt in_mono mem_Collect_eq restricted_ideal_to_def)+

  have eq_successI: \<open>st' \<noteq> FAILED \<Longrightarrow>
       st' \<noteq> FOUND \<Longrightarrow> st' = SUCCESS\<close> for st'
    by (cases st') auto
  have vars_diff_inv: \<open>vars (Var x2 - r) = vars (r - Var x2 :: int mpoly)\<close> for x2 r
    using vars_uminus[of \<open>Var x2 - r\<close>]
    by (auto simp del: vars_uminus)
  have vars_add_inv: \<open>vars (Var x2 + r) = vars (r + Var x2 :: int mpoly)\<close> for x2 r
    unfolding add.commute[of \<open>Var x2\<close> r] ..

  have [iff]: \<open>a \<noteq> FAILED\<close> and
    [intro]: \<open>a \<noteq> SUCCESS \<Longrightarrow> a = FOUND\<close> and
    [simp]: \<open>merge_status a FOUND = FOUND\<close>
    using assms(2) by (cases a; auto)+
  note [[goals_limit=1]]
  show ?thesis
    unfolding PAC_checker_step_def PAC_checker_specification_step_spec_def
      normalize_poly_spec_alt_def check_mult_def check_add_def
      check_extension_def polys_rel_full_def
    apply (cases st)
    apply clarsimp_all
    subgoal for x11 x12 x13 x14
      apply (refine_vcg lhs_step_If)
      subgoal for r eqa st'
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(merge_status a st',\<V>,add_mset r B)\<close> in exI)
        by (auto simp: polys_rel_update_remove ran_m_mapsto_upd_notin
          intro: PAC_Format_add_and_remove H2 dest: rtranclp_PAC_Format_subset_ideal)
      subgoal
        by (rule RETURN_SPEC_refine)
         (auto simp: Ex_status_iff dest: rtranclp_PAC_Format_subset_ideal)
      done
    subgoal for x11 x12 x13 x14
      apply (refine_vcg lhs_step_If)
      subgoal for r q eqa st'
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(merge_status a st',\<V>,add_mset r B)\<close> in exI)
        by (auto intro: polys_rel_update_remove intro: PAC_Format_add_and_remove(3-) H3
           dest: rtranclp_PAC_Format_subset_ideal)
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    subgoal for x31 x32 x34
      apply (refine_vcg lhs_step_If)
      subgoal for r x
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(a,insert x32 \<V>, add_mset r B)\<close> in exI)
        apply (auto simp: intro!: polys_rel_update_remove PAC_Format_add_and_remove(5-)
           dest: rtranclp_PAC_Format_subset_ideal)
        done
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    subgoal for x11
      unfolding check_del_def
      apply (refine_vcg lhs_step_If)
      subgoal for eq
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (cases \<open>x11 \<in># dom_m A\<close>)
        subgoal
          apply (rule_tac x = \<open>(a,\<V>, remove1_mset (the (fmlookup A x11)) B)\<close> in exI)
          apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove
               is_failed_def is_success_def is_found_def
            dest!: eq_successI
            split: if_splits
            dest: rtranclp_PAC_Format_subset_ideal
            intro: PAC_Format_add_and_remove H3)
          done
        subgoal
          apply (rule_tac x = \<open>(a,\<V>, B)\<close> in exI)
          apply (auto simp: fmdrop_irrelevant
               is_failed_def is_success_def is_found_def
            dest!: eq_successI
            split: if_splits
            dest: rtranclp_PAC_Format_subset_ideal
            intro: PAC_Format_add_and_remove)
          done
        done
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    done
qed

definition PAC_checker
  :: \<open>int_poly \<Rightarrow> fpac_step \<Rightarrow> status \<Rightarrow> (int_poly, nat, nat) pac_step list \<Rightarrow>
    (status \<times> fpac_step) nres\<close>
where
  \<open>PAC_checker spec A b st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b :: status, A :: fpac_step), st). \<not>is_failed b \<and> st \<noteq> [])
       (\<lambda>((bA), st). do {
          ASSERT(st \<noteq> []);
          S \<leftarrow> PAC_checker_step spec (bA) (hd st);
          RETURN (S, tl st)
        })
      ((b, A), st);
    RETURN S
  }\<close>

lemma PAC_checker_PAC_checker_specification2:
  \<open>(A, B) \<in>  polys_rel_full \<Longrightarrow>
    \<not>is_failed a \<Longrightarrow>
    (a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset (snd B))) \<Longrightarrow>
    \<Union>(vars ` set_mset (ran_m (snd A))) \<subseteq> fst B \<Longrightarrow>
    vars spec \<subseteq> fst B \<Longrightarrow>
  PAC_checker spec A a st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification2 spec B)\<close>
  unfolding PAC_checker_def conc_fun_RES
  apply (subst RES_SPEC_eq)
  apply (refine_vcg WHILET_rule[where
      I = \<open>\<lambda>((bB), st). bB \<in> (status_rel \<times>\<^sub>r polys_rel_full)\<inverse> ``
                      Collect (PAC_checker_specification_spec spec B)\<close>
    and R = \<open>measure (\<lambda>(_, st).  Suc (length st))\<close>])
  subgoal by auto
  subgoal apply (auto simp: PAC_checker_specification_spec_def)
    apply (cases B; cases A)
    apply (auto simp:polys_rel_def polys_rel_full_def Image_iff)
    done
  subgoal by auto
  subgoal
    apply auto
    apply (rule
     PAC_checker_step_PAC_checker_specification2[of _ _ _ _ _ _ _ \<open>fst B\<close>, THEN order_trans])
     apply assumption
     apply assumption
     apply (auto intro: PAC_checker_specification_spec_trans simp: conc_fun_RES)
     apply (auto simp: PAC_checker_specification_spec_def polys_rel_full_def polys_rel_def
       dest: PAC_Format_subset_ideal
       dest: is_failed_is_success_completeD; fail)+
    by (auto simp: Image_iff intro: PAC_checker_specification_spec_trans
        simp: polys_rel_def polys_rel_full_def)
  subgoal
    by auto
  done

subsection \<open>Full Checker\<close>

definition full_checker
  :: \<open>int_poly \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> (int_poly, nat,nat) pac_step list \<Rightarrow> (status \<times> _) nres\<close>
 where
  \<open>full_checker spec0 A pac = do {
     spec \<leftarrow> normalize_poly_spec spec0;
     (st, \<V>, A) \<leftarrow> remap_polys_change_all spec {} A;
     if is_failed st then
     RETURN (st, \<V>, A)
     else do {
       \<V> \<leftarrow> SPEC(\<lambda>\<V>'. \<V> \<union> vars spec0 \<subseteq> \<V>');
       PAC_checker spec (\<V>, A) st pac
    }
}\<close>

lemma full_checker_spec:
  assumes \<open>(A, A') \<in> polys_rel\<close>
  shows
      \<open>full_checker spec A pac \<le> \<Down>{((st, G), (st', G')). (st, st') \<in> status_rel \<and>
           (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> polys_rel_full)}
        (PAC_checker_specification spec (A'))\<close>
proof -
  have H: \<open>set_mset b \<subseteq> pac_ideal (set_mset (ran_m A)) \<Longrightarrow>
       x \<in> pac_ideal (set_mset b) \<Longrightarrow> x \<in> pac_ideal (set_mset A')\<close> for b x
    using assms apply -
    by (drule pac_ideal_mono) (auto simp: polys_rel_def pac_ideal_idemp)
  have 1: \<open>x \<in> {(st, \<V>', A').
          ( \<not> is_failed st \<longrightarrow> pac_ideal (set_mset (ran_m x2)) =
              pac_ideal (set_mset (ran_m A')) \<and>
              \<Union> (vars ` set_mset (ran_m ABC)) \<subseteq> \<V>' \<and>
              \<Union> (vars ` set_mset (ran_m A')) \<subseteq> \<V>') \<and>
            (st = FOUND \<longrightarrow> speca \<in># ran_m A')} \<Longrightarrow>
         x = (st, x') \<Longrightarrow> x' = (\<V>, Aa) \<Longrightarrow>((\<V>', Aa), \<V>', ran_m Aa) \<in> polys_rel_full\<close> for Aa speca x2 st x \<V>' \<V> x' ABC
    by (auto simp: polys_rel_def polys_rel_full_def)
  have H1: \<open>\<And>a aa b xa x x1a x1 x2 speca.
       vars spec \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m A)) \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m x2a)) \<subseteq> x1b \<Longrightarrow>
       restricted_ideal_to\<^sub>I x1b b \<subseteq> restricted_ideal_to\<^sub>I x1b (ran_m x2a) \<Longrightarrow>
       xa \<in> restricted_ideal_to\<^sub>I (\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec) b \<Longrightarrow>
       xa \<in> restricted_ideal_to\<^sub>I (\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec) (ran_m x2a)\<close>
    for x1b b xa x2a
    by (drule restricted_ideal_to_mono[of _ _ _ _ \<open>\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec\<close>])
      auto
  have H2: \<open>\<And>a aa b speca x2 x1a x1b x2a.
       spec - speca \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       vars spec \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m A)) \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m x2a)) \<subseteq> x1b \<Longrightarrow>
       speca \<in> pac_ideal (set_mset (ran_m x2a)) \<Longrightarrow>
       restricted_ideal_to\<^sub>I x1b b \<subseteq> restricted_ideal_to\<^sub>I x1b (ran_m x2a) \<Longrightarrow>
       spec \<in> pac_ideal (set_mset (ran_m x2a))\<close>
    by (metis (no_types, lifting) group_eq_aux ideal.span_add ideal.span_base in_mono
        pac_ideal_alt_def sup.cobounded2)

  show ?thesis
    supply[[goals_limit=1]]
    unfolding full_checker_def normalize_poly_spec_def
      PAC_checker_specification_def remap_polys_change_all_def
    apply (refine_vcg PAC_checker_PAC_checker_specification2[THEN order_trans, of _ _]
      lhs_step_If)
    subgoal by (auto simp: is_failed_def RETURN_RES_refine_iff)
    apply (rule 1; assumption)
    subgoal
      using fmap_ext assms by (auto simp: polys_rel_def ran_m_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal for speca x1 x2 x x1a x2a x1b
      apply (rule ref_two_step[OF conc_fun_R_mono])
       apply auto[]
      using assms
      by (auto simp add: PAC_checker_specification_spec_def conc_fun_RES polys_rel_def H1 H2
          polys_rel_full_def
          dest!: rtranclp_PAC_Format_subset_ideal dest: is_failed_is_success_completeD)
    done
qed


lemma full_checker_spec':
  shows
    \<open>(uncurry2 full_checker, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A)) \<in>
       (Id \<times>\<^sub>r polys_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>{((st, G), (st', G')). (st, st') \<in> status_rel \<and>
           (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> polys_rel_full)}\<rangle>nres_rel\<close>
  using full_checker_spec
  by (auto intro!: frefI nres_relI)

end

