theory Simulation_SCLFOL_ORDRES
  imports
    Background
    ORD_RES
    ORD_RES_1
    ORD_RES_2
    ORD_RES_3
    ORD_RES_4
    ORD_RES_5
    ORD_RES_6
    ORD_RES_7
    ORD_RES_8
    ORD_RES_9
    ORD_RES_10
    ORD_RES_11
    Clause_Could_Propagate
begin

section \<open>ORD-RES-1 (deterministic)\<close>

type_synonym 'f ord_res_1_state = "'f gclause fset"

context simulation_SCLFOL_ground_ordered_resolution begin

sublocale backward_simulation_with_measuring_function where
  step1 = ord_res and
  step2 = ord_res_1 and
  final1 = ord_res_final and
  final2 = ord_res_1_final and
  order = "\<lambda>_ _. False" and
  match = "(=)" and
  measure = "\<lambda>_. ()"
proof unfold_locales
  show "wfP (\<lambda>_ _. False)"
    by simp
next
  show "\<And>N1 N2. N1 = N2 \<Longrightarrow> ord_res_1_final N2 \<Longrightarrow> ord_res_final N1"
    unfolding ord_res_1_final_def by metis
next
  fix N1 N2 N2' :: "'f ord_res_1_state"
  assume match: "N1 = N2" and step2: "ord_res_1 N2 N2'"
  show "(\<exists>N1'. ord_res\<^sup>+\<^sup>+ N1 N1' \<and> N1' = N2') \<or> N1 = N2' \<and> False"
  proof (intro disjI1 exI conjI)

    have mempty_no_in: "{#} |\<notin>| N2"
      if C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N2.
        \<not> ord_res.interp (fset N2) C \<union> ord_res.production (fset N2) C \<TTurnstile> C|} C" and
        L_max: "linorder_lit.is_maximal_in_mset C L"
      for C L
    proof (rule notI)
      assume "{#} |\<in>| N2"
      moreover have "\<not> ord_res.interp (fset N2) {#} \<union> ord_res.production (fset N2) {#} \<TTurnstile> {#}"
        by simp
      moreover have "\<And>C. {#} \<preceq>\<^sub>c C"
        using mempty_lesseq_cls by metis
      ultimately have "C = {#}"
        using C_least
        by (metis (no_types, lifting) ffmember_filter linorder_cls.is_least_in_fset_iff
            linorder_cls.less_le_not_le)
      moreover have "L \<in># C"
        using L_max by (simp add: linorder_lit.is_maximal_in_mset_iff)
      ultimately show "False"
        by simp
    qed

    have "ord_res N2 N2'"
      using step2
    proof (cases N2 N2' rule: ord_res_1.cases)
      case hyps: (factoring C L C')
      show ?thesis
      proof (rule ord_res.factoring)
        show "{#} |\<notin>| N2"
          using hyps mempty_no_in is_least_false_clause_def by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps is_least_false_clause_def
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(1) by blast
      next
        show "ord_res.ground_factoring C C'"
          using hyps by argo
      next
        show "N2' = finsert C' N2"
          using hyps by argo
      qed
    next
      case hyps: (resolution C L D CD)
      show ?thesis
      proof (rule ord_res.resolution)
        show "{#} |\<notin>| N2"
          using hyps mempty_no_in is_least_false_clause_def by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps is_least_false_clause_def
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(1) by blast
      next
        show "D |\<in>| N2"
          using hyps by argo
      next
        show "ord_res.ground_resolution C D CD"
          using hyps by argo
      next
        show "N2' = finsert CD N2"
          using hyps by argo
      qed
    qed
    thus "ord_res\<^sup>+\<^sup>+ N1 N2'"
      unfolding match by simp
  next
    show "N2' = N2'" ..
  qed
qed

end


section \<open>ORD-RES-2 (full factorization)\<close>

type_synonym 'f ord_res_2_state = "'f gclause fset \<times> 'f gclause fset \<times> 'f gclause fset"

context simulation_SCLFOL_ground_ordered_resolution begin

fun ord_res_1_matches_ord_res_2
  :: "'f ord_res_1_state \<Rightarrow> _ \<Rightarrow> bool" where
  "ord_res_1_matches_ord_res_2 S1 (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) \<longleftrightarrow> (\<exists>U\<^sub>f.
      S1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f \<and>
      (\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
        (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)))"

lemma ord_res_1_matches_ord_res_2_simps':
  "ord_res_1_matches_ord_res_2 S1 (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    (\<exists>U\<^sub>f. S1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f \<and>
      (\<forall>C\<^sub>f |\<in>| U\<^sub>f. C\<^sub>f \<noteq> efac C\<^sub>f \<and> (\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and>
        (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C))))"
  unfolding ord_res_1_matches_ord_res_2.simps by metis

lemma ord_res_1_matches_ord_res_2_simps'':
  "ord_res_1_matches_ord_res_2 S1 (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    (\<exists>U\<^sub>f. S1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f \<and>
      (\<forall>C\<^sub>f |\<in>| U\<^sub>f. C\<^sub>f \<noteq> efac C\<^sub>f \<and> (\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and>
        (efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C))))"
  unfolding ord_res_1_matches_ord_res_2_simps'
  by (metis ground_factorings_preserves_efac tranclp_into_rtranclp)

lemma ord_res_1_final_iff_ord_res_2_final:
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 S\<^sub>2"
  shows "ord_res_1_final S\<^sub>1 \<longleftrightarrow> ord_res_2_final S\<^sub>2"
proof -
  obtain N U\<^sub>r U\<^sub>e\<^sub>f where "S\<^sub>2 = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)
  with match obtain U\<^sub>f where
    S\<^sub>1_def: "S\<^sub>1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
      (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    by auto

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> efac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_efac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  have "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> {#} |\<in>| U\<^sub>f"
      by simp
    thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        by assumption
    next
      assume "{#} |\<in>| U\<^sub>f"
      hence "{#} \<noteq> efac {#}"
        using U\<^sub>f_spec[rule_format, of "{#}"] by metis
      hence False
        by simp
      thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" ..
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
      by simp
  qed

  moreover have "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) \<longleftrightarrow>
    \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
  proof (rule iffI; erule contrapos_nn)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f))"
      unfolding ex_false_clause_def Interp_eq by auto
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f))"
    then obtain C where
      "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f" and
      C_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
      unfolding ex_false_clause_def Interp_eq by metis
    hence "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    proof (elim disjE)
      assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
        unfolding ex_false_clause_def using C_false by metis
    next
      assume "C |\<in>| U\<^sub>f"
      then obtain C' where "C' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
       "ord_res.ground_factoring\<^sup>+\<^sup>+ C' C" and
       "C \<noteq> efac C" and
       "efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C'"
        using U\<^sub>f_spec[rule_format, of C] by metis
      thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      proof (elim disjE exE conjE)
        assume "efac C |\<in>| U\<^sub>e\<^sub>f"

        show "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
        proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (efac C) \<TTurnstile> efac C")
          case efac_C_true: True
          have "efac C \<subseteq># C"
            using efac_subset[of C] .
          hence "efac C \<preceq>\<^sub>c C"
            using subset_implies_reflclp_multp by metis
          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> efac C"
            using efac_C_true ord_res.entailed_clause_stays_entailed by fastforce
          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
            using efac_C_true by (simp add: true_cls_def)
          with C_false have False
            by contradiction
          thus ?thesis ..
        next
          case False

          moreover have "efac C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>efac C |\<in>| U\<^sub>e\<^sub>f\<close> by simp

          ultimately show "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
            unfolding ex_false_clause_def by metis
        qed
      next
        assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C'"
        hence "C' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C' \<TTurnstile> C'"
          using linorder_cls.is_least_in_ffilter_iff is_least_false_clause_def by simp_all
        thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
          unfolding ex_false_clause_def by metis
      qed
    qed
  qed

  ultimately show ?thesis
    by (simp add: S\<^sub>1_def \<open>S\<^sub>2 = (N, U\<^sub>r, U\<^sub>e\<^sub>f)\<close> ord_res_1_final_def ord_res_2_final.simps
        ord_res_final_def)
qed

lemma safe_states_if_ord_res_1_matches_ord_res_2:
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 S\<^sub>2"
  shows "safe_state ord_res_1 ord_res_1_final S\<^sub>1 \<and> safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
proof -
  have "safe_state ord_res_1 ord_res_1_final S\<^sub>1"
    using safe_state_if_all_states_safe ord_res_1_safe by metis

  moreover have "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    using safe_state_if_all_states_safe ord_res_2_step_safe by metis

  ultimately show ?thesis
    by argo
qed

definition ord_res_1_measure where
  "ord_res_1_measure s1 =
    (if \<exists>C. is_least_false_clause s1 C then
      The (is_least_false_clause s1)
    else
      {#})"

lemma forward_simulation:
  assumes match: "ord_res_1_matches_ord_res_2 s1 s2" and
    step1: "ord_res_1 s1 s1'"
  shows "(\<exists>s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> ord_res_1_matches_ord_res_2 s1' s2') \<or>
    ord_res_1_matches_ord_res_2 s1' s2 \<and> ord_res_1_measure s1' \<subset># ord_res_1_measure s1"
proof -
  let
    ?match = "ord_res_1_matches_ord_res_2" and
    ?measure = "ord_res_1_measure" and
    ?order = "(\<subset>#)"

  obtain N U\<^sub>r U\<^sub>e\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)

  from match obtain U\<^sub>f where
    s1_def: "s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
      (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    unfolding s2_def ord_res_1_matches_ord_res_2.simps by metis

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> efac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_efac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  show "(\<exists>s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> ?match s1' s2') \<or>
    ?match s1' s2 \<and> ?order (?measure s1') (?measure s1)"
    using step1
  proof (cases s1 s1' rule: ord_res_1.cases)
    case (factoring C L C')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f) C"
      using factoring
      unfolding is_least_false_clause_def s1_def by argo

    hence C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff s1_def by argo
    hence C_in_disj: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp

    show ?thesis
    proof (cases "C' = efac C'")
      case True
      let ?s2' = "(N, (U\<^sub>r, finsert C' U\<^sub>e\<^sub>f))"

      have "ord_res_2_step\<^sup>+\<^sup>+ s2 ?s2'"
      proof (rule tranclp.r_into_trancl)
        show "ord_res_2_step s2 (N, U\<^sub>r, finsert C' U\<^sub>e\<^sub>f)"
          using C_in_disj
        proof (elim disjE)
          assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          show ?thesis
            unfolding s2_def
          proof (intro ord_res_2_step.intros ord_res_2.factoring)
            show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
              using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                  OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> C_least_false]
              unfolding is_least_false_clause_def .
          next
            show "ord_res.is_maximal_lit L C"
              using \<open>ord_res.is_maximal_lit L C\<close> .
          next
            show "is_pos L"
              using \<open>is_pos L\<close> .
          next
            show "finsert C' U\<^sub>e\<^sub>f = finsert (efac C) U\<^sub>e\<^sub>f"
              using True factoring ground_factoring_preserves_efac by metis
          qed
        next
          assume "C |\<in>| U\<^sub>f"
          then obtain x where
            "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
            "ord_res.ground_factoring\<^sup>+\<^sup>+ x C" and
            "C \<noteq> efac C" and
            "efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
            using U\<^sub>f_spec by metis

          show ?thesis
            unfolding s2_def
          proof (intro ord_res_2_step.intros ord_res_2.factoring)
            have \<open>efac C |\<notin>| U\<^sub>e\<^sub>f\<close>
            proof (rule notI)
              have "efac C \<preceq>\<^sub>c C"
                using efac_subset[of C] subset_implies_reflclp_multp by metis
              hence "efac C \<prec>\<^sub>c C"
                using \<open>C \<noteq> efac C\<close> by order

              moreover assume "efac C |\<in>| U\<^sub>e\<^sub>f"

              ultimately show False
                using C_least_false[unfolded is_least_false_clause_def
                    linorder_cls.is_least_in_ffilter_iff]
                by (metis \<open>C \<noteq> efac C\<close> funionCI linorder_cls.not_less_iff_gr_or_eq
                    ord_res.entailed_clause_stays_entailed set_mset_efac true_cls_def)
            qed
            thus "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
              using \<open>efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close> by argo
          next
            show "ord_res.is_maximal_lit L x"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.is_maximal_lit L C\<close>
              using ord_res.ground_factorings_preserves_maximal_literal
              by (metis tranclp_into_rtranclp)
          next
            show "is_pos L"
              using \<open>is_pos L\<close> .
          next
            show "finsert C' U\<^sub>e\<^sub>f = finsert (efac x) U\<^sub>e\<^sub>f"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.ground_factoring C C'\<close>
              using True ground_factorings_preserves_efac ground_factoring_preserves_efac
              by (metis tranclp_into_rtranclp)
          qed
        qed
      qed

      moreover have "?match s1' ?s2'"
      proof -
        have "s1' = N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
          unfolding \<open>s1' = finsert C' s1\<close> s1_def by simp

        moreover have "\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f.
          ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
          (efac C\<^sub>f |\<in>| finsert C' U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f) C)"
          if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
        proof -
          obtain x where
            "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
            "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
            "C\<^sub>f \<noteq> efac C\<^sub>f" and
            "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
            using \<open>C\<^sub>f |\<in>| U\<^sub>f\<close> U\<^sub>f_spec by metis

          show ?thesis
          proof (intro bexI conjI)
            show "x |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f"
              using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
          next
            show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
          next
            show "C\<^sub>f \<noteq> efac C\<^sub>f"
              using \<open>C\<^sub>f \<noteq> efac C\<^sub>f\<close> .
          next
            show "efac C\<^sub>f |\<in>| finsert C' U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f) x"
              using \<open>efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
            proof (elim disjE)
              assume "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f"
              thus ?thesis
                by simp
            next
              assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
              show ?thesis
              proof (cases "C' = efac x")
                case True
                moreover have "efac x = efac C\<^sub>f"
                  using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> ground_factorings_preserves_efac
                  by (metis tranclp_into_rtranclp)
                ultimately show ?thesis
                  by simp
              next
                case False
                show ?thesis
                  using C_in_disj
                proof (elim disjE)
                  assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                  then show ?thesis
                    by (smt (verit) C_least_false True U\<^sub>f_unproductive
                        \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close> \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close>
                        finsert_iff ground_factoring_preserves_efac ground_factorings_preserves_efac
                        linorder_cls.Uniq_is_least_in_fset local.factoring(4)
                        is_least_false_clause_def
                        is_least_false_clause_if_is_least_false_clause_in_union_unproductive
                        the1_equality' tranclp_into_rtranclp)
                next
                  assume "C |\<in>| U\<^sub>f"
                  then show ?thesis
                    using C_least_false
                    using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                        OF U\<^sub>f_unproductive]
                    by (smt (z3) True U\<^sub>f_spec \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
                        \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> finsert_absorb finsert_iff
                        ground_factoring_preserves_efac ground_factorings_preserves_efac
                        linorder_cls.Uniq_is_least_in_fset local.factoring(4)
                        is_least_false_clause_def the1_equality' tranclp_into_rtranclp)
                qed
              qed
            qed
          qed
        qed

        ultimately show ?thesis
          by auto
      qed

      ultimately show ?thesis
        by metis
    next
      case False
      let ?U\<^sub>f' = "finsert C' U\<^sub>f"

      have "?match s1' s2"
      proof -
        have "finsert C' s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| ?U\<^sub>f'"
          unfolding s1_def by simp

        moreover have "\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
          (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
          if "C\<^sub>f |\<in>| ?U\<^sub>f'" for C\<^sub>f
        proof -
          from \<open>C\<^sub>f |\<in>| ?U\<^sub>f'\<close> have "C\<^sub>f = C' \<or> C\<^sub>f |\<in>| U\<^sub>f"
            by simp
          thus ?thesis
          proof (elim disjE)
            assume "C\<^sub>f = C'"
            thus ?thesis
              using C_in_disj
            proof (elim disjE)
              assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              show ?thesis
              proof (intro bexI conjI)
                show "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                  using \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
              next
                show "ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f"
                  using \<open>ord_res.ground_factoring C C'\<close> \<open>C\<^sub>f = C'\<close> by simp
              next
                show "C\<^sub>f \<noteq> efac C\<^sub>f"
                  using False \<open>C\<^sub>f = C'\<close> by argo
              next
                have "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
                  using factoring
                  using Interp_eq \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> linorder_cls.is_least_in_ffilter_iff
                  by (simp add: s1_def is_least_false_clause_def)
                thus "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C" ..
              qed
            next
              assume "C |\<in>| U\<^sub>f"
              then obtain x where
                "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
                "ord_res.ground_factoring\<^sup>+\<^sup>+ x C" and
                "C \<noteq> efac C" and
                "efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
                using U\<^sub>f_spec by metis

              show ?thesis
              proof (intro bexI conjI)
                show "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                  using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
              next
                show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
                  using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.ground_factoring C C'\<close> \<open>C\<^sub>f = C'\<close>
                  by simp
              next
                show "C\<^sub>f \<noteq> efac C\<^sub>f"
                  using False \<open>C\<^sub>f = C'\<close> by argo
              next
                show "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
                  using \<open>efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
                proof (elim disjE)
                  assume "efac C |\<in>| U\<^sub>e\<^sub>f"

                  moreover have "efac C = efac C\<^sub>f"
                    unfolding \<open>C\<^sub>f = C'\<close>
                    using \<open>ord_res.ground_factoring C C'\<close> ground_factoring_preserves_efac by metis

                  ultimately show ?thesis
                    by argo
                next
                  assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
                  thus ?thesis
                    by argo
                qed
              qed
            qed
          next
            assume "C\<^sub>f |\<in>| U\<^sub>f"
            thus ?thesis
              using U\<^sub>f_spec by metis
          qed
        qed

        ultimately have "ord_res_1_matches_ord_res_2 (finsert C' s1) (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
          unfolding ord_res_1_matches_ord_res_2.simps by metis
        thus ?thesis
          unfolding s2_def \<open>s1' = finsert C' s1\<close> by simp
      qed

      moreover have "?order (?measure s1') (?measure s1)"
      proof -
        have "?measure s1 = C"
          unfolding ord_res_1_measure_def
          using C_least_false[folded s1_def]
          by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
              is_least_false_clause_def the1_equality' the_equality)

        moreover have "?measure s1' = C'"
        proof -
          have "C' \<prec>\<^sub>c C"
            using factoring ord_res.ground_factoring_smaller_conclusion by metis

          have unproductive: "\<forall>x\<in>{C'}. ord_res.production (fset s1 \<union> {C'}) x = {}"
            using \<open>C' \<noteq> efac C'\<close>
            by (simp add: nex_strictly_maximal_pos_lit_if_neq_efac
                unproductive_if_nex_strictly_maximal_pos_lit)

          have Interp_eq: "\<And>D. ord_res_Interp (fset s1) D = ord_res_Interp (fset (finsert C' s1)) D"
            using Interp_union_unproductive[of "fset s1" "{C'}", folded union_fset,
                OF finite_fset _ unproductive]
            by simp

          have "is_least_false_clause (finsert C' s1) C'"
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            have "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C"
              using C_least_false s1_def is_least_false_clause_def
                linorder_cls.is_least_in_ffilter_iff by simp
            thus "\<not> ord_res_Interp (fset (finsert C' s1)) C' \<TTurnstile> C'"
              by (metis Interp_eq \<open>C' \<prec>\<^sub>c C\<close> local.factoring(4)
                  ord_res.entailed_clause_stays_entailed
                  ord_res.set_mset_eq_set_mset_if_ground_factoring subset_refl true_cls_mono)
          next
            fix y
            assume "y |\<in>| finsert C' s1" and "y \<noteq> C'" and
              y_false: "\<not> ord_res_Interp (fset (finsert C' s1)) y \<TTurnstile> y"
            hence "y |\<in>| s1"
              by simp

            moreover have "\<not> ord_res_Interp (fset s1) y \<TTurnstile> y"
              using y_false
              unfolding Interp_eq .

            ultimately have "C \<preceq>\<^sub>c y"
              using C_least_false[folded s1_def, unfolded is_least_false_clause_def]
              unfolding linorder_cls.is_least_in_ffilter_iff
              by force
            thus "C' \<prec>\<^sub>c y"
              using \<open>C' \<prec>\<^sub>c C\<close> by order
          qed simp
          thus ?thesis
            unfolding ord_res_1_measure_def \<open>s1' = finsert C' s1\<close>
            by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
                is_least_false_clause_def the1_equality' the_equality)
        qed

        moreover have "C' \<subset># C"
          using factoring ord_res.strict_subset_mset_if_ground_factoring by metis

        ultimately show ?thesis
          unfolding s1_def  by simp
      qed

      ultimately show ?thesis
        by argo
    qed
  next
    case (resolution C L D CD)

    have "is_least_false_clause s1 C"
      using resolution unfolding is_least_false_clause_def by argo
    hence
      "C |\<in>| s1" and
      "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C" and
      "\<forall>x |\<in>| s1. \<not> ord_res_Interp (fset s1) x \<TTurnstile> x \<longrightarrow> x \<noteq> C \<longrightarrow> C \<prec>\<^sub>c x"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by simp_all

    have "C |\<notin>| U\<^sub>f"
    proof (rule notI)
      assume "C |\<in>| U\<^sub>f"
      then show False
        by (metis U\<^sub>f_spec Uniq_D is_pos_def linorder_lit.Uniq_is_maximal_in_mset local.resolution(2)
            local.resolution(3) efac_spec)
    qed
    hence "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      using \<open>C |\<in>| s1\<close> by (simp add: s1_def)

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f) C"
      using resolution s1_def by metis
    hence C_least_false': "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
          OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>] by argo

    define s2' where
      "s2' = (N, (finsert CD U\<^sub>r, U\<^sub>e\<^sub>f))"

    have "ord_res_2_step\<^sup>+\<^sup>+ s2 s2'"
    proof -
      have "D |\<notin>| U\<^sub>f"
      proof (rule notI)
        assume "D |\<in>| U\<^sub>f"
        thus False
          using \<open>ord_res.production (fset s1) D = {atm_of L}\<close>
          using U\<^sub>f_unproductive s1_def by simp
      qed
      hence D_in: "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        using \<open>D |\<in>| s1\<close>[unfolded s1_def] by simp

      have "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) (finsert CD U\<^sub>r, U\<^sub>e\<^sub>f)"
      proof (rule ord_res_2.resolution)
        show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
          using C_least_false' .
      next
        show "ord_res.is_maximal_lit L C"
          using resolution by argo
      next
        show "is_neg L"
          using resolution by argo
      next
        show "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          using D_in .
      next
        show "D \<prec>\<^sub>c C"
          using resolution by argo
      next
        show "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}"
          using resolution
          unfolding s1_def
          using production_union_unproductive[OF finite_fset finite_fset _ D_in] U\<^sub>f_unproductive
          by (metis (no_types, lifting) union_fset)
      next
        show "ord_res.ground_resolution C D CD"
          using resolution by argo
      qed simp_all
      thus ?thesis
        by (auto simp: s2_def s2'_def ord_res_2_step.simps)
    qed

    moreover have "?match s1' s2'"
    proof -
      have "finsert CD (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f) = N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
        by simp

      moreover have "\<exists>C |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
        ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
        (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
        if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
      proof -
        obtain x where
          "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
          "C\<^sub>f \<noteq> efac C\<^sub>f" and
          "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
          using \<open>C\<^sub>f |\<in>| U\<^sub>f\<close> U\<^sub>f_spec by metis
        show ?thesis
        proof (intro bexI conjI)
          show "x |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        next
          show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
            using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
        next
          show "C\<^sub>f \<noteq> efac C\<^sub>f"
            using \<open>C\<^sub>f \<noteq> efac C\<^sub>f\<close> .
        next
          show \<open>efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
            using \<open>efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close> \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
            by (metis (no_types, lifting) C_least_false' Uniq_D \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close>
                is_least_false_clause_def is_pos_def linorder_cls.Uniq_is_least_in_fset
                linorder_lit.Uniq_is_maximal_in_mset local.resolution(2) local.resolution(3)
                ord_res.ground_factoring.cases tranclpD)
        qed
      qed

      ultimately show ?thesis
        unfolding s1_def resolution s2'_def by auto
    qed

    ultimately show ?thesis
      by metis
  qed
qed

theorem bisimulation_ord_res_1_ord_res_2:
  defines "match \<equiv> \<lambda>i s1 s2. i = ord_res_1_measure s1 \<and> ord_res_1_matches_ord_res_2 s1 s2"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_1_state \<Rightarrow> 'f ord_res_2_state \<Rightarrow> bool) \<R>.
    bisimulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final \<R> MATCH"  
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_1_state \<Rightarrow> 'f ord_res_2_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation ord_res_1 ord_res_1_final ord_res_2_step ord_res_2_final MATCH \<R>\<^sub>f \<R>\<^sub>b" *)
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_1"
    using right_unique_ord_res_1 .
next
  show "right_unique ord_res_2_step"
    using right_unique_ord_res_2_step .
next
  show "\<forall>s1. ord_res_1_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_1 s1 s1')"
    using ord_res_1_semantics.final_finished
    by (simp add: finished_def)
next
  show "\<forall>s2. ord_res_2_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_2_step s2 s2')"
    using ord_res_2_semantics.final_finished
    by (simp add: finished_def)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_1_final s1 = ord_res_2_final s2"
    using ord_res_1_final_iff_ord_res_2_final
    by (simp add: match_def)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_1 ord_res_1_final s1 \<and>
    safe_state ord_res_2_step ord_res_2_final s2"
  proof (intro allI impI)
    fix i s1 S2
    assume "match i s1 S2"

    then obtain N s2 where
      S2_def: "S2 = (N, s2)" and
      "i = ord_res_1_measure s1" and
      match: "ord_res_1_matches_ord_res_2 s1 S2"
      unfolding match_def
      by (metis prod.exhaust)

    show "safe_state ord_res_1 ord_res_1_final s1 \<and> safe_state ord_res_2_step ord_res_2_final S2"
      using safe_states_if_ord_res_1_matches_ord_res_2[OF match] .
  qed
next
  show "wfP (\<subset>#)"
    using wfp_subset_mset .
next
  show "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> ord_res_1 s1 s1' \<longrightarrow>
    (\<exists>i' s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> i' \<subset># i)"
  proof (intro allI impI)
    fix i s1 S2 s1'
    assume "match i s1 S2"
    then obtain N s2 where
      S2_def: "S2 = (N, s2)" and "i = ord_res_1_measure s1" and "ord_res_1_matches_ord_res_2 s1 S2"
      unfolding match_def
      by (metis prod.exhaust)

    moreover assume "ord_res_1 s1 s1'"

    ultimately have "(\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> ord_res_1_matches_ord_res_2 s1' S2') \<or>
    ord_res_1_matches_ord_res_2 s1' S2 \<and> ord_res_1_measure s1' \<subset># ord_res_1_measure s1"
      using forward_simulation by metis

    thus "(\<exists>i' S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match i' s1' S2') \<or> (\<exists>i'. match i' s1' S2 \<and> i' \<subset># i)"
      unfolding S2_def prod.case
      using lift_tranclp_to_pairs_with_constant_fst[of ord_res_2 N s2]
      by (metis (mono_tags, lifting) \<open>i = ord_res_1_measure s1\<close> match_def)
  qed
qed

end


section \<open>ORD-RES-3 (full resolve)\<close>

type_synonym 'f ord_res_3_state = "'f gclause fset \<times> 'f gclause fset \<times> 'f gclause fset"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_2_matches_ord_res_3 :: "_ \<Rightarrow> 'f ord_res_3_state \<Rightarrow> bool" where
  "(\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
      (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r) \<Longrightarrow>
  ord_res_2_matches_ord_res_3 (N, (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)) (N, (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f))"

lemma ord_res_2_final_iff_ord_res_3_final:
  assumes match: "ord_res_2_matches_ord_res_3 S\<^sub>2 S\<^sub>3"
  shows "ord_res_2_final S\<^sub>2 \<longleftrightarrow> ord_res_3_final S\<^sub>3"
  using match
proof (cases S\<^sub>2 S\<^sub>3 rule: ord_res_2_matches_ord_res_3.cases)
  case match_hyps: (1 U\<^sub>p\<^sub>r N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)

  note invars = match_hyps(3-)

  have U\<^sub>p\<^sub>r_spec: "\<forall>C|\<in>|U\<^sub>p\<^sub>r. \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
    using invars by argo

  have least_false_spec: "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) =
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    using invars is_least_false_clause_conv_if_partial_resolution_invariant by metis

  have U\<^sub>p\<^sub>r_unproductive: "\<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
  proof (intro ballI)
    fix C
    assume "C |\<in>| U\<^sub>p\<^sub>r"
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
      using U\<^sub>p\<^sub>r_spec
      by (metis eres_eq_after_tranclp_ground_resolution nex_strictly_maximal_pos_lit_if_neq_eres)
    thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f: "\<And>C.
    ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: funion_left_commute sup_commute)

  have "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
  proof (rule iffI)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    then obtain C where "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      using obtains_least_false_clause_if_ex_false_clause by metis
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      using least_false_spec ex_false_clause_iff by metis
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      unfolding ex_false_clause_def
      unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f
      by auto
  qed

  moreover have "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f \<or> {#} |\<in>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
      by auto
    thus "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f"
      thus ?thesis
        by auto
    next
      have "{#} |\<notin>| U\<^sub>p\<^sub>r"
        using U\<^sub>p\<^sub>r_spec[rule_format, of "{#}"]
        by (metis eres_eq_after_tranclp_ground_resolution eres_mempty_right)
      moreover assume "{#} |\<in>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
      ultimately show ?thesis
        by simp
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    then show "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      by auto
  qed

  ultimately have "ord_res_final (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = ord_res_final (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    unfolding ord_res_final_def by argo

  thus "ord_res_2_final S\<^sub>2 \<longleftrightarrow> ord_res_3_final S\<^sub>3"
    unfolding match_hyps(1,2)
    by (simp add: ord_res_2_final.simps ord_res_3_final.simps sup_assoc)
qed

definition ord_res_2_measure where
  "ord_res_2_measure S1 =
    (let (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) = S1 in
    (if \<exists>C. is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C then
      The (is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))
    else
      {#}))"

definition resolvent_at where
  "resolvent_at C D i = (THE CD. (ground_resolution C ^^ i) D CD)"

lemma resolvent_at_0[simp]: "resolvent_at C D 0 = D"
  by (simp add: resolvent_at_def)

lemma resolvent_at_less_cls_resolvent_at:
  assumes reso_at: "(ground_resolution C ^^ n) D CD"
  assumes "i < j" and "j \<le> n"
  shows "resolvent_at C D j \<prec>\<^sub>c resolvent_at C D i"
proof -
  obtain j' where
    "j = i + Suc j'"
    using \<open>i < j\<close> by (metis less_iff_Suc_add nat_arith.suc1)

  obtain n' where
    "n = j + n'"
    using \<open>j \<le> n\<close> by (metis le_add_diff_inverse)

  obtain CD\<^sub>i CD\<^sub>j CD\<^sub>n where
    "(ground_resolution C ^^ i) D CD\<^sub>i" and
    "(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j"
    "(ground_resolution C ^^ n') CD\<^sub>j CD\<^sub>n"
    using reso_at \<open>n = j + n'\<close> \<open>j = i + Suc j'\<close> by (metis relpowp_plusD)

  have *: "resolvent_at C D i = CD\<^sub>i"
    unfolding resolvent_at_def
    using \<open>(ground_resolution C ^^ i) D CD\<^sub>i\<close>
    by (simp add: Uniq_ground_resolution Uniq_relpowp the1_equality')

  have "(ground_resolution C ^^ j) D CD\<^sub>j"
    unfolding \<open>j = i + Suc j'\<close>
    using \<open>(ground_resolution C ^^ i) D CD\<^sub>i\<close> \<open>(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j\<close>
    by (metis relpowp_trans)
  hence **: "resolvent_at C D j = CD\<^sub>j"
    unfolding resolvent_at_def
    by (simp add: Uniq_ground_resolution Uniq_relpowp the1_equality')

  have "(ground_resolution C)\<^sup>+\<^sup>+ CD\<^sub>i CD\<^sub>j"
    using \<open>(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j\<close>
    by (metis Zero_not_Suc tranclp_if_relpowp)
  hence "CD\<^sub>j \<prec>\<^sub>c CD\<^sub>i"
    using resolvent_lt_right_premise_if_tranclp_ground_resolution by metis
  thus ?thesis
    unfolding * ** .
qed

lemma
  assumes reso_at: "(ground_resolution C ^^ n) D CD" and "i < n"
  shows
    left_premisse_lt_resolvent_at: "C \<prec>\<^sub>c resolvent_at C D i" and
    max_lit_resolvent_at:
      "ord_res.is_maximal_lit L D \<Longrightarrow> ord_res.is_maximal_lit L (resolvent_at C D i)" and
    nex_pos_strictly_max_lit_in_resolvent_at:
      "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at C D i)" and
    ground_resolution_resolvent_at_resolvent_at_Suc:
      "ground_resolution C (resolvent_at C D i) (resolvent_at C D (Suc i))" and
    relpowp_to_resolvent_at: "(ground_resolution C ^^ i) D (resolvent_at C D i)"
proof -
  obtain j where n_def: "n = i + Suc j"
    using \<open>i < n\<close> less_natE by auto

  obtain CD' where "(ground_resolution C ^^ i) D CD'" and "(ground_resolution C ^^ Suc j) CD' CD"
    using reso_at n_def by (metis relpowp_plusD)

  have "resolvent_at C D i = CD'"
    unfolding resolvent_at_def
    using \<open>(ground_resolution C ^^ i) D CD'\<close>
    by (simp add: Uniq_ground_resolution Uniq_relpowp the1_equality')

  have "C \<prec>\<^sub>c CD'"
  proof (rule left_premise_lt_right_premise_if_tranclp_ground_resolution)
    show "(ground_resolution C)\<^sup>+\<^sup>+ CD' CD"
      using \<open>(ground_resolution C ^^ Suc j) CD' CD\<close>
      by (metis Zero_not_Suc tranclp_if_relpowp)
  qed
  thus "C \<prec>\<^sub>c resolvent_at C D i"
    unfolding \<open>resolvent_at C D i = CD'\<close> by argo

  show "ord_res.is_maximal_lit L (resolvent_at C D i)" if "ord_res.is_maximal_lit L D"
    unfolding \<open>resolvent_at C D i = CD'\<close>
    using that
    using \<open>(ground_resolution C ^^ i) D CD'\<close>
    by (smt (verit, ccfv_SIG) Uniq_ground_resolution Uniq_relpowp Zero_not_Suc
        \<open>\<And>thesis. (\<And>CD'. \<lbrakk>(ground_resolution C ^^ i) D CD'; (ground_resolution C ^^ Suc j) CD' CD\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        linorder_lit.Uniq_is_greatest_in_mset linorder_lit.Uniq_is_maximal_in_mset literal.sel(1)
        n_def relpowp_ground_resolutionD reso_at the1_equality' zero_eq_add_iff_both_eq_0)

  show "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at C D i)"
    unfolding \<open>resolvent_at C D i = CD'\<close>
    by (metis Zero_not_Suc \<open>(ground_resolution C ^^ Suc j) CD' CD\<close>
        nex_strictly_maximal_pos_lit_if_resolvable tranclpD tranclp_if_relpowp)

  show "ground_resolution C (resolvent_at C D i) (resolvent_at C D (Suc i))"
  proof -
    obtain CD'' where "ground_resolution C CD' CD''" and "(ground_resolution C ^^ j) CD'' CD"
      using \<open>(ground_resolution C ^^ Suc j) CD' CD\<close> by (metis relpowp_Suc_D2)
    hence "(ground_resolution C ^^ Suc i) D CD''"
      using \<open>(ground_resolution C ^^ i) D CD'\<close> by auto
    hence "resolvent_at C D (Suc i) = CD''"
      unfolding resolvent_at_def
      by (meson Uniq_ground_resolution Uniq_relpowp the1_equality')

    show ?thesis
      unfolding \<open>resolvent_at C D i = CD'\<close> \<open>resolvent_at C D (Suc i) = CD''\<close>
      using \<open>ground_resolution C CD' CD''\<close> .
  qed

  show "(ground_resolution C ^^ i) D (resolvent_at C D i)"
    using \<open>(ground_resolution C ^^ i) D CD'\<close> \<open>resolvent_at C D i = CD'\<close> by argo
qed

definition resolvents_upto where
  "resolvents_upto C D n = resolvent_at C D |`| fset_upto (Suc 0) n"

lemma resolvents_upto_0[simp]:
  "resolvents_upto C D 0 = {||}"
  by (simp add: resolvents_upto_def)

lemma resolvents_upto_Suc[simp]:
  "resolvents_upto C D (Suc n) = finsert (resolvent_at C D (Suc n)) (resolvents_upto C D n)"
  by (simp add: resolvents_upto_def)

lemma resolvent_at_fmember_resolvents_upto:
  assumes "k \<noteq> 0"
  shows "resolvent_at C D k |\<in>| resolvents_upto C D k"
  unfolding resolvents_upto_def
proof (rule fimageI)
  show "k |\<in>| fset_upto (Suc 0) k"
    using assms by simp
qed

lemma backward_simulation_2_to_3:
  fixes match measure less
  defines "match \<equiv> ord_res_2_matches_ord_res_3"
  assumes
    match: "match S2 S3" and
    step2: "ord_res_3_step S3 S3'"
  shows "(\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match S2' S3')"
  using match[unfolded match_def]
proof (cases S2 S3 rule: ord_res_2_matches_ord_res_3.cases)
  case match_hyps: (1 U\<^sub>p\<^sub>r N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note invars = match_hyps(3-)

  have U\<^sub>p\<^sub>r_spec: "\<forall>C|\<in>|U\<^sub>p\<^sub>r. \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
    using invars by argo

  hence C_not_least_with_partial: "\<not> is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    if C_in: "C |\<in>| U\<^sub>p\<^sub>r" for C
  proof -
    obtain D1 D2 where
      "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
      "C \<noteq> eres D1 D2" and
      "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
      using U\<^sub>p\<^sub>r_spec C_in by metis

    have "eres D1 C = eres D1 D2"
      using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_eq_after_tranclp_ground_resolution by metis
    hence "eres D1 C \<prec>\<^sub>c C"
      using eres_le[of D1 C] \<open>C \<noteq> eres D1 D2\<close> by order

    show ?thesis
    proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (eres D1 D2) \<TTurnstile> eres D1 D2")
      case True
      then show ?thesis
        by (metis (no_types, lifting) \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> \<open>eres D1 C = eres D1 D2\<close>
            clause_true_if_eres_true is_least_false_clause_def
            linorder_cls.is_least_in_fset_ffilterD(2))
    next
      case False
      then show ?thesis
        by (metis (mono_tags, lifting) Un_iff \<open>eres D1 C = eres D1 D2\<close> \<open>eres D1 C \<prec>\<^sub>c C\<close>
            \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
            linorder_cls.not_less_iff_gr_or_eq sup_fset.rep_eq)
    qed
  qed

  have least_false_conv: "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) =
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    using invars is_least_false_clause_conv_if_partial_resolution_invariant by metis

  have U\<^sub>p\<^sub>r_unproductive: "\<And>N. \<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production N C = {}"
  proof (intro ballI)
    fix C
    assume "C |\<in>| U\<^sub>p\<^sub>r"
    hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. (\<exists>C'. ground_resolution D C C')"
      using U\<^sub>p\<^sub>r_spec by (metis eres_eq_after_tranclp_ground_resolution resolvable_if_neq_eres)
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
      using nex_strictly_maximal_pos_lit_if_resolvable by metis
    thus "\<And>N. ord_res.production N C = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f:
    "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C = ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: funion_left_commute sup_commute)

  have U\<^sub>p\<^sub>r_have_generalization: "\<forall>Ca |\<in>| U\<^sub>p\<^sub>r. \<exists>D |\<in>| U\<^sub>e\<^sub>r. D \<prec>\<^sub>c Ca \<and> {D} \<TTurnstile>e {Ca}"
  proof (intro ballI)
    fix Ca
    assume "Ca |\<in>| U\<^sub>p\<^sub>r"
    then obtain D1 D2 where
      "D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca" and
      "Ca \<noteq> eres D1 D2" and
      "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
      using U\<^sub>p\<^sub>r_spec by metis

    have "eres D1 D2 = eres D1 Ca"
      using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca\<close> eres_eq_after_tranclp_ground_resolution by metis

    show "\<exists>D |\<in>| U\<^sub>e\<^sub>r. D \<prec>\<^sub>c Ca \<and> {D} \<TTurnstile>e {Ca}"
    proof (intro bexI conjI)
      have "eres D1 Ca \<preceq>\<^sub>c Ca"
        using eres_le .
      thus "eres D1 D2 \<prec>\<^sub>c Ca"
        using \<open>Ca \<noteq> eres D1 D2\<close> \<open>eres D1 D2 = eres D1 Ca\<close> by order
    next
      show "{eres D1 D2} \<TTurnstile>e {Ca}"
        using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca\<close> eres_entails_resolvent by metis
    next
      show "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> by simp
    qed
  qed

  from step2 obtain s3' where S3'_def: "S3' = (N, s3')" and "ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'"
    by (auto simp: match_hyps(1,2) elim: ord_res_3_step.cases)

  show ?thesis
    using \<open>ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'\<close>
  proof (cases N "(U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" s3' rule: ord_res_3.cases)
    case (factoring C L U\<^sub>e\<^sub>f')

    define S2' where
      "S2' = (N, (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, finsert (efac C) U\<^sub>e\<^sub>f))"

    have "ord_res_2_step\<^sup>+\<^sup>+ S2 S2'"
      unfolding match_hyps(1,2) S2'_def
    proof (intro tranclp.r_into_trancl ord_res_2_step.intros ord_res_2.factoring)
      show "is_least_false_clause (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r) |\<union>| U\<^sub>e\<^sub>f) C"
        using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
        using least_false_conv
        by (metis sup_assoc)
    next
      show "ord_res.is_maximal_lit L C"
        using factoring by metis
    next
      show "is_pos L"
        using factoring by metis
    next
      show "finsert (efac C) U\<^sub>e\<^sub>f = finsert (efac C) U\<^sub>e\<^sub>f"
        by argo
    qed

    moreover have "match S2' S3'"
      unfolding S2'_def S3'_def
      unfolding factoring
      unfolding match_def
    proof (rule ord_res_2_matches_ord_res_3.intros)
      show "\<forall>Ca|\<in>|U\<^sub>p\<^sub>r.
        \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (efac C) U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (efac C) U\<^sub>e\<^sub>f.
        (ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca \<and> Ca \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using U\<^sub>p\<^sub>r_spec by auto
    qed

    ultimately show ?thesis
      by metis
  next
    case (resolution C L D U\<^sub>r\<^sub>r')

    have "(ground_resolution D)\<^sup>*\<^sup>* C (eres D C)" "\<nexists>x. ground_resolution D (eres D C) x"
      unfolding atomize_conj
      by (metis ex1_eres_eq_full_run_ground_resolution full_run_def)

    moreover have "\<exists>x. ground_resolution D C x"
      unfolding ground_resolution_def
      using resolution
      by (metis Neg_atm_of_iff ex_ground_resolutionI ord_res.mem_productionE singletonI)

    ultimately have "(ground_resolution D)\<^sup>+\<^sup>+ C (eres D C)"
      by (metis rtranclpD)

    then obtain n where "(ground_resolution D ^^ Suc n) C (eres D C)"
      by (metis not0_implies_Suc not_gr_zero tranclp_power)

    hence "resolvent_at D C (Suc n) = eres D C"
      by (metis Uniq_ground_resolution Uniq_relpowp resolvent_at_def the1_equality')

    have steps: "k \<le> Suc n \<Longrightarrow> (ord_res_2_step ^^ k)
      (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)" for k
    proof (induction k)
      case 0
      show ?case
        by simp
    next
      case (Suc k)
      have "k < Suc n"
        using \<open>Suc k \<le> Suc n\<close> by presburger
      hence "k \<le> Suc n"
        by presburger
      hence "(ord_res_2_step ^^ k) (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)"
        using Suc.IH by metis

      moreover have "ord_res_2_step
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k), U\<^sub>e\<^sub>f)"
        unfolding resolvents_upto_Suc
      proof (intro ord_res_2_step.intros ord_res_2.resolution)
        show "is_least_false_clause (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)
          (resolvent_at D C k)"
          using \<open>k < Suc n\<close>
        proof (induction k)
          case 0
          have "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
            using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
            unfolding least_false_conv .
          thus ?case
            unfolding funion_fempty_right funion_assoc[symmetric]
            by simp
        next
          case (Suc k')

          have "\<And>x. ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) x =
              ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) x"
            by (simp add: funion_left_commute sup_assoc sup_commute)
          also have "\<And>x. ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) x =
            ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x"
          proof (intro Interp_union_unproductive ballI)
            fix x y assume "y |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k')"
            hence "y |\<in>| U\<^sub>p\<^sub>r \<or> y |\<in>| resolvents_upto D C (Suc k')"
              by blast
            thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) y = {}"
            proof (elim disjE)
              assume "y |\<in>| U\<^sub>p\<^sub>r"
              thus ?thesis
                using U\<^sub>p\<^sub>r_unproductive by metis
            next
              assume "y |\<in>| resolvents_upto D C (Suc k')"
              then obtain i where "i |\<in>| fset_upto (Suc 0) (Suc k')" and "y = resolvent_at D C i"
                unfolding resolvents_upto_def by blast

              have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at D C i)"
              proof (rule nex_pos_strictly_max_lit_in_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C (eres D C)"
                  using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
              next
                have "i \<le> Suc k'"
                  using \<open>i |\<in>| fset_upto (Suc 0) (Suc k')\<close> by auto
                thus "i < Suc n"
                  using \<open>Suc k' < Suc n\<close> by presburger
              qed

              then show ?thesis
                using \<open>y = resolvent_at D C i\<close> unproductive_if_nex_strictly_maximal_pos_lit
                by metis
            qed
          qed simp_all
          finally have Interp_simp: "\<And>x.
            ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) x =
            ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x" .

          show ?case
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            have "resolvent_at D C (Suc k') |\<in>| resolvents_upto D C (Suc k')"
              using resolvent_at_fmember_resolvents_upto by simp
            thus "resolvent_at D C (Suc k') |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f"
              by simp
          next

            show "\<not> ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f))
              (resolvent_at D C (Suc k')) \<TTurnstile> resolvent_at D C (Suc k')"
              unfolding Interp_simp
              by (metis (no_types, lifting) Suc.prems Zero_not_Suc
                  \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> clause_true_if_resolved_true
                  insert_not_empty is_least_false_clause_def
                  linorder_cls.is_least_in_fset_ffilterD(2) local.resolution(2) local.resolution(7)
                  relpowp_to_resolvent_at tranclp_if_relpowp)
          next
            fix y
            assume "y \<noteq> resolvent_at D C (Suc k')"
            assume "\<not> ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
            hence "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
              unfolding Interp_simp .
            hence "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
              using Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f by metis

            assume "y |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f"
            hence "y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> y |\<in>| resolvents_upto D C (Suc k')"
              by auto
            thus "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
            proof (elim disjE)
              assume "y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              have "C \<preceq>\<^sub>c y"
              proof (cases "y = C")
                case True
                thus ?thesis
                  by order
              next
                case False
                thus ?thesis
                  using \<open>y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
                  using \<open>\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y\<close>
                  using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
                  unfolding least_false_conv[symmetric]
                  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
                  by simp
              qed

              moreover have "resolvent_at D C (Suc k') \<prec>\<^sub>c C"
                by (metis Suc.prems \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> less_or_eq_imp_le
                    resolvent_at_less_cls_resolvent_at resolvent_at_0 zero_less_Suc)

              ultimately show "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
                by order
            next
              assume "y |\<in>| resolvents_upto D C (Suc k')"
              then obtain i where
                i_in: "i |\<in>| fset_upto (Suc 0) (Suc k')" and y_def: "y = resolvent_at D C i"
                unfolding resolvents_upto_def by blast

              hence "i < Suc k'"
                using \<open>y \<noteq> resolvent_at D C (Suc k')\<close>
                by auto

              show "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
                unfolding y_def
              proof (rule resolvent_at_less_cls_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C (eres D C)"
                  using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
              next
                show "i < Suc k'"
                  using \<open>y \<noteq> resolvent_at D C (Suc k')\<close> i_in y_def by auto
              next
                show "Suc k' \<le> Suc n"
                  using \<open>Suc k' < Suc n\<close> by presburger
              qed
            qed
          qed
        qed
      next
        show "ord_res.is_maximal_lit L (resolvent_at D C k)"
        proof (rule max_lit_resolvent_at)
          show "(ground_resolution D ^^ Suc n) C (eres D C)"
            using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        next
          show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
        qed
      next
        show "is_neg L"
          using \<open>is_neg L\<close> .
      next
        show "D |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f"
          using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by auto
      next
        show "D \<prec>\<^sub>c resolvent_at D C k"
        proof (rule left_premisse_lt_resolvent_at)
          show "(ground_resolution D ^^ Suc n) C (eres D C)"
            using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        qed
      next
        have "ord_res.production (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)) D =
          ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k)) D"
          by (simp add: funion_left_commute sup_assoc sup_commute)
        also have "\<dots> = ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D"
        proof (intro production_union_unproductive ballI)
          fix x
          assume "x |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k"
          hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L x"
            unfolding funion_iff
          proof (elim disjE)
            assume "x |\<in>| U\<^sub>p\<^sub>r"
            thus ?thesis
              using U\<^sub>p\<^sub>r_spec
              by (metis eres_eq_after_tranclp_ground_resolution nex_strictly_maximal_pos_lit_if_neq_eres)
          next
            assume "x |\<in>| resolvents_upto D C k"
            then obtain i where "i |\<in>| fset_upto (Suc 0) k" and x_def: "x = resolvent_at D C i"
              unfolding resolvents_upto_def by auto

            have "0 < i" and "i \<le> k"
              using \<open>i |\<in>| fset_upto (Suc 0) k\<close> by simp_all

            show ?thesis
              unfolding x_def
            proof (rule nex_pos_strictly_max_lit_in_resolvent_at)
              show "(ground_resolution D ^^ Suc n) C (eres D C)"
                using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
            next
              show "i < Suc n"
                using \<open>i \<le> k\<close> \<open>k < Suc n\<close> by presburger
            qed
          qed
          thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union>
            fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k)) x = {}"
            using unproductive_if_nex_strictly_maximal_pos_lit by metis
        next
          show "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
        qed simp_all
        finally show "ord_res.production (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)) D =
          {atm_of L}"
          using \<open>ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}\<close> by argo
      next
        show "ord_res.ground_resolution (resolvent_at D C k) D (resolvent_at D C (Suc k))"
          unfolding ground_resolution_def[symmetric]
        proof (rule ground_resolution_resolvent_at_resolvent_at_Suc)
          show "(ground_resolution D ^^ Suc n) C (eres D C)"
            using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        qed
      next
        show "U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (resolvent_at D C (Suc k)) (resolvents_upto D C k) =
          finsert (resolvent_at D C (Suc k)) (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k)"
          by simp
      qed

      ultimately show ?case
        by (meson relpowp_Suc_I)
    qed

    hence "(ord_res_2_step ^^ Suc n) S2 (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n), U\<^sub>e\<^sub>f)"
      unfolding match_hyps(1,2) by blast

    moreover have "match (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n), U\<^sub>e\<^sub>f) S3'"
    proof -
      have 1: "S3' = (N, finsert (eres D C) U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)"
        unfolding S3'_def \<open>s3' = (U\<^sub>r\<^sub>r', U\<^sub>e\<^sub>f)\<close> \<open>U\<^sub>r\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r\<close> ..

      have 2: "U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n) =
        U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r"
        by (auto simp: \<open>resolvent_at D C (Suc n) = eres D C\<close>)

      show ?thesis
        unfolding match_def 1 2
      proof (rule ord_res_2_matches_ord_res_3.intros)
        show "\<forall>E|\<in>|U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n.
          \<exists>D1|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          (ground_resolution D1)\<^sup>+\<^sup>+ D2 E \<and> E \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
        proof (intro ballI)
          fix Ca
          assume "Ca |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n"
          hence "Ca |\<in>| U\<^sub>p\<^sub>r \<or> Ca |\<in>| resolvents_upto D C n"
            by simp
          thus "\<exists>D1|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
            (ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca \<and> Ca \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
          proof (elim disjE)
            show "Ca |\<in>| U\<^sub>p\<^sub>r \<Longrightarrow> ?thesis"
              using U\<^sub>p\<^sub>r_spec by auto
          next
            assume "Ca |\<in>| resolvents_upto D C n"
            then obtain i where i_in: "i |\<in>| fset_upto (Suc 0) n" and Ca_def:"Ca = resolvent_at D C i"
              unfolding resolvents_upto_def by auto

            from i_in have "0 < i" "i \<le> n"
              by simp_all

            show "?thesis"
            proof (intro bexI conjI)
              have "(ground_resolution D ^^ i) C Ca"
                unfolding \<open>Ca = resolvent_at D C i\<close>
              proof (rule relpowp_to_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C (eres D C)"
                  using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
              next
                show "i < Suc n"
                  using \<open>i \<le> n\<close> by presburger
              qed
              thus "(ground_resolution D)\<^sup>+\<^sup>+ C Ca"
                using \<open>0 < i\<close> by (simp add: tranclp_if_relpowp)
            next
              show "Ca \<noteq> eres D C"
                by (metis Ca_def \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close>
                  \<open>\<nexists>x. ground_resolution D (eres D C) x\<close> \<open>i \<le> n\<close>
                  ground_resolution_resolvent_at_resolvent_at_Suc less_Suc_eq_le)
            next
              show "eres D C |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
                by simp
            next
              show "D |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using resolution by simp
            next
              have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using resolution
                by (simp add: is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff)
              thus "C |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                by simp
            qed
          qed
        qed
      qed
    qed

    ultimately have "\<exists>S2'. (ord_res_2_step ^^ Suc n) S2 S2' \<and> match S2' S3'"
      by metis

    thus "\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match S2' S3'"
      by (metis Zero_neq_Suc tranclp_if_relpowp)
  qed
qed

lemma safe_states_if_ord_res_2_matches_ord_res_3:
  assumes match: "ord_res_2_matches_ord_res_3 S\<^sub>2 S\<^sub>3"
  shows
    "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    "safe_state ord_res_3_step ord_res_3_final S\<^sub>3"
proof -
  show "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    using safe_state_if_all_states_safe ord_res_2_step_safe by metis

  show "safe_state ord_res_3_step ord_res_3_final S\<^sub>3"
    using safe_state_if_all_states_safe ord_res_3_step_safe by metis
qed

theorem bisimulation_ord_res_2_ord_res_3:
  defines "match \<equiv> \<lambda>_ S2 S3. ord_res_2_matches_ord_res_3 S2 S3"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_2_state \<Rightarrow> 'f ord_res_3_state \<Rightarrow> bool) \<R>.
    bisimulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_2_state \<Rightarrow> 'f ord_res_3_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation ord_res_2_step ord_res_2_final ord_res_3_step ord_res_3_final MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_2_step"
    using right_unique_ord_res_2_step .
next
  show "right_unique ord_res_3_step"
    using right_unique_ord_res_3_step .
next
  show "\<forall>s1. ord_res_2_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_2_step s1 s1')"
    by (metis finished_def ord_res_2_semantics.final_finished)
next
  show "\<forall>s2. ord_res_3_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_3_step s2 s2')"
    by (metis finished_def ord_res_3_semantics.final_finished)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_2_final s1 = ord_res_3_final s2"
    unfolding match_def
    using ord_res_2_final_iff_ord_res_3_final by metis
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_2_step ord_res_2_final s1 \<and> safe_state ord_res_3_step ord_res_3_final s2"
    unfolding match_def
    using safe_states_if_ord_res_2_matches_ord_res_3 by metis
next
  show "wfP (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i s1 s2 s2'.
       match i s1 s2 \<longrightarrow>
       ord_res_3_step s2 s2' \<longrightarrow>
       (\<exists>i' s1'. ord_res_2_step\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> False)"
    unfolding match_def
    using backward_simulation_2_to_3 by metis
qed

end


section \<open>ORD-RES-4 (implicit factorization)\<close>

type_synonym 'f ord_res_4_state = "'f gclause fset \<times> 'f gclause fset \<times> 'f gclause fset"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_3_matches_ord_res_4 :: "'f ord_res_3_state \<Rightarrow> 'f ord_res_4_state \<Rightarrow> bool" where
  "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> U\<^sub>e\<^sub>f = iefac \<F> |`| {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} \<Longrightarrow>
  ord_res_3_matches_ord_res_4 (N, (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)) (N, U\<^sub>e\<^sub>r, \<F>)"

lemma ord_res_3_final_iff_ord_res_4_final:
  assumes match: "ord_res_3_matches_ord_res_4 S3 S4"
  shows "ord_res_3_final S3 \<longleftrightarrow> ord_res_4_final S4"
  using match
proof (cases S3 S4 rule: ord_res_3_matches_ord_res_4.cases)
  case match_hyps: (1 \<F> N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note invars = match_hyps(3-)

  have "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<longleftrightarrow> {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using invars by (auto simp: iefac_def)

  moreover have "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
    unfolding ex_false_clause_iff
    unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF invars(2)]
    unfolding is_least_false_clause_with_iefac_conv ..

  ultimately have "ord_res_final (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<longleftrightarrow> ord_res_final (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding ord_res_final_def by argo

  thus ?thesis
    unfolding match_hyps(1,2)
    by (simp add: ord_res_3_final.simps ord_res_4_final.simps)
qed

lemma forward_simulation_between_3_and_4:
  assumes
    match: "ord_res_3_matches_ord_res_4 S3 S4" and
    step: "ord_res_3_step S3 S3'"
  shows "(\<exists>S4'. ord_res_4_step\<^sup>+\<^sup>+ S4 S4' \<and> ord_res_3_matches_ord_res_4 S3' S4')"
  using match
proof (cases S3 S4 rule: ord_res_3_matches_ord_res_4.cases)
  case match_hyps: (1 \<F> N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note match_invars = match_hyps(3-)

  from step obtain s3' where step': "ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'" and "S3' = (N, s3')"
    unfolding match_hyps(1,2)
    by (auto elim: ord_res_3_step.cases)

  from step' show ?thesis
  proof (cases N "(U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" s3' rule: ord_res_3.cases)
    case (factoring C L U\<^sub>e\<^sub>f')

    have "\<not> ord_res.is_strictly_maximal_lit L C"
      using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close> \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
      by (metis (no_types, lifting) is_least_false_clause_def is_pos_def
        pos_lit_not_greatest_if_maximal_in_least_false_clause)

    have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    proof -
      have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
        by (simp add: is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff)
      moreover have "C |\<notin>| U\<^sub>e\<^sub>f"
      proof (rule notI)
        assume "C |\<in>| U\<^sub>e\<^sub>f"
        then obtain C\<^sub>0 where "C = iefac \<F> C\<^sub>0" and "C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac \<F> C\<^sub>0 \<noteq> C\<^sub>0"
          using match_invars(2) by force
        then show False
          by (metis Uniq_D \<open>\<not> ord_res.is_strictly_maximal_lit L C\<close> iefac_def
            linorder_lit.Uniq_is_maximal_in_mset
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset local.factoring(3)
            obtains_positive_greatest_lit_if_efac_not_ident)
      qed
      ultimately show ?thesis
        by simp
    qed

    show ?thesis
    proof (intro exI conjI)
      show "ord_res_4_step\<^sup>+\<^sup>+ S4 (N, U\<^sub>e\<^sub>r, finsert C \<F>)"
        unfolding match_hyps(1,2)
      proof (intro tranclp.r_into_trancl ord_res_4_step.intros ord_res_4.factoring)
        have "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
          using factoring by argo
        hence "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] .
        thus "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          unfolding is_least_false_clause_with_iefac_conv .
      next
        show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
      next
        show "is_pos L"
          using \<open>is_pos L\<close> .
      qed (rule refl)+
    next
      show "ord_res_3_matches_ord_res_4 S3' (N, U\<^sub>e\<^sub>r, finsert C \<F>)"
        unfolding \<open>S3' = (N, s3')\<close> \<open>s3' = (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f')\<close> \<open>U\<^sub>e\<^sub>f' = finsert (efac C) U\<^sub>e\<^sub>f\<close>
      proof (rule ord_res_3_matches_ord_res_4.intros)
        show "finsert C \<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
          using match_invars \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by simp
      next
        have "\<exists>C'. ord_res.ground_factoring C C'"
          using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
          by (metis \<open>\<not> ord_res.is_strictly_maximal_lit L C\<close> ex_ground_factoringI is_pos_def)
        hence "efac C \<noteq> C"
          by (metis ex1_efac_eq_factoring_chain)
        hence "iefac (finsert C \<F>) C \<noteq> C"
          by (simp add: iefac_def)

        have "{|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|} =
          finsert C {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> Ca \<noteq> Ca|}"
        proof (intro fsubset_antisym fsubsetI)
          fix x
          assume "x |\<in>| {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|}"
          hence "x |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac (finsert C \<F>) x \<noteq> x"
            by simp_all
          then show "x |\<in>| finsert C {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> Ca \<noteq> Ca|}"
            by (smt (verit, best) ffmember_filter finsert_iff iefac_def)
        next
          fix x
          assume "x |\<in>| finsert C {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> Ca \<noteq> Ca|}"
          hence "x = C \<or> x |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<and> iefac \<F> x \<noteq> x"
            by auto
          thus "x |\<in>| {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|}"
          proof (elim disjE conjE)
            assume "x = C"
            thus ?thesis
              using \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> \<open>iefac (finsert C \<F>) C \<noteq> C\<close> by auto
          next
            assume "x |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac \<F> x \<noteq> x"
            thus ?thesis
              by (smt (verit, best) ffmember_filter finsertCI iefac_def)
          qed
        qed
        thus "finsert (efac C) U\<^sub>e\<^sub>f =
          iefac (finsert C \<F>) |`| {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|}"
          using iefac_def match_invars(2) by auto
      qed
    qed
  next
    case (resolution C L D U\<^sub>r\<^sub>r')

    have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    proof -
      have "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        using resolution by argo
      hence "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] .
      moreover have "D |\<notin>| N |\<union>| U\<^sub>e\<^sub>r - iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        by (metis clauses_for_iefac_are_unproductive insert_not_empty local.resolution(7))
      ultimately show ?thesis
        by blast
    qed

    show ?thesis
    proof (intro exI conjI)
      show "ord_res_4_step\<^sup>+\<^sup>+ S4 (N, finsert (eres D C) U\<^sub>e\<^sub>r, \<F>)"
        unfolding match_hyps(1,2)
        proof (intro tranclp.r_into_trancl ord_res_4_step.intros ord_res_4.resolution)
          have "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
            using resolution by argo
          hence "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
            unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] .
          thus "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
            unfolding is_least_false_clause_with_iefac_conv .
        next
          show "ord_res.is_maximal_lit L C"
            using resolution by argo
        next
          show "is_neg L"
            using resolution by argo
        next
          show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
        next
          show "D \<prec>\<^sub>c C"
            using resolution by argo
        next
          have "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D =
            ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
            unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] ..
          also have "\<dots> = ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<union> fset (N |\<union>| U\<^sub>e\<^sub>r)) D"
            by (simp add: sup.commute)
          also have "\<dots> = ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          proof (rule production_union_unproductive_strong)
            show "\<forall>x \<in> fset (N |\<union>| U\<^sub>e\<^sub>r) - fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)).
              ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<union> fset (N |\<union>| U\<^sub>e\<^sub>r)) x = {}"
              using clauses_for_iefac_are_unproductive[of "N |\<union>| U\<^sub>e\<^sub>r" \<F>] by simp
          next
            show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
          qed (rule finite_fset)+

          finally show "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {atm_of L}"
            using resolution by argo
        qed (rule refl)+
    next
      show "ord_res_3_matches_ord_res_4 S3' (N, finsert (eres D C) U\<^sub>e\<^sub>r, \<F>)"
        unfolding \<open>S3' = (N, s3')\<close> \<open>s3' = (U\<^sub>r\<^sub>r', U\<^sub>e\<^sub>f)\<close> \<open>U\<^sub>r\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r\<close>
      proof (rule ord_res_3_matches_ord_res_4.intros)
        show "\<F> |\<subseteq>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r"
          using match_invars by auto
      next
        show "U\<^sub>e\<^sub>f = iefac \<F> |`| {|C |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} "
        proof (cases "eres D C |\<in>| \<F>")
          case True
          then show ?thesis
            using \<open>\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r\<close>
            using match_invars by force
        next
          case False
          hence "iefac \<F> (eres D C) = eres D C"
            by (simp add: iefac_def)
          hence "{|C |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} = {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|}"
            using ffilter_eq_ffilter_minus_singleton by auto
          thus ?thesis
            using match_invars by argo
        qed
      qed
    qed
  qed
qed

theorem bisimulation_ord_res_3_ord_res_4:
  defines "match \<equiv> \<lambda>_ S3 S4. ord_res_3_matches_ord_res_4 S3 S4"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_3_state \<Rightarrow> 'f ord_res_4_state \<Rightarrow> bool) \<R>.
    bisimulation ord_res_3_step ord_res_4_step ord_res_3_final ord_res_4_final \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_3_state \<Rightarrow> 'f ord_res_4_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation ord_res_3_step ord_res_3_final ord_res_4_step ord_res_4_final MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_3_step"
    using right_unique_ord_res_3_step .
next
  show "right_unique ord_res_4_step"
    using right_unique_ord_res_4_step .
next
  show "\<forall>s1. ord_res_3_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_3_step s1 s1')"
    by (metis finished_def ord_res_3_semantics.final_finished)
next
  show "\<forall>s2. ord_res_4_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_4_step s2 s2')"
    by (metis finished_def ord_res_4_semantics.final_finished)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_3_final s1 \<longleftrightarrow> ord_res_4_final s2"
    unfolding match_def
    using ord_res_3_final_iff_ord_res_4_final by metis
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_3_step ord_res_3_final s1 \<and> safe_state ord_res_4_step ord_res_4_final s2"
    using ord_res_3_step_safe ord_res_4_step_safe
    by (simp add: safe_state_if_all_states_safe)
next
  show "wfP (\<lambda>i' i. False)"
    by simp
next
  show "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> ord_res_3_step s1 s1' \<longrightarrow>
    (\<exists>i' s2'. ord_res_4_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> False)"
    unfolding match_def
    using forward_simulation_between_3_and_4 by metis
qed

end


section \<open>ORD-RES-5 (explicit model construction)\<close>

type_synonym 'f ord_res_5_state = "'f gclause fset \<times> 'f gclause fset \<times> 'f gclause fset \<times>
  ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_4_matches_ord_res_5 :: "'f ord_res_4_state \<Rightarrow> 'f ord_res_5_state \<Rightarrow> bool" where
  "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<Longrightarrow>
    (\<forall>C. \<C> = Some C \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C) \<Longrightarrow>
    ord_res_4_matches_ord_res_5 (N, U\<^sub>e\<^sub>r, \<F>) (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"

lemma ord_res_4_final_iff_ord_res_5_final:
  assumes match: "ord_res_4_matches_ord_res_5 S4 S5"
  shows "ord_res_4_final S4 \<longleftrightarrow> ord_res_5_final S5"
  using match
proof (cases S4 S5 rule: ord_res_4_matches_ord_res_5.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)

  show ?thesis
    unfolding match_hyps(1,2,3)
  proof (intro iffI ord_res_5_final.intros)
    assume "ord_res_4_final (N, U\<^sub>e\<^sub>r, \<F>)"
    hence "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<or> \<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
      by (simp add: ord_res_4_final.simps ord_res_final_def)
    thus "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    proof (elim disjE)
      assume "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      hence "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) {#}"
        using is_least_false_clause_mempty by metis
      hence "\<C> = Some {#}"
        by (smt (verit) all_smaller_clauses_true_wrt_respective_Interp_def is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff linorder_cls.le_imp_less_or_eq match_hyps(3)
            mempty_lesseq_cls ord_res_5_invars_def)
      thus ?thesis
        using ord_res_5_final.contradiction_found by metis
    next
      assume "\<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
      hence "\<C> = None"
        using match_hyps(2-)
        by (metis ex_false_clause_if_least_false_clause option.exhaust)
      thus ?thesis
        using ord_res_5_final.model_found by metis
    qed
  next
    assume "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    thus "ord_res_4_final (N, U\<^sub>e\<^sub>r, \<F>)"
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" rule: ord_res_5_final.cases)
      case model_found
      have "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
        using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        unfolding ord_res_5_invars_def by metis
      hence "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). ord_res_Interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r)) C \<TTurnstile> C"
        by (simp add: model_found all_smaller_clauses_true_wrt_respective_Interp_def)
      hence "\<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
        by (simp add: ex_false_clause_def)
      then show ?thesis
        by (metis ord_res_4_final.intros ord_res_final_def)
    next
      case contradiction_found
      hence "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        by (metis next_clause_in_factorized_clause_def ord_res_5_invars_def)
      then show ?thesis
        by (metis ord_res_4_final.intros ord_res_final_def)
    qed
  qed
qed

lemma forward_simulation_between_4_and_5:
  fixes S4 S4' S5
  assumes match: "ord_res_4_matches_ord_res_5 S4 S5" and step: "ord_res_4_step S4 S4'"
  shows "\<exists>S5'. ord_res_5_step\<^sup>+\<^sup>+ S5 S5' \<and> ord_res_4_matches_ord_res_5 S4' S5'"
  using match
proof (cases S4 S5 rule: ord_res_4_matches_ord_res_5.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)
  hence
    S4_def: "S4 = (N, U\<^sub>e\<^sub>r, \<F>)" and
    S5_def: "S5 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    unfolding atomize_conj by metis

  have dom_\<M>_eq: "\<And>C. \<C> = Some C \<Longrightarrow> dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    using match_hyps unfolding ord_res_5_invars_def model_eq_interp_upto_next_clause_def by simp

  obtain s4' where S4'_def: "S4' = (N, s4')" and step': "ord_res_4 N (U\<^sub>e\<^sub>r, \<F>) s4'"
    using step unfolding S4_def by (auto simp: ord_res_4_step.simps)

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>)" s4' rule: ord_res_4.cases)
    case step_hyps: (factoring NN C L \<F>')
    have "\<C> = Some C"
      using match_hyps(3-) step_hyps by metis

    define \<M>' :: "'f gterm \<Rightarrow> 'f gterm literal multiset option" where
      "\<M>' = (\<lambda>_. None)"

    define \<C>' :: "'f gclause option" where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)))"

    have ord_res_5_step: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>')"
    proof (rule ord_res_5.factoring)
      have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        using step_hyps by argo
      then show "\<not> dom \<M> \<TTurnstile> C"
        using dom_\<M>_eq[OF \<open>\<C> = Some C\<close>]
        by (metis (mono_tags, lifting) is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff ord_res_Interp_entails_if_greatest_lit_is_pos
            unproductive_if_nex_strictly_maximal_pos_lit sup_bot.right_neutral)
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by metis
    next
      show "is_pos L"
        using step_hyps by metis
    next
      show "\<not> ord_res.is_strictly_maximal_lit L C"
        using step_hyps
        by (metis (no_types, lifting) is_least_false_clause_def literal.collapse(1)
            pos_lit_not_greatest_if_maximal_in_least_false_clause)
    next
      show "\<F>' = finsert C \<F>"
        using step_hyps by metis
    qed (simp_all add: \<M>'_def \<C>'_def)

    moreover have "\<exists>\<M>'' \<C>''.
       (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'') \<and>
       (\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
    proof (rule ord_res_5_construct_model_upto_least_false_clause)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>')"
        using ord_res_5_step \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some C\<close>
        by (metis ord_res_5_preserves_invars)
    qed

    ultimately obtain \<M>'' \<C>'' where
      s5_steps: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')" and
      next_clause_least_false:
        "(\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
      by (meson rtranclp_into_tranclp2)

    have "ord_res_5_step\<^sup>+\<^sup>+ S5 (N, U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')"
      unfolding S5_def \<open>\<C> = Some C\<close>
      using s5_steps by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

    moreover have "ord_res_4_matches_ord_res_5 S4' (N, U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')"
      unfolding S4'_def \<open>s4' = (U\<^sub>e\<^sub>r, \<F>')\<close>
    proof (intro ord_res_4_matches_ord_res_5.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')"
        using s5_steps \<open>\<C> = Some C\<close> \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        by (smt (verit, best) ord_res_5_preserves_invars tranclp_induct)
    next
      show "\<forall>C. (\<C>'' = Some C) = is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        using next_clause_least_false .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution NN C L D U\<^sub>e\<^sub>r')
    have "\<C> = Some C"
      using match_hyps(3-) step_hyps by metis

    define \<M>' :: "'f gterm \<Rightarrow> 'f gterm literal multiset option" where
      "\<M>' = (\<lambda>_. None)"

    define \<C>' :: "'f gclause option" where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')))"

    have ord_res_5_step: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>')"
    proof (rule ord_res_5.resolution)
      have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        using step_hyps by argo
      then show "\<not> dom \<M> \<TTurnstile> C"
        using dom_\<M>_eq[OF \<open>\<C> = Some C\<close>]
        by (metis (mono_tags, lifting) is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff ord_res_Interp_entails_if_greatest_lit_is_pos
            unproductive_if_nex_strictly_maximal_pos_lit sup_bot.right_neutral)
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by metis
    next
      show "is_neg L"
        using step_hyps by metis
    next
      show "\<M> (atm_of L) = Some D"
        using step_hyps
        by (smt (verit) \<open>\<C> = Some C\<close> all_produced_atoms_in_model_def insertI1 match_hyps(3)
            ord_res_5_invars_def)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r"
        using step_hyps by metis
    qed (simp_all add: \<M>'_def \<C>'_def)

    moreover have "\<exists>\<M>'' \<C>''.
       (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'') \<and>
       (\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C)"
    proof (rule ord_res_5_construct_model_upto_least_false_clause)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>')"
        using ord_res_5_step \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some C\<close>
        by (metis ord_res_5_preserves_invars)
    qed

    ultimately obtain \<M>'' \<C>'' where
      s5_steps: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')" and
      next_clause_least_false:
        "(\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C)"
      by (meson rtranclp_into_tranclp2)

    have "ord_res_5_step\<^sup>+\<^sup>+ S5 (N, U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')"
      unfolding S5_def \<open>\<C> = Some C\<close>
      using s5_steps by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

    moreover have "ord_res_4_matches_ord_res_5 S4' (N, U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')"
      unfolding S4'_def \<open>s4' = (U\<^sub>e\<^sub>r', \<F>)\<close>
    proof (intro ord_res_4_matches_ord_res_5.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')"
        using s5_steps \<open>\<C> = Some C\<close> \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        by (smt (verit, best) ord_res_5_preserves_invars tranclp_induct)
    next
      show "\<forall>C. (\<C>'' = Some C) = is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
        using next_clause_least_false .
    qed

    ultimately show ?thesis
      by metis
  qed
qed

theorem bisimulation_ord_res_4_ord_res_5:
  defines "match \<equiv> \<lambda>_. ord_res_4_matches_ord_res_5"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_4_state \<Rightarrow> 'f ord_res_5_state \<Rightarrow> bool) \<R>.
    bisimulation ord_res_4_step ord_res_5_step ord_res_4_final ord_res_5_final \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_4_state \<Rightarrow> 'f ord_res_5_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation ord_res_4_step ord_res_4_final ord_res_5_step ord_res_5_final MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_4_step"
    using right_unique_ord_res_4_step .
next
  show "right_unique ord_res_5_step"
    using right_unique_ord_res_5_step .
next
  show "\<forall>s. ord_res_4_final s \<longrightarrow> (\<nexists>s'. ord_res_4_step s s')"
    by (metis finished_def ord_res_4_semantics.final_finished)
next
  show "\<forall>s. ord_res_5_final s \<longrightarrow> (\<nexists>s'. ord_res_5_step s s')"
    by (metis finished_def ord_res_5_semantics.final_finished)
next
  show "\<forall>i s4 s5. match i s4 s5 \<longrightarrow> ord_res_4_final s4 \<longleftrightarrow> ord_res_5_final s5"
    unfolding match_def
    using ord_res_4_final_iff_ord_res_5_final by metis
next
  show "\<forall>i S4 S5. match i S4 S5 \<longrightarrow>
    safe_state ord_res_4_step ord_res_4_final S4 \<and> safe_state ord_res_5_step ord_res_5_final S5"
  proof (intro allI impI conjI)
    fix i S4 S5
    show "safe_state ord_res_4_step ord_res_4_final S4"
      using ord_res_4_step_safe safe_state_if_all_states_safe by metis

    assume "match i S4 S5"
    thus "safe_state ord_res_5_step ord_res_5_final S5"
      using \<open>match i S4 S5\<close>
      using ord_res_5_safe_state_if_invars
      using match_def ord_res_4_matches_ord_res_5.cases by metis
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i s1 s2 s1'.
       match i s1 s2 \<longrightarrow>
       ord_res_4_step s1 s1' \<longrightarrow>
       (\<exists>i' s2'. ord_res_5_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> False)"
    unfolding match_def
    using forward_simulation_between_4_and_5 by metis
qed

end


section \<open>ORD-RES-6 (model backjump)\<close>

type_synonym 'f ord_res_6_state = "'f gclause fset \<times> 'f gclause fset \<times> 'f gclause fset \<times>
  ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_5_matches_ord_res_6 :: "'f ord_res_5_state \<Rightarrow> 'f ord_res_6_state \<Rightarrow> bool" where
  "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<Longrightarrow>
    ord_res_5_matches_ord_res_6 (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"

lemma ord_res_5_final_iff_ord_res_6_final:
  fixes i S5 S6
  assumes match: "ord_res_5_matches_ord_res_6 S5 S6"
  shows "ord_res_5_final S5 \<longleftrightarrow> ord_res_6_final S6"
  using match
proof (cases S5 S6 rule: ord_res_5_matches_ord_res_6.cases)
  case (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)
  thus ?thesis
    by (metis (no_types, opaque_lifting) ord_res_5_final.simps ord_res_6_final.cases
        ord_res_6_final.contradiction_found ord_res_6_final.model_found)
qed

lemma backward_simulation_between_5_and_6:
  fixes S5 S6 S6'
  assumes match: "ord_res_5_matches_ord_res_6 S5 S6" and step: "ord_res_6_step S6 S6'"
  shows "\<exists>S5'. ord_res_5_step\<^sup>+\<^sup>+ S5 S5' \<and> ord_res_5_matches_ord_res_6 S5' S6'"
  using match
proof (cases S5 S6 rule: ord_res_5_matches_ord_res_6.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)
  hence S5_def: "S5 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" and S6_def: "S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    by metis+

  obtain s6' where S6'_def: "S6' = (N, s6')" and step': "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) s6'"
    using step unfolding S6_def
    using ord_res_6_step.simps by auto

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" s6' rule: ord_res_6.cases)
    case step_hyps: (skip C \<C>')

    define S5' where
      "S5' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"

    show ?thesis
    proof (intro exI conjI)
      have step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using ord_res_5.skip step_hyps by metis
      hence "ord_res_5_step S5 S5'"
        unfolding S5_def S5'_def
        by (metis ord_res_5_step.simps step_hyps(1))
      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        by simp

      have "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using step5 match_hyps(3) ord_res_5_preserves_invars step_hyps(1) by metis
      thus "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')\<close>
        using ord_res_5_matches_ord_res_6.intros by metis
    qed
  next
    case step_hyps: (production C L \<M>' \<C>')

    define S5' where
      "S5' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"

    show ?thesis
    proof (intro exI conjI)
      have step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using ord_res_5.production step_hyps by metis
      hence "ord_res_5_step S5 S5'"
        unfolding S5_def S5'_def
        by (metis ord_res_5_step.simps step_hyps(1))
      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        by simp

      have "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using step5 match_hyps(3) ord_res_5_preserves_invars step_hyps(1) by metis
      thus "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close>
        using ord_res_5_matches_ord_res_6.intros by metis
    qed
  next
    case step_hyps: (factoring D K \<F>')

    define S5' where
      "S5' = (N, U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"

    have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      by (metis match_hyps(3) next_clause_in_factorized_clause_def ord_res_5_invars_def step_hyps(1))
    hence "iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) \<noteq> {||}"
      by blast
    then obtain C where C_least: "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
      by (metis linorder_cls.ex1_least_in_fset)

    have "efac D \<noteq> D"
      by (metis ex1_efac_eq_factoring_chain is_pos_def ex_ground_factoringI step_hyps(4,5,6))

    show ?thesis
    proof (intro exI conjI)
      have "The_optional (linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) = Some C"
      proof (rule The_optional_eq_SomeI)
        show "\<exists>\<^sub>\<le>\<^sub>1 x. linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) x"
          by blast
      next
        show "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          using C_least .
      qed
      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>', Map.empty, Some C)"
        using ord_res_5.factoring step_hyps by metis
      moreover have "(ord_res_5 N)\<^sup>*\<^sup>* \<dots> (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
      proof (rule full_rtranclp_ord_res_5_run_upto)
        show "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
          using step' S6_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))\<close> \<open>\<C> = Some D\<close> by argo
      next
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
          using match_hyps(3) ord_res_6_preserves_invars step' step_hyps(2) by blast
      next
        have "iefac \<F> D = D" and "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
          unfolding atomize_conj
          using \<open>efac D \<noteq> D\<close> \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>[unfolded fimage_iff]
          unfolding iefac_def
          by (metis ex1_efac_eq_factoring_chain factorizable_if_neq_efac)

        have iefac_\<F>'_eq: "iefac \<F>' = (iefac \<F>)(D := efac D)"
          unfolding \<open>\<F>' = finsert D \<F>\<close> iefac_def by auto

        have fimage_iefac_\<F>'_eq:
          "iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (efac D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r - {|D|}))"
          unfolding iefac_\<F>'_eq
          unfolding fun_upd_fimage[of "iefac \<F>" D "efac D"] \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close>
          using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by argo

        have "{|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|} =
          {|C |\<in>| finsert (efac D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r - {|D|})). C \<prec>\<^sub>c efac D|}"
          unfolding fimage_iefac_\<F>'_eq ..

        also have "\<dots> = {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r - {|D|}). C \<prec>\<^sub>c efac D|}"
          by auto

        also have "\<dots> = {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|}"
          by (smt (verit, ccfv_SIG) \<open>iefac \<F> D = D\<close> efac_properties_if_not_ident(1)
              ffilter_eq_ffilter_minus_singleton fimage_finsert finsertI1 finsert_fminus1
              finsert_fminus_single linorder_cls.less_imp_not_less)

        finally have "{|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|} =
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|}" .
      next
        have dom_\<M>_eq: "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some D\<close>
          unfolding ord_res_5_invars_def model_eq_interp_upto_next_clause_def
          by metis

        have "atm_of K \<notin> dom \<M>"
          by (metis linorder_lit.is_maximal_in_mset_iff literal.collapse(1)
              pos_literal_in_imp_true_cls step_hyps(3) step_hyps(4) step_hyps(5))

        have "A \<prec>\<^sub>t atm_of K" if "A \<in> dom \<M>" for A
        proof -
          obtain C where
            "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            "C \<prec>\<^sub>c D" and
            "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
            using \<open>A \<in> dom \<M>\<close> unfolding dom_\<M>_eq
            unfolding ord_res.interp_def UN_iff
            by blast

          hence "ord_res.is_strictly_maximal_lit (Pos A) C"
            using ord_res.mem_productionE by metis

          hence "Pos A \<preceq>\<^sub>l K"
            using \<open>ord_res.is_maximal_lit K D\<close> \<open>C \<prec>\<^sub>c D\<close>
            by (metis ord_res.asymp_less_lit ord_res.transp_less_lit linorder_cls.less_asym
                linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.leI
                linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp_eq_multp\<^sub>H\<^sub>O)

          hence "A \<preceq>\<^sub>t atm_of K"
            by (metis literal.collapse(1) literal.sel(1) ord_res.less_lit_simps(1) reflclp_iff
                step_hyps(5))

          moreover have "A \<noteq> atm_of K"
            using \<open>atm_of K \<notin> dom \<M>\<close> \<open>A \<in> dom \<M>\<close> by metis

          ultimately show ?thesis
            by order
        qed
        hence "dom \<M> \<subseteq> {A. \<exists>K. ord_res.is_maximal_lit K (efac D) \<and> A \<prec>\<^sub>t atm_of K}"
          using linorder_lit.is_maximal_in_mset_iff step_hyps(4) by auto
        thus "\<M> = restrict_map \<M> {A. \<exists>K. ord_res.is_maximal_lit K (efac D) \<and> A \<prec>\<^sub>t atm_of K}"
          using restrict_map_ident_if_dom_subset by fastforce
      next
        show "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          using C_least .
      qed
      ultimately have steps5: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
        by simp
      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        using S5'_def S5_def step_hyps(1) tranclp_ord_res_5_step_if_tranclp_ord_res_5 by metis

      have "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
        using steps5 match_hyps(3) tranclp_ord_res_5_preserves_invars step_hyps(1) by metis
      thus "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))\<close>
        using ord_res_5_matches_ord_res_6.intros by metis
    qed
  next
    case step_hyps: (resolution_bot C L D U\<^sub>e\<^sub>r' \<M>')

    define S5' :: "_ \<times> _ \<times> _ \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option" where
      "S5' = (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some {#})"

    show ?thesis
    proof (intro exI conjI)
      have "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
        using \<open>U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r\<close> \<open>eres D C = {#}\<close>
        using iefac_def by simp

      hence "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) {#}"
        by (metis linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
            linorder_cls.is_minimal_in_fset_iff linorder_cls.leD mempty_lesseq_cls)

      hence "The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) = Some {#}"
        by (metis linorder_cls.Uniq_is_least_in_fset The_optional_eq_SomeI)

      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some {#})"
        using ord_res_5.resolution step_hyps by metis

      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        unfolding S5_def \<open>\<C> = Some C\<close> S5'_def
        by (simp only: ord_res_5_step.intros tranclp.r_into_trancl)

      show "ord_res_5_matches_ord_res_6 S5' S6'"
        using step5
        by (metis S5'_def S6'_def match_hyps(3) ord_res_5_matches_ord_res_6.intros
            ord_res_5_preserves_invars step_hyps(1) step_hyps(2))
    qed
  next
    case step_hyps: (resolution_pos E L D U\<^sub>e\<^sub>r' \<M>' K)

    define S5' :: "_ \<times> _ \<times> _ \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option" where
      "S5' = (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"

    hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<noteq> {||}"
      using \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp
    then obtain C where C_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
      by (metis linorder_cls.ex1_least_in_fset)

    show ?thesis
    proof (intro exI conjI)
      have "The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) = Some C"
      proof (rule The_optional_eq_SomeI)
        show "\<exists>\<^sub>\<le>\<^sub>1 x. linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) x"
          by blast
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
          using C_least .
      qed

      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, Map.empty, Some C)"
        using ord_res_5.resolution step_hyps by metis

      moreover have "(ord_res_5 N)\<^sup>*\<^sup>* \<dots> (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      proof (rule full_rtranclp_ord_res_5_run_upto)
        show "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
          using step' \<open>\<C> = Some E\<close> \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))\<close> by argo
      next
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
          using match_hyps(3) ord_res_6_preserves_invars step' step_hyps(2) by blast
      next
        have "eres D E \<noteq> E"
          using step_hyps by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

        moreover have "eres D E \<preceq>\<^sub>c E"
          using eres_le .

        ultimately have "eres D E \<prec>\<^sub>c E"
          by order

        have "\<forall>F. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) F \<longrightarrow> E \<preceq>\<^sub>c F"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
          unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
          using next_clause_lt_least_false_clause[of N "(U\<^sub>e\<^sub>r, \<F>, \<M>, Some E)"]
          by simp

        have E_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) E"
          unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
        proof (intro conjI ballI impI)
          show "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
            unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
            by (metis next_clause_in_factorized_clause_def)
        next
          have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
            using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
            unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
            using \<open>\<not> dom \<M> \<TTurnstile> E\<close> by (metis model_eq_interp_upto_next_clause_def)
          moreover have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E = {}"
          proof -
            have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L E"
              using \<open>ord_res.is_maximal_lit L E\<close> \<open>is_neg L\<close>
              by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset
                  linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
            thus ?thesis
              using unproductive_if_nex_strictly_maximal_pos_lit by metis
          qed
          ultimately show "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
            by simp
        next
          fix F
          assume F_in: "F |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "F \<noteq> E" and
            F_false: "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) F \<TTurnstile> F"
          have "\<not> F \<prec>\<^sub>c E"
            using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
            unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
            unfolding all_smaller_clauses_true_wrt_respective_Interp_def
            using F_in F_false
            by (metis option.inject)
          thus "E \<prec>\<^sub>c F"
            using \<open>F \<noteq> E\<close> by order
        qed

        have D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<noteq> {}"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
          unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
          by (metis atoms_in_model_were_produced_def empty_iff step_hyps(6))

        have "iefac \<F> (eres D E) = eres D E"
          using E_least_false D_prod
          by (smt (verit, ccfv_threshold)
              \<open>\<forall>F. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) F \<longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= E F\<close>
              \<open>eres D E \<prec>\<^sub>c E\<close> clause_true_if_resolved_true ex1_eres_eq_full_run_ground_resolution
              fimage_finsert finsert_absorb finsert_iff full_run_def funion_finsert_right
              is_least_false_clause_def is_least_false_clause_finsert_smaller_false_clause
              linorder_cls.is_least_in_fset_ffilterD(2) linorder_cls.leD match_hyps(3)
              next_clause_in_factorized_clause_def ord_res_5_invars_def ord_res_6_preserves_invars
              rtranclpD step' step_hyps(2) step_hyps(7))

        hence "{|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c eres D E|} =
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c eres D E|}"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by auto
      next
        show "\<M>' = restrict_map \<M> {A. \<exists>K. ord_res.is_maximal_lit K (eres D E) \<and> A \<prec>\<^sub>t atm_of K}"
          using \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close>
          by (smt (verit, ccfv_SIG) Collect_cong linorder_lit.Uniq_is_maximal_in_mset step_hyps(10)
              the1_equality')
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
          using C_least .
      qed

      ultimately have steps5: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
        by simp

      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        unfolding S5_def \<open>\<C> = Some E\<close> S5'_def
        by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

      show "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))\<close>
        using steps5
        using match_hyps(3) ord_res_5_matches_ord_res_6.intros ord_res_6_preserves_invars step'
          step_hyps(2) by metis
    qed
  next
    case step_hyps: (resolution_neg E L D U\<^sub>e\<^sub>r' \<M>' K C)

    define S5' :: "_ \<times> _ \<times> _ \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option" where
      "S5' = (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"

    hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<noteq> {||}"
      using \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp
    then obtain B where B_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) B"
      by (metis linorder_cls.ex1_least_in_fset)

    show ?thesis
    proof (intro exI conjI)
      have "The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) = Some B"
      proof (rule The_optional_eq_SomeI)
        show "\<exists>\<^sub>\<le>\<^sub>1 x. linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) x"
          by blast
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) B"
          using B_least .
      qed

      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, Map.empty, Some B)"
        using ord_res_5.resolution step_hyps by metis

      moreover have "(ord_res_5 N)\<^sup>*\<^sup>* \<dots> (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      proof (rule full_rtranclp_ord_res_5_run_upto)
        show "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
          using step' \<open>\<C> = Some E\<close> \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)\<close> by argo
      next
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
          using match_hyps(3) ord_res_6_preserves_invars step' step_hyps(2) by blast
      next
        have "ord_res.is_strictly_maximal_lit (Pos (atm_of K)) C"
          using \<open>\<M> (atm_of K) = Some C\<close>
            \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>[unfolded ord_res_5_invars_def
              atoms_in_model_were_produced_def, simplified]
          using ord_res.mem_productionE by blast

        moreover have "Pos (atm_of K) \<prec>\<^sub>l K"
          using \<open>is_neg K\<close> by (cases K) simp_all

        ultimately have "C \<prec>\<^sub>c eres D E"
          using \<open>ord_res.is_maximal_lit K (eres D E)\<close>
          by (metis ord_res.asymp_less_lit ord_res.transp_less_lit
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
              linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp_eq_multp\<^sub>H\<^sub>O)

        hence "C \<prec>\<^sub>c E"
          using eres_le[of D E] by order

        have "C \<prec>\<^sub>c efac (eres D E)"
          by (metis Uniq_D \<open>C \<prec>\<^sub>c eres D E\<close> efac_spec is_pos_def linorder_lit.Uniq_is_maximal_in_mset
              step_hyps(10) step_hyps(11))

        moreover have "efac (eres D E) \<preceq>\<^sub>c eres D E"
          by (metis efac_subset subset_implies_reflclp_multp)

        ultimately have "C \<prec>\<^sub>c iefac \<F> (eres D E)"
          unfolding iefac_def by auto

        hence "{|Ca |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). Ca \<prec>\<^sub>c C|} =
          {|Ca |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). Ca \<prec>\<^sub>c C|}"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by auto

        have "(\<exists>K. ord_res.is_maximal_lit K C \<and> A \<prec>\<^sub>t atm_of K) \<longleftrightarrow> A \<prec>\<^sub>t atm_of K" for A
          using \<open>ord_res.is_strictly_maximal_lit (Pos (atm_of K)) C\<close>
          by (metis Uniq_def linorder_lit.Uniq_is_maximal_in_mset
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.sel(1))

        hence "{A. \<exists>K. ord_res.is_maximal_lit K C \<and> A \<prec>\<^sub>t atm_of K} = {A. A \<prec>\<^sub>t atm_of K}"
          by metis

        thus "\<M>' = restrict_map \<M> {A. \<exists>K. ord_res.is_maximal_lit K C \<and> A \<prec>\<^sub>t atm_of K}"
          using \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by argo
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) B"
          using B_least .
      qed

      ultimately have steps5: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
        by simp

      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        unfolding S5_def \<open>\<C> = Some E\<close> S5'_def
        by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

      show "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)\<close>
        using steps5
        using match_hyps(3) ord_res_5_matches_ord_res_6.intros ord_res_6_preserves_invars step'
          step_hyps(2) by metis
    qed
  qed
qed

theorem bisimulation_ord_res_5_ord_res_6:
  defines "match \<equiv> \<lambda>_. ord_res_5_matches_ord_res_6"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_5_state \<Rightarrow> 'f ord_res_6_state \<Rightarrow> bool) \<R>.
    bisimulation ord_res_5_step ord_res_6_step ord_res_5_final ord_res_6_final \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_5_state \<Rightarrow> 'f ord_res_6_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation ord_res_5_step ord_res_5_final ord_res_6_step ord_res_6_final MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_5_step"
    using right_unique_ord_res_5_step .
next
  show "right_unique ord_res_6_step"
    using right_unique_ord_res_6_step .
next
  show "\<forall>s. ord_res_5_final s \<longrightarrow> (\<nexists>s'. ord_res_5_step s s')"
    by (metis finished_def ord_res_5_semantics.final_finished)
next
  show "\<forall>s. ord_res_6_final s \<longrightarrow> (\<nexists>s'. ord_res_6_step s s')"
    by (metis finished_def ord_res_6_semantics.final_finished)
next
  show "\<forall>i S5 S6. match i S5 S6 \<longrightarrow> ord_res_5_final S5 \<longleftrightarrow> ord_res_6_final S6"
    unfolding match_def
    using ord_res_5_final_iff_ord_res_6_final by metis
next
  show "\<forall>i S5 S6.
       match i S5 S6 \<longrightarrow>
       safe_state ord_res_5_step ord_res_5_final S5 \<and> safe_state ord_res_6_step ord_res_6_final S6"
  proof (intro allI impI conjI)
    fix i S5 S6
    assume "match i S5 S6"
    show "safe_state ord_res_5_step ord_res_5_final S5"
      using \<open>match i S5 S6\<close>
      using ord_res_5_safe_state_if_invars
      using match_def ord_res_5_matches_ord_res_6.cases by metis
    show "safe_state ord_res_6_step ord_res_6_final S6"
      using \<open>match i S5 S6\<close>
      using ord_res_6_safe_state_if_invars
      using match_def ord_res_5_matches_ord_res_6.cases by metis
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i S5 S6 S6'.
       match i S5 S6 \<longrightarrow>
       ord_res_6_step S6 S6' \<longrightarrow>
       (\<exists>i' S5'. ord_res_5_step\<^sup>+\<^sup>+ S5 S5' \<and> match i' S5' S6') \<or> (\<exists>i'. match i' S5 S6' \<and> False)"
    unfolding match_def
    using backward_simulation_between_5_and_6 by metis
qed

end


section \<open>ORD-RES-7 (clause-guided literal trail construction)\<close>

type_synonym 'f ord_res_7_state =
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gliteral \<times> 'f gclause option) list \<times>
    'f gclause option"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_6_matches_ord_res_7 ::
  "'f gterm fset \<Rightarrow> 'f ord_res_6_state \<Rightarrow> 'f ord_res_7_state \<Rightarrow> bool" where
  "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<Longrightarrow>
    ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) \<Longrightarrow>
    (\<forall>A C. \<M> A = Some C \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)) \<Longrightarrow>
    (\<forall>A. \<M> A = None \<longleftrightarrow> map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) - trail_atms \<Gamma> \<Longrightarrow>
    ord_res_6_matches_ord_res_7 i (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"

lemma ord_res_6_final_iff_ord_res_7_final:
  fixes i S6 S7
  assumes match: "ord_res_6_matches_ord_res_7 i S6 S7"
  shows "ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
  using match
proof (cases i S6 S7 rule: ord_res_6_matches_ord_res_7.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C> \<Gamma>)

  show "ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
  proof (rule iffI)
    assume "ord_res_6_final S6"
    thus "ord_res_7_final S7"
      unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" rule: ord_res_6_final.cases)
      case model_found
      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.model_found
        by metis
    next
      case contradiction_found
      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.contradiction_found
        by metis
    qed
  next
    assume "ord_res_7_final S7"
    thus "ord_res_6_final S6"
      unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_final.cases)
      case model_found
      thus "ord_res_6_final S6"
        unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        using ord_res_6_final.model_found
        by metis
    next
      case contradiction_found
      thus "ord_res_6_final S6"
        unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        using ord_res_6_final.contradiction_found
        by metis
    qed
  qed
qed

lemma backward_simulation_between_6_and_7:
  fixes i S6 S7 S7'
  assumes match: "ord_res_6_matches_ord_res_7 i S6 S7" and step: "constant_context ord_res_7 S7 S7'"
  shows "
    (\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> ord_res_6_matches_ord_res_7 i' S6' S7') \<or>
    (\<exists>i'. ord_res_6_matches_ord_res_7 i' S6 S7' \<and> i' |\<subset>| i)"
  using match
proof (cases i S6 S7 rule: ord_res_6_matches_ord_res_7.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C> \<Gamma>)

  note S6_def = \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
  note invars_6 = \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
  note invars_7 = \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>[
      unfolded ord_res_7_invars_def, rule_format, OF refl] 

  have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invars_7 by argo

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using invars_7 by (metis trail_consistent_if_sorted_wrt_atoms)

  hence \<Gamma>_distinct_atoms: "distinct (map fst \<Gamma>)"
    using distinct_lits_if_trail_consistent by iprover

  have clause_true_wrt_model_if_true_wrt_\<Gamma>: "dom \<M> \<TTurnstile> D"
    if D_true: "trail_true_cls \<Gamma> D" for D
  proof -
    obtain L where "L \<in># D" and L_true: "trail_true_lit \<Gamma> L"
      using D_true unfolding trail_true_cls_def by auto

    have "\<exists>\<C>. (L, \<C>) \<in> set \<Gamma>"
      using L_true unfolding trail_true_lit_def by auto

    show ?thesis
    proof (cases L)
      case (Pos A)

      then obtain C where "(Pos A, Some C) \<in> set \<Gamma>"
        using invars_7 \<open>\<exists>\<C>. (L, \<C>) \<in> set \<Gamma>\<close>
        by (metis fst_conv literal.disc(1) not_None_eq snd_conv)

      hence "map_of \<Gamma> (Pos A) = Some (Some C)"
        using \<Gamma>_distinct_atoms by (metis map_of_is_SomeI)

      hence "\<M> A = Some C"
        using \<open>\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))\<close> by metis

      hence "A \<in> dom \<M>"
        by blast

      then show ?thesis
        using \<open>L \<in># D\<close> \<open>L = Pos A\<close> by blast
    next
      case (Neg A)

      hence "(Neg A, None) \<in> set \<Gamma>"
        using invars_7 \<open>\<exists>\<C>. (L, \<C>) \<in> set \<Gamma>\<close>
        by (metis fst_conv literal.disc(2) snd_conv)

      hence "map_of \<Gamma> (Neg A) \<noteq> None"
        by (simp add: weak_map_of_SomeI)

      hence "\<M> A = None"
        using \<open>\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)\<close> by metis

      hence "A \<notin> dom \<M>"
        by blast

      then show ?thesis
        using \<open>L \<in># D\<close> \<open>L = Neg A\<close> by blast
    qed
  qed

  have clause_false_wrt_model_if_false_wrt_\<Gamma>: "\<not> dom \<M> \<TTurnstile> D"
    if D_false: "trail_false_cls \<Gamma> D" for D
    unfolding true_cls_def
  proof (intro notI , elim bexE)
    fix L :: "'f gterm literal"
    assume "L \<in># D" and "dom \<M> \<TTurnstile>l L"

    have "trail_false_lit \<Gamma> L"
      using \<open>L \<in># D\<close> D_false unfolding trail_false_cls_def by metis

    hence "\<not> trail_true_lit \<Gamma> L" and "trail_defined_lit \<Gamma> L"
      unfolding atomize_conj
      using \<Gamma>_consistent \<open>L \<in># D\<close> not_trail_true_cls_and_trail_false_cls that
        trail_defined_lit_iff_true_or_false trail_true_cls_def by blast

    show False
    proof (cases L)
      case (Pos A)

      hence "\<M> A \<noteq> None"
        using \<open>dom \<M> \<TTurnstile>l L\<close> by blast

      hence "map_of \<Gamma> (Pos A) \<noteq> None"
        using \<open>\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))\<close> by blast

      hence "Pos A \<in> fst ` set \<Gamma>"
        by (simp add: map_of_eq_None_iff)

      hence "trail_true_lit \<Gamma> (Pos A)"
        unfolding trail_true_lit_def .

      moreover have "\<not> trail_true_lit \<Gamma> (Pos A)"
        using \<open>\<not> trail_true_lit \<Gamma> L\<close> \<open>L = Pos A\<close> by argo

      ultimately show False
        by contradiction
    next
      case (Neg A)

      hence "\<M> A = None"
        using \<open>dom \<M> \<TTurnstile>l L\<close> by blast

      hence "map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
        using \<open>\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)\<close> by blast

      hence "trail_true_lit \<Gamma> (Neg A) \<or> \<not> trail_defined_lit \<Gamma> (Neg A)"
        unfolding map_of_eq_None_iff not_not
        unfolding trail_true_lit_def trail_defined_lit_iff_trail_defined_atm literal.sel
        .

      then show ?thesis
        using \<open>\<not> trail_true_lit \<Gamma> L\<close> \<open>trail_defined_lit \<Gamma> L\<close> \<open>L = Neg A\<close> by argo
    qed
  qed

  obtain s7' where
    "S7' = (N, s7')" and
    step': "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) s7'"
    using step unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    by (auto elim: constant_context.cases)

  have invars_s7': "ord_res_7_invars N s7'"
    using ord_res_7_preserves_invars[OF step' \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>] .

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" s7' rule: ord_res_7.cases)
    case step_hyps: (decide_neg C L A \<Gamma>')

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "A \<prec>\<^sub>t atm_of L" and "A |\<notin>| trail_atms \<Gamma>"
      using step_hyps unfolding atomize_conj linorder_trm.is_least_in_ffilter_iff by argo

    have "ord_res_6_matches_ord_res_7 i' S6 S7'"
      unfolding S6_def \<open>\<C> = Some C\<close> \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
        using invars_6 unfolding \<open>\<C> = Some C\<close> .
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        using match_hyps unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
        using match_hyps \<open>A |\<notin>| trail_atms \<Gamma>\<close> by force
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        unfolding i'_def ..
    qed

    moreover have "i' |\<subset>| i"
    proof -
      have "i = finsert A i'"
        unfolding match_hyps i'_def
        using \<open>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>A |\<notin>| trail_atms \<Gamma>\<close> step_hyps(6) by force

      moreover have "A |\<notin>| i'"
        unfolding i'_def
        using step_hyps(6) by fastforce

      ultimately show ?thesis
        by auto
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_defined C L \<C>')

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"

    have C_almost_defined: "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      using step_hyps by (metis clause_almost_definedI invars_7)

    hence C_defined: "trail_defined_cls \<Gamma> C"
      using step_hyps unfolding trail_defined_cls_def by auto

    hence C_true: "trail_true_cls \<Gamma> C"
      using step_hyps by (metis trail_true_or_false_cls_if_defined)

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using clause_true_wrt_model_if_true_wrt_\<Gamma>[OF C_true] .
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps by argo
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)"
        using match_hyps by argo
    next
      show "i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>"
        using match_hyps by argo
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_undefined_neg C L \<Gamma>' \<C>')

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "trail_true_lit \<Gamma>' L"
      unfolding \<open>\<Gamma>' = (L, None) # \<Gamma>\<close> by (simp add: trail_true_lit_def)

    hence C_true: "trail_true_cls \<Gamma>' C"
      using step_hyps unfolding linorder_lit.is_maximal_in_mset_iff trail_true_cls_def by metis

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using C_true
        by (metis domIff linorder_lit.is_maximal_in_mset_iff literal.collapse(2) match_hyps(6)
            step_hyps(4) step_hyps(6) step_hyps(7) trail_defined_lit_iff_trail_defined_atm
            true_cls_def true_lit_simps(2))
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        using match_hyps
        unfolding \<open>\<Gamma>' = (L, None) # \<Gamma>\<close>
        by (metis literal.disc(1) map_of_Cons_code(2) step_hyps(7))
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        using match_hyps
        unfolding \<open>\<Gamma>' = (L, None) # \<Gamma>\<close>
        by (metis finsert_iff literal.collapse(2) literal.sel(2) map_of_Cons_code(2) option.discI
            prod.sel(1) step_hyps(6) step_hyps(7) trail_atms.simps(2)
            trail_defined_lit_iff_trail_defined_atm)
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_undefined_pos C L D)

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"

    have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L \<and> x \<noteq> - L#}"
    proof (rule clause_almost_almost_definedI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars_7 step_hyps by metis
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)"
        using step_hyps by argo
    qed

    moreover have "- L \<notin># C"
      by (metis atm_of_uminus is_pos_def linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE
          linorder_trm.less_irrefl literal.collapse(2) literal.sel(1) ord_res.less_lit_simps(4)
          step_hyps(4) step_hyps(7) uminus_not_id')

    ultimately have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      unfolding trail_defined_cls_def by auto

    hence "trail_true_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      using \<open>\<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close> by (metis trail_true_or_false_cls_if_defined)

    hence C_true: "trail_true_cls \<Gamma> C"
      by (auto simp: trail_true_cls_def)

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using clause_true_wrt_model_if_true_wrt_\<Gamma>[OF C_true] .
    next
      show "Some D = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using linorder_cls.Uniq_is_least_in_fset step_hyps(9) The_optional_eq_SomeI
        by fastforce
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps by argo
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)"
        using match_hyps by argo
    next
      show "i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>"
        using match_hyps by argo
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_undefined_pos_ultimate C L \<Gamma>')
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, None :: 'f gclause option)"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L \<and> x \<noteq> - L#}"
    proof (rule clause_almost_almost_definedI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars_7 step_hyps by metis
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)"
        using step_hyps by argo
    qed

    moreover have "- L \<notin># C"
      by (metis atm_of_uminus is_pos_def linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE
          linorder_trm.less_irrefl literal.collapse(2) literal.sel(1) ord_res.less_lit_simps(4)
          step_hyps(4) step_hyps(7) uminus_not_id')

    ultimately have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      unfolding trail_defined_cls_def by auto

    hence "trail_true_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      using \<open>\<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close> by (metis trail_true_or_false_cls_if_defined)

    hence C_true: "trail_true_cls \<Gamma> C"
      by (auto simp: trail_true_cls_def)

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, None)"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using clause_true_wrt_model_if_true_wrt_\<Gamma>[OF C_true] .
    next
      have "\<not> (\<exists>D. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D)"
        using \<open>\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) ((\<prec>\<^sub>c) C)\<close>
        by (meson linorder_cls.is_least_in_ffilter_iff)

      thus "None = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        unfolding The_optional_def by metis
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, None)"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (- L, None) # \<Gamma>\<close>
        by (metis is_pos_neg_not_is_pos literal.disc(1) map_of_Cons_code(2) step_hyps(7))
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (- L, None) # \<Gamma>\<close>
        by (metis (no_types, opaque_lifting) atm_of_eq_atm_of eq_fst_iff fset_simps(2) insertCI
            insertE literal.discI(2) literal.sel(2) map_of_Cons_code(2) option.distinct(1)
            trail_defined_lit_iff_trail_defined_atm step_hyps(6) step_hyps(7) trail_atms.simps(2))
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (production C L \<Gamma>' \<C>')
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>(atm_of L \<mapsto> C), \<C>')"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "L \<in># C"
      using step_hyps unfolding linorder_lit.is_maximal_in_mset_iff by argo

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>(atm_of L \<mapsto> C), \<C>')"
    proof (rule ord_res_6.production)
      have "atm_of L |\<notin>| trail_atms \<Gamma>"
        using \<open>\<not> trail_defined_lit \<Gamma> L\<close>
        unfolding trail_defined_lit_iff_trail_defined_atm .

      hence "\<M> (atm_of L) = None"
        using match_hyps(3-) by metis

      hence "atm_of L \<notin> dom \<M>"
        unfolding dom_def by simp

      hence "\<not> dom \<M> \<TTurnstile>l L"
        using \<open>is_pos L\<close> unfolding true_lit_def by metis

      moreover have "\<not> dom \<M> \<TTurnstile> {#K \<in># C. K \<noteq> L#}"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close>] .

      ultimately show "\<not> dom \<M> \<TTurnstile> C"
        using \<open>L \<in># C\<close>
        unfolding true_cls_def by auto
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "is_pos L"
        using step_hyps by argo
    next
      show "ord_res.is_strictly_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<M>(atm_of L \<mapsto> C) = \<M>(atm_of L \<mapsto> C)" ..
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>(atm_of L \<mapsto> C), \<C>')"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> .
    next
      show "\<forall>A D. ((\<M>(atm_of L \<mapsto> C)) A = Some D) = (map_of \<Gamma>' (Pos A) = Some (Some D))"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>
        using step_hyps(7) by auto
    next
      show "\<forall>A. ((\<M>(atm_of L \<mapsto> C)) A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>
        by (metis (no_types, opaque_lifting) domI domIff finsert_iff fun_upd_apply
            literal.collapse(1) literal.discI(2) map_of_Cons_code(2) map_of_eq_None_iff prod.sel(1)
            step_hyps(6) step_hyps(7) trail_atms.simps(2) trail_defined_lit_def uminus_Pos)
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (factoring C L \<F>')
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"

    have "L \<in># C"
      using step_hyps unfolding linorder_lit.is_maximal_in_mset_iff by argo

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
    proof (rule ord_res_6.factoring)
      have "atm_of L |\<notin>| trail_atms \<Gamma>"
        using \<open>\<not> trail_defined_lit \<Gamma> L\<close>
        unfolding trail_defined_lit_iff_trail_defined_atm .

      hence "\<M> (atm_of L) = None"
        using match_hyps(3-) by metis

      hence "atm_of L \<notin> dom \<M>"
        unfolding dom_def by simp

      hence "\<not> dom \<M> \<TTurnstile>l L"
        using \<open>is_pos L\<close> unfolding true_lit_def by metis

      moreover have "\<not> dom \<M> \<TTurnstile> {#K \<in># C. K \<noteq> L#}"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close>] .

      ultimately show "\<not> dom \<M> \<TTurnstile> C"
        using \<open>L \<in># C\<close>
        unfolding true_cls_def by auto
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "is_pos L"
        using step_hyps by argo
    next
      show "\<not> ord_res.is_strictly_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<F>' = finsert C \<F>"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps(3-) by argo
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)"
        using match_hyps(3-) by argo
    next
      show "i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>"
        using match_hyps(3-) by argo
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution_bot E L D U\<^sub>e\<^sub>r' \<Gamma>')
   
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r', \<F>, (\<lambda>_. None) :: 'f gterm \<Rightarrow> 'f gclause option, Some ({#} :: 'f gclause))"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<lambda>_. None, Some {#})"
    proof (rule ord_res_6.resolution_bot)
      show "\<not> dom \<M> \<TTurnstile> E"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> E\<close>] .
    next
      show "ord_res.is_maximal_lit L E"
        using step_hyps by argo
    next
      show "is_neg L"
        using step_hyps by argo
    next
      show "\<M> (atm_of L) = Some D"
        by (metis literal.collapse(2) match_hyps(5) step_hyps(5) step_hyps(6) uminus_Neg)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
        using step_hyps by argo
    next
      show "eres D E = {#}"
        using step_hyps by argo
    next
      show "((\<lambda>_. None)) = (\<lambda>_. None)" ..
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some E\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<lambda>_. None, Some {#})"
        using invars_6 unfolding \<open>\<C> = Some E\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})\<close> .
    next
      show "\<forall>A C. (None = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        unfolding \<open>\<Gamma>' = []\<close> by simp
    next
      show "\<forall>A. (None = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        unfolding \<open>\<Gamma>' = []\<close> by simp
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution_pos E L D U\<^sub>e\<^sub>r' \<Gamma>' K)

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some (eres D E))"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"

    have mem_set_\<Gamma>'_iff: "\<And>x. (x \<in> set \<Gamma>') = (atm_of (fst x) \<prec>\<^sub>t atm_of K \<and> x \<in> set \<Gamma>)"
      unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
      unfolding mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
      by auto

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some (eres D E))"
    proof (rule ord_res_6.resolution_pos)
      show "\<not> dom \<M> \<TTurnstile> E"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> E\<close>] .
    next
      show "ord_res.is_maximal_lit L E"
        using step_hyps by argo
    next
      show "is_neg L"
        using step_hyps by argo
    next
      show "\<M> (atm_of L) = Some D"
        by (metis literal.collapse(2) match_hyps(5) step_hyps(5) step_hyps(6) uminus_Neg)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
        using step_hyps by argo
    next
      show "eres D E \<noteq> {#}"
        using step_hyps by argo
    next
      show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}"
        ..
    next
      show "ord_res.is_maximal_lit K (eres D E)"
        using step_hyps by argo
    next
      show "is_pos K"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some E\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some (eres D E))"
        using invars_6 unfolding \<open>\<C> = Some E\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))\<close> .
    next
      show "\<forall>A C. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C) =
        (map_of \<Gamma>' (Pos A) = Some (Some C))"
      proof (intro allI)
        fix A :: "'f gterm" and C :: "'f gclause"
        show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
        proof (cases "A \<in> dom \<M> \<and> A \<prec>\<^sub>t atm_of K")
          case True
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> \<M> A = Some C"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)"
            using match_hyps(3-) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
          proof -
            have "Pos A \<in> fst ` set \<Gamma>"
              using True 
              by (metis domIff map_of_eq_None_iff match_hyps(5) not_None_eq)

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma>"
              by fastforce

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma> \<and> (Pos A, \<C>) \<in> set \<Gamma>'"
              using True unfolding mem_set_\<Gamma>'_iff prod.sel literal.sel by metis

            moreover have "distinct (map fst \<Gamma>')"
              using \<Gamma>_distinct_atoms
            proof (rule distinct_suffix)
              show "suffix (map fst \<Gamma>') (map fst \<Gamma>)"
                using map_mono_suffix step_hyps(9) suffix_dropWhile by blast
            qed

            ultimately have "map_of \<Gamma> (Pos A) = map_of \<Gamma>' (Pos A)"
              using \<Gamma>_distinct_atoms by (auto dest: map_of_is_SomeI)

            thus ?thesis
              by argo
          qed

          finally show ?thesis .
        next
          case False
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False unfolding restrict_map_def by auto

          moreover have "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
            using False unfolding de_Morgan_conj
          proof (elim disjE)
            assume "A \<notin> dom \<M>"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>"
              using match_hyps(5)
              by (metis (no_types, opaque_lifting) domIff fst_eqD invars_7 is_pos_def map_of_SomeD
                  not_None_eq snd_conv weak_map_of_SomeI)

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          next
            assume "\<not> A \<prec>\<^sub>t atm_of K"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          qed

          ultimately show ?thesis
            by simp
        qed
      qed
    next
      show "\<forall>A. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
        (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
      proof (intro allI)
        fix A :: "'f gterm"
        show "(restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
          (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        proof (cases "A \<prec>\<^sub>t atm_of K")
          case True

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None \<longleftrightarrow> \<M> A = None"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using match_hyps(6) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using True mem_set_\<Gamma>'_iff
            by (metis eq_fst_iff literal.sel(2) map_of_SomeD not_None_eq weak_map_of_SomeI)

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>'"
            using True mem_set_\<Gamma>'_iff
            by (smt (verit, best) fset_trail_atms image_iff)

          finally show ?thesis .
        next
          case False

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False by simp

          moreover have "A |\<notin>| trail_atms \<Gamma>'"
            using False mem_set_\<Gamma>'_iff
            by (smt (verit, ccfv_threshold) fset_trail_atms image_iff)

          ultimately show ?thesis
            by metis
        qed
      qed
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution_neg E L D U\<^sub>e\<^sub>r' \<Gamma>' K C)
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some C)"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"

    have mem_set_\<Gamma>'_iff: "\<And>x. (x \<in> set \<Gamma>') = (atm_of (fst x) \<prec>\<^sub>t atm_of K \<and> x \<in> set \<Gamma>)"
      unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
      unfolding mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
      by auto

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some C)"
    proof (rule ord_res_6.resolution_neg)
      show "\<not> dom \<M> \<TTurnstile> E"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> E\<close>] .
    next
      show "ord_res.is_maximal_lit L E"
        using step_hyps by argo
    next
      show "is_neg L"
        using step_hyps by argo
    next
      show "\<M> (atm_of L) = Some D"
        by (metis literal.collapse(2) match_hyps(5) step_hyps(5) step_hyps(6) uminus_Neg)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
        using step_hyps by argo
    next
      show "eres D E \<noteq> {#}"
        using step_hyps by argo
    next
      show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}"
        ..
    next
      show "ord_res.is_maximal_lit K (eres D E)"
        using step_hyps by argo
    next
      show "is_neg K"
        using step_hyps by argo
    next
      show "\<M> (atm_of K) = Some C"
        using match_hyps(3-)
        by (metis (mono_tags, lifting) step_hyps(11) step_hyps(12) uminus_literal_def)
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some E\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some C)"
        using invars_6 unfolding \<open>\<C> = Some E\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)\<close> .
    next
      show "\<forall>A C. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C) =
        (map_of \<Gamma>' (Pos A) = Some (Some C))"
      proof (intro allI)
        fix A :: "'f gterm" and C :: "'f gclause"
        show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
        proof (cases "A \<in> dom \<M> \<and> A \<prec>\<^sub>t atm_of K")
          case True
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> \<M> A = Some C"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)"
            using match_hyps(3-) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
          proof -
            have "Pos A \<in> fst ` set \<Gamma>"
              using True 
              by (metis domIff map_of_eq_None_iff match_hyps(5) not_None_eq)

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma>"
              by fastforce

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma> \<and> (Pos A, \<C>) \<in> set \<Gamma>'"
              using True unfolding mem_set_\<Gamma>'_iff prod.sel literal.sel by metis

            moreover have "distinct (map fst \<Gamma>')"
              using \<Gamma>_distinct_atoms
            proof (rule distinct_suffix)
              show "suffix (map fst \<Gamma>') (map fst \<Gamma>)"
                using map_mono_suffix step_hyps(9) suffix_dropWhile by blast
            qed

            ultimately have "map_of \<Gamma> (Pos A) = map_of \<Gamma>' (Pos A)"
              using \<Gamma>_distinct_atoms by (auto dest: map_of_is_SomeI)

            thus ?thesis
              by argo
          qed

          finally show ?thesis .
        next
          case False
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False unfolding restrict_map_def by auto

          moreover have "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
            using False unfolding de_Morgan_conj
          proof (elim disjE)
            assume "A \<notin> dom \<M>"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>"
              using match_hyps(5)
              by (metis (no_types, opaque_lifting) domIff fst_eqD invars_7 is_pos_def map_of_SomeD
                  not_None_eq snd_conv weak_map_of_SomeI)

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          next
            assume "\<not> A \<prec>\<^sub>t atm_of K"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          qed

          ultimately show ?thesis
            by simp
        qed
      qed
    next
      show "\<forall>A. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
        (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
      proof (intro allI)
        fix A :: "'f gterm"
        show "(restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
          (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        proof (cases "A \<prec>\<^sub>t atm_of K")
          case True

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None \<longleftrightarrow> \<M> A = None"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using match_hyps(6) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using True mem_set_\<Gamma>'_iff
            by (metis eq_fst_iff literal.sel(2) map_of_SomeD not_None_eq weak_map_of_SomeI)

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>'"
            using True mem_set_\<Gamma>'_iff
            by (smt (verit, best) fset_trail_atms image_iff)

          finally show ?thesis .
        next
          case False

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False by simp

          moreover have "A |\<notin>| trail_atms \<Gamma>'"
            using False mem_set_\<Gamma>'_iff
            by (smt (verit, ccfv_threshold) fset_trail_atms image_iff)

          ultimately show ?thesis
            by metis
        qed
      qed
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  qed
qed

theorem bisimulation_ord_res_6_ord_res_7:
  defines "match \<equiv> ord_res_6_matches_ord_res_7"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_6_state \<Rightarrow> 'f ord_res_7_state \<Rightarrow> bool) \<R>.
    bisimulation ord_res_6_step (constant_context ord_res_7) ord_res_6_final ord_res_7_final
      \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_6_state \<Rightarrow> 'f ord_res_7_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation ord_res_6_step ord_res_6_final (constant_context ord_res_7) ord_res_7_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_6_step"
    using right_unique_ord_res_6_step .
next
  show "right_unique (constant_context ord_res_7)"
    using right_unique_constant_context right_unique_ord_res_7 by metis
next
  show "\<forall>S. ord_res_6_final S \<longrightarrow> (\<nexists>S'. ord_res_6_step S S')"
    by (metis finished_def ord_res_6_semantics.final_finished)
next
  show "\<forall>S. ord_res_7_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_7 S S')"
    by (metis finished_def ord_res_7_semantics.final_finished)
next
  show "\<forall>i S6 S7. match i S6 S7 \<longrightarrow> ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
    unfolding match_def
    using ord_res_6_final_iff_ord_res_7_final by metis
next
  show "\<forall>i S6 S7. match i S6 S7 \<longrightarrow>
       safe_state ord_res_6_step ord_res_6_final S6 \<and>
       safe_state (constant_context ord_res_7) ord_res_7_final S7"
  proof (intro allI impI conjI)
    fix i S6 S7
    assume "match i S6 S7"
    show "safe_state ord_res_6_step ord_res_6_final S6"
      using \<open>match i S6 S7\<close>[unfolded match_def]
      using ord_res_6_safe_state_if_invars
      using ord_res_6_matches_ord_res_7.simps by auto

    show "safe_state (constant_context ord_res_7) ord_res_7_final S7"
      using \<open>match i S6 S7\<close>[unfolded match_def]
      using ord_res_7_safe_state_if_invars
      using ord_res_6_matches_ord_res_7.simps by auto
  qed
next
  show "wfp (|\<subset>|)"
    using wfP_pfsubset .
next
  show "\<forall>i S6 S7 S7'. match i S6 S7 \<longrightarrow> constant_context ord_res_7 S7 S7' \<longrightarrow>
    (\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> match i' S6' S7') \<or>
    (\<exists>i'. match i' S6 S7' \<and> i' |\<subset>| i)"
    unfolding match_def
    using backward_simulation_between_6_and_7 by metis
qed

end


section \<open>ORD-RES-8 (atom-guided literal trail construction)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_8_can_decide_neg where
  "\<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>|} A \<Longrightarrow>
    ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

inductive ord_res_8_can_skip_undefined_neg where
  "\<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not>(\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

inductive ord_res_8_can_skip_undefined_pos_ultimate where
  "\<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not>(\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    \<not>(\<exists>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D) \<Longrightarrow>
    ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

inductive ord_res_8_can_produce where
  "\<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

inductive ord_res_8_can_factorize where
  "\<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    \<not> linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

definition is_least_nonskipped_clause where
  "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      trail_false_cls \<Gamma> C \<or>
      ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
      ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
      ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
      ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
      ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C|} C"

lemma is_least_nonskipped_clause_mempty:
  assumes bot_in: "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
  shows "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> {#}"
  unfolding is_least_nonskipped_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using bot_in .
next
  show "trail_false_cls \<Gamma> {#} \<or>
    ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> {#} \<or>
    ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> {#} \<or>
    ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> {#} \<or>
    ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> {#} \<or> ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> {#}"
    by simp
next
  fix C :: "'f gclause"
  assume "C \<noteq> {#}"
  thus "{#} \<prec>\<^sub>c C"
    using mempty_lesseq_cls by blast
qed

lemma nex_is_least_nonskipped_clause_if:
  assumes
    no_undef_atom: "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>)" and
    no_false_clause: "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)"
  shows "\<nexists>C. is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
  unfolding not_ex
proof (intro allI notI)
  fix C :: "'f gclause"
  assume "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

  hence C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
     ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
     ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
     ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
     ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
    unfolding atomize_conj
    unfolding is_least_nonskipped_clause_def
    unfolding linorder_cls.is_least_in_ffilter_iff
    using no_false_clause by metis

  hence "\<exists>L. linorder_lit.is_maximal_in_mset C L \<and> \<not> trail_defined_lit \<Gamma> L"
  proof (elim disjE)
    assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
    then show ?thesis
      by (metis (mono_tags, lifting) assms(1) linorder_trm.is_least_in_ffilter_iff
          ord_res_8_can_decide_neg.cases)
  qed (auto elim:
      ord_res_8_can_skip_undefined_neg.cases
      ord_res_8_can_skip_undefined_pos_ultimate.cases
      ord_res_8_can_produce.cases
      ord_res_8_can_factorize.cases)

  hence "\<exists>L. atm_of L |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) \<and> atm_of L |\<notin>| trail_atms \<Gamma>"
    using C_in
    unfolding linorder_lit.is_maximal_in_mset_iff trail_defined_lit_iff_trail_defined_atm
    by (metis atm_of_in_atms_of_clssI)

  thus False
    using no_undef_atom by metis
qed

lemma MAGIC5:
  assumes invars: "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" and
    no_more_steps: "\<nexists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')"
  shows "(\<forall>C. \<C> = Some C \<longleftrightarrow> is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C)"
proof (cases \<C>)
  case None

  have "trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using None invars[unfolded ord_res_7_invars_def] by simp

  have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_true_cls \<Gamma> C"
    using None invars[unfolded ord_res_7_invars_def] by simp

  hence no_false: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<not> trail_false_cls \<Gamma> C"
    using invars[unfolded ord_res_7_invars_def]
    by (meson invars not_trail_true_cls_and_trail_false_cls
        ord_res_7_invars_implies_trail_consistent)

  have "\<nexists>C. is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
  proof (rule notI, elim exE)
    fix C
    assume "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"

    hence
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_spec_disj: "
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      unfolding atomize_conj
      unfolding is_least_nonskipped_clause_def
      unfolding linorder_cls.is_least_in_ffilter_iff
      using no_false by metis

    thus False
    proof (elim disjE)
      assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      thus ?thesis
        using \<open>trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using ord_res_8_can_decide_neg.cases
        by (metis (no_types, lifting) linorder_trm.is_least_in_ffilter_iff)
    next
      assume "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      thus ?thesis
        using \<open>trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using ord_res_8_can_skip_undefined_neg.cases
        by (metis C_in atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff
            trail_defined_lit_iff_trail_defined_atm)
    next
      assume "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      thus ?thesis
        using \<open>trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using ord_res_8_can_skip_undefined_pos_ultimate.cases
        by (metis C_in atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff
            trail_defined_lit_iff_trail_defined_atm)
    next
      assume "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      thus False
        using \<open>trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using ord_res_8_can_produce.cases
        by (metis C_in atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff
            trail_defined_lit_iff_trail_defined_atm)
    next
      assume "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      thus False
        using \<open>trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using ord_res_8_can_factorize.cases
        by (metis C_in atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff
            trail_defined_lit_iff_trail_defined_atm)
    qed
  qed

  thus ?thesis
    using None by simp
next
  case (Some D)

  have D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using Some invars[unfolded ord_res_7_invars_def] by simp

  have "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
  proof (cases "D = {#}")
    case True
    thus ?thesis
      using D_in is_least_nonskipped_clause_mempty by metis
  next
    case False

    then obtain L\<^sub>D where D_max_lit: "linorder_lit.is_maximal_in_mset D L\<^sub>D"
      using linorder_lit.ex_maximal_in_mset by presburger

    show ?thesis
      unfolding is_least_nonskipped_clause_def
      unfolding linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using D_in .
    next
      show "trail_false_cls \<Gamma> D \<or>
      ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
      ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
      ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
      ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or> ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      proof (cases "trail_false_cls \<Gamma> D")
        case True
        then show ?thesis
          by metis
      next
        case D_not_false: False

        then obtain L where D_max_lit: "linorder_lit.is_maximal_in_mset D L"
          by (metis linorder_lit.ex_maximal_in_mset trail_false_cls_mempty)

        show ?thesis
        proof (cases "\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>")
          case True

          hence "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
            using ord_res_8_can_decide_neg.intros[OF D_not_false D_max_lit]
            by (metis (no_types, lifting) equalsffemptyD ffmember_filter linorder_trm.ex_least_in_fset)

          thus ?thesis
            by argo
        next
          case no_undef_atm: False
          show ?thesis
          proof (cases "trail_defined_lit \<Gamma> L")
            case L_defined: True

            hence "\<exists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')"
              unfolding \<open>\<C> = Some D\<close>
              using ord_res_7.skip_defined[OF D_not_false D_max_lit no_undef_atm]
              by metis

            hence False
              using no_more_steps by contradiction

            thus ?thesis ..
          next
            case L_undef: False
            show ?thesis
            proof (cases L)
              case (Pos A)

              hence L_pos: "is_pos L"
                by simp

              show ?thesis
              proof (cases "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}")
                case D_almost_false: True
                thus ?thesis
                  using ord_res_8_can_factorize.intros[
                      OF D_not_false D_max_lit no_undef_atm L_undef L_pos]
                  using ord_res_8_can_produce.intros[
                      OF D_not_false D_max_lit no_undef_atm L_undef L_pos]
                  by metis
              next
                case D_not_flagrantly_false: False
                show ?thesis
                proof (cases "\<exists>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c E")
                  case True

                  hence "\<exists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')"
                    unfolding \<open>\<C> = Some D\<close>
                    using ord_res_7.skip_undefined_pos[
                        OF D_not_false D_max_lit no_undef_atm L_undef L_pos D_not_flagrantly_false]
                    by (metis femptyE ffmember_filter linorder_cls.ex_least_in_fset)

                  hence False
                    using no_more_steps by contradiction

                  thus ?thesis ..
                next
                  case False

                  hence "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
                    using ord_res_8_can_skip_undefined_pos_ultimate.intros[
                        OF D_not_false D_max_lit no_undef_atm L_undef L_pos D_not_flagrantly_false]
                    by metis

                  thus ?thesis
                    by argo
                qed
              qed
            next
              case (Neg A)
              hence L_neg: "is_neg L"
                by simp

              hence "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
                unfolding \<open>\<C> = Some D\<close>
                using ord_res_8_can_skip_undefined_neg.intros[
                    OF D_not_false D_max_lit no_undef_atm L_undef]
                by metis

              thus ?thesis
                by argo
            qed
          qed
        qed
      qed

      fix E :: "'f gterm literal multiset"
      assume
        E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        E_neq: "E \<noteq> D" and
        E_spec: "trail_false_cls \<Gamma> E \<or>
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> E"

      have true_cls_if_lt_D:
        "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C"
        using invars[unfolded ord_res_7_invars_def] Some by simp

      have \<Gamma>_lower_set: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
        using invars[unfolded ord_res_7_invars_def] by simp

      have FOO:
        "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
          (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))"
        using invars[unfolded ord_res_7_invars_def] Some E_in by simp

      hence BAR:
        "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
          (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
            \<not> trail_defined_lit \<Gamma> K \<longrightarrow> (trail_true_cls \<Gamma> {#x \<in># C. x \<noteq> K#} \<and> is_pos K))"
        using invars[unfolded ord_res_7_invars_def] Some by simp

      show "D \<prec>\<^sub>c E"
        using E_spec
      proof (elim disjE)
        assume "trail_false_cls \<Gamma> E"
        hence "\<not> trail_true_cls \<Gamma> E"
          using invars not_trail_true_cls_and_trail_false_cls
            ord_res_7_invars_implies_trail_consistent by blast
        thus "D \<prec>\<^sub>c E"
          using E_in E_neq true_cls_if_lt_D by force
      next
        assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
        thus "D \<prec>\<^sub>c E"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> E rule: ord_res_8_can_decide_neg.cases)
          case (1 L\<^sub>E A)
          hence "\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L\<^sub>E \<and> A |\<notin>| trail_atms \<Gamma>"
            unfolding linorder_trm.is_least_in_ffilter_iff by metis
          thus ?thesis
            using FOO[rule_format, OF E_in _ \<open>ord_res.is_maximal_lit L\<^sub>E E\<close>] E_in E_neq
            by force
        qed
      next
        assume "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
        thus "D \<prec>\<^sub>c E"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> E rule: ord_res_8_can_skip_undefined_neg.cases)
          case hyps: (1 L\<^sub>E)
          thus ?thesis
            using BAR[rule_format, OF E_in _ \<open>ord_res.is_maximal_lit L\<^sub>E E\<close>]
            using invars[unfolded ord_res_7_invars_def Some, rule_format, OF refl] Some E_in
            using E_neq by fastforce
        qed
      next
        assume "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
        thus "D \<prec>\<^sub>c E"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> E rule: ord_res_8_can_skip_undefined_pos_ultimate.cases)
          case (1 L)
          then show ?thesis using E_neq D_in by force
        qed
      next
        assume "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
        hence "\<not> trail_true_cls \<Gamma> E"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> E rule: ord_res_8_can_produce.cases)
          case (1 L)
          then show ?thesis
            using invars[THEN ord_res_7_invars_implies_trail_consistent]
            by (smt (verit, ccfv_SIG) mem_Collect_eq not_trail_true_cls_and_trail_false_cls
                set_mset_filter trail_defined_lit_iff_true_or_false trail_true_cls_def)
        qed
        thus "D \<prec>\<^sub>c E"
          using E_in E_neq true_cls_if_lt_D by force
      next
        assume "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
        hence "\<not> trail_true_cls \<Gamma> E"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> E rule: ord_res_8_can_factorize.cases)
          case (1 L)
          then show ?thesis
            using invars[THEN ord_res_7_invars_implies_trail_consistent]
            by (smt (verit, ccfv_SIG) mem_Collect_eq not_trail_true_cls_and_trail_false_cls
                set_mset_filter trail_defined_lit_iff_true_or_false trail_true_cls_def)
        qed
        thus "D \<prec>\<^sub>c E"
          using E_in E_neq true_cls_if_lt_D by force
      qed
    qed
  qed

  moreover have "Uniq (is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>)"
    unfolding is_least_nonskipped_clause_def
    using linorder_cls.Uniq_is_least_in_fset
    by simp

  ultimately show ?thesis
    using Some
    by (metis (no_types) The_optional_eq_SomeD The_optional_eq_SomeI)
qed

lemma MAGIC6:
  assumes invars: "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"
  shows "\<exists>\<C>'. (ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>') \<and>
    (\<nexists>\<C>''. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>') (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>''))"
proof -
  define R where
    "R = (\<lambda>\<C> \<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>'))"

  define f :: "'f gclause option \<Rightarrow> 'f gclause fset" where
    "f = (\<lambda>\<C>. case \<C> of None \<Rightarrow> {||} | Some C \<Rightarrow> {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|})"

  let ?less_f = "(|\<subset>|)"

  have "Wellfounded.wfp_on {x'. R\<^sup>*\<^sup>* \<C> x'} R\<inverse>\<inverse>"
  proof (rule wfp_on_if_convertible_to_wfp_on)
    have "wfp (|\<subset>|)"
      by auto
    thus "Wellfounded.wfp_on (f ` {x'. R\<^sup>*\<^sup>* \<C> x'}) ?less_f"
      using Wellfounded.wfp_on_subset subset_UNIV by metis
  next
    fix \<C>\<^sub>x \<C>\<^sub>y :: "'f gclause option"

    have rtranclp_with_constsD: "(\<lambda>y y'. R (x, y) (x, y'))\<^sup>*\<^sup>* y y' \<Longrightarrow>
      R\<^sup>*\<^sup>* (x, y) (x, y')" for R x y y'
    proof (induction y arbitrary: rule: converse_rtranclp_induct)
      case base
      show ?case
        by simp
    next
      case (step w)
      thus ?case
        by force
    qed 

    assume "\<C>\<^sub>x \<in> {x'. R\<^sup>*\<^sup>* \<C> x'}" and  "\<C>\<^sub>y \<in> {x'. R\<^sup>*\<^sup>* \<C> x'}"
    hence
      "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>x)" and
      "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>y)"
      unfolding atomize_conj mem_Collect_eq R_def
      by (auto intro: rtranclp_with_constsD)
    hence
      x_invars: "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>x)" and
      y_invars: "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>y)"
      using ord_res_7_preserves_invars
      using invars by (metis rtranclp_ord_res_7_preserves_ord_res_7_invars)+

    have \<Gamma>_consistent: "trail_consistent \<Gamma>"
      using x_invars by (metis ord_res_7_invars_implies_trail_consistent)

    have less_f_if: "?less_f (f \<C>\<^sub>y) (f \<C>\<^sub>x)"
      if "\<C>\<^sub>x = Some C" and
        \<C>\<^sub>y_disj: "\<C>\<^sub>y = None \<or> \<C>\<^sub>y = Some D \<and> C \<prec>\<^sub>c D" and
        C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      for C D
    proof -
      have f_x: "f \<C>\<^sub>x = {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|}"
        by (auto simp add: \<open>\<C>\<^sub>x = Some C\<close> f_def)

      moreover have "C |\<in>| f \<C>\<^sub>x"
        using C_in f_x by simp

      moreover have "C |\<notin>| f \<C>\<^sub>y \<and> f \<C>\<^sub>y |\<subseteq>| f \<C>\<^sub>x"
        using \<C>\<^sub>y_disj
      proof (elim disjE conjE; intro conjI)
        assume "\<C>\<^sub>y = None"
        thus "C |\<notin>| f \<C>\<^sub>y" and "f \<C>\<^sub>y |\<subseteq>| f \<C>\<^sub>x"
          unfolding f_x
          by (simp_all add: f_def)
      next
        assume "\<C>\<^sub>y = Some D" and "C \<prec>\<^sub>c D"

        have "\<And>x. D \<preceq>\<^sub>c x \<Longrightarrow> C \<preceq>\<^sub>c x"
          using \<open>C \<prec>\<^sub>c D\<close> by auto

        moreover have fst_f_y: "f \<C>\<^sub>y = {|E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<preceq>\<^sub>c E|}"
          by (auto simp add: \<open>\<C>\<^sub>y = Some D\<close> f_def)

        ultimately show "f \<C>\<^sub>y |\<subseteq>| f \<C>\<^sub>x"
          using f_x by auto

        show "C |\<notin>| f \<C>\<^sub>y"
          using \<open>C \<prec>\<^sub>c D\<close> fst_f_y by auto
      qed

      ultimately have "f \<C>\<^sub>y |\<subset>| f \<C>\<^sub>x"
        by blast

      thus ?thesis
        by (simp add: lex_prodp_def)
    qed

    have eres_not_in_if: "eres D E |\<notin>| U\<^sub>e\<^sub>r"
      if "\<C>\<^sub>x = Some E" and E_false: "trail_false_cls \<Gamma> E" and
        E_max_lit: "ord_res.is_maximal_lit L E" and L_neg: "is_neg L"
        "map_of \<Gamma> (- L) = Some (Some D)"
      for D E L
    proof -
      have
        clauses_lt_E_true:
        "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
        \<Gamma>_prop_greatest:
        "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
        using x_invars unfolding \<open>\<C>\<^sub>x = Some E\<close> ord_res_7_invars_def by simp_all

      have "(- L, Some D) \<in> set \<Gamma>"
        using \<open>map_of \<Gamma> (- L) = Some (Some D)\<close> by (metis map_of_SomeD)

      hence D_greatest_lit: "linorder_lit.is_greatest_in_mset D (- L)"
        using \<Gamma>_prop_greatest by fastforce

      have "eres D E \<prec>\<^sub>c E"
        using eres_lt_if
        using E_max_lit L_neg D_greatest_lit
        by metis

      hence "eres D E \<noteq> E"
        by order

      have "L \<in># E"
        using E_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by metis

      hence "- L \<notin># E"
        using not_both_lit_and_comp_lit_in_false_clause_if_trail_consistent
        using \<Gamma>_consistent E_false by metis

      hence "\<forall>K \<in># eres D E. atm_of K \<prec>\<^sub>t atm_of L"
        using lit_in_eres_lt_greatest_lit_in_grestest_resolvant[OF \<open>eres D E \<noteq> E\<close> E_max_lit]
        by metis

      hence "\<forall>K \<in># eres D E. K \<noteq> L \<and> K \<noteq> - L"
        by fastforce

      moreover have "\<forall>L \<in># eres D E. L \<in># D \<or> L \<in># E"
        using lit_in_one_of_resolvents_if_in_eres by metis

      moreover have D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> - L#}"
        using ord_res_7_invars_implies_propagated_clause_almost_false
        using \<open>(- L, Some D) \<in> set \<Gamma>\<close> x_invars
        by metis

      ultimately have "trail_false_cls \<Gamma> (eres D E)"
        using E_false unfolding trail_false_cls_def by fastforce

      have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
        using eres_not_in_known_clauses_if_trail_false_cls
        using \<Gamma>_consistent clauses_lt_E_true \<open>eres D E \<prec>\<^sub>c E\<close> \<open>trail_false_cls \<Gamma> (eres D E)\<close>
        by metis

      thus "eres D E |\<notin>| U\<^sub>e\<^sub>r"
        by blast
    qed

    assume "R\<inverse>\<inverse> \<C>\<^sub>y \<C>\<^sub>x"
    hence "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>x) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>y)"
      unfolding conversep_iff R_def .
    thus "?less_f (f \<C>\<^sub>y) (f \<C>\<^sub>x)"
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>x)" "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>\<^sub>y)" rule: ord_res_7.cases)
      case step_hyps: (decide_neg C L A)
      hence False by simp
      thus ?thesis ..
    next
      case step_hyps: (skip_defined C L)

      have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using ord_res_7_invars_def step_hyps(1) x_invars by presburger

      moreover have "\<exists>D. \<C>\<^sub>y = None \<or> \<C>\<^sub>y = Some D \<and> C \<prec>\<^sub>c D"
      proof (cases \<C>\<^sub>y)
        case None
        thus ?thesis
          by simp
      next
        case (Some D)
        thus ?thesis
          using step_hyps
          by (metis linorder_cls.is_least_in_ffilter_iff Some_eq_The_optionalD)
      qed

      ultimately show ?thesis
        using less_f_if step_hyps by metis
    next
      case step_hyps: (skip_undefined_neg C L)
      hence False by simp
      thus ?thesis ..
    next
      case step_hyps: (skip_undefined_pos C L D)

      have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using ord_res_7_invars_def step_hyps(1) x_invars by presburger

      moreover have "\<exists>D. \<C>\<^sub>y = None \<or> \<C>\<^sub>y = Some D \<and> C \<prec>\<^sub>c D"
        using step_hyps by (metis linorder_cls.is_least_in_ffilter_iff)

      ultimately show ?thesis
        using less_f_if step_hyps by metis
    next
      case step_hyps: (skip_undefined_pos_ultimate C L)
      hence False by simp
      thus ?thesis ..
    next
      case step_hyps: (production C L)
      hence False by simp
      thus ?thesis ..
    next
      case step_hyps: (factoring C L)

      have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using ord_res_7_invars_def step_hyps(1) x_invars by presburger

      moreover have "efac C \<noteq> C"
        using step_hyps by (metis greatest_literal_in_efacI)
      
      ultimately have "C |\<notin>| \<F>"
        by (smt (verit, ccfv_threshold) fimage_iff iefac_def ex1_efac_eq_factoring_chain
            factorizable_if_neq_efac)

      hence False
        using \<open>\<F> = finsert C \<F>\<close> by blast

      thus ?thesis ..
    next
      case step_hyps: (resolution_bot E L D)
      hence "eres D E |\<notin>| U\<^sub>e\<^sub>r"
        using eres_not_in_if by metis
      hence False
        using \<open>U\<^sub>e\<^sub>r = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by blast
      thus ?thesis ..
    next
      case (resolution_pos E L D K)
      hence "eres D E |\<notin>| U\<^sub>e\<^sub>r"
        using eres_not_in_if by metis
      hence False
        using \<open>U\<^sub>e\<^sub>r = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by blast
      thus ?thesis ..
    next
      case (resolution_neg E L D K C)
      hence "eres D E |\<notin>| U\<^sub>e\<^sub>r"
        using eres_not_in_if by metis
      hence False
        using \<open>U\<^sub>e\<^sub>r = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by blast
      thus ?thesis ..
    qed
  qed

  then obtain \<C>' where "R\<^sup>*\<^sup>* \<C> \<C>'" and "\<nexists>z. R \<C>' z"
    using ex_terminating_rtranclp_strong by metis

  show ?thesis
  proof (intro exI conjI)
    show "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')"
      using \<open>R\<^sup>*\<^sup>* \<C> \<C>'\<close>
      by (induction \<C> rule: converse_rtranclp_induct) (auto simp: R_def)
  next
    show "\<nexists>\<C>''. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>') (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>'')"
      using \<open>\<nexists>z. R \<C>' z\<close>
      by (simp add: R_def)
  qed
qed

inductive ord_res_7_matches_ord_res_8 :: "'f ord_res_7_state \<Rightarrow> 'f ord_res_8_state \<Rightarrow> bool" where
  "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) \<Longrightarrow>
    ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<Longrightarrow>
    (\<forall>C. \<C> = Some C \<longleftrightarrow> is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C) \<Longrightarrow>
    ord_res_7_matches_ord_res_8 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"

lemma ord_res_7_final_iff_ord_res_8_final:
  fixes S7 S8
  assumes match: "ord_res_7_matches_ord_res_8 S7 S8"
  shows "ord_res_7_final S7 \<longleftrightarrow> ord_res_8_final S8"
  using match
proof (cases S7 S8 rule: ord_res_7_matches_ord_res_8.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>)

  note invars7 = \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>[unfolded ord_res_7_invars_def,
      rule_format, OF refl]

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using invars7 by (metis trail_consistent_if_sorted_wrt_atoms)

  show "ord_res_7_final S7 \<longleftrightarrow> ord_res_8_final S8"
  proof (rule iffI)
    assume "ord_res_7_final S7"
    thus "ord_res_8_final S8"
      unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_final.cases)
      case model_found
      show "ord_res_8_final S8"
        unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      proof (rule ord_res_8_final.model_found)
        have "\<C> = None \<longrightarrow> trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars7 by argo

        hence "trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          using model_found by argo

        thus "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>)"
          by metis
      next
        have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_true_cls \<Gamma> C"
          using invars7 model_found by simp

        moreover have "\<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)" for C
          using not_trail_true_cls_and_trail_false_cls[OF \<Gamma>_consistent] .

        ultimately show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)"
          by metis
      qed
    next
      case contradiction_found
      show "ord_res_8_final S8"
        unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      proof (rule ord_res_8_final.contradiction_found)
        show "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars7 \<open>\<C> = Some {#}\<close> by metis
      qed
    qed
  next
    assume "ord_res_8_final S8"
    thus "ord_res_7_final S7"
      unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" rule: ord_res_8_final.cases)
      case model_found

      hence "\<nexists>C. is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
        using nex_is_least_nonskipped_clause_if by metis

      hence "\<C> = None"
        using match_hyps by simp

      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.model_found by metis
    next
      case contradiction_found

      hence "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> {#}"
        using is_least_nonskipped_clause_mempty by metis

      hence "\<C> = Some {#}"
        using match_hyps by presburger

      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.contradiction_found by metis
    qed
  qed
qed

lemma backward_simulation_between_7_and_8:
  fixes i S7 S8 S8'
  assumes match: "ord_res_7_matches_ord_res_8 S7 S8" and step: "constant_context ord_res_8 S8 S8'"
  shows "\<exists>S7'. (constant_context ord_res_7)\<^sup>+\<^sup>+ S7 S7' \<and> ord_res_7_matches_ord_res_8 S7' S8'"
  using match
proof (cases S7 S8 rule: ord_res_7_matches_ord_res_8.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>)

  note S7_def = \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>

  note invars7 = \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>[unfolded ord_res_7_invars_def,
      rule_format, OF refl]

  have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invars7 by argo

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms[OF \<Gamma>_sorted] .

  have \<Gamma>_lower_set: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using invars7 by argo

  have \<C>_eq_None_implies_all_atoms_defined: "\<C> = None \<longrightarrow> trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using invars7 by argo

  obtain s8' where
    S8'_def: "S8' = (N, s8')" and
    step': "ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) s8'"
    using step unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    by (auto elim: constant_context.cases)

  have invars_s8': "ord_res_8_invars N s8'"
    using ord_res_8_preserves_invars[OF step' \<open>ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>] .

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" s8' rule: ord_res_8.cases)
    case step_hyps: (decide_neg A \<Gamma>')

    have
      A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
      A_undef: "A |\<notin>| trail_atms \<Gamma>" and
      A_least: "\<forall>y|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> A \<longrightarrow> (\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t y) \<longrightarrow> A \<prec>\<^sub>t y"
      using step_hyps(3) unfolding linorder_trm.is_least_in_fset_iff by auto

    have "\<C> \<noteq> None"
      using \<C>_eq_None_implies_all_atoms_defined A_in A_undef by metis

    then obtain D :: "'f gclause" where "\<C> = Some D"
      by blast

    hence D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      by (metis \<open>\<C> = Some D\<close> invars7)

    have "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      using match_hyps \<open>\<C> = Some D\<close> by metis

    moreover have D_not_false: "\<not> trail_false_cls \<Gamma> D"
      using D_in step_hyps by metis

    moreover have "\<not> ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
    proof (rule notI)
      assume "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      thus False
      proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_produce.cases)
        case (1 L')
        thus ?thesis
          by (metis A_in A_least A_undef D_in atm_of_in_atms_of_clssI
              atoms_of_trail_lt_atom_of_propagatable_literal clause_could_propagate_def invars7
              linorder_lit.is_maximal_in_mset_iff literal.collapse(1) step_hyps(4))
      qed
    qed

    moreover have "\<not> ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
    proof (rule notI)
      assume "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      thus False
      proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_factorize.cases)
        case (1 L')
        thus False
          by (metis A_in A_least A_undef D_in atm_of_in_atms_of_clssI
              atoms_of_trail_lt_atom_of_propagatable_literal clause_could_propagate_def invars7
              linorder_lit.is_maximal_in_mset_iff literal.collapse(1) step_hyps(4))
      qed
    qed

    ultimately have "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
      ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
      ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      unfolding is_least_nonskipped_clause_def
      unfolding linorder_cls.is_least_in_ffilter_iff
      by argo

    then obtain \<C>' where first_step7: "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
    proof (elim disjE; atomize_elim)
      assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      thus "\<exists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
      proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_decide_neg.cases)
        case hyps: (1 L A')
        hence "A' = A"
          by (smt (verit, del_insts) \<Gamma>_lower_set linorder_trm.is_least_in_ffilter_iff
              linorder_trm.neq_iff linorder_trm.not_in_lower_setI linorder_trm.order.strict_trans
              step_hyps(3))
        thus ?thesis
          using hyps \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          using ord_res_7.decide_neg[of \<Gamma> D _ N U\<^sub>e\<^sub>r A \<Gamma>' \<F>] by blast
      qed
    next
      assume "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      thus "\<exists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
      proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_skip_undefined_neg.cases)
        case hyps: (1 L)
        hence "L = Neg A"
          by (smt (verit) A_in A_least A_undef D_in \<Gamma>_lower_set atm_of_in_atms_of_clssI
              linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
              linorder_trm.not_in_lower_setI literal.disc(2) literal.expand literal.sel(2)
              trail_defined_lit_iff_trail_defined_atm)
        thus ?thesis
          using hyps \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          using ord_res_7.skip_undefined_neg by blast
      qed
    next
      assume "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      thus "\<exists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
      proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_skip_undefined_pos_ultimate.cases)
        case hyps: (1 L)
        hence "L = Pos A"
          by (smt (verit, best) A_in A_least A_undef D_in atm_of_in_atms_of_clssI invars7
              linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
              linorder_trm.not_in_lower_setI literal.disc(1) literal.expand literal.sel(1)
              trail_defined_lit_iff_trail_defined_atm)
        thus ?thesis
          using hyps \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          using ord_res_7.skip_undefined_pos_ultimate by fastforce
      qed
    qed

    moreover have "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
      using \<open>\<C> = Some D\<close> first_step7 match_hyps(3) ord_res_7_preserves_invars by blast

    ultimately obtain \<C>'' where
      following_steps7: "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')" and
      no_more_step7: "(\<nexists>\<C>'''. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'') (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'''))"
      using MAGIC6 by metis

    show ?thesis
    proof (intro exI conjI)
      have "(ord_res_7 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')"
        unfolding \<open>\<C> = Some D\<close>
        using first_step7 following_steps7 by simp

      thus "(constant_context ord_res_7)\<^sup>+\<^sup>+ S7 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')"
        unfolding S7_def by (simp add: tranclp_constant_context)

      show "ord_res_7_matches_ord_res_8 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'') S8'"
        unfolding S8'_def \<open>s8' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
      proof (intro ord_res_7_matches_ord_res_8.intros allI)
        show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> following_steps7
            rtranclp_ord_res_7_preserves_ord_res_7_invars by blast

        show "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
          using invars_s8' step_hyps(1) by blast

        fix C :: "'f gclause"
        show "\<C>'' = Some C \<longleftrightarrow> is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>' C"
          using MAGIC5 \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')\<close> no_more_step7 by metis
      qed
    qed
  next
    case step_hyps: (propagate A C \<Gamma>')

    have
      A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
      A_undef: "A |\<notin>| trail_atms \<Gamma>" and
      A_least: "\<forall>y|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> A \<longrightarrow> (\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t y) \<longrightarrow> A \<prec>\<^sub>t y"
      using step_hyps(3) unfolding linorder_trm.is_least_in_fset_iff by auto

    have
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_can_prop:"clause_could_propagate \<Gamma> C (Pos A)" and
      C_least: "\<forall>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        D \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> D (Pos A) \<longrightarrow> C \<prec>\<^sub>c D"
      using step_hyps unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

    hence
      Pos_A_undef: "\<not> trail_defined_lit \<Gamma> (Pos A)" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C (Pos A)" and
      C_almost_false: "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
      unfolding atomize_conj clause_could_propagate_def by argo

    have "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      unfolding is_least_nonskipped_clause_def
      unfolding linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using C_in .
    next
      have "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      proof (rule ord_res_8_can_produce.intros)
        show "\<not> trail_false_cls \<Gamma> C"
          using step_hyps C_in by metis
      next
        show "ord_res.is_maximal_lit (Pos A) C"
          using step_hyps by blast
      next
        show "\<not> (\<exists>Aa|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). Aa \<prec>\<^sub>t atm_of (Pos A) \<and> Aa |\<notin>| trail_atms \<Gamma>)"
          unfolding literal.sel
          using step_hyps
          by (smt (verit, ccfv_threshold) \<Gamma>_lower_set linorder_trm.dual_order.asym
              linorder_trm.is_least_in_ffilter_iff linorder_trm.is_lower_set_iff
              linorder_trm.neq_iff)
      next
        show "\<not> trail_defined_lit \<Gamma> (Pos A)"
          using A_undef unfolding trail_defined_lit_iff_trail_defined_atm literal.sel .
      next
        show "is_pos (Pos A)"
          by simp
      next
        show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
          using \<open>clause_could_propagate \<Gamma> C (Pos A)\<close>
          unfolding clause_could_propagate_def by argo
      next
        show "ord_res.is_strictly_maximal_lit (Pos A) C"
          using step_hyps by argo
      qed

      thus "trail_false_cls \<Gamma> C \<or>
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or> ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
        by argo
    next
      fix D :: "'f gclause"
      assume
        D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        D_neq: "D \<noteq> C" and
        D_spec_disj: "trail_false_cls \<Gamma> D \<or>
          ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"

      hence "
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        using step_hyps D_in by metis

      thus "C \<prec>\<^sub>c D"
      proof (elim disjE)
        assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        thus "C \<prec>\<^sub>c D"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_decide_neg.cases)
          case hyps: (1 L A')
          hence "A = A'"
            using step_hyps
            by (smt (verit, del_insts) \<Gamma>_lower_set linorder_trm.antisym_conv3
                linorder_trm.dual_order.strict_implies_not_eq linorder_trm.dual_order.strict_trans
                linorder_trm.is_least_in_ffilter_iff linorder_trm.not_in_lower_setI)
          hence "A \<prec>\<^sub>t atm_of L"
            using hyps
            unfolding linorder_trm.is_least_in_ffilter_iff
            by argo
          hence "Pos A \<prec>\<^sub>l L"
            by (cases L) simp_all
          thus ?thesis
            using C_max_lit \<open>linorder_lit.is_maximal_in_mset D L\<close>
            by (metis linorder_lit.multp_if_maximal_less_that_maximal)
        qed
      next
        assume "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        thus "C \<prec>\<^sub>c D"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_skip_undefined_neg.cases)
          case hyps: (1 L)
          hence "atm_of L = A"
            using step_hyps
            by (smt (verit, best)
                A_in A_least A_undef D_in \<Gamma>_lower_set atm_of_in_atms_of_clssI
                linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
                linorder_trm.not_in_lower_setI trail_defined_lit_iff_trail_defined_atm)
          hence "Pos A \<prec>\<^sub>l L"
            using \<open>is_neg L\<close> by (cases L) simp_all
          thus ?thesis
            using C_max_lit \<open>linorder_lit.is_maximal_in_mset D L\<close>
            by (metis linorder_lit.multp_if_maximal_less_that_maximal)
        qed
      next
        assume "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        thus "C \<prec>\<^sub>c D"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_skip_undefined_pos_ultimate.cases)
          case hyps: (1 L)
          thus ?thesis
            by (meson C_in D_neq linorder_cls.linorder_cases)
        qed
      next
        assume "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D"

        then obtain L where
          D_max_lit: "ord_res.is_maximal_lit L D" and
          "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)" and
          L_undef: "\<not> trail_defined_lit \<Gamma> L" and
          D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}" and
          "is_pos L"
          by (auto elim: ord_res_8_can_factorize.cases ord_res_8_can_produce.cases)

        hence "atm_of L = A"
          using step_hyps
          by (smt (verit, ccfv_SIG) A_in A_least A_undef D_in \<Gamma>_lower_set
              linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
              linorder_trm.not_in_lower_setI atm_of_in_atms_of_clssI
              trail_defined_lit_iff_trail_defined_atm)

        hence "L = Pos A"
          using \<open>is_pos L\<close> by (cases L) simp_all

        hence "clause_could_propagate \<Gamma> D (Pos A)"
          unfolding clause_could_propagate_def
          using D_almost_false D_max_lit L_undef by metis

        thus "C \<prec>\<^sub>c D"
          using D_in D_neq C_least by metis
      next
        assume "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"

        then obtain L where
          D_max_lit: "ord_res.is_maximal_lit L D" and
          "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)" and
          L_undef: "\<not> trail_defined_lit \<Gamma> L" and
          D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}" and
          "is_pos L"
          by (auto elim: ord_res_8_can_factorize.cases ord_res_8_can_produce.cases)

        hence "atm_of L = A"
          using step_hyps
          by (smt (verit, ccfv_SIG) A_in A_least A_undef D_in \<Gamma>_lower_set
              linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
              linorder_trm.not_in_lower_setI atm_of_in_atms_of_clssI
              trail_defined_lit_iff_trail_defined_atm)

        hence "L = Pos A"
          using \<open>is_pos L\<close> by (cases L) simp_all

        hence "clause_could_propagate \<Gamma> D (Pos A)"
          unfolding clause_could_propagate_def
          using D_almost_false D_max_lit L_undef by metis

        thus "C \<prec>\<^sub>c D"
          using D_in D_neq C_least by metis
      qed
    qed

    hence "\<C> = Some C"
      using match_hyps by metis

    define \<C>' where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"

    have first_step7: "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
    proof (rule ord_res_7.production)
      show "\<not> trail_false_cls \<Gamma> C"
        using C_in step_hyps(2) by blast
    next
      show "ord_res.is_maximal_lit (Pos A) C"
        using C_max_lit by force
    next
      show "\<not> (\<exists>Aa|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). Aa \<prec>\<^sub>t atm_of (Pos A) \<and> Aa |\<notin>| trail_atms \<Gamma>)"
        by (metis A_least \<Gamma>_lower_set linorder_trm.dual_order.asym linorder_trm.neq_iff
            linorder_trm.not_in_lower_setI literal.sel(1))
    next
      show "\<not> trail_defined_lit \<Gamma> (Pos A)"
        using Pos_A_undef .
    next
      show "is_pos (Pos A)"
        by simp
    next
      show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
        using C_almost_false .
    next
      show "ord_res.is_strictly_maximal_lit (Pos A) C"
        using step_hyps by argo
    next
      show "\<Gamma>' = (Pos A, Some C) # \<Gamma>"
        using step_hyps by argo
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using \<C>'_def .
    qed

    moreover have "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
      using \<open>\<C> = Some C\<close> first_step7 match_hyps(3) ord_res_7_preserves_invars by blast

    ultimately obtain \<C>'' where
      following_steps7: "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')" and
      no_more_step7: "(\<nexists>\<C>'''. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'') (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'''))"
      using MAGIC6 by metis

    show ?thesis
    proof (intro exI conjI)
      have "(ord_res_7 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')"
        unfolding \<open>\<C> = Some C\<close>
        using first_step7 following_steps7 by simp

      thus "(constant_context ord_res_7)\<^sup>+\<^sup>+ S7 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')"
        unfolding S7_def by (simp add: tranclp_constant_context)

      show "ord_res_7_matches_ord_res_8 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'') S8'"
        unfolding S8'_def \<open>s8' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
      proof (intro ord_res_7_matches_ord_res_8.intros allI)
        show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> following_steps7
            rtranclp_ord_res_7_preserves_ord_res_7_invars by blast

        show "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
          using invars_s8' step_hyps(1) by blast

        fix C :: "'f gclause"
        show "\<C>'' = Some C \<longleftrightarrow> is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>' C"
          using MAGIC5 \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>'')\<close> no_more_step7 by metis
      qed
    qed
  next
    case step_hyps: (factorize A C \<F>')

    have
      A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
      A_undef: "A |\<notin>| trail_atms \<Gamma>" and
      A_least: "\<forall>y|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> A \<longrightarrow> (\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t y) \<longrightarrow> A \<prec>\<^sub>t y"
      using step_hyps(3) unfolding linorder_trm.is_least_in_fset_iff by auto

    have
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_can_prop:"clause_could_propagate \<Gamma> C (Pos A)" and
      C_least: "\<forall>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        D \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> D (Pos A) \<longrightarrow> C \<prec>\<^sub>c D"
      using step_hyps unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

    hence
      Pos_A_undef: "\<not> trail_defined_lit \<Gamma> (Pos A)" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C (Pos A)" and
      C_almost_false: "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
      unfolding atomize_conj clause_could_propagate_def by argo

    have C_not_false: "\<not> trail_false_cls \<Gamma> C"
      using C_in step_hyps by metis

    have no_undef_atm_lt_A:
      "\<not> (\<exists>Aa|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). Aa \<prec>\<^sub>t A \<and> Aa |\<notin>| trail_atms \<Gamma>)"
      by (metis A_least \<Gamma>_lower_set linorder_trm.dual_order.asym linorder_trm.neq_iff
          linorder_trm.not_in_lower_setI)

    have "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      unfolding is_least_nonskipped_clause_def
      unfolding linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using C_in .
    next
      have "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      proof (intro ord_res_8_can_factorize.intros)
        show "\<not> trail_false_cls \<Gamma> C"
          using C_not_false .
      next
        show "ord_res.is_maximal_lit (Pos A) C"
          using C_max_lit .
      next
        show "\<not> (\<exists>Aa|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). Aa \<prec>\<^sub>t atm_of (Pos A) \<and> Aa |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_A by simp
      next
        show "\<not> trail_defined_lit \<Gamma> (Pos A)"
          using Pos_A_undef .
      next
        show "is_pos (Pos A)"
          by simp
      next
        show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
          using C_almost_false .
      next
        show "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
          using step_hyps by argo
      qed

      thus "trail_false_cls \<Gamma> C \<or>
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<or>
        ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
        using \<open>ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> C\<close> by argo
    next
      fix D :: "'f gclause"
      assume
        D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        D_neq: "D \<noteq> C" and
        D_spec_disj: "trail_false_cls \<Gamma> D \<or>
          ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
          ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"

      hence "
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D \<or>
        ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        using step_hyps D_in by metis

      thus "C \<prec>\<^sub>c D"
      proof (elim disjE)
        assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        thus "C \<prec>\<^sub>c D"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_decide_neg.cases)
          case hyps: (1 L A')
          hence "A = A'"
            using step_hyps
            by (smt (verit, del_insts) \<Gamma>_lower_set linorder_trm.antisym_conv3
                linorder_trm.dual_order.strict_implies_not_eq linorder_trm.dual_order.strict_trans
                linorder_trm.is_least_in_ffilter_iff linorder_trm.not_in_lower_setI)
          hence "A \<prec>\<^sub>t atm_of L"
            using hyps
            unfolding linorder_trm.is_least_in_ffilter_iff
            by argo
          hence "Pos A \<prec>\<^sub>l L"
            by (cases L) simp_all
          thus ?thesis
            using C_max_lit \<open>linorder_lit.is_maximal_in_mset D L\<close>
            by (metis linorder_lit.multp_if_maximal_less_that_maximal)
        qed
      next
        assume "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        thus "C \<prec>\<^sub>c D"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_skip_undefined_neg.cases)
          case hyps: (1 L)
          hence "atm_of L = A"
            using step_hyps
            by (smt (verit, best)
                A_in A_least A_undef D_in \<Gamma>_lower_set atm_of_in_atms_of_clssI
                linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
                linorder_trm.not_in_lower_setI trail_defined_lit_iff_trail_defined_atm)
          hence "Pos A \<prec>\<^sub>l L"
            using \<open>is_neg L\<close> by (cases L) simp_all
          thus ?thesis
            using C_max_lit \<open>linorder_lit.is_maximal_in_mset D L\<close>
            by (metis linorder_lit.multp_if_maximal_less_that_maximal)
        qed
      next
        assume "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
        thus "C \<prec>\<^sub>c D"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> D rule: ord_res_8_can_skip_undefined_pos_ultimate.cases)
          case hyps: (1 L)
          thus ?thesis
            by (meson C_in D_neq linorder_cls.linorder_cases)
        qed
      next
        assume "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> D"

        then obtain L where
          D_max_lit: "ord_res.is_maximal_lit L D" and
          "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)" and
          L_undef: "\<not> trail_defined_lit \<Gamma> L" and
          D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}" and
          "is_pos L"
          by (auto elim: ord_res_8_can_factorize.cases ord_res_8_can_produce.cases)

        hence "atm_of L = A"
          using step_hyps
          by (smt (verit, ccfv_SIG) A_in A_least A_undef D_in \<Gamma>_lower_set
              linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
              linorder_trm.not_in_lower_setI atm_of_in_atms_of_clssI
              trail_defined_lit_iff_trail_defined_atm)

        hence "L = Pos A"
          using \<open>is_pos L\<close> by (cases L) simp_all

        hence "clause_could_propagate \<Gamma> D (Pos A)"
          unfolding clause_could_propagate_def
          using D_almost_false D_max_lit L_undef by metis

        thus "C \<prec>\<^sub>c D"
          using D_in D_neq C_least by metis
      next
        assume "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> D"

        then obtain L where
          D_max_lit: "ord_res.is_maximal_lit L D" and
          "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)" and
          L_undef: "\<not> trail_defined_lit \<Gamma> L" and
          D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}" and
          "is_pos L"
          by (auto elim: ord_res_8_can_factorize.cases ord_res_8_can_produce.cases)

        hence "atm_of L = A"
          using step_hyps
          by (smt (verit, ccfv_SIG) A_in A_least A_undef D_in \<Gamma>_lower_set
              linorder_lit.is_maximal_in_mset_iff linorder_trm.antisym_conv3
              linorder_trm.not_in_lower_setI atm_of_in_atms_of_clssI
              trail_defined_lit_iff_trail_defined_atm)

        hence "L = Pos A"
          using \<open>is_pos L\<close> by (cases L) simp_all

        hence "clause_could_propagate \<Gamma> D (Pos A)"
          unfolding clause_could_propagate_def
          using D_almost_false D_max_lit L_undef by metis

        thus "C \<prec>\<^sub>c D"
          using D_in D_neq C_least by metis
      qed
    qed

    hence "\<C> = Some C"
      using match_hyps by metis

    define \<C>' where
      "\<C>' = Some (efac C)"

    have first_step7: "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>')"
      unfolding \<C>'_def
    proof (rule ord_res_7.factoring)
      show "\<not> trail_false_cls \<Gamma> C"
        using C_not_false .
    next
      show "ord_res.is_maximal_lit (Pos A) C"
        using C_max_lit .
    next
      show "\<not> (\<exists>Aa|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). Aa \<prec>\<^sub>t atm_of (Pos A) \<and> Aa |\<notin>| trail_atms \<Gamma>)"
        using no_undef_atm_lt_A by simp
    next
      show "\<not> trail_defined_lit \<Gamma> (Pos A)"
        using Pos_A_undef .
    next
      show "is_pos (Pos A)"
        by simp
    next
      show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
        using C_almost_false .
    next
      show "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
        using step_hyps by argo
    next
      show "\<F>' = finsert C \<F>"
        using step_hyps by argo
    qed

    moreover have "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>')"
      using \<open>\<C> = Some C\<close> first_step7 match_hyps(3) ord_res_7_preserves_invars by blast

    ultimately obtain \<C>'' where
      following_steps7: "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>') (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'')" and
      no_more_step7: "(\<nexists>\<C>'''. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'') (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'''))"
      using MAGIC6 by metis

    show ?thesis
    proof (intro exI conjI)
      have "(ord_res_7 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'')"
        unfolding \<open>\<C> = Some C\<close>
        using first_step7 following_steps7 by simp

      thus "(constant_context ord_res_7)\<^sup>+\<^sup>+ S7 (N, U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'')"
        unfolding S7_def by (simp add: tranclp_constant_context)

      show "ord_res_7_matches_ord_res_8 (N, U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'') S8'"
        unfolding S8'_def \<open>s8' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)\<close>
      proof (intro ord_res_7_matches_ord_res_8.intros allI)
        show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'')"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>')\<close> following_steps7
            rtranclp_ord_res_7_preserves_ord_res_7_invars by blast

        show "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)"
          using invars_s8' step_hyps(1) by blast

        fix C :: "'f gclause"
        show "\<C>'' = Some C \<longleftrightarrow> is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F>' \<Gamma> C"
          using MAGIC5 \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, \<C>'')\<close> no_more_step7 by metis
      qed
    qed
  next
    case step_hyps: (resolution E A D U\<^sub>e\<^sub>r' \<Gamma>')

    note E_max_lit = \<open>ord_res.is_maximal_lit (Neg A) E\<close>

    have
      E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      E_false: "trail_false_cls \<Gamma> E" and
      E_least: "\<forall>F |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). F \<noteq> E \<longrightarrow> trail_false_cls \<Gamma> F \<longrightarrow> E \<prec>\<^sub>c F"
      using step_hyps
      unfolding atomize_conj
      unfolding linorder_cls.is_least_in_ffilter_iff
      by argo

    have "is_least_nonskipped_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
      unfolding is_least_nonskipped_clause_def
      unfolding linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using E_in .
    next
      show "trail_false_cls \<Gamma> E \<or>
        ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> E \<or>
        ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
        using E_false by argo
    next
      fix F :: "'f gclause"
      assume
        F_in: "F |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        F_neq: "F \<noteq> E" and
        D_spec_disj: "trail_false_cls \<Gamma> F \<or>
          ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> F \<or>
          ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> F \<or>
          ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> F \<or>
          ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> F \<or>
          ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> F"

      show "E \<prec>\<^sub>c F"
        using D_spec_disj
      proof (elim disjE)
        assume "trail_false_cls \<Gamma> F"
        thus "E \<prec>\<^sub>c F"
          using E_least F_in F_neq by metis
      next
        assume "ord_res_8_can_decide_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> F"
        thus "E \<prec>\<^sub>c F"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> F rule: ord_res_8_can_decide_neg.cases)
          case hyps: (1 L' A')
          thus ?thesis
            using no_undef_atom_le_max_lit_if_lt_false_clause[
                OF \<Gamma>_lower_set E_in E_false E_max_lit F_in \<open>ord_res.is_maximal_lit L' F\<close>]
            by (metis (no_types, lifting) F_neq linorder_cls.neq_iff
                linorder_trm.is_least_in_ffilter_iff reflclp_iff)
        qed
      next
        assume "ord_res_8_can_skip_undefined_neg N U\<^sub>e\<^sub>r \<F> \<Gamma> F"
        thus "E \<prec>\<^sub>c F"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> F rule: ord_res_8_can_skip_undefined_neg.cases)
          case (1 L')
          thus ?thesis
            using no_undef_atom_le_max_lit_if_lt_false_clause[
                OF \<Gamma>_lower_set E_in E_false E_max_lit F_in \<open>ord_res.is_maximal_lit L' F\<close>]
            by (metis F_in F_neq atm_of_in_atms_of_clssI linorder_cls.not_less_iff_gr_or_eq
                linorder_lit.is_maximal_in_mset_iff reflclp_iff
                trail_defined_lit_iff_trail_defined_atm)
        qed
      next
        assume "ord_res_8_can_skip_undefined_pos_ultimate N U\<^sub>e\<^sub>r \<F> \<Gamma> F"
        thus "E \<prec>\<^sub>c F"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> F rule: ord_res_8_can_skip_undefined_pos_ultimate.cases)
          case (1 L')
          thus ?thesis
            using no_undef_atom_le_max_lit_if_lt_false_clause[
                OF \<Gamma>_lower_set E_in E_false E_max_lit F_in \<open>ord_res.is_maximal_lit L' F\<close>]
            by (metis F_in F_neq atm_of_in_atms_of_clssI linorder_cls.not_less_iff_gr_or_eq
                linorder_lit.is_maximal_in_mset_iff reflclp_iff
                trail_defined_lit_iff_trail_defined_atm)
        qed
      next
        assume "ord_res_8_can_produce N U\<^sub>e\<^sub>r \<F> \<Gamma> F"
        thus "E \<prec>\<^sub>c F"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> F rule: ord_res_8_can_produce.cases)
          case (1 L')
          thus ?thesis
            using no_undef_atom_le_max_lit_if_lt_false_clause[
                OF \<Gamma>_lower_set E_in E_false E_max_lit F_in \<open>ord_res.is_maximal_lit L' F\<close>]
            by (metis F_in F_neq atm_of_in_atms_of_clssI linorder_cls.not_less_iff_gr_or_eq
                linorder_lit.is_maximal_in_mset_iff reflclp_iff
                trail_defined_lit_iff_trail_defined_atm)
        qed
      next
        assume "ord_res_8_can_factorize N U\<^sub>e\<^sub>r \<F> \<Gamma> F"
        thus "E \<prec>\<^sub>c F"
        proof (cases N U\<^sub>e\<^sub>r \<F> \<Gamma> F rule: ord_res_8_can_factorize.cases)
          case (1 L')
          thus ?thesis
            using no_undef_atom_le_max_lit_if_lt_false_clause[
                OF \<Gamma>_lower_set E_in E_false E_max_lit F_in \<open>ord_res.is_maximal_lit L' F\<close>]
            by (metis F_in F_neq atm_of_in_atms_of_clssI linorder_cls.not_less_iff_gr_or_eq
                linorder_lit.is_maximal_in_mset_iff reflclp_iff
                trail_defined_lit_iff_trail_defined_atm)
        qed
      qed
    qed

    hence "\<C> = Some E"
      using match_hyps by metis

    obtain \<C>' where first_step7: "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>')"
    proof atomize_elim
      have "(Pos A, Some D) \<in> set \<Gamma>"
        using \<open>map_of \<Gamma> (Pos A) = Some (Some D)\<close> by (metis map_of_SomeD)

      hence D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> Pos A#}"
        using ord_res_7_invars_implies_propagated_clause_almost_false
          \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> by metis

      have eres_false: "trail_false_cls \<Gamma> (eres D E)"
        unfolding trail_false_cls_def
      proof (intro ballI)
        fix K :: "'f gliteral"
        assume "K \<in># eres D E"
        hence "K \<in># D \<and> K \<noteq> Pos A \<or> K \<in># E"
          using strong_lit_in_one_of_resolvents_if_in_eres[OF E_max_lit] by simp
        thus "trail_false_lit \<Gamma> K"
        proof (elim disjE conjE)
          assume "K \<in># D" and "K \<noteq> Pos A"
          thus "trail_false_lit \<Gamma> K"
            using D_almost_false unfolding trail_false_cls_def by simp
        next
          assume "K \<in># E"
          thus "trail_false_lit \<Gamma> K"
            using E_false unfolding trail_false_cls_def by simp
        qed
      qed

      show "\<exists>\<C>'. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>')"
      proof (cases "eres D E = {#}")
        case True
        hence "\<And>Ln. \<forall>K. ord_res.is_maximal_lit K (eres D E) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
          unfolding linorder_lit.is_maximal_in_mset_iff
          by simp
        hence "\<Gamma>' = dropWhile (\<lambda>Ln. True) \<Gamma>"
          using step_hyps by meson
        hence "\<Gamma>' = []"
          by simp
        show ?thesis
        proof (intro exI)
          show "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})"
            using ord_res_7.resolution_bot[OF E_false E_max_lit]
              \<open>map_of \<Gamma> (Pos A) = Some (Some D)\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> True \<open>\<Gamma>' = []\<close>
            by simp
        qed
      next
        case False
        then obtain K where eres_max_lit: "ord_res.is_maximal_lit K (eres D E)"
          using linorder_lit.ex_maximal_in_mset by presburger
        hence "\<And>Ln. (\<forall>K. ord_res.is_maximal_lit K (eres D E) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<longleftrightarrow>
          atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
          by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')
        hence \<Gamma>'_eq: "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"
          using step_hyps by meson
        show ?thesis
        proof (cases K)
          case (Pos A\<^sub>K)
          hence K_pos: "is_pos K"
            by simp

          then show ?thesis
            using ord_res_7.resolution_pos[OF E_false E_max_lit _ _ _ False \<Gamma>'_eq
                eres_max_lit K_pos]
            using step_hyps by fastforce
        next
          case (Neg A\<^sub>K)

          hence K_neg: "is_neg K"
            by simp

          have "trail_false_lit \<Gamma> K"
            using eres_false eres_max_lit
            unfolding linorder_lit.is_maximal_in_mset_iff trail_false_cls_def by metis

          hence "\<exists>opt. (- K, opt) \<in> set \<Gamma>"
            unfolding trail_false_lit_def by auto

          moreover have "\<forall>Ln\<in>set \<Gamma>. is_neg (fst Ln) = (snd Ln = None)"
            using invars7 by argo

          ultimately obtain C where "(- K, Some C) \<in> set \<Gamma>"
            unfolding Neg uminus_Neg by fastforce

          hence "map_of \<Gamma> (- K) = Some (Some C)"
          proof (rule map_of_is_SomeI[rotated])
            show "distinct (map fst \<Gamma>)"
              using \<Gamma>_consistent
              by (metis distinct_lits_if_trail_consistent)
          qed

          then show ?thesis
            using ord_res_7.resolution_neg[OF E_false E_max_lit _ _ _ False \<Gamma>'_eq
                eres_max_lit K_neg]
            using step_hyps by fastforce
        qed
      qed
    qed

    moreover have "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>')"
      using \<open>\<C> = Some E\<close> first_step7 match_hyps(3) ord_res_7_preserves_invars by blast

    ultimately obtain \<C>'' where
      following_steps7: "(ord_res_7 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>') (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'')" and
      no_more_step7: "(\<nexists>\<C>'''. ord_res_7 N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'') (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'''))"
      using MAGIC6 by metis

    show ?thesis
    proof (intro exI conjI)
      have "(ord_res_7 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'')"
        unfolding \<open>\<C> = Some E\<close>
        using first_step7 following_steps7 by simp

      thus "(constant_context ord_res_7)\<^sup>+\<^sup>+ S7 (N, U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'')"
        unfolding S7_def by (simp add: tranclp_constant_context)

      show "ord_res_7_matches_ord_res_8 (N, U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'') S8'"
        unfolding S8'_def \<open>s8' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close>
      proof (intro ord_res_7_matches_ord_res_8.intros allI)
        show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'')"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>')\<close> following_steps7
            rtranclp_ord_res_7_preserves_ord_res_7_invars by blast

        show "ord_res_8_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')"
          using invars_s8' step_hyps(1) by blast

        fix C :: "'f gclause"
        show "\<C>'' = Some C \<longleftrightarrow> is_least_nonskipped_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C"
          using MAGIC5 \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', \<C>'')\<close> no_more_step7 by metis
      qed
    qed
  qed
qed

theorem bisimulation_ord_res_7_ord_res_8:
  defines "match \<equiv> \<lambda>_. ord_res_7_matches_ord_res_8"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_7_state \<Rightarrow> 'f ord_res_8_state \<Rightarrow> bool) \<R>.
    bisimulation
      (constant_context ord_res_7) (constant_context ord_res_8)
      ord_res_7_final ord_res_8_final
      \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_7_state \<Rightarrow> 'f ord_res_8_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation
      (constant_context ord_res_7) ord_res_7_final
      (constant_context ord_res_8) ord_res_8_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique (constant_context ord_res_7)"
    using right_unique_constant_context right_unique_ord_res_7 by metis
next
  show "right_unique (constant_context ord_res_8)"
    using right_unique_constant_context right_unique_ord_res_8 by metis
next
  show "\<forall>S. ord_res_7_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_7 S S')"
    by (metis finished_def ord_res_7_semantics.final_finished)
next
  show "\<forall>S. ord_res_8_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_8 S S')"
    by (metis finished_def ord_res_8_semantics.final_finished)
next
  show "\<forall>i S7 S8. match i S7 S8 \<longrightarrow> ord_res_7_final S7 \<longleftrightarrow> ord_res_8_final S8"
    unfolding match_def
    using ord_res_7_final_iff_ord_res_8_final by metis
next
  show "\<forall>i S7 S8. match i S7 S8 \<longrightarrow>
       safe_state (constant_context ord_res_7) ord_res_7_final S7 \<and>
       safe_state (constant_context ord_res_8) ord_res_8_final S8"
  proof (intro allI impI conjI)
    fix i S7 S8
    assume match: "match i S7 S8"
    show "safe_state (constant_context ord_res_7) ord_res_7_final S7"
      using match[unfolded match_def]
      using ord_res_7_safe_state_if_invars
      using ord_res_7_matches_ord_res_8.simps by auto

    show "safe_state (constant_context ord_res_8) ord_res_8_final S8"
      using match[unfolded match_def]
      using ord_res_8_safe_state_if_invars
      using ord_res_7_matches_ord_res_8.simps by auto
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i S7 S8 S8'. match i S7 S8 \<longrightarrow> constant_context ord_res_8 S8 S8' \<longrightarrow>
    (\<exists>i' S7'. (constant_context ord_res_7)\<^sup>+\<^sup>+ S7 S7' \<and> match i' S7' S8') \<or>
    (\<exists>i'. match i' S7 S8' \<and> False)"
    unfolding match_def
    using backward_simulation_between_7_and_8 by metis
qed

end


section \<open>ORD-RES-9 (factorize when propagating)\<close>

type_synonym 'f ord_res_9_state =
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gliteral \<times> 'f gclause option) list"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_8_matches_ord_res_9 :: "'f ord_res_8_state \<Rightarrow> 'f ord_res_9_state \<Rightarrow> bool" where
  "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<Longrightarrow>
    ord_res_8_matches_ord_res_9 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"

lemma ord_res_8_final_iff_ord_res_9_final:
  fixes S8 S9
  assumes match: "ord_res_8_matches_ord_res_9 S8 S9"
  shows "ord_res_8_final S8 \<longleftrightarrow> ord_res_8_final S9"
  using match
proof (cases S8 S9 rule: ord_res_8_matches_ord_res_9.cases)
  case (1 N U\<^sub>e\<^sub>r \<F> \<Gamma>)
  then show ?thesis
    by argo
qed

lemma backward_simulation_between_8_and_9:
  fixes S8 S9 S9'
  assumes match: "ord_res_8_matches_ord_res_9 S8 S9" and step: "constant_context ord_res_9 S9 S9'"
  shows "\<exists>S8'. (constant_context ord_res_8)\<^sup>+\<^sup>+ S8 S8' \<and> ord_res_8_matches_ord_res_9 S8' S9'"
  using match
proof (cases S8 S9 rule: ord_res_8_matches_ord_res_9.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<Gamma>)

  note S8_def = \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
  note S9_def = \<open>S9 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
  note invars = \<open>ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>

  obtain s9' where S9'_def: "S9' = (N, s9')" and step': "ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) s9'"
    using step unfolding S9_def
    using constant_context.cases by blast

  have "ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) s9' \<or> (ord_res_8 N OO ord_res_8 N) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) s9'"
    using step' ord_res_9_is_one_or_two_ord_res_9_steps by metis

  hence steps8: "(ord_res_8 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) s9'"
    by auto

  show ?thesis
  proof (intro exI conjI)
    show "(constant_context ord_res_8)\<^sup>+\<^sup>+ S8 (N, s9')"
      unfolding S8_def
      using steps8 by (simp add: tranclp_constant_context)
  next
    have "ord_res_8_invars N s9'"
      using invars steps8 tranclp_ord_res_8_preserves_invars by metis

    thus "ord_res_8_matches_ord_res_9 (N, s9') S9'"
      unfolding S9'_def
      by (metis ord_res_8_matches_ord_res_9.intros prod_cases3)
  qed
qed

theorem bisimulation_ord_res_8_ord_res_9:
  defines "match \<equiv> \<lambda>_. ord_res_8_matches_ord_res_9"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_8_state \<Rightarrow> 'f ord_res_9_state \<Rightarrow> bool) \<R>.
    bisimulation
      (constant_context ord_res_8) (constant_context ord_res_9)
      ord_res_8_final ord_res_8_final
      \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_8_state \<Rightarrow> 'f ord_res_9_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation
      (constant_context ord_res_8) ord_res_8_final
      (constant_context ord_res_9) ord_res_8_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique (constant_context ord_res_8)"
    using right_unique_constant_context right_unique_ord_res_8 by metis
next
  show "right_unique (constant_context ord_res_9)"
    using right_unique_constant_context right_unique_ord_res_9 by metis
next
  show "\<forall>S. ord_res_8_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_8 S S')"
    by (metis finished_def ord_res_8_semantics.final_finished)
next
  show "\<forall>S. ord_res_8_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_9 S S')"
    by (metis finished_def ord_res_9_semantics.final_finished)
next
  show "\<forall>i S8 S9. match i S8 S9 \<longrightarrow> ord_res_8_final S8 \<longleftrightarrow> ord_res_8_final S9"
    unfolding match_def
    using ord_res_8_final_iff_ord_res_9_final by metis
next
  show "\<forall>i S8 S9. match i S8 S9 \<longrightarrow>
       safe_state (constant_context ord_res_8) ord_res_8_final S8 \<and>
       safe_state (constant_context ord_res_9) ord_res_8_final S9"
  proof (intro allI impI conjI)
    fix i S8 S9
    assume match: "match i S8 S9"
    show "safe_state (constant_context ord_res_8) ord_res_8_final S8"
      using match[unfolded match_def]
      using ord_res_8_safe_state_if_invars
      using ord_res_8_matches_ord_res_9.simps by auto

    show "safe_state (constant_context ord_res_9) ord_res_8_final S9"
      using match[unfolded match_def]
      using ord_res_9_safe_state_if_invars
      using ord_res_8_matches_ord_res_9.simps by auto
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i S8 S9 S9'. match i S8 S9 \<longrightarrow> constant_context ord_res_9 S9 S9' \<longrightarrow>
    (\<exists>i' S8'. (constant_context ord_res_8)\<^sup>+\<^sup>+ S8 S8' \<and> match i' S8' S9') \<or>
    (\<exists>i'. match i' S8 S9' \<and> False)"
    unfolding match_def
    using backward_simulation_between_8_and_9 by metis
qed

end


section \<open>ORD-RES-10 (propagate iff a conflict is produced)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_9_matches_ord_res_10 :: "'f ord_res_9_state \<Rightarrow> 'f ord_res_10_state \<Rightarrow> bool" where
  "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9) \<Longrightarrow>
    ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0) \<Longrightarrow>
    list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 \<Longrightarrow>
    list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 \<Longrightarrow>
    ord_res_9_matches_ord_res_10 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9) (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0)"

lemma ord_res_9_final_iff_ord_res_10_final:
  fixes S9 S10
  assumes match: "ord_res_9_matches_ord_res_10 S9 S10"
  shows "ord_res_8_final S9 \<longleftrightarrow> ord_res_8_final S10"
  using match
proof (cases S9 S10 rule: ord_res_9_matches_ord_res_10.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0)
  then show ?thesis
    using trail_atms_eq_trail_atms_if_same_lits[OF \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>]
    using trail_false_cls_eq_trail_false_cls_if_same_lits[OF \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>]
    unfolding ord_res_8_final.simps
    by simp
qed

lemma backward_simulation_between_9_and_10:
  fixes S9 S10 S10'
  assumes
    match: "ord_res_9_matches_ord_res_10 S9 S10" and
    step: "constant_context ord_res_10 S10 S10'"
  shows "\<exists>S9'. (constant_context ord_res_9)\<^sup>+\<^sup>+ S9 S9' \<and> ord_res_9_matches_ord_res_10 S9' S10'"
  using match
proof (cases S9 S10 rule: ord_res_9_matches_ord_res_10.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0)

  note S9_def = \<open>S9 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9)\<close>
  note S10_def = \<open>S10 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0)\<close>
  note invars9 = \<open>ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9)\<close>
  note invars10 = \<open>ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0)\<close>

  have "trail_atms \<Gamma>\<^sub>9 = trail_atms \<Gamma>\<^sub>1\<^sub>0"
    using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close> trail_atms_eq_trail_atms_if_same_lits
    by metis

  have "trail_false_lit \<Gamma>\<^sub>9 = trail_false_lit \<Gamma>\<^sub>1\<^sub>0"
    using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close> trail_false_lit_eq_trail_false_lit_if_same_lits
    by metis

  have "trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0"
    using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close> trail_false_cls_eq_trail_false_cls_if_same_lits
    by metis

  have "trail_defined_lit \<Gamma>\<^sub>9 = trail_defined_lit \<Gamma>\<^sub>1\<^sub>0"
    using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
      trail_defined_lit_eq_trail_defined_lit_if_same_lits by metis

  have "trail_defined_cls \<Gamma>\<^sub>9 = trail_defined_cls \<Gamma>\<^sub>1\<^sub>0"
    using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
      trail_defined_cls_eq_trail_defined_cls_if_same_lits by metis

  have "clause_could_propagate \<Gamma>\<^sub>9 = clause_could_propagate \<Gamma>\<^sub>1\<^sub>0"
    unfolding clause_could_propagate_def
    unfolding \<open>trail_defined_lit \<Gamma>\<^sub>9 = trail_defined_lit \<Gamma>\<^sub>1\<^sub>0\<close>
    unfolding \<open>trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0\<close> ..

  have \<Gamma>\<^sub>9_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>\<^sub>9"
    using invars9[unfolded ord_res_8_invars_def trail_is_sorted_def, simplified] by argo

  obtain s10' where "S10' = (N, s10')" and step10: "ord_res_10 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0) s10'"
    using step unfolding S10_def by (auto elim: constant_context.cases)

  show ?thesis
    using step10
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0)" s10' rule: ord_res_10.cases)
    case step_hyps: (decide_neg A \<Gamma>\<^sub>1\<^sub>0')

    define \<Gamma>\<^sub>9' where
      "\<Gamma>\<^sub>9' = (Neg A, None) # \<Gamma>\<^sub>9"

    show ?thesis
    proof (intro exI conjI)
      have step9: "ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9')"
      proof (rule ord_res_9.decide_neg)
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>\<^sub>9 C)"
          using step_hyps \<open>trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_trm.is_least_in_fset
          {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>\<^sub>9. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using step_hyps \<open>trail_atms \<Gamma>\<^sub>9 = trail_atms \<Gamma>\<^sub>1\<^sub>0\<close> by metis
      next
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma>\<^sub>9 C (Pos A))"
          using step_hyps \<open>clause_could_propagate \<Gamma>\<^sub>9 = clause_could_propagate \<Gamma>\<^sub>1\<^sub>0\<close> by metis
      next
        show "\<Gamma>\<^sub>9' = (Neg A, None) # \<Gamma>\<^sub>9"
          using \<Gamma>\<^sub>9'_def .
      qed

      thus "(constant_context ord_res_9)\<^sup>+\<^sup>+ S9 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9')"
        unfolding S9_def by (auto intro: constant_context.intros)

      show "ord_res_9_matches_ord_res_10 (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9') S10'"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0')\<close>
      proof (rule ord_res_9_matches_ord_res_10.intros)
        show "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9')"
          using invars9 step9 ord_res_9_preserves_invars by metis 
      next
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0')"
          using invars10 step10 ord_res_10_preserves_invars \<open>s10' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>1\<^sub>0')\<close> by metis
      next
        show "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding \<open>\<Gamma>\<^sub>9' = (Neg A, None) # \<Gamma>\<^sub>9\<close> \<open>\<Gamma>\<^sub>1\<^sub>0' = (Neg A, None) # \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close> by simp
      next
        show "list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding \<open>\<Gamma>\<^sub>9' = (Neg A, None) # \<Gamma>\<^sub>9\<close> \<open>\<Gamma>\<^sub>1\<^sub>0' = (Neg A, None) # \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
          by simp
      qed
    qed
  next
    case step_hyps: (decide_pos A C \<Gamma>\<^sub>1\<^sub>0' \<F>')

    define \<Gamma>\<^sub>9' where
      "\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9"
    
    show ?thesis
    proof (intro exI conjI)
      have step9: "ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9')"
      proof (rule ord_res_9.propagate)
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>\<^sub>9 C)"
          using step_hyps \<open>trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_trm.is_least_in_fset
          {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>\<^sub>9. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using step_hyps \<open>trail_atms \<Gamma>\<^sub>9 = trail_atms \<Gamma>\<^sub>1\<^sub>0\<close> by metis
      next
        show "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma>\<^sub>9 C (Pos A)|} C"
          using step_hyps \<open>clause_could_propagate \<Gamma>\<^sub>9 = clause_could_propagate \<Gamma>\<^sub>1\<^sub>0\<close> by metis
      next
        show "\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9"
          using \<Gamma>\<^sub>9'_def .
      next
        show "\<F>' = (if ord_res.is_strictly_maximal_lit (Pos A) C then \<F> else finsert C \<F>)"
          using step_hyps by argo
      qed

      thus "(constant_context ord_res_9)\<^sup>+\<^sup>+ S9 (N, U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9')"
        unfolding S9_def by (auto intro: constant_context.intros)

      show "ord_res_9_matches_ord_res_10 (N, U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9') S10'"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>1\<^sub>0')\<close>
      proof (rule ord_res_9_matches_ord_res_10.intros)
        show "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9')"
          using invars9 step9 ord_res_9_preserves_invars by metis 
      next
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>1\<^sub>0')"
          using invars10 step10 ord_res_10_preserves_invars \<open>s10' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>1\<^sub>0')\<close> by metis
      next
        show "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding \<open>\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9\<close> \<open>\<Gamma>\<^sub>1\<^sub>0' = (Pos A, None) # \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close> by simp
      next
        show "list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding \<open>\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9\<close> \<open>\<Gamma>\<^sub>1\<^sub>0' = (Pos A, None) # \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
          by simp
      qed
    qed
  next
    case step_hyps: (propagate A C \<Gamma>\<^sub>1\<^sub>0' \<F>')

    define \<Gamma>\<^sub>9' where
      "\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9"
    
    show ?thesis
    proof (intro exI conjI)
      have step9: "ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9')"
      proof (rule ord_res_9.propagate)
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>\<^sub>9 C)"
          using step_hyps \<open>trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_trm.is_least_in_fset
          {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>\<^sub>9. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using step_hyps \<open>trail_atms \<Gamma>\<^sub>9 = trail_atms \<Gamma>\<^sub>1\<^sub>0\<close> by metis
      next
        show "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma>\<^sub>9 C (Pos A)|} C"
          using step_hyps \<open>clause_could_propagate \<Gamma>\<^sub>9 = clause_could_propagate \<Gamma>\<^sub>1\<^sub>0\<close> by metis
      next
        show "\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9"
          using \<Gamma>\<^sub>9'_def .
      next
        show "\<F>' = (if ord_res.is_strictly_maximal_lit (Pos A) C then \<F> else finsert C \<F>)"
          using step_hyps by argo
      qed

      thus "(constant_context ord_res_9)\<^sup>+\<^sup>+ S9 (N, U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9')"
        unfolding S9_def by (auto intro: constant_context.intros)

      show "ord_res_9_matches_ord_res_10 (N, U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9') S10'"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>1\<^sub>0')\<close>
      proof (rule ord_res_9_matches_ord_res_10.intros)
        show "ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>9')"
          using invars9 step9 ord_res_9_preserves_invars by metis 
      next
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>1\<^sub>0')"
          using invars10 step10 ord_res_10_preserves_invars \<open>s10' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>\<^sub>1\<^sub>0')\<close> by metis
      next
        show "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding \<open>\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9\<close> \<open>\<Gamma>\<^sub>1\<^sub>0' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close> by simp
      next
        show "list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding \<open>\<Gamma>\<^sub>9' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>9\<close> \<open>\<Gamma>\<^sub>1\<^sub>0' = (Pos A, Some (efac C)) # \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
          by simp
      qed
    qed
  next
    case step_hyps: (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>\<^sub>1\<^sub>0')

    have "\<forall>Ln \<Gamma>'. \<Gamma>\<^sub>1\<^sub>0 = Ln # \<Gamma>' \<longrightarrow>
      (snd Ln \<noteq> None) = fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>\<^sub>1\<^sub>0) \<and>
      (\<forall>x\<in>set \<Gamma>'. snd x = None)"
      using invars10 by (simp add: ord_res_10_invars.simps)

    then obtain \<Gamma>\<^sub>1\<^sub>0'' where "\<Gamma>\<^sub>1\<^sub>0 = (Pos A, Some C) # \<Gamma>\<^sub>1\<^sub>0''"
      using \<open>map_of \<Gamma>\<^sub>1\<^sub>0 (Pos A) = Some (Some C)\<close>
      by (metis list.set_cases map_of_SomeD not_Some_eq snd_conv)

    then obtain \<Gamma>\<^sub>9'' where "\<Gamma>\<^sub>9 = (Pos A, Some C) # \<Gamma>\<^sub>9''"
      using \<open>list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
      by (smt (verit, best) list_all2_Cons2 option.discI snd_conv)

    define \<Gamma>\<^sub>9' where
      "\<Gamma>\<^sub>9' = dropWhile (\<lambda>Ln. \<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow>
        atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>9"
    
    show ?thesis
    proof (intro exI conjI)
      have step9: "ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>9) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>9')"
      proof (rule ord_res_9.resolution)
        show "linorder_cls.is_least_in_fset (ffilter (trail_false_cls \<Gamma>\<^sub>9) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using step_hyps \<open>trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0\<close> by argo
      next
        show "ord_res.is_maximal_lit (Neg A) D"
          using step_hyps by argo
      next
        show "map_of \<Gamma>\<^sub>9 (Pos A) = Some (Some C)"
          unfolding \<open>\<Gamma>\<^sub>9 = (Pos A, Some C) # \<Gamma>\<^sub>9''\<close> by simp
      next
        show "U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r"
          using step_hyps by argo
      next
        show "\<Gamma>\<^sub>9' = dropWhile (\<lambda>Ln. \<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow>
          atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>9"
          using \<Gamma>\<^sub>9'_def .
      qed

      thus "(constant_context ord_res_9)\<^sup>+\<^sup>+ S9 (N, U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>9')"
        unfolding S9_def by (auto intro: constant_context.intros)

      show "ord_res_9_matches_ord_res_10 (N, U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>9') S10'"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>1\<^sub>0')\<close>
      proof (rule ord_res_9_matches_ord_res_10.intros)
        show "ord_res_8_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>9')"
          using invars9 step9 ord_res_9_preserves_invars by metis 
      next
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>1\<^sub>0')"
          using invars10 step10 ord_res_10_preserves_invars \<open>s10' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>\<^sub>1\<^sub>0')\<close> by metis
      next
        define P :: "'f gterm literal \<times> 'f gterm literal multiset option \<Rightarrow> bool" where
          "P \<equiv> \<lambda>Ln. \<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"

        have "length (takeWhile P \<Gamma>\<^sub>9) = length (takeWhile P \<Gamma>\<^sub>1\<^sub>0)"
          using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
        proof (induction \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 rule: list.rel_induct)
          case Nil
          show ?case
            by simp
        next
          case (Cons x xs y ys)
          then show ?case
            by (simp add: P_def)
        qed

        moreover have "\<Gamma>\<^sub>9 = takeWhile P \<Gamma>\<^sub>9 @ \<Gamma>\<^sub>9'"
          unfolding takeWhile_dropWhile_id
          unfolding P_def \<open>\<Gamma>\<^sub>9' = dropWhile _ \<Gamma>\<^sub>9\<close> by simp

        moreover have "\<Gamma>\<^sub>1\<^sub>0 = takeWhile P \<Gamma>\<^sub>1\<^sub>0 @ \<Gamma>\<^sub>1\<^sub>0'"
          unfolding takeWhile_dropWhile_id
          unfolding P_def \<open>\<Gamma>\<^sub>1\<^sub>0' = dropWhile _ \<Gamma>\<^sub>1\<^sub>0\<close> by simp

        ultimately have "\<And>Q. list_all2 Q \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 \<longleftrightarrow>
          (list_all2 Q (takeWhile P \<Gamma>\<^sub>9) (takeWhile P \<Gamma>\<^sub>1\<^sub>0) \<and> list_all2 Q \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0')"
          using list_all2_append by metis

        thus
          "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          "list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9' \<Gamma>\<^sub>1\<^sub>0'"
          unfolding atomize_conj
          using \<open>list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
          using \<open>list_all2 (\<lambda>x y. snd y \<noteq> None \<longrightarrow> x = y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0\<close>
          by (simp only:)
      qed
    qed
  qed
qed

theorem bisimulation_ord_res_9_ord_res_10:
  defines "match \<equiv> \<lambda>_. ord_res_9_matches_ord_res_10"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_8_state \<Rightarrow> 'f ord_res_9_state \<Rightarrow> bool) \<R>.
    bisimulation
      (constant_context ord_res_9) (constant_context ord_res_10)
      ord_res_8_final ord_res_8_final
      \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_8_state \<Rightarrow> 'f ord_res_9_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation
      (constant_context ord_res_9) ord_res_8_final
      (constant_context ord_res_10) ord_res_8_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique (constant_context ord_res_9)"
    using right_unique_constant_context right_unique_ord_res_9 by metis
next
  show "right_unique (constant_context ord_res_10)"
    using right_unique_constant_context right_unique_ord_res_10 by metis
next
  show "\<forall>S. ord_res_8_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_9 S S')"
    by (metis finished_def ord_res_9_semantics.final_finished)
next
  show "\<forall>S. ord_res_8_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_10 S S')"
    by (metis finished_def ord_res_10_semantics.final_finished)
next
  show "\<forall>i S9 S10. match i S9 S10 \<longrightarrow> ord_res_8_final S9 \<longleftrightarrow> ord_res_8_final S10"
    unfolding match_def
    using ord_res_9_final_iff_ord_res_10_final by metis
next
  show "\<forall>i S9 S10. match i S9 S10 \<longrightarrow>
       safe_state (constant_context ord_res_9) ord_res_8_final S9 \<and>
       safe_state (constant_context ord_res_10) ord_res_8_final S10"
  proof (intro allI impI conjI)
    fix i S9 S10
    assume match: "match i S9 S10"
    show "safe_state (constant_context ord_res_9) ord_res_8_final S9"
      using match[unfolded match_def]
      using ord_res_9_safe_state_if_invars
      using ord_res_9_matches_ord_res_10.simps by auto

    show "safe_state (constant_context ord_res_10) ord_res_8_final S10"
      using match[unfolded match_def]
      using ord_res_10_safe_state_if_invars
      using ord_res_9_matches_ord_res_10.simps by auto
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i S9 S10 S10'. match i S9 S10 \<longrightarrow> constant_context ord_res_10 S10 S10' \<longrightarrow>
    (\<exists>i' S9'. (constant_context ord_res_9)\<^sup>+\<^sup>+ S9 S9' \<and> match i' S9' S10') \<or>
    (\<exists>i'. match i' S9 S10' \<and> False)"
    unfolding match_def
    using backward_simulation_between_9_and_10 by metis
qed

end


section \<open>ORD-RES-11 (SCL strategy)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_10_matches_ord_res_11 :: "'f ord_res_10_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool" where
  "ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>) \<Longrightarrow>
    ord_res_11_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, \<C>) \<Longrightarrow>
    U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 - {|{#}|} \<Longrightarrow>
    if {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0) then \<Gamma> = [] \<and> \<C> = Some {#} else \<C> = None \<Longrightarrow>
    ord_res_10_matches_ord_res_11 (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>) (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, \<C>)"

lemma ord_res_10_final_iff_ord_res_11_final:
  fixes S10 S11
  assumes match: "ord_res_10_matches_ord_res_11 S10 S11"
  shows "ord_res_8_final S10 \<longleftrightarrow> ord_res_11_final S11"
  using match
proof (cases S10 S11 rule: ord_res_10_matches_ord_res_11.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 \<F> \<Gamma> U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 \<C>)
  show ?thesis
  proof (rule iffI)
    assume "ord_res_8_final S10"
    thus "ord_res_11_final S11"
      unfolding \<open>S10 = _\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>)" rule: ord_res_8_final.cases)
      case model_found
      hence "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
        using trail_false_cls_mempty by blast
      hence "\<C> = None"
        using match_hyps by argo
      moreover have "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
        using match_hyps
        by (metis \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)\<close> fimage_eqI finsert_fminus1 finsert_iff
            fminus_finsert_absorb funionI2 iefac_mempty)
      ultimately show ?thesis
        unfolding \<open>S11 = _\<close>
        using model_found
        using ord_res_11_final.model_found
        by metis
    next
      case contradiction_found
      hence "\<Gamma> = [] \<and> \<C> = Some {#}"
        using match_hyps by argo
      thus ?thesis
        unfolding \<open>S11 = _\<close>
        using ord_res_11_final.contradiction_found by metis
    qed
  next
    assume "ord_res_11_final S11"
    thus "ord_res_8_final S10"
      unfolding \<open>S11 = _\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, \<C>)" rule: ord_res_11_final.cases)
      case model_found
      show ?thesis
        unfolding \<open>S10 = _\<close>
      proof (rule ord_res_8_final.model_found)
        show "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0). A |\<notin>| trail_atms \<Gamma>)"
          by (metis (no_types, lifting) fimage_iff fminus_finsert_absorb fminus_idemp funionCI
              iefac_mempty local.model_found(1,2) match_hyps(5,6) option.simps(3))
      next
        show "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0). trail_false_cls \<Gamma> C)"
          by (metis finsertCI finsert_fminus1 fminus_finsert_absorb funionI2 iefac_mempty
              local.model_found(1,3) match_hyps(5,6) option.simps(3) rev_fimage_eqI)
      qed
    next
      case contradiction_found
      show ?thesis
        unfolding \<open>S10 = _\<close>
      proof (rule ord_res_8_final.contradiction_found)
        show "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
          using match_hyps contradiction_found
          by auto
      qed
    qed
  qed
qed

lemma forward_simulation_between_10_and_11:
  fixes S10 S11 S10'
  assumes
    match: "ord_res_10_matches_ord_res_11 S10 S11" and
    step: "constant_context ord_res_10 S10 S10'"
  shows "\<exists>S11'. (constant_context ord_res_11)\<^sup>+\<^sup>+ S11 S11' \<and> ord_res_10_matches_ord_res_11 S10' S11'"
  using match
proof (cases S10 S11 rule: ord_res_10_matches_ord_res_11.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 \<F> \<Gamma> U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 \<C>)

  note S10_def = \<open>S10 = (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>)\<close>
  note S11_def = \<open>S11 = (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, \<C>)\<close>
  note invars10 = \<open>ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>)\<close>
  note invars11 = \<open>ord_res_11_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, \<C>)\<close>

  have mempty_not_in_if_no_false_cls: "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
    if "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)) (trail_false_cls \<Gamma>)"
    using that by force

  have \<C>_eq_None_if_no_false_cls: "\<C> = None"
    if "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)) (trail_false_cls \<Gamma>)"
    using match_hyps mempty_not_in_if_no_false_cls[OF that] by argo

  have mempty_not_in_if: "{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
    if "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)) (trail_false_cls \<Gamma>)"
    using that
    by (metis (no_types, opaque_lifting) fimageI iefac_mempty trail_false_cls_mempty)

  have U\<^sub>e\<^sub>r\<^sub>1\<^sub>1_eq_U\<^sub>e\<^sub>r\<^sub>1\<^sub>0_if: "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
    if "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)) (trail_false_cls \<Gamma>)"
    using mempty_not_in_if[OF that] \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 |-| {|{#}|}\<close>
    by (metis (no_types, opaque_lifting) finsertI1 finsert_ident fminusD2 funionCI
        funion_fempty_right funion_finsert_right funion_fminus_cancel2)

  obtain s10' where "S10' = (N, s10')" and step10: "ord_res_10 N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>) s10'"
    using step unfolding S10_def by (auto elim: constant_context.cases)

  show ?thesis
    using step10
  proof (cases N "(U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>)" s10' rule: ord_res_10.cases)
    case step_hyps: (decide_neg A \<Gamma>')

    have "\<C> = None"
      using step_hyps \<C>_eq_None_if_no_false_cls by argo

    have "{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using step_hyps mempty_not_in_if by argo

    have "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using step_hyps U\<^sub>e\<^sub>r\<^sub>1\<^sub>1_eq_U\<^sub>e\<^sub>r\<^sub>1\<^sub>0_if by argo

    show ?thesis
    proof (intro exI conjI)
      have step11: "ord_res_11 N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
      proof (rule ord_res_11.decide_neg)
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). trail_false_cls \<Gamma> C)"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_trm.is_least_in_fset
          {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). \<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). clause_could_propagate \<Gamma> C (Pos A))"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "\<Gamma>' = (Neg A, None) # \<Gamma>"
          using step_hyps by argo
      qed

      thus "(constant_context ord_res_11)\<^sup>+\<^sup>+ S11 (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
        unfolding S11_def \<open>\<C> = None\<close> by (auto intro: constant_context.intros)

      show "ord_res_10_matches_ord_res_11 S10' (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = _\<close>
      proof (rule ord_res_10_matches_ord_res_11.intros)
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>, \<Gamma>')"
          using step10 \<open>s10' = _\<close> invars10 ord_res_10_preserves_invars by metis
      next
        show "ord_res_11_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
          using step11 invars11 \<open>\<C> = None\<close> ord_res_11_preserves_invars by metis
      next
        show "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 |-| {|{#}|}"
          unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close>
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by simp
      next
        have "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by (simp add: iefac_def)
        thus "if {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0) then \<Gamma>' = [] \<and> None = Some {#} else None = None"
          by argo
      qed
    qed
  next
    case step_hyps: (decide_pos A C \<Gamma>' \<F>')
    
    have "\<C> = None"
      using step_hyps \<C>_eq_None_if_no_false_cls by argo

    have "{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using step_hyps mempty_not_in_if by argo

    have "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using step_hyps U\<^sub>e\<^sub>r\<^sub>1\<^sub>1_eq_U\<^sub>e\<^sub>r\<^sub>1\<^sub>0_if by argo

    show ?thesis
    proof (intro exI conjI)
      have step11: "ord_res_11 N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
      proof (rule ord_res_11.decide_pos)
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). trail_false_cls \<Gamma> C)"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_trm.is_least_in_fset
          {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). \<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). clause_could_propagate \<Gamma> C (Pos A)|} C"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "\<Gamma>' = (Pos A, None) # \<Gamma>"
          using step_hyps by argo
      next
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). trail_false_cls \<Gamma>' C)"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "\<F>' = (if ord_res.is_strictly_maximal_lit (Pos A) C then \<F> else finsert C \<F>)"
          using step_hyps by argo
      qed

      thus "(constant_context ord_res_11)\<^sup>+\<^sup>+ S11 (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
        unfolding S11_def \<open>\<C> = None\<close> by (auto intro: constant_context.intros)

      show "ord_res_10_matches_ord_res_11 S10' (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = _\<close>
      proof (rule ord_res_10_matches_ord_res_11.intros)
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>', \<Gamma>')"
          using step10 \<open>s10' = _\<close> invars10 ord_res_10_preserves_invars by metis
      next
        show "ord_res_11_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
          using step11 invars11 \<open>\<C> = None\<close> ord_res_11_preserves_invars by metis
      next
        show "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 |-| {|{#}|}"
          unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close>
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by simp
      next
        have "{#} |\<notin>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by (simp add: iefac_def)
        thus "if {#} |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0) then \<Gamma>' = [] \<and> None = Some {#} else None = None"
          by argo
      qed
    qed
  next
    case step_hyps: (propagate A C \<Gamma>' \<F>')

    have "\<C> = None"
      using step_hyps \<C>_eq_None_if_no_false_cls by argo

    have "{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using step_hyps mempty_not_in_if by argo

    have "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using step_hyps U\<^sub>e\<^sub>r\<^sub>1\<^sub>1_eq_U\<^sub>e\<^sub>r\<^sub>1\<^sub>0_if by argo

    show ?thesis
    proof (intro exI conjI)
      have step11: "ord_res_11 N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
      proof (rule ord_res_11.propagate)
        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). trail_false_cls \<Gamma> C)"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_trm.is_least_in_fset
          {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). \<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). clause_could_propagate \<Gamma> C (Pos A)|} C"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "\<Gamma>' = (Pos A, Some (efac C)) # \<Gamma>"
          using step_hyps by argo
      next
        show "\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1). trail_false_cls \<Gamma>' C"
          using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
      next
        show "\<F>' = (if ord_res.is_strictly_maximal_lit (Pos A) C then \<F> else finsert C \<F>)"
          using step_hyps by argo
      qed

      thus "(constant_context ord_res_11)\<^sup>+\<^sup>+ S11 (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
        unfolding S11_def \<open>\<C> = None\<close> by (auto intro: constant_context.intros)

      show "ord_res_10_matches_ord_res_11 S10' (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
        unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = _\<close>
      proof (rule ord_res_10_matches_ord_res_11.intros)
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0, \<F>', \<Gamma>')"
          using step10 \<open>s10' = _\<close> invars10 ord_res_10_preserves_invars by metis
      next
        show "ord_res_11_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>', \<Gamma>', None)"
          using step11 invars11 \<open>\<C> = None\<close> ord_res_11_preserves_invars by metis
      next
        show "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 |-| {|{#}|}"
          unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close>
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by simp
      next
        have "{#} |\<notin>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by (simp add: iefac_def)
        thus "if {#} |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0) then \<Gamma>' = [] \<and> None = Some {#} else None = None"
          by argo
      qed
    qed
  next
    case step_hyps: (resolution D A C U\<^sub>e\<^sub>r\<^sub>1\<^sub>0' \<Gamma>')

    note D_max_lit = \<open>ord_res.is_maximal_lit (Neg A) D\<close>

    have "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)"
      using \<open>linorder_cls.is_least_in_fset _ D\<close> \<open>linorder_lit.is_maximal_in_mset D _\<close>
      unfolding linorder_cls.is_least_in_ffilter_iff linorder_lit.is_maximal_in_mset_iff
      by (metis (no_types, lifting) empty_iff linorder_cls.leD mempty_lesseq_cls set_mset_empty
          trail_false_cls_mempty)

    have "\<C> = None"
      using match_hyps \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)\<close> by argo

    have "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0"
      using match_hyps \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)\<close> by force

    have step11_conf: "ord_res_11 N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, Some D)"
    proof (rule ord_res_11.conflict)
      show "linorder_cls.is_least_in_fset
        (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>1))) D"
        using step_hyps unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> by argo
    qed

    have \<Gamma>_spec: "\<forall>Ln \<Gamma>'. \<Gamma> = Ln # \<Gamma>' \<longrightarrow>
      (snd Ln \<noteq> None) = fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)) (trail_false_cls \<Gamma>) \<and>
      (\<forall>x\<in>set \<Gamma>'. snd x = None)"
      using invars10 by (simp add: ord_res_10_invars.simps)

    then obtain \<Gamma>''' where "\<Gamma> = (Pos A, Some C) # \<Gamma>'''"
      using \<open>map_of \<Gamma> (Pos A) = Some (Some C)\<close>
      by (metis list.set_cases map_of_SomeD not_Some_eq snd_conv)

    have C_max_lit: "linorder_lit.is_greatest_in_mset C (Pos A)"
      using invars10 by (simp add: ord_res_10_invars.simps \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close>)

    have "ord_res.ground_resolution D C ((D - {#Neg A#}) + (C - {#Pos A#}))"
    proof (rule ord_res.ground_resolutionI)
      show "D = add_mset (Neg A) (D - {#Neg A#})"
        using D_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by simp
    next
      show "C = add_mset (Pos A) (C - {#Pos A#})"
        using C_max_lit unfolding linorder_lit.is_greatest_in_mset_iff by simp
    next
      show "C \<prec>\<^sub>c D"
        using C_max_lit D_max_lit
        by (simp add: clause_lt_clause_if_max_lit_comp
            linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one)
    next
      show "{#} = {#} \<and> ord_res.is_maximal_lit (Neg A) D \<or> Neg A \<in># {#}"
        using D_max_lit by argo
    next
      show "{#} = {#}"
        by argo
    next
      show "ord_res.is_strictly_maximal_lit (Pos A) C"
        using C_max_lit .
    next
      show "remove1_mset (Neg A) D + remove1_mset (Pos A) C = (D - {#Neg A#}) + (C - {#Pos A#})"
        ..
    qed

    hence "eres C D \<noteq> D"
      unfolding eres_ident_iff not_not ground_resolution_def by metis

    have D_false: "trail_false_cls \<Gamma> D"
      using step_hyps unfolding linorder_cls.is_least_in_ffilter_iff by argo

    have "clause_could_propagate \<Gamma>''' C (Pos A)"
      using invars10 \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close> by (simp add: ord_res_10_invars.simps)

    hence "trail_false_cls \<Gamma>''' {#L \<in># C. L \<noteq> Pos A#}"
      unfolding clause_could_propagate_def by argo

    hence C_almost_false: "trail_false_cls \<Gamma> {#L \<in># C. L \<noteq> Pos A#}"
      unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close>
      by (meson suffix_ConsD suffix_order.dual_order.refl trail_false_cls_if_trail_false_suffix)

    have eres_false: "trail_false_cls \<Gamma> (eres C D)"
      unfolding trail_false_cls_def
    proof (intro ballI)
      fix K :: "'f gliteral"
      assume "K \<in># eres C D"
      hence "K \<in># C \<and> K \<noteq> Pos A \<or> K \<in># D"
        using strong_lit_in_one_of_resolvents_if_in_eres[OF D_max_lit] by simp
      thus "trail_false_lit \<Gamma> K"
      proof (elim disjE conjE)
        assume "K \<in># C" and "K \<noteq> Pos A"
        thus "trail_false_lit \<Gamma> K"
          using C_almost_false unfolding trail_false_cls_def by simp
      next
        assume "K \<in># D"
        thus "trail_false_lit \<Gamma> K"
          using D_false unfolding trail_false_cls_def by simp
      qed
    qed

    have "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> ord_res.is_strictly_maximal_lit (fst Ln) C"
      using invars10 by (simp add: ord_res_10_invars.simps)

    hence C_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) C"
      unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close> by simp

    have steps11_reso: "(ord_res_11 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, Some D) (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, Some (eres C D))"
      unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close>
      using C_max_lit rtrancl_ord_res_11_all_resolution_steps by metis

    define strict_P :: "'f gterm literal \<times> 'f gterm literal multiset option \<Rightarrow> bool" where
      "strict_P \<equiv> \<lambda>Ln. \<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<prec>\<^sub>t atm_of (fst Ln)"

    have "\<forall>K \<in># eres C D. - K \<in> fst ` set \<Gamma>"
      using eres_false unfolding trail_false_cls_def trail_false_lit_def .

    moreover have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
      using invars10 by (simp add: ord_res_10_invars.simps)

    ultimately have "dropWhile strict_P \<Gamma> = dropWhile (\<lambda>Ln. - fst Ln \<notin># eres C D) \<Gamma>"
    proof (induction \<Gamma>)
      case Nil
      show ?case by simp
    next
      case (Cons Ln \<Gamma>)

      show ?case
      proof (cases "eres C D = {#}")
        case True
        thus ?thesis
          unfolding strict_P_def linorder_lit.is_maximal_in_mset_iff by simp
      next
        case False

        then obtain L where eres_max_lit: "ord_res.is_maximal_lit L (eres C D)"
          using linorder_lit.ex_maximal_in_mset by metis

        hence strict_P_Ln_iff: "strict_P Ln \<longleftrightarrow> atm_of L \<prec>\<^sub>t atm_of (fst Ln)"
          unfolding strict_P_def
          by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

        show ?thesis
        proof (cases "atm_of L \<prec>\<^sub>t atm_of (fst Ln)")
          case True

          moreover have "- fst Ln \<notin># eres C D"
            using True
            by (smt (verit, best) atm_of_uminus eres_max_lit linorder_lit.dual_order.strict_trans
                linorder_lit.is_maximal_in_mset_iff linorder_lit.neq_iff linorder_trm.order.irrefl
                literal.exhaust_sel ord_res.less_lit_simps(4))

          moreover have "dropWhile strict_P \<Gamma> = dropWhile (\<lambda>Ln. - fst Ln \<notin># eres C D) \<Gamma>"
          proof (rule Cons.IH)
            show "\<forall>K\<in>#eres C D. - K \<in> fst ` set \<Gamma>"
              using Cons.prems True \<open>- fst Ln \<notin># eres C D\<close>
              using image_iff by fastforce
          next
            show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
              using Cons.prems by simp
          qed

          ultimately show ?thesis
            unfolding dropWhile.simps
            unfolding strict_P_Ln_iff
            by simp
        next
          case False

          hence "atm_of (fst Ln) \<preceq>\<^sub>t atm_of L"
            by order

          hence "atm_of (fst Ln) = atm_of L"
            using Cons.prems
            using atm_of_eq_atm_of eres_max_lit linorder_lit.is_maximal_in_mset_iff by fastforce

          hence "L = fst Ln \<or> L = - fst Ln"
            by (metis atm_of_eq_atm_of)

          moreover have "- fst Ln \<notin> fst ` set \<Gamma>"
            using \<open>sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (Ln # \<Gamma>)\<close>
            by fastforce

          moreover have "- L \<in> fst ` (set (Ln # \<Gamma>))"
            using Cons.prems(1) eres_max_lit linorder_lit.is_maximal_in_mset_iff by blast

          ultimately have "- fst Ln \<in># eres C D"
            using eres_max_lit linorder_lit.is_maximal_in_mset_iff by auto

          then show ?thesis
            unfolding dropWhile.simps
            unfolding strict_P_Ln_iff
            using False
            by argo
        qed
      qed
    qed

    hence steps11_skip: "(ord_res_11 N)\<^sup>*\<^sup>*
      (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, Some (eres C D))
      (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, dropWhile strict_P \<Gamma>, Some (eres C D))"
      using rtrancl_ord_res_11_all_skip_steps by metis

    have most_steps11: "(ord_res_11 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, None)
     (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, dropWhile strict_P \<Gamma>, Some (eres C D))"
      using step11_conf steps11_reso steps11_skip by simp

    show ?thesis
    proof (cases "eres C D = {#}")
      case True

      hence "dropWhile strict_P \<Gamma> = []"
        unfolding strict_P_def \<open>eres C D = {#}\<close>
        unfolding linorder_lit.is_maximal_in_mset_iff
        by simp

      have "\<Gamma>' = []"
        unfolding \<open>\<Gamma>' = dropWhile _ \<Gamma>\<close> \<open>eres C D = {#}\<close>
        unfolding linorder_lit.is_maximal_in_mset_iff
        by simp

      show ?thesis
      proof (intro exI conjI)
        show "(constant_context ord_res_11)\<^sup>+\<^sup>+ S11 (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, [], Some {#})"
          unfolding S11_def \<open>\<C> = None\<close>
          using most_steps11[unfolded \<open>dropWhile strict_P \<Gamma> = []\<close> \<open>eres C D = {#}\<close>]
          using tranclp_constant_context by metis

        show "ord_res_10_matches_ord_res_11 S10' (N, U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, [], Some {#})"
          unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = _\<close> \<open>\<Gamma>' = []\<close>
        proof (rule ord_res_10_matches_ord_res_11.intros)
          show "ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0', \<F>, [])"
            using step10 \<open>s10' = _\<close> \<open>\<Gamma>' = []\<close> invars10 ord_res_10_preserves_invars by metis
        next
          show "ord_res_11_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, [], Some {#})"
            using most_steps11 invars11
            unfolding \<open>\<C> = None\<close> \<open>dropWhile strict_P \<Gamma> = []\<close> \<open>eres C D = {#}\<close>
            by (metis tranclp_ord_res_11_preserves_invars)
        next
          show "U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0' |-| {|{#}|}"
            unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>0' = finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> \<open>eres C D = {#}\<close>
            using \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)\<close>
            by force
        next
          show "if {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0') then
            [] = [] \<and> Some {#} = Some {#} else Some {#} = None"
            unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>0' = finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> \<open>eres C D = {#}\<close>
            by simp
        qed
      qed
    next
      case False

      then obtain L where eres_max_lit: "ord_res.is_maximal_lit L (eres C D)"
        using linorder_lit.ex_maximal_in_mset by metis

      hence "L \<in># eres C D"
        unfolding linorder_lit.is_maximal_in_mset_iff by argo

      hence "L \<in># C \<and> L \<noteq> Pos A \<or> L \<in># D \<and> L \<noteq> Neg A"
        using stronger_lit_in_one_of_resolvents_if_in_eres \<open>eres C D \<noteq> D\<close> D_max_lit
        by (metis uminus_Neg)

      hence "L \<prec>\<^sub>l Neg A"
        using C_max_lit D_max_lit
        unfolding linorder_lit.is_greatest_in_mset_iff linorder_lit.is_maximal_in_mset_iff
        by (metis C_max_lit D_max_lit \<open>L \<in># eres C D\<close> eres_lt_if ord_res.asymp_less_lit
            ord_res.less_lit_simps(3,4) ord_res.transp_less_lit in_remove1_mset_neq
            linorder_lit.less_than_maximal_if_multp\<^sub>H\<^sub>O linorder_lit.order.not_eq_order_implies_strict
            literal.disc(2) multp_eq_multp\<^sub>H\<^sub>O uminus_Neg)

      have "dropWhile strict_P \<Gamma> = dropWhile (\<lambda>Ln. atm_of L \<prec>\<^sub>t atm_of (fst Ln)) \<Gamma>"
        unfolding strict_P_def
        using eres_max_lit
        by (metis (no_types) Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

      also have "\<dots> = (- L, None) # dropWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"
      proof -
        have "- L \<noteq> Pos A"
          using \<open>L \<prec>\<^sub>l Neg A\<close> by (cases L) simp_all

        hence "- L \<in> fst ` set \<Gamma>'''"
          using eres_false \<open>L \<in># eres C D\<close>
          unfolding trail_false_cls_def trail_false_lit_def 
          unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close>
          by auto

        hence "(- L, None) \<in> set \<Gamma>'''"
          using \<Gamma>_spec unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close> by auto

        then obtain \<Gamma>\<^sub>0 \<Gamma>\<^sub>1 where "\<Gamma>''' = \<Gamma>\<^sub>1 @ (- L, None) # \<Gamma>\<^sub>0"
          by (meson split_list)

        hence "\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>1 @ (- L, None) # \<Gamma>\<^sub>0"
          unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>'''\<close> by (simp only:)

        have AAA: "\<forall>Ln \<in> set ((Pos A, Some C) # \<Gamma>\<^sub>1). atm_of L \<prec>\<^sub>t atm_of (fst Ln)"
          using \<Gamma>_sorted unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>1 @ (- L, None) # \<Gamma>\<^sub>0\<close>
          by (simp add: sorted_wrt_append)

        hence BBB: "\<forall>Ln \<in> set ((Pos A, Some C) # \<Gamma>\<^sub>1 @ [(- L, None)]). atm_of L \<preceq>\<^sub>t atm_of (fst Ln)"
          by simp

        have "\<forall>Ln \<in> set \<Gamma>\<^sub>0. atm_of (fst Ln) \<prec>\<^sub>t atm_of L"
          using \<Gamma>_sorted unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>1 @ (- L, None) # \<Gamma>\<^sub>0\<close>
          by (simp add: sorted_wrt_append)

        hence CCC: "\<forall>Ln \<in> set \<Gamma>\<^sub>0. \<not> atm_of L \<preceq>\<^sub>t atm_of (fst Ln)"
          using linorder_trm.leD by blast

        have "dropWhile (\<lambda>Ln. atm_of L \<prec>\<^sub>t atm_of (fst Ln)) \<Gamma> = (- L, None) # \<Gamma>\<^sub>0"
          unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>1 @ (- L, None) # \<Gamma>\<^sub>0\<close>
          using dropWhile_append2 AAA by simp

        also have "\<dots> = (- L, None) # dropWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>0"
          using CCC by (simp add: dropWhile_ident_if_pred_always_false)

        also have "\<dots> = (- L, None) # dropWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"
          unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>1 @ (- L, None) # \<Gamma>\<^sub>0\<close>
          using dropWhile_append2 BBB by simp

        finally show ?thesis .
      qed

      also have "\<dots> = (- L, None) # \<Gamma>'"
        unfolding \<open>\<Gamma>' = dropWhile _ \<Gamma>\<close>
        using eres_max_lit
        by (metis (no_types) Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

      finally have "dropWhile strict_P \<Gamma> = (- L, None) # \<Gamma>'" .

      have step10_back: "ord_res_11 N
        (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, dropWhile strict_P \<Gamma>, Some (eres C D))
        (finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
        unfolding \<open>dropWhile strict_P \<Gamma> = (- L, None) # \<Gamma>'\<close>
      proof (rule ord_res_11.backtrack)
        show "(- L, None) # \<Gamma>' = (- L, None) # \<Gamma>'" ..
      next
        show "- (- L) \<in># eres C D"
          unfolding uminus_of_uminus_id
          using eres_max_lit
          unfolding linorder_lit.is_maximal_in_mset_iff by argo
      qed

      hence all_steps11: "(ord_res_11 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>, None)
        (finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
        using most_steps11 by simp

      show ?thesis
      proof (intro exI conjI)
        show "(constant_context ord_res_11)\<^sup>+\<^sup>+ S11 (N, finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
          unfolding S11_def \<open>\<C> = None\<close>
          using all_steps11 tranclp_constant_context by metis

        have "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0')"
          by (smt (verit, del_insts) False \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0)\<close> fimage.rep_eq
              fimageE fimageI finsertE funion_iff iefac_def mempty_in_image_efac_iff step_hyps(5))

        show "ord_res_10_matches_ord_res_11 S10' (N, finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
          unfolding \<open>S10' = (N, s10')\<close> \<open>s10' = _\<close>
        proof (rule ord_res_10_matches_ord_res_11.intros)
          show "ord_res_10_invars N (U\<^sub>e\<^sub>r\<^sub>1\<^sub>0', \<F>, \<Gamma>')"
            using step10 \<open>s10' = _\<close> invars10 ord_res_10_preserves_invars by metis
        next
          show "ord_res_11_invars N (finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>1, \<F>, \<Gamma>', None)"
            using all_steps11 invars11
            unfolding \<open>\<C> = None\<close>
            by (metis tranclp_ord_res_11_preserves_invars)
        next
          show "finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0' |-| {|{#}|}"
            unfolding \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>0' = finsert (eres C D) U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close>
            using \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0')\<close>
            using False \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0\<close> \<open>U\<^sub>e\<^sub>r\<^sub>1\<^sub>1 = U\<^sub>e\<^sub>r\<^sub>1\<^sub>0 |-| {|{#}|}\<close> by auto
        next
          show "if {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0') then
            \<Gamma>' = [] \<and> None = Some {#} else None = None"
            using \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r\<^sub>1\<^sub>0')\<close> by simp
        qed
      qed
    qed
  qed
qed

theorem bisimulation_ord_res_10_ord_res_11:
  defines "match \<equiv> \<lambda>_. ord_res_10_matches_ord_res_11"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_10_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool) \<R>.
    bisimulation
      (constant_context ord_res_10) (constant_context ord_res_11)
      ord_res_8_final ord_res_11_final
      \<R> MATCH"
(* For AFP-devel
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f ord_res_10_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool) \<R>\<^sub>f \<R>\<^sub>b.
    bisimulation
      (constant_context ord_res_10) ord_res_8_final
      (constant_context ord_res_11) ord_res_11_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b"
*)
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique (constant_context ord_res_10)"
    using right_unique_constant_context right_unique_ord_res_10 by metis
next
  show "right_unique (constant_context ord_res_11)"
    using right_unique_constant_context right_unique_ord_res_11 by metis
next
  show "\<forall>S. ord_res_8_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_10 S S')"
    by (metis finished_def ord_res_10_semantics.final_finished)
next
  show "\<forall>S. ord_res_11_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_11 S S')"
    by (metis finished_def ord_res_11_semantics.final_finished)
next
  show "\<forall>i S10 S11. match i S10 S11 \<longrightarrow> ord_res_8_final S10 \<longleftrightarrow> ord_res_11_final S11"
    unfolding match_def
    using ord_res_10_final_iff_ord_res_11_final by metis
next
  show "\<forall>i S10 S11. match i S10 S11 \<longrightarrow>
       safe_state (constant_context ord_res_10) ord_res_8_final S10 \<and>
       safe_state (constant_context ord_res_11) ord_res_11_final S11"
  proof (intro allI impI conjI)
    fix i S10 S11
    assume match: "match i S10 S11"
    show "safe_state (constant_context ord_res_10) ord_res_8_final S10"
      using match[unfolded match_def]
      using ord_res_10_safe_state_if_invars
      unfolding ord_res_10_matches_ord_res_11.simps by auto

    show "safe_state (constant_context ord_res_11) ord_res_11_final S11"
      using match[unfolded match_def]
      using ord_res_11_safe_state_if_invars
      using ord_res_10_matches_ord_res_11.simps by auto
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i S10 S11 S10'. match i S10 S11 \<longrightarrow> constant_context ord_res_10 S10 S10' \<longrightarrow>
    (\<exists>i' S11'. (constant_context ord_res_11)\<^sup>+\<^sup>+ S11 S11' \<and> match i' S10' S11') \<or>
    (\<exists>i'. match i' S10' S11 \<and> False)"
    unfolding match_def
    using forward_simulation_between_10_and_11 by metis
qed

end

lemma forward_simulation_composition:
  assumes
    "forward_simulation step1 step2 final1 final2 order1 match1"
    "forward_simulation step2 step3 final2 final3 order2 match2"
  defines "\<R> \<equiv> \<lambda>i i'. lex_prodp order2\<^sup>+\<^sup>+ order1 (prod.swap i) (prod.swap i')"
  shows "forward_simulation step1 step3 final1 final3 \<R> (rel_comp match1 match2)"
proof intro_locales
  show "semantics step1 final1"
    using assms
    by (auto intro: forward_simulation.axioms)
next
  show "semantics step3 final3"
    using assms
    by (auto intro: forward_simulation.axioms)
next
  have "well_founded order1" "well_founded order2"
    using assms
    by (auto intro: forward_simulation.axioms)

  hence "wfp \<R>"
    unfolding \<R>_def
    by (metis (no_types, lifting) lex_prodp_wfP well_founded.wf wfP_trancl
        wfp_if_convertible_to_wfp)

  thus "well_founded \<R>"
    by unfold_locales
next
  show "forward_simulation_axioms step1 step3 final1 final3 \<R> (rel_comp match1 match2)"
  proof unfold_locales
    fix i s1 s3
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      final: "final1 s1"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    thus "final3 s3"
      using final assms(1,2)[THEN forward_simulation.match_final]
      by simp
  next
    fix i s1 s3 s1'
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      step: "step1 s1 s1'"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and i_def: "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    from forward_simulation.simulation[OF assms(1) \<open>match1 i1 s1 s2\<close> step]
    show "(\<exists>i' s3'. step3\<^sup>+\<^sup>+ s3 s3' \<and> rel_comp match1 match2 i' s1' s3') \<or>
       (\<exists>i'. rel_comp match1 match2 i' s1' s3 \<and> \<R> i' i)"
      (is "(\<exists>i' s1'. ?STEPS i' s1') \<or> (\<exists>i'. ?STALL i')")
    proof (elim disjE exE conjE)
      fix i1' s2'
      assume "step2\<^sup>+\<^sup>+ s2 s2'" and "match1 i1' s1' s2'"
      from forward_simulation.lift_simulation_plus[OF assms(2) \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> \<open>match2 i2 s2 s3\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix i2' s3'
        assume "step3\<^sup>+\<^sup>+ s3 s3'" and "match2 i2' s2' s3'"
        hence "?STEPS (i1', i2') s3'"
          by (auto intro: \<open>match1 i1' s1' s2'\<close> simp: rel_comp_def)
        thus ?thesis by auto
      next
        fix i2''
        assume "match2 i2'' s2' s3" and "order2\<^sup>+\<^sup>+ i2'' i2"
        hence "?STALL (i1', i2'')"
          unfolding rel_comp_def i_def comp_def prod.swap_def prod.sel
        proof (intro conjI)
          show "(match1 i1' OO match2 i2'') s1' s3"
            using \<open>match1 i1' s1' s2'\<close> \<open>match2 i2'' s2' s3\<close>
            by (auto simp add: relcompp_apply)
        next
          show "\<R> (i1', i2'') (i1, i2)"
            unfolding \<R>_def lex_prodp_def prod.swap_def prod.sel
            using \<open>order2\<^sup>+\<^sup>+ i2'' i2\<close> by argo
        qed
        thus ?thesis
          by metis
      qed
    next
      fix i1'
      assume "match1 i1' s1' s2" and "order1 i1' i1"
      hence "?STALL (i1', i2)"
        unfolding rel_comp_def i_def prod.sel
        using \<open>match2 i2 s2 s3\<close> by (auto simp: \<R>_def lex_prodp_def)
      thus ?thesis
        by metis
    qed
  qed
qed

text \<open>For AFP-devel, delete
@{thm Simulation_SCLFOL_ORDRES.forward_simulation_composition}
as it is available in \<^theory>\<open>VeriComp.Simulation\<close>.\<close>

type_synonym bisim_index_1_2 = "nat \<times> nat"
type_synonym bisim_index_1_3 = "bisim_index_1_2 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_4 = "bisim_index_1_3 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_5 = "bisim_index_1_4 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_6 = "bisim_index_1_5 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_7 = "bisim_index_1_6 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_8 = "bisim_index_1_7 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_9 = "bisim_index_1_8 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_10 = "bisim_index_1_9 \<times> (nat \<times> nat)"
type_synonym bisim_index_1_11 = "bisim_index_1_10 \<times> (nat \<times> nat)"

context simulation_SCLFOL_ground_ordered_resolution begin

theorem forward_simulation_ord_res_1_ord_res_11:
  obtains
    MATCH :: "bisim_index_1_11 \<Rightarrow> 'f ord_res_1_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool" and
    \<R> :: "bisim_index_1_11 \<Rightarrow> bisim_index_1_11 \<Rightarrow> bool"
  where
    "forward_simulation
      ord_res_1 (constant_context ord_res_11)
      ord_res_1_final ord_res_11_final
      \<R> MATCH"
proof -
  have bi_to_fwd: "\<exists>MATCH (\<R> :: 'a \<Rightarrow> 'a \<Rightarrow> bool).
    forward_simulation step1 step2 final1 final2 \<R> MATCH"
    if "\<exists>MATCH (\<R> :: 'a \<Rightarrow> 'a \<Rightarrow> bool). bisimulation step1 step2 final1 final2 \<R> MATCH"
    for step1 step2 final1 final2
    using that by (auto intro: bisimulation.axioms)

  show ?thesis
    using that
  using bisimulation_ord_res_1_ord_res_2[THEN bi_to_fwd]
    bisimulation_ord_res_2_ord_res_3[THEN bi_to_fwd]
    bisimulation_ord_res_3_ord_res_4[THEN bi_to_fwd]
    bisimulation_ord_res_4_ord_res_5[THEN bi_to_fwd]
    bisimulation_ord_res_5_ord_res_6[THEN bi_to_fwd]
    bisimulation_ord_res_6_ord_res_7[THEN bi_to_fwd]
    bisimulation_ord_res_7_ord_res_8[THEN bi_to_fwd]
    bisimulation_ord_res_8_ord_res_9[THEN bi_to_fwd]
    bisimulation_ord_res_9_ord_res_10[THEN bi_to_fwd]
    bisimulation_ord_res_10_ord_res_11[THEN bi_to_fwd]
  using forward_simulation_composition by meson
qed

theorem backward_simulation_ord_res_1_ord_res_11:
  obtains
    MATCH :: "bisim_index_1_11 \<Rightarrow> 'f ord_res_1_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool" and
    \<R> :: "bisim_index_1_11 \<Rightarrow> bisim_index_1_11 \<Rightarrow> bool"
  where
    "backward_simulation
      ord_res_1 (constant_context ord_res_11)
      ord_res_1_final ord_res_11_final
      \<R> MATCH"
proof -
  have bi_to_bwd: "\<exists>MATCH (\<R> :: 'a \<Rightarrow> 'a \<Rightarrow> bool).
    backward_simulation step1 step2 final1 final2 \<R> MATCH"
    if "\<exists>MATCH (\<R> :: 'a \<Rightarrow> 'a \<Rightarrow> bool). bisimulation step1 step2 final1 final2 \<R> MATCH"
    for step1 step2 final1 final2
    using that by (auto intro: bisimulation.axioms)

  show ?thesis
    using that
  using bisimulation_ord_res_1_ord_res_2[THEN bi_to_bwd]
    bisimulation_ord_res_2_ord_res_3[THEN bi_to_bwd]
    bisimulation_ord_res_3_ord_res_4[THEN bi_to_bwd]
    bisimulation_ord_res_4_ord_res_5[THEN bi_to_bwd]
    bisimulation_ord_res_5_ord_res_6[THEN bi_to_bwd]
    bisimulation_ord_res_6_ord_res_7[THEN bi_to_bwd]
    bisimulation_ord_res_7_ord_res_8[THEN bi_to_bwd]
    bisimulation_ord_res_8_ord_res_9[THEN bi_to_bwd]
    bisimulation_ord_res_9_ord_res_10[THEN bi_to_bwd]
    bisimulation_ord_res_10_ord_res_11[THEN bi_to_bwd]
  using backward_simulation_composition by meson
qed


(* For AFP-devel, uncomment this theorem; it depends on a changed definition of the locale
bisimulation.

theorem bisimulation_ord_res_1_ord_res_11:
  obtains
    MATCH :: "bisim_index_1_11 \<Rightarrow> 'f ord_res_1_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool" and
    \<R>\<^sub>f \<R>\<^sub>b :: "bisim_index_1_11 \<Rightarrow> bisim_index_1_11 \<Rightarrow> bool"
  where
    "bisimulation
      ord_res_1 ord_res_1_final
      (constant_context ord_res_11) ord_res_11_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b"
  apply atomize_elim
  using bisimulation_ord_res_1_ord_res_2
    bisimulation_ord_res_2_ord_res_3
    bisimulation_ord_res_3_ord_res_4
    bisimulation_ord_res_4_ord_res_5
    bisimulation_ord_res_5_ord_res_6
    bisimulation_ord_res_6_ord_res_7
    bisimulation_ord_res_7_ord_res_8
    bisimulation_ord_res_8_ord_res_9
    bisimulation_ord_res_9_ord_res_10
    bisimulation_ord_res_10_ord_res_11
  using bisimulation_composition by meson

theorem
  obtains
    MATCH :: "bisim_index_1_11 \<Rightarrow> 'f ord_res_1_state \<Rightarrow> 'f ord_res_11_state \<Rightarrow> bool" and
    \<R>\<^sub>f \<R>\<^sub>b :: "bisim_index_1_11 \<Rightarrow> bisim_index_1_11 \<Rightarrow> bool"
  where
    "bisimulation
      ord_res_1 ord_res_1_final
      (constant_context ord_res_11) ord_res_11_final
      MATCH \<R>\<^sub>f \<R>\<^sub>b" and
    "\<And>j S1 S11. MATCH j S1 S11 \<Longrightarrow> ord_res_1_final S1 \<longleftrightarrow> ord_res_11_final S11"
  using bisimulation_ord_res_1_ord_res_11 bisimulation.agree_on_final
  by (metis (no_types, opaque_lifting))
*)


section \<open>ORD-RES-11 is a regular SCL strategy\<close>

definition gtrailelem_of_trailelem where
  "gtrailelem_of_trailelem \<equiv> \<lambda>(L, opt).
    (lit_of_glit L, map_option (\<lambda>C. (cls_of_gcls {#K \<in># C. K \<noteq> L#}, lit_of_glit L, Var)) opt)"

fun state_of_gstate :: "_ \<Rightarrow> ('f, 'v) SCL_FOL.state" where
  "state_of_gstate (U\<^sub>G, _, \<Gamma>\<^sub>G, \<C>\<^sub>G) =
    (let
      \<Gamma> = map gtrailelem_of_trailelem \<Gamma>\<^sub>G;
      U = cls_of_gcls |`| U\<^sub>G;
      \<C> = map_option (\<lambda>C\<^sub>G. (cls_of_gcls C\<^sub>G, Var)) \<C>\<^sub>G
    in (\<Gamma>, U, \<C>))"


lemma fst_case_prod_simp: "fst (case p of (x, y) \<Rightarrow> (f x, g x y)) = f (fst p)"
  by (cases p) simp

lemma trail_false_cls_nonground_iff_trail_false_cls_ground:
  fixes \<Gamma>\<^sub>G and D\<^sub>G :: "'f gclause"
  fixes \<Gamma> :: "('f, 'v) SCL_FOL.trail" and D :: "('f, 'v) term clause"
  defines "\<Gamma> \<equiv> map gtrailelem_of_trailelem \<Gamma>\<^sub>G" and "D \<equiv> cls_of_gcls D\<^sub>G"
  shows "trail_false_cls \<Gamma> D \<longleftrightarrow> trail_false_cls \<Gamma>\<^sub>G D\<^sub>G"
proof -
  have "trail_false_cls \<Gamma> D \<longleftrightarrow> (\<forall>L \<in># D. trail_false_lit \<Gamma> L)"
    unfolding trail_false_cls_def ..
  also have "\<dots> \<longleftrightarrow> (\<forall>L\<^sub>G \<in># D\<^sub>G. trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G))"
    unfolding D_def cls_of_gcls_def by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>L\<^sub>G \<in># D\<^sub>G. trail_false_lit \<Gamma>\<^sub>G L\<^sub>G)"
  proof -
    have "trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G) \<longleftrightarrow> trail_false_lit \<Gamma>\<^sub>G L\<^sub>G"
      for L\<^sub>G :: "'f gterm literal"
    proof -
      have "trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G) \<longleftrightarrow> - lit_of_glit L\<^sub>G \<in> fst ` set \<Gamma>"
        unfolding trail_false_lit_def ..
      also have "\<dots> \<longleftrightarrow>
        - (lit_of_glit L\<^sub>G :: ('f, 'v) term literal) \<in> set (map (\<lambda>x. lit_of_glit (fst x)) \<Gamma>\<^sub>G)"
        unfolding \<Gamma>_def image_set list.map_comp
        unfolding gtrailelem_of_trailelem_def
        unfolding list.map_comp
        unfolding comp_def fst_case_prod_simp ..
      also have "\<dots> \<longleftrightarrow> (lit_of_glit (- L\<^sub>G) :: ('f, 'v) term literal) \<in> lit_of_glit ` fst ` set \<Gamma>\<^sub>G"
        by (cases L\<^sub>G) (auto simp: lit_of_glit_def)
      also have "\<dots> \<longleftrightarrow> - L\<^sub>G \<in> fst ` set \<Gamma>\<^sub>G"
        using inj_image_mem_iff inj_lit_of_glit by metis
      also have "\<dots> \<longleftrightarrow> trail_false_lit \<Gamma>\<^sub>G L\<^sub>G"
        unfolding trail_false_lit_def ..
      finally show "trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G) = trail_false_lit \<Gamma>\<^sub>G L\<^sub>G" .
    qed
    thus ?thesis by metis
  qed
  also have "\<dots> \<longleftrightarrow> trail_false_cls \<Gamma>\<^sub>G D\<^sub>G"
    unfolding trail_false_cls_def ..
  finally show ?thesis .
qed

theorem ord_res_11_is_strategy_for_regular_scl:
  fixes
    N\<^sub>G :: "'f gclause fset" and
    N :: "('f, 'v) term clause fset" and
    \<beta>\<^sub>G :: "'f gterm" and
    \<beta> :: "('f, 'v) term" and
    S\<^sub>G S\<^sub>G' :: "'f gclause fset \<times> 'f gclause fset \<times> ('f gliteral \<times> 'f gclause option) list \<times> 'f gclause option" and
    S S' :: "('f, 'v) SCL_FOL.state"
  defines
    "N \<equiv> cls_of_gcls |`| N\<^sub>G" and
    "\<beta> \<equiv> term_of_gterm \<beta>\<^sub>G" and
    "S \<equiv> state_of_gstate S\<^sub>G" and
    "S' \<equiv> state_of_gstate S\<^sub>G'"
  assumes
    ball_le_\<beta>\<^sub>G: "\<forall>A\<^sub>G |\<in>| atms_of_clss N\<^sub>G. A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G" and
    run: "(ord_res_11 N\<^sub>G)\<^sup>*\<^sup>* ({||}, {||}, [], None) S\<^sub>G" and
    step: "ord_res_11 N\<^sub>G S\<^sub>G S\<^sub>G'"
  shows
    "scl_fol.regular_scl N \<beta> S S'"
proof -
  have "ord_res_11_invars N\<^sub>G ({||}, {||}, [], None)"
    using ord_res_11_invars_initial_state .

  hence "ord_res_11_invars N\<^sub>G S\<^sub>G"
    using run rtranclp_ord_res_11_preserves_invars by metis

  obtain U\<^sub>G \<F> \<Gamma>\<^sub>G \<C>\<^sub>G where S\<^sub>G_def: "S\<^sub>G = (U\<^sub>G, \<F>, \<Gamma>\<^sub>G, \<C>\<^sub>G)"
    by (metis surj_pair)

  obtain \<Gamma> U \<C> where S_def: "S = (\<Gamma>, U, \<C>)"
    by (metis surj_pair)

  have \<Gamma>_def: "\<Gamma> = map gtrailelem_of_trailelem \<Gamma>\<^sub>G"
    using S_def S\<^sub>G_def \<open>S \<equiv> state_of_gstate S\<^sub>G\<close> by simp

  have U_def: "U = cls_of_gcls |`| U\<^sub>G"
    using S_def S\<^sub>G_def \<open>S \<equiv> state_of_gstate S\<^sub>G\<close> by simp

  have \<C>_def: "\<C> = map_option (\<lambda>C\<^sub>G. (cls_of_gcls C\<^sub>G, Var)) \<C>\<^sub>G"
    using S_def S\<^sub>G_def \<open>S \<equiv> state_of_gstate S\<^sub>G\<close> by simp

  obtain \<F>' U\<^sub>G' :: "'f gclause fset" and \<Gamma>\<^sub>G' :: "_ list" and \<C>\<^sub>G' :: "_ option" where
    S\<^sub>G'_def: "S\<^sub>G' = (U\<^sub>G', \<F>', \<Gamma>\<^sub>G', \<C>\<^sub>G')"
    by (metis surj_pair)

  obtain \<Gamma>' :: "_ list" and U' :: "_ fset" and \<C>' :: "_ option" where
    S'_def: "S' = (\<Gamma>', U', \<C>')"
    by (metis surj_pair)

  have \<Gamma>'_def: "\<Gamma>' = map gtrailelem_of_trailelem \<Gamma>\<^sub>G'"
    using S'_def S\<^sub>G'_def \<open>S' \<equiv> state_of_gstate S\<^sub>G'\<close> by simp

  have U'_def: "U' = cls_of_gcls |`| U\<^sub>G'"
    using S'_def S\<^sub>G'_def \<open>S' \<equiv> state_of_gstate S\<^sub>G'\<close> by simp

  have \<C>'_def: "\<C>' = map_option (\<lambda>C\<^sub>G. (cls_of_gcls C\<^sub>G, Var)) \<C>\<^sub>G'"
    using S'_def S\<^sub>G'_def \<open>S' \<equiv> state_of_gstate S\<^sub>G'\<close> by simp

  have "atms_of_clss U\<^sub>G |\<subseteq>| atms_of_clss N\<^sub>G"
    using \<open>ord_res_11_invars N\<^sub>G S\<^sub>G\<close>[unfolded S\<^sub>G_def]
    unfolding ord_res_11_invars.simps by simp

  have "atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G) = atms_of_clss N\<^sub>G |\<union>| atms_of_clss U\<^sub>G"
    by (simp add: atms_of_clss_def fimage_funion)

  also have "\<dots> = atms_of_clss N\<^sub>G"
    using \<open>atms_of_clss U\<^sub>G |\<subseteq>| atms_of_clss N\<^sub>G\<close> by auto

  finally have "atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G) = atms_of_clss N\<^sub>G" .

  have clauses_in_\<F>_have_pos_max_lit: "\<forall>C|\<in>|\<F>. \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
    using \<open>ord_res_11_invars N\<^sub>G S\<^sub>G\<close>[unfolded S\<^sub>G_def ord_res_11_invars.simps]
    by simp

  have nex_conflict_if_nbex_trail_false:
    "\<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G) \<Longrightarrow> \<not> Ex (scl_fol.conflict N \<beta> S)"
  proof (elim contrapos_nn exE)
    fix x :: "('f, 'v) state"
    assume "scl_fol.conflict N \<beta> S x"
    hence "fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)"
      unfolding S_def
    proof (cases N \<beta> "(\<Gamma>, U, \<C>)" x rule: scl_fol.conflict.cases)
      case (conflictI D \<gamma>)

      obtain D\<^sub>G where "D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and D_def: "D = cls_of_gcls D\<^sub>G"
        using \<open>D |\<in>| N |\<union>| U\<close>
        unfolding N_def U_def by blast

      moreover have "trail_false_cls \<Gamma>\<^sub>G D\<^sub>G"
      proof -
        have "is_ground_cls D"
          using \<open>D = cls_of_gcls D\<^sub>G\<close> by simp
        hence "D \<cdot> \<gamma> = D"
          by simp
        hence "trail_false_cls \<Gamma> D"
          using conflictI
          unfolding SCL_FOL.trail_false_cls_def trail_false_cls_def
          unfolding SCL_FOL.trail_false_lit_def trail_false_lit_def
          by argo

        thus ?thesis
          unfolding \<Gamma>_def D_def
          unfolding trail_false_cls_nonground_iff_trail_false_cls_ground .
      qed
      ultimately show ?thesis by metis
    qed

    thus "fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G)"
      unfolding bex_trail_false_cls_simp .
  qed

  have nex_conflict_if_alread_in_conflict: "\<C>\<^sub>G = Some C\<^sub>G \<Longrightarrow> \<not> Ex (scl_fol.conflict N \<beta> S)" for C\<^sub>G
    unfolding S_def \<C>_def by (simp add: scl_fol.conflict.simps)

  have nex_conflict_if_no_clause_could_propagate_comp:
    "\<not> Ex (scl_fol.conflict N \<beta> ((lit_of_glit L\<^sub>G, None) # \<Gamma>, U, \<C>))"
    if
      nex_false_clause_wrt_\<Gamma>\<^sub>G: "\<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G)" and
      ball_lt_atm_L\<^sub>G: "\<forall>x |\<in>| trail_atms \<Gamma>\<^sub>G. x \<prec>\<^sub>t atm_of L\<^sub>G" and
      nex_clause_that_propagate: "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G).
        clause_could_propagate \<Gamma>\<^sub>G C (- L\<^sub>G))"
    for L\<^sub>G
  proof (intro notI, elim exE)
    fix S'' :: "('f, 'v) SCL_FOL.state"
    assume "scl_fol.conflict N \<beta> ((lit_of_glit L\<^sub>G, None) # \<Gamma>, U, \<C>) S''"
    thus "False"
    proof (cases N \<beta> "((lit_of_glit L\<^sub>G, None) # \<Gamma>, U, \<C>)" S'' rule: scl_fol.conflict.cases)
      case (conflictI D \<gamma>)

      obtain D\<^sub>G where "D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and D_def: "D = cls_of_gcls D\<^sub>G"
        using \<open>D |\<in>| N |\<union>| U\<close> N_def U_def by blast

      have "(lit_of_glit L\<^sub>G :: ('f, 'v) term literal, None) # \<Gamma> =
        (map gtrailelem_of_trailelem ((L\<^sub>G, None) # \<Gamma>\<^sub>G) :: ('f, 'v) SCL_FOL.trail)"
        by (simp add: \<Gamma>_def gtrailelem_of_trailelem_def)

      moreover have "D \<cdot> \<gamma> = cls_of_gcls D\<^sub>G"
        unfolding D_def by simp

      ultimately have "trail_false_cls
        (map gtrailelem_of_trailelem ((L\<^sub>G, None) # \<Gamma>\<^sub>G) :: ('f, 'v) SCL_FOL.trail) (cls_of_gcls D\<^sub>G)"
        using \<open>SCL_FOL.trail_false_cls ((lit_of_glit L\<^sub>G, None) # \<Gamma>) (D \<cdot> \<gamma>)\<close>
        unfolding SCL_FOL.trail_false_cls_def trail_false_cls_def
        unfolding SCL_FOL.trail_false_lit_def trail_false_lit_def
        by metis

      hence "trail_false_cls ((L\<^sub>G, None) # \<Gamma>\<^sub>G) D\<^sub>G"
        using trail_false_cls_nonground_iff_trail_false_cls_ground by blast

      hence "trail_false_cls \<Gamma>\<^sub>G {#K\<^sub>G \<in># D\<^sub>G. K\<^sub>G \<noteq> - L\<^sub>G#}"
        unfolding trail_false_cls_def trail_false_lit_def
        by auto

      moreover have "ord_res.is_maximal_lit (- L\<^sub>G) D\<^sub>G"
        unfolding linorder_lit.is_maximal_in_mset_iff
      proof (intro conjI ballI impI)
        show "- L\<^sub>G \<in># D\<^sub>G"
          using \<open>D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close> \<open>trail_false_cls ((L\<^sub>G, None) # \<Gamma>\<^sub>G) D\<^sub>G\<close> subtrail_falseI
            nex_false_clause_wrt_\<Gamma>\<^sub>G
          unfolding bex_trail_false_cls_simp
          by blast
      next
        fix K\<^sub>G assume "K\<^sub>G \<in># D\<^sub>G" and "K\<^sub>G \<noteq> - L\<^sub>G"
        hence "trail_false_lit \<Gamma>\<^sub>G K\<^sub>G"
          using \<open>trail_false_cls \<Gamma>\<^sub>G {#K\<^sub>G \<in># D\<^sub>G. K\<^sub>G \<noteq> - L\<^sub>G#}\<close>
          unfolding trail_false_cls_def by simp
        hence "trail_defined_lit \<Gamma>\<^sub>G K\<^sub>G"
          by (simp add: trail_defined_lit_iff_true_or_false)
        hence "atm_of K\<^sub>G |\<in>| trail_atms \<Gamma>\<^sub>G"
          unfolding trail_defined_lit_iff_trail_defined_atm .
        hence "atm_of K\<^sub>G \<prec>\<^sub>t atm_of L\<^sub>G"
          using ball_lt_atm_L\<^sub>G by metis
        hence "K\<^sub>G \<prec>\<^sub>l - L\<^sub>G"
          by (cases L\<^sub>G; cases K\<^sub>G) simp_all
        thus "\<not> - L\<^sub>G \<prec>\<^sub>l K\<^sub>G"
          by order
      qed

      moreover have "\<not> trail_defined_lit \<Gamma>\<^sub>G (- L\<^sub>G)"
        by (metis atm_of_uminus linorder_trm.less_irrefl that(2)
            trail_defined_lit_iff_trail_defined_atm)

      ultimately have "clause_could_propagate \<Gamma>\<^sub>G D\<^sub>G (- L\<^sub>G)"
        unfolding clause_could_propagate_def by argo

      hence "\<exists>C|\<in>| N\<^sub>G |\<union>| U\<^sub>G. clause_could_propagate \<Gamma>\<^sub>G C (- L\<^sub>G)"
        using \<open>D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close> by metis

      hence False
         using nex_clause_that_propagate
         unfolding bex_clause_could_propagate_simp
         by contradiction

      thus ?thesis .
    qed
  qed

  show ?thesis
    using step unfolding S\<^sub>G_def S\<^sub>G'_def
  proof (cases N\<^sub>G "(U\<^sub>G, \<F>, \<Gamma>\<^sub>G, \<C>\<^sub>G)" "(U\<^sub>G', \<F>', \<Gamma>\<^sub>G', \<C>\<^sub>G')" rule: ord_res_11.cases)
    case step_hyps: (decide_neg A\<^sub>G)

    define A :: "('f, 'v) term" where
      "A = term_of_gterm A\<^sub>G"

    let ?f = "gtrailelem_of_trailelem"
    have "\<Gamma>' = map ?f \<Gamma>\<^sub>G'"
      unfolding \<Gamma>'_def ..
    also have "\<dots> = map ?f ((Neg A\<^sub>G, None) # \<Gamma>\<^sub>G)"
      unfolding \<open>\<Gamma>\<^sub>G' = (Neg A\<^sub>G, None) # \<Gamma>\<^sub>G\<close> ..
    also have "\<dots> = ?f (Neg A\<^sub>G, None) # map ?f \<Gamma>\<^sub>G"
      unfolding list.map ..
    also have "\<dots> = ?f (Neg A\<^sub>G, None) # \<Gamma>"
      unfolding \<Gamma>_def ..
    also have "\<dots> = (lit_of_glit (Neg A\<^sub>G), None) # \<Gamma>"
      unfolding gtrailelem_of_trailelem_def prod.case option.map ..
    also have "\<dots> = (Neg (term_of_gterm A\<^sub>G), None) # \<Gamma>"
      unfolding lit_of_glit_def literal.map ..
    also have "\<dots> = (Neg A, None) # \<Gamma>"
      unfolding A_def ..
    finally have "\<Gamma>' = decide_lit (Neg A) # \<Gamma>"
      unfolding decide_lit_def .

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G)\<close> nex_conflict_if_nbex_trail_false
      by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.decide N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = None\<close> option.map
      proof (rule scl_fol.decideI')
        show "is_ground_lit (Neg A \<cdot>l Var)"
          by (simp add: A_def)
      next
        have "\<forall>x |\<in>| trail_atms \<Gamma>\<^sub>G. x \<prec>\<^sub>t A\<^sub>G"
          using step_hyps linorder_trm.is_least_in_ffilter_iff by simp
        hence "A\<^sub>G |\<notin>| trail_atms \<Gamma>\<^sub>G"
          by blast
        hence "A\<^sub>G \<notin> atm_of ` fst ` set \<Gamma>\<^sub>G"
          unfolding fset_trail_atms .
        hence "term_of_gterm A\<^sub>G \<notin> term_of_gterm ` atm_of ` fst ` set \<Gamma>\<^sub>G"
          using inj_image_mem_iff inj_term_of_gterm by metis
        hence "term_of_gterm A\<^sub>G \<notin> set (map (\<lambda>x. term_of_gterm (atm_of (fst x))) \<Gamma>\<^sub>G)"
          unfolding image_set list.map_comp comp_def .
        hence "A \<notin> set (map (\<lambda>x. atm_of (lit_of_glit (fst x))) \<Gamma>\<^sub>G)"
          unfolding A_def atm_of_lit_of_glit_conv .
        hence "A \<notin> atm_of ` fst ` set \<Gamma>"
          unfolding image_set list.map_comp comp_def \<Gamma>_def gtrailelem_of_trailelem_def
            fst_case_prod_simp .
        hence "A |\<notin>| trail_atms \<Gamma>"
          unfolding fset_trail_atms .
        hence "\<not> trail_defined_lit \<Gamma> (Neg A \<cdot>l Var)"
          by (simp add: trail_defined_lit_iff_trail_defined_atm)
        thus "\<not> SCL_FOL.trail_defined_lit \<Gamma> (Neg A \<cdot>l Var)"
          by (simp add: SCL_FOL.trail_defined_lit_def trail_defined_lit_def)
      next
        have "A\<^sub>G |\<in>| atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G)"
          using step_hyps linorder_trm.is_least_in_ffilter_iff by blast
        hence "A\<^sub>G |\<in>| atms_of_clss N\<^sub>G"
          unfolding \<open>atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G) = atms_of_clss N\<^sub>G\<close> .
        hence "A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G"
          using ball_le_\<beta>\<^sub>G by metis
        moreover have "gterm_of_term A = A\<^sub>G"
          by (simp add: A_def)
        moreover have "gterm_of_term \<beta> = \<beta>\<^sub>G"
          by (simp add: \<beta>_def)
        ultimately have "gterm_of_term A \<preceq>\<^sub>t gterm_of_term \<beta>"
          by argo
        thus "less_B\<^sup>=\<^sup>= (atm_of (Neg A) \<cdot>a Var) \<beta>"
          using inj_term_of_gterm[THEN injD]
          by (auto simp: less_B_def A_def \<beta>_def)
      next
        show "\<Gamma>' = trail_decide \<Gamma> (Neg A \<cdot>l Var)"
          using \<open>\<Gamma>' = decide_lit (Neg A) # \<Gamma>\<close>
          unfolding subst_lit_id_subst .
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"

      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
      proof -
        have "\<not> Ex (scl_fol.conflict N \<beta> ((lit_of_glit (Neg A\<^sub>G), None) # \<Gamma>, U, \<C>))"
        proof (rule nex_conflict_if_no_clause_could_propagate_comp)
          show "\<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G)"
            using step_hyps by argo
        next
          show "\<forall>x |\<in>| trail_atms \<Gamma>\<^sub>G. x \<prec>\<^sub>t atm_of (Neg A\<^sub>G)"
            unfolding literal.sel
            using step_hyps linorder_trm.is_least_in_fset_iff by simp
        next
          show "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G). clause_could_propagate \<Gamma>\<^sub>G C (- Neg A\<^sub>G))"
            using step_hyps by simp
        qed
        moreover have "lit_of_glit (Neg A\<^sub>G) = Neg A"
          unfolding A_def lit_of_glit_def literal.map ..
        ultimately show ?thesis
          unfolding S'_def \<open>\<Gamma>' = decide_lit (Neg A) # \<Gamma>\<close> decide_lit_def
          using \<C>'_def \<C>_def \<open>U' = U\<close> step_hyps(1,4) by argo
      qed

      ultimately show False
        by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (decide_pos A\<^sub>G)

    define A :: "('f, 'v) term" where
      "A = term_of_gterm A\<^sub>G"

    let ?f = "gtrailelem_of_trailelem"
    have "\<Gamma>' = map ?f \<Gamma>\<^sub>G'"
      unfolding \<Gamma>'_def ..
    also have "\<dots> = map ?f ((Pos A\<^sub>G, None) # \<Gamma>\<^sub>G)"
      unfolding \<open>\<Gamma>\<^sub>G' = (Pos A\<^sub>G, None) # \<Gamma>\<^sub>G\<close> ..
    also have "\<dots> = ?f (Pos A\<^sub>G, None) # map ?f \<Gamma>\<^sub>G"
      unfolding list.map ..
    also have "\<dots> = ?f (Pos A\<^sub>G, None) # \<Gamma>"
      unfolding \<Gamma>_def ..
    also have "\<dots> = (lit_of_glit (Pos A\<^sub>G), None) # \<Gamma>"
      unfolding prod.case option.map gtrailelem_of_trailelem_def ..
    also have "\<dots> = (Pos (term_of_gterm A\<^sub>G), None) # \<Gamma>"
      unfolding lit_of_glit_def literal.map ..
    also have "\<dots> = (Pos A, None) # \<Gamma>"
      unfolding A_def ..
    finally have "\<Gamma>' = decide_lit (Pos A) # \<Gamma>"
      unfolding decide_lit_def .

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using step_hyps nex_conflict_if_nbex_trail_false by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.decide N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = None\<close> option.map
      proof (rule scl_fol.decideI')
        show "is_ground_lit (Pos A \<cdot>l Var)"
          by (simp add: A_def)
      next
        have "\<forall>x |\<in>| trail_atms \<Gamma>\<^sub>G. x \<prec>\<^sub>t A\<^sub>G"
          using step_hyps linorder_trm.is_least_in_ffilter_iff by simp
        hence "A\<^sub>G |\<notin>| trail_atms \<Gamma>\<^sub>G"
          by blast
        hence "A\<^sub>G \<notin> atm_of ` fst ` set \<Gamma>\<^sub>G"
          unfolding fset_trail_atms .
        hence "term_of_gterm A\<^sub>G \<notin> term_of_gterm ` atm_of ` fst ` set \<Gamma>\<^sub>G"
          using inj_image_mem_iff inj_term_of_gterm by metis
        hence "term_of_gterm A\<^sub>G \<notin> set (map (\<lambda>x. term_of_gterm (atm_of (fst x))) \<Gamma>\<^sub>G)"
          unfolding image_set list.map_comp comp_def .
        hence "A \<notin> set (map (\<lambda>x. atm_of (lit_of_glit (fst x))) \<Gamma>\<^sub>G)"
          unfolding A_def atm_of_lit_of_glit_conv .
        hence "A \<notin> atm_of ` fst ` set \<Gamma>"
          unfolding image_set list.map_comp comp_def \<Gamma>_def gtrailelem_of_trailelem_def
            fst_case_prod_simp .
        hence "A |\<notin>| trail_atms \<Gamma>"
          unfolding fset_trail_atms .
        hence "\<not> trail_defined_lit \<Gamma> (Pos A \<cdot>l Var)"
          by (simp add: trail_defined_lit_iff_trail_defined_atm)
        thus "\<not> SCL_FOL.trail_defined_lit \<Gamma> (Pos A \<cdot>l Var)"
          by (simp add: SCL_FOL.trail_defined_lit_def trail_defined_lit_def)
      next
        have "A\<^sub>G |\<in>| atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G)"
          using step_hyps linorder_trm.is_least_in_ffilter_iff by simp
        hence "A\<^sub>G |\<in>| atms_of_clss N\<^sub>G"
          unfolding \<open>atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G) = atms_of_clss N\<^sub>G\<close> .
        hence "A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G"
          using ball_le_\<beta>\<^sub>G by metis
        moreover have "gterm_of_term A = A\<^sub>G"
          by (simp add: A_def)
        moreover have "gterm_of_term \<beta> = \<beta>\<^sub>G"
          by (simp add: \<beta>_def)
        ultimately have "gterm_of_term A \<preceq>\<^sub>t gterm_of_term \<beta>"
          by argo
        thus "less_B\<^sup>=\<^sup>= (atm_of (Pos A) \<cdot>a Var) \<beta>"
          using inj_term_of_gterm[THEN injD]
          by (auto simp: less_B_def A_def \<beta>_def)
      next
        show "\<Gamma>' = trail_decide \<Gamma> (Pos A \<cdot>l Var)"
          using \<open>\<Gamma>' = decide_lit (Pos A) # \<Gamma>\<close>
          unfolding subst_lit_id_subst .
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"
      
      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
      proof -
        have "\<not> Ex (scl_fol.conflict N \<beta> ((lit_of_glit (Pos A\<^sub>G), None) # \<Gamma>, U, \<C>))"
        proof (rule nex_conflict_if_no_clause_could_propagate_comp)
          show "\<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G)"
            using step_hyps by argo
        next
          show "\<forall>x|\<in>| trail_atms \<Gamma>\<^sub>G. x \<prec>\<^sub>t atm_of (Pos A\<^sub>G)"
            unfolding literal.sel
            using step_hyps linorder_trm.is_least_in_ffilter_iff by simp
        next
          have "clause_could_propagate \<Gamma>\<^sub>G C (Neg A\<^sub>G) \<Longrightarrow> trail_false_cls \<Gamma>\<^sub>G' C" for C
            unfolding \<open>\<Gamma>\<^sub>G' = (Pos A\<^sub>G, None) # \<Gamma>\<^sub>G\<close>
            using trail_false_if_could_have_propagatated by fastforce

          thus "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G). clause_could_propagate \<Gamma>\<^sub>G C (- Pos A\<^sub>G))"
            unfolding uminus_Pos
            using step_hyps by metis
        qed
        moreover have "lit_of_glit (Pos A\<^sub>G) = Pos A"
          unfolding A_def lit_of_glit_def literal.map ..
        ultimately show ?thesis
          unfolding S'_def \<open>\<Gamma>' = decide_lit (Pos A) # \<Gamma>\<close> decide_lit_def
          using \<C>'_def \<C>_def \<open>U' = U\<close> step_hyps(1) step_hyps(3) by argo
      qed

      ultimately show False by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (propagate A\<^sub>G C\<^sub>G)

    have "C\<^sub>G |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)" and C\<^sub>G_prop: "clause_could_propagate \<Gamma>\<^sub>G C\<^sub>G (Pos A\<^sub>G)"
      using step_hyps linorder_cls.is_least_in_fset_iff by simp_all

    define A :: "('f, 'v) term" where
      "A = term_of_gterm A\<^sub>G"

    define C :: "('f, 'v) term clause" where
      "C = cls_of_gcls C\<^sub>G"

    have "ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G" and "trail_false_cls \<Gamma>\<^sub>G {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}"
      using \<open>clause_could_propagate \<Gamma>\<^sub>G C\<^sub>G (Pos A\<^sub>G)\<close>
      unfolding clause_could_propagate_def by metis+

    then obtain C\<^sub>G' where "C\<^sub>G = add_mset (Pos A\<^sub>G) C\<^sub>G'"
      by (metis linorder_lit.is_maximal_in_mset_iff mset_add)

    define C' :: "('f, 'v) term clause" where
      "C' = cls_of_gcls C\<^sub>G'"

    let ?f = "gtrailelem_of_trailelem"
    have "\<Gamma>' = map ?f \<Gamma>\<^sub>G'"
      unfolding \<Gamma>'_def ..
    also have "\<dots> = map ?f ((Pos A\<^sub>G, Some (efac C\<^sub>G)) # \<Gamma>\<^sub>G)"
      unfolding \<open>\<Gamma>\<^sub>G' = (Pos A\<^sub>G, Some _) # \<Gamma>\<^sub>G\<close> ..
    also have "\<dots> = ?f (Pos A\<^sub>G, Some (efac C\<^sub>G)) # map ?f \<Gamma>\<^sub>G"
      unfolding list.map ..
    also have "\<dots> = ?f (Pos A\<^sub>G, Some (efac C\<^sub>G)) # \<Gamma>"
      unfolding \<Gamma>_def ..
    also have "\<dots> = (lit_of_glit (Pos A\<^sub>G),
      Some (cls_of_gcls {#K \<in># efac C\<^sub>G. K \<noteq> Pos A\<^sub>G#}, lit_of_glit (Pos A\<^sub>G), Var)) # \<Gamma>"
      unfolding gtrailelem_of_trailelem_def prod.case option.map ..
    also have "\<dots> = (lit_of_glit (Pos A\<^sub>G),
      Some (cls_of_gcls {#K \<in># add_mset (Pos A\<^sub>G) {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}. K \<noteq> Pos A\<^sub>G#},
        lit_of_glit (Pos A\<^sub>G), Var)) # \<Gamma>"
    proof -
      have "is_pos (Pos A\<^sub>G)"
        by simp

      moreover have "linorder_lit.is_maximal_in_mset C\<^sub>G (Pos A\<^sub>G)"
        using C\<^sub>G_prop unfolding clause_could_propagate_def by argo

      ultimately show ?thesis
        using efac_spec_if_pos_lit_is_maximal by metis
    qed
    also have "\<dots> = (lit_of_glit (Pos A\<^sub>G),
      Some (cls_of_gcls {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}, lit_of_glit (Pos A\<^sub>G), Var)) # \<Gamma>"
      by (simp add: filter_filter_mset)
    also have "\<dots> = (Pos A, Some (cls_of_gcls {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}, Pos A, Var)) # \<Gamma>"
      by (simp add: A_def lit_of_glit_def)
    also have "\<dots> = (Pos A, Some (cls_of_gcls {#L \<in># C\<^sub>G. lit_of_glit L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      by (metis A_def glit_of_lit_lit_of_glit lit_of_glit_def literal.simps(9))
    also have "\<dots> = (Pos A, Some ({#L \<in># cls_of_gcls C\<^sub>G. L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      unfolding cls_of_gcls_def
      unfolding image_mset_filter_mset_swap[of "lit_of_glit" "\<lambda>L. L \<noteq> Pos A" C\<^sub>G]
      unfolding cls_of_gcls_def[symmetric] ..
    also have "\<dots> = (Pos A \<cdot>l Var, Some ({#L \<in># cls_of_gcls C\<^sub>G. L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      by simp
    also have "\<dots> = (Pos A \<cdot>l Var, Some ({#L \<in># C. L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      unfolding C_def ..
    finally have "\<Gamma>' = propagate_lit (Pos A) {#L \<in># C. L \<noteq> Pos A#} Var # \<Gamma>"
      unfolding propagate_lit_def .

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    obtain C\<^sub>G\<^sub>0 where "C\<^sub>G\<^sub>0 |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and "C\<^sub>G = iefac \<F> C\<^sub>G\<^sub>0"
      using \<open>C\<^sub>G |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)\<close> by blast

    define C\<^sub>0 :: "('f, 'v) term clause" where
      "C\<^sub>0 = cls_of_gcls C\<^sub>G\<^sub>0"

    have "ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<^sub>0"
      using \<open>ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<close> \<open>C\<^sub>G = iefac \<F> C\<^sub>G\<^sub>0\<close>
      by (metis iefac_def linorder_lit.is_maximal_in_mset_iff set_mset_efac)

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using step_hyps nex_conflict_if_nbex_trail_false by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.propagate N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = None\<close> option.map
      proof (rule scl_fol.propagateI')
        show "C\<^sub>0 |\<in>| N |\<union>| U"
          unfolding C\<^sub>0_def N_def U_def
          using \<open>C\<^sub>G\<^sub>0 |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close>
          by blast
      next
        show "is_ground_cls (C\<^sub>0 \<cdot> Var)"
          by (simp add: C\<^sub>0_def)

        have "Pos A \<in># C\<^sub>0"
          unfolding A_def C\<^sub>0_def
          by (metis (no_types, lifting) \<open>C\<^sub>G = iefac \<F> C\<^sub>G\<^sub>0\<close> \<open>ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<close>
              cls_of_gcls_def iefac_def image_eqI linorder_lit.is_maximal_in_mset_iff
              lit_of_glit_def literal.map(1) multiset.set_map set_mset_efac)

        then show "C\<^sub>0 = add_mset (Pos A) (C\<^sub>0 - {#Pos A#})"
          by simp

        have "A\<^sub>G |\<in>| atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G)"
          using step_hyps linorder_trm.is_least_in_ffilter_iff by simp
        hence "A\<^sub>G |\<in>| atms_of_clss N\<^sub>G"
          unfolding \<open>atms_of_clss (N\<^sub>G |\<union>| U\<^sub>G) = atms_of_clss N\<^sub>G\<close> .
        hence "A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G"
          using ball_le_\<beta>\<^sub>G by metis
        moreover have "gterm_of_term A = A\<^sub>G"
          by (simp add: A_def)
        moreover have "gterm_of_term \<beta> = \<beta>\<^sub>G"
          by (simp add: \<beta>_def)
        ultimately have "gterm_of_term A \<preceq>\<^sub>t gterm_of_term \<beta>"
          by argo
        hence "less_B\<^sup>=\<^sup>= A \<beta>"
          by (auto simp: less_B_def A_def \<beta>_def)

        show "\<forall>K \<in># C\<^sub>0 \<cdot> Var. less_B\<^sup>=\<^sup>= (atm_of K) \<beta>"
          unfolding subst_cls_id_subst
        proof (intro ballI)
          fix K :: "('f, 'v) Term.term literal"
          assume "K \<in># C\<^sub>0"
          then obtain K\<^sub>G where "K\<^sub>G \<in># C\<^sub>G\<^sub>0" and K_def: "K = lit_of_glit K\<^sub>G"
            unfolding C\<^sub>0_def cls_of_gcls_def by blast

          have "K\<^sub>G \<preceq>\<^sub>l Pos A\<^sub>G"
            using \<open>ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<^sub>0\<close> \<open>K\<^sub>G \<in># C\<^sub>G\<^sub>0\<close>
            unfolding linorder_lit.is_maximal_in_mset_iff by fastforce

          hence "atm_of K\<^sub>G \<preceq>\<^sub>t A\<^sub>G"
            by (metis literal.collapse(1) literal.collapse(2) literal.sel(1)
                ord_res.less_lit_simps(1) ord_res.less_lit_simps(4) reflclp_iff)

          hence "less_B\<^sup>=\<^sup>= (atm_of K) A"
            by (auto simp: less_B_def K_def A_def atm_of_lit_of_glit_conv)

          then show "less_B\<^sup>=\<^sup>= (atm_of K) \<beta>"
            using \<open>less_B\<^sup>=\<^sup>= A \<beta>\<close> by order
        qed

        show "{#K \<in># C\<^sub>0. K \<noteq> Pos A#} = {#K \<in># remove1_mset (Pos A) C\<^sub>0. K \<cdot>l Var \<noteq> Pos A \<cdot>l Var#}"
          by simp

        show "{#K \<in># remove1_mset (Pos A) C\<^sub>0. K = Pos A#} =
          {#K \<in># remove1_mset (Pos A) C\<^sub>0. K \<cdot>l Var = Pos A \<cdot>l Var#}"
          by simp

        have "trail_false_cls \<Gamma>\<^sub>G ({#K\<^sub>G \<in># C\<^sub>G\<^sub>0. K\<^sub>G \<noteq> Pos A\<^sub>G#})"
          by (smt (verit, ccfv_threshold) \<open>C\<^sub>G = iefac \<F> C\<^sub>G\<^sub>0\<close>
              \<open>trail_false_cls \<Gamma>\<^sub>G {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}\<close> iefac_def mem_Collect_eq set_mset_efac
              set_mset_filter trail_false_cls_def)

        moreover have "(cls_of_gcls {#K\<^sub>G \<in># C\<^sub>G\<^sub>0. K\<^sub>G \<noteq> Pos A\<^sub>G#} :: ('f, 'v) term clause) =
          {#K \<in># C\<^sub>0. K \<noteq> Pos A#}"
          by (smt (verit) A_def C\<^sub>0_def cls_of_gcls_def filter_mset_cong0 glit_of_lit_lit_of_glit
              image_mset_filter_mset_swap lit_of_glit_def literal.map(1))

        ultimately have "trail_false_cls \<Gamma> ({#K \<in># C\<^sub>0. K \<noteq> Pos A#} \<cdot> Var)"
          unfolding subst_cls_id_subst
          using trail_false_cls_nonground_iff_trail_false_cls_ground[THEN iffD2]
          by (metis \<Gamma>_def)

        thus "SCL_FOL.trail_false_cls \<Gamma> ({#K \<in># C\<^sub>0. K \<noteq> Pos A#} \<cdot> Var)"
          unfolding SCL_FOL.trail_false_cls_def trail_false_cls_def
          unfolding SCL_FOL.trail_false_lit_def trail_false_lit_def
          by argo

        have "\<forall>x |\<in>| trail_atms \<Gamma>\<^sub>G. x \<prec>\<^sub>t A\<^sub>G"
          using step_hyps linorder_trm.is_least_in_ffilter_iff by simp
        hence "A\<^sub>G |\<notin>| trail_atms \<Gamma>\<^sub>G"
          by blast
        hence "A\<^sub>G \<notin> atm_of ` fst ` set \<Gamma>\<^sub>G"
          unfolding fset_trail_atms .
        hence "term_of_gterm A\<^sub>G \<notin> term_of_gterm ` atm_of ` fst ` set \<Gamma>\<^sub>G"
          using inj_image_mem_iff inj_term_of_gterm by metis
        hence "term_of_gterm A\<^sub>G \<notin> set (map (\<lambda>x. term_of_gterm (atm_of (fst x))) \<Gamma>\<^sub>G)"
          unfolding image_set list.map_comp comp_def .
        hence "A \<notin> set (map (\<lambda>x. atm_of (lit_of_glit (fst x))) \<Gamma>\<^sub>G)"
          unfolding A_def atm_of_lit_of_glit_conv .
        hence "A \<notin> atm_of ` fst ` set \<Gamma>"
          unfolding image_set list.map_comp comp_def \<Gamma>_def gtrailelem_of_trailelem_def
            fst_case_prod_simp .
        hence "A |\<notin>| trail_atms \<Gamma>"
          unfolding fset_trail_atms .
        hence "\<not> trail_defined_lit \<Gamma> (Pos A \<cdot>l Var)"
          by (simp add: trail_defined_lit_iff_trail_defined_atm)
        thus "\<not> SCL_FOL.trail_defined_lit \<Gamma> (Pos A \<cdot>l Var)"
          by (simp add: SCL_FOL.trail_defined_lit_def trail_defined_lit_def)

        have "set_mset (add_mset (Pos A) {#K \<in># remove1_mset (Pos A) C\<^sub>0. K = Pos A#}) =
          {Pos A}"
          by (smt (verit) Collect_cong insert_compr mem_Collect_eq set_mset_add_mset_insert
              set_mset_filter singletonD)
        hence "is_unifier Var (atm_of ` set_mset
          (add_mset (Pos A) {#K \<in># remove1_mset (Pos A) C\<^sub>0. K = Pos A#}))"
          by (metis (no_types, lifting) finite_imageI finite_set_mset image_empty image_insert
              is_unifier_alt singletonD)
        hence "is_unifiers Var {atm_of ` set_mset
          (add_mset (Pos A) {#K \<in># remove1_mset (Pos A) C\<^sub>0. K = Pos A#})}"
          unfolding SCL_FOL.is_unifiers_def by simp
        thus "SCL_FOL.is_imgu Var {atm_of ` set_mset
          (add_mset (Pos A) {#K \<in># remove1_mset (Pos A) C\<^sub>0. K = Pos A#})}"
          unfolding SCL_FOL.is_imgu_def by simp

        have "{#K \<in># C\<^sub>G\<^sub>0. K \<noteq> Pos A\<^sub>G#} = {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}"
          using \<open>ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<close>
          using \<open>ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<^sub>0\<close>
          unfolding \<open>C\<^sub>G = iefac \<F> C\<^sub>G\<^sub>0\<close>
          by (metis add_mset_remove_trivial efac_spec_if_pos_lit_is_maximal
              ex1_efac_eq_factoring_chain factorizable_if_neq_efac iefac_def literal.disc(1))

        hence "{#K \<in># C\<^sub>0. K \<noteq> Pos A#} = {#K \<in># C. K \<noteq> Pos A#}"
          unfolding C\<^sub>0_def C_def
          by (smt (verit, ccfv_SIG) A_def cls_of_gcls_def filter_mset_cong0 glit_of_lit_lit_of_glit
              image_mset_filter_mset_swap lit_of_glit_def literal.map(1))

        thus "\<Gamma>' = trail_propagate \<Gamma> (Pos A \<cdot>l Var) ({#K \<in># C\<^sub>0. K \<noteq> Pos A#} \<cdot> Var) Var"
          unfolding subst_cls_id_subst subst_lit_id_subst
          using \<open>\<Gamma>' = propagate_lit (Pos A) {#L \<in># C. L \<noteq> Pos A#} Var # \<Gamma>\<close>
          by argo
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.decide N \<beta> S S'"
      thus False
        unfolding S_def S'_def
      proof (cases N \<beta> "(\<Gamma>, U, \<C>)" "(\<Gamma>', U', \<C>')" rule: scl_fol.decide.cases)
        case (decideI L \<gamma>)
        show False
          using \<open>\<Gamma>' = decide_lit (L \<cdot>l \<gamma>) # \<Gamma>\<close>
          using \<open>\<Gamma>' = propagate_lit (Pos A) {#L \<in># C. L \<noteq> Pos A#} Var # \<Gamma>\<close>
          unfolding decide_lit_def propagate_lit_def
          by blast
      qed
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (conflict C\<^sub>G)

    have "\<Gamma>' = \<Gamma>"
      unfolding \<Gamma>'_def \<open>\<Gamma>\<^sub>G' = \<Gamma>\<^sub>G\<close> \<Gamma>_def ..

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have
      C\<^sub>G_in: "C\<^sub>G |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)" and
      C\<^sub>G_false: "trail_false_cls \<Gamma>\<^sub>G C\<^sub>G" and
      C\<^sub>G_lt: "\<forall>E\<^sub>G |\<in>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G). E\<^sub>G \<noteq> C\<^sub>G \<longrightarrow> trail_false_cls \<Gamma>\<^sub>G E\<^sub>G \<longrightarrow> C\<^sub>G \<prec>\<^sub>c E\<^sub>G"
      using \<open>linorder_cls.is_least_in_fset _ C\<^sub>G\<close>
      unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

    have "\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C\<^sub>G"
    proof (rule notI , elim exE conjE)
      fix L :: "'f gliteral"
      assume "is_pos L" and C\<^sub>G_max_lit: "ord_res.is_maximal_lit L C\<^sub>G"

      have "{#} |\<notin>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)"
        using C\<^sub>G_lt
        by (metis (full_types) C\<^sub>G_max_lit bot_fset.rep_eq fBex_fempty linorder_cls.leD
            linorder_lit.is_maximal_in_mset_iff mempty_lesseq_cls set_mset_empty
            trail_false_cls_mempty)

      have "trail_false_lit \<Gamma>\<^sub>G L"
        using C\<^sub>G_max_lit C\<^sub>G_false
        unfolding linorder_lit.is_maximal_in_mset_iff trail_false_cls_def
        by metis

      then obtain Ln \<Gamma>\<^sub>G\<^sub>0 where "\<Gamma>\<^sub>G = Ln # \<Gamma>\<^sub>G\<^sub>0"
        unfolding trail_false_lit_def
        by (metis (no_types) List.insert_def image_iff insert_Nil neq_Nil_conv)

      moreover have
        AAA: "\<forall>x xs. \<Gamma>\<^sub>G = x # xs \<longrightarrow>
          ((snd x \<noteq> None) \<longleftrightarrow> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls (x # xs))) \<and>
          (snd x \<noteq> None \<longrightarrow> is_pos (fst x)) \<and>
          (\<forall>x \<in> set xs. snd x = None)" and
        BBB: "(\<forall>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma>\<^sub>G = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<longrightarrow> snd Ln = None \<longrightarrow>
          \<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls (Ln # \<Gamma>\<^sub>0)))" and
        \<Gamma>\<^sub>G_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>\<^sub>G"
        using \<open>ord_res_11_invars N\<^sub>G S\<^sub>G\<close>[unfolded S\<^sub>G_def ord_res_11_invars.simps
            ord_res_10_invars.simps]
        by simp_all

      moreover have "fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G)"
        using C\<^sub>G_in C\<^sub>G_false by metis

      ultimately have "snd Ln \<noteq> None" and "is_pos (fst Ln)" and "\<forall>x \<in> set \<Gamma>\<^sub>G\<^sub>0. snd x = None"
        unfolding atomize_conj by metis

      have "\<not> fBex (iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)) (trail_false_cls \<Gamma>\<^sub>G\<^sub>0)"
      proof (cases \<Gamma>\<^sub>G\<^sub>0)
        case Nil
        then show ?thesis
          using \<open>{#} |\<notin>| iefac \<F> |`| (N\<^sub>G |\<union>| U\<^sub>G)\<close>
          unfolding trail_false_cls_def trail_false_lit_def
          by simp
      next
        case (Cons x xs)
        then show ?thesis
          using \<open>\<Gamma>\<^sub>G = Ln # \<Gamma>\<^sub>G\<^sub>0\<close>
          using \<open>\<forall>x \<in> set \<Gamma>\<^sub>G\<^sub>0. snd x = None\<close>
          using BBB[rule_format, of "[Ln]", unfolded append_Cons append_Nil]
          by simp
      qed

      hence "\<not> trail_false_cls \<Gamma>\<^sub>G\<^sub>0 C\<^sub>G"
        using C\<^sub>G_in by metis

      hence "fst Ln = - L"
        using C\<^sub>G_false C\<^sub>G_max_lit \<Gamma>\<^sub>G_sorted[unfolded \<open>\<Gamma>\<^sub>G = Ln # \<Gamma>\<^sub>G\<^sub>0\<close> sorted_wrt.simps]
        by (smt (verit, ccfv_SIG) Neg_atm_of_iff \<open>\<Gamma>\<^sub>G = Ln # \<Gamma>\<^sub>G\<^sub>0\<close> atm_of_uminus
            ord_res.less_lit_simps(4) imageE image_insert insertE
            linorder_lit.dual_order.strict_trans linorder_lit.is_maximal_in_mset_iff
            linorder_lit.neq_iff linorder_trm.order.irrefl list.simps(15) literal.collapse(1)
            ord_res.ground_ordered_resolution_calculus_axioms trail_false_cls_def
            trail_false_lit_def)

      hence "\<not> is_pos L"
        using \<open>is_pos (fst Ln)\<close>
        by (simp add: is_pos_neg_not_is_pos)

      thus False
        using \<open>is_pos L\<close> by contradiction
    qed

    hence "C\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G"
    proof -
      obtain C where "C |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and "C\<^sub>G = iefac \<F> C"
        using C\<^sub>G_in by blast

      hence "C\<^sub>G = C"
        using \<open>\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C\<^sub>G\<close>
        by (metis clauses_in_\<F>_have_pos_max_lit ex1_efac_eq_factoring_chain iefac_def
            ord_res.ground_factorings_preserves_maximal_literal)

      thus ?thesis
        using \<open>C |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close> by simp
    qed

    have "scl_fol.conflict N \<beta> S S'"
      unfolding S_def S'_def \<open>\<Gamma>' = \<Gamma>\<close> \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = Some C\<^sub>G\<close> option.map
    proof (rule scl_fol.conflictI)
      show "cls_of_gcls C\<^sub>G |\<in>| N |\<union>| U"
        unfolding N_def U_def
        using \<open>C\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close> by auto
    next
      show "is_ground_cls (cls_of_gcls C\<^sub>G \<cdot> (Var::'v \<Rightarrow> ('f, _) Term.term))"
        by simp
    next
      have "trail_false_cls \<Gamma>\<^sub>G C\<^sub>G"
        using \<open>trail_false_cls \<Gamma>\<^sub>G C\<^sub>G\<close> .

      hence "trail_false_cls \<Gamma> (cls_of_gcls C\<^sub>G \<cdot> Var)"
        unfolding \<Gamma>_def subst_cls_id_subst
        using trail_false_cls_nonground_iff_trail_false_cls_ground by metis

      thus "SCL_FOL.trail_false_cls \<Gamma> (cls_of_gcls C\<^sub>G \<cdot> Var)"
        unfolding SCL_FOL.trail_false_cls_def trail_false_cls_def
        unfolding SCL_FOL.trail_false_lit_def trail_false_lit_def
        by argo
    qed

    thus ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (skip L\<^sub>G C\<^sub>G n\<^sub>G)

    have "\<Gamma> = gtrailelem_of_trailelem (L\<^sub>G, n\<^sub>G) # \<Gamma>'"
      unfolding \<Gamma>_def \<Gamma>'_def \<open>\<Gamma>\<^sub>G = (L\<^sub>G, n\<^sub>G) # \<Gamma>\<^sub>G'\<close> by simp

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<C>\<^sub>G = Some C\<^sub>G\<close> nex_conflict_if_alread_in_conflict by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.skip N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = Some C\<^sub>G\<close> \<open>\<C>\<^sub>G' = Some C\<^sub>G\<close> option.map
        unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> gtrailelem_of_trailelem_def prod.case
      proof (rule scl_fol.skipI)
        have "- lit_of_glit L\<^sub>G = lit_of_glit (- L\<^sub>G)"
          by (cases L\<^sub>G) (simp_all add: lit_of_glit_def)
        show "- lit_of_glit L\<^sub>G \<notin># cls_of_gcls C\<^sub>G \<cdot> Var"
          unfolding subst_cls_id_subst
          unfolding \<open>- lit_of_glit L\<^sub>G = lit_of_glit (- L\<^sub>G)\<close>
          unfolding cls_of_gcls_def
          using \<open>- L\<^sub>G \<notin># C\<^sub>G\<close> inj_image_mset_mem_iff[OF inj_lit_of_glit]
          by metis
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"

      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
        unfolding S'_def \<C>'_def \<open>\<C>\<^sub>G' = Some C\<^sub>G\<close> by (simp add: scl_fol.conflict.simps)

      ultimately show False
        by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (resolution L\<^sub>G C\<^sub>G \<Gamma>\<^sub>G'' D\<^sub>G)

    have "\<Gamma>' = \<Gamma>"
      unfolding \<Gamma>'_def \<open>\<Gamma>\<^sub>G' = \<Gamma>\<^sub>G\<close> \<Gamma>_def ..

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<C> = Some (cls_of_gcls D\<^sub>G, Var)"
      unfolding \<C>_def \<open>\<C>\<^sub>G = Some D\<^sub>G\<close> option.map ..

    hence \<C>_eq: "\<C> = Some
      (add_mset (- lit_of_glit L\<^sub>G) (remove1_mset (- lit_of_glit L\<^sub>G) (cls_of_gcls D\<^sub>G)), Var)"
      by (smt (verit, best) add_mset_remove_trivial atm_of_eq_atm_of atm_of_lit_of_glit_conv
          cls_of_gcls_def glit_of_lit_lit_of_glit image_mset_add_mset insert_DiffM step_hyps(7)
          uminus_not_id')

    have "\<C>' = Some (
      remove1_mset (- (lit_of_glit L\<^sub>G)) (cls_of_gcls D\<^sub>G) +
      remove1_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G), Var)"
      unfolding \<C>'_def \<open>\<C>\<^sub>G' = Some _\<close> option.map
      apply (simp add: cls_of_gcls_def)
      by (smt (verit, ccfv_threshold) add_diff_cancel_right' add_mset_add_single atm_of_eq_atm_of
          atm_of_lit_of_glit_conv diff_single_trivial glit_of_lit_lit_of_glit
          image_mset_remove1_mset_if insert_DiffM is_pos_neg_not_is_pos msed_map_invR)
    hence \<C>'_eq: "\<C>' = Some (
      (remove1_mset (- (lit_of_glit L\<^sub>G)) (cls_of_gcls D\<^sub>G) \<cdot> Var +
      remove1_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G) \<cdot> Var) \<cdot> Var, Var)"
      by simp

    have "linorder_lit.is_greatest_in_mset C\<^sub>G L\<^sub>G"
      using \<open>ord_res_11_invars N\<^sub>G S\<^sub>G\<close>[unfolded S\<^sub>G_def \<open>\<Gamma>\<^sub>G = (L\<^sub>G, Some C\<^sub>G) # \<Gamma>\<^sub>G''\<close>]
      unfolding ord_res_11_invars.simps ord_res_10_invars.simps
      by simp

    hence "add_mset L\<^sub>G {#y \<in># C\<^sub>G. y \<noteq> L\<^sub>G#} = C\<^sub>G"
      using linorder_lit.explode_greatest_in_mset by metis

    hence "C\<^sub>G - {#L\<^sub>G#} = {#K \<in># C\<^sub>G. K \<noteq> L\<^sub>G#}"
      by (metis add_mset_remove_trivial)

    hence "cls_of_gcls (C\<^sub>G - {#L\<^sub>G#}) = cls_of_gcls {#K \<in># C\<^sub>G. K \<noteq> L\<^sub>G#}"
      by argo

    moreover have "cls_of_gcls (C\<^sub>G - {#L\<^sub>G#}) = cls_of_gcls C\<^sub>G - cls_of_gcls {#L\<^sub>G#}"
      unfolding cls_of_gcls_def
    proof (rule image_mset_Diff)
      show "{#L\<^sub>G#} \<subseteq># C\<^sub>G"
        by (metis \<open>ord_res.is_strictly_maximal_lit L\<^sub>G C\<^sub>G\<close> linorder_lit.is_greatest_in_mset_iff
            single_subset_iff)
    qed

    ultimately have "cls_of_gcls C\<^sub>G - {#lit_of_glit L\<^sub>G#} = cls_of_gcls {#K \<in># C\<^sub>G. K \<noteq> L\<^sub>G#}"
      by (metis \<open>add_mset L\<^sub>G {#y \<in># C\<^sub>G. y \<noteq> L\<^sub>G#} = C\<^sub>G\<close> cls_of_gcls_def image_mset_remove1_mset_if
          union_single_eq_member)

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<C>\<^sub>G = Some _\<close> nex_conflict_if_alread_in_conflict by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.resolve N \<beta> S S'"
        unfolding S_def S'_def \<open>\<Gamma>' = \<Gamma>\<close> \<open>U' = U\<close>
        unfolding \<C>_eq \<C>'_eq
      proof (rule scl_fol.resolveI)
        show "\<Gamma> = trail_propagate (map gtrailelem_of_trailelem \<Gamma>\<^sub>G'')
          (lit_of_glit L\<^sub>G) (remove1_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G)) Var"
          unfolding \<Gamma>_def \<open>\<Gamma>\<^sub>G = (L\<^sub>G, Some C\<^sub>G) # \<Gamma>\<^sub>G''\<close> gtrailelem_of_trailelem_def list.map prod.case
          unfolding propagate_lit_def subst_lit_id_subst option.map
          unfolding \<open>remove1_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G) = cls_of_gcls {#K \<in># C\<^sub>G. K \<noteq> L\<^sub>G#}\<close>
          by argo
      next
        show "lit_of_glit L\<^sub>G \<cdot>l Var = - (- lit_of_glit L\<^sub>G \<cdot>l Var)"
          by simp
      next
        show "SCL_FOL.is_renaming Var"
          by simp
      next
        show "SCL_FOL.is_renaming Var"
          by simp
      next
        show "
          vars_cls (add_mset (- lit_of_glit L\<^sub>G)
            (remove1_mset (- lit_of_glit L\<^sub>G) (cls_of_gcls D\<^sub>G)) \<cdot> Var) \<inter>
          vars_cls (add_mset (lit_of_glit L\<^sub>G)
            (remove1_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G)) \<cdot> Var) =
          {}"
          by (metis (no_types, lifting) boolean_algebra.conj_zero_right cls_of_gcls_def
              diff_single_trivial image_mset_add_mset insert_DiffM subst_cls_id_subst
              vars_cls_cls_of_gcls)
      next
        show "SCL_FOL.is_imgu Var
          {{atm_of (- lit_of_glit L\<^sub>G) \<cdot>a Var, atm_of (lit_of_glit L\<^sub>G) \<cdot>a Var}}"
          by (simp add: SCL_FOL.is_imgu_def SCL_FOL.is_unifiers_def SCL_FOL.is_unifier_def)
      next
        show "is_grounding_merge Var
          (vars_cls
            (add_mset (- lit_of_glit L\<^sub>G) (remove1_mset (- lit_of_glit L\<^sub>G) (cls_of_gcls D\<^sub>G)) \<cdot> Var))
          (rename_subst_domain Var Var)
          (vars_cls
            (add_mset (lit_of_glit L\<^sub>G) (remove1_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G)) \<cdot> Var))
          (rename_subst_domain Var Var)"
          by (simp add: is_grounding_merge_def)
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"

      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
        unfolding S'_def \<C>'_def \<open>\<C>\<^sub>G' = Some _\<close> by (simp add: scl_fol.conflict.simps)

      ultimately show False
        by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (backtrack L\<^sub>G C\<^sub>G)

    define K :: "('f, 'v) term literal" where
      "K = - lit_of_glit L\<^sub>G"

    define D :: "('f, 'v) term clause" where
      "D = cls_of_gcls C\<^sub>G - {#K#}"

    have "add_mset K D = cls_of_gcls C\<^sub>G"
      by (smt (verit, best) D_def K_def add_mset_remove_trivial atm_of_eq_atm_of
          atm_of_lit_of_glit_conv cls_of_gcls_def glit_of_lit_lit_of_glit image_mset_add_mset
          insert_DiffM step_hyps(6) uminus_not_id')

    have "U' = finsert (add_mset K D) U"
      unfolding U_def U'_def \<open>U\<^sub>G' = finsert C\<^sub>G U\<^sub>G\<close>
      by (smt (verit, ccfv_SIG) D_def K_def add_mset_remove_trivial atm_of_eq_atm_of
          atm_of_lit_of_glit_conv cls_of_gcls_def fimage_finsert glit_of_lit_lit_of_glit
          image_mset_add_mset insert_DiffM step_hyps(6) uminus_not_id')

    have "\<C> = Some (add_mset K D, Var)"
      by (smt (verit) D_def K_def \<C>_def add_mset_remove_trivial atm_of_eq_atm_of
          atm_of_lit_of_glit_conv cls_of_gcls_def glit_of_lit_lit_of_glit image_mset_add_mset
          insert_DiffM option.map(2) step_hyps(1,6) uminus_not_id')

    have "\<C>' = None"
      unfolding \<C>'_def \<open>\<C>\<^sub>G' = None\<close> option.map ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<C>\<^sub>G = Some _\<close> nex_conflict_if_alread_in_conflict by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.backtrack N \<beta> S S'"
        unfolding S_def S'_def
        unfolding \<open>U' = finsert (add_mset K D) U\<close> \<open>\<C> = Some (add_mset K D, Var)\<close> \<open>\<C>' = None\<close>
      proof (rule scl_fol.backtrackI)
        show "\<Gamma> = trail_decide ([] @ \<Gamma>') (lit_of_glit L\<^sub>G)"
          unfolding append_Nil
          unfolding decide_lit_def
          unfolding \<Gamma>_def \<open>\<Gamma>\<^sub>G = _ # _\<close> list.map \<Gamma>'_def[symmetric]
          unfolding gtrailelem_of_trailelem_def prod.case option.map
          ..
      next
        show "lit_of_glit L\<^sub>G = - (K \<cdot>l Var)"
          unfolding K_def by simp
      next
        have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>\<^sub>G"
          using \<open>ord_res_11_invars N\<^sub>G S\<^sub>G\<close>[unfolded S\<^sub>G_def]
          unfolding ord_res_11_invars.simps ord_res_10_invars.simps
          by fast

        hence "trail_consistent \<Gamma>\<^sub>G"
          using trail_consistent_if_sorted_wrt_atoms by metis

        hence "\<not> trail_defined_lit \<Gamma>\<^sub>G' (- L\<^sub>G)"
          by (metis trail_consistent.cases atm_of_eq_atm_of list.distinct(1) list.inject
              prod.sel(1) step_hyps(5) trail_defined_lit_iff_trail_defined_atm)

        hence "\<not> trail_false_lit \<Gamma>\<^sub>G' (- L\<^sub>G)"
          using trail_defined_lit_iff_true_or_false by metis

        hence "\<not> trail_false_cls \<Gamma>\<^sub>G' C\<^sub>G"
          using \<open>- L\<^sub>G \<in># C\<^sub>G\<close>
          unfolding trail_false_cls_def by metis

        hence "\<not> trail_false_cls \<Gamma>' (add_mset K D)"
          unfolding \<Gamma>'_def \<open>add_mset K D = cls_of_gcls C\<^sub>G\<close>
          unfolding trail_false_cls_nonground_iff_trail_false_cls_ground .

        moreover have "is_ground_cls (add_mset K D)"
          using \<C>_def \<open>\<C> = Some (add_mset K D, Var)\<close> step_hyps(1) by auto

        ultimately have "\<nexists>\<gamma>. is_ground_cls (add_mset K D \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma>' (add_mset K D \<cdot> \<gamma>)"
          by simp

        thus "\<nexists>\<gamma>. is_ground_cls (add_mset K D \<cdot> \<gamma>) \<and> SCL_FOL.trail_false_cls \<Gamma>' (add_mset K D \<cdot> \<gamma>)"
          unfolding SCL_FOL.trail_false_cls_def trail_false_cls_def
          unfolding SCL_FOL.trail_false_lit_def trail_false_lit_def
          by argo
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.decide N \<beta> S S'"
      thus False
        unfolding S_def \<open>\<C> = Some _\<close>
        by (auto elim!: scl_fol.decide.cases)
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  qed
qed

end

lemma wfp_on_antimono_stronger:
  fixes
    A :: "'a set" and B :: "'b set" and
    f :: "'a \<Rightarrow> 'b" and
    R :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and Q :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    wf: "wfp_on B R" and
    sub: "f ` A \<subseteq> B" and
    mono: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> Q x y \<Longrightarrow> R (f x) (f y)"
  shows "wfp_on A Q"
  unfolding wfp_on_iff_ex_minimal
proof (intro allI impI)
  fix A' :: "'a set"
  assume "A' \<subseteq> A" and "A' \<noteq> {}"
  have "f ` A' \<subseteq> B"
    using \<open>A' \<subseteq> A\<close> sub by blast
  moreover have "f ` A' \<noteq> {}"
    using \<open>A' \<noteq> {}\<close> by blast
  ultimately have "\<exists>z\<in>f ` A'. \<forall>y. R y z \<longrightarrow> y \<notin> f ` A'"
    using wf wfp_on_iff_ex_minimal by blast
  hence "\<exists>z\<in>A'. \<forall>y. R (f y) (f z) \<longrightarrow> y \<notin> A'"
    by blast
  thus "\<exists>z\<in>A'. \<forall>y. Q y z \<longrightarrow> y \<notin> A'"
    using \<open>A' \<subseteq> A\<close> mono by blast
qed

text \<open>For AFP-devel, delete
@{thm Simulation_SCLFOL_ORDRES.wfp_on_antimono_stronger}
as it is available in \<^theory>\<open>HOL.Wellfounded\<close>.\<close>

corollary (in scl_fol_calculus) termination_projectable_strategy:
  fixes
    N :: "('f, 'v) Term.term clause fset" and
    \<beta> :: "('f, 'v) Term.term" and
    strategy and strategy_init and proj
  assumes strategy_restricts_regular_scl:
    "\<And>S S'. strategy\<^sup>*\<^sup>* strategy_init S \<Longrightarrow> strategy S S' \<Longrightarrow> regular_scl N \<beta> (proj S) (proj S')" and
    initial_state: "proj strategy_init = initial_state"
  shows "wfp_on {S. strategy\<^sup>*\<^sup>* strategy_init S} strategy\<inverse>\<inverse>"
proof (rule wfp_on_antimono_stronger)
  show "wfp_on {proj S | S. strategy\<^sup>*\<^sup>* strategy_init S} (regular_scl N \<beta>)\<inverse>\<inverse>"
  proof (rule wfp_on_subset)
    show "wfp_on {S. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S} (regular_scl N \<beta>)\<inverse>\<inverse>"
      using termination_regular_scl by metis
  next
    show "{proj S | S. strategy\<^sup>*\<^sup>* strategy_init S} \<subseteq> {S. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S}"
    proof (intro Collect_mono impI, elim exE conjE)
      fix s S assume "s = proj S" and "strategy\<^sup>*\<^sup>* strategy_init S"
      show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state s"
        unfolding \<open>s = proj S\<close>
        using \<open>strategy\<^sup>*\<^sup>* strategy_init S\<close>
      proof (induction S rule: rtranclp_induct)
        case base
        thus ?case
          unfolding initial_state by simp
      next
        case (step y z)
        thus ?case
          using strategy_restricts_regular_scl
          by (meson rtranclp.simps)
      qed
    qed
  qed
next
  show "proj ` {S. strategy\<^sup>*\<^sup>* strategy_init S} \<subseteq> {proj S |S. strategy\<^sup>*\<^sup>* strategy_init S}"
    by blast
next
  show "\<And>S' S. S \<in> {S. strategy\<^sup>*\<^sup>* strategy_init S} \<Longrightarrow> strategy\<inverse>\<inverse> S' S \<Longrightarrow>
    (regular_scl N \<beta>)\<inverse>\<inverse> (proj S') (proj S)"
    using strategy_restricts_regular_scl by simp
qed

text \<open>For AFP-devel, delete
@{thm Simulation_SCLFOL_ORDRES.scl_fol_calculus.termination_projectable_strategy}
as it is available in \<^theory>\<open>Simple_Clause_Learning.Termination\<close>.\<close>

corollary (in simulation_SCLFOL_ground_ordered_resolution) ord_res_11_termination:
  fixes N :: "'f gclause fset"
  shows "wfp_on {S. (ord_res_11 N)\<^sup>*\<^sup>* ({||}, {||}, [], None) S} (ord_res_11 N)\<inverse>\<inverse>"
proof (rule scl_fol.termination_projectable_strategy)
  fix S S'
  assume run: "(ord_res_11 N)\<^sup>*\<^sup>* ({||}, {||}, [], None) S" and step: "ord_res_11 N S S'"

  define \<beta> :: "'f gterm" where
    "\<beta> = (THE A. linorder_trm.is_greatest_in_fset (atms_of_clss N) A)"

  show "scl_fol.regular_scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) (state_of_gstate S) (state_of_gstate S')"
  proof (rule ord_res_11_is_strategy_for_regular_scl)
    show "\<forall>A\<^sub>G |\<in>| atms_of_clss N. A\<^sub>G \<preceq>\<^sub>t \<beta>"
    proof (cases "atms_of_clss N = {||}")
      case True
      thus ?thesis
        by simp
    next
      case False
      then show ?thesis
        unfolding \<beta>_def
        by (metis (full_types) linorder_trm.Uniq_is_greatest_in_fset
            linorder_trm.ex_greatest_in_fset linorder_trm.is_greatest_in_fset_iff sup2CI
            the1_equality')
    qed
  next
    show "(ord_res_11 N)\<^sup>*\<^sup>* ({||}, {||}, [], None) S"
      using run .
  next
    show "ord_res_11 N S S'"
      using step .
  qed
next
  show "state_of_gstate ({||}, {||}, [], None) = SCL_FOL.initial_state"
    by simp
qed

corollary (in scl_fol_calculus) static_non_subsumption_projectable_strategy:
  fixes strategy and strategy_init and proj
  assumes
    run: "strategy\<^sup>*\<^sup>* strategy_init S" and
    step: "backtrack N \<beta> (proj S) S'" and
    strategy_restricts_regular_scl:
      "\<And>S S'. strategy\<^sup>*\<^sup>* strategy_init S \<Longrightarrow> strategy S S' \<Longrightarrow> regular_scl N \<beta> (proj S) (proj S')" and
    initial_state: "proj strategy_init = initial_state"
  defines
    "U \<equiv> state_learned (proj S)"
  shows "\<exists>C \<gamma>. state_conflict (proj S) = Some (C, \<gamma>) \<and> \<not> (\<exists>D |\<in>| N |\<union>| U. subsumes D C)"
proof -
  have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state (proj S)"
    using run
  proof (induction S rule: rtranclp_induct)
    case base
    thus ?case
      unfolding initial_state by simp
  next
    case (step y z)
    thus ?case
      using strategy_restricts_regular_scl
      by (meson rtranclp.simps)
  qed

  moreover have "backtrack N \<beta> (proj S) S'"
    using step by simp

  ultimately show ?thesis
    unfolding U_def
    using static_non_subsumption_regular_scl
    by simp
qed

text \<open>For AFP-devel, delete
@{thm Simulation_SCLFOL_ORDRES.scl_fol_calculus.static_non_subsumption_projectable_strategy}
as it is available in \<^theory>\<open>Simple_Clause_Learning.Non_Redundancy\<close>.\<close>

corollary (in simulation_SCLFOL_ground_ordered_resolution) ord_res_11_non_subsumption:
  fixes N\<^sub>G :: "'f gclause fset" and s :: "_ \<times> _ \<times> _ \<times> _"
  defines
    "\<beta> \<equiv> (THE A. linorder_trm.is_greatest_in_fset (atms_of_clss N\<^sub>G) A)"
  assumes
    run: "(ord_res_11 N\<^sub>G)\<^sup>*\<^sup>* ({||}, {||}, [], None) s" and
    step: "scl_fol.backtrack (cls_of_gcls |`| N\<^sub>G) (term_of_gterm \<beta>) (state_of_gstate s) s'"
  shows "\<exists>U\<^sub>e\<^sub>r \<F> \<Gamma> D. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D) \<and> \<not> (\<exists>C |\<in>| N\<^sub>G |\<union>| U\<^sub>e\<^sub>r. C \<subseteq># D)"
proof -
  have "\<exists>C \<gamma>. state_conflict (state_of_gstate s) = Some (C, \<gamma>) \<and>
        \<not> (\<exists>D|\<in>| cls_of_gcls |`| N\<^sub>G |\<union>| state_learned (state_of_gstate s). subsumes D C)"
  proof (rule scl_fol.static_non_subsumption_projectable_strategy[
        of "ord_res_11 N\<^sub>G" _ _ _ _ state_of_gstate , OF run step])
    fix S S'
    assume run: "(ord_res_11 N\<^sub>G)\<^sup>*\<^sup>* ({||}, {||}, [], None) S" and step: "ord_res_11 N\<^sub>G S S'"
    show "scl_fol.regular_scl (cls_of_gcls |`| N\<^sub>G) (term_of_gterm \<beta>)
      (state_of_gstate S) (state_of_gstate S')"
    proof (intro ord_res_11_is_strategy_for_regular_scl ballI)
      fix A\<^sub>G :: "'f gterm"
      assume "A\<^sub>G |\<in>| atms_of_clss N\<^sub>G"
      show "A\<^sub>G \<preceq>\<^sub>t \<beta>"
      proof (cases "atms_of_clss N\<^sub>G = {||}")
        case True
        thus ?thesis
          using \<open>A\<^sub>G |\<in>| atms_of_clss N\<^sub>G\<close>
          by simp
      next
        case False
        then show ?thesis
          using \<open>A\<^sub>G |\<in>| atms_of_clss N\<^sub>G\<close>
          unfolding \<beta>_def
          by (metis (full_types) linorder_trm.Uniq_is_greatest_in_fset
              linorder_trm.ex_greatest_in_fset linorder_trm.is_greatest_in_fset_iff sup2CI
              the1_equality')
      qed
    next
      show "(ord_res_11 N\<^sub>G)\<^sup>*\<^sup>* ({||}, {||}, [], None) S"
        using run .
    next
      show "ord_res_11 N\<^sub>G S S'"
        using step .
    qed
  next
    show "state_of_gstate ({||}, {||}, [], None) = initial_state"
      by simp
  qed

  moreover obtain U\<^sub>G \<F> \<Gamma> D where "s = (U\<^sub>G, \<F>, \<Gamma>, Some D)"
  proof atomize_elim
    obtain U\<^sub>G \<F> \<Gamma> \<C> where "s = (U\<^sub>G, \<F>, \<Gamma>, \<C>)"
      by (metis prod.exhaust)

    moreover obtain D where "\<C> = Some D"
      using step
      by (auto simp: \<open>s = (U\<^sub>G, \<F>, \<Gamma>, \<C>)\<close> elim: scl_fol.backtrack.cases)

    ultimately show "\<exists>U\<^sub>e\<^sub>r \<F> \<Gamma> D. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)"
      by metis
  qed

  ultimately have "\<not> (\<exists>C |\<in>| N\<^sub>G |\<union>|U\<^sub>G.
    subsumes (cls_of_gcls C :: ('f, 'v) term clause) (cls_of_gcls D))"
    by auto

  hence "\<not> (\<exists>C |\<in>| N\<^sub>G |\<union>|U\<^sub>G. (cls_of_gcls C :: ('f, 'v) term clause) \<subseteq># (cls_of_gcls D))"
    by (simp add: subsumes_def)

  hence "\<not> (\<exists>C |\<in>| N\<^sub>G |\<union>|U\<^sub>G. C \<subseteq># D)"
    by (metis cls_of_gcls_def image_mset_subseteq_mono)

  thus ?thesis
    unfolding \<open>s = (U\<^sub>G, \<F>, \<Gamma>, Some D)\<close> by metis
qed

end
