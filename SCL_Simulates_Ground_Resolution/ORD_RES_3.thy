theory ORD_RES_3
  imports
    ORD_RES
    Exhaustive_Factorization
    Exhaustive_Resolution
begin

section \<open>ORD-RES-3 (full resolve)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_3 where
  factoring: "
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    U\<^sub>e\<^sub>f' = finsert (efac C) U\<^sub>e\<^sub>f \<Longrightarrow>
    ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f')" |

  resolution: "
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L} \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>e\<^sub>r', U\<^sub>e\<^sub>f)"

inductive ord_res_3_step where
  "ord_res_3 N s s' \<Longrightarrow> ord_res_3_step (N, s) (N, s')"

inductive ord_res_3_final where
  "ord_res_final (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<Longrightarrow> ord_res_3_final (N, (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f))"

inductive ord_res_3_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_3_load N (N, ({||}, {||}))"

sublocale ord_res_3_semantics: semantics where
  step = ord_res_3_step and
  final = ord_res_3_final
proof unfold_locales
  fix S3 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>r\<^sub>r U\<^sub>e\<^sub>f :: "'f gterm clause fset" where
    S3_def: "S3 = (N, (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)

  assume "ord_res_3_final S3"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (simp add: S3_def ord_res_3_final.simps ord_res_final_def)
  thus "finished ord_res_3_step S3"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    hence "is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) {#}"
      using is_least_false_clause_mempty by metis
    hence "\<nexists>C L. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<and> linorder_lit.is_maximal_in_mset C L"
      by (metis Uniq_D Uniq_is_least_false_clause bot_fset.rep_eq fBex_fempty
          linorder_lit.is_maximal_in_mset_iff set_mset_empty)
    hence "\<nexists>x. ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f) x"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def ord_res_3_step.simps S3_def)
  next
    assume "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    hence "\<nexists>C. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      unfolding ex_false_clause_def is_least_false_clause_def
      by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
          linorder_cls.is_least_in_fset_ffilterD(2))
    hence "\<nexists>x. ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f) x"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def ord_res_3_step.simps S3_def)
  qed
qed

sublocale ord_res_3_language: language where
  step = ord_res_3_step and
  final = ord_res_3_final and
  load = ord_res_3_load
  by unfold_locales

lemma is_least_false_clause_conv_if_partial_resolution_invariant:
  assumes "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
  shows "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
proof -
  have "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)"
    by (simp add: sup_commute sup_left_commute)
  also have "\<dots> = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
  proof (rule is_least_false_clause_funion_cancel_right)
    show "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<forall>U. ord_res.production U C = {}"
    proof (intro ballI)
      fix C
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. (\<exists>C'. ground_resolution D C C')"
        using assms by (metis eres_eq_after_tranclp_ground_resolution resolvable_if_neq_eres)
      hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
        using nex_strictly_maximal_pos_lit_if_resolvable by metis
      thus "\<forall>U. ord_res.production U C = {}"
        using unproductive_if_nex_strictly_maximal_pos_lit by metis
    qed
  next
    show "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
    proof (intro ballI)
      fix C
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      then obtain D1 D2 where
        "D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
        "C \<noteq> eres D1 D2" and
        "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using assms by metis

      have "eres D1 D2 = eres D1 C"
        using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_eq_after_tranclp_ground_resolution by metis

      show "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
      proof (intro bexI conjI)
        have "eres D1 C \<preceq>\<^sub>c C"
          using eres_le .
        thus "eres D1 D2 \<prec>\<^sub>c C"
          using \<open>C \<noteq> eres D1 D2\<close> \<open>eres D1 D2 = eres D1 C\<close> by order
      next
        show "{eres D1 D2} \<TTurnstile>e {C}"
          using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_entails_resolvent by metis
      next
        show "eres D1 D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          using \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> by simp
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma right_unique_ord_res_3: "right_unique (ord_res_3 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_3 N s s'" and step2: "ord_res_3 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_3.cases)
    case hyps1: (factoring U\<^sub>r\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 U\<^sub>e\<^sub>f1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_3.cases)
      case (factoring U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f2')
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 D2 U\<^sub>r\<^sub>r2')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution U\<^sub>r\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 D1 U\<^sub>r\<^sub>r1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_3.cases)
      case (factoring U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f2')
      with hyps1 have False
        by (metis Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset prod.inject the1_equality')
      thus ?thesis ..
    next
      case hyps2: (resolution U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 D2 U\<^sub>r\<^sub>r2')

      have *: "U\<^sub>r\<^sub>r1 = U\<^sub>r\<^sub>r2" "U\<^sub>e\<^sub>f1 = U\<^sub>e\<^sub>f2"
        using hyps1 hyps2 by  simp_all

      have **: "C1 = C2"
        using hyps1 hyps2
        unfolding *
        by (metis Uniq_is_least_false_clause the1_equality')

      have ***: "L1 = L2"
        using hyps1 hyps2
        unfolding * **
        by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

      have ****: "D1 = D2"
        using hyps1 hyps2
        unfolding * ** ***
        by (metis linorder_cls.less_irrefl linorder_cls.linorder_cases
            ord_res.less_trm_iff_less_cls_if_mem_production singletonI)

      show ?thesis
        using hyps1 hyps2
        unfolding * ** *** ****
        by argo
    qed
  qed
qed

lemma right_unique_ord_res_3_step: "right_unique ord_res_3_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_3_step x y \<Longrightarrow> ord_res_3_step x z \<Longrightarrow> y = z"
    apply (cases x; cases y; cases z)
    apply (simp add: ord_res_3_step.simps)
    using right_unique_ord_res_3[THEN right_uniqueD]
    by blast
qed

lemma ex_ord_res_3_if_not_final:
  assumes "\<not> ord_res_3_final S"
  shows "\<exists>S'. ord_res_3_step S S'"
proof -
  from assms obtain N U\<^sub>r U\<^sub>e\<^sub>f where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))" and
    "{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
    "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (metis ord_res_3_final.intros ord_res_final_def surj_pair)

  obtain C where C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    using \<open>ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))\<close> obtains_least_false_clause_if_ex_false_clause
    by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using ord_res_3.factoring[OF C_least_false C_max] S_def is_pos_def
      by (metis ord_res_3_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain DC where
      "full_run (ground_resolution D) C DC"
      using ex_ground_resolutionI C_max Neg
      using ex1_eres_eq_full_run_ground_resolution by blast

    ultimately show ?thesis
      using ord_res_3.resolution[OF C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_3_step.intros)
  qed
qed

corollary ord_res_3_step_safe: "ord_res_3_final S \<or> (\<exists>S'. ord_res_3_step S S')"
  using ex_ord_res_3_if_not_final by metis

end

end