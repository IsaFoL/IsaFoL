theory ORD_RES_2
  imports
    ORD_RES
    Exhaustive_Factorization
begin

section \<open>ORD-RES-2 (full factorization)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_2 where
  factoring: "
    is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    U\<^sub>e\<^sub>f' = finsert (efac C) U\<^sub>e\<^sub>f \<Longrightarrow>
    ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>r, U\<^sub>e\<^sub>f')" |

  resolution: "
    is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    U\<^sub>r' = finsert CD U\<^sub>r \<Longrightarrow>
    ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>r', U\<^sub>e\<^sub>f)"

inductive ord_res_2_step where
  "ord_res_2 N S S' \<Longrightarrow> ord_res_2_step (N, S) (N, S')"

inductive ord_res_2_final where
  "ord_res_final (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<Longrightarrow> ord_res_2_final (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"

inductive ord_res_2_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_2_load N (N, ({||}, {||}))"

sublocale ord_res_2_semantics: semantics where
  step = ord_res_2_step and
  final = ord_res_2_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>r U\<^sub>e\<^sub>f :: "'f gterm clause fset" where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)

  assume "ord_res_2_final S"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (simp add: S_def ord_res_2_final.simps ord_res_final_def)
  thus "finished ord_res_2_step S"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    have False if "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) x" for x
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>e\<^sub>f)" x rule: ord_res_2.cases)
      case hyps: (factoring C L U\<^sub>e\<^sub>f')
      from hyps have "C = {#}"
        using is_least_false_clause_mempty[OF \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>]
        by (metis Uniq_D Uniq_is_least_false_clause)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    next
      case hyps: (resolution C L D CD U\<^sub>e\<^sub>f')
      from hyps \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> have "C = {#}"
        using is_least_false_clause_mempty[OF \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>]
        by (metis Uniq_D Uniq_is_least_false_clause)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    qed
    thus "finished ord_res_2_step S"
      unfolding finished_def ord_res_2_step.simps S_def
      by (metis prod.inject)
  next
    assume no_false_cls: "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    have False if "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) x" for x
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>e\<^sub>f)" x rule: ord_res_2.cases)
      case hyps: (factoring C L U\<^sub>e\<^sub>f')
      thus False
        using no_false_cls[unfolded ex_false_clause_def]
        using is_least_false_clause_def linorder_cls.is_least_in_fset_iff by auto
    next
      case hyps: (resolution C L D CD U\<^sub>e\<^sub>f')
      thus False
        using no_false_cls[unfolded ex_false_clause_def]
        using is_least_false_clause_def linorder_cls.is_least_in_fset_iff by auto
    qed
    thus "finished ord_res_2_step S"
      unfolding finished_def ord_res_2_step.simps S_def
      by (metis prod.inject)
  qed
qed

sublocale ord_res_2_language: language where
  step = ord_res_2_step and
  final = ord_res_2_final and
  load = ord_res_2_load
  by unfold_locales

lemma is_least_in_fset_with_irrelevant_clauses_if_is_least_in_fset:
  assumes
    irrelevant: "\<forall>D |\<in>| N'. \<exists>E |\<in>| N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"
  shows "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| N'. \<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C|} C"
proof -
  have
    C_in: "C |\<in>| N" and
    C_not_entailed: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_lt: "\<forall>x |\<in>| N. x \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) x \<TTurnstile> x \<longrightarrow> C \<prec>\<^sub>c x"
    using C_least linorder_cls.is_least_in_ffilter_iff by simp_all

  have "C |\<in>| N |\<union>| N'"
    using C_in by simp

  moreover have "\<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C"
    using extended_partial_model_entails_iff_partial_model_entails[
        of "fset N" "fset N'", OF finite_fset finite_fset irrelevant]
    using C_in C_not_entailed
    by simp

  moreover have "C \<prec>\<^sub>c x"
    if
      x_in: "x |\<in>| N |\<union>| N'" and
      x_neq: "x \<noteq> C" and
      x_not_entailed: "\<not> ord_res_Interp (fset (N |\<union>| N')) x \<TTurnstile> x"
    for x
  proof -

    from x_in have "x |\<in>| N \<or> x |\<in>| N'"
      by simp
    thus "C \<prec>\<^sub>c x"
    proof (elim disjE)
      assume x_in: "x |\<in>| N"

      moreover have "\<not> ord_res_Interp (fset N) x \<TTurnstile> x"
        using extended_partial_model_entails_iff_partial_model_entails[
            of "fset N" "fset N'", OF finite_fset finite_fset irrelevant x_in]
        using x_not_entailed by simp

      ultimately show "C \<prec>\<^sub>c x"
        using C_lt[rule_format, of x] x_neq by argo
    next
      assume "x |\<in>| N'"
      then obtain x' where "x' |\<in>| N" and "x' \<subset># x" "set_mset x' = set_mset x"
        using irrelevant by metis

      have "x' \<prec>\<^sub>c x"
        using \<open>x' \<subset># x\<close> by (metis strict_subset_implies_multp)

      moreover have "C \<preceq>\<^sub>c x'"
      proof (cases "x' = C")
        case True
        thus ?thesis
          by order
      next
        case False

        have "C \<prec>\<^sub>c x'"
        proof (rule C_lt[rule_format])
          show "x' |\<in>| N"
            using \<open>x' |\<in>| N\<close> .
        next
          show "x' \<noteq> C"
            using False .
        next
          have "\<not> ord_res_Interp (fset (N |\<union>| N')) x \<TTurnstile> x'"
            using x_not_entailed \<open>set_mset x' = set_mset x\<close>
            by (metis true_cls_def)
          hence "\<not> ord_res_Interp (fset (N |\<union>| N')) x' \<TTurnstile> x'"
            by (metis \<open>x' \<prec>\<^sub>c x\<close> ord_res.entailed_clause_stays_entailed)
          thus "\<not> ord_res_Interp (fset N) x' \<TTurnstile> x'"
            using extended_partial_model_entails_iff_partial_model_entails[
                of "fset N" "fset N'" x', OF finite_fset finite_fset irrelevant]
            using \<open>x' |\<in>| N\<close> by simp
        qed
        thus ?thesis
          by order
      qed

      ultimately show "C \<prec>\<^sub>c x"
        by order
    qed
  qed

  ultimately show "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| N'.
    \<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C|} C"
    using C_in C_not_entailed
    unfolding linorder_cls.is_least_in_ffilter_iff by metis
qed

primrec fset_upto :: "nat \<Rightarrow> nat \<Rightarrow> nat fset" where
  "fset_upto i 0 = (if i = 0 then {|0|} else {||})" |
  "fset_upto i (Suc n) = (if i \<le> Suc n then finsert (Suc n) (fset_upto i n) else {||})"

lemma
  "fset_upto 0 0 = {|0|}"
  "fset_upto 0 1 = {|0, 1|}"
  "fset_upto 0 2 = {|0, 1, 2|}"
  "fset_upto 0 3 = {|0, 1, 2, 3|}"
  "fset_upto 1 3 = {|1, 2, 3|}"
  "fset_upto 2 3 = {|2, 3|}"
  "fset_upto 3 3 = {|3|}"
  "fset_upto 4 3 = {||}"
  unfolding numeral_2_eq_2 numeral_3_eq_3
  by auto

lemma "i \<le> 1 + j \<Longrightarrow> List.upto i (1 + j) = List.upto i j @ [1 + j]"
  using upto_rec2 by simp

lemma fset_of_append_singleton: "fset_of_list (xs @ [x]) = finsert x (fset_of_list xs)"
  by simp

lemma "fset_of_list (List.upto (int i) (int j)) = int |`| fset_upto i j"
proof (induction j)
  case 0
  show ?case
    by simp
next
  case (Suc j)
  show ?case
  proof (cases "i \<le> Suc j")
    case True
    hence AAA: "int i \<le> 1 + int j"
      by presburger

    from True show ?thesis
      apply simp
      unfolding Suc.IH[symmetric]
      unfolding upto_rec2[OF AAA] fset_of_append_singleton
      by simp
  next
    case False
    thus ?thesis
      by simp
  qed
qed

lemma fset_fset_upto[simp]: "fset (fset_upto m n) = {m..n}"
  apply (induction n)
  apply simp
  apply simp
  using atLeastAtMostSuc_conv by presburger

lemma minus_mset_replicate_strict_subset_minus_msetI:
  assumes "m < n" and "n < count C L"
  shows "C - replicate_mset n L \<subset># C - replicate_mset m L"
proof -
  from \<open>m < n\<close> obtain k1 where n_def: "n = m + Suc k1"
    using less_natE by auto

  with \<open>n < count C L\<close> obtain k2 where
    count_eq: "count C L = m + Suc k1 + Suc k2"
    by (metis add.commute add_Suc group_cancel.add1 less_natE)

  define C\<^sub>0 where
    "C\<^sub>0 = {#K \<in># C. K \<noteq> L#}"

  have C_eq: "C = C\<^sub>0 + replicate_mset m L + replicate_mset (Suc k1) L + replicate_mset (Suc k2) L"
    using C\<^sub>0_def count_eq
    by (metis (mono_tags, lifting) filter_mset_eq group_cancel.add1 replicate_mset_plus
        union_filter_mset_complement)

  have "C - replicate_mset n L = C\<^sub>0 + replicate_mset (Suc k2) L"
    unfolding C_eq n_def
    by (simp add: replicate_mset_plus)
  also have "\<dots> \<subset># C\<^sub>0 + replicate_mset (Suc k1) L + replicate_mset (Suc k2) L"
    by simp
  also have "\<dots> = C - replicate_mset m L"
    unfolding C_eq
    by (simp add: replicate_mset_plus)
  finally show ?thesis .
qed

lemma factoring_all_is_between_efac_and_original_clause:
  fixes z
  assumes
    "is_pos L" and "ord_res.is_maximal_lit L C" and "count C L = Suc (Suc n)"
    "m' \<le> n" and
    z_in: "z |\<in>| (\<lambda>i. C - replicate_mset i L) |`| fset_upto 0 m'"
  shows "efac C \<subset># z" and "z \<subseteq># C"
proof -
  from z_in obtain i where
    "i \<le> m'" and
    z_def: "z = C - replicate_mset i L"
    by auto

  have "i \<le> n"
    using \<open>i \<le> m'\<close> \<open>m' \<le> n\<close> by presburger
  hence "i < count C L"
    using \<open>count C L = Suc (Suc n)\<close> by presburger
  thus "z \<subseteq># C"
    unfolding z_def by simp

  show "efac C \<subset># z"
  proof -
    have "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      using efac_spec_if_pos_lit_is_maximal[OF \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L C\<close>] .
    also have "\<dots> \<subset># add_mset L (add_mset L {#K \<in># C. K \<noteq> L#})"
      by simp
    also have "\<dots> = C - replicate_mset n L"
      using minus_mset_replicate_mset_eq_add_mset_add_mset_filter_mset[
          OF \<open>count C L = Suc (Suc n)\<close>] ..
    also have "\<dots> \<subseteq># C - replicate_mset i L"
      using \<open>i \<le> n\<close> by (simp add: subseteq_mset_def)
    also have "\<dots> = z"
      using z_def ..
    finally show ?thesis .
  qed
qed

lemma
  assumes
    "linorder_cls.is_least_in_fset {|x |\<in>| N1. P N1 x|} x" and
    "linorder_cls.is_least_in_fset N2 y" and
    "\<forall>z |\<in>| N2. z \<preceq>\<^sub>c x" and
    "P (N1 |\<union>| N2) y" and
    "\<forall>z |\<in>| N1. z \<prec>\<^sub>c x \<longrightarrow> \<not> P (N1 |\<union>| N2) z"
  shows "linorder_cls.is_least_in_fset {|x |\<in>| N1 |\<union>| N2. P (N1 |\<union>| N2) x|} y"
proof -
  show ?thesis
    unfolding linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    from assms(2) show "y |\<in>| N1 |\<union>| N2"
      unfolding linorder_cls.is_least_in_fset_iff by simp
  next
    from assms(4) show "P (N1 |\<union>| N2) y"
      by argo
  next
    fix z
    assume z_in: "z |\<in>| N1 |\<union>| N2" and "z \<noteq> y" and "P (N1 |\<union>| N2) z"
    show "y \<prec>\<^sub>c z"
      using z_in[unfolded funion_iff]
    proof (elim disjE)
      from assms(2,3,5) show "z |\<in>| N1 \<Longrightarrow> y \<prec>\<^sub>c z"
        by (metis \<open>P (N1 |\<union>| N2) z\<close> \<open>z \<noteq> y\<close> linorder_cls.dual_order.not_eq_order_implies_strict
            linorder_cls.is_least_in_fset_iff linorder_cls.less_linear
            linorder_cls.order.strict_trans)
    next
      from assms(2) show "z |\<in>| N2 \<Longrightarrow> y \<prec>\<^sub>c z"
        using \<open>z \<noteq> y\<close> linorder_cls.is_least_in_fset_iff by blast
    qed
  qed
qed

lemma ground_factoring_preserves_efac:
  assumes "ord_res.ground_factoring P C"
  shows "efac P = efac C"
  using assms
  by (smt (verit, ccfv_threshold) filter_mset_add_mset is_pos_def ord_res.ground_factoring.cases
      ord_res.ground_factoring_preserves_maximal_literal efac_spec_if_pos_lit_is_maximal)

lemma ground_factorings_preserves_efac:
  assumes "ord_res.ground_factoring\<^sup>*\<^sup>* P C"
  shows "efac P = efac C"
  using assms
  by (induction P rule: converse_rtranclp_induct)
    (simp_all add: ground_factoring_preserves_efac)


lemma ex_ord_res_2_if_not_final:
  assumes "\<not> ord_res_2_final S"
  shows "\<exists>S'. ord_res_2_step S S'"
proof -
  from assms obtain N U\<^sub>r U\<^sub>e\<^sub>f where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))" and
    "{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
    "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (metis ord_res_2_final.intros ord_res_final_def surj_pair)

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
      using ord_res_2.factoring[OF C_least_false C_max] S_def is_pos_def
      by (metis ord_res_2_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain CD where
      "ord_res.ground_resolution C D CD"
      using ex_ground_resolutionI C_max Neg by metis

    ultimately show ?thesis
      using ord_res_2.resolution[OF C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_2_step.intros)
  qed
qed

corollary ord_res_2_step_safe: "ord_res_2_final S \<or> (\<exists>S'. ord_res_2_step S S')"
  using ex_ord_res_2_if_not_final by metis

lemma is_least_false_clause_if_is_least_false_clause_in_union_unproductive:
  assumes
    N2_unproductive: "\<forall>C |\<in>| N2. ord_res.production (fset (N1 |\<union>| N2)) C = {}" and
    C_in: "C |\<in>| N1" and
    C_least_false: "is_least_false_clause (N1 |\<union>| N2) C"
  shows "is_least_false_clause N1 C"
  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "C |\<in>| N1"
    using C_in .
next
  have "\<not> ord_res_Interp (fset (N1 |\<union>| N2)) C \<TTurnstile> C"
    using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
    by argo
  thus "\<not> ord_res.interp (fset N1) C \<union> ord_res.production (fset N1) C \<TTurnstile> C"
    unfolding Interp_union_unproductive[of "fset N1" "fset N2", folded union_fset,
        OF finite_fset finite_fset N2_unproductive] .
next
  fix D
  have "\<forall>D |\<in>| N1 |\<union>| N2. D \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset (N1 |\<union>| N2)) D \<TTurnstile> D \<longrightarrow> C \<prec>\<^sub>c D"
    using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
    by argo

  moreover assume "D |\<in>| N1" and "D \<noteq> C" and "\<not> ord_res_Interp (fset N1) D \<TTurnstile> D"

  ultimately show "C \<prec>\<^sub>c D"
    using Interp_union_unproductive[of "fset N1" "fset N2", folded union_fset,
        OF finite_fset finite_fset N2_unproductive]
    by simp
qed

lemma ground_factoring_replicate_max_pos_lit:
  "ord_res.ground_factoring
    (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))
    (C\<^sub>0 + replicate_mset (Suc n) (Pos A))"
  if "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
  for A C\<^sub>0 n
proof (rule ord_res.ground_factoringI)
  show "C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A) =
            add_mset (Pos A) (add_mset (Pos A) (C\<^sub>0 + replicate_mset n (Pos A)))"
    by simp
next
  show "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
    using that .
next
  show "C\<^sub>0 + replicate_mset (Suc n) (Pos A) =
            add_mset (Pos A) (C\<^sub>0 + replicate_mset n (Pos A))"
    by simp
qed simp

lemma ground_factorings_replicate_max_pos_lit:
  assumes
    "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
  shows "m \<le> Suc n \<Longrightarrow> (ord_res.ground_factoring ^^ m)
    (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))
    (C\<^sub>0 + replicate_mset (Suc (Suc n - m)) (Pos A))"
proof (induction m)
  case 0
  show ?case
    by simp
next
  case (Suc m')
  then show ?case
    apply (cases m')
    using assms ground_factoring_replicate_max_pos_lit apply auto[1]
    by (metis (no_types, lifting) Suc_diff_le Suc_leD assms diff_Suc_Suc
        ground_factoring_replicate_max_pos_lit ord_res.ground_factorings_preserves_maximal_literal
        relpowp_Suc_I relpowp_imp_rtranclp)
qed

lemma ord_res_Interp_entails_if_greatest_lit_is_pos:
  assumes C_in: "C \<in> N" and L_greatest: "linorder_lit.is_greatest_in_mset C L" and L_pos: "is_pos L"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof (cases "ord_res.interp N C \<TTurnstile> C")
  case True
  hence "ord_res.production N C = {}"
    by (simp add: ord_res.production_unfold)
  with True show ?thesis
    by simp
next
  case False

  from L_pos obtain A where L_def: "L = Pos A"
    by (cases L) simp_all

  from L_greatest obtain C' where C_def: "C = add_mset L C'"
    unfolding linorder_lit.is_greatest_in_mset_iff
    by (metis insert_DiffM)

  with C_in L_greatest have "A \<in> ord_res.production N C"
    unfolding L_def ord_res.production_unfold
    using False
    by (simp add: linorder_lit.is_greatest_in_mset_iff multi_member_split)
  thus ?thesis
    by (simp add: true_cls_def C_def L_def)
qed

lemma right_unique_ord_res_2: "right_unique (ord_res_2 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_2 N s s'" and step2: "ord_res_2 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_2.cases)
    case hyps1: (factoring U\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 U\<^sub>e\<^sub>f'1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_2.cases)
      case (factoring U\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f'2)
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution U\<^sub>r U\<^sub>e\<^sub>f C L D CD U\<^sub>r')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution U\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 D1 CD1 U\<^sub>r'1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_2.cases)
      case (factoring U\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f'2)
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    next
      case (resolution U\<^sub>r U\<^sub>e\<^sub>f C L D CD U\<^sub>r')
      with hyps1 show ?thesis
        by (metis (mono_tags, lifting) Uniq_is_least_false_clause
            linorder_lit.Uniq_is_maximal_in_mset ord_res.Uniq_production_eq_singleton
            ord_res.unique_ground_resolution prod.inject the1_equality')
    qed
  qed
qed

lemma right_unique_ord_res_2_step: "right_unique ord_res_2_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_2_step x y \<Longrightarrow> ord_res_2_step x z \<Longrightarrow> y = z"
    apply (cases x; cases y; cases z)
    apply (simp add: ord_res_2_step.simps)
    using right_unique_ord_res_2[THEN right_uniqueD]
    by blast
qed

end

end