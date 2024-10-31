theory ORD_RES_1
  imports ORD_RES
begin


section \<open>ORD-RES-1 (deterministic)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_1 where
  factoring: "
    is_least_false_clause N C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    ord_res.ground_factoring C C' \<Longrightarrow>
    N' = finsert C' N \<Longrightarrow>
    ord_res_1 N N'" |

  resolution: "
    is_least_false_clause N C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset N) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    N' = finsert CD N \<Longrightarrow>
    ord_res_1 N N'"

lemma
  assumes "ord_res.ground_resolution C D CD"
  shows "D \<prec>\<^sub>c C"
  using assms
  by (auto simp add: ord_res.ground_resolution.simps)

lemma right_unique_ord_res_1: "right_unique ord_res_1"
proof (rule right_uniqueI)
  fix N N' N'' :: "'f gterm clause fset"
  assume step1: "ord_res_1 N N'" and step2: "ord_res_1 N N''"
  from step1 show "N' = N''"
  proof (cases N N' rule: ord_res_1.cases)
    case hyps1: (factoring C1 L1 C1')
    from step2 show ?thesis
    proof (cases N N'' rule: ord_res_1.cases)
      case hyps2: (factoring C2 L2 C2')
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "C1' = C2'"
        by (metis (no_types, lifting) Uniq_D ord_res.unique_ground_factoring)
      with hyps1 hyps2 show ?thesis
        by argo
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution C1 L1 D1 CD1)
    from step2 show ?thesis
    proof (cases N N'' rule: ord_res_1.cases)
      case hyps2: (factoring C2 L2 C2')
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have "D1 = D2"
        by (metis (mono_tags) Uniq_D ord_res.Uniq_production_eq_singleton)
      with hyps1 hyps2 have "CD1 = CD2"
        by (metis (no_types, lifting) Uniq_D \<open>C1 = C2\<close> ord_res.unique_ground_resolution)
      with hyps1 hyps2 show ?thesis
        by argo
    qed
  qed
qed

definition ord_res_1_final where
  "ord_res_1_final N \<longleftrightarrow> ord_res_final N"

inductive ord_res_1_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_1_load N N"

sublocale ord_res_1_semantics: semantics where
  step = ord_res_1 and
  final = ord_res_1_final
proof unfold_locales
  fix N :: "'f gterm clause fset"
  assume "ord_res_1_final N"
  thus "finished ord_res_1 N"
    unfolding ord_res_1_final_def ord_res_final_def
  proof (elim disjE)
    assume "{#} |\<in>| N"
    have False if "ord_res_1 N N'" for N'
      using that
    proof (cases N N' rule: ord_res_1.cases)
      case hyps: (factoring C L C')
      from hyps \<open>{#} |\<in>| N\<close> have "C = {#}"
        unfolding is_least_false_clause_def
        by (metis (no_types, lifting) emptyE ffmember_filter linorder_cls.dual_order.strict_trans
            linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl
            ord_res.multp_if_all_left_smaller set_mset_empty true_cls_empty)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    next
      case hyps: (resolution C L D CD)
      from hyps \<open>{#} |\<in>| N\<close> have "C = {#}"
        unfolding is_least_false_clause_def
        by (metis (no_types, lifting) emptyE ffmember_filter linorder_cls.dual_order.strict_trans
            linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl
            ord_res.multp_if_all_left_smaller set_mset_empty true_cls_empty)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    qed
    thus "finished ord_res_1 N"
      unfolding finished_def by metis
  next
    assume "\<not> ex_false_clause (fset N)"
    have False if "ord_res_1 N N'" for N'
      using that
    proof (cases N N' rule: ord_res_1.cases)
      case (factoring C L C')
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def is_least_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    next
      case (resolution C L D CD)
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def is_least_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    qed
    thus "finished ord_res_1 N"
      unfolding finished_def by metis
  qed
qed

sublocale ord_res_1_language: language where
  step = ord_res_1 and
  final = ord_res_1_final and
  load = ord_res_1_load
  by unfold_locales

lemma ex_ord_res_1_if_not_final:
  assumes "\<not> ord_res_1_final N"
  shows "\<exists>N'. ord_res_1 N N'"
proof -
  from assms have "{#} |\<notin>| N" and "ex_false_clause (fset N)"
    unfolding ord_res_1_final_def ord_res_final_def by argo+

  obtain C where C_least_false: "is_least_false_clause N C"
    using \<open>ex_false_clause (fset N)\<close> obtains_least_false_clause_if_ex_false_clause by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)

    hence "\<not> linorder_lit.is_greatest_in_mset C L"
      using pos_lit_not_greatest_if_maximal_in_least_false_clause
      using C_least_false is_least_false_clause_def by blast

    then obtain C' where "ord_res.ground_factoring C C'"
      using ex_ground_factoringI C_max Pos by metis

    thus ?thesis
      using ord_res_1.factoring
      by (metis \<open>is_least_false_clause N C\<close> is_pos_def ord_res.ground_factoring.cases)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset N) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain CD where
      "ord_res.ground_resolution C D CD"
      using ex_ground_resolutionI C_max Neg by metis

    ultimately show ?thesis
      using ord_res_1.resolution[of N C L D CD "finsert CD N"]
      using C_least_false C_max Neg by auto
  qed
qed

corollary ord_res_1_safe: "ord_res_1_final N \<or> (\<exists>N'. ord_res_1 N N')"
  using ex_ord_res_1_if_not_final by metis

end

end