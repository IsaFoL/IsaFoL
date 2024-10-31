theory ORD_RES_4
  imports
    ORD_RES
    Implicit_Exhaustive_Factorization
    Exhaustive_Resolution
begin

section \<open>ORD-RES-4 (implicit factorization)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_4 where
  factoring: "
    NN = iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<Longrightarrow>
    is_least_false_clause NN C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<F>' = finsert C \<F> \<Longrightarrow>
    ord_res_4 N (U\<^sub>e\<^sub>r, \<F>) (U\<^sub>e\<^sub>r, \<F>')" |

  resolution: "
    NN = iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<Longrightarrow>
    is_least_false_clause NN C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| NN \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset NN) D = {atm_of L} \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    ord_res_4 N (U\<^sub>e\<^sub>r, \<F>) (U\<^sub>e\<^sub>r', \<F>)"

inductive ord_res_4_step where
  "ord_res_4 N s s' \<Longrightarrow> ord_res_4_step (N, s) (N, s')"

inductive ord_res_4_final where
  "ord_res_final (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<Longrightarrow> ord_res_4_final (N, U\<^sub>e\<^sub>r, \<F>)"

sublocale ord_res_4_semantics: semantics where
  step = ord_res_4_step and
  final = ord_res_4_final
proof unfold_locales
  fix S4 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" where
    S4_def: "S4 = (N, (U\<^sub>e\<^sub>r, \<F>))"
    by (metis prod.exhaust)

  assume "ord_res_4_final S4"
  hence "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<or> \<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
    by (simp add: S4_def ord_res_4_final.simps ord_res_final_def)
  thus "finished ord_res_4_step S4"
  proof (elim disjE)
    assume "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    hence "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) {#}"
      using is_least_false_clause_mempty by metis
    hence "\<nexists>C L. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C \<and> linorder_lit.is_maximal_in_mset C L"
      by (metis Uniq_D Uniq_is_least_false_clause bot_fset.rep_eq fBex_fempty
          linorder_lit.is_maximal_in_mset_iff set_mset_empty)
    hence "\<nexists>x. ord_res_4 N (U\<^sub>e\<^sub>r, \<F>) x"
      by (auto simp: S4_def elim: ord_res_4.cases)
    thus ?thesis
      by (simp add: S4_def finished_def ord_res_4_step.simps)
  next
    assume "\<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
    hence "\<nexists>C. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
      unfolding ex_false_clause_def is_least_false_clause_def
      by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
          linorder_cls.is_least_in_fset_ffilterD(2))
    hence "\<nexists>x. ord_res_4 N (U\<^sub>e\<^sub>r, \<F>) x"
      by (auto simp: S4_def elim: ord_res_4.cases)
    thus ?thesis
      by (simp add: S4_def finished_def ord_res_4_step.simps)
  qed
qed

lemma right_unique_ord_res_4: "right_unique (ord_res_4 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_4 N s s'" and step2: "ord_res_4 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_4.cases)
    case hyps1: (factoring NN1 \<F>1 U\<^sub>e\<^sub>r1 C1 L1 \<F>1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_4.cases)
      case (factoring NN2 \<F>2 U\<^sub>e\<^sub>r2 C2 L2 \<F>2')
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution NN2 \<F>2 U\<^sub>e\<^sub>r2 C2 L2 D2 U\<^sub>e\<^sub>r2')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
          the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution NN1 \<F>1 U\<^sub>e\<^sub>r1 C1 L1 D1 U\<^sub>e\<^sub>r1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_4.cases)
      case (factoring NN \<F> U\<^sub>e\<^sub>r C L \<F>')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
          the1_equality')
      thus ?thesis ..
    next
      case (resolution NN \<F> U\<^sub>e\<^sub>r C L D U\<^sub>e\<^sub>r')
      with hyps1 show ?thesis
        by (metis (mono_tags, lifting) Uniq_D Uniq_is_least_false_clause
          ord_res.less_trm_iff_less_cls_if_mem_production insertI1 linorder_cls.neq_iff
          linorder_lit.Uniq_is_maximal_in_mset prod.inject)
    qed
  qed
qed

lemma right_unique_ord_res_4_step: "right_unique ord_res_4_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_4_step x y \<Longrightarrow> ord_res_4_step x z \<Longrightarrow> y = z"
    using right_unique_ord_res_4[THEN right_uniqueD]
    by (elim ord_res_4_step.cases) (metis prod.inject)
qed

lemma ex_ord_res_4_if_not_final:
  assumes "\<not> ord_res_4_final S"
  shows "\<exists>S'. ord_res_4_step S S'"
proof -
  from assms obtain N U\<^sub>e\<^sub>r \<F> where
    S_def: "S = (N, (U\<^sub>e\<^sub>r, \<F>))" and
    "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    "ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
    by (metis ord_res_4_final.intros ord_res_final_def surj_pair)

  obtain C where C_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
    using \<open>ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))\<close>
      obtains_least_false_clause_if_ex_false_clause
    by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using ord_res_4.factoring[OF refl C_least_false C_max] S_def is_pos_def
      by (metis ord_res_4_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    thus ?thesis
      using ord_res_4.resolution[OF refl C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_4_step.simps)
  qed
qed

corollary ord_res_4_step_safe: "ord_res_4_final S \<or> (\<exists>S'. ord_res_4_step S S')"
  using ex_ord_res_4_if_not_final by metis

end

end