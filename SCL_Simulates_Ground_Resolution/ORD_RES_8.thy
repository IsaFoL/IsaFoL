theory ORD_RES_8
  imports
    Background
    Implicit_Exhaustive_Factorization
    Exhaustive_Resolution
    Clause_Could_Propagate
begin

section \<open>ORD-RES-8 (atom-guided literal trail construction)\<close>

type_synonym 'f ord_res_8_state =
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gliteral \<times> 'f gclause option) list"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_8 where
  decide_neg: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')" |

  propagate: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    linorder_lit.is_greatest_in_mset C (Pos A) \<Longrightarrow>
    \<Gamma>' = (Pos A, Some C) # \<Gamma> \<Longrightarrow>
    ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')" |

  factorize: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<not> linorder_lit.is_greatest_in_mset C (Pos A) \<Longrightarrow>
    \<F>' = finsert C \<F> \<Longrightarrow>
    ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)" |

  resolution: "
    linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> D|} D \<Longrightarrow>
    linorder_lit.is_maximal_in_mset D (Neg A) \<Longrightarrow>
    map_of \<Gamma> (Pos A) = Some (Some C) \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r \<Longrightarrow>
    \<Gamma>' = dropWhile (\<lambda>Ln. \<forall>K.
      linorder_lit.is_maximal_in_mset (eres C D) K \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma> \<Longrightarrow>
    ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')"

lemma right_unique_ord_res_8:
  fixes N :: "'f gclause fset"
  shows "right_unique (ord_res_8 N)"
proof (rule right_uniqueI)
  fix x y z
  assume step1: "ord_res_8 N x y" and step2: "ord_res_8 N x z"
  show "y = z"
    using step1
  proof (cases N x y rule: ord_res_8.cases)
    case step1_hyps: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_8.cases)
      case (decide_neg A \<Gamma>')
      with step1_hyps show ?thesis
        by (metis (no_types, lifting) linorder_trm.dual_order.asym linorder_trm.is_least_in_fset_iff)
    next
      case (propagate A2 C2 \<Gamma>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
            linorder_cls.is_least_in_fset_ffilterD(2) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
      thus ?thesis ..
    next
      case (factorize A2 C2 \<F>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
            linorder_cls.is_least_in_fset_ffilterD(2) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
      thus ?thesis ..
    next
      case (resolution D2 A2 C2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      with step1_hyps have False
        by (metis linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case step1_hyps: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_8.cases)
      case (decide_neg A2 \<Gamma>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
            linorder_cls.is_least_in_fset_ffilterD(2) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
      thus ?thesis ..
    next
      case (propagate A2 C2 \<Gamma>2')
      with step1_hyps show ?thesis
        by (metis (no_types, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_trm.dual_order.asym linorder_trm.is_least_in_fset_iff The_optional_eq_SomeI)
    next
      case (factorize A2 C2 \<F>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_trm.Uniq_is_least_in_fset the1_equality')
      thus ?thesis ..
    next
      case (resolution D2 A2 C2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      with step1_hyps have False
        by (metis linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case step1_hyps: (factorize \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<F>')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_8.cases)
      case (decide_neg A2 \<Gamma>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
            linorder_cls.is_least_in_fset_ffilterD(2) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
      thus ?thesis ..
    next
      case (propagate A2 C2 \<Gamma>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_trm.Uniq_is_least_in_fset the1_equality')
      thus ?thesis ..
    next
      case (factorize A2 C2 \<F>2')
      with step1_hyps show ?thesis
        by (metis (no_types, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_trm.Uniq_is_least_in_fset the1_equality')
    next
      case (resolution D2 A2 C2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      with step1_hyps have False
        by (metis linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case step1_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D A C U\<^sub>e\<^sub>r' \<Gamma>')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_8.cases)
      case (decide_neg A \<Gamma>')
      with step1_hyps have False
        by (metis (no_types, opaque_lifting) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>')
      with step1_hyps have False
        by (metis (no_types, opaque_lifting) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (factorize A C \<F>')
      with step1_hyps have False
        by (metis (no_types, opaque_lifting) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case step2_hyps: (resolution D2 A2 C2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have "D2 = D"
        using \<open>linorder_cls.is_least_in_fset (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D\<close>
        using \<open>linorder_cls.is_least_in_fset (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D2\<close>
        by (metis linorder_cls.Uniq_is_least_in_fset Uniq_D)

      have "A2 = A"
        using \<open>linorder_lit.is_maximal_in_mset D (Neg A)\<close>
        using \<open>linorder_lit.is_maximal_in_mset D2 (Neg A2)\<close>
        unfolding \<open>D2 = D\<close>
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset literal.sel(2))

      have "C2 = C"
        using step1_hyps(5) step2_hyps(4)
        unfolding \<open>A2 = A\<close>
        by simp

      show ?thesis
        unfolding \<open>y = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close> \<open>z = (U\<^sub>e\<^sub>r2', \<F>, \<Gamma>2')\<close> prod.inject
      proof (intro conjI)
        show "U\<^sub>e\<^sub>r' = U\<^sub>e\<^sub>r2'"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r\<close> \<open>U\<^sub>e\<^sub>r2' = finsert (eres C2 D2) U\<^sub>e\<^sub>r\<close>
          unfolding \<open>D2 = D\<close> \<open>C2 = C\<close> ..
      next
        show "\<F> = \<F>" ..
      next
        show "\<Gamma>' = \<Gamma>2'"
          using step1_hyps(7) step2_hyps(6)
          unfolding \<open>D2 = D\<close> \<open>C2 = C\<close>
          by argo
      qed
    qed
  qed
qed

inductive ord_res_8_final :: "'f ord_res_8_state \<Rightarrow> bool" where
  model_found: "
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    ord_res_8_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" |

  contradiction_found: "
    {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<Longrightarrow>
    ord_res_8_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"

sublocale ord_res_8_semantics: semantics where
  step = "constant_context ord_res_8" and
  final = ord_res_8_final
proof unfold_locales
  fix S :: "'f ord_res_8_state"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" and
    \<Gamma> :: "('f gterm literal \<times> 'f gterm literal multiset option) list" where
    S_def: "S = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
    by (metis prod.exhaust)

  assume "ord_res_8_final S"

  hence "\<nexists>x. ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) x"
    unfolding S_def
  proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" rule: ord_res_8_final.cases)
    case model_found

    have "\<nexists>A. linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
      using \<open>\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>)\<close>
      using linorder_trm.is_least_in_ffilter_iff by fastforce

    moreover have "\<nexists>C. linorder_cls.is_least_in_fset
      (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
      using \<open>\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)\<close>
      by (metis linorder_cls.is_least_in_ffilter_iff)

    ultimately show ?thesis
      unfolding ord_res_8.simps by blast
  next
    case contradiction_found

    hence "\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C"
      using trail_false_cls_mempty by metis

    moreover have "\<nexists>D A. linorder_cls.is_least_in_fset (ffilter (trail_false_cls \<Gamma>)
      (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<and> ord_res.is_maximal_lit (Neg A) D"
      by (metis empty_iff linorder_cls.is_least_in_ffilter_iff linorder_cls.leD
          linorder_lit.is_maximal_in_mset_iff local.contradiction_found(1) mempty_lesseq_cls
          set_mset_empty trail_false_cls_mempty)

    ultimately show ?thesis
      unfolding ord_res_8.simps by blast
  qed

  thus "finished (constant_context ord_res_8) S"
    by (simp add: S_def finished_def constant_context.simps)
qed

definition trail_is_sorted where
  "trail_is_sorted N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<Gamma>. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<longrightarrow>
      sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>)"

lemma ord_res_8_preserves_trail_is_sorted:
  assumes
    step: "ord_res_8 N s s'" and
    invar: "trail_is_sorted N s"
  shows "trail_is_sorted N s'"
  using step
proof (cases N s s' rule: ord_res_8.cases)
  case step_hyps: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')

  have "\<forall>x |\<in>| trail_atms \<Gamma>. x \<prec>\<^sub>t A"
    using step_hyps unfolding linorder_trm.is_least_in_ffilter_iff by simp

  hence "\<forall>x \<in> set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t A"
    by (simp add: fset_trail_atms)

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def)

  ultimately have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    by (simp add: \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>)

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> trail_is_sorted_def)
next
  case step_hyps: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>')

  have "\<forall>x |\<in>| trail_atms \<Gamma>. x \<prec>\<^sub>t A"
    using step_hyps unfolding linorder_trm.is_least_in_ffilter_iff by simp

  hence "\<forall>x \<in> set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t A"
    by (simp add: fset_trail_atms)

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def)

  ultimately have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    by (simp add: \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>)

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> trail_is_sorted_def)
next
  case (factorize \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<F>')

  have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def)

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)\<close> trail_is_sorted_def)
next
  case step_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D A C U\<^sub>e\<^sub>r' \<Gamma>')

  have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def)

  hence "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    unfolding step_hyps(7) by (rule sorted_wrt_dropWhile)

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close> trail_is_sorted_def)
qed

inductive trail_annotations_invars
  for N :: "'f gterm literal multiset fset"
  where
    Nil:
      "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, [])" |
    Cons_None:
      "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, (L, None) # \<Gamma>)"
      if "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" |
    Cons_Some:
      "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, (L, Some D) # \<Gamma>)"
      if "linorder_lit.is_greatest_in_mset D L" and
         "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
         "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}" and
         "linorder_cls.is_least_in_fset
           {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> D L|} D" and
         "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"

lemma
  assumes
    "linorder_lit.is_greatest_in_mset C L" and
    "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}" and
    "\<not> trail_defined_cls \<Gamma> C"
  shows "clause_could_propagate \<Gamma> C L"
  unfolding clause_could_propagate_iff
proof (intro conjI)
  show "linorder_lit.is_maximal_in_mset C L"
    using \<open>linorder_lit.is_greatest_in_mset C L\<close>
    by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)

  hence "L \<in># C"
    unfolding linorder_lit.is_maximal_in_mset_iff ..

  show "\<forall>K \<in># C. K \<noteq> L \<longrightarrow> trail_false_lit \<Gamma> K"
    using \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close>
    unfolding trail_false_cls_def
    by simp

  hence "\<forall>K \<in># C. K \<noteq> L \<longrightarrow> trail_defined_lit \<Gamma> K"
    using trail_defined_lit_iff_true_or_false by metis

  thus "\<not> trail_defined_lit \<Gamma> L"
    using \<open>\<not> trail_defined_cls \<Gamma> C\<close> \<open>L \<in># C\<close>
    unfolding trail_defined_cls_def
    by metis
qed

lemma propagating_clause_in_clauses:
  assumes "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" and "map_of \<Gamma> L = Some (Some C)"
  shows "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
  using assms
proof (induction "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" arbitrary: \<Gamma> rule: trail_annotations_invars.induct)
  case Nil
  hence False
    by simp
  thus ?case ..
next
  case (Cons_None \<Gamma> K)
  thus ?case
    by (metis map_of_Cons_code(2) option.discI option.inject)
next
  case (Cons_Some D K \<Gamma>)
  thus ?case
    by (metis map_of_Cons_code(2) option.inject)
qed

lemma trail_annotations_invars_mono_wrt_trail_suffix:
  assumes "suffix \<Gamma>' \<Gamma>" "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
  shows "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
  using assms(2,1)
proof (induction "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" arbitrary: \<Gamma> \<Gamma>' rule: trail_annotations_invars.induct)
  case Nil
  thus ?case
    by (simp add: trail_annotations_invars.Nil)
next
  case (Cons_None \<Gamma> L)
  have "\<Gamma>' = (L, None) # \<Gamma> \<or> suffix \<Gamma>' \<Gamma>"
    using Cons_None.prems unfolding suffix_Cons .
  thus ?case
    using Cons_None.hyps
    by (metis trail_annotations_invars.Cons_None)
next
  case (Cons_Some C L \<Gamma>)
  have "\<Gamma>' = (L, Some C) # \<Gamma> \<or> suffix \<Gamma>' \<Gamma>"
    using Cons_Some.prems unfolding suffix_Cons .
  then show ?case
    using Cons_Some.hyps
    by (metis trail_annotations_invars.Cons_Some)
qed

lemma ord_res_8_preserves_trail_annotations_invars:
  assumes
    step: "ord_res_8 N s s'" and
    invars:
      "trail_annotations_invars N s"
      "trail_is_sorted N s"
  shows "trail_annotations_invars N s'"
  using step
proof (cases N s s' rule: ord_res_8.cases)
  case step_hyps: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')
  show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
  proof (rule trail_annotations_invars.Cons_None)
    show "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
      using invars(1) by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>)
  qed
next
  case step_hyps: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>')
  show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>
  proof (rule trail_annotations_invars.Cons_Some)
    show "ord_res.is_strictly_maximal_lit (Pos A) C"
      using step_hyps by argo
  next
    show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using step_hyps(5)
      by (simp add: linorder_cls.is_least_in_fset_iff)
  next
    show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
      using step_hyps(5)
      by (simp add: linorder_cls.is_least_in_fset_iff clause_could_propagate_def)
  next
    show "linorder_cls.is_least_in_fset
      {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} C"
      using step_hyps by argo
  next
    show "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
      using invars(1) by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>)
  qed
next
  case step_hyps: (factorize \<F> U\<^sub>e\<^sub>r \<Gamma> A E \<F>')

  hence "efac E \<noteq> E"
    by (metis (no_types, lifting) ex1_efac_eq_factoring_chain ex_ground_factoringI
        linorder_cls.is_least_in_ffilter_iff clause_could_propagate_iff)

  moreover have "clause_could_propagate \<Gamma> E (Pos A)"
    using step_hyps unfolding linorder_cls.is_least_in_ffilter_iff by metis

  ultimately have "ord_res.is_strictly_maximal_lit (Pos A) (efac E)"
    unfolding clause_could_propagate_def
    using ex1_efac_eq_factoring_chain ex_ground_factoringI
      ord_res.ground_factorings_preserves_maximal_literal by blast

  have "\<F> |\<subseteq>| \<F>'"
    unfolding \<open>\<F>' = finsert E \<F>\<close> by auto

  have "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
    using invars(1) by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>)

  moreover have "\<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A"
    using step_hyps unfolding linorder_trm.is_least_in_ffilter_iff by blast

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)\<close>
  proof (induction "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" arbitrary: \<Gamma> rule: trail_annotations_invars.induct)
    case Nil
    show ?case
      by (simp add: trail_annotations_invars.Nil)
  next
    case (Cons_None \<Gamma> L)
    show ?case
    proof (rule trail_annotations_invars.Cons_None)
      have "\<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A"
        using Cons_None.prems by (simp add: fset_trail_atms)

      thus "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)"
        using Cons_None.hyps by argo
    qed
  next
    case (Cons_Some C L \<Gamma>)

    have
      "clause_could_propagate \<Gamma> C L" and
      C_least: "\<forall>y|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> y L \<longrightarrow> C \<prec>\<^sub>c y"
      using Cons_Some.hyps(4) unfolding linorder_cls.is_least_in_ffilter_iff by metis+

    hence "ord_res.is_maximal_lit L C"
      unfolding clause_could_propagate_def by argo

    show ?case
    proof (rule trail_annotations_invars.Cons_Some)
      show "ord_res.is_strictly_maximal_lit L C"
        using \<open>ord_res.is_strictly_maximal_lit L C\<close> .

      have "efac C = C"
        using Cons_Some
        by (metis (no_types, opaque_lifting) efac_spec is_pos_def linorder_lit.Uniq_is_maximal_in_mset
            linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one
            nex_strictly_maximal_pos_lit_if_neq_efac the1_equality')

      hence "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>\<F> |\<subseteq>| \<F>'\<close>
        by (smt (verit, best) assms fimage_iff fsubsetD iefac_def)

      show "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<open>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> .

      show "trail_false_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
        using \<open>trail_false_cls \<Gamma> {#x \<in># C. x \<noteq> L#}\<close> .

      show "linorder_cls.is_least_in_fset
        {|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C L|} C"
        unfolding linorder_cls.is_least_in_ffilter_iff
      proof (intro conjI ballI impI)
        show "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using \<open>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
      next
        show "clause_could_propagate \<Gamma> C L"
          using \<open>clause_could_propagate \<Gamma> C L\<close> .
      next
        fix D :: "'f gterm literal multiset"
        assume "D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "D \<noteq> C" and "clause_could_propagate \<Gamma> D L"

        have "atm_of L \<prec>\<^sub>t A"
          using Cons_Some.prems by (simp add: fset_trail_atms)

        hence "L \<prec>\<^sub>l Pos A"
          by (cases L) simp_all

        moreover have "ord_res.is_maximal_lit L D"
          using \<open>clause_could_propagate \<Gamma> D L\<close> unfolding clause_could_propagate_iff by metis

        ultimately have "D \<prec>\<^sub>c efac E"
          using \<open>ord_res.is_strictly_maximal_lit (Pos A) (efac E)\<close>
          by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
              linorder_lit.multp_if_maximal_less_that_maximal)

        hence "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using \<open>D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
          unfolding \<open>\<F>' = finsert E \<F>\<close>
          using iefac_def by force
          
        thus "C \<prec>\<^sub>c D"
          using C_least \<open>D \<noteq> C\<close> \<open>clause_could_propagate \<Gamma> D L\<close> by metis
      qed

      have "\<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A"
        using Cons_Some.prems by (simp add: fset_trail_atms)

      thus "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)"
        using Cons_Some.hyps by argo
    qed
  qed
next
  case step_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r E A D U\<^sub>e\<^sub>r' \<Gamma>')

  show ?thesis
  proof (cases "eres D E = {#}")
    case True
    hence "\<nexists>K. ord_res.is_maximal_lit K (eres D E)"
      by (simp add: linorder_lit.is_maximal_in_mset_iff)
    hence "\<Gamma>' = []"
      unfolding step_hyps by simp
    thus ?thesis
      unfolding \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close>
      using trail_annotations_invars.Nil by metis
  next
    case False

    then obtain K where eres_max_lit: "linorder_lit.is_maximal_in_mset (eres D E) K"
      using linorder_lit.ex_maximal_in_mset by metis

    have \<Gamma>'_eq: "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"
      unfolding step_hyps(7)
    proof (rule dropWhile_cong)
      show "\<Gamma> = \<Gamma>" ..
    next
      fix x :: "'f gterm literal \<times> 'f gterm literal multiset option"
      assume "x \<in> set \<Gamma>"
      show "(\<forall>K. ord_res.is_maximal_lit K (eres D E) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst x)) =
        (atm_of K \<preceq>\<^sub>t atm_of (fst x))"
        unfolding case_prod_beta
        using eres_max_lit
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
    qed

    have "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
      using invars(1) by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>)

    moreover have "suffix \<Gamma>' \<Gamma>"
      unfolding step_hyps
      using suffix_dropWhile by metis

    moreover have "\<forall>Ln \<in> set \<Gamma>'. \<not> (atm_of K \<preceq>\<^sub>t atm_of (fst Ln))"
      unfolding \<Gamma>'_eq
    proof (rule ball_set_dropWhile_if_sorted_wrt_and_monotone_on)
      have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
        using invars(2)
        by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def sorted_wrt_map)

      thus "sorted_wrt (\<lambda>x y. fst y \<prec>\<^sub>l fst x) \<Gamma>"
      proof (rule sorted_wrt_mono_rel[rotated])
        show "\<And>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x) \<Longrightarrow> fst y \<prec>\<^sub>l fst x"
          by (metis (no_types, lifting) linorder_lit.antisym_conv3 linorder_trm.dual_order.asym
              literal.exhaust_sel ord_res.less_lit_simps(1) ord_res.less_lit_simps(3)
              ord_res.less_lit_simps(4))
      qed
    next
      show "monotone_on (set \<Gamma>) (\<lambda>x y. fst y \<prec>\<^sub>l fst x) (\<lambda>Ln y. y \<le> Ln)
     (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln))"
        apply (simp add: monotone_on_def)
        by (smt (verit, best) Neg_atm_of_iff Pos_atm_of_iff linorder_lit.order.asym
            linorder_trm.less_linear linorder_trm.order.strict_trans ord_res.less_lit_simps(1)
            ord_res.less_lit_simps(3) ord_res.less_lit_simps(4))
    qed

    ultimately show ?thesis
      unfolding \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close>
    proof (induction "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" arbitrary: \<Gamma> \<Gamma>' rule: trail_annotations_invars.induct)
      case Nil
      thus ?case
        by (simp add: trail_annotations_invars.Nil)
    next
      case (Cons_None \<Gamma> L)
      thus ?case
        by (metis insert_iff list.simps(15) suffix_Cons suffix_order.dual_order.refl
            trail_annotations_invars.Cons_None)
    next
      case (Cons_Some C L \<Gamma>)

      have
        "clause_could_propagate \<Gamma> C L" and
        C_least: "\<forall>y|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> y L \<longrightarrow> C \<prec>\<^sub>c y"
        using Cons_Some.hyps(4) unfolding linorder_cls.is_least_in_ffilter_iff by metis+

      hence C_max_lit: "ord_res.is_maximal_lit L C"
        unfolding clause_could_propagate_def by argo

      obtain \<Gamma>'' where "(L, Some C) # \<Gamma> = \<Gamma>'' @ \<Gamma>'"
        using Cons_Some.prems by (auto elim: suffixE)

      show ?case
      proof (cases \<Gamma>'')
        case Nil
        hence "\<Gamma>' = (L, Some C) # \<Gamma>"
          using \<open>(L, Some C) # \<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> by simp

        show ?thesis
          unfolding \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>
        proof (rule trail_annotations_invars.Cons_Some)
          show "ord_res.is_strictly_maximal_lit L C"
            using \<open>ord_res.is_strictly_maximal_lit L C\<close> .

          show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
            using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp

          show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}"
            using \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close> .

          show "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). clause_could_propagate \<Gamma> C L|} C"
            unfolding linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
              using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')\<close> .
          next
            show "clause_could_propagate \<Gamma> C L"
              using Cons_Some.hyps(4) unfolding linorder_cls.is_least_in_ffilter_iff by metis
          next
            fix x :: "'f gterm literal multiset"
            assume "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
              and "x \<noteq> C"
              and "clause_could_propagate \<Gamma> x L"

            have "linorder_lit.is_maximal_in_mset x L"
              using \<open>clause_could_propagate \<Gamma> x L\<close> unfolding clause_could_propagate_def by argo

            moreover have "L \<prec>\<^sub>l K"
              using \<open>\<forall>Ln \<in> set \<Gamma>'. \<not> (atm_of K \<preceq>\<^sub>t atm_of (fst Ln))\<close>
              unfolding \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>
              apply simp
              by (metis Neg_atm_of_iff linorder_lit.antisym_conv3 linorder_trm.less_linear
                  literal.collapse(1) ord_res.less_lit_simps(1) ord_res.less_lit_simps(3)
                  ord_res.less_lit_simps(4))

            ultimately have "set_mset x \<noteq> set_mset (eres D E)"
              using eres_max_lit
              by (metis linorder_lit.is_maximal_in_mset_iff linorder_lit.neq_iff)

            hence "x \<noteq> iefac \<F> (eres D E)"
              using iefac_def by auto

            hence "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              using \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')\<close>
              unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
              by simp

            then show "C \<prec>\<^sub>c x"
              using C_least \<open>x \<noteq> C\<close> \<open>clause_could_propagate \<Gamma> x L\<close> by metis
          qed

          show "trail_annotations_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>)"
            using Cons_Some
            by (simp add: \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>)
        qed
      next
        case (Cons a list)
        then show ?thesis
          by (metis Cons_Some.hyps(6) Cons_Some.prems \<open>(L, Some C) # \<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> empty_iff
              list.set(1) list.set_intros(1) self_append_conv2 suffix_Cons)
      qed
    qed
  qed
qed

definition trail_is_lower_set where
  "trail_is_lower_set N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<Gamma>. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<longrightarrow>
      linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"

lemma atoms_not_in_clause_set_undefined_if_trail_is_sorted_lower_set:
  assumes invar: "trail_is_lower_set N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
  shows "\<forall>A. A |\<notin>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) \<longrightarrow> A |\<notin>| trail_atms \<Gamma>"
  using invar[unfolded trail_is_lower_set_def, simplified]
  by (metis Un_iff linorder_trm.is_lower_set_iff sup.absorb2)

lemma ord_res_8_preserves_atoms_in_trail_lower_set:
  assumes
    step: "ord_res_8 N s s'" and
    invars:
      "trail_is_lower_set N s"
      "trail_annotations_invars N s"
      "trail_is_sorted N s"
  shows "trail_is_lower_set N s'"
  using step
proof (cases N s s' rule: ord_res_8.cases)
  case step_hyps: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')

  have
    A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
    A_gt: "\<forall>x |\<in>| trail_atms \<Gamma>. x \<prec>\<^sub>t A" and
    A_least: "\<forall>x |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>w |\<in>| trail_atms \<Gamma>. w \<prec>\<^sub>t x) \<longrightarrow> x \<noteq> A \<longrightarrow> A \<prec>\<^sub>t x"
    using step_hyps unfolding linorder_trm.is_least_in_ffilter_iff by simp_all

  have "trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)"
    using step_hyps by simp

  have
    inv1: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    inv2: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using invars(1,3)
    by (simp_all only: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_lower_set_def trail_is_sorted_def)

  have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> list.map sorted_wrt.simps
  proof (intro conjI ballI)
    fix x
    assume "x \<in> set \<Gamma>"
    hence "atm_of (fst x) |\<in>| trail_atms \<Gamma>"
      by (auto simp: fset_trail_atms)
    hence "atm_of (fst x) \<prec>\<^sub>t atm_of (Neg A)"
      using A_gt by simp
    thus "atm_of (fst x) \<prec>\<^sub>t atm_of (fst (Neg A, None))"
      unfolding comp_def prod.sel .
  next
    show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
      using inv1 .
  qed

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding \<open>trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)\<close> finsert.rep_eq
  proof (rule linorder_trm.is_lower_set_insertI)
    show "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using A_in .
  next
    show "\<forall>w |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t A \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
      using A_least inv2
      by (metis linorder_trm.is_lower_set_iff linorder_trm.not_less_iff_gr_or_eq)
  next
    show "linorder_trm.is_lower_fset (trail_atms \<Gamma>)
     (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
      using inv2 .
  qed

  ultimately show ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> trail_is_lower_set_def)
next
  case step_hyps: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>')

  have
    A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
    A_gt: "\<forall>x |\<in>| trail_atms \<Gamma>. x \<prec>\<^sub>t A" and
    A_least: "\<forall>x |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>w |\<in>| trail_atms \<Gamma>. w \<prec>\<^sub>t x) \<longrightarrow> x \<noteq> A \<longrightarrow> A \<prec>\<^sub>t x"
    using step_hyps unfolding linorder_trm.is_least_in_ffilter_iff by simp_all

  have "trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)"
    using step_hyps by simp

  have
    inv1: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    inv2: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using invars(1,3)
    by (simp_all only: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_lower_set_def trail_is_sorted_def)

  have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close> list.map sorted_wrt.simps
  proof (intro conjI ballI)
    fix x
    assume "x \<in> set \<Gamma>"
    hence "atm_of (fst x) |\<in>| trail_atms \<Gamma>"
      by (auto simp: fset_trail_atms)
    hence "atm_of (fst x) \<prec>\<^sub>t atm_of (Pos A)"
      using A_gt by simp
    thus "atm_of (fst x) \<prec>\<^sub>t atm_of (fst (Pos A, Some C))"
      unfolding comp_def prod.sel .
  next
    show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
      using inv1 .
  qed

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding \<open>trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)\<close> finsert.rep_eq
  proof (rule linorder_trm.is_lower_set_insertI)
    show "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using A_in .
  next
    show "\<forall>w|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t A \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
      using A_least inv2
      by (metis linorder_trm.is_lower_set_iff linorder_trm.not_less_iff_gr_or_eq)
  next
    show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
      using inv2 .
  qed

  ultimately show ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> trail_is_lower_set_def)
next
  case (factorize \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<F>')
  thus ?thesis
    using invars(1) by (simp add: trail_is_lower_set_def fset_trail_atms)
next
  case step_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D A C U\<^sub>e\<^sub>r' \<Gamma>')

  have "suffix \<Gamma>' \<Gamma>"
    using step_hyps suffix_dropWhile by blast

  then obtain \<Gamma>'' where "\<Gamma> = \<Gamma>'' @ \<Gamma>'"
    unfolding suffix_def by metis

  have "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_clss (finsert (eres C D) (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r\<close> by simp
  also have "\<dots> = atms_of_cls (eres C D) |\<union>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    unfolding atms_of_clss_finsert ..
  also have "\<dots> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
  proof -
    have "\<forall>A |\<in>| atms_of_cls (eres C D). A |\<in>| atms_of_cls C \<or> A |\<in>| atms_of_cls D"
      using lit_in_one_of_resolvents_if_in_eres
      by (smt (verit, best) atms_of_cls_def fimage_iff fset_fset_mset)

    moreover have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars(2)[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>] step_hyps(5)
      by (metis propagating_clause_in_clauses)

    moreover have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using linorder_cls.is_least_in_ffilter_iff step_hyps(3) by blast

    ultimately have "\<forall>A |\<in>| atms_of_cls (eres C D). A |\<in>| atms_of_clss (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
      by (metis atms_of_clss_finsert funion_iff mk_disjoint_finsert)

    hence "\<forall>A |\<in>| atms_of_cls (eres C D). A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      unfolding atms_of_clss_fimage_iefac .

    thus ?thesis
      by blast
  qed
  finally have "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" .

  have
    inv1: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    inv2: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using invars(1,3)
    by (simp_all only: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_lower_set_def trail_is_sorted_def)

  have "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) (map (atm_of \<circ> fst) \<Gamma>)"
    using inv1 by (simp add: sorted_wrt_map)

  hence "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) (map (atm_of \<circ> fst) \<Gamma>'' @ map (atm_of \<circ> fst) \<Gamma>')"
    by (simp add: \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close>)

  moreover have "linorder_trm.is_lower_set (set (map (atm_of \<circ> fst) \<Gamma>'' @ map (atm_of \<circ> fst) \<Gamma>'))
    (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"
    using inv2 \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close>
    by (metis image_comp list.set_map map_append fset_trail_atms)

  ultimately have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'))"
    using linorder_trm.sorted_and_lower_set_appendD_right
    using \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
    by (metis (no_types, lifting) image_comp list.set_map fset_trail_atms)

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close> trail_is_lower_set_def)
qed

definition false_cls_is_mempty_or_has_neg_max_lit where
  "false_cls_is_mempty_or_has_neg_max_lit N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<Gamma>. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<longrightarrow> (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      trail_false_cls \<Gamma> C \<longrightarrow> C = {#} \<or> (\<exists>A. linorder_lit.is_maximal_in_mset C (Neg A))))"

lemma ord_res_8_preserves_false_cls_is_mempty_or_has_neg_max_lit:
  assumes
    step: "ord_res_8 N s s'" and
    invars:
      "false_cls_is_mempty_or_has_neg_max_lit N s"
      "trail_is_lower_set N s"
      "trail_is_sorted N s"
  shows "false_cls_is_mempty_or_has_neg_max_lit N s'"
  using step
proof (cases N s s' rule: ord_res_8.cases)
  case step_hyps: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')

  have \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using \<open>trail_is_lower_set N s\<close>[unfolded trail_is_lower_set_def,
        rule_format, OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>] .

  have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using \<open>trail_is_sorted N s\<close>[unfolded trail_is_sorted_def,
        rule_format, OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>] .

  have "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms[OF \<Gamma>_sorted] .

  hence "trail_consistent \<Gamma>'"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
  proof (rule trail_consistent.Cons [rotated])
    show "\<not> trail_defined_lit \<Gamma> (Neg A)"
      unfolding trail_defined_lit_iff_trail_defined_atm
      using linorder_trm.is_least_in_fset_ffilterD(2) linorder_trm.less_irrefl step_hyps(4)
        trail_defined_lit_iff_trail_defined_atm by force
  qed

  have atm_defined_iff_lt_A: "x |\<in>| trail_atms \<Gamma> \<longleftrightarrow> x \<prec>\<^sub>t A"
    if x_in: "x |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" for x
  proof (rule iffI)
    assume "x |\<in>| trail_atms \<Gamma>"
    thus "x \<prec>\<^sub>t A"
      using step_hyps(4)
      unfolding linorder_trm.is_least_in_ffilter_iff
      by blast
  next
    assume "x \<prec>\<^sub>t A"
    thus "x |\<in>| trail_atms \<Gamma>"
      using step_hyps(4)[unfolded linorder_trm.is_least_in_ffilter_iff]
      using \<Gamma>_lower[unfolded linorder_trm.is_lower_set_iff]
      by (metis linorder_trm.dual_order.asym linorder_trm.neq_iff x_in)
  qed

  have "\<not> trail_false_cls \<Gamma>' C" if C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "\<not> trail_false_cls \<Gamma> C"
      using C_in step_hyps(3) by metis
    hence "trail_true_cls \<Gamma> C \<or> \<not> trail_defined_cls \<Gamma> C"
      using trail_true_or_false_cls_if_defined by metis
    thus "\<not> trail_false_cls \<Gamma>' C"
    proof (elim disjE)
      assume "trail_true_cls \<Gamma> C"
      hence "trail_true_cls \<Gamma>' C"
        unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> trail_true_cls_def
        by (metis image_insert insert_iff list.set(2) trail_true_lit_def)
      thus "\<not> trail_false_cls \<Gamma>' C"
        using \<open>trail_consistent \<Gamma>'\<close>
        by (metis not_trail_true_cls_and_trail_false_cls)
    next
      assume "\<not> trail_defined_cls \<Gamma> C"
      then obtain L where L_max: "ord_res.is_maximal_lit L C"
        by (metis \<open>\<not> trail_false_cls \<Gamma> C\<close> linorder_lit.ex_maximal_in_mset trail_false_cls_mempty)

      have "L \<in># C"
        using L_max linorder_lit.is_maximal_in_mset_iff by metis

      have "atm_of L |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        using C_in \<open>L \<in># C\<close> by (metis atm_of_in_atms_of_clssI)

      show "\<not> trail_false_cls \<Gamma>' C"
      proof (cases "atm_of L = A")
        case True

        have "\<not> trail_defined_lit \<Gamma> (Pos A)"
          using step_hyps(4)
          unfolding trail_defined_lit_iff_trail_defined_atm linorder_trm.is_least_in_ffilter_iff
          by auto

        hence "(\<exists>K \<in># C. K \<noteq> Pos A \<and> \<not> trail_false_lit \<Gamma> K) \<or>
          \<not> ord_res.is_maximal_lit (Pos A) C"
          using step_hyps(5) C_in
          unfolding clause_could_propagate_iff
          unfolding bex_simps de_Morgan_conj not_not by blast

        thus ?thesis
        proof (elim disjE bexE conjE)
          fix K :: "'f gterm literal"
          assume "K \<in># C" and "K \<noteq> Pos A" and "\<not> trail_false_lit \<Gamma> K"
          thus "\<not> trail_false_cls \<Gamma>' C"
            by (smt (verit) fst_conv image_iff insertE list.simps(15) step_hyps(6)
                trail_false_cls_def trail_false_lit_def uminus_Pos uminus_lit_swap)
        next
          assume "\<not> ord_res.is_maximal_lit (Pos A) C"

          hence "L = Neg A"
            using \<open>atm_of L = A\<close> L_max by (metis literal.exhaust_sel)

          thus "\<not> trail_false_cls \<Gamma>' C"
            unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
            unfolding trail_false_cls_def trail_false_lit_def
            using \<open>L \<in># C\<close>[unfolded \<open>L = Neg A\<close>]
            by (metis \<open>\<not> trail_defined_cls \<Gamma> C\<close> fst_conv image_insert insertE list.simps(15)
                trail_defined_cls_def trail_defined_lit_def uminus_lit_swap uminus_not_id')
        qed
      next
        case False

        moreover have "\<not> atm_of L \<prec>\<^sub>t A"
        proof (rule notI)
          assume "atm_of L \<prec>\<^sub>t A"
          moreover have "\<forall>K \<in># C. atm_of K \<preceq>\<^sub>t atm_of L"
            using L_max linorder_lit.is_maximal_in_mset_iff
            by (metis Neg_atm_of_iff linorder_trm.le_less_linear linorder_trm.linear
                literal.collapse(1) ord_res.less_lit_simps(1) ord_res.less_lit_simps(2)
                ord_res.less_lit_simps(3) ord_res.less_lit_simps(4))
          ultimately have "\<forall>K \<in># C. atm_of K \<prec>\<^sub>t A"
            by (metis linorder_trm.antisym_conv1 linorder_trm.dual_order.strict_trans)
          moreover have "\<forall>K \<in># C. atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            using C_in by (metis atm_of_in_atms_of_clssI)
          ultimately have "\<forall>K \<in># C. atm_of K |\<in>| trail_atms \<Gamma>"
            using atm_defined_iff_lt_A by metis
          hence "\<forall>K \<in># C. trail_defined_lit \<Gamma> K"
            using trail_defined_lit_iff_trail_defined_atm by metis
          hence "trail_defined_cls \<Gamma> C"
            unfolding trail_defined_cls_def by argo
          thus False
            using \<open>\<not> trail_defined_cls \<Gamma> C\<close> by contradiction
        qed

        ultimately have "A \<prec>\<^sub>t atm_of L"
          by order

        hence "atm_of L |\<notin>| trail_atms \<Gamma>'"
          unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          unfolding trail_atms.simps prod.sel literal.sel
          using atm_defined_iff_lt_A[OF \<open>atm_of L |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>]
          using \<open>\<not> atm_of L \<prec>\<^sub>t A\<close> by simp

        hence "\<not> trail_defined_lit \<Gamma>' L"
          using trail_defined_lit_iff_trail_defined_atm by blast

        hence "\<not> trail_false_lit \<Gamma>' L"
          using trail_defined_lit_iff_true_or_false by blast

        thus "\<not> trail_false_cls \<Gamma>' C"
          unfolding trail_false_cls_def
          using \<open>L \<in># C\<close> by metis
      qed
    qed
  qed

  hence "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C \<longrightarrow>
    C = {#} \<or> (\<exists>A. ord_res.is_maximal_lit (Neg A) C)"
    by metis

  thus ?thesis
    unfolding false_cls_is_mempty_or_has_neg_max_lit_def \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> by simp
next
  case step_hyps: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>')

  have "E = {#} \<or> (\<exists>A. ord_res.is_maximal_lit (Neg A) E)"
    if E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and E_false: "trail_false_cls \<Gamma>' E" for E
  proof (cases "A \<in> atm_of ` set_mset E")
    case True
    have "\<not> trail_false_cls \<Gamma> E"
      using \<open>\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)\<close> E_in by metis

    hence "Neg A \<in># E"
      using E_false[unfolded \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>]
      by (metis subtrail_falseI uminus_Pos)

    have "atm_of L |\<in>| trail_atms \<Gamma>'" if "L \<in># E" for L
      using E_false \<open>L \<in># E\<close>
      by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set fset_trail_atms
          trail_false_cls_def trail_false_lit_def)

    moreover have "x \<prec>\<^sub>t A" if "x |\<in>| trail_atms \<Gamma>" for x
      using step_hyps(4) that
      by (simp add: linorder_trm.is_least_in_ffilter_iff)

    ultimately have "atm_of L \<preceq>\<^sub>t A" if "L \<in># E" for L
      unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close> trail_atms.simps prod.sel literal.sel
      using \<open>L \<in># E\<close> by blast

    hence "L \<preceq>\<^sub>l Neg A" if "L \<in># E" for L
      using \<open>L \<in># E\<close>
      by (metis linorder_lit.leI linorder_trm.leD literal.collapse(1) literal.collapse(2)
          ord_res.less_lit_simps(3) ord_res.less_lit_simps(4))

    hence "\<exists>A. ord_res.is_maximal_lit (Neg A) E"
      using \<open>Neg A \<in># E\<close>
      by (metis \<open>\<not> trail_false_cls \<Gamma> E\<close> linorder_lit.ex_maximal_in_mset
          linorder_lit.is_maximal_in_mset_iff reflclp_iff trail_false_cls_mempty)

    thus ?thesis ..
  next
    case False
    hence "trail_false_cls \<Gamma> E"
      using E_false[unfolded \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>]
      by (metis atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1) subtrail_falseI)

    moreover have "\<not> trail_false_cls \<Gamma> E"
      using \<open>\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)\<close> E_in by metis

    ultimately have False
      by contradiction

    thus ?thesis ..
  qed

  thus ?thesis
    unfolding false_cls_is_mempty_or_has_neg_max_lit_def \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> by simp
next
  case step_hyps: (factorize \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<F>')

  have "trail_false_cls \<Gamma> (iefac \<F> C) \<longleftrightarrow> trail_false_cls \<Gamma> C" if "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r" for \<F> C
    using that by (simp add: iefac_def trail_false_cls_def)

  hence "\<forall>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r).
    trail_false_cls \<Gamma> C \<longrightarrow> C = {#} \<or> (\<exists>A. ord_res.is_maximal_lit (Neg A) C)"
    using step_hyps(3) by force

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)\<close> false_cls_is_mempty_or_has_neg_max_lit_def)
next
  case step_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D A C U\<^sub>e\<^sub>r' \<Gamma>')

  have false_wrt_\<Gamma>_if_false_wrt_\<Gamma>': "trail_false_cls \<Gamma> E" if "trail_false_cls \<Gamma>' E" for E
    using that
    unfolding step_hyps(7) trail_false_cls_def trail_false_lit_def
    using image_iff set_dropWhileD by fastforce

  have "iefac \<F> E = {#} \<or> (\<exists>A. ord_res.is_maximal_lit (Neg A) (iefac \<F> E))"
    if "E |\<in>| N |\<union>| U\<^sub>e\<^sub>r'" "trail_false_cls \<Gamma>' (iefac \<F> E)" for E
  proof (cases "E = eres C D")
    case True

    show ?thesis
    proof (cases "eres C D = {#}")
      case True
      thus ?thesis
        by (simp add: \<open>E = eres C D\<close>)
    next
      case False
      then obtain K where K_max: "ord_res.is_maximal_lit K (eres C D)"
        using linorder_lit.ex_maximal_in_mset by metis

      have "\<Gamma>' = dropWhile (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x)) \<Gamma>"
        unfolding step_hyps(7)
      proof (rule dropWhile_cong)
        show "\<Gamma> = \<Gamma>" ..
      next
        fix Ln :: "'f gterm literal \<times> 'f gterm literal multiset option"
        obtain L annot where "Ln = (L, annot)"
          by force
        have "(\<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of L) \<longleftrightarrow>
          (atm_of K \<preceq>\<^sub>t atm_of L)"
          using K_max by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')
        thus "(\<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<longleftrightarrow>
          (atm_of K \<preceq>\<^sub>t atm_of (fst Ln))"
          unfolding \<open>Ln = (L, annot)\<close> prod.case prod.sel .
      qed

      have "K \<in># eres C D"
        using K_max linorder_lit.is_maximal_in_mset_iff by metis

      moreover have "\<not> trail_defined_lit \<Gamma>' K"
      proof -
        have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
          using invars[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def]
          by (simp add: sorted_wrt_map)

        have "\<forall>Ln \<in> set \<Gamma>'. \<not> (atm_of K \<preceq>\<^sub>t atm_of (fst Ln))"
          unfolding \<open>\<Gamma>' = dropWhile (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x)) \<Gamma>\<close>
        proof (rule ball_set_dropWhile_if_sorted_wrt_and_monotone_on)
          show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
            using invars[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> trail_is_sorted_def]
            by (simp add: sorted_wrt_map)
        next
          show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<ge>)
            (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
            by (rule monotone_onI) auto
        qed

        hence "\<forall>Ln \<in> set \<Gamma>'. atm_of (fst Ln) \<prec>\<^sub>t atm_of K"
          by auto

        hence "atm_of K |\<notin>| trail_atms \<Gamma>'"
          by (smt (verit, best) fset_trail_atms image_iff linorder_trm.dual_order.asym)

        thus ?thesis
          using trail_defined_lit_iff_trail_defined_atm by metis
      qed

      ultimately have "\<not> trail_false_cls \<Gamma>' (eres C D)"
        using trail_defined_lit_iff_true_or_false trail_false_cls_def by metis

      hence "\<not> trail_false_cls \<Gamma>' E"
        unfolding \<open>E = eres C D\<close> .

      hence "\<not> trail_false_cls \<Gamma>' (iefac \<F> E)"
        unfolding trail_false_cls_def by (metis iefac_def set_mset_efac)

      thus ?thesis
        using \<open>trail_false_cls \<Gamma>' (iefac \<F> E)\<close>
        by contradiction
    qed
  next
    case False
    hence "E |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
      using step_hyps(6) that(1) by force

    moreover hence "iefac \<F> E \<noteq> {#}"
      using step_hyps(3-)
      by (metis (no_types, opaque_lifting) empty_iff linorder_cls.is_least_in_ffilter_iff
          linorder_cls.not_less linorder_lit.is_maximal_in_mset_iff mempty_lesseq_cls rev_fimage_eqI
          set_mset_empty trail_false_cls_mempty)

    moreover have "trail_false_cls \<Gamma> (iefac \<F> E)"
      using \<open>trail_false_cls \<Gamma>' (iefac \<F> E)\<close> false_wrt_\<Gamma>_if_false_wrt_\<Gamma>' by metis

    ultimately have "\<exists>A. ord_res.is_maximal_lit (Neg A) (iefac \<F> E)"
      using invars(1)[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> false_cls_is_mempty_or_has_neg_max_lit_def]
      by auto

    thus ?thesis ..
  qed

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close> false_cls_is_mempty_or_has_neg_max_lit_def)
qed


definition decided_literals_all_neg where
  "decided_literals_all_neg N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<Gamma>. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<longrightarrow>
      (\<forall>Ln \<in> set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L))"

lemma ord_res_8_preserves_decided_literals_all_neg:
  assumes
    step: "ord_res_8 N s s'" and
    invar: "decided_literals_all_neg N s"
  shows "decided_literals_all_neg N s'"
  using step
proof (cases N s s' rule: ord_res_8.cases)
  case (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')

  have "\<forall>Ln\<in>set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> decided_literals_all_neg_def)

  hence "\<forall>Ln\<in>set \<Gamma>'. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> decided_literals_all_neg_def)
next
  case (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>')

  have "\<forall>Ln\<in>set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> decided_literals_all_neg_def)

  hence "\<forall>Ln\<in>set \<Gamma>'. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close> by simp

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> decided_literals_all_neg_def)
next
  case (factorize \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<F>')

  have "\<forall>Ln\<in>set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> decided_literals_all_neg_def)

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)\<close> decided_literals_all_neg_def)
next
  case step_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D A C U\<^sub>e\<^sub>r' \<Gamma>')

  have "\<forall>Ln\<in>set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    using invar by (simp add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> decided_literals_all_neg_def)

  moreover have "set \<Gamma>' \<subseteq> set \<Gamma>"
    unfolding \<open>\<Gamma>' = dropWhile _ \<Gamma>\<close>
    by (meson set_mono_suffix suffix_dropWhile)

  ultimately have "\<forall>Ln\<in>set \<Gamma>'. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
    by blast

  thus ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close> decided_literals_all_neg_def)
qed

definition ord_res_8_invars where
  "ord_res_8_invars N s \<longleftrightarrow>
    trail_is_sorted N s \<and>
    trail_is_lower_set N s \<and>
    false_cls_is_mempty_or_has_neg_max_lit N s \<and>
    trail_annotations_invars N s \<and>
    decided_literals_all_neg N s"

lemma ord_res_8_preserves_invars:
  assumes
    step: "ord_res_8 N s s'" and
    invars: "ord_res_8_invars N s"
  shows "ord_res_8_invars N s'"
  using invars
  unfolding ord_res_8_invars_def
  using
    ord_res_8_preserves_trail_is_sorted[OF step]
    ord_res_8_preserves_atoms_in_trail_lower_set[OF step]
    ord_res_8_preserves_false_cls_is_mempty_or_has_neg_max_lit[OF step]
    ord_res_8_preserves_trail_annotations_invars[OF step]
    ord_res_8_preserves_decided_literals_all_neg[OF step]
  by metis

lemma rtranclp_ord_res_8_preserves_invars:
  assumes
    step: "(ord_res_8 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_8_invars N s"
  shows "ord_res_8_invars N s'"
  using step invars ord_res_8_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

lemma tranclp_ord_res_8_preserves_invars:
  assumes
    step: "(ord_res_8 N)\<^sup>+\<^sup>+ s s'" and
    invars: "ord_res_8_invars N s"
  shows "ord_res_8_invars N s'"
  using step invars ord_res_8_preserves_invars
  by (smt (verit, del_insts) tranclp_induct)


lemma ex_ord_res_8_if_not_final:
  assumes
    not_final: "\<not> ord_res_8_final (N, s)" and
    invars: "ord_res_8_invars N s"
  shows "\<exists>s'. ord_res_8 N s s'"
proof -
  obtain U\<^sub>e\<^sub>r \<F> \<Gamma> where "s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
    by (metis surj_pair)

  note invars' = invars[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> ord_res_8_invars_def]
  
  have
    undef_atm_or_false_cls: "
      (\<exists>x |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). x |\<notin>| trail_atms \<Gamma>) \<and>
        \<not> (\<exists>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> x)\<or>
      (\<exists>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> x)" and
    "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    unfolding atomize_conj
    using not_final[unfolded ord_res_8_final.simps] \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> by metis

  show ?thesis
    using undef_atm_or_false_cls
  proof (elim disjE conjE)
    assume
      ex_undef_atm: "\<exists>x |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). x |\<notin>| trail_atms \<Gamma>" and
      no_conflict: "\<not> (\<exists>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> x)"

    moreover have "{|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} \<noteq> {||}"
    proof -
      obtain A\<^sub>2 :: "'f gterm" where
        A\<^sub>2_in: "A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
        A\<^sub>2_undef: "A\<^sub>2 |\<notin>| trail_atms \<Gamma>"
        using ex_undef_atm by metis

      have "A\<^sub>1 \<prec>\<^sub>t A\<^sub>2" if A\<^sub>1_in: "A\<^sub>1 |\<in>| trail_atms \<Gamma>" for A\<^sub>1 :: "'f gterm"
      proof -
        have "A\<^sub>1 \<noteq> A\<^sub>2"
          using A\<^sub>1_in A\<^sub>2_undef by metis

        moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
          using invars'[unfolded trail_is_lower_set_def, simplified] by argo

        ultimately show ?thesis
          by (meson A\<^sub>2_in A\<^sub>2_undef linorder_trm.is_lower_set_iff linorder_trm.linorder_cases that)
      qed

      thus ?thesis
        using A\<^sub>2_in
        by (smt (verit, ccfv_threshold) femptyE ffmember_filter)
    qed

    ultimately obtain A :: "'f gterm" where
      A_least: "linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
        \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
      using ex_undef_atm linorder_trm.ex_least_in_fset by presburger

    show "\<exists>s'. ord_res_8 N s s'"
    proof (cases "\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)")
      case True
      hence "{|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} \<noteq> {||}"
        by force

      then obtain C where
        C_least: "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} C"
        using linorder_cls.ex1_least_in_fset by meson

      show ?thesis
        unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
        using ord_res_8.propagate[OF no_conflict A_least C_least]
        using ord_res_8.factorize[OF no_conflict A_least C_least]
        by metis
    next
      case False
      thus ?thesis
        unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
        using ord_res_8.decide_neg[OF no_conflict A_least] by metis
    qed
  next
    assume "\<exists>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> x"
    then obtain D :: "'f gclause" where
      D_least: "linorder_cls.is_least_in_fset
        (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      by (metis femptyE ffmember_filter linorder_cls.ex_least_in_fset)

    hence "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "trail_false_cls \<Gamma> D"
      unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

    moreover have "D \<noteq> {#}"
      using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis

    ultimately obtain A where Neg_A_max: "linorder_lit.is_maximal_in_mset D (Neg A)"
      using invars' false_cls_is_mempty_or_has_neg_max_lit_def by metis

    hence "trail_false_lit \<Gamma> (Neg A)"
      using \<open>trail_false_cls \<Gamma> D\<close>
      by (metis linorder_lit.is_maximal_in_mset_iff trail_false_cls_def)

    hence "Pos A \<in> fst ` set \<Gamma>"
      unfolding trail_false_lit_def by simp

    hence "\<exists>C. (Pos A, Some C) \<in> set \<Gamma>"
      using invars'[unfolded decided_literals_all_neg_def, simplified]
      by fastforce

    then obtain C :: "'f gclause" where
      "map_of \<Gamma> (Pos A) = Some (Some C)"
      by (metis invars' is_pos_def map_of_SomeD not_Some_eq decided_literals_all_neg_def
          weak_map_of_SomeI)

    thus "\<exists>s'. ord_res_8 N s s'"
      unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      using ord_res_8.resolution D_least Neg_A_max by blast
  qed
qed

lemma ord_res_8_safe_state_if_invars:
  fixes N s
  assumes invars: "ord_res_8_invars N s"
  shows "safe_state (constant_context ord_res_8) ord_res_8_final (N, s)"
  using safe_state_constant_context_if_invars[where
      \<R> = ord_res_8 and \<F> = ord_res_8_final and \<I> = ord_res_8_invars]
  using ord_res_8_preserves_invars ex_ord_res_8_if_not_final invars by metis

end

end