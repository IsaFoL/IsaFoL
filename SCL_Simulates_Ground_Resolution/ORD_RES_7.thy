theory ORD_RES_7
  imports
    Background
    Implicit_Exhaustive_Factorization
    Exhaustive_Resolution
begin

section \<open>ORD-RES-7 (clause-guided literal trail construction)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_7 where
  decide_neg: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>|} A \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)" |

  skip_defined: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not>(\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    trail_defined_lit \<Gamma> L \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')" |

  skip_undefined_neg: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not>(\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<Gamma>' = (L, None) # \<Gamma> \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')" |

  skip_undefined_pos: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not>(\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|} D \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)" |

  skip_undefined_pos_ultimate: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not>(\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    \<Gamma>' = (- L, None) # \<Gamma> \<Longrightarrow>
    \<not>(\<exists>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D) \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)" |

  production: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<Gamma>' = (L, Some C) # \<Gamma> \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')" |

  factoring: "
    \<not> trail_false_cls \<Gamma> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#} \<Longrightarrow>
    \<not> linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<F>' = finsert C \<F> \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))" |

  resolution_bot: "
    trail_false_cls \<Gamma> E \<Longrightarrow>
    linorder_lit.is_maximal_in_mset E L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    map_of \<Gamma> (- L) = Some (Some D) \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r \<Longrightarrow>
    eres D E = {#} \<Longrightarrow>
    \<Gamma>' = [] \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})" |

  resolution_pos: "
    trail_false_cls \<Gamma> E \<Longrightarrow>
    linorder_lit.is_maximal_in_mset E L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    map_of \<Gamma> (- L) = Some (Some D) \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r \<Longrightarrow>
    eres D E \<noteq> {#} \<Longrightarrow>
    \<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma> \<Longrightarrow>
    linorder_lit.is_maximal_in_mset (eres D E) K \<Longrightarrow>
    is_pos K \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))" |

  resolution_neg: "
    trail_false_cls \<Gamma> E \<Longrightarrow>
    linorder_lit.is_maximal_in_mset E L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    map_of \<Gamma> (- L) = Some (Some D) \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r \<Longrightarrow>
    eres D E \<noteq> {#} \<Longrightarrow>
    \<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma> \<Longrightarrow>
    linorder_lit.is_maximal_in_mset (eres D E) K \<Longrightarrow>
    is_neg K \<Longrightarrow>
    map_of \<Gamma> (- K) = Some (Some C) \<Longrightarrow>
    ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)"


lemma right_unique_ord_res_7:
  fixes N :: "'f gclause fset"
  shows "right_unique (ord_res_7 N)"
proof (rule right_uniqueI)
  fix x y z
  assume step1: "ord_res_7 N x y" and step2: "ord_res_7 N x z"
  show "y = z"
    using step1
  proof (cases N x y rule: ord_res_7.cases)
    case step_hyps1: (decide_neg \<Gamma> C L U\<^sub>e\<^sub>r A \<Gamma>' \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have "A2 = A"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        using linorder_trm.Uniq_is_least_in_fset[THEN Uniq_D] by presburger
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> \<open>A2 = A\<close> by metis
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>\<Gamma>2' = \<Gamma>'\<close> ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (skip_defined \<Gamma> C L U\<^sub>e\<^sub>r \<C>' \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have "\<C>2' = \<C>'"
        using step_hyps1 step_hyps2 by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>\<C>2' = \<C>'\<close> ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (skip_undefined_neg \<Gamma> C L U\<^sub>e\<^sub>r \<Gamma>' \<C>' \<F>)
    show ?thesis
      using step2 unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      have "\<C>2' = \<C>'"
        using step_hyps1 step_hyps2 by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>\<C>2' = \<C>'\<close> \<open>\<Gamma>2' = \<Gamma>'\<close> ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (skip_undefined_pos \<Gamma> C L U\<^sub>e\<^sub>r \<F> D)
    show ?thesis
      using step2 unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>D2 = D\<close> ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>')
      have False
        using step_hyps1 step_hyps2
        by (metis linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (skip_undefined_pos_ultimate \<Gamma> C L U\<^sub>e\<^sub>r \<Gamma>' \<F>)
    show ?thesis
      using step2 unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have False
        using step_hyps1 step_hyps2
        by (metis linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>\<Gamma>2' = \<Gamma>'\<close> ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (production \<Gamma> C L U\<^sub>e\<^sub>r \<Gamma>' \<C>' \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      have "\<C>2' = \<C>'"
        using step_hyps1 step_hyps2 by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>\<Gamma>2' = \<Gamma>'\<close> \<open>\<C>2' = \<C>'\<close> ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (factoring \<Gamma> C L U\<^sub>e\<^sub>r \<F>' \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of C, THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        unfolding linorder_trm.is_least_in_ffilter_iff by metis
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have "\<F>2' = \<F>'"
        using step_hyps1 step_hyps2
        by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>\<F>2' = \<F>'\<close> ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (resolution_bot \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have "U\<^sub>e\<^sub>r2' = U\<^sub>e\<^sub>r'"
        using step_hyps1 step_hyps2
        by argo
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>U\<^sub>e\<^sub>r2' = U\<^sub>e\<^sub>r'\<close> \<open>\<Gamma>2' = \<Gamma>'\<close> ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (resolution_pos \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' K \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have "K2 = K"
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        using linorder_lit.Uniq_is_maximal_in_mset[of "eres D E", THEN Uniq_D] by metis
      have "U\<^sub>e\<^sub>r2' = U\<^sub>e\<^sub>r'"
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        by argo
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        unfolding \<open>K2 = K\<close>
        by argo
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>U\<^sub>e\<^sub>r2' = U\<^sub>e\<^sub>r'\<close> \<open>\<Gamma>2' = \<Gamma>'\<close> \<open>D2 = D\<close> ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have "K2 = K"
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        using linorder_lit.Uniq_is_maximal_in_mset[of "eres D E", THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>K2 = K\<close>
        by argo
      then show ?thesis ..
    qed
  next
    case step_hyps1: (resolution_neg \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' K C \<F>)
    show ?thesis
      using step2
      unfolding step_hyps1(1)
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)" z rule: ord_res_7.cases)
      case step_hyps2: (decide_neg L2 A2 \<Gamma>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_defined L2 \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_neg L2 \<Gamma>2' \<C>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos L2 D2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (skip_undefined_pos_ultimate L2 \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close> by argo
      then show ?thesis ..
    next
      case step_hyps2: (production L2 \<Gamma>2' \<C>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (factoring L2 \<F>2')
      have False
        using step_hyps1 step_hyps2 by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_bot L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2')
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_pos L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have "K2 = K"
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        using linorder_lit.Uniq_is_maximal_in_mset[of "eres D E", THEN Uniq_D] by metis
      have False
        using step_hyps1 step_hyps2
        unfolding \<open>K2 = K\<close>
        by argo
      then show ?thesis ..
    next
      case step_hyps2: (resolution_neg L2 D2 U\<^sub>e\<^sub>r2' \<Gamma>2' K2 C2)
      have "L2 = L"
        using step_hyps1 step_hyps2
        using linorder_lit.Uniq_is_maximal_in_mset[of E, THEN Uniq_D] by metis
      have "D2 = D"
        using step_hyps1 step_hyps2
        unfolding \<open>L2 = L\<close>
        by (metis option.inject)
      have "K2 = K"
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        using linorder_lit.Uniq_is_maximal_in_mset[of "eres D E", THEN Uniq_D] by metis
      have "U\<^sub>e\<^sub>r2' = U\<^sub>e\<^sub>r'"
        using step_hyps1 step_hyps2
        unfolding \<open>D2 = D\<close>
        by argo
      have "\<Gamma>2' = \<Gamma>'"
        using step_hyps1 step_hyps2
        unfolding \<open>K2 = K\<close>
        by argo
      have "C2 = C"
        using step_hyps1 step_hyps2
        unfolding \<open>K2 = K\<close>
        by (metis option.inject)
      show ?thesis
        unfolding step_hyps1(2) step_hyps2(1)
        unfolding \<open>U\<^sub>e\<^sub>r2' = U\<^sub>e\<^sub>r'\<close> \<open>\<Gamma>2' = \<Gamma>'\<close> \<open>C2 = C\<close> ..
    qed
  qed
qed

inductive ord_res_7_final where
  model_found:
    "ord_res_7_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None)" |

  contradiction_found:
    "ord_res_7_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some {#})"

sublocale ord_res_7_semantics: semantics where
  step = "constant_context ord_res_7" and
  final = ord_res_7_final
proof unfold_locales
  fix S :: "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
    ('f gterm literal \<times> 'f gterm literal multiset option) list \<times>
   'f gterm literal multiset option"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" and
    \<Gamma> :: "('f gterm literal \<times> 'f gterm literal multiset option) list" and
    \<C> :: "'f gclause option"
    where
    S_def: "S = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"
    by (metis prod.exhaust)

  assume "ord_res_7_final S"

  hence "\<nexists>x. ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) x"
    unfolding S_def
  proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_final.cases)
    case model_found
    thus ?thesis
      by (auto elim: ord_res_7.cases)
  next
    case contradiction_found
    thus ?thesis
      by (auto simp: linorder_lit.is_maximal_in_mset_iff elim: ord_res_7.cases)
  qed

  thus "finished (constant_context ord_res_7) S"
    by (simp add: S_def finished_def constant_context.simps)
qed

inductive ord_res_7_invars for N where
  "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" if
      "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
      "(\<forall>C. \<C> = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))" and
      "(\<forall>D. \<C> = Some D \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
          (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
              \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))))" and
      "(\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma> C)" and
      "(\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
          \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)))" and
      "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
      "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
      "(\<C> = None \<longrightarrow> trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
      "(\<forall>C. \<C> = Some C \<longrightarrow>
        (\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. linorder_lit.is_maximal_in_mset C L \<and> A \<preceq>\<^sub>t atm_of L))" and
      "(\<forall>Ln \<in> set \<Gamma>. is_neg (fst Ln) \<longleftrightarrow> snd Ln = None)" and
      "(\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C))" and
      "(\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln))" and
      "(\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))" and
      "(\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#})" and
      "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"

lemma clause_almost_defined_if_lt_next_clause:
  assumes "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"
  shows "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
proof (intro ballI impI allI)
  fix C :: "'f gclause" and K :: "'f gliteral"
  assume
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_lt: "\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D" and
    C_max_lit: "ord_res.is_maximal_lit K C"

  show "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#}"
    using assms
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_invars.cases)
    case invars: 1

    have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
      using invars C_in C_lt C_max_lit by metis

    hence C_almost_almost_defined: "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K \<and> L \<noteq> - K#}"
      using clause_almost_almost_definedI[OF C_in C_max_lit] by blast

    show ?thesis
    proof (cases "trail_defined_lit \<Gamma> K")
      case True
      hence "trail_defined_lit \<Gamma> (- K)"
        unfolding trail_defined_lit_def uminus_of_uminus_id by argo
      then show ?thesis
        using C_almost_almost_defined
        unfolding trail_defined_cls_def
        by auto
    next
      case False
      show ?thesis
      proof (cases \<C>)
        case None
        hence "trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars by argo
        then show ?thesis
          by (metis C_in C_max_lit False atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff
              trail_defined_lit_iff_trail_defined_atm)
      next
        case (Some D)
        hence "C \<prec>\<^sub>c D"
          using C_lt by simp
        then show ?thesis
          using invars
          by (smt (verit, ccfv_SIG) C_almost_almost_defined C_in C_max_lit False Some
              \<open>\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)\<close>
              atm_of_in_atms_of_clssI atm_of_uminus filter_mset_cong0
              linorder_lit.is_greatest_in_set_iff linorder_lit.is_maximal_in_mset_iff
              linorder_lit.is_maximal_in_set_eq_is_greatest_in_set
              linorder_lit.is_maximal_in_set_iff literal.collapse(1) literal.exhaust_sel
              ord_res.less_lit_simps(4) trail_defined_lit_iff_trail_defined_atm)
      qed
    qed
  qed
qed

lemma ord_res_7_invars_def:
  "ord_res_7_invars N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) \<longrightarrow>
      \<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r \<and>
      (\<forall>C. \<C> = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
      (\<forall>D. \<C> = Some D \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
          (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
              \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C)))) \<and>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma> C) \<and>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
          \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))) \<and>
      sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma> \<and>
      linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
      (\<C> = None \<longrightarrow> trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
      (\<forall>C. \<C> = Some C \<longrightarrow>
        (\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. linorder_lit.is_maximal_in_mset C L \<and> A \<preceq>\<^sub>t atm_of L)) \<and>
      (\<forall>Ln \<in> set \<Gamma>. is_neg (fst Ln) \<longleftrightarrow> snd Ln = None) \<and>
      (\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)) \<and>
      (\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)) \<and>
      (\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
      (\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}) \<and>
      (\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)))"
  (is "?NICE N s \<longleftrightarrow> ?UGLY N s")
proof (rule iffI)
  show "?NICE N s \<Longrightarrow> ?UGLY N s"
    apply (intro allI impI)
    subgoal premises prems for U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>
      using prems(1) unfolding prems(2)
      by (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_invars.cases) (simp only:)
    done
next
  assume "?UGLY N s"
  obtain U\<^sub>e\<^sub>r \<F> \<Gamma> \<C> where s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"
    by (metis prod.exhaust)
  show "?NICE N s"
    using \<open>?UGLY N s\<close>[rule_format, OF s_def]
    unfolding s_def
    by (intro ord_res_7_invars.intros) simp_all
qed

lemma ord_res_7_invars_implies_trail_consistent:
  assumes "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"
  shows "trail_consistent \<Gamma>"
  using assms unfolding ord_res_7_invars_def
  by (metis trail_consistent_if_sorted_wrt_atoms)

lemma ord_res_7_invars_implies_propagated_clause_almost_false:
  assumes invars: "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" and "(L, Some C) \<in> set \<Gamma>"
  shows "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}"
proof -
  obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 where \<Gamma>_eq: "\<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0"
    using \<open>(L, Some C) \<in> set \<Gamma>\<close> by (metis split_list)

  hence "trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using invars by (simp_all add: ord_res_7_invars_def)

  moreover have "suffix \<Gamma>\<^sub>0 \<Gamma>"
    using \<Gamma>_eq by (simp add: suffix_def)

  ultimately show ?thesis
    by (metis trail_false_cls_if_trail_false_suffix)
qed

lemma ord_res_7_preserves_invars:
  assumes step: "ord_res_7 N s s'" and invar: "ord_res_7_invars N s"
  shows "ord_res_7_invars N s'"
  using step
proof (cases N s s' rule: ord_res_7.cases)
  case step_hyps: (decide_neg \<Gamma> D L U\<^sub>e\<^sub>r A \<Gamma>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit L D\<close>

  have
    "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
    "A \<prec>\<^sub>t atm_of L" and
    "A |\<notin>| trail_atms \<Gamma>"
    using step_hyps unfolding atomize_conj linorder_trm.is_least_in_ffilter_iff by argo

  have "suffix \<Gamma> \<Gamma>'"
    using step_hyps unfolding suffix_def by simp

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of L"
    using trail_atms_le0 \<open>ord_res.is_maximal_lit L D\<close>
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. Some D = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in by simp

  moreover have "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "Some D = Some E" and
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_lt: "C \<prec>\<^sub>c E" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>C"
    for E C L\<^sub>C
  proof -
    have "E = D"
      using that by simp
    hence "C \<prec>\<^sub>c D"
      using C_lt by argo

    moreover have "\<not> trail_defined_lit \<Gamma> L\<^sub>C"
      using L\<^sub>C_undef \<open>suffix \<Gamma> \<Gamma>'\<close>
      using trail_defined_lit_if_trail_defined_suffix by blast

    ultimately have "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
      using clauses_lt_D_seldomly_have_undef_max_lit[rule_format, OF C_in _ C_max_lit] by metis

    thus ?thesis
      using \<open>suffix \<Gamma> \<Gamma>'\<close> trail_true_cls_if_trail_true_suffix by blast
  qed

  moreover have
    "trail_true_cls \<Gamma>' C"
    "\<And>K. linorder_lit.is_maximal_in_mset C K \<Longrightarrow>
      \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>')"
    if C_lt: "\<And>D'. Some D = Some D' \<Longrightarrow> C \<prec>\<^sub>c D'" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "C \<prec>\<^sub>c D"
      using C_lt by metis

    hence "trail_true_cls \<Gamma> C"
      using clauses_lt_D_true \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis

    thus "trail_true_cls \<Gamma>' C"
      using \<open>suffix \<Gamma> \<Gamma>'\<close>
      by (metis trail_true_cls_if_trail_true_suffix)

    fix K
    assume C_max_lit: "linorder_lit.is_maximal_in_mset C K"

    have "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
      using no_undef_atm_lt_max_lit_if_lt_D
      using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c D\<close> C_max_lit by metis

    thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>')"
      using step_hyps(6) by auto
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
  proof -
    have "\<forall>x |\<in>| trail_atms \<Gamma>. x \<prec>\<^sub>t A"
      using step_hyps(5)[unfolded linorder_trm.is_least_in_ffilter_iff, simplified]
      by (metis \<Gamma>_lower linorder_trm.antisym_conv3 linorder_trm.is_lower_set_iff)

    hence "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t A"
      by (simp add: fset_trail_atms)

    thus ?thesis
      using \<Gamma>_sorted by (simp add: \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>)
  qed

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
  proof -
    have "linorder_trm.is_lower_set (insert A (fset (trail_atms \<Gamma>)))
     (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"
    proof (rule linorder_trm.is_lower_set_insertI)
      show "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        using step_hyps(5)[unfolded linorder_trm.is_least_in_ffilter_iff, simplified]
        by argo
    next
      show "\<forall>w|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t A \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
        using step_hyps(5)[unfolded linorder_trm.is_least_in_ffilter_iff, simplified]
        by fastforce
    next
      show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
        using \<Gamma>_lower .
    qed

    moreover have "trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)"
      by (simp add: \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>)

    ultimately show ?thesis
      by simp
  qed

  moreover have "\<forall>A |\<in>| trail_atms \<Gamma>'. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)"
  proof (intro ballI exI conjI)
    show "ord_res.is_maximal_lit L D"
      using \<open>ord_res.is_maximal_lit L D\<close> .
  next
    fix x assume "x |\<in>| trail_atms \<Gamma>'"

    hence "x = A \<or> x |\<in>| trail_atms \<Gamma>"
      unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp

    thus "x \<preceq>\<^sub>t atm_of L"
    proof (elim disjE)
      assume "x = A"
      thus "x \<preceq>\<^sub>t atm_of L"
        using step_hyps(5) by (simp add: linorder_trm.is_least_in_ffilter_iff)
    next
      assume "x |\<in>| trail_atms \<Gamma>"
      thus "x \<preceq>\<^sub>t atm_of L"
        using trail_atms_le by metis
    qed
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
    using \<Gamma>_deci_iff_neg by simp

  moreover have "trail_true_cls \<Gamma>' C"
    if "Ln \<in> set \<Gamma>'" and "snd Ln = None" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "Ln = (Neg A, None) \<or> Ln \<in> set \<Gamma>"
      using \<open>Ln \<in> set \<Gamma>'\<close> unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp

    hence "trail_true_cls \<Gamma> C"
    proof (elim disjE)
      assume "Ln = (Neg A, None)"

      hence "fst Ln \<prec>\<^sub>l L"
        by (metis \<open>A \<prec>\<^sub>t atm_of L\<close> fst_conv literal.exhaust_sel ord_res.less_lit_simps(3)
            ord_res.less_lit_simps(4))

      moreover have "linorder_lit.is_maximal_in_mset {#fst Ln#} (fst Ln)"
        unfolding linorder_lit.is_maximal_in_mset_iff by simp

      ultimately have "{#fst Ln#} \<prec>\<^sub>c D"
        using D_max_lit
        using linorder_lit.multp_if_maximal_less_that_maximal by metis

      hence "C \<prec>\<^sub>c D"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close> by order

      thus "trail_true_cls \<Gamma> C"
        using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using clauses_lt_D_true by blast
    next
      assume "Ln \<in> set \<Gamma>"

      thus "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>snd Ln = None\<close> \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        by metis
    qed

    thus "trail_true_cls \<Gamma>' C"
      using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> using \<Gamma>_prop_in by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> using \<Gamma>_prop_greatest by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> using \<Gamma>_prop_almost_false
    by (metis (no_types, lifting) append_eq_Cons_conv list.inject option.discI prod.inject)

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using \<Gamma>_prop_ball_lt_true
    unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
    by (smt (verit, best) append_eq_Cons_conv list.inject option.discI snd_conv)

  ultimately show ?thesis
    by (auto simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some D)\<close> ord_res_7_invars_def)
next
  case step_hyps: (skip_defined \<Gamma> D K U\<^sub>e\<^sub>r \<C>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms \<Gamma>_sorted by metis

  have "K \<in># D" and lit_in_D_le_K: "\<And>L. L \<in># D \<Longrightarrow> L \<preceq>\<^sub>l K"
    using \<open>ord_res.is_maximal_lit K D\<close>
    unfolding atomize_imp atomize_all atomize_conj linorder_lit.is_maximal_in_mset_iff
    using linorder_lit.leI by blast

  hence "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in atm_of_in_atms_of_clssI by metis

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of K"
    using trail_atms_le0 \<open>ord_res.is_maximal_lit K D\<close>
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "trail_defined_cls \<Gamma> {#Ka \<in># D. Ka \<noteq> K#}"
    using step_hyps(4,5,6) D_in by (metis clause_almost_definedI)

  show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')\<close>
  proof (intro ord_res_7_invars.intros)
    show "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
      using \<F>_subset .

    show "\<forall>C'. \<C>' = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using step_hyps(7) by (metis linorder_cls.is_least_in_ffilter_iff Some_eq_The_optionalD)

    have "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
      if "\<C>' = Some E" and
        C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        C_lt: "C \<prec>\<^sub>c E" and
        C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
        L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma> L\<^sub>C"
      for E C L\<^sub>C
    proof -
      have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
        using \<open>\<C>' = Some E\<close> step_hyps by (metis Some_eq_The_optionalD)
      hence "C \<prec>\<^sub>c D \<or> C = D"
        unfolding linorder_cls.is_least_in_ffilter_iff
        using C_lt by (metis C_in linorder_cls.not_less_iff_gr_or_eq)
      thus ?thesis
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        thus ?thesis
          using clauses_lt_D_seldomly_have_undef_max_lit[rule_format, OF C_in _ C_max_lit L\<^sub>C_undef]
          by argo
      next
        assume "C = D"
        hence "L\<^sub>C = K"
          using C_max_lit D_max_lit
          by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
        hence False
          using L\<^sub>C_undef \<open>trail_defined_lit \<Gamma> K\<close> by argo
        thus ?thesis ..
      qed
    qed

    thus "\<forall>D. \<C>' = Some D \<longrightarrow> (\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>L\<^sub>C. ord_res.is_maximal_lit L\<^sub>C C \<longrightarrow> \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow>
        trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))"
      by metis

    have
      "trail_true_cls \<Gamma> C"
      "\<And>K. linorder_lit.is_maximal_in_mset C K \<Longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
      if C_lt: "\<And>E. \<C>' = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
    proof -
      have "C \<preceq>\<^sub>c D"
        using step_hyps that by (metis clause_le_if_lt_least_greater)

      hence "C \<prec>\<^sub>c D \<or> C = D"
        by simp

      thus "trail_true_cls \<Gamma> C"
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        thus "trail_true_cls \<Gamma> C"
          using clauses_lt_D_true \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis
      next
        assume "C = D"

        have "trail_defined_cls \<Gamma> D"
          using \<open>trail_defined_lit \<Gamma> K\<close> \<open>trail_defined_cls \<Gamma> {#Ka \<in># D. Ka \<noteq> K#}\<close>
          unfolding trail_defined_cls_def by auto

        hence "trail_true_cls \<Gamma> D"
          using \<Gamma>_consistent \<open>\<not> trail_false_cls \<Gamma> D\<close>
          by (metis trail_true_or_false_cls_if_defined)

        thus "trail_true_cls \<Gamma> C"
          using \<open>C = D\<close> by simp
      qed

      fix K\<^sub>c
      assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>c"
      thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>c \<and> A |\<notin>| trail_atms \<Gamma>)"
        using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        thus ?thesis
          using no_undef_atm_lt_max_lit_if_lt_D \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis
      next
        assume "C = D"
        thus ?thesis 
          by (metis C_max_lit D_max_lit Uniq_D linorder_lit.Uniq_is_maximal_in_mset step_hyps(5))
      qed
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma> C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))"
      unfolding atomize_conj by metis

    show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
      using \<Gamma>_sorted .

    show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
      using \<Gamma>_lower .

    have "trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" if "\<C>' = None"
    proof (intro fsubset_antisym)
      show "trail_atms \<Gamma> |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<Gamma>_lower unfolding linorder_trm.is_lower_set_iff by blast
    next
      have nbex_gt_D: "\<not> (\<exists>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c E)"
        using step_hyps \<open>\<C>' = None\<close>
        by (metis clause_le_if_lt_least_greater linorder_cls.leD option.simps(3))

      have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). atm_of K \<prec>\<^sub>t A)"
      proof (intro notI , elim bexE)
        fix A :: "'f gterm"
        assume "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "atm_of K \<prec>\<^sub>t A"

        hence "A |\<in>| atms_of_clss (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
          by simp

        then obtain E L where E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "L \<in># E" and "A = atm_of L"
          unfolding atms_of_clss_def atms_of_cls_def
          by (smt (verit, del_insts) fimage_iff fmember_ffUnion_iff fset_fset_mset)

        have "K \<prec>\<^sub>l L"
          using \<open>atm_of K \<prec>\<^sub>t A\<close> \<open>A = atm_of L\<close>
          by (cases K; cases L) simp_all

        hence "D \<prec>\<^sub>c E"
          using D_max_lit \<open>L \<in># E\<close>
          by (metis empty_iff linorder_lit.ex_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
              linorder_lit.less_linear linorder_lit.less_trans
              linorder_lit.multp_if_maximal_less_that_maximal set_mset_empty)

        thus False
          using E_in nbex_gt_D by metis
      qed

      hence "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>)"
        using step_hyps(5) step_hyps(6)
        by (metis linorder_trm.linorder_cases 
            trail_defined_lit_iff_trail_defined_atm)

      then show "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |\<subseteq>| trail_atms \<Gamma>"
        by blast
    qed

    thus "\<C>' = None \<longrightarrow> trail_atms \<Gamma> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      by metis

    show "\<forall>D. \<C>' = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>.
      \<exists>L. ord_res.is_maximal_lit L D \<and> A \<preceq>\<^sub>t atm_of L)"
    proof (intro allI impI ballI)
      fix E :: "'f gterm literal multiset" and A :: "'f gterm"
      assume "\<C>' = Some E" and "A |\<in>| trail_atms \<Gamma>"

      have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
        using step_hyps(7) \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)

      hence "D \<prec>\<^sub>c E"
        unfolding linorder_cls.is_least_in_ffilter_iff by argo

      obtain L where "linorder_lit.is_maximal_in_mset E L"
        by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.leD linorder_lit.ex_maximal_in_mset mempty_lesseq_cls)

      show "\<exists>L. ord_res.is_maximal_lit L E \<and> A \<preceq>\<^sub>t atm_of L"
      proof (intro exI conjI)
        show "ord_res.is_maximal_lit L E"
          using \<open>ord_res.is_maximal_lit L E\<close> .
      next
        have "K \<preceq>\<^sub>l L"
          using step_hyps(4) \<open>ord_res.is_maximal_lit L E\<close>
          by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.less_asym linorder_lit.leI
              linorder_lit.multp_if_maximal_less_that_maximal)

        hence "atm_of K \<preceq>\<^sub>t atm_of L"
          by (cases K; cases L) simp_all

        moreover have "A \<preceq>\<^sub>t atm_of K"
          using \<open>A |\<in>| trail_atms \<Gamma>\<close> trail_atms_le by blast

        ultimately show "A \<preceq>\<^sub>t atm_of L"
          by order
      qed
    qed

    show "\<forall>Ln\<in>set \<Gamma>. is_neg (fst Ln) = (snd Ln = None)"
      using \<Gamma>_deci_iff_neg by metis

    show "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)"
      using \<Gamma>_deci_ball_lt_true .

    show "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<Gamma>_prop_in by simp

    show "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
      using \<Gamma>_prop_greatest by simp

    show "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
      using \<Gamma>_prop_almost_false .

    show "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
      using \<Gamma>_prop_ball_lt_true .
  qed
next
  case step_hyps: (skip_undefined_neg \<Gamma> D K U\<^sub>e\<^sub>r \<Gamma>' \<C>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have "suffix \<Gamma> \<Gamma>'"
    using step_hyps unfolding suffix_def by simp

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms \<Gamma>_sorted by metis

  have "K \<in># D"
    using \<open>ord_res.is_maximal_lit K D\<close>
    unfolding linorder_lit.is_maximal_in_mset_iff by argo

  hence "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in atm_of_in_atms_of_clssI by metis

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of K"
    using trail_atms_le0 \<open>ord_res.is_maximal_lit K D\<close>
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. \<C>' = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using step_hyps(9) by (metis linorder_cls.is_least_in_ffilter_iff Some_eq_The_optionalD)

  moreover have "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "\<C>' = Some E" and
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_lt: "C \<prec>\<^sub>c E" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>C"
    for E C L\<^sub>C
  proof -
    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using \<open>\<C>' = Some E\<close> step_hyps by (metis Some_eq_The_optionalD)
    hence "C \<prec>\<^sub>c D \<or> C = D"
      unfolding linorder_cls.is_least_in_ffilter_iff
      using C_lt by (metis C_in linorder_cls.not_less_iff_gr_or_eq)
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"

      moreover have "\<not> trail_defined_lit \<Gamma> L\<^sub>C"
        using L\<^sub>C_undef \<open>suffix \<Gamma> \<Gamma>'\<close>
        using trail_defined_lit_if_trail_defined_suffix by blast

      ultimately have "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
        using clauses_lt_D_seldomly_have_undef_max_lit[rule_format, OF C_in _ C_max_lit] by metis

      thus ?thesis
        using \<open>suffix \<Gamma> \<Gamma>'\<close> trail_true_cls_if_trail_true_suffix by blast
    next
      assume "C = D"
      hence "L\<^sub>C = K"
        using C_max_lit D_max_lit
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      moreover have "trail_defined_lit \<Gamma>' K"
        by (simp add: step_hyps(8) trail_defined_lit_def)
      ultimately have False
        using L\<^sub>C_undef by argo
      thus ?thesis ..
    qed
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
  proof -
    have "atm_of K |\<notin>| trail_atms \<Gamma>"
      using \<open>\<not> trail_defined_lit \<Gamma> K\<close>
      by (simp add: trail_defined_lit_iff_trail_defined_atm)

    have "x \<prec>\<^sub>t atm_of K" if x_in: "x |\<in>| trail_atms \<Gamma>" for x
    proof -
      have "x \<preceq>\<^sub>t atm_of K"
        using x_in trail_atms_le by metis

      moreover have "x \<noteq> atm_of K"
        using x_in \<open>atm_of K |\<notin>| trail_atms \<Gamma>\<close> by metis

      ultimately show ?thesis
        by order
    qed

    hence "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t atm_of K"
      by (simp add: fset_trail_atms)

    thus ?thesis
      using \<Gamma>_sorted \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> by simp
  qed

  moreover have \<Gamma>'_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
  proof -
    have "linorder_trm.is_lower_set (insert (atm_of K) (fset (trail_atms \<Gamma>)))
     (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"
    proof (rule linorder_trm.is_lower_set_insertI)
      show "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<open>atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
    next
      show "\<forall>w|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t (atm_of K) \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
        using step_hyps(5)[unfolded linorder_trm.is_least_in_ffilter_iff, simplified]
        by fastforce
    next
      show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
        using \<Gamma>_lower .
    qed

    moreover have "trail_atms \<Gamma>' = finsert (atm_of K) (trail_atms \<Gamma>)"
      by (simp add: \<open>\<Gamma>' = (K, None) # \<Gamma>\<close>)

    ultimately show ?thesis
      by simp
  qed

  moreover have "trail_atms \<Gamma>' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" if "\<C>' = None"
  proof (intro fsubset_antisym)
    show "trail_atms \<Gamma>' |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<Gamma>'_lower unfolding linorder_trm.is_lower_set_iff by blast
  next
    have nbex_gt_D: "\<not> (\<exists>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c E)"
      using step_hyps \<open>\<C>' = None\<close>
      by (metis clause_le_if_lt_least_greater linorder_cls.leD option.simps(3))

    have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). atm_of K \<prec>\<^sub>t A)"
    proof (intro notI , elim bexE)
      fix A :: "'f gterm"
      assume "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "atm_of K \<prec>\<^sub>t A"

      hence "A |\<in>| atms_of_clss (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
        by simp

      then obtain E L where E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "L \<in># E" and "A = atm_of L"
        unfolding atms_of_clss_def atms_of_cls_def
        by (smt (verit, del_insts) fimage_iff fmember_ffUnion_iff fset_fset_mset)

      have "K \<prec>\<^sub>l L"
        using \<open>atm_of K \<prec>\<^sub>t A\<close> \<open>A = atm_of L\<close>
        by (cases K; cases L) simp_all

      hence "D \<prec>\<^sub>c E"
        using D_max_lit \<open>L \<in># E\<close>
        by (metis empty_iff linorder_lit.ex_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
            linorder_lit.less_linear linorder_lit.less_trans
            linorder_lit.multp_if_maximal_less_that_maximal set_mset_empty)

      thus False
        using E_in nbex_gt_D by metis
    qed

    hence "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>')"
      using step_hyps
      by (metis finsert_iff linorder_trm.antisym_conv3 prod.sel(1) trail_atms.simps(2))

    then show "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |\<subseteq>| trail_atms \<Gamma>'"
      by blast
  qed

  moreover have "\<forall>D. \<C>' = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>'.
    \<exists>L. ord_res.is_maximal_lit L D \<and> A \<preceq>\<^sub>t atm_of L)"
  proof (intro allI impI ballI)
    fix E :: "'f gterm literal multiset" and A :: "'f gterm"
    assume "\<C>' = Some E" and "A |\<in>| trail_atms \<Gamma>'"

    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps(9) \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)

    hence "D \<prec>\<^sub>c E"
      unfolding linorder_cls.is_least_in_ffilter_iff by argo

    obtain L where "linorder_lit.is_maximal_in_mset E L"
      by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.leD linorder_lit.ex_maximal_in_mset mempty_lesseq_cls)

    show "\<exists>L. ord_res.is_maximal_lit L E \<and> A \<preceq>\<^sub>t atm_of L"
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit L E"
        using \<open>ord_res.is_maximal_lit L E\<close> .
    next
      have "K \<preceq>\<^sub>l L"
        using step_hyps(4) \<open>ord_res.is_maximal_lit L E\<close>
        by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.less_asym linorder_lit.leI
            linorder_lit.multp_if_maximal_less_that_maximal)

      hence "atm_of K \<preceq>\<^sub>t atm_of L"
        by (cases K; cases L) simp_all

      moreover have "A \<preceq>\<^sub>t atm_of K"
      proof -
        have "A = atm_of K \<or> A |\<in>| trail_atms \<Gamma>"
          using \<open>A |\<in>| trail_atms \<Gamma>'\<close>
          unfolding \<open>\<Gamma>' = (K, None) # \<Gamma>\<close>
          by (metis (mono_tags, lifting) finsertE prod.sel(1) trail_atms.simps(2))

        thus "A \<preceq>\<^sub>t atm_of K"
          using trail_atms_le by blast
      qed

      ultimately show "A \<preceq>\<^sub>t atm_of L"
        by order
    qed
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    unfolding \<open>\<Gamma>' = (K, None) # \<Gamma>\<close>
    using \<Gamma>_deci_iff_neg \<open>is_neg K\<close> by simp

  moreover have "trail_true_cls \<Gamma>' C"
    if "Ln \<in> set \<Gamma>'" and "snd Ln = None" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "Ln = (K, None) \<or> Ln \<in> set \<Gamma>"
      using \<open>Ln \<in> set \<Gamma>'\<close> unfolding \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> by simp

    hence "trail_true_cls \<Gamma> C"
    proof (elim disjE)
      assume "Ln = (K, None)"

      hence "\<forall>x \<in># C. x \<prec>\<^sub>l K"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        unfolding multp_singleton_right[OF linorder_lit.transp_on_less]
        by simp

      hence "C \<prec>\<^sub>c D"
        using D_max_lit
        by (metis \<open>K \<in># D\<close> empty_iff ord_res.multp_if_all_left_smaller set_mset_empty)

      thus "trail_true_cls \<Gamma> C"
        using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        using clauses_lt_D_true by blast
    next
      assume "Ln \<in> set \<Gamma>"

      thus "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>snd Ln = None\<close> \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        by metis
    qed

    thus "trail_true_cls \<Gamma>' C"
      using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    unfolding \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> using \<Gamma>_prop_almost_false
    by (metis (no_types, lifting) append_eq_Cons_conv list.inject option.discI prod.inject)

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    unfolding \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> using \<Gamma>_prop_ball_lt_true
    by (smt (verit, ccfv_SIG) append_eq_Cons_conv list.inject option.discI prod.inject)

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close>
  proof (intro ord_res_7_invars.intros)
    have "trail_true_cls \<Gamma>' C"
      "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow>
      \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
      if C_lt: "\<And>E. \<C>' = Some E \<longrightarrow> C \<prec>\<^sub>c E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
    proof -
      have "C \<preceq>\<^sub>c D"
        using step_hyps that by (metis clause_le_if_lt_least_greater)

      hence "C \<prec>\<^sub>c D \<or> C = D"
        by simp

      thus "trail_true_cls \<Gamma>' C"
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"

        hence "trail_true_cls \<Gamma> C"
          using clauses_lt_D_true \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis

        thus "trail_true_cls \<Gamma>' C"
          using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)
      next
        assume "C = D"

        have "trail_true_lit \<Gamma>' K"
          unfolding \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> trail_true_lit_def by simp

        thus "trail_true_cls \<Gamma>' C"
          unfolding \<open>C = D\<close> trail_true_cls_def 
          using \<open>K \<in># D\<close> by metis
      qed

      fix K\<^sub>C
      assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>C"
      show "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
        using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"

        hence "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_max_lit_if_lt_D \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis

        thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
          by (metis finsert_iff step_hyps(8) trail_atms.simps(2))
      next
        assume "C = D"
        thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
          by (metis (mono_tags, lifting) C_max_lit D_max_lit Uniq_D \<Gamma>'_lower finsert_iff
              linorder_lit.Uniq_is_maximal_in_mset linorder_trm.not_in_lower_setI prod.sel(1)
              step_hyps(8) trail_atms.simps(2))
      qed
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma>' C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>'))"
      unfolding atomize_conj by metis
  qed simp_all
next
  case step_hyps: (skip_undefined_pos \<Gamma> D K U\<^sub>e\<^sub>r \<F> E)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>
  note E_least = \<open>linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E\<close>

  have "D \<prec>\<^sub>c E"
    using E_least unfolding linorder_cls.is_least_in_ffilter_iff by argo

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms \<Gamma>_sorted by metis

  have "K \<in># D"
    using \<open>ord_res.is_maximal_lit K D\<close>
    unfolding linorder_lit.is_maximal_in_mset_iff by argo

  hence "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in atm_of_in_atms_of_clssI by metis

  have "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
    using clause_almost_almost_definedI[OF D_in step_hyps(4,5)] .

  moreover have "- K \<notin># D"
    using \<open>is_pos K\<close> D_max_lit
    by (metis (no_types, opaque_lifting) is_pos_def linorder_lit.antisym_conv3
        linorder_lit.is_maximal_in_mset_iff linorder_trm.less_imp_not_eq ord_res.less_lit_simps(4)
        uminus_Pos uminus_not_id)

  ultimately have D_almost_defined: "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K#}"
    unfolding trail_defined_cls_def by auto

  hence "trail_true_cls \<Gamma> {#L \<in># D. L \<noteq> K#}"
    using \<open>\<not> trail_false_cls \<Gamma> {#L \<in># D. L \<noteq> K#}\<close>
    using trail_true_or_false_cls_if_defined by metis

  hence D_true: "trail_true_cls \<Gamma> D"
    unfolding trail_true_cls_def by auto

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of K"
    using trail_atms_le0 D_max_lit
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  obtain L where E_max_lit: "linorder_lit.is_maximal_in_mset E L"
    by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.leD linorder_lit.ex_maximal_in_mset mempty_lesseq_cls)

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. Some E = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using step_hyps unfolding linorder_cls.is_least_in_ffilter_iff by simp

  moreover have "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "Some E = Some E'" and
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_lt: "C \<prec>\<^sub>c E'" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma> L\<^sub>C"
    for E' C L\<^sub>C
  proof -
    have "E' = E"
      using that by simp
    hence "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps by metis
    hence "C \<prec>\<^sub>c D \<or> C = D"
      unfolding linorder_cls.is_least_in_ffilter_iff
      using C_lt \<open>E' = E\<close> by (metis C_in linorder_cls.not_less_iff_gr_or_eq)
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      thus "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
        using clauses_lt_D_seldomly_have_undef_max_lit[rule_format, OF C_in _ C_max_lit L\<^sub>C_undef]
        by metis
    next
      assume "C = D"
      hence "L\<^sub>C = K"
        using C_max_lit D_max_lit
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      thus ?thesis
        using \<open>C = D\<close> \<open>trail_true_cls \<Gamma> {#L \<in># D. L \<noteq> K#}\<close> \<open>is_pos K\<close> by metis
    qed
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using \<Gamma>_sorted .

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using \<Gamma>_lower .

  moreover have "\<forall>D. Some E = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>.
    \<exists>L. ord_res.is_maximal_lit L D \<and> A \<preceq>\<^sub>t atm_of L)"
  proof -
    have "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L E \<and> A \<preceq>\<^sub>t atm_of L"
    proof (intro ballI)
      fix A :: "'f gterm"
      assume "A |\<in>| trail_atms \<Gamma>"
      show "\<exists>L. ord_res.is_maximal_lit L E \<and> A \<preceq>\<^sub>t atm_of L"
      proof (intro exI conjI)
        show "ord_res.is_maximal_lit L E"
          using E_max_lit .
      next
        have "K \<preceq>\<^sub>l L"
          using D_max_lit E_max_lit
          by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.less_asym linorder_lit.leI
              linorder_lit.multp_if_maximal_less_that_maximal)

        hence "atm_of K \<preceq>\<^sub>t atm_of L"
          by (cases K; cases L) simp_all

        moreover have "A \<preceq>\<^sub>t atm_of K"
          using \<open>A |\<in>| trail_atms \<Gamma>\<close> trail_atms_le by metis

        ultimately show "A \<preceq>\<^sub>t atm_of L"
          by order
      qed
    qed

    thus ?thesis
      by simp
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    using \<Gamma>_deci_iff_neg .

  moreover have "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)"
    using \<Gamma>_deci_ball_lt_true .

  moreover have "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in .

  moreover have "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest .

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<Gamma>_prop_almost_false .

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using \<Gamma>_prop_ball_lt_true .

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close>
  proof (intro ord_res_7_invars.intros)
    have "trail_true_cls \<Gamma> C"
      "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow>
      \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
      if C_lt: "\<And>E'. Some E = Some E' \<Longrightarrow> C \<prec>\<^sub>c E'" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
    proof -
      have "C \<prec>\<^sub>c E"
        using C_lt by simp

      hence "C \<prec>\<^sub>c D \<or> C = D"
        using E_least C_in
        by (metis linorder_cls.is_least_in_ffilter_iff linorder_cls.less_imp_triv
            linorder_cls.linorder_cases)

      thus "trail_true_cls \<Gamma> C"
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        thus "trail_true_cls \<Gamma> C"
          using clauses_lt_D_true \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis
      next
        assume "C = D"
        thus "trail_true_cls \<Gamma> C"
          using D_true by argo
      qed

      fix K\<^sub>C
      assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>C"
      show "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
        using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_max_lit_if_lt_D \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis
      next
        assume "C = D"
        thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
          by (metis C_max_lit D_max_lit Uniq_D linorder_lit.Uniq_is_maximal_in_mset step_hyps(5))
      qed
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. Some E = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma> C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. Some E = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))"
      unfolding atomize_conj by metis
  qed simp_all
next
  case step_hyps: (skip_undefined_pos_ultimate \<Gamma> D K U\<^sub>e\<^sub>r \<Gamma>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have "suffix \<Gamma> \<Gamma>'"
    using \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close> by (simp add: suffix_def)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms \<Gamma>_sorted by metis

  have "K \<in># D"
    using \<open>ord_res.is_maximal_lit K D\<close>
    unfolding linorder_lit.is_maximal_in_mset_iff by argo

  hence "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in atm_of_in_atms_of_clssI by metis

  have "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
    using clause_almost_almost_definedI[OF D_in step_hyps(4,5)] .

  moreover have "- K \<notin># D"
    using \<open>is_pos K\<close> D_max_lit
    by (metis (no_types, opaque_lifting) is_pos_def linorder_lit.antisym_conv3
        linorder_lit.is_maximal_in_mset_iff linorder_trm.less_imp_not_eq ord_res.less_lit_simps(4)
        uminus_Pos uminus_not_id)

  ultimately have D_almost_defined: "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K#}"
    unfolding trail_defined_cls_def by auto

  hence "trail_true_cls \<Gamma> {#L \<in># D. L \<noteq> K#}"
    using \<open>\<not> trail_false_cls \<Gamma> {#L \<in># D. L \<noteq> K#}\<close>
    using trail_true_or_false_cls_if_defined by metis

  hence D_true: "trail_true_cls \<Gamma> D"
    unfolding trail_true_cls_def by auto

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of K"
    using trail_atms_le0 D_max_lit
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. None = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    by simp

  moreover have "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "None = Some E'" and
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_lt: "C \<prec>\<^sub>c E'" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>C"
    for E' C L\<^sub>C
    using that by simp

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
  proof -
    have "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t atm_of K"
      by (metis image_eqI linorder_trm.less_linear linorder_trm.not_le step_hyps(6) trail_atms_le
          trail_defined_lit_def trail_defined_lit_iff_trail_defined_atm)

    thus ?thesis
      unfolding \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close>
      using \<Gamma>_sorted by simp
  qed

  moreover have \<Gamma>'_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
  proof -
    have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<open>atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close> .

    moreover have "\<forall>w|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t atm_of K \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
      using step_hyps(5) by blast

    ultimately show ?thesis
      using \<Gamma>_lower by (simp add: \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close> linorder_trm.is_lower_set_insertI)
  qed

  moreover have "trail_atms \<Gamma>' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
  proof (intro fsubset_antisym)
    show "trail_atms \<Gamma>' |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<Gamma>'_lower unfolding linorder_trm.is_lower_set_iff by blast
  next
    have nbex_gt_D: "\<not> (\<exists>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c E)"
      using step_hyps by argo

    have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). atm_of K \<prec>\<^sub>t A)"
    proof (intro notI , elim bexE)
      fix A :: "'f gterm"
      assume "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "atm_of K \<prec>\<^sub>t A"

      hence "A |\<in>| atms_of_clss (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
        by simp

      then obtain E L where E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "L \<in># E" and "A = atm_of L"
        unfolding atms_of_clss_def atms_of_cls_def
        by (smt (verit, del_insts) fimage_iff fmember_ffUnion_iff fset_fset_mset)

      have "K \<prec>\<^sub>l L"
        using \<open>atm_of K \<prec>\<^sub>t A\<close> \<open>A = atm_of L\<close>
        by (cases K; cases L) simp_all

      hence "D \<prec>\<^sub>c E"
        using D_max_lit \<open>L \<in># E\<close>
        by (metis empty_iff linorder_lit.ex_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
            linorder_lit.less_linear linorder_lit.less_trans
            linorder_lit.multp_if_maximal_less_that_maximal set_mset_empty)

      thus False
        using E_in nbex_gt_D by metis
    qed

    hence "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>')"
      using step_hyps
      by (metis atm_of_uminus finsert_iff fst_conv linorder_trm.antisym_conv3 trail_atms.simps(2))

    then show "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |\<subseteq>| trail_atms \<Gamma>'"
      by blast
  qed

  moreover have "\<forall>D. None = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>.
    \<exists>L. ord_res.is_maximal_lit L D \<and> A \<preceq>\<^sub>t atm_of L)"
    by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    using \<Gamma>_deci_iff_neg \<open>is_pos K\<close>
    by (simp add: \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close> is_pos_neg_not_is_pos)

  moreover have "trail_true_cls \<Gamma>' C"
    if "Ln \<in> set \<Gamma>'" and "snd Ln = None" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "Ln = (- K, None) \<or> Ln \<in> set \<Gamma>"
      using \<open>Ln \<in> set \<Gamma>'\<close> unfolding \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close> by simp

    hence "trail_true_cls \<Gamma> C"
    proof (elim disjE)
      assume "Ln = (- K, None)"

      hence "\<forall>x \<in># C. x \<prec>\<^sub>l - K"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        unfolding multp_singleton_right[OF linorder_lit.transp_on_less]
        by simp

      hence "C \<preceq>\<^sub>c D"
        using D_max_lit step_hyps
        using linorder_cls.leI that(3) by blast

      thus "trail_true_cls \<Gamma> C"
        using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> D_true
        using clauses_lt_D_true by blast
    next
      assume "Ln \<in> set \<Gamma>"

      thus "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>snd Ln = None\<close> \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        by metis
    qed

    thus "trail_true_cls \<Gamma>' C"
      using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in by (simp add: \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close>)

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest by (simp add: \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close>)

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<Gamma>_prop_almost_false
    unfolding \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close>
    by (metis (no_types, lifting) append_eq_Cons_conv list.inject option.discI prod.inject)

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using \<Gamma>_prop_ball_lt_true
    unfolding \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close>
    by (metis D_true clauses_lt_D_true linorder_cls.neq_iff list.inject step_hyps(10) suffix_Cons
        suffix_def)

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close>
  proof (intro ord_res_7_invars.intros)
    have "trail_true_cls \<Gamma>' C"
      "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
      if C_lt: "\<And>E. None = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
    proof -
      have "None = The_optional (linorder_cls.is_least_in_fset
      (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps
        by (metis (no_types, opaque_lifting) Some_eq_The_optionalD
            linorder_cls.is_least_in_ffilter_iff not_Some_eq)

      hence "C \<preceq>\<^sub>c D"
        using step_hyps that by (metis clause_le_if_lt_least_greater)

      hence "C \<prec>\<^sub>c D \<or> C = D"
        by simp

      hence "trail_true_cls \<Gamma> C"
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        thus "trail_true_cls \<Gamma> C"
          using clauses_lt_D_true \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis
      next
        assume "C = D"
        thus "trail_true_cls \<Gamma> C"
          using D_true by argo
      qed

      thus "trail_true_cls \<Gamma>' C"
        using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)

      fix K\<^sub>C
      assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>C"
      thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
        using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        hence "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_max_lit_if_lt_D C_in C_max_lit by force
        thus ?thesis
          using step_hyps(9) by force
      next
        assume "C = D"
        thus ?thesis
          by (metis C_max_lit D_max_lit finsert_iff linorder_cls.order.irrefl
              linorder_lit.antisym_conv3 linorder_lit.multp_if_maximal_less_that_maximal
              step_hyps(5) step_hyps(9) trail_atms.simps(2))
      qed
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. None = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma>' C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. None = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
      (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
        \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>'))"
      unfolding atomize_conj by metis
  qed simp_all
next
  case step_hyps: (production \<Gamma> D K U\<^sub>e\<^sub>r \<Gamma>' \<C>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have "suffix \<Gamma> \<Gamma>'"
    using step_hyps by (simp add: suffix_def)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have "K \<in># D"
    using \<open>ord_res.is_maximal_lit K D\<close>
    unfolding linorder_lit.is_maximal_in_mset_iff by argo

  hence "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in atm_of_in_atms_of_clssI by metis

  have "atm_of K |\<notin>| trail_atms \<Gamma>"
    using \<open>\<not> trail_defined_lit \<Gamma> K\<close>
    by (metis trail_defined_lit_iff_trail_defined_atm)

  hence trail_atms_lt: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<prec>\<^sub>t atm_of K"
    using trail_atms_le0 \<open>ord_res.is_maximal_lit K D\<close>
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset linorder_trm.antisym_conv1)

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. \<C>' = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using step_hyps(11) by (metis linorder_cls.is_least_in_ffilter_iff Some_eq_The_optionalD)

  moreover have "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "\<C>' = Some E" and
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_lt: "C \<prec>\<^sub>c E" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>C"
    for E C L\<^sub>C
  proof -
    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using \<open>\<C>' = Some E\<close> step_hyps by (metis Some_eq_The_optionalD)
    hence "C \<prec>\<^sub>c D \<or> C = D"
      unfolding linorder_cls.is_least_in_ffilter_iff
      using C_lt by (metis C_in linorder_cls.not_less_iff_gr_or_eq)
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"

      moreover have "\<not> trail_defined_lit \<Gamma> L\<^sub>C"
        using L\<^sub>C_undef \<open>suffix \<Gamma> \<Gamma>'\<close>
        using trail_defined_lit_if_trail_defined_suffix by blast

      ultimately have "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
        using clauses_lt_D_seldomly_have_undef_max_lit[rule_format, OF C_in _ C_max_lit] by metis

      thus ?thesis
        using \<open>suffix \<Gamma> \<Gamma>'\<close> trail_true_cls_if_trail_true_suffix by blast
    next
      assume "C = D"
      hence "L\<^sub>C = K"
        using C_max_lit D_max_lit
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      moreover have "trail_defined_lit \<Gamma>' K"
        by (simp add: step_hyps trail_defined_lit_def)
      ultimately have False
        using L\<^sub>C_undef by argo
      thus ?thesis ..
    qed
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
  proof -
    have "x \<prec>\<^sub>t atm_of K" if x_in: "x |\<in>| trail_atms \<Gamma>" for x
      using x_in trail_atms_lt by metis

    hence "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t atm_of K"
      by (simp add: fset_trail_atms)
 
    thus ?thesis
      using \<Gamma>_sorted
      by (simp add: \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close>)
  qed

  moreover have \<Gamma>'_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
  proof -
    have "linorder_trm.is_lower_set (insert (atm_of K) (fset (trail_atms \<Gamma>)))
     (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"
    proof (rule linorder_trm.is_lower_set_insertI)
      show "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<open>atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
    next
      show "\<forall>w|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t (atm_of K) \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
        using step_hyps(5)[unfolded linorder_trm.is_least_in_ffilter_iff, simplified]
        by fastforce
    next
      show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
        using \<Gamma>_lower .
    qed

    moreover have "trail_atms \<Gamma>' = finsert (atm_of K) (trail_atms \<Gamma>)"
      by (simp add: \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close>)

    ultimately show ?thesis
      by simp
  qed

  moreover have "trail_atms \<Gamma>' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" if "\<C>' = None"
  proof (intro fsubset_antisym)
    show "trail_atms \<Gamma>' |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<Gamma>'_lower unfolding linorder_trm.is_lower_set_iff by blast
  next
    have nbex_gt_D: "\<not> (\<exists>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c E)"
      using step_hyps \<open>\<C>' = None\<close>
      by (metis clause_le_if_lt_least_greater linorder_cls.leD option.simps(3))

    have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). atm_of K \<prec>\<^sub>t A)"
    proof (intro notI , elim bexE)
      fix A :: "'f gterm"
      assume "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "atm_of K \<prec>\<^sub>t A"

      hence "A |\<in>| atms_of_clss (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
        by simp

      then obtain E L where E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "L \<in># E" and "A = atm_of L"
        unfolding atms_of_clss_def atms_of_cls_def
        by (smt (verit, del_insts) fimage_iff fmember_ffUnion_iff fset_fset_mset)

      have "K \<prec>\<^sub>l L"
        using \<open>atm_of K \<prec>\<^sub>t A\<close> \<open>A = atm_of L\<close>
        by (cases K; cases L) simp_all

      hence "D \<prec>\<^sub>c E"
        using D_max_lit \<open>L \<in># E\<close>
        by (metis empty_iff linorder_lit.ex_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
            linorder_lit.less_linear linorder_lit.less_trans
            linorder_lit.multp_if_maximal_less_that_maximal set_mset_empty)

      thus False
        using E_in nbex_gt_D by metis
    qed

    hence "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>')"
      using step_hyps
      by (metis finsert_iff fst_conv linorder_trm.antisym_conv3 trail_atms.simps(2))

    then show "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |\<subseteq>| trail_atms \<Gamma>'"
      by blast
  qed

  moreover have "\<forall>D. \<C>' = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>'.
    \<exists>L. ord_res.is_maximal_lit L D \<and> A \<preceq>\<^sub>t atm_of L)"
  proof (intro allI impI ballI)
    fix E :: "'f gterm literal multiset" and A :: "'f gterm"
    assume "\<C>' = Some E" and "A |\<in>| trail_atms \<Gamma>'"

    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps(11) \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)

    hence "D \<prec>\<^sub>c E"
      unfolding linorder_cls.is_least_in_ffilter_iff by argo

    obtain L where "linorder_lit.is_maximal_in_mset E L"
      by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.leD linorder_lit.ex_maximal_in_mset mempty_lesseq_cls)

    show "\<exists>L. ord_res.is_maximal_lit L E \<and> A \<preceq>\<^sub>t atm_of L"
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit L E"
        using \<open>ord_res.is_maximal_lit L E\<close> .
    next
      have "K \<preceq>\<^sub>l L"
        using step_hyps(4) \<open>ord_res.is_maximal_lit L E\<close>
        by (metis \<open>D \<prec>\<^sub>c E\<close> linorder_cls.less_asym linorder_lit.leI
            linorder_lit.multp_if_maximal_less_that_maximal)

      hence "atm_of K \<preceq>\<^sub>t atm_of L"
        by (cases K; cases L) simp_all

      moreover have "A \<preceq>\<^sub>t atm_of K"
      proof -
        have "A = atm_of K \<or> A |\<in>| trail_atms \<Gamma>"
          using \<open>A |\<in>| trail_atms \<Gamma>'\<close>
          unfolding \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close>
          by simp

        thus "A \<preceq>\<^sub>t atm_of K"
          using trail_atms_lt by blast
      qed

      ultimately show "A \<preceq>\<^sub>t atm_of L"
        by order
    qed
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    unfolding \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close>
    using \<Gamma>_deci_iff_neg \<open>is_pos K\<close> by simp

  moreover have "trail_true_cls \<Gamma>' C"
    if "Ln \<in> set \<Gamma>'" and "snd Ln = None" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "Ln = (K, Some D) \<or> Ln \<in> set \<Gamma>"
      using \<open>Ln \<in> set \<Gamma>'\<close> unfolding \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close> by simp

    hence "trail_true_cls \<Gamma> C"
    proof (elim disjE)
      assume "Ln = (K, Some D)"
      hence False
        using \<open>snd Ln = None\<close> by simp
      thus ?thesis ..
    next
      assume "Ln \<in> set \<Gamma>"

      thus "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>snd Ln = None\<close> \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        by metis
    qed

    thus "trail_true_cls \<Gamma>' C"
      using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in step_hyps(10) \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest step_hyps(8,9,10) by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    unfolding \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close>
    using \<Gamma>_prop_almost_false \<open>trail_false_cls \<Gamma> {#x \<in># D. x \<noteq> K#}\<close>
    by (metis (no_types, lifting) append_eq_Cons_conv list.inject option.inject prod.inject)

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
  proof -
    have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C"
    proof (intro ballI impI)
      fix C :: "'f gterm literal multiset"
      assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c D"
      thus "trail_true_cls \<Gamma> C"
        using clauses_lt_D_true by metis
    qed

    thus ?thesis
      unfolding \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close>
      by (smt (verit, ccfv_SIG) \<Gamma>_prop_ball_lt_true append_eq_Cons_conv list.inject option.inject
          prod.inject)
  qed

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close>
  proof (intro ord_res_7_invars.intros)
    have "trail_true_cls \<Gamma>' C"
      "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow>
      \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
      if C_lt: "\<And>E. \<C>' = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
    proof -
      have "C \<preceq>\<^sub>c D"
        using step_hyps that by (metis clause_le_if_lt_least_greater)

      hence "C \<prec>\<^sub>c D \<or> C = D"
        by simp

      thus "trail_true_cls \<Gamma>' C"
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"

        hence "trail_true_cls \<Gamma> C"
          using clauses_lt_D_true \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis

        thus "trail_true_cls \<Gamma>' C"
          using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_true_cls_if_trail_true_suffix)
      next
        assume "C = D"

        have "trail_true_lit \<Gamma>' K"
          using \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close> \<open>is_pos K\<close>
          unfolding trail_true_lit_def by (cases K) simp_all

        thus "trail_true_cls \<Gamma>' C"
          unfolding \<open>C = D\<close> trail_true_cls_def 
          using \<open>K \<in># D\<close> by metis
      qed

      fix K\<^sub>C
      assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>C"
      show "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>')"
        using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
      proof (elim disjE)
        assume "C \<prec>\<^sub>c D"
        hence "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_max_lit_if_lt_D C_in C_max_lit by force
        thus ?thesis
          using step_hyps by force
      next
        assume "C = D"
        thus ?thesis
          by (metis C_max_lit D_max_lit \<open>suffix \<Gamma> \<Gamma>'\<close> linorder_lit.Uniq_is_maximal_in_mset
              literal.sel(2) step_hyps(5) the1_equality' trail_defined_lit_if_trail_defined_suffix
              trail_defined_lit_iff_trail_defined_atm)
      qed
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma>' C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
      (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
        \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>'))"
      unfolding atomize_conj by metis
  qed simp_all
next
  case step_hyps: (factoring \<Gamma> D K U\<^sub>e\<^sub>r \<F>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_D: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L D \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>D. snd Ln = Some D \<longrightarrow> D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>D. snd Ln = Some D \<longrightarrow> linorder_lit.is_greatest_in_mset D (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> ord_res_7_invars_def)

  have clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
    (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have "atm_of K |\<notin>| trail_atms \<Gamma>"
    using \<open>\<not> trail_defined_lit \<Gamma> K\<close>
    by (metis trail_defined_lit_iff_trail_defined_atm)

  hence trail_atms_lt: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<prec>\<^sub>t atm_of K"
    using trail_atms_le0 \<open>ord_res.is_maximal_lit K D\<close>
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset linorder_trm.antisym_conv1)

  have "efac D \<noteq> D"
    using \<open>\<not> ord_res.is_strictly_maximal_lit K D\<close> D_max_lit \<open>is_pos K\<close>
    by (metis ex1_efac_eq_factoring_chain ex_ground_factoringI is_pos_def)

  hence "efac D \<prec>\<^sub>c D"
    by (metis efac_properties_if_not_ident(1))

  hence D_in_strong: "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "D |\<notin>| \<F>"
    using D_in \<open>efac D \<noteq> D\<close>
    unfolding atomize_conj iefac_def
    by (smt (verit) factorizable_if_neq_efac fimage_iff iefac_def ex1_efac_eq_factoring_chain)

  have "\<F>' |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    unfolding \<open>\<F>' = finsert D \<F>\<close>
    using \<F>_subset D_in_strong by simp

  moreover have "\<forall>C'. Some (efac D) = Some C' \<longrightarrow> C' |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
  proof -
    have "efac D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using D_in_strong by (simp add: iefac_def \<open>\<F>' = finsert D \<F>\<close>)

    thus ?thesis
      by simp
  qed

  moreover have "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "Some (efac D) = Some E" and
      C_in: "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_lt: "C \<prec>\<^sub>c E" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma> L\<^sub>C"
    for E C L\<^sub>C
  proof -
    have "E = efac D"
      using that by simp
    hence "C \<prec>\<^sub>c efac D"
      using C_lt by order
    hence "C \<noteq> efac D"
      by order
    hence "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using C_in iefac_def step_hyps(10) by auto
    moreover have "C \<prec>\<^sub>c D"
      using \<open>C \<prec>\<^sub>c efac D\<close> \<open>efac D \<prec>\<^sub>c D\<close> by order
    ultimately show "trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
        using clauses_lt_D_seldomly_have_undef_max_lit C_max_lit L\<^sub>C_undef by metis
  qed

  moreover have "trail_true_cls \<Gamma> C"
    "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
    if C_lt: "\<And>E. Some (efac D) = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and C_in: "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "C \<prec>\<^sub>c efac D"
      using C_lt by metis

    hence "C \<noteq> efac D"
      by order

    hence "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using C_in by (auto simp: \<open>\<F>' = finsert D \<F>\<close> iefac_def)

    moreover have "C \<prec>\<^sub>c D"
      using \<open>C \<prec>\<^sub>c efac D\<close> \<open>efac D \<prec>\<^sub>c D\<close> by order

    ultimately show "trail_true_cls \<Gamma> C"
      using clauses_lt_D_true by metis

    fix K\<^sub>C
    assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>C"
    show "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
      using clauses_lt_D_almost_defined  \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c D\<close> C_max_lit
      by metis
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using \<Gamma>_sorted .

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using \<Gamma>_lower .

  moreover have "\<forall>D'. Some (efac D) = Some D' \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>.
    \<exists>L. ord_res.is_maximal_lit L D' \<and> A \<preceq>\<^sub>t atm_of L)"
  proof -
    have "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L (efac D) \<and> A \<preceq>\<^sub>t atm_of L"
      using trail_atms_lt
      using ex1_efac_eq_factoring_chain step_hyps(4)
        ord_res.ground_factorings_preserves_maximal_literal by blast

    thus ?thesis
      by simp
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    using \<Gamma>_deci_iff_neg .

  moreover have "trail_true_cls \<Gamma> C"
    if "Ln \<in> set \<Gamma>" and "snd Ln = None" and "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "C = efac D \<or> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<open>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by (auto simp: iefac_def \<open>\<F>' = finsert D \<F>\<close>)

    thus "trail_true_cls \<Gamma> C"
    proof (elim disjE)
      assume "C = efac D"

      hence "linorder_lit.is_greatest_in_mset C K"
        using D_max_lit \<open>is_pos K\<close>
        by (metis greatest_literal_in_efacI)

      hence "K \<prec>\<^sub>l fst Ln"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        by (simp add: linorder_lit.is_greatest_in_mset_iff)

      hence "atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
        by (cases K; cases "fst Ln") simp_all

      moreover have "atm_of (fst Ln) |\<in>| trail_atms \<Gamma>"
        using \<open>Ln \<in> set \<Gamma>\<close> by (simp add: fset_trail_atms)

      moreover have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        by (meson D_in D_max_lit atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff)

      ultimately have "atm_of K |\<in>| trail_atms \<Gamma>"
        using \<Gamma>_lower
        unfolding linorder_trm.is_lower_set_iff
        by fastforce

      hence False
        using \<open>atm_of K |\<notin>| trail_atms \<Gamma>\<close> by contradiction

      thus "trail_true_cls \<Gamma> C" ..
    next
      assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      thus "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>Ln \<in> set \<Gamma>\<close> \<open>snd Ln = None\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        by metis
    qed
  qed

  moreover have "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" if "Ln \<in> set \<Gamma>" and "snd Ln = Some C" for Ln C
  proof -
    have "atm_of (fst Ln) \<prec>\<^sub>t atm_of K"
      using trail_atms_lt[unfolded fset_trail_atms, simplified] \<open>Ln \<in> set \<Gamma>\<close> by metis

    hence "atm_of (fst Ln) \<noteq> atm_of K"
      by order

    hence "fst Ln \<noteq> K"
      by (cases "fst Ln"; cases K) simp_all

    moreover have "ord_res.is_maximal_lit (fst Ln) C"
      using \<Gamma>_prop_greatest \<open>Ln \<in> set \<Gamma>\<close> \<open>snd Ln = Some C\<close> by blast

    ultimately have "C \<noteq> D"
      using \<open>ord_res.is_maximal_lit K D\<close> by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

    moreover have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<Gamma>_prop_in \<open>Ln \<in> set \<Gamma>\<close> \<open>snd Ln = Some C\<close> by metis
      
    ultimately show ?thesis
      by (auto simp: \<open>\<F>' = finsert D \<F>\<close> iefac_def)
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>. \<forall>D. snd Ln = Some D \<longrightarrow> linorder_lit.is_greatest_in_mset D (fst Ln)"
    using \<Gamma>_prop_greatest by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<Gamma>_prop_almost_false .

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
  proof (intro allI impI ballI)
    fix
      \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 :: "('f gliteral \<times> 'f gclause option) list" and
      L :: "'f gliteral" and
      C\<^sub>0 C\<^sub>1 :: "'f gclause"
    assume
      \<Gamma>_eq: "\<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C\<^sub>1) # \<Gamma>\<^sub>0" and
      C\<^sub>0_in: "C\<^sub>0 |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      "C\<^sub>0 \<prec>\<^sub>c C\<^sub>1"

    have "C\<^sub>0 = efac D \<or> C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using C\<^sub>0_in by (auto simp: iefac_def \<open>\<F>' = finsert D \<F>\<close>)

    thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0"
    proof (elim disjE)
      assume "C\<^sub>0 = efac D"

      have "atm_of L |\<in>| trail_atms \<Gamma>"
        using \<Gamma>_eq unfolding fset_trail_atms by simp

      hence "atm_of L \<prec>\<^sub>t atm_of K"
        using trail_atms_lt by metis

      hence "L \<prec>\<^sub>l K"
        by (cases L; cases K) simp_all

      moreover have "linorder_lit.is_greatest_in_mset C\<^sub>1 L"
        using \<Gamma>_eq \<Gamma>_prop_greatest by simp

      moreover have "linorder_lit.is_greatest_in_mset (efac D) K"
        using \<open>is_pos K\<close> D_max_lit by (metis greatest_literal_in_efacI)

      ultimately have "C\<^sub>1 \<prec>\<^sub>c efac D"
        by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
            linorder_lit.multp_if_maximal_less_that_maximal)

      hence False
        using \<open>C\<^sub>0 = efac D\<close> \<open>C\<^sub>0 \<prec>\<^sub>c C\<^sub>1\<close> by order

      thus ?thesis ..
    next
      assume "C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      thus ?thesis
        using \<Gamma>_prop_ball_lt_true \<Gamma>_eq \<open>C\<^sub>0 \<prec>\<^sub>c C\<^sub>1\<close> by metis
    qed
  qed

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac D))\<close>
  proof (intro ord_res_7_invars.intros)
    have "trail_true_cls \<Gamma> C"
      "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
      if C_lt: "\<And>E. Some (efac D) = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and C_in: "C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      for C
    proof -
      have "C \<prec>\<^sub>c efac D"
        using C_lt by metis

      hence "C \<noteq> efac D"
        by order

      hence "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using C_in by (auto simp: \<open>\<F>' = finsert D \<F>\<close> iefac_def)

      moreover have "C \<prec>\<^sub>c D"
        using \<open>C \<prec>\<^sub>c efac D\<close> \<open>efac D \<prec>\<^sub>c D\<close> by order

      ultimately show "trail_true_cls \<Gamma> C"
        using clauses_lt_D_true by metis

      fix K\<^sub>C
      assume C_max_lit: "linorder_lit.is_maximal_in_mset C K\<^sub>C"
      thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>C \<and> A |\<notin>| trail_atms \<Gamma>)"
        using no_undef_atm_lt_max_lit_if_lt_D \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c D\<close> by metis
    qed

    thus
      "\<forall>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>Da. Some (efac D) = Some Da \<longrightarrow> C \<prec>\<^sub>c Da) \<longrightarrow>
        trail_true_cls \<Gamma> C"
      "\<forall>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>Da. Some (efac D) = Some Da \<longrightarrow> C \<prec>\<^sub>c Da) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))"
      unfolding atomize_conj by metis
  qed simp_all
next
  case step_hyps: (resolution_bot \<Gamma> E K D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' \<F>)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_E_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_E: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L E \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close> ord_res_7_invars_def)
  
  have clauses_lt_E_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
    using \<F>_subset by blast

  moreover have "\<forall>C'. Some {#} = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    by (simp add: \<open>eres D E = {#}\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

  moreover have "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
    if "Some {#} = Some E" and
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and
      C_lt: "C \<prec>\<^sub>c E" and
      C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
      L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>C"
    for E C L\<^sub>C
  proof -
    have "E = {#}"
      using that by simp
    hence False
      using C_lt linorder_cls.leD mempty_lesseq_cls by blast
    thus ?thesis ..
  qed

  moreover have "trail_defined_cls \<Gamma>' {#L \<in># x. L \<noteq> K\<^sub>x#}"
    if "Some {#} = Some y" and x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and "x \<prec>\<^sub>c y" and
      x_max_lit: "linorder_lit.is_maximal_in_mset x K\<^sub>x" for x y K\<^sub>x
  proof -
    have False
      using linorder_cls.leD mempty_lesseq_cls that(1) that(3) by blast
    thus ?thesis ..
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    unfolding \<open>\<Gamma>' = []\<close> by simp

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'))"
    unfolding \<open>\<Gamma>' = []\<close>
    by (simp add: linorder_trm.is_lower_set_iff)

  moreover have "\<forall>D. Some {#} = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>'.
    \<exists>L. ord_res.is_maximal_lit L D \<and> A \<preceq>\<^sub>t atm_of L)"
    unfolding \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    unfolding \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma>' C)"
    using \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longrightarrow>
      \<not>(\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). linorder_lit.is_maximal_in_mset C (- (fst Ln)))"
    using \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>D. snd Ln = Some D \<longrightarrow>
      \<not>(\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c D \<and> fst Ln \<in># C)"
    using \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    using \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<open>\<Gamma>' = []\<close> by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)"
    using \<open>\<Gamma>' = []\<close> by simp

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})\<close>
  proof (intro ord_res_7_invars.intros)
    have "trail_true_cls \<Gamma>' x"
      "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>')"
      if C_lt: "\<And>E. Some {#} = Some E \<Longrightarrow> x \<prec>\<^sub>c E" and C_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
      for x
    proof -
      have "x \<prec>\<^sub>c {#}"
        using C_lt by metis
      hence False
        using linorder_cls.leD mempty_lesseq_cls by blast
      thus
        "trail_true_cls \<Gamma>' x"
        "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow>
          \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>')"
        by argo+
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). (\<forall>D. Some {#} = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma>' C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). (\<forall>D. Some {#} = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>'))"
      unfolding atomize_conj by metis
  qed simp_all
next
  case step_hyps: (resolution_pos \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' K \<F>)

  note E_max_lit = \<open>ord_res.is_maximal_lit L E\<close>
  note eres_max_lit = \<open>ord_res.is_maximal_lit K (eres D E)\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_E: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L E \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close> ord_res_7_invars_def)
  
  have clauses_lt_E_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms \<Gamma>_sorted by metis

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of L"
    using trail_atms_le0 E_max_lit
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "(- L, Some D) \<in> set \<Gamma>"
    using \<open>map_of \<Gamma> (- L) = Some (Some D)\<close> by (metis map_of_SomeD)

  hence D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in by simp

  have D_max_lit: "linorder_lit.is_greatest_in_mset D (- L)"
    using \<Gamma>_prop_greatest \<open>(- L, Some D) \<in> set \<Gamma>\<close> by fastforce

  have "suffix \<Gamma>' \<Gamma>"
    using step_hyps(9) suffix_dropWhile by metis

  hence "atms_of_cls (eres D E) |\<subseteq>| atms_of_cls D |\<union>| atms_of_cls E"
    using lit_in_one_of_resolvents_if_in_eres
    unfolding atms_of_cls_def by fastforce

  moreover have "atms_of_cls D |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
    by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb funion_upper1)

  moreover have "atms_of_cls E |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<open>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
    by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb funion_upper1)

  ultimately have "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> atms_of_clss_def by auto

  obtain A\<^sub>L where L_def: "L = Neg A\<^sub>L"
    using \<open>is_neg L\<close> by (cases L) simp_all

  have "D \<prec>\<^sub>c E"
    using clause_lt_clause_if_max_lit_comp
    using E_max_lit \<open>is_neg L\<close> D_max_lit
    by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)

  have "eres D E \<prec>\<^sub>c E"
    using eres_lt_if
    using E_max_lit \<open>is_neg L\<close> D_max_lit by metis

  hence "eres D E \<noteq> E"
    by order

  have "L \<in># E"
    using E_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by metis

  hence "- L \<notin># E"
    using not_both_lit_and_comp_lit_in_false_clause_if_trail_consistent
    using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> E\<close> by metis

  hence "\<forall>K \<in># eres D E. atm_of K \<prec>\<^sub>t atm_of L"
    using lit_in_eres_lt_greatest_lit_in_grestest_resolvant[OF \<open>eres D E \<noteq> E\<close> E_max_lit] by metis

  hence "\<forall>K \<in># eres D E. K \<noteq> L \<and> K \<noteq> - L"
    by fastforce

  moreover have "\<forall>L \<in># eres D E. L \<in># D \<or> L \<in># E"
    using lit_in_one_of_resolvents_if_in_eres by metis

  moreover have D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> - L#}"
    using ord_res_7_invars_implies_propagated_clause_almost_false
    using \<open>(- L, Some D) \<in> set \<Gamma>\<close> invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close>]
    by metis

  ultimately have "trail_false_cls \<Gamma> (eres D E)"
    using \<open>trail_false_cls \<Gamma> E\<close> unfolding trail_false_cls_def by fastforce

  hence "trail_false_lit \<Gamma> K"
    using eres_max_lit unfolding linorder_lit.is_maximal_in_mset_iff trail_false_cls_def by metis

  have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
    using eres_not_in_known_clauses_if_trail_false_cls
    using \<Gamma>_consistent clauses_lt_E_true \<open>eres D E \<prec>\<^sub>c E\<close> \<open>trail_false_cls \<Gamma> (eres D E)\<close> by metis

  hence "eres D E |\<notin>| \<F>"
    using \<F>_subset by blast

  hence "iefac \<F> (eres D E) = eres D E"
    by (simp add: iefac_def)

  hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp

  have "trail_false_lit \<Gamma> K"
    by (meson \<open>trail_false_cls \<Gamma> (eres D E)\<close> linorder_lit.is_maximal_in_mset_iff step_hyps(10)
        trail_false_cls_def)

  have mem_set_\<Gamma>'_iff: "(Ln \<in> set \<Gamma>') = (\<not> atm_of K \<preceq>\<^sub>t atm_of (fst Ln) \<and> Ln \<in> set \<Gamma>)" for Ln
    unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
  proof (rule mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone)
    show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
      using \<Gamma>_sorted .
  next
    show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
          (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln))"
      by (rule monotone_onI) auto
  qed

  hence atms_in_\<Gamma>'_lt_atm_K: "\<forall>x |\<in>| trail_atms \<Gamma>'. x \<prec>\<^sub>t atm_of K"
    by (auto simp add: fset_trail_atms)

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
    using \<F>_subset by blast

  moreover have "\<forall>C'. Some (eres D E) = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
  proof -
    have "eres D E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
      using \<open>iefac \<F> (eres D E) = eres D E\<close>
      by (simp add: \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

    thus ?thesis
      by simp
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    using \<Gamma>_sorted step_hyps(9) by (metis sorted_wrt_dropWhile)

  moreover have \<Gamma>'_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'))"
  proof -
    have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (trail_atms \<Gamma>)"
      unfolding linorder_trm.is_lower_set_iff
    proof (intro conjI ballI impI)
      show "fset (trail_atms \<Gamma>') \<subseteq> fset (trail_atms \<Gamma>)"
        unfolding fset_trail_atms using \<open>suffix \<Gamma>' \<Gamma>\<close> by (metis image_mono set_mono_suffix)
    next
      obtain \<Gamma>'' where "\<Gamma> = \<Gamma>'' @ \<Gamma>'"
        using \<open>suffix \<Gamma>' \<Gamma>\<close> unfolding suffix_def by metis

      fix l x
      assume "l |\<in>| trail_atms \<Gamma>'" and "x |\<in>| trail_atms \<Gamma>" and "x \<prec>\<^sub>t l"

      have "x |\<in>| trail_atms \<Gamma>'' \<or> x |\<in>| trail_atms \<Gamma>'"
        using \<open>x |\<in>| trail_atms \<Gamma>\<close> unfolding \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> fset_trail_atms by auto

      thus "x |\<in>| trail_atms \<Gamma>'"
      proof (elim disjE)
        assume "x |\<in>| trail_atms \<Gamma>''"

        hence "l \<prec>\<^sub>t x"
          using \<Gamma>_sorted \<open>l |\<in>| trail_atms \<Gamma>'\<close>
          unfolding \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> sorted_wrt_append fset_trail_atms by blast

        hence False
          using \<open>x \<prec>\<^sub>t l\<close> by order

        thus "x |\<in>| trail_atms \<Gamma>'" ..
      next
        assume "x |\<in>| trail_atms \<Gamma>'"
        thus "x |\<in>| trail_atms \<Gamma>'" .
      qed
    qed

    thus ?thesis
      using \<Gamma>_lower
      unfolding \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')\<close>
      by order
  qed

  moreover have "\<forall>DE. Some (eres D E) = Some DE \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>'.
    \<exists>L. ord_res.is_maximal_lit L DE \<and> A \<preceq>\<^sub>t atm_of L)"
    using atms_in_\<Gamma>'_lt_atm_K eres_max_lit by blast

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    using \<Gamma>_deci_iff_neg \<open>suffix \<Gamma>' \<Gamma>\<close>
    by (metis (no_types, opaque_lifting) in_set_conv_decomp suffixE suffix_appendD)

  moreover have "trail_true_cls \<Gamma>' C"
    if "Ln \<in> set \<Gamma>'" and "snd Ln = None" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "Ln \<in> set \<Gamma>"
      using \<open>Ln \<in> set \<Gamma>'\<close> \<open>suffix \<Gamma>' \<Gamma>\<close> set_mono_suffix by blast

    have "C = eres D E \<or> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')\<close>
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    thus "trail_true_cls \<Gamma>' C"
    proof (elim disjE)
      assume "C = eres D E"

      hence "K \<prec>\<^sub>l fst Ln"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close> eres_max_lit
        by (simp add: linorder_lit.is_maximal_in_mset_iff)

      hence "atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
        by (cases K; cases "fst Ln") simp_all

      moreover have "atm_of (fst Ln) |\<in>| trail_atms \<Gamma>'"
        using \<open>Ln \<in> set \<Gamma>'\<close> by (simp add: fset_trail_atms)

      moreover have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')"
        by (metis \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
            atm_of_in_atms_of_clssI eres_max_lit finsert_iff linorder_lit.is_maximal_in_mset_iff)

      ultimately have "atm_of K |\<in>| trail_atms \<Gamma>'"
        using \<Gamma>'_lower
        unfolding linorder_trm.is_lower_set_iff
        by fastforce

      moreover have "atm_of K |\<notin>| trail_atms \<Gamma>'"
        using atms_in_\<Gamma>'_lt_atm_K by blast

      ultimately show "trail_true_cls \<Gamma>' C"
        by contradiction
    next
      assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"

      hence "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>Ln \<in> set \<Gamma>\<close> \<open>snd Ln = None\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close> by metis

      then obtain L\<^sub>C where "L\<^sub>C \<in># C" and "trail_true_lit \<Gamma> L\<^sub>C"
        unfolding trail_true_cls_def by auto

      hence "\<forall>x \<in># C. x \<prec>\<^sub>l fst Ln"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        unfolding multp_singleton_right[OF linorder_lit.transp_on_less]
        by simp

      hence "L\<^sub>C \<prec>\<^sub>l fst Ln"
        using \<open>L\<^sub>C \<in># C\<close> by metis

      hence "atm_of L\<^sub>C \<preceq>\<^sub>t atm_of (fst Ln)"
        by (cases L\<^sub>C; cases "fst Ln") simp_all

      moreover have "atm_of (fst Ln) \<prec>\<^sub>t atm_of K"
        using atms_in_\<Gamma>'_lt_atm_K
        by (simp add: fset_trail_atms that(1))

      ultimately have "atm_of L\<^sub>C \<prec>\<^sub>t atm_of K"
        by order

      have "L\<^sub>C \<in> fst ` set \<Gamma>"
        using \<open>trail_true_lit \<Gamma> L\<^sub>C\<close>
        unfolding trail_true_lit_def .

      hence "L\<^sub>C \<in> fst ` set \<Gamma>'"
        using mem_set_\<Gamma>'_iff
        using \<open>atm_of L\<^sub>C \<prec>\<^sub>t atm_of K\<close> linorder_trm.not_le by auto

      hence "trail_true_lit \<Gamma>' L\<^sub>C"
        unfolding trail_true_lit_def .

      thus "trail_true_cls \<Gamma>' C"
        using \<open>L\<^sub>C \<in># C\<close>
        unfolding trail_true_cls_def by auto
    qed
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    using \<Gamma>_prop_in \<open>suffix \<Gamma>' \<Gamma>\<close> set_mono_suffix \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by blast

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest \<open>suffix \<Gamma>' \<Gamma>\<close> set_mono_suffix by blast

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<Gamma>_prop_almost_false \<open>suffix \<Gamma>' \<Gamma>\<close>
    by (metis (no_types, lifting) append.assoc suffix_def)

  moreover have "\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)"
  proof (intro allI impI ballI)
    fix
      \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 :: "('f gliteral \<times> 'f gclause option) list" and
      L :: "'f gliteral" and
      C\<^sub>0 C\<^sub>1 :: "'f gclause"
    assume
      \<Gamma>'_eq: "\<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C\<^sub>1) # \<Gamma>\<^sub>0" and
      C\<^sub>0_in: "C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and
      "C\<^sub>0 \<prec>\<^sub>c C\<^sub>1"

    have "C\<^sub>0 = eres D E \<or> C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using C\<^sub>0_in
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0"
    proof (elim disjE)
      assume "C\<^sub>0 = eres D E"

      have "\<not> atm_of K \<preceq>\<^sub>t atm_of (fst (L, Some C\<^sub>1))" and "(L, Some C\<^sub>1) \<in> set \<Gamma>"
        unfolding atomize_conj
        using \<Gamma>'_eq \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
        using mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
        by (metis in_set_conv_decomp)

      then have "\<not> atm_of K \<preceq>\<^sub>t atm_of L"
        by simp

      hence "atm_of L \<prec>\<^sub>t atm_of K"
        by order

      moreover have "linorder_lit.is_greatest_in_mset C\<^sub>1 L"
        using \<Gamma>_prop_greatest \<open>(L, Some C\<^sub>1) \<in> set \<Gamma>\<close> by fastforce

      ultimately have False
        using \<open>C\<^sub>0 \<prec>\<^sub>c C\<^sub>1\<close>
        by (metis Neg_atm_of_iff \<open>C\<^sub>0 = eres D E\<close> asympD eres_max_lit
            linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one
            linorder_lit.multp_if_maximal_less_that_maximal literal.collapse(1)
            ord_res.asymp_less_cls ord_res.less_lit_simps(1) ord_res.less_lit_simps(4)
            step_hyps(11))

      thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0" ..
    next
      assume "C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0"
        using \<Gamma>_prop_ball_lt_true \<Gamma>'_eq \<open>C\<^sub>0 \<prec>\<^sub>c C\<^sub>1\<close>
        by (metis (no_types, opaque_lifting) \<open>suffix \<Gamma>' \<Gamma>\<close> append_assoc suffixE)
    qed
  qed

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))\<close>
  proof (intro ord_res_7_invars.intros)
    have clause_true_in_\<Gamma>'_if: "trail_true_cls \<Gamma>' x" and
      "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>')"
      if x_lt: "\<And>DE. Some (eres D E) = Some DE \<longrightarrow> x \<prec>\<^sub>c DE" and x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
      for x
    proof -
      have "x \<prec>\<^sub>c eres D E"
        using x_lt by metis

      hence "x \<noteq> eres D E"
        by order

      hence x_in': "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using x_in \<open>iefac \<F> (eres D E) = eres D E\<close>
        by (simp add: \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

      have "x \<prec>\<^sub>c E"
        using \<open>x \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

      have x_true: "trail_true_cls \<Gamma> x"
        using clauses_lt_E_true x_in' \<open>x \<prec>\<^sub>c E\<close> by metis

      have "(- K, None) \<in> set \<Gamma>"
        using \<open>trail_false_lit \<Gamma> K\<close>
        using \<open>is_pos K\<close>
        using \<Gamma>_deci_iff_neg
        by (metis is_pos_neg_not_is_pos map_of_SomeD map_of_eq_None_iff not_Some_eq prod.collapse
            prod.inject trail_false_lit_def)

      obtain  L\<^sub>x where "L\<^sub>x \<in># x" and L\<^sub>x_true: "trail_true_lit \<Gamma> L\<^sub>x"
        using x_true unfolding trail_true_cls_def by metis

      moreover have "L\<^sub>x \<noteq> K"
        using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> (eres D E)\<close> L\<^sub>x_true eres_max_lit
        by (metis linorder_lit.is_maximal_in_mset_iff not_trail_true_cls_and_trail_false_cls
            trail_true_cls_def)

      moreover have "L\<^sub>x \<noteq> - K"
        using eres_max_lit \<open>x \<prec>\<^sub>c eres D E\<close> \<open>L\<^sub>x \<noteq> K\<close> \<open>L\<^sub>x \<in># x\<close>
        by (smt (verit, del_insts) empty_iff linorder_cls.less_not_sym
            linorder_lit.ex_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
            linorder_lit.less_trans linorder_lit.multp_if_maximal_less_that_maximal linorder_lit.neqE
            linorder_trm.not_less_iff_gr_or_eq literal.collapse(1) ord_res.less_lit_simps(4)
            set_mset_empty step_hyps(11) uminus_literal_def)

      ultimately  have "atm_of L\<^sub>x \<noteq> atm_of K"
        by (simp add: atm_of_eq_atm_of)

      moreover have "L\<^sub>x \<preceq>\<^sub>l K"
      proof (rule linorder_lit.less_than_maximal_if_multp\<^sub>H\<^sub>O[OF eres_max_lit _ \<open>L\<^sub>x \<in># x\<close>])
        show "multp\<^sub>H\<^sub>O (\<prec>\<^sub>l) x (eres D E)"
          using \<open>x \<prec>\<^sub>c eres D E\<close>
          by (simp add: multp_imp_multp\<^sub>H\<^sub>O)
      qed

      ultimately have "atm_of L\<^sub>x \<prec>\<^sub>t atm_of K"
        by (cases L\<^sub>x; cases K) simp_all

      hence "trail_true_lit \<Gamma>' L\<^sub>x"
        unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
        using L\<^sub>x_true
        unfolding trail_true_lit_def
        using mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
        by (metis (no_types, lifting) image_iff linorder_trm.not_le)

      thus "trail_true_cls \<Gamma>' x"
        using \<open>L\<^sub>x \<in># x\<close> unfolding trail_true_cls_def by metis


      fix K\<^sub>x
      assume x_max_lit: "ord_res.is_maximal_lit K\<^sub>x x"

      hence "K\<^sub>x \<preceq>\<^sub>l K"
        using \<open>x \<prec>\<^sub>c eres D E\<close> eres_max_lit
        using linorder_lit.multp_if_maximal_less_that_maximal by fastforce

      hence "atm_of K\<^sub>x \<preceq>\<^sub>t atm_of K"
        by (cases K\<^sub>x; cases K) simp_all

      have "A |\<in>| trail_atms \<Gamma>'"
        if A_lt: "A \<prec>\<^sub>t atm_of K\<^sub>x" and A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" for A
        unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
      proof (rule in_trail_atms_dropWhileI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
          using \<Gamma>_sorted .
      next
        show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x) (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
          using mono_atms_lt .
      next
        show "\<not> atm_of K \<preceq>\<^sub>t A"
          using A_lt \<open>atm_of K\<^sub>x \<preceq>\<^sub>t atm_of K\<close> by order
      next
        have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_max_lit_if_lt_E \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>x \<prec>\<^sub>c E\<close> x_max_lit
          by metis

        thus "A |\<in>| trail_atms \<Gamma>"
          using A_in A_lt by metis
      qed

      thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>')"
        using \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')\<close> by metis
    qed

    thus
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). (\<forall>DE. Some (eres D E) = Some DE \<longrightarrow> C \<prec>\<^sub>c DE) \<longrightarrow>
        trail_true_cls \<Gamma>' C"
      "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). (\<forall>DE. Some (eres D E) = Some DE \<longrightarrow> C \<prec>\<^sub>c DE) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K C \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>'))"
      unfolding atomize_conj by metis

    have "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
      if "Some (eres D E) = Some DE" and
        C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and
        C_lt: "C \<prec>\<^sub>c DE" and
        C_max_lit: "linorder_lit.is_maximal_in_mset C L\<^sub>C" and
        L\<^sub>C_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>C"
      for DE C L\<^sub>C
    proof -
      have "DE = eres D E"
        using that by simp
      hence "C \<prec>\<^sub>c eres D E"
        using C_lt by order
      hence "C \<noteq> eres D E"
        by order
      hence "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using C_in \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        by simp
      moreover have "C \<prec>\<^sub>c E"
        using \<open>C \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

      have "L\<^sub>C \<preceq>\<^sub>l K"
        using \<open>C \<prec>\<^sub>c eres D E\<close> C_max_lit eres_max_lit
        by (meson linorder_cls.dual_order.asym linorder_lit.leI
            linorder_lit.multp_if_maximal_less_that_maximal)
      hence "L\<^sub>C \<prec>\<^sub>l K \<or> L\<^sub>C = K"
        by simp

      thus ?thesis
      proof (elim disjE)
        assume "L\<^sub>C \<prec>\<^sub>l K"
        hence "atm_of L\<^sub>C \<prec>\<^sub>t atm_of K"
          using \<open>is_pos K\<close>
          by (cases L\<^sub>C; cases K) simp_all

        have "trail_defined_lit \<Gamma>' L\<^sub>C"
          unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
        proof (intro trail_defined_lit_dropWhileI ballI)
          show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
            using \<Gamma>_sorted .
        next
          show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
        (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
            using mono_atms_lt .
        next
          have "\<not> atm_of K \<preceq>\<^sub>t atm_of L\<^sub>C"
            using \<open>atm_of L\<^sub>C \<prec>\<^sub>t atm_of K\<close> by order
          thus "\<not> atm_of K \<preceq>\<^sub>t atm_of L\<^sub>C \<and> \<not> atm_of K \<preceq>\<^sub>t atm_of (- L\<^sub>C)"
            by simp
        next
          have "trail_defined_lit \<Gamma> K"
            using \<open>trail_false_lit \<Gamma> K\<close>
            using trail_defined_lit_iff_true_or_false by blast
          moreover have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            by (metis \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')\<close>
                \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
                atm_of_in_atms_of_clssI eres_max_lit finsertI1 linorder_lit.is_maximal_in_mset_iff)
          moreover have "atm_of L\<^sub>C |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit atm_of_in_atms_of_clssI
            unfolding linorder_lit.is_maximal_in_mset_iff
            by metis
          ultimately show "trail_defined_lit \<Gamma> L\<^sub>C"
            using \<open>atm_of L\<^sub>C \<prec>\<^sub>t atm_of K\<close> \<Gamma>_lower
            unfolding trail_defined_lit_iff_trail_defined_atm
            by (meson linorder_trm.is_lower_set_iff)
        qed

        hence False
          using L\<^sub>C_undef by contradiction

        thus ?thesis ..
      next
        have "trail_true_cls \<Gamma>' C"
          using clause_true_in_\<Gamma>'_if C_in \<open>C \<prec>\<^sub>c eres D E\<close> by blast
        hence "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#}"
          using L\<^sub>C_undef
          by (smt (verit, best) mem_Collect_eq set_mset_filter trail_defined_lit_iff_true_or_false
              trail_true_cls_def)
        moreover assume "L\<^sub>C = K"
        ultimately show "trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C"
          using \<open>is_pos K\<close> by metis
      qed
    qed

    thus "\<forall>Da. Some (eres D E) = Some Da \<longrightarrow>
      (\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c Da \<longrightarrow> (\<forall>L\<^sub>C. ord_res.is_maximal_lit L\<^sub>C C \<longrightarrow>
        \<not> trail_defined_lit \<Gamma>' L\<^sub>C \<longrightarrow> trail_true_cls \<Gamma>' {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))"
      by metis
  qed simp_all
next
  case step_hyps: (resolution_neg \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' K C \<F>)

  note E_max_lit = \<open>ord_res.is_maximal_lit L E\<close>
  note eres_max_lit = \<open>ord_res.is_maximal_lit K (eres D E)\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_seldomly_have_undef_max_lit:
      "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
        (\<forall>L\<^sub>C. linorder_lit.is_maximal_in_mset C L\<^sub>C \<longrightarrow>
          \<not> trail_defined_lit \<Gamma> L\<^sub>C \<longrightarrow> (trail_true_cls \<Gamma> {#K \<in># C. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    no_undef_atm_lt_max_lit_if_lt_E: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>))" and
    \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    trail_atms_le0: "\<forall>A |\<in>| trail_atms \<Gamma>. \<exists>L. ord_res.is_maximal_lit L E \<and> (A \<preceq>\<^sub>t atm_of L)" and
    \<Gamma>_deci_iff_neg: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)" and
    \<Gamma>_deci_ball_lt_true: "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)" and
    \<Gamma>_prop_in: "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    \<Gamma>_prop_greatest:
      "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    \<Gamma>_prop_almost_false:
      "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}" and
    \<Gamma>_prop_ball_lt_true: "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
        (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))" and
    \<Gamma>_prop_ball_lt_true: "\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)"
    using invar by (simp_all add: \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close> ord_res_7_invars_def)
  
  have clauses_lt_E_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})"
    using invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close>] clause_almost_defined_if_lt_next_clause
    by simp

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using trail_consistent_if_sorted_wrt_atoms \<Gamma>_sorted by metis

  have trail_atms_le: "\<forall>A |\<in>| trail_atms \<Gamma>. A \<preceq>\<^sub>t atm_of L"
    using trail_atms_le0 E_max_lit
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "(- L, Some D) \<in> set \<Gamma>"
    using \<open>map_of \<Gamma> (- L) = Some (Some D)\<close> by (metis map_of_SomeD)

  hence D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in by simp

  have D_max_lit: "linorder_lit.is_greatest_in_mset D (- L)"
    using \<Gamma>_prop_greatest \<open>(- L, Some D) \<in> set \<Gamma>\<close> by fastforce

  have "D \<prec>\<^sub>c E"
    using clause_lt_clause_if_max_lit_comp
    using E_max_lit \<open>is_neg L\<close> D_max_lit
    by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)

  have "eres D E \<prec>\<^sub>c E"
    using eres_lt_if
    using E_max_lit \<open>is_neg L\<close> D_max_lit by metis

  hence "eres D E \<noteq> E"
    by order

  have "(- K, Some C) \<in> set \<Gamma>"
    using \<open>map_of \<Gamma> (- K) = Some (Some C)\<close> by (metis map_of_SomeD)

  hence C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in by simp

  have C_max_lit: "linorder_lit.is_greatest_in_mset C (- K)"
    using \<Gamma>_prop_greatest \<open>(- K, Some C) \<in> set \<Gamma>\<close> by fastforce

  hence "C \<prec>\<^sub>c eres D E"
    using \<open>ord_res.is_maximal_lit K (eres D E)\<close> \<open>is_neg L\<close>
    by (metis Neg_atm_of_iff Pos_atm_of_iff linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
        linorder_lit.multp_if_maximal_less_that_maximal linorder_lit.not_less_iff_gr_or_eq
        linorder_trm.less_irrefl ord_res.less_lit_simps(4) step_hyps(11) uminus_Neg)

  have "suffix \<Gamma>' \<Gamma>"
    using step_hyps(9) suffix_dropWhile by metis

  hence "atms_of_cls (eres D E) |\<subseteq>| atms_of_cls D |\<union>| atms_of_cls E"
    using lit_in_one_of_resolvents_if_in_eres
    unfolding atms_of_cls_def by fastforce

  moreover have "atms_of_cls D |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in
    by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb funion_upper1)

  moreover have "atms_of_cls E |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using E_in
    by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb funion_upper1)

  ultimately have "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> atms_of_clss_def by auto

  have "L \<in># E"
    using E_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by metis

  hence "- L \<notin># E"
    using not_both_lit_and_comp_lit_in_false_clause_if_trail_consistent
    using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> E\<close> by metis

  hence "\<forall>K \<in># eres D E. atm_of K \<prec>\<^sub>t atm_of L"
    using lit_in_eres_lt_greatest_lit_in_grestest_resolvant[OF \<open>eres D E \<noteq> E\<close> E_max_lit] by metis

  hence "\<forall>K \<in># eres D E. K \<noteq> L \<and> K \<noteq> - L"
    by fastforce

  moreover have "\<forall>L \<in># eres D E. L \<in># D \<or> L \<in># E"
    using lit_in_one_of_resolvents_if_in_eres by metis

  moreover have D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> - L#}"
    using ord_res_7_invars_implies_propagated_clause_almost_false
    using \<open>(- L, Some D) \<in> set \<Gamma>\<close> invar[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close>]
    by metis

  ultimately have "trail_false_cls \<Gamma> (eres D E)"
    using \<open>trail_false_cls \<Gamma> E\<close> unfolding trail_false_cls_def by fastforce

  have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
    using eres_not_in_known_clauses_if_trail_false_cls
    using \<Gamma>_consistent clauses_lt_E_true \<open>eres D E \<prec>\<^sub>c E\<close> \<open>trail_false_cls \<Gamma> (eres D E)\<close> by metis

  hence "eres D E |\<notin>| \<F>"
    using \<F>_subset by blast

  hence "iefac \<F> (eres D E) = eres D E"
    by (simp add: iefac_def)

  hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
    by (simp add: \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

  have mem_set_\<Gamma>'_iff: "(Ln \<in> set \<Gamma>') = (\<not> atm_of K \<preceq>\<^sub>t atm_of (fst Ln) \<and> Ln \<in> set \<Gamma>)" for Ln
    unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
  proof (rule mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone)
    show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
      using \<Gamma>_sorted .
  next
    show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
          (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln))"
      by (rule monotone_onI) auto
  qed

  have atms_in_\<Gamma>'_lt_atm_K: "\<forall>A |\<in>| trail_atms \<Gamma>'. A \<prec>\<^sub>t atm_of K"
  proof -
    have "\<exists>L. ord_res.is_maximal_lit L C \<and> x \<prec>\<^sub>t atm_of L" if "x |\<in>| trail_atms \<Gamma>'" for x
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (- K) C"
        using C_max_lit by blast
    next
      show "x \<prec>\<^sub>t atm_of (- K)"
        using \<open>x |\<in>| trail_atms \<Gamma>'\<close> mem_set_\<Gamma>'_iff unfolding fset_trail_atms by fastforce
    qed

    hence "\<forall>A|\<in>|trail_atms \<Gamma>'. A \<prec>\<^sub>t atm_of (- K)"
      using C_max_lit
      by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset
          linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)

    thus ?thesis
      by (metis atm_of_uminus)
  qed

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
    using \<F>_subset by blast

  moreover have "\<forall>C'. Some C = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    using C_in by (simp add: \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

  moreover have
    "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow> trail_defined_cls \<Gamma>' {#L \<in># x. L \<noteq> K\<^sub>x#}" and
    clause_true_in_\<Gamma>'_if: "trail_true_cls \<Gamma>' x"
    if x_lt: "\<And>y. Some C = Some y \<Longrightarrow> x \<prec>\<^sub>c y" and x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" for x
  proof -
    have "x \<prec>\<^sub>c C"
      using x_lt by metis

    hence "x \<prec>\<^sub>c eres D E"
      using \<open>C \<prec>\<^sub>c eres D E\<close> by order

    hence "x \<noteq> eres D E"
      by order

    have "x \<prec>\<^sub>c E"
      using \<open>x \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

    moreover have x_in': "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using x_in \<open>x \<noteq> eres D E\<close>
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    ultimately have x_true: "trail_true_cls \<Gamma> x"
      using clauses_lt_E_true by metis

    then obtain L\<^sub>x where "L\<^sub>x \<in># x" and "trail_true_lit \<Gamma> L\<^sub>x"
      unfolding trail_true_cls_def by metis

    have "L\<^sub>x \<preceq>\<^sub>l - K"
      using C_max_lit \<open>x \<prec>\<^sub>c C\<close> \<open>L\<^sub>x \<in># x\<close>
      by (smt (verit, ccfv_threshold) asympD empty_not_add_mset ord_res.transp_less_lit insert_DiffM
          linorder_lit.is_greatest_in_set_iff linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
          linorder_lit.is_maximal_in_mset_iff linorder_lit.is_maximal_in_set_eq_is_greatest_in_set
          linorder_lit.is_maximal_in_set_iff linorder_lit.leI ord_res.asymp_less_cls
          ord_res.multp_if_all_left_smaller transpE)

    have mono_atms_lt: "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
        (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
    proof (intro monotone_onI, unfold le_bool_def, intro impI)
      fix x y
      assume "atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)" and "atm_of K \<preceq>\<^sub>t atm_of (fst y)"
      thus "atm_of K \<preceq>\<^sub>t atm_of (fst x)"
        by order
    qed

    obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 where \<Gamma>_eq: "\<Gamma> = \<Gamma>\<^sub>1 @ (- K, Some C) # \<Gamma>\<^sub>0"
      using \<open>(- K, Some C) \<in> set \<Gamma>\<close> by (metis split_list)

    hence "trail_true_cls \<Gamma>\<^sub>0 x"
      using \<Gamma>_prop_ball_lt_true x_in' \<open>x \<prec>\<^sub>c C\<close> by metis

    then obtain  L\<^sub>x where "L\<^sub>x \<in># x" and L\<^sub>x_true: "trail_true_lit \<Gamma>\<^sub>0 L\<^sub>x"
      unfolding trail_true_cls_def by auto

    moreover have "\<Gamma>' = \<Gamma>\<^sub>0"
    proof -
      have "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) ((\<Gamma>\<^sub>1 @ [(- K, Some C)]) @ \<Gamma>\<^sub>0)"
        unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close> \<Gamma>_eq by simp

      also have "\<dots> = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>0"
      proof (rule dropWhile_append2)
        fix Ln :: "'f gterm literal \<times> 'f gclause option"
        assume "Ln \<in> set (\<Gamma>\<^sub>1 @ [(- K, Some C)])"

        moreover have "\<forall>x\<in>set \<Gamma>\<^sub>1. atm_of K \<prec>\<^sub>t atm_of (fst x)"
          using \<Gamma>_sorted by (simp add: \<Gamma>_eq sorted_wrt_append)

        ultimately show "atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
          using \<open>is_neg K\<close> by auto
      qed

      also have "\<dots> = \<Gamma>\<^sub>0"
      proof (cases \<Gamma>\<^sub>0)
        case Nil
        thus ?thesis
          by (simp add: dropWhile_eq_self_iff)
      next
        case (Cons Ln \<Gamma>\<^sub>0')

        hence "atm_of (fst Ln) \<prec>\<^sub>t atm_of K"
          using \<Gamma>_sorted by (simp add: \<Gamma>_eq sorted_wrt_append)

        hence "\<not> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
          by order

        hence "\<not> atm_of K \<preceq>\<^sub>t atm_of (fst (hd \<Gamma>\<^sub>0))"
          by (simp add: \<open>\<Gamma>\<^sub>0 = Ln # \<Gamma>\<^sub>0'\<close>)

        thus ?thesis
          by (simp add: dropWhile_eq_self_iff)
      qed

      finally show ?thesis .
    qed

    ultimately have "trail_true_lit \<Gamma>' L\<^sub>x"
      by argo

    thus "trail_true_cls \<Gamma>' x"
      using \<open>L\<^sub>x \<in># x\<close> unfolding trail_true_cls_def by metis

    fix K\<^sub>x assume x_max_lit: "ord_res.is_maximal_lit K\<^sub>x x"
    show "trail_defined_cls \<Gamma>' {#L \<in># x. L \<noteq> K\<^sub>x#}"
      unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
    proof (intro trail_defined_cls_dropWhileI ballI)
      show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
        using \<Gamma>_sorted .
    next
      show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
        (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
        using mono_atms_lt .
    next
      fix L\<^sub>x
      assume "L\<^sub>x \<in># {#L \<in># x. L \<noteq> K\<^sub>x#}"

      hence "L\<^sub>x \<in># x" and "L\<^sub>x \<noteq> K\<^sub>x"
        by simp_all

      hence "L\<^sub>x \<prec>\<^sub>l K\<^sub>x"
        using x_max_lit \<open>L\<^sub>x \<in># x\<close> \<open>L\<^sub>x \<noteq> K\<^sub>x\<close> unfolding linorder_lit.is_maximal_in_mset_iff
        by fastforce

      moreover have "K\<^sub>x \<preceq>\<^sub>l K"
        using \<open>x \<prec>\<^sub>c eres D E\<close>
        using linorder_lit.multp_if_maximal_less_that_maximal[OF eres_max_lit x_max_lit]
        by fastforce

      ultimately have "atm_of L\<^sub>x \<prec>\<^sub>t atm_of K"
        using \<open>is_neg K\<close>
        by (metis C_max_lit Pos_atm_of_iff \<open>x \<prec>\<^sub>c C\<close> linorder_cls.dual_order.asym
            linorder_lit.dual_order.strict_trans1
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.less_le_not_le
            linorder_lit.multp_if_maximal_less_that_maximal linorder_trm.linorder_cases
            literal.collapse(2) ord_res.less_lit_simps(3) ord_res.less_lit_simps(4) uminus_Neg
            x_max_lit)

      hence "\<not> atm_of K \<preceq>\<^sub>t atm_of L\<^sub>x"
        by order

      thus "\<not> atm_of K \<preceq>\<^sub>t atm_of L\<^sub>x \<and> \<not> atm_of K \<preceq>\<^sub>t atm_of (- L\<^sub>x)"
        unfolding atm_of_uminus conj_absorb .
    next
      show "trail_defined_cls \<Gamma> {#L \<in># x. L \<noteq> K\<^sub>x#}"
        using clauses_lt_E_almost_defined x_in' \<open>x \<prec>\<^sub>c E\<close> x_max_lit by metis
    qed
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
    using \<Gamma>_sorted step_hyps(9) by (metis sorted_wrt_dropWhile)

  moreover have \<Gamma>'_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'))"
  proof -
    have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (trail_atms \<Gamma>)"
      unfolding linorder_trm.is_lower_set_iff
    proof (intro conjI ballI impI)
      show "fset (trail_atms \<Gamma>') \<subseteq> fset (trail_atms \<Gamma>)"
        unfolding fset_trail_atms using \<open>suffix \<Gamma>' \<Gamma>\<close> by (metis image_mono set_mono_suffix)
    next
      obtain \<Gamma>'' where "\<Gamma> = \<Gamma>'' @ \<Gamma>'"
        using \<open>suffix \<Gamma>' \<Gamma>\<close> unfolding suffix_def by metis

      fix l x
      assume "l |\<in>| trail_atms \<Gamma>'" and "x |\<in>| trail_atms \<Gamma>" and "x \<prec>\<^sub>t l"

      have "x |\<in>| trail_atms \<Gamma>'' \<or> x |\<in>| trail_atms \<Gamma>'"
        using \<open>x |\<in>| trail_atms \<Gamma>\<close> unfolding \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> fset_trail_atms by auto

      thus "x |\<in>| trail_atms \<Gamma>'"
      proof (elim disjE)
        assume "x |\<in>| trail_atms \<Gamma>''"

        hence "l \<prec>\<^sub>t x"
          using \<Gamma>_sorted \<open>l |\<in>| trail_atms \<Gamma>'\<close>
          unfolding \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> sorted_wrt_append fset_trail_atms by blast

        hence False
          using \<open>x \<prec>\<^sub>t l\<close> by order

        thus "x |\<in>| trail_atms \<Gamma>'" ..
      next
        assume "x |\<in>| trail_atms \<Gamma>'"
        thus "x |\<in>| trail_atms \<Gamma>'" .
      qed
    qed

    thus ?thesis
      using \<Gamma>_lower
      unfolding \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')\<close>
      by order
  qed

  moreover have "\<forall>DE. Some C = Some DE \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>'.
    \<exists>L. ord_res.is_maximal_lit L DE \<and> A \<preceq>\<^sub>t atm_of L)"
    using atms_in_\<Gamma>'_lt_atm_K C_max_lit by fastforce

  moreover have "\<forall>Ln \<in> set \<Gamma>'. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    using \<Gamma>_deci_iff_neg \<open>suffix \<Gamma>' \<Gamma>\<close>
    by (metis (no_types, opaque_lifting) in_set_conv_decomp suffixE suffix_appendD)

  moreover have "trail_true_cls \<Gamma>' C"
    if "Ln \<in> set \<Gamma>'" and "snd Ln = None" and "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and "C \<prec>\<^sub>c {#fst Ln#}"
    for Ln C
  proof -
    have "Ln \<in> set \<Gamma>"
      using \<open>Ln \<in> set \<Gamma>'\<close> \<open>suffix \<Gamma>' \<Gamma>\<close> set_mono_suffix by blast

    have "C = eres D E \<or> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')\<close>
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    thus "trail_true_cls \<Gamma>' C"
    proof (elim disjE)
      assume "C = eres D E"

      hence "K \<prec>\<^sub>l fst Ln"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close> eres_max_lit
        by (simp add: linorder_lit.is_maximal_in_mset_iff)

      hence "atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
        by (cases K; cases "fst Ln") simp_all

      moreover have "atm_of (fst Ln) |\<in>| trail_atms \<Gamma>'"
        using \<open>Ln \<in> set \<Gamma>'\<close> by (simp add: fset_trail_atms)

      moreover have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')"
        by (metis \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
            atm_of_in_atms_of_clssI eres_max_lit finsert_iff linorder_lit.is_maximal_in_mset_iff)

      ultimately have "atm_of K |\<in>| trail_atms \<Gamma>'"
        using \<Gamma>'_lower
        unfolding linorder_trm.is_lower_set_iff
        by fastforce

      moreover have "atm_of K |\<notin>| trail_atms \<Gamma>'"
        using atms_in_\<Gamma>'_lt_atm_K by blast

      ultimately show "trail_true_cls \<Gamma>' C"
        by contradiction
    next
      assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"

      hence "trail_true_cls \<Gamma> C"
        using \<Gamma>_deci_ball_lt_true \<open>Ln \<in> set \<Gamma>\<close> \<open>snd Ln = None\<close> \<open>C \<prec>\<^sub>c {#fst Ln#}\<close> by metis

      then obtain L\<^sub>C where "L\<^sub>C \<in># C" and "trail_true_lit \<Gamma> L\<^sub>C"
        unfolding trail_true_cls_def by auto

      hence "\<forall>x \<in># C. x \<prec>\<^sub>l fst Ln"
        using \<open>C \<prec>\<^sub>c {#fst Ln#}\<close>
        unfolding multp_singleton_right[OF linorder_lit.transp_on_less]
        by simp

      hence "L\<^sub>C \<prec>\<^sub>l fst Ln"
        using \<open>L\<^sub>C \<in># C\<close> by metis

      hence "atm_of L\<^sub>C \<preceq>\<^sub>t atm_of (fst Ln)"
        by (cases L\<^sub>C; cases "fst Ln") simp_all

      moreover have "atm_of (fst Ln) \<prec>\<^sub>t atm_of K"
        using atms_in_\<Gamma>'_lt_atm_K
        by (simp add: fset_trail_atms that(1))

      ultimately have "atm_of L\<^sub>C \<prec>\<^sub>t atm_of K"
        by order

      have "L\<^sub>C \<in> fst ` set \<Gamma>"
        using \<open>trail_true_lit \<Gamma> L\<^sub>C\<close>
        unfolding trail_true_lit_def .

      hence "L\<^sub>C \<in> fst ` set \<Gamma>'"
        using mem_set_\<Gamma>'_iff
        using \<open>atm_of L\<^sub>C \<prec>\<^sub>t atm_of K\<close> linorder_trm.not_le by auto

      hence "trail_true_lit \<Gamma>' L\<^sub>C"
        unfolding trail_true_lit_def .

      thus "trail_true_cls \<Gamma>' C"
        using \<open>L\<^sub>C \<in># C\<close>
        unfolding trail_true_cls_def by auto
    qed
  qed

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    using \<Gamma>_prop_in \<open>suffix \<Gamma>' \<Gamma>\<close> set_mono_suffix \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by blast

  moreover have "\<forall>Ln \<in> set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest \<open>suffix \<Gamma>' \<Gamma>\<close> set_mono_suffix by blast

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<Gamma>_prop_almost_false \<open>suffix \<Gamma>' \<Gamma>\<close>
    by (metis (no_types, lifting) append.assoc suffix_def)

  moreover have "\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C)"
  proof (intro allI impI ballI)
    fix
      \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 :: "('f gliteral \<times> 'f gclause option) list" and
      L :: "'f gliteral" and
      C\<^sub>0 C\<^sub>1 :: "'f gclause"
    assume
      \<Gamma>'_eq: "\<Gamma>' = \<Gamma>\<^sub>1 @ (L, Some C\<^sub>1) # \<Gamma>\<^sub>0" and
      C\<^sub>0_in: "C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and
      "C\<^sub>0 \<prec>\<^sub>c C\<^sub>1"

    have "C\<^sub>0 = eres D E \<or> C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using C\<^sub>0_in
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0"
    proof (elim disjE)
      assume "C\<^sub>0 = eres D E"

      have "\<not> atm_of K \<preceq>\<^sub>t atm_of (fst (L, Some C\<^sub>1))" and "(L, Some C\<^sub>1) \<in> set \<Gamma>"
        unfolding atomize_conj
        using \<Gamma>'_eq \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
        using mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
        by (metis in_set_conv_decomp)

      then have "\<not> atm_of K \<preceq>\<^sub>t atm_of L"
        by simp

      hence "atm_of L \<prec>\<^sub>t atm_of K"
        by order

      moreover have "linorder_lit.is_greatest_in_mset C\<^sub>1 L"
        using \<Gamma>_prop_greatest \<open>(L, Some C\<^sub>1) \<in> set \<Gamma>\<close> by fastforce

      ultimately have False
        using \<open>C\<^sub>0 \<prec>\<^sub>c C\<^sub>1\<close>
        by (smt (verit) \<open>C\<^sub>0 = eres D E\<close> eres_max_lit linorder_cls.dual_order.asym
            linorder_lit.dual_order.strict_trans
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
            linorder_lit.multp_if_maximal_less_that_maximal linorder_lit.not_less_iff_gr_or_eq
            literal.collapse(1) literal.collapse(2) ord_res.less_lit_simps(1)
            ord_res.less_lit_simps(4))

      thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0" ..
    next
      assume "C\<^sub>0 |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      thus "trail_true_cls \<Gamma>\<^sub>0 C\<^sub>0"
        using \<Gamma>_prop_ball_lt_true \<Gamma>'_eq \<open>C\<^sub>0 \<prec>\<^sub>c C\<^sub>1\<close>
        by (metis (no_types, opaque_lifting) \<open>suffix \<Gamma>' \<Gamma>\<close> append_assoc suffixE)
    qed
  qed

  ultimately show ?thesis
    unfolding \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)\<close>
  proof (intro ord_res_7_invars.intros)
    have clause_true_in_\<Gamma>'_if: "trail_true_cls \<Gamma>' x" and
      "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow>
        \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>')"
      if x_lt: "\<And>DE. Some C = Some DE \<longrightarrow> x \<prec>\<^sub>c DE" and x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
      for x
    proof -
      have "x \<prec>\<^sub>c C"
        using x_lt by metis

      hence "x \<prec>\<^sub>c eres D E"
        using \<open>C \<prec>\<^sub>c eres D E\<close> by order

      hence "x \<noteq> eres D E"
        by order

      have "x \<prec>\<^sub>c E"
        using \<open>x \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

      moreover have x_in': "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using x_in \<open>x \<noteq> eres D E\<close>
        unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        by simp

      ultimately have x_true: "trail_true_cls \<Gamma> x"
        using clauses_lt_E_true by metis

      then obtain L\<^sub>x where "L\<^sub>x \<in># x" and "trail_true_lit \<Gamma> L\<^sub>x"
        unfolding trail_true_cls_def by metis

      have "L\<^sub>x \<preceq>\<^sub>l - K"
        using C_max_lit \<open>x \<prec>\<^sub>c C\<close> \<open>L\<^sub>x \<in># x\<close>
        by (smt (verit, ccfv_threshold) asympD empty_not_add_mset ord_res.transp_less_lit insert_DiffM
            linorder_lit.is_greatest_in_set_iff linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
            linorder_lit.is_maximal_in_mset_iff linorder_lit.is_maximal_in_set_eq_is_greatest_in_set
            linorder_lit.is_maximal_in_set_iff linorder_lit.leI ord_res.asymp_less_cls
            ord_res.multp_if_all_left_smaller transpE)

      have mono_atms_lt: "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
        (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
      proof (intro monotone_onI, unfold le_bool_def, intro impI)
        fix x y
        assume "atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)" and "atm_of K \<preceq>\<^sub>t atm_of (fst y)"
        thus "atm_of K \<preceq>\<^sub>t atm_of (fst x)"
          by order
      qed

      obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 where \<Gamma>_eq: "\<Gamma> = \<Gamma>\<^sub>1 @ (- K, Some C) # \<Gamma>\<^sub>0"
        using \<open>(- K, Some C) \<in> set \<Gamma>\<close> by (metis split_list)

      hence "trail_true_cls \<Gamma>\<^sub>0 x"
        using \<Gamma>_prop_ball_lt_true x_in' \<open>x \<prec>\<^sub>c C\<close> by metis

      then obtain  L\<^sub>x where "L\<^sub>x \<in># x" and L\<^sub>x_true: "trail_true_lit \<Gamma>\<^sub>0 L\<^sub>x"
        unfolding trail_true_cls_def by auto

      moreover have "\<Gamma>' = \<Gamma>\<^sub>0"
      proof -
        have "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) ((\<Gamma>\<^sub>1 @ [(- K, Some C)]) @ \<Gamma>\<^sub>0)"
          unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close> \<Gamma>_eq by simp

        also have "\<dots> = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>0"
        proof (rule dropWhile_append2)
          fix Ln :: "'f gterm literal \<times> 'f gclause option"
          assume "Ln \<in> set (\<Gamma>\<^sub>1 @ [(- K, Some C)])"

          moreover have "\<forall>x\<in>set \<Gamma>\<^sub>1. atm_of K \<prec>\<^sub>t atm_of (fst x)"
            using \<Gamma>_sorted by (simp add: \<Gamma>_eq sorted_wrt_append)

          ultimately show "atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
            using \<open>is_neg K\<close> by auto
        qed

        also have "\<dots> = \<Gamma>\<^sub>0"
        proof (cases \<Gamma>\<^sub>0)
          case Nil
          thus ?thesis
            by (simp add: dropWhile_eq_self_iff)
        next
          case (Cons Ln \<Gamma>\<^sub>0')

          hence "atm_of (fst Ln) \<prec>\<^sub>t atm_of K"
            using \<Gamma>_sorted by (simp add: \<Gamma>_eq sorted_wrt_append)

          hence "\<not> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
            by order

          hence "\<not> atm_of K \<preceq>\<^sub>t atm_of (fst (hd \<Gamma>\<^sub>0))"
            by (simp add: \<open>\<Gamma>\<^sub>0 = Ln # \<Gamma>\<^sub>0'\<close>)

          thus ?thesis
            by (simp add: dropWhile_eq_self_iff)
        qed

        finally show ?thesis .
      qed

      ultimately have "trail_true_lit \<Gamma>' L\<^sub>x"
        by argo

      thus "trail_true_cls \<Gamma>' x"
        using \<open>L\<^sub>x \<in># x\<close> unfolding trail_true_cls_def by metis


      fix K\<^sub>x
      assume x_max_lit: "ord_res.is_maximal_lit K\<^sub>x x"

      hence "K\<^sub>x \<preceq>\<^sub>l K"
        using \<open>x \<prec>\<^sub>c eres D E\<close> eres_max_lit
        using linorder_lit.multp_if_maximal_less_that_maximal by fastforce

      hence "atm_of K\<^sub>x \<preceq>\<^sub>t atm_of K"
        by (cases K\<^sub>x; cases K) simp_all

      have "A |\<in>| trail_atms \<Gamma>'"
        if A_lt: "A \<prec>\<^sub>t atm_of K\<^sub>x" and A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" for A
        unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
      proof (rule in_trail_atms_dropWhileI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
          using \<Gamma>_sorted .
      next
        show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x) (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
          using mono_atms_lt .
      next
        show "\<not> atm_of K \<preceq>\<^sub>t A"
          using A_lt \<open>atm_of K\<^sub>x \<preceq>\<^sub>t atm_of K\<close> by order
      next
        have "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>)"
          using no_undef_atm_lt_max_lit_if_lt_E \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>x \<prec>\<^sub>c E\<close> x_max_lit
          by metis

        thus "A |\<in>| trail_atms \<Gamma>"
          using A_in A_lt by metis
      qed

      thus "\<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K\<^sub>x \<and> A |\<notin>| trail_atms \<Gamma>')"
        using \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')\<close> by metis
    qed

    thus
      "\<forall>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). (\<forall>DE. Some C = Some DE \<longrightarrow> x \<prec>\<^sub>c DE) \<longrightarrow>
        trail_true_cls \<Gamma>' x"
      "\<forall>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). (\<forall>DE. Some C = Some DE \<longrightarrow> x \<prec>\<^sub>c DE) \<longrightarrow>
        (\<forall>K. ord_res.is_maximal_lit K x \<longrightarrow>
          \<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>'))"
      unfolding atomize_conj by metis

    have "trail_true_cls \<Gamma>' {#K \<in># B. K \<noteq> L\<^sub>B#} \<and> is_pos L\<^sub>B"
      if "Some C = Some C'" and
        B_in: "B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and
        B_lt: "B \<prec>\<^sub>c C'" and
        B_max_lit: "linorder_lit.is_maximal_in_mset B L\<^sub>B" and
        L\<^sub>B_undef: "\<not> trail_defined_lit \<Gamma>' L\<^sub>B"
      for C' B L\<^sub>B
    proof -
      have "C' = C"
        using that by simp
      hence "B \<prec>\<^sub>c C"
        using B_lt by order
      hence "B \<prec>\<^sub>c eres D E"
        using \<open>C \<prec>\<^sub>c eres D E\<close> by order
      hence "B \<noteq> eres D E"
        by order
      hence "B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using B_in \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        by simp
      moreover have "B \<prec>\<^sub>c E"
        using \<open>B \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

      have "L\<^sub>B \<preceq>\<^sub>l - K"
        using \<open>B \<prec>\<^sub>c C\<close> B_max_lit C_max_lit
        by (metis asympD linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.leI
            linorder_lit.multp_if_maximal_less_that_maximal ord_res.asymp_less_cls)
      hence "L\<^sub>B \<prec>\<^sub>l - K \<or> L\<^sub>B = - K"
        by simp

      thus ?thesis
      proof (elim disjE)
        assume "L\<^sub>B \<prec>\<^sub>l - K"
        hence "atm_of L\<^sub>B \<prec>\<^sub>t atm_of K"
          using \<open>is_neg K\<close>
          by (cases L\<^sub>B; cases K) simp_all

        have "trail_defined_lit \<Gamma>' L\<^sub>B"
          unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
        proof (intro trail_defined_lit_dropWhileI ballI)
          show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
            using \<Gamma>_sorted .
        next
          show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
        (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))"
            using mono_atms_lt .
        next
          have "\<not> atm_of K \<preceq>\<^sub>t atm_of L\<^sub>B"
            using \<open>atm_of L\<^sub>B \<prec>\<^sub>t atm_of K\<close> by order
          thus "\<not> atm_of K \<preceq>\<^sub>t atm_of L\<^sub>B \<and> \<not> atm_of K \<preceq>\<^sub>t atm_of (- L\<^sub>B)"
            by simp
        next
          have "trail_defined_lit \<Gamma> K"
            by (metis map_of_eq_None_iff option.discI step_hyps(12) trail_defined_lit_def)
          moreover have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            by (metis \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')\<close>
                \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
                atm_of_in_atms_of_clssI eres_max_lit finsertI1 linorder_lit.is_maximal_in_mset_iff)
          moreover have "atm_of L\<^sub>B |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> B_max_lit atm_of_in_atms_of_clssI
            unfolding linorder_lit.is_maximal_in_mset_iff
            by metis
          ultimately show "trail_defined_lit \<Gamma> L\<^sub>B"
            using \<open>atm_of L\<^sub>B \<prec>\<^sub>t atm_of K\<close> \<Gamma>_lower
            unfolding trail_defined_lit_iff_trail_defined_atm
            by (meson linorder_trm.is_lower_set_iff)
        qed

        hence False
          using L\<^sub>B_undef by contradiction

        thus ?thesis ..
      next
        have "trail_true_cls \<Gamma>' B"
          using clause_true_in_\<Gamma>'_if B_in \<open>B \<prec>\<^sub>c C\<close> by blast
        hence "trail_true_cls \<Gamma>' {#K \<in># B. K \<noteq> L\<^sub>B#}"
          using L\<^sub>B_undef
          by (smt (verit, best) mem_Collect_eq set_mset_filter trail_defined_lit_iff_true_or_false
              trail_true_cls_def)
        moreover assume "L\<^sub>B = - K"
        ultimately show "trail_true_cls \<Gamma>' {#K \<in># B. K \<noteq> L\<^sub>B#} \<and> is_pos L\<^sub>B"
          using \<open>is_neg K\<close>
          by (cases K) simp_all
      qed
    qed

    thus "\<forall>Da. Some C = Some Da \<longrightarrow>
      (\<forall>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). x \<prec>\<^sub>c Da \<longrightarrow> (\<forall>L\<^sub>C. ord_res.is_maximal_lit L\<^sub>C x \<longrightarrow>
        \<not> trail_defined_lit \<Gamma>' L\<^sub>C \<longrightarrow> trail_true_cls \<Gamma>' {#K \<in># x. K \<noteq> L\<^sub>C#} \<and> is_pos L\<^sub>C))"
      by metis
  qed simp_all
qed

lemma rtranclp_ord_res_7_preserves_ord_res_7_invars:
  assumes
    step: "(ord_res_7 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_7_invars N s"
  shows "ord_res_7_invars N s'"
  using step invars ord_res_7_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

lemma tranclp_ord_res_7_preserves_ord_res_7_invars:
  assumes
    step: "(ord_res_7 N)\<^sup>+\<^sup>+ s s'" and
    invars: "ord_res_7_invars N s"
  shows "ord_res_7_invars N s'"
  using step invars ord_res_7_preserves_invars
  by (smt (verit, del_insts) tranclp_induct)

lemma propagating_clause_almost_false:
  assumes invars: "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" and "(L, Some C) \<in> set \<Gamma>"
  shows "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}"
proof -
  have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using invars unfolding ord_res_7_invars_def by metis

  hence "\<exists>\<Gamma>\<^sub>1 \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<and> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<open>(L, Some C) \<in> set \<Gamma>\<close> unfolding in_set_conv_decomp by metis

  thus "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}"
    by (metis suffixI suffix_ConsD trail_false_cls_if_trail_false_suffix)
qed

lemma ex_ord_res_7_if_not_final:
  assumes
    not_final: "\<not> ord_res_7_final (N, s)" and
    invars: "ord_res_7_invars N s"
  shows "\<exists>s'. ord_res_7 N s s'"
proof -
  obtain U\<^sub>e\<^sub>r \<F> \<Gamma> \<C> where "s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"
    by (metis surj_pair)

  note invars' = invars[unfolded ord_res_7_invars_def, rule_format, OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>]

  have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invars' by argo

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using \<Gamma>_sorted trail_consistent_if_sorted_wrt_atoms by metis

  have "distinct (map fst \<Gamma>)"
  proof (rule distinct_if_sorted_wrt_asymp)
    have "sorted_wrt (\<lambda>x y. fst y \<prec>\<^sub>l fst x) \<Gamma>"
    proof (rule sorted_wrt_mono_rel)
      show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
        using \<Gamma>_sorted .
    next
      fix x y :: "'f gterm literal \<times> 'f gterm literal multiset option"
      assume "atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)"
      thus "fst y \<prec>\<^sub>l fst x"
        by (cases "fst x"; cases "fst y") (simp_all only: literal.sel ord_res.less_lit_simps)
    qed

    thus "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>l x) (map fst \<Gamma>)"
      unfolding sorted_wrt_map .
  next
    show "asymp_on (set (map fst \<Gamma>)) (\<lambda>x y. y \<prec>\<^sub>l x)"
      using linorder_lit.asymp_on_greater .
  qed

  hence map_of_\<Gamma>_eq_SomeI: "\<And>x y. (x, y) \<in> set \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some y"
    by (metis map_of_is_SomeI)

  have \<Gamma>_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using invars' by argo

  obtain E where "\<C> = Some E" and "E \<noteq> {#}"
    using not_final[unfolded \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> ord_res_7_final.simps, simplified]
    by metis

  have E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using invars' \<open>\<C> = Some E\<close> by metis

  obtain L where E_max_lit: "ord_res.is_maximal_lit L E"
    using \<open>E \<noteq> {#}\<close> linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases "trail_false_cls \<Gamma> E")
    case E_false: True

    hence L_false: "trail_false_lit \<Gamma> L"
      using E_max_lit unfolding linorder_lit.is_maximal_in_mset_iff trail_false_cls_def by metis

    hence "\<exists>opt. (- L, opt) \<in> set \<Gamma>"
        by (auto simp: trail_false_lit_def)

    have "\<not> is_pos L"
    proof (rule notI)
      assume "is_pos L"

      hence "is_neg (- L)"
        by (metis \<open>is_pos L\<close> is_pos_neg_not_is_pos)

      hence "(- L, None) \<in> set \<Gamma>"
        using invars' \<open>\<exists>opt. (- L, opt) \<in> set \<Gamma>\<close> by (metis prod.sel)

      moreover have "E \<prec>\<^sub>c {#- L#}"
        using E_max_lit \<open>is_pos L\<close>
        by (smt (verit, best) Neg_atm_of_iff add_mset_remove_trivial empty_iff
            ord_res.less_lit_simps(4) linorder_cls.less_irrefl linorder_lit.is_greatest_in_mset_iff
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.less_linear
            linorder_lit.multp_if_maximal_less_that_maximal literal.collapse(1)
            ord_res.less_lit_simps(1) set_mset_empty uminus_literal_def union_single_eq_member)

      ultimately have "trail_true_cls \<Gamma> E"
        using invars' E_in by force

      hence "\<not> trail_false_cls \<Gamma> E"
        by (metis \<Gamma>_consistent not_trail_true_cls_and_trail_false_cls)

      thus False
        using E_false by contradiction
    qed

    hence L_neg: "is_neg L"
      by argo

    then obtain D where "(- L, Some D) \<in> set \<Gamma>"
      using invars' \<open>is_neg L\<close> \<open>\<exists>opt. (- L, opt) \<in> set \<Gamma>\<close>
      by (metis prod.sel is_pos_neg_not_is_pos not_Some_eq)

    hence "map_of \<Gamma> (- L) = Some (Some D)"
      using map_of_\<Gamma>_eq_SomeI by metis

    have "\<exists>\<Gamma>\<^sub>1 \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (- L, Some D) # \<Gamma>\<^sub>0 \<and> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D. K \<noteq> - L#}"
      using invars' \<open>(- L, Some D) \<in> set \<Gamma>\<close> propagating_clause_almost_false
      unfolding in_set_conv_decomp by metis

    have D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> - L#}"
      using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>(- L, Some D) \<in> set \<Gamma>\<close> propagating_clause_almost_false
      by metis

    show ?thesis
    proof (cases "eres D E = {#}")
      case True
      thus ?thesis
        unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
        using E_false E_max_lit L_neg \<open>map_of \<Gamma> (- L) = Some (Some D)\<close>
        using ord_res_7.resolution_bot by metis
    next
      case False

      then obtain K where eres_max_lit: "ord_res.is_maximal_lit K (eres D E)"
        using linorder_lit.ex_maximal_in_mset by metis

      hence "K \<in># eres D E"
        unfolding linorder_lit.is_maximal_in_mset_iff by argo

      hence "K \<in># D \<and> K \<noteq> - L \<or> K \<in># E"
        using strong_lit_in_one_of_resolvents_if_in_eres[OF E_max_lit] by metis

      hence K_false: "trail_false_lit \<Gamma> K"
        using D_almost_false E_false unfolding trail_false_cls_def by auto

      hence "\<exists>opt. (- K, opt) \<in> set \<Gamma>"
        by (auto simp: trail_false_lit_def)

      show ?thesis
      proof (cases K)
        case (Pos A\<^sub>K)

        hence "is_pos K"
          by simp

        thus ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
          using E_false E_max_lit L_neg \<open>map_of \<Gamma> (- L) = Some (Some D)\<close> False eres_max_lit
          using ord_res_7.resolution_pos by metis
      next
        case (Neg A\<^sub>K)

        hence "is_neg K"
          by simp

        then obtain C where "(- K, Some C) \<in> set \<Gamma>"
          using invars' \<open>is_neg L\<close> \<open>\<exists>opt. (- K, opt) \<in> set \<Gamma>\<close>
          by (metis prod.sel is_pos_neg_not_is_pos not_Some_eq)

        hence "map_of \<Gamma> (- K) = Some (Some C)"
          using map_of_\<Gamma>_eq_SomeI by metis

        thus ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
          using E_false E_max_lit L_neg \<open>map_of \<Gamma> (- L) = Some (Some D)\<close> False eres_max_lit
            \<open>is_neg K\<close>
          using ord_res_7.resolution_neg by metis
      qed
    qed
  next
    case E_not_false: False
    show ?thesis
    proof (cases "\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>")
      case True

      then obtain A where A_least: "linorder_trm.is_least_in_fset
        {|A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>|} A"
        by (metis (no_types, lifting) bot_fset.rep_eq empty_iff ffmember_filter
            linorder_trm.ex_least_in_fset)

      show ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
          using ord_res_7.decide_neg[OF E_not_false E_max_lit A_least refl, of \<F>]
          by metis
    next
      case nex_undef_atm_lt_L: False
      show ?thesis
      proof (cases "trail_defined_lit \<Gamma> L")
        case True
        thus ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
          using ord_res_7.skip_defined[OF E_not_false E_max_lit nex_undef_atm_lt_L]
          by metis
      next
        case L_undef: False
        show ?thesis
        proof (cases L)
          case L_eq: (Pos A\<^sub>L)

          hence L_pos: "is_pos L"
            by simp

          show ?thesis
          proof (cases "trail_false_cls \<Gamma> {#K \<in># E. K \<noteq> L#}")
            case E_almost_false: True
            show ?thesis
            proof (cases "ord_res.is_strictly_maximal_lit L E")
              case True
              thus ?thesis
                unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
                using ord_res_7.production[OF E_not_false E_max_lit nex_undef_atm_lt_L L_undef L_pos
                    E_almost_false]
                by metis
            next
              case False
              thus ?thesis
                unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
                using ord_res_7.factoring[OF E_not_false E_max_lit nex_undef_atm_lt_L L_undef L_pos
                    E_almost_false]
                by metis
            qed
          next
            case E_not_almost_false: False
            show ?thesis
            proof (cases "\<exists>D|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). E \<prec>\<^sub>c D")
              case True

              then obtain F where "linorder_cls.is_least_in_fset
                (ffilter ((\<prec>\<^sub>c) E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) F"
                by (metis bot_fset.rep_eq empty_iff ffmember_filter linorder_cls.ex1_least_in_fset)

              thus ?thesis
                unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
                using ord_res_7.skip_undefined_pos[OF E_not_false E_max_lit nex_undef_atm_lt_L L_undef
                    L_pos E_not_almost_false]
                by metis
            next
              case False
              thus ?thesis
                unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
                using ord_res_7.skip_undefined_pos_ultimate[OF E_not_false E_max_lit
                    nex_undef_atm_lt_L L_undef L_pos E_not_almost_false]
                by metis
            qed
          qed
        next
          case L_eq: (Neg A\<^sub>L)

          hence "is_neg L"
            by simp

          thus ?thesis
            unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some E\<close>
            using ord_res_7.skip_undefined_neg[OF E_not_false E_max_lit nex_undef_atm_lt_L L_undef]
            by metis
        qed
      qed
    qed
  qed
qed

lemma ord_res_7_safe_state_if_invars:
  fixes N :: "'f gclause fset" and s
  assumes invars: "ord_res_7_invars N s"
  shows "safe_state (constant_context ord_res_7) ord_res_7_final (N, s)"
  using safe_state_constant_context_if_invars[where
      \<R> = ord_res_7 and \<F> = ord_res_7_final and \<I> = ord_res_7_invars]
  using ord_res_7_preserves_invars ex_ord_res_7_if_not_final invars by metis

end

end