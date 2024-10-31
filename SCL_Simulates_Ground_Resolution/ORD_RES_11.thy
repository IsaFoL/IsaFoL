theory ORD_RES_11
  imports ORD_RES_10
begin

section \<open>ORD-RES-11 (SCL strategy)\<close>

type_synonym 'f ord_res_11_state =
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gliteral \<times> 'f gclause option) list \<times>
    'f gclause option"

context simulation_SCLFOL_ground_ordered_resolution begin

lemma
  fixes N U\<^sub>e\<^sub>r \<F> \<Gamma> A
  assumes
    no_false_cls: "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)" and
    A_least: "linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A" and
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C"
  defines
    "\<Gamma>' \<equiv> (Pos A, None) # \<Gamma>" and
    "\<F>' \<equiv> (if linorder_lit.is_greatest_in_mset C (Pos A) then \<F> else finsert C \<F>)"
  shows "
    (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C) \<longleftrightarrow>
    (\<exists>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
  by (meson bex_trail_false_cls_simp)

inductive ord_res_11 where
  decide_neg: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)" |

  decide_pos: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<Gamma>' = (Pos A, None) # \<Gamma> \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C) \<Longrightarrow>
    \<F>' = (if linorder_lit.is_greatest_in_mset C (Pos A) then \<F> else finsert C \<F>) \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>', None)" |

  propagate: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<Gamma>' = (Pos A, Some (efac C)) # \<Gamma> \<Longrightarrow>
    (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C) \<Longrightarrow>
    \<F>' = (if linorder_lit.is_greatest_in_mset C (Pos A) then \<F> else finsert C \<F>) \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>', None)" |

  conflict: "
    linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> D|} D \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)" |

  skip: "- L \<notin># C \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, (L, n) # \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" |

  resolution: "
    \<Gamma> = (L, Some D) # \<Gamma>' \<Longrightarrow> - L \<in># C \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some ((C - {#- L#}) + (D - {#L#})))" |

  backtrack: "
    \<Gamma> = (L, None) # \<Gamma>' \<Longrightarrow> - L \<in># C \<Longrightarrow>
    ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C) (finsert C U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)"

(* ORD-RES-10's resolution rule is equivalent to "conflict resolution+ skip+ backtrack" here. *)

lemma right_unique_ord_res_11:
  fixes N :: "'f gclause fset"
  shows "right_unique (ord_res_11 N)"
proof (rule right_uniqueI)
  fix x y z
  assume step1: "ord_res_11 N x y" and step2: "ord_res_11 N x z"
  show "y = z"
    using step1
  proof (cases N x y rule: ord_res_11.cases)
    case hyps1: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A1 \<Gamma>1')
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None :: 'f gclause option)" z rule: ord_res_11.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 show ?thesis
        by (metis (no_types, lifting) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
    next
      case (decide_pos A C \<Gamma>' \<F>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff
            linorder_trm.dual_order.asym linorder_trm.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff
            linorder_trm.dual_order.asym linorder_trm.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (conflict D)
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (decide_pos \<F> U\<^sub>e\<^sub>r \<Gamma> A1 C1 \<Gamma>1' \<F>1')
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None :: 'f gclause option)" z rule: ord_res_11.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff
            linorder_trm.dual_order.asym linorder_trm.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (decide_pos A C \<Gamma>' \<F>')
      with hyps1 show ?thesis
        by (metis (no_types, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_trm.Uniq_is_least_in_fset the1_equality')
    next
      case hyps2: (propagate A C \<Gamma>' \<F>')
      have "A1 = A"
        using \<open>linorder_trm.is_least_in_fset _ A1\<close> \<open>linorder_trm.is_least_in_fset _ A\<close>
        by (metis (no_types) linorder_trm.Uniq_is_least_in_fset Uniq_D)
      hence "trail_false_cls \<Gamma>1' = trail_false_cls \<Gamma>'"
        unfolding \<open>\<Gamma>1' = _ # \<Gamma>\<close> \<open>\<Gamma>' = _ # \<Gamma>\<close>
        unfolding trail_false_cls_def trail_false_lit_def
        by simp
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    next
      case (conflict D)
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A1 C1 \<Gamma>1' \<F>1')
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None :: 'f gclause option)" z rule: ord_res_11.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff
            linorder_trm.dual_order.asym linorder_trm.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case hyps2: (decide_pos A C \<Gamma>' \<F>')
      have "A1 = A"
        using \<open>linorder_trm.is_least_in_fset _ A1\<close> \<open>linorder_trm.is_least_in_fset _ A\<close>
        by (metis (no_types) linorder_trm.Uniq_is_least_in_fset Uniq_D)
      hence "trail_false_cls \<Gamma>1' = trail_false_cls \<Gamma>'"
        unfolding \<open>\<Gamma>1' = _ # \<Gamma>\<close> \<open>\<Gamma>' = _ # \<Gamma>\<close>
        unfolding trail_false_cls_def trail_false_lit_def
        by simp
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 show ?thesis
        by (metis (no_types, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_trm.Uniq_is_least_in_fset the1_equality')
    next
      case (conflict D)
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (conflict \<Gamma> \<F> U\<^sub>e\<^sub>r D1)
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None :: 'f gclause option)" z rule: ord_res_11.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (decide_pos A C \<Gamma>' \<F>')
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (conflict D)
      with hyps1 show ?thesis
        by (metis (no_types) linorder_cls.Uniq_is_least_in_fset Uniq_D)
    qed
  next
    case hyps1: (skip L C U\<^sub>e\<^sub>r \<F> n \<Gamma>)
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, (L, n) # \<Gamma>, Some C)" z rule: ord_res_11.cases)
      case skip
      with hyps1 show ?thesis
        by argo
    next
      case (resolution L' D' \<Gamma>')
      with hyps1 have False
        by simp
      thus ?thesis ..
    next
      case (backtrack K \<Gamma>')
      with hyps1 have False
        by simp
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution \<Gamma> L1 D1 \<Gamma>1' C U\<^sub>e\<^sub>r \<F>)
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_11.cases)
      case (skip L n \<Gamma>)
      with hyps1 have False
        by simp
      thus ?thesis ..
    next
      case (resolution L D \<Gamma>')
      with hyps1 show ?thesis
        by simp
    next
      case (backtrack K \<Gamma>')
      with hyps1 have False
        by simp
      thus ?thesis ..
    qed
  next
    case hyps1: (backtrack \<Gamma> L \<Gamma>' C U\<^sub>e\<^sub>r \<F>)
    show ?thesis
      using step2 unfolding \<open>x = _\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some C)" z rule: ord_res_11.cases)
      case (skip L n \<Gamma>)
      with hyps1 have False
        by simp
      thus ?thesis ..
    next
      case (resolution L D \<Gamma>')
      with hyps1 have False
        by simp
      thus ?thesis ..
    next
      case (backtrack K \<Gamma>')
      with hyps1 show ?thesis
        by simp
    qed
  qed
qed


inductive ord_res_11_final :: "'f ord_res_11_state \<Rightarrow> bool" where
  model_found: "
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    ord_res_11_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None)" |

  contradiction_found: "
    ord_res_11_final (N, U\<^sub>e\<^sub>r, \<F>, [], Some {#})"

sublocale ord_res_11_semantics: semantics where
  step = "constant_context ord_res_11" and
  final = ord_res_11_final
proof unfold_locales
  fix S :: "'f ord_res_11_state"

  assume "ord_res_11_final S"
  thus "finished (constant_context ord_res_11) S"
  proof (cases S rule: ord_res_11_final.cases)
    case (model_found N U\<^sub>e\<^sub>r \<Gamma> \<F>)

    have "\<nexists>A. linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
      using \<open>\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>)\<close>
      unfolding linorder_trm.is_least_in_ffilter_iff
      by blast

    moreover have "\<nexists>D. linorder_cls.is_least_in_fset
      (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      using \<open>\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)\<close>
      unfolding linorder_cls.is_least_in_ffilter_iff
      by metis

    ultimately have "\<nexists>x. ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, None) x"
      by (auto elim: ord_res_11.cases)

    thus ?thesis
      by (simp add: \<open>S = _\<close> finished_def constant_context.simps)
  next
    case (contradiction_found N U\<^sub>e\<^sub>r \<F>)
    hence "\<nexists>x. ord_res_11 N (U\<^sub>e\<^sub>r, \<F>, [], Some {#}) x"
      by (auto elim: ord_res_11.cases)
    thus ?thesis
      by (simp add: \<open>S = _\<close> finished_def constant_context.simps)
  qed
qed

inductive ord_res_11_invars where
  "ord_res_11_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" if
    "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" and
    "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<longrightarrow> \<Gamma> = []" and
    "\<forall>C. \<C> = Some C \<longrightarrow> atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
    "\<forall>C. \<C> = Some C \<longrightarrow> trail_false_cls \<Gamma> C" and
    "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N" and
    "\<forall>C |\<in>| \<F>. \<exists>L. is_pos L \<and> linorder_lit.is_maximal_in_mset C L"

lemma ord_res_11_invars_initial_state: "ord_res_11_invars N ({||}, {||}, [], None)"
  by (intro ord_res_11_invars.intros ord_res_10_invars.intros) simp_all

lemma mempty_in_fimage_iefac[simp]: "{#} |\<in>| iefac \<F> |`| N \<longleftrightarrow> {#} |\<in>| N"
  using iefac_def by auto

lemma ord_res_11_preserves_invars:
  assumes
    step: "ord_res_11 N s s'" and
    invars: "ord_res_11_invars N s"
  shows "ord_res_11_invars N s'"
  using invars
proof (cases N s rule: ord_res_11_invars.cases)
  case more_invars: (1 U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>)
  show ?thesis
    using \<open>ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" rule: ord_res_10_invars.cases)
    case invars: 1

    note \<Gamma>_sorted = \<open>sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>\<close>
    note \<Gamma>_lower = \<open>linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))\<close>

    have "trail_consistent \<Gamma>"
      using \<Gamma>_sorted trail_consistent_if_sorted_wrt_atoms by metis

    show ?thesis
      using step unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" s' rule: ord_res_11.cases)
      case step_hyps: (decide_neg A \<Gamma>')

      have
        A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
        A_gt: "\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A" and
        A_lt: "\<forall>y|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
        y \<noteq> A \<longrightarrow> (\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t y) \<longrightarrow> A \<prec>\<^sub>t y"
        using \<open>linorder_trm.is_least_in_fset _ A\<close>
        unfolding atomize_conj linorder_trm.is_least_in_ffilter_iff
        by argo

      have "trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)"
        unfolding \<open>\<Gamma>' = (Neg A, _) # \<Gamma>\<close> by simp

      show ?thesis
        unfolding \<open>s' = (_, _, _)\<close>
      proof (intro ord_res_11_invars.intros ord_res_10_invars.intros allI impI conjI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
          unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> sorted_wrt.simps
        proof (intro conjI ballI)
          fix Ln :: "'f gliteral \<times> 'f gclause option"
          assume "Ln \<in> set \<Gamma>"

          hence "atm_of (fst Ln) |\<in>| trail_atms \<Gamma>"
            by (simp add: fset_trail_atms)

          thus "atm_of (fst Ln) \<prec>\<^sub>t atm_of (fst (Neg A, None))"
            unfolding prod.sel literal.sel
            using A_gt by metis
        next
          show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
            using \<Gamma>_sorted .
        qed

        show "\<forall>Ln\<in>set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> ord_res.is_strictly_maximal_lit (fst Ln) C"
          unfolding \<open>\<Gamma>' = (_, None) # \<Gamma>\<close>
          using invars by simp

        show "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
          unfolding \<open>trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)\<close> finsert.rep_eq
        proof (intro linorder_trm.is_lower_set_insertI ballI impI)
          show "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            using A_in .
        next
          fix w :: "'f gterm"
          assume "w |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "w \<prec>\<^sub>t A"
          thus "w |\<in>| trail_atms \<Gamma>"
            by (metis A_lt \<Gamma>_lower linorder_trm.dual_order.asym linorder_trm.neq_iff
                linorder_trm.not_in_lower_setI)
        next
          show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
            using \<Gamma>_lower .
        qed

        {
          fix
            Ln :: "'f gliteral \<times> 'f gclause option" and
            \<Gamma>'' :: "('f gliteral \<times> 'f gclause option) list"

          assume "\<Gamma>' = Ln # \<Gamma>''"

          have "snd Ln = None"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> step_hyps by auto

          moreover have "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls ((Neg A, None) # \<Gamma>) C)"
          proof (rule notI , elim bexE)
            fix C :: "'f gclause"
            assume
              C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
              C_false: "trail_false_cls ((Neg A, None) # \<Gamma>) C"

            have "clause_could_propagate \<Gamma> C (Pos A)"
              unfolding clause_could_propagate_def
            proof (intro conjI)
              show "\<not> trail_defined_lit \<Gamma> (Pos A)"
                unfolding trail_defined_lit_iff_trail_defined_atm literal.sel
                by (metis A_gt linorder_trm.less_irrefl)
            next
              show "ord_res.is_maximal_lit (Pos A) C"
                unfolding linorder_lit.is_maximal_in_mset_iff
              proof (intro conjI ballI impI)
                have "\<not> trail_false_cls \<Gamma> C"
                  using step_hyps C_in by metis

                thus "Pos A \<in># C"
                  using C_false by (metis subtrail_falseI uminus_Neg)
              next

                fix L :: "'f gliteral"
                assume L_in: "L \<in># C" and L_neq: "L \<noteq> Pos A"

                have "trail_false_lit ((Neg A, None) # \<Gamma>) L"
                  using C_false L_in unfolding trail_false_cls_def by metis

                hence "- L \<in> fst ` set \<Gamma>"
                  unfolding trail_false_lit_def
                  using L_neq
                  by (cases L) simp_all

                hence "trail_defined_lit \<Gamma> L"
                  unfolding trail_defined_lit_def by argo

                hence "atm_of L |\<in>| trail_atms \<Gamma>"
                  unfolding trail_defined_lit_iff_trail_defined_atm .

                moreover have "\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A"
                  using step_hyps unfolding linorder_trm.is_least_in_ffilter_iff by argo

                ultimately have "atm_of L \<prec>\<^sub>t A"
                  by metis

                hence "L \<preceq>\<^sub>l Pos A"
                  by (cases L) simp_all

                thus "\<not> Pos A \<prec>\<^sub>l L"
                  by order
              qed
            next
              show "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
                using C_false
                unfolding trail_false_cls_def trail_false_lit_def
                by (smt (verit, ccfv_SIG) mem_Collect_eq set_mset_filter subtrail_falseI
                    trail_false_cls_def trail_false_lit_def uminus_Neg)
            qed

            moreover have "\<not> clause_could_propagate \<Gamma> C (Pos A)"
              using C_in step_hyps by metis

            ultimately show False
              by contradiction
          qed

          ultimately show "(snd Ln \<noteq> None) = (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
            unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by argo

          show "snd Ln \<noteq> None \<Longrightarrow> is_pos (fst Ln)"
            using \<open>snd Ln = None\<close> by argo

          have "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)"
            using step_hyps by argo

          hence "\<forall>x\<in>set \<Gamma>. snd x = None"
            using invars by (metis list.set_cases)

          thus "\<forall>x \<in> set \<Gamma>''. snd x = None"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp

          show "\<And>C. snd Ln = Some C \<Longrightarrow> clause_could_propagate \<Gamma>'' C (fst Ln)"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by force

          show "\<And>D. snd Ln = Some D \<Longrightarrow> D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by force
        }

        have "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls ((Neg A, None) # \<Gamma>) C)"
        proof (intro notI , elim bexE)
          fix C :: "'f gclause"
          assume
            C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            C_false: "trail_false_cls ((Neg A, None) # \<Gamma>) C"

          have "clause_could_propagate \<Gamma> C (Pos A)"
            unfolding clause_could_propagate_def
          proof (intro conjI)
            show "\<not> trail_defined_lit \<Gamma> (Pos A)"
              unfolding trail_defined_lit_iff_trail_defined_atm
              by (metis A_gt linorder_trm.less_irrefl literal.sel(1))
          next
            have "\<not> trail_false_cls \<Gamma> C"
              using C_in step_hyps by metis

            thus "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
              by (smt (verit) C_false mem_Collect_eq set_mset_filter subtrail_falseI
                  trail_false_cls_def uminus_Neg)

            show "ord_res.is_maximal_lit (Pos A) C"
              unfolding linorder_lit.is_maximal_in_mset_iff
            proof (intro conjI ballI impI)
              show "Pos A \<in># C"
                by (metis C_false \<open>\<not> trail_false_cls \<Gamma> C\<close> subtrail_falseI uminus_Neg)
            next
              fix L
              assume "L \<in># C" and "L \<noteq> Pos A"
              hence "atm_of L |\<in>| trail_atms \<Gamma>"
                using \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}\<close>
                using trail_defined_lit_iff_trail_defined_atm trail_defined_lit_iff_true_or_false
                  trail_false_cls_filter_mset_iff by blast
              hence "atm_of L \<prec>\<^sub>t A"
                using A_gt by metis
              hence "L \<prec>\<^sub>l Pos A"
                by (cases L) simp_all
              thus "\<not> Pos A \<prec>\<^sub>l L"
                by order
            qed
          qed

          moreover have "\<not> clause_could_propagate \<Gamma> C (Pos A)"
            using C_in step_hyps by metis

          ultimately show False
            by contradiction
        qed

        thus "\<And>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<Longrightarrow> snd Ln = None \<Longrightarrow>
        \<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"
          unfolding \<open>\<Gamma>' = (_, None) # \<Gamma>\<close>
          by (metis suffixI trail_false_cls_if_trail_false_suffix)

        show "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma>' = []"
          using bex_trail_false_cls_simp more_invars(3) step_hyps(3) trail_false_cls_mempty by blast
      next
        show "\<And>C. None = Some C \<Longrightarrow> atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by simp
      next
        show "\<And>C. None = Some C \<Longrightarrow> trail_false_cls \<Gamma>' C"
          by  simp
      next
        show "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N"
          using more_invars by argo
      next
        show "\<forall>C|\<in>|\<F>. \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars by argo
      qed
    next
      case step_hyps: (decide_pos A C \<Gamma>' \<F>')

      have
        A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
        A_gt: "\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A" and
        A_lt: "\<forall>y|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
        y \<noteq> A \<longrightarrow> (\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t y) \<longrightarrow> A \<prec>\<^sub>t y"
        using \<open>linorder_trm.is_least_in_fset _ A\<close>
        unfolding atomize_conj linorder_trm.is_least_in_ffilter_iff
        by argo

      have "trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)"
        unfolding \<open>\<Gamma>' = (Pos A, _) # \<Gamma>\<close> by simp

      show ?thesis
        unfolding \<open>s' = (_, _, _)\<close>
      proof (intro ord_res_11_invars.intros ord_res_10_invars.intros allI impI conjI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
          unfolding \<open>\<Gamma>' = (Pos A, None) # \<Gamma>\<close> sorted_wrt.simps
        proof (intro conjI ballI)
          fix Ln :: "'f gliteral \<times> 'f gclause option"
          assume "Ln \<in> set \<Gamma>"

          hence "atm_of (fst Ln) |\<in>| trail_atms \<Gamma>"
            by (simp add: fset_trail_atms)

          thus "atm_of (fst Ln) \<prec>\<^sub>t atm_of (fst (Pos A, None))"
            unfolding prod.sel literal.sel
            using A_gt by metis
        next
          show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
            using \<Gamma>_sorted .
        qed

        show "\<forall>Ln\<in>set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> ord_res.is_strictly_maximal_lit (fst Ln) C"
          unfolding \<open>\<Gamma>' = (_, None) # \<Gamma>\<close>
          using invars by simp

        show "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
          unfolding \<open>trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)\<close> finsert.rep_eq
        proof (intro linorder_trm.is_lower_set_insertI ballI impI)
          show "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            using A_in .
        next
          fix w :: "'f gterm"
          assume "w |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "w \<prec>\<^sub>t A"
          thus "w |\<in>| trail_atms \<Gamma>"
            by (metis A_lt \<Gamma>_lower linorder_trm.dual_order.asym linorder_trm.neq_iff
                linorder_trm.not_in_lower_setI)
        next
          show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
            using \<Gamma>_lower .
        qed

        {
          fix Ln and \<Gamma>''
          assume "\<Gamma>' = Ln # \<Gamma>''"

          have "snd Ln = None"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> step_hyps by auto

          moreover have "\<not> (\<exists>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls ((Pos A, None) # \<Gamma>) C)"
          proof (rule notI , elim bexE)
            fix D :: "'f gclause"
            assume D_in: "D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"

            hence "D = efac C \<or> D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              unfolding \<open>\<F>' = (if ord_res.is_strictly_maximal_lit (Pos A) C then \<F> else finsert C \<F>)\<close>
              by (smt (z3) fimage_iff finsert_iff iefac_def)

            hence "\<not> trail_false_cls \<Gamma>' D"
            proof (elim disjE)
              assume "D = efac C"

              hence "trail_false_cls \<Gamma>' D \<longleftrightarrow> trail_false_cls \<Gamma>' C"
                by (simp add: trail_false_cls_def)

              moreover have "\<not> trail_false_cls \<Gamma>' C"
                using step_hyps unfolding linorder_cls.is_least_in_ffilter_iff by metis

              ultimately show "\<not> trail_false_cls \<Gamma>' D"
                by argo
            next
              assume "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              thus "\<not> trail_false_cls \<Gamma>' D"
                using step_hyps by metis
            qed

            moreover assume "trail_false_cls ((Pos A, None) # \<Gamma>) D"

            ultimately show False
              unfolding \<open>\<Gamma>' = (Pos A, None) # \<Gamma>\<close>
              by contradiction
          qed

          ultimately show "snd Ln \<noteq> None \<longleftrightarrow>
          (\<exists>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
            unfolding \<open>\<Gamma>' = (Pos A, None) # \<Gamma>\<close> by argo

          show "snd Ln \<noteq> None \<Longrightarrow> is_pos (fst Ln)"
            using \<open>snd Ln = None\<close> by argo

          have "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)"
            using step_hyps by argo

          hence "\<forall>x\<in>set \<Gamma>. snd x = None"
            using invars by (metis list.set_cases)

          thus "\<forall>x\<in>set \<Gamma>''. snd x = None"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Pos A, None) # \<Gamma>\<close> by simp

          show "\<And>C. snd Ln = Some C \<Longrightarrow> clause_could_propagate \<Gamma>'' C (fst Ln)"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Pos A, None) # \<Gamma>\<close> by force

          show "\<And>D. snd Ln = Some D \<Longrightarrow> D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Pos A, None) # \<Gamma>\<close> by force
        }

        show "\<And>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<Longrightarrow> snd Ln = None \<Longrightarrow>
        \<not> (\<exists>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"
          using step_hyps
          unfolding bex_trail_false_cls_simp
          by (meson suffixI trail_false_cls_if_trail_false_suffix)

        show "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma>' = []"
          by (meson bex_trail_false_cls_simp step_hyps(3) trail_false_cls_mempty)
      next
        show "\<And>C. None = Some C \<Longrightarrow> atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by simp
      next
        show "\<And>C. None = Some C \<Longrightarrow> trail_false_cls \<Gamma>' C"
          by  simp
      next
        show "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N"
          using more_invars by argo
      next
        have "\<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using step_hyps
          by (metis (no_types, lifting) clause_could_propagate_def
              linorder_cls.is_least_in_ffilter_iff literal.discI(1))

        thus "\<forall>C|\<in>|\<F>'. \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars \<open>\<F>' = (if _ then \<F> else finsert C \<F>)\<close> by simp
      qed
    next
      case step_hyps: (propagate A C \<Gamma>' \<F>')

      have
        A_in: "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and
        A_gt: "\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A" and
        A_lt: "\<forall>y|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
        y \<noteq> A \<longrightarrow> (\<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t y) \<longrightarrow> A \<prec>\<^sub>t y"
        using \<open>linorder_trm.is_least_in_fset _ A\<close>
        unfolding atomize_conj linorder_trm.is_least_in_ffilter_iff
        by argo

      have
        C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        C_prop: "clause_could_propagate \<Gamma> C (Pos A)" and
        C_lt: "\<forall>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        D \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> D (Pos A) \<longrightarrow> C \<prec>\<^sub>c D"
        using \<open>linorder_cls.is_least_in_fset _ C\<close>
        unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

      have "trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)"
        unfolding \<open>\<Gamma>' = (Pos A, _) # \<Gamma>\<close> by simp

      show ?thesis
        unfolding \<open>s' = (_, _, _)\<close>
      proof (intro ord_res_11_invars.intros ord_res_10_invars.intros allI impI conjI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
          unfolding \<open>\<Gamma>' = (Pos A, _) # \<Gamma>\<close> sorted_wrt.simps
        proof (intro conjI ballI)
          fix Ln :: "'f gliteral \<times> 'f gclause option"
          assume "Ln \<in> set \<Gamma>"

          hence "atm_of (fst Ln) |\<in>| trail_atms \<Gamma>"
            by (simp add: fset_trail_atms)

          thus "atm_of (fst Ln) \<prec>\<^sub>t atm_of (fst (Pos A, Some (efac C)))"
            unfolding prod.sel literal.sel
            using A_gt by metis
        next
          show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
            using \<Gamma>_sorted .
        qed

        show "\<forall>Ln\<in>set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> ord_res.is_strictly_maximal_lit (fst Ln) C"
          unfolding \<open>\<Gamma>' = (Pos A, Some (efac C)) # \<Gamma>\<close>
          using invars step_hyps
          by (simp add: clause_could_propagate_def greatest_literal_in_efacI
              linorder_cls.is_least_in_ffilter_iff)

        show "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
          unfolding \<open>trail_atms \<Gamma>' = finsert A (trail_atms \<Gamma>)\<close> finsert.rep_eq
        proof (intro linorder_trm.is_lower_set_insertI ballI impI)
          show "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
            using A_in .
        next
          fix w :: "'f gterm"
          assume "w |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "w \<prec>\<^sub>t A"
          thus "w |\<in>| trail_atms \<Gamma>"
            by (metis A_lt \<Gamma>_lower linorder_trm.dual_order.asym linorder_trm.neq_iff
                linorder_trm.not_in_lower_setI)
        next
          show "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
            using \<Gamma>_lower .
        qed

        {
          fix Ln and \<Gamma>''
          assume "\<Gamma>' = Ln # \<Gamma>''"
          hence "Ln = (Pos A, Some (efac C))" and "\<Gamma>'' = \<Gamma>"
            using \<open>\<Gamma>' = (Pos A, Some (efac C)) # \<Gamma>\<close> by simp_all

          obtain D where D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and D_false: "trail_false_cls \<Gamma>' D"
            using step_hyps by metis

          have "(\<exists>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
          proof (rule bexI)
            show "trail_false_cls \<Gamma>' D"
              using D_false .
          next
            have "\<not> trail_false_lit \<Gamma>' (Pos A)"
              by (metis C_prop map_of_Cons_code(2) map_of_eq_None_iff clause_could_propagate_def
                  step_hyps(6) trail_defined_lit_def trail_false_lit_def uminus_not_id)

            moreover have "Pos A \<in># C"
              using C_prop
              unfolding clause_could_propagate_def linorder_lit.is_maximal_in_mset_iff
              by argo

            ultimately have "\<not> trail_false_cls \<Gamma>' C"
              unfolding trail_false_cls_def by metis

            hence "D \<noteq> C"
              using D_false by metis

            thus "D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              unfolding \<open>\<F>' = (if ord_res.is_strictly_maximal_lit (Pos A) C then \<F> else finsert C \<F>)\<close>
              using D_in iefac_def by auto
          qed

          moreover have "snd Ln \<noteq> None"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> step_hyps by auto

          ultimately show "snd Ln \<noteq> None \<longleftrightarrow>
          (\<exists>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
            by argo

          show "snd Ln \<noteq> None \<Longrightarrow> is_pos (fst Ln)"
            using \<open>Ln = (Pos A, Some (efac C))\<close> by auto

          show "\<forall>x\<in>set \<Gamma>''. snd x = None"
            unfolding \<open>\<Gamma>'' = \<Gamma>\<close>
            using invars by (meson list.set_cases step_hyps)

          have "clause_could_propagate \<Gamma> (efac C) (Pos A)"
            using C_prop clause_could_propagate_efac by metis

          thus "\<And>C. snd Ln = Some C \<Longrightarrow> clause_could_propagate \<Gamma>'' C (fst Ln)"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Pos A, Some (efac C)) # \<Gamma>\<close>
            by force

          have "efac C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          proof (cases "ord_res.is_strictly_maximal_lit (Pos A) C")
            case True
            thus ?thesis
              unfolding \<open>\<F>' = _\<close>
              using C_in
              by (metis (mono_tags, opaque_lifting) literal.discI(1)
                  nex_strictly_maximal_pos_lit_if_neq_efac)
          next
            case False
            then show ?thesis
              unfolding \<open>\<F>' = _\<close>
              using C_in
              by (smt (z3) fimage_iff finsert_iff iefac_def nex_strictly_maximal_pos_lit_if_neq_efac
                  obtains_positive_greatest_lit_if_efac_not_ident)
          qed

          thus "\<And>D. snd Ln = Some D \<Longrightarrow> D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>\<Gamma>' = Ln # \<Gamma>''\<close> \<open>\<Gamma>' = (Pos A, Some (efac C)) # \<Gamma>\<close> by force
        }

        show "\<And>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<Longrightarrow> snd Ln = None \<Longrightarrow>
        \<not> (\<exists>C|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"
          unfolding \<open>\<Gamma>' = (_, Some _) # \<Gamma>\<close>
          using invars
          unfolding bex_trail_false_cls_simp
          by (metis list.inject not_None_eq split_pairs suffix_Cons suffix_def)

        show "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma>' = []"
          by (meson bex_trail_false_cls_simp step_hyps(3) trail_false_cls_mempty)
      next
        show "\<And>C. None = Some C \<Longrightarrow> atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by simp
      next
        show "\<And>C. None = Some C \<Longrightarrow> trail_false_cls \<Gamma>' C"
          by  simp
      next
        show "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N"
          using more_invars by argo
      next
        have "\<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using step_hyps
          by (metis (no_types, lifting) clause_could_propagate_def
              linorder_cls.is_least_in_ffilter_iff literal.discI(1))

        thus "\<forall>C|\<in>|\<F>'. \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars \<open>\<F>' = (if _ then \<F> else finsert C \<F>)\<close> by simp
      qed
    next
      case step_hyps: (conflict D)
      show ?thesis
        unfolding \<open>s' = _\<close>
      proof (intro ord_res_11_invars.intros allI impI)
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
          using more_invars by argo
      next
        show "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma> = []"
          using more_invars by argo
      next
        show "\<And>C. Some D = Some C \<Longrightarrow> atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by (metis atm_of_in_atms_of_clssI atms_of_cls_def fimage_fsubsetI fset_fset_mset
              linorder_cls.is_least_in_ffilter_iff option.inject step_hyps(3))
      next
        show "\<And>C. Some D = Some C \<Longrightarrow> trail_false_cls \<Gamma> C"
          using \<open>linorder_cls.is_least_in_fset _ D\<close>
          unfolding linorder_cls.is_least_in_ffilter_iff
          by  simp
      next
        show "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N"
          using more_invars by argo
      next
        show "\<forall>C|\<in>|\<F>. \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars by argo
      qed
    next
      case step_hyps: (skip L C n \<Gamma>')

      have "\<And>xs. fset (trail_atms xs) = atm_of ` fst ` set xs"
        unfolding fset_trail_atms ..
      also have "\<And>xs. atm_of ` fst ` set xs = set (map (atm_of o fst) xs)"
        by (simp add: image_comp)
      finally have "\<And>xs. fset (trail_atms xs) = set (map (atm_of o fst) xs)" .

      show ?thesis
        unfolding \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)\<close>
      proof (intro ord_res_11_invars.intros ord_res_10_invars.intros ballI allI impI conjI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
          using invars unfolding \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> by simp
      next
        fix Ln :: "'f gliteral \<times> 'f gclause option" and C :: "'f gclause"
        assume "Ln \<in> set \<Gamma>'" and "snd Ln = Some C"
        then show "ord_res.is_strictly_maximal_lit (fst Ln) C"
          using invars unfolding \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> by simp
      next
        show "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
          unfolding \<open>fset (trail_atms \<Gamma>') = set (map (atm_of o fst) \<Gamma>')\<close>
        proof (rule linorder_trm.sorted_and_lower_set_appendD_right(2))
          have "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) (map (atm_of \<circ> fst) \<Gamma>)"
            using \<Gamma>_sorted by (simp add: sorted_wrt_map)

          thus "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) ([atm_of L] @ map (atm_of \<circ> fst) \<Gamma>')"
            unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> by simp
        next
          have "set ([atm_of L] @ map (atm_of \<circ> fst) \<Gamma>') = fset (trail_atms \<Gamma>)"
            unfolding append_Cons append_Nil list.set
            unfolding \<open>fset (trail_atms \<Gamma>') = set (map (atm_of o fst) \<Gamma>')\<close>[symmetric]
            unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> trail_atms.simps prod.sel
            by simp

          thus "linorder_trm.is_lower_set (set ([atm_of L] @ map (atm_of \<circ> fst) \<Gamma>'))
            (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"
            using \<Gamma>_lower
            by (simp only:)
        qed
      next
        fix
          Ln :: "'f gliteral \<times> 'f gclause option" and
          \<Gamma>'' :: "('f gliteral \<times> 'f gclause option) list"
        assume "\<Gamma>' = Ln # \<Gamma>''"

        have "snd Ln = None"
          by (metis \<open>\<Gamma>' = Ln # \<Gamma>''\<close> in_set_conv_decomp invars(4) step_hyps(1) suffixE suffix_Cons)

        show "(snd Ln \<noteq> None) = (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
          using \<open>snd Ln = None\<close>
          by (metis \<open>\<Gamma>' = Ln # \<Gamma>''\<close> invars(5) step_hyps(1) suffixE suffix_Cons)

        show "snd Ln \<noteq> None \<Longrightarrow> is_pos (fst Ln)"
          using \<open>snd Ln = None\<close> by simp

        show "\<And>C. snd Ln = Some C \<Longrightarrow> clause_could_propagate \<Gamma>'' C (fst Ln)"
          using \<open>snd Ln = None\<close> by simp

        show "\<And>C. snd Ln = Some C \<Longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using \<open>snd Ln = None\<close> by simp

        show "\<And>x. x \<in> set \<Gamma>'' \<Longrightarrow> snd x = None"
          by (simp add: \<open>\<Gamma>' = Ln # \<Gamma>''\<close> invars(4) step_hyps(1))
      next
        fix
          Ln :: "'f gliteral \<times> 'f gclause option" and
          \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 :: "('f gliteral \<times> 'f gclause option) list"
        assume "\<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0" and "snd Ln = None"
        thus "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"
          by (metis append_Cons invars(5) step_hyps(1))
      next
        show "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma>' = []"
          using step_hyps(1) more_invars(3) by fastforce
      next
        show "\<And>D. Some C = Some D \<Longrightarrow> atms_of_cls D |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          using more_invars(4) step_hyps(2) by presburger
      next
        show "\<And>D. Some C = Some D \<Longrightarrow> trail_false_cls \<Gamma>' D"
          using more_invars \<open>\<C> = Some C\<close> \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> \<open>- L \<notin># C\<close>
          using subtrail_falseI by auto
      next
        show "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N"
          using more_invars by argo
      next
        show "\<And>C. C |\<in>| \<F> \<Longrightarrow> \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars by metis
      qed
    next
      case step_hyps: (resolution L D \<Gamma>' C)

      have D_max_lit: "ord_res.is_strictly_maximal_lit L D"
        using invars \<open>\<Gamma> = (L, Some D) # \<Gamma>'\<close> by simp

      show ?thesis
        unfolding \<open>s' = _\<close>
      proof (intro ord_res_11_invars.intros allI impI)
        show "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
          using more_invars by argo
      next
        show "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma> = []"
          using more_invars by argo
      next
        have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars \<open>\<Gamma> = (L, Some D) # \<Gamma>'\<close>
          by (metis snd_conv)

        hence "atms_of_cls D |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb funion_upper1)

        moreover have "atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by (smt (verit) add_mset_add_single atms_of_cls_def dual_order.trans fimage_fsubsetI
              fimage_iff fset_fset_mset more_invars(4) step_hyps(1) union_iff)

        ultimately show "\<And>E. Some (remove1_mset (- L) C + remove1_mset L D) = Some E \<Longrightarrow>
          atms_of_cls E |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          by (smt (verit, ccfv_threshold) add_mset_add_single atms_of_cls_def diff_single_trivial
              fimage_iff fset_fset_mset fsubsetI fsubset_funion_eq funionI1 insert_DiffM
              option.inject union_iff)
      next
        fix E :: "'f gclause"
        assume "Some (remove1_mset (- L) C + remove1_mset L D) = Some E"
        
        hence "E = remove1_mset (- L) C + remove1_mset L D"
          by simp

        show "trail_false_cls \<Gamma> E"
          unfolding trail_false_cls_def
        proof (intro ballI)
          fix K :: "'f gliteral"
          assume "K \<in># E"

          hence "K \<in># remove1_mset (- L) C \<or> K \<in># remove1_mset L D"
            unfolding \<open>E = _\<close> by simp

          thus "trail_false_lit \<Gamma> K"
          proof (elim disjE)
            assume "K \<in># remove1_mset (- L) C"

            moreover have "trail_false_cls \<Gamma> C"
              using more_invars \<open>\<C> = Some C\<close> by metis

            ultimately show "trail_false_lit \<Gamma> K"
              unfolding trail_false_cls_def
              by (metis in_diffD)
          next
            assume K_in: "K \<in># remove1_mset L D"

            have "clause_could_propagate \<Gamma>' D L"
              using invars \<open>\<Gamma> = (L, Some D) # \<Gamma>'\<close> by simp

            hence "trail_false_cls \<Gamma>' {#K \<in># D. K \<noteq> L#}"
              by (simp only: clause_could_propagate_def)

            hence "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}"
              unfolding \<open>\<Gamma> = (L, Some D) # \<Gamma>'\<close>
              by (simp add: trail_false_cls_def trail_false_lit_def)

            moreover have "K \<in># {#K \<in># D. K \<noteq> L#}"
              using D_max_lit K_in in_diffD linorder_lit.is_greatest_in_mset_iff by fastforce

            ultimately show "trail_false_lit \<Gamma> K"
              unfolding trail_false_cls_def by metis
          qed
        qed
      next
        show "atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N"
          using more_invars by argo
      next
        show "\<forall>C |\<in>| \<F>. \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars by metis
      qed
    next
      case step_hyps: (backtrack L \<Gamma>' C)

      have "{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
        using more_invars step_hyps(3) by fastforce

      hence "{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        unfolding mempty_in_fimage_iefac .

      hence "\<not>(\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)"
        using invars \<open>\<Gamma> = _ # \<Gamma>'\<close>
        by (metis (no_types, opaque_lifting) split_pairs)

      hence "\<not>(\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
        by (metis append.simps(1) step_hyps(3) suffix_ConsD suffix_def
            trail_false_cls_if_trail_false_suffix)

      moreover have "\<not> trail_false_cls \<Gamma>' C"
        by (metis \<open>trail_consistent \<Gamma>\<close> fst_conv list.distinct(1) list.inject step_hyps(3,4)
            trail_consistent.simps trail_defined_lit_def trail_false_cls_def trail_false_lit_def
            uminus_lit_swap)

      ultimately have "\<not>(\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| finsert C U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
        by (simp add: iefac_def trail_false_cls_def)

      have "\<And>xs. fset (trail_atms xs) = atm_of ` fst ` set xs"
        unfolding fset_trail_atms ..
      also have "\<And>xs. atm_of ` fst ` set xs = set (map (atm_of o fst) xs)"
        by (simp add: image_comp)
      finally have "\<And>xs. fset (trail_atms xs) = set (map (atm_of o fst) xs)" .

      have "atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        using more_invars \<open>\<C> = Some C\<close> by metis

      hence "atms_of_clss (N |\<union>| finsert C U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        by auto

      show ?thesis
        unfolding \<open>s' = (finsert C U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close>
      proof (intro ord_res_11_invars.intros ord_res_10_invars.intros ballI allI impI conjI)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
          using invars unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> by simp
      next
        fix Ln :: "'f gliteral \<times> 'f gclause option" and C :: "'f gclause"
        assume "Ln \<in> set \<Gamma>'" and "snd Ln = Some C"
        then show "ord_res.is_strictly_maximal_lit (fst Ln) C"
          using invars unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> by simp
      next
        show "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| finsert C U\<^sub>e\<^sub>r))"
          unfolding \<open>fset (trail_atms \<Gamma>') = set (map (atm_of o fst) \<Gamma>')\<close>
          unfolding \<open>atms_of_clss (N |\<union>| finsert C U\<^sub>e\<^sub>r) = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        proof (rule linorder_trm.sorted_and_lower_set_appendD_right(2))
          have "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) (map (atm_of \<circ> fst) \<Gamma>)"
            using \<Gamma>_sorted by (simp add: sorted_wrt_map)

          thus "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) ([atm_of L] @ map (atm_of \<circ> fst) \<Gamma>')"
            unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> by simp
        next
          have "set ([atm_of L] @ map (atm_of \<circ> fst) \<Gamma>') = fset (trail_atms \<Gamma>)"
            unfolding append_Cons append_Nil list.set
            unfolding \<open>fset (trail_atms \<Gamma>') = set (map (atm_of o fst) \<Gamma>')\<close>[symmetric]
            unfolding \<open>\<Gamma> = _ # \<Gamma>'\<close> trail_atms.simps prod.sel
            by simp

          thus "linorder_trm.is_lower_set (set ([atm_of L] @ map (atm_of \<circ> fst) \<Gamma>'))
            (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)))"
            using \<Gamma>_lower
            by (simp only:)
        qed
      next
        fix
          Ln :: "'f gliteral \<times> 'f gclause option" and
          \<Gamma>'' :: "('f gliteral \<times> 'f gclause option) list"
        assume "\<Gamma>' = Ln # \<Gamma>''"
        
        have "snd Ln = None"
          by (simp add: \<open>\<Gamma>' = Ln # \<Gamma>''\<close> invars(4) step_hyps(3))

        thus "(snd Ln \<noteq> None) \<longleftrightarrow> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| finsert C U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)"
          using \<open>\<not>(\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| finsert C U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)\<close>
          by argo

        show "snd Ln \<noteq> None \<Longrightarrow> is_pos (fst Ln)"
          using \<open>snd Ln = None\<close> by simp

        show "\<And>C. snd Ln = Some C \<Longrightarrow> clause_could_propagate \<Gamma>'' C (fst Ln)"
          using \<open>snd Ln = None\<close> by simp

        show "\<And>D. snd Ln = Some D \<Longrightarrow> D |\<in>| iefac \<F> |`| (N |\<union>| finsert C U\<^sub>e\<^sub>r)"
          using \<open>snd Ln = None\<close> by simp

        show "\<And>x. x \<in> set \<Gamma>'' \<Longrightarrow> snd x = None"
          by (simp add: \<open>\<Gamma>' = Ln # \<Gamma>''\<close> invars(4) step_hyps(3))
      next
        fix
          Ln :: "'f gliteral \<times> 'f gclause option" and
          \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 :: "('f gliteral \<times> 'f gclause option) list"
        assume "\<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0" and "snd Ln = None"
        thus "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| finsert C U\<^sub>e\<^sub>r). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"
          using \<open>\<not>(\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| finsert C U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C)\<close>
          by (metis suffixI trail_false_cls_if_trail_false_suffix)
      next
        have "C \<noteq> {#}"
          using \<open>- L \<in># C\<close> by force

        hence "{#} |\<notin>| N |\<union>| finsert C U\<^sub>e\<^sub>r"
          using \<open>{#} |\<notin>| N |\<union>| U\<^sub>e\<^sub>r\<close> by simp

        thus "{#} |\<in>| N |\<union>| finsert C U\<^sub>e\<^sub>r \<Longrightarrow> \<Gamma>' = []"
          by contradiction
      next
        show "\<And>D. None = Some D \<Longrightarrow> atms_of_cls D |\<subseteq>| atms_of_clss (N |\<union>| finsert C U\<^sub>e\<^sub>r)"
          by simp
      next
        show "\<And>C. None = Some C \<Longrightarrow> trail_false_cls \<Gamma>' C"
          by simp
      next
        have "atms_of_cls C |\<subseteq>| atms_of_clss N"
          by (smt (verit, ccfv_threshold) \<open>atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
              atms_of_clss_def fin_mono fmember_ffUnion_iff fsubsetI funion_iff more_invars(6))

        thus "atms_of_clss (finsert C U\<^sub>e\<^sub>r) |\<subseteq>| atms_of_clss N"
          using \<open>atms_of_clss U\<^sub>e\<^sub>r |\<subseteq>| atms_of_clss N\<close> by simp
      next
        show "\<And>C. C |\<in>| \<F> \<Longrightarrow> \<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
          using more_invars by metis
      qed
    qed
  qed
qed

lemma rtranclp_ord_res_11_preserves_invars:
  assumes
    step: "(ord_res_11 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_11_invars N s"
  shows "ord_res_11_invars N s'"
  using step invars ord_res_11_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

lemma tranclp_ord_res_11_preserves_invars:
  assumes
    step: "(ord_res_11 N)\<^sup>+\<^sup>+ s s'" and
    invars: "ord_res_11_invars N s"
  shows "ord_res_11_invars N s'"
  using step invars ord_res_11_preserves_invars
  by (smt (verit, del_insts) tranclp_induct)

lemma ex_ord_res_11_if_not_final:
  assumes
    not_final: "\<not> ord_res_11_final (N, s)" and
    invars: "ord_res_11_invars N s"
  shows "\<exists>s'. ord_res_11 N s s'"
  using invars
proof (cases N s rule: ord_res_11_invars.cases)
  case more_invars: (1 U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>)
  show ?thesis
    using \<open>ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" rule: ord_res_10_invars.cases)
    case invars: 1

    show ?thesis
    proof (cases \<C>)
      case None
      show ?thesis
      proof (cases "\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C")
        case True

        then obtain C where
          "linorder_cls.is_least_in_fset (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
          using linorder_cls.ex_is_least_in_ffilter_iff by metis

        thus ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = None\<close>
          using ord_res_11.conflict by metis
      next
        case no_false_cls: False

        hence "\<exists>A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2"
          using not_final
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = None\<close>
          by (smt (verit) invars(3) linorder_trm.antisym_conv3 linorder_trm.not_in_lower_setI
              ord_res_11_final.model_found)

        then obtain A where
          A_least: "linorder_trm.is_least_in_fset
            {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
          using linorder_trm.ex_is_least_in_ffilter_iff by presburger

        show ?thesis
        proof (cases "\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)")
          case True

          then obtain C where
            C_least: "linorder_cls.is_least_in_fset
              {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} C"
            using linorder_cls.ex_is_least_in_ffilter_iff by presburger

          show ?thesis
          proof (cases "\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls ((Pos A, None) # \<Gamma>) C")
            case True

            moreover have "trail_false_cls ((Pos A, None) # \<Gamma>) =
              trail_false_cls ((Pos A, Some (efac C)) # \<Gamma>)"
              unfolding trail_false_cls_def trail_false_lit_def by simp

            ultimately show ?thesis
              unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = None\<close>
              using ord_res_11.propagate[OF no_false_cls A_least C_least]
              by metis
          next
            case False
            thus ?thesis
              unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = None\<close>
              using ord_res_11.decide_pos[OF no_false_cls A_least C_least]
              by metis
          qed
        next
          case False
          thus ?thesis
            unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = None\<close>
            using ord_res_11.decide_neg[OF no_false_cls A_least] by metis
        qed
      qed
    next
      case (Some D)

      hence D_false: "trail_false_cls \<Gamma> D"
        using more_invars by metis

      show ?thesis
      proof (cases "D = {#}")
        case True

        hence "\<Gamma> \<noteq> []"
          using not_final
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some D\<close>
          unfolding ord_res_11_final.simps by metis

        then obtain L n \<Gamma>' where "\<Gamma> = (L, n) # \<Gamma>'"
          by (metis list.exhaust prod.exhaust)

        moreover have "- L \<notin># D"
          unfolding \<open>D = {#}\<close> by simp

        ultimately show ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<C> = Some D\<close>
          using ord_res_11.skip by metis
      next
        case False

        then obtain L n \<Gamma>' where "\<Gamma> = (L, n) # \<Gamma>'"
          using D_false[unfolded trail_false_cls_def trail_false_lit_def]
          by (metis eq_fst_iff image_iff list.set_cases multiset_nonemptyE)

        show ?thesis
        proof (cases "- L \<in># D")
          case True
          show ?thesis
          proof (cases n)
            case None
            show ?thesis
            proof (cases "- L \<in># D")
              case True
              thus ?thesis
                unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> \<open>n = None\<close> \<open>\<C> = Some D\<close>
                using ord_res_11.backtrack by metis
            next
              case False
              thus ?thesis
                using ord_res_11.skip
                unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> \<open>n = None\<close> \<open>\<C> = Some D\<close> by metis
            qed
          next
            case (Some C)
            thus ?thesis
              unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> \<open>n = Some C\<close> \<open>\<C> = Some D\<close>
              using ord_res_11.resolution[OF _ \<open>- L \<in># D\<close>] by metis
          qed
        next
          case False
          thus ?thesis
            using ord_res_11.skip
            unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close> \<open>\<Gamma> = (L, n) # \<Gamma>'\<close> \<open>\<C> = Some D\<close> by metis
        qed
      qed
    qed
  qed
qed

lemma ord_res_11_safe_state_if_invars:
  fixes N s
  assumes invars: "ord_res_11_invars N s"
  shows "safe_state (constant_context ord_res_11) ord_res_11_final (N, s)"
  using safe_state_constant_context_if_invars[where
      \<R> = ord_res_11 and \<F> = ord_res_11_final and \<I> = ord_res_11_invars]
  using ord_res_11_preserves_invars ex_ord_res_11_if_not_final invars by metis

lemma rtrancl_ord_res_11_all_resolution_steps:
  assumes C_max_lit: "ord_res.is_strictly_maximal_lit K C"
  shows "(ord_res_11 N)\<^sup>*\<^sup>* (U, \<F>, (K, Some C) # \<Gamma>, Some D) (U, \<F>, (K, Some C) # \<Gamma>, Some (eres C D))"
proof -
  obtain CD where "eres C D = CD" and run: "full_run (ground_resolution C) D CD"
    using ex1_eres_eq_full_run_ground_resolution by metis

  have "(ord_res_11 N)\<^sup>*\<^sup>* (U, \<F>, (K, Some C) # \<Gamma>, Some D) (U, \<F>, (K, Some C) # \<Gamma>, Some CD)"
  proof (rule full_run_preserves_invariant[OF run])
    show "(ord_res_11 N)\<^sup>*\<^sup>* (U, \<F>, (K, Some C) # \<Gamma>, Some D) (U, \<F>, (K, Some C) # \<Gamma>, Some D)"
      by simp
  next
    fix x y
    assume "ground_resolution C x y"

    hence "ord_res_11 N (U, \<F>, (K, Some C) # \<Gamma>, Some x) (U, \<F>, (K, Some C) # \<Gamma>, Some y)"
      unfolding ground_resolution_def
    proof (cases x C y rule: ord_res.ground_resolution.cases)
      case res_hyps: (ground_resolutionI A P\<^sub>1' P\<^sub>2')

      have "K = - Neg A"
        using C_max_lit
        by (metis ord_res.Uniq_striclty_maximal_lit_in_ground_cls res_hyps(6) the1_equality'
            uminus_Neg)

      hence "- K \<in># x"
        by (simp add: \<open>x = add_mset (Neg A) P\<^sub>1'\<close>)

      moreover have "y = remove1_mset (- K) x + remove1_mset K C"
        using res_hyps \<open>K = - Neg A\<close> by force 

      ultimately show ?thesis
        using ord_res_11.resolution[OF refl, of K x N U \<F> C \<Gamma>]
        by metis
    qed

    moreover assume "(ord_res_11 N)\<^sup>*\<^sup>*
      (U, \<F>, (K, Some C) # \<Gamma>, Some D)
      (U, \<F>, (K, Some C) # \<Gamma>, Some x)"

    ultimately show "(ord_res_11 N)\<^sup>*\<^sup>*
      (U, \<F>, (K, Some C) # \<Gamma>, Some D)
      (U, \<F>, (K, Some C) # \<Gamma>, Some y)"
      by simp
  qed

  then show ?thesis
    unfolding \<open>eres C D = CD\<close>
    by argo
qed

lemma rtrancl_ord_res_11_all_skip_steps:
  "(ord_res_11 N)\<^sup>*\<^sup>* (U, \<F>, \<Gamma>, Some C) (U, \<F>, dropWhile (\<lambda>Ln. - fst Ln \<notin># C) \<Gamma>, Some C)"
proof (induction \<Gamma>)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "- fst Ln \<in># C")
    case True
    hence "dropWhile (\<lambda>Ln. - fst Ln \<notin># C) (Ln # \<Gamma>) = Ln # \<Gamma>"
      by simp
    thus ?thesis
      by simp
  next
    case False
    hence *: "dropWhile (\<lambda>Ln. - fst Ln \<notin># C) (Ln # \<Gamma>) = dropWhile (\<lambda>Ln. - fst Ln \<notin># C) \<Gamma>"
      by simp

    obtain L \<C> where "Ln = (L, \<C>)"
      by (metis prod.exhaust)

    have "ord_res_11 N (U, \<F>, Ln # \<Gamma>, Some C) (U, \<F>, \<Gamma>, Some C)"
      unfolding \<open>Ln = (L, \<C>)\<close>
    proof (rule ord_res_11.skip)
      show "- L \<notin># C"
        using False unfolding \<open>Ln = (L, \<C>)\<close> by simp
    qed

    thus ?thesis
      unfolding *
      using Cons.IH
      by simp
  qed
qed

end

end