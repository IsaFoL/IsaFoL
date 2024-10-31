theory ORD_RES_10
  imports ORD_RES_8
begin

section \<open>ORD-RES-10 (propagate iff a conflict is produced)\<close>


type_synonym 'f ord_res_10_state =
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gliteral \<times> 'f gclause option) list"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_10 where
  decide_neg: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    ord_res_10 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')" |

  decide_pos: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<Gamma>' = (Pos A, None) # \<Gamma> \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C) \<Longrightarrow>
    \<F>' = (if linorder_lit.is_greatest_in_mset C (Pos A) then \<F> else finsert C \<F>) \<Longrightarrow>
    ord_res_10 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>')" |

  propagate: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<Gamma>' = (Pos A, Some (efac C)) # \<Gamma> \<Longrightarrow>
    (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' C) \<Longrightarrow>
    \<F>' = (if linorder_lit.is_greatest_in_mset C (Pos A) then \<F> else finsert C \<F>) \<Longrightarrow>
    ord_res_10 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>')" |

  resolution: "
    linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> D|} D \<Longrightarrow>
    linorder_lit.is_maximal_in_mset D (Neg A) \<Longrightarrow>
    map_of \<Gamma> (Pos A) = Some (Some C) \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r \<Longrightarrow>
    \<Gamma>' = dropWhile (\<lambda>Ln. \<forall>K.
      linorder_lit.is_maximal_in_mset (eres C D) K \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma> \<Longrightarrow>
    ord_res_10 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')"

lemma right_unique_ord_res_10:
  fixes N :: "'f gclause fset"
  shows "right_unique (ord_res_10 N)"
proof (rule right_uniqueI)
  fix x y z
  assume step1: "ord_res_10 N x y" and step2: "ord_res_10 N x z"
  show "y = z"
    using step1
  proof (cases N x y rule: ord_res_10.cases)
    case hyps1: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A1 \<Gamma>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_10.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 show ?thesis
        by (metis (no_types, lifting) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_ffilter_iff)
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
      case (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      with hyps1 have False
        by (metis (no_types, opaque_lifting) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (decide_pos \<F> U\<^sub>e\<^sub>r \<Gamma> A1 C1 \<Gamma>1' \<F>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_10.cases)
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
        using hyps1 hyps2
        by (metis (no_types, lifting) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_ffilter_iff)
      hence "trail_false_cls \<Gamma>1' = trail_false_cls \<Gamma>'"
        using hyps1 hyps2
        unfolding trail_false_cls_def trail_false_lit_def
        by simp
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    next
      case (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      with hyps1 have False
        by (meson linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A1 C1 \<Gamma>1' \<F>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_10.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff
            linorder_trm.dual_order.asym linorder_trm.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case hyps2: (decide_pos A C \<Gamma>' \<F>')
      have "A1 = A"
        using hyps1 hyps2
        by (metis (no_types, lifting) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_ffilter_iff)
      hence "trail_false_cls \<Gamma>1' = trail_false_cls \<Gamma>'"
        using hyps1 hyps2
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
      case (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      with hyps1 have False
        by (meson linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D1 A1 C1 U\<^sub>e\<^sub>r1' \<Gamma>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_10.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (meson linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (decide_pos A C \<Gamma>' \<F>')
      with hyps1 have False
        by (meson linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 have False
        by (meson linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case hyps2: (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      have "D1 = D"
        using hyps1 hyps2
        by (metis (no_types, opaque_lifting) linorder_cls.Uniq_is_least_in_fset Uniq_D)
      have "A1 = A"
        using hyps1 hyps2
        unfolding \<open>D1 = D\<close>
        by (metis (mono_tags, opaque_lifting) Uniq_D linorder_lit.Uniq_is_maximal_in_mset
            literal.sel(2))
      have "C1 = C"
        using hyps1 hyps2
        unfolding \<open>A1 = A\<close>
        by simp
      show ?thesis
        using hyps1 hyps2
        unfolding \<open>D1 = D\<close> \<open>A1 = A\<close> \<open>C1 = C\<close>
        by argo
    qed
  qed
qed

sublocale ord_res_10_semantics: semantics where
  step = "constant_context ord_res_10" and
  final = ord_res_8_final
proof unfold_locales
  fix S :: "'f ord_res_10_state"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gclause fset" and
    \<Gamma> :: "('f gliteral \<times> 'f gclause option) list" where
    S_def: "S = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
    by (metis prod.exhaust)

  assume "ord_res_8_final S"

  hence "\<nexists>x. ord_res_10 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) x"
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
      unfolding ord_res_10.simps by blast
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
      unfolding ord_res_10.simps by blast
  qed

  thus "finished (constant_context ord_res_10) S"
    by (simp add: S_def finished_def constant_context.simps)
qed

inductive ord_res_10_invars for N where
  "ord_res_10_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" if
    "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>" and
    "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)" and
    "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    "\<forall>Ln \<Gamma>'. \<Gamma> = Ln # \<Gamma>' \<longrightarrow>
        (snd Ln \<noteq> None \<longleftrightarrow> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)) \<and>
        (snd Ln \<noteq> None \<longrightarrow> is_pos (fst Ln)) \<and>
        (\<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
        (\<forall>C. snd Ln = Some C \<longrightarrow> clause_could_propagate \<Gamma>' C (fst Ln)) \<and>
        (\<forall>x \<in> set \<Gamma>'. snd x = None)" and
    "\<forall>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<longrightarrow>
        snd Ln = None \<longrightarrow> \<not>(\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"

lemma ord_res_10_preserves_invars:
  assumes
    step: "ord_res_10 N s s'" and
    invars: "ord_res_10_invars N s"
  shows "ord_res_10_invars N s'"
  using invars
proof (cases N s rule: ord_res_10_invars.cases)
  case invars: (1 \<Gamma> U\<^sub>e\<^sub>r \<F>)

  note \<Gamma>_sorted = \<open>sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>\<close>
  note \<Gamma>_lower = \<open>linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))\<close>
  
  have "trail_consistent \<Gamma>"
    using \<Gamma>_sorted trail_consistent_if_sorted_wrt_atoms by metis

  show ?thesis
    using step unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" s' rule: ord_res_10.cases)
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
    proof (intro ord_res_10_invars.intros allI impI conjI)
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
    proof (intro ord_res_10_invars.intros allI impI conjI)
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
    proof (intro ord_res_10_invars.intros allI impI conjI)
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
          have "\<not> trail_false_cls \<Gamma>' C"
            by (metis clause_could_propagate_def linorder_cls.is_least_in_ffilter_iff
                linorder_lit.is_maximal_in_mset_iff ord_res.less_lit_simps(2) reflclp_iff
                step_hyps(2,4,5) subtrail_falseI uminus_Pos uminus_not_id')

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
          using invars by (meson list.set_cases step_hyps(2))

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
    qed
  next
    case step_hyps: (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')

    note D_max_lit = \<open>ord_res.is_maximal_lit (Neg A) D\<close>
    have C_max_lit: \<open>ord_res.is_strictly_maximal_lit (Pos A) C\<close>
      using invars by (metis map_of_SomeD split_pairs step_hyps(4))

    have
      D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      D_false: "trail_false_cls \<Gamma> D" and
      D_lt: "\<forall>E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). E \<noteq> D \<longrightarrow> trail_false_cls \<Gamma> E \<longrightarrow> D \<prec>\<^sub>c E"
      using \<open>linorder_cls.is_least_in_fset _ D\<close>
      unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

    have "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using D_in D_max_lit
      by (metis atm_of_in_atms_of_clssI linorder_lit.is_maximal_in_mset_iff literal.sel(2))

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

    obtain \<Gamma>\<^sub>b where "\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b"
      using \<open>map_of \<Gamma> (Pos A) = Some (Some C)\<close> invars
      by (metis list.set_cases map_of_SomeD not_Some_eq snd_conv)

    have "A |\<in>| trail_atms \<Gamma>"
      unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close> trail_atms_def by simp

    moreover have "A |\<notin>| trail_atms \<Gamma>'"
    proof (cases "eres C D = {#}")
      case True

      hence "\<nexists>K. ord_res.is_maximal_lit K (eres C D)"
        unfolding linorder_lit.is_maximal_in_mset_iff by simp

      hence "\<Gamma>' = dropWhile (\<lambda>Ln. True) \<Gamma>"
        using step_hyps(6) by simp

      also have "\<dots> = []"
        by simp

      finally show ?thesis
        using \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close> by simp
    next
      case False

      then obtain K where eres_max_lit: "ord_res.is_maximal_lit K (eres C D)"
        using linorder_lit.ex_maximal_in_mset by presburger

      have "atm_of K \<prec>\<^sub>t atm_of (Neg A)"
      proof (rule lit_in_eres_lt_greatest_lit_in_grestest_resolvant [of C D])
        show "eres C D \<noteq> D"
          using \<open>eres C D \<noteq> D\<close> .
      next
        show "ord_res.is_maximal_lit (Neg A) D"
          using D_max_lit .
      next
        show "- Neg A \<notin># D"
          using D_false \<open>trail_consistent \<Gamma>\<close>
          by (meson D_max_lit linorder_lit.is_maximal_in_mset_iff
              not_both_lit_and_comp_lit_in_false_clause_if_trail_consistent)
      next
        show "K \<in># eres C D"
          using eres_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by argo
      qed

      hence "atm_of K \<prec>\<^sub>t A"
        unfolding literal.sel .

      hence "atm_of K \<preceq>\<^sub>t A"
        by order

      have "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"
        using step_hyps(6) eres_max_lit
        by (smt (verit, ccfv_threshold) Uniq_D dropWhile_cong linorder_lit.Uniq_is_maximal_in_mset)

      also have "\<dots> = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>b"
        unfolding \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close>
        unfolding dropWhile.simps prod.sel literal.sel
        using \<open>atm_of K \<preceq>\<^sub>t A\<close> by simp

      finally have "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<^sub>b" .

      hence "trail_atms \<Gamma>' |\<subseteq>| trail_atms \<Gamma>\<^sub>b"
        by (simp only: suffix_dropWhile trail_atms_subset_if_suffix)

      moreover have "A |\<notin>| trail_atms \<Gamma>\<^sub>b"
      proof (rule notI)
        assume "A |\<in>| trail_atms \<Gamma>\<^sub>b"
        then obtain Ln where "Ln \<in> set \<Gamma>\<^sub>b" and "atm_of (fst Ln) = A"
          unfolding fset_trail_atms by blast
        moreover have "\<forall>y\<in>set \<Gamma>\<^sub>b. atm_of (fst y) \<prec>\<^sub>t A"
          using \<Gamma>_sorted[unfolded \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close>] by simp
        ultimately have "A \<prec>\<^sub>t A"
          by metis
        thus False
          by order
      qed

      moreover have "trail_atms \<Gamma>\<^sub>b |\<subseteq>| trail_atms \<Gamma>"
      proof (rule trail_atms_subset_if_suffix)
        show "suffix \<Gamma>\<^sub>b \<Gamma>"
          by (simp only: \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close> suffix_ConsI)
      qed

      ultimately show ?thesis
        by fast
    qed

    ultimately have "\<Gamma>' \<noteq> \<Gamma>"
      by metis

    have C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars
      by (meson \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close> snd_conv)

    define P :: "'f gliteral \<times> 'f gclause option \<Rightarrow> bool" where
      "P \<equiv> \<lambda>Ln. \<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"

    have "\<Gamma> = takeWhile P \<Gamma> @ \<Gamma>'"
      unfolding takeWhile_dropWhile_id
      unfolding P_def \<open>\<Gamma>' = dropWhile _ \<Gamma>\<close> by simp

    hence "suffix \<Gamma>' \<Gamma>"
      unfolding suffix_def by metis

    show ?thesis
      unfolding \<open>s' = (_, _, _)\<close>
    proof (intro ord_res_10_invars.intros allI impI conjI)
      show \<Gamma>'_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
        by (metis (no_types, lifting) \<Gamma>_sorted \<open>suffix \<Gamma>' \<Gamma>\<close> sorted_wrt_append suffix_def)

      show "\<forall>Ln\<in>set \<Gamma>'. \<forall>C. snd Ln = Some C \<longrightarrow> ord_res.is_strictly_maximal_lit (fst Ln) C"
        using \<open>suffix \<Gamma>' \<Gamma>\<close> invars(3) set_mono_suffix by blast

      have "\<And>xs. fset (trail_atms xs) = atm_of ` fst ` set xs"
        unfolding fset_trail_atms ..
      also have "\<And>xs. atm_of ` fst ` set xs = set (map (atm_of o fst) xs)"
        by (simp add: image_comp)
      finally have "\<And>xs. fset (trail_atms xs) = set (map (atm_of o fst) xs)" .

      have "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_cls (eres C D) |\<union>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
        unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r\<close> by simp

      also have "\<dots> = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      proof -
        have "atms_of_cls (eres C D) |\<subseteq>| atms_of_cls C |\<union>| atms_of_cls D"
          by (smt (verit, best) atms_of_cls_def fimage_iff fset_fset_mset fsubsetI funionCI
              lit_in_one_of_resolvents_if_in_eres)

        moreover have "atms_of_cls C |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          using C_in
          by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb fsubset_funion_eq)

        moreover have "atms_of_cls D |\<subseteq>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
          using D_in
          by (metis atms_of_clss_fimage_iefac atms_of_clss_finsert finsert_absorb fsubset_funion_eq)

        ultimately show ?thesis
          by blast
      qed

      finally have "atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" .

      show \<Gamma>'_lower: "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r'))"
        unfolding \<open>fset (trail_atms \<Gamma>') = set (map (atm_of o fst) \<Gamma>')\<close>
      proof (rule linorder_trm.sorted_and_lower_set_appendD_right(2))
        have "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) (map (atm_of \<circ> fst) \<Gamma>)"
          using \<Gamma>_sorted by (simp add: sorted_wrt_map)

        thus "sorted_wrt (\<lambda>x y. y \<prec>\<^sub>t x) (map (atm_of \<circ> fst) (takeWhile P \<Gamma>) @ map (atm_of \<circ> fst) \<Gamma>')"
          using \<open>\<Gamma> = takeWhile P \<Gamma> @ \<Gamma>'\<close>
          by (metis map_append)
      next
        show "linorder_trm.is_lower_set
          (set (map (atm_of \<circ> fst) (takeWhile P \<Gamma>) @ map (atm_of \<circ> fst) \<Gamma>'))
          (fset (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')))"
          unfolding map_append[symmetric]
          unfolding \<open>\<Gamma> = takeWhile P \<Gamma> @ \<Gamma>'\<close>[symmetric]
          using \<Gamma>_lower
          unfolding \<open>fset (trail_atms \<Gamma>) = set (map (atm_of o fst) \<Gamma>)\<close>
          unfolding \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
          .
      qed

      have no_false_cls_in_\<Gamma>': "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). trail_false_cls \<Gamma>' C)"
        if eres_max_lit: "ord_res.is_maximal_lit K (eres C D)"
        for K
      proof -
        have FOO: "\<And>Ln.
          (\<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<longleftrightarrow>
          atm_of K \<preceq>\<^sub>t atm_of (fst Ln)"
          using eres_max_lit
          by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

        have "\<forall>x \<in> set \<Gamma>'. atm_of (fst x) \<prec>\<^sub>t atm_of K"
          using \<open>\<Gamma>' = dropWhile _ \<Gamma>\<close>[unfolded FOO] \<Gamma>_sorted
          by (metis linorder_trm.not_le mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone
              mono_atms_lt)

        hence "\<forall>x \<in> set \<Gamma>'. atm_of (fst x) \<noteq> atm_of K"
          by fastforce

        hence "atm_of K |\<notin>| trail_atms \<Gamma>'"
          unfolding fset_trail_atms by auto

        hence "\<not> trail_defined_lit \<Gamma>' K"
          unfolding trail_defined_lit_iff_trail_defined_atm .

        hence "\<not> trail_false_lit \<Gamma>' K"
          by (metis trail_defined_lit_iff_true_or_false)

        hence "\<not> trail_false_cls \<Gamma>' (eres C D)"
          using eres_max_lit
          unfolding linorder_lit.is_maximal_in_mset_iff trail_false_cls_def
          by metis

        show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). trail_false_cls \<Gamma>' C)"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r\<close>
        proof (rule notI , elim bexE)
          fix E :: "'f gclause"
          assume
            E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| finsert (eres C D) U\<^sub>e\<^sub>r)" and
            E_false: "trail_false_cls \<Gamma>' E"

          have "E = iefac \<F> (eres C D) \<or> E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using E_in by simp

          thus False
          proof (elim disjE)
            assume "E = iefac \<F> (eres C D)"

            hence "trail_false_cls \<Gamma>' (eres C D)"
              using E_false
              by (simp add: iefac_def trail_false_cls_def)

            thus False
              using \<open>\<not> trail_false_cls \<Gamma>' (eres C D)\<close> by contradiction
          next
            assume "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"

            moreover have "trail_false_cls \<Gamma> E"
              using E_false \<open>suffix \<Gamma>' \<Gamma>\<close> by (metis trail_false_cls_if_trail_false_suffix)

            ultimately have "D \<preceq>\<^sub>c E"
              using D_lt E_false by fast

            then obtain L where "L \<in># E" and "Neg A \<preceq>\<^sub>l L"
              using D_max_lit
              by (metis empty_iff linorder_cls.leD linorder_lit.is_maximal_in_mset_iff
                  linorder_lit.leI ord_res.multp_if_all_left_smaller set_mset_empty)

            hence "A \<preceq>\<^sub>t atm_of L"
              by (cases L) simp_all

            moreover have "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r')"
              using \<open>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
              using \<open>atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close>
              by (simp only:)

            ultimately have "atm_of L |\<notin>| trail_atms \<Gamma>'"
              using linorder_trm.not_in_lower_setI[OF \<Gamma>'_lower] \<open>A |\<notin>| trail_atms \<Gamma>'\<close> by blast

            hence "\<not> trail_defined_lit \<Gamma>' L"
              unfolding trail_defined_lit_iff_trail_defined_atm .

            hence "\<not> trail_false_lit \<Gamma>' L"
              by (metis trail_defined_lit_iff_true_or_false)

            moreover have "trail_false_lit \<Gamma>' L"
              using E_false \<open>L \<in># E\<close> unfolding trail_false_cls_def by metis

            ultimately show False
              by contradiction
          qed
        qed
      qed

      have ex_max_lit_in_eres_if: "\<exists>K. ord_res.is_maximal_lit K (eres C D)"
        if "\<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0" for Ln and \<Gamma>\<^sub>1 \<Gamma>\<^sub>0
      proof -
        have "\<exists>x xs. \<Gamma>' = x # xs"
          using that neq_Nil_conv by blast

        hence "\<exists>x. \<not> (\<forall>K. ord_res.is_maximal_lit K (eres C D) \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst x))"
          unfolding step_hyps(6) dropWhile_eq_Cons_conv by auto

        thus ?thesis
          by metis
      qed

      {
        fix Ln and \<Gamma>''
        assume "\<Gamma>' = Ln # \<Gamma>''"

        then obtain K where
          eres_max_lit: "ord_res.is_maximal_lit K (eres C D)"
          using ex_max_lit_in_eres_if[of "[]", simplified] by metis


        have "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). trail_false_cls \<Gamma>' C)"
          using no_false_cls_in_\<Gamma>' eres_max_lit by metis

        moreover have "snd Ln = None"
          using invars \<open>\<Gamma>' \<noteq> \<Gamma>\<close> \<open>suffix \<Gamma>' \<Gamma>\<close>
          by (metis \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close> \<open>\<Gamma>' = Ln # \<Gamma>''\<close> in_set_conv_decomp suffix_Cons
              suffix_def)

        ultimately show "snd Ln \<noteq> None \<longleftrightarrow> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). trail_false_cls \<Gamma>' C)"
          by argo

        show "snd Ln \<noteq> None \<Longrightarrow> is_pos (fst Ln)"
          using \<open>snd Ln = None\<close> by argo

        show "\<forall>x\<in>set \<Gamma>''. snd x = None"
          using invars \<open>\<Gamma>' \<noteq> \<Gamma>\<close> \<open>suffix \<Gamma>' \<Gamma>\<close>
          by (metis \<open>\<Gamma> = (Pos A, Some C) # \<Gamma>\<^sub>b\<close> \<open>\<Gamma>' = Ln # \<Gamma>''\<close> set_mono_suffix subsetD suffix_ConsD2)


        show "\<And>C. snd Ln = Some C \<Longrightarrow> clause_could_propagate \<Gamma>'' C (fst Ln)"
          by (simp add: \<open>snd Ln = None\<close>)

        show "\<And>E. snd Ln = Some E \<Longrightarrow> E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
          by (simp add: \<open>snd Ln = None\<close>)
      }

      show "\<And>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma>' = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<Longrightarrow> snd Ln = None \<Longrightarrow>
        \<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). trail_false_cls (Ln # \<Gamma>\<^sub>0) C)"
        using ex_max_lit_in_eres_if no_false_cls_in_\<Gamma>'
        by (metis suffixI trail_false_cls_if_trail_false_suffix)
    qed
  qed
qed

lemma rtranclp_ord_res_10_preserves_invars:
  assumes
    step: "(ord_res_10 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_10_invars N s"
  shows "ord_res_10_invars N s'"
  using step invars ord_res_10_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

lemma ex_ord_res_10_if_not_final:
  assumes
    not_final: "\<not> ord_res_8_final (N, s)" and
    invars: "ord_res_10_invars N s"
  shows "\<exists>s'. ord_res_10 N s s'"
  using invars
proof (cases N s rule: ord_res_10_invars.cases)
  case invars': (1 \<Gamma> U\<^sub>e\<^sub>r \<F>)
  
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

    show "\<exists>s'. ord_res_10 N s s'"
    proof (cases "\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)")
      case True
      hence "{|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} \<noteq> {||}"
        by force

      then obtain C where
        C_least: "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} C"
        using linorder_cls.ex1_least_in_fset by meson

      show ?thesis
      proof (cases "\<exists>D|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls ((Pos A, Some (efac C)) # \<Gamma>) D")
        case True
        then show ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
          using ord_res_10.propagate[OF no_conflict A_least C_least]
          by metis
      next
        case False
        hence "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls ((Pos A, None) # \<Gamma>) C)"
          by (simp add: trail_false_cls_def trail_false_lit_def)
        then show ?thesis
          unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
          using ord_res_10.decide_pos[OF no_conflict A_least C_least]
          by metis
      qed
    next
      case False
      thus ?thesis
        unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
        using ord_res_10.decide_neg[OF no_conflict A_least]
        by metis
    qed
  next
    assume "\<exists>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> x"

    then obtain D :: "'f gclause" where
      D_least: "linorder_cls.is_least_in_fset
        (ffilter (trail_false_cls \<Gamma>) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      by (metis femptyE ffmember_filter linorder_cls.ex_least_in_fset)

    hence D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and D_false: "trail_false_cls \<Gamma> D"
      unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

    have "D \<noteq> {#}"
      using D_in \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis

    hence "\<Gamma> \<noteq> []"
      using D_false
      by (auto simp add: trail_false_cls_def trail_false_lit_def)

    then obtain Ln \<Gamma>' where "\<Gamma> = Ln # \<Gamma>'"
      using neq_Nil_conv by metis

    hence "snd Ln \<noteq> None"
      using invars' \<open>\<exists>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> x\<close> by presburger

    have "\<forall>x\<in>set \<Gamma>'. snd x = None"
      using invars' \<open>\<Gamma> = Ln # \<Gamma>'\<close> by metis

    have "\<not>(\<exists>x|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma>' x)"
    proof (cases \<Gamma>')
      case Nil
      thus ?thesis
        using \<open>{#} |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
        by (simp add: trail_false_cls_def trail_false_lit_def)
    next
      case (Cons x xs)
      hence "snd x = None"
        using \<open>\<forall>x\<in>set \<Gamma>'. snd x = None\<close> by simp
      then show ?thesis
        using \<open>\<forall>\<Gamma>\<^sub>1 Ln \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ Ln # \<Gamma>\<^sub>0 \<longrightarrow> snd Ln = None \<longrightarrow>
          \<not> (\<exists>C |\<in>| _. trail_false_cls (Ln # \<Gamma>\<^sub>0) C)\<close>[rule_format, of "[Ln]" x xs, simplified]
        using Cons \<open>\<Gamma> = Ln # \<Gamma>'\<close> by blast
    qed

    hence "\<not> trail_false_cls \<Gamma>' D"
      using D_in by metis

    hence "- fst Ln \<in># D"
      using D_false \<open>\<Gamma> = Ln # \<Gamma>'\<close> by (metis eq_fst_iff subtrail_falseI)

    moreover have "is_pos (fst Ln)"
      using invars' \<open>\<Gamma> = Ln # \<Gamma>'\<close> \<open>snd Ln \<noteq> None\<close> by metis

    moreover have "\<forall>L \<in># D. atm_of L |\<in>| trail_atms \<Gamma>"
      using D_false
      unfolding trail_false_cls_def
      using trail_defined_lit_iff_true_or_false[of \<Gamma>]
      using trail_defined_lit_iff_trail_defined_atm[of \<Gamma>]
      by metis

    moreover have "\<forall>x |\<in>| trail_atms \<Gamma>'. x \<prec>\<^sub>t atm_of (fst Ln)"
      using \<open>sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>\<close>[
          unfolded \<open>\<Gamma> = Ln # \<Gamma>'\<close> sorted_wrt.simps]
      by (simp add: fset_trail_atms)

    ultimately have "linorder_lit.is_maximal_in_mset D (- fst Ln)"
      unfolding linorder_lit.is_maximal_in_mset_iff
      by (smt (verit, best) \<open>\<Gamma> = Ln # \<Gamma>'\<close> finsertE ord_res.less_lit_simps(4)
          linorder_lit.not_less_iff_gr_or_eq literal.exhaust_sel ord_res.less_lit_simps(3)
          trail_atms.simps(2) uminus_literal_def)

    moreover obtain A where "fst Ln = Pos A"
      using \<open>is_pos (fst Ln)\<close> by (cases "fst Ln") simp_all

    ultimately have eres_max_lit: "ord_res.is_maximal_lit (Neg A) D"
      by simp

    obtain C :: "'f gclause" where
      "map_of \<Gamma> (Pos A) = Some (Some C)"
      unfolding \<open>\<Gamma> = Ln # \<Gamma>'\<close>
      using \<open>fst Ln = Pos A\<close> \<open>snd Ln \<noteq> None\<close> by force

    thus "\<exists>s'. ord_res_10 N s s'"
      unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      using ord_res_10.resolution[OF D_least eres_max_lit]  by blast
  qed
qed

lemma ord_res_10_safe_state_if_invars:
  fixes N s
  assumes invars: "ord_res_10_invars N s"
  shows "safe_state (constant_context ord_res_10) ord_res_8_final (N, s)"
  using safe_state_constant_context_if_invars[where
      \<R> = ord_res_10 and \<F> = ord_res_8_final and \<I> = ord_res_10_invars]
  using ord_res_10_preserves_invars ex_ord_res_10_if_not_final invars by metis

end

end