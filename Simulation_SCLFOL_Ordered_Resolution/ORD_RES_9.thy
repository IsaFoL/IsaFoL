theory ORD_RES_9
  imports
    ORD_RES_8
begin

section \<open>ORD-RES-9 (factorize when propagating)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_9 where
  decide_neg: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')" |

  propagate: "
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
      \<forall>A\<^sub>1 |\<in>| trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<Gamma>' = (Pos A, Some (efac C)) # \<Gamma> \<Longrightarrow>
    \<F>' = (if linorder_lit.is_greatest_in_mset C (Pos A) then \<F> else finsert C \<F>) \<Longrightarrow>
    ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>')" |

  resolution: "
    linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> D|} D \<Longrightarrow>
    linorder_lit.is_maximal_in_mset D (Neg A) \<Longrightarrow>
    map_of \<Gamma> (Pos A) = Some (Some C) \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres C D) U\<^sub>e\<^sub>r \<Longrightarrow>
    \<Gamma>' = dropWhile (\<lambda>Ln. \<forall>K.
      linorder_lit.is_maximal_in_mset (eres C D) K \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma> \<Longrightarrow>
    ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')"

lemma right_unique_ord_res_9:
  fixes N :: "'f gclause fset"
  shows "right_unique (ord_res_9 N)"
proof (rule right_uniqueI)
  fix x y z
  assume step1: "ord_res_9 N x y" and step2: "ord_res_9 N x z"
  show "y = z"
    using step1
  proof (cases N x y rule: ord_res_9.cases)
    case hyps1: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A\<^sub>1 \<Gamma>\<^sub>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_9.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 show ?thesis
        by (metis (no_types, lifting) linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff
            linorder_trm.dual_order.asym linorder_trm.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      with hyps1 have False
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A\<^sub>1 C\<^sub>1 \<Gamma>\<^sub>1' \<F>\<^sub>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_9.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (metis (no_types, lifting) Uniq_D linorder_cls.is_least_in_ffilter_iff
            linorder_trm.Uniq_is_least_in_fset)
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 show ?thesis
        by (metis (no_types, lifting) linorder_cls.dual_order.asym
            linorder_cls.is_least_in_ffilter_iff linorder_trm.dual_order.asym
            linorder_trm.is_least_in_fset_iff)
    next
      case (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D\<^sub>1 A\<^sub>1 C\<^sub>1 U\<^sub>e\<^sub>r\<^sub>1' \<Gamma>\<^sub>1')
    show ?thesis
      using step2 unfolding \<open>x = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" z rule: ord_res_9.cases)
      case (decide_neg A \<Gamma>')
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case (propagate A C \<Gamma>' \<F>')
      with hyps1 have False
        by (metis (no_types) linorder_cls.is_least_in_ffilter_iff)
      thus ?thesis ..
    next
      case hyps2: (resolution D A C U\<^sub>e\<^sub>r' \<Gamma>')
      have "D\<^sub>1 = D"
        using hyps1 hyps2
        by (metis (no_types) Uniq_D linorder_cls.Uniq_is_least_in_fset)
      have "C\<^sub>1 = C"
        using hyps1 hyps2
        unfolding \<open>D\<^sub>1 = D\<close>
        by (metis (no_types) Uniq_D linorder_lit.Uniq_is_maximal_in_mset option.inject uminus_Neg)
      show ?thesis
        using hyps1 hyps2
        unfolding \<open>D\<^sub>1 = D\<close> \<open>C\<^sub>1 = C\<close>
        by argo
    qed
  qed
qed

lemma ord_res_9_is_one_or_two_ord_res_9_steps:
  fixes N s s'
  assumes step: "ord_res_9 N s s'"
  shows "ord_res_8 N s s' \<or> (ord_res_8 N OO ord_res_8 N) s s'"
  using step
proof (cases N s s' rule: ord_res_9.cases)
  case step_hyps: (decide_neg \<F> U\<^sub>e\<^sub>r \<Gamma> A \<Gamma>')
  show ?thesis
  proof (rule disjI1)
    show "ord_res_8 N s s'"
      using step_hyps ord_res_8.decide_neg by (simp only:)
  qed
next
  case step_hyps: (propagate \<F> U\<^sub>e\<^sub>r \<Gamma> A C \<Gamma>' \<F>')

  have
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_could_prop: "clause_could_propagate \<Gamma> C (Pos A)" and
    C_lt: "\<forall>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        D \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> D (Pos A) \<longrightarrow> C \<prec>\<^sub>c D"
    using step_hyps unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by argo

  hence C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
    unfolding clause_could_propagate_def by argo

  show ?thesis
  proof (cases "ord_res.is_strictly_maximal_lit (Pos A) C")
    case True

    hence "efac C = C"
      using nex_strictly_maximal_pos_lit_if_neq_efac by force

    thus ?thesis
      using True step_hyps ord_res_8.propagate by simp
  next
    case False

    have "\<F>' = finsert C \<F>"
      using False step_hyps by simp

    have "efac C \<noteq> C"
      using False C_max_lit by (metis greatest_literal_in_efacI literal.disc(1))

    hence C_in': "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
      using C_in
      by (smt (verit, ccfv_threshold) fimage_iff iefac_def ex1_efac_eq_factoring_chain
          factorizable_if_neq_efac)

    have "C |\<notin>| \<F>"
      by (smt (verit, ccfv_threshold) C_in \<open>efac C \<noteq> C\<close> factorizable_if_neq_efac fimage_iff
          ex1_efac_eq_factoring_chain iefac_def)

    have fimage_iefac_\<F>'_eq:
      "iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (efac C) ((iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) - {|C|})"
    proof (intro fsubset_antisym fsubsetI)
      fix x :: "'f gclause"
      assume "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      then obtain x' where "x' |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "x = iefac \<F>' x'"
        by blast
      thus "x |\<in>| finsert (efac C) ((iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|})"
      proof (cases "x' = C")
        case True
        hence "x = efac C"
          using \<open>x = iefac \<F>' x'\<close> by (simp add: \<open>\<F>' = finsert C \<F>\<close> iefac_def)
        thus ?thesis
          using \<open>efac C \<noteq> C\<close> by simp
      next
        case False
        hence "x = iefac \<F> x'"
          using \<open>x = iefac \<F>' x'\<close> by (auto simp add: \<open>\<F>' = finsert C \<F>\<close> iefac_def)
        then show ?thesis
          by (metis (no_types, lifting) False \<open>x' |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> ex1_efac_eq_factoring_chain
              factorizable_if_neq_efac fimage_eqI finsertCI fminus_iff fsingletonE iefac_def)
      qed
    next
      fix x :: "'f gclause"
      assume x_in: "x |\<in>| finsert (efac C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) |-| {|C|})"
      hence "x = efac C \<or> x |\<in>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) |-| {|C|})"
        by blast
      thus "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      proof (elim disjE)
        assume "x = efac C"
        hence "x = iefac \<F>' C"
          by (simp add: \<open>\<F>' = finsert C \<F>\<close> iefac_def)
        thus "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by blast
      next
        assume "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) |-| {|C|}"
        hence "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "x \<noteq> C"
          by simp_all
        then obtain x' where "x' |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "x = iefac \<F> x'"
          by auto
        moreover have "x' \<noteq> C"
          using \<open>x \<noteq> C\<close> \<open>x = iefac \<F> x'\<close>
          using \<open>C |\<notin>| \<F>\<close> iefac_def by force
        ultimately show "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          by (simp add: \<open>\<F>' = finsert C \<F>\<close> iefac_def)
      qed
    qed

    have first_step8: "ord_res_8 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)"
      using False step_hyps ord_res_8.factorize by simp

    moreover have "ord_res_8 N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>) (U\<^sub>e\<^sub>r, \<F>', \<Gamma>')"
    proof (rule ord_res_8.propagate)
      have "\<not> trail_false_cls \<Gamma> C"
        using step_hyps using C_in by metis

      hence "\<not> trail_false_cls \<Gamma> (efac C)"
        by (simp add: trail_false_cls_def)

      thus "\<not> (\<exists>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)"
        using step_hyps unfolding fimage_iefac_\<F>'_eq by blast
    next
      show "linorder_trm.is_least_in_fset {|A\<^sub>2 |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
          \<forall>A\<^sub>1|\<in>|trail_atms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2|} A"
        using step_hyps by argo
    next
      show "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r).
            clause_could_propagate \<Gamma> C (Pos A)|} (efac C)"
        unfolding linorder_cls.is_least_in_ffilter_iff
      proof (intro conjI ballI impI)
        show "efac C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          unfolding fimage_iefac_\<F>'_eq by simp
      next
        show "clause_could_propagate \<Gamma> (efac C) (Pos A)"
          using C_could_prop
          unfolding clause_could_propagate_def
          by (simp add: trail_false_cls_def greatest_literal_in_efacI
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
      next
        fix D :: "'f gterm literal multiset"
        assume
          "D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
          "D \<noteq> efac C" and
          "clause_could_propagate \<Gamma> D (Pos A)"
        thus "efac C \<prec>\<^sub>c D"
          using C_lt
          by (metis (no_types, opaque_lifting) C_in efac_properties_if_not_ident(1)
              fimage_iefac_\<F>'_eq finsert_fminus finsert_iff linorder_cls.less_trans)
      qed
    next
      show "ord_res.is_strictly_maximal_lit (Pos A) (efac C)"
        using step_hyps
        by (simp add: clause_could_propagate_def greatest_literal_in_efacI
            linorder_cls.is_least_in_ffilter_iff)
    next
      show "\<Gamma>' = (Pos A, Some (efac C)) # \<Gamma>"
        using step_hyps by argo
    qed

    ultimately have "(ord_res_8 N OO ord_res_8 N) s s'"
      using step_hyps by blast

    thus ?thesis
      by argo
  qed
next
  case step_hyps: (resolution \<Gamma> \<F> U\<^sub>e\<^sub>r D A C U\<^sub>e\<^sub>r' \<Gamma>')
  show ?thesis
  proof (rule disjI1)
    show "ord_res_8 N s s'"
      using step_hyps ord_res_8.resolution by (simp only:)
  qed
qed

lemma ord_res_9_preserves_invars:
  assumes
    step: "ord_res_9 N s s'" and
    invars: "ord_res_8_invars N s"
  shows "ord_res_8_invars N s'"
  using invars ord_res_9_is_one_or_two_ord_res_9_steps
  by (metis local.step ord_res_8_preserves_invars relcomppE)

lemma rtranclp_ord_res_9_preserves_ord_res_8_invars:
  assumes
    step: "(ord_res_9 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_8_invars N s"
  shows "ord_res_8_invars N s'"
  using step invars ord_res_9_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

lemma ex_ord_res_9_if_not_final:
  assumes
    not_final: "\<not> ord_res_8_final (N, s)" and
    invars: "ord_res_8_invars N s"
  shows "\<exists>s'. ord_res_9 N s s'"
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

    show "\<exists>s'. ord_res_9 N s s'"
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
        using ord_res_9.propagate[OF no_conflict A_least C_least]
        by metis
    next
      case False
      thus ?thesis
        unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
        using ord_res_9.decide_neg[OF no_conflict A_least] by metis
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

    thus "\<exists>s'. ord_res_9 N s s'"
      unfolding \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      using ord_res_9.resolution D_least Neg_A_max by blast
  qed
qed

lemma ord_res_9_safe_state_if_invars:
  fixes N s
  assumes invars: "ord_res_8_invars N s"
  shows "safe_state (constant_context ord_res_9) ord_res_8_final (N, s)"
  using safe_state_constant_context_if_invars[where
      \<R> = ord_res_9 and \<F> = ord_res_8_final and \<I> = ord_res_8_invars]
  using ord_res_9_preserves_invars ex_ord_res_9_if_not_final invars by metis

sublocale ord_res_9_semantics: semantics where
  step = "constant_context ord_res_9" and
  final = ord_res_8_final
proof unfold_locales
  fix S :: "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
    ('f gliteral \<times> 'f gclause option) list"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" and
    \<Gamma> :: "('f gterm literal \<times> 'f gterm literal multiset option) list" where
    S_def: "S = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
    by (metis prod.exhaust)

  assume "ord_res_8_final S"

  hence "\<nexists>x. ord_res_9 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) x"
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
      unfolding ord_res_9.simps by blast
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
      unfolding ord_res_9.simps by blast
  qed

  thus "finished (constant_context ord_res_9) S"
    by (simp add: S_def finished_def constant_context.simps)
qed

end

end