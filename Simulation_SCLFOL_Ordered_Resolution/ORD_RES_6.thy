theory ORD_RES_6
  imports
    ORD_RES_5
begin

section \<open>ORD-RES-6 (model backjump)\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_6 where
  skip: "
    (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')" |

  production: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<M>' = \<M>(atm_of L := Some C) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')" |

  factoring: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<F>' = finsert C \<F> \<Longrightarrow>
    ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))" |

  resolution_bot: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<M> (atm_of L) = Some D \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    eres D C = {#} \<Longrightarrow>
    \<M>' = (\<lambda>_. None) \<Longrightarrow>
    ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some {#})" |

  resolution_pos: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<M> (atm_of L) = Some D \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    eres D C \<noteq> {#} \<Longrightarrow>
    \<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} \<Longrightarrow>
    linorder_lit.is_maximal_in_mset (eres D C) K \<Longrightarrow>
    is_pos K \<Longrightarrow>
    ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D C))" |

  resolution_neg: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<M> (atm_of L) = Some D \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    eres D C \<noteq> {#} \<Longrightarrow>
    \<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} \<Longrightarrow>
    linorder_lit.is_maximal_in_mset (eres D C) K \<Longrightarrow>
    is_neg K \<Longrightarrow>
    \<M> (atm_of K) = Some E \<Longrightarrow>
    ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some E)"

inductive ord_res_6_step where
  "ord_res_6 N s s' \<Longrightarrow> ord_res_6_step (N, s) (N, s')"

lemma tranclp_ord_res_6_step_if_tranclp_ord_res_6:
  "(ord_res_6 N)\<^sup>+\<^sup>+ s s' \<Longrightarrow> ord_res_6_step\<^sup>+\<^sup>+ (N, s) (N, s')"
  by (induction s' rule: tranclp_induct)
   (auto intro: ord_res_6_step.intros tranclp.intros)

lemma right_unique_ord_res_6: "right_unique (ord_res_6 N)"
proof (rule right_uniqueI)
  fix s s' s''
  assume step1: "ord_res_6 N s s'" and step2: "ord_res_6 N s s''"
  thus "s' = s''"
    by (smt (verit) Pair_inject linorder_lit.Uniq_is_maximal_in_mset option.inject ord_res_6.cases
        the1_equality')
qed

lemma right_unique_ord_res_6_step: "right_unique ord_res_6_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_6_step x y \<Longrightarrow> ord_res_6_step x z \<Longrightarrow> y = z"
    using right_unique_ord_res_6[THEN right_uniqueD]
    by (elim ord_res_6_step.cases) (metis prod.inject)
qed

inductive ord_res_6_final where
  model_found:
    "ord_res_6_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, None)" |

  contradiction_found:
    "ord_res_6_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, Some {#})"

sublocale ord_res_6_semantics: semantics where
  step = ord_res_6_step and
  final = ord_res_6_final
proof unfold_locales
  fix S :: "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
    ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" and
    \<M> :: "'f gterm \<Rightarrow> 'f gclause option" and
    \<C> :: "'f gclause option" where
    S_def: "S = (N, (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>))"
    by (metis prod.exhaust)

  assume "ord_res_6_final S"
  hence "\<C> = None \<or> \<C> = Some {#}"
    by (simp add: S_def ord_res_6_final.simps)
  hence "\<nexists>x. ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) x"
    by (auto simp: linorder_lit.is_maximal_in_mset_iff elim: ord_res_6.cases)
  thus "finished ord_res_6_step S"
    by (simp add: S_def finished_def ord_res_6_step.simps)
qed

lemma ord_res_6_preserves_invars:
  assumes step: "ord_res_6 N s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
  using step
proof (cases N s s' rule: ord_res_6.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    by (metis invars ord_res_5_preserves_invars ord_res_5.skip)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    by (metis invars ord_res_5.production ord_res_5_preserves_invars)
next
  case step_hyps: (factoring \<M> C L \<F>' \<F> U\<^sub>e\<^sub>r)

  have "efac C \<noteq> C"
    by (metis ex1_efac_eq_factoring_chain is_pos_def ex_ground_factoringI step_hyps(4,5,6))
  moreover have "efac C \<preceq>\<^sub>c C"
    by (metis efac_subset subset_implies_reflclp_multp)
  ultimately have "efac C \<prec>\<^sub>c C"
    by order

  show ?thesis
    unfolding step_hyps(1,2) ord_res_5_invars_def
  proof (intro conjI)
    have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars step_hyps
      by (metis next_clause_in_factorized_clause_def ord_res_5_invars_def)
    hence "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
      using \<open>efac C \<noteq> C\<close>
      by (smt (verit, best) fimage_iff iefac_def ex1_efac_eq_factoring_chain
          factorizable_if_neq_efac)
    hence "efac C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using step_hyps(3-)
      using iefac_def by auto
    thus "next_clause_in_factorized_clause N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding next_clause_in_factorized_clause_def by simp

    have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
      using invars
      unfolding step_hyps(1,2) ord_res_5_invars_def implicitly_factorized_clauses_subset_def
      by metis

    hence "\<F>' |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
      using \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> \<open>\<F>' = finsert C \<F>\<close> by simp

    thus "implicitly_factorized_clauses_subset N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding implicitly_factorized_clauses_subset_def by simp

    have dom_\<M>_eq: "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
      using invars step_hyps
      by (simp add: model_eq_interp_upto_next_clause_def ord_res_5_invars_def)

    have "efac C |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    proof (rule notI)
      assume "efac C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      show False
      proof (cases "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac C)")
        assume "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac C)"
        hence "atm_of L \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
          using \<open>efac C \<prec>\<^sub>c C\<close> ord_res.production_subset_if_less_cls by blast
        hence "dom \<M> \<TTurnstile> C"
          using step_hyps
          by (metis dom_\<M>_eq linorder_lit.is_maximal_in_mset_iff literal.collapse(1)
              pos_literal_in_imp_true_cls)
        thus False
          using \<open>\<not> dom \<M> \<TTurnstile> C\<close> by contradiction
      next
        assume "atm_of L \<notin> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac C)"
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac C) \<TTurnstile> efac C"
          unfolding ord_res.production_unfold mem_Collect_eq
          using \<open>efac C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
          by (metis Pos_atm_of_iff \<open>efac C \<noteq> C\<close> insert_DiffM
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
              linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE
              obtains_positive_greatest_lit_if_efac_not_ident set_mset_efac step_hyps(4))
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> efac C"
          using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>efac C \<prec>\<^sub>c C\<close> \<open>efac C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
            ord_res.lift_interp_entails by metis
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
          by (simp add: true_cls_def)
        hence "dom \<M> \<TTurnstile> C"
          using dom_\<M>_eq by argo
        thus False
          using \<open>\<not> dom \<M> \<TTurnstile> C\<close> by contradiction
      qed
    qed

    have "iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) - {|C|}"
    proof (intro fsubset_antisym fsubsetI)
      fix x :: "'f gclause"
      assume "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      thus "x |\<in>| finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}"
        by (smt (verit) \<open>efac C \<noteq> C\<close> factorizable_if_neq_efac fimage_iff finsert_iff fminusI
            fsingletonE iefac_def ex1_efac_eq_factoring_chain step_hyps(7))
    next
      fix x :: "'f gclause"
      assume x_in: "x |\<in>| finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}"
      hence "x = iefac \<F>' C \<or> x |\<in>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}"
        by blast
      thus "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      proof (elim disjE)
        assume "x = iefac \<F>' C"
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
          by (metis \<open>efac C |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> iefac_def)
        ultimately show "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using iefac_def step_hyps(7) by simp
      qed
    qed

    have "ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac C) =
      ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac C)"
    proof (rule ord_res.interp_swap_clause_set)
      show "{D. D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> D \<prec>\<^sub>c efac C} =
        {D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> D \<prec>\<^sub>c efac C}"
        unfolding \<open>iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) - {|C|}\<close>
        using \<open>efac C \<prec>\<^sub>c C\<close>
        using iefac_def by force
    qed

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    proof -
      have "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>c C \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
        using invars[unfolded ord_res_5_invars_def step_hyps(1)
            all_smaller_clauses_true_wrt_respective_Interp_def, simplified]
        by simp
      then have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x = {}"
        if "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "efac C \<prec>\<^sub>c x" and "x \<prec>\<^sub>c C" for x
      proof -
        have "x \<preceq>\<^sub>l y \<and> y \<preceq>\<^sub>l z"
          if "X \<preceq>\<^sub>c Y" and "Y \<preceq>\<^sub>c Z" and
            "linorder_lit.is_maximal_in_mset X x" and
            "linorder_lit.is_maximal_in_mset Y y" and
            "linorder_lit.is_maximal_in_mset Z z"
          for x y z X Y Z
          using that
          unfolding linorder_lit.is_maximal_in_mset_iff
          by (metis ord_res.asymp_less_lit ord_res.transp_less_lit linorder_cls.leD
              linorder_lit.leI linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp_eq_multp\<^sub>H\<^sub>O
              that(3) that(4) that(5))

        hence "y = x"
          if "X \<preceq>\<^sub>c Y" and "Y \<preceq>\<^sub>c Z" and
            "linorder_lit.is_maximal_in_mset X x" and
            "linorder_lit.is_maximal_in_mset Y y" and
            "linorder_lit.is_maximal_in_mset Z x"
          for x y X Y Z
          using that
          by (metis linorder_lit.order.ordering_axioms ordering.antisym)

        hence "y = x"
          if "X \<prec>\<^sub>c Y" and "Y \<prec>\<^sub>c Z" and
            "linorder_lit.is_maximal_in_mset X x" and
            "linorder_lit.is_maximal_in_mset Y y" and
            "linorder_lit.is_maximal_in_mset Z x"
          for x y X Y Z
          using that by blast

        hence "K = L"
          if "efac C \<prec>\<^sub>c x" and "x \<prec>\<^sub>c C" and
            "linorder_lit.is_maximal_in_mset (efac C) L" and
            "linorder_lit.is_maximal_in_mset x K" and
            "linorder_lit.is_maximal_in_mset C L"
          for K
          using that by metis

        hence "K = L"
          if "linorder_lit.is_maximal_in_mset x K"
          for K
          using that
          using \<open>ord_res.is_maximal_lit L C\<close>
          using \<open>efac C \<prec>\<^sub>c x\<close> \<open>x \<prec>\<^sub>c C\<close> ex1_efac_eq_factoring_chain
            ord_res.ground_factorings_preserves_maximal_literal by blast

        hence "ord_res.is_maximal_lit L x"
          by (metis linorder_cls.leD linorder_lit.ex_maximal_in_mset mempty_lesseq_cls that(2))

        have "\<nexists>A. A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
        proof (rule notI , elim exE)
          fix A :: "'f gterm"
          assume "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
          then obtain x' where
            "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            "x = add_mset (Pos A) x'" and
            "ord_res.is_strictly_maximal_lit (Pos A) x" and
            "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
            by (metis ord_res.mem_productionE)

          have "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
            using \<open>A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x\<close>
              ord_res.production_subset_if_less_cls that(3) by fastforce

          moreover have "L = Pos A"
            using \<open>ord_res.is_maximal_lit L x\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) x\<close>
            by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset
                linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)

          moreover have "L \<in># C"
            using step_hyps linorder_lit.is_maximal_in_mset_iff by metis

          ultimately have "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
            by auto

          hence "dom \<M> \<TTurnstile> C"
            using dom_\<M>_eq by argo

          thus False
            using \<open>\<not> dom \<M> \<TTurnstile> C\<close> by contradiction
        qed

        thus ?thesis
          by simp
      qed

      moreover have "{x. x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> x \<prec>\<^sub>c C} =
        {x. x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> x \<prec>\<^sub>c efac C} \<union>
        {x. x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> efac C \<prec>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
      proof -
        have "{w \<in> NN. w \<prec>\<^sub>c z} = {w \<in> NN. w \<prec>\<^sub>c x} \<union> {y \<in> NN. x \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c z}"
          if "x \<notin> NN" and "x \<prec>\<^sub>c z" for NN x z
        proof -
          have "{w \<in> NN. w \<prec>\<^sub>c z} = {w \<in> NN. w \<preceq>\<^sub>c x \<or> x \<prec>\<^sub>c w \<and> w \<prec>\<^sub>c z}"
            using that(2) by auto
          also have "\<dots> = {w \<in> NN. w \<prec>\<^sub>c x \<or> x \<prec>\<^sub>c w \<and> w \<prec>\<^sub>c z}"
            using that(1) by auto
          also have "\<dots> = {w \<in> NN. w \<prec>\<^sub>c x} \<union> {y \<in> NN. x \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c z}"
            by auto
          finally show ?thesis .
        qed
        thus ?thesis
          using \<open>efac C \<prec>\<^sub>c C\<close> \<open>efac C |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by (simp only:)
      qed

      ultimately show ?thesis
        unfolding ord_res.interp_def by auto
    qed

    finally show "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding model_eq_interp_upto_next_clause_def
      using dom_\<M>_eq
      by simp

    have "ord_res_Interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
      if "x |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "x \<prec>\<^sub>c efac C" for x
    proof -
      have "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using that
        by (metis \<open>iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}\<close>
            finsert_iff fminusE iefac_def linorder_cls.neq_iff)

      moreover have "x \<prec>\<^sub>c C"
        using \<open>x \<prec>\<^sub>c efac C\<close> \<open>efac C \<prec>\<^sub>c C\<close> by order

      ultimately have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
        using invars
        unfolding ord_res_5_invars_def
        unfolding all_smaller_clauses_true_wrt_respective_Interp_def step_hyps(1,2)
        by blast

      moreover have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x =
        ord_res_Interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      proof (rule ord_res.Interp_swap_clause_set)
        show "{D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x} =
          {D. D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x}"
          unfolding \<open>iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}\<close>
          using \<open>x \<prec>\<^sub>c efac C\<close> \<open>x \<prec>\<^sub>c C\<close>
          by (metis (no_types, opaque_lifting) finsertCI finsertE fminusE fminusI fsingleton_iff
              iefac_def linorder_cls.less_le_not_le)
      qed

      ultimately show ?thesis
        by argo
    qed

    thus "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding all_smaller_clauses_true_wrt_respective_Interp_def by blast

    have "linorder_lit.is_greatest_in_mset (efac C) L"
      using \<open>linorder_lit.is_maximal_in_mset C L\<close>
      by (metis \<open>efac C \<noteq> C\<close> ex1_efac_eq_factoring_chain linorder_lit.Uniq_is_maximal_in_mset
          linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one
          ord_res.ground_factorings_preserves_maximal_literal
          obtains_positive_greatest_lit_if_efac_not_ident the1_equality')

    have "A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      if "\<M> A = Some D" for A D
    proof -
      have "A \<in> dom \<M>"
        using \<open>\<M> A = Some D\<close> by blast

      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using dom_\<M>_eq by argo

      have "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using invars \<open>\<M> A = Some D\<close>
        unfolding ord_res_5_invars_def step_hyps(1,2)
        unfolding atoms_in_model_were_produced_def
        by simp

      hence "linorder_lit.is_greatest_in_mset D (Pos A)"
        by (metis ord_res.mem_productionE)

      moreover have "Pos A \<prec>\<^sub>l L"
        using \<open>A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C\<close>
        by (smt (verit, del_insts) UN_E \<open>A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D\<close>
            calculation dom_\<M>_eq ord_res.interp_def ord_res.less_lit_simps(1)
            ord_res.totalp_less_lit linorder_cls.less_trans
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
            linorder_lit.is_maximal_in_mset_iff linorder_lit.less_irrefl
            linorder_lit.multp_if_maximal_less_that_maximal mem_Collect_eq
            ord_res.less_trm_iff_less_cls_if_mem_production
            pos_literal_in_imp_true_cls step_hyps(3) step_hyps(4) totalpD)

      ultimately have "D \<prec>\<^sub>c efac C"
        using \<open>linorder_lit.is_greatest_in_mset (efac C) L\<close>
        by (metis ord_res.asymp_less_lit ord_res.transp_less_lit
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
            linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp_eq_multp\<^sub>H\<^sub>O)

      have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D =
        ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      proof (rule ord_res.production_swap_clause_set)
        have "D \<prec>\<^sub>c C"
          using \<open>D \<prec>\<^sub>c efac C\<close> \<open>efac C \<prec>\<^sub>c C\<close> by order
        thus "{Da. Da |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da D} =
          {Da. Da |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da D}"
          using \<open>D \<prec>\<^sub>c efac C\<close>
          unfolding \<open>iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}\<close>
          by (metis (no_types, opaque_lifting) finsertE finsertI2 fminus_iff fsingleton_iff
              iefac_def linorder_cls.leD)
      qed

      thus ?thesis
        using \<open>A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D\<close> by argo
    qed

    thus "atoms_in_model_were_produced N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding atoms_in_model_were_produced_def by simp

    have "\<M> A = Some x"
      if "x \<prec>\<^sub>c efac C" and "A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      for x A
    proof -
      have "x \<prec>\<^sub>c C"
        using \<open>x \<prec>\<^sub>c efac C\<close> \<open>efac C \<prec>\<^sub>c C\<close> by order

      moreover have "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      proof -
        have "ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) x =
          ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
        proof (rule ord_res.production_swap_clause_set)
          show "{D. D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x} = {D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x}"
            using \<open>x \<prec>\<^sub>c efac C\<close> \<open>x \<prec>\<^sub>c C\<close>
            unfolding \<open>iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (iefac \<F>' C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) |-| {|C|}\<close>
            by (metis (no_types, opaque_lifting) finsert_iff fminus_iff fsingleton_iff iefac_def
                linorder_cls.dual_order.strict_iff_not)
        qed

        thus ?thesis
          using \<open>A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) x\<close> by argo
      qed

      ultimately show ?thesis
        using invars
        unfolding ord_res_5_invars_def step_hyps(1,2)
        unfolding all_produced_atoms_in_model_def
        by simp
    qed

    thus "all_produced_atoms_in_model N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding all_produced_atoms_in_model_def by simp
  qed
next
  case step_hyps: (resolution_bot \<M> D L C U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<F>)
  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using invars
    unfolding step_hyps(1,2) ord_res_5_invars_def implicitly_factorized_clauses_subset_def
    by metis

  hence "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
    using step_hyps by blast

  moreover have "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) {#}"
    using step_hyps linorder_cls.is_least_in_fset_iff mempty_lesseq_cls by fastforce

  ultimately show ?thesis
    using step_hyps
    using ord_res_5_invars_initial_state
    by (metis ord_res_5_invars_initial_state)
next
  case step_hyps: (resolution_pos \<M> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' K \<F>)

  hence
    L_max: "ord_res.is_maximal_lit L E" and
    L_neg: "is_neg L"
    using step_hyps by simp_all

  have \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using invars
    unfolding step_hyps(1,2) ord_res_5_invars_def implicitly_factorized_clauses_subset_def
    by metis

  have "eres D E \<noteq> E"
    using step_hyps by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

  moreover have "eres D E \<preceq>\<^sub>c E"
    using eres_le .

  ultimately have "eres D E \<prec>\<^sub>c E"
    by order

  have "\<forall>F. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) F \<longrightarrow> E \<preceq>\<^sub>c F"
    using invars
    unfolding ord_res_5_invars_def step_hyps(1,2)
    using next_clause_lt_least_false_clause[of N "(U\<^sub>e\<^sub>r, \<F>, \<M>, Some E)"]
    by simp

  have E_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) E"
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    show "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars
      unfolding ord_res_5_invars_def step_hyps(1,2)
      by (metis next_clause_in_factorized_clause_def)
  next
    have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
      using invars
      unfolding ord_res_5_invars_def step_hyps(1,2)
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
      using invars
      unfolding ord_res_5_invars_def step_hyps(1,2)
      unfolding all_smaller_clauses_true_wrt_respective_Interp_def
      using F_in F_false
      by (metis option.inject)

    thus "E \<prec>\<^sub>c F"
      using \<open>F \<noteq> E\<close> by order
  qed

  have L_prod_by_D: "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using invars
    unfolding ord_res_5_invars_def step_hyps(1,2)
    by (metis atoms_in_model_were_produced_def step_hyps(6))

  hence D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<noteq> {}"
    by (metis empty_iff)

  have "ord_res.is_maximal_lit (-L) D"
    using L_prod_by_D L_neg
    by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.collapse(2)
        ord_res.mem_productionE uminus_Neg)

  moreover have "-L \<prec>\<^sub>l L"
    using L_neg
    by (metis Neg_atm_of_iff atm_of_uminus linorder_lit.not_less_iff_gr_or_eq
        linorder_trm.less_imp_not_eq literal.collapse(1) ord_res.less_lit_simps(4) uminus_not_id)

  ultimately have "D \<prec>\<^sub>c E"
    using L_max linorder_lit.multp_if_maximal_less_that_maximal by metis

  have "eres D E |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
  proof (rule notI)
    assume "eres D E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    moreover have "\<not> (E \<prec>\<^sub>c eres D E)"
      using \<open>eres D E \<prec>\<^sub>c E\<close> by order
    ultimately have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (eres D E) \<TTurnstile> eres D E"
      using E_least_false \<open>eres D E \<noteq> E\<close>
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by metis
    then show False
      by (metis (no_types, lifting) D_prod E_least_false clause_true_if_resolved_true
          ex1_eres_eq_full_run_ground_resolution full_run_def is_least_false_clause_def
          linorder_cls.is_least_in_fset_ffilterD(2) rtranclpD)
  qed

  moreover have "efac (eres D E) |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
  proof (rule notI)
    have "efac (eres D E) \<preceq>\<^sub>c eres D E"
      by (meson efac_subset subset_implies_reflclp_multp)
    hence "\<not> (E \<prec>\<^sub>c efac (eres D E))"
      using \<open>eres D E \<prec>\<^sub>c E\<close> by order
    moreover assume "efac (eres D E) |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    moreover have "efac (eres D E) \<noteq> E"
      by (metis \<open>eres D E \<prec>\<^sub>c E\<close> efac_properties_if_not_ident(1) linorder_cls.not_less_iff_gr_or_eq)
    ultimately have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (efac (eres D E)) \<TTurnstile> efac (eres D E)"
      using E_least_false
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by metis
    hence "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (eres D E) \<TTurnstile> eres D E"
      using \<open>efac (eres D E) \<preceq>\<^sub>c eres D E\<close> ord_res.entailed_clause_stays_entailed by fastforce
    hence "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
      using clause_true_if_resolved_true
      by (smt (verit) D_prod ex1_eres_eq_full_run_ground_resolution full_run_def rtranclpD)
    moreover have "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
      using E_least_false is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(2)
      by blast
    ultimately show False
      by contradiction
  qed

  ultimately have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
    unfolding iefac_def by fastforce

  hence "iefac \<F> (eres D E) = eres D E"
    unfolding iefac_def
    using \<F>_subset by auto

  hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp

  show ?thesis
    unfolding ord_res_5_invars_def step_hyps(1,2)
  proof (intro conjI)
    have "eres D E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close> by simp

    thus "next_clause_in_factorized_clause N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      unfolding next_clause_in_factorized_clause_def by simp

    have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
      unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
      using \<open>\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r\<close> by blast

    thus "implicitly_factorized_clauses_subset N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      unfolding implicitly_factorized_clauses_subset_def by simp

    have dom_\<M>_eq: "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using invars
      unfolding step_hyps(1,2) ord_res_5_invars_def model_eq_interp_upto_next_clause_def
      by metis

    have "\<forall>x \<in># E. \<not> dom \<M> \<TTurnstile>l x"
      using \<open>\<not> dom \<M> \<TTurnstile> E\<close> by (simp add: true_cls_def)

    moreover have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> \<not> dom \<M> \<TTurnstile>l x"
    proof -
      have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> \<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile>l x"
        using L_prod_by_D by (metis ord_res.mem_productionE true_cls_def)
      moreover have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> atm_of x \<prec>\<^sub>t atm_of (- L)"
        using \<open>ord_res.is_maximal_lit (-L) D\<close> L_neg
        by (smt (verit, best) L_prod_by_D atm_of_eq_atm_of linorder_cls.order_refl
            linorder_trm.antisym_conv1 ord_res.less_trm_if_neg ord_res.lesseq_trm_if_pos)
      ultimately have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> \<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile>l x"
        using ord_res.interp_fixed_for_smaller_literals[
            OF \<open>ord_res.is_maximal_lit (-L) D\<close> _ \<open>D \<prec>\<^sub>c E\<close>]
        by fastforce

      then show ?thesis
        unfolding dom_\<M>_eq[symmetric] .
    qed

    moreover have "K \<in># eres D E"
      using \<open>ord_res.is_maximal_lit K (eres D E)\<close>
      using linorder_lit.is_maximal_in_mset_iff by metis

    moreover have "\<forall>x \<in># eres D E. x \<in># D \<or> x \<in># E"
      using lit_in_one_of_resolvents_if_in_eres by metis

    moreover have "\<forall>x \<in># eres D E. x \<noteq> - L"
    proof (intro ballI notI)
      fix x assume "x \<in># eres D E" "x = - L"
      obtain m A D' E' where
        "ord_res.is_strictly_maximal_lit (Pos A) D" and
        "D = add_mset (Pos A) D'" and
        "E = replicate_mset (Suc m) (Neg A) + E'" and
        "Neg A \<notin># E'" and
        "eres D E = repeat_mset (Suc m) D' + E'"
        using \<open>eres D E \<noteq> E\<close>[THEN eres_not_identD] by metis

      have "L = Neg A"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
        by (metis L_neg L_prod_by_D Uniq_D ord_res.mem_productionE
            linorder_lit.Uniq_is_greatest_in_mset literal.collapse(2) uminus_Pos)

      have "x \<in># D' \<or> x \<in># E'"
        using \<open>x \<in># eres D E\<close>
        unfolding \<open>eres D E = repeat_mset (Suc m) D' + E'\<close>
        by (metis member_mset_repeat_mset_Suc union_iff)
      thus False
      proof (elim disjE)
        assume "x \<in># D'"
        hence "Pos A \<in># D'"
          unfolding \<open>x = - L\<close> \<open>L = Neg A\<close> by simp
        hence "\<not> ord_res.is_strictly_maximal_lit (Pos A) D"
          using \<open>D = add_mset (Pos A) D'\<close>
          using linorder_lit.is_greatest_in_mset_iff by auto
        thus False
          using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> by contradiction
      next
        assume "x \<in># E'"
        hence "Pos A \<in># E'"
          unfolding \<open>x = - L\<close> \<open>L = Neg A\<close> by simp
        hence "Pos A \<in># E"
          unfolding \<open>E = replicate_mset (Suc m) (Neg A) + E'\<close> by simp
        hence "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile>l Pos A"
          using L_prod_by_D \<open>L = Neg A\<close> by auto
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile>l Pos A"
          by (metis \<open>L = Neg A\<close> dom_\<M>_eq linorder_lit.is_maximal_in_mset_iff
              neg_literal_notin_imp_true_cls step_hyps(3) step_hyps(4) true_lit_simps(1))
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
          using \<open>Pos A \<in># E\<close> by blast
        hence "dom \<M> \<TTurnstile> E"
          using dom_\<M>_eq by argo
        thus False
          using \<open>\<not> dom \<M> \<TTurnstile> E\<close> by contradiction
      qed
    qed

    ultimately have "\<not> dom \<M> \<TTurnstile>l K"
      by metis

    have "dom \<M>' = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) (eres D E)"
    proof (intro subset_antisym subsetI)
      fix A :: "'f gterm"
      assume "A \<in> dom \<M>'"
      hence "A \<in> dom \<M>" and "A \<prec>\<^sub>t atm_of K"
        unfolding \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by simp_all

      have "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
        using \<open>A \<in> dom \<M>\<close>
        unfolding \<open>dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E\<close> .
      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (eres D E)"
        using ord_res.interp_fixed_for_smaller_literals \<open>ord_res.is_maximal_lit K (eres D E)\<close>
          \<open>A \<prec>\<^sub>t atm_of K\<close> \<open>eres D E \<prec>\<^sub>c E\<close>
        by metis
      thus "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) (eres D E)"
        unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        using ord_res.interp_insert_greater_clause_strong by simp
    next
      fix A :: "'f gterm"
      assume "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) (eres D E)"
      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (eres D E)"
        unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        using ord_res.interp_insert_greater_clause_strong by simp
      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
        using \<open>eres D E \<prec>\<^sub>c E\<close> ord_res.interp_subset_if_less_cls by blast
      hence "A \<in> dom \<M>"
        unfolding \<open>dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E\<close> .
      
      moreover have "A \<prec>\<^sub>t atm_of K"
      proof -
        obtain C where
          "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
          "C \<prec>\<^sub>c eres D E" and
          A_prod_by_C: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
          using \<open>A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (eres D E)\<close>
          unfolding ord_res.interp_def by blast

        have "ord_res.is_maximal_lit (Pos A) C"
          using A_prod_by_C ord_res.mem_productionE by blast

        hence "A \<preceq>\<^sub>t atm_of K"
          using \<open>ord_res.is_maximal_lit K (eres D E)\<close> \<open>C \<prec>\<^sub>c eres D E\<close>
          by (metis linorder_cls.dual_order.asym linorder_lit.multp_if_maximal_less_that_maximal
              linorder_trm.not_le_imp_less literal.collapse(1) ord_res.less_lit_simps(1)
              step_hyps(11))

        moreover have "A \<noteq> atm_of K"
          using \<open>A \<in> dom \<M>\<close> \<open>\<not> dom \<M> \<TTurnstile>l K\<close> \<open>is_pos K\<close> by force

        ultimately show ?thesis
          by order
      qed

      ultimately show "A \<in> dom \<M>'"
        unfolding \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by simp
    qed

    thus "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      unfolding model_eq_interp_upto_next_clause_def by simp

    have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c eres D E \<longrightarrow>
       ord_res_Interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r')) C \<TTurnstile> C"
      by (smt (verit, ccfv_threshold) E_least_false Uniq_def Uniq_is_least_false_clause
          \<open>eres D E \<prec>\<^sub>c E\<close> \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
          finite_fset finsert.rep_eq finsertE finsert_absorb
          fset.set_map ord_res.transp_less_cls
          is_least_false_clause_finsert_smaller_false_clause linorder_cls.max.strict_order_iff
          ord_res.interp_insert_greater_clause ord_res.production_insert_greater_clause transpE
          true_cls_iefac_iff union_fset)

    hence "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c eres D E \<longrightarrow>
       ord_res_Interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r')) C \<TTurnstile> C"
      unfolding \<open>eres D E \<prec>\<^sub>c E\<close> \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    thus "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      unfolding all_smaller_clauses_true_wrt_respective_Interp_def by simp

    have "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
      if "\<M>' A = Some C" for A C
    proof -
      have "\<M> A = Some C" and "A \<prec>\<^sub>t atm_of K"
        unfolding atomize_conj
        using \<open>\<M>' A = Some C\<close> \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close>
        by (metis Int_iff domI dom_restrict mem_Collect_eq restrict_in)

      hence A_prod_by_C: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using invars
        unfolding step_hyps(1,2) ord_res_5_invars_def atoms_in_model_were_produced_def
        by metis

      moreover have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C =
        ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
      proof (rule ord_res.production_swap_clause_set)
        have "ord_res.is_strictly_maximal_lit (Pos A) C"
          using A_prod_by_C ord_res.mem_productionE by metis
        moreover have "Pos A \<prec>\<^sub>l K"
          using \<open>A \<prec>\<^sub>t atm_of K\<close>
          by (metis Pos_atm_of_iff ord_res.less_lit_simps(1) step_hyps(11))
        ultimately have "C \<prec>\<^sub>c eres D E"
          using linorder_lit.multp_if_maximal_less_that_maximal step_hyps(10) by blast
        thus "{D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C} =
          {D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C}"
          unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
          by auto
      qed

      ultimately show ?thesis
        by argo
    qed

    thus "atoms_in_model_were_produced N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      unfolding atoms_in_model_were_produced_def by simp

    have "\<M>' A = Some C"
      if "C \<prec>\<^sub>c eres D E" and A_in: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
      for C A
    proof -
      have "C \<prec>\<^sub>c E"
        using \<open>C \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

      moreover have A_prod_by_C: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
      proof -
        have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C =
          ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
        proof (rule ord_res.production_swap_clause_set)
          show "{D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C} =
            {D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C}"
            unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
            using \<open>C \<prec>\<^sub>c eres D E\<close>
            by (metis (no_types, opaque_lifting) finsert_iff linorder_cls.less_le_not_le)
        qed

        thus ?thesis
          using A_in by argo
      qed

      ultimately have "\<M> A = Some C"
        using invars
        unfolding step_hyps(1,2) ord_res_5_invars_def all_produced_atoms_in_model_def
        by metis

      moreover have "A \<prec>\<^sub>t atm_of K"
      proof -
        have "A \<in> dom \<M>"
          using \<open>\<M> A = Some C\<close> by auto

        have "ord_res.is_maximal_lit (Pos A) C"
          using A_prod_by_C ord_res.mem_productionE by blast

        hence "A \<preceq>\<^sub>t atm_of K"
          using \<open>ord_res.is_maximal_lit K (eres D E)\<close> \<open>C \<prec>\<^sub>c eres D E\<close>
          by (metis linorder_cls.dual_order.asym linorder_lit.multp_if_maximal_less_that_maximal
              linorder_trm.not_le_imp_less literal.collapse(1) ord_res.less_lit_simps(1)
              step_hyps(11))

        moreover have "A \<noteq> atm_of K"
          using \<open>A \<in> dom \<M>\<close> \<open>\<not> dom \<M> \<TTurnstile>l K\<close> \<open>is_pos K\<close> by force

        ultimately show ?thesis
          by order
      qed

      ultimately show "\<M>' A = Some C"
        unfolding \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by simp
    qed

    thus "all_produced_atoms_in_model N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      unfolding all_produced_atoms_in_model_def by simp
  qed
next
  case step_hyps: (resolution_neg \<M> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' K C \<F>)

  obtain A\<^sub>L where L_def: "L = Neg A\<^sub>L"
    using \<open>is_neg L\<close> by (cases L) simp_all

  have "A\<^sub>L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using invars \<open>\<M> (atm_of L) = Some D\<close>
    unfolding step_hyps(1,2) ord_res_5_invars_def atoms_in_model_were_produced_def
    unfolding L_def literal.sel
    by metis

  hence "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    "ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) D" and
    D_false: "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    unfolding atomize_conj by (metis ord_res.mem_productionE)

  obtain A\<^sub>K where K_def: "K = Neg A\<^sub>K"
    using \<open>is_neg K\<close> by (cases K) simp_all

  have "A\<^sub>K \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    using invars \<open>\<M> (atm_of K) = Some C\<close>
    unfolding step_hyps(1,2) ord_res_5_invars_def atoms_in_model_were_produced_def
    unfolding K_def literal.sel
    by metis

  hence "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    "ord_res.is_strictly_maximal_lit (Pos A\<^sub>K) C" and
    C_false: "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    unfolding atomize_conj by (metis ord_res.mem_productionE)

  have "D \<prec>\<^sub>c E"
    using \<open>ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) D\<close> \<open>ord_res.is_maximal_lit L E\<close>[unfolded L_def]
    using linorder_lit.multp_if_maximal_less_that_maximal ord_res.less_lit_simps(2) by blast

  have "eres D E \<noteq> E"
    using \<open>ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) D\<close> \<open>ord_res.is_maximal_lit L E\<close>[unfolded L_def]
    by (metis L_def eres_ident_iff ex_ground_resolutionI is_pos_def
        linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one
        linorder_lit.multp_if_maximal_less_that_maximal linorder_lit.neq_iff
        linorder_trm.dual_order.asym ord_res.less_lit_simps(4) ground_resolution_def step_hyps(5))

  moreover have "eres D E \<preceq>\<^sub>c E"
    using eres_le .

  ultimately have "eres D E \<prec>\<^sub>c E"
    by order

  have "iefac \<F> (eres D E) = eres D E"
    by (metis (mono_tags, lifting) Uniq_D efac_spec iefac_def is_pos_def
        linorder_lit.Uniq_is_maximal_in_mset step_hyps(10) step_hyps(11))

  hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp

  hence "{|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c eres D E|} =
    {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c eres D E|}"
    by auto

  show ?thesis
    unfolding step_hyps(1,2) ord_res_5_invars_def
  proof (intro conjI)
    have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
      using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by simp

    thus "next_clause_in_factorized_clause N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      unfolding next_clause_in_factorized_clause_def by simp

    have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
      using invars
      unfolding step_hyps(1,2) ord_res_5_invars_def implicitly_factorized_clauses_subset_def
      by metis

    hence "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
      unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by blast

    thus "implicitly_factorized_clauses_subset N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      unfolding implicitly_factorized_clauses_subset_def by simp

    have "Pos A\<^sub>K \<prec>\<^sub>l Neg A\<^sub>K"
      by simp

    hence "C \<prec>\<^sub>c eres D E"
      using \<open>ord_res.is_strictly_maximal_lit (Pos A\<^sub>K) C\<close>
        \<open>ord_res.is_maximal_lit K (eres D E)\<close>[unfolded K_def]
      using linorder_lit.multp_if_maximal_less_that_maximal by blast

    have "C \<prec>\<^sub>c E"
      using \<open>C \<prec>\<^sub>c eres D E\<close> \<open>eres D E \<prec>\<^sub>c E\<close> by order

    have "{|x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). x \<prec>\<^sub>c C|} = {|x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>c C|}"
      using \<open>C \<prec>\<^sub>c eres D E\<close>
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by (metis ffilter_eq_ffilter_minus_singleton finsert_absorb fminus_finsert_absorb
          linorder_cls.less_asym)

    hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C =
      ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
      using \<open>C \<prec>\<^sub>c eres D E\<close>
      by (simp add: \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
          ord_res.interp_insert_greater_clause)

    have dom_\<M>_eq: "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using invars
      unfolding step_hyps(1,2) ord_res_5_invars_def model_eq_interp_upto_next_clause_def
      by metis

    have "\<forall>x \<in># E. \<not> dom \<M> \<TTurnstile>l x"
      using \<open>\<not> dom \<M> \<TTurnstile> E\<close> by (simp add: true_cls_def)

    moreover have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> \<not> dom \<M> \<TTurnstile>l x"
    proof -
      have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> \<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile>l x"
        using D_false by blast
      moreover have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> atm_of x \<prec>\<^sub>t atm_of (- L)"
        unfolding L_def uminus_Neg literal.sel
        using \<open>ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) D\<close>
        by (metis Pos_atm_of_iff \<open>A\<^sub>L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D\<close>
            ord_res.less_trm_if_neg ord_res.lesseq_trm_if_pos reflclp_iff)
      ultimately have "\<forall>x \<in># D. x \<noteq> -L \<longrightarrow> \<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile>l x"
        using ord_res.interp_fixed_for_smaller_literals
        using \<open>ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) D\<close> \<open>D \<prec>\<^sub>c E\<close>
        using L_def by fastforce
      thus ?thesis
        unfolding dom_\<M>_eq[symmetric] .
    qed

    moreover have "K \<in># eres D E"
      using \<open>ord_res.is_maximal_lit K (eres D E)\<close>
      using linorder_lit.is_maximal_in_mset_iff by metis

    moreover have "\<forall>x \<in># eres D E. x \<in># D \<or> x \<in># E"
      using lit_in_one_of_resolvents_if_in_eres by metis

    moreover have "\<forall>x \<in># eres D E. x \<noteq> - L"
    proof (intro ballI notI)
      fix x assume "x \<in># eres D E" "x = - L"
      obtain m A D' E' where
        "ord_res.is_strictly_maximal_lit (Pos A) D" and
        "D = add_mset (Pos A) D'" and
        "E = replicate_mset (Suc m) (Neg A) + E'" and
        "Neg A \<notin># E'" and
        "eres D E = repeat_mset (Suc m) D' + E'"
        using \<open>eres D E \<noteq> E\<close>[THEN eres_not_identD] by metis

      have "L = Neg A"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
        by (metis L_def Uniq_D \<open>ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) D\<close>
            linorder_lit.Uniq_is_greatest_in_mset literal.inject(1))

      have "x \<in># D' \<or> x \<in># E'"
        using \<open>x \<in># eres D E\<close>
        unfolding \<open>eres D E = repeat_mset (Suc m) D' + E'\<close>
        by (metis member_mset_repeat_mset_Suc union_iff)
      thus False
      proof (elim disjE)
        assume "x \<in># D'"
        hence "Pos A \<in># D'"
          unfolding \<open>x = - L\<close> \<open>L = Neg A\<close> by simp
        hence "\<not> ord_res.is_strictly_maximal_lit (Pos A) D"
          using \<open>D = add_mset (Pos A) D'\<close>
          using linorder_lit.is_greatest_in_mset_iff by auto
        thus False
          using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> by contradiction
      next
        assume "x \<in># E'"
        hence "Pos A \<in># E'"
          unfolding \<open>x = - L\<close> \<open>L = Neg A\<close> by simp
        hence "Pos A \<in># E"
          unfolding \<open>E = replicate_mset (Suc m) (Neg A) + E'\<close> by simp
        hence "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile>l Pos A"
          using L_def \<open>A\<^sub>L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D\<close> \<open>L = Neg A\<close>
          by blast
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile>l Pos A"
          by (metis \<open>L = Neg A\<close> dom_\<M>_eq linorder_lit.is_maximal_in_mset_iff
              neg_literal_notin_imp_true_cls step_hyps(3) step_hyps(4) true_lit_simps(1))
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
          using \<open>Pos A \<in># E\<close> by blast
        hence "dom \<M> \<TTurnstile> E"
          using dom_\<M>_eq by argo
        thus False
          using \<open>\<not> dom \<M> \<TTurnstile> E\<close> by contradiction
      qed
    qed

    ultimately have "\<not> dom \<M> \<TTurnstile>l K"
      by metis

    have "dom \<M>' = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
    proof (intro subset_antisym subsetI)
      fix A :: "'f gterm"
      assume "A \<in> dom \<M>'"
      hence "A \<in> dom \<M>" and "A \<prec>\<^sub>t atm_of K"
        unfolding \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by simp_all

      have "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
        using \<open>A \<in> dom \<M>\<close>
        unfolding \<open>dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E\<close> .
      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using ord_res.interp_fixed_for_smaller_literals \<open>ord_res.is_maximal_lit K (eres D E)\<close>
          \<open>A \<prec>\<^sub>t atm_of K\<close> \<open>C \<prec>\<^sub>c E\<close>
        by (smt (verit, del_insts) K_def
            \<open>A\<^sub>K \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C\<close> \<open>eres D E \<prec>\<^sub>c E\<close>
            literal.sel(2) ord_res.lesser_atoms_in_previous_interp_are_in_final_interp
            ord_res.lesser_atoms_not_in_previous_interp_are_not_in_final_interp_if_productive)
      thus "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
        unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        using ord_res.interp_insert_greater_clause_strong
        by (simp add: \<open>C \<prec>\<^sub>c eres D E\<close>)
    next
      fix A :: "'f gterm"
      assume "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        using ord_res.interp_insert_greater_clause_strong by (simp add: \<open>C \<prec>\<^sub>c eres D E\<close>)
      hence "A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
        using \<open>C \<prec>\<^sub>c E\<close> ord_res.interp_subset_if_less_cls by blast
      hence "A \<in> dom \<M>"
        unfolding \<open>dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E\<close> .

      moreover have "A \<prec>\<^sub>t atm_of K"
      proof -
        obtain B where
          "B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
          "B \<prec>\<^sub>c C" and
          A_prod_by_B: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) B"
          using \<open>A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C\<close>
          unfolding ord_res.interp_def by blast

        have "ord_res.is_maximal_lit (Pos A) B"
          using A_prod_by_B ord_res.mem_productionE by blast

        hence "A \<preceq>\<^sub>t atm_of K"
          using \<open>ord_res.is_maximal_lit K (eres D E)\<close> \<open>C \<prec>\<^sub>c eres D E\<close>
          by (metis K_def \<open>B \<prec>\<^sub>c C\<close> asympD
              linorder_cls.less_trans linorder_lit.multp_if_maximal_less_that_maximal
              linorder_trm.le_less_linear literal.sel(2)
              ord_res.asymp_less_cls ord_res.less_lit_simps(4))

        moreover have "A \<noteq> atm_of K"
          using \<open>A \<in> dom \<M>\<close> \<open>\<not> dom \<M> \<TTurnstile>l K\<close>
          unfolding K_def
          by (metis \<open>A \<in> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C\<close>
              \<open>A\<^sub>K \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C\<close> atm_of_uminus
              linorder_lit.is_greatest_in_mset_iff literal.sel(1) ord_res.mem_productionE
              pos_literal_in_imp_true_cls uminus_Neg)

        ultimately show ?thesis
          by order
      qed

      ultimately show "A \<in> dom \<M>'"
        unfolding \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by simp
    qed

    thus "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      unfolding model_eq_interp_upto_next_clause_def by simp

    have "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>c E \<longrightarrow>
      ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
      using invars
      unfolding step_hyps(1,2) ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def
      by simp

    hence "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>c C \<longrightarrow>
      ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
      using \<open>C \<prec>\<^sub>c E\<close> by simp

    moreover have "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>c C \<longrightarrow>
      ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x =
      ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) x"
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      by (metis (no_types, lifting) \<open>C \<prec>\<^sub>c eres D E\<close> finite_fset finsert.rep_eq
          linorder_cls.dual_order.strict_trans2 ord_res.Interp_insert_greater_clause sup2CI)

    ultimately have "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>c C \<longrightarrow>
      ord_res_Interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r')) x \<TTurnstile> x"
      by simp

    hence "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). x \<prec>\<^sub>c C \<longrightarrow>
      ord_res_Interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r')) x \<TTurnstile> x"
      unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
      using \<open>C \<prec>\<^sub>c eres D E\<close> by auto

    thus "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      unfolding all_smaller_clauses_true_wrt_respective_Interp_def
      by simp

    have "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
      if "\<M>' A = Some C" for A C
    proof -
      have "\<M> A = Some C" and "A \<prec>\<^sub>t atm_of K"
        unfolding atomize_conj
        using \<open>\<M>' A = Some C\<close> \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close>
        by (metis Int_iff domI dom_restrict mem_Collect_eq restrict_in)

      hence A_prod_by_C: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using invars
        unfolding step_hyps(1,2) ord_res_5_invars_def atoms_in_model_were_produced_def
        by metis

      moreover have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C =
        ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
      proof (rule ord_res.production_swap_clause_set)
        have "ord_res.is_strictly_maximal_lit (Pos A) C"
          using A_prod_by_C ord_res.mem_productionE by metis
        moreover have "Pos A \<prec>\<^sub>l K"
          using \<open>A \<prec>\<^sub>t atm_of K\<close>
          by (simp add: K_def)
        ultimately have "C \<prec>\<^sub>c eres D E"
          using linorder_lit.multp_if_maximal_less_that_maximal step_hyps(10) by blast
        thus "{D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C} =
          {D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C}"
          unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
          by auto
      qed

      ultimately show ?thesis
        by argo
    qed

    thus "atoms_in_model_were_produced N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      unfolding atoms_in_model_were_produced_def by simp

    have "\<M>' A = Some B"
      if "B \<prec>\<^sub>c C" and A_in: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) B"
      for B A
    proof -
      have "B \<prec>\<^sub>c eres D E"
        using \<open>B \<prec>\<^sub>c C\<close> \<open>C \<prec>\<^sub>c eres D E\<close> by order
      hence "B \<prec>\<^sub>c E"
        using \<open>eres D E \<prec>\<^sub>c E\<close> by order

      moreover have A_prod_by_B: "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) B"
      proof -
        have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) B =
          ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) B"
        proof (rule ord_res.production_swap_clause_set)
          show "{D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D B} =
            {D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D B}"
            unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
            using \<open>B \<prec>\<^sub>c eres D E\<close>
            by (metis (no_types, opaque_lifting) finsert_iff linorder_cls.less_le_not_le)
        qed

        thus ?thesis
          using A_in by argo
      qed

      ultimately have "\<M> A = Some B"
        using invars
        unfolding step_hyps(1,2) ord_res_5_invars_def all_produced_atoms_in_model_def
        by metis

      moreover have "A \<prec>\<^sub>t atm_of K"
      proof -
        have "A \<in> dom \<M>"
          using \<open>\<M> A = Some B\<close> by auto

        have "ord_res.is_maximal_lit (Pos A) B"
          using A_prod_by_B ord_res.mem_productionE by blast

        hence "A \<preceq>\<^sub>t atm_of K"
          using \<open>ord_res.is_maximal_lit K (eres D E)\<close> \<open>B \<prec>\<^sub>c eres D E\<close>
          by (metis K_def asympD linorder_lit.multp_if_maximal_less_that_maximal
              linorder_trm.le_less_linear literal.sel(2) ord_res.asymp_less_cls
              ord_res.less_lit_simps(4))

        moreover have "A \<noteq> atm_of K"
          using \<open>A \<in> dom \<M>\<close> \<open>\<not> dom \<M> \<TTurnstile>l K\<close>
          using \<open>\<M> A = Some B\<close> step_hyps(12) that(1) by force

        ultimately show ?thesis
          by order
      qed

      ultimately show "\<M>' A = Some B"
        unfolding \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by simp
    qed

    thus "all_produced_atoms_in_model N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      unfolding all_produced_atoms_in_model_def by simp
  qed
qed

lemma rtranclp_ord_res_6_preserves_invars:
  assumes steps: "(ord_res_6 N)\<^sup>*\<^sup>* s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
  using steps invars
  by (induction s rule: converse_rtranclp_induct) (auto intro: ord_res_6_preserves_invars)

lemma ex_ord_res_6_if_not_final:
  assumes
    not_final: "\<not> ord_res_6_final S" and
    invars: "\<forall>N s. S = (N, s) \<longrightarrow> ord_res_5_invars N s"
  shows "\<exists>S'. ord_res_6_step S S'"
proof -
  from not_final obtain N U\<^sub>e\<^sub>r \<F> \<M> C where
    S_def: "S = (N, (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C))" and "C \<noteq> {#}"
    unfolding ord_res_6_final.simps de_Morgan_disj not_ex
    by (metis option.exhaust surj_pair)

  note invars' = invars[unfolded ord_res_5_invars_def, rule_format, OF S_def]

  have "\<exists>s'. ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s'"
  proof (cases "dom \<M> \<TTurnstile> C")
    case True
    thus ?thesis
      using ord_res_6.skip by metis
  next
    case C_false: False
    obtain L where L_max: "linorder_lit.is_maximal_in_mset C L"
      using linorder_lit.ex_maximal_in_mset[OF \<open>C \<noteq> {#}\<close>] ..

    show ?thesis
    proof (cases L)
      case (Pos A)
      hence L_pos: "is_pos L"
        by simp
      show ?thesis
      proof (cases "ord_res.is_strictly_maximal_lit L C")
        case True
        then show ?thesis
          using ord_res_6.production[OF C_false L_max L_pos] by metis
      next
        case L_not_striclty_max: False
        thus ?thesis
          using ord_res_6.factoring[OF C_false L_max L_pos L_not_striclty_max refl] by metis
      qed
    next
      case (Neg A)
      hence L_neg: "is_neg L"
        by simp

      have C_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      proof (intro conjI ballI impI)
        show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars' by (metis next_clause_in_factorized_clause_def)
      next
        have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
          using invars' C_false by (metis model_eq_interp_upto_next_clause_def)
        moreover have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
        proof -
          have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
            using L_max L_neg
            by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset
                linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
          thus ?thesis
            using unproductive_if_nex_strictly_maximal_pos_lit by metis
        qed
        ultimately show "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
          by simp
      next
        fix D
        assume D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "D \<noteq> C" and
          C_false: "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
        have "\<not> D \<prec>\<^sub>c C"
          using C_false
          using invars' D_in
          unfolding all_smaller_clauses_true_wrt_respective_Interp_def
          by auto
        thus "C \<prec>\<^sub>c D"
          using \<open>D \<noteq> C\<close> by order
      qed
      then obtain D where "D|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        "D \<prec>\<^sub>c C" and
        "ord_res.is_strictly_maximal_lit (Pos A) D" and
        D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {A}"
        using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
          L_max[unfolded Neg] by metis

      hence "\<exists>DC. ground_resolution D C DC"
        unfolding ground_resolution_def
        using L_max Neg ex_ground_resolutionI by blast

      hence "eres D C \<noteq> C"
        unfolding eres_ident_iff by metis

      hence "eres D C \<prec>\<^sub>c C"
        using eres_le[of D C] by order

      have "\<M> (atm_of L) = Some D"
        using invars'
        by (metis Neg \<open>D \<prec>\<^sub>c C\<close> all_produced_atoms_in_model_def D_prod insertI1 literal.sel(2))

      show ?thesis
      proof (cases "eres D C = {#}")
        case True
        then show ?thesis
          using ord_res_6.resolution_bot[OF C_false L_max L_neg \<open>\<M> (atm_of L) = Some D\<close>] by metis
      next
        case False
        then obtain K where K_max: "ord_res.is_maximal_lit K (eres D C)"
          using linorder_lit.ex_maximal_in_mset by metis
        show ?thesis
        proof (cases K)
          case K_def: (Pos A\<^sub>K)
          hence "is_pos K"
            by  simp
          thus ?thesis
            using ord_res_6.resolution_pos
            using C_false L_max L_neg \<open>\<M> (atm_of L) = Some D\<close> \<open>eres D C \<noteq> {#}\<close> K_max by metis
        next
          case K_def: (Neg A\<^sub>K)
          hence K_neg: "is_neg K"
            by simp

          have "\<not> ord_res_Interp (fset (finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))) (eres D C) \<TTurnstile> eres D C"
            by (smt (verit) C_least_false D_prod Interp_insert_unproductive K_max K_neg Uniq_D
                \<open>eres D C \<noteq> C\<close> clause_true_if_resolved_true ex1_eres_eq_full_run_ground_resolution
                finite_fset fset_simps(2) full_run_def insert_not_empty is_least_false_clause_def
                linorder_cls.is_least_in_fset_ffilterD(2) linorder_lit.Uniq_is_maximal_in_mset
                linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset rtranclpD
                unproductive_if_nex_strictly_maximal_pos_lit)

          hence eres_least:
            "is_least_false_clause (finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (eres D C)"
            using C_least_false \<open>eres D C \<prec>\<^sub>c C\<close>
            by (metis is_least_false_clause_finsert_smaller_false_clause)

          then obtain E where "E |\<in>| finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))" and
            "E \<prec>\<^sub>c eres D C" and
            "ord_res.is_strictly_maximal_lit (Pos A\<^sub>K) E" and
            E_prod: "ord_res.production (fset (finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))) E = {A\<^sub>K}"
            using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
              K_max K_def
            by  metis

          have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E =
            ord_res.production (fset (finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))) E"
          proof (rule ord_res.production_swap_clause_set)
            have "eres D C |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            proof (rule notI)
              assume "eres D C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              hence "finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) = iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
                by blast
              hence "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (eres D C)"
                using eres_least by argo
              thus False
                using C_least_false \<open>eres D C \<noteq> C\<close>
                by (metis Uniq_D Uniq_is_least_false_clause)
            qed

            thus "{D. D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D E} =
              {Da. Da |\<in>| finsert (eres D C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da E}"
              by (metis (mono_tags, lifting) \<open>E \<prec>\<^sub>c eres D C\<close> finsert_iff linorder_cls.leD)
          qed

          also have "\<dots> = {A\<^sub>K}"
            using E_prod .

          finally have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E = {A\<^sub>K}" .

          hence "\<M> (atm_of K) = Some E"
            using invars'
            unfolding ord_res_5_invars_def all_produced_atoms_in_model_def
            by (metis K_def \<open>E \<prec>\<^sub>c eres D C\<close> eres_le insertI1 linorder_cls.dual_order.strict_trans1
                literal.sel(2))

          thus ?thesis
            using ord_res_6.resolution_neg
            using C_false L_max L_neg \<open>\<M> (atm_of L) = Some D\<close> \<open>eres D C \<noteq> {#}\<close> K_max K_neg by metis
        qed
      qed
    qed
  qed
  thus ?thesis
    using S_def ord_res_6_step.simps by metis
qed

lemma ord_res_6_safe_state_if_invars:
  "safe_state ord_res_6_step ord_res_6_final (N, s)" if invars: "ord_res_5_invars N s" for N s
proof -
  {
    fix S'
    assume "ord_res_6_semantics.eval (N, s) S'" and stuck: "stuck_state ord_res_6_step S'"
    then obtain s' where "S' = (N, s')" and "(ord_res_6 N)\<^sup>*\<^sup>* s s'"
    proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
      case base
      thus ?case by simp
    next
      case (step z)
      thus ?case
        by (smt (verit, ccfv_SIG) converse_rtranclp_into_rtranclp ord_res_6_step.cases prod.inject)
    qed
    hence "ord_res_5_invars N s'"
      using invars rtranclp_ord_res_6_preserves_invars by metis
    hence "\<not> ord_res_6_final S' \<Longrightarrow> \<exists>S''. ord_res_6_step S' S''"
      using ex_ord_res_6_if_not_final[of S'] \<open>S' = (N, s')\<close> by blast
    hence "ord_res_6_final S'"
      using stuck[unfolded stuck_state_def] by argo
  }
  thus ?thesis
    unfolding safe_state_def stuck_state_def by metis
qed

lemma ex_model_build_from_least_clause_to_any_less_than_least_false:
  assumes
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    C_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    D_lt_least_false: "\<forall>E. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) E \<longrightarrow> D \<preceq>\<^sub>c E" and
    "C \<preceq>\<^sub>c D"
  shows "\<exists>\<M>. (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, Map.empty, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"
  using ord_res.wfP_less_cls D_in \<open>C \<preceq>\<^sub>c D\<close> D_lt_least_false
proof (induction D rule: wfp_induct_rule)
  case (less D)

  have invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, Map.empty, Some C)"
    using ord_res_5_invars_initial_state \<F>_subset C_least by metis

  define clauses_lt_D :: "'f gclause fset" where
    "clauses_lt_D = {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}"

  show ?case
  proof (cases "clauses_lt_D = {||}")
    case True
    hence "C = D"
      unfolding clauses_lt_D_def
      using C_least \<open>C \<preceq>\<^sub>c D\<close>
      by (metis fempty_iff ffmember_filter linorder_cls.antisym_conv3
          linorder_cls.is_least_in_fset_iff linorder_cls.less_le_not_le)
    thus ?thesis
      by blast
  next
    case False

    obtain x where x_greatest: "linorder_cls.is_greatest_in_fset clauses_lt_D x"
      using False linorder_cls.ex_greatest_in_fset by metis

    have "x \<prec>\<^sub>c D" and "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using x_greatest by (simp_all add: clauses_lt_D_def linorder_cls.is_greatest_in_fset_iff)

    moreover have "C \<preceq>\<^sub>c x"
      using x_greatest C_least
      by (metis clauses_lt_D_def ffmember_filter linorder_cls.is_greatest_in_fset_iff
          linorder_cls.not_less nbex_less_than_least_in_fset)

    moreover have "\<And>E. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) E \<Longrightarrow> x \<prec>\<^sub>c E"
      using \<open>x \<prec>\<^sub>c D\<close> less.prems by force

    ultimately obtain \<M> where
      IH: "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, Map.empty, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, Some x)"
      using less.IH by blast

    moreover have "\<exists>\<M>'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some x) (U\<^sub>e\<^sub>r, \<F>, \<M>', Some D)"
    proof -
      have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) x) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using x_greatest[unfolded clauses_lt_D_def]
        by (smt (verit) ffmember_filter less.prems(1) linorder_cls.is_greatest_in_fset_iff
            linorder_cls.is_least_in_ffilter_iff linorder_cls.not_less_iff_gr_or_eq)
      hence next_clause_eq: "The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) x) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))) = Some D"
        by (metis linorder_cls.Uniq_is_least_in_fset The_optional_eq_SomeI)

      have x_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
        using less.prems
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
        
        by (metis \<open>\<And>E. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) E \<Longrightarrow> x \<prec>\<^sub>c E\<close> \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
            ex_false_clause_iff finsert_absorb is_least_false_clause_finsert_smaller_false_clause
            linorder_cls.order.irrefl ex_false_clause_def)

      show ?thesis
      proof (cases "dom \<M> \<TTurnstile> x")
        case True
        thus ?thesis
          using ord_res_5.skip next_clause_eq by metis
      next
        case False
        hence "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x \<TTurnstile> x"
          using rtranclp_ord_res_5_preserves_invars[OF IH invars, unfolded ord_res_5_invars_def,
              simplified]
          by (simp add: model_eq_interp_upto_next_clause_def)

        thus ?thesis
          using ord_res_5.production[OF False] next_clause_eq
          using x_true
          by (metis Un_empty_right linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
              unproductive_if_nex_strictly_maximal_pos_lit)
      qed
    qed

    ultimately show ?thesis
      by (smt (verit) rtranclp.rtrancl_into_rtrancl)
  qed
qed

lemma full_rtranclp_ord_res_5_run_upto:
  assumes
    "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>', \<M>', Some D)" and
    invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>', \<M>', Some D)" and
    \<M>'_def: "\<M>' = restrict_map \<M> {A. \<exists>K. linorder_lit.is_maximal_in_mset D K \<and> A \<prec>\<^sub>t atm_of K}" and
    C_least: "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
  shows "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>', Map.empty, Some C) (U\<^sub>e\<^sub>r', \<F>', \<M>', Some D)"
proof -
  have D_in: "D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    using invars
    by (metis next_clause_in_factorized_clause_def ord_res_5_invars_def)

  have "\<F>' |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
    using invars
    by (metis implicitly_factorized_clauses_subset_def ord_res_5_invars_def)

  moreover have "C \<preceq>\<^sub>c D"
    using C_least D_in
    by (metis linorder_cls.dual_order.strict_iff_order linorder_cls.is_least_in_fset_iff
        linorder_cls.le_cases)

  moreover have "\<forall>F. is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r')) F \<longrightarrow> D \<preceq>\<^sub>c F"
    using invars le_least_false_clause by metis

  ultimately obtain \<M>'' where
    steps: "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>', Map.empty, Some C) (U\<^sub>e\<^sub>r', \<F>', \<M>'', Some D)"
    using C_least D_in
    by (metis ex_model_build_from_least_clause_to_any_less_than_least_false)

  have "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>', Map.empty, Some C)"
    using \<open>\<F>' |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'\<close> C_least ord_res_5_invars_initial_state by metis

  hence "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>', \<M>'', Some D)"
    using \<open>(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>', \<lambda>x. None, Some C) (U\<^sub>e\<^sub>r', \<F>', \<M>'', Some D)\<close>
      rtranclp_ord_res_5_preserves_invars by metis

  hence \<M>''_spec:
    "dom \<M>'' = ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D"
    "\<forall>A C. \<M>'' A = Some C \<longrightarrow> A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
    "\<forall>C A. C \<prec>\<^sub>c D \<longrightarrow> A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C \<longrightarrow> \<M>'' A = Some C"
    unfolding ord_res_5_invars_def
    unfolding model_eq_interp_upto_next_clause_def atoms_in_model_were_produced_def
      all_produced_atoms_in_model_def
    by metis+

  have "\<M>' = \<M>''"
  proof (cases "D = {#}")
    case True
    have "\<M>' = Map.empty"
    proof -
      have "\<nexists>K. ord_res.is_maximal_lit K D \<and> A \<prec>\<^sub>t atm_of K" for A
        unfolding \<open>D = {#}\<close>
        by (simp add: linorder_lit.is_maximal_in_mset_iff)
      hence "{A. \<exists>K. ord_res.is_maximal_lit K D \<and> A \<prec>\<^sub>t atm_of K} = {}"
        by simp
      thus ?thesis
        unfolding \<M>'_def by auto
    qed

    also have "Map.empty = \<M>''"
    proof -
      have "ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D = {}"
        unfolding \<open>D = {#}\<close> by simp
      thus ?thesis
        using \<M>''_spec(1) by simp
    qed

    finally show ?thesis .
  next
    case False
    then obtain K where "ord_res.is_maximal_lit K D"
      using linorder_lit.ex_maximal_in_mset by metis
    hence "{A. \<exists>K. ord_res.is_maximal_lit K D \<and> A \<prec>\<^sub>t atm_of K} = {A. A \<prec>\<^sub>t atm_of K}"
      by (metis (no_types, lifting) linorder_lit.Uniq_is_maximal_in_mset the1_equality')
    hence \<M>'_def': "\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}"
      unfolding \<M>'_def by argo

    show ?thesis
    proof (intro ext)
      fix x
      have \<M>'_spec:
        "dom \<M>' = ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D"
        "\<forall>A C. \<M>' A = Some C \<longrightarrow> A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C"
        "\<forall>C A. C \<prec>\<^sub>c D \<longrightarrow> A \<in> ord_res.production (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r'))) C \<longrightarrow> \<M>' A = Some C"
        using invars
        unfolding ord_res_5_invars_def
        unfolding model_eq_interp_upto_next_clause_def atoms_in_model_were_produced_def
          all_produced_atoms_in_model_def
        by metis+

      have "dom \<M>' = dom \<M>''"
        using \<M>'_spec(1) \<M>''_spec(1) by argo

      moreover have "\<forall>A C. \<M>' A = Some C \<longleftrightarrow> \<M>'' A = Some C"
        using \<M>'_spec(2) \<M>''_spec(2)
        by (smt (verit, del_insts) calculation domD domI linorder_cls.less_irrefl linorder_cls.neqE
            ord_res.less_trm_iff_less_cls_if_mem_production)

      ultimately show "\<M>' x = \<M>'' x"
        by (metis domD domIff)
    qed
  qed

  thus ?thesis
    using \<open>(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>', Map.empty, Some C) (U\<^sub>e\<^sub>r', \<F>', \<M>'', Some D)\<close> by argo
qed

end

end