theory Implicit_Exhaustive_Factorization
  imports
    Exhaustive_Factorization
    Exhaustive_Resolution
begin

section \<open>Function for implicit full factorization\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition iefac where
  "iefac \<F> C = (if C |\<in>| \<F> then efac C else C)"

lemma iefac_mempty[simp]:
  fixes \<F> :: "'f gclause fset"
  shows "iefac \<F> {#} = {#}"
  by (metis efac_mempty iefac_def)

lemma fset_mset_iefac[simp]: 
  fixes \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "fset_mset (iefac \<F> C) = fset_mset C"
proof (cases "C |\<in>| \<F>")
  case True
  hence "iefac \<F> C = efac C"
    unfolding iefac_def by simp
  thus ?thesis
    by auto
next
  case False
  hence "iefac \<F> C = C"
    unfolding iefac_def by simp
  thus ?thesis by simp
qed

lemma atms_of_cls_iefac[simp]:
  fixes \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "atms_of_cls (iefac \<F> C) = atms_of_cls C"
  by (simp add: atms_of_cls_def)

lemma iefac_le:
  fixes \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "iefac \<F> C \<preceq>\<^sub>c C"
  by (metis efac_subset iefac_def reflclp_iff subset_implies_reflclp_multp)

lemma true_cls_iefac_iff[simp]:
  fixes \<I> :: "'f gterm set" and \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "\<I> \<TTurnstile> iefac \<F> C \<longleftrightarrow> \<I> \<TTurnstile> C"
  by (metis iefac_def true_cls_efac_iff)

(*
ifac |`| (N |\<union>| U\<^sub>e\<^sub>r) |\<subseteq>| (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = (ifac |`| (N |\<union>| U\<^sub>e\<^sub>r)) |\<union>| N |\<union>| U\<^sub>e\<^sub>r
*)
lemma funion_funion_eq_funion_funion_fimage_iefac_if:
  assumes U\<^sub>e\<^sub>f_eq: "U\<^sub>e\<^sub>f = iefac \<F> |`| {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|}"
  shows "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f = N |\<union>| U\<^sub>e\<^sub>r |\<union>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
proof (intro fsubset_antisym fsubsetI)
  fix C :: "'f gterm clause"
  assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  hence "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<or> C |\<in>| U\<^sub>e\<^sub>f"
    by simp
  thus "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
  proof (elim disjE)
    assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    thus ?thesis
      by simp
  next
    assume "C |\<in>| U\<^sub>e\<^sub>f"
    hence "C |\<in>| iefac \<F> |`| {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|}"
      using U\<^sub>e\<^sub>f_eq by argo
    then obtain C\<^sub>0 :: "'f gterm clause" where
      "C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac \<F> C\<^sub>0 \<noteq> C\<^sub>0" and "C = iefac \<F> C\<^sub>0"
      by auto
    thus ?thesis
      by simp
  qed
next
  fix C :: "'f gterm clause"
  assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
  hence "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<or> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    by simp
  thus "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (elim disjE)
    assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    thus ?thesis
      by simp
  next
    assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    then obtain C\<^sub>0 :: "'f gterm clause" where
      "C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "C = iefac \<F> C\<^sub>0"
      by auto

    show ?thesis
    proof (cases "iefac \<F> C\<^sub>0 = C\<^sub>0")
      case True
      hence "C = C\<^sub>0"
        using \<open>C = iefac \<F> C\<^sub>0\<close> by argo
      thus ?thesis
        using \<open>C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by simp
    next
      case False
      hence "C |\<in>| U\<^sub>e\<^sub>f"
        unfolding U\<^sub>e\<^sub>f_eq
        using \<open>C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> \<open>C = iefac \<F> C\<^sub>0\<close> by simp
      thus ?thesis
        by simp
    qed
  qed
qed


lemma clauses_for_iefac_are_unproductive:
  "\<forall>C |\<in>| N |-| iefac \<F> |`| N. \<forall>U. ord_res.production U C = {}"
proof (intro ballI allI)
  fix C U
  assume "C |\<in>| N |-| iefac \<F> |`| N"
  hence "C |\<in>| N" and "C |\<notin>| iefac \<F> |`| N"
    by simp_all
  hence "iefac \<F> C \<noteq> C"
    by (metis fimage_iff)
  hence "efac C \<noteq> C"
    by (metis iefac_def)
  hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
    using nex_strictly_maximal_pos_lit_if_neq_efac by metis
  thus "ord_res.production U C = {}"
    using unproductive_if_nex_strictly_maximal_pos_lit by metis
qed

lemma clauses_for_iefac_have_smaller_entailing_clause:
  "\<forall>C |\<in>| N |-| iefac \<F> |`| N. \<exists>D |\<in>| iefac \<F> |`| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
proof (intro ballI allI)
  fix C
  assume "C |\<in>| N |-| iefac \<F> |`| N"
  hence "C |\<in>| N" and "C |\<notin>| iefac \<F> |`| N"
    by simp_all
  hence "iefac \<F> C \<noteq> C"
    by (metis fimage_iff)
  hence "efac C \<noteq> C"
    by (metis iefac_def)

  show "\<exists>D |\<in>| iefac \<F> |`| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  proof (intro bexI conjI)
    show "efac C \<prec>\<^sub>c C" and "{efac C} \<TTurnstile>e {C}"
      using efac_properties_if_not_ident[OF \<open>efac C \<noteq> C\<close>] by simp_all
  next
    show "efac C |\<in>| iefac \<F> |`| N"
      using \<open>C |\<in>| N\<close> \<open>iefac \<F> C \<noteq> C\<close> by (metis fimageI iefac_def)
  qed
qed

lemma is_least_false_clause_with_iefac_conv:
  "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) =
    is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
  using is_least_false_clause_funion_cancel_right_strong[OF clauses_for_iefac_are_unproductive
    clauses_for_iefac_have_smaller_entailing_clause]
  by (simp add: sup_commute)

lemma MAGIC4:
  fixes N \<F> \<F>' U\<^sub>e\<^sub>r U\<^sub>e\<^sub>r'
  defines
    "N1 \<equiv> iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    "N2 \<equiv> iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r')"
  assumes
    subsets_agree: "{|x |\<in>| N1. x \<prec>\<^sub>c C|} = {|x |\<in>| N2. x \<prec>\<^sub>c C|}" and
    "is_least_false_clause N1 D" and
    "is_least_false_clause N2 E" and
    "C \<prec>\<^sub>c D"
  shows "C \<preceq>\<^sub>c E"
proof -
  have "\<not> E \<prec>\<^sub>c C"
  proof (rule notI)
    assume "E \<prec>\<^sub>c C"

    have "is_least_false_clause N2 E \<longleftrightarrow> is_least_false_clause {|x |\<in>| N2. x \<preceq>\<^sub>c E|} E"
    proof (rule is_least_false_clause_swap_swap_compatible_fsets)
      show "{|x |\<in>| N2. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|} = {|x |\<in>| {|x |\<in>| N2. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}"
        using \<open>E \<prec>\<^sub>c C\<close> by force
    qed

    also have "\<dots> \<longleftrightarrow> is_least_false_clause {|x |\<in>| N1. x \<preceq>\<^sub>c E|} E"
    proof (rule is_least_false_clause_swap_swap_compatible_fsets)
      show "{|x |\<in>| {|x |\<in>| N2. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|} =
        {|x |\<in>| {|x |\<in>| N1. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}"
        using subsets_agree \<open>E \<prec>\<^sub>c C\<close> by fastforce
    qed

    also have "\<dots> \<longleftrightarrow> is_least_false_clause N1 E"
    proof (rule is_least_false_clause_swap_swap_compatible_fsets)
      show "{|x |\<in>| {|x |\<in>| N1. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|} = {|x |\<in>| N1. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x E|}"
        using \<open>E \<prec>\<^sub>c C\<close> by fastforce
    qed

    finally have "is_least_false_clause N1 E"
      using \<open>is_least_false_clause N2 E\<close> by argo

    hence "D = E"
      using \<open>is_least_false_clause N1 D\<close>
      by (metis Uniq_is_least_false_clause the1_equality')

    thus False
      using \<open>E \<prec>\<^sub>c C\<close> \<open>C \<prec>\<^sub>c D\<close> by order
  qed
  thus "C \<preceq>\<^sub>c E"
    by order
qed

lemma atms_of_clss_fimage_iefac[simp]:
  "atms_of_clss (iefac \<F> |`| N) = atms_of_clss N"
proof -
  have "atms_of_clss (iefac \<F> |`| N) = ffUnion (atms_of_cls |`| iefac \<F> |`| N)"
    unfolding atms_of_clss_def ..

  also have "\<dots> = ffUnion ((atms_of_cls \<circ> iefac \<F>) |`| N)"
    by simp

  also have "\<dots> = ffUnion (atms_of_cls |`| N)"
    unfolding comp_def atms_of_cls_iefac ..

  also have "\<dots> = atms_of_clss N"
    unfolding atms_of_clss_def ..

  finally show ?thesis .
qed

lemma atm_of_in_atms_of_clssI:
  assumes L_in: "L \<in># C" and C_in: "C |\<in>| iefac \<F> |`| N"
  shows "atm_of L |\<in>| atms_of_clss N"
proof -
  have "atm_of L |\<in>| atms_of_cls C"
    unfolding atms_of_cls_def
    using L_in by simp

  hence "atm_of L |\<in>| atms_of_clss (iefac \<F> |`| N)"
    unfolding atms_of_clss_def
    using C_in by (metis fmember_ffUnion_iff)

  thus "atm_of L |\<in>| atms_of_clss N"
    by simp
qed

lemma clause_almost_almost_definedI:
  fixes \<Gamma> D K
  assumes
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    D_max_lit: "ord_res.is_maximal_lit K D" and
    no_undef_atm: "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
  shows "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
  unfolding trail_defined_cls_def
proof (intro ballI)
  have "K \<in># D" and lit_in_D_le_K: "\<And>L. L \<in># D \<Longrightarrow> L \<preceq>\<^sub>l K"
    using D_max_lit
    unfolding atomize_imp atomize_all atomize_conj linorder_lit.is_maximal_in_mset_iff
    using linorder_lit.leI by blast

  fix L :: "'f gterm literal"
  assume "L \<in># {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"

  hence "L \<in># D" and "L \<noteq> K" and "L \<noteq> - K"
    by simp_all

  have "atm_of L |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<open>L \<in># D\<close> D_in by (metis atm_of_in_atms_of_clssI)

  hence "atm_of L \<prec>\<^sub>t atm_of K \<Longrightarrow> atm_of L |\<in>| trail_atms \<Gamma>"
    using no_undef_atm by metis

  moreover have "atm_of L \<prec>\<^sub>t atm_of K"
    using lit_in_D_le_K[OF \<open>L \<in># D\<close>] \<open>L \<noteq> K\<close> \<open>L \<noteq> - K\<close>
    by (cases L; cases K) simp_all

  ultimately show "trail_defined_lit \<Gamma> L"
    using trail_defined_lit_iff_trail_defined_atm by auto
qed

lemma clause_almost_definedI:
  fixes \<Gamma> D K
  assumes
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    D_max_lit: "ord_res.is_maximal_lit K D" and
    no_undef_atm: "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)" and
    K_defined: "trail_defined_lit \<Gamma> K"
  shows "trail_defined_cls \<Gamma> {#Ka \<in># D. Ka \<noteq> K#}"
  using clause_almost_almost_definedI[OF D_in D_max_lit no_undef_atm]
  using K_defined
  unfolding trail_defined_cls_def trail_defined_lit_def
  by (metis (mono_tags, lifting) mem_Collect_eq set_mset_filter uminus_lit_swap)

lemma eres_not_in_known_clauses_if_trail_false_cls:
  fixes
    \<F> :: "'f gclause fset" and
    \<Gamma> :: "('f gliteral \<times> 'f gclause option) list"
  assumes
    \<Gamma>_consistent: "trail_consistent \<Gamma>" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    "eres D E \<prec>\<^sub>c E" and
    "trail_false_cls \<Gamma> (eres D E)"
  shows "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
proof (rule notI)
  have "iefac \<F> (eres D E) \<preceq>\<^sub>c eres D E"
    using iefac_le by metis
  hence "iefac \<F> (eres D E) \<prec>\<^sub>c E"
    using \<open>eres D E \<prec>\<^sub>c E\<close> by order

  moreover assume "eres D E |\<in>| N |\<union>| U\<^sub>e\<^sub>r"

  ultimately have "trail_true_cls \<Gamma> (iefac \<F> (eres D E))"
    using clauses_lt_E_true[rule_format, of "iefac \<F> (eres D E)"]
    by (simp add: iefac_def linorder_lit.is_maximal_in_mset_iff)

  hence "trail_true_cls \<Gamma> (eres D E)"
    unfolding trail_true_cls_def
    by (metis fset_fset_mset fset_mset_iefac)

  thus False
    using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> (eres D E)\<close>
    by (metis not_trail_true_cls_and_trail_false_cls)
qed

lemma no_undefined_atom_le_max_lit_of_false_clause:
  assumes
    \<Gamma>_lower_set: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    D_false: "trail_false_cls \<Gamma> D" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D L"
  shows "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<preceq>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)"
proof -
  have "trail_false_lit \<Gamma> L"
    using D_false D_max_lit
    unfolding trail_false_cls_def linorder_lit.is_maximal_in_mset_iff by simp

  hence "trail_defined_lit \<Gamma> L"
    unfolding trail_false_lit_def trail_defined_lit_def by argo

  hence "atm_of L |\<in>| trail_atms \<Gamma>"
    unfolding trail_defined_lit_iff_trail_defined_atm .

  thus ?thesis
    using \<Gamma>_lower_set
    using linorder_trm.not_in_lower_setI by blast
qed

lemma trail_defined_if_no_undef_atom_le_max_lit:
  assumes
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_max_lit: "linorder_lit.is_maximal_in_mset C K" and
    no_undef_atom_le_K:
      "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<preceq>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
  shows "trail_defined_cls \<Gamma> C"
proof -

  have "\<And>x. x \<in># C \<Longrightarrow> atm_of x \<preceq>\<^sub>t atm_of K"
    using C_in C_max_lit
    unfolding linorder_lit.is_maximal_in_mset_iff
    by (metis linorder_trm.le_cases linorder_trm.le_less_linear literal.exhaust_sel
        ord_res.less_lit_simps(1) ord_res.less_lit_simps(2) ord_res.less_lit_simps(3)
        ord_res.less_lit_simps(4))

  hence "\<And>x. x \<in># C \<Longrightarrow> trail_defined_lit \<Gamma> x"
    using C_in no_undef_atom_le_K
    by (meson atm_of_in_atms_of_clssI trail_defined_lit_iff_trail_defined_atm)

  thus "trail_defined_cls \<Gamma> C"
    unfolding trail_defined_cls_def
    by metis
qed

lemma no_undef_atom_le_max_lit_if_lt_false_clause:
  assumes
    \<Gamma>_lower_set: "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    D_false: "trail_false_cls \<Gamma> D" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_max_lit: "linorder_lit.is_maximal_in_mset C K" and
    C_lt: "C \<prec>\<^sub>c D"
  shows "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<preceq>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
proof -
  have "K \<preceq>\<^sub>l L"
    using C_lt C_max_lit D_max_lit
    using linorder_cls.less_imp_not_less linorder_lit.multp_if_maximal_less_that_maximal
      linorder_lit.nle_le by blast

  hence "atm_of K \<preceq>\<^sub>t atm_of L"
    by (cases K; cases L) simp_all

  thus "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<preceq>\<^sub>t atm_of K \<and> A |\<notin>| trail_atms \<Gamma>)"
    using no_undefined_atom_le_max_lit_of_false_clause[OF assms(1,2,3,4)]
    by fastforce
qed

lemma bex_trail_false_cls_simp:
  fixes \<F> N \<Gamma>
  shows "fBex (iefac \<F> |`| N) (trail_false_cls \<Gamma>) \<longleftrightarrow> fBex N (trail_false_cls \<Gamma>)"
proof (rule iffI ; elim bexE)
  fix C :: "'f gclause"
  assume C_in: "C |\<in>| iefac \<F> |`| N" and C_false: "trail_false_cls \<Gamma> C"
  thus "fBex N (trail_false_cls \<Gamma>)"
    by (smt (verit, ccfv_SIG) fimage_iff iefac_def set_mset_efac trail_false_cls_def)
next
  fix C :: "'f gclause"
  assume "C |\<in>| N" and "trail_false_cls \<Gamma> C"
  thus "fBex (iefac \<F> |`| N) (trail_false_cls \<Gamma>)"
    by (metis fimageI iefac_def set_mset_efac trail_false_cls_def)
qed

end

end