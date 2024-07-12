theory Implicit_Exhaustive_Factorization
  imports Exhaustive_Factorization
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

end

end