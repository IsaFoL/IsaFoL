theory Exhaustive_Factorization
  imports Background
begin

section \<open>Function for full factorization\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition efac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "efac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

text \<open>The function \<^const>\<open>efac\<close> performs exhaustive factorization of its input clause.\<close>

lemma ex1_efac_eq_factoring_chain:
  "\<exists>!C'. efac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
proof -
  have "right_unique (\<lambda>x y. ord_res.ground_factoring\<^sup>*\<^sup>* x y \<and> (\<nexists>z. ord_res.ground_factoring y z))"
    using ord_res.unique_ground_factoring right_unique_terminating_rtranclp right_unique_iff
    by blast

  moreover obtain C' where "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex_terminating_rtranclp[OF ord_res.termination_ground_factoring]
    by metis

  ultimately have "efac C = C'"
    by (simp add: efac_def right_unique_def the_equality)

  then show ?thesis
    using \<open>ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')\<close> by blast
qed

lemma efac_eq_disj:
  "efac C = C \<or> (\<exists>!C'. efac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"
  using ex1_efac_eq_factoring_chain
  by (metis is_pos_def)

lemma member_mset_if_count_eq_Suc: "count X x = Suc n \<Longrightarrow> x \<in># X"
  by (simp add: count_inI)

lemmas member_fsetE = mset_add

lemma ord_res_ground_factoring_iff: "ord_res.ground_factoring C C' \<longleftrightarrow>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and> C' = C - {#Pos A#}))"
proof (rule iffI)
  assume "ord_res.ground_factoring C C'"
  thus "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and> C' = C - {#Pos A#})"
  proof (cases C C' rule: ord_res.ground_factoring.cases)
    case (ground_factoringI A P')
    show ?thesis
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (Pos A) C"
        using \<open>ord_res.is_maximal_lit (Pos A) C\<close> .
    next
      show "count C (Pos A) = Suc (Suc (count P' (Pos A)))"
        unfolding \<open>C = add_mset (Pos A) (add_mset (Pos A) P')\<close> by simp
    next
      show "C' = remove1_mset (Pos A) C"
        unfolding \<open>C = add_mset (Pos A) (add_mset (Pos A) P')\<close> \<open>C' = add_mset (Pos A) P'\<close> by simp
    qed
  qed
next
  assume "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and>
    (\<exists>n. count C (Pos A) = Suc (Suc n) \<and> C' = C - {#Pos A#})"
  then obtain A n where
    "ord_res.is_maximal_lit (Pos A) C" and
    "count C (Pos A) = Suc (Suc n)" and
    "C' = C - {#Pos A#}"
    by metis

  have "Pos A \<in># C"
    using \<open>count C (Pos A) = Suc (Suc n)\<close> member_mset_if_count_eq_Suc by metis
  then obtain C'' where "C = add_mset (Pos A) C''"
    by (auto elim: member_fsetE)
  with \<open>count C (Pos A) = Suc (Suc n)\<close> have "count C'' (Pos A) = Suc n"
    by simp
  hence "Pos A \<in># C''"
    using member_mset_if_count_eq_Suc by metis
  then obtain C''' where "C'' = add_mset (Pos A) C'''"
    by (auto elim: member_fsetE)

  show "ord_res.ground_factoring C C'"
  proof (rule ord_res.ground_factoringI)
    show "C = add_mset (Pos A) (add_mset (Pos A) C''')"
      using \<open>C = add_mset (Pos A) C''\<close> \<open>C'' = add_mset (Pos A) C'''\<close> by metis
  next
    show "ord_res.is_maximal_lit (Pos A) C"
      using \<open>ord_res.is_maximal_lit (Pos A) C\<close> .
  next
    show "C' = add_mset (Pos A) C'''"
      using \<open>C' = C - {#Pos A#}\<close> \<open>C = add_mset (Pos A) C''\<close> \<open>C'' = add_mset (Pos A) C'''\<close> by simp
  qed simp_all
qed

lemma tranclp_ord_res_ground_factoring_iff:
  "ord_res.ground_factoring\<^sup>+\<^sup>+ C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'') \<longleftrightarrow>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and>
    C' = C - replicate_mset (Suc n) (Pos A)))"
proof (intro iffI; elim exE conjE)
  assume "ord_res.ground_factoring\<^sup>+\<^sup>+ C C'" and "(\<nexists>C''. ord_res.ground_factoring C' C'')"
  then show "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and>
    C' = C - replicate_mset (Suc n) (Pos A))"
  proof (induction C rule: converse_tranclp_induct)
    case (base C)
    from base.hyps obtain A n where
      "ord_res.is_maximal_lit (Pos A) C" and
      "count C (Pos A) = Suc (Suc n)" and
      "C' = remove1_mset (Pos A) C"
      unfolding ord_res_ground_factoring_iff by auto

    moreover have "n = 0"
    proof (rule ccontr)
      assume "n \<noteq> 0"
      then obtain C'' where "C' = add_mset (Pos A) (add_mset (Pos A) C'')"
        by (metis (no_types, lifting) Zero_not_Suc calculation(2,3) count_add_mset count_inI
            diff_Suc_1 insert_DiffM)
      hence "ord_res.ground_factoring C' (add_mset (Pos A) C'')"
        using ord_res.ground_factoringI
        by (metis calculation(1,3) linorder_lit.is_maximal_in_mset_iff more_than_one_mset_mset_diff
            union_single_eq_member)
      with base.prems show False
        by metis
    qed

    ultimately show ?case
      by (metis replicate_mset_0 replicate_mset_Suc)
  next
    case (step C C'')
    from step.IH step.prems obtain A n where
      "ord_res.is_maximal_lit (Pos A) C''" and
      "count C'' (Pos A) = Suc (Suc n)" and
      "C' = C'' - replicate_mset (Suc n) (Pos A)"
      by metis

    from step.hyps(1) obtain A' m where
      "ord_res.is_maximal_lit (Pos A') C" and
      "count C (Pos A') = Suc (Suc m)" and
      "C'' = remove1_mset (Pos A') C"
      unfolding ord_res_ground_factoring_iff by metis

    have "A' = A"
      using \<open>ord_res.is_maximal_lit (Pos A) C''\<close> \<open>ord_res.is_maximal_lit (Pos A') C\<close>
      by (metis \<open>C'' = remove1_mset (Pos A') C\<close> \<open>count C (Pos A') = Suc (Suc m)\<close>
          add_mset_remove_trivial_eq count_add_mset count_greater_zero_iff diff_Suc_1
          linorder_lit.antisym_conv3 linorder_lit.is_maximal_in_mset_iff literal.inject(1)
          zero_less_Suc)

    have "m = Suc n"
      using \<open>count C'' (Pos A) = Suc (Suc n)\<close> \<open>count C (Pos A') = Suc (Suc m)\<close>
      unfolding \<open>C'' = remove1_mset (Pos A') C\<close> \<open>A' = A\<close>
      by simp

    show ?case
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (Pos A) C"
        using \<open>ord_res.is_maximal_lit (Pos A') C\<close> \<open>A' = A\<close> by metis
    next
      show "count C (Pos A) = Suc (Suc m)"
        using \<open>count C (Pos A') = Suc (Suc m)\<close> \<open>A' = A\<close> by metis
    next
      show "C' = C - replicate_mset (Suc m) (Pos A)"
        unfolding \<open>C' = C'' - replicate_mset (Suc n) (Pos A)\<close> \<open>C'' = remove1_mset (Pos A') C\<close>
          \<open>A' = A\<close> \<open>m = Suc n\<close>
        by simp
    qed
  qed
next
  fix A n assume "ord_res.is_maximal_lit (Pos A) C"
  thus "count C (Pos A) = Suc (Suc n) \<Longrightarrow> C' = C - replicate_mset (Suc n) (Pos A) \<Longrightarrow>
    ord_res.ground_factoring\<^sup>+\<^sup>+ C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
  proof (induction n arbitrary: C)
    case 0
    hence "(ord_res.is_maximal_lit (Pos A) C \<and>
         (count C (Pos A) = Suc (Suc 0) \<and>
              C' = remove1_mset (Pos A) C))"
      by (metis replicate_mset_0 replicate_mset_Suc)
    hence "ord_res.ground_factoring C C' \<and> (\<nexists>a. ord_res.ground_factoring C' a)"
      unfolding ord_res_ground_factoring_iff
      by (metis Zero_not_Suc add_mset_remove_trivial_eq count_add_mset count_inI
          linorder_lit.antisym_conv3 linorder_lit.is_maximal_in_mset_iff nat.inject)
    thus ?case
      by blast
  next
    case (Suc n)
    have "ord_res.ground_factoring\<^sup>+\<^sup>+ (C - {#Pos A#}) C' \<and> (\<nexists>a. ord_res.ground_factoring C' a)"
    proof (rule Suc.IH)
      show "count (remove1_mset (Pos A) C) (Pos A) = Suc (Suc n)"
        using Suc.prems by simp
    next
      show "C' = remove1_mset (Pos A) C - replicate_mset (Suc n) (Pos A)"
        using Suc.prems by simp
    next
      show "ord_res.is_maximal_lit (Pos A) (remove1_mset (Pos A) C)"
        using Suc.prems
        by (smt (verit, ccfv_SIG) Zero_not_Suc add_diff_cancel_left' add_mset_remove_trivial_eq
            count_add_mset count_inI linorder_lit.is_maximal_in_mset_iff plus_1_eq_Suc)
    qed

    moreover have "ord_res.ground_factoring C (C - {#Pos A#})"
      unfolding ord_res_ground_factoring_iff
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (Pos A) C"
        using Suc.prems by metis
    next
      show "count C (Pos A) = Suc (Suc (Suc n))"
        using Suc.prems by metis
    next
      show "remove1_mset (Pos A) C = remove1_mset (Pos A) C" ..
    qed

    ultimately show ?case
      by auto
  qed
qed

lemma minus_mset_replicate_mset_eq_add_mset_filter_mset:
  assumes "count X x = Suc n"
  shows "X - replicate_mset n x = add_mset x {#y \<in># X. y \<noteq> x#}"
  using assms
  by (metis add_diff_cancel_left' add_mset_diff_bothsides filter_mset_eq filter_mset_neq
      multiset_partition replicate_mset_Suc union_mset_add_mset_right)

lemma minus_mset_replicate_mset_eq_add_mset_add_mset_filter_mset:
  assumes "count X x = Suc (Suc n)"
  shows "X - replicate_mset n x = add_mset x (add_mset x {#y \<in># X. y \<noteq> x#})"
  using assms
  by (metis add_diff_cancel_left' add_mset_diff_bothsides filter_mset_eq filter_mset_neq
      multiset_partition replicate_mset_Suc union_mset_add_mset_right)

lemma rtrancl_ground_factoring_iff:
  shows "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'') \<longleftrightarrow>
  ((\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> count C (Pos A) \<ge> 2) \<and> C = C' \<or>
   (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}))"
proof (intro iffI; elim exE conjE disjE)
  show "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<Longrightarrow> \<nexists>C''. ord_res.ground_factoring C' C'' \<Longrightarrow>
    (\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> 2 \<le> count C (Pos A)) \<and> C = C' \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
  proof (induction C rule: converse_rtranclp_induct)
    case base
    thus ?case
      by (metis add_2_eq_Suc le_Suc_ex ord_res_ground_factoring_iff)
  next
    case (step y z)
    hence "ord_res.ground_factoring\<^sup>+\<^sup>+ y C' \<and> (\<nexists>x. ord_res.ground_factoring C' x)"
      by simp
    thus ?case
      unfolding tranclp_ord_res_ground_factoring_iff
      by (metis minus_mset_replicate_mset_eq_add_mset_filter_mset)
  qed
next
  assume "\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> 2 \<le> count C (Pos A)" and "C = C'"
  thus "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    by (metis One_nat_def Suc_1 Suc_le_eq Suc_le_mono ord_res_ground_factoring_iff
        rtranclp.rtrancl_refl zero_less_Suc)
next
  fix A assume "ord_res.is_maximal_lit (Pos A) C"
  then obtain n where "count C (Pos A) = Suc n"
    by (meson in_countE linorder_lit.is_maximal_in_mset_iff)
  with \<open>ord_res.is_maximal_lit (Pos A) C\<close> show "C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#} \<Longrightarrow>
    ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
  proof (induction n arbitrary: C)
    case 0

    have "(\<nexists>a. ord_res.ground_factoring C a)"
    proof (intro notI, elim exE)
      fix D assume "ord_res.ground_factoring C D"
      thus False
      proof (cases rule: ord_res.ground_factoring.cases)
        case (ground_factoringI A' P')
        hence "A' = A"
          using \<open>ord_res.is_maximal_lit (Pos A) C\<close>
          using linorder_lit.Uniq_is_maximal_in_mset
          by (metis Uniq_D literal.inject(1))
        thus False
          using \<open>count C (Pos A) = Suc 0\<close> \<open>C = add_mset (Pos A') (add_mset (Pos A') P')\<close> by simp
      qed
    qed
    thus ?case
      by (metis "0.prems"(1) "0.prems"(3) diff_zero
          minus_mset_replicate_mset_eq_add_mset_filter_mset replicate_mset_0 rtranclp.rtrancl_refl)
  next
    case (Suc x)
    then show ?case
      by (metis minus_mset_replicate_mset_eq_add_mset_filter_mset tranclp_into_rtranclp
          tranclp_ord_res_ground_factoring_iff)
  qed
qed

lemma efac_spec: "efac C = C \<or>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
  using efac_eq_disj[of C]
proof (elim disjE)
  assume "efac C = C"
  thus "efac C = C \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
    by metis
next
  assume "\<exists>!C'. efac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and>
    (\<nexists>C''. ord_res.ground_factoring C' C'')"
  then obtain C' where
    "efac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    by metis
  thus "efac C = C \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
    unfolding rtrancl_ground_factoring_iff
    by metis
qed

lemma efac_spec_if_pos_lit_is_maximal:
  assumes L_pos: "is_pos L" and L_max: "ord_res.is_maximal_lit L C"
  shows "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
proof -
  from assms obtain C' where
    "efac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex1_efac_eq_factoring_chain by metis
  thus ?thesis
    unfolding rtrancl_ground_factoring_iff
  proof (elim disjE conjE)
    assume hyps: "\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> 2 \<le> count C (Pos A)" "C = C'"
    with assms have "count C L = 1"
      by (metis One_nat_def in_countE is_pos_def le_less_linear less_2_cases_iff
          linorder_lit.is_maximal_in_mset_iff nat_less_le zero_less_Suc)
    hence "C = add_mset L {#K \<in># C. K \<noteq> L#}"
      by (metis One_nat_def diff_zero minus_mset_replicate_mset_eq_add_mset_filter_mset
          replicate_mset_0)
    thus "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      using \<open>efac C = C'\<close> \<open>C = C'\<close> by argo
  next
    assume "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
    thus "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      by (metis L_max Uniq_D \<open>efac C = C'\<close> linorder_lit.Uniq_is_maximal_in_mset)
  qed
qed

lemma efac_mempty[simp]: "efac {#} = {#}"
  by (metis empty_iff linorder_lit.is_maximal_in_mset_iff set_mset_empty efac_spec)

lemma set_mset_efac[simp]: "set_mset (efac C) = set_mset C"
  using efac_spec[of C]
proof (elim disjE exE conjE)
  show "efac C = C \<Longrightarrow> set_mset (efac C) = set_mset C"
    by simp
next
  fix A
  assume "ord_res.is_maximal_lit (Pos A) C"
  hence "Pos A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

  assume efac_C_eq: "efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
  show "set_mset (efac C) = set_mset C"
  proof (intro Set.subset_antisym Set.subsetI)
    fix L assume "L \<in># efac C"
    then show "L \<in># C"
      unfolding efac_C_eq
      using \<open>Pos A \<in># C\<close> by auto
  next
    fix L assume "L \<in># C"
    then show "L \<in># efac C"
      unfolding efac_C_eq
      by simp
  qed
qed

lemma efac_subset: "efac C \<subseteq># C"
  using efac_spec[of C]
proof (elim disjE exE conjE)
  show "efac C = C \<Longrightarrow> efac C \<subseteq># C"
    by simp
next
  fix A
  assume "ord_res.is_maximal_lit (Pos A) C" and
    efac_C_eq: "efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
  then show "efac C \<subseteq># C"
    by (smt (verit, ccfv_SIG) filter_mset_add_mset insert_DiffM insert_subset_eq_iff
        linorder_lit.is_maximal_in_mset_iff multiset_filter_subset)
qed

lemma true_cls_efac_iff[simp]:
  fixes \<I> :: "'f gterm set" and C :: "'f gclause"
  shows "\<I> \<TTurnstile> efac C \<longleftrightarrow> \<I> \<TTurnstile> C"
  by (metis set_mset_efac true_cls_iff_set_mset_eq)

lemma obtains_positive_greatest_lit_if_efac_not_ident:
  assumes "efac C \<noteq> C"
  obtains L where "is_pos L" and "linorder_lit.is_greatest_in_mset (efac C) L"
proof -
  from \<open>efac C \<noteq> C\<close> obtain A where
    Pos_A_maximal: "linorder_lit.is_maximal_in_mset C (Pos A)" and
    efac_C_eq: "efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
    using efac_spec by metis

  assume hyp: "\<And>L. is_pos L \<Longrightarrow> linorder_lit.is_greatest_in_mset (efac C) L \<Longrightarrow> thesis"
  show thesis
  proof (rule hyp)
    show "is_pos (Pos A)"
      by simp
  next
    show "linorder_lit.is_greatest_in_mset(efac C) (Pos A)"
      unfolding efac_C_eq linorder_lit.is_greatest_in_mset_iff
      using Pos_A_maximal[unfolded linorder_lit.is_maximal_in_mset_iff]
      by auto
  qed
qed

lemma mempty_in_image_efac_iff[simp]: "{#} \<in> efac ` N \<longleftrightarrow> {#} \<in> N"
  by (metis empty_iff imageE image_eqI linorder_lit.is_maximal_in_mset_iff set_mset_empty set_mset_efac efac_spec)

lemma greatest_literal_in_efacI:
  assumes "is_pos L" and C_max_lit: "linorder_lit.is_maximal_in_mset C L"
  shows "linorder_lit.is_greatest_in_mset (efac C) L"
  unfolding efac_spec_if_pos_lit_is_maximal[OF assms] linorder_lit.is_greatest_in_mset_iff
proof (intro conjI ballI)
  show "L \<in># add_mset L {#K \<in># C. K \<noteq> L#}"
    by simp
next
  fix y :: "'f gterm literal"
  assume "y \<in># remove1_mset L (add_mset L {#K \<in># C. K \<noteq> L#})"
  then show "y \<prec>\<^sub>l L"
    using C_max_lit[unfolded linorder_lit.is_maximal_in_mset_iff]
    by  auto
qed

lemma "linorder_lit.is_maximal_in_mset (efac C) L \<longleftrightarrow> linorder_lit.is_maximal_in_mset C L"
  by (simp add: linorder_lit.is_maximal_in_mset_iff)

lemma
  assumes "is_pos L"
  shows "linorder_lit.is_greatest_in_mset (efac C) L \<longleftrightarrow> linorder_lit.is_maximal_in_mset C L"
  by (metis (no_types, opaque_lifting) Uniq_D assms efac_spec greatest_literal_in_efacI
      linorder_lit.Uniq_is_greatest_in_mset linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
      literal.disc(1))

lemma factorizable_if_neq_efac:
  assumes "C \<noteq> efac C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
  using assms
  by (metis converse_rtranclpE ex1_efac_eq_factoring_chain)

lemma nex_strictly_maximal_pos_lit_if_neq_efac:
  assumes "C \<noteq> efac C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms factorizable_if_neq_efac nex_strictly_maximal_pos_lit_if_factorizable by metis

lemma efac_properties_if_not_ident:
  assumes "efac C \<noteq> C"
  shows "efac C \<prec>\<^sub>c C" and "{efac C} \<TTurnstile>e {C}"
proof -
  have "efac C \<subseteq># C"
    using efac_subset .
  hence "efac C \<preceq>\<^sub>c C"
    using subset_implies_reflclp_multp by blast
  thus "efac C \<prec>\<^sub>c C"
    using \<open>efac C \<noteq> C\<close> by order

  show "{efac C} \<TTurnstile>e {C}"
    using \<open>efac C \<subseteq># C\<close> true_clss_subclause by metis
qed

end

end