theory Simulation
  imports
    Background
begin

type_synonym ('f, 'v) scl_fol_sim_state =
  "('f, 'v) SCL_FOL.state \<times> nat \<times> 'f gterm clause \<times> ('f gterm clause \<Rightarrow> 'f gterm clause)"

type_synonym 'f gliteral = "'f gterm literal"
type_synonym 'f gclause = "'f gterm clause"

locale simulation_SCLFOL_ground_ordered_resolution =
  renaming_apart renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    finite_less_trm: "\<And>\<beta>. finite {x. x \<prec>\<^sub>t \<beta>}" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
begin

section \<open>Ground ordered resolution for ground terms\<close>

interpretation ord_res: ground_ordered_resolution_calculus "(\<prec>\<^sub>t)" "\<lambda>_. {#}"
  by unfold_locales auto

interpretation linorder_trm: linorder "(\<preceq>\<^sub>t)" "(\<prec>\<^sub>t)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>t y) = (x \<preceq>\<^sub>t y \<and> \<not> y \<preceq>\<^sub>t x)"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>t x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t z \<Longrightarrow> x \<preceq>\<^sub>t z"
    by (meson transpE transp_less_trm transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<or> y \<preceq>\<^sub>t x"
    by (metis reflclp_iff totalpD totalp_less_trm)
qed

interpretation linorder_lit: linorder "(\<preceq>\<^sub>l)" "(\<prec>\<^sub>l)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = (x \<preceq>\<^sub>l y \<and> \<not> y \<preceq>\<^sub>l x)"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>l x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l z \<Longrightarrow> x \<preceq>\<^sub>l z"
    by (meson transpE ord_res.transp_less_lit transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_lit)
qed

interpretation linorder_cls: linorder "(\<preceq>\<^sub>c)" "(\<prec>\<^sub>c)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = (x \<preceq>\<^sub>c y \<and> \<not> y \<preceq>\<^sub>c x)"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>c x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c z \<Longrightarrow> x \<preceq>\<^sub>c z"
    by (meson transpE ord_res.transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_cls)
qed

section \<open>Function for full factorization\<close>

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


section \<open>Lemmas about going between ground and first-order terms\<close>

lemma ex1_gterm_of_term:
  fixes t :: "'f gterm"
  shows "\<exists>!(t' :: ('f, 'v) term). ground t' \<and> t = gterm_of_term t'"
proof (rule ex1I)
  show "ground (term_of_gterm t) \<and> t = gterm_of_term (term_of_gterm t)"
    by simp
next
  fix t' :: "('f, 'v) term"
  show "ground t' \<and> t = gterm_of_term t' \<Longrightarrow> t' = term_of_gterm t"
    by (induction t') (simp_all add: map_idI)
qed

lemma binj_betw_gterm_of_term: "bij_betw gterm_of_term {t. ground t} UNIV"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on gterm_of_term {t. ground t}"
    by (metis gterm_of_term_inj mem_Collect_eq)
next
  show "gterm_of_term ` {t. ground t} = UNIV"
  proof (rule Set.subset_antisym)
    show "gterm_of_term ` {t. Term_Context.ground t} \<subseteq> UNIV"
      by simp
  next
    show "UNIV \<subseteq> gterm_of_term ` {t. Term_Context.ground t}"
      by (metis (mono_tags, opaque_lifting) ground_term_of_gterm image_iff mem_Collect_eq subsetI
          term_of_gterm_inv)
  qed
qed


section \<open>SCL(FOL) for first-order terms\<close>

definition less_B where
  "less_B x y \<longleftrightarrow> ground x \<and> ground y \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term y"

interpretation order_less_B: order "less_B\<^sup>=\<^sup>=" less_B
  by unfold_locales (auto simp add: less_B_def)

interpretation scl_fol: scl_fol_calculus renaming_vars less_B
proof unfold_locales
  fix \<beta> :: "('f, 'v) term"

  have Collect_gterms_eq: "\<And>P. {y. P y} = gterm_of_term ` {t. ground t \<and> P (gterm_of_term t)}"
    using Collect_eq_image_filter_Collect_if_bij_betw[OF binj_betw_gterm_of_term subset_UNIV]
    by auto

  have "{t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>} = gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using Collect_gterms_eq[of "\<lambda>t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>"] .
  hence "finite (gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>})"
    using finite_less_trm[of "gterm_of_term \<beta>"] by metis
  moreover have "inj_on gterm_of_term {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    by (rule gterm_of_term_inj) simp
  ultimately have "finite {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using finite_imageD by blast
  thus "finite {x. less_B x \<beta>}"
    unfolding less_B_def
    using not_finite_existsD by force
qed


section \<open>Common definitions and lemmas\<close>

abbreviation ord_res_Interp where
  "ord_res_Interp N C \<equiv> ord_res.interp N C \<union> ord_res.production N C"

definition is_least_false_clause where
  "is_least_false_clause N C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"

lemma is_least_false_clause_finsert_smaller_false_clause:
  assumes
    D_least: "is_least_false_clause N D" and
    "C \<prec>\<^sub>c D" and
    C_false: "\<not> ord_res_Interp (fset (finsert C N)) C \<TTurnstile> C"
  shows "is_least_false_clause (finsert C N) C"
  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "C |\<in>| finsert C N"
    by simp
next
  show "\<not> ord_res_Interp (fset (finsert C N)) C \<TTurnstile> C"
    using assms by metis
next
  fix y
  assume "y |\<in>| finsert C N" and "y \<noteq> C" and y_false: "\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y"
  hence "y |\<in>| N"
    by simp

  have "\<not> (y \<prec>\<^sub>c C)"
  proof (rule notI)
    assume "y \<prec>\<^sub>c C"
    hence "ord_res_Interp (fset (finsert C N)) y = ord_res_Interp (fset N) y"
      using ord_res.Interp_insert_greater_clause by simp

    hence "\<not> ord_res_Interp (fset N) y \<TTurnstile> y"
      using y_false by argo

    moreover have "y \<prec>\<^sub>c D"
      using \<open>y \<prec>\<^sub>c C\<close> \<open>C \<prec>\<^sub>c D\<close> by order

    ultimately show False
      using D_least
      by (metis (mono_tags, lifting) \<open>y |\<in>| N\<close> linorder_cls.is_least_in_ffilter_iff
          linorder_cls.less_asym' is_least_false_clause_def)
  qed
  thus "C \<prec>\<^sub>c y"
    using \<open>y \<noteq> C\<close> by order
qed

lemma is_least_false_clause_swap_swap_compatible_fsets:
  assumes "{|x |\<in>| N1. x \<preceq>\<^sub>c C|} = {|x |\<in>| N2. x \<preceq>\<^sub>c C|}"
  shows "is_least_false_clause N1 C \<longleftrightarrow> is_least_false_clause N2 C"
proof -
  have "is_least_false_clause N2 C" if
    subsets_agree: "{|x |\<in>| N1. x \<preceq>\<^sub>c C|} = {|x |\<in>| N2. x \<preceq>\<^sub>c C|}" and
    C_least: "is_least_false_clause N1 C" for N1 N2 C
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    have "C |\<in>| N1"
      using C_least
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by argo
    thus "C |\<in>| N2"
      using subsets_agree by auto
  next
    have "\<not> ord_res_Interp (fset N1) C \<TTurnstile> C"
      using C_least
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by argo
    moreover have "ord_res_Interp (fset N1) C = ord_res_Interp (fset N2) C"
      using subsets_agree by (auto intro!: ord_res.Interp_swap_clause_set) 
    ultimately show "\<not> ord_res_Interp (fset N2) C \<TTurnstile> C"
      by argo
  next
    fix y assume "y |\<in>| N2" and "y \<noteq> C"
    show "\<not> ord_res_Interp (fset N2) y \<TTurnstile> y \<Longrightarrow> C \<prec>\<^sub>c y"
    proof (erule contrapos_np)
      assume "\<not> C \<prec>\<^sub>c y"
      hence "y \<preceq>\<^sub>c C"
        by order
      hence "y |\<in>| N1"
        using \<open>y |\<in>| N2\<close> using subsets_agree by auto
      hence "\<not> ord_res_Interp (fset N1) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
        using \<open>is_least_false_clause N1 C\<close> \<open>y \<noteq> C\<close>
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
        by metis
      moreover have "ord_res_Interp (fset N1) y = ord_res_Interp (fset N2) y"
      proof (rule ord_res.Interp_swap_clause_set)
        show "{D. D |\<in>| N1 \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D y} = {D. D |\<in>| N2 \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D y}"
          using subsets_agree \<open>y \<preceq>\<^sub>c C\<close> by fastforce
      qed simp_all
      ultimately show "ord_res_Interp (fset N2) y \<TTurnstile> y"
        using \<open>y \<preceq>\<^sub>c C\<close> by auto
    qed
  qed
  thus ?thesis
    using assms by metis
qed

lemma Uniq_is_least_false_clause: "\<exists>\<^sub>\<le>\<^sub>1 C. is_least_false_clause N C"
proof (rule Uniq_I)
  show "\<And>x y z. is_least_false_clause x y \<Longrightarrow> is_least_false_clause x z \<Longrightarrow> y = z"
    unfolding is_least_false_clause_def
    by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
qed

lemma mempty_lesseq_cls[simp]: "{#} \<preceq>\<^sub>c C" for C
  by (cases C) (simp_all add: strict_subset_implies_multp)

lemma is_least_false_clause_mempty: "{#} |\<in>| N \<Longrightarrow> is_least_false_clause N {#}"
  using is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff mempty_lesseq_cls
  by fastforce

definition ex_false_clause where
  "ex_false_clause N = (\<exists>C \<in> N. \<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C)"

lemma obtains_least_false_clause_if_ex_false_clause:
  assumes "ex_false_clause (fset N)"
  obtains C where "is_least_false_clause N C"
  using assms
  by (metis (mono_tags, lifting) bot_fset.rep_eq emptyE ex_false_clause_def ffmember_filter
      linorder_cls.ex_least_in_fset is_least_false_clause_def)

lemma ex_false_clause_if_least_false_clause:
  assumes "is_least_false_clause N C"
  shows "ex_false_clause (fset N)"
  using assms
  by (metis (no_types, lifting) ex_false_clause_def is_least_false_clause_def
      linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2))

lemma ex_false_clause_iff: "ex_false_clause (fset N) \<longleftrightarrow> (\<exists>C. is_least_false_clause N C)"
  using obtains_least_false_clause_if_ex_false_clause ex_false_clause_if_least_false_clause by metis

definition ord_res_model where
  "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"

lemma ord_res_model_eq_interp_union_production_of_greatest_clause:
  assumes C_greatest: "linorder_cls.is_greatest_in_set N C"
  shows "ord_res_model N = ord_res.interp N C \<union> ord_res.production N C"
proof -
  have "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"
    unfolding ord_res_model_def ..
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<preceq>\<^sub>c C}. ord_res.production N D)"
    using C_greatest linorder_cls.is_greatest_in_set_iff by auto
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<union> {C}. ord_res.production N D)"
    using C_greatest linorder_cls.is_greatest_in_set_iff by auto
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. ord_res.production N D) \<union> ord_res.production N C"
    by auto
  also have "\<dots> = ord_res.interp N C \<union> ord_res.production N C"
    unfolding ord_res.interp_def ..
  finally show ?thesis .
qed

lemma ord_res_model_entails_clauses_if_nex_false_clause:
  assumes "finite N" and "N \<noteq> {}" and "\<not> ex_false_clause N"
  shows "ord_res_model N \<TTurnstile>s N"
  unfolding true_clss_def
proof (intro ballI)
  from \<open>\<not> ex_false_clause N\<close> have ball_true:
    "\<forall>C \<in> N. ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    by (simp add: ex_false_clause_def)

  from \<open>finite N\<close> \<open>N \<noteq> {}\<close> obtain D where
    D_greatest: "linorder_cls.is_greatest_in_set N D"
    using linorder_cls.ex_greatest_in_set by metis

  fix C assume "C \<in> N"
  hence "ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    using ball_true by metis

  moreover have "C \<preceq>\<^sub>c D"
    using \<open>C \<in> N\<close> D_greatest[unfolded linorder_cls.is_greatest_in_set_iff] by auto

  ultimately have "ord_res.interp N D \<union> ord_res.production N D \<TTurnstile> C"
    using ord_res.entailed_clause_stays_entailed by auto

  thus "ord_res_model N \<TTurnstile> C"
    using ord_res_model_eq_interp_union_production_of_greatest_clause[OF D_greatest] by argo
qed


section \<open>ORD-RES-0\<close>

definition ord_res_final where
  "ord_res_final N \<longleftrightarrow> {#} |\<in>| N \<or> \<not> ex_false_clause (fset N)"

inductive ord_res where
  factoring: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    \<comment> \<open>Maybe write \<^term>\<open>\<not> ord_res_final N\<close> instead?\<close>
    P |\<in>| N \<Longrightarrow> ord_res.ground_factoring P C \<Longrightarrow>
    N' = finsert C N \<Longrightarrow>
    ord_res N N'" |

  resolution: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    P1 |\<in>| N \<Longrightarrow> P2 |\<in>| N \<Longrightarrow> ord_res.ground_resolution P1 P2 C \<Longrightarrow>
    N' = finsert C N \<Longrightarrow>
    ord_res N N'"

inductive ord_res_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_load N N"

interpretation ord_res_semantics: semantics where
  step = ord_res and
  final = ord_res_final
proof unfold_locales
  fix N :: "'f gterm clause fset"
  assume "ord_res_final N"
  thus "finished ord_res N"
    unfolding ord_res_final_def
  proof (elim disjE)
    show "{#} |\<in>| N \<Longrightarrow> finished ord_res N"
      by (simp add: finished_def ord_res.simps)
  next
    show "\<not> ex_false_clause (fset N) \<Longrightarrow> finished ord_res N"
      by (simp add: finished_def ord_res.simps)
  qed
qed

interpretation ord_res_language: language where
  step = ord_res and
  final = ord_res_final and
  load = ord_res_load
  by unfold_locales


section \<open>ORD-RES-1 (deterministic)\<close>

lemma pos_lit_not_greatest_if_maximal_in_least_false_clause:
  assumes
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C" and
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
  shows "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Pos A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

  from C_least have
    C_in: "C |\<in>| N" and
    C_false: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_lt: "\<forall>y |\<in>| N. y \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
    unfolding linorder_cls.is_least_in_ffilter_iff by auto

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> ord_res_Interp (fset N) C"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  have "{D \<in> fset N. D \<preceq>\<^sub>c C} = {D \<in> fset N. D \<prec>\<^sub>c C} \<union> {D \<in> fset N. D = C}"
    by fastforce
  with C_unproductive have
    "ord_res_Interp (fset N) C = ord_res.interp (fset N) C"
    by simp
  with C_false have C_false': "\<not> ord_res.interp (fset N) C \<TTurnstile> C"
    by simp

  from C_unproductive have "A \<notin> ord_res.production (fset N) C"
    by simp
  thus ?thesis
  proof (rule contrapos_nn)
    assume "ord_res.is_strictly_maximal_lit (Pos A) C"
    then show "A \<in> ord_res.production (fset N) C"
      unfolding ord_res.production_unfold[of "fset N" C] mem_Collect_eq
      using C_in C_def C_false'
      by metis
  qed
qed

lemma ex_ground_factoringI:
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C" and
    C_not_max_lit: "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
proof -
  from C_max_lit C_not_max_lit have "count C (Pos A) \<ge> 2"
    using linorder_lit.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset by metis
  then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
    by (metis two_le_countE)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_factoring C (add_mset (Pos A) C')"
      using ord_res.ground_factoringI[of C A C']
      using C_def C_max_lit by metis
  qed
qed

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

lemma bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit:
  assumes
    C_least_false: "is_least_false_clause N C" and
    Neg_A_max: "ord_res.is_maximal_lit (Neg A) C"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
    ord_res.production (fset N) D = {A})"
proof -
  from C_least_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_min: "\<forall>y |\<in>| N. y \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
    unfolding atomize_conj is_least_false_clause_def
    unfolding linorder_cls.is_least_in_ffilter_iff
    by argo

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> ord_res_Interp (fset N) C"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  from Neg_A_max have "Neg A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

  from C_false have "\<not> ord_res_Interp (fset N) C \<TTurnstile>l Neg A"
    using true_cls_if_true_lit_in[OF \<open>Neg A \<in># C\<close>]
    by meson
  hence "A \<in> ord_res_Interp (fset N) C"
    by simp
  with C_unproductive have "A \<in> ord_res.interp (fset N) C"
    by blast
  then obtain D where
    D_in: "D |\<in>| N" and D_lt_C: "D \<prec>\<^sub>c C" and D_productive: "A \<in> ord_res.production (fset N) D"
    unfolding ord_res.interp_def by auto

  from D_productive have "ord_res.is_strictly_maximal_lit (Pos A) D"
    using ord_res.mem_productionE by metis

  moreover have "ord_res.production (fset N) D = {A}"
    using D_productive ord_res.production_eq_empty_or_singleton by fastforce

  ultimately show ?thesis
    using D_in D_lt_C by metis
qed

lemma bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit':
  assumes
    C_least_false: "is_least_false_clause N C" and
    L_max: "ord_res.is_maximal_lit L C" and
    L_neg: "is_neg L"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (- L) D \<and>
    ord_res.production (fset N) D = {atm_of L})"
  using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit[OF C_least_false]
  by (simp add: L_max L_neg uminus_literal_def)

lemma ex_ground_resolutionI:
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_lt: "D \<prec>\<^sub>c C" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D"
  shows "\<exists>CD. ord_res.ground_resolution C D CD"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Neg A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

  from D_max_lit obtain D' where D_def: "D = add_mset (Pos A) D'"
    by (meson linorder_lit.is_greatest_in_mset_iff mset_add)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_resolution C D (C' + D')"
      using ord_res.ground_resolutionI[of C A C' D D']
      using C_def D_def D_lt C_max_lit D_max_lit by metis
  qed
qed

inductive ord_res_1 where
  factoring: "
    is_least_false_clause N C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    ord_res.ground_factoring C C' \<Longrightarrow>
    N' = finsert C' N \<Longrightarrow>
    ord_res_1 N N'" |

  resolution: "
    is_least_false_clause N C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset N) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    N' = finsert CD N \<Longrightarrow>
    ord_res_1 N N'"

lemma right_unique_ord_res_1: "right_unique ord_res_1"
proof (rule right_uniqueI)
  fix N N' N'' :: "'f gterm clause fset"
  assume step1: "ord_res_1 N N'" and step2: "ord_res_1 N N''"
  from step1 show "N' = N''"
  proof (cases N N' rule: ord_res_1.cases)
    case hyps1: (factoring C1 L1 C1')
    from step2 show ?thesis
    proof (cases N N'' rule: ord_res_1.cases)
      case hyps2: (factoring C2 L2 C2')
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "C1' = C2'"
        by (metis (no_types, lifting) Uniq_D ord_res.unique_ground_factoring)
      with hyps1 hyps2 show ?thesis
        by argo
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution C1 L1 D1 CD1)
    from step2 show ?thesis
    proof (cases N N'' rule: ord_res_1.cases)
      case hyps2: (factoring C2 L2 C2')
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have "D1 = D2"
        by (metis (mono_tags) Uniq_D ord_res.Uniq_production_eq_singleton)
      with hyps1 hyps2 have "CD1 = CD2"
        by (metis (no_types, lifting) Uniq_D \<open>C1 = C2\<close> ord_res.unique_ground_resolution)
      with hyps1 hyps2 show ?thesis
        by argo
    qed
  qed
qed

definition ord_res_1_final where
  "ord_res_1_final N \<longleftrightarrow> ord_res_final N"

inductive ord_res_1_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_1_load N N"

interpretation ord_res_1_semantics: semantics where
  step = ord_res_1 and
  final = ord_res_1_final
proof unfold_locales
  fix N :: "'f gterm clause fset"
  assume "ord_res_1_final N"
  thus "finished ord_res_1 N"
    unfolding ord_res_1_final_def ord_res_final_def
  proof (elim disjE)
    assume "{#} |\<in>| N"
    have False if "ord_res_1 N N'" for N'
      using that
    proof (cases N N' rule: ord_res_1.cases)
      case hyps: (factoring C L C')
      from hyps \<open>{#} |\<in>| N\<close> have "C = {#}"
        unfolding is_least_false_clause_def
        by (metis (no_types, lifting) emptyE ffmember_filter linorder_cls.dual_order.strict_trans
            linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl
            ord_res.multp_if_all_left_smaller set_mset_empty true_cls_empty)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    next
      case hyps: (resolution C L D CD)
      from hyps \<open>{#} |\<in>| N\<close> have "C = {#}"
        unfolding is_least_false_clause_def
        by (metis (no_types, lifting) emptyE ffmember_filter linorder_cls.dual_order.strict_trans
            linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl
            ord_res.multp_if_all_left_smaller set_mset_empty true_cls_empty)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    qed
    thus "finished ord_res_1 N"
      unfolding finished_def by metis
  next
    assume "\<not> ex_false_clause (fset N)"
    have False if "ord_res_1 N N'" for N'
      using that
    proof (cases N N' rule: ord_res_1.cases)
      case (factoring C L C')
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def is_least_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    next
      case (resolution C L D CD)
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def is_least_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    qed
    thus "finished ord_res_1 N"
      unfolding finished_def by metis
  qed
qed

interpretation ord_res_1_language: language where
  step = ord_res_1 and
  final = ord_res_1_final and
  load = ord_res_1_load
  by unfold_locales

interpretation backward_simulation_with_measuring_function where
  step1 = ord_res and
  step2 = ord_res_1 and
  final1 = ord_res_final and
  final2 = ord_res_1_final and
  order = "\<lambda>_ _. False" and
  match = "(=)" and
  measure = "\<lambda>_. ()"
proof unfold_locales
  show "wfP (\<lambda>_ _. False)"
    by simp
next
  show "\<And>N1 N2. N1 = N2 \<Longrightarrow> ord_res_1_final N2 \<Longrightarrow> ord_res_final N1"
    unfolding ord_res_1_final_def by metis
next
  fix N1 N2 N2' :: "'f gterm clause fset"
  assume match: "N1 = N2" and step2: "ord_res_1 N2 N2'"
  show "(\<exists>N1'. ord_res\<^sup>+\<^sup>+ N1 N1' \<and> N1' = N2') \<or> N1 = N2' \<and> False"
  proof (intro disjI1 exI conjI)

    have mempty_no_in: "{#} |\<notin>| N2"
      if C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N2.
        \<not> ord_res.interp (fset N2) C \<union> ord_res.production (fset N2) C \<TTurnstile> C|} C" and
        L_max: "linorder_lit.is_maximal_in_mset C L"
      for C L
    proof (rule notI)
      assume "{#} |\<in>| N2"
      moreover have "\<not> ord_res.interp (fset N2) {#} \<union> ord_res.production (fset N2) {#} \<TTurnstile> {#}"
        by simp
      moreover have "\<And>C. {#} \<preceq>\<^sub>c C"
        using mempty_lesseq_cls by metis
      ultimately have "C = {#}"
        using C_least
        by (metis (no_types, lifting) ffmember_filter linorder_cls.is_least_in_fset_iff
            linorder_cls.less_le_not_le)
      moreover have "L \<in># C"
        using L_max by (simp add: linorder_lit.is_maximal_in_mset_iff)
      ultimately show "False"
        by simp
    qed

    have "ord_res N2 N2'"
      using step2
    proof (cases N2 N2' rule: ord_res_1.cases)
      case hyps: (factoring C L C')
      show ?thesis
      proof (rule ord_res.factoring)
        show "{#} |\<notin>| N2"
          using hyps mempty_no_in is_least_false_clause_def by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps is_least_false_clause_def
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(1) by blast
      next
        show "ord_res.ground_factoring C C'"
          using hyps by argo
      next
        show "N2' = finsert C' N2"
          using hyps by argo
      qed
    next
      case hyps: (resolution C L D CD)
      show ?thesis
      proof (rule ord_res.resolution)
        show "{#} |\<notin>| N2"
          using hyps mempty_no_in is_least_false_clause_def by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps is_least_false_clause_def
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(1) by blast
      next
        show "D |\<in>| N2"
          using hyps by argo
      next
        show "ord_res.ground_resolution C D CD"
          using hyps by argo
      next
        show "N2' = finsert CD N2"
          using hyps by argo
      qed
    qed
    thus "ord_res\<^sup>+\<^sup>+ N1 N2'"
      unfolding match by simp
  next
    show "N2' = N2'" ..
  qed
qed

lemma ex_ord_res_1_if_not_final:
  assumes "\<not> ord_res_1_final N"
  shows "\<exists>N'. ord_res_1 N N'"
proof -
  from assms have "{#} |\<notin>| N" and "ex_false_clause (fset N)"
    unfolding ord_res_1_final_def ord_res_final_def by argo+

  obtain C where C_least_false: "is_least_false_clause N C"
    using \<open>ex_false_clause (fset N)\<close> obtains_least_false_clause_if_ex_false_clause by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)

    hence "\<not> linorder_lit.is_greatest_in_mset C L"
      using pos_lit_not_greatest_if_maximal_in_least_false_clause
      using C_least_false is_least_false_clause_def by blast

    then obtain C' where "ord_res.ground_factoring C C'"
      using ex_ground_factoringI C_max Pos by metis

    thus ?thesis
      using ord_res_1.factoring
      by (metis \<open>is_least_false_clause N C\<close> is_pos_def ord_res.ground_factoring.cases)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset N) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain CD where
      "ord_res.ground_resolution C D CD"
      using ex_ground_resolutionI C_max Neg by metis

    ultimately show ?thesis
      using ord_res_1.resolution[of N C L D CD "finsert CD N"]
      using C_least_false C_max Neg by auto
  qed
qed

corollary ord_res_1_safe: "ord_res_1_final N \<or> (\<exists>N'. ord_res_1 N N')"
  using ex_ord_res_1_if_not_final by metis


section \<open>ORD-RES-2 (full factorization)\<close>

inductive ord_res_2 where
  factoring: "
    is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    U\<^sub>e\<^sub>f' = finsert (efac C) U\<^sub>e\<^sub>f \<Longrightarrow>
    ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>r, U\<^sub>e\<^sub>f')" |

  resolution: "
    is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    U\<^sub>r' = finsert CD U\<^sub>r \<Longrightarrow>
    ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>r', U\<^sub>e\<^sub>f)"

inductive ord_res_2_step where
  "ord_res_2 N S S' \<Longrightarrow> ord_res_2_step (N, S) (N, S')"

inductive ord_res_2_final where
  "ord_res_final (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<Longrightarrow> ord_res_2_final (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"

inductive ord_res_2_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_2_load N (N, ({||}, {||}))"

interpretation ord_res_2_semantics: semantics where
  step = ord_res_2_step and
  final = ord_res_2_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>r U\<^sub>e\<^sub>f :: "'f gterm clause fset" where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)

  assume "ord_res_2_final S"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (simp add: S_def ord_res_2_final.simps ord_res_final_def)
  thus "finished ord_res_2_step S"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    have False if "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) x" for x
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>e\<^sub>f)" x rule: ord_res_2.cases)
      case hyps: (factoring C L U\<^sub>e\<^sub>f')
      from hyps have "C = {#}"
        using is_least_false_clause_mempty[OF \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>]
        by (metis Uniq_D Uniq_is_least_false_clause)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    next
      case hyps: (resolution C L D CD U\<^sub>e\<^sub>f')
      from hyps \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> have "C = {#}"
        using is_least_false_clause_mempty[OF \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>]
        by (metis Uniq_D Uniq_is_least_false_clause)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    qed
    thus "finished ord_res_2_step S"
      unfolding finished_def ord_res_2_step.simps S_def
      by (metis prod.inject)
  next
    assume no_false_cls: "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    have False if "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) x" for x
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>e\<^sub>f)" x rule: ord_res_2.cases)
      case hyps: (factoring C L U\<^sub>e\<^sub>f')
      thus False
        using no_false_cls[unfolded ex_false_clause_def]
        using is_least_false_clause_def linorder_cls.is_least_in_fset_iff by auto
    next
      case hyps: (resolution C L D CD U\<^sub>e\<^sub>f')
      thus False
        using no_false_cls[unfolded ex_false_clause_def]
        using is_least_false_clause_def linorder_cls.is_least_in_fset_iff by auto
    qed
    thus "finished ord_res_2_step S"
      unfolding finished_def ord_res_2_step.simps S_def
      by (metis prod.inject)
  qed
qed

interpretation ord_res_2_language: language where
  step = ord_res_2_step and
  final = ord_res_2_final and
  load = ord_res_2_load
  by unfold_locales

fun ord_res_1_matches_ord_res_2 where
  "ord_res_1_matches_ord_res_2 S1 (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) \<longleftrightarrow> (\<exists>U\<^sub>f.
      S1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f \<and>
      (\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
        (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)))"

lemma
  fixes N N'
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N" and
    C_not_entailed: "\<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
  shows "\<not> ord_res.interp (N \<union> N') C \<union> ord_res.production (N \<union> N') C \<TTurnstile> C"
  using C_not_entailed
proof (rule contrapos_nn)
  assume "ord_res.interp (N \<union> N') C \<union> ord_res.production (N \<union> N') C \<TTurnstile> C"
  then show "ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
    using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
    by metis
qed


lemma production_union_unproductive_strong:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2 - N1. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using ord_res.wfP_less_cls C_in
proof (induction C rule: wfP_induct_rule)
  case (less C)
  hence C_in_iff: "C \<in> N1 \<union> N2 \<longleftrightarrow> C \<in> N1"
    by simp

  have interp_eq: "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C"
  proof -
    have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
      unfolding ord_res.interp_def ..
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2 - N1. D \<prec>\<^sub>c C})"
      by auto
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C})"
      using N2_unproductive by simp
    also have "\<dots> = \<Union> (ord_res.production N1 ` {D \<in> N1. D \<prec>\<^sub>c C})"
      using less.IH by simp
    also have "\<dots> = ord_res.interp N1 C"
      unfolding ord_res.interp_def ..
    finally show "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C" .
  qed

  show ?case
    unfolding ord_res.production_unfold C_in_iff interp_eq by argo
qed

lemma production_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using production_union_unproductive_strong assms by simp

lemma interp_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}"
  shows "ord_res.interp (N1 \<union> N2) = ord_res.interp N1"
proof (rule ext)
  fix C
  have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
    unfolding ord_res.interp_def ..
  also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2. D \<prec>\<^sub>c C})"
    by auto
  also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C})"
    using N2_unproductive by simp
  also have "\<dots> = \<Union> (ord_res.production N1 ` {D \<in> N1. D \<prec>\<^sub>c C})"
    using production_union_unproductive[OF fin N2_unproductive] by simp
  also have "\<dots> = ord_res.interp N1 C"
    unfolding ord_res.interp_def ..
  finally show "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C" .
qed

lemma Interp_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}"
  shows "ord_res_Interp (N1 \<union> N2) C = ord_res_Interp N1 C"
  unfolding interp_union_unproductive[OF assms]
  using production_union_unproductive[OF assms]
  using N2_unproductive[rule_format]
  by (metis (no_types, lifting) Un_iff empty_Collect_eq ord_res.production_unfold)

lemma Interp_insert_unproductive:
  assumes
    fin: "finite N1" and
    x_unproductive: "ord_res.production (insert x N1) x = {}"
  shows "ord_res_Interp (insert x N1) C = ord_res_Interp N1 C"
  using assms Interp_union_unproductive
  by (metis Un_commute finite.emptyI finite.insertI insert_is_Un singletonD)

lemma extended_partial_model_entails_iff_partial_model_entails:
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N"
  shows "ord_res_Interp (N \<union> N') C \<TTurnstile> C \<longleftrightarrow> ord_res_Interp N C \<TTurnstile> C"
  using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  by metis


lemma factorizable_if_neq_efac:
  assumes "C \<noteq> efac C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
  using assms
  by (metis converse_rtranclpE ex1_efac_eq_factoring_chain)

lemma nex_strictly_maximal_pos_lit_if_factorizable:
  assumes "ord_res.ground_factoring C C'"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  by (metis Uniq_D add_mset_remove_trivial assms linorder_lit.Uniq_is_maximal_in_mset
      linorder_lit.dual_order.order_iff_strict linorder_lit.is_greatest_in_mset_iff
      linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.not_less
      ord_res.ground_factoring.cases union_single_eq_member)

lemma nex_strictly_maximal_pos_lit_if_neq_efac:
  assumes "C \<noteq> efac C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms factorizable_if_neq_efac nex_strictly_maximal_pos_lit_if_factorizable by metis

lemma unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "ord_res.production N C = {}"
  using assms by (simp add: ord_res.production_unfold)

lemma ball_unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<forall>C \<in> N'. \<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "\<forall>C \<in> N'. ord_res.production (N \<union> N') C = {}"
  using assms unproductive_if_nex_strictly_maximal_pos_lit by metis

lemma is_least_in_fset_with_irrelevant_clauses_if_is_least_in_fset:
  assumes
    irrelevant: "\<forall>D |\<in>| N'. \<exists>E |\<in>| N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"
  shows "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| N'. \<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C|} C"
proof -
  have
    C_in: "C |\<in>| N" and
    C_not_entailed: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_lt: "\<forall>x |\<in>| N. x \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) x \<TTurnstile> x \<longrightarrow> C \<prec>\<^sub>c x"
    using C_least linorder_cls.is_least_in_ffilter_iff by simp_all

  have "C |\<in>| N |\<union>| N'"
    using C_in by simp

  moreover have "\<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C"
    using extended_partial_model_entails_iff_partial_model_entails[
        of "fset N" "fset N'", OF finite_fset finite_fset irrelevant]
    using C_in C_not_entailed
    by simp

  moreover have "C \<prec>\<^sub>c x"
    if
      x_in: "x |\<in>| N |\<union>| N'" and
      x_neq: "x \<noteq> C" and
      x_not_entailed: "\<not> ord_res_Interp (fset (N |\<union>| N')) x \<TTurnstile> x"
    for x
  proof -

    from x_in have "x |\<in>| N \<or> x |\<in>| N'"
      by simp
    thus "C \<prec>\<^sub>c x"
    proof (elim disjE)
      assume x_in: "x |\<in>| N"

      moreover have "\<not> ord_res_Interp (fset N) x \<TTurnstile> x"
        using extended_partial_model_entails_iff_partial_model_entails[
            of "fset N" "fset N'", OF finite_fset finite_fset irrelevant x_in]
        using x_not_entailed by simp

      ultimately show "C \<prec>\<^sub>c x"
        using C_lt[rule_format, of x] x_neq by argo
    next
      assume "x |\<in>| N'"
      then obtain x' where "x' |\<in>| N" and "x' \<subset># x" "set_mset x' = set_mset x"
        using irrelevant by metis

      have "x' \<prec>\<^sub>c x"
        using \<open>x' \<subset># x\<close> by (metis strict_subset_implies_multp)

      moreover have "C \<preceq>\<^sub>c x'"
      proof (cases "x' = C")
        case True
        thus ?thesis
          by order
      next
        case False

        have "C \<prec>\<^sub>c x'"
        proof (rule C_lt[rule_format])
          show "x' |\<in>| N"
            using \<open>x' |\<in>| N\<close> .
        next
          show "x' \<noteq> C"
            using False .
        next
          have "\<not> ord_res_Interp (fset (N |\<union>| N')) x \<TTurnstile> x'"
            using x_not_entailed \<open>set_mset x' = set_mset x\<close>
            by (metis true_cls_def)
          hence "\<not> ord_res_Interp (fset (N |\<union>| N')) x' \<TTurnstile> x'"
            by (metis \<open>x' \<prec>\<^sub>c x\<close> ord_res.entailed_clause_stays_entailed)
          thus "\<not> ord_res_Interp (fset N) x' \<TTurnstile> x'"
            using extended_partial_model_entails_iff_partial_model_entails[
                of "fset N" "fset N'" x', OF finite_fset finite_fset irrelevant]
            using \<open>x' |\<in>| N\<close> by simp
        qed
        thus ?thesis
          by order
      qed

      ultimately show "C \<prec>\<^sub>c x"
        by order
    qed
  qed

  ultimately show "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| N'.
    \<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C|} C"
    using C_in C_not_entailed
    unfolding linorder_cls.is_least_in_ffilter_iff by metis
qed

thm List.upto.simps

primrec fset_upto :: "nat \<Rightarrow> nat \<Rightarrow> nat fset" where
  "fset_upto i 0 = (if i = 0 then {|0|} else {||})" |
  "fset_upto i (Suc n) = (if i \<le> Suc n then finsert (Suc n) (fset_upto i n) else {||})"

lemma
  "fset_upto 0 0 = {|0|}"
  "fset_upto 0 1 = {|0, 1|}"
  "fset_upto 0 2 = {|0, 1, 2|}"
  "fset_upto 0 3 = {|0, 1, 2, 3|}"
  "fset_upto 1 3 = {|1, 2, 3|}"
  "fset_upto 2 3 = {|2, 3|}"
  "fset_upto 3 3 = {|3|}"
  "fset_upto 4 3 = {||}"
  unfolding numeral_2_eq_2 numeral_3_eq_3
  by auto

lemma "i \<le> 1 + j \<Longrightarrow> List.upto i (1 + j) = List.upto i j @ [1 + j]"
  using upto_rec2 by simp

lemma fset_of_append_singleton: "fset_of_list (xs @ [x]) = finsert x (fset_of_list xs)"
  by simp

lemma "fset_of_list (List.upto (int i) (int j)) = int |`| fset_upto i j"
proof (induction j)
  case 0
  show ?case
    by simp
next
  case (Suc j)
  show ?case
  proof (cases "i \<le> Suc j")
    case True
    hence AAA: "int i \<le> 1 + int j"
      by presburger

    from True show ?thesis
      apply simp
      unfolding Suc.IH[symmetric]
      unfolding upto_rec2[OF AAA] fset_of_append_singleton
      by simp
  next
    case False
    thus ?thesis
      by simp
  qed
qed

lemma fset_fset_upto[simp]: "fset (fset_upto m n) = {m..n}"
  apply (induction n)
  apply simp
  apply simp
  using atLeastAtMostSuc_conv by presburger

lemma minus_mset_replicate_strict_subset_minus_msetI:
  assumes "m < n" and "n < count C L"
  shows "C - replicate_mset n L \<subset># C - replicate_mset m L"
proof -
  from \<open>m < n\<close> obtain k1 where n_def: "n = m + Suc k1"
    using less_natE by auto

  with \<open>n < count C L\<close> obtain k2 where
    count_eq: "count C L = m + Suc k1 + Suc k2"
    by (metis add.commute add_Suc group_cancel.add1 less_natE)

  define C\<^sub>0 where
    "C\<^sub>0 = {#K \<in># C. K \<noteq> L#}"

  have C_eq: "C = C\<^sub>0 + replicate_mset m L + replicate_mset (Suc k1) L + replicate_mset (Suc k2) L"
    using C\<^sub>0_def count_eq
    by (metis (mono_tags, lifting) filter_mset_eq group_cancel.add1 replicate_mset_plus
        union_filter_mset_complement)

  have "C - replicate_mset n L = C\<^sub>0 + replicate_mset (Suc k2) L"
    unfolding C_eq n_def
    by (simp add: replicate_mset_plus)
  also have "\<dots> \<subset># C\<^sub>0 + replicate_mset (Suc k1) L + replicate_mset (Suc k2) L"
    by simp
  also have "\<dots> = C - replicate_mset m L"
    unfolding C_eq
    by (simp add: replicate_mset_plus)
  finally show ?thesis .
qed

lemma factoring_all_is_between_efac_and_original_clause:
  fixes z
  assumes
    "is_pos L" and "ord_res.is_maximal_lit L C" and "count C L = Suc (Suc n)"
    "m' \<le> n" and
    z_in: "z |\<in>| (\<lambda>i. C - replicate_mset i L) |`| fset_upto 0 m'"
  shows "efac C \<subset># z" and "z \<subseteq># C"
proof -
  from z_in obtain i where
    "i \<le> m'" and
    z_def: "z = C - replicate_mset i L"
    by auto

  have "i \<le> n"
    using \<open>i \<le> m'\<close> \<open>m' \<le> n\<close> by presburger
  hence "i < count C L"
    using \<open>count C L = Suc (Suc n)\<close> by presburger
  thus "z \<subseteq># C"
    unfolding z_def by simp

  show "efac C \<subset># z"
  proof -
    have "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      using efac_spec_if_pos_lit_is_maximal[OF \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L C\<close>] .
    also have "\<dots> \<subset># add_mset L (add_mset L {#K \<in># C. K \<noteq> L#})"
      by simp
    also have "\<dots> = C - replicate_mset n L"
      using minus_mset_replicate_mset_eq_add_mset_add_mset_filter_mset[
          OF \<open>count C L = Suc (Suc n)\<close>] ..
    also have "\<dots> \<subseteq># C - replicate_mset i L"
      using \<open>i \<le> n\<close> by (simp add: subseteq_mset_def)
    also have "\<dots> = z"
      using z_def ..
    finally show ?thesis .
  qed
qed

lemma
  assumes
    "linorder_cls.is_least_in_fset {|x |\<in>| N1. P N1 x|} x" and
    "linorder_cls.is_least_in_fset N2 y" and
    "\<forall>z |\<in>| N2. z \<preceq>\<^sub>c x" and
    "P (N1 |\<union>| N2) y" and
    "\<forall>z |\<in>| N1. z \<prec>\<^sub>c x \<longrightarrow> \<not> P (N1 |\<union>| N2) z"
  shows "linorder_cls.is_least_in_fset {|x |\<in>| N1 |\<union>| N2. P (N1 |\<union>| N2) x|} y"
proof -
  show ?thesis
    unfolding linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    from assms(2) show "y |\<in>| N1 |\<union>| N2"
      unfolding linorder_cls.is_least_in_fset_iff by simp
  next
    from assms(4) show "P (N1 |\<union>| N2) y"
      by argo
  next
    fix z
    assume z_in: "z |\<in>| N1 |\<union>| N2" and "z \<noteq> y" and "P (N1 |\<union>| N2) z"
    show "y \<prec>\<^sub>c z"
      using z_in[unfolded funion_iff]
    proof (elim disjE)
      from assms(2,3,5) show "z |\<in>| N1 \<Longrightarrow> y \<prec>\<^sub>c z"
        by (metis \<open>P (N1 |\<union>| N2) z\<close> \<open>z \<noteq> y\<close> linorder_cls.dual_order.not_eq_order_implies_strict
            linorder_cls.is_least_in_fset_iff linorder_cls.less_linear
            linorder_cls.order.strict_trans)
    next
      from assms(2) show "z |\<in>| N2 \<Longrightarrow> y \<prec>\<^sub>c z"
        using \<open>z \<noteq> y\<close> linorder_cls.is_least_in_fset_iff by blast
    qed
  qed
qed


lemma ground_factoring_preserves_efac:
  assumes "ord_res.ground_factoring P C"
  shows "efac P = efac C"
  using assms
  by (smt (verit, ccfv_threshold) filter_mset_add_mset is_pos_def ord_res.ground_factoring.cases
      ord_res.ground_factoring_preserves_maximal_literal efac_spec_if_pos_lit_is_maximal)

lemma ground_factorings_preserves_efac:
  assumes "ord_res.ground_factoring\<^sup>*\<^sup>* P C"
  shows "efac P = efac C"
  using assms
  by (induction P rule: converse_rtranclp_induct)
    (simp_all add: ground_factoring_preserves_efac)

lemma ord_res_1_final_iff_ord_res_2_final:
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 S\<^sub>2"
  shows "ord_res_1_final S\<^sub>1 \<longleftrightarrow> ord_res_2_final S\<^sub>2"
proof -
  obtain N U\<^sub>r U\<^sub>e\<^sub>f where "S\<^sub>2 = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)
  with match obtain U\<^sub>f where
    S\<^sub>1_def: "S\<^sub>1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
      (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    by auto

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> efac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_efac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  have "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> {#} |\<in>| U\<^sub>f"
      by simp
    thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        by assumption
    next
      assume "{#} |\<in>| U\<^sub>f"
      hence "{#} \<noteq> efac {#}"
        using U\<^sub>f_spec[rule_format, of "{#}"] by metis
      hence False
        by simp
      thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" ..
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
      by simp
  qed

  moreover have "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) \<longleftrightarrow>
    \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
  proof (rule iffI; erule contrapos_nn)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f))"
      unfolding ex_false_clause_def Interp_eq by auto
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f))"
    then obtain C where
      "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f" and
      C_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
      unfolding ex_false_clause_def Interp_eq by metis
    hence "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    proof (elim disjE)
      assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
        unfolding ex_false_clause_def using C_false by metis
    next
      assume "C |\<in>| U\<^sub>f"
      then obtain C' where "C' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
       "ord_res.ground_factoring\<^sup>+\<^sup>+ C' C" and
       "C \<noteq> efac C" and
       "efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C'"
        using U\<^sub>f_spec[rule_format, of C] by metis
      thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      proof (elim disjE exE conjE)
        assume "efac C |\<in>| U\<^sub>e\<^sub>f"

        show "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
        proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (efac C) \<TTurnstile> efac C")
          case efac_C_true: True
          have "efac C \<subseteq># C"
            using efac_subset[of C] .
          hence "efac C \<preceq>\<^sub>c C"
            using subset_implies_reflclp_multp by metis
          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> efac C"
            using efac_C_true ord_res.entailed_clause_stays_entailed by fastforce
          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
            using efac_C_true by (simp add: true_cls_def)
          with C_false have False
            by contradiction
          thus ?thesis ..
        next
          case False

          moreover have "efac C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>efac C |\<in>| U\<^sub>e\<^sub>f\<close> by simp

          ultimately show "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
            unfolding ex_false_clause_def by metis
        qed
      next
        assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C'"
        hence "C' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C' \<TTurnstile> C'"
          using linorder_cls.is_least_in_ffilter_iff is_least_false_clause_def by simp_all
        thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
          unfolding ex_false_clause_def by metis
      qed
    qed
  qed

  ultimately show ?thesis
    by (simp add: S\<^sub>1_def \<open>S\<^sub>2 = (N, U\<^sub>r, U\<^sub>e\<^sub>f)\<close> ord_res_1_final_def ord_res_2_final.simps
        ord_res_final_def)
qed


lemma ex_ord_res_2_if_not_final:
  assumes "\<not> ord_res_2_final S"
  shows "\<exists>S'. ord_res_2_step S S'"
proof -
  from assms obtain N U\<^sub>r U\<^sub>e\<^sub>f where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))" and
    "{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
    "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (metis ord_res_2_final.intros ord_res_final_def surj_pair)

  obtain C where C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    using \<open>ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))\<close> obtains_least_false_clause_if_ex_false_clause
    by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using ord_res_2.factoring[OF C_least_false C_max] S_def is_pos_def
      by (metis ord_res_2_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain CD where
      "ord_res.ground_resolution C D CD"
      using ex_ground_resolutionI C_max Neg by metis

    ultimately show ?thesis
      using ord_res_2.resolution[OF C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_2_step.intros)
  qed
qed

corollary ord_res_2_step_safe: "ord_res_2_final S \<or> (\<exists>S'. ord_res_2_step S S')"
  using ex_ord_res_2_if_not_final by metis

lemma safe_states_if_ord_res_1_matches_ord_res_2:
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 S\<^sub>2"
  shows "safe_state ord_res_1 ord_res_1_final S\<^sub>1 \<and> safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
proof -
  have "safe_state ord_res_1 ord_res_1_final S\<^sub>1"
    using safe_state_if_all_states_safe ord_res_1_safe by metis

  moreover have "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    using safe_state_if_all_states_safe ord_res_2_step_safe by metis

  ultimately show ?thesis
    by argo
qed

definition ord_res_1_measure where
  "ord_res_1_measure s1 =
    (if \<exists>C. is_least_false_clause s1 C then
      The (is_least_false_clause s1)
    else
      {#})"

lemma is_least_false_clause_if_is_least_false_clause_in_union_unproductive:
  assumes
    N2_unproductive: "\<forall>C |\<in>| N2. ord_res.production (fset (N1 |\<union>| N2)) C = {}" and
    C_in: "C |\<in>| N1" and
    C_least_false: "is_least_false_clause (N1 |\<union>| N2) C"
  shows "is_least_false_clause N1 C"
  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "C |\<in>| N1"
    using C_in .
next
  have "\<not> ord_res_Interp (fset (N1 |\<union>| N2)) C \<TTurnstile> C"
    using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
    by argo
  thus "\<not> ord_res.interp (fset N1) C \<union> ord_res.production (fset N1) C \<TTurnstile> C"
    unfolding Interp_union_unproductive[of "fset N1" "fset N2", folded union_fset,
        OF finite_fset finite_fset N2_unproductive] .
next
  fix D
  have "\<forall>D |\<in>| N1 |\<union>| N2. D \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset (N1 |\<union>| N2)) D \<TTurnstile> D \<longrightarrow> C \<prec>\<^sub>c D"
    using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
    by argo

  moreover assume "D |\<in>| N1" and "D \<noteq> C" and "\<not> ord_res_Interp (fset N1) D \<TTurnstile> D"

  ultimately show "C \<prec>\<^sub>c D"
    using Interp_union_unproductive[of "fset N1" "fset N2", folded union_fset,
        OF finite_fset finite_fset N2_unproductive]
    by simp
qed

lemma ground_factoring_replicate_max_pos_lit:
  "ord_res.ground_factoring
    (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))
    (C\<^sub>0 + replicate_mset (Suc n) (Pos A))"
  if "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
  for A C\<^sub>0 n
proof (rule ord_res.ground_factoringI)
  show "C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A) =
            add_mset (Pos A) (add_mset (Pos A) (C\<^sub>0 + replicate_mset n (Pos A)))"
    by simp
next
  show "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
    using that .
next
  show "C\<^sub>0 + replicate_mset (Suc n) (Pos A) =
            add_mset (Pos A) (C\<^sub>0 + replicate_mset n (Pos A))"
    by simp
qed simp

lemma ground_factorings_replicate_max_pos_lit:
  assumes
    "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
  shows "m \<le> Suc n \<Longrightarrow> (ord_res.ground_factoring ^^ m)
    (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))
    (C\<^sub>0 + replicate_mset (Suc (Suc n - m)) (Pos A))"
proof (induction m)
  case 0
  show ?case
    by simp
next
  case (Suc m')
  then show ?case
    apply (cases m')
    using assms ground_factoring_replicate_max_pos_lit apply auto[1]
    by (metis (no_types, lifting) Suc_diff_le Suc_leD assms diff_Suc_Suc
        ground_factoring_replicate_max_pos_lit ord_res.ground_factorings_preserves_maximal_literal
        relpowp_Suc_I relpowp_imp_rtranclp)
qed

lemma ord_res_Interp_entails_if_greatest_lit_is_pos:
  assumes C_in: "C \<in> N" and L_greatest: "linorder_lit.is_greatest_in_mset C L" and L_pos: "is_pos L"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof (cases "ord_res.interp N C \<TTurnstile> C")
  case True
  hence "ord_res.production N C = {}"
    by (simp add: ord_res.production_unfold)
  with True show ?thesis
    by simp
next
  case False

  from L_pos obtain A where L_def: "L = Pos A"
    by (cases L) simp_all

  from L_greatest obtain C' where C_def: "C = add_mset L C'"
    unfolding linorder_lit.is_greatest_in_mset_iff
    by (metis insert_DiffM)

  with C_in L_greatest have "A \<in> ord_res.production N C"
    unfolding L_def ord_res.production_unfold
    using False
    by (simp add: linorder_lit.is_greatest_in_mset_iff multi_member_split)
  thus ?thesis
    by (simp add: true_cls_def C_def L_def)
qed

lemma right_unique_ord_res_2: "right_unique (ord_res_2 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_2 N s s'" and step2: "ord_res_2 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_2.cases)
    case hyps1: (factoring U\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 U\<^sub>e\<^sub>f'1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_2.cases)
      case (factoring U\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f'2)
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution U\<^sub>r U\<^sub>e\<^sub>f C L D CD U\<^sub>r')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution U\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 D1 CD1 U\<^sub>r'1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_2.cases)
      case (factoring U\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f'2)
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    next
      case (resolution U\<^sub>r U\<^sub>e\<^sub>f C L D CD U\<^sub>r')
      with hyps1 show ?thesis
        by (metis (mono_tags, lifting) Uniq_is_least_false_clause
            linorder_lit.Uniq_is_maximal_in_mset ord_res.Uniq_production_eq_singleton
            ord_res.unique_ground_resolution prod.inject the1_equality')
    qed
  qed
qed

lemma right_unique_ord_res_2_step: "right_unique ord_res_2_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_2_step x y \<Longrightarrow> ord_res_2_step x z \<Longrightarrow> y = z"
    apply (cases x; cases y; cases z)
    apply (simp add: ord_res_2_step.simps)
    using right_unique_ord_res_2[THEN right_uniqueD]
    by blast
qed

lemma forward_simulation:
  assumes match: "ord_res_1_matches_ord_res_2 s1 s2" and
    step1: "ord_res_1 s1 s1'"
  shows "(\<exists>s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> ord_res_1_matches_ord_res_2 s1' s2') \<or>
    ord_res_1_matches_ord_res_2 s1' s2 \<and> ord_res_1_measure s1' \<subset># ord_res_1_measure s1"
proof -
  let
    ?match = "ord_res_1_matches_ord_res_2" and
    ?measure = "ord_res_1_measure" and
    ?order = "(\<subset>#)"

  obtain N U\<^sub>r U\<^sub>e\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)

  from match obtain U\<^sub>f where
    s1_def: "s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
      (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    unfolding s2_def ord_res_1_matches_ord_res_2.simps by metis

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> efac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_efac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  show "(\<exists>s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> ?match s1' s2') \<or>
    ?match s1' s2 \<and> ?order (?measure s1') (?measure s1)"
    using step1
  proof (cases s1 s1' rule: ord_res_1.cases)
    case (factoring C L C')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f) C"
      using factoring
      unfolding is_least_false_clause_def s1_def by argo

    hence C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff s1_def by argo
    hence C_in_disj: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp

    show ?thesis
    proof (cases "C' = efac C'")
      case True
      let ?s2' = "(N, (U\<^sub>r, finsert C' U\<^sub>e\<^sub>f))"

      have "ord_res_2_step\<^sup>+\<^sup>+ s2 ?s2'"
      proof (rule tranclp.r_into_trancl)
        show "ord_res_2_step s2 (N, U\<^sub>r, finsert C' U\<^sub>e\<^sub>f)"
          using C_in_disj
        proof (elim disjE)
          assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          show ?thesis
            unfolding s2_def
          proof (intro ord_res_2_step.intros ord_res_2.factoring)
            show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
              using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                  OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> C_least_false]
              unfolding is_least_false_clause_def .
          next
            show "ord_res.is_maximal_lit L C"
              using \<open>ord_res.is_maximal_lit L C\<close> .
          next
            show "is_pos L"
              using \<open>is_pos L\<close> .
          next
            show "finsert C' U\<^sub>e\<^sub>f = finsert (efac C) U\<^sub>e\<^sub>f"
              using True factoring ground_factoring_preserves_efac by metis
          qed
        next
          assume "C |\<in>| U\<^sub>f"
          then obtain x where
            "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
            "ord_res.ground_factoring\<^sup>+\<^sup>+ x C" and
            "C \<noteq> efac C" and
            "efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
            using U\<^sub>f_spec by metis

          show ?thesis
            unfolding s2_def
          proof (intro ord_res_2_step.intros ord_res_2.factoring)
            have \<open>efac C |\<notin>| U\<^sub>e\<^sub>f\<close>
            proof (rule notI)
              have "efac C \<preceq>\<^sub>c C"
                using efac_subset[of C] subset_implies_reflclp_multp by metis
              hence "efac C \<prec>\<^sub>c C"
                using \<open>C \<noteq> efac C\<close> by order

              moreover assume "efac C |\<in>| U\<^sub>e\<^sub>f"

              ultimately show False
                using C_least_false[unfolded is_least_false_clause_def
                    linorder_cls.is_least_in_ffilter_iff]
                by (metis \<open>C \<noteq> efac C\<close> funionCI linorder_cls.not_less_iff_gr_or_eq
                    ord_res.entailed_clause_stays_entailed set_mset_efac true_cls_def)
            qed
            thus "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
              using \<open>efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close> by argo
          next
            show "ord_res.is_maximal_lit L x"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.is_maximal_lit L C\<close>
              using ord_res.ground_factorings_preserves_maximal_literal
              by (metis tranclp_into_rtranclp)
          next
            show "is_pos L"
              using \<open>is_pos L\<close> .
          next
            show "finsert C' U\<^sub>e\<^sub>f = finsert (efac x) U\<^sub>e\<^sub>f"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.ground_factoring C C'\<close>
              using True ground_factorings_preserves_efac ground_factoring_preserves_efac
              by (metis tranclp_into_rtranclp)
          qed
        qed
      qed

      moreover have "?match s1' ?s2'"
      proof -
        have "s1' = N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
          unfolding \<open>s1' = finsert C' s1\<close> s1_def by simp

        moreover have "\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f.
          ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
          (efac C\<^sub>f |\<in>| finsert C' U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f) C)"
          if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
        proof -
          obtain x where
            "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
            "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
            "C\<^sub>f \<noteq> efac C\<^sub>f" and
            "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
            using \<open>C\<^sub>f |\<in>| U\<^sub>f\<close> U\<^sub>f_spec by metis

          show ?thesis
          proof (intro bexI conjI)
            show "x |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f"
              using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
          next
            show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
          next
            show "C\<^sub>f \<noteq> efac C\<^sub>f"
              using \<open>C\<^sub>f \<noteq> efac C\<^sub>f\<close> .
          next
            show "efac C\<^sub>f |\<in>| finsert C' U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>e\<^sub>f) x"
              using \<open>efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
            proof (elim disjE)
              assume "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f"
              thus ?thesis
                by simp
            next
              assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
              show ?thesis
              proof (cases "C' = efac x")
                case True
                moreover have "efac x = efac C\<^sub>f"
                  using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> ground_factorings_preserves_efac
                  by (metis tranclp_into_rtranclp)
                ultimately show ?thesis
                  by simp
              next
                case False
                show ?thesis
                  using C_in_disj
                proof (elim disjE)
                  assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                  then show ?thesis
                    by (smt (verit) C_least_false True U\<^sub>f_unproductive
                        \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close> \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close>
                        finsert_iff ground_factoring_preserves_efac ground_factorings_preserves_efac
                        linorder_cls.Uniq_is_least_in_fset local.factoring(4)
                        is_least_false_clause_def
                        is_least_false_clause_if_is_least_false_clause_in_union_unproductive
                        the1_equality' tranclp_into_rtranclp)
                next
                  assume "C |\<in>| U\<^sub>f"
                  then show ?thesis
                    using C_least_false
                    using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                        OF U\<^sub>f_unproductive]
                    by (smt (z3) True U\<^sub>f_spec \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
                        \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> finsert_absorb finsert_iff
                        ground_factoring_preserves_efac ground_factorings_preserves_efac
                        linorder_cls.Uniq_is_least_in_fset local.factoring(4)
                        is_least_false_clause_def the1_equality' tranclp_into_rtranclp)
                qed
              qed
            qed
          qed
        qed

        ultimately show ?thesis
          by auto
      qed

      ultimately show ?thesis
        by metis
    next
      case False
      let ?U\<^sub>f' = "finsert C' U\<^sub>f"

      have "?match s1' s2"
      proof -
        have "finsert C' s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| ?U\<^sub>f'"
          unfolding s1_def by simp

        moreover have "\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
          (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
          if "C\<^sub>f |\<in>| ?U\<^sub>f'" for C\<^sub>f
        proof -
          from \<open>C\<^sub>f |\<in>| ?U\<^sub>f'\<close> have "C\<^sub>f = C' \<or> C\<^sub>f |\<in>| U\<^sub>f"
            by simp
          thus ?thesis
          proof (elim disjE)
            assume "C\<^sub>f = C'"
            thus ?thesis
              using C_in_disj
            proof (elim disjE)
              assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              show ?thesis
              proof (intro bexI conjI)
                show "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                  using \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
              next
                show "ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f"
                  using \<open>ord_res.ground_factoring C C'\<close> \<open>C\<^sub>f = C'\<close> by simp
              next
                show "C\<^sub>f \<noteq> efac C\<^sub>f"
                  using False \<open>C\<^sub>f = C'\<close> by argo
              next
                have "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
                  using factoring
                  using Interp_eq \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> linorder_cls.is_least_in_ffilter_iff
                  by (simp add: s1_def is_least_false_clause_def)
                thus "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C" ..
              qed
            next
              assume "C |\<in>| U\<^sub>f"
              then obtain x where
                "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
                "ord_res.ground_factoring\<^sup>+\<^sup>+ x C" and
                "C \<noteq> efac C" and
                "efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
                using U\<^sub>f_spec by metis

              show ?thesis
              proof (intro bexI conjI)
                show "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                  using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
              next
                show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
                  using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.ground_factoring C C'\<close> \<open>C\<^sub>f = C'\<close>
                  by simp
              next
                show "C\<^sub>f \<noteq> efac C\<^sub>f"
                  using False \<open>C\<^sub>f = C'\<close> by argo
              next
                show "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
                  using \<open>efac C |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
                proof (elim disjE)
                  assume "efac C |\<in>| U\<^sub>e\<^sub>f"

                  moreover have "efac C = efac C\<^sub>f"
                    unfolding \<open>C\<^sub>f = C'\<close>
                    using \<open>ord_res.ground_factoring C C'\<close> ground_factoring_preserves_efac by metis

                  ultimately show ?thesis
                    by argo
                next
                  assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
                  thus ?thesis
                    by argo
                qed
              qed
            qed
          next
            assume "C\<^sub>f |\<in>| U\<^sub>f"
            thus ?thesis
              using U\<^sub>f_spec by metis
          qed
        qed

        ultimately have "ord_res_1_matches_ord_res_2 (finsert C' s1) (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"
          unfolding ord_res_1_matches_ord_res_2.simps by metis
        thus ?thesis
          unfolding s2_def \<open>s1' = finsert C' s1\<close> by simp
      qed

      moreover have "?order (?measure s1') (?measure s1)"
      proof -
        have "?measure s1 = C"
          unfolding ord_res_1_measure_def
          using C_least_false[folded s1_def]
          by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
              is_least_false_clause_def the1_equality' the_equality)

        moreover have "?measure s1' = C'"
        proof -
          have "C' \<prec>\<^sub>c C"
            using factoring ord_res.ground_factoring_smaller_conclusion by metis

          have unproductive: "\<forall>x\<in>{C'}. ord_res.production (fset s1 \<union> {C'}) x = {}"
            using \<open>C' \<noteq> efac C'\<close>
            by (simp add: nex_strictly_maximal_pos_lit_if_neq_efac
                unproductive_if_nex_strictly_maximal_pos_lit)

          have Interp_eq: "\<And>D. ord_res_Interp (fset s1) D = ord_res_Interp (fset (finsert C' s1)) D"
            using Interp_union_unproductive[of "fset s1" "{C'}", folded union_fset,
                OF finite_fset _ unproductive]
            by simp

          have "is_least_false_clause (finsert C' s1) C'"
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            have "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C"
              using C_least_false s1_def is_least_false_clause_def
                linorder_cls.is_least_in_ffilter_iff by simp
            thus "\<not> ord_res_Interp (fset (finsert C' s1)) C' \<TTurnstile> C'"
              by (metis Interp_eq \<open>C' \<prec>\<^sub>c C\<close> local.factoring(4)
                  ord_res.entailed_clause_stays_entailed
                  ord_res.set_mset_eq_set_mset_if_ground_factoring subset_refl true_cls_mono)
          next
            fix y
            assume "y |\<in>| finsert C' s1" and "y \<noteq> C'" and
              y_false: "\<not> ord_res_Interp (fset (finsert C' s1)) y \<TTurnstile> y"
            hence "y |\<in>| s1"
              by simp

            moreover have "\<not> ord_res_Interp (fset s1) y \<TTurnstile> y"
              using y_false
              unfolding Interp_eq .

            ultimately have "C \<preceq>\<^sub>c y"
              using C_least_false[folded s1_def, unfolded is_least_false_clause_def]
              unfolding linorder_cls.is_least_in_ffilter_iff
              by force
            thus "C' \<prec>\<^sub>c y"
              using \<open>C' \<prec>\<^sub>c C\<close> by order
          qed simp
          thus ?thesis
            unfolding ord_res_1_measure_def \<open>s1' = finsert C' s1\<close>
            by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
                is_least_false_clause_def the1_equality' the_equality)
        qed

        moreover have "C' \<subset># C"
          using factoring ord_res.strict_subset_mset_if_ground_factoring by metis

        ultimately show ?thesis
          unfolding s1_def  by simp
      qed

      ultimately show ?thesis
        by argo
    qed
  next
    case (resolution C L D CD)

    have "is_least_false_clause s1 C"
      using resolution unfolding is_least_false_clause_def by argo
    hence
      "C |\<in>| s1" and
      "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C" and
      "\<forall>x |\<in>| s1. \<not> ord_res_Interp (fset s1) x \<TTurnstile> x \<longrightarrow> x \<noteq> C \<longrightarrow> C \<prec>\<^sub>c x"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by simp_all

    have "C |\<notin>| U\<^sub>f"
    proof (rule notI)
      assume "C |\<in>| U\<^sub>f"
      then show False
        by (metis U\<^sub>f_spec Uniq_D is_pos_def linorder_lit.Uniq_is_maximal_in_mset local.resolution(2)
            local.resolution(3) efac_spec)
    qed
    hence "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      using \<open>C |\<in>| s1\<close> by (simp add: s1_def)

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f) C"
      using resolution s1_def by metis
    hence C_least_false': "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
          OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>] by argo

    define s2' where
      "s2' = (N, (finsert CD U\<^sub>r, U\<^sub>e\<^sub>f))"

    have "ord_res_2_step\<^sup>+\<^sup>+ s2 s2'"
    proof -
      have "D |\<notin>| U\<^sub>f"
      proof (rule notI)
        assume "D |\<in>| U\<^sub>f"
        thus False
          using \<open>ord_res.production (fset s1) D = {atm_of L}\<close>
          using U\<^sub>f_unproductive s1_def by simp
      qed
      hence D_in: "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        using \<open>D |\<in>| s1\<close>[unfolded s1_def] by simp

      have "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) (finsert CD U\<^sub>r, U\<^sub>e\<^sub>f)"
      proof (rule ord_res_2.resolution)
        show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
          using C_least_false' .
      next
        show "ord_res.is_maximal_lit L C"
          using resolution by argo
      next
        show "is_neg L"
          using resolution by argo
      next
        show "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          using D_in .
      next
        show "D \<prec>\<^sub>c C"
          using resolution by argo
      next
        show "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}"
          using resolution
          unfolding s1_def
          using production_union_unproductive[OF finite_fset finite_fset _ D_in] U\<^sub>f_unproductive
          by (metis (no_types, lifting) union_fset)
      next
        show "ord_res.ground_resolution C D CD"
          using resolution by argo
      qed simp_all
      thus ?thesis
        by (auto simp: s2_def s2'_def ord_res_2_step.simps)
    qed

    moreover have "?match s1' s2'"
    proof -
      have "finsert CD (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f) = N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>f"
        by simp

      moreover have "\<exists>C |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
        ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> efac C\<^sub>f \<and>
        (efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
        if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
      proof -
        obtain x where
          "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
          "C\<^sub>f \<noteq> efac C\<^sub>f" and
          "efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x"
          using \<open>C\<^sub>f |\<in>| U\<^sub>f\<close> U\<^sub>f_spec by metis
        show ?thesis
        proof (intro bexI conjI)
          show "x |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        next
          show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
            using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
        next
          show "C\<^sub>f \<noteq> efac C\<^sub>f"
            using \<open>C\<^sub>f \<noteq> efac C\<^sub>f\<close> .
        next
          show \<open>efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close>
            using \<open>efac C\<^sub>f |\<in>| U\<^sub>e\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) x\<close> \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
            by (metis (no_types, lifting) C_least_false' Uniq_D \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close>
                is_least_false_clause_def is_pos_def linorder_cls.Uniq_is_least_in_fset
                linorder_lit.Uniq_is_maximal_in_mset local.resolution(2) local.resolution(3)
                ord_res.ground_factoring.cases tranclpD)
        qed
      qed

      ultimately show ?thesis
        unfolding s1_def resolution s2'_def by auto
    qed

    ultimately show ?thesis
      by metis
  qed
qed

lemma lift_tranclp_to_pairs_with_constant_fst:
  "(R x)\<^sup>+\<^sup>+ y z \<Longrightarrow> (\<lambda>(x, y) (x', z). x = x' \<and> R x y z)\<^sup>+\<^sup>+ (x, y) (x, z)"
  by (induction z arbitrary: rule: tranclp_induct) (auto simp: tranclp.trancl_into_trancl)

theorem bisimulation_ord_res_1_ord_res_2:
  defines "match \<equiv> \<lambda>i s1 s2. i = ord_res_1_measure s1 \<and> ord_res_1_matches_ord_res_2 s1 s2"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f gterm clause fset \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow> bool) ORDER.
    bisimulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final ORDER MATCH"
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_1"
    using right_unique_ord_res_1 .
next
  show "right_unique ord_res_2_step"
    using right_unique_ord_res_2_step .
next
  show "\<forall>s1. ord_res_1_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_1 s1 s1')"
    using ord_res_1_semantics.final_finished
    by (simp add: finished_def)
next
  show "\<forall>s2. ord_res_2_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_2_step s2 s2')"
    using ord_res_2_semantics.final_finished
    by (simp add: finished_def)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_1_final s1 = ord_res_2_final s2"
    using ord_res_1_final_iff_ord_res_2_final
    by (simp add: match_def)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_1 ord_res_1_final s1 \<and>
    safe_state ord_res_2_step ord_res_2_final s2"
  proof (intro allI impI)
    fix i s1 S2
    assume "match i s1 S2"

    then obtain N s2 where
      S2_def: "S2 = (N, s2)" and
      "i = ord_res_1_measure s1" and
      match: "ord_res_1_matches_ord_res_2 s1 S2"
      unfolding match_def
      by (metis prod.exhaust)

    show "safe_state ord_res_1 ord_res_1_final s1 \<and> safe_state ord_res_2_step ord_res_2_final S2"
      using safe_states_if_ord_res_1_matches_ord_res_2[OF match] .
  qed
next
  show "wfP (\<subset>#)"
    using wfP_subset_mset .
next
  show "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> ord_res_1 s1 s1' \<longrightarrow>
    (\<exists>i' s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> i' \<subset># i)"
  proof (intro allI impI)
    fix i s1 S2 s1'
    assume "match i s1 S2"
    then obtain N s2 where
      S2_def: "S2 = (N, s2)" and "i = ord_res_1_measure s1" and "ord_res_1_matches_ord_res_2 s1 S2"
      unfolding match_def
      by (metis prod.exhaust)

    moreover assume "ord_res_1 s1 s1'"

    ultimately have "(\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> ord_res_1_matches_ord_res_2 s1' S2') \<or>
    ord_res_1_matches_ord_res_2 s1' S2 \<and> ord_res_1_measure s1' \<subset># ord_res_1_measure s1"
      using forward_simulation by metis

    thus "(\<exists>i' S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match i' s1' S2') \<or> (\<exists>i'. match i' s1' S2 \<and> i' \<subset># i)"
      unfolding S2_def prod.case
      using lift_tranclp_to_pairs_with_constant_fst[of ord_res_2 N s2]
      by (metis (mono_tags, lifting) \<open>i = ord_res_1_measure s1\<close> match_def)
  qed
qed


section \<open>ORD-RES-3 (full resolve)\<close>

definition full_run where
  "full_run \<R> x y \<longleftrightarrow> \<R>\<^sup>*\<^sup>* x y \<and> (\<nexists>z. \<R> y z)"

lemma Uniq_full_run:
  assumes Uniq_R: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y"
  shows "\<exists>\<^sub>\<le>\<^sub>1y. full_run R x y"
  unfolding full_run_def
  using assms
  by (smt (verit, best) UniqI right_unique_iff rtranclp_complete_run_right_unique)

lemma ex1_full_run:
  assumes Uniq_R: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y" and wfP_R: "wfP R\<inverse>\<inverse>"
  shows "\<exists>!y. full_run R x y"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1 y. full_run R x y"
    using Uniq_full_run[of R x] Uniq_R by argo

  moreover have "\<exists>y. full_run R x y"
    using ex_terminating_rtranclp[OF wfP_R, of x, folded full_run_def] .

  ultimately show ?thesis
    using Uniq_implies_ex1 by metis
qed

lemma full_run_preserves_invariant:
  assumes
    run: "full_run R x y" and
    P_init: "P x" and
    R_preserves_P: "\<And>x y. R x y \<Longrightarrow> P x \<Longrightarrow> P y"
  shows "P y"
proof -
  from run have "R\<^sup>*\<^sup>* x y"
    unfolding full_run_def by simp
  thus "P y"
    using P_init
  proof (induction x rule: converse_rtranclp_induct)
    case base
    thus ?case
      by assumption
  next
    case (step x x')
    then show ?case
      using R_preserves_P by metis
  qed
qed

definition ground_resolution where
  "ground_resolution D C CD = ord_res.ground_resolution C D CD"

lemma Uniq_ground_resolution: "\<exists>\<^sub>\<le>\<^sub>1DC. ground_resolution D C DC"
  by (simp add: ground_resolution_def ord_res.unique_ground_resolution)

lemma ground_resolution_terminates: "wfP (ground_resolution D)\<inverse>\<inverse>"
proof (rule wfP_if_convertible_to_wfP)
  show "wfP (\<prec>\<^sub>c)"
    using ord_res.wfP_less_cls .
next
  show "\<And>x y. (ground_resolution D)\<inverse>\<inverse> x y \<Longrightarrow> x \<prec>\<^sub>c y"
  unfolding ground_resolution_def conversep_iff
  using ord_res.ground_resolution_smaller_conclusion by metis
qed

lemma not_ground_resolution_mempty_left: "\<not> ground_resolution {#} C x"
  by (auto simp: ground_resolution_def elim: ord_res.ground_resolution.cases)

lemma not_ground_resolution_mempty_right: "\<not> ground_resolution C {#} x"
  by (auto simp: ground_resolution_def elim: ord_res.ground_resolution.cases)

lemma not_tranclp_ground_resolution_mempty_left: "\<not> (ground_resolution {#})\<^sup>+\<^sup>+ C x"
  by (metis not_ground_resolution_mempty_left tranclpD)

lemma not_tranclp_ground_resolution_mempty_right: "\<not> (ground_resolution C)\<^sup>+\<^sup>+ {#} x"
  by (metis not_ground_resolution_mempty_right tranclpD)

lemma left_premise_lt_right_premise_if_ground_resolution:
  "ground_resolution D C DC \<Longrightarrow> D \<prec>\<^sub>c C"
  by (auto simp: ground_resolution_def elim: ord_res.ground_resolution.cases)

lemma left_premise_lt_right_premise_if_tranclp_ground_resolution:
  "(ground_resolution D)\<^sup>+\<^sup>+ C DC \<Longrightarrow> D \<prec>\<^sub>c C"
  by (induction DC rule: tranclp_induct)
    (auto simp add: left_premise_lt_right_premise_if_ground_resolution)

lemma resolvent_lt_right_premise_if_ground_resolution:
  "ground_resolution D C DC \<Longrightarrow> DC \<prec>\<^sub>c C"
  by (simp add: ground_resolution_def ord_res.ground_resolution_smaller_conclusion)

lemma resolvent_lt_right_premise_if_tranclp_ground_resolution:
  "(ground_resolution D)\<^sup>+\<^sup>+ C DC \<Longrightarrow> DC \<prec>\<^sub>c C"
proof (induction DC rule: tranclp_induct)
  case (base y)
  thus ?case
    by (simp add: resolvent_lt_right_premise_if_ground_resolution)
next
  case (step y z)
  have "z \<prec>\<^sub>c y"
    using step.hyps resolvent_lt_right_premise_if_ground_resolution by metis
  thus ?case
    using step.IH by order
qed


text \<open>Exhaustive resolution\<close>

definition eres where
  "eres D C = (THE DC. full_run (ground_resolution D) C DC)"

text \<open>The function \<^const>\<open>eres\<close> performs exhaustive resolution between its two input clauses. The
  first clause is repeatedly used, while the second clause is only use to start the resolution
  chain.\<close>

lemma eres_ident_iff: "eres D C = C \<longleftrightarrow> (\<nexists>DC. ground_resolution D C DC)"
proof (rule iffI)
  assume "eres D C = C"
  thus "\<nexists>DC. ground_resolution D C DC"
    unfolding eres_def
    by (metis Uniq_full_run Uniq_ground_resolution full_run_def ground_resolution_terminates
        ex1_full_run the1_equality')
next
  assume stuck: "\<nexists>DC. ground_resolution D C DC"
  have "(ground_resolution D)\<^sup>*\<^sup>* C C"
    by auto

  with stuck have "full_run (ground_resolution D) C C"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show "eres D C = C"
    unfolding eres_def by (metis the1_equality')
qed

lemma
  assumes
    step1: "ground_resolution D C DC" and
    stuck: "\<nexists>DDC. ground_resolution D DC DDC"
  shows "eres D C = DC"
proof -
  from step1 have "(ground_resolution D)\<^sup>*\<^sup>* C DC"
    by auto

  with stuck have "full_run (ground_resolution D) C DC"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
    unfolding eres_def by (metis the1_equality')
qed

lemma
  assumes
    step1: "ground_resolution D C DC" and
    step2: "ground_resolution D DC DDC" and
    stuck: "\<nexists>DDDC. ground_resolution D DDC DDDC"
  shows "eres D C = DDC"
proof -
  from step1 have "(ground_resolution D)\<^sup>*\<^sup>* C DC"
    by auto

  with step2 have "(ground_resolution D)\<^sup>*\<^sup>* C DDC"
    by (metis rtranclp.simps)

  with stuck have "full_run (ground_resolution D) C DDC"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
    unfolding eres_def by (metis the1_equality')
qed

lemma
  assumes
    step1: "ground_resolution D C DC" and
    step2: "ground_resolution D DC DDC" and
    step3: "ground_resolution D DDC DDDC" and
    stuck: "\<nexists>DDDDC. ground_resolution D DDDC DDDDC"
  shows "eres D C = DDDC"
proof -
  from step1 have "(ground_resolution D)\<^sup>*\<^sup>* C DC"
    by auto

  with step2 have "(ground_resolution D)\<^sup>*\<^sup>* C DDC"
    by (metis rtranclp.simps)

  with step3 have "(ground_resolution D)\<^sup>*\<^sup>* C DDDC"
    by (metis rtranclp.simps)

  with stuck have "full_run (ground_resolution D) C DDDC"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
    unfolding eres_def by (metis the1_equality')
qed

lemma eres_mempty_left[simp]: "eres {#} C = C"
  unfolding eres_def
  by (metis Uniq_full_run Uniq_ground_resolution full_run_def not_ground_resolution_mempty_left
      rtranclp.rtrancl_refl the1_equality')

lemma eres_mempty_right[simp]: "eres C {#} = {#}"
  unfolding eres_def
  by (metis Uniq_full_run Uniq_ground_resolution full_run_def not_ground_resolution_mempty_right
      rtranclp.rtrancl_refl the1_equality')

lemma ex1_eres_eq_full_run_ground_resolution: "\<exists>!DC. eres D C = DC \<and> full_run (ground_resolution D) C DC"
  using ex1_full_run[of "ground_resolution D" C]
  by (metis Uniq_ground_resolution eres_def ground_resolution_terminates theI')

lemma eres_le: "eres D C \<preceq>\<^sub>c C"
proof -
  have "full_run (ground_resolution D) C (eres D C)"
    using ex1_eres_eq_full_run_ground_resolution by metis
  thus ?thesis
  proof (rule full_run_preserves_invariant)
    show "C \<preceq>\<^sub>c C"
      by simp
  next
    show "\<And>x y. ground_resolution D x y \<Longrightarrow> x \<preceq>\<^sub>c C \<Longrightarrow> y \<preceq>\<^sub>c C"
      unfolding ground_resolution_def
      using ord_res.ground_resolution_smaller_conclusion by fastforce
  qed
qed

lemma eres_eq_after_ground_resolution:
  assumes "ground_resolution D C DC"
  shows "eres D C = eres D DC"
  using assms
  by (metis (no_types, opaque_lifting) Uniq_def Uniq_full_run Uniq_ground_resolution
      converse_rtranclpE ex1_eres_eq_full_run_ground_resolution full_run_def)

lemma eres_eq_after_rtranclp_ground_resolution:
  assumes "(ground_resolution D)\<^sup>*\<^sup>* C DC"
  shows "eres D C = eres D DC"
  using assms
  by (induction DC rule: rtranclp_induct) (simp_all add: eres_eq_after_ground_resolution)

lemma eres_eq_after_tranclp_ground_resolution:
  assumes "(ground_resolution D)\<^sup>+\<^sup>+ C DC"
  shows "eres D C = eres D DC"
  using assms
  by (induction DC rule: tranclp_induct) (simp_all add: eres_eq_after_ground_resolution)

lemma resolvable_if_neq_eres:
  assumes "C \<noteq> eres D C"
  shows "\<exists>!DC. ground_resolution D C DC"
  using assms ex1_eres_eq_full_run_ground_resolution
  by (metis (no_types, opaque_lifting) Uniq_def Uniq_full_run Uniq_ground_resolution full_run_def
      rtranclp.rtrancl_refl)

lemma nex_maximal_pos_lit_if_resolvable:
  assumes "ground_resolution D C DC"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
  using assms unfolding ground_resolution_def
  by (metis Uniq_D empty_iff is_pos_def linorder_lit.Uniq_is_maximal_in_mset
      literal.simps(4) ord_res.ground_resolution.cases set_mset_empty)

corollary nex_strictly_maximal_pos_lit_if_resolvable:
  assumes "ground_resolution D C DC"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms nex_maximal_pos_lit_if_resolvable by blast

corollary nex_maximal_pos_lit_if_neq_eres:
  assumes "C \<noteq> eres D C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
  using assms resolvable_if_neq_eres nex_maximal_pos_lit_if_resolvable by metis

corollary nex_strictly_maximal_pos_lit_if_neq_eres:
  assumes "C \<noteq> eres D C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms resolvable_if_neq_eres nex_strictly_maximal_pos_lit_if_resolvable by metis

lemma ground_resolutionD:
  assumes "ground_resolution D C DC"
  shows "\<exists>m A D' C'.
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DC = D' + replicate_mset m (Neg A) + C'"
  using assms
  unfolding ground_resolution_def
proof (cases C D DC rule: ord_res.ground_resolution.cases)
  case (ground_resolutionI A C' D')

  then obtain m where "count C (Neg A) = Suc m"
    by simp

  define C'' where
    "C'' = {#L \<in># C. L \<noteq> Neg A#}"

  have "C = replicate_mset (Suc m) (Neg A) + C''"
    using \<open>count C (Neg A) = Suc m\<close> C''_def
    by (metis filter_eq_replicate_mset union_filter_mset_complement)

  show ?thesis
  proof (intro exI conjI)
    show "linorder_lit.is_greatest_in_mset D (Pos A)"
      using \<open>linorder_lit.is_greatest_in_mset D (Pos A)\<close> .
  next
    show "linorder_lit.is_maximal_in_mset C (Neg A)"
      using ground_resolutionI by simp
  next
    show "D = add_mset (Pos A) D'"
      using \<open>D = add_mset (Pos A) D'\<close> .
  next
    show "C = replicate_mset (Suc m) (Neg A) + C''"
      using \<open>C = replicate_mset (Suc m) (Neg A) + C''\<close> .
  next
    show "Neg A \<notin># C''"
      by (simp add: C''_def)
  next
    show "DC = D' + replicate_mset m (Neg A) + C''"
      using \<open>DC = C' + D'\<close> \<open>C = add_mset (Neg A) C'\<close> \<open>C = replicate_mset (Suc m) (Neg A) + C''\<close>
      by simp
  qed
qed

lemma relpowp_ground_resolutionD:
  assumes "n \<noteq> 0" and "(ground_resolution D ^^ n) C DnC"
  shows "\<exists>m A D' C'. Suc m \<ge> n \<and>
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DnC = repeat_mset n D' + replicate_mset (Suc m - n) (Neg A) + C'"
  using assms
proof (induction n arbitrary: C)
  case 0
  hence False
    by simp
  thus ?case ..
next
  case (Suc n')
  then obtain DC where
    "ground_resolution D C DC" and "(ground_resolution D ^^ n') DC DnC"
    by (metis relpowp_Suc_E2)

  then obtain m A D' C' where
    "linorder_lit.is_greatest_in_mset D (Pos A)" and
    "linorder_lit.is_maximal_in_mset C (Neg A)"
    "D = add_mset (Pos A) D'" and
    "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "DC = D' + replicate_mset m (Neg A) + C'"
    using \<open>ground_resolution D C DC\<close>[THEN ground_resolutionD] by metis

  have "Neg A \<notin># D'"
    using \<open>linorder_lit.is_greatest_in_mset D (Pos A)\<close>
    unfolding \<open>D = add_mset (Pos A) D'\<close>
    unfolding linorder_lit.is_greatest_in_mset_iff
    by auto

  show ?case
  proof (cases n')
    case 0
    hence "DnC = DC"
      using \<open>(ground_resolution D ^^ n') DC DnC\<close> by simp

    show ?thesis
      unfolding 0 \<open>DnC = DC\<close>
      unfolding repeat_mset_Suc repeat_mset_0 empty_neutral
      unfolding diff_Suc_Suc minus_nat.diff_0
      using \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> \<open>D = add_mset (Pos A) D'\<close>
        \<open>DC = D' + replicate_mset m (Neg A) + C'\<close> \<open>Neg A \<notin># C'\<close>
        \<open>linorder_lit.is_greatest_in_mset D (Pos A)\<close> \<open>linorder_lit.is_maximal_in_mset C (Neg A)\<close>
      using linorder_lit.is_greatest_in_mset_iff
      by blast
  next
    case (Suc n'')
    hence "n' \<noteq> 0"
      by presburger
    then obtain m' A' D'' DC' where "n' \<le> Suc m'" and
       "ord_res.is_strictly_maximal_lit (Pos A') D" and
       "ord_res.is_maximal_lit (Neg A') DC" and
       "D = add_mset (Pos A') D''" and
       "DC = replicate_mset (Suc m') (Neg A') + DC'" and
       "Neg A' \<notin># DC'" and
       "DnC = repeat_mset n' D'' + replicate_mset (Suc m' - n') (Neg A') + DC'"
      using Suc.IH[OF _ \<open>(ground_resolution D ^^ n') DC DnC\<close>]
      by metis

    have "A' = A"
      using \<open>ord_res.is_strictly_maximal_lit (Pos A') D\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
      by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset
          linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.inject(1))

    hence "D'' = D'"
      using \<open>D = add_mset (Pos A') D''\<close> \<open>D = add_mset (Pos A) D'\<close> by auto

    have "m = Suc m'"
      using \<open>DC = D' + replicate_mset m (Neg A) + C'\<close> \<open>DC = replicate_mset (Suc m') (Neg A') + DC'\<close>
        \<open>Neg A \<notin># D'\<close> \<open>Neg A \<notin># C'\<close> \<open>Neg A' \<notin># DC'\<close>
      unfolding \<open>A' = A\<close>
      by (metis add_0 count_eq_zero_iff count_replicate_mset count_union union_commute)

    hence "DC' = D' + C'"
      using \<open>DC = D' + replicate_mset m (Neg A) + C'\<close> \<open>DC = replicate_mset (Suc m') (Neg A') + DC'\<close>
      by (simp add: \<open>A' = A\<close>)

    show ?thesis
    proof (intro exI conjI)
      show "Suc n' \<le> Suc (Suc m')"
        using \<open>n' \<le> Suc m'\<close> by presburger
    next
      show "ord_res.is_strictly_maximal_lit (Pos A) D"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> .
    next
      show "ord_res.is_maximal_lit (Neg A) C"
        using \<open>ord_res.is_maximal_lit (Neg A) C\<close> by metis
    next
      show "D = add_mset (Pos A) D'"
        using \<open>D = add_mset (Pos A) D'\<close> .
    next
      show "C = replicate_mset (Suc (Suc m')) (Neg A) + C'"
        using \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> \<open>m = Suc m'\<close> by argo
    next
      show "Neg A \<notin># C'"
        using \<open>Neg A \<notin># C'\<close> .
    next
      show "DnC = repeat_mset (Suc n') D' + replicate_mset (Suc (Suc m') - Suc n') (Neg A) + C'"
        using \<open>DnC = repeat_mset n' D'' + replicate_mset (Suc m' - n') (Neg A') + DC'\<close>
        unfolding \<open>A' = A\<close> \<open>D'' = D'\<close> diff_Suc_Suc \<open>DC' = D' + C'\<close>
        by simp
    qed
  qed
qed


lemma tranclp_ground_resolutionD:
  assumes "(ground_resolution D)\<^sup>+\<^sup>+ C DnC"
  shows "\<exists>n m A D' C'. Suc m \<ge> Suc n \<and>
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DnC = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'"
proof -
  from assms obtain n :: nat where
    "(ground_resolution D ^^ Suc n) C DnC"
    by (metis Suc_pred tranclp_power)
  thus ?thesis
    using assms relpowp_ground_resolutionD
    by (meson nat.discI)
qed

lemma eres_not_identD:
  assumes "eres D C \<noteq> C"
  shows "\<exists>m A D' C'.
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    eres D C = repeat_mset (Suc m) D' + C'"
proof -
  have "\<And>n. Suc n \<noteq> 0"
    by presburger

  obtain n where
    steps: "(ground_resolution D ^^ Suc n) C (eres D C)" and
    stuck: "\<nexists>x. ground_resolution D (eres D C) x"
    using \<open>eres D C \<noteq> C\<close> ex1_eres_eq_full_run_ground_resolution
    by (metis full_run_def gr0_conv_Suc rtranclpD tranclp_power)

  obtain m A D' C' where
    "Suc n \<le> Suc m" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D" and
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_eq: "D = add_mset (Pos A) D'" and
    C_eq: "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    eres_eq: "eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'"
    using relpowp_ground_resolutionD[of "Suc n", OF \<open>Suc n \<noteq> 0\<close> steps] by metis

  from stuck have "count (eres D C) (Neg A) = 0"
  proof (rule contrapos_np)
    assume "count (eres D C) (Neg A) \<noteq> 0"
    then obtain ERES' where "eres D C = add_mset (Neg A) ERES'"
      by (meson count_eq_zero_iff mset_add)

    moreover have "ord_res.is_maximal_lit (Neg A) (eres D C)"
      unfolding linorder_lit.is_maximal_in_mset_iff
    proof (intro conjI ballI impI)
      show "Neg A \<in># eres D C"
        unfolding \<open>eres D C = add_mset (Neg A) ERES'\<close> by simp
    next
      fix L
      assume "L \<in># eres D C" and "L \<noteq> Neg A"
      hence "L \<in># repeat_mset (Suc n) D' \<or> L \<in># C'"
        unfolding eres_eq
        by (metis Zero_not_Suc count_replicate_mset in_countE union_iff)
      thus "\<not> Neg A \<prec>\<^sub>l L"
      proof (elim disjE)
        assume "L \<in># repeat_mset (Suc n) D'"
        hence "L \<in># D'"
          using member_mset_repeat_msetD by metis
        hence "L \<prec>\<^sub>l Pos A"
          using D_max_lit
          unfolding D_eq linorder_lit.is_greatest_in_mset_iff by simp
        also have "Pos A \<prec>\<^sub>l Neg A"
          by simp
        finally show ?thesis
          by order
      next
        assume "L \<in># C'"
        thus ?thesis
          using C_eq \<open>L \<noteq> Neg A\<close> C_max_lit linorder_lit.is_maximal_in_mset_iff by auto
      qed
    qed

    moreover have "D \<prec>\<^sub>c eres D C"
      using D_max_lit
      using \<open>ord_res.is_maximal_lit (Neg A) (eres D C)\<close>
      using linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal[of D "Pos A" "eres D C" "Neg A", simplified]
      using multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M by blast

    ultimately show "\<exists>x. ground_resolution D (eres D C) x"
      unfolding ground_resolution_def
      using D_eq D_max_lit
      using ord_res.ground_resolutionI[of "eres D C" A ERES' D D' "ERES' + D'"]
      by metis
  qed

  hence "m = n"
    using \<open>eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'\<close>
    using \<open>Suc n \<le> Suc m\<close> by auto

  show ?thesis
  proof (intro exI conjI)
    show "ord_res.is_strictly_maximal_lit (Pos A) D"
      using D_max_lit .
  next
    show "ord_res.is_maximal_lit (Neg A) C"
      using C_max_lit .
  next
    show "D = add_mset (Pos A) D'"
      using D_eq .
  next
    show "C = replicate_mset (Suc m) (Neg A) + C'"
      using C_eq .
  next
    show "Neg A \<notin># C'"
      using \<open>Neg A \<notin># C'\<close> .
  next
    show "eres D C = repeat_mset (Suc m) D' + C'"
      using eres_eq unfolding \<open>m = n\<close> by simp
  qed
qed

lemma lit_in_one_of_resolvents_if_in_eres:
  fixes L :: "'f gterm literal" and C D :: "'f gclause"
  assumes "L \<in># eres C D"
  shows "L \<in># C \<or> L \<in># D"
proof (cases "eres C D = D")
  assume "eres C D = D"
  thus "L \<in># C \<or> L \<in># D"
    using \<open>L \<in># eres C D\<close> by argo
next
  assume "eres C D \<noteq> D"
  thus "L \<in># C \<or> L \<in># D"
    using \<open>L \<in># eres C D\<close>
    by (metis eres_not_identD member_mset_repeat_msetD repeat_mset_distrib_add_mset union_iff)
qed

lemma strong_lit_in_one_of_resolvents_if_in_eres:
  fixes L :: "'f gterm literal" and C D :: "'f gclause"
  assumes
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    K_in: "K \<in># eres C D"
  shows "K \<in># C \<and> K \<noteq> -L \<or> K \<in># D"
proof (cases "eres C D = D")
  assume "eres C D = D"
  thus "K \<in># C \<and> K \<noteq> -L \<or> K \<in># D"
    using K_in by argo
next
  assume "eres C D \<noteq> D"
  then obtain m :: nat and A :: "'f gterm" and C' D' :: "'f gterm literal multiset" where
    C_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) C" and
    D_max_lit': "ord_res.is_maximal_lit (Neg A) D" and
    C_eq: "C = add_mset (Pos A) C'" and
    D_eq: "D = replicate_mset (Suc m) (Neg A) + D'" and
    "Neg A \<notin># D'" and
    "eres C D = repeat_mset (Suc m) C' + D'"
    using eres_not_identD by metis

  have L_eq: "L = Neg A"
    using D_max_lit D_max_lit' by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "K \<in># repeat_mset (Suc m) C' + D'"
    using K_in unfolding \<open>eres C D = repeat_mset (Suc m) C' + D'\<close> .

  hence "K \<in># repeat_mset (Suc m) C' \<or> K \<in># D'"
    unfolding Multiset.union_iff .

  hence "K \<in># C' \<or> K \<in># D'"
    unfolding member_mset_repeat_mset_Suc .

  thus "K \<in># C \<and> K \<noteq> -L \<or> K \<in># D"
    sketch (elim disjE)
  proof (elim disjE)
    assume "K \<in># C'"

    hence "K \<in># C \<and> K \<noteq> - L"
      using C_max_lit
      unfolding C_eq L_eq linorder_lit.is_greatest_in_mset_iff by auto

    thus "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D" ..
  next
    assume "K \<in># D'"

    hence "K \<in># D"
      unfolding D_eq by simp

    thus "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D" ..
  qed
qed

lemma lit_in_eres_lt_greatest_lit_in_grestest_resolvant:
  fixes K L :: "'f gterm literal" and C D :: "'f gclause"
  assumes "eres C D \<noteq> D" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    "- L \<notin># D" and
    K_in_eres: "K \<in># eres C D"
  shows "atm_of K \<prec>\<^sub>t atm_of L"
proof -
  obtain m :: nat and A :: "'f gterm" and C' D' :: "'f gterm literal multiset" where
    C_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) C" and
    C_def: "C = add_mset (Pos A) C'" and
    "D = replicate_mset (Suc m) (Neg A) + D'" and
    "Neg A \<notin># D'" and
    "eres C D = repeat_mset (Suc m) C' + D'"
    using \<open>eres C D \<noteq> D\<close>[THEN eres_not_identD] by metis

  have "L = Neg A"
    using assms(1) D_max_lit C_max_lit
    by (metis ground_resolutionD linorder_lit.Uniq_is_greatest_in_mset
        linorder_lit.Uniq_is_maximal_in_mset resolvable_if_neq_eres the1_equality' uminus_Pos)

  have "K \<in># repeat_mset (Suc m) C' + D'"
    using K_in_eres unfolding \<open>eres C D = repeat_mset (Suc m) C' + D'\<close> .

  hence "K \<in># repeat_mset (Suc m) C' \<or> K \<in># D'"
    unfolding Multiset.union_iff .

  hence "K \<in># C' \<or> K \<in># D'"
    unfolding member_mset_repeat_mset_Suc .

  thus "atm_of K \<prec>\<^sub>t atm_of L"
  proof (elim disjE)
    assume "K \<in># C'"
    hence "K \<prec>\<^sub>l Pos A"
      using C_max_lit C_def \<open>L = Neg A\<close>
      unfolding linorder_lit.is_greatest_in_mset_iff
      by simp
    thus "atm_of K \<prec>\<^sub>t atm_of L"
      unfolding \<open>L = Neg A\<close> literal.sel
      by (cases K) simp_all
  next
    assume "K \<in># D'"
    hence "K \<prec>\<^sub>l Neg A"
      by (metis D_max_lit \<open>D = replicate_mset (Suc m) (Neg A) + D'\<close> \<open>L = Neg A\<close> \<open>Neg A \<notin># D'\<close>
          linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE union_iff)

    moreover have "K \<noteq> Pos A"
      using \<open>- L \<notin># D\<close>
      using \<open>D = replicate_mset (Suc m) (Neg A) + D'\<close> \<open>K \<in># D'\<close> \<open>L = Neg A\<close> by fastforce

    ultimately have "K \<prec>\<^sub>l Pos A"
      by (metis linorder_lit.less_asym linorder_lit.less_linear literal.exhaust
          ord_res.less_lit_simps(1) ord_res.less_lit_simps(3) ord_res.less_lit_simps(4))

    thus "atm_of K \<prec>\<^sub>t atm_of L"
      unfolding \<open>L = Neg A\<close> literal.sel
      by (cases K) simp_all
  qed
qed

lemma eres_entails_resolvent:
  fixes C D :: "'f gterm clause"
  assumes "(ground_resolution C)\<^sup>+\<^sup>+ D\<^sub>0 D"
  shows "{eres C D\<^sub>0} \<TTurnstile>e {D}"
  unfolding true_clss_singleton
proof (intro allI impI)
  have "eres C D\<^sub>0 = eres C D"
    using assms eres_eq_after_tranclp_ground_resolution by metis

  obtain n m :: nat and A :: "'f gterm" and C' D\<^sub>0' :: "'f gterm clause" where
    "Suc n \<le> Suc m" and
    "ord_res.is_strictly_maximal_lit (Pos A) C" and
    "ord_res.is_maximal_lit (Neg A) D\<^sub>0" and
    "C = add_mset (Pos A) C'" and
    "D\<^sub>0 = replicate_mset (Suc m) (Neg A) + D\<^sub>0'" and
    "Neg A \<notin># D\<^sub>0'" and
    "D = repeat_mset (Suc n) C' + replicate_mset (Suc m - Suc n) (Neg A) + D\<^sub>0'"
    using \<open>(ground_resolution C)\<^sup>+\<^sup>+ D\<^sub>0 D\<close>[THEN tranclp_ground_resolutionD] by metis

  fix I :: "'f gterm set"
  assume "I \<TTurnstile> eres C D\<^sub>0"
  show "I \<TTurnstile> D"
  proof (cases "eres C D\<^sub>0 = D")
    case True
    thus ?thesis
      using \<open>I \<TTurnstile> eres C D\<^sub>0\<close> by argo
  next
    case False
    then obtain k :: nat and D' :: "'f gterm clause" where
      "ord_res.is_strictly_maximal_lit (Pos A) C" and
      "C = add_mset (Pos A) C'" and
      "D = replicate_mset (Suc k) (Neg A) + D'" and
      "Neg A \<notin># D'" and
      "eres C D = repeat_mset (Suc k) C' + D'"
      unfolding \<open>eres C D\<^sub>0 = eres C D\<close>
      using eres_not_identD
      using \<open>ord_res.is_strictly_maximal_lit (Pos A) C\<close> \<open>C = add_mset (Pos A) C'\<close>
      by (metis Uniq_D add_mset_remove_trivial linorder_lit.Uniq_is_greatest_in_mset literal.sel(1))

    have "I \<TTurnstile> repeat_mset (Suc k) C' + D'"
      using \<open>I \<TTurnstile> eres C D\<^sub>0\<close>
      unfolding \<open>eres C D\<^sub>0 = eres C D\<close> \<open>eres C D = repeat_mset (Suc k) C' + D'\<close> .

    hence "I \<TTurnstile> D' \<or> I \<TTurnstile> repeat_mset (Suc k) C'"
      by auto

    thus "I \<TTurnstile> D"
    proof (elim disjE)
      assume "I \<TTurnstile> D'"
      thus "I \<TTurnstile> D"
        unfolding \<open>D = replicate_mset (Suc k) (Neg A) + D'\<close>
        by simp
    next
      assume "I \<TTurnstile> repeat_mset (Suc k) C'"
      thus "I \<TTurnstile> D"
        using \<open>D = replicate_mset (Suc k) (Neg A) + D'\<close>
        using \<open>D = repeat_mset (Suc n) C' + replicate_mset (Suc m - Suc n) (Neg A) + D\<^sub>0'\<close>
        by (metis member_mset_repeat_msetD repeat_mset_Suc true_cls_def true_cls_union)
    qed
  qed
qed


inductive ord_res_3 where
  factoring: "
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    U\<^sub>e\<^sub>f' = finsert (efac C) U\<^sub>e\<^sub>f \<Longrightarrow>
    ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f')" |

  resolution: "
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L} \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (U\<^sub>e\<^sub>r', U\<^sub>e\<^sub>f)"

inductive ord_res_3_step where
  "ord_res_3 N s s' \<Longrightarrow> ord_res_3_step (N, s) (N, s')"

inductive ord_res_3_final where
  "ord_res_final (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<Longrightarrow> ord_res_3_final (N, (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f))"

inductive ord_res_3_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_3_load N (N, ({||}, {||}))"

interpretation ord_res_3_semantics: semantics where
  step = ord_res_3_step and
  final = ord_res_3_final
proof unfold_locales
  fix S3 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>r\<^sub>r U\<^sub>e\<^sub>f :: "'f gterm clause fset" where
    S3_def: "S3 = (N, (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f))"
    by (metis prod.exhaust)

  assume "ord_res_3_final S3"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (simp add: S3_def ord_res_3_final.simps ord_res_final_def)
  thus "finished ord_res_3_step S3"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    hence "is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) {#}"
      using is_least_false_clause_mempty by metis
    hence "\<nexists>C L. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C \<and> linorder_lit.is_maximal_in_mset C L"
      by (metis Uniq_D Uniq_is_least_false_clause bot_fset.rep_eq fBex_fempty
          linorder_lit.is_maximal_in_mset_iff set_mset_empty)
    hence "\<nexists>x. ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f) x"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def ord_res_3_step.simps S3_def)
  next
    assume "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    hence "\<nexists>C. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      unfolding ex_false_clause_def is_least_false_clause_def
      by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
          linorder_cls.is_least_in_fset_ffilterD(2))
    hence "\<nexists>x. ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>e\<^sub>f) x"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def ord_res_3_step.simps S3_def)
  qed
qed

interpretation ord_res_3_language: language where
  step = ord_res_3_step and
  final = ord_res_3_final and
  load = ord_res_3_load
  by unfold_locales

inductive ord_res_2_matches_ord_res_3 where
  "(\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
      (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r) \<Longrightarrow>
  ord_res_2_matches_ord_res_3 (N, (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)) (N, (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f))"

lemma is_least_false_clause_finsert_cancel:
  assumes
    C_unproductive: "ord_res.production (fset (finsert C N)) C = {}" and
    C_entailed_by_smaller: "\<exists>D |\<in>| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (finsert C N) = is_least_false_clause N"
proof (intro ext iffI)
  fix E
  assume E_least: "is_least_false_clause (finsert C N) E"
  hence
    E_in: "E |\<in>| finsert C N" and
    E_false: "\<not> ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E" and
    E_least: "(\<forall>y |\<in>| finsert C N. y \<noteq> E \<longrightarrow> \<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y \<longrightarrow> E \<prec>\<^sub>c y)"
    unfolding atomize_conj is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  obtain D where
    "D |\<in>| N" and "D \<prec>\<^sub>c C" and "{D} \<TTurnstile>e {C}"
    using C_entailed_by_smaller by metis

  show "is_least_false_clause N E"
  proof (cases "C = E")
    case True

    have "E \<prec>\<^sub>c D"
    proof (rule E_least[rule_format])
      show "D |\<in>| finsert C N"
        using \<open>D |\<in>| N\<close> by simp
    next
      show "D \<noteq> E"
        using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> by order
    next
      show "\<not> ord_res_Interp (fset (finsert C N)) D \<TTurnstile> D"
        using E_false
      proof (rule contrapos_nn)
        assume "ord_res_Interp (fset (finsert C N)) D \<TTurnstile> D"
        thus "ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E"
          using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> \<open>{D} \<TTurnstile>e {C}\<close> ord_res.entailed_clause_stays_entailed by auto
      qed
    qed
    hence False
      using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> by order
    thus ?thesis ..
  next
    case False
    show ?thesis
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "E |\<in>| N"
        using E_in \<open>C \<noteq> E\<close> by simp
    next
      have "ord_res_Interp (fset (finsert C N)) E = ord_res_Interp (fset N) E"
        using C_unproductive Interp_insert_unproductive by simp
      thus "\<not> ord_res_Interp (fset N) E \<TTurnstile> E"
        using E_false by argo
    next
      show "\<And>y. y |\<in>| N \<Longrightarrow> y \<noteq> E \<Longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<Longrightarrow> E \<prec>\<^sub>c y"
        using E_least C_unproductive Interp_insert_unproductive by auto
    qed
  qed
next
  fix E
  assume "is_least_false_clause N E"
  hence
    E_in: "E |\<in>| N" and
    E_false: "\<not> ord_res_Interp (fset N) E \<TTurnstile> E" and
    E_least: "(\<forall>y |\<in>| N. y \<noteq> E \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> E \<prec>\<^sub>c y)"
    unfolding atomize_conj is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  show "is_least_false_clause (finsert C N) E"
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    show "E |\<in>| finsert C N"
      using E_in by simp
  next
    show "\<not> ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E"
      using E_least E_false C_unproductive Interp_insert_unproductive by simp
  next
    fix y
    assume "y |\<in>| finsert C N" and "y \<noteq> E" and "\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y"
    show "E \<prec>\<^sub>c y"
    proof (cases "y = C")
      case True
      thus ?thesis
      using E_least \<open>\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y\<close>
      by (metis (no_types, lifting) C_entailed_by_smaller C_unproductive Interp_insert_unproductive
          finite_fset fset_simps(2) linorder_cls.dual_order.strict_trans
          ord_res.entailed_clause_stays_entailed true_clss_singleton)
    next
      case False
      thus ?thesis
        using E_least \<open>y |\<in>| finsert C N\<close> \<open>y \<noteq> E\<close> \<open>\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y\<close>
        using C_unproductive Interp_insert_unproductive by auto
    qed
  qed
qed

lemma is_least_false_clause_funion_cancel_right_strong:
  assumes
    "\<forall>C |\<in>| N2 - N1. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2 - N1. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms
proof (induction N2)
  case empty
  thus ?case
    by simp
next
  case (insert C N2)

  have IH: "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  proof (rule insert.IH)
    show "\<forall>C|\<in>|N2 |-| N1. \<forall>U. ord_res.production U C = {}"
      using insert.prems(1) by auto
  next
    show "\<forall>C|\<in>|N2 |-| N1. \<exists>D|\<in>|N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
      using insert.prems(2) by auto
  qed

  show ?case
  proof (cases "C |\<in>| N1")
    case True
    hence "is_least_false_clause (N1 |\<union>| finsert C N2) = is_least_false_clause (N1 |\<union>| N2)"
      by (simp add: finsert_absorb)
    also have "\<dots> = is_least_false_clause N1"
      using IH .
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using is_least_false_clause_finsert_cancel IH
      by (metis finsertCI fminusI funionI1 funion_finsert_right insert.prems(1) insert.prems(2))
  qed
qed

lemma is_least_false_clause_funion_cancel_right:
  assumes
    "\<forall>C |\<in>| N2. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms is_least_false_clause_funion_cancel_right_strong by simp

lemma is_least_false_clause_conv_if_partial_resolution_invariant:
  assumes "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
  shows "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
proof -
  have "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)"
    by (simp add: sup_commute sup_left_commute)
  also have "\<dots> = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
  proof (rule is_least_false_clause_funion_cancel_right)
    show "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<forall>U. ord_res.production U C = {}"
    proof (intro ballI)
      fix C
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. (\<exists>C'. ground_resolution D C C')"
        using assms by (metis eres_eq_after_tranclp_ground_resolution resolvable_if_neq_eres)
      hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
        using nex_strictly_maximal_pos_lit_if_resolvable by metis
      thus "\<forall>U. ord_res.production U C = {}"
        using unproductive_if_nex_strictly_maximal_pos_lit by metis
    qed
  next
    show "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
    proof (intro ballI)
      fix C
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      then obtain D1 D2 where
        "D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
        "C \<noteq> eres D1 D2" and
        "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using assms by metis

      have "eres D1 D2 = eres D1 C"
        using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_eq_after_tranclp_ground_resolution by metis

      show "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
      proof (intro bexI conjI)
        have "eres D1 C \<preceq>\<^sub>c C"
          using eres_le .
        thus "eres D1 D2 \<prec>\<^sub>c C"
          using \<open>C \<noteq> eres D1 D2\<close> \<open>eres D1 D2 = eres D1 C\<close> by order
      next
        show "{eres D1 D2} \<TTurnstile>e {C}"
          using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_entails_resolvent by metis
      next
        show "eres D1 D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          using \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> by simp
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma ord_res_2_final_iff_ord_res_3_final:
  assumes match: "ord_res_2_matches_ord_res_3 S\<^sub>2 S\<^sub>3"
  shows "ord_res_2_final S\<^sub>2 \<longleftrightarrow> ord_res_3_final S\<^sub>3"
  using match
proof (cases S\<^sub>2 S\<^sub>3 rule: ord_res_2_matches_ord_res_3.cases)
  case match_hyps: (1 U\<^sub>p\<^sub>r N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)

  note invars = match_hyps(3-)

  have U\<^sub>p\<^sub>r_spec: "\<forall>C|\<in>|U\<^sub>p\<^sub>r. \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
    using invars by argo

  have least_false_spec: "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) =
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    using invars is_least_false_clause_conv_if_partial_resolution_invariant by metis

  have U\<^sub>p\<^sub>r_unproductive: "\<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
  proof (intro ballI)
    fix C
    assume "C |\<in>| U\<^sub>p\<^sub>r"
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
      using U\<^sub>p\<^sub>r_spec
      by (metis eres_eq_after_tranclp_ground_resolution nex_strictly_maximal_pos_lit_if_neq_eres)
    thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f: "\<And>C.
    ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: funion_left_commute sup_commute)

  have "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
  proof (rule iffI)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    then obtain C where "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      using obtains_least_false_clause_if_ex_false_clause by metis
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      using least_false_spec ex_false_clause_iff by metis
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      unfolding ex_false_clause_def
      unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f
      by auto
  qed

  moreover have "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f \<or> {#} |\<in>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
      by auto
    thus "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f"
      thus ?thesis
        by auto
    next
      have "{#} |\<notin>| U\<^sub>p\<^sub>r"
        using U\<^sub>p\<^sub>r_spec[rule_format, of "{#}"]
        by (metis eres_eq_after_tranclp_ground_resolution eres_mempty_right)
      moreover assume "{#} |\<in>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
      ultimately show ?thesis
        by simp
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    then show "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      by auto
  qed

  ultimately have "ord_res_final (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = ord_res_final (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    unfolding ord_res_final_def by argo

  thus "ord_res_2_final S\<^sub>2 \<longleftrightarrow> ord_res_3_final S\<^sub>3"
    unfolding match_hyps(1,2)
    by (simp add: ord_res_2_final.simps ord_res_3_final.simps sup_assoc)
qed

definition ord_res_2_measure where
  "ord_res_2_measure S1 =
    (let (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) = S1 in
    (if \<exists>C. is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C then
      The (is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))
    else
      {#}))"

lemma tranclp_if_relpowp: "n \<noteq> 0 \<Longrightarrow> (R ^^ n) x y \<Longrightarrow> R\<^sup>+\<^sup>+ x y"
  by (meson bot_nat_0.not_eq_extremum tranclp_power)

lemma clause_true_if_resolved_true:
  assumes
    "(ground_resolution D)\<^sup>+\<^sup>+ C DC" and
    D_productive: "ord_res.production N D \<noteq> {}" and
    C_true: "ord_res_Interp N DC \<TTurnstile> DC"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof -
  obtain n where
    steps: "(ground_resolution D ^^ Suc n) C DC"
    using \<open>(ground_resolution D)\<^sup>+\<^sup>+ C DC\<close>
    by (metis less_not_refl not0_implies_Suc tranclp_power)

  obtain m A D' C' where
    "n \<le> m" and
    "ord_res.is_strictly_maximal_lit (Pos A) D" and
    "ord_res.is_maximal_lit (Neg A) C" and
    "D = add_mset (Pos A) D'" and
    "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'"
    using relpowp_ground_resolutionD[OF Suc_not_Zero steps]
    by (metis diff_Suc_Suc Suc_le_mono)

  have "Neg A \<notin># D'"
    by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
        ord_res.less_lit_simps(4) linorder_lit.is_greatest_in_mset_iff linorder_trm.eq_refl
        linorder_trm.leD remove1_mset_add_mset_If)

  have "DC \<prec>\<^sub>c C"
  proof (cases "m = n")
    case True
    show ?thesis
    proof (intro one_step_implies_multp[of _ _ _ "{#}", simplified] ballI)
      show "C \<noteq> {#}"
        by (simp add: \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>)
    next
      fix L
      assume "L \<in># DC"
      hence "L \<in># D' \<or> L \<in># C'"
        unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close> \<open>m = n\<close>
        using member_mset_repeat_msetD by fastforce
      hence "L \<prec>\<^sub>l Neg A"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> \<open>ord_res.is_maximal_lit (Neg A) C\<close>
        unfolding \<open>D = add_mset (Pos A) D'\<close> \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>
        unfolding linorder_lit.is_maximal_in_mset_iff linorder_lit.is_greatest_in_mset_iff
        by (metis \<open>Neg A \<notin># C'\<close> add_mset_remove_trivial ord_res.less_lit_simps(4)
            linorder_lit.antisym_conv3 linorder_lit.dual_order.strict_trans
            linorder_trm.dual_order.asym union_iff)

      moreover have "Neg A \<in># C"
        by (simp add: \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>)

      ultimately show "\<exists>K \<in># C. L \<prec>\<^sub>l K"
        by metis
    qed
  next
    case False
    hence "n < m"
      using \<open>n \<le> m\<close> by presburger

    have "multp\<^sub>H\<^sub>O (\<prec>\<^sub>l) DC C"
    proof (rule linorder_lit.multp\<^sub>H\<^sub>O_if_same_maximal_and_count_lt)
      show "ord_res.is_maximal_lit (Neg A) DC"
        unfolding linorder_lit.is_maximal_in_mset_iff
      proof (intro conjI ballI impI)
        show "Neg A \<in># DC"
          unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
          using \<open>n < m\<close> by simp
      next
        fix L
        assume "L \<in># DC" and "L \<noteq> Neg A"
        hence "L \<in># D' \<or> L \<in># C'"
          unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
          by (metis in_replicate_mset member_mset_repeat_msetD union_iff)
        thus "\<not> Neg A \<prec>\<^sub>l L"
          using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> \<open>ord_res.is_maximal_lit (Neg A) C\<close>
          unfolding \<open>D = add_mset (Pos A) D'\<close> \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>
          unfolding linorder_lit.is_maximal_in_mset_iff linorder_lit.is_greatest_in_mset_iff
          by (metis \<open>L \<noteq> Neg A\<close> add_mset_diff_bothsides diff_zero
              linorder_lit.dual_order.strict_trans linorder_trm.less_irrefl
              ord_res.less_lit_simps(4) union_iff)
      qed
    next
      show "ord_res.is_maximal_lit (Neg A) C"
        using \<open>ord_res.is_maximal_lit (Neg A) C\<close> .
    next
      have "count DC (Neg A) = count (repeat_mset (Suc n) D') (Neg A) +
      count (replicate_mset (m - n) (Neg A)) (Neg A) + count C' (Neg A)"
        unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close> by simp
      also have "\<dots> = count D' (Neg A) * Suc n + count {#Neg A#} (Neg A) * (m - n) + count C' (Neg A)"
        by simp
      also have "\<dots> = 0 * Suc n + 1 * (m - n) + 0"
        by (simp add: \<open>Neg A \<notin># C'\<close> \<open>Neg A \<notin># D'\<close> count_eq_zero_iff)
      also have "\<dots> = m - n"
        by presburger
      also have "\<dots> < Suc m"
        by presburger
      also have "\<dots> = 1 * Suc m + 0"
        by presburger
      also have "\<dots> = count {#Neg A#} (Neg A) * Suc m + count C' (Neg A)"
        by (simp add: \<open>Neg A \<notin># C'\<close> count_eq_zero_iff)
      also have "\<dots> = count (replicate_mset (Suc m) (Neg A)) (Neg A) + count C' (Neg A)"
        by simp
      also have "\<dots> = count C (Neg A)"
        unfolding \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> by simp
      finally show "count DC (Neg A) < count C (Neg A)" .
    qed
    thus ?thesis
      by (simp add: multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M)
  qed

  with C_true have "ord_res_Interp N C \<TTurnstile> DC"
    using ord_res.entailed_clause_stays_entailed by metis

  thus "ord_res_Interp N C \<TTurnstile> C"
    unfolding true_cls_def
  proof (elim bexE)
    fix L
    assume
      L_in: "L \<in># DC" and
      L_true: "ord_res_Interp N C \<TTurnstile>l L"

    from L_in have "L \<in># D' \<or> L = Neg A \<or> L \<in># C'"
      unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
      by (metis in_replicate_mset member_mset_repeat_msetD union_iff)

    moreover have "L \<notin># D'"
    proof (rule notI)
      assume "L \<in># D'"

      moreover have "\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile> add_mset (Pos A) D'"
        using D_productive[unfolded \<open>D = add_mset (Pos A) D'\<close>]
        unfolding ord_res.production_unfold
        by fast

      ultimately have "\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile>l L"
        by auto

      have "L \<prec>\<^sub>l Pos A"
        using \<open>D = add_mset (Pos A) D'\<close> \<open>L \<in># D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
          linorder_lit.is_greatest_in_mset_iff by fastforce

      have "\<not> ord_res_Interp N C \<TTurnstile>l L"
      proof (cases L)
        case (Pos B)
        hence "B \<notin> ord_res.interp N (add_mset (Pos A) D')"
          using \<open>\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile>l L\<close> by simp

        moreover have "add_mset (Pos A) D' \<prec>\<^sub>c C"
          by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>\<And>thesis. (\<And>m A D' C'. \<lbrakk>n \<le> m; ord_res.is_strictly_maximal_lit (Pos A) D; ord_res.is_maximal_lit (Neg A) C; D = add_mset (Pos A) D'; C = replicate_mset (Suc m) (Neg A) + C'; Neg A \<notin># C'; DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M ord_res.less_lit_simps(2) reflclp_iff)

        ultimately have "B \<notin> ord_res.interp N C"
          using \<open>L \<prec>\<^sub>l Pos A\<close>[unfolded Pos, simplified]
          using ord_res.interp_fixed_for_smaller_literals
          by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.sel(1))

        moreover have "B \<notin> ord_res.production N C"
          by (metis Uniq_D \<open>ord_res.is_maximal_lit (Neg A) C\<close> ground_ordered_resolution_calculus.mem_productionE linorder_lit.Uniq_is_maximal_in_mset linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.simps(4) ord_res.ground_ordered_resolution_calculus_axioms)

        ultimately show ?thesis
          unfolding Pos by simp
      next
        case (Neg B)
        hence "B \<in> ord_res.interp N (add_mset (Pos A) D')"
          using \<open>\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile>l L\<close> by simp

        moreover have "add_mset (Pos A) D' \<prec>\<^sub>c C"
          by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>\<And>thesis. (\<And>m A D' C'. \<lbrakk>n \<le> m; ord_res.is_strictly_maximal_lit (Pos A) D; ord_res.is_maximal_lit (Neg A) C; D = add_mset (Pos A) D'; C = replicate_mset (Suc m) (Neg A) + C'; Neg A \<notin># C'; DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M ord_res.less_lit_simps(2) reflclp_iff)

        ultimately have "B \<in> ord_res.interp N C"
          by (metis Un_iff ord_res.not_interp_to_Interp_imp_le linorder_cls.leD)

        then show ?thesis
          unfolding Neg
          by simp
      qed

      with L_true show False
        by contradiction
    qed

    ultimately have "L \<in># C"
      unfolding \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> by simp

    with L_true show "\<exists>L \<in># C. ord_res_Interp N C \<TTurnstile>l L"
      by metis
  qed
qed

lemma clause_true_if_eres_true:
  assumes
    "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
    "C \<noteq> eres D1 C" and
    eres_C_true: "ord_res_Interp N (eres D1 C) \<TTurnstile> eres D1 C"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof -
  obtain n where
    steps: "(ground_resolution D1 ^^ Suc n) D2 C"
    using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close>
    by (metis less_not_refl not0_implies_Suc tranclp_power)

  obtain m A D' C' where
    "n \<le> m" and
    "ord_res.is_strictly_maximal_lit (Pos A) D1" and
    "ord_res.is_maximal_lit (Neg A) D2" and
    "D1 = add_mset (Pos A) D'" and
    "D2 = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'"
    using relpowp_ground_resolutionD[OF Suc_not_Zero steps]
    by (metis diff_Suc_Suc Suc_le_mono)

  have "Neg A \<notin># D'"
    by (metis \<open>D1 = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D1\<close>
        ord_res.less_lit_simps(4) linorder_lit.is_greatest_in_mset_iff linorder_trm.eq_refl
        linorder_trm.leD remove1_mset_add_mset_If)

  obtain m' C'' where
    "C = replicate_mset (Suc m') (Neg A) + C''" and
    "Neg A \<notin># C''" and
    "eres D1 C = repeat_mset (Suc m') D' + C''"
    using \<open>C \<noteq> eres D1 C\<close> eres_not_identD
    using \<open>ord_res.is_strictly_maximal_lit (Pos A) D1\<close> linorder_lit.Uniq_is_greatest_in_mset
    using \<open>D1 = add_mset (Pos A) D'\<close>
    by (metis Uniq_D add_mset_remove_trivial literal.inject(1))

  have "m - n = Suc m'"
  proof -
    have "count C (Neg A) = count (repeat_mset (Suc n) D') (Neg A) +
              count (replicate_mset (m - n) (Neg A)) (Neg A) + count C' (Neg A)"
      using \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close> by simp
    also have "\<dots> = count D' (Neg A) * Suc n + count {#Neg A#} (Neg A) * (m - n) +
              count C' (Neg A)"
      by simp
    also have "\<dots> = 0 * Suc n + 1 * (m - n) + 0"
      using \<open>Neg A \<notin># D'\<close> \<open>Neg A \<notin># C'\<close> by (simp add: count_eq_zero_iff)
    also have "\<dots> = m - n"
      by presburger
    finally have "count C (Neg A) = m - n" .

    have "count C (Neg A) = count (replicate_mset (Suc m') (Neg A)) (Neg A) +
              count C'' (Neg A)"
      using \<open>C = replicate_mset (Suc m') (Neg A) + C''\<close> by simp
    also have "\<dots> = count {#Neg A#} (Neg A) * Suc m' + count C'' (Neg A)"
      by simp
    also have "\<dots> = 1 * Suc m' + 0"
      using \<open>Neg A \<notin># C''\<close> by (simp add: count_eq_zero_iff)
    also have "\<dots> = Suc m'"
      by presburger
    finally have "count C (Neg A) = Suc m'" .

    show ?thesis
      using \<open>count C (Neg A) = m - n\<close> \<open>count C (Neg A) = Suc m'\<close> by argo
  qed

  hence "C'' = repeat_mset (Suc n) D' + C'"
    using \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
      \<open>C = replicate_mset (Suc m') (Neg A) + C''\<close>
    by simp

  hence eres_D1_C_eq: "eres D1 C = repeat_mset (Suc m' + Suc n) D' + C'"
    using \<open>eres D1 C = repeat_mset (Suc m') D' + C''\<close> by simp

  have "ord_res_Interp N (eres D1 C) \<TTurnstile> eres D1 C"
    using eres_C_true .

  moreover have "eres D1 C \<prec>\<^sub>c C"
    using eres_le[of D1 C] \<open>C \<noteq> eres D1 C\<close> by order

  ultimately have "ord_res_Interp N C \<TTurnstile> eres D1 C"
    using ord_res.entailed_clause_stays_entailed by metis

  thus "ord_res_Interp N C \<TTurnstile> C"
    unfolding true_cls_def
  proof (elim bexE)
    fix L
    assume
      L_in: "L \<in># eres D1 C" and
      L_true: "ord_res_Interp N C \<TTurnstile>l L"

    from L_in have "L \<in># D' \<or> L \<in># C'"
      unfolding eres_D1_C_eq
      using member_mset_repeat_msetD by fastforce
    hence "L \<in># C"
      by (auto simp: \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>)
    with L_true show "\<exists>L \<in># C. ord_res_Interp N C \<TTurnstile>l L"
      by metis
  qed
qed

lemma
  assumes "\<exists>\<^sub>\<le>\<^sub>1x. P x"
  shows "finite {x. P x}"
  using assms Collect_eq_if_Uniq by fastforce

lemma finite_if_Uniq_Uniq:
  assumes
    "\<exists>\<^sub>\<le>\<^sub>1x. P x"
    "\<forall>x. \<exists>\<^sub>\<le>\<^sub>1y. Q x y"
  shows "finite {y. \<exists>x. P x \<and> Q x y}"
  using assms
  by (smt (verit, best) Collect_eq_if_Uniq UniqI Uniq_D finite.emptyI finite_insert)

lemma finite_if_finite_finite:
  assumes
    "finite {x. P x}"
    "\<forall>x. finite {y. Q x y}"
  shows "finite {y. \<exists>x. P x \<and> Q x y}"
  using assms by auto

definition resolvent_at where
  "resolvent_at C D i = (THE CD. (ground_resolution C ^^ i) D CD)"

lemma resolvent_at_0[simp]: "resolvent_at C D 0 = D"
  by (simp add: resolvent_at_def)

lemma resolvent_at_less_cls_resolvent_at:
  assumes reso_at: "(ground_resolution C ^^ n) D CD"
  assumes "i < j" and "j \<le> n"
  shows "resolvent_at C D j \<prec>\<^sub>c resolvent_at C D i"
proof -
  obtain j' where
    "j = i + Suc j'"
    using \<open>i < j\<close> by (metis less_iff_Suc_add nat_arith.suc1)

  obtain n' where
    "n = j + n'"
    using \<open>j \<le> n\<close> by (metis le_add_diff_inverse)

  obtain CD\<^sub>i CD\<^sub>j CD\<^sub>n where
    "(ground_resolution C ^^ i) D CD\<^sub>i" and
    "(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j"
    "(ground_resolution C ^^ n') CD\<^sub>j CD\<^sub>n"
    using reso_at \<open>n = j + n'\<close> \<open>j = i + Suc j'\<close> by (metis relpowp_plusD)

  have *: "resolvent_at C D i = CD\<^sub>i"
    unfolding resolvent_at_def
    using \<open>(ground_resolution C ^^ i) D CD\<^sub>i\<close>
    by (simp add: Uniq_ground_resolution Uniq_relpowp the1_equality')

  have "(ground_resolution C ^^ j) D CD\<^sub>j"
    unfolding \<open>j = i + Suc j'\<close>
    using \<open>(ground_resolution C ^^ i) D CD\<^sub>i\<close> \<open>(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j\<close>
    by (metis relpowp_trans)
  hence **: "resolvent_at C D j = CD\<^sub>j"
    unfolding resolvent_at_def
    by (simp add: Uniq_ground_resolution Uniq_relpowp the1_equality')

  have "(ground_resolution C)\<^sup>+\<^sup>+ CD\<^sub>i CD\<^sub>j"
    using \<open>(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j\<close>
    by (metis Zero_not_Suc tranclp_if_relpowp)
  hence "CD\<^sub>j \<prec>\<^sub>c CD\<^sub>i"
    using resolvent_lt_right_premise_if_tranclp_ground_resolution by metis
  thus ?thesis
    unfolding * ** .
qed

lemma
  assumes reso_at: "(ground_resolution C ^^ n) D CD" and "i < n"
  shows
    left_premisse_lt_resolvent_at: "C \<prec>\<^sub>c resolvent_at C D i" and
    max_lit_resolvent_at:
      "ord_res.is_maximal_lit L D \<Longrightarrow> ord_res.is_maximal_lit L (resolvent_at C D i)" and
    nex_pos_strictly_max_lit_in_resolvent_at:
      "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at C D i)" and
    ground_resolution_resolvent_at_resolvent_at_Suc:
      "ground_resolution C (resolvent_at C D i) (resolvent_at C D (Suc i))" and
    relpowp_to_resolvent_at: "(ground_resolution C ^^ i) D (resolvent_at C D i)"
proof -
  obtain j where n_def: "n = i + Suc j"
    using \<open>i < n\<close> less_natE by auto

  obtain CD' where "(ground_resolution C ^^ i) D CD'" and "(ground_resolution C ^^ Suc j) CD' CD"
    using reso_at n_def by (metis relpowp_plusD)

  have "resolvent_at C D i = CD'"
    unfolding resolvent_at_def
    using \<open>(ground_resolution C ^^ i) D CD'\<close>
    by (simp add: Uniq_ground_resolution Uniq_relpowp the1_equality')

  have "C \<prec>\<^sub>c CD'"
  proof (rule left_premise_lt_right_premise_if_tranclp_ground_resolution)
    show "(ground_resolution C)\<^sup>+\<^sup>+ CD' CD"
      using \<open>(ground_resolution C ^^ Suc j) CD' CD\<close>
      by (metis Zero_not_Suc tranclp_if_relpowp)
  qed
  thus "C \<prec>\<^sub>c resolvent_at C D i"
    unfolding \<open>resolvent_at C D i = CD'\<close> by argo

  show "ord_res.is_maximal_lit L (resolvent_at C D i)" if "ord_res.is_maximal_lit L D"
    unfolding \<open>resolvent_at C D i = CD'\<close>
    using that
    using \<open>(ground_resolution C ^^ i) D CD'\<close>
    by (smt (verit, ccfv_SIG) Uniq_ground_resolution Uniq_relpowp Zero_not_Suc
        \<open>\<And>thesis. (\<And>CD'. \<lbrakk>(ground_resolution C ^^ i) D CD'; (ground_resolution C ^^ Suc j) CD' CD\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        linorder_lit.Uniq_is_greatest_in_mset linorder_lit.Uniq_is_maximal_in_mset literal.sel(1)
        n_def relpowp_ground_resolutionD reso_at the1_equality' zero_eq_add_iff_both_eq_0)

  show "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at C D i)"
    unfolding \<open>resolvent_at C D i = CD'\<close>
    by (metis Zero_not_Suc \<open>(ground_resolution C ^^ Suc j) CD' CD\<close>
        nex_strictly_maximal_pos_lit_if_resolvable tranclpD tranclp_if_relpowp)

  show "ground_resolution C (resolvent_at C D i) (resolvent_at C D (Suc i))"
  proof -
    obtain CD'' where "ground_resolution C CD' CD''" and "(ground_resolution C ^^ j) CD'' CD"
      using \<open>(ground_resolution C ^^ Suc j) CD' CD\<close> by (metis relpowp_Suc_D2)
    hence "(ground_resolution C ^^ Suc i) D CD''"
      using \<open>(ground_resolution C ^^ i) D CD'\<close> by auto
    hence "resolvent_at C D (Suc i) = CD''"
      unfolding resolvent_at_def
      by (meson Uniq_ground_resolution Uniq_relpowp the1_equality')

    show ?thesis
      unfolding \<open>resolvent_at C D i = CD'\<close> \<open>resolvent_at C D (Suc i) = CD''\<close>
      using \<open>ground_resolution C CD' CD''\<close> .
  qed

  show "(ground_resolution C ^^ i) D (resolvent_at C D i)"
    using \<open>(ground_resolution C ^^ i) D CD'\<close> \<open>resolvent_at C D i = CD'\<close> by argo
qed

definition resolvents_upto where
  "resolvents_upto C D n = resolvent_at C D |`| fset_upto (Suc 0) n"

lemma resolvents_upto_0[simp]:
  "resolvents_upto C D 0 = {||}"
  by (simp add: resolvents_upto_def)

lemma resolvents_upto_Suc[simp]:
  "resolvents_upto C D (Suc n) = finsert (resolvent_at C D (Suc n)) (resolvents_upto C D n)"
  by (simp add: resolvents_upto_def)

lemma resolvent_at_fmember_resolvents_upto:
  assumes "k \<noteq> 0"
  shows "resolvent_at C D k |\<in>| resolvents_upto C D k"
  unfolding resolvents_upto_def
proof (rule fimageI)
  show "k |\<in>| fset_upto (Suc 0) k"
    using assms by simp
qed

lemma backward_simulation_2_to_3:
  fixes match measure less
  defines "match \<equiv> ord_res_2_matches_ord_res_3"
  assumes
    match: "match S2 S3" and
    step2: "ord_res_3_step S3 S3'"
  shows "(\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match S2' S3')"
  using match[unfolded match_def]
proof (cases S2 S3 rule: ord_res_2_matches_ord_res_3.cases)
  case match_hyps: (1 U\<^sub>p\<^sub>r N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note invars = match_hyps(3-)

  have U\<^sub>p\<^sub>r_spec: "\<forall>C|\<in>|U\<^sub>p\<^sub>r. \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
    using invars by argo

  hence C_not_least_with_partial: "\<not> is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    if C_in: "C |\<in>| U\<^sub>p\<^sub>r" for C
  proof -
    obtain D1 D2 where
      "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
      "C \<noteq> eres D1 D2" and
      "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
      using U\<^sub>p\<^sub>r_spec C_in by metis

    have "eres D1 C = eres D1 D2"
      using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_eq_after_tranclp_ground_resolution by metis
    hence "eres D1 C \<prec>\<^sub>c C"
      using eres_le[of D1 C] \<open>C \<noteq> eres D1 D2\<close> by order

    show ?thesis
    proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (eres D1 D2) \<TTurnstile> eres D1 D2")
      case True
      then show ?thesis
        by (metis (no_types, lifting) \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> \<open>eres D1 C = eres D1 D2\<close>
            clause_true_if_eres_true is_least_false_clause_def
            linorder_cls.is_least_in_fset_ffilterD(2))
    next
      case False
      then show ?thesis
        by (metis (mono_tags, lifting) Un_iff \<open>eres D1 C = eres D1 D2\<close> \<open>eres D1 C \<prec>\<^sub>c C\<close>
            \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
            linorder_cls.not_less_iff_gr_or_eq sup_fset.rep_eq)
    qed
  qed

  have least_false_conv: "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) =
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    using invars is_least_false_clause_conv_if_partial_resolution_invariant by metis

  have U\<^sub>p\<^sub>r_unproductive: "\<And>N. \<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production N C = {}"
  proof (intro ballI)
    fix C
    assume "C |\<in>| U\<^sub>p\<^sub>r"
    hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. (\<exists>C'. ground_resolution D C C')"
      using U\<^sub>p\<^sub>r_spec by (metis eres_eq_after_tranclp_ground_resolution resolvable_if_neq_eres)
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
      using nex_strictly_maximal_pos_lit_if_resolvable by metis
    thus "\<And>N. ord_res.production N C = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f:
    "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C = ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: funion_left_commute sup_commute)

  have U\<^sub>p\<^sub>r_have_generalization: "\<forall>Ca |\<in>| U\<^sub>p\<^sub>r. \<exists>D |\<in>| U\<^sub>e\<^sub>r. D \<prec>\<^sub>c Ca \<and> {D} \<TTurnstile>e {Ca}"
  proof (intro ballI)
    fix Ca
    assume "Ca |\<in>| U\<^sub>p\<^sub>r"
    then obtain D1 D2 where
      "D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca" and
      "Ca \<noteq> eres D1 D2" and
      "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
      using U\<^sub>p\<^sub>r_spec by metis

    have "eres D1 D2 = eres D1 Ca"
      using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca\<close> eres_eq_after_tranclp_ground_resolution by metis

    show "\<exists>D |\<in>| U\<^sub>e\<^sub>r. D \<prec>\<^sub>c Ca \<and> {D} \<TTurnstile>e {Ca}"
    proof (intro bexI conjI)
      have "eres D1 Ca \<preceq>\<^sub>c Ca"
        using eres_le .
      thus "eres D1 D2 \<prec>\<^sub>c Ca"
        using \<open>Ca \<noteq> eres D1 D2\<close> \<open>eres D1 D2 = eres D1 Ca\<close> by order
    next
      show "{eres D1 D2} \<TTurnstile>e {Ca}"
        using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca\<close> eres_entails_resolvent by metis
    next
      show "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> by simp
    qed
  qed

  from step2 obtain s3' where S3'_def: "S3' = (N, s3')" and "ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'"
    by (auto simp: match_hyps(1,2) elim: ord_res_3_step.cases)

  show ?thesis
    using \<open>ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'\<close>
  proof (cases N "(U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" s3' rule: ord_res_3.cases)
    case (factoring C L U\<^sub>e\<^sub>f')

    define S2' where
      "S2' = (N, (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, finsert (efac C) U\<^sub>e\<^sub>f))"

    have "ord_res_2_step\<^sup>+\<^sup>+ S2 S2'"
      unfolding match_hyps(1,2) S2'_def
    proof (intro tranclp.r_into_trancl ord_res_2_step.intros ord_res_2.factoring)
      show "is_least_false_clause (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r) |\<union>| U\<^sub>e\<^sub>f) C"
        using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
        using least_false_conv
        by (metis sup_assoc)
    next
      show "ord_res.is_maximal_lit L C"
        using factoring by metis
    next
      show "is_pos L"
        using factoring by metis
    next
      show "finsert (efac C) U\<^sub>e\<^sub>f = finsert (efac C) U\<^sub>e\<^sub>f"
        by argo
    qed

    moreover have "match S2' S3'"
      unfolding S2'_def S3'_def
      unfolding factoring
      unfolding match_def
    proof (rule ord_res_2_matches_ord_res_3.intros)
      show "\<forall>Ca|\<in>|U\<^sub>p\<^sub>r.
        \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (efac C) U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (efac C) U\<^sub>e\<^sub>f.
        (ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca \<and> Ca \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using U\<^sub>p\<^sub>r_spec by auto
    qed

    ultimately show ?thesis
      by metis
  next
    case (resolution C L D U\<^sub>r\<^sub>r')

    have "(ground_resolution D)\<^sup>*\<^sup>* C (eres D C)" "\<nexists>x. ground_resolution D (eres D C) x"
      unfolding atomize_conj
      by (metis ex1_eres_eq_full_run_ground_resolution full_run_def)

    moreover have "\<exists>x. ground_resolution D C x"
      unfolding ground_resolution_def
      using resolution
      by (metis Neg_atm_of_iff ex_ground_resolutionI ord_res.mem_productionE singletonI)

    ultimately have "(ground_resolution D)\<^sup>+\<^sup>+ C (eres D C)"
      by (metis rtranclpD)

    then obtain n where "(ground_resolution D ^^ Suc n) C (eres D C)"
      by (metis not0_implies_Suc not_gr_zero tranclp_power)

    hence "resolvent_at D C (Suc n) = eres D C"
      by (metis Uniq_ground_resolution Uniq_relpowp resolvent_at_def the1_equality')

    have steps: "k \<le> Suc n \<Longrightarrow> (ord_res_2_step ^^ k)
      (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)" for k
    proof (induction k)
      case 0
      show ?case
        by simp
    next
      case (Suc k)
      have "k < Suc n"
        using \<open>Suc k \<le> Suc n\<close> by presburger
      hence "k \<le> Suc n"
        by presburger
      hence "(ord_res_2_step ^^ k) (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)"
        using Suc.IH by metis

      moreover have "ord_res_2_step
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k), U\<^sub>e\<^sub>f)"
        unfolding resolvents_upto_Suc
      proof (intro ord_res_2_step.intros ord_res_2.resolution)
        show "is_least_false_clause (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)
          (resolvent_at D C k)"
          using \<open>k < Suc n\<close>
        proof (induction k)
          case 0
          have "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
            using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
            unfolding least_false_conv .
          thus ?case
            unfolding funion_fempty_right funion_assoc[symmetric]
            by simp
        next
          case (Suc k')

          have "\<And>x. ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) x =
              ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) x"
            by (simp add: funion_left_commute sup_assoc sup_commute)
          also have "\<And>x. ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) x =
            ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x"
          proof (intro Interp_union_unproductive ballI)
            fix x y assume "y |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k')"
            hence "y |\<in>| U\<^sub>p\<^sub>r \<or> y |\<in>| resolvents_upto D C (Suc k')"
              by blast
            thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) y = {}"
            proof (elim disjE)
              assume "y |\<in>| U\<^sub>p\<^sub>r"
              thus ?thesis
                using U\<^sub>p\<^sub>r_unproductive by metis
            next
              assume "y |\<in>| resolvents_upto D C (Suc k')"
              then obtain i where "i |\<in>| fset_upto (Suc 0) (Suc k')" and "y = resolvent_at D C i"
                unfolding resolvents_upto_def by blast

              have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at D C i)"
              proof (rule nex_pos_strictly_max_lit_in_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C (eres D C)"
                  using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
              next
                have "i \<le> Suc k'"
                  using \<open>i |\<in>| fset_upto (Suc 0) (Suc k')\<close> by auto
                thus "i < Suc n"
                  using \<open>Suc k' < Suc n\<close> by presburger
              qed

              then show ?thesis
                using \<open>y = resolvent_at D C i\<close> unproductive_if_nex_strictly_maximal_pos_lit
                by metis
            qed
          qed simp_all
          finally have Interp_simp: "\<And>x.
            ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) x =
            ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x" .

          show ?case
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            have "resolvent_at D C (Suc k') |\<in>| resolvents_upto D C (Suc k')"
              using resolvent_at_fmember_resolvents_upto by simp
            thus "resolvent_at D C (Suc k') |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f"
              by simp
          next

            show "\<not> ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f))
              (resolvent_at D C (Suc k')) \<TTurnstile> resolvent_at D C (Suc k')"
              unfolding Interp_simp
              by (metis (no_types, lifting) Suc.prems Zero_not_Suc
                  \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> clause_true_if_resolved_true
                  insert_not_empty is_least_false_clause_def
                  linorder_cls.is_least_in_fset_ffilterD(2) local.resolution(2) local.resolution(7)
                  relpowp_to_resolvent_at tranclp_if_relpowp)
          next
            fix y
            assume "y \<noteq> resolvent_at D C (Suc k')"
            assume "\<not> ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
            hence "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
              unfolding Interp_simp .
            hence "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
              using Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f by metis

            assume "y |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f"
            hence "y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> y |\<in>| resolvents_upto D C (Suc k')"
              by auto
            thus "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
            proof (elim disjE)
              assume "y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              have "C \<preceq>\<^sub>c y"
              proof (cases "y = C")
                case True
                thus ?thesis
                  by order
              next
                case False
                thus ?thesis
                  using \<open>y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
                  using \<open>\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y\<close>
                  using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
                  unfolding least_false_conv[symmetric]
                  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
                  by simp
              qed

              moreover have "resolvent_at D C (Suc k') \<prec>\<^sub>c C"
                by (metis Suc.prems \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> less_or_eq_imp_le
                    resolvent_at_less_cls_resolvent_at resolvent_at_0 zero_less_Suc)

              ultimately show "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
                by order
            next
              assume "y |\<in>| resolvents_upto D C (Suc k')"
              then obtain i where
                i_in: "i |\<in>| fset_upto (Suc 0) (Suc k')" and y_def: "y = resolvent_at D C i"
                unfolding resolvents_upto_def by blast

              hence "i < Suc k'"
                using \<open>y \<noteq> resolvent_at D C (Suc k')\<close>
                by auto

              show "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
                unfolding y_def
              proof (rule resolvent_at_less_cls_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C (eres D C)"
                  using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
              next
                show "i < Suc k'"
                  using \<open>y \<noteq> resolvent_at D C (Suc k')\<close> i_in y_def by auto
              next
                show "Suc k' \<le> Suc n"
                  using \<open>Suc k' < Suc n\<close> by presburger
              qed
            qed
          qed
        qed
      next
        show "ord_res.is_maximal_lit L (resolvent_at D C k)"
        proof (rule max_lit_resolvent_at)
          show "(ground_resolution D ^^ Suc n) C (eres D C)"
            using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        next
          show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
        qed
      next
        show "is_neg L"
          using \<open>is_neg L\<close> .
      next
        show "D |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f"
          using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by auto
      next
        show "D \<prec>\<^sub>c resolvent_at D C k"
        proof (rule left_premisse_lt_resolvent_at)
          show "(ground_resolution D ^^ Suc n) C (eres D C)"
            using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        qed
      next
        have "ord_res.production (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)) D =
          ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k)) D"
          by (simp add: funion_left_commute sup_assoc sup_commute)
        also have "\<dots> = ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D"
        proof (intro production_union_unproductive ballI)
          fix x
          assume "x |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k"
          hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L x"
            unfolding funion_iff
          proof (elim disjE)
            assume "x |\<in>| U\<^sub>p\<^sub>r"
            thus ?thesis
              using U\<^sub>p\<^sub>r_spec
              by (metis eres_eq_after_tranclp_ground_resolution nex_strictly_maximal_pos_lit_if_neq_eres)
          next
            assume "x |\<in>| resolvents_upto D C k"
            then obtain i where "i |\<in>| fset_upto (Suc 0) k" and x_def: "x = resolvent_at D C i"
              unfolding resolvents_upto_def by auto

            have "0 < i" and "i \<le> k"
              using \<open>i |\<in>| fset_upto (Suc 0) k\<close> by simp_all

            show ?thesis
              unfolding x_def
            proof (rule nex_pos_strictly_max_lit_in_resolvent_at)
              show "(ground_resolution D ^^ Suc n) C (eres D C)"
                using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
            next
              show "i < Suc n"
                using \<open>i \<le> k\<close> \<open>k < Suc n\<close> by presburger
            qed
          qed
          thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union>
            fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k)) x = {}"
            using unproductive_if_nex_strictly_maximal_pos_lit by metis
        next
          show "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
        qed simp_all
        finally show "ord_res.production (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)) D =
          {atm_of L}"
          using \<open>ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}\<close> by argo
      next
        show "ord_res.ground_resolution (resolvent_at D C k) D (resolvent_at D C (Suc k))"
          unfolding ground_resolution_def[symmetric]
        proof (rule ground_resolution_resolvent_at_resolvent_at_Suc)
          show "(ground_resolution D ^^ Suc n) C (eres D C)"
            using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        qed
      next
        show "U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (resolvent_at D C (Suc k)) (resolvents_upto D C k) =
          finsert (resolvent_at D C (Suc k)) (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k)"
          by simp
      qed

      ultimately show ?case
        by (meson relpowp_Suc_I)
    qed

    hence "(ord_res_2_step ^^ Suc n) S2 (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n), U\<^sub>e\<^sub>f)"
      unfolding match_hyps(1,2) by blast

    moreover have "match (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n), U\<^sub>e\<^sub>f) S3'"
    proof -
      have 1: "S3' = (N, finsert (eres D C) U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)"
        unfolding S3'_def \<open>s3' = (U\<^sub>r\<^sub>r', U\<^sub>e\<^sub>f)\<close> \<open>U\<^sub>r\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r\<close> ..

      have 2: "U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n) =
        U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r"
        by (auto simp: \<open>resolvent_at D C (Suc n) = eres D C\<close>)

      show ?thesis
        unfolding match_def 1 2
      proof (rule ord_res_2_matches_ord_res_3.intros)
        show "\<forall>E|\<in>|U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n.
          \<exists>D1|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          (ground_resolution D1)\<^sup>+\<^sup>+ D2 E \<and> E \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
        proof (intro ballI)
          fix Ca
          assume "Ca |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n"
          hence "Ca |\<in>| U\<^sub>p\<^sub>r \<or> Ca |\<in>| resolvents_upto D C n"
            by simp
          thus "\<exists>D1|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
            (ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca \<and> Ca \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
          proof (elim disjE)
            show "Ca |\<in>| U\<^sub>p\<^sub>r \<Longrightarrow> ?thesis"
              using U\<^sub>p\<^sub>r_spec by auto
          next
            assume "Ca |\<in>| resolvents_upto D C n"
            then obtain i where i_in: "i |\<in>| fset_upto (Suc 0) n" and Ca_def:"Ca = resolvent_at D C i"
              unfolding resolvents_upto_def by auto

            from i_in have "0 < i" "i \<le> n"
              by simp_all

            show "?thesis"
            proof (intro bexI conjI)
              have "(ground_resolution D ^^ i) C Ca"
                unfolding \<open>Ca = resolvent_at D C i\<close>
              proof (rule relpowp_to_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C (eres D C)"
                  using \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close> .
              next
                show "i < Suc n"
                  using \<open>i \<le> n\<close> by presburger
              qed
              thus "(ground_resolution D)\<^sup>+\<^sup>+ C Ca"
                using \<open>0 < i\<close> by (simp add: tranclp_if_relpowp)
            next
              show "Ca \<noteq> eres D C"
                by (metis Ca_def \<open>(ground_resolution D ^^ Suc n) C (eres D C)\<close>
                  \<open>\<nexists>x. ground_resolution D (eres D C) x\<close> \<open>i \<le> n\<close>
                  ground_resolution_resolvent_at_resolvent_at_Suc less_Suc_eq_le)
            next
              show "eres D C |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
                by simp
            next
              show "D |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using resolution by simp
            next
              have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using resolution
                by (simp add: is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff)
              thus "C |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                by simp
            qed
          qed
        qed
      qed
    qed

    ultimately have "\<exists>S2'. (ord_res_2_step ^^ Suc n) S2 S2' \<and> match S2' S3'"
      by metis

    thus "\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match S2' S3'"
      by (metis Zero_neq_Suc tranclp_if_relpowp)
  qed
qed

lemma right_unique_ord_res_3: "right_unique (ord_res_3 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_3 N s s'" and step2: "ord_res_3 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_3.cases)
    case hyps1: (factoring U\<^sub>r\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 U\<^sub>e\<^sub>f1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_3.cases)
      case (factoring U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f2')
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 D2 U\<^sub>r\<^sub>r2')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution U\<^sub>r\<^sub>r1 U\<^sub>e\<^sub>f1 C1 L1 D1 U\<^sub>r\<^sub>r1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_3.cases)
      case (factoring U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 U\<^sub>e\<^sub>f2')
      with hyps1 have False
        by (metis Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset prod.inject the1_equality')
      thus ?thesis ..
    next
      case hyps2: (resolution U\<^sub>r\<^sub>r2 U\<^sub>e\<^sub>f2 C2 L2 D2 U\<^sub>r\<^sub>r2')

      have *: "U\<^sub>r\<^sub>r1 = U\<^sub>r\<^sub>r2" "U\<^sub>e\<^sub>f1 = U\<^sub>e\<^sub>f2"
        using hyps1 hyps2 by  simp_all

      have **: "C1 = C2"
        using hyps1 hyps2
        unfolding *
        by (metis Uniq_is_least_false_clause the1_equality')

      have ***: "L1 = L2"
        using hyps1 hyps2
        unfolding * **
        by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

      have ****: "D1 = D2"
        using hyps1 hyps2
        unfolding * ** ***
        by (metis linorder_cls.less_irrefl linorder_cls.linorder_cases
            ord_res.less_trm_iff_less_cls_if_mem_production singletonI)

      show ?thesis
        using hyps1 hyps2
        unfolding * ** *** ****
        by argo
    qed
  qed
qed

lemma right_unique_ord_res_3_step: "right_unique ord_res_3_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_3_step x y \<Longrightarrow> ord_res_3_step x z \<Longrightarrow> y = z"
    apply (cases x; cases y; cases z)
    apply (simp add: ord_res_3_step.simps)
    using right_unique_ord_res_3[THEN right_uniqueD]
    by blast
qed

lemma ex_ord_res_3_if_not_final:
  assumes "\<not> ord_res_3_final S"
  shows "\<exists>S'. ord_res_3_step S S'"
proof -
  from assms obtain N U\<^sub>r U\<^sub>e\<^sub>f where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))" and
    "{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
    "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (metis ord_res_3_final.intros ord_res_final_def surj_pair)

  obtain C where C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    using \<open>ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))\<close> obtains_least_false_clause_if_ex_false_clause
    by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using ord_res_3.factoring[OF C_least_false C_max] S_def is_pos_def
      by (metis ord_res_3_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain DC where
      "full_run (ground_resolution D) C DC"
      using ex_ground_resolutionI C_max Neg
      using ex1_eres_eq_full_run_ground_resolution by blast

    ultimately show ?thesis
      using ord_res_3.resolution[OF C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_3_step.intros)
  qed
qed

corollary ord_res_3_step_safe: "ord_res_3_final S \<or> (\<exists>S'. ord_res_3_step S S')"
  using ex_ord_res_3_if_not_final by metis

lemma safe_states_if_ord_res_2_matches_ord_res_3:
  assumes match: "ord_res_2_matches_ord_res_3 S\<^sub>2 S\<^sub>3"
  shows
    "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    "safe_state ord_res_3_step ord_res_3_final S\<^sub>3"
proof -
  show "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    using safe_state_if_all_states_safe ord_res_2_step_safe by metis

  show "safe_state ord_res_3_step ord_res_3_final S\<^sub>3"
    using safe_state_if_all_states_safe ord_res_3_step_safe by metis
qed

theorem bisimulation_ord_res_2_ord_res_3:
  defines "match \<equiv> \<lambda>_ S2 S3. ord_res_2_matches_ord_res_3 S2 S3"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow> bool) ORDER.
    bisimulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final ORDER MATCH"
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_2_step"
    using right_unique_ord_res_2_step .
next
  show "right_unique ord_res_3_step"
    using right_unique_ord_res_3_step .
next
  show "\<forall>s1. ord_res_2_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_2_step s1 s1')"
    by (metis finished_def ord_res_2_semantics.final_finished)
next
  show "\<forall>s2. ord_res_3_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_3_step s2 s2')"
    by (metis finished_def ord_res_3_semantics.final_finished)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_2_final s1 = ord_res_3_final s2"
    unfolding match_def
    using ord_res_2_final_iff_ord_res_3_final by metis
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_2_step ord_res_2_final s1 \<and> safe_state ord_res_3_step ord_res_3_final s2"
    unfolding match_def
    using safe_states_if_ord_res_2_matches_ord_res_3 by metis
next
  show "wfP (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i s1 s2 s2'.
       match i s1 s2 \<longrightarrow>
       ord_res_3_step s2 s2' \<longrightarrow>
       (\<exists>i' s1'. ord_res_2_step\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> False)"
    unfolding match_def
    using backward_simulation_2_to_3 by metis
qed

corollary backward_simulation_ord_res_1_ord_res_3:
  shows "\<exists>MATCH (ORDER :: (nat \<times> nat) \<times> (nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<times> (nat \<times> nat) \<Rightarrow> bool).
    backward_simulation ord_res_1 ord_res_3_step ord_res_1_final ord_res_3_final ORDER MATCH"
proof -
  obtain
    MATCH12 :: "nat \<times> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" and
    ORDER12 :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
    "bisimulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final ORDER12 MATCH12"
    using bisimulation_ord_res_1_ord_res_2 by metis
  hence bsim12: "backward_simulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final ORDER12 MATCH12"
    by (simp add: bisimulation_def)

  obtain
    MATCH23 :: "nat \<times> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" and
    ORDER23 :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
    "bisimulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final ORDER23 MATCH23"
    using bisimulation_ord_res_2_ord_res_3 by metis
  hence bsim23: "backward_simulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final ORDER23 MATCH23"
    by (simp add: bisimulation_def)

  show ?thesis
    using backward_simulation_composition[OF bsim12 bsim23] by metis
qed


section \<open>ORD-RES-4 (implicit factorization)\<close>

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

interpretation ord_res_4_semantics: semantics where
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

(* interpretation ord_res_4_language: language where
  step = ord_res_4_step and
  final = ord_res_4_final and
  load = ord_res_4_load
  by unfold_locales *)

(* {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} sollte eingentlich gleich \<F> sein... *)

inductive ord_res_3_matches_ord_res_4 where
  "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r \<Longrightarrow> U\<^sub>e\<^sub>f = iefac \<F> |`| {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} \<Longrightarrow>
  ord_res_3_matches_ord_res_4 (N, (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)) (N, U\<^sub>e\<^sub>r, \<F>)"

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

(*
efac C \<noteq> C \<Longrightarrow> efac C \<prec>\<^sub>c C \<and> {efac C} entails {C}
*)
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

lemma ord_res_3_final_iff_ord_res_4_final:
  assumes match: "ord_res_3_matches_ord_res_4 S3 S4"
  shows "ord_res_3_final S3 \<longleftrightarrow> ord_res_4_final S4"
  using match
proof (cases S3 S4 rule: ord_res_3_matches_ord_res_4.cases)
  case match_hyps: (1 \<F> N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note invars = match_hyps(3-)

  have "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<longleftrightarrow> {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using invars by (auto simp: iefac_def)

  moreover have "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
    unfolding ex_false_clause_iff
    unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF invars(2)]
    unfolding is_least_false_clause_with_iefac_conv ..

  ultimately have "ord_res_final (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<longleftrightarrow> ord_res_final (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
    unfolding ord_res_final_def by argo

  thus ?thesis
    unfolding match_hyps(1,2)
    by (simp add: ord_res_3_final.simps ord_res_4_final.simps)
qed

lemma forward_simulation_between_3_and_4:
  assumes
    match: "ord_res_3_matches_ord_res_4 S3 S4" and
    step: "ord_res_3_step S3 S3'"
  shows "(\<exists>S4'. ord_res_4_step\<^sup>+\<^sup>+ S4 S4' \<and> ord_res_3_matches_ord_res_4 S3' S4')"
  using match
proof (cases S3 S4 rule: ord_res_3_matches_ord_res_4.cases)
  case match_hyps: (1 \<F> N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note match_invars = match_hyps(3-)

  from step obtain s3' where step': "ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'" and "S3' = (N, s3')"
    unfolding match_hyps(1,2)
    by (auto elim: ord_res_3_step.cases)

  from step' show ?thesis
  proof (cases N "(U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" s3' rule: ord_res_3.cases)
    case (factoring C L U\<^sub>e\<^sub>f')

    have "\<not> ord_res.is_strictly_maximal_lit L C"
      using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close> \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
      by (metis (no_types, lifting) is_least_false_clause_def is_pos_def
        pos_lit_not_greatest_if_maximal_in_least_false_clause)

    have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    proof -
      have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
        by (simp add: is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff)
      moreover have "C |\<notin>| U\<^sub>e\<^sub>f"
      proof (rule notI)
        assume "C |\<in>| U\<^sub>e\<^sub>f"
        then obtain C\<^sub>0 where "C = iefac \<F> C\<^sub>0" and "C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac \<F> C\<^sub>0 \<noteq> C\<^sub>0"
          using match_invars(2) by force
        then show False
          by (metis Uniq_D \<open>\<not> ord_res.is_strictly_maximal_lit L C\<close> iefac_def
            linorder_lit.Uniq_is_maximal_in_mset
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset local.factoring(3)
            obtains_positive_greatest_lit_if_efac_not_ident)
      qed
      ultimately show ?thesis
        by simp
    qed

    show ?thesis
    proof (intro exI conjI)
      show "ord_res_4_step\<^sup>+\<^sup>+ S4 (N, U\<^sub>e\<^sub>r, finsert C \<F>)"
        unfolding match_hyps(1,2)
      proof (intro tranclp.r_into_trancl ord_res_4_step.intros ord_res_4.factoring)
        have "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
          using factoring by argo
        hence "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] .
        thus "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          unfolding is_least_false_clause_with_iefac_conv .
      next
        show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
      next
        show "is_pos L"
          using \<open>is_pos L\<close> .
      qed (rule refl)+
    next
      show "ord_res_3_matches_ord_res_4 S3' (N, U\<^sub>e\<^sub>r, finsert C \<F>)"
        unfolding \<open>S3' = (N, s3')\<close> \<open>s3' = (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f')\<close> \<open>U\<^sub>e\<^sub>f' = finsert (efac C) U\<^sub>e\<^sub>f\<close>
      proof (rule ord_res_3_matches_ord_res_4.intros)
        show "finsert C \<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
          using match_invars \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by simp
      next
        have "\<exists>C'. ord_res.ground_factoring C C'"
          using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
          by (metis \<open>\<not> ord_res.is_strictly_maximal_lit L C\<close> ex_ground_factoringI is_pos_def)
        hence "efac C \<noteq> C"
          by (metis ex1_efac_eq_factoring_chain)
        hence "iefac (finsert C \<F>) C \<noteq> C"
          by (simp add: iefac_def)

        have "{|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|} =
          finsert C {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> Ca \<noteq> Ca|}"
        proof (intro fsubset_antisym fsubsetI)
          fix x
          assume "x |\<in>| {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|}"
          hence "x |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac (finsert C \<F>) x \<noteq> x"
            by simp_all
          then show "x |\<in>| finsert C {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> Ca \<noteq> Ca|}"
            by (smt (verit, best) ffmember_filter finsert_iff iefac_def)
        next
          fix x
          assume "x |\<in>| finsert C {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> Ca \<noteq> Ca|}"
          hence "x = C \<or> x |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<and> iefac \<F> x \<noteq> x"
            by auto
          thus "x |\<in>| {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|}"
          proof (elim disjE conjE)
            assume "x = C"
            thus ?thesis
              using \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> \<open>iefac (finsert C \<F>) C \<noteq> C\<close> by auto
          next
            assume "x |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac \<F> x \<noteq> x"
            thus ?thesis
              by (smt (verit, best) ffmember_filter finsertCI iefac_def)
          qed
        qed
        thus "finsert (efac C) U\<^sub>e\<^sub>f =
          iefac (finsert C \<F>) |`| {|Ca |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac (finsert C \<F>) Ca \<noteq> Ca|}"
          using iefac_def match_invars(2) by auto
      qed
    qed
  next
    case (resolution C L D U\<^sub>r\<^sub>r')

    have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    proof -
      have "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
        using resolution by argo
      hence "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] .
      moreover have "D |\<notin>| N |\<union>| U\<^sub>e\<^sub>r - iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        by (metis clauses_for_iefac_are_unproductive insert_not_empty local.resolution(7))
      ultimately show ?thesis
        by blast
    qed

    show ?thesis
    proof (intro exI conjI)
      show "ord_res_4_step\<^sup>+\<^sup>+ S4 (N, finsert (eres D C) U\<^sub>e\<^sub>r, \<F>)"
        unfolding match_hyps(1,2)
        proof (intro tranclp.r_into_trancl ord_res_4_step.intros ord_res_4.resolution)
          have "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
            using resolution by argo
          hence "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
            unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] .
          thus "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
            unfolding is_least_false_clause_with_iefac_conv .
        next
          show "ord_res.is_maximal_lit L C"
            using resolution by argo
        next
          show "is_neg L"
            using resolution by argo
        next
          show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
        next
          show "D \<prec>\<^sub>c C"
            using resolution by argo
        next
          have "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D =
            ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
            unfolding funion_funion_eq_funion_funion_fimage_iefac_if[OF match_invars(2)] ..
          also have "\<dots> = ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<union> fset (N |\<union>| U\<^sub>e\<^sub>r)) D"
            by (simp add: sup.commute)
          also have "\<dots> = ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          proof (rule production_union_unproductive_strong)
            show "\<forall>x \<in> fset (N |\<union>| U\<^sub>e\<^sub>r) - fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)).
              ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<union> fset (N |\<union>| U\<^sub>e\<^sub>r)) x = {}"
              using clauses_for_iefac_are_unproductive[of "N |\<union>| U\<^sub>e\<^sub>r" \<F>] by simp
          next
            show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> .
          qed (rule finite_fset)+

          finally show "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {atm_of L}"
            using resolution by argo
        qed (rule refl)+
    next
      show "ord_res_3_matches_ord_res_4 S3' (N, finsert (eres D C) U\<^sub>e\<^sub>r, \<F>)"
        unfolding \<open>S3' = (N, s3')\<close> \<open>s3' = (U\<^sub>r\<^sub>r', U\<^sub>e\<^sub>f)\<close> \<open>U\<^sub>r\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r\<close>
      proof (rule ord_res_3_matches_ord_res_4.intros)
        show "\<F> |\<subseteq>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r"
          using match_invars by auto
      next
        show "U\<^sub>e\<^sub>f = iefac \<F> |`| {|C |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} "
        proof (cases "eres D C |\<in>| \<F>")
          case True
          then show ?thesis
            using \<open>\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r\<close>
            using match_invars by force
        next
          case False
          hence "iefac \<F> (eres D C) = eres D C"
            by (simp add: iefac_def)
          hence "{|C |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|} = {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|}"
            using ffilter_eq_ffilter_minus_singleton by auto
          thus ?thesis
            using match_invars by argo
        qed
      qed
    qed
  qed
qed

theorem bisimulation_ord_res_3_ord_res_4:
  defines "match \<equiv> \<lambda>_ S3 S4. ord_res_3_matches_ord_res_4 S3 S4"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow> bool) ORDER.
    bisimulation ord_res_3_step ord_res_4_step ord_res_3_final ord_res_4_final ORDER MATCH"
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_3_step"
    using right_unique_ord_res_3_step .
next
  show "right_unique ord_res_4_step"
    using right_unique_ord_res_4_step .
next
  show "\<forall>s1. ord_res_3_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_3_step s1 s1')"
    by (metis finished_def ord_res_3_semantics.final_finished)
next
  show "\<forall>s2. ord_res_4_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_4_step s2 s2')"
    by (metis finished_def ord_res_4_semantics.final_finished)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_3_final s1 \<longleftrightarrow> ord_res_4_final s2"
    unfolding match_def
    using ord_res_3_final_iff_ord_res_4_final by metis
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_3_step ord_res_3_final s1 \<and> safe_state ord_res_4_step ord_res_4_final s2"
    using ord_res_3_step_safe ord_res_4_step_safe
    by (simp add: safe_state_if_all_states_safe)
next
  show "wfP (\<lambda>i' i. False)"
    by simp
next
  show "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> ord_res_3_step s1 s1' \<longrightarrow>
    (\<exists>i' s2'. ord_res_4_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> False)"
    unfolding match_def
    using forward_simulation_between_3_and_4 by metis
qed


section \<open>ORD-RES-5 (explicit model construction)\<close>

definition The_optional :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "The_optional P = (if \<exists>!x. P x then Some (THE x. P x) else None)"

lemma The_optional_eq_SomeD: "The_optional P = Some x \<Longrightarrow> P x"
  unfolding The_optional_def
  by (metis option.discI option.inject theI_unique)

lemma Some_eq_The_optionalD: "Some x = The_optional P \<Longrightarrow> P x"
  using The_optional_eq_SomeD by metis

lemma The_optional_eq_NoneD: "The_optional P = None \<Longrightarrow> \<nexists>!x. P x"
  unfolding The_optional_def
  by (metis option.discI)

lemma None_eq_The_optionalD: "None = The_optional P \<Longrightarrow> \<nexists>!x. P x"
  unfolding The_optional_def
  by (metis option.discI)

lemma The_optional_eq_SomeI:
  assumes "\<exists>\<^sub>\<le>\<^sub>1x. P x" and "P x"
  shows "The_optional P = Some x"
  using assms by (metis The_optional_def the1_equality')

inductive ord_res_5 where
  skip: "
    (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')" |

  production: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<M>' = \<M>(atm_of L := Some C) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')" |

  factoring: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<F>' = finsert C \<F> \<Longrightarrow>
    \<M>' = (\<lambda>_. None) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>')" |

  resolution: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<M> (atm_of L) = Some D \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    \<M>' = (\<lambda>_. None) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>')"

inductive ord_res_5_step where
  "ord_res_5 N s s' \<Longrightarrow> ord_res_5_step (N, s) (N, s')"

lemma tranclp_ord_res_5_step_if_tranclp_ord_res_5:
  "(ord_res_5 N)\<^sup>+\<^sup>+ s s' \<Longrightarrow> ord_res_5_step\<^sup>+\<^sup>+ (N, s) (N, s')"
  by (induction s' rule: tranclp_induct)
   (auto intro: ord_res_5_step.intros tranclp.intros)

inductive ord_res_5_final where
  model_found:
    "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, None)" |

  contradiction_found:
    "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, Some {#})"

interpretation ord_res_5_semantics: semantics where
  step = ord_res_5_step and
  final = ord_res_5_final
proof unfold_locales
  fix S5 :: "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
    ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" and
    \<M> :: "'f gterm \<Rightarrow> 'f gclause option" and
    \<C> :: "'f gclause option" where
    S5_def: "S5 = (N, (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>))"
    by (metis prod.exhaust)

  assume "ord_res_5_final S5"
  hence "\<C> = None \<or> \<C> = Some {#}"
    by (simp add: S5_def ord_res_5_final.simps)
  hence "\<nexists>x. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) x"
    by (auto simp: linorder_lit.is_maximal_in_mset_iff elim: ord_res_5.cases)
  thus "finished ord_res_5_step S5"
    by (simp add: S5_def finished_def ord_res_5_step.simps)
qed

lemma right_unique_ord_res_5: "right_unique (ord_res_5 N)"
proof (rule right_uniqueI)
  fix s s' s''
  assume step1: "ord_res_5 N s s'" and step2: "ord_res_5 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_5.cases)
    case hyps1: (skip \<M>1 C1 \<C>1' \<F>1 U1\<^sub>e\<^sub>r)
    with step2 show ?thesis
      by (cases N s s'' rule: ord_res_5.cases) simp_all
  next
    case hyps1: (production \<M>1 C1 L1 \<M>1' \<C>1' \<F>1 U1\<^sub>e\<^sub>r)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_5.cases)
      case (skip \<M>2 C2 \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      with hyps1 show ?thesis
        by simp
    next
      case hyps2: (production \<M>2 C2 L2 \<M>2' \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (factoring \<M>2 C2 L2 \<F>2 \<F>2' \<M>2' \<C>2' U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (resolution \<M>2 C2 L2 D2 U2\<^sub>e\<^sub>r' U2\<^sub>e\<^sub>r \<M>2' \<C>2' \<F>2)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    qed
  next
    case hyps1: (factoring \<M>1 C1 L1 \<F>1 \<F>1' \<M>1' \<C>1' U1\<^sub>e\<^sub>r)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_5.cases)
      case (skip \<M>2 C2 \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      with hyps1 show ?thesis
        by simp
    next
      case hyps2: (production \<M>2 C2 L2 \<M>2' \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (factoring \<M>2 C2 L2 \<F>2 \<F>2' \<M>2' \<C>2' U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (resolution \<M>2 C2 L2 D2 U2\<^sub>e\<^sub>r' U2\<^sub>e\<^sub>r \<M>2' \<C>2' \<F>2)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution \<M>1 C1 L1 D1 U1\<^sub>e\<^sub>r' U1\<^sub>e\<^sub>r \<M>1' \<C>1' \<F>1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_5.cases)
      case (skip \<M>2 C2 \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      with hyps1 show ?thesis
        by simp
    next
      case hyps2: (production \<M>2 C2 L2 \<M>2' \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (factoring \<M>2 C2 L2 \<F>2 \<F>2' \<M>2' \<C>2' U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    next
      case hyps2: (resolution \<M>2 C2 L2 D2 U2\<^sub>e\<^sub>r' U2\<^sub>e\<^sub>r \<M>2' \<C>2' \<F>2)
      have "U1\<^sub>e\<^sub>r = U2\<^sub>e\<^sub>r" "\<F>1 = \<F>2" "\<M>1 = \<M>2" "C1 = C2"
        using hyps1 hyps2 by simp_all
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      hence "D1 = D2"
        using \<open>\<M>1 (atm_of L1) = Some D1\<close> \<open>\<M>2 (atm_of L2) = Some D2\<close> \<open>\<M>1 = \<M>2\<close>
        by simp

      have "U1\<^sub>e\<^sub>r' = U2\<^sub>e\<^sub>r'"
        using \<open>U1\<^sub>e\<^sub>r' = finsert (eres D1 C1) U1\<^sub>e\<^sub>r\<close> \<open>U2\<^sub>e\<^sub>r' = finsert (eres D2 C2) U2\<^sub>e\<^sub>r\<close>
          \<open>D1 = D2\<close> \<open>C1 = C2\<close> \<open>U1\<^sub>e\<^sub>r = U2\<^sub>e\<^sub>r\<close>
        by argo

      moreover have "\<M>1' = \<M>2'"
        using \<open>\<M>1' = (\<lambda>_. None)\<close> \<open>\<M>2' = (\<lambda>_. None)\<close>
        by argo

      moreover have "\<C>1' = \<C>2'"
        using hyps1 hyps2 \<open>\<F>1 = \<F>2\<close> \<open>U1\<^sub>e\<^sub>r' = U2\<^sub>e\<^sub>r'\<close> by simp

      ultimately show ?thesis
        using \<open>s' = (U1\<^sub>e\<^sub>r', \<F>1, \<M>1', \<C>1')\<close> \<open>s'' = (U2\<^sub>e\<^sub>r', \<F>2, \<M>2', \<C>2')\<close>
          \<open>\<F>1 = \<F>2\<close>
        by argo
    qed
  qed
qed

lemma right_unique_ord_res_5_step: "right_unique ord_res_5_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_5_step x y \<Longrightarrow> ord_res_5_step x z \<Longrightarrow> y = z"
    using right_unique_ord_res_5[THEN right_uniqueD]
    by (elim ord_res_5_step.cases) (metis prod.inject)
qed

definition next_clause_in_factorized_clause where
  "next_clause_in_factorized_clause N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> C. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"

lemma next_clause_in_factorized_clause:
  assumes step: "ord_res_5 N s s'"
  shows "next_clause_in_factorized_clause N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
        linorder_cls.is_minimal_in_fset_ffilter_iff)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
        linorder_cls.is_minimal_in_fset_ffilter_iff)
next
  case (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff)
next
  case (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff)
qed

definition implicitly_factorized_clauses_subset where
  "implicitly_factorized_clauses_subset N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow> \<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r)"

lemma ord_res_5_preserves_implicitly_factorized_clauses_subset:
  assumes
    step: "ord_res_5 N s s'" and
    invars:
      "implicitly_factorized_clauses_subset N s" and
      "next_clause_in_factorized_clause N s"
  shows "implicitly_factorized_clauses_subset N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars
    by (simp add: implicitly_factorized_clauses_subset_def)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars
    by (simp add: implicitly_factorized_clauses_subset_def)
next
  case (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars
    by (smt (verit) Pair_inject assms(3) fimage_iff finsert_fsubset iefac_def
        implicitly_factorized_clauses_subset_def literal.collapse(1)
        next_clause_in_factorized_clause_def ex1_efac_eq_factoring_chain ex_ground_factoringI)
next
  case (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  thus ?thesis
    using invars
    by (simp add: fsubset_funion_eq implicitly_factorized_clauses_subset_def)
qed

lemma interp_eq_Interp_if_least_greater:
  assumes
    C_in: "C |\<in>| NN" and
    D_least_gt_C: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) NN) D"
  shows "ord_res.interp (fset NN) D = ord_res.interp (fset NN) C \<union> ord_res.production (fset NN) C"
proof -
  have nex_between_C_and_D: "\<not> (\<exists>CD |\<in>| NN. C \<prec>\<^sub>c CD \<and> CD \<prec>\<^sub>c D)"
    using D_least_gt_C
    unfolding linorder_cls.is_least_in_ffilter_iff by auto

  have "ord_res.interp (fset NN) D = ord_res.interp (fset {|B |\<in>| NN. B \<preceq>\<^sub>c C|}) D"
  proof (rule ord_res.interp_swap_clause_set)
    have "NN = {|B |\<in>| NN. B \<preceq>\<^sub>c C|} |\<union>| {|E |\<in>| NN. D \<preceq>\<^sub>c E|}"
      using nex_between_C_and_D by force
    show "{Da. Da |\<in>| NN \<and> Da \<prec>\<^sub>c D} = {Da. Da |\<in>| {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|} \<and> Da \<prec>\<^sub>c D}"
      using \<open>NN = {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|} |\<union>| ffilter ((\<prec>\<^sub>c)\<^sup>=\<^sup>= D) NN\<close> linorder_cls.leD by auto
  qed simp_all

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da. Da |\<in>| {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|} \<and> Da \<prec>\<^sub>c D})"
    unfolding ord_res.interp_def ..

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da \<in> fset NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C \<and> Da \<prec>\<^sub>c D})"
    by auto

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da \<in> fset NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C})"
  proof -
    have "{|Da |\<in>| NN. Da \<preceq>\<^sub>c C \<and> Da \<prec>\<^sub>c D|} = {|Da |\<in>| NN. Da \<preceq>\<^sub>c C|}"
      using nex_between_C_and_D
      by (metis (no_types, opaque_lifting) D_least_gt_C linorder_cls.is_least_in_fset_ffilterD(2)
          linorder_cls.le_less_trans)
    thus ?thesis
      by fastforce
  qed

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da \<in> fset NN. Da \<prec>\<^sub>c C}) \<union> ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C"
  proof -
    have "{Da. Da |\<in>| NN \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C} = insert C {Da. Da |\<in>| NN \<and> Da \<prec>\<^sub>c C}"
      using C_in by auto
    thus ?thesis
      by blast
  qed

  also have "\<dots> = ord_res_Interp (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C"
    unfolding ord_res.interp_def by auto

  also have "\<dots> = ord_res_Interp (fset NN) C"
  proof -
    have "ord_res.interp (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C = ord_res.interp (fset NN) C"
      using ord_res.interp_swap_clause_set[of "fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}" C "fset NN"]
      by auto

    moreover have "ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C = ord_res.production (fset NN) C"
      using ord_res.production_swap_clause_set[of "fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}" C "fset NN"]
      by auto

    ultimately show ?thesis
      by simp
  qed

  finally show ?thesis .
qed

lemma interp_eq_empty_if_least_in_set:
  assumes "linorder_cls.is_least_in_set N C"
  shows "ord_res.interp N C = {}"
  using assms
  unfolding ord_res.interp_def
  unfolding linorder_cls.is_least_in_set_iff
  by auto

definition model_eq_interp_upto_next_clause where
  "model_eq_interp_upto_next_clause N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> C. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) \<longrightarrow>
      dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C)"

lemma model_eq_interp_upto_next_clause:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "model_eq_interp_upto_next_clause N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case step_hyps: (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)

  have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
      using invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .

    also have "\<dots> = ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    proof -
      have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
        using \<open>dom \<M> \<TTurnstile> C\<close>
        unfolding invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>]
        by (simp add: ord_res.production_unfold)
      thus ?thesis
        by simp
    qed

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    proof (rule interp_eq_Interp_if_least_greater[symmetric])
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars(2)[unfolded next_clause_in_factorized_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
    next
      show "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using step_hyps(3-) that by (metis Some_eq_The_optionalD)
    qed

    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
next
  case step_hyps: (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)

  have "dom \<M>' = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M>' = dom \<M> \<union> {atm_of L}"
      unfolding \<open>\<M>' = \<M>(atm_of L \<mapsto> C)\<close> by simp

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<union> {atm_of L}"
      unfolding invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] ..

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<union>
      ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    proof -
      have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        using \<open>\<not> dom \<M> \<TTurnstile> C\<close>
        unfolding invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
      hence "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using \<open>is_pos L\<close> \<open>ord_res.is_strictly_maximal_lit L C\<close>
        using invars(2)[unfolded next_clause_in_factorized_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>]
        unfolding ord_res.production_unfold mem_Collect_eq
        by (metis linorder_lit.is_greatest_in_mset_iff literal.collapse(1) multi_member_split)
      hence "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {atm_of L}"
        by (metis empty_iff insertE ord_res.production_eq_empty_or_singleton)
      thus ?thesis
        by argo
    qed

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    proof (rule interp_eq_Interp_if_least_greater[symmetric])
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars(2)[unfolded next_clause_in_factorized_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
    next
      show "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using step_hyps(3-) that by (metis Some_eq_The_optionalD)
    qed

    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
next
  case step_hyps: (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)

  have "dom \<M>' = ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M>' = {}"
      using step_hyps(3-) by simp
    also have "\<dots> = ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    proof (rule interp_eq_empty_if_least_in_set[symmetric])
      show "linorder_cls.is_least_in_set (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using step_hyps(3-) that
        by (metis Some_eq_The_optionalD linorder_cls.is_least_in_fset_iff
            linorder_cls.is_least_in_set_iff)
    qed
    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
next
  case step_hyps: (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)

  have "dom \<M>' = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M>' = {}"
      using step_hyps(3-) by simp
    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D"
    proof (rule interp_eq_empty_if_least_in_set[symmetric])
      show "linorder_cls.is_least_in_set (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D"
        using step_hyps(3-) that
        by (metis Some_eq_The_optionalD linorder_cls.is_least_in_fset_iff
            linorder_cls.is_least_in_set_iff)
    qed
    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
qed

definition all_smaller_clauses_true_wrt_respective_Interp where
  "all_smaller_clauses_true_wrt_respective_Interp N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C))"

lemma all_smaller_clauses_true_wrt_respective_Interp:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "all_smaller_clauses_true_wrt_respective_Interp N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case step_hyps: (skip \<M> D \<C>' \<F> U\<^sub>e\<^sub>r)

  have D_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    using invars(2) ord_res.production_unfold step_hyps(1) step_hyps(3)
    by (auto simp: model_eq_interp_upto_next_clause_def)

  have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = Some E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c E" for C E
  proof -
    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)
    hence "C \<preceq>\<^sub>c D"
      using C_in \<open>C \<prec>\<^sub>c E\<close>
      by (metis asympD linorder_cls.is_least_in_ffilter_iff linorder_cls.le_less_linear
          ord_res.asymp_less_cls)
    thus ?thesis
      using D_true
      using invars(1)[unfolded all_smaller_clauses_true_wrt_respective_Interp_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in] by auto
  qed

  moreover have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = None" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "\<nexists>x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      using step_hyps \<open>\<C>' = None\<close>
      by (metis (no_types, opaque_lifting) None_eq_The_optionalD linorder_cls.Uniq_is_least_in_fset
          the1_equality')
    hence "\<not> (\<exists>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c x)"
      by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)
    hence "C \<prec>\<^sub>c D \<or> C = D"
      using C_in by force
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      then show ?thesis
        using invars(1) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in
        by (auto simp: all_smaller_clauses_true_wrt_respective_Interp_def)
    next
      assume "C = D"
      then show ?thesis
        using D_true by argo
    qed
  qed

  ultimately show ?thesis
    using step_hyps
    by (smt (verit, best) all_smaller_clauses_true_wrt_respective_Interp_def old.prod.inject option.exhaust)
next
  case step_hyps: (production \<M> D K \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)

  have "K \<in># D"
    using step_hyps(3-) by (metis linorder_lit.is_greatest_in_mset_iff)

  have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    using \<open>\<not> dom \<M> \<TTurnstile> D\<close>
    unfolding invars(2)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
        OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>] .
  hence "atm_of K \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using \<open>is_pos K\<close> \<open>ord_res.is_strictly_maximal_lit K D\<close> \<open>K \<in># D\<close>
    using invars(3)[unfolded next_clause_in_factorized_clause_def, rule_format,
        OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>]
    unfolding ord_res.production_unfold mem_Collect_eq
    by (metis literal.collapse(1) multi_member_split)
  hence prod_D_eq: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {atm_of K}"
    by (metis empty_iff insertE ord_res.production_eq_empty_or_singleton)
  hence "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile>l K"
    using \<open>is_pos K\<close> by force
  hence D_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    using \<open>K \<in># D\<close> by auto

  have "dom \<M>' = dom \<M> \<union> {atm_of K}"
    unfolding \<open>\<M>' = \<M>(atm_of K \<mapsto> D)\<close> by simp

  also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<union> {atm_of K}"
    unfolding invars(2)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
        OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>] ..

  also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<union>
      ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using prod_D_eq by argo

  finally have dom_\<M>'_eq: "dom \<M>' = ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" .

  have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = Some E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c E" for C E
  proof -
    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)
    hence "C \<preceq>\<^sub>c D"
      using C_in \<open>C \<prec>\<^sub>c E\<close>
      by (metis asympD linorder_cls.is_least_in_ffilter_iff linorder_cls.le_less_linear
          ord_res.asymp_less_cls)
    thus ?thesis
      using D_true
      using invars(1)[unfolded all_smaller_clauses_true_wrt_respective_Interp_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in] by auto
  qed

  moreover have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = None" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "\<nexists>x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      using step_hyps \<open>\<C>' = None\<close>
      by (metis (no_types, opaque_lifting) None_eq_The_optionalD linorder_cls.Uniq_is_least_in_fset
          the1_equality')
    hence "\<not> (\<exists>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c x)"
      by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)
    hence "C \<prec>\<^sub>c D \<or> C = D"
      using C_in by force
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      then show ?thesis
        using invars(1) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in
        by (auto simp: all_smaller_clauses_true_wrt_respective_Interp_def)
    next
      assume "C = D"
      thus ?thesis
        using D_true by argo
    qed
  qed

  ultimately show ?thesis
    unfolding step_hyps(2) all_smaller_clauses_true_wrt_respective_Interp_def
    by (metis prod.inject option.exhaust)
next
  case step_hyps: (factoring \<M> D K \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using invars(2-) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>
    by (metis next_clause_in_factorized_clause_def)
  hence "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    using step_hyps(3-)
    by (smt (verit, ccfv_threshold) fimage_iff iefac_def literal.collapse(1)
        ex1_efac_eq_factoring_chain ex_ground_factoringI)
  hence "iefac \<F>' D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    unfolding \<open>\<F>' = finsert D \<F>\<close> by simp
  hence "\<C>' \<noteq> None"
    using step_hyps(3-)
    by (metis The_optional_eq_NoneD finsert_not_fempty linorder_cls.ex1_least_in_fset set_finsert)
  then obtain E where
    "\<C>' = Some E"
    by auto

  have "\<not> (\<exists>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E)"
    using \<open>\<C>' = Some E\<close> step_hyps(9)
    by (metis The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff
        linorder_cls.less_imp_not_less)

  thus ?thesis
    unfolding step_hyps(1,2) all_smaller_clauses_true_wrt_respective_Interp_def
    using \<open>\<C>' = Some E\<close> by simp
next
  case step_hyps: (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  hence "eres D C |\<in>| N |\<union>| U\<^sub>e\<^sub>r'"
    by simp
  hence "iefac \<F> (eres D C) |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    by simp
  hence "\<C>' \<noteq> None"
    using step_hyps(3-)
    by (metis The_optional_eq_NoneD finsert_not_fempty linorder_cls.ex1_least_in_fset set_finsert)
  then obtain E where
    "\<C>' = Some E"
    by auto

  have "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c E)"
    using \<open>\<C>' = Some E\<close> step_hyps(9)
    by (metis The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff
        linorder_cls.less_imp_not_less)

  thus ?thesis
    unfolding step_hyps(1,2) all_smaller_clauses_true_wrt_respective_Interp_def
    using \<open>\<C>' = Some E\<close> by simp
qed

lemma all_smaller_clauses_true_wrt_model:
  assumes
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
  shows "\<forall>U\<^sub>e\<^sub>r \<F> \<M> D. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> dom \<M> \<TTurnstile> C)"
proof (intro allI impI ballI)
  fix U\<^sub>e\<^sub>r \<F> \<M> D C
  assume
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)" and
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_lt: "C \<prec>\<^sub>c D"

  hence C_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    using invars(1)[unfolded all_smaller_clauses_true_wrt_respective_Interp_def s_def]
    by auto

  moreover have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using invars(2) s_def by (metis model_eq_interp_upto_next_clause_def)

  ultimately show "dom \<M> \<TTurnstile> C"
    using ord_res.entailed_clause_stays_entailed' C_lt by metis
qed

definition model_eq_interpretation where
  "model_eq_interpretation N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, None) \<longrightarrow>
      (let NN = fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) in dom \<M> = \<Union> (ord_res.production NN ` NN)))"

lemma all_smaller_clauses_true_wrt_model_strong:
  assumes
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
      "model_eq_interpretation N s"
  shows "\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> dom \<M> \<TTurnstile> C)"
proof (intro allI impI ballI)
  fix U\<^sub>e\<^sub>r \<F> \<M> \<C> C
  assume
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" and
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_lt: "\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D"
  hence C_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    using invars(1) by (metis all_smaller_clauses_true_wrt_respective_Interp_def)

  show "dom \<M> \<TTurnstile> C"
  proof (cases \<C>)
    case \<C>_def: None
    have "let NN = fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) in dom \<M> = \<Union> (ord_res.production NN ` NN)"
      using invars(3) s_def \<C>_def
      by (metis model_eq_interpretation_def)
    then show ?thesis
      using C_true
      by (smt (verit, ccfv_SIG) C_in UN_I insertCI linorder_lit.is_greatest_in_mset_iff
          ord_res.lift_entailment_to_Union ord_res.mem_productionE
          ord_res.production_eq_empty_or_singleton pos_literal_in_imp_true_cls
          sup_bot.right_neutral)
  next
    case \<C>_def: (Some D)
    have "C \<prec>\<^sub>c D"
      using C_lt \<C>_def by metis
    moreover have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      using invars(2) s_def \<C>_def by (metis model_eq_interp_upto_next_clause_def)
    ultimately show ?thesis
      using ord_res.entailed_clause_stays_entailed' C_true by metis
  qed
qed

lemma next_clause_lt_least_false_clause:
  assumes
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
  shows "\<forall>U\<^sub>e\<^sub>r \<F> \<M> C. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) \<longrightarrow>
    (\<forall>D. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D \<longrightarrow> C \<preceq>\<^sub>c D)"
proof (intro allI impI ballI)
  fix U\<^sub>e\<^sub>r \<F> \<M> C D
  assume
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)" and
    D_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
  then show "C \<preceq>\<^sub>c D"
    using invars[unfolded model_eq_interp_upto_next_clause_def
        all_smaller_clauses_true_wrt_respective_Interp_def, rule_format, OF s_def, simplified]
    by (metis (no_types, lifting) fimage.rep_eq is_least_false_clause_def
        linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2)
        linorder_cls.le_less_linear sup_fset.rep_eq)
qed

definition atoms_in_model_were_produced where
  "atoms_in_model_were_produced N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow> (\<forall>A C. \<M> A = Some C \<longrightarrow>
      A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C))"

lemma atoms_in_model_were_produced:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "atoms_in_model_were_produced N s"
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "atoms_in_model_were_produced N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars(1) by (simp add: atoms_in_model_were_produced_def)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  obtain A where "L = Pos A"
    using \<open>is_pos L\<close> by (cases L) simp_all

  have "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    unfolding ord_res.production_unfold mem_Collect_eq
  proof (intro exI conjI)
    show "atm_of L = A"
      unfolding \<open>L = Pos A\<close> literal.sel ..
  next
    show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars(3)[unfolded next_clause_in_factorized_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
  next
    have "L \<in># C"
      using \<open>linorder_lit.is_maximal_in_mset C L\<close>
      unfolding linorder_lit.is_maximal_in_mset_iff ..
    thus "C = add_mset (Pos A) (C - {#Pos A#})"
      unfolding \<open>L = Pos A\<close> by simp
  next
    show "ord_res.is_strictly_maximal_lit (Pos A) C"
      using \<open>ord_res.is_strictly_maximal_lit L C\<close>
      unfolding \<open>L = Pos A\<close> .
  next
    show "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
      using \<open>\<not> dom \<M> \<TTurnstile> C\<close>
      unfolding invars(2)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
  qed simp_all

  thus ?thesis
    using invars(1)
    by (simp add: atoms_in_model_were_produced_def
        \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close> \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close> \<open>\<M>' = \<M>(atm_of L \<mapsto> C)\<close>)
qed (simp_all add: atoms_in_model_were_produced_def)

lemma nbex_less_than_least_in_fset: "\<not> (\<exists>w |\<in>| X. w \<prec>\<^sub>c x)" if "linorder_cls.is_least_in_fset X x" for X x
  using that unfolding linorder_cls.is_least_in_fset_iff by auto

definition all_produced_atoms_in_model where
  "all_produced_atoms_in_model N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> D. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) \<longrightarrow> (\<forall>C A. C \<prec>\<^sub>c D \<longrightarrow>
      A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<longrightarrow> \<M> A = Some C))"

lemma all_produced_atoms_in_model:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "all_produced_atoms_in_model N s"
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "all_produced_atoms_in_model N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
    using invars
    by (metis ex_in_conv model_eq_interp_upto_next_clause_def local.skip(1) local.skip(3)
        ord_res.mem_productionE)
  thus ?thesis
    using invars(1) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>
    unfolding all_produced_atoms_in_model_def
    by (smt (verit, del_insts) Pair_inject The_optional_eq_SomeD empty_iff
        linorder_cls.is_least_in_ffilter_iff linorder_cls.not_less_iff_gr_or_eq local.skip(2)
        local.skip(4) ord_res.mem_productionE)
next
  case step_hyps: (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  obtain A where "L = Pos A"
    using \<open>is_pos L\<close> by (cases L) simp_all

  have "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    unfolding ord_res.production_unfold mem_Collect_eq
  proof (intro exI conjI)
    show "atm_of L = A"
      unfolding \<open>L = Pos A\<close> literal.sel ..
  next
    show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close> by (metis next_clause_in_factorized_clause_def)
  next
    have "L \<in># C"
      using \<open>linorder_lit.is_maximal_in_mset C L\<close>
      unfolding linorder_lit.is_maximal_in_mset_iff ..
    thus "C = add_mset (Pos A) (C - {#Pos A#})"
      unfolding \<open>L = Pos A\<close> by simp
  next
    show "ord_res.is_strictly_maximal_lit (Pos A) C"
      using \<open>ord_res.is_strictly_maximal_lit L C\<close>
      unfolding \<open>L = Pos A\<close> .
  next
    show "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
      using \<open>\<not> dom \<M> \<TTurnstile> C\<close>
      using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close> by (metis model_eq_interp_upto_next_clause_def)
  qed simp_all

  thus ?thesis
    using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>
    unfolding all_produced_atoms_in_model_def
    using \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close> \<open>\<M>' = \<M>(atm_of L \<mapsto> C)\<close>
    using prod.inject
    by (smt (verit, del_insts) Some_eq_The_optionalD asympD ord_res.mem_productionE
        linorder_cls.antisym_conv3 linorder_cls.is_least_in_ffilter_iff
        linorder_trm.not_less_iff_gr_or_eq step_hyps(8) map_upd_Some_unfold
        ord_res.asymp_less_cls ord_res.less_trm_iff_less_cls_if_mem_production)
next
  case step_hyps: (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  have "\<not> (\<exists>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D)" if "\<C>' = Some D" for D
  proof (rule nbex_less_than_least_in_fset)
    show "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
      using step_hyps that by (metis The_optional_eq_SomeD)
  qed
  thus ?thesis
    unfolding all_produced_atoms_in_model_def
    by (metis step_hyps(2) ord_res.mem_productionE prod.inject)
next
  case step_hyps: (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  have "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c D)" if "\<C>' = Some D" for D
  proof (rule nbex_less_than_least_in_fset)
    show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) D"
      using step_hyps that by (metis The_optional_eq_SomeD)
  qed
  thus ?thesis
    unfolding all_produced_atoms_in_model_def
    by (metis step_hyps(2) ord_res.mem_productionE prod.inject)
qed


definition ord_res_5_invars where
  "ord_res_5_invars N s \<longleftrightarrow>
    next_clause_in_factorized_clause N s \<and>
    implicitly_factorized_clauses_subset N s \<and>
    model_eq_interp_upto_next_clause N s \<and>
    all_smaller_clauses_true_wrt_respective_Interp N s \<and>
    atoms_in_model_were_produced N s \<and>
    all_produced_atoms_in_model N s"

lemma ord_res_5_invars_initial_state:
  assumes
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    C_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
  shows "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, Map.empty, Some C)"
  unfolding ord_res_5_invars_def
proof (intro conjI)
  show "next_clause_in_factorized_clause N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding next_clause_in_factorized_clause_def
    using C_least[unfolded linorder_cls.is_least_in_fset_iff] by simp
next
  show "implicitly_factorized_clauses_subset N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding implicitly_factorized_clauses_subset_def
    using \<F>_subset by simp
next
  have "ord_res.interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r)) C = {}"
    using C_least[unfolded linorder_cls.is_least_in_fset_iff]
    by (simp add: interp_eq_empty_if_least_in_set linorder_cls.is_least_in_set_iff)
  thus "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding model_eq_interp_upto_next_clause_def by simp
next
  have "\<not>(\<exists>Ca |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). Ca \<prec>\<^sub>c C)"
    using C_least[unfolded linorder_cls.is_least_in_fset_iff]
    by (metis linorder_cls.less_asym)
  thus "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding all_smaller_clauses_true_wrt_respective_Interp_def by simp
next
  show "atoms_in_model_were_produced N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding atoms_in_model_were_produced_def by simp
next
  have "\<forall>Ca. Ca \<prec>\<^sub>c C \<longrightarrow> Ca |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using C_least[unfolded linorder_cls.is_least_in_fset_iff]
    by (metis linorder_cls.order.asym)
  thus "all_produced_atoms_in_model N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding all_produced_atoms_in_model_def
    by (simp add: ord_res.production_unfold)
qed

lemma ord_res_5_preserves_invars:
  assumes step: "ord_res_5 N s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
proof -
  obtain U\<^sub>e\<^sub>r \<F> \<M> \<C> where s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    by (metis prod.exhaust)

  then show ?thesis
    unfolding ord_res_5_invars_def
    using invars[unfolded ord_res_5_invars_def]
    using next_clause_in_factorized_clause[OF step]
      ord_res_5_preserves_implicitly_factorized_clauses_subset[OF step]
      model_eq_interp_upto_next_clause[OF step]
      all_smaller_clauses_true_wrt_respective_Interp[OF step]
      atoms_in_model_were_produced[OF step]
      all_produced_atoms_in_model[OF step]
    by metis
qed

lemma rtranclp_ord_res_5_preserves_invars:
  assumes steps: "(ord_res_5 N)\<^sup>*\<^sup>* s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
  using steps invars
  by (induction s rule: converse_rtranclp_induct) (auto intro: ord_res_5_preserves_invars)

lemma tranclp_ord_res_5_preserves_invars:
  assumes steps: "(ord_res_5 N)\<^sup>+\<^sup>+ s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
  using rtranclp_ord_res_5_preserves_invars
  by (metis invars steps tranclp_into_rtranclp)

lemma le_least_false_clause:
  fixes N s U\<^sub>e\<^sub>r \<F> \<M> C D
  assumes
    invars: "ord_res_5_invars N s" and
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)" and
    D_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
  shows "C \<preceq>\<^sub>c D"
proof -
  have D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_least_false
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by argo

  show "C \<preceq>\<^sub>c D"
  proof (rule next_clause_lt_least_false_clause[rule_format])
    show "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
      using D_least_false .
  next
    show "(U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)" ..
  next
    show "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
      using invars by (metis s_def ord_res_5_invars_def)
  next
    show "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
      using invars by (metis s_def ord_res_5_invars_def)
  qed
qed

lemma ex_ord_res_5_if_not_final:
  assumes
    not_final: "\<not> ord_res_5_final S" and
    invars: "\<forall>N s. S = (N, s) \<longrightarrow> ord_res_5_invars N s"
  shows "\<exists>S'. ord_res_5_step S S'"
proof -
  from not_final obtain N U\<^sub>e\<^sub>r \<F> \<M> C where
    S_def: "S = (N, (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C))" and "C \<noteq> {#}"
    unfolding ord_res_5_final.simps de_Morgan_disj not_ex
    by (metis option.exhaust surj_pair)

  note invars' = invars[unfolded ord_res_5_invars_def, rule_format, OF S_def]

  have "\<exists>s'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s'"
  proof (cases "dom \<M> \<TTurnstile> C")
    case True
    thus ?thesis
      using ord_res_5.skip by metis
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
          using ord_res_5.production[OF C_false L_max L_pos] by metis
      next
        case L_not_striclty_max: False
        thus ?thesis
          using ord_res_5.factoring[OF C_false L_max L_pos L_not_striclty_max _ refl refl] by metis
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

      have "\<M> (atm_of L) = Some D"
        using invars'
        by (metis Neg \<open>D \<prec>\<^sub>c C\<close> all_produced_atoms_in_model_def D_prod insertI1 literal.sel(2))

      then show ?thesis
        using ord_res_5.resolution[OF C_false L_max L_neg] by metis
    qed
  qed
  thus ?thesis
    using S_def ord_res_5_step.simps by metis
qed

lemma ord_res_5_safe_state_if_invars:
  "safe_state ord_res_5_step ord_res_5_final (N, s)" if invars: "ord_res_5_invars N s" for N s
  unfolding safe_state_def
proof (intro allI impI)
  fix S'
  assume "ord_res_5_semantics.eval (N, s) S'"
  then obtain s' where "S' = (N, s')" and "(ord_res_5 N)\<^sup>*\<^sup>* s s'"
  proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
    case base
    thus ?case by simp
  next
    case (step z)
    thus ?case
      by (smt (verit, ccfv_SIG) converse_rtranclp_into_rtranclp ord_res_5_step.cases prod.inject)
  qed
  hence "ord_res_5_invars N s'"
    using invars rtranclp_ord_res_5_preserves_invars by metis
  hence "\<not> ord_res_5_final S' \<Longrightarrow> \<exists>S''. ord_res_5_step S' S''"
    using ex_ord_res_5_if_not_final[of S'] \<open>S' = (N, s')\<close> by blast
  thus "ord_res_5_final S' \<or> Ex (ord_res_5_step S')"
    by argo
qed

lemma MAGIC1:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
  shows "\<exists>\<M>' \<C>'. (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') \<and>
    (\<nexists>\<M>'' \<C>''. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<M>'', \<C>''))"
proof -
  define R where
    "R = (\<lambda>(\<M>, \<C>) (\<M>', \<C>'). ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>'))"

  define f :: "('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow> 'f gclause fset" where
    "f = (\<lambda>(\<M>, \<C>). case \<C> of None \<Rightarrow> {||} | Some C \<Rightarrow> finsert C {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|})"

  have "Wellfounded.wfp_on {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'} R\<inverse>\<inverse>"
  proof (rule wfp_on_if_convertible_to_wfp_on)
    have "wfp (|\<subset>|)"
      by auto
    thus "Wellfounded.wfp_on (f ` {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'}) (|\<subset>|)"
      using Wellfounded.wfp_on_subset subset_UNIV by metis
  next
    fix x y :: "('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

    obtain \<M>\<^sub>x \<C>\<^sub>x where x_def: "x = (\<M>\<^sub>x, \<C>\<^sub>x)"
      by force

    obtain \<M>\<^sub>y \<C>\<^sub>y where y_def: "y = (\<M>\<^sub>y, \<C>\<^sub>y)"
      by force

    have rtranclp_with_constsD: "(\<lambda>(y, z) (y', z'). R (x, y, z) (x, y', z'))\<^sup>*\<^sup>* (y, z) (y', z') \<Longrightarrow>
      R\<^sup>*\<^sup>* (x, y, z) (x, y', z')" for R x y z y' z'
    proof (induction "(y, z)" arbitrary: y z rule: converse_rtranclp_induct)
      case base
      show ?case
        by simp
    next
      case (step w)
      thus ?case
        by force
    qed 

    assume "x \<in> {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'}" and  "y \<in> {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'}"
    hence
      "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x)" and
      "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)"
      unfolding atomize_conj mem_Collect_eq R_def x_def y_def
      by (auto intro: rtranclp_with_constsD)
    hence
      x_invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x)" and
      y_invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)"
      using invars by (metis rtranclp_ord_res_5_preserves_invars)+

    assume "R\<inverse>\<inverse> y x"
    hence "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x) (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)"
      unfolding conversep_iff R_def x_def y_def prod.case .
    thus "f y |\<subset>| f x"
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x)" "(U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)")
      case step_hyps: (skip C)

      have "f y |\<subseteq>| {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}"
      proof (cases \<C>\<^sub>y)
        case None
        thus ?thesis
          unfolding f_def y_def prod.case by simp
      next
        case \<C>\<^sub>y_def: (Some D)

        have D_least: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using step_hyps \<C>\<^sub>y_def by (metis The_optional_eq_SomeD)
        hence f_y_eq: "f y = {|E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<preceq>\<^sub>c E|}"
          unfolding f_def y_def prod.case \<C>\<^sub>y_def option.case linorder_cls.is_least_in_ffilter_iff
          by auto

        show ?thesis
          unfolding f_y_eq subset_ffilter
          using D_least
          unfolding linorder_cls.is_least_in_ffilter_iff
          by auto
      qed

      also have "\<dots> |\<subset>| finsert C {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|}"
        by auto

      also have "\<dots> = f x"
        unfolding f_def x_def y_def prod.case step_hyps option.case by metis

      finally show ?thesis .
    next
      case step_hyps: (production C L)

      have "f y |\<subseteq>| {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}"
      proof (cases \<C>\<^sub>y)
        case None
        thus ?thesis
          unfolding f_def y_def prod.case by simp
      next
        case \<C>\<^sub>y_def: (Some D)

        have D_least: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using step_hyps \<C>\<^sub>y_def by (metis The_optional_eq_SomeD)
        hence f_y_eq: "f y = {|E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<preceq>\<^sub>c E|}"
          unfolding f_def y_def prod.case \<C>\<^sub>y_def option.case linorder_cls.is_least_in_ffilter_iff
          by auto

        show ?thesis
          unfolding f_y_eq subset_ffilter
          using D_least
          unfolding linorder_cls.is_least_in_ffilter_iff
          by auto
      qed

      also have "\<dots> |\<subset>| finsert C {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|}"
        by auto

      also have "\<dots> = f x"
        unfolding f_def x_def y_def prod.case step_hyps option.case by metis

      finally show ?thesis .
    next
      case step_hyps: (factoring C L)

      have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using x_invars unfolding \<open>\<C>\<^sub>x = Some C\<close>
        by (metis next_clause_in_factorized_clause_def ord_res_5_invars_def)
      hence "C |\<notin>| \<F>"
        using step_hyps(3,4,5)
        by (smt (verit, ccfv_SIG) fimage_iff iefac_def literal.collapse(1)
            ex1_efac_eq_factoring_chain ex_ground_factoringI)
      moreover have "C |\<in>| \<F>"
        using \<open>\<F> = finsert C \<F>\<close> by auto
      ultimately have False
        by contradiction
      thus ?thesis ..
    next
      case step_hyps: (resolution C L D)

      have D_productive: "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using x_invars step_hyps
        by (metis ord_res_5_invars_def atoms_in_model_were_produced_def)

      hence "\<exists>DC. ground_resolution D C DC"
        unfolding ground_resolution_def
        using step_hyps
        by (metis Neg_atm_of_iff ord_res.mem_productionE linorder_cls.le_less_linear
            linorder_lit.is_maximal_in_mset_iff linorder_trm.dual_order.order_iff_strict
            linorder_trm.not_less ord_res.less_trm_if_neg ex_ground_resolutionI)

      hence "eres D C \<noteq> C"
        unfolding eres_ident_iff by metis

      have "eres D C |\<notin>| U\<^sub>e\<^sub>r"
      proof (rule notI)
        assume "eres D C |\<in>| U\<^sub>e\<^sub>r"
        hence "iefac \<F> (eres D C) |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          by simp

        moreover have "iefac \<F> (eres D C) \<prec>\<^sub>c C"
        proof -
          have "iefac \<F> C \<prec>\<^sub>c D" if "C \<prec>\<^sub>c D" for \<F> C D
          proof (cases "C |\<in>| \<F>")
            case True
            hence "iefac \<F> C = efac C"
              by (simp add: iefac_def)
            also have "\<dots> \<preceq>\<^sub>c C"
              by (metis efac_subset subset_implies_reflclp_multp)
            also have "\<dots> \<prec>\<^sub>c D"
              using that .
            finally show ?thesis .
          next
            case False
            thus ?thesis
              using that by (simp add: iefac_def)
          qed

          moreover have "eres D C \<prec>\<^sub>c C"
          proof -
            have "eres D C \<preceq>\<^sub>c C"
              using eres_le by metis
            thus "eres D C \<prec>\<^sub>c C"
              using \<open>eres D C \<noteq> C\<close> by order
          qed

          ultimately show ?thesis
            by metis
        qed

        ultimately have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (iefac \<F> (eres D C)) \<TTurnstile> iefac \<F> (eres D C)"
          using x_invars unfolding \<open>\<C>\<^sub>x = Some C\<close>
          unfolding ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def by fast
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> iefac \<F> (eres D C)"
          using ord_res.entailed_clause_stays_entailed' \<open>iefac \<F> (eres D C) \<prec>\<^sub>c C\<close> by metis
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> eres D C"
        proof (rule true_cls_iff_set_mset_eq[THEN iffD1, rotated])
          show "set_mset (iefac \<F> (eres D C)) = set_mset (eres D C)"
            using iefac_def by auto
        qed
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        proof -
          obtain m A D' C' where
            "ord_res.is_strictly_maximal_lit (Pos A) D" and
            D_def: "D = add_mset (Pos A) D'" and
            C_def: "C = replicate_mset (Suc m) (Neg A) + C'" and
            "Neg A \<notin># C'" and
            eres_D_C_eq: "eres D C = repeat_mset (Suc m) D' + C'"
            using \<open>eres D C \<noteq> C\<close>[THEN eres_not_identD] by metis

          hence
            "atm_of L = A" and
            D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            D_false: "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
            unfolding atomize_conj
            using D_productive
            unfolding ord_res.production_unfold mem_Collect_eq
            by (metis linorder_lit.Uniq_is_greatest_in_mset literal.inject(1) the1_equality')

          have D'_false: "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D'"
            using D_false D_def by fastforce

          have "D \<prec>\<^sub>c C"
            using \<open>\<exists>DC. ground_resolution D C DC\<close> left_premise_lt_right_premise_if_ground_resolution by blast

          let ?I = "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"

          assume "?I \<TTurnstile> eres D C"
          hence "?I \<TTurnstile> D' \<or> ?I \<TTurnstile> C'"
            unfolding eres_D_C_eq true_cls_union true_cls_repeat_mset_Suc .

          moreover have "\<not> ?I \<TTurnstile> D'"
            using (* D_false *) (* D'_false *) \<open>D \<prec>\<^sub>c C\<close>
            by (smt (verit) D_def D_productive \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
                diff_single_eq_union ord_res.mem_productionE linorder_lit.is_greatest_in_mset_iff
                ord_res.Uniq_striclty_maximal_lit_in_ground_cls
                ord_res.false_cls_if_productive_production ord_res_5_invars_def
                next_clause_in_factorized_clause_def step_hyps(1) the1_equality' x_invars)

          ultimately show "?I \<TTurnstile> C"
            by (simp add: C_def)
        qed
        hence "dom \<M>\<^sub>x \<TTurnstile> C"
          using x_invars \<open>\<C>\<^sub>x = Some C\<close>
          by (metis model_eq_interp_upto_next_clause_def ord_res_5_invars_def)
        thus False
          using \<open>\<not> dom \<M>\<^sub>x \<TTurnstile> C\<close> by contradiction
      qed
      hence False
        using \<open>U\<^sub>e\<^sub>r = finsert (eres D C) U\<^sub>e\<^sub>r\<close> by auto
      thus ?thesis ..
    qed
  qed

  then obtain \<M>' \<C>' where "R\<^sup>*\<^sup>* (\<M>, \<C>) (\<M>', \<C>')" and "\<nexists>z. R (\<M>', \<C>') z"
    using ex_terminating_rtranclp_strong by (metis surj_pair)

  show ?thesis
  proof (intro exI conjI)
    show "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
      using \<open>R\<^sup>*\<^sup>* (\<M>, \<C>) (\<M>', \<C>')\<close>
      by (induction "(\<M>, \<C>)" arbitrary: \<M> \<C> rule: converse_rtranclp_induct) (auto simp: R_def)
  next
    show "\<nexists>\<M>'' \<C>''. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<M>'', \<C>'')"
      using \<open>\<nexists>z. R (\<M>', \<C>') z\<close>
      by (simp add: R_def)
  qed
qed

lemma MAGIC2:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
  assumes "C \<noteq> {#}"
  shows "\<exists>s'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s'"
proof (cases "(dom \<M>) \<TTurnstile> C")
  case C_true: True
  thus ?thesis
    using ord_res_5.skip by metis
next
  case C_false: False
  obtain L where L_max: "linorder_lit.is_maximal_in_mset C L"
    using \<open>C \<noteq> {#}\<close> linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    hence L_pos: "is_pos L"
      by simp

    show ?thesis
    proof (cases "linorder_lit.is_greatest_in_mset C L")
      case L_greatest: True
      thus ?thesis
        using C_false L_max L_pos ord_res_5.production by metis
    next
      case L_not_greatest: False
      thus ?thesis
        using C_false L_max L_pos ord_res_5.factoring by metis
    qed
  next
    case (Neg A)
    hence L_neg: "is_neg L"
      by simp

    have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars unfolding ord_res_5_invars_def next_clause_in_factorized_clause_def by metis
    next
      have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using invars unfolding ord_res_5_invars_def model_eq_interp_upto_next_clause_def by metis

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
        using C_false model_eq_interp_upto_next_clause_def by simp
    next
      fix D
      assume
        "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        "D \<noteq> C" and
        "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"

      moreover have "\<forall>B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). B \<prec>\<^sub>c C \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) B \<TTurnstile> B"
        using invars
        unfolding ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def
        by simp

      ultimately show "C \<prec>\<^sub>c D"
        by force
    qed
    then obtain D where "D|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
        L_max[unfolded Neg] by metis

    have "\<M> (atm_of L) = Some D"
      using invars
      unfolding ord_res_5_invars_def all_produced_atoms_in_model_def
      by (metis Neg \<open>D \<prec>\<^sub>c C\<close> D_prod insertI1 literal.sel(2))

    thus ?thesis
      using ord_res_5.resolution C_false L_max L_neg by metis
  qed
qed

lemma MAGIC3:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" and
    steps: "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')" and
    no_more_steps: "(\<nexists>\<M>'' \<C>''. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<M>'', \<C>''))"
  shows "(\<forall>C. \<C>' = Some C \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
proof -
  have invars': "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
    using steps invars rtranclp_ord_res_5_preserves_invars by metis

  show ?thesis
  proof (cases \<C>')
    case None

    moreover have "\<nexists>C. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
    proof (rule notI, elim exE)
      fix C

      have "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using invars' unfolding ord_res_5_invars_def by metis
      hence "(\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C)"
        by (simp add: \<open>\<C>' = None\<close> all_smaller_clauses_true_wrt_respective_Interp_def)

      moreover assume "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"

      ultimately show False
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by metis
    qed

    ultimately show ?thesis
      by simp
  next
    case (Some D)

    moreover have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars' \<open>\<C>' = Some D\<close>
        unfolding ord_res_5_invars_def next_clause_in_factorized_clause_def
        by metis
    next
      have "D \<noteq> {#} \<Longrightarrow> \<exists>s'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', Some D) s'"
        using MAGIC2 invars' \<open>\<C>' = Some D\<close> by metis

      thus "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
        by (smt (verit) Pair_inject Un_empty_right Uniq_D calculation empty_iff invars'
            linorder_lit.Uniq_is_maximal_in_mset
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset no_more_steps option.inject
            ord_res_5.cases set_mset_empty model_eq_interp_upto_next_clause_def ord_res_5_invars_def
            true_cls_def unproductive_if_nex_strictly_maximal_pos_lit)
    next
      fix E
      assume
        "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        "E \<noteq> D" and
        "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"

      moreover have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        using invars' \<open>\<C>' = Some D\<close>
        unfolding ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def
        by simp

      ultimately show "D \<prec>\<^sub>c E"
        by force
    qed

    ultimately show ?thesis
      by (metis Uniq_D Uniq_is_least_false_clause option.inject)
  qed
qed

lemma ord_res_5_construct_model_upto_least_false_clause:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
  shows "\<exists>\<M>' \<C>'. (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') \<and>
    (\<forall>C. \<C>' = Some C \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
  using MAGIC1[OF invars] MAGIC3[OF invars] by metis

inductive ord_res_4_matches_ord_res_5 ::
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow> bool" where
  "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<Longrightarrow>
    (\<forall>C. \<C> = Some C \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C) \<Longrightarrow>
    ord_res_4_matches_ord_res_5 (N, U\<^sub>e\<^sub>r, \<F>) (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"

lemma ord_res_4_final_iff_ord_res_5_final:
  assumes match: "ord_res_4_matches_ord_res_5 S4 S5"
  shows "ord_res_4_final S4 \<longleftrightarrow> ord_res_5_final S5"
  using match
proof (cases S4 S5 rule: ord_res_4_matches_ord_res_5.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)

  show ?thesis
    unfolding match_hyps(1,2,3)
  proof (intro iffI ord_res_5_final.intros)
    assume "ord_res_4_final (N, U\<^sub>e\<^sub>r, \<F>)"
    hence "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<or> \<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
      by (simp add: ord_res_4_final.simps ord_res_final_def)
    thus "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    proof (elim disjE)
      assume "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      hence "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) {#}"
        using is_least_false_clause_mempty by metis
      hence "\<C> = Some {#}"
        by (smt (verit) all_smaller_clauses_true_wrt_respective_Interp_def is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff linorder_cls.le_imp_less_or_eq match_hyps(3)
            mempty_lesseq_cls ord_res_5_invars_def)
      thus ?thesis
        using ord_res_5_final.contradiction_found by metis
    next
      assume "\<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
      hence "\<C> = None"
        using match_hyps(2-)
        by (metis ex_false_clause_if_least_false_clause option.exhaust)
      thus ?thesis
        using ord_res_5_final.model_found by metis
    qed
  next
    assume "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    thus "ord_res_4_final (N, U\<^sub>e\<^sub>r, \<F>)"
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" rule: ord_res_5_final.cases)
      case model_found
      have "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
        using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        unfolding ord_res_5_invars_def by metis
      hence "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). ord_res_Interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r)) C \<TTurnstile> C"
        by (simp add: model_found all_smaller_clauses_true_wrt_respective_Interp_def)
      hence "\<not> ex_false_clause (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
        by (simp add: ex_false_clause_def)
      then show ?thesis
        by (metis ord_res_4_final.intros ord_res_final_def)
    next
      case contradiction_found
      hence "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        by (metis next_clause_in_factorized_clause_def ord_res_5_invars_def)
      then show ?thesis
        by (metis ord_res_4_final.intros ord_res_final_def)
    qed
  qed
qed

lemma forward_simulation_between_4_and_5:
  fixes S4 S4' S5
  assumes match: "ord_res_4_matches_ord_res_5 S4 S5" and step: "ord_res_4_step S4 S4'"
  shows "\<exists>S5'. ord_res_5_step\<^sup>+\<^sup>+ S5 S5' \<and> ord_res_4_matches_ord_res_5 S4' S5'"
  using match
proof (cases S4 S5 rule: ord_res_4_matches_ord_res_5.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)
  hence
    S4_def: "S4 = (N, U\<^sub>e\<^sub>r, \<F>)" and
    S5_def: "S5 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    unfolding atomize_conj by metis

  have dom_\<M>_eq: "\<And>C. \<C> = Some C \<Longrightarrow> dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    using match_hyps unfolding ord_res_5_invars_def model_eq_interp_upto_next_clause_def by simp

  obtain s4' where S4'_def: "S4' = (N, s4')" and step': "ord_res_4 N (U\<^sub>e\<^sub>r, \<F>) s4'"
    using step unfolding S4_def by (auto simp: ord_res_4_step.simps)

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>)" s4' rule: ord_res_4.cases)
    case step_hyps: (factoring NN C L \<F>')
    have "\<C> = Some C"
      using match_hyps(3-) step_hyps by metis

    define \<M>' :: "'f gterm \<Rightarrow> 'f gterm literal multiset option" where
      "\<M>' = (\<lambda>_. None)"

    define \<C>' :: "'f gclause option" where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)))"

    have ord_res_5_step: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>')"
    proof (rule ord_res_5.factoring)
      have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        using step_hyps by argo
      then show "\<not> dom \<M> \<TTurnstile> C"
        using dom_\<M>_eq[OF \<open>\<C> = Some C\<close>]
        by (metis (mono_tags, lifting) is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff ord_res_Interp_entails_if_greatest_lit_is_pos
            unproductive_if_nex_strictly_maximal_pos_lit sup_bot.right_neutral)
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by metis
    next
      show "is_pos L"
        using step_hyps by metis
    next
      show "\<not> ord_res.is_strictly_maximal_lit L C"
        using step_hyps
        by (metis (no_types, lifting) is_least_false_clause_def literal.collapse(1)
            pos_lit_not_greatest_if_maximal_in_least_false_clause)
    next
      show "\<F>' = finsert C \<F>"
        using step_hyps by metis
    qed (simp_all add: \<M>'_def \<C>'_def)

    moreover have "\<exists>\<M>'' \<C>''.
       (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'') \<and>
       (\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
    proof (rule ord_res_5_construct_model_upto_least_false_clause)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>')"
        using ord_res_5_step \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some C\<close>
        by (metis ord_res_5_preserves_invars)
    qed

    ultimately obtain \<M>'' \<C>'' where
      s5_steps: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')" and
      next_clause_least_false:
        "(\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
      by (meson rtranclp_into_tranclp2)

    have "ord_res_5_step\<^sup>+\<^sup>+ S5 (N, U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')"
      unfolding S5_def \<open>\<C> = Some C\<close>
      using s5_steps by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

    moreover have "ord_res_4_matches_ord_res_5 S4' (N, U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')"
      unfolding S4'_def \<open>s4' = (U\<^sub>e\<^sub>r, \<F>')\<close>
    proof (intro ord_res_4_matches_ord_res_5.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>'', \<C>'')"
        using s5_steps \<open>\<C> = Some C\<close> \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        by (smt (verit, best) ord_res_5_preserves_invars tranclp_induct)
    next
      show "\<forall>C. (\<C>'' = Some C) = is_least_false_clause (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        using next_clause_least_false .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution NN C L D U\<^sub>e\<^sub>r')
    have "\<C> = Some C"
      using match_hyps(3-) step_hyps by metis

    define \<M>' :: "'f gterm \<Rightarrow> 'f gterm literal multiset option" where
      "\<M>' = (\<lambda>_. None)"

    define \<C>' :: "'f gclause option" where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')))"

    have ord_res_5_step: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>')"
    proof (rule ord_res_5.resolution)
      have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        using step_hyps by argo
      then show "\<not> dom \<M> \<TTurnstile> C"
        using dom_\<M>_eq[OF \<open>\<C> = Some C\<close>]
        by (metis (mono_tags, lifting) is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff ord_res_Interp_entails_if_greatest_lit_is_pos
            unproductive_if_nex_strictly_maximal_pos_lit sup_bot.right_neutral)
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by metis
    next
      show "is_neg L"
        using step_hyps by metis
    next
      show "\<M> (atm_of L) = Some D"
        using step_hyps
        by (smt (verit) \<open>\<C> = Some C\<close> all_produced_atoms_in_model_def insertI1 match_hyps(3)
            ord_res_5_invars_def)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r"
        using step_hyps by metis
    qed (simp_all add: \<M>'_def \<C>'_def)

    moreover have "\<exists>\<M>'' \<C>''.
       (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'') \<and>
       (\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C)"
    proof (rule ord_res_5_construct_model_upto_least_false_clause)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>')"
        using ord_res_5_step \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some C\<close>
        by (metis ord_res_5_preserves_invars)
    qed

    ultimately obtain \<M>'' \<C>'' where
      s5_steps: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')" and
      next_clause_least_false:
        "(\<forall>C. (\<C>'' = Some C) \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C)"
      by (meson rtranclp_into_tranclp2)

    have "ord_res_5_step\<^sup>+\<^sup>+ S5 (N, U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')"
      unfolding S5_def \<open>\<C> = Some C\<close>
      using s5_steps by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

    moreover have "ord_res_4_matches_ord_res_5 S4' (N, U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')"
      unfolding S4'_def \<open>s4' = (U\<^sub>e\<^sub>r', \<F>)\<close>
    proof (intro ord_res_4_matches_ord_res_5.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>'', \<C>'')"
        using s5_steps \<open>\<C> = Some C\<close> \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        by (smt (verit, best) ord_res_5_preserves_invars tranclp_induct)
    next
      show "\<forall>C. (\<C>'' = Some C) = is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
        using next_clause_least_false .
    qed

    ultimately show ?thesis
      by metis
  qed
qed

theorem bisimulation_ord_res_4_ord_res_5:
  defines "match \<equiv> \<lambda>_. ord_res_4_matches_ord_res_5"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow> bool) ORDER.
    bisimulation ord_res_4_step ord_res_5_step ord_res_4_final ord_res_5_final ORDER MATCH"
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_4_step"
    using right_unique_ord_res_4_step .
next
  show "right_unique ord_res_5_step"
    using right_unique_ord_res_5_step .
next
  show "\<forall>s. ord_res_4_final s \<longrightarrow> (\<nexists>s'. ord_res_4_step s s')"
    by (metis finished_def ord_res_4_semantics.final_finished)
next
  show "\<forall>s. ord_res_5_final s \<longrightarrow> (\<nexists>s'. ord_res_5_step s s')"
    by (metis finished_def ord_res_5_semantics.final_finished)
next
  show "\<forall>i s4 s5. match i s4 s5 \<longrightarrow> ord_res_4_final s4 \<longleftrightarrow> ord_res_5_final s5"
    unfolding match_def
    using ord_res_4_final_iff_ord_res_5_final by metis
next
  show "\<forall>i S4 S5. match i S4 S5 \<longrightarrow>
    safe_state ord_res_4_step ord_res_4_final S4 \<and> safe_state ord_res_5_step ord_res_5_final S5"
  proof (intro allI impI conjI)
    fix i S4 S5
    show "safe_state ord_res_4_step ord_res_4_final S4"
      using ord_res_4_step_safe safe_state_if_all_states_safe by metis

    assume "match i S4 S5"
    thus "safe_state ord_res_5_step ord_res_5_final S5"
      using \<open>match i S4 S5\<close>
      using ord_res_5_safe_state_if_invars
      using match_def ord_res_4_matches_ord_res_5.cases by metis
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i s1 s2 s1'.
       match i s1 s2 \<longrightarrow>
       ord_res_4_step s1 s1' \<longrightarrow>
       (\<exists>i' s2'. ord_res_5_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> False)"
    unfolding match_def
    using forward_simulation_between_4_and_5 by metis
qed


section \<open>ORD-RES-6 (model backjump)\<close>

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
    qed simp_all

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
        show "finite (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
          by simp
      next
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
        show "finite (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
          by simp
      next
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
          show "finite (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
            by simp
        next
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
        show "finite (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
          by simp
      next
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
          show "finite (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
            by simp
        next
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
        show "finite (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
          by simp
      next
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
          show "finite (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)))"
            by simp
        next
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

inductive ord_res_6_final where
  model_found:
    "ord_res_6_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, None)" |

  contradiction_found:
    "ord_res_6_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, Some {#})"

interpretation ord_res_6_semantics: semantics where
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
          qed simp_all

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
  unfolding safe_state_def
proof (intro allI impI)
  fix S'
  assume "ord_res_6_semantics.eval (N, s) S'"
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
  thus "ord_res_6_final S' \<or> Ex (ord_res_6_step S')"
    by argo
qed

inductive ord_res_5_matches_ord_res_6 ::
  "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow> bool" where
  "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<Longrightarrow>
    ord_res_5_matches_ord_res_6 (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"

lemma ord_res_5_final_iff_ord_res_6_final:
  fixes i S5 S6
  assumes match: "ord_res_5_matches_ord_res_6 S5 S6"
  shows "ord_res_5_final S5 \<longleftrightarrow> ord_res_6_final S6"
  using match
proof (cases S5 S6 rule: ord_res_5_matches_ord_res_6.cases)
  case (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)
  thus ?thesis
    by (metis (no_types, opaque_lifting) ord_res_5_final.simps ord_res_6_final.cases
        ord_res_6_final.contradiction_found ord_res_6_final.model_found)
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
proof (induction D rule: wfP_induct_rule)
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

lemma backward_simulation_between_5_and_6:
  fixes S5 S6 S6'
  assumes match: "ord_res_5_matches_ord_res_6 S5 S6" and step: "ord_res_6_step S6 S6'"
  shows "\<exists>S5'. ord_res_5_step\<^sup>+\<^sup>+ S5 S5' \<and> ord_res_5_matches_ord_res_6 S5' S6'"
  using match
proof (cases S5 S6 rule: ord_res_5_matches_ord_res_6.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C>)
  hence S5_def: "S5 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" and S6_def: "S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    by metis+

  obtain s6' where S6'_def: "S6' = (N, s6')" and step': "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) s6'"
    using step unfolding S6_def
    using ord_res_6_step.simps by auto

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" s6' rule: ord_res_6.cases)
    case step_hyps: (skip C \<C>')

    define S5' where
      "S5' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"

    show ?thesis
    proof (intro exI conjI)
      have step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using ord_res_5.skip step_hyps by metis
      hence "ord_res_5_step S5 S5'"
        unfolding S5_def S5'_def
        by (metis ord_res_5_step.simps step_hyps(1))
      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        by simp

      have "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using step5 match_hyps(3) ord_res_5_preserves_invars step_hyps(1) by metis
      thus "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')\<close>
        using ord_res_5_matches_ord_res_6.intros by metis
    qed
  next
    case step_hyps: (production C L \<M>' \<C>')

    define S5' where
      "S5' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"

    show ?thesis
    proof (intro exI conjI)
      have step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using ord_res_5.production step_hyps by metis
      hence "ord_res_5_step S5 S5'"
        unfolding S5_def S5'_def
        by (metis ord_res_5_step.simps step_hyps(1))
      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        by simp

      have "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using step5 match_hyps(3) ord_res_5_preserves_invars step_hyps(1) by metis
      thus "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close>
        using ord_res_5_matches_ord_res_6.intros by metis
    qed
  next
    case step_hyps: (factoring D K \<F>')

    define S5' where
      "S5' = (N, U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"

    have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      by (metis match_hyps(3) next_clause_in_factorized_clause_def ord_res_5_invars_def step_hyps(1))
    hence "iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) \<noteq> {||}"
      by blast
    then obtain C where C_least: "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
      by (metis linorder_cls.ex1_least_in_fset)

    have "efac D \<noteq> D"
      by (metis ex1_efac_eq_factoring_chain is_pos_def ex_ground_factoringI step_hyps(4,5,6))

    show ?thesis
    proof (intro exI conjI)
      have "The_optional (linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) = Some C"
      proof (rule The_optional_eq_SomeI)
        show "\<exists>\<^sub>\<le>\<^sub>1 x. linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) x"
          by blast
      next
        show "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          using C_least .
      qed
      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>', Map.empty, Some C)"
        using ord_res_5.factoring step_hyps by metis
      moreover have "(ord_res_5 N)\<^sup>*\<^sup>* \<dots> (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
      proof (rule full_rtranclp_ord_res_5_run_upto)
        show "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
          using step' S6_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))\<close> \<open>\<C> = Some D\<close> by argo
      next
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
          using match_hyps(3) ord_res_6_preserves_invars step' step_hyps(2) by blast
      (* next
        show "efac D \<prec>\<^sub>c D"
          using \<open>efac D \<noteq> D\<close> efac_properties_if_not_ident(1) by metis *)
      next
        have "iefac \<F> D = D" and "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
          unfolding atomize_conj
          using \<open>efac D \<noteq> D\<close> \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>[unfolded fimage_iff]
          unfolding iefac_def
          by (metis ex1_efac_eq_factoring_chain factorizable_if_neq_efac)

        have iefac_\<F>'_eq: "iefac \<F>' = (iefac \<F>)(D := efac D)"
          unfolding \<open>\<F>' = finsert D \<F>\<close> iefac_def by auto

        have fimage_iefac_\<F>'_eq:
          "iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r) = finsert (efac D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r - {|D|}))"
          unfolding iefac_\<F>'_eq
          unfolding fun_upd_fimage[of "iefac \<F>" D "efac D"] \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close>
          using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by argo

        have "{|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|} =
          {|C |\<in>| finsert (efac D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r - {|D|})). C \<prec>\<^sub>c efac D|}"
          unfolding fimage_iefac_\<F>'_eq ..

        also have "\<dots> = {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r - {|D|}). C \<prec>\<^sub>c efac D|}"
          by auto

        also have "\<dots> = {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|}"
          by (smt (verit, ccfv_SIG) \<open>iefac \<F> D = D\<close> efac_properties_if_not_ident(1)
              ffilter_eq_ffilter_minus_singleton fimage_finsert finsertI1 finsert_fminus1
              finsert_fminus_single linorder_cls.less_imp_not_less)

        finally have "{|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|} =
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c efac D|}" .
      next
        have dom_\<M>_eq: "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some D\<close>
          unfolding ord_res_5_invars_def model_eq_interp_upto_next_clause_def
          by metis

        have "atm_of K \<notin> dom \<M>"
          by (metis linorder_lit.is_maximal_in_mset_iff literal.collapse(1)
              pos_literal_in_imp_true_cls step_hyps(3) step_hyps(4) step_hyps(5))

        have "A \<prec>\<^sub>t atm_of K" if "A \<in> dom \<M>" for A
        proof -
          obtain C where
            "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            "C \<prec>\<^sub>c D" and
            "A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
            using \<open>A \<in> dom \<M>\<close> unfolding dom_\<M>_eq
            unfolding ord_res.interp_def UN_iff
            by blast

          hence "ord_res.is_strictly_maximal_lit (Pos A) C"
            using ord_res.mem_productionE by metis

          hence "Pos A \<preceq>\<^sub>l K"
            using \<open>ord_res.is_maximal_lit K D\<close> \<open>C \<prec>\<^sub>c D\<close>
            by (metis ord_res.asymp_less_lit ord_res.transp_less_lit linorder_cls.less_asym
                linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.leI
                linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp_eq_multp\<^sub>H\<^sub>O)

          hence "A \<preceq>\<^sub>t atm_of K"
            by (metis literal.collapse(1) literal.sel(1) ord_res.less_lit_simps(1) reflclp_iff
                step_hyps(5))

          moreover have "A \<noteq> atm_of K"
            using \<open>atm_of K \<notin> dom \<M>\<close> \<open>A \<in> dom \<M>\<close> by metis

          ultimately show ?thesis
            by order
        qed
        hence "dom \<M> \<subseteq> {A. \<exists>K. ord_res.is_maximal_lit K (efac D) \<and> A \<prec>\<^sub>t atm_of K}"
          using linorder_lit.is_maximal_in_mset_iff step_hyps(4) by auto
        thus "\<M> = restrict_map \<M> {A. \<exists>K. ord_res.is_maximal_lit K (efac D) \<and> A \<prec>\<^sub>t atm_of K}"
          using restrict_map_ident_if_dom_subset by fastforce
      next
        show "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
          using C_least .
      qed
      ultimately have steps5: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
        by simp
      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        using S5'_def S5_def step_hyps(1) tranclp_ord_res_5_step_if_tranclp_ord_res_5 by metis

      have "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))"
        using steps5 match_hyps(3) tranclp_ord_res_5_preserves_invars step_hyps(1) by metis
      thus "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac D))\<close>
        using ord_res_5_matches_ord_res_6.intros by metis
    qed
  next
    case step_hyps: (resolution_bot C L D U\<^sub>e\<^sub>r' \<M>')

    define S5' :: "_ \<times> _ \<times> _ \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option" where
      "S5' = (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some {#})"

    show ?thesis
    proof (intro exI conjI)
      have "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
        using \<open>U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r\<close> \<open>eres D C = {#}\<close>
        using iefac_def by simp

      hence "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) {#}"
        by (metis linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
            linorder_cls.is_minimal_in_fset_iff linorder_cls.leD mempty_lesseq_cls)

      hence "The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) = Some {#}"
        by (metis linorder_cls.Uniq_is_least_in_fset The_optional_eq_SomeI)

      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some {#})"
        using ord_res_5.resolution step_hyps by metis

      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        unfolding S5_def \<open>\<C> = Some C\<close> S5'_def
        by (simp only: ord_res_5_step.intros tranclp.r_into_trancl)

      show "ord_res_5_matches_ord_res_6 S5' S6'"
        using step5
        by (metis S5'_def S6'_def match_hyps(3) ord_res_5_matches_ord_res_6.intros
            ord_res_5_preserves_invars step_hyps(1) step_hyps(2))
    qed
  next
    case step_hyps: (resolution_pos E L D U\<^sub>e\<^sub>r' \<M>' K)

    define S5' :: "_ \<times> _ \<times> _ \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option" where
      "S5' = (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"

    hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<noteq> {||}"
      using \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp
    then obtain C where C_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
      by (metis linorder_cls.ex1_least_in_fset)

    show ?thesis
    proof (intro exI conjI)
      have "The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) = Some C"
      proof (rule The_optional_eq_SomeI)
        show "\<exists>\<^sub>\<le>\<^sub>1 x. linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) x"
          by blast
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
          using C_least .
      qed

      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, Map.empty, Some C)"
        using ord_res_5.resolution step_hyps by metis

      moreover have "(ord_res_5 N)\<^sup>*\<^sup>* \<dots> (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
      proof (rule full_rtranclp_ord_res_5_run_upto)
        show "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
          using step' \<open>\<C> = Some E\<close> \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))\<close> by argo
      next
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
          using match_hyps(3) ord_res_6_preserves_invars step' step_hyps(2) by blast
      (* next
        show "eres D E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
          by (metis match_hyps(3) ord_res_6_preserves_invars next_clause_in_factorized_clause_def
              ord_res_5_invars_def step' step_hyps(2)) *)
      next
        have "eres D E \<noteq> E"
          using step_hyps by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

        moreover have "eres D E \<preceq>\<^sub>c E"
          using eres_le .

        ultimately have "eres D E \<prec>\<^sub>c E"
          by order

        have "\<forall>F. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) F \<longrightarrow> E \<preceq>\<^sub>c F"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
          unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
          using next_clause_lt_least_false_clause[of N "(U\<^sub>e\<^sub>r, \<F>, \<M>, Some E)"]
          by simp

        have E_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) E"
          unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
        proof (intro conjI ballI impI)
          show "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
            using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
            unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
            by (metis next_clause_in_factorized_clause_def)
        next
          have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"
            using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
            unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
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
            using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
            unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
            unfolding all_smaller_clauses_true_wrt_respective_Interp_def
            using F_in F_false
            by (metis option.inject)
          thus "E \<prec>\<^sub>c F"
            using \<open>F \<noteq> E\<close> by order
        qed

        have D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<noteq> {}"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
          unfolding ord_res_5_invars_def \<open>\<C> = Some E\<close>
          by (metis atoms_in_model_were_produced_def empty_iff step_hyps(6))

        have "iefac \<F> (eres D E) = eres D E"
          using E_least_false D_prod
          by (smt (verit, ccfv_threshold)
              \<open>\<forall>F. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) F \<longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= E F\<close>
              \<open>eres D E \<prec>\<^sub>c E\<close> clause_true_if_resolved_true ex1_eres_eq_full_run_ground_resolution
              fimage_finsert finsert_absorb finsert_iff full_run_def funion_finsert_right
              is_least_false_clause_def is_least_false_clause_finsert_smaller_false_clause
              linorder_cls.is_least_in_fset_ffilterD(2) linorder_cls.leD match_hyps(3)
              next_clause_in_factorized_clause_def ord_res_5_invars_def ord_res_6_preserves_invars
              rtranclpD step' step_hyps(2) step_hyps(7))

        hence "{|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c eres D E|} =
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c eres D E|}"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by auto
      next
        show "\<M>' = restrict_map \<M> {A. \<exists>K. ord_res.is_maximal_lit K (eres D E) \<and> A \<prec>\<^sub>t atm_of K}"
          using \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close>
          by (smt (verit, ccfv_SIG) Collect_cong linorder_lit.Uniq_is_maximal_in_mset step_hyps(10)
              the1_equality')
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) C"
          using C_least .
      qed

      ultimately have steps5: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
        by simp

      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        unfolding S5_def \<open>\<C> = Some E\<close> S5'_def
        by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

      show "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))\<close>
        using steps5
        using match_hyps(3) ord_res_5_matches_ord_res_6.intros ord_res_6_preserves_invars step'
          step_hyps(2) by metis
    qed
  next
    case step_hyps: (resolution_neg E L D U\<^sub>e\<^sub>r' \<M>' K C)

    define S5' :: "_ \<times> _ \<times> _ \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option" where
      "S5' = (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"

    hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<noteq> {||}"
      using \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by simp
    then obtain B where B_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) B"
      by (metis linorder_cls.ex1_least_in_fset)

    show ?thesis
    proof (intro exI conjI)
      have "The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) = Some B"
      proof (rule The_optional_eq_SomeI)
        show "\<exists>\<^sub>\<le>\<^sub>1 x. linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) x"
          by blast
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) B"
          using B_least .
      qed

      hence step5: "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, Map.empty, Some B)"
        using ord_res_5.resolution step_hyps by metis

      moreover have "(ord_res_5 N)\<^sup>*\<^sup>* \<dots> (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
      proof (rule full_rtranclp_ord_res_5_run_upto)
        show "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
          using step' \<open>\<C> = Some E\<close> \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)\<close> by argo
      next
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
          using match_hyps(3) ord_res_6_preserves_invars step' step_hyps(2) by blast
        (* show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
          by (metis match_hyps(3) ord_res_6_preserves_invars next_clause_in_factorized_clause_def
              ord_res_5_invars_def step' step_hyps(2)) *)
      next
        have "ord_res.is_strictly_maximal_lit (Pos (atm_of K)) C"
          using \<open>\<M> (atm_of K) = Some C\<close>
            \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>[unfolded ord_res_5_invars_def
              atoms_in_model_were_produced_def, simplified]
          using ord_res.mem_productionE by blast

        moreover have "Pos (atm_of K) \<prec>\<^sub>l K"
          using \<open>is_neg K\<close> by (cases K) simp_all

        ultimately have "C \<prec>\<^sub>c eres D E"
          using \<open>ord_res.is_maximal_lit K (eres D E)\<close>
          by (metis ord_res.asymp_less_lit ord_res.transp_less_lit
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
              linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp_eq_multp\<^sub>H\<^sub>O)

        hence "C \<prec>\<^sub>c E"
          using eres_le[of D E] by order

        have "C \<prec>\<^sub>c efac (eres D E)"
          by (metis Uniq_D \<open>C \<prec>\<^sub>c eres D E\<close> efac_spec is_pos_def linorder_lit.Uniq_is_maximal_in_mset
              step_hyps(10) step_hyps(11))

        moreover have "efac (eres D E) \<preceq>\<^sub>c eres D E"
          by (metis efac_subset subset_implies_reflclp_multp)

        ultimately have "C \<prec>\<^sub>c iefac \<F> (eres D E)"
          unfolding iefac_def by auto

        hence "{|Ca |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). Ca \<prec>\<^sub>c C|} =
          {|Ca |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). Ca \<prec>\<^sub>c C|}"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> by auto

        have "(\<exists>K. ord_res.is_maximal_lit K C \<and> A \<prec>\<^sub>t atm_of K) \<longleftrightarrow> A \<prec>\<^sub>t atm_of K" for A
          using \<open>ord_res.is_strictly_maximal_lit (Pos (atm_of K)) C\<close>
          by (metis Uniq_def linorder_lit.Uniq_is_maximal_in_mset
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.sel(1))

        hence "{A. \<exists>K. ord_res.is_maximal_lit K C \<and> A \<prec>\<^sub>t atm_of K} = {A. A \<prec>\<^sub>t atm_of K}"
          by metis

        thus "\<M>' = restrict_map \<M> {A. \<exists>K. ord_res.is_maximal_lit K C \<and> A \<prec>\<^sub>t atm_of K}"
          using \<open>\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}\<close> by argo
      next
        show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) B"
          using B_least .
      qed

      ultimately have steps5: "(ord_res_5 N)\<^sup>+\<^sup>+ (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
        by simp

      thus "ord_res_5_step\<^sup>+\<^sup>+ S5 S5'"
        unfolding S5_def \<open>\<C> = Some E\<close> S5'_def
        by (metis tranclp_ord_res_5_step_if_tranclp_ord_res_5)

      show "ord_res_5_matches_ord_res_6 S5' S6'"
        unfolding S5'_def S6'_def \<open>s6' = (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)\<close>
        using steps5
        using match_hyps(3) ord_res_5_matches_ord_res_6.intros ord_res_6_preserves_invars step'
          step_hyps(2) by metis
    qed
  qed
qed

theorem bisimulation_ord_res_5_ord_res_6:
  defines "match \<equiv> \<lambda>_. ord_res_5_matches_ord_res_6"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow> bool) ORDER.
    bisimulation ord_res_5_step ord_res_6_step ord_res_5_final ord_res_6_final ORDER MATCH"
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_5_step"
    using right_unique_ord_res_5_step .
next
  show "right_unique ord_res_6_step"
    using right_unique_ord_res_6_step .
next
  show "\<forall>s. ord_res_5_final s \<longrightarrow> (\<nexists>s'. ord_res_5_step s s')"
    by (metis finished_def ord_res_5_semantics.final_finished)
next
  show "\<forall>s. ord_res_6_final s \<longrightarrow> (\<nexists>s'. ord_res_6_step s s')"
    by (metis finished_def ord_res_6_semantics.final_finished)
next
  show "\<forall>i S5 S6. match i S5 S6 \<longrightarrow> ord_res_5_final S5 \<longleftrightarrow> ord_res_6_final S6"
    unfolding match_def
    using ord_res_5_final_iff_ord_res_6_final by metis
next
  show "\<forall>i S5 S6.
       match i S5 S6 \<longrightarrow>
       safe_state ord_res_5_step ord_res_5_final S5 \<and> safe_state ord_res_6_step ord_res_6_final S6"
  proof (intro allI impI conjI)
    fix i S5 S6
    assume "match i S5 S6"
    show "safe_state ord_res_5_step ord_res_5_final S5"
      using \<open>match i S5 S6\<close>
      using ord_res_5_safe_state_if_invars
      using match_def ord_res_5_matches_ord_res_6.cases by metis
    show "safe_state ord_res_6_step ord_res_6_final S6"
      using \<open>match i S5 S6\<close>
      using ord_res_6_safe_state_if_invars
      using match_def ord_res_5_matches_ord_res_6.cases by metis
  qed
next
  show "wfp (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i S5 S6 S6'.
       match i S5 S6 \<longrightarrow>
       ord_res_6_step S6 S6' \<longrightarrow>
       (\<exists>i' S5'. ord_res_5_step\<^sup>+\<^sup>+ S5 S5' \<and> match i' S5' S6') \<or> (\<exists>i'. match i' S5 S6' \<and> False)"
    unfolding match_def
    using backward_simulation_between_5_and_6 by metis
qed


section \<open>ORD-RES-7 (literal trail)\<close>

lemma atms_of_clss_finsert[simp]:
  "atms_of_clss (finsert C N) = atms_of_cls C |\<union>| atms_of_clss N"
  unfolding atms_of_clss_def by simp

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

lemma "\<I> \<TTurnstile> C \<Longrightarrow> C \<noteq> {#}"
  by blast

primrec trail_atms :: "(_ literal \<times> _) list \<Rightarrow> _ fset" where
  "trail_atms [] = {||}" |
  "trail_atms (Ln # \<Gamma>) = finsert (atm_of (fst Ln)) (trail_atms \<Gamma>)"

lemma fset_trail_atms: "fset (trail_atms \<Gamma>) = atm_of ` fst ` set \<Gamma>"
  by (induction \<Gamma>) simp_all

definition clause_could_propagate where
  "clause_could_propagate \<Gamma> C L \<longleftrightarrow> \<not> trail_defined_lit \<Gamma> L \<and>
    linorder_lit.is_maximal_in_mset C L \<and> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}"

lemma trail_defined_lit_iff_trail_defined_atm:
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L |\<in>| trail_atms \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  show ?case
    by simp
next
  case (Cons Ln \<Gamma>)

  have "trail_defined_lit (Ln # \<Gamma>) L \<longleftrightarrow> L = fst Ln \<or> - L = fst Ln \<or> trail_defined_lit \<Gamma> L"
    unfolding trail_defined_lit_def by auto

  also have "\<dots> \<longleftrightarrow> atm_of L = atm_of (fst Ln) \<or> trail_defined_lit \<Gamma> L"
    by (cases L; cases "fst Ln") simp_all

  also have "\<dots> \<longleftrightarrow> atm_of L = atm_of (fst Ln) \<or> atm_of L |\<in>| trail_atms \<Gamma>"
    unfolding Cons.IH ..

  also have "\<dots> \<longleftrightarrow> atm_of L |\<in>| trail_atms (Ln # \<Gamma>)"
    by simp

  finally show ?case .
qed

lemma trail_false_cls_filter_mset_iff:
  "trail_false_cls \<Gamma> {#Ka \<in># C. Ka \<noteq> K#} \<longleftrightarrow> (\<forall>L\<in>#C. L \<noteq> K \<longrightarrow> trail_false_lit \<Gamma> L)"
  unfolding trail_false_cls_def by auto

lemma clause_could_propagate_iff: "clause_could_propagate \<Gamma> C K \<longleftrightarrow>
  \<not> trail_defined_lit \<Gamma> K \<and> ord_res.is_maximal_lit K C \<and> (\<forall>L\<in>#C. L \<noteq> K \<longrightarrow> trail_false_lit \<Gamma> L)"
  unfolding clause_could_propagate_def trail_false_cls_filter_mset_iff ..

lemma true_cls_imp_neq_mempty: "\<I> \<TTurnstile> C \<Longrightarrow> C \<noteq> {#}"
  by blast

thm ord_res_6.skip

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

interpretation ord_res_7_semantics: semantics where
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

lemma trail_consistent_if_sorted_wrt_atoms:
  assumes "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
  shows "trail_consistent \<Gamma>"
  using assms
proof (induction \<Gamma>)
  case Nil
  show ?case
    by simp
next
  case (Cons Ln \<Gamma>)

  obtain L opt where
    "Ln = (L, opt)"
    by fastforce

  show ?case
    unfolding \<open>Ln = (L, opt)\<close>
  proof (rule trail_consistent.Cons)
    have "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t atm_of (fst Ln)"
      using Cons.prems by simp

    hence "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<noteq> atm_of L"
      unfolding \<open>Ln = (L, opt)\<close> by fastforce

    thus "\<not> trail_defined_lit \<Gamma> L"
      unfolding trail_defined_lit_def by fastforce
  next
    show "trail_consistent \<Gamma>"
      using Cons by simp
  qed
qed

definition ord_res_7_invars where
  "ord_res_7_invars N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) \<longrightarrow>
      \<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r \<and>
      (\<forall>C. \<C> = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma> C) \<and>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})) \<and>
      sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma> \<and>
      linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)) \<and>
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

term \<open>      (\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
        (\<forall>C L. linorder_lit.is_maximal_in_mset C L \<longrightarrow> L \<prec>\<^sub>l fst Ln \<longrightarrow> trail_true_cls \<Gamma> C))\<close>

lemma not_lit_and_comp_lit_false_if_trail_consistent:
  assumes "trail_consistent \<Gamma>"
  shows "\<not> (trail_false_lit \<Gamma> L \<and> trail_false_lit \<Gamma> (- L))"
  using assms
proof (induction \<Gamma>)
  case Nil
  show ?case
    by simp
next
  case (Cons \<Gamma> K u)
  show ?case
  proof (cases "K = L \<or> K = - L")
    case True
    thus ?thesis
      unfolding trail_false_lit_def uminus_of_uminus_id
      unfolding de_Morgan_conj list.set image_insert prod.sel
      by (metis Cons.hyps(1) insertE trail_defined_lit_def uminus_not_id' uminus_of_uminus_id)
  next
    case False
    thus ?thesis
      unfolding trail_false_lit_def uminus_of_uminus_id
      by (metis (no_types, lifting) Cons.IH fst_conv image_iff set_ConsD trail_false_lit_def
          uminus_of_uminus_id)
  qed
qed

lemma not_trail_true_cls_and_trail_false_cls:
  fixes \<Gamma> :: "('a literal \<times> 'a clause option) list" and C :: "'a clause"
  shows "trail_consistent \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
proof (induction \<Gamma> rule: trail_consistent.induct)
  case Nil
  show ?case
    by simp
next
  case (Cons \<Gamma> L u)
  then show ?case
    by (metis trail_consistent.Cons trail_defined_lit_iff_true_or_false trail_false_cls_def
        trail_false_cls_iff_not_trail_interp_entails trail_interp_cls_if_trail_true)
qed

lemma trail_true_lit_if_trail_true_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma>' K \<Longrightarrow> trail_true_lit \<Gamma> K"
  by (meson image_mono set_mono_suffix subsetD trail_true_lit_def)

lemma trail_true_cls_if_trail_true_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_true_cls \<Gamma>' C \<Longrightarrow> trail_true_cls \<Gamma> C"
  using trail_true_cls_def trail_true_lit_if_trail_true_suffix by metis



lemma mono_atms_lt: "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
  (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))" for K
proof (intro monotone_onI, unfold le_bool_def, intro impI)
  fix x y
  assume "atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)" and "atm_of K \<preceq>\<^sub>t atm_of (fst y)"
  thus "atm_of K \<preceq>\<^sub>t atm_of (fst x)"
    by order
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
  by (metis (mono_tags, lifting) mem_Collect_eq set_mset_filter trail_defined_cls_def
      trail_defined_lit_iff_defined_uminus)

lemma trail_defined_cls_dropWhileI:
  assumes
    "sorted_wrt R \<Gamma>" and
    "monotone_on (set \<Gamma>) R (\<ge>) (\<lambda>x. P (fst x))" and
    "\<forall>L \<in># C. \<not> P L \<and> \<not> P (- L)" and
    "trail_defined_cls \<Gamma> C"
  shows "trail_defined_cls (dropWhile (\<lambda>Ln. P (fst Ln)) \<Gamma>) C"
  using assms(1,2,4)
proof (induction \<Gamma>)
  case Nil
  hence "C = {#}"
    by (simp add: trail_defined_cls_def)
  thus ?case
    by (simp add: trail_defined_cls_def)
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "P (fst Ln)")
    case True

    have "trail_defined_cls (dropWhile (\<lambda>Ln. P (fst Ln)) \<Gamma>) C"
    proof (rule Cons.IH)
      show "sorted_wrt R \<Gamma>"
        using Cons.prems(1) by simp
    next
      show "monotone_on (set \<Gamma>) R (\<lambda>x y. y \<le> x) (\<lambda>x. P (fst x))"
        using Cons.prems(2) by (meson monotone_on_subset set_subset_Cons)
    next
      show "trail_defined_cls \<Gamma> C"
        unfolding trail_defined_cls_def
      proof (intro ballI)
        fix L :: "'a literal"
        assume "L \<in># C"
        hence "\<not> P L \<and> \<not> P (- L)"
          using \<open>\<forall>L \<in># C. \<not> P L \<and> \<not> P (- L)\<close> by metis
        hence "L \<noteq> fst Ln \<and> - L \<noteq> fst Ln"
          using \<open>P (fst Ln)\<close> by metis
        moreover have "trail_defined_lit (Ln # \<Gamma>) L"
          using Cons.prems(3) \<open>L \<in># C\<close> by (metis trail_defined_cls_def)
        ultimately show "trail_defined_lit \<Gamma> L"
          by (simp add: trail_defined_lit_def)
      qed
    qed

    thus ?thesis
      using \<open>P (fst Ln)\<close>
      by simp
  next
    case False
    thus ?thesis
      using Cons.prems(3) by simp
  qed
qed

lemma trail_true_cls_dropWhileI:
  assumes
    "sorted_wrt R \<Gamma>" and
    "monotone_on (set \<Gamma>) R (\<ge>) (\<lambda>x. P (fst x))" and
    "\<forall>L \<in># C. \<not> P L" and
    "trail_true_cls \<Gamma> C"
  shows "trail_true_cls (dropWhile (\<lambda>Ln. P (fst Ln)) \<Gamma>) C"
  using assms(1,2,4)
proof (induction \<Gamma>)
  case Nil
  hence False
    by simp
  thus ?case ..
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "P (fst Ln)")
    case True

    have "trail_true_cls (dropWhile (\<lambda>Ln. P (fst Ln)) \<Gamma>) C"
    proof (rule Cons.IH)
      show "sorted_wrt R \<Gamma>"
        using Cons.prems(1) by simp
    next
      show "monotone_on (set \<Gamma>) R (\<lambda>x y. y \<le> x) (\<lambda>x. P (fst x))"
        using Cons.prems(2) by (meson monotone_on_subset set_subset_Cons)
    next
      show "trail_true_cls \<Gamma> C"
        using Cons.prems(3)
        using \<open>\<forall>L \<in># C. \<not> P L\<close> \<open>P (fst Ln)\<close>
        by (metis (no_types, lifting) image_insert insert_iff list.simps(15) trail_true_cls_def
            trail_true_lit_def)
    qed

    thus ?thesis
      using \<open>P (fst Ln)\<close>
      by simp
  next
    case False
    thus ?thesis
      using Cons.prems(3) by simp
  qed
qed

lemma clause_le_if_lt_least_greater:
  fixes N U\<^sub>e\<^sub>r \<F> C D
  defines
    "\<C> \<equiv> The_optional (linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) N))"
  assumes
    C_lt: "\<And>E. \<C> = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and
    C_in: "C |\<in>| N"
  shows "C \<preceq>\<^sub>c D"
proof (cases \<C>)
  case None

  hence "\<not> (\<exists>E. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) N) E)"
    using \<C>_def
    by (metis None_eq_The_optionalD Uniq_D linorder_cls.Uniq_is_least_in_fset)

  hence "\<not> (\<exists>E |\<in>| N. D \<prec>\<^sub>c E)"
    by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)

  thus ?thesis
    using C_in linorder_cls.less_linear by blast
next
  case (Some E)

  hence "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) N) E"
    using \<C>_def by (metis Some_eq_The_optionalD)

  hence "C \<prec>\<^sub>c D \<or> C = D"
    by (metis C_in C_lt Some ffmember_filter linorder_cls.neqE nbex_less_than_least_in_fset)

  thus ?thesis
    by simp
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
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. Some D = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_in by simp

  moreover have
    "trail_true_cls \<Gamma>' C"
    "\<And>K. linorder_lit.is_maximal_in_mset C K \<Longrightarrow> trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K#}"
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

    have "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#}"
      using clauses_lt_D_almost_defined
      using \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>C \<prec>\<^sub>c D\<close> C_max_lit by metis

    thus "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K#}"
      using \<open>suffix \<Gamma> \<Gamma>'\<close>
      by (metis trail_defined_cls_if_trail_defined_suffix)
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some D)\<close> ord_res_7_invars_def)
next
  case step_hyps: (skip_defined \<Gamma> D K U\<^sub>e\<^sub>r \<C>' \<F>)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
    using \<F>_subset .

  moreover have "\<forall>C'. \<C>' = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using step_hyps(7) by (metis linorder_cls.is_least_in_ffilter_iff Some_eq_The_optionalD)

  moreover have
    "trail_true_cls \<Gamma> C"
    "\<And>K. linorder_lit.is_maximal_in_mset C K \<Longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#}"
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
    thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>c#}"
      using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>c#}"
        using clauses_lt_D_almost_defined \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis
    next
      assume "C = D"

      have "trail_defined_cls \<Gamma> D"
        using \<open>trail_defined_lit \<Gamma> K\<close> \<open>trail_defined_cls \<Gamma> {#Ka \<in># D. Ka \<noteq> K#}\<close>
        unfolding trail_defined_cls_def by auto

      thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>c#}"
        using \<open>C = D\<close> unfolding trail_defined_cls_def by simp
    qed
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using \<Gamma>_sorted .

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>) (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
    using \<Gamma>_lower .

  moreover have "\<forall>D. \<C>' = Some D \<longrightarrow> (\<forall>A |\<in>| trail_atms \<Gamma>.
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

  moreover have "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longleftrightarrow> is_neg (fst Ln)"
    using \<Gamma>_deci_iff_neg .

  moreover have "\<forall>Ln \<in> set \<Gamma>. snd Ln = None \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c {#fst Ln#} \<longrightarrow> trail_true_cls \<Gamma> C)"
    using \<Gamma>_deci_ball_lt_true .

  moreover have "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using \<Gamma>_prop_in by simp

  moreover have "\<forall>Ln \<in> set \<Gamma>. \<forall>C. snd Ln = Some C \<longrightarrow> linorder_lit.is_greatest_in_mset C (fst Ln)"
    using \<Gamma>_prop_greatest by simp

  moreover have "\<forall>\<Gamma>\<^sub>1 L C \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some C) # \<Gamma>\<^sub>0 \<longrightarrow> trail_false_cls \<Gamma>\<^sub>0 {#K \<in># C. K \<noteq> L#}"
    using \<Gamma>_prop_almost_false .

  moreover have "(\<forall>\<Gamma>\<^sub>1 L D \<Gamma>\<^sub>0. \<Gamma> = \<Gamma>\<^sub>1 @ (L, Some D) # \<Gamma>\<^sub>0 \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma>\<^sub>0 C))"
    using \<Gamma>_prop_ball_lt_true .

  ultimately show ?thesis
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')\<close> ord_res_7_invars_def)
next
  case step_hyps: (skip_undefined_neg \<Gamma> D K U\<^sub>e\<^sub>r \<Gamma>' \<C>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have "suffix \<Gamma> \<Gamma>'"
    using step_hyps unfolding suffix_def by simp

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  moreover have "trail_true_cls \<Gamma>' C"
    "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow> trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
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
    show "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
      using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"

      hence "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using clauses_lt_D_almost_defined \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis

      thus "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_defined_cls_if_trail_defined_suffix)
    next
      assume "C = D"

      have "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
        using clause_almost_almost_definedI[OF D_in step_hyps(4,5)] .

      hence "trail_defined_cls \<Gamma>' {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
        using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis (no_types) trail_defined_cls_if_trail_defined_suffix)

      moreover have "trail_defined_lit \<Gamma>' K" and "trail_defined_lit \<Gamma>' (- K)"
        unfolding atomize_conj \<open>\<Gamma>' = (K, None) # \<Gamma>\<close> trail_defined_lit_def by simp

      ultimately show "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
        unfolding \<open>C = D\<close> trail_defined_cls_def by auto
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

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> ord_res_7_invars_def)
next
  case step_hyps: (skip_undefined_pos \<Gamma> D K U\<^sub>e\<^sub>r \<F> E)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>
  note E_least = \<open>linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E\<close>

  have "D \<prec>\<^sub>c E"
    using E_least unfolding linorder_cls.is_least_in_ffilter_iff by argo

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  moreover have "trail_true_cls \<Gamma> C"
    "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
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
    show "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
      using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"

      thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using clauses_lt_D_almost_defined \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis
    next
      assume "C = D"

      hence "K\<^sub>C = K"
        using C_max_lit D_max_lit by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

      thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using D_almost_defined unfolding \<open>C = D\<close> by metis
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some E)\<close> ord_res_7_invars_def)
next
  case step_hyps: (skip_undefined_pos_ultimate \<Gamma> D K U\<^sub>e\<^sub>r \<Gamma>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have "suffix \<Gamma> \<Gamma>'"
    using \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close> by (simp add: suffix_def)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  moreover have "trail_true_cls \<Gamma>' C"
    "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow> trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
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

    have "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
      using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using clauses_lt_D_almost_defined \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis
    next
      assume "C = D"
      thus "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using D_almost_defined C_max_lit D_max_lit
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
    qed

    thus "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
      using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_defined_cls_if_trail_defined_suffix)
  qed

  moreover have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>'"
  proof -
    have "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t atm_of K"
      by (metis image_eqI linorder_trm.less_linear linorder_trm.not_le step_hyps(6) trail_atms_le
          trail_defined_lit_def trail_defined_lit_iff_trail_defined_atm)

    thus ?thesis
      unfolding \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close>
      using \<Gamma>_sorted by simp
  qed

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
  proof -
    have "atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
      using \<open>atm_of K |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close> .

    moreover have "\<forall>w|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). w \<prec>\<^sub>t atm_of K \<longrightarrow> w |\<in>| trail_atms \<Gamma>"
      using step_hyps(5) by blast

    ultimately show ?thesis
      using \<Gamma>_lower by (simp add: \<open>\<Gamma>' = (- K, None) # \<Gamma>\<close> linorder_trm.is_lower_set_insertI)
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close> ord_res_7_invars_def)
next
  case step_hyps: (production \<Gamma> D K U\<^sub>e\<^sub>r \<Gamma>' \<C>' \<F>)

  have "suffix \<Gamma> \<Gamma>'"
    using step_hyps by (simp add: suffix_def)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  moreover have "trail_true_cls \<Gamma>' C"
    "\<And>K\<^sub>C. linorder_lit.is_maximal_in_mset C K\<^sub>C \<Longrightarrow> trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
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
    show "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
      using \<open>C \<prec>\<^sub>c D \<or> C = D\<close>
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"

      hence "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using clauses_lt_D_almost_defined \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> C_max_lit by metis

      thus "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
        using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_defined_cls_if_trail_defined_suffix)
    next
      assume "C = D"

      have "trail_defined_cls \<Gamma> {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
        using clause_almost_almost_definedI[OF D_in step_hyps(4,5)] .

      hence "trail_defined_cls \<Gamma>' {#L \<in># D. L \<noteq> K \<and> L \<noteq> - K#}"
        using \<open>suffix \<Gamma> \<Gamma>'\<close> by (metis trail_defined_cls_if_trail_defined_suffix)

      moreover have "trail_defined_lit \<Gamma>' K" and "trail_defined_lit \<Gamma>' (- K)"
        unfolding atomize_conj \<open>\<Gamma>' = (K, Some D) # \<Gamma>\<close> trail_defined_lit_def
        using \<open>is_pos K\<close> by (cases K) simp_all

      ultimately show "trail_defined_cls \<Gamma>' {#L \<in># C. L \<noteq> K\<^sub>C#}"
        unfolding \<open>C = D\<close> trail_defined_cls_def by auto
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

  moreover have "linorder_trm.is_lower_fset (trail_atms \<Gamma>') (atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r))"
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> ord_res_7_invars_def)
next
  case step_hyps: (factoring \<Gamma> D K U\<^sub>e\<^sub>r \<F>' \<F>)

  note D_max_lit = \<open>ord_res.is_maximal_lit K D\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_D_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_D_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac D))\<close> ord_res_7_invars_def)
next
  case step_hyps: (resolution_bot \<Gamma> E K D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' \<F>)

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_E_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  thm ord_res_7_invars_def

  have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r'"
    unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
    using \<F>_subset by blast

  moreover have "\<forall>C'. Some {#} = Some C' \<longrightarrow> C' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    by (simp add: \<open>eres D E = {#}\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

  moreover have "trail_true_cls \<Gamma>' x"
    "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow> trail_defined_cls \<Gamma> {#L \<in># x. L \<noteq> K\<^sub>x#}"
    if C_lt: "\<And>y. Some {#} = Some y \<Longrightarrow> x \<prec>\<^sub>c y" and x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" for x
  proof -
    have "x \<prec>\<^sub>c {#}"
      using C_lt by metis
    hence False
      using linorder_cls.leD mempty_lesseq_cls by blast
    thus
      "trail_true_cls \<Gamma>' x"
      "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow> trail_defined_cls \<Gamma> {#L \<in># x. L \<noteq> K\<^sub>x#}"
      by argo+
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})\<close> ord_res_7_invars_def)
next
  case step_hyps: (resolution_pos \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' K \<F>)

  note E_max_lit = \<open>ord_res.is_maximal_lit L E\<close>
  note eres_max_lit = \<open>ord_res.is_maximal_lit K (eres D E)\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_E_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  hence "D \<prec>\<^sub>c E"
    by (metis Uniq_D eres_ident_iff left_premise_lt_right_premise_if_ground_resolution
        linorder_lit.Uniq_is_maximal_in_mset step_hyps(4,5,10,11))

  have "eres D E \<noteq> E"
    unfolding eres_ident_iff not_not ground_resolution_def
  proof (rule ex_ground_resolutionI)
    show "ord_res.is_maximal_lit (Neg (atm_of L)) E"
      using \<open>ord_res.is_maximal_lit L E\<close> \<open>is_neg L\<close>
      by (cases L) simp_all
  next
    show "D \<prec>\<^sub>c E"
      using \<open>D \<prec>\<^sub>c E\<close> .
  next
    show "ord_res.is_strictly_maximal_lit (Pos (atm_of L)) D"
      using D_max_lit \<open>is_neg L\<close>
      by (cases L) simp_all
  qed

  have "eres D E \<prec>\<^sub>c E"
    using \<open>eres D E \<noteq> E\<close> eres_le by blast

  have "- L \<notin># E"
  proof (rule notI)
    assume "- L \<in># E"

    moreover have "L \<in># E"
      using E_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by metis

    ultimately have "trail_false_lit \<Gamma> (- L)" and "trail_false_lit \<Gamma> L"
      using \<open>trail_false_cls \<Gamma> E\<close> unfolding atomize_conj trail_false_cls_def by metis

    thus False
      using \<Gamma>_consistent not_lit_and_comp_lit_false_if_trail_consistent by metis
  qed

  hence "\<forall>K \<in># eres D E. atm_of K \<prec>\<^sub>t atm_of L"
    using lit_in_eres_lt_greatest_lit_in_grestest_resolvant[OF \<open>eres D E \<noteq> E\<close> E_max_lit] by metis

  hence "\<forall>K \<in># eres D E. K \<noteq> L \<and> K \<noteq> - L"
    by fastforce

  moreover have "\<forall>L \<in># eres D E. L \<in># D \<or> L \<in># E"
    using lit_in_one_of_resolvents_if_in_eres by metis

  moreover have D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> - L#}"
  proof -
    obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 where \<Gamma>_eq: "\<Gamma> = \<Gamma>\<^sub>1 @ (- L, Some D) # \<Gamma>\<^sub>0"
      using \<open>(- L, Some D) \<in> set \<Gamma>\<close> by (metis split_list)

    hence "trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D. K \<noteq> - L#}"
      using \<Gamma>_prop_almost_false by metis

    moreover have "suffix \<Gamma>\<^sub>0 \<Gamma>"
      using \<Gamma>_eq by (simp add: suffix_def)

    ultimately show ?thesis
      by (metis trail_false_cls_if_trail_false_suffix)
  qed

  ultimately have "trail_false_cls \<Gamma> (eres D E)"
    using \<open>trail_false_cls \<Gamma> E\<close> unfolding trail_false_cls_def by fastforce

  hence "trail_false_lit \<Gamma> K"
    using eres_max_lit unfolding linorder_lit.is_maximal_in_mset_iff trail_false_cls_def by metis

  have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
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
      using trail_false_cls_ignores_duplicates by (metis iefac_def set_mset_efac)

    thus False
      using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> (eres D E)\<close>
      by (metis not_trail_true_cls_and_trail_false_cls)
  qed

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

  moreover have
    "\<And>K\<^sub>x. linorder_lit.is_maximal_in_mset x K\<^sub>x \<Longrightarrow> trail_defined_cls \<Gamma>' {#L \<in># x. L \<noteq> K\<^sub>x#}" and
    "trail_true_cls \<Gamma>' x"
    if x_lt: "\<And>y. Some (eres D E) = Some y \<Longrightarrow> x \<prec>\<^sub>c y" and x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" for x
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
      using eres_max_lit \<open>x \<prec>\<^sub>c eres D E\<close>
      by (smt (verit, del_insts) calculation(1) calculation(3) empty_iff linorder_cls.less_not_sym
          linorder_lit.ex_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
          linorder_lit.less_trans linorder_lit.multp_if_maximal_less_that_maximal linorder_lit.neqE
          linorder_trm.not_less_iff_gr_or_eq literal.collapse(1) ord_res.less_lit_simps(4)
          set_mset_empty step_hyps(11) uminus_literal_def)

    ultimately have "atm_of L\<^sub>x \<prec>\<^sub>t atm_of K"
      by (smt (verit, best) \<Gamma>_consistent \<open>x \<prec>\<^sub>c eres D E\<close> asympD ord_res.less_lit_simps(1)
          linorder_lit.dual_order.strict_trans linorder_lit.is_greatest_in_set_iff
          linorder_lit.is_maximal_in_mset_iff linorder_lit.is_maximal_in_set_eq_is_greatest_in_set
          linorder_lit.is_maximal_in_set_iff linorder_trm.le_less_linear linorder_trm.less_linear
          literal.collapse(1) literal.exhaust_sel not_trail_true_cls_and_trail_false_cls
          ord_res.asymp_less_cls ord_res.less_lit_simps(2) ord_res.multp_if_all_left_smaller
          step_hyps(10) step_hyps(11) trail_false_cls_mempty x_true)

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
        using \<open>is_pos K\<close>
        by (metis linorder_lit.less_le_trans literal.collapse(1) literal.exhaust_sel
            ord_res.less_lit_simps(1) ord_res.less_lit_simps(4))

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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))\<close> ord_res_7_invars_def)
next
  case step_hyps: (resolution_neg \<Gamma> E L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<Gamma>' K C \<F>)

  note E_max_lit = \<open>ord_res.is_maximal_lit L E\<close>
  note eres_max_lit = \<open>ord_res.is_maximal_lit K (eres D E)\<close>

  have
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    clauses_lt_E_true: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow> trail_true_cls \<Gamma> C" and
    clauses_lt_E_almost_defined: "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E \<longrightarrow>
      (\<forall>K. linorder_lit.is_maximal_in_mset C K \<longrightarrow> trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#})" and
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

  hence "D \<prec>\<^sub>c E"
    using D_max_lit E_max_lit \<open>is_neg L\<close>
    by (metis Pos_atm_of_iff atm_of_eq_atm_of is_pos_neg_not_is_pos
        linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one
        linorder_lit.multp_if_maximal_less_that_maximal linorder_trm.dual_order.order_iff_strict
        literal.collapse(2) ord_res.less_lit_simps(2))

  have "eres D E \<noteq> E"
    unfolding eres_ident_iff not_not ground_resolution_def
  proof (rule ex_ground_resolutionI)
    show "ord_res.is_maximal_lit (Neg (atm_of L)) E"
      using \<open>ord_res.is_maximal_lit L E\<close> \<open>is_neg L\<close>
      by (cases L) simp_all
  next
    show "D \<prec>\<^sub>c E"
      using \<open>D \<prec>\<^sub>c E\<close> .
  next
    show "ord_res.is_strictly_maximal_lit (Pos (atm_of L)) D"
      using D_max_lit \<open>is_neg L\<close>
      by (cases L) simp_all
  qed

  hence "eres D E \<prec>\<^sub>c E"
    using eres_le by blast

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

  have "- L \<notin># E"
  proof (rule notI)
    assume "- L \<in># E"

    moreover have "L \<in># E"
      using E_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by metis

    ultimately have "trail_false_lit \<Gamma> (- L)" and "trail_false_lit \<Gamma> L"
      using \<open>trail_false_cls \<Gamma> E\<close> unfolding atomize_conj trail_false_cls_def by metis

    thus False
      using \<Gamma>_consistent not_lit_and_comp_lit_false_if_trail_consistent by metis
  qed

  hence "\<forall>K \<in># eres D E. atm_of K \<prec>\<^sub>t atm_of L"
    using lit_in_eres_lt_greatest_lit_in_grestest_resolvant[OF \<open>eres D E \<noteq> E\<close> E_max_lit] by metis

  hence "\<forall>K \<in># eres D E. K \<noteq> L \<and> K \<noteq> - L"
    by fastforce

  moreover have "\<forall>L \<in># eres D E. L \<in># D \<or> L \<in># E"
    using lit_in_one_of_resolvents_if_in_eres by metis

  moreover have D_almost_false: "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> - L#}"
  proof -
    obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>0 where \<Gamma>_eq: "\<Gamma> = \<Gamma>\<^sub>1 @ (- L, Some D) # \<Gamma>\<^sub>0"
      using \<open>(- L, Some D) \<in> set \<Gamma>\<close> by (metis split_list)

    hence "trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D. K \<noteq> - L#}"
      using \<Gamma>_prop_almost_false by metis

    moreover have "suffix \<Gamma>\<^sub>0 \<Gamma>"
      using \<Gamma>_eq by (simp add: suffix_def)

    ultimately show ?thesis
      by (metis trail_false_cls_if_trail_false_suffix)
  qed

  ultimately have "trail_false_cls \<Gamma> (eres D E)"
    using \<open>trail_false_cls \<Gamma> E\<close> unfolding trail_false_cls_def by fastforce

  have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
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
      using trail_false_cls_ignores_duplicates by (metis iefac_def set_mset_efac)

    thus False
      using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> (eres D E)\<close>
      by (metis not_trail_true_cls_and_trail_false_cls)
  qed

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
    "trail_true_cls \<Gamma>' x"
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
    by (simp add: \<open>s' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)\<close> ord_res_7_invars_def)
qed

lemma rtranclp_ord_res_7_preserves_ord_res_7_invars:
  assumes
    step: "(ord_res_7 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_7_invars N s"
  shows "ord_res_7_invars N s'"
  using step invars ord_res_7_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

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
  fixes N s
  assumes invars: "ord_res_7_invars N s"
  shows "safe_state (constant_context ord_res_7) ord_res_7_final (N, s)"
  unfolding safe_state_def
proof (intro allI impI)
  fix S'
  assume "ord_res_7_semantics.eval (N, s) S'"
  then obtain s' where "S' = (N, s')" and "(ord_res_7 N)\<^sup>*\<^sup>* s s'"
  proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
    case base
    thus ?case by simp
  next
    case (step z)
    thus ?case
      by (smt (verit, ccfv_SIG) converse_rtranclp_into_rtranclp constant_context.cases prod.inject)
  qed
  hence "ord_res_7_invars N s'"
    using invars by (metis rtranclp_ord_res_7_preserves_ord_res_7_invars)
  hence "\<not> ord_res_7_final (N, s') \<Longrightarrow> \<exists>s''. ord_res_7 N s' s''"
    using ex_ord_res_7_if_not_final[of N s'] by argo
  hence "\<not> ord_res_7_final S' \<Longrightarrow> \<exists>S''. constant_context ord_res_7 S' S''"
    unfolding \<open>S' = (N, s')\<close> using constant_context.intros by metis
  thus "ord_res_7_final S' \<or> Ex (constant_context ord_res_7 S')"
    by argo
qed

lemma dom_model_eq_trail_interp:
  assumes
    "\<forall>A C. \<M> A = Some C \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)" and
    "\<forall>Ln \<in> set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
  shows "dom \<M> = trail_interp \<Gamma>"
proof -
  have "dom \<M> = {A. \<exists>C. \<M> A = Some C}"
    unfolding dom_def by simp
  also have "\<dots> = {A. \<exists>C. map_of \<Gamma> (Pos A) = Some (Some C)}"
    using assms(1) by metis
  also have "\<dots> = {A. \<exists>opt. map_of \<Gamma> (Pos A) = Some opt}"
  proof (rule Collect_cong)
    show "\<And>A. (\<exists>C. map_of \<Gamma> (Pos A) = Some (Some C)) \<longleftrightarrow> (\<exists>opt. map_of \<Gamma> (Pos A) = Some opt)"
      using assms(2)
      by (metis literal.disc(1) map_of_SomeD option.exhaust)
  qed
  also have "\<dots> = trail_interp \<Gamma>"
  proof (induction \<Gamma>)
    case Nil
    thus ?case
      by (simp add: trail_interp_def)
  next
    case (Cons Ln \<Gamma>)

    have "{A. \<exists>opt. map_of (Ln # \<Gamma>) (Pos A) = Some opt} =
      {A. \<exists>opt. map_of [Ln] (Pos A) = Some opt} \<union> {A. \<exists>opt. map_of \<Gamma> (Pos A) = Some opt}"
      by auto

    also have "\<dots> = {A. Pos A = fst Ln} \<union> trail_interp \<Gamma>"
      unfolding Cons.IH by simp

    also have "\<dots> = trail_interp [Ln] \<union> trail_interp \<Gamma>"
      by (cases "fst Ln") (simp_all add: trail_interp_def)

    also have "\<dots> = trail_interp (Ln # \<Gamma>)"
      unfolding trail_interp_Cons[of Ln \<Gamma>] ..

    finally show ?case .
  qed
  finally show ?thesis .
qed

inductive ord_res_6_matches_ord_res_7 ::
  "'f gterm fset \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gterm literal \<times> 'f gclause option) list \<times> 'f gclause option \<Rightarrow> bool" where
  "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<Longrightarrow>
    ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) \<Longrightarrow>
    (\<forall>A C. \<M> A = Some C \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)) \<Longrightarrow>
    (\<forall>A. \<M> A = None \<longleftrightarrow> map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) - trail_atms \<Gamma> \<Longrightarrow>
    ord_res_6_matches_ord_res_7 i (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)"

lemma ord_res_6_final_iff_ord_res_7_final:
  fixes i S6 S7
  assumes match: "ord_res_6_matches_ord_res_7 i S6 S7"
  shows "ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
  using match
proof (cases i S6 S7 rule: ord_res_6_matches_ord_res_7.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C> \<Gamma>)

  show "ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
  proof (rule iffI)
    assume "ord_res_6_final S6"
    thus "ord_res_7_final S7"
      unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" rule: ord_res_6_final.cases)
      case model_found
      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.model_found
        by metis
    next
      case contradiction_found
      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.contradiction_found
        by metis
    qed
  next
    assume "ord_res_7_final S7"
    thus "ord_res_6_final S6"
      unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_final.cases)
      case model_found
      thus "ord_res_6_final S6"
        unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        using ord_res_6_final.model_found
        by metis
    next
      case contradiction_found
      thus "ord_res_6_final S6"
        unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
        using ord_res_6_final.contradiction_found
        by metis
    qed
  qed
qed

lemma backward_simulation_between_6_and_7:
  fixes i S6 S7 S7'
  assumes match: "ord_res_6_matches_ord_res_7 i S6 S7" and step: "constant_context ord_res_7 S7 S7'"
  shows "
    (\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> ord_res_6_matches_ord_res_7 i' S6' S7') \<or>
    (\<exists>i'. ord_res_6_matches_ord_res_7 i' S6 S7' \<and> i' |\<subset>| i)"
  using match
proof (cases i S6 S7 rule: ord_res_6_matches_ord_res_7.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C> \<Gamma>)

  note S6_def = \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
  note invars_6 = \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
  note invars_7 = \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>[
      unfolded ord_res_7_invars_def, rule_format, OF refl] 

  have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using invars_7 by argo

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using invars_7 by (metis trail_consistent_if_sorted_wrt_atoms)

  have \<Gamma>_distinct_atoms: "distinct (map fst \<Gamma>)"
    by (metis List.map.compositionality \<Gamma>_consistent distinct_atm_of_trail_if_trail_consistent
        distinct_map)

  have clause_true_wrt_model_if_true_wrt_\<Gamma>: "dom \<M> \<TTurnstile> D"
    if D_true: "trail_true_cls \<Gamma> D" for D
  proof -
    obtain L where "L \<in># D" and L_true: "trail_true_lit \<Gamma> L"
      using D_true unfolding trail_true_cls_def by auto

    have "\<exists>\<C>. (L, \<C>) \<in> set \<Gamma>"
      using L_true unfolding trail_true_lit_def by auto

    show ?thesis
    proof (cases L)
      case (Pos A)

      then obtain C where "(Pos A, Some C) \<in> set \<Gamma>"
        using invars_7 \<open>\<exists>\<C>. (L, \<C>) \<in> set \<Gamma>\<close>
        by (metis fst_conv literal.disc(1) not_None_eq snd_conv)

      hence "map_of \<Gamma> (Pos A) = Some (Some C)"
        using \<Gamma>_distinct_atoms by (metis map_of_is_SomeI)

      hence "\<M> A = Some C"
        using \<open>\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))\<close> by metis

      hence "A \<in> dom \<M>"
        by blast

      then show ?thesis
        using \<open>L \<in># D\<close> \<open>L = Pos A\<close> by blast
    next
      case (Neg A)

      hence "(Neg A, None) \<in> set \<Gamma>"
        using invars_7 \<open>\<exists>\<C>. (L, \<C>) \<in> set \<Gamma>\<close>
        by (metis fst_conv literal.disc(2) snd_conv)

      hence "map_of \<Gamma> (Neg A) \<noteq> None"
        by (simp add: weak_map_of_SomeI)

      hence "\<M> A = None"
        using \<open>\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)\<close> by metis

      hence "A \<notin> dom \<M>"
        by blast

      then show ?thesis
        using \<open>L \<in># D\<close> \<open>L = Neg A\<close> by blast
    qed
  qed

  have clause_false_wrt_model_if_false_wrt_\<Gamma>: "\<not> dom \<M> \<TTurnstile> D"
    if D_false: "trail_false_cls \<Gamma> D" for D
    unfolding true_cls_def
  proof (intro notI , elim bexE)
    fix L :: "'f gterm literal"
    assume "L \<in># D" and "dom \<M> \<TTurnstile>l L"

    have "trail_false_lit \<Gamma> L"
      using \<open>L \<in># D\<close> D_false unfolding trail_false_cls_def by metis

    hence "\<not> trail_true_lit \<Gamma> L" and "trail_defined_lit \<Gamma> L"
      unfolding atomize_conj
      using \<Gamma>_consistent \<open>L \<in># D\<close> not_trail_true_cls_and_trail_false_cls that
        trail_defined_lit_iff_true_or_false trail_true_cls_def by blast

    show False
    proof (cases L)
      case (Pos A)

      hence "\<M> A \<noteq> None"
        using \<open>dom \<M> \<TTurnstile>l L\<close> by blast

      hence "map_of \<Gamma> (Pos A) \<noteq> None"
        using \<open>\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))\<close> by blast

      hence "Pos A \<in> fst ` set \<Gamma>"
        by (simp add: map_of_eq_None_iff)

      hence "trail_true_lit \<Gamma> (Pos A)"
        unfolding trail_true_lit_def .

      moreover have "\<not> trail_true_lit \<Gamma> (Pos A)"
        using \<open>\<not> trail_true_lit \<Gamma> L\<close> \<open>L = Pos A\<close> by argo

      ultimately show False
        by contradiction
    next
      case (Neg A)

      hence "\<M> A = None"
        using \<open>dom \<M> \<TTurnstile>l L\<close> by blast

      hence "map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
        using \<open>\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)\<close> by blast

      hence "trail_true_lit \<Gamma> (Neg A) \<or> \<not> trail_defined_lit \<Gamma> (Neg A)"
        unfolding map_of_eq_None_iff not_not
        unfolding trail_true_lit_def trail_defined_lit_iff_trail_defined_atm literal.sel
        .

      then show ?thesis
        using \<open>\<not> trail_true_lit \<Gamma> L\<close> \<open>trail_defined_lit \<Gamma> L\<close> \<open>L = Neg A\<close> by argo
    qed
  qed

  obtain s7' where
    "S7' = (N, s7')" and
    step': "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) s7'"
    using step unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    by (auto elim: constant_context.cases)

  have invars_s7': "ord_res_7_invars N s7'"
    using ord_res_7_preserves_invars[OF step' \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>] .

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" s7' rule: ord_res_7.cases)
    case step_hyps: (decide_neg C L A \<Gamma>')

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)" and "A \<prec>\<^sub>t atm_of L" and "A |\<notin>| trail_atms \<Gamma>"
      using step_hyps unfolding atomize_conj linorder_trm.is_least_in_ffilter_iff by argo

    have "ord_res_6_matches_ord_res_7 i' S6 S7'"
      unfolding S6_def \<open>\<C> = Some C\<close> \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
        using invars_6 unfolding \<open>\<C> = Some C\<close> .
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', Some C)\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        using match_hyps unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
        using match_hyps \<open>A |\<notin>| trail_atms \<Gamma>\<close> by force
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        unfolding i'_def ..
    qed

    moreover have "i' |\<subset>| i"
    proof -
      have "i = finsert A i'"
        unfolding match_hyps i'_def
        using \<open>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>A |\<notin>| trail_atms \<Gamma>\<close> step_hyps(6) by force

      moreover have "A |\<notin>| i'"
        unfolding i'_def
        using step_hyps(6) by fastforce

      ultimately show ?thesis
        by auto
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_defined C L \<C>')

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"

    have C_almost_defined: "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      using step_hyps by (metis clause_almost_definedI invars_7)

    hence C_defined: "trail_defined_cls \<Gamma> C"
      using step_hyps unfolding trail_defined_cls_def by auto

    hence C_true: "trail_true_cls \<Gamma> C"
      using step_hyps by (metis trail_true_or_false_cls_if_defined)

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using clause_true_wrt_model_if_true_wrt_\<Gamma>[OF C_true] .
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>')\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps by argo
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)"
        using match_hyps by argo
    next
      show "i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>"
        using match_hyps by argo
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_undefined_neg C L \<Gamma>' \<C>')

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "trail_true_lit \<Gamma>' L"
      unfolding \<open>\<Gamma>' = (L, None) # \<Gamma>\<close> by (simp add: trail_true_lit_def)

    hence C_true: "trail_true_cls \<Gamma>' C"
      using step_hyps unfolding linorder_lit.is_maximal_in_mset_iff trail_true_cls_def by metis

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using C_true
        by (metis domIff linorder_lit.is_maximal_in_mset_iff literal.collapse(2) match_hyps(6)
            step_hyps(4) step_hyps(6) step_hyps(7) trail_defined_lit_iff_trail_defined_atm
            true_cls_def true_lit_simps(2))
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        using match_hyps
        unfolding \<open>\<Gamma>' = (L, None) # \<Gamma>\<close>
        by (metis literal.disc(1) map_of_Cons_code(2) step_hyps(7))
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        using match_hyps
        unfolding \<open>\<Gamma>' = (L, None) # \<Gamma>\<close>
        by (metis finsert_iff literal.collapse(2) literal.sel(2) map_of_Cons_code(2) option.discI
            prod.sel(1) step_hyps(6) step_hyps(7) trail_atms.simps(2)
            trail_defined_lit_iff_trail_defined_atm)
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_undefined_pos C L D)

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"

    have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L \<and> x \<noteq> - L#}"
    proof (rule clause_almost_almost_definedI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars_7 step_hyps by metis
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)"
        using step_hyps by argo
    qed

    moreover have "- L \<notin># C"
      by (metis atm_of_uminus is_pos_def linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE
          linorder_trm.less_irrefl literal.collapse(2) literal.sel(1) ord_res.less_lit_simps(4)
          step_hyps(4) step_hyps(7) uminus_not_id')

    ultimately have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      unfolding trail_defined_cls_def by auto

    hence "trail_true_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      using \<open>\<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close> by (metis trail_true_or_false_cls_if_defined)

    hence C_true: "trail_true_cls \<Gamma> C"
      by (auto simp: trail_true_cls_def)

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using clause_true_wrt_model_if_true_wrt_\<Gamma>[OF C_true] .
    next
      show "Some D = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using linorder_cls.Uniq_is_least_in_fset step_hyps(9) The_optional_eq_SomeI
        by fastforce
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, Some D)\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps by argo
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)"
        using match_hyps by argo
    next
      show "i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>"
        using match_hyps by argo
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (skip_undefined_pos_ultimate C L \<Gamma>')
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, None :: 'f gclause option)"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L \<and> x \<noteq> - L#}"
    proof (rule clause_almost_almost_definedI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars_7 step_hyps by metis
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A \<prec>\<^sub>t atm_of L \<and> A |\<notin>| trail_atms \<Gamma>)"
        using step_hyps by argo
    qed

    moreover have "- L \<notin># C"
      by (metis atm_of_uminus is_pos_def linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE
          linorder_trm.less_irrefl literal.collapse(2) literal.sel(1) ord_res.less_lit_simps(4)
          step_hyps(4) step_hyps(7) uminus_not_id')

    ultimately have "trail_defined_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      unfolding trail_defined_cls_def by auto

    hence "trail_true_cls \<Gamma> {#x \<in># C. x \<noteq> L#}"
      using \<open>\<not> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close> by (metis trail_true_or_false_cls_if_defined)

    hence C_true: "trail_true_cls \<Gamma> C"
      by (auto simp: trail_true_cls_def)

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, None)"
    proof (rule ord_res_6.skip)
      show "dom \<M> \<TTurnstile> C"
        using clause_true_wrt_model_if_true_wrt_\<Gamma>[OF C_true] .
    next
      have "\<not> (\<exists>D. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D)"
        using \<open>\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) ((\<prec>\<^sub>c) C)\<close>
        by (meson linorder_cls.is_least_in_ffilter_iff)

      thus "None = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        unfolding The_optional_def by metis
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, None)"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', None)\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (- L, None) # \<Gamma>\<close>
        by (metis is_pos_neg_not_is_pos literal.disc(1) map_of_Cons_code(2) step_hyps(7))
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (- L, None) # \<Gamma>\<close>
        by (metis (no_types, opaque_lifting) atm_of_eq_atm_of eq_fst_iff fset_simps(2) insertCI
            insertE literal.discI(2) literal.sel(2) map_of_Cons_code(2) option.distinct(1)
            trail_defined_lit_iff_trail_defined_atm step_hyps(6) step_hyps(7) trail_atms.simps(2))
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (production C L \<Gamma>' \<C>')
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>, \<M>(atm_of L \<mapsto> C), \<C>')"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"

    have "L \<in># C"
      using step_hyps unfolding linorder_lit.is_maximal_in_mset_iff by argo

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>(atm_of L \<mapsto> C), \<C>')"
    proof (rule ord_res_6.production)
      have "atm_of L |\<notin>| trail_atms \<Gamma>"
        using \<open>\<not> trail_defined_lit \<Gamma> L\<close>
        unfolding trail_defined_lit_iff_trail_defined_atm .

      hence "\<M> (atm_of L) = None"
        using match_hyps(3-) by metis

      hence "atm_of L \<notin> dom \<M>"
        unfolding dom_def by simp

      hence "\<not> dom \<M> \<TTurnstile>l L"
        using \<open>is_pos L\<close> unfolding true_lit_def by metis

      moreover have "\<not> dom \<M> \<TTurnstile> {#K \<in># C. K \<noteq> L#}"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close>] .

      ultimately show "\<not> dom \<M> \<TTurnstile> C"
        using \<open>L \<in># C\<close>
        unfolding true_cls_def by auto
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "is_pos L"
        using step_hyps by argo
    next
      show "ord_res.is_strictly_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<M>(atm_of L \<mapsto> C) = \<M>(atm_of L \<mapsto> C)" ..
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>(atm_of L \<mapsto> C), \<C>')"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>', \<C>')\<close> .
    next
      show "\<forall>A D. ((\<M>(atm_of L \<mapsto> C)) A = Some D) = (map_of \<Gamma>' (Pos A) = Some (Some D))"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>
        using step_hyps(7) by auto
    next
      show "\<forall>A. ((\<M>(atm_of L \<mapsto> C)) A = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        using match_hyps(3-)
        unfolding \<open>\<Gamma>' = (L, Some C) # \<Gamma>\<close>
        by (metis (no_types, opaque_lifting) domI domIff finsert_iff fun_upd_apply
            literal.collapse(1) literal.discI(2) map_of_Cons_code(2) map_of_eq_None_iff prod.sel(1)
            step_hyps(6) step_hyps(7) trail_atms.simps(2) trail_defined_lit_def uminus_Pos)
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (factoring C L \<F>')
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"

    have "L \<in># C"
      using step_hyps unfolding linorder_lit.is_maximal_in_mset_iff by argo

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
    proof (rule ord_res_6.factoring)
      have "atm_of L |\<notin>| trail_atms \<Gamma>"
        using \<open>\<not> trail_defined_lit \<Gamma> L\<close>
        unfolding trail_defined_lit_iff_trail_defined_atm .

      hence "\<M> (atm_of L) = None"
        using match_hyps(3-) by metis

      hence "atm_of L \<notin> dom \<M>"
        unfolding dom_def by simp

      hence "\<not> dom \<M> \<TTurnstile>l L"
        using \<open>is_pos L\<close> unfolding true_lit_def by metis

      moreover have "\<not> dom \<M> \<TTurnstile> {#K \<in># C. K \<noteq> L#}"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}\<close>] .

      ultimately show "\<not> dom \<M> \<TTurnstile> C"
        using \<open>L \<in># C\<close>
        unfolding true_cls_def by auto
    next
      show "ord_res.is_maximal_lit L C"
        using step_hyps by argo
    next
      show "is_pos L"
        using step_hyps by argo
    next
      show "\<not> ord_res.is_strictly_maximal_lit L C"
        using step_hyps by argo
    next
      show "\<F>' = finsert C \<F>"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some C\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
        using invars_6 unfolding \<open>\<C> = Some C\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>, Some (efac C))\<close> .
    next
      show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps(3-) by argo
    next
      show "\<forall>A. (\<M> A = None) = (map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>)"
        using match_hyps(3-) by argo
    next
      show "i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) |-| trail_atms \<Gamma>"
        using match_hyps(3-) by argo
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution_bot E L D U\<^sub>e\<^sub>r' \<Gamma>')
   
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r', \<F>, (\<lambda>_. None) :: 'f gterm \<Rightarrow> 'f gclause option, Some ({#} :: 'f gclause))"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<lambda>_. None, Some {#})"
    proof (rule ord_res_6.resolution_bot)
      show "\<not> dom \<M> \<TTurnstile> E"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> E\<close>] .
    next
      show "ord_res.is_maximal_lit L E"
        using step_hyps by argo
    next
      show "is_neg L"
        using step_hyps by argo
    next
      show "\<M> (atm_of L) = Some D"
        by (metis literal.collapse(2) match_hyps(5) step_hyps(5) step_hyps(6) uminus_Neg)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
        using step_hyps by argo
    next
      show "eres D E = {#}"
        using step_hyps by argo
    next
      show "((\<lambda>_. None)) = (\<lambda>_. None)" ..
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some E\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<lambda>_. None, Some {#})"
        using invars_6 unfolding \<open>\<C> = Some E\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some {#})\<close> .
    next
      show "\<forall>A C. (None = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
        unfolding \<open>\<Gamma>' = []\<close> by simp
    next
      show "\<forall>A. (None = None) = (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        unfolding \<open>\<Gamma>' = []\<close> by simp
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution_pos E L D U\<^sub>e\<^sub>r' \<Gamma>' K)

    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some (eres D E))"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"

    have mem_set_\<Gamma>'_iff: "\<And>x. (x \<in> set \<Gamma>') = (atm_of (fst x) \<prec>\<^sub>t atm_of K \<and> x \<in> set \<Gamma>)"
      unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
      unfolding mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
      by auto

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some (eres D E))"
    proof (rule ord_res_6.resolution_pos)
      show "\<not> dom \<M> \<TTurnstile> E"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> E\<close>] .
    next
      show "ord_res.is_maximal_lit L E"
        using step_hyps by argo
    next
      show "is_neg L"
        using step_hyps by argo
    next
      show "\<M> (atm_of L) = Some D"
        by (metis literal.collapse(2) match_hyps(5) step_hyps(5) step_hyps(6) uminus_Neg)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
        using step_hyps by argo
    next
      show "eres D E \<noteq> {#}"
        using step_hyps by argo
    next
      show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}"
        ..
    next
      show "ord_res.is_maximal_lit K (eres D E)"
        using step_hyps by argo
    next
      show "is_pos K"
        using step_hyps by argo
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some E\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some (eres D E))"
        using invars_6 unfolding \<open>\<C> = Some E\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some (eres D E))\<close> .
    next
      show "\<forall>A C. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C) =
        (map_of \<Gamma>' (Pos A) = Some (Some C))"
      proof (intro allI)
        fix A :: "'f gterm" and C :: "'f gclause"
        show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
        proof (cases "A \<in> dom \<M> \<and> A \<prec>\<^sub>t atm_of K")
          case True
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> \<M> A = Some C"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)"
            using match_hyps(3-) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
          proof -
            have "Pos A \<in> fst ` set \<Gamma>"
              using True 
              by (metis domIff map_of_eq_None_iff match_hyps(5) not_None_eq)

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma>"
              by fastforce

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma> \<and> (Pos A, \<C>) \<in> set \<Gamma>'"
              using True unfolding mem_set_\<Gamma>'_iff prod.sel literal.sel by metis

            moreover have "distinct (map fst \<Gamma>')"
              using \<Gamma>_distinct_atoms
            proof (rule distinct_suffix)
              show "suffix (map fst \<Gamma>') (map fst \<Gamma>)"
                using map_mono_suffix step_hyps(9) suffix_dropWhile by blast
            qed

            ultimately have "map_of \<Gamma> (Pos A) = map_of \<Gamma>' (Pos A)"
              using \<Gamma>_distinct_atoms by (auto dest: map_of_is_SomeI)

            thus ?thesis
              by argo
          qed

          finally show ?thesis .
        next
          case False
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False unfolding restrict_map_def by auto

          moreover have "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
            using False unfolding de_Morgan_conj
          proof (elim disjE)
            assume "A \<notin> dom \<M>"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>"
              using match_hyps(5)
              by (metis (no_types, opaque_lifting) domIff fst_eqD invars_7 is_pos_def map_of_SomeD
                  not_None_eq snd_conv weak_map_of_SomeI)

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          next
            assume "\<not> A \<prec>\<^sub>t atm_of K"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          qed

          ultimately show ?thesis
            by simp
        qed
      qed
    next
      show "\<forall>A. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
        (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
      proof (intro allI)
        fix A :: "'f gterm"
        show "(restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
          (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        proof (cases "A \<prec>\<^sub>t atm_of K")
          case True

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None \<longleftrightarrow> \<M> A = None"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using match_hyps(6) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using True mem_set_\<Gamma>'_iff
            by (metis eq_fst_iff literal.sel(2) map_of_SomeD not_None_eq weak_map_of_SomeI)

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>'"
            using True mem_set_\<Gamma>'_iff
            by (smt (verit, best) fset_trail_atms image_iff)

          finally show ?thesis .
        next
          case False

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False by simp

          moreover have "A |\<notin>| trail_atms \<Gamma>'"
            using False mem_set_\<Gamma>'_iff
            by (smt (verit, ccfv_threshold) fset_trail_atms image_iff)

          ultimately show ?thesis
            by metis
        qed
      qed
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution_neg E L D U\<^sub>e\<^sub>r' \<Gamma>' K C)
    
    define S6' where
      "S6' = (N, U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some C)"

    define i' where
      "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"

    have mem_set_\<Gamma>'_iff: "\<And>x. (x \<in> set \<Gamma>') = (atm_of (fst x) \<prec>\<^sub>t atm_of K \<and> x \<in> set \<Gamma>)"
      unfolding \<open>\<Gamma>' = dropWhile (\<lambda>Ln. atm_of K \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>\<close>
      unfolding mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone[OF \<Gamma>_sorted mono_atms_lt]
      by auto

    have step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some C)"
    proof (rule ord_res_6.resolution_neg)
      show "\<not> dom \<M> \<TTurnstile> E"
        using clause_false_wrt_model_if_false_wrt_\<Gamma>[OF \<open>trail_false_cls \<Gamma> E\<close>] .
    next
      show "ord_res.is_maximal_lit L E"
        using step_hyps by argo
    next
      show "is_neg L"
        using step_hyps by argo
    next
      show "\<M> (atm_of L) = Some D"
        by (metis literal.collapse(2) match_hyps(5) step_hyps(5) step_hyps(6) uminus_Neg)
    next
      show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
        using step_hyps by argo
    next
      show "eres D E \<noteq> {#}"
        using step_hyps by argo
    next
      show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}"
        ..
    next
      show "ord_res.is_maximal_lit K (eres D E)"
        using step_hyps by argo
    next
      show "is_neg K"
        using step_hyps by argo
    next
      show "\<M> (atm_of K) = Some C"
        using match_hyps(3-)
        by (metis (mono_tags, lifting) step_hyps(11) step_hyps(12) uminus_literal_def)
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 S6'"
      using S6_def \<open>\<C> = Some E\<close> S6'_def ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding S6'_def \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K}, Some C)"
        using invars_6 unfolding \<open>\<C> = Some E\<close>
        using ord_res_6_preserves_invars[OF step6] by argo
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)"
        using invars_s7' unfolding \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>', Some C)\<close> .
    next
      show "\<forall>A C. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C) =
        (map_of \<Gamma>' (Pos A) = Some (Some C))"
      proof (intro allI)
        fix A :: "'f gterm" and C :: "'f gclause"
        show "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
        proof (cases "A \<in> dom \<M> \<and> A \<prec>\<^sub>t atm_of K")
          case True
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = Some C \<longleftrightarrow> \<M> A = Some C"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)"
            using match_hyps(3-) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Pos A) = Some (Some C)"
          proof -
            have "Pos A \<in> fst ` set \<Gamma>"
              using True 
              by (metis domIff map_of_eq_None_iff match_hyps(5) not_None_eq)

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma>"
              by fastforce

            hence "\<exists>\<C>. (Pos A, \<C>) \<in> set \<Gamma> \<and> (Pos A, \<C>) \<in> set \<Gamma>'"
              using True unfolding mem_set_\<Gamma>'_iff prod.sel literal.sel by metis

            moreover have "distinct (map fst \<Gamma>')"
              using \<Gamma>_distinct_atoms
            proof (rule distinct_suffix)
              show "suffix (map fst \<Gamma>') (map fst \<Gamma>)"
                using map_mono_suffix step_hyps(9) suffix_dropWhile by blast
            qed

            ultimately have "map_of \<Gamma> (Pos A) = map_of \<Gamma>' (Pos A)"
              using \<Gamma>_distinct_atoms by (auto dest: map_of_is_SomeI)

            thus ?thesis
              by argo
          qed

          finally show ?thesis .
        next
          case False
          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False unfolding restrict_map_def by auto

          moreover have "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
            using False unfolding de_Morgan_conj
          proof (elim disjE)
            assume "A \<notin> dom \<M>"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>"
              using match_hyps(5)
              by (metis (no_types, opaque_lifting) domIff fst_eqD invars_7 is_pos_def map_of_SomeD
                  not_None_eq snd_conv weak_map_of_SomeI)

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          next
            assume "\<not> A \<prec>\<^sub>t atm_of K"

            hence "\<And>\<C>. (Pos A, \<C>) \<notin> set \<Gamma>'"
              unfolding mem_set_\<Gamma>'_iff by simp

            then show "map_of \<Gamma>' (Pos A) \<noteq> Some (Some C)"
              by (meson map_of_SomeD)
          qed

          ultimately show ?thesis
            by simp
        qed
      qed
    next
      show "\<forall>A. (restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
        (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
      proof (intro allI)
        fix A :: "'f gterm"
        show "(restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None) =
          (map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>')"
        proof (cases "A \<prec>\<^sub>t atm_of K")
          case True

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None \<longleftrightarrow> \<M> A = None"
            using True by simp

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma> (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using match_hyps(6) by metis

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>"
            using True mem_set_\<Gamma>'_iff
            by (metis eq_fst_iff literal.sel(2) map_of_SomeD not_None_eq weak_map_of_SomeI)

          also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Neg A) \<noteq> None \<or> A |\<notin>| trail_atms \<Gamma>'"
            using True mem_set_\<Gamma>'_iff
            by (smt (verit, best) fset_trail_atms image_iff)

          finally show ?thesis .
        next
          case False

          have "restrict_map \<M> {A. A \<prec>\<^sub>t atm_of K} A = None"
            using False by simp

          moreover have "A |\<notin>| trail_atms \<Gamma>'"
            using False mem_set_\<Gamma>'_iff
            by (smt (verit, ccfv_threshold) fset_trail_atms image_iff)

          ultimately show ?thesis
            by metis
        qed
      qed
    next
      show "i' = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r') |-| trail_atms \<Gamma>'"
        using i'_def .
    qed

    ultimately show ?thesis
      by metis
  qed
qed

theorem bisimulation_ord_res_6_ord_res_7:
  defines "match \<equiv> ord_res_6_matches_ord_res_7"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm literal \<times> 'f gclause option) list \<times> 'f gclause option \<Rightarrow> bool)
    ORDER.
    bisimulation ord_res_6_step (constant_context ord_res_7) ord_res_6_final ord_res_7_final
      ORDER MATCH"
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_6_step"
    using right_unique_ord_res_6_step .
next
  show "right_unique (constant_context ord_res_7)"
    using right_unique_constant_context right_unique_ord_res_7 by metis
next
  show "\<forall>S. ord_res_6_final S \<longrightarrow> (\<nexists>S'. ord_res_6_step S S')"
    by (metis finished_def ord_res_6_semantics.final_finished)
next
  show "\<forall>S. ord_res_7_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_7 S S')"
    by (metis finished_def ord_res_7_semantics.final_finished)
next
  show "\<forall>i S6 S7. match i S6 S7 \<longrightarrow> ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
    unfolding match_def
    using ord_res_6_final_iff_ord_res_7_final by metis
next
  show "\<forall>i S6 S7. match i S6 S7 \<longrightarrow>
       safe_state ord_res_6_step ord_res_6_final S6 \<and>
       safe_state (constant_context ord_res_7) ord_res_7_final S7"
  proof (intro allI impI conjI)
    fix i S6 S7
    assume "match i S6 S7"
    show "safe_state ord_res_6_step ord_res_6_final S6"
      using \<open>match i S6 S7\<close>[unfolded match_def]
      using ord_res_6_safe_state_if_invars
      using ord_res_6_matches_ord_res_7.simps by auto

    show "safe_state (constant_context ord_res_7) ord_res_7_final S7"
      using \<open>match i S6 S7\<close>[unfolded match_def]
      using ord_res_7_safe_state_if_invars
      using ord_res_6_matches_ord_res_7.simps by auto
  qed
next
  show "wfp (|\<subset>|)"
    using wfP_pfsubset .
next
  show "\<forall>i S6 S7 S7'. match i S6 S7 \<longrightarrow> constant_context ord_res_7 S7 S7' \<longrightarrow>
    (\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> match i' S6' S7') \<or>
    (\<exists>i'. match i' S6 S7' \<and> i' |\<subset>| i)"
    unfolding match_def
    using backward_simulation_between_6_and_7 by metis
qed


section \<open>ORD-RES-8 (atom-guided trail construction)\<close>

thm ord_res_7.intros


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

thm ord_res_7_final.model_found

inductive ord_res_8_final where
  model_found: "
    \<not> (\<exists>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>) \<Longrightarrow>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<Longrightarrow>
    ord_res_8_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" |

  contradiction_found: "
    {#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<Longrightarrow>
    ord_res_8_final (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"

interpretation ord_res_8_semantics: semantics where
  step = "constant_context ord_res_8" and
  final = ord_res_8_final
proof unfold_locales
  fix S :: "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
    ('f gterm literal \<times> 'f gterm literal multiset option) list"

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
         (* "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> trail_true_cls \<Gamma> C" and *)
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
        by (metis trail_defined_lit_iff_true_or_false trail_false_cls_def
            trail_false_cls_iff_not_trail_interp_entails trail_interp_cls_if_trail_true)
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

lemma rtranclp_ord_res_8_preserves_ord_res_8_invars:
  assumes
    step: "(ord_res_8 N)\<^sup>*\<^sup>* s s'" and
    invars: "ord_res_8_invars N s"
  shows "ord_res_8_invars N s'"
  using step invars ord_res_8_preserves_invars
  by (smt (verit, del_insts) rtranclp_induct)

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
  unfolding safe_state_def
proof (intro allI impI)
  fix S'
  assume "ord_res_8_semantics.eval (N, s) S'"
  then obtain s' where "S' = (N, s')" and "(ord_res_8 N)\<^sup>*\<^sup>* s s'"
  proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
    case base
    thus ?case by simp
  next
    case (step z)
    thus ?case
      by (smt (verit, ccfv_SIG) converse_rtranclp_into_rtranclp constant_context.cases prod.inject)
  qed
  hence "ord_res_8_invars N s'"
    using invars by (metis rtranclp_ord_res_8_preserves_ord_res_8_invars)
  hence "\<not> ord_res_8_final (N, s') \<Longrightarrow> \<exists>s''. ord_res_8 N s' s''"
    using ex_ord_res_8_if_not_final[of N s'] by argo
  hence "\<not> ord_res_8_final S' \<Longrightarrow> \<exists>S''. constant_context ord_res_8 S' S''"
    unfolding \<open>S' = (N, s')\<close> using constant_context.intros by metis
  thus "ord_res_8_final S' \<or> Ex (constant_context ord_res_8 S')"
    by argo
qed

definition trail_is_least_false_clause where
  "trail_is_least_false_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C|} C"

definition trail_is_least_propagating_clause where
  "trail_is_least_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      \<exists>L. clause_could_propagate \<Gamma> C L|} C"

definition is_least_false_or_propagating_clause where
  "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      trail_false_cls \<Gamma> C|} C \<or>
    \<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C) \<and>
      linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        \<exists>L. clause_could_propagate \<Gamma> C L|} C"

lemma Uniq_is_least_false_or_propagating_clause:
  "\<exists>\<^sub>\<le>\<^sub>1C. is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
  unfolding is_least_false_or_propagating_clause_def
  by (smt (verit) Uniq_def linorder_cls.Uniq_is_least_in_fset linorder_cls.is_least_in_ffilter_iff)

inductive ord_res_7_matches_ord_res_8 ::
  "'f gterm fset \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gliteral \<times> 'f gclause option) list \<times> 'f gclause option \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
      ('f gliteral \<times> 'f gclause option) list \<Rightarrow> bool" where
  "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) \<Longrightarrow>
    ord_res_8_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) \<Longrightarrow>
    (\<forall>C. \<C> = Some C \<longleftrightarrow> is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C) \<Longrightarrow>
    i = atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r) - trail_atms \<Gamma> \<Longrightarrow>
    ord_res_7_matches_ord_res_8 i (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>) (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"

lemma linorder_cls_is_least_in_fset_swap_predicate:
  assumes
    x_least: "linorder_cls.is_least_in_fset {|x |\<in>| X. P x|} y" and
    same_on_prefix: "\<And>x. x |\<in>| X \<Longrightarrow> x \<preceq>\<^sub>c y \<Longrightarrow> P x \<longleftrightarrow> Q x"
  shows "linorder_cls.is_least_in_fset {|x |\<in>| X. Q x|} y"
  unfolding linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  have "y |\<in>| X" and "P y" and ball_x_lt: "\<forall>z |\<in>| X. z \<noteq> y \<longrightarrow> P z \<longrightarrow> y \<prec>\<^sub>c z"
    using x_least unfolding linorder_cls.is_least_in_ffilter_iff by argo+

  show "y |\<in>| X"
    using \<open>y |\<in>| X\<close> .

  show "Q y"
    using same_on_prefix[of y] \<open>y |\<in>| X\<close> \<open>P y\<close> linorder_cls.reflp_on_le[THEN reflp_onD] by metis

  fix z :: "'f gterm literal multiset"
  assume "z |\<in>| X" and "z \<noteq> y" and "Q z"
  then show "y \<prec>\<^sub>c z"
    using ball_x_lt[rule_format, of z]
    using same_on_prefix[of z]
    by (metis linorder_cls.le_less_linear)
qed

lemma ord_res_7_final_iff_ord_res_8_final:
  fixes i S7 S8
  assumes match: "ord_res_7_matches_ord_res_8 i S7 S8"
  shows "ord_res_7_final S7 \<longleftrightarrow> ord_res_8_final S8"
  using match
proof (cases i S7 S8 rule: ord_res_7_matches_ord_res_8.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<Gamma> \<C>)

  note invars7 = \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>[unfolded ord_res_7_invars_def,
      rule_format, OF refl]

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using invars7 by (metis trail_consistent_if_sorted_wrt_atoms)

  show "ord_res_7_final S7 \<longleftrightarrow> ord_res_8_final S8"
  proof (rule iffI)
    assume "ord_res_7_final S7"
    thus "ord_res_8_final S8"
      unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)" rule: ord_res_7_final.cases)
      case model_found
      show "ord_res_8_final S8"
        unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      proof (rule ord_res_8_final.model_found)
        have "\<nexists>C. is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
          using match_hyps model_found by simp
          

        have MAGIC: "\<forall>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r).
          (\<forall>D. \<C> = Some D \<longrightarrow> (\<exists>L. linorder_lit.is_maximal_in_mset D L \<and> A \<prec>\<^sub>t atm_of L)) \<longrightarrow>
          A |\<in>| trail_atms \<Gamma>"
          using invars7 match_hyps model_found
          sorry

        hence "\<forall>A |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<in>| trail_atms \<Gamma>"
          using model_found by simp

        thus "\<not> (\<exists>A|\<in>|atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r). A |\<notin>| trail_atms \<Gamma>)"
          by metis

        (* {
          fix C D K
          assume
            "\<C> = Some D" and
            C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            "C \<prec>\<^sub>c D" and
            C_max_lit: "ord_res.is_maximal_lit K C"

          have "trail_defined_cls \<Gamma> {#L \<in># C. L \<noteq> K#}"
            unfolding trail_defined_cls_def
          proof (intro ballI)
            fix L :: "'f gliteral"
            assume "L \<in># {#L \<in># C. L \<noteq> K#}"

            hence "L \<in># C" and "L \<noteq> K"
              by simp_all

            have "atm_of L |\<in>| trail_atms \<Gamma>"
            proof (intro MAGIC [rule_format])
              show "atm_of L |\<in>| atms_of_clss (N |\<union>| U\<^sub>e\<^sub>r)"
                using \<open>L \<in># C\<close> C_in by (metis atm_of_in_atms_of_clssI)
            next
              fix D' :: "'f gclause"
              assume "\<C> = Some D'"

              hence "D' = D"
                using \<open>\<C> = Some D\<close> by simp

              show "\<exists>La. ord_res.is_maximal_lit La D' \<and> atm_of L \<prec>\<^sub>t atm_of La"
                unfolding \<open>D' = D\<close>
                using C_max_lit sledgehammer
                sorry
            qed

            thus "trail_defined_lit \<Gamma> L"
              unfolding trail_defined_lit_iff_trail_defined_atm .
          qed
        } *)

      next
        have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_true_cls \<Gamma> C"
          using invars7 model_found by simp

        moreover have "\<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)" for C
          using not_trail_true_cls_and_trail_false_cls[OF \<Gamma>_consistent] .

        ultimately show "\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). trail_false_cls \<Gamma> C)"
          by metis
      qed
    next
      case contradiction_found
      show "ord_res_8_final S8"
        unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      proof (rule ord_res_8_final.contradiction_found)
        show "{#} |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars7 \<open>\<C> = Some {#}\<close> by metis
      qed
    qed
  next
    assume "ord_res_8_final S8"
    thus "ord_res_7_final S7"
      unfolding \<open>S8 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    proof (cases "(N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" rule: ord_res_8_final.cases)
      case model_found
      hence "\<forall>A |\<in>| atms_of_clss (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)). A |\<in>| trail_atms \<Gamma>"
        by simp
      hence "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A |\<in>| atms_of_cls C. A |\<in>| trail_atms \<Gamma>"
        by (metis atms_of_clss_finsert funionCI mk_disjoint_finsert)
      hence "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<forall>L \<in># C. atm_of L |\<in>| trail_atms \<Gamma>"
        by (meson atm_of_in_atms_of_clssI local.model_found(1))
      hence "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<forall>L \<in># C. trail_defined_lit \<Gamma> L"
        unfolding trail_defined_lit_iff_trail_defined_atm .

      have "\<not> trail_false_cls \<Gamma> x \<and> \<not> Ex (clause_could_propagate \<Gamma> x)"
        if x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for x
      proof (intro conjI)
        show "\<not> trail_false_cls \<Gamma> x"
          using model_found(2) x_in by metis

        show "\<not> Ex (clause_could_propagate \<Gamma> x)"
          unfolding clause_could_propagate_def
          unfolding not_ex de_Morgan_conj not_not
          using \<open>\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<forall>L \<in># C. trail_defined_lit \<Gamma> L\<close>
          using linorder_lit.is_maximal_in_mset_iff x_in by blast
      qed

      hence "\<nexists>C. is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
        unfolding is_least_false_or_propagating_clause_def
        using linorder_cls.is_least_in_ffilter_iff by simp

      hence "\<C> = None"
        using match_hyps by simp

      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.model_found by metis
    next
      case contradiction_found

      hence "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> {#}"
        unfolding is_least_false_or_propagating_clause_def
        by (simp add: linorder_cls.is_least_in_ffilter_iff ord_res.multp_if_all_left_smaller)

      hence "\<C> = Some {#}"
        using match_hyps by metis

      thus "ord_res_7_final S7"
        unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>, \<C>)\<close>
        using ord_res_7_final.contradiction_found by metis
    qed
  qed
qed


(* TODO: move *)
lemma fstrict_subset_iff_fset_strict_subset_fset:
  fixes \<X> \<Y> :: "_ fset"
  shows "\<X> |\<subset>| \<Y> \<longleftrightarrow> fset \<X> \<subset> fset \<Y>"
    by blast

lemma backward_simulation_between_6_and_7:
  fixes i S6 S7 S7'
  assumes match: "ord_res_6_matches_ord_res_7 i S6 S7" and step: "constant_context ord_res_7 S7 S7'"
  shows "(\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> ord_res_6_matches_ord_res_7 i' S6' S7') \<or>
    (\<exists>i'. ord_res_6_matches_ord_res_7 i' S6 S7' \<and> i' |\<subset>| i)"
  using match
proof (cases i S6 S7 rule: ord_res_6_matches_ord_res_7.cases)
  case match_hyps: (1 N U\<^sub>e\<^sub>r \<F> \<M> \<C> \<Gamma>)

  have \<Gamma>_consistent: "trail_consistent \<Gamma>"
    using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    by (metis ord_res_7_invars_def trail_is_consistent_def)

  have \<Gamma>_sorted: "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
    using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    by (simp add: ord_res_7_invars_def trail_is_sorted_def)

  have \<Gamma>_lower_set: "linorder_trm.is_lower_set (trail_atoms \<Gamma>) (atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r))"
    using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    by (simp add: ord_res_7_invars_def trail_is_lower_set_def)

  have "dom \<M> = trail_interp \<Gamma>"
  proof (rule dom_model_eq_trail_interp)
    show "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
      using match_hyps by argo
  next
    show "\<forall>Ln\<in>set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
      using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      by (simp add: ord_res_7_invars_def decided_literals_all_neg_def)
  qed

  obtain s7' where
    "S7' = (N, s7')" and
    step': "ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>) s7'"
    using step unfolding \<open>S7 = (N, U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
    by (auto elim: constant_context.cases)

  have C_not_entailed_if_could_propagate_and_trail_consistent:
    "\<not> trail_interp \<Gamma> \<TTurnstile> C"
    if C_could_propagate: "clause_could_propagate \<Gamma> C (Pos A)"
    for C :: "'f gclause" and A :: "'f gterm"
  proof -
    have "\<not> trail_defined_lit \<Gamma> (Pos A)" and
      "ord_res.is_maximal_lit (Pos A) C" and
      "trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}"
      using C_could_propagate by (simp_all add: clause_could_propagate_def)

    have "trail_consistent ((Neg A, None) # \<Gamma>)"
      using \<open>trail_consistent \<Gamma>\<close>
      by (metis \<open>\<not> trail_defined_lit \<Gamma> (Pos A)\<close> trail_consistent.Cons trail_defined_lit_def
          uminus_Neg uminus_Pos)

    moreover have "trail_false_cls ((Neg A, None) # \<Gamma>) C"
      using \<open>trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> Pos A#}\<close>
      unfolding trail_false_cls_def trail_false_lit_def
      by auto

    ultimately have "\<not> trail_interp ((Neg A, None) # \<Gamma>) \<TTurnstile> C"
      by (metis trail_defined_lit_iff_true_or_false trail_false_cls_def
          trail_false_cls_iff_not_trail_interp_entails)

    moreover have "trail_interp ((Neg A, None) # \<Gamma>) = trail_interp \<Gamma>"
      by (simp add: trail_interp_def)

    ultimately show "\<not> trail_interp \<Gamma> \<TTurnstile> C"
      by argo
  qed

  have \<C>_eq_Some_if: "\<C> = Some C"
    if
      no_false_clause: "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)" and
      A_least_undef_atom: "linorder_trm.is_least_in_set
        {A\<^sub>2 \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). \<forall>A\<^sub>1\<in>trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A" and
      C_least_propagating: "linorder_cls.is_least_in_fset
        {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A)|} C"
    for C :: "'f gclause" and A :: "'f gterm"
  proof -
    have "\<not> (\<exists>K. clause_could_propagate \<Gamma> B K)"
      if B_in: "B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "B \<prec>\<^sub>c C" for B :: "'f gclause"
      unfolding not_ex
    proof (intro allI notI)
      fix K assume "clause_could_propagate \<Gamma> B K"
      hence
        "\<not> trail_defined_lit \<Gamma> K" and
        K_max: "ord_res.is_maximal_lit K B" and
        "trail_false_cls \<Gamma> {#Ka \<in># B. Ka \<noteq> K#}"
        unfolding atomize_conj clause_could_propagate_def .

      have "atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
        using K_max
        by (metis B_in Un_iff atoms_of_clause_set_finsert atoms_of_clause_set_image_fset_iefac
            image_eqI linorder_lit.is_maximal_in_mset_iff mk_disjoint_finsert)

      moreover have "\<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t atm_of K"
      proof -
        have "atm_of K \<notin> trail_atoms \<Gamma>"
          using \<open>\<not> trail_defined_lit \<Gamma> K\<close>
          by (metis trail_atoms_def trail_defined_lit_iff)
        thus ?thesis
          using \<Gamma>_lower_set
          using \<open>atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)\<close>
          by (metis linorder_trm.antisym_conv3 linorder_trm.is_lower_set_iff)
      qed

      ultimately have "A \<preceq>\<^sub>t atm_of K"
        using A_least_undef_atom
        unfolding linorder_trm.is_least_in_set_iff
        by auto

      hence "Pos A \<preceq>\<^sub>l K"
        by (cases K) simp_all

      then show False
      proof (cases "K = Pos A")
        case True
        hence "C \<preceq>\<^sub>c B"
          using C_least_propagating[unfolded linorder_cls.is_least_in_ffilter_iff]
          using B_in \<open>clause_could_propagate \<Gamma> B K\<close>
          by force
        thus False
          using \<open>B \<prec>\<^sub>c C\<close> by order
      next
        case False
        hence "Pos A \<prec>\<^sub>l K"
          using \<open>Pos A \<preceq>\<^sub>l K\<close> by order
        then show ?thesis
          using B_in \<open>B \<prec>\<^sub>c C\<close> \<open>clause_could_propagate \<Gamma> B K\<close>
          using C_least_propagating[unfolded linorder_cls.is_least_in_ffilter_iff]
          by (meson linorder_cls.less_asym linorder_lit.multp_if_maximal_less_that_maximal
              clause_could_propagate_iff)
      qed
    qed

    hence "linorder_cls.is_least_in_fset
      {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). Ex (clause_could_propagate \<Gamma> C)|} C"
      using C_least_propagating
      unfolding linorder_cls.is_least_in_ffilter_iff
      by (metis linorder_cls.less_linear)

    hence "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> C"
      unfolding is_least_false_or_propagating_clause_def
      using no_false_clause by metis

    thus "\<C> = Some C"
      using match_hyps(6) by metis
  qed

  show ?thesis
    using step'
  proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<Gamma>)" s7' rule: ord_res_7.cases)
    case step_hyps: (decide_neg A \<Gamma>')

    have A_in: "A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)" and A_undef: "\<not> trail_defined_atm \<Gamma> A"
      unfolding atomize_conj
      using step_hyps(3)
      unfolding linorder_trm.is_least_in_set_iff trail_defined_atm_iff_mem_trail_atoms
      by blast

    have "A \<notin> trail_atoms \<Gamma>"
      using A_undef unfolding trail_defined_atm_def trail_atoms_def .

    have "\<C> \<noteq> None"
    proof (rule notI)
      assume "\<C> = None"

      hence "\<forall>A\<in>atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). trail_defined_atm \<Gamma> A"
        using match_hyps(8) by simp

      hence "trail_defined_atm \<Gamma> A"
        using A_in by metis

      thus False
        using A_undef by contradiction
    qed

    then obtain D :: "'f gclause" where "\<C> = Some D"
      by blast

    have D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using match_hyps(3) \<open>\<C> = Some D\<close>
      by (metis ord_res_5_invars_def next_clause_in_factorized_clause_def)

    hence "\<not> clause_could_propagate \<Gamma> D (Pos A)"
      using \<open>\<not> (\<exists>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma> C (Pos A))\<close> by metis

    have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> D"
      using match_hyps(6) \<open>\<C> = Some D\<close> by metis

    hence "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
      Ex (clause_could_propagate \<Gamma> C)|} D"
      unfolding is_least_false_or_propagating_clause_def linorder_cls.is_least_in_ffilter_iff
      using \<open>\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)\<close> by metis

    then obtain L where
      "clause_could_propagate \<Gamma> D L" and
      "\<forall>y|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> D \<longrightarrow> Ex (clause_could_propagate \<Gamma> y) \<longrightarrow> D \<prec>\<^sub>c y"
      unfolding linorder_cls.is_least_in_ffilter_iff by metis

    have
      "\<not> trail_defined_lit \<Gamma> L" and
      D_max_lit: "ord_res.is_maximal_lit L D" and
      "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> L#}"
      using \<open>clause_could_propagate \<Gamma> D L\<close>
      unfolding atomize_conj clause_could_propagate_def by metis

    have "L \<in># D"
      using D_max_lit unfolding linorder_lit.is_maximal_in_mset_iff by argo

    have "atm_of L \<notin> trail_atoms \<Gamma>"
      using \<open>\<not> trail_defined_lit \<Gamma> L\<close>
      by (metis trail_atoms_def trail_defined_lit_iff)

    have "atm_of L \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
      using D_max_lit D_in
      unfolding linorder_lit.is_maximal_in_mset_iff atoms_of_clause_set_def
      by blast

    hence "atm_of L \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
      by simp

    hence "A \<preceq>\<^sub>t atm_of L"
      using step_hyps(3)[unfolded linorder_trm.is_least_in_set_iff, simplified]
      by (metis \<Gamma>_lower_set \<open>atm_of L \<notin> trail_atoms \<Gamma>\<close> linorder_trm.antisym_conv3
          linorder_trm.dual_order.eq_iff linorder_trm.dual_order.strict_implies_order
          linorder_trm.is_lower_set_iff)

    have "L \<noteq> Pos A"
      using \<open>clause_could_propagate \<Gamma> D L\<close> \<open>\<not> clause_could_propagate \<Gamma> D (Pos A)\<close> by metis


    have False if "L \<noteq> Neg A"
      using that
        A_undef Neg_atm_of_iff[of L]
        \<open>A \<preceq>\<^sub>t atm_of L\<close>[unfolded reflclp_iff] \<open>L \<noteq> Pos A\<close> \<open>\<C> = Some D\<close>
        \<open>clause_could_propagate \<Gamma> D L\<close>[unfolded clause_could_propagate_def]
        literal.collapse(1)[of L] match_hyps(8)[rule_format, of A, OF A_in] option.inject[of D]
      by metis

    hence "L = Neg A"
      by argo

    have "A \<notin> dom \<M>"
      using match_hyps
      by (metis \<open>A \<notin> trail_atoms \<Gamma>\<close> domD image_eqI literal.sel(1) map_of_eq_None_iff
          option.distinct(1) trail_atoms_def)

    hence "dom \<M> \<TTurnstile> D"
      using \<open>L \<in># D\<close>[unfolded \<open>L = Neg A\<close>] by blast

    define \<C>' where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset
        (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"

    define i' where
      "i' = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"

    have "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
      unfolding \<C>'_def
      using ord_res_6.skip[OF \<open>dom \<M> \<TTurnstile> D\<close> refl, of N U\<^sub>e\<^sub>r \<F>] .

    have "ord_res_6_matches_ord_res_7 i' (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>') S7'"
      unfolding \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
    proof (intro ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')"
        sorry
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
        using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
        using ord_res_7_preserves_invars step' step_hyps(1) by metis
    next
      have "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps by argo

      moreover have "map_of \<Gamma>' (Pos x) = map_of \<Gamma> (Pos x)" for x
        unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp

      ultimately show "\<forall>x C. (\<M> x = Some C) = (map_of \<Gamma>' (Pos x) = Some (Some C))"
        by metis
    next
      show "\<forall>C. (\<C>' = Some C) = is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>' C"
        sorry
    next
      show "\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C>' = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> trail_true_cls \<Gamma>' C"
        sorry
    next
      show "\<forall>A\<in>atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>C. \<C>' = Some C \<longrightarrow> (\<exists>L. ord_res.is_maximal_lit L C \<and> A \<prec>\<^sub>t atm_of L)) \<longrightarrow> trail_defined_atm \<Gamma>' A"
        sorry
    next
      show "i' = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
        unfolding i'_def ..
    qed

    have "\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> ord_res_6_matches_ord_res_7 i' S6' S7'"
      unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
      sorry

    thus ?thesis
      by metis

    show ?thesis
    proof (cases "L = Neg A")
      case True
      \<comment> \<open>ORD-RES-6 is using @{thm [source] ord_res_6.skip}\<close>
    next
      case False
      \<comment> \<open>ORD-RES-6 is not doing anything\<close>

      define i' where
        "i' = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"

      have "ord_res_6_matches_ord_res_7 i' S6 S7'"
        unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
      proof (intro ord_res_6_matches_ord_res_7.intros ballI impI)
        show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
          using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> .
      next
        show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
          using ord_res_7_preserves_invars step' step_hyps(1) by blast
      next
        have "\<And>x. map_of \<Gamma>' (Pos x) = map_of \<Gamma> (Pos x)" for x
          unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close> by simp
        thus "\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma>' (Pos A) = Some (Some C))"
          using match_hyps by metis
      next
        have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>' D"
          using \<open>is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> D\<close>
          by (metis A_in A_undef False Neg_atm_of_iff \<open>A \<preceq>\<^sub>t atm_of L\<close> \<open>L \<noteq> Pos A\<close> \<open>\<C> = Some D\<close>
              \<open>clause_could_propagate \<Gamma> D L\<close> literal.collapse(1) match_hyps(8) option.inject
              reflclp_iff clause_could_propagate_def)
        thus "\<forall>C. (\<C> = Some C) = is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>' C"
          using \<open>\<C> = Some D\<close>
          by (metis Uniq_D Uniq_is_least_false_or_propagating_clause option.inject)
      next
        fix C
        assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D"

        hence "trail_true_cls \<Gamma> C"
          using match_hyps(7) by metis

        thus "trail_true_cls \<Gamma>' C"
          unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          by (auto simp: trail_true_cls_def trail_true_lit_def)
      next
        fix x
        assume
          "x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)" and
          "(\<forall>C. \<C> = Some C \<longrightarrow> (\<exists>L. ord_res.is_maximal_lit L C \<and> x \<prec>\<^sub>t atm_of L))"

        hence "trail_defined_atm \<Gamma> x"
          using match_hyps(8) by metis

        thus "trail_defined_atm \<Gamma>' x"
          unfolding \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          by (simp add: trail_defined_atm_def)
      next
        show "i' = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
          unfolding i'_def ..
      qed

      moreover have "i' |\<subset>| i"
      proof -
        have "trail_atoms \<Gamma>' = insert A (trail_atoms \<Gamma>)"
          using \<open>\<Gamma>' = (Neg A, None) # \<Gamma>\<close>
          by (simp add: trail_atoms_def)

        hence "atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r) - trail_atoms \<Gamma>' \<subset>
        atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r) - trail_atoms \<Gamma>"
          using \<open>A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>A \<notin> trail_atoms \<Gamma>\<close>
          by blast

        moreover have "finite (atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r) - trail_atoms \<Gamma>')"
          using finite_atoms_of_clause_set finite_Diff by metis

        moreover have "finite (atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r) - trail_atoms \<Gamma>)"
          using finite_atoms_of_clause_set finite_Diff by metis

        ultimately show ?thesis
          unfolding i'_def \<open>i = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
          unfolding measure_ord_res_7.simps
          unfolding fstrict_subset_iff_fset_strict_subset_fset
          by (simp add: fset.Abs_fset_inverse[simplified])
      qed

      ultimately show ?thesis
        by metis
    qed
  next
    case step_hyps: (propagate A C \<Gamma>')

    define \<M>' where
      "\<M>' = \<M>(A \<mapsto> C)"

    define \<C>' where
      "\<C>' = The_optional (linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"

    define s6' where
      "s6' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"

    have
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_could_propagate: "clause_could_propagate \<Gamma> C (Pos A)" and
      C_least: "\<forall>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        D \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> D (Pos A) \<longrightarrow> C \<prec>\<^sub>c D"
      using step_hyps(4) unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by metis
    
    have "\<C> = Some C"
      using \<C>_eq_Some_if[of A C] step_hyps(2,3,4) by metis

    have "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
      using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      using step'[unfolded \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>]
      using ord_res_7_preserves_invars by metis

    have "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s6'"
      unfolding s6'_def
    proof (rule ord_res_6.production)
      have "\<not> trail_interp \<Gamma> \<TTurnstile> C"
        using C_not_entailed_if_could_propagate_and_trail_consistent
        using C_could_propagate by metis

      thus "\<not> dom \<M> \<TTurnstile> C"
        unfolding \<open>dom \<M> = trail_interp \<Gamma>\<close> .
    next
      show "ord_res.is_maximal_lit (Pos A) C"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) C\<close> by blast
    next
      show "is_pos (Pos A)"
        by simp
    next
      show "ord_res.is_strictly_maximal_lit (Pos A) C"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) C\<close> .
    next
      show "\<M>' = \<M>(atm_of (Pos A) \<mapsto> C)"
        by (simp add: \<M>'_def)
    next
      show "\<C>' = The_optional (linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))))"
        by  (simp add: \<C>'_def)
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 (N, s6')"
      unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some C\<close>
      using ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7 (measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')) (N, s6') S7'"
      unfolding \<open>s6' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close> \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
    proof (intro ord_res_6_matches_ord_res_7.intros allI ballI impI)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>[unfolded \<open>\<C> = Some C\<close>]
        using \<open>ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s6'\<close>[unfolded s6'_def]
        using ord_res_6_preserves_invars by metis
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')"
        using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close> .
    next
      fix B D
      show "(\<M>' B = Some D) = (map_of \<Gamma>' (Pos B) = Some (Some D))"
      proof (cases "B = A")
        case True
        thus ?thesis
          by (simp add: \<open>\<M>' = \<M>(A \<mapsto> C)\<close> \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>)
      next
        case False
        thus ?thesis
          using match_hyps
          by (simp add: \<open>\<M>' = \<M>(A \<mapsto> C)\<close> \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>)
      qed
    next
      show "\<And>C. (\<C>' = Some C) = is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma>' C"
        sorry
    next
      fix B
      assume B_in: "B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and B_lt: "\<forall>D. \<C>' = Some D \<longrightarrow> B \<prec>\<^sub>c D"

      moreover have "B \<preceq>\<^sub>c C"
      proof (cases \<C>')
        case None
        hence "\<nexists>!x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
          using \<C>'_def by (metis None_eq_The_optionalD)
        hence "\<nexists>x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
          using linorder_cls.Uniq_is_least_in_fset by (meson Uniq_D)
        hence "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<not> (C \<prec>\<^sub>c x)"
          by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)
        hence "\<not> (C \<prec>\<^sub>c B)"
          using B_in by metis
        thus "B \<preceq>\<^sub>c C"
          by order
      next
        case (Some D)
        hence "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using \<C>'_def by (metis Some_eq_The_optionalD)
        moreover have "B \<prec>\<^sub>c D"
          using B_lt Some by metis
        ultimately show "B \<preceq>\<^sub>c C"
          by (metis B_in ffmember_filter linorder_cls.not_le_imp_less nbex_less_than_least_in_fset)
      qed

      moreover have "\<And>B. B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<Longrightarrow> B \<prec>\<^sub>c C \<Longrightarrow> trail_true_cls \<Gamma> B"
        using match_hyps \<open>\<C> = Some C\<close> by blast

      moreover have "\<And>B. trail_true_cls \<Gamma> B \<Longrightarrow> trail_true_cls \<Gamma>' B"
        unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>
        by (auto simp add: trail_true_cls_def trail_true_lit_def)

      moreover have "trail_true_cls \<Gamma>' C"
      proof -
        have "ord_res.is_maximal_lit (Pos A) C"
          using C_could_propagate[unfolded clause_could_propagate_def] by argo+

        hence "Pos A \<in># C"
          unfolding linorder_lit.is_maximal_in_mset_iff ..

        moreover have "trail_true_lit \<Gamma>' (Pos A)"
          unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>
          by (simp add: trail_true_lit_def)

        ultimately show ?thesis
          unfolding trail_true_cls_def by metis
      qed

      ultimately show "trail_true_cls \<Gamma>' B"
        by blast
    next
      fix x
      assume
        "x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)" and
        "\<forall>C. \<C>' = Some C \<longrightarrow> (\<exists>L. ord_res.is_maximal_lit L C \<and> x \<prec>\<^sub>t atm_of L)"

      thm match_hyps

      have "trail_defined_atm \<Gamma>' x \<longleftrightarrow> x = A \<or> trail_defined_atm \<Gamma> x"
        unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>
        by (simp add: trail_defined_atm_def)

      show "trail_defined_atm \<Gamma>' x"
      proof (cases \<C>')
        case None
        hence "\<nexists>!x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
          using \<C>'_def by (metis None_eq_The_optionalD)
        hence "\<nexists>x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
          using linorder_cls.Uniq_is_least_in_fset by (meson Uniq_D)
        hence "\<forall>B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<not> (C \<prec>\<^sub>c B)"
          by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)
        hence "\<forall>B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<forall>L. ord_res.is_maximal_lit L B \<longrightarrow> L \<preceq>\<^sub>l Pos A"
          by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.leI
              linorder_lit.multp_if_maximal_less_that_maximal step_hyps(5))

        moreover have "atm_of K \<preceq>\<^sub>t A"
          if "B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            ball_lt_Pos_A: "\<forall>L. ord_res.is_maximal_lit L B \<longrightarrow> L \<preceq>\<^sub>l Pos A" and
            "K \<in># B"
          for K B
        proof (cases "ord_res.is_maximal_lit K B")
          case True
          hence "K \<preceq>\<^sub>l (Pos A)"
            using ball_lt_Pos_A by metis
          thus "atm_of K \<preceq>\<^sub>t A"
            by (cases K) simp_all
        next
          case False
          moreover obtain L where "ord_res.is_maximal_lit L B"
            by (metis \<open>K \<in># B\<close> empty_iff linorder_lit.ex_maximal_in_mset set_mset_empty)
          ultimately have "K \<prec>\<^sub>l L"
            using \<open>K \<in># B\<close>
            by (metis linorder_lit.is_maximal_in_mset_iff linorder_lit.less_linear)
          moreover have "L \<preceq>\<^sub>l Pos A"
            using \<open>ord_res.is_maximal_lit L B\<close> ball_lt_Pos_A by metis
          ultimately have "K \<preceq>\<^sub>l Pos A"
            by order
          thus "atm_of K \<preceq>\<^sub>t A"
            by (cases K) simp_all
        qed

        ultimately have "\<forall>B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). \<forall>L \<in># B. atm_of L \<preceq>\<^sub>t A"
          by meson

        hence "\<forall>x \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)). x \<preceq>\<^sub>t A"
          unfolding atoms_of_clause_set_def by auto

        hence "\<forall>x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). x \<preceq>\<^sub>t A"
          by simp

        moreover have "linorder_trm.is_lower_set (trail_atoms \<Gamma>') (atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r))"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
          unfolding ord_res_7_invars_def trail_is_lower_set_def
          by metis

        moreover have "A \<in> trail_atoms \<Gamma>'"
          unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>
          by (simp add: trail_atoms_def)

        ultimately have "\<forall>x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). x \<in> trail_atoms \<Gamma>'"
          unfolding linorder_trm.is_lower_set_iff by blast

        hence "\<forall>x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). trail_defined_atm \<Gamma>' x"
          by (simp only: trail_defined_atm_iff_mem_trail_atoms)

        thus "trail_defined_atm \<Gamma>' x"
          using \<open>x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)\<close> by metis
      next
        case (Some D)
        hence "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using \<C>'_def by (metis Some_eq_The_optionalD)

        hence
          "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
          "C \<prec>\<^sub>c D" and
          "\<forall>y|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). y \<noteq> D \<longrightarrow> C \<prec>\<^sub>c y \<longrightarrow> D \<prec>\<^sub>c y"
          unfolding linorder_cls.is_least_in_ffilter_iff by argo+

        have "D \<noteq> {#}"
          using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
          using linorder_cls.is_least_in_fset_ffilterD(1) step_hyps(2) trail_false_cls_mempty
          by blast

        then obtain L where "ord_res.is_maximal_lit L D"
          using linorder_lit.ex_maximal_in_mset by metis

        hence "Pos A \<preceq>\<^sub>l L"
          using \<open>ord_res.is_maximal_lit L D\<close> \<open>C \<prec>\<^sub>c D\<close>
          using linorder_cls.order.strict_trans linorder_lit.leI
            linorder_lit.multp_if_maximal_less_that_maximal step_hyps(5) by blast

        hence "A \<preceq>\<^sub>t atm_of L"
          by (cases L) simp_all

        moreover have "linorder_trm.is_lower_set (trail_atoms \<Gamma>') (atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r))"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')\<close>
          unfolding ord_res_7_invars_def trail_is_lower_set_def
          by metis

        moreover have "A \<in> trail_atoms \<Gamma>'"
          unfolding \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close>
          by (simp add: trail_atoms_def)

        ultimately have
          "trail_atoms \<Gamma>' \<subseteq> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)" and
          "x \<prec>\<^sub>t A \<longrightarrow> x \<in> trail_atoms \<Gamma>'"
          unfolding linorder_trm.is_lower_set_iff
          using \<open>x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)\<close>
          by metis+

        (* have "x \<in> trail_atoms \<Gamma>' \<longleftrightarrow> x \<prec>\<^sub>t atm_of L"
        proof (rule iffI)
          assume "x \<in> trail_atoms \<Gamma>'"
          hence "x = A \<or> x \<in> trail_atoms \<Gamma>"
            unfolding trail_atoms_def \<open>\<Gamma>' = (Pos A, Some C) # \<Gamma>\<close> by simp
          hence "x \<preceq>\<^sub>t A"
            using step_hyps(3)
            unfolding linorder_trm.is_least_in_set_iff by auto
          hence "x \<preceq>\<^sub>t atm_of L"
            using \<open>A \<preceq>\<^sub>t atm_of L\<close> by order
          thus "x \<prec>\<^sub>t atm_of L"
            \<comment> \<open>This is not true if \<open>L\<close> is either
              \<^term>\<open>Pos A\<close> (with more duplicates than in \<open>C\<close>) or \<^term>\<open>Neg A\<close>.\<close>
            \<comment> \<open>When simulating, ORD-RES-6 may have to perform multiple skip in order to reach
              a \<open>\<C>'\<close> that matches the state in ORD-RES-7.\<close>
            sorry
        next
          assume "x \<prec>\<^sub>t atm_of L"
          hence "x \<preceq>\<^sub>t A"
            sorry
          then show "x \<in> trail_atoms \<Gamma>'"
            using \<open>A \<in> trail_atoms \<Gamma>'\<close> \<open>x \<prec>\<^sub>t A \<longrightarrow> x \<in> trail_atoms \<Gamma>'\<close> by blast
        qed

        hence "trail_defined_atm \<Gamma>' x \<longleftrightarrow> x \<prec>\<^sub>t atm_of L"
          unfolding trail_atoms_def trail_defined_atm_def by argo

        hence "trail_defined_atm \<Gamma>' x = (\<exists>L. ord_res.is_maximal_lit L D \<and> x \<prec>\<^sub>t atm_of L)"
          using \<open>ord_res.is_maximal_lit L D\<close>
          by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset) *)

        thus "trail_defined_atm \<Gamma>' x"
          (* using \<open>\<C>' = Some D\<close> by simp *)
          sorry
      qed
    next
      show "measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>') = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>')" ..
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (factorize A C \<F>')

    have
      C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      C_could_propagate: "clause_could_propagate \<Gamma> C (Pos A)" and
      C_least: "\<forall>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r).
        D \<noteq> C \<longrightarrow> clause_could_propagate \<Gamma> D (Pos A) \<longrightarrow> C \<prec>\<^sub>c D"
      using step_hyps(4) unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by metis

    have "Pos A \<in># C" and lit_le_Pos_A: "\<And>L. L \<in># C \<Longrightarrow> L \<preceq>\<^sub>l Pos A"
      unfolding atomize_conj atomize_imp atomize_all
      using C_could_propagate
      by (metis linorder_lit.dual_order.eq_iff linorder_lit.is_maximal_in_mset_iff linorder_lit.leI
          clause_could_propagate_iff)

    have C_lesser_lits_defined: "trail_defined_lit \<Gamma> L" if "L \<in># C" and "L \<noteq> Pos A" for L
    proof -
      have "\<not> Pos A \<prec>\<^sub>l L"
        using lit_le_Pos_A[OF \<open>L \<in># C\<close>] \<open>L \<noteq> Pos A\<close> by order

      hence "L \<prec>\<^sub>l Pos A"
        using \<open>L \<noteq> Pos A\<close> by order

      hence "atm_of L \<prec>\<^sub>t A"
        by (cases L) simp_all

      moreover have "atm_of L \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
        using C_in \<open>L \<in># C\<close>
        by (metis Un_iff atoms_of_clause_set_finsert atoms_of_clause_set_image_fset_iefac
            finsert_absorb image_eqI)

      ultimately have "atm_of L \<in> trail_atoms \<Gamma>"
        using step_hyps(3) \<Gamma>_lower_set
        unfolding linorder_trm.is_least_in_set_iff
        by (smt (verit, best) linorder_trm.is_lower_set_iff linorder_trm.not_less_iff_gr_or_eq
            mem_Collect_eq)

      hence "trail_defined_atm \<Gamma> (atm_of L)"
        by (simp add: trail_defined_atm_iff_mem_trail_atoms)

      then show ?thesis
        by (simp add: trail_defined_lit_iff_trail_defined_atm)
    qed

    have "\<not> trail_defined_lit \<Gamma> (Pos A)"
      by (metis (no_types, lifting) linorder_trm.is_least_in_set_iff linorder_trm.less_irrefl
          literal.sel(1) mem_Collect_eq step_hyps(3) trail_atoms_def trail_defined_lit_iff)

    hence "\<not> trail_defined_cls \<Gamma> C"
      using \<open>Pos A \<in># C\<close> trail_defined_cls_def by blast

    have "\<C> = Some C"
      using \<C>_eq_Some_if[of A C] step_hyps(2,3,4) by metis

    have "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
    proof (rule ord_res_6.factoring)
      have "\<not> trail_interp \<Gamma> \<TTurnstile> C"
        using C_not_entailed_if_could_propagate_and_trail_consistent
        using C_could_propagate by metis

      thus "\<not> dom \<M> \<TTurnstile> C"
        unfolding \<open>dom \<M> = trail_interp \<Gamma>\<close> .
    next
      show "ord_res.is_maximal_lit (Pos A) C"
        using C_could_propagate[unfolded clause_could_propagate_def] by argo
    next
      show "is_pos (Pos A)"
        by simp
    next
      show "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
        using \<open>\<not> ord_res.is_strictly_maximal_lit (Pos A) C\<close> .
    next
      show "\<F>' = finsert C \<F>"
        using \<open>\<F>' = finsert C \<F>\<close> .
    qed

    hence "ord_res_6_step\<^sup>+\<^sup>+ S6 (N, U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
      unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some C\<close>
      using ord_res_6_step.intros by blast

    moreover have "ord_res_6_matches_ord_res_7
      (measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)) (N, U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C)) S7'"
      unfolding \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)\<close>
    proof (rule ord_res_6_matches_ord_res_7.intros)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))"
        using \<open>\<C> = Some C\<close> \<open>ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))\<close>
          match_hyps(3) ord_res_6_preserves_invars by blast
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)"
        using match_hyps(4) ord_res_7_preserves_invars step' step_hyps(1) by blast
    next
      show "\<forall>A C. (\<M> A = Some C) \<longleftrightarrow> (map_of \<Gamma> (Pos A) = Some (Some C))"
        using match_hyps by argo
    next
      have "\<not> fBex (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>)"
        using step_hyps(2)
        by (smt (verit, ccfv_threshold) fimage_iff iefac_def set_mset_efac trail_false_cls_def)

      moreover have "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r).
        \<exists>L. clause_could_propagate \<Gamma> C L|} (efac C)"
        unfolding linorder_cls.is_least_in_ffilter_iff
      proof (intro conjI ballI impI)
        show "efac C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          by (metis \<open>\<C> = Some C\<close> \<open>ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>, Some (efac C))\<close>
              match_hyps(3) next_clause_in_factorized_clause_def ord_res_6_preserves_invars
              ord_res_5_invars_def)

        have "\<not> trail_defined_lit \<Gamma> (Pos A)"
          using \<open>\<not> trail_defined_lit \<Gamma> (Pos A)\<close> .

        moreover have "ord_res.is_maximal_lit (Pos A) (efac C)"
          by (metis \<open>Pos A \<in># C\<close> linorder_lit.is_maximal_in_mset_iff linorder_lit.leD lit_le_Pos_A
              set_mset_efac)

        moreover have "trail_false_cls \<Gamma> {#K \<in># efac C. K \<noteq> Pos A#}"
          using C_could_propagate clause_could_propagate_iff trail_false_cls_def by fastforce

        ultimately have "clause_could_propagate \<Gamma> (efac C) (Pos A)"
          unfolding clause_could_propagate_def by argo

        thus "Ex (clause_could_propagate \<Gamma> (efac C))"
          by metis

        fix D :: "'f gterm literal multiset"
        assume
          D_in: "D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
          D_neq: "D \<noteq> efac C" and
          D_propagating: "Ex (clause_could_propagate \<Gamma> D)"

        have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using D_in D_neq iefac_def step_hyps(6) by auto

        hence "C \<prec>\<^sub>c D" if "D \<noteq> C"
        proof -
          obtain K where "clause_could_propagate \<Gamma> D K"
            using D_propagating by metis

          hence
            K_undef: "\<not> trail_defined_lit \<Gamma> K" and
            K_max: "ord_res.is_maximal_lit K D" and
            "trail_false_cls \<Gamma> {#Ka \<in># D. Ka \<noteq> K#}"
            unfolding atomize_conj
            unfolding clause_could_propagate_def .

          have "atm_of K \<notin> trail_atoms \<Gamma>"
            using K_undef
            unfolding trail_defined_lit_iff_trail_defined_atm
            unfolding trail_defined_atm_def trail_atoms_def .

          moreover have "atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
            using K_max
            unfolding linorder_lit.is_maximal_in_mset_iff
            using \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
            by (metis (no_types, opaque_lifting) UnCI atoms_of_clause_set_finsert
                atoms_of_clause_set_image_fset_iefac imageI mk_disjoint_finsert)

          ultimately have "A \<preceq>\<^sub>t atm_of K"
            using step_hyps(3)
            unfolding linorder_trm.is_least_in_set_iff mem_Collect_eq
            by (smt (verit) \<Gamma>_lower_set linorder_trm.antisym_conv3 linorder_trm.is_lower_set_iff
                mem_Collect_eq reflclp_iff)

          hence "Pos A \<preceq>\<^sub>l K"
            by (metis Neg_atm_of_iff linorder_lit.leI linorder_trm.leD literal.collapse(1)
                ord_res.less_lit_simps(1) ord_res.less_lit_simps(4))

          thus "C \<prec>\<^sub>c D"
            using C_least[rule_format, OF \<open>D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>D \<noteq> C\<close>]
            by (metis C_could_propagate \<open>clause_could_propagate \<Gamma> D K\<close> clause_could_propagate_def
                linorder_lit.multp_if_maximal_less_that_maximal reflclp_iff)
        qed

        hence "C \<preceq>\<^sub>c D"
          by auto

        moreover have "efac C \<prec>\<^sub>c C"
        proof -
          have "ord_res.is_maximal_lit (Pos A) C"
            using C_could_propagate clause_could_propagate_iff by metis

          moreover have "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
            using step_hyps(5) .

          ultimately have "efac C \<noteq> C"
            by (metis ex1_efac_eq_factoring_chain ex_ground_factoringI)

          thus "efac C \<prec>\<^sub>c C"
            using efac_properties_if_not_ident by metis
        qed

        ultimately show "efac C \<prec>\<^sub>c D"
          by order
      qed

      ultimately have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F>' \<Gamma> (efac C)"
        unfolding is_least_false_or_propagating_clause_def by argo

      thus "\<forall>C'. (Some (efac C) = Some C') = is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F>' \<Gamma> C'"
        unfolding option.inject
        by (metis Uniq_D Uniq_is_least_false_or_propagating_clause)
    next
      have "\<forall>Ca|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). Ca \<prec>\<^sub>c efac C \<longrightarrow> trail_true_cls \<Gamma> Ca"
        by (metis \<open>\<C> = Some C\<close> efac_properties_if_not_ident(1) linorder_cls.dual_order.strict_trans
            match_hyps(7) option.inject)
      hence "\<forall>Ca|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). Ca \<prec>\<^sub>c efac C \<longrightarrow> trail_true_cls \<Gamma> Ca"
        using iefac_def step_hyps(6) by auto
      thus "\<forall>Ca|\<in>|iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. Some (efac C) = Some D \<longrightarrow> Ca \<prec>\<^sub>c D) \<longrightarrow>
        trail_true_cls \<Gamma> Ca"
        unfolding option.inject
        by blast
    next
      show "\<forall>A\<in>atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r).
        (\<forall>Ca. Some (efac C) = Some Ca \<longrightarrow> (\<exists>L. ord_res.is_maximal_lit L Ca \<and> A \<prec>\<^sub>t atm_of L)) \<longrightarrow>
        trail_defined_atm \<Gamma> A"
        unfolding option.inject
        by (metis \<open>\<C> = Some C\<close> ex1_efac_eq_factoring_chain match_hyps(8) option.inject
            ord_res.ground_factorings_preserves_maximal_literal)
    next
      show "measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>) = measure_ord_res_7 N (U\<^sub>e\<^sub>r, \<F>', \<Gamma>)" ..
    qed

    ultimately show ?thesis
      by metis
  next
    case step_hyps: (resolution E A D U\<^sub>e\<^sub>r' \<Gamma>')

    define \<M>' where
      "\<M>' = restrict_map \<M> {A. \<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> A \<prec>\<^sub>t atm_of L}"

    have
      E_in: "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      E_false: "trail_false_cls \<Gamma> E" and
      E_least_false: "\<forall>F |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). F \<noteq> E \<longrightarrow> trail_false_cls \<Gamma> F \<longrightarrow> E \<prec>\<^sub>c F"
      using step_hyps(2) unfolding atomize_conj linorder_cls.is_least_in_ffilter_iff by metis

    have "Pos A \<in> dom (map_of \<Gamma>)"
      using \<open>map_of \<Gamma> (Pos A) = Some (Some D)\<close> by blast

    hence "Pos A \<in> fst ` set \<Gamma>"
      unfolding dom_map_of_conv_image_fst .

    hence "A \<in> trail_atoms \<Gamma>"
      unfolding trail_atoms_def by force

    hence atoms_lt_A_in_\<Gamma>: "\<forall>x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r). x \<prec>\<^sub>t A \<longrightarrow> x \<in> trail_atoms \<Gamma>"
      using \<Gamma>_lower_set unfolding linorder_trm.is_lower_set_iff by metis

    have \<Gamma>'_eq_if_eres_empty: "\<Gamma>' = []" if "eres D E = {#}"
      unfolding step_hyps that
      unfolding dropWhile_eq_Nil_conv
    proof (intro ballI allI impI)
      fix Ln K
      assume "Ln \<in> set \<Gamma>" and "ord_res.is_maximal_lit K {#}"
      hence False
        using linorder_lit.is_maximal_in_mset_iff by simp
      thus "atm_of K \<preceq>\<^sub>t atm_of (fst Ln)" ..
    qed

    have \<Gamma>'_eq_if_eres_not_empty: "\<Gamma>' = dropWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"
      if "linorder_lit.is_maximal_in_mset (eres D E) L"
      for L
      unfolding step_hyps
      using that
      by (metis (no_types, opaque_lifting) linorder_cls.dual_order.strict_implies_not_eq
          linorder_lit.antisym_conv3 linorder_lit.multp_if_maximal_less_that_maximal)

    have mem_trail_atoms_\<Gamma>'_iff:
      "A \<in> trail_atoms \<Gamma>' \<longleftrightarrow> A \<prec>\<^sub>t atm_of L \<and> A \<in> trail_atoms \<Gamma>"
      if "linorder_lit.is_maximal_in_mset (eres D E) L" for A L
    proof -
      have "Ln \<in> set \<Gamma>' \<longleftrightarrow> \<not> atm_of L \<preceq>\<^sub>t atm_of (fst Ln) \<and> Ln \<in> set \<Gamma>" for Ln
        unfolding \<Gamma>'_eq_if_eres_not_empty[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
      proof (rule mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
          using \<Gamma>_sorted .
      next
        show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x))
                  (\<lambda>x y. y \<le> x) (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln))"
          apply (rule monotone_onI)
          by (meson le_boolI' linorder_trm.dual_order.order_iff_strict
              linorder_trm.le_less_trans)
      qed

      thus ?thesis
        unfolding trail_atoms_def by force
    qed

    have ball_\<Gamma>'_lt_atm_of_max_lit_in_eres:
      "\<forall>Ln \<in> set \<Gamma>'. atm_of (fst Ln) \<prec>\<^sub>t atm_of L"
      if "linorder_lit.is_maximal_in_mset (eres D E) L" for L
    proof -
      have "\<forall>Ln \<in> set \<Gamma>'. \<not> (atm_of L \<preceq>\<^sub>t atm_of (fst Ln))"
        unfolding \<Gamma>'_eq_if_eres_not_empty[OF that]
      proof (rule ball_set_dropWhile_if_sorted_wrt_and_monotone_on)
        have "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
          using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
          by (simp add: ord_res_7_invars_def trail_is_sorted_def sorted_wrt_map)

        thus "sorted_wrt (\<lambda>x y. fst y \<prec>\<^sub>l fst x) \<Gamma>"
        proof (rule sorted_wrt_mono_rel[rotated])
          show "\<And>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x) \<Longrightarrow> fst y \<prec>\<^sub>l fst x"
            by (metis (no_types, lifting) linorder_lit.antisym_conv3 linorder_trm.dual_order.asym
                literal.exhaust_sel ord_res.less_lit_simps(1) ord_res.less_lit_simps(3)
                ord_res.less_lit_simps(4))
        qed

        show "monotone_on (set \<Gamma>) (\<lambda>x y. fst y \<prec>\<^sub>l fst x) (\<ge>) (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln))"
        proof (rule monotone_onI)
          show "\<And>x y. fst y \<prec>\<^sub>l fst x \<Longrightarrow>
              (atm_of L \<preceq>\<^sub>t atm_of (fst y)) \<le> (atm_of L \<preceq>\<^sub>t atm_of (fst x))"
            by (metis (mono_tags, lifting) le_boolI' linorder_lit.dual_order.asym
                linorder_trm.dual_order.strict_trans1 linorder_trm.le_less_linear
                literal.exhaust_sel ord_res.less_lit_simps(1) ord_res.less_lit_simps(3)
                ord_res.less_lit_simps(4))
        qed
      qed

      thus ?thesis
        using linorder_trm.le_less_linear by metis
    qed

    have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r \<F> \<Gamma> E"
      unfolding is_least_false_or_propagating_clause_def
      using step_hyps by argo

    hence "\<C> = Some E"
      using match_hyps(6)[rule_format, of E] by metis

    have "\<not> dom \<M> \<TTurnstile> E"
      using \<open>dom \<M> = trail_interp \<Gamma>\<close>
      by (metis E_false \<Gamma>_consistent trail_defined_lit_iff_true_or_false trail_false_cls_def
          trail_false_cls_iff_not_trail_interp_entails)

    have "is_neg (Neg A)"
      by simp

    have "trail_false_lit \<Gamma> (Neg A)"
      using \<open>ord_res.is_maximal_lit (Neg A) E\<close> E_false
      by (metis linorder_lit.is_maximal_in_mset_iff trail_false_cls_def)

    hence "Pos A \<in> fst ` set \<Gamma>"
      unfolding trail_false_lit_def by simp

    hence "\<exists>D. (Pos A, Some D) \<in> set \<Gamma>"
      using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>
      by (force simp add: ord_res_7_invars_def decided_literals_all_neg_def)

    hence "\<exists>\<Gamma>\<^sub>0 D \<Gamma>\<^sub>1. \<Gamma> = \<Gamma>\<^sub>1 @ (Pos A, Some D) # \<Gamma>\<^sub>0"
      by (meson split_list)

    then obtain \<Gamma>\<^sub>0 where "\<exists>D. suffix ((Pos A, Some D) # \<Gamma>\<^sub>0) \<Gamma>"
      unfolding suffix_def by metis

    hence "\<exists>D. suffix ((Pos A, Some D) # \<Gamma>\<^sub>0) \<Gamma> \<and>
      trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, ((Pos A, Some D) # \<Gamma>\<^sub>0))"
      using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close>[unfolded ord_res_7_invars_def]
      using trail_annotations_invars_mono_wrt_trail_suffix by metis

    hence "\<exists>D'. suffix ((Pos A, Some D') # \<Gamma>\<^sub>0) \<Gamma> \<and>
      D' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r) \<and>
      ord_res.is_strictly_maximal_lit (Pos A) D' \<and>
      trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D'. K \<noteq> Pos A#} \<and>
      linorder_cls.is_least_in_fset
        {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma>\<^sub>0 C (Pos A)|} D' \<and>
      trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>0)"
      apply (elim exE conjE)
      apply (erule trail_annotations_invars.cases)
      by auto

    hence "suffix ((Pos A, Some D) # \<Gamma>\<^sub>0) \<Gamma>" and
      D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D. K \<noteq> Pos A#}" and
      "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>0)"
      unfolding atomize_conj
    proof (elim exE conjE, intro conjI)
      fix D' :: "'f gterm literal multiset"
      assume hyps:
        "suffix ((Pos A, Some D') # \<Gamma>\<^sub>0) \<Gamma>"
        "D' |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        "ord_res.is_strictly_maximal_lit (Pos A) D'"
        "trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D'. K \<noteq> Pos A#}"
        "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>0)" and
        "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma>\<^sub>0 C (Pos A)|} D'"

      obtain \<Gamma>\<^sub>1 where "\<Gamma> = \<Gamma>\<^sub>1 @ (Pos A, Some D') # \<Gamma>\<^sub>0"
        using \<open>suffix ((Pos A, Some D') # \<Gamma>\<^sub>0) \<Gamma>\<close>
        by (auto elim: suffixE)

      hence "map_of \<Gamma> = (map_of ((Pos A, Some D') # \<Gamma>\<^sub>0) ++ map_of \<Gamma>\<^sub>1)"
        by (metis map_of_append)

      moreover have "Pos A \<notin> dom (map_of \<Gamma>\<^sub>1)"
        using \<Gamma>_consistent[unfolded \<open>\<Gamma> = \<Gamma>\<^sub>1 @ (Pos A, Some D') # \<Gamma>\<^sub>0\<close>]
      proof (induction \<Gamma>\<^sub>1)
        case Nil
        show ?case
          by simp
      next
        case (Cons Ln \<Gamma>\<^sub>1)
        obtain L opt where "Ln = (L, opt)"
          by fastforce

        have "trail_consistent (Ln # \<Gamma>\<^sub>1 @ (Pos A, Some D') # \<Gamma>\<^sub>0)"
          using Cons.prems by simp

        hence
          L_undef: "\<not> trail_defined_lit (\<Gamma>\<^sub>1 @ (Pos A, Some D') # \<Gamma>\<^sub>0) L" and
          "trail_consistent (\<Gamma>\<^sub>1 @ (Pos A, Some D') # \<Gamma>\<^sub>0)"
          unfolding atomize_conj
          by (auto simp: \<open>Ln = (L, opt)\<close> elim: trail_consistent.cases)

        hence "Pos A \<notin> dom (map_of \<Gamma>\<^sub>1)"
          using Cons.IH by argo

        moreover have "L \<noteq> Pos A"
          using L_undef
          by (simp add: trail_defined_lit_def)

        ultimately show ?case
          unfolding \<open>Ln = (L, opt)\<close>
          by (simp add: domIff)
      qed

      ultimately have "map_of \<Gamma> (Pos A) = Some (Some D')"
        by (simp add: map_add_dom_app_simps)

      hence "D' = D"
        using step_hyps(4) by simp

      show "suffix ((Pos A, Some D) # \<Gamma>\<^sub>0) \<Gamma>"
        using hyps \<open>D' = D\<close> by argo

      show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using hyps \<open>D' = D\<close> by argo

      show "ord_res.is_strictly_maximal_lit (Pos A) D"
        using hyps \<open>D' = D\<close> by argo

      show "trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D. K \<noteq> Pos A#}"
        using hyps \<open>D' = D\<close> by argo

      show "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>\<^sub>0)"
        using hyps \<open>D' = D\<close> by argo
    qed

    have "trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> Pos A#}"
      using \<open>trail_false_cls \<Gamma>\<^sub>0 {#K \<in># D. K \<noteq> Pos A#}\<close> \<open>suffix ((Pos A, Some D) # \<Gamma>\<^sub>0) \<Gamma>\<close>
      by (meson suffix_ConsD trail_false_cls_if_trail_false_suffix)

    have "Pos A \<prec>\<^sub>l Neg A"
      by simp

    hence "D \<prec>\<^sub>c E"
      using \<open>ord_res.is_maximal_lit (Neg A) E\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
      by (metis linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
          linorder_lit.multp_if_maximal_less_that_maximal)

    have "eres D E \<noteq> E"
      using D_max_lit \<open>D \<prec>\<^sub>c E\<close> eres_ident_iff ex_ground_resolutionI ground_resolution_def
        step_hyps(3) by blast

    have "- Neg A \<notin># E"
      using \<open>trail_false_cls \<Gamma> E\<close> \<open>ord_res.is_maximal_lit (Neg A) E\<close>
      by (metis \<open>\<not> dom \<M> \<TTurnstile> E\<close> atm_of_uminus is_pos_def is_pos_neg_not_is_pos
          linorder_lit.is_maximal_in_mset_iff literal.sel(1) literal.sel(2) true_cls_def
          true_lit_simps(1) true_lit_simps(2))

    have "\<M> A = Some D"
      using match_hyps(5) step_hyps(4) by metis

    hence "\<M> (atm_of (Neg A)) = Some D"
      unfolding literal.sel .

    have \<M>'_eq_if_eres_not_mempty: "\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of L}"
      if L_max: "ord_res.is_maximal_lit L (eres D E)" for L
    proof -
      have pred_iff:
        "(\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> A \<prec>\<^sub>t atm_of L) \<longleftrightarrow> A \<prec>\<^sub>t atm_of L" for A
      proof (rule iffI)
        assume "\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> A \<prec>\<^sub>t atm_of L"
        then obtain K where "ord_res.is_maximal_lit K (eres D E)" and "A \<prec>\<^sub>t atm_of K"
          by metis
        thus "A \<prec>\<^sub>t atm_of L"
          using L_max by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      next
        assume "A \<prec>\<^sub>t atm_of L"
        show "\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> A \<prec>\<^sub>t atm_of L"
          using L_max \<open>A \<prec>\<^sub>t atm_of L\<close> by metis
      qed

      show ?thesis
        unfolding \<M>'_def pred_iff ..
    qed

    have "eres D E \<prec>\<^sub>c E"
      using \<open>eres D E \<noteq> E\<close> eres_le by blast

    have "trail_false_cls \<Gamma> (eres D E)"
    proof (cases "eres D E = {#}")
      case True
      thus ?thesis
        by simp
    next
      case False
      hence "\<forall>L \<in># eres D E. atm_of L \<prec>\<^sub>t A"
        using lit_in_eres_lt_greatest_lit_in_grestest_resolvant[
            OF \<open>eres D E \<noteq> E\<close> \<open>ord_res.is_maximal_lit (Neg A) E\<close> \<open>- Neg A \<notin># E\<close>]
        by auto

      hence "\<forall>L \<in># eres D E. L \<noteq> Pos A"
        by fastforce

      moreover have "\<forall>L \<in># eres D E. L \<in># D \<or> L \<in># E"
        using lit_in_one_of_resolvents_if_in_eres by metis

      ultimately show ?thesis
        using \<open>trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> Pos A#}\<close> \<open>trail_false_cls \<Gamma> E\<close>
        unfolding trail_false_cls_def by fastforce
    qed

    have "eres D E |\<notin>| N |\<union>| U\<^sub>e\<^sub>r"
    proof (rule notI)
      have "iefac \<F> (eres D E) \<preceq>\<^sub>c eres D E"
        using iefac_le by metis
      hence "iefac \<F> (eres D E) \<prec>\<^sub>c E"
        using \<open>eres D E \<prec>\<^sub>c E\<close> by order

      moreover assume "eres D E |\<in>| N |\<union>| U\<^sub>e\<^sub>r"

      ultimately have "trail_true_cls \<Gamma> (iefac \<F> (eres D E))"
        using \<open>\<C> = Some E\<close> match_hyps(7) by blast

      hence "trail_true_cls \<Gamma> (eres D E)"
        using trail_false_cls_ignores_duplicates by (metis iefac_def set_mset_efac)

      thus False
        using \<Gamma>_consistent \<open>trail_false_cls \<Gamma> (eres D E)\<close>
        by (metis not_trail_true_cls_and_trail_false_cls)
    qed

    moreover have "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r"
      using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close>
      by (simp add: ord_res_5_invars_def implicitly_factorized_clauses_subset_def)

    ultimately have "eres D E |\<notin>| \<F>"
      by blast

    hence "iefac \<F> (eres D E) = eres D E"
      by (simp add: iefac_def)

    hence "iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
      by (simp add: \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)

    have trail_false_lit_in_eres: "trail_false_lit \<Gamma>' x"
      if "ord_res.is_maximal_lit L (eres D E)" and "x \<in># eres D E" and "atm_of x \<noteq> atm_of L"
      for x L
    proof -
      have "atm_of x \<prec>\<^sub>t A"
        using \<open>eres D E \<noteq> E\<close> \<open>ord_res.is_maximal_lit (Neg A) E\<close> \<open>- Neg A \<notin># E\<close>
          \<open>x \<in># eres D E\<close>
        by (metis lit_in_eres_lt_greatest_lit_in_grestest_resolvant literal.sel(2))

      hence "x \<prec>\<^sub>l Pos A"
        by (metis literal.exhaust_sel ord_res.less_lit_simps(1) ord_res.less_lit_simps(4))

      hence "trail_false_lit \<Gamma> x"
        using E_false \<open>trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> Pos A#}\<close>
          linorder_lit.order.strict_implies_not_eq lit_in_one_of_resolvents_if_in_eres
          that(2) trail_false_cls_def trail_false_cls_filter_mset_iff
        by blast

      have "Ln \<in> set \<Gamma>' \<longleftrightarrow> \<not> atm_of L \<preceq>\<^sub>t atm_of (fst Ln) \<and> Ln \<in> set \<Gamma>" for Ln
        unfolding \<Gamma>'_eq_if_eres_not_empty[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
      proof (rule mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone)
        show "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
          using \<Gamma>_sorted .
      next
        show "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x))
                  (\<lambda>x y. y \<le> x) (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln))"
          apply (rule monotone_onI)
          by (meson le_boolI' linorder_trm.dual_order.order_iff_strict
              linorder_trm.le_less_trans)
      qed

      hence "y \<in> fst ` set \<Gamma>' \<longleftrightarrow> atm_of y \<prec>\<^sub>t atm_of L \<and> y \<in> fst ` set \<Gamma>" for y
        by force

      moreover have "atm_of x \<prec>\<^sub>t atm_of L"
        using \<open>ord_res.is_maximal_lit L (eres D E)\<close> \<open>x \<in># eres D E\<close> \<open>atm_of x \<noteq> atm_of L\<close>
        by (metis (no_types, opaque_lifting) linorder_lit.is_maximal_in_mset_iff
            linorder_lit.neq_iff linorder_trm.not_less_iff_gr_or_eq literal.exhaust_sel
            ord_res.less_lit_simps(1) ord_res.less_lit_simps(3) ord_res.less_lit_simps(4))

      ultimately show ?thesis
        using \<open>trail_false_lit \<Gamma> x\<close>
        unfolding trail_false_lit_def
        by simp
    qed

    have not_bex_false_clause_in_\<Gamma>': "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>')"
      if "ord_res.is_maximal_lit L (eres D E)" for L
    proof (rule notI , elim bexE)
      fix C :: "'f gterm literal multiset"
      assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "trail_false_cls \<Gamma>' C"

      have "L \<in># eres D E"
        using linorder_lit.is_maximal_in_mset_iff that by blast

      have "suffix \<Gamma>' \<Gamma>"
        unfolding \<Gamma>'_eq_if_eres_not_empty[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
        using suffix_dropWhile .

      hence "trail_false_cls \<Gamma> C"
        using \<open>trail_false_cls \<Gamma>' C\<close> by (metis trail_false_cls_if_trail_false_suffix)

      moreover have "C \<prec>\<^sub>c E"
      proof -
        have "\<forall>K \<in># C. trail_false_lit \<Gamma>' K"
          using \<open>trail_false_cls \<Gamma>' C\<close> unfolding trail_false_cls_def by metis

        hence "\<forall>K \<in># C. trail_defined_lit \<Gamma>' K"
          using trail_defined_lit_iff_true_or_false by metis

        hence "\<forall>K \<in># C. trail_defined_atm \<Gamma>' (atm_of K)"
          using trail_defined_lit_iff_trail_defined_atm by metis

        hence "\<forall>K \<in># C. atm_of K \<in> trail_atoms \<Gamma>'"
          using trail_defined_atm_def trail_atoms_def by metis

        hence "\<forall>K\<in>#C. atm_of K \<prec>\<^sub>t atm_of L"
          using mem_trail_atoms_\<Gamma>'_iff[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] by metis

        moreover have "atm_of L \<prec>\<^sub>t A"
          by (metis \<open>- Neg A \<notin># E\<close> \<open>L \<in># eres D E\<close> \<open>eres D E \<noteq> E\<close>
              lit_in_eres_lt_greatest_lit_in_grestest_resolvant literal.sel(2) step_hyps(3))

        ultimately have "\<forall>K\<in>#C. atm_of K \<prec>\<^sub>t A"
          by auto

        thus "C \<prec>\<^sub>c E"
          using \<open>linorder_lit.is_maximal_in_mset E (Neg A)\<close>
          by (smt (verit) empty_iff linorder_lit.is_maximal_in_mset_iff linorder_lit.less_linear
              linorder_trm.dual_order.asym literal.exhaust_sel ord_res.less_lit_simps(3)
              ord_res.less_lit_simps(4) ord_res.multp_if_all_left_smaller set_mset_empty)
      qed

      ultimately show False
        using E_least_false \<open>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by auto
    qed

    have stronger_not_bex_false_clause_in_\<Gamma>':
      "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) (trail_false_cls \<Gamma>')"
      if "ord_res.is_maximal_lit L (eres D E)" for L
    proof -
      have "L \<in># eres D E"
        using \<open>ord_res.is_maximal_lit L (eres D E)\<close> unfolding linorder_lit.is_maximal_in_mset_iff
        by argo

      moreover have "\<not> trail_defined_lit \<Gamma>' L"
        unfolding trail_defined_lit_iff_trail_defined_atm
        unfolding trail_defined_atm_def
        unfolding trail_atoms_def[symmetric]
        unfolding mem_trail_atoms_\<Gamma>'_iff[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
        by simp

      ultimately have "\<not> trail_defined_cls \<Gamma>' (eres D E)"
        unfolding trail_defined_cls_def by metis

      hence "\<not> trail_false_cls \<Gamma>' (eres D E)"
        unfolding trail_false_cls_def trail_false_lit_def
          trail_defined_cls_def trail_defined_lit_def by metis

      moreover have "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) (trail_false_cls \<Gamma>')"
        using not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] .

      ultimately show "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) (trail_false_cls \<Gamma>')"
        unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
        by simp
    qed

    have mem_trail_atoms_\<Gamma>_if: "A \<in> trail_atoms \<Gamma>"
      if eres_max_lit: "ord_res.is_maximal_lit L (eres D E)" and
        A_in: "A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')" and
        "A \<prec>\<^sub>t atm_of L"
      for A L
    proof -
      have "atm_of L \<in> trail_atoms \<Gamma>"
        using eres_max_lit
        by (metis \<open>trail_false_cls \<Gamma> (eres D E)\<close>
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set linorder_lit.is_maximal_in_mset_iff
            trail_atoms_def trail_false_cls_def trail_false_lit_def)

      moreover have "A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
      proof -
        have "atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r') =
              atm_of ` set_mset (eres D E) \<union> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
          unfolding \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> atoms_of_clause_set_def by simp

        moreover have "atm_of ` set_mset (eres D E) \<subseteq> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
        proof (rule subsetI)
          fix x
          assume "x \<in> atm_of ` set_mset (eres D E)"
          then obtain K where "K \<in># eres D E" and "x = atm_of K"
            by blast

          have "K \<in># D \<or> K \<in># E"
            using \<open>K \<in># eres D E\<close> lit_in_one_of_resolvents_if_in_eres by metis

          hence "x \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
          proof (elim disjE)
            assume "K \<in># D"
            show "x \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
              unfolding atoms_of_clause_set_def
            proof (rule UN_I)
              show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
                using D_in .
            next
              show "x \<in> atm_of ` set_mset D"
                using \<open>x = atm_of K\<close> \<open>K \<in># D\<close> by simp
            qed
          next
            assume "K \<in># E"
            show "x \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
              unfolding atoms_of_clause_set_def
            proof (rule UN_I)
              show "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
                using E_in .
            next
              show "x \<in> atm_of ` set_mset E"
                using \<open>x = atm_of K\<close> \<open>K \<in># E\<close> by simp
            qed
          qed

          thus "x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
            by simp
        qed

        ultimately show ?thesis
          using A_in by auto
      qed

      ultimately show "A \<in> trail_atoms \<Gamma>"
        using \<Gamma>_lower_set[unfolded linorder_trm.is_lower_set_iff] \<open>A \<prec>\<^sub>t atm_of L\<close> by metis
    qed

    have "\<exists>C. ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C) \<and>
      is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C \<and>
      (\<forall>A. A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r') \<longrightarrow>
        (\<exists>L. ord_res.is_maximal_lit L C \<and> A \<prec>\<^sub>t atm_of L) \<longrightarrow>
        trail_defined_atm \<Gamma>' A) \<and>
      (\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). x \<prec>\<^sub>c C \<longrightarrow> trail_true_cls \<Gamma>' x)"
    proof (cases "eres D E = {#}")
      case True

      moreover have "\<M>' = (\<lambda>_. None)"
        unfolding \<M>'_def \<open>eres D E = {#}\<close>
        by (simp add: linorder_lit.is_maximal_in_mset_iff)

      ultimately have "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some {#})"
        using \<open>\<not> dom \<M> \<TTurnstile> E\<close> \<open>ord_res.is_maximal_lit (Neg A) E\<close> \<open>is_neg (Neg A)\<close>
          \<open>\<M> (atm_of (Neg A)) = Some D\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>
        using ord_res_6.resolution_bot
        by metis

      moreover have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' {#}"
        unfolding is_least_false_or_propagating_clause_def
      proof (rule disjI1)
        show "linorder_cls.is_least_in_fset
          (ffilter (trail_false_cls \<Gamma>') (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) {#}"
          unfolding linorder_cls.is_least_in_ffilter_iff
          using mempty_lesseq_cls
          by (auto simp: \<open>eres D E = {#}\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close>)
      qed

      moreover have "trail_defined_atm \<Gamma>' A"
        if A_in: "A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')" and
          ex_max_lit_gt_A: "\<exists>L. ord_res.is_maximal_lit L {#} \<and> A \<prec>\<^sub>t atm_of L"
        for A
        using ex_max_lit_gt_A unfolding linorder_lit.is_maximal_in_mset_iff by simp

      moreover have "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). x \<prec>\<^sub>c {#} \<longrightarrow> trail_true_cls \<Gamma>' x"
        by (metis linorder_cls.leD mempty_lesseq_cls)

      ultimately show ?thesis
        by metis
    next
      case False
      then obtain L where eres_max_lit: "ord_res.is_maximal_lit L (eres D E)"
        using linorder_lit.ex_maximal_in_mset by metis

      show ?thesis
      proof (cases L)
        case (Pos A\<^sub>L)
        hence "is_pos L"
          by simp

        have "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some (eres D E))"
          sketch (rule ord_res_6.resolution_pos)
        proof (rule ord_res_6.resolution_pos)
          show "\<not> dom \<M> \<TTurnstile> E"
            using \<open>\<not> dom \<M> \<TTurnstile> E\<close> .
        next
          show "ord_res.is_maximal_lit (Neg A) E"
            using \<open>ord_res.is_maximal_lit (Neg A) E\<close> .
        next
          show "is_neg (Neg A)"
            by simp
        next
          show "\<M> (atm_of (Neg A)) = Some D"
            using \<open>\<M> (atm_of (Neg A)) = Some D\<close> .
        next
          show "U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r"
            using \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> .
        next
          show "eres D E \<noteq> {#}"
            using \<open>eres D E \<noteq> {#}\<close> .
        next
          show "\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of L}"
            using eres_max_lit \<M>'_eq_if_eres_not_mempty by metis
        next
          show "ord_res.is_maximal_lit L (eres D E)"
            using \<open>ord_res.is_maximal_lit L (eres D E)\<close> .
        next
          show "is_pos L"
            unfolding \<open>L = Pos A\<^sub>L\<close> by simp
        qed

        moreover have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' (eres D E)"
          unfolding is_least_false_or_propagating_clause_def
        proof (intro disjI2 conjI)
          show "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) (trail_false_cls \<Gamma>')"
            using stronger_not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] .
        next
          show "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r').
          Ex (clause_could_propagate \<Gamma>' C)|} (eres D E)"
            unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
            unfolding linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI exI)
            show "eres D E |\<in>| finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
              by simp
          next
            show "clause_could_propagate \<Gamma>' (eres D E) L"
              unfolding clause_could_propagate_def
            proof (intro conjI)
              show "\<not> trail_defined_lit \<Gamma>' L"
                using \<open>ord_res.is_maximal_lit L (eres D E)\<close>
                by (simp add: ball_\<Gamma>'_lt_atm_of_max_lit_in_eres image_iff linorder_trm.neq_iff
                    trail_defined_lit_iff)
            next
              show "ord_res.is_maximal_lit L (eres D E)"
                using \<open>ord_res.is_maximal_lit L (eres D E)\<close> .
            next
              have "trail_false_lit \<Gamma>' x" if "x \<in># eres D E" and "x \<noteq> L" for x
              proof (rule trail_false_lit_in_eres[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close> \<open>x \<in># eres D E\<close>])
                show "atm_of x \<noteq> atm_of L"
                  using \<open>x \<noteq> L\<close> \<open>is_pos L\<close>
                  by (metis eres_max_lit linorder_lit.is_maximal_in_mset_iff
                      linorder_trm.dual_order.order_iff_strict literal.collapse(1)
                      literal.exhaust_sel ord_res.less_lit_simps(2) that(1))
              qed

              thus "trail_false_cls \<Gamma>' {#K \<in># eres D E. K \<noteq> L#}"
                by (simp add: trail_false_cls_def)
            qed
          next
            fix y
            assume
              "y |\<in>| finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))" and
              "y \<noteq> eres D E" and
              "Ex (clause_could_propagate \<Gamma>' y)"

            hence "y |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              by simp

            obtain K where
              "\<not> trail_defined_lit \<Gamma>' K" and
              "ord_res.is_maximal_lit K y" and
              "trail_false_cls \<Gamma>' {#a \<in># y. a \<noteq> K#}"
              using \<open>Ex (clause_could_propagate \<Gamma>' y)\<close>
              unfolding clause_could_propagate_def
              by metis

            show "eres D E \<prec>\<^sub>c y"
            proof (cases "L = K")
              case True
              hence "trail_false_cls \<Gamma> y"
                by (smt (verit, del_insts) eres_max_lit Uniq_D \<open>\<And>thesis. (\<And>K. \<lbrakk>\<not> trail_defined_lit \<Gamma>' K;
              ord_res.is_maximal_lit K y; trail_false_cls \<Gamma>' {#a \<in># y. a \<noteq> K#}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow>
              thesis\<close> \<open>ord_res.is_maximal_lit K y\<close> \<open>trail_false_cls \<Gamma> (eres D E)\<close>
                    linorder_lit.Uniq_is_maximal_in_mset linorder_lit.is_maximal_in_mset_iff
                    step_hyps(6) suffix_dropWhile trail_false_cls_def trail_false_cls_filter_mset_iff
                    trail_false_cls_if_trail_false_suffix)

              hence "E \<preceq>\<^sub>c y"
                using E_least_false \<open>y |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> by force

              thus ?thesis
                using \<open>eres D E \<prec>\<^sub>c E\<close> by order
            next
              case False

              have "atm_of K \<notin> trail_atoms \<Gamma>'"
                using \<open>\<not> trail_defined_lit \<Gamma>' K\<close>
                unfolding trail_defined_lit_iff_trail_defined_atm
                unfolding trail_defined_atm_def
                unfolding trail_atoms_def .

              hence "atm_of L \<preceq>\<^sub>t atm_of K \<or> atm_of K \<notin> trail_atoms \<Gamma>"
                unfolding mem_trail_atoms_\<Gamma>'_iff[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] by auto

              hence "L \<prec>\<^sub>l K"
              proof (elim disjE)
                assume "atm_of L \<preceq>\<^sub>t atm_of K"
                thus "L \<prec>\<^sub>l K"
                  using \<open>L \<noteq> K\<close> \<open>is_pos L\<close>
                  by (metis linorder_lit.linorder_cases linorder_trm.leD literal.collapse(1)
                      literal.exhaust_sel ord_res.less_lit_simps(1) ord_res.less_lit_simps(4))
              next
                assume "atm_of K \<notin> trail_atoms \<Gamma>"

                moreover have "atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
                proof -
                  have "K \<in># y"
                    using \<open>ord_res.is_maximal_lit K y\<close>
                    unfolding linorder_lit.is_maximal_in_mset_iff by argo

                  hence "atm_of K \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
                    unfolding atoms_of_clause_set_def
                    using \<open>y |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
                    by blast

                  thus ?thesis
                    by simp
                qed

                ultimately have "\<not> (atm_of K \<prec>\<^sub>t A)"
                  using \<Gamma>_lower_set[unfolded linorder_trm.is_lower_set_iff, THEN conjunct2,
                      rule_format, OF \<open>A \<in> trail_atoms \<Gamma>\<close> \<open>atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)\<close>]
                  by argo

                hence "A \<preceq>\<^sub>t atm_of K"
                  by order

                hence "Pos A \<preceq>\<^sub>l K"
                  by (cases K) simp_all

                moreover have "L \<prec>\<^sub>l Pos A"
                  by (metis eres_max_lit \<open>is_pos L\<close> \<open>- Neg A \<notin># E\<close> \<open>eres D E \<noteq> E\<close>
                      linorder_lit.is_maximal_in_mset_iff
                      lit_in_eres_lt_greatest_lit_in_grestest_resolvant literal.collapse(1)
                      literal.sel(2) ord_res.less_lit_simps(1) step_hyps(3))

                ultimately show "L \<prec>\<^sub>l K"
                  by order
              qed

              thus ?thesis
                using \<open>ord_res.is_maximal_lit L (eres D E)\<close> \<open>ord_res.is_maximal_lit K y\<close>
                using linorder_lit.multp_if_maximal_less_that_maximal by metis
            qed
          qed
        qed

        moreover have atom_defined_in_\<Gamma>': "trail_defined_atm \<Gamma>' A"
          if A_in: "A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')" and
            ex_max_lit_gt_A: "\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> A \<prec>\<^sub>t atm_of L"
          for A
        proof -
          have "A \<prec>\<^sub>t atm_of L"
            using ex_max_lit_gt_A \<open>ord_res.is_maximal_lit L (eres D E)\<close>
            by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

          moreover hence "A \<in> trail_atoms \<Gamma>"
            using mem_trail_atoms_\<Gamma>_if \<open>ord_res.is_maximal_lit L (eres D E)\<close> A_in by metis

          ultimately have "A \<in> trail_atoms \<Gamma>'"
            unfolding mem_trail_atoms_\<Gamma>'_iff[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] by argo

          thus ?thesis
            unfolding trail_atoms_def trail_defined_atm_def .
        qed

        moreover have "trail_true_cls \<Gamma>' x"
          if x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and "x \<prec>\<^sub>c eres D E" for x
        proof -
          have "\<not> trail_false_cls \<Gamma>' x"
            using stronger_not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] x_in
            by metis

          hence "x \<noteq> {#}"
            using trail_false_cls_mempty by metis

          then obtain K where x_max_lit: "linorder_lit.is_maximal_in_mset x K"
            using linorder_lit.ex_maximal_in_mset by metis

          hence "K \<preceq>\<^sub>l L"
            using \<open>x \<prec>\<^sub>c eres D E\<close> \<open>ord_res.is_maximal_lit L (eres D E)\<close>
            by (metis linorder_cls.less_asym linorder_lit.leI
                linorder_lit.multp_if_maximal_less_that_maximal)

          have "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r').
          Ex (clause_could_propagate \<Gamma>' C)|} (eres D E)"
            using \<open>is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' (eres D E)\<close>
            using stronger_not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
            by (metis is_least_false_or_propagating_clause_def linorder_cls.is_least_in_ffilter_iff)

          hence "\<not> clause_could_propagate \<Gamma>' x K"
            using \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')\<close> \<open>x \<prec>\<^sub>c eres D E\<close>
            unfolding linorder_cls.is_least_in_ffilter_iff
            by (metis linorder_cls.order.asym)

          hence FOO: "trail_defined_lit \<Gamma>' K \<or> \<not> trail_false_cls \<Gamma>' {#Ka \<in># x. Ka \<noteq> K#}"
            unfolding clause_could_propagate_def de_Morgan_conj not_not
            using x_max_lit by metis

          have "trail_defined_lit \<Gamma>' J"
            if "J \<in># x" and "J \<prec>\<^sub>l K" for J
            unfolding trail_defined_lit_iff_trail_defined_atm
          proof (rule atom_defined_in_\<Gamma>')
            have "atm_of J \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))"
              using \<open>J \<in># x\<close> x_in
              unfolding atoms_of_clause_set_def by blast
            thus "atm_of J \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')"
              by simp
          next
            have "J \<prec>\<^sub>l L"
              using \<open>J \<prec>\<^sub>l K\<close> \<open>K \<preceq>\<^sub>l L\<close> by order
            then show "\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> atm_of J \<prec>\<^sub>t atm_of L"
              using \<open>ord_res.is_maximal_lit L (eres D E)\<close> \<open>is_pos L\<close>
              by (metis literal.collapse(1) literal.exhaust_sel ord_res.less_lit_simps(1)
                  ord_res.less_lit_simps(4))
          qed

          hence "trail_defined_cls \<Gamma>' {#Ka \<in># x. Ka \<noteq> K#}"
            unfolding trail_defined_cls_def
            using linorder_lit.is_maximal_in_mset_iff linorder_lit.not_less_iff_gr_or_eq x_max_lit
            by fastforce

          thus ?thesis
            using \<open>\<not> trail_false_cls \<Gamma>' x\<close> FOO
            by (smt (verit, best) mem_Collect_eq set_mset_filter trail_defined_cls_def
                trail_defined_lit_iff_true_or_false trail_false_cls_def trail_true_cls_def)
        qed

        ultimately show ?thesis
          by metis
      next
        case (Neg A\<^sub>L)
        hence "is_neg L"
          by simp

        have "trail_false_lit \<Gamma> (Neg A\<^sub>L)"
          using E_false \<open>trail_false_cls \<Gamma> {#K \<in># D. K \<noteq> Pos A#}\<close>
          using \<open>eres D E \<noteq> {#}\<close> \<open>ord_res.is_maximal_lit L (eres D E)\<close>
          unfolding \<open>L = Neg A\<^sub>L\<close>
          by (metis linorder_lit.is_maximal_in_mset_iff lit_in_one_of_resolvents_if_in_eres
              literal.distinct(1) trail_false_cls_def trail_false_cls_filter_mset_iff)

        hence "Pos A\<^sub>L \<in> fst ` set \<Gamma>"
          unfolding trail_false_lit_def by simp

        moreover have "decided_literals_all_neg N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
          using match_hyps unfolding ord_res_7_invars_def by metis

        ultimately obtain C where "map_of \<Gamma> (Pos A\<^sub>L) = Some (Some C)"
          by (metis (no_types, opaque_lifting) is_pos_def map_of_SomeD map_of_eq_None_iff
              not_Some_eq decided_literals_all_neg_def)

        define \<Gamma>'' where
          "\<Gamma>'' = takeWhile (\<lambda>Ln. atm_of L \<prec>\<^sub>t atm_of (fst Ln)) \<Gamma>"

        have "(Pos A\<^sub>L, Some C) \<in> set \<Gamma>"
          using \<open>map_of \<Gamma> (Pos A\<^sub>L) = Some (Some C)\<close>
          by (metis map_of_SomeD)

        hence "\<Gamma> = \<Gamma>'' @ (Pos A\<^sub>L, Some C) # \<Gamma>'"
          unfolding \<Gamma>''_def
          unfolding \<Gamma>'_eq_if_eres_not_empty[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
          using \<Gamma>_sorted
        proof (induction \<Gamma>)
          case Nil
          hence False by simp
          thus ?case ..
        next
          case (Cons x xs)

          show ?case
          proof (cases "x = (Pos A\<^sub>L, Some C)")
            case True

            have "\<forall>y\<in>set xs. atm_of (fst y) \<prec>\<^sub>t A\<^sub>L"
              using \<open>sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (x # xs)\<close>
              unfolding sorted_wrt.simps \<open>x = (Pos A\<^sub>L, Some C)\<close> prod.sel literal.sel
              by metis

            hence "dropWhile (\<lambda>Ln. A\<^sub>L \<preceq>\<^sub>t atm_of (fst Ln)) xs = xs"
              unfolding dropWhile_eq_self_iff
              by (cases xs) auto

            moreover have "A\<^sub>L \<preceq>\<^sub>t A\<^sub>L"
              by order

            ultimately have "dropWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) (x # xs) = xs"
              unfolding dropWhile.simps
              unfolding \<open>L = Neg A\<^sub>L\<close> \<open>x = (Pos A\<^sub>L, Some C)\<close> prod.sel literal.sel
              by simp

            moreover have "takeWhile (\<lambda>Ln. atm_of L \<prec>\<^sub>t atm_of (fst Ln)) (x # xs) = []"
              unfolding \<open>L = Neg A\<^sub>L\<close> \<open>x = (Pos A\<^sub>L, Some C)\<close> by simp

            ultimately show ?thesis
              unfolding \<open>x = (Pos A\<^sub>L, Some C)\<close> by simp
          next
            case False

            have "atm_of L \<prec>\<^sub>t atm_of (fst x)"
              using \<open>sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (x # xs)\<close>
              using Cons.prems(1) False \<open>L = Neg A\<^sub>L\<close> by fastforce

            moreover have "xs = takeWhile (\<lambda>Ln. atm_of L \<prec>\<^sub>t atm_of (fst Ln)) xs @
                  (Pos A\<^sub>L, Some C) # dropWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) xs"
              using Cons.IH Cons.prems \<open>x \<noteq> (Pos A\<^sub>L, Some C)\<close> by simp

            ultimately show ?thesis
              by simp
          qed
        qed

        have "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)"
          using match_hyps(4)[unfolded ord_res_7_invars_def] by argo

        hence "trail_annotations_invars N (U\<^sub>e\<^sub>r, \<F>, (Pos A\<^sub>L, Some C) # \<Gamma>')"
          using \<open>\<Gamma> = \<Gamma>'' @ (Pos A\<^sub>L, Some C) # \<Gamma>'\<close>
          by (metis suffixI trail_annotations_invars_mono_wrt_trail_suffix)

        hence "ord_res.is_strictly_maximal_lit (Pos A\<^sub>L) C" and
          "C \<in> iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r)" and
          "trail_false_cls \<Gamma>' {#K \<in># C. K \<noteq> Pos A\<^sub>L#}" and
          C_least_propagating: "linorder_cls.is_least_in_fset
            {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). clause_could_propagate \<Gamma>' D (Pos A\<^sub>L)|} C"
          unfolding \<open>\<Gamma> = \<Gamma>'' @ (Pos A\<^sub>L, Some C) # \<Gamma>'\<close>
          by (auto elim: trail_annotations_invars.cases)

        hence "ord_res.is_maximal_lit (Pos A\<^sub>L) C"
          by blast

        have "C \<prec>\<^sub>c eres D E"
          using \<open>ord_res.is_maximal_lit (Pos A\<^sub>L) C\<close> \<open>ord_res.is_maximal_lit L (eres D E)\<close>
          unfolding \<open>L = Neg A\<^sub>L\<close>
          by (simp add: linorder_lit.multp_if_maximal_less_that_maximal)

        have "\<M> (atm_of L) = Some C"
          using \<open>map_of \<Gamma> (Pos A\<^sub>L) = Some (Some C)\<close>
          unfolding \<open>L = Neg A\<^sub>L\<close> literal.sel
          using \<open>\<forall>A C. (\<M> A = Some C) = (map_of \<Gamma> (Pos A) = Some (Some C))\<close>
          by metis

        moreover have "\<M>' = restrict_map \<M> {A. A \<prec>\<^sub>t atm_of L}"
          using \<M>'_eq_if_eres_not_mempty eres_max_lit by metis

        ultimately have "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
          using \<open>\<not> dom \<M> \<TTurnstile> E\<close> \<open>ord_res.is_maximal_lit (Neg A) E\<close> \<open>is_neg (Neg A)\<close>
            \<open>\<M> (atm_of (Neg A)) = Some D\<close> \<open>U\<^sub>e\<^sub>r' = finsert (eres D E) U\<^sub>e\<^sub>r\<close> \<open>eres D E \<noteq> {#}\<close>
            eres_max_lit \<open>is_neg L\<close>
          using ord_res_6.resolution_neg by metis

        moreover have "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C"
          unfolding is_least_false_or_propagating_clause_def
        proof (intro disjI2 conjI)
          show "\<not> fBex (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) (trail_false_cls \<Gamma>')"
            using stronger_not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] .

          show "linorder_cls.is_least_in_fset
          {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). Ex (clause_could_propagate \<Gamma>' C)|} C"
            unfolding \<open>iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') = finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close>
            unfolding linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI exI)
            have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
              using match_hyps(4) \<open>map_of \<Gamma> (Pos A\<^sub>L) = Some (Some C)\<close>
              by (metis propagating_clause_in_clauses ord_res_7_invars_def)

            thus "C |\<in>| finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
              by simp

            show "clause_could_propagate \<Gamma>' C (Pos A\<^sub>L)"
              unfolding clause_could_propagate_def
            proof (intro conjI)
              show "\<not> trail_defined_lit \<Gamma>' (Pos A\<^sub>L)"
                by (metis \<open>L = Neg A\<^sub>L\<close> eres_max_lit linorder_trm.less_imp_not_eq2 literal.sel
                    mem_trail_atoms_\<Gamma>'_iff trail_atoms_def trail_defined_lit_iff)
            next
              show "ord_res.is_maximal_lit (Pos A\<^sub>L) C"
                using \<open>ord_res.is_maximal_lit (Pos A\<^sub>L) C\<close> .

              show "trail_false_cls \<Gamma>' {#K \<in># C. K \<noteq> Pos A\<^sub>L#}"
                using \<open>trail_false_cls \<Gamma>' {#K \<in># C. K \<noteq> Pos A\<^sub>L#}\<close> .
            qed
          next
            fix y
            assume
              "y |\<in>| finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))" and
              "y \<noteq> C" and
              "Ex (clause_could_propagate \<Gamma>' y)"

            obtain K where "clause_could_propagate \<Gamma>' y K"
              using \<open>Ex (clause_could_propagate \<Gamma>' y)\<close> by metis

            hence
              "\<not> trail_defined_lit \<Gamma>' K" and
              "ord_res.is_maximal_lit K y" and
              "trail_false_cls \<Gamma>' {#a \<in># y. a \<noteq> K#}"
              unfolding atomize_conj clause_could_propagate_def
              by metis

            show "C \<prec>\<^sub>c y"
            proof (cases "y = eres D E")
              case True
              thus ?thesis
                using \<open>C \<prec>\<^sub>c eres D E\<close> by argo
            next
              case False

              hence "y |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
                using \<open>y |\<in>| finsert (eres D E) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))\<close> by simp

              show ?thesis
              proof (cases "K = Pos A\<^sub>L")
                case True
                thus ?thesis
                  using C_least_propagating
                  unfolding linorder_cls.is_least_in_ffilter_iff
                  using \<open>y |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close> \<open>y \<noteq> C\<close> \<open>clause_could_propagate \<Gamma>' y K\<close>
                  by metis
              next
                case False

                have "atm_of K \<notin> trail_atoms \<Gamma>'"
                  using \<open>\<not> trail_defined_lit \<Gamma>' K\<close>
                  unfolding trail_defined_lit_iff_trail_defined_atm
                  unfolding trail_defined_atm_def
                  unfolding trail_atoms_def .

                hence "atm_of L \<preceq>\<^sub>t atm_of K \<or> atm_of K \<notin> trail_atoms \<Gamma>"
                  unfolding mem_trail_atoms_\<Gamma>'_iff[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] by auto

                hence "Pos A\<^sub>L \<prec>\<^sub>l K"
                proof (elim disjE)
                  assume "atm_of L \<preceq>\<^sub>t atm_of K"
                  thus "Pos A\<^sub>L \<prec>\<^sub>l K"
                    using \<open>L = Neg A\<^sub>L\<close> \<open>K \<noteq> Pos A\<^sub>L\<close>
                    by (metis atm_of_eq_atm_of linorder_lit.antisym_conv3 linorder_trm.leD
                        literal.sel(2) ord_res.less_lit_simps(1) ord_res.less_lit_simps(4) uminus_Neg)
                next
                  assume "atm_of K \<notin> trail_atoms \<Gamma>"

                  moreover have "atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)"
                  proof -
                    have "K \<in># y"
                      using \<open>ord_res.is_maximal_lit K y\<close>
                      unfolding linorder_lit.is_maximal_in_mset_iff by argo

                    hence "atm_of K \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
                      unfolding atoms_of_clause_set_def
                      using \<open>y |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)\<close>
                      by blast

                    thus ?thesis
                      by simp
                  qed

                  ultimately have "\<not> (atm_of K \<prec>\<^sub>t A)"
                    using \<Gamma>_lower_set[unfolded linorder_trm.is_lower_set_iff, THEN conjunct2,
                        rule_format, OF \<open>A \<in> trail_atoms \<Gamma>\<close> \<open>atm_of K \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r)\<close>]
                    by argo

                  hence "A \<preceq>\<^sub>t atm_of K"
                    by order

                  hence "Pos A \<preceq>\<^sub>l K"
                    by (cases K) simp_all

                  moreover have "Pos A\<^sub>L \<prec>\<^sub>l Pos A"
                    by (metis \<open>- Neg A \<notin># E\<close> \<open>L = Neg A\<^sub>L\<close> \<open>eres D E \<noteq> E\<close> eres_max_lit
                        linorder_lit.is_maximal_in_mset_iff
                        lit_in_eres_lt_greatest_lit_in_grestest_resolvant literal.sel(2)
                        ord_res.less_lit_simps(1) step_hyps(3))

                  ultimately show "Pos A\<^sub>L \<prec>\<^sub>l K"
                    by order
                qed

                thus "C \<prec>\<^sub>c y"
                  using \<open>ord_res.is_maximal_lit (Pos A\<^sub>L) C\<close> \<open>ord_res.is_maximal_lit K y\<close>
                  using linorder_lit.multp_if_maximal_less_that_maximal by metis
              qed
            qed
          qed
        qed

        moreover have atom_defined_in_\<Gamma>': "trail_defined_atm \<Gamma>' A"
          if A_in: "A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')" and
            ex_max_lit_gt_A: "\<exists>L. ord_res.is_maximal_lit L C \<and> A \<prec>\<^sub>t atm_of L"
          for A
        proof -
          have "A \<prec>\<^sub>t atm_of (Pos A\<^sub>L)"
            using ex_max_lit_gt_A \<open>ord_res.is_maximal_lit (Pos A\<^sub>L) C\<close>
            by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

          hence "A \<prec>\<^sub>t atm_of L"
            by (simp add: \<open>L = Neg A\<^sub>L\<close>)

          moreover hence "A \<in> trail_atoms \<Gamma>"
            using mem_trail_atoms_\<Gamma>_if[of L A] \<open>ord_res.is_maximal_lit L (eres D E)\<close> A_in by argo

          ultimately have "A \<in> trail_atoms \<Gamma>'"
            unfolding mem_trail_atoms_\<Gamma>'_iff[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] by argo

          thus ?thesis
            unfolding trail_atoms_def trail_defined_atm_def .
        qed


        moreover have "trail_true_cls \<Gamma>' x"
          if x_in: "x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')" and "x \<prec>\<^sub>c C" for x
        proof -
          have "x \<prec>\<^sub>c eres D E"
            using \<open>x \<prec>\<^sub>c C\<close> \<open>C \<prec>\<^sub>c eres D E\<close> by order

          have "\<not> trail_false_cls \<Gamma>' x"
            using stronger_not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>] x_in
            by metis

          hence "x \<noteq> {#}"
            using trail_false_cls_mempty by metis

          then obtain K where x_max_lit: "linorder_lit.is_maximal_in_mset x K"
            using linorder_lit.ex_maximal_in_mset by metis

          hence "K \<preceq>\<^sub>l Pos A\<^sub>L"
            using \<open>x \<prec>\<^sub>c C\<close> \<open>ord_res.is_maximal_lit (Pos A\<^sub>L) C\<close>
            by (metis linorder_cls.less_asym linorder_lit.leI
                linorder_lit.multp_if_maximal_less_that_maximal)

          have "linorder_cls.is_least_in_fset {|C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r').
          Ex (clause_could_propagate \<Gamma>' C)|} C"
            using \<open>is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C\<close>
            using stronger_not_bex_false_clause_in_\<Gamma>'[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
            by (metis is_least_false_or_propagating_clause_def linorder_cls.is_least_in_ffilter_iff)

          hence "\<not> clause_could_propagate \<Gamma>' x K"
            using \<open>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')\<close> \<open>x \<prec>\<^sub>c C\<close>
            unfolding linorder_cls.is_least_in_ffilter_iff
            by (metis linorder_cls.order.asym)

          hence FOO: "trail_defined_lit \<Gamma>' K \<or> \<not> trail_false_cls \<Gamma>' {#Ka \<in># x. Ka \<noteq> K#}"
            unfolding clause_could_propagate_def de_Morgan_conj not_not
            using x_max_lit by metis

          have "trail_defined_lit \<Gamma>' J"
            if "J \<in># x" and "J \<prec>\<^sub>l K" for J
            unfolding trail_defined_lit_iff_trail_defined_atm
          proof (rule atom_defined_in_\<Gamma>')
            have "atm_of J \<in> atoms_of_clause_set (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))"
              using \<open>J \<in># x\<close> x_in
              unfolding atoms_of_clause_set_def by blast
            thus "atm_of J \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')"
              by simp
          next
            have "J \<prec>\<^sub>l Pos A\<^sub>L"
              using \<open>J \<prec>\<^sub>l K\<close> \<open>K \<preceq>\<^sub>l Pos A\<^sub>L\<close> by order
            thus "\<exists>L. ord_res.is_maximal_lit L C \<and> atm_of J \<prec>\<^sub>t atm_of L"
              using \<open>ord_res.is_maximal_lit (Pos A\<^sub>L) C\<close>
              by (metis literal.exhaust_sel literal.sel(1) ord_res.less_lit_simps(1)
                  ord_res.less_lit_simps(4))
          qed

          hence "trail_defined_cls \<Gamma>' {#Ka \<in># x. Ka \<noteq> K#}"
            unfolding trail_defined_cls_def
            using linorder_lit.is_maximal_in_mset_iff linorder_lit.not_less_iff_gr_or_eq x_max_lit
            by fastforce

          thus ?thesis
            using \<open>\<not> trail_false_cls \<Gamma>' x\<close> FOO
            by (smt (verit, best) mem_Collect_eq set_mset_filter trail_defined_cls_def
                trail_defined_lit_iff_true_or_false trail_false_cls_def trail_true_cls_def)
        qed

        ultimately show ?thesis
          by metis
      qed
    qed

    moreover have "ord_res_6_matches_ord_res_7 (measure_ord_res_7 N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>'))
      (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some C) S7'"
      if step6: "ord_res_6 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some E) (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)" and
        invars:
          "is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C"
          "\<forall>A. A \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r') \<longrightarrow>
            (\<exists>L. ord_res.is_maximal_lit L C \<and> A \<prec>\<^sub>t atm_of L) \<longrightarrow>
            trail_defined_atm \<Gamma>' A"
          "\<forall>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). x \<prec>\<^sub>c C \<longrightarrow> trail_true_cls \<Gamma>' x"
      for C
      unfolding \<open>S7' = (N, s7')\<close> \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close>
    proof (intro ord_res_6_matches_ord_res_7.intros allI ballI impI)
      show "ord_res_5_invars N (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)"
        using \<open>ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some E\<close> step6
        by (metis ord_res_6_preserves_invars)
    next
      show "ord_res_7_invars N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')"
        using \<open>ord_res_7_invars N (U\<^sub>e\<^sub>r, \<F>, \<Gamma>)\<close> step' \<open>s7' = (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')\<close>
        by (metis ord_res_7_preserves_invars)
    next
      fix x y
      have "\<M>' x = Some y \<longleftrightarrow>
        (\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> x \<prec>\<^sub>t atm_of L) \<and> \<M> x = Some y"
        by (simp add: \<M>'_def restrict_map_def)

      also have "\<dots> \<longleftrightarrow> map_of \<Gamma>' (Pos x) = Some (Some y)"
      proof (cases "eres D E = {#}")
        case True
        thus ?thesis
          by (simp add: \<Gamma>'_eq_if_eres_empty linorder_lit.is_maximal_in_mset_iff)
      next
        case False
        then obtain L where "ord_res.is_maximal_lit L (eres D E)"
          using linorder_lit.ex_maximal_in_mset by metis

        hence "\<forall>Ln \<in> set \<Gamma>'. atm_of (fst Ln) \<prec>\<^sub>t atm_of L"
          using ball_\<Gamma>'_lt_atm_of_max_lit_in_eres by metis

        define \<Gamma>'' where
          "\<Gamma>'' = takeWhile (\<lambda>Ln. atm_of L \<preceq>\<^sub>t atm_of (fst Ln)) \<Gamma>"

        have "\<Gamma> = \<Gamma>'' @ \<Gamma>'"
          unfolding \<Gamma>''_def
          unfolding \<Gamma>'_eq_if_eres_not_empty[OF \<open>ord_res.is_maximal_lit L (eres D E)\<close>]
          unfolding takeWhile_dropWhile_id ..

        have map_of_\<Gamma>_eq_map_of_\<Gamma>'_if: "map_of \<Gamma> (Pos x) = map_of \<Gamma>' (Pos x)" if "x \<prec>\<^sub>t atm_of L"
        proof -
          have "map_of \<Gamma> (Pos x) = map_of (\<Gamma>'' @ \<Gamma>') (Pos x)"
            unfolding \<open>\<Gamma> = \<Gamma>'' @ \<Gamma>'\<close> ..

          also have "\<dots> = (map_of \<Gamma>' ++ map_of \<Gamma>'') (Pos x)"
            unfolding map_of_append ..

          also have "\<dots> = map_of \<Gamma>' (Pos x)"
          proof (rule map_add_dom_app_simps(3))
            show "Pos x \<notin> dom (map_of \<Gamma>'')"
              unfolding \<Gamma>''_def
              unfolding dom_map_of_conv_image_fst
              by (metis (no_types, lifting) \<open>x \<prec>\<^sub>t atm_of L\<close> image_iff linorder_trm.leD
                  literal.sel(1) takeWhile_eq_all_conv takeWhile_idem)
          qed

          finally show ?thesis .
        qed

        show ?thesis
        proof (intro iffI conjI , elim conjE)
          assume "\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> x \<prec>\<^sub>t atm_of L"
          hence "x \<prec>\<^sub>t atm_of L"
            using \<open>ord_res.is_maximal_lit L (eres D E)\<close>
            by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

          assume "\<M> x = Some y"

          hence "map_of \<Gamma> (Pos x) = Some (Some y)"
            using match_hyps(5) by metis

          thus "map_of \<Gamma>' (Pos x) = Some (Some y)"
             using map_of_\<Gamma>_eq_map_of_\<Gamma>'_if \<open>x \<prec>\<^sub>t atm_of L\<close> by argo
        next
          assume "map_of \<Gamma>' (Pos x) = Some (Some y)"

          hence "(Pos x, Some y) \<in> set \<Gamma>'"
            by (metis map_of_SomeD)

          hence "x \<prec>\<^sub>t atm_of L"
            using \<open>\<forall>Ln \<in> set \<Gamma>'. atm_of (fst Ln) \<prec>\<^sub>t atm_of L\<close> by auto

          thus "\<exists>L. ord_res.is_maximal_lit L (eres D E) \<and> x \<prec>\<^sub>t atm_of L"
            using \<open>ord_res.is_maximal_lit L (eres D E)\<close> by metis

          have "map_of \<Gamma> (Pos x) = Some (Some y)"
            using map_of_\<Gamma>_eq_map_of_\<Gamma>'_if \<open>x \<prec>\<^sub>t atm_of L\<close> \<open>map_of \<Gamma>' (Pos x) = Some (Some y)\<close>
            by argo

          thus "\<M> x = Some y"
            using match_hyps(5) by metis
        qed
      qed

      finally show "\<M>' x = Some y \<longleftrightarrow> map_of \<Gamma>' (Pos x) = Some (Some y)" .
    next
      show "\<And>C'. (Some C = Some C') = is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C'"
        using \<open>is_least_false_or_propagating_clause N U\<^sub>e\<^sub>r' \<F> \<Gamma>' C\<close>
        by (metis Uniq_D Uniq_is_least_false_or_propagating_clause option.inject)
    next
      show "\<And>x. x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r') \<Longrightarrow>
          \<forall>C'. Some C = Some C' \<longrightarrow> x \<prec>\<^sub>c C' \<Longrightarrow> trail_true_cls \<Gamma>' x"
        using invars(3) by metis
    next
      fix x
      assume
        "x \<in> atoms_of_clause_set (N |\<union>| U\<^sub>e\<^sub>r')" and
        "\<forall>Ca. Some C = Some Ca \<longrightarrow> (\<exists>L. ord_res.is_maximal_lit L Ca \<and> x \<prec>\<^sub>t atm_of L)"

      thus "trail_defined_atm \<Gamma>' x"
        using invars(2) by blast
    next
      show "measure_ord_res_7 N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>') = measure_ord_res_7 N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')" ..
    qed

    ultimately have "\<exists>C.
      ord_res_6_step\<^sup>+\<^sup>+ S6 (N, (U\<^sub>e\<^sub>r', \<F>, \<M>', Some C)) \<and>
      ord_res_6_matches_ord_res_7 (measure_ord_res_7 N (U\<^sub>e\<^sub>r', \<F>, \<Gamma>')) (N, U\<^sub>e\<^sub>r', \<F>, \<M>', Some C) S7'"
      unfolding \<open>S6 = (N, U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)\<close> \<open>\<C> = Some E\<close>
      using ord_res_6_step.intros by blast

    thus ?thesis by metis
  qed
qed

theorem bisimulation_ord_res_6_ord_res_7:
  defines "match \<equiv> ord_res_6_matches_ord_res_7"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow>
    'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times> ('f gterm literal \<times> 'f gclause option) list \<Rightarrow> bool) ORDER.
    bisimulation ord_res_6_step (constant_context ord_res_7) ord_res_6_final ord_res_7_final ORDER MATCH"
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_6_step"
    using right_unique_ord_res_6_step .
next
  show "right_unique (constant_context ord_res_7)"
    using right_unique_constant_context right_unique_ord_res_7 by metis
next
  show "\<forall>S. ord_res_6_final S \<longrightarrow> (\<nexists>S'. ord_res_6_step S S')"
    by (metis finished_def ord_res_6_semantics.final_finished)
next
  show "\<forall>S. ord_res_7_final S \<longrightarrow> (\<nexists>S'. constant_context ord_res_7 S S')"
    by (metis finished_def ord_res_7_semantics.final_finished)
next
  show "\<forall>i S6 S7. match i S6 S7 \<longrightarrow> ord_res_6_final S6 \<longleftrightarrow> ord_res_7_final S7"
    unfolding match_def
    using ord_res_6_final_iff_ord_res_7_final by metis
next
  show "\<forall>i S6 S7. match i S6 S7 \<longrightarrow>
       safe_state ord_res_6_step ord_res_6_final S6 \<and>
       safe_state (constant_context ord_res_7) ord_res_7_final S7"
  proof (intro allI impI conjI)
    fix i S6 S7
    assume "match i S6 S7"
    show "safe_state ord_res_6_step ord_res_6_final S6"
      using \<open>match i S6 S7\<close>[unfolded match_def]
      using ord_res_6_safe_state_if_invars
      using ord_res_6_matches_ord_res_7.simps by auto

    show "safe_state (constant_context ord_res_7) ord_res_7_final S7"
      using \<open>match i S6 S7\<close>[unfolded match_def]
      using ord_res_7_safe_state_if_invars
      using ord_res_6_matches_ord_res_7.simps by auto
  qed
next
  show "wfp (|\<subset>|)"
    using wfP_pfsubset .
next
  show "\<forall>i S6 S7 S7'. match i S6 S7 \<longrightarrow> constant_context ord_res_7 S7 S7' \<longrightarrow>
    (\<exists>i' S6'. ord_res_6_step\<^sup>+\<^sup>+ S6 S6' \<and> match i' S6' S7') \<or>
    (\<exists>i'. match i' S6 S7' \<and> i' |\<subset>| i)"
    unfolding match_def
    using backward_simulation_between_6_and_7 by metis
qed


section \<open>ORD-RES-8 (only propagate when necessary)\<close>


section \<open>SCL(FOL)-2 (one-step conflict resolution)\<close>

inductive scl_fol_2 where
  decide_neg: "\<not> (\<exists>C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_set {A\<^sub>2 \<in> atoms_of_clause_set N. \<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A \<Longrightarrow>
    \<not> (\<exists>C |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    scl_fol_2 N (\<Gamma>, U, None) (\<Gamma>', U)" |

  decide_pos: "\<not> (\<exists>C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_set {A\<^sub>2 \<in> atoms_of_clause_set N. \<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    \<not> (\<exists>D |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> D (Neg A)) \<Longrightarrow>
    \<Gamma>' = (Pos A, None) # \<Gamma> \<Longrightarrow>
    scl_fol_2 N (\<Gamma>, U, None) (\<Gamma>', U)" |

  propagate_pos: "\<not> (\<exists>C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_set {A\<^sub>2 \<in> atoms_of_clause_set N. \<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    (\<exists>D |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> D (Neg A)) \<Longrightarrow>
    \<Gamma>' = (Pos A, Some {#L \<in># C. L \<noteq> Pos A#}) # \<Gamma> \<Longrightarrow>
    scl_fol_2 N (\<Gamma>, U, None) (\<Gamma>', U)" |

  conflict_resolution: "
    linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C|} D \<Longrightarrow>
    linorder_lit.is_maximal_in_mset D (Neg A) \<Longrightarrow>
    C = add_mset (Pos A) C' \<Longrightarrow>
    U' = finsert (eres C D) U \<Longrightarrow>
    \<Gamma>' = dropWhile (\<lambda>(L, _). \<forall>K.
      linorder_lit.is_maximal_in_mset (eres C D) K \<longrightarrow> atm_of K \<preceq>\<^sub>t atm_of L) \<Gamma> \<Longrightarrow>
    scl_fol_2 N ((Pos A, Some C') # \<Gamma>, U, None) (\<Gamma>', U')"


section \<open>SCL(FOL)-1 (resolution-driven strategy)\<close>

inductive scl_fol_1 where
  decide_neg: "\<not> (\<exists>C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_set {A\<^sub>2 \<in> atoms_of_clause_set N. \<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A \<Longrightarrow>
    \<not> (\<exists>C |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<Gamma>' = (Neg A, None) # \<Gamma> \<Longrightarrow>
    scl_fol_1 N (\<Gamma>, U, None) (\<Gamma>', U, None)" |

  decide_pos: "\<not> (\<exists>C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_set {A\<^sub>2 \<in> atoms_of_clause_set N. \<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A \<Longrightarrow>
    (\<exists>C |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> C (Pos A)) \<Longrightarrow>
    \<not> (\<exists>D |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> D (Neg A)) \<Longrightarrow>
    \<Gamma>' = (Pos A, None) # \<Gamma> \<Longrightarrow>
    scl_fol_1 N (\<Gamma>, U, None) (\<Gamma>', U, None)" |

  propagate_pos: "\<not> (\<exists>C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C) \<Longrightarrow>
    linorder_trm.is_least_in_set {A\<^sub>2 \<in> atoms_of_clause_set N. \<forall>A\<^sub>1 \<in> trail_atoms \<Gamma>. A\<^sub>1 \<prec>\<^sub>t A\<^sub>2} A \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> C (Pos A)|} C \<Longrightarrow>
    (\<exists>D |\<in>| N |\<union>| U. clause_could_propagate \<Gamma> D (Neg A)) \<Longrightarrow>
    \<Gamma>' = (Pos A, Some {#L \<in># C. L \<noteq> Pos A#}) # \<Gamma> \<Longrightarrow>
    scl_fol_1 N (\<Gamma>, U, None) (\<Gamma>', U, None)" |

  conflict: "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| U. trail_false_cls \<Gamma> C|} C \<Longrightarrow>
    scl_fol_1 N (\<Gamma>, U, None) (\<Gamma>, U, Some C)" |

  skip: "- L \<notin># C \<Longrightarrow>
    scl_fol_1 N ((L, n) # \<Gamma>, U, Some C) (\<Gamma>, U, Some C)" |

  resolve: "\<Gamma> = (L, Some C) # \<Gamma>' \<Longrightarrow> L = - K \<Longrightarrow>
    scl_fol_1 N (\<Gamma>, U, Some (add_mset K D)) (\<Gamma>, U, Some (C + D))" |

  backjump: "\<Gamma> = (L, None) # \<Gamma>' \<Longrightarrow> L = - K \<Longrightarrow>
    scl_fol_1 N (\<Gamma>, U, Some (add_mset K D)) (\<Gamma>', finsert (add_mset K D) U, None)"

lemma "right_unique (scl_fol_1 N)"
proof (rule right_uniqueI)
  fix x y z
  assume step1: "scl_fol_1 N x y" and step2: "scl_fol_1 N x z"
  show "y = z"
    using step1
  proof (cases N x y rule: scl_fol_1.cases)
    case step1_hyps: (decide_neg U \<Gamma> A \<Gamma>')
    show ?thesis
      using step2
      unfolding \<open>x = (\<Gamma>, U, None)\<close>
    proof (cases N "(\<Gamma>, U, None :: 'f gterm literal multiset option)" z rule: scl_fol_1.cases)
      case (decide_neg A2 \<Gamma>2')
      with step1_hyps show ?thesis
        by (metis (no_types, lifting) linorder_trm.Uniq_is_least_in_set the1_equality')
    next
      case (decide_pos A2 \<Gamma>2')
      with step1_hyps have False
        by (metis (mono_tags, lifting) Uniq_D linorder_trm.Uniq_is_least_in_set)
      thus ?thesis ..
    next
      case (propagate_pos A2 C2 \<Gamma>2')
      with step1_hyps have False
        by (metis (mono_tags, lifting) Uniq_D linorder_cls.is_least_in_fset_ffilterD(1)
            linorder_cls.is_least_in_fset_ffilterD(2) linorder_trm.Uniq_is_least_in_set)
      thus ?thesis ..
    next
      case (conflict C2)
      with step1_hyps have False
        using linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2)
        by blast
      thus ?thesis ..
    qed
  next
    case step1_hyps: (decide_pos U \<Gamma> A \<Gamma>')
    show ?thesis
      using step2
      unfolding \<open>x = (\<Gamma>, U, None)\<close>
    proof (cases N "(\<Gamma>, U, None :: 'f gterm literal multiset option)" z rule: scl_fol_1.cases)
      case (decide_neg A2 \<Gamma>2')
      with step1_hyps have False
        by (metis (mono_tags, lifting) Uniq_D linorder_trm.Uniq_is_least_in_set)
      thus ?thesis ..
    next
      case (decide_pos A2 \<Gamma>2')
      with step1_hyps show ?thesis
        by (metis (no_types, lifting) linorder_trm.Uniq_is_least_in_set the1_equality')
    next
      case (propagate_pos A2 C2 \<Gamma>2')
      with step1_hyps have False
        by (metis (no_types, lifting) linorder_trm.Uniq_is_least_in_set the1_equality')
      thus ?thesis ..
    next
      case (conflict C2)
      with step1_hyps have False
        using linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2)
        by blast
      thus ?thesis ..
    qed
  next
    case step1_hyps: (propagate_pos U \<Gamma> A C \<Gamma>')
    show ?thesis
      using step2
      unfolding \<open>x = (\<Gamma>, U, None)\<close>
    proof (cases N "(\<Gamma>, U, None :: 'f gterm literal multiset option)" z rule: scl_fol_1.cases)
      case (decide_neg A2 \<Gamma>2')
      with step1_hyps have False
        by (metis (mono_tags, lifting) Uniq_D linorder_cls.is_least_in_fset_ffilterD(1)
            linorder_cls.is_least_in_fset_ffilterD(2) linorder_trm.Uniq_is_least_in_set)
      thus ?thesis ..
    next
      case (decide_pos A2 \<Gamma>2')
      with step1_hyps show ?thesis
        by (metis (no_types, lifting) linorder_trm.Uniq_is_least_in_set the1_equality')
    next
      case step2_hyps: (propagate_pos A2 C2 \<Gamma>2')
      have "A2 = A"
        using step1_hyps step2_hyps
        by (metis (no_types, lifting) linorder_trm.dual_order.asym linorder_trm.is_least_in_set_iff)

      have "C2 = C"
        using step1_hyps step2_hyps
        unfolding \<open>A2 = A\<close>
        by (metis (no_types, lifting) linorder_cls.is_least_in_ffilter_iff linorder_cls.not_less_iff_gr_or_eq)

      have "\<Gamma>2' = \<Gamma>'"
        using step1_hyps step2_hyps
        unfolding \<open>A2 = A\<close> \<open>C2 = C\<close> by argo

      thus "y = z"
        unfolding \<open>y = (\<Gamma>', U, None)\<close> \<open>z = (\<Gamma>2', U, None)\<close>
        unfolding prod.inject by argo
    next
      case (conflict C2)
      with step1_hyps have False
        using linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2)
        by blast
      thus ?thesis ..
    qed
  next
    case step1_hyps: (conflict \<Gamma> U C)
    show ?thesis
      using step2
      unfolding \<open>x = (\<Gamma>, U, None)\<close>
    proof (cases N "(\<Gamma>, U, None :: 'f gterm literal multiset option)" z rule: scl_fol_1.cases)
      case (decide_neg A2 \<Gamma>2')
      with step1_hyps have False
        using linorder_cls.is_least_in_ffilter_iff by metis
      thus ?thesis ..
    next
      case (decide_pos A2 \<Gamma>2')
      with step1_hyps have False
        using linorder_cls.is_least_in_ffilter_iff by metis
      thus ?thesis ..
    next
      case (propagate_pos A2 C2 \<Gamma>2')
      with step1_hyps have False
        using linorder_cls.is_least_in_ffilter_iff by metis
      thus ?thesis ..
    next
      case (conflict C2)
      with step1_hyps show ?thesis
        by (metis Uniq_D linorder_cls.Uniq_is_least_in_fset)
    qed
  next
    case step2_hyps: (skip L C n \<Gamma> U)
    show ?thesis
      using step2
      unfolding \<open>x = ((L, n) # \<Gamma>, U, Some C)\<close>
    proof (cases N "((L, n) # \<Gamma>, U, Some C)" z rule: scl_fol_1.cases)
      case skip
      with step2_hyps show ?thesis
        by argo
    next
      case (resolve L2 C2 \<Gamma>2' K2 D2)
      with step2_hyps have False
        by force
      thus ?thesis ..
    next
      case (backjump L2 \<Gamma>2' K2 D2)
      with step2_hyps have False
        by force
      thus ?thesis ..
    qed
  next
    case step2_hyps: (resolve \<Gamma> L C \<Gamma>' K U D)
    thus ?thesis
      using step2 by (simp add: scl_fol_1.simps)
  next
    case (backjump \<Gamma> L \<Gamma>' K U D)
    thus ?thesis
      using step2 by (simp add: scl_fol_1.simps)
  qed
qed


abbreviation trail_of_gtrail where
  "trail_of_gtrail \<equiv> map (\<lambda>(L, opt). (lit_of_glit L, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L, Var)) opt))"

fun state_of_gstate ::
  "('f gterm literal \<times> 'f gterm clause option) list \<times> 'f gclause fset \<times> 'f gclause option \<Rightarrow> ('f, 'v) state" where
  "state_of_gstate (\<Gamma>\<^sub>G, U\<^sub>G, \<C>\<^sub>G) =
    (let
      \<Gamma> = trail_of_gtrail \<Gamma>\<^sub>G;
      U = cls_of_gcls |`| U\<^sub>G;
      \<C> = map_option (\<lambda>C\<^sub>G. (cls_of_gcls C\<^sub>G, Var)) \<C>\<^sub>G
    in (\<Gamma>, U, \<C>))"

lemma fst_case_prod_simp: "fst (case p of (x, y) \<Rightarrow> (f x, g x y)) = f (fst p)"
  by (cases p) simp

lemma trail_false_cls_nonground_iff_trail_false_cls_ground:
  fixes \<Gamma>\<^sub>G and D\<^sub>G :: "'f gclause"
  fixes \<Gamma> :: "('f, 'v) SCL_FOL.trail" and D :: "('f, 'v) term clause"
  defines "\<Gamma> \<equiv> trail_of_gtrail \<Gamma>\<^sub>G" and "D \<equiv> cls_of_gcls D\<^sub>G"
  shows "trail_false_cls \<Gamma> D \<longleftrightarrow> trail_false_cls \<Gamma>\<^sub>G D\<^sub>G"
proof -
  have "trail_false_cls \<Gamma> D \<longleftrightarrow> (\<forall>L \<in># D. trail_false_lit \<Gamma> L)"
    unfolding trail_false_cls_def ..
  also have "\<dots> \<longleftrightarrow> (\<forall>L\<^sub>G \<in># D\<^sub>G. trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G))"
    unfolding D_def cls_of_gcls_def by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>L\<^sub>G \<in># D\<^sub>G. trail_false_lit \<Gamma>\<^sub>G L\<^sub>G)"
  proof -
    have "trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G) \<longleftrightarrow> trail_false_lit \<Gamma>\<^sub>G L\<^sub>G"
      for L\<^sub>G :: "'f gterm literal"
    proof -
      have "trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G) \<longleftrightarrow> - lit_of_glit L\<^sub>G \<in> fst ` set \<Gamma>"
        unfolding trail_false_lit_def ..
      also have "\<dots> \<longleftrightarrow>
        - (lit_of_glit L\<^sub>G :: ('f, 'v) term literal) \<in> set (map (\<lambda>x. lit_of_glit (fst x)) \<Gamma>\<^sub>G)"
        unfolding \<Gamma>_def image_set list.map_comp
        unfolding comp_def fst_case_prod_simp
        unfolding image_set[symmetric] ..
      also have "\<dots> \<longleftrightarrow> (lit_of_glit (- L\<^sub>G) :: ('f, 'v) term literal) \<in> lit_of_glit ` fst ` set \<Gamma>\<^sub>G"
        by (cases L\<^sub>G) (auto simp: lit_of_glit_def)
      also have "\<dots> \<longleftrightarrow> - L\<^sub>G \<in> fst ` set \<Gamma>\<^sub>G"
        using inj_image_mem_iff inj_lit_of_glit by metis
      also have "\<dots> \<longleftrightarrow> trail_false_lit \<Gamma>\<^sub>G L\<^sub>G"
        unfolding trail_false_lit_def ..
      finally show "trail_false_lit \<Gamma> (lit_of_glit L\<^sub>G) = trail_false_lit \<Gamma>\<^sub>G L\<^sub>G" .
    qed
    thus ?thesis by metis
  qed
  also have "\<dots> \<longleftrightarrow> trail_false_cls \<Gamma>\<^sub>G D\<^sub>G"
    unfolding trail_false_cls_def ..
  finally show ?thesis .
qed

lemma
  fixes
    N\<^sub>G :: "'f gclause fset" and
    N :: "('f, 'v) term clause fset" and
    \<beta>\<^sub>G :: "'f gterm" and
    \<beta> :: "('f, 'v) term" and
    S\<^sub>G S\<^sub>G' :: "('f gterm literal \<times> 'f gterm clause option) list \<times> 'f gclause fset \<times> 'f gclause option" and
    S S' :: "('f, 'v) state"
  defines
    "N \<equiv> cls_of_gcls |`| N\<^sub>G" and
    "\<beta> \<equiv> term_of_gterm \<beta>\<^sub>G" and
    "S \<equiv> state_of_gstate S\<^sub>G" and
    "S' \<equiv> state_of_gstate S\<^sub>G'"
  assumes
    ball_le_\<beta>\<^sub>G: "\<forall>A\<^sub>G \<in> atoms_of_clause_set N\<^sub>G. A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G" and
    invar: "trail_consistent (fst S\<^sub>G)" and
    step: "scl_fol_1 N\<^sub>G S\<^sub>G S\<^sub>G'"
  shows
    "scl_fol.regular_scl N \<beta> S S'"
proof -
  obtain \<Gamma>\<^sub>G U\<^sub>G \<C>\<^sub>G where S\<^sub>G_def: "S\<^sub>G = (\<Gamma>\<^sub>G, U\<^sub>G, \<C>\<^sub>G)"
    by (metis surj_pair)

  obtain \<Gamma> U \<C> where S_def: "S = (\<Gamma>, U, \<C>)"
    by (metis surj_pair)

  have \<Gamma>_def: "\<Gamma> = trail_of_gtrail \<Gamma>\<^sub>G"
    using S_def S\<^sub>G_def \<open>S \<equiv> state_of_gstate S\<^sub>G\<close> by simp

  have U_def: "U = cls_of_gcls |`| U\<^sub>G"
    using S_def S\<^sub>G_def \<open>S \<equiv> state_of_gstate S\<^sub>G\<close> by simp

  have \<C>_def: "\<C> = map_option (\<lambda>C\<^sub>G. (cls_of_gcls C\<^sub>G, Var)) \<C>\<^sub>G"
    using S_def S\<^sub>G_def \<open>S \<equiv> state_of_gstate S\<^sub>G\<close> by simp

  obtain \<Gamma>\<^sub>G' U\<^sub>G' \<C>\<^sub>G' where S\<^sub>G'_def: "S\<^sub>G' = (\<Gamma>\<^sub>G', U\<^sub>G', \<C>\<^sub>G')"
    by (metis surj_pair)

  obtain \<Gamma>' U' \<C>' where S'_def: "S' = (\<Gamma>', U', \<C>')"
    by (metis surj_pair)

  have \<Gamma>'_def: "\<Gamma>' = map (\<lambda>(L, opt). (lit_of_glit L, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L, Var)) opt)) \<Gamma>\<^sub>G'"
    using S'_def S\<^sub>G'_def \<open>S' \<equiv> state_of_gstate S\<^sub>G'\<close> by simp

  have U'_def: "U' = cls_of_gcls |`| U\<^sub>G'"
    using S'_def S\<^sub>G'_def \<open>S' \<equiv> state_of_gstate S\<^sub>G'\<close> by simp

  have \<C>'_def: "\<C>' = map_option (\<lambda>C\<^sub>G. (cls_of_gcls C\<^sub>G, Var)) \<C>\<^sub>G'"
    using S'_def S\<^sub>G'_def \<open>S' \<equiv> state_of_gstate S\<^sub>G'\<close> by simp

  have nex_conflict_if_nbex_trail_false:
    "\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G) \<Longrightarrow> \<not> Ex (scl_fol.conflict N \<beta> S)"
  proof (elim contrapos_nn exE)
    fix x :: "('f, 'v) state"
    assume "scl_fol.conflict N \<beta> S x"
    thus "fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)"
      unfolding S_def
    proof (cases N \<beta> "(\<Gamma>, U, \<C>)" x rule: scl_fol.conflict.cases)
      case (conflictI D \<gamma>)

      obtain D\<^sub>G where "D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and D_def: "D = cls_of_gcls D\<^sub>G"
        using \<open>D |\<in>| N |\<union>| U\<close>
        unfolding N_def U_def by blast

      moreover have "trail_false_cls \<Gamma>\<^sub>G D\<^sub>G"
      proof -
        have "is_ground_cls D"
          using \<open>D = cls_of_gcls D\<^sub>G\<close> by simp
        hence "D \<cdot> \<gamma> = D"
          by simp
        hence "trail_false_cls \<Gamma> D"
          using conflictI by argo

        thus ?thesis
          unfolding \<Gamma>_def D_def
          unfolding trail_false_cls_nonground_iff_trail_false_cls_ground .
      qed
      ultimately show ?thesis by metis
    qed
  qed

  have nex_conflict_if_alread_in_conflict: "\<C>\<^sub>G = Some C\<^sub>G \<Longrightarrow> \<not> Ex (scl_fol.conflict N \<beta> S)" for C\<^sub>G
    unfolding S_def \<C>_def by (simp add: scl_fol.conflict.simps)

  have nex_conflict_if_no_clause_could_propagate_comp:
    "\<not> Ex (scl_fol.conflict N \<beta> ((lit_of_glit L\<^sub>G, None) # \<Gamma>, U, \<C>))"
    if
      nex_false_clause_wrt_\<Gamma>\<^sub>G: "\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)" and
      ball_lt_atm_L\<^sub>G: "\<forall>x \<in> trail_atoms \<Gamma>\<^sub>G. x \<prec>\<^sub>t atm_of L\<^sub>G" and
      nex_clause_that_propagate: "\<not> (\<exists>C|\<in>|N\<^sub>G |\<union>| U\<^sub>G. clause_could_propagate \<Gamma>\<^sub>G C (- L\<^sub>G))"
    for L\<^sub>G
  proof (intro notI, elim exE)
    fix S'' :: "('f, 'v) SCL_FOL.state"
    assume "scl_fol.conflict N \<beta> ((lit_of_glit L\<^sub>G, None) # \<Gamma>, U, \<C>) S''"
    thus "False"
    proof (cases N \<beta> "((lit_of_glit L\<^sub>G, None) # \<Gamma>, U, \<C>)" S'' rule: scl_fol.conflict.cases)
      case (conflictI D \<gamma>)

      obtain D\<^sub>G where "D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and D_def: "D = cls_of_gcls D\<^sub>G"
        using \<open>D |\<in>| N |\<union>| U\<close> N_def U_def by blast

      have "(lit_of_glit L\<^sub>G :: ('f, 'v) term literal, None) # \<Gamma> = (trail_of_gtrail ((L\<^sub>G, None) # \<Gamma>\<^sub>G) :: ('f, 'v) SCL_FOL.trail)"
        by (simp add: \<Gamma>_def)

      moreover have "D \<cdot> \<gamma> = cls_of_gcls D\<^sub>G"
        unfolding D_def by simp

      ultimately have "trail_false_cls (trail_of_gtrail ((L\<^sub>G, None) # \<Gamma>\<^sub>G) :: ('f, 'v) SCL_FOL.trail) (cls_of_gcls D\<^sub>G)"
        using \<open>trail_false_cls ((lit_of_glit L\<^sub>G, None) # \<Gamma>) (D \<cdot> \<gamma>)\<close> by argo

      hence "trail_false_cls ((L\<^sub>G, None) # \<Gamma>\<^sub>G) D\<^sub>G"
        using trail_false_cls_nonground_iff_trail_false_cls_ground by blast

      hence "trail_false_cls \<Gamma>\<^sub>G {#K\<^sub>G \<in># D\<^sub>G. K\<^sub>G \<noteq> - L\<^sub>G#}"
        unfolding trail_false_cls_def trail_false_lit_def
        by auto

      moreover have "ord_res.is_maximal_lit (- L\<^sub>G) D\<^sub>G"
        unfolding linorder_lit.is_maximal_in_mset_iff
      proof (intro conjI ballI impI)
        show "- L\<^sub>G \<in># D\<^sub>G"
          using \<open>D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close> \<open>trail_false_cls ((L\<^sub>G, None) # \<Gamma>\<^sub>G) D\<^sub>G\<close> subtrail_falseI
            nex_false_clause_wrt_\<Gamma>\<^sub>G
          by blast
      next
        fix K\<^sub>G assume "K\<^sub>G \<in># D\<^sub>G" and "K\<^sub>G \<noteq> - L\<^sub>G"
        hence "trail_false_lit \<Gamma>\<^sub>G K\<^sub>G"
          using \<open>trail_false_cls \<Gamma>\<^sub>G {#K\<^sub>G \<in># D\<^sub>G. K\<^sub>G \<noteq> - L\<^sub>G#}\<close>
          unfolding trail_false_cls_def by simp
        hence "atm_of K\<^sub>G \<in> trail_atoms \<Gamma>\<^sub>G"
          unfolding trail_false_lit_def
          by (metis atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_atoms_def)
        hence "atm_of K\<^sub>G \<prec>\<^sub>t atm_of L\<^sub>G"
          using ball_lt_atm_L\<^sub>G by metis
        hence "K\<^sub>G \<prec>\<^sub>l - L\<^sub>G"
          by (cases L\<^sub>G; cases K\<^sub>G) simp_all
        thus "\<not> - L\<^sub>G \<prec>\<^sub>l K\<^sub>G"
          by order
      qed

      ultimately have "clause_could_propagate \<Gamma>\<^sub>G D\<^sub>G (- L\<^sub>G)"
        unfolding clause_could_propagate_def by argo

      hence False
        using \<open>D\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close> nex_clause_that_propagate by metis

      thus ?thesis .
    qed
  qed

  show ?thesis
    using \<open>scl_fol_1 N\<^sub>G S\<^sub>G S\<^sub>G'\<close> unfolding S\<^sub>G_def S\<^sub>G'_def
  proof (cases N\<^sub>G "(\<Gamma>\<^sub>G, U\<^sub>G, \<C>\<^sub>G)" "(\<Gamma>\<^sub>G', U\<^sub>G', \<C>\<^sub>G')" rule: scl_fol_1.cases)
    case step_hyps: (decide_neg A\<^sub>G)

    define A :: "('f, 'v) term" where
      "A = term_of_gterm A\<^sub>G"

    let ?f = "(\<lambda>(L, opt). (lit_of_glit L, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L, Var)) opt))"
    have "\<Gamma>' = map ?f \<Gamma>\<^sub>G'"
      unfolding \<Gamma>'_def ..
    also have "\<dots> = map ?f ((Neg A\<^sub>G, None) # \<Gamma>\<^sub>G)"
      unfolding \<open>\<Gamma>\<^sub>G' = (Neg A\<^sub>G, None) # \<Gamma>\<^sub>G\<close> ..
    also have "\<dots> = ?f (Neg A\<^sub>G, None) # map ?f \<Gamma>\<^sub>G"
      unfolding list.map ..
    also have "\<dots> = ?f (Neg A\<^sub>G, None) # \<Gamma>"
      unfolding \<Gamma>_def ..
    also have "\<dots> = (lit_of_glit (Neg A\<^sub>G), None) # \<Gamma>"
      unfolding prod.case option.map ..
    also have "\<dots> = (Neg (term_of_gterm A\<^sub>G), None) # \<Gamma>"
      unfolding lit_of_glit_def literal.map ..
    also have "\<dots> = (Neg A, None) # \<Gamma>"
      unfolding A_def ..
    finally have "\<Gamma>' = decide_lit (Neg A) # \<Gamma>"
      unfolding decide_lit_def .

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)\<close> nex_conflict_if_nbex_trail_false by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.decide N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = None\<close> option.map
      proof (rule scl_fol.decideI')
        show "is_ground_lit (Neg A \<cdot>l Var)"
          by (simp add: A_def)
      next
        have "\<forall>x \<in> trail_atoms \<Gamma>\<^sub>G. x \<prec>\<^sub>t A\<^sub>G"
          using step_hyps linorder_trm.is_least_in_set_iff by simp
        hence "\<not> trail_defined_atm \<Gamma>\<^sub>G A\<^sub>G"
          unfolding trail_defined_atm_def
          by (metis linorder_trm.less_irrefl trail_atoms_def)
        hence "A\<^sub>G \<notin> atm_of ` fst ` set \<Gamma>\<^sub>G"
          unfolding trail_defined_atm_def .
        hence "term_of_gterm A\<^sub>G \<notin> term_of_gterm ` atm_of ` fst ` set \<Gamma>\<^sub>G"
          using inj_image_mem_iff inj_term_of_gterm by metis
        hence "term_of_gterm A\<^sub>G \<notin> set (map (\<lambda>x. term_of_gterm (atm_of (fst x))) \<Gamma>\<^sub>G)"
          unfolding image_set list.map_comp comp_def .
        hence "A \<notin> set (map (\<lambda>x. atm_of (lit_of_glit (fst x))) \<Gamma>\<^sub>G)"
          unfolding A_def atm_of_lit_of_glit_conv .
        hence "A \<notin> atm_of ` fst ` set \<Gamma>"
          unfolding image_set list.map_comp comp_def \<Gamma>_def fst_case_prod_simp .
        hence "\<not> trail_defined_atm \<Gamma> A"
          unfolding trail_defined_atm_def .
        thus "\<not> trail_defined_lit \<Gamma> (Neg A \<cdot>l Var)"
          by (simp add: trail_defined_lit_iff_trail_defined_atm)
      next
        have "A\<^sub>G \<in> atoms_of_clause_set N\<^sub>G"
          using step_hyps linorder_trm.is_least_in_set_iff by simp
        hence "A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G"
          using ball_le_\<beta>\<^sub>G by metis
        moreover have "gterm_of_term A = A\<^sub>G"
          by (simp add: A_def)
        moreover have "gterm_of_term \<beta> = \<beta>\<^sub>G"
          by (simp add: \<beta>_def)
        ultimately have "gterm_of_term A \<preceq>\<^sub>t gterm_of_term \<beta>"
          by argo
        thus "less_B\<^sup>=\<^sup>= (atm_of (Neg A) \<cdot>a Var) \<beta>"
          using inj_term_of_gterm[THEN injD]
          by (auto simp: less_B_def A_def \<beta>_def)
      next
        show "\<Gamma>' = trail_decide \<Gamma> (Neg A \<cdot>l Var)"
          using \<open>\<Gamma>' = decide_lit (Neg A) # \<Gamma>\<close>
          unfolding subst_lit_id_subst .
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"

      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
      proof -
        have "\<not> Ex (scl_fol.conflict N \<beta> ((lit_of_glit (Neg A\<^sub>G), None) # \<Gamma>, U, \<C>))"
        proof (rule nex_conflict_if_no_clause_could_propagate_comp)
          show "\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)"
            using \<open>\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)\<close> .
        next
          show "\<forall>x\<in>trail_atoms \<Gamma>\<^sub>G. x \<prec>\<^sub>t atm_of (Neg A\<^sub>G)"
            unfolding literal.sel
            using step_hyps linorder_trm.is_least_in_set_iff by simp
        next
          show "\<not> (\<exists>C|\<in>|N\<^sub>G |\<union>| U\<^sub>G. clause_could_propagate \<Gamma>\<^sub>G C (- Neg A\<^sub>G))"
            using \<open>\<not> (\<exists>C|\<in>|N\<^sub>G |\<union>| U\<^sub>G. clause_could_propagate \<Gamma>\<^sub>G C (Pos A\<^sub>G))\<close> by simp
        qed
        moreover have "lit_of_glit (Neg A\<^sub>G) = Neg A"
          unfolding A_def lit_of_glit_def literal.map ..
        ultimately show ?thesis
          unfolding S'_def \<open>\<Gamma>' = decide_lit (Neg A) # \<Gamma>\<close> decide_lit_def
          using \<C>'_def \<C>_def \<open>U' = U\<close> step_hyps(1) step_hyps(3) by argo
      qed

      ultimately show False
        by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (decide_pos A\<^sub>G)

    define A :: "('f, 'v) term" where
      "A = term_of_gterm A\<^sub>G"

    let ?f = "(\<lambda>(L, opt). (lit_of_glit L, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L, Var)) opt))"
    have "\<Gamma>' = map ?f \<Gamma>\<^sub>G'"
      unfolding \<Gamma>'_def ..
    also have "\<dots> = map ?f ((Pos A\<^sub>G, None) # \<Gamma>\<^sub>G)"
      unfolding \<open>\<Gamma>\<^sub>G' = (Pos A\<^sub>G, None) # \<Gamma>\<^sub>G\<close> ..
    also have "\<dots> = ?f (Pos A\<^sub>G, None) # map ?f \<Gamma>\<^sub>G"
      unfolding list.map ..
    also have "\<dots> = ?f (Pos A\<^sub>G, None) # \<Gamma>"
      unfolding \<Gamma>_def ..
    also have "\<dots> = (lit_of_glit (Pos A\<^sub>G), None) # \<Gamma>"
      unfolding prod.case option.map ..
    also have "\<dots> = (Pos (term_of_gterm A\<^sub>G), None) # \<Gamma>"
      unfolding lit_of_glit_def literal.map ..
    also have "\<dots> = (Pos A, None) # \<Gamma>"
      unfolding A_def ..
    finally have "\<Gamma>' = decide_lit (Pos A) # \<Gamma>"
      unfolding decide_lit_def .

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)\<close> nex_conflict_if_nbex_trail_false by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.decide N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = None\<close> option.map
      proof (rule scl_fol.decideI')
        show "is_ground_lit (Pos A \<cdot>l Var)"
          by (simp add: A_def)
      next
        have "\<forall>x \<in> trail_atoms \<Gamma>\<^sub>G. x \<prec>\<^sub>t A\<^sub>G"
          using step_hyps linorder_trm.is_least_in_set_iff by simp
        hence "\<not> trail_defined_atm \<Gamma>\<^sub>G A\<^sub>G"
          unfolding trail_defined_atm_def
          by (metis linorder_trm.less_irrefl trail_atoms_def)
        hence "A\<^sub>G \<notin> atm_of ` fst ` set \<Gamma>\<^sub>G"
          unfolding trail_defined_atm_def .
        hence "term_of_gterm A\<^sub>G \<notin> term_of_gterm ` atm_of ` fst ` set \<Gamma>\<^sub>G"
          using inj_image_mem_iff inj_term_of_gterm by metis
        hence "term_of_gterm A\<^sub>G \<notin> set (map (\<lambda>x. term_of_gterm (atm_of (fst x))) \<Gamma>\<^sub>G)"
          unfolding image_set list.map_comp comp_def .
        hence "A \<notin> set (map (\<lambda>x. atm_of (lit_of_glit (fst x))) \<Gamma>\<^sub>G)"
          unfolding A_def atm_of_lit_of_glit_conv .
        hence "A \<notin> atm_of ` fst ` set \<Gamma>"
          unfolding image_set list.map_comp comp_def \<Gamma>_def fst_case_prod_simp .
        hence "\<not> trail_defined_atm \<Gamma> A"
          unfolding trail_defined_atm_def .
        thus "\<not> trail_defined_lit \<Gamma> (Pos A \<cdot>l Var)"
          by (simp add: trail_defined_lit_iff_trail_defined_atm)
      next
        have "A\<^sub>G \<in> atoms_of_clause_set N\<^sub>G"
          using step_hyps linorder_trm.is_least_in_set_iff by simp
        hence "A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G"
          using ball_le_\<beta>\<^sub>G by metis
        moreover have "gterm_of_term A = A\<^sub>G"
          by (simp add: A_def)
        moreover have "gterm_of_term \<beta> = \<beta>\<^sub>G"
          by (simp add: \<beta>_def)
        ultimately have "gterm_of_term A \<preceq>\<^sub>t gterm_of_term \<beta>"
          by argo
        thus "less_B\<^sup>=\<^sup>= (atm_of (Pos A) \<cdot>a Var) \<beta>"
          using inj_term_of_gterm[THEN injD]
          by (auto simp: less_B_def A_def \<beta>_def)
      next
        show "\<Gamma>' = trail_decide \<Gamma> (Pos A \<cdot>l Var)"
          using \<open>\<Gamma>' = decide_lit (Pos A) # \<Gamma>\<close>
          unfolding subst_lit_id_subst .
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"
      
      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
      proof -
        have "\<not> Ex (scl_fol.conflict N \<beta> ((lit_of_glit (Pos A\<^sub>G), None) # \<Gamma>, U, \<C>))"
        proof (rule nex_conflict_if_no_clause_could_propagate_comp)
          show "\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)"
            using \<open>\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)\<close> .
        next
          show "\<forall>x\<in>trail_atoms \<Gamma>\<^sub>G. x \<prec>\<^sub>t atm_of (Pos A\<^sub>G)"
            unfolding literal.sel
            using step_hyps linorder_trm.is_least_in_set_iff by simp
        next
          show "\<not> (\<exists>C|\<in>|N\<^sub>G |\<union>| U\<^sub>G. clause_could_propagate \<Gamma>\<^sub>G C (- Pos A\<^sub>G))"
            using \<open>\<not> (\<exists>D|\<in>|N\<^sub>G |\<union>| U\<^sub>G. clause_could_propagate \<Gamma>\<^sub>G D (Neg A\<^sub>G))\<close> by simp
        qed
        moreover have "lit_of_glit (Pos A\<^sub>G) = Pos A"
          unfolding A_def lit_of_glit_def literal.map ..
        ultimately show ?thesis
          unfolding S'_def \<open>\<Gamma>' = decide_lit (Pos A) # \<Gamma>\<close> decide_lit_def
          using \<C>'_def \<C>_def \<open>U' = U\<close> step_hyps(1) step_hyps(3) by argo
      qed

      ultimately show False by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (propagate_pos A\<^sub>G C\<^sub>G)

    have "C\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G" and "clause_could_propagate \<Gamma>\<^sub>G C\<^sub>G (Pos A\<^sub>G)"
      using step_hyps linorder_cls.is_least_in_fset_iff by simp_all

    define A :: "('f, 'v) term" where
      "A = term_of_gterm A\<^sub>G"

    define C :: "('f, 'v) term clause" where
      "C = cls_of_gcls C\<^sub>G"

    have "ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G" and "trail_false_cls \<Gamma>\<^sub>G {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}"
      using \<open>clause_could_propagate \<Gamma>\<^sub>G C\<^sub>G (Pos A\<^sub>G)\<close>
      unfolding clause_could_propagate_def by metis+

    then obtain C\<^sub>G' where "C\<^sub>G = add_mset (Pos A\<^sub>G) C\<^sub>G'"
      by (metis linorder_lit.is_maximal_in_mset_iff mset_add)

    define C' :: "('f, 'v) term clause" where
      "C' = cls_of_gcls C\<^sub>G'"

    let ?f = "(\<lambda>(L, opt). (lit_of_glit L, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L, Var)) opt))"
    have "\<Gamma>' = map ?f \<Gamma>\<^sub>G'"
      unfolding \<Gamma>'_def ..
    also have "\<dots> = map ?f ((Pos A\<^sub>G, Some {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}) # \<Gamma>\<^sub>G)"
      unfolding \<open>\<Gamma>\<^sub>G' = (Pos A\<^sub>G, Some {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}) # \<Gamma>\<^sub>G\<close> ..
    also have "\<dots> = ?f (Pos A\<^sub>G, Some {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}) # map ?f \<Gamma>\<^sub>G"
      unfolding list.map ..
    also have "\<dots> = ?f (Pos A\<^sub>G, Some {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}) # \<Gamma>"
      unfolding \<Gamma>_def ..
    also have "\<dots> = (lit_of_glit (Pos A\<^sub>G),
      Some (cls_of_gcls {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}, lit_of_glit (Pos A\<^sub>G), Var)) # \<Gamma>"
      unfolding prod.case option.map ..
    also have "\<dots> = (Pos (term_of_gterm A\<^sub>G),
      Some (cls_of_gcls {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}, Pos (term_of_gterm A\<^sub>G), Var)) # \<Gamma>"
      unfolding lit_of_glit_def literal.map ..
    also have "\<dots> = (Pos A, Some (cls_of_gcls {#L \<in># C\<^sub>G. L \<noteq> Pos A\<^sub>G#}, Pos A, Var)) # \<Gamma>"
      unfolding A_def ..
    also have "\<dots> = (Pos A, Some (cls_of_gcls {#L \<in># C\<^sub>G. lit_of_glit L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      by (metis A_def glit_of_lit_lit_of_glit lit_of_glit_def literal.simps(9))
    also have "\<dots> = (Pos A, Some ({#L \<in># cls_of_gcls C\<^sub>G. L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      unfolding cls_of_gcls_def
      unfolding image_mset_filter_mset_swap[of "lit_of_glit" "\<lambda>L. L \<noteq> Pos A" C\<^sub>G]
      unfolding cls_of_gcls_def[symmetric] ..
    also have "\<dots> = (Pos A \<cdot>l Var, Some ({#L \<in># cls_of_gcls C\<^sub>G. L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      by simp
    also have "\<dots> = (Pos A \<cdot>l Var, Some ({#L \<in># C. L \<noteq> Pos A#}, Pos A, Var)) # \<Gamma>"
      unfolding C_def ..
    finally have "\<Gamma>' = propagate_lit (Pos A) {#L \<in># C. L \<noteq> Pos A#} Var # \<Gamma>"
      unfolding propagate_lit_def .

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<not> fBex (N\<^sub>G |\<union>| U\<^sub>G) (trail_false_cls \<Gamma>\<^sub>G)\<close> nex_conflict_if_nbex_trail_false by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.propagate N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = None\<close> option.map
      proof (rule scl_fol.propagateI')
        show "C |\<in>| N |\<union>| U"
          using \<open>C\<^sub>G |\<in>| N\<^sub>G |\<union>| U\<^sub>G\<close>
          unfolding C_def N_def U_def by blast
      next
        have "C = cls_of_gcls C\<^sub>G"
          unfolding C_def ..
        also have "\<dots> = cls_of_gcls (add_mset (Pos A\<^sub>G) C\<^sub>G')"
          unfolding \<open>C\<^sub>G = add_mset (Pos A\<^sub>G) C\<^sub>G'\<close> ..
        also have "\<dots> = add_mset (lit_of_glit (Pos A\<^sub>G)) (cls_of_gcls C\<^sub>G')"
          unfolding cls_of_gcls_def by simp
        also have "\<dots> = add_mset (lit_of_glit (Pos A\<^sub>G)) C'"
          unfolding C'_def ..
        also have "\<dots> = add_mset (Pos (term_of_gterm A\<^sub>G)) C'"
          unfolding lit_of_glit_def literal.map ..
        also have "\<dots> = add_mset (Pos A) C'"
          unfolding A_def ..
        finally show "C = add_mset (Pos A) C'" .

        show "is_ground_cls (C \<cdot> Var)"
          by (simp add: C_def)

        have "A\<^sub>G \<in> atoms_of_clause_set N\<^sub>G"
          using step_hyps linorder_trm.is_least_in_set_iff by simp
        hence "A\<^sub>G \<preceq>\<^sub>t \<beta>\<^sub>G"
          using ball_le_\<beta>\<^sub>G by metis
        moreover have "gterm_of_term A = A\<^sub>G"
          by (simp add: A_def)
        moreover have "gterm_of_term \<beta> = \<beta>\<^sub>G"
          by (simp add: \<beta>_def)
        ultimately have "gterm_of_term A \<preceq>\<^sub>t gterm_of_term \<beta>"
          by argo
        hence "less_B\<^sup>=\<^sup>= A \<beta>"
          by (auto simp: less_B_def A_def \<beta>_def)

        show "\<forall>K\<in>#C \<cdot> Var. less_B\<^sup>=\<^sup>= (atm_of K) \<beta>"
        proof (intro ballI)
          fix K :: "('f, 'v) Term.term literal"
          assume "K \<in># C \<cdot> Var"
          hence "K \<in># C"
            by simp
          then obtain K\<^sub>G where "K\<^sub>G \<in># C\<^sub>G" and K_def: "K = lit_of_glit K\<^sub>G"
            unfolding C_def cls_of_gcls_def by blast

          have "K\<^sub>G \<preceq>\<^sub>l Pos A\<^sub>G"
            using \<open>ord_res.is_maximal_lit (Pos A\<^sub>G) C\<^sub>G\<close> \<open>K\<^sub>G \<in># C\<^sub>G\<close>
            using linorder_lit.is_maximal_in_mset_iff by auto

          hence "atm_of K\<^sub>G \<preceq>\<^sub>t A\<^sub>G"
            by (metis literal.collapse(1) literal.collapse(2) literal.sel(1)
                ord_res.less_lit_simps(1) ord_res.less_lit_simps(4) reflclp_iff)

          hence "less_B\<^sup>=\<^sup>= (atm_of K) A"
            by (auto simp: less_B_def K_def A_def atm_of_lit_of_glit_conv)

          then show "less_B\<^sup>=\<^sup>= (atm_of K) \<beta>"
            using \<open>less_B\<^sup>=\<^sup>= A \<beta>\<close> by order
        qed

        show "{#K \<in># C'. K \<noteq> Pos A#} = {#K \<in># C'. K \<cdot>l Var \<noteq> Pos A \<cdot>l Var#}"
          by simp

        show "{#K \<in># C'. K = Pos A#} = {#K \<in># C'. K \<cdot>l Var = Pos A \<cdot>l Var#}"
          by simp

        have "trail_false_cls \<Gamma>\<^sub>G ({#K\<^sub>G \<in># C\<^sub>G'. K\<^sub>G \<noteq> Pos A\<^sub>G#})"
          using \<open>C\<^sub>G = add_mset (Pos A\<^sub>G) C\<^sub>G'\<close> \<open>trail_false_cls \<Gamma>\<^sub>G {#K \<in># C\<^sub>G. K \<noteq> Pos A\<^sub>G#}\<close> by fastforce

        hence "trail_false_cls \<Gamma> (cls_of_gcls {#K\<^sub>G \<in># C\<^sub>G'. K\<^sub>G \<noteq> Pos A\<^sub>G#} :: ('f, 'v) term clause)"
          unfolding \<Gamma>_def
          using trail_false_cls_nonground_iff_trail_false_cls_ground by blast

        moreover have "(cls_of_gcls {#K\<^sub>G \<in># C\<^sub>G'. K\<^sub>G \<noteq> Pos A\<^sub>G#} :: ('f, 'v) term clause) = {#K \<in># C'. K \<noteq> Pos A#}"
        proof -
          have "{#K \<in># C'. K \<noteq> Pos A#} = cls_of_gcls {#K \<in># C\<^sub>G'. lit_of_glit K \<noteq> Pos A#}"
            unfolding C'_def cls_of_gcls_def
            by (simp add: filter_mset_neq)
          also have "\<dots> = cls_of_gcls {#K\<^sub>G \<in># C\<^sub>G'. K\<^sub>G \<noteq> Pos A\<^sub>G#}"
            unfolding A_def
            by (metis glit_of_lit_lit_of_glit lit_of_glit_def literal.simps(9))
          finally show ?thesis
            by argo
        qed

        ultimately show "trail_false_cls \<Gamma> ({#K \<in># C'. K \<noteq> Pos A#} \<cdot> Var)"
          by simp

        have "\<forall>x \<in> trail_atoms \<Gamma>\<^sub>G. x \<prec>\<^sub>t A\<^sub>G"
          using step_hyps linorder_trm.is_least_in_set_iff by simp
        hence "\<not> trail_defined_atm \<Gamma>\<^sub>G A\<^sub>G"
          unfolding trail_defined_atm_def
          by (metis linorder_trm.less_irrefl trail_atoms_def)
        hence "A\<^sub>G \<notin> atm_of ` fst ` set \<Gamma>\<^sub>G"
          unfolding trail_defined_atm_def .
        hence "term_of_gterm A\<^sub>G \<notin> term_of_gterm ` atm_of ` fst ` set \<Gamma>\<^sub>G"
          using inj_image_mem_iff inj_term_of_gterm by metis
        hence "term_of_gterm A\<^sub>G \<notin> set (map (\<lambda>x. term_of_gterm (atm_of (fst x))) \<Gamma>\<^sub>G)"
          unfolding image_set list.map_comp comp_def .
        hence "A \<notin> set (map (\<lambda>x. atm_of (lit_of_glit (fst x))) \<Gamma>\<^sub>G)"
          unfolding A_def atm_of_lit_of_glit_conv .
        hence "A \<notin> atm_of ` fst ` set \<Gamma>"
          unfolding image_set list.map_comp comp_def \<Gamma>_def fst_case_prod_simp .
        hence "\<not> trail_defined_atm \<Gamma> A"
          unfolding trail_defined_atm_def .
        thus "\<not> trail_defined_lit \<Gamma> (Pos A \<cdot>l Var)"
          by (simp add: trail_defined_lit_iff_trail_defined_atm)

        have FOO: "set_mset (add_mset (Pos A) {#K \<in># C'. K = Pos A#}) = {Pos A}"
          by auto
        have "is_unifier Var (atm_of ` set_mset (add_mset (Pos A) {#K \<in># C'. K = Pos A#}))"
          unfolding FOO
          by (simp add: SCL_FOL.is_unifier_def)
        hence "is_unifiers Var {atm_of ` set_mset (add_mset (Pos A) {#K \<in># C'. K = Pos A#})}"
          unfolding SCL_FOL.is_unifiers_def by simp
        thus "SCL_FOL.is_imgu Var {atm_of ` set_mset (add_mset (Pos A) {#K \<in># C'. K = Pos A#})}"
          unfolding SCL_FOL.is_imgu_def by simp

        show "\<Gamma>' = trail_propagate \<Gamma> (Pos A \<cdot>l Var) ({#K \<in># C'. K \<noteq> Pos A#} \<cdot> Var) Var"
          using \<open>\<Gamma>' = propagate_lit (Pos A) {#L \<in># C. L \<noteq> Pos A#} Var # \<Gamma>\<close>
          using \<open>C = add_mset (Pos A) C'\<close>
          by simp
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.decide N \<beta> S S'"
      thus False
        unfolding S_def S'_def
      proof (cases N \<beta> "(\<Gamma>, U, \<C>)" "(\<Gamma>', U', \<C>')" rule: scl_fol.decide.cases)
        case (decideI L \<gamma>)
        show False
          using \<open>\<Gamma>' = decide_lit (L \<cdot>l \<gamma>) # \<Gamma>\<close>
          using \<open>\<Gamma>' = propagate_lit (Pos A) {#L \<in># C. L \<noteq> Pos A#} Var # \<Gamma>\<close>
          unfolding decide_lit_def propagate_lit_def
          by blast
      qed
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (conflict C\<^sub>G)

    have "\<Gamma>' = \<Gamma>"
      unfolding \<Gamma>'_def \<open>\<Gamma>\<^sub>G' = \<Gamma>\<^sub>G\<close> \<Gamma>_def ..

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "scl_fol.conflict N \<beta> S S'"
      unfolding S_def S'_def \<open>\<Gamma>' = \<Gamma>\<close> \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = None\<close> \<open>\<C>\<^sub>G' = Some C\<^sub>G\<close> option.map
    proof (rule scl_fol.conflictI)
      show "cls_of_gcls C\<^sub>G |\<in>| N |\<union>| U"
        unfolding N_def U_def
        by (metis fimage_funion finsert_fimage finsert_iff linorder_cls.is_least_in_fset_ffilterD(1)
            step_hyps(5))
    next
      show "is_ground_cls (cls_of_gcls C\<^sub>G \<cdot> (Var::'v \<Rightarrow> ('f, _) Term.term))"
        by simp
    next
      have "trail_false_cls \<Gamma>\<^sub>G C\<^sub>G"
        using linorder_cls.is_least_in_fset_iff step_hyps(5) by force

      thus "trail_false_cls \<Gamma> (cls_of_gcls C\<^sub>G \<cdot> Var)"
        using \<Gamma>'_def \<open>\<Gamma>' = \<Gamma>\<close> step_hyps(2) trail_false_cls_nonground_iff_trail_false_cls_ground
        by simp
    qed

    thus ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (skip L\<^sub>G C\<^sub>G n\<^sub>G)

    have "\<Gamma> = (lit_of_glit L\<^sub>G, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L\<^sub>G, Var)) n\<^sub>G) # \<Gamma>'"
      unfolding \<Gamma>_def \<Gamma>'_def \<open>\<Gamma>\<^sub>G = (L\<^sub>G, n\<^sub>G) # \<Gamma>\<^sub>G'\<close> by auto

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<C>\<^sub>G = Some C\<^sub>G\<close> nex_conflict_if_alread_in_conflict by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.skip N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = U\<close> \<C>_def \<C>'_def \<open>\<C>\<^sub>G = Some C\<^sub>G\<close> \<open>\<C>\<^sub>G' = Some C\<^sub>G\<close> option.map
        unfolding \<open>\<Gamma> = (lit_of_glit L\<^sub>G, map_option (\<lambda>C. (cls_of_gcls C, lit_of_glit L\<^sub>G, Var)) n\<^sub>G) # \<Gamma>'\<close>
      proof (rule scl_fol.skipI)
        have "- lit_of_glit L\<^sub>G = lit_of_glit (- L\<^sub>G)"
          by (cases L\<^sub>G) (simp_all add: lit_of_glit_def)
        show "- lit_of_glit L\<^sub>G \<notin># cls_of_gcls C\<^sub>G \<cdot> Var"
          unfolding subst_cls_id_subst
          unfolding \<open>- lit_of_glit L\<^sub>G = lit_of_glit (- L\<^sub>G)\<close>
          unfolding cls_of_gcls_def
          using \<open>- L\<^sub>G \<notin># C\<^sub>G\<close> inj_image_mset_mem_iff[OF inj_lit_of_glit]
          by metis
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"

      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
        unfolding S'_def \<C>'_def \<open>\<C>\<^sub>G' = Some C\<^sub>G\<close> by (simp add: scl_fol.conflict.simps)

      ultimately show False
        by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (resolve L\<^sub>G C\<^sub>G \<Gamma>\<^sub>G'' K\<^sub>G D\<^sub>G)

    have "\<Gamma>' = \<Gamma>"
      unfolding \<Gamma>'_def \<open>\<Gamma>\<^sub>G' = \<Gamma>\<^sub>G\<close> \<Gamma>_def ..

    have "U' = U"
      unfolding U'_def \<open>U\<^sub>G' = U\<^sub>G\<close> U_def ..

    have "\<C> = Some (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G), Var)"
      unfolding \<C>_def
      unfolding \<open>\<C>\<^sub>G = Some (add_mset K\<^sub>G D\<^sub>G)\<close> \<open>\<C>\<^sub>G' = Some (C\<^sub>G + D\<^sub>G)\<close> option.map
      by (simp add: cls_of_gcls_def)

    have "\<C>' = Some (cls_of_gcls C\<^sub>G + cls_of_gcls D\<^sub>G, Var)"
      unfolding \<C>'_def \<open>\<C>\<^sub>G' = Some (C\<^sub>G + D\<^sub>G)\<close> option.map
      by (simp add: cls_of_gcls_def)
    hence "\<C>' = Some ((cls_of_gcls D\<^sub>G \<cdot> Var + cls_of_gcls C\<^sub>G \<cdot> Var) \<cdot> Var, Var)"
      by simp

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<C>\<^sub>G = Some (add_mset K\<^sub>G D\<^sub>G)\<close> nex_conflict_if_alread_in_conflict by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.resolve N \<beta> S S'"
        unfolding S_def S'_def \<open>\<Gamma>' = \<Gamma>\<close> \<open>U' = U\<close>
        unfolding \<open>\<C> = Some (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G), Var)\<close>
        unfolding \<open>\<C>' = Some ((cls_of_gcls D\<^sub>G \<cdot> Var + cls_of_gcls C\<^sub>G \<cdot> Var) \<cdot> Var, Var)\<close>
      proof (rule scl_fol.resolveI)
        show "\<Gamma> = trail_propagate (trail_of_gtrail \<Gamma>\<^sub>G'') (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G) Var"
          unfolding \<Gamma>_def \<open>\<Gamma>\<^sub>G = (L\<^sub>G, Some C\<^sub>G) # \<Gamma>\<^sub>G''\<close> list.map prod.case
          by (simp add: propagate_lit_def)
      next
        show "lit_of_glit L\<^sub>G \<cdot>l Var = - (lit_of_glit K\<^sub>G \<cdot>l Var)"
          unfolding subst_lit_id_subst
          using \<open>L\<^sub>G = - K\<^sub>G\<close>
          by (metis atm_of_eq_atm_of atm_of_lit_of_glit_conv glit_of_lit_lit_of_glit uminus_not_id')
      next
        show "SCL_FOL.is_renaming Var"
          by simp
      next
        show "SCL_FOL.is_renaming Var"
          by simp
      next
        show "vars_cls (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G) \<cdot> Var) \<inter>
          vars_cls (add_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G) \<cdot> Var) = {}"
          by simp
      next
        show "SCL_FOL.is_imgu Var {{atm_of (lit_of_glit K\<^sub>G) \<cdot>a Var, atm_of (lit_of_glit L\<^sub>G) \<cdot>a Var}}"
          by (simp add: \<open>L\<^sub>G = - K\<^sub>G\<close> atm_of_lit_of_glit_conv SCL_FOL.is_imgu_def
              SCL_FOL.is_unifiers_def SCL_FOL.is_unifier_def)
      next
        show "is_grounding_merge Var
          (vars_cls (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G) \<cdot> Var))
          (rename_subst_domain Var Var)
          (vars_cls (add_mset (lit_of_glit L\<^sub>G) (cls_of_gcls C\<^sub>G) \<cdot> Var))
          (rename_subst_domain Var Var)"
          by (simp add: is_grounding_merge_def)
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.conflict N \<beta> S' S''"

      moreover have "\<nexists>S''. scl_fol.conflict N \<beta> S' S''"
        unfolding S'_def \<C>'_def \<open>\<C>\<^sub>G' = Some (C\<^sub>G + D\<^sub>G)\<close> by (simp add: scl_fol.conflict.simps)

      ultimately show False
        by metis
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  next
    case step_hyps: (backjump L\<^sub>G K\<^sub>G D\<^sub>G)

    have "U' = finsert (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G)) U"
      unfolding U_def U'_def \<open>U\<^sub>G' = finsert (add_mset K\<^sub>G D\<^sub>G) U\<^sub>G\<close>
      by (simp add: cls_of_gcls_def)

    have "\<C> = Some (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G), Var)"
      unfolding \<C>_def \<open>\<C>\<^sub>G = Some (add_mset K\<^sub>G D\<^sub>G)\<close> option.map
      by (simp add: cls_of_gcls_def)

    have "\<C>' = None"
      unfolding \<C>'_def \<open>\<C>\<^sub>G' = None\<close> option.map ..

    have "\<not> Ex (scl_fol.conflict N \<beta> S)"
      using \<open>\<C>\<^sub>G = Some (add_mset K\<^sub>G D\<^sub>G)\<close> nex_conflict_if_alread_in_conflict by metis

    moreover have "scl_fol.reasonable_scl N \<beta> S S'"
      unfolding scl_fol.reasonable_scl_def
    proof (intro conjI impI notI ; (elim exE) ?)
      have "scl_fol.backtrack N \<beta> S S'"
        unfolding S_def S'_def \<open>U' = finsert (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G)) U\<close>
        unfolding \<open>\<C> = Some (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G), Var)\<close>
        unfolding \<open>\<C>' = None\<close>
        sketch (rule scl_fol.backtrackI)
      proof (rule scl_fol.backtrackI)
        show "\<Gamma> = trail_decide ([] @ \<Gamma>') (lit_of_glit L\<^sub>G)"
          unfolding \<Gamma>_def \<Gamma>'_def \<open>\<Gamma>\<^sub>G = (L\<^sub>G, None) # \<Gamma>\<^sub>G'\<close> decide_lit_def
          by simp
      next
        show "lit_of_glit L\<^sub>G = - (lit_of_glit K\<^sub>G \<cdot>l Var)"
          unfolding \<open>L\<^sub>G = - K\<^sub>G\<close>
          by (cases K\<^sub>G) (simp_all add: lit_of_glit_def)
      next
        have "trail_consistent \<Gamma>\<^sub>G"
          using \<open>trail_consistent (fst S\<^sub>G)\<close>[unfolded S\<^sub>G_def prod.sel] .
        hence "\<not> trail_defined_lit \<Gamma>\<^sub>G' L\<^sub>G"
          unfolding \<open>\<Gamma>\<^sub>G = (L\<^sub>G, None) # \<Gamma>\<^sub>G'\<close>
          by (auto elim: trail_consistent.cases)
        hence "\<not> trail_defined_lit \<Gamma>\<^sub>G' K\<^sub>G"
          unfolding \<open>L\<^sub>G = - K\<^sub>G\<close>
          by (simp add: trail_defined_lit_def) 
        hence "\<not> trail_false_lit \<Gamma>\<^sub>G' K\<^sub>G"
          using trail_defined_lit_iff_true_or_false by metis
        hence "\<not> trail_false_cls \<Gamma>\<^sub>G' (add_mset K\<^sub>G D\<^sub>G)"
          by (simp add: trail_false_cls_def)
        hence "\<not> trail_false_cls \<Gamma>' (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G))"
          by (metis (no_types, lifting) \<Gamma>'_def cls_of_gcls_def image_mset_add_mset
              trail_false_cls_nonground_iff_trail_false_cls_ground)
        thus "\<nexists>\<gamma>. is_ground_cls (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G) \<cdot> \<gamma>) \<and>
          trail_false_cls \<Gamma>' (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G) \<cdot> \<gamma>)"
          by simp
      qed

      thus "scl_fol.scl N \<beta> S S'"
        unfolding scl_fol.scl_def by argo
    next
      fix S'' :: "('f, 'v) SCL_FOL.state"
      assume "scl_fol.decide N \<beta> S S'"
      thus False
        unfolding S_def \<open>\<C> = Some (add_mset (lit_of_glit K\<^sub>G) (cls_of_gcls D\<^sub>G), Var)\<close>
        by (auto elim!: scl_fol.decide.cases)
    qed

    ultimately show ?thesis
      unfolding scl_fol.regular_scl_def by argo
  qed
qed


section \<open>SCL(FOL)-0\<close>

lemma "grounding_of_clss (fset (cls_of_gcls |`| N)) = fset (cls_of_gcls |`| N)"
proof (rule scl_fol.grounding_of_clss_ground)
  show "is_ground_clss (fset (cls_of_gcls |`| N::('a, 'b) Term.term literal multiset fset))"
    by (simp add: is_ground_clss_def)
qed

thm scl_fol.correct_termination_regular_scl_run[of "cls_of_gcls |`| N" "term_of_gterm \<beta>" for N \<beta>]

inductive scl_fol_0_step where
  "\<nexists>\<gamma>. state_conflict S = Some ({#}, \<gamma>) \<Longrightarrow>
    \<exists>C |\<in>| N. \<not> trail_true_cls (state_trail S) (cls_of_gcls C) \<Longrightarrow>
    scl_fol.regular_scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) S S' \<Longrightarrow>
    scl_fol_0_step (N, \<beta>, S) (N, \<beta>, S')"

fun scl_fol_0_final :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state \<Rightarrow> bool" where
  "scl_fol_0_final (N, \<beta>, \<Gamma>, U, \<C>) \<longleftrightarrow>
    (\<exists>\<gamma>. \<C> = Some ({#}, \<gamma>)) \<or> (\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C))"

interpretation scl_fol_semantics: semantics where
  step = scl_fol_0_step and
  final = scl_fol_0_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state"
  obtain N \<beta> \<Gamma> U \<C> where
    S_def: "S = (N, \<beta>, \<Gamma>, U, \<C>)"
    by (metis prod.exhaust)

  assume "scl_fol_0_final S"
  hence "(\<exists>\<gamma>. \<C> = Some ({#}, \<gamma>)) \<or> (\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C))"
    unfolding S_def by simp
  hence "\<nexists>S'. scl_fol_0_step S S'"
  proof (elim disjE exE conjE)
    fix \<gamma>
    assume "\<C> = Some ({#}, \<gamma>)"
    thus ?thesis
      by (auto simp: S_def elim: scl_fol_0_step.cases)
  next
    assume "\<forall>C|\<in>|N. trail_true_cls \<Gamma> (cls_of_gcls C)"
    then show ?thesis
      by (auto simp: S_def elim: scl_fol_0_step.cases)
  qed
  thus "finished scl_fol_0_step S"
    by (simp add: finished_def)
qed

end

end
