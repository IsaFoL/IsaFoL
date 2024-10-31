theory Exhaustive_Resolution
  imports Background
begin

section \<open>Function for full resolution\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition ground_resolution where
  "ground_resolution D C CD = ord_res.ground_resolution C D CD"

lemma Uniq_ground_resolution: "\<exists>\<^sub>\<le>\<^sub>1DC. ground_resolution D C DC"
  by (simp add: ground_resolution_def ord_res.unique_ground_resolution)

lemma ground_resolution_terminates: "wfP (ground_resolution D)\<inverse>\<inverse>"
proof (rule wfp_if_convertible_to_wfp)
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

lemma clause_lt_clause_if_max_lit_comp:
  assumes E_max_lit: "linorder_lit.is_maximal_in_mset E L" and L_neg: "is_neg L" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D (- L)"
  shows "D \<prec>\<^sub>c E"
proof -
  have "- L \<prec>\<^sub>l L"
    using L_neg by (cases L) simp_all

  thus ?thesis
    using D_max_lit E_max_lit
    by (metis linorder_lit.multp_if_maximal_less_that_maximal)
qed

lemma eres_lt_if:
  assumes E_max_lit: "ord_res.is_maximal_lit L E" and L_neg: "is_neg L" and
    D_max_lit: "linorder_lit.is_greatest_in_mset D (- L)"
  shows "eres D E \<prec>\<^sub>c E"
proof -
  have "eres D E \<noteq> E"
    unfolding eres_ident_iff not_not ground_resolution_def
  proof (rule ex_ground_resolutionI)
    show "ord_res.is_maximal_lit (Neg (atm_of L)) E"
      using E_max_lit L_neg by (cases L) simp_all
  next
    show "D \<prec>\<^sub>c E"
      using E_max_lit D_max_lit L_neg
      by (metis clause_lt_clause_if_max_lit_comp
          linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
  next
    show "ord_res.is_strictly_maximal_lit (Pos (atm_of L)) D"
      using D_max_lit \<open>is_neg L\<close>
      by (cases L) simp_all
  qed

  thus "eres D E \<prec>\<^sub>c E"
    using eres_le[of D E] by order
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

lemma stronger_lit_in_one_of_resolvents_if_in_eres:
  fixes K L :: "'f gterm literal" and C D :: "'f gclause"
  assumes "eres C D \<noteq> D" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    K_in_eres: "K \<in># eres C D"
  shows "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D \<and> K \<noteq> L "
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

  thus "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D \<and> K \<noteq> L "
  proof (elim disjE)
    assume "K \<in># C'"

    hence "K \<in># C \<and> K \<noteq> - L"
      using C_max_lit[unfolded linorder_lit.is_greatest_in_mset_iff]
      unfolding \<open>C = add_mset (Pos A) C'\<close> \<open>L = Neg A\<close>
      by auto

    thus ?thesis
      by argo
  next
    assume "K \<in># D'"

    hence "K \<in># D \<and> K \<noteq> L "
      unfolding \<open>D = replicate_mset (Suc m) (Neg A) +  D'\<close> \<open>L = Neg A\<close>
      using \<open>Neg A \<notin># D'\<close>
      by auto

    thus ?thesis
      by argo
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

end

end