theory Trail_Induced_Ordering
  imports
    (* Isabelle theories *)
    Main

    (* AFP theories *)
    "List-Index.List_Index"

    (* Local theories *)
    Relation_Extra
begin


definition trail_less_id_id where
  "trail_less_id_id Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i > j \<and> L = Ls ! i \<and> K = Ls ! j)"

definition trail_less_comp_id where
  "trail_less_comp_id Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i > j \<and> L = - (Ls ! i) \<and> K = Ls ! j)"

definition trail_less_id_comp where
  "trail_less_id_comp Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i \<ge> j \<and> L = Ls ! i \<and> K = - (Ls ! j))"

definition trail_less_comp_comp where
  "trail_less_comp_comp Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i > j \<and> L = - (Ls ! i) \<and> K = - (Ls ! j))"

definition trail_less where
  "trail_less Ls L K \<longleftrightarrow> trail_less_id_id Ls L K \<or> trail_less_comp_id Ls L K \<or>
    trail_less_id_comp Ls L K \<or> trail_less_comp_comp Ls L K"

definition trail_less' where
  "trail_less' Ls = (\<lambda>L K.
    (\<exists>i. i < length Ls \<and> L = Ls ! i \<and> K = - (Ls ! i)) \<or>
    (\<exists>i. Suc i < length Ls \<and> L = - (Ls ! Suc i) \<and> K = Ls ! i))\<^sup>+\<^sup>+"

lemma transp_trail_less': "transp (trail_less' Ls)"
proof (rule transpI)
  show "\<And>x y z. trail_less' Ls x y \<Longrightarrow> trail_less' Ls y z \<Longrightarrow> trail_less' Ls x z"
    by (metis (no_types, lifting) trail_less'_def tranclp_trans)
qed

lemma trail_less'_Suc:
  assumes "Suc i < length Ls"
  shows "trail_less' Ls (Ls ! Suc i) (Ls ! i)"
proof -
  have "trail_less' Ls (Ls ! Suc i) (- (Ls ! Suc i))"
    unfolding trail_less'_def
    using assms by blast
  moreover have "trail_less' Ls (- (Ls ! Suc i)) (Ls ! i)"
    by (metis (mono_tags, lifting) assms trail_less'_def tranclp.r_into_trancl)
  ultimately show ?thesis
    using transp_trail_less'[THEN transpD] by auto
qed

lemma trail_less'_comp_Suc_comp:
  assumes "Suc i < length Ls"
  shows "trail_less' Ls (- (Ls ! Suc i)) (- (Ls ! i))"
proof -
  have "trail_less' Ls (- (Ls ! Suc i)) (Ls ! i)"
    unfolding trail_less'_def
    using assms Suc_lessD by blast
  moreover have "trail_less' Ls (Ls ! i) (- (Ls ! i))"
    unfolding trail_less'_def
    using assms Suc_lessD by blast
  ultimately show ?thesis
    using transp_trail_less'[THEN transpD] by auto
qed

lemma trail_less'_id_id: "j < i \<Longrightarrow> i < length Ls \<Longrightarrow> trail_less' Ls (Ls ! i) (Ls ! j)"
proof (induction i arbitrary: j)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
    using trail_less'_Suc
    by (metis Suc_lessD less_Suc_eq transpD transp_trail_less')
qed

lemma trail_less'_comp_comp:
  "j < i \<Longrightarrow> i < length Ls \<Longrightarrow> trail_less' Ls (- (Ls ! i)) (- (Ls ! j))"
proof (induction i arbitrary: j)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
    using trail_less'_comp_Suc_comp
    by (metis Suc_lessD less_Suc_eq transpD transp_trail_less')
qed

lemma trail_less'_id_comp:
  assumes "j < i" and "i < length Ls"
  shows "trail_less' Ls (Ls ! i) (- (Ls ! j))"
proof -
  have "trail_less' Ls (Ls ! j) (- (Ls ! j))"
    unfolding trail_less'_def
    using assms dual_order.strict_trans by blast
  thus ?thesis
    using trail_less'_id_id[OF assms]
    using transp_trail_less'[THEN transpD] by auto
qed

lemma trail_less'_comp_id:
  assumes "j < i" and "i < length Ls"
  shows "trail_less' Ls (- (Ls ! i)) (Ls ! j)"
proof (cases i)
  case 0
  then show ?thesis
    using assms(1) by blast
next
  case (Suc i')
  hence "trail_less' Ls (- Ls ! i) (Ls ! i')"
    unfolding trail_less'_def
    using Suc_lessD assms(2) by blast
  show ?thesis
  proof (cases "i' = j")
    case True
    then show ?thesis
      using \<open>trail_less' Ls (- Ls ! i) (Ls ! i')\<close> by metis
  next
    case False
    hence "trail_less' Ls (Ls ! i') (Ls ! j)"
      by (metis Suc Suc_lessD assms(1) assms(2) less_SucE trail_less'_id_id)
    then show ?thesis
      using \<open>trail_less' Ls (- Ls ! i) (Ls ! i')\<close>
      using transp_trail_less'[THEN transpD] by auto
  qed
qed

lemma trail_less_eq_trail_less':
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "trail_less Ls = trail_less' Ls"
proof (intro ext iffI)
  fix L K
  show "trail_less Ls L K \<Longrightarrow> trail_less' Ls L K"
    unfolding trail_less_def
  proof (elim disjE)
    assume "trail_less_id_id Ls L K"
    thus ?thesis
      using trail_less'_id_id by (metis trail_less_id_id_def)
  next
    show "trail_less_comp_id Ls L K \<Longrightarrow> ?thesis"
      using trail_less'_comp_id by (metis trail_less_comp_id_def)
  next
    show "trail_less_id_comp Ls L K \<Longrightarrow> ?thesis"
      using trail_less'_id_comp
      unfolding trail_less_id_comp_def
      by (metis (mono_tags, lifting) le_eq_less_or_eq trail_less'_def tranclp.r_into_trancl)
  next
    show "trail_less_comp_comp Ls L K \<Longrightarrow> ?thesis"
      using trail_less'_comp_comp
      by (metis trail_less_comp_comp_def)
  qed
next
  fix L K
  show "trail_less' Ls L K \<Longrightarrow> trail_less Ls L K"
    unfolding trail_less'_def
  proof (induction K rule: tranclp_induct)
    case (base K)
    then show ?case
    proof (elim exE conjE disjE)
      fix i assume "i < length Ls" and "L = Ls ! i" and "K = - (Ls ! i)"
      hence "trail_less_id_comp Ls L K"
        by (auto simp: trail_less_id_comp_def)
      thus "trail_less Ls L K"
        by (simp add: trail_less_def)
    next
      fix i assume "Suc i < length Ls" and "L = - (Ls ! Suc i)" and "K = Ls ! i"
      hence "trail_less_comp_id Ls L K"
        unfolding trail_less_comp_id_def
        using Suc_lessD by blast
      thus "trail_less Ls L K"
        by (simp add: trail_less_def)
    qed
  next
    case (step y z)
    from step.hyps(2) show ?case
    proof (elim exE conjE disjE)
      fix i assume "i < length Ls" and "y = Ls ! i" and "z = - (Ls ! i)"

      from step.IH[unfolded trail_less_def] show "trail_less Ls L z"
      proof (elim disjE)
        assume "trail_less_id_id Ls L y"
        hence "trail_less_id_comp Ls L z"
          unfolding trail_less_id_id_def trail_less_id_comp_def
          by (metis \<open>y = Ls ! i\<close> \<open>z = - Ls ! i\<close> less_or_eq_imp_le)
        thus "trail_less Ls L z"
          by (simp add: trail_less_def)
      next
        assume "trail_less_comp_id Ls L y"
        hence "trail_less_comp_comp Ls L z"
          unfolding trail_less_comp_id_def trail_less_comp_comp_def
          by (metis \<open>y = Ls ! i\<close> \<open>z = - Ls ! i\<close>)
        thus "trail_less Ls L z"
          by (simp add: trail_less_def)
      next
        assume "trail_less_id_comp Ls L y"
        hence "trail_less_id_comp Ls L z"
          unfolding trail_less_id_comp_def
          by (metis \<open>i < length Ls\<close> \<open>y = Ls ! i\<close> \<open>z = - Ls ! i\<close> pairwise_distinct)
        thus "trail_less Ls L z"
          by (simp add: trail_less_def)
      next
        assume "trail_less_comp_comp Ls L y"
        hence "trail_less_comp_comp Ls L z"
          unfolding trail_less_comp_comp_def
          by (metis \<open>i < length Ls\<close> \<open>y = Ls ! i\<close> \<open>z = - Ls ! i\<close> pairwise_distinct)
        thus "trail_less Ls L z"
          by (simp add: trail_less_def)
      qed
    next
      fix i assume "Suc i < length Ls" and "y = - Ls ! Suc i" and "z = Ls ! i"

      from step.IH[unfolded trail_less_def] show "trail_less Ls L z"
      proof (elim disjE)
        show "trail_less_id_id Ls L y \<Longrightarrow> trail_less Ls L z"
          by (metis \<open>Suc i < length Ls\<close> \<open>y = - Ls ! Suc i\<close> \<open>z = Ls ! i\<close> not_less_eq
              order_less_imp_not_less pairwise_distinct trail_less_def trail_less_id_id_def)
      next
        show "trail_less_comp_id Ls L y \<Longrightarrow> trail_less Ls L z"
          by (smt (verit, best) \<open>Suc i < length Ls\<close> \<open>y = - Ls ! Suc i\<close> \<open>z = Ls ! i\<close>
              dual_order.strict_trans lessI pairwise_distinct trail_less_comp_id_def trail_less_def)
      next
        assume "trail_less_id_comp Ls L y"
        hence "trail_less_id_id Ls L z"
          unfolding trail_less_def trail_less_id_comp_def trail_less_id_id_def
          by (metis Suc_le_lessD Suc_lessD \<open>Suc i < length Ls\<close> \<open>y = - Ls ! Suc i\<close> \<open>z = Ls ! i\<close>
              pairwise_distinct uminus_uminus_id)
        thus "trail_less Ls L z"
          by (simp add: trail_less_def)
      next
        assume "trail_less_comp_comp Ls L y"
        hence "trail_less_comp_id Ls L z"
          unfolding trail_less_comp_comp_def trail_less_comp_id_def
          by (metis Suc_lessD \<open>Suc i < length Ls\<close> \<open>y = - Ls ! Suc i\<close> \<open>z = Ls ! i\<close> pairwise_distinct
              uminus_uminus_id)
        thus "trail_less Ls L z"
          by (simp add: trail_less_def)
      qed
    qed
  qed
qed




subsection \<open>Examples\<close>

experiment
  fixes L0 L1 L2 :: "'a :: uminus"
begin

lemma "trail_less_id_comp [L2, L1, L0] L2 (- L2)"
  unfolding trail_less_id_comp_def
proof (intro exI conjI)
  show "(0 :: nat) \<le> 0" by presburger
qed simp_all

lemma "trail_less_comp_id [L2, L1, L0] (- L1) L2"
  unfolding trail_less_comp_id_def
proof (intro exI conjI)
  show "(0 :: nat) < 1" by presburger
qed simp_all

lemma "trail_less_id_comp [L2, L1, L0] L1 (- L1)"
  unfolding trail_less_id_comp_def
proof (intro exI conjI)
  show "(1 :: nat) \<le> 1" by presburger
qed simp_all

lemma "trail_less_comp_id [L2, L1, L0] (- L0) L1"
  unfolding trail_less_comp_id_def
proof (intro exI conjI)
  show "(1 :: nat) < 2" by presburger
qed simp_all

lemma "trail_less_id_comp [L2, L1, L0] L0 (- L0)"
  unfolding trail_less_id_comp_def
proof (intro exI conjI)
  show "(2 :: nat) \<le> 2" by presburger
qed simp_all

lemma "trail_less_id_id [L2, L1, L0] L1 L2"
  unfolding trail_less_id_id_def
proof (intro exI conjI)
  show "(0 :: nat) < 1" by presburger
qed simp_all

lemma "trail_less_id_id [L2, L1, L0] L0 L1"
  unfolding trail_less_id_id_def
proof (intro exI conjI)
  show "(1 :: nat) < 2" by presburger
qed simp_all

lemma "trail_less_comp_comp [L2, L1, L0] (- L1) (- L2)"
  unfolding trail_less_comp_comp_def
proof (intro exI conjI)
  show "(0 :: nat) < 1" by presburger
qed simp_all

lemma "trail_less_comp_comp [L2, L1, L0] (- L0) (- L1)"
  unfolding trail_less_comp_comp_def
proof (intro exI conjI)
  show "(1 :: nat) < 2" by presburger
qed simp_all

end


subsection \<open>Miscellaneous Lemmas\<close>

lemma not_trail_less_Nil: "\<not> trail_less [] L K"
  unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
    trail_less_id_comp_def trail_less_comp_comp_def
  by simp


lemma defined_if_trail_less:
  assumes "trail_less Ls L K"
  shows "L \<in> set Ls \<union> uminus ` set Ls" "K \<in> set Ls \<union> uminus ` set Ls"
   apply (atomize (full))
  using assms unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
    trail_less_id_comp_def trail_less_comp_comp_def
  by (elim disjE exE conjE) simp_all

lemma not_less_if_undefined:
  fixes L :: "'a :: uminus"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    "L \<notin> set Ls" "- L \<notin> set Ls"
  shows "\<not> trail_less Ls L K" "\<not> trail_less Ls K L"
  using assms
  unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  by auto

lemma defined_conv:
  fixes L :: "'a :: uminus"
  assumes uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "L \<in> set Ls \<union> uminus ` set Ls \<longleftrightarrow> L \<in> set Ls \<or> - L \<in> set Ls"
  by (auto simp: rev_image_eqI uminus_uminus_id)

lemma trail_less_comp_rightI: "L \<in> set Ls \<Longrightarrow> trail_less Ls L (- L)"
  by (metis in_set_conv_nth le_eq_less_or_eq trail_less_def trail_less_id_comp_def)

lemma trail_less_comp_leftI:
  fixes Ls :: "('a :: uminus) list"
  assumes uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "- L \<in> set Ls \<Longrightarrow> trail_less Ls (- L) L"
  by (rule trail_less_comp_rightI[of "- L", unfolded uminus_uminus_id])


subsection \<open>Well-Defined\<close>

lemma trail_less_id_id_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_id_id Ls L K"
  shows
    "\<not> trail_less_id_comp Ls L K"
    "\<not> trail_less_comp_id Ls L K"
    "\<not> trail_less_comp_comp Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+

lemma trail_less_id_comp_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_id_comp Ls L K"
  shows
    "\<not> trail_less_id_id Ls L K"
    "\<not> trail_less_comp_id Ls L K"
    "\<not> trail_less_comp_comp Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+

lemma trail_less_comp_id_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_comp_id Ls L K"
  shows
    "\<not> trail_less_id_id Ls L K"
    "\<not> trail_less_id_comp Ls L K"
    "\<not> trail_less_comp_comp Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+

lemma trail_less_comp_comp_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_comp_comp Ls L K"
  shows
    "\<not> trail_less_id_id Ls L K"
    "\<not> trail_less_id_comp Ls L K"
    "\<not> trail_less_comp_id Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+


subsection \<open>Strict Partial Order\<close>

lemma irreflp_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "irreflp (trail_less Ls)"
proof (rule irreflpI, rule notI)
  fix L :: 'a
  assume "trail_less Ls L L"
  then show False
    unfolding trail_less_def
  proof (elim disjE)
    show "trail_less_id_id Ls L L \<Longrightarrow> False"
      unfolding trail_less_id_id_def
      using pairwise_distinct by fastforce
  next
    show "trail_less_comp_id Ls L L \<Longrightarrow> False"
      unfolding trail_less_comp_id_def
      by (metis pairwise_distinct uminus_not_id)
  next
    show "trail_less_id_comp Ls L L \<Longrightarrow> False"
      unfolding trail_less_id_comp_def
      by (metis pairwise_distinct uminus_not_id)
  next
    show "trail_less_comp_comp Ls L L \<Longrightarrow> False"
      unfolding trail_less_comp_comp_def
      by (metis pairwise_distinct uminus_uminus_id nat_less_le)
  qed
qed

lemma transp_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "transp (trail_less Ls)"
proof (rule transpI)
  fix L K H :: 'a
  show "trail_less Ls L K \<Longrightarrow> trail_less Ls K H \<Longrightarrow> trail_less Ls L H"
    using pairwise_distinct[rule_format] uminus_not_id uminus_uminus_id
    unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
      trail_less_id_comp_def trail_less_comp_comp_def
    (* Approximately 3 seconds on AMD Ryzen 7 PRO 5850U CPU. *)
    by (smt (verit, best) le_eq_less_or_eq order.strict_trans)
qed

lemma asymp_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "asymp (trail_less Ls)"
  using irreflp_trail_less[OF assms] transp_trail_less[OF assms]
  using asymp_on_iff_irreflp_on_if_transp_on
  by auto


subsection \<open>Strict Total (w.r.t. Elements in Trail) Order\<close>

lemma totalp_on_trail_less:
  "totalp_on (set Ls \<union> uminus ` set Ls) (trail_less Ls)"
proof (rule totalp_onI, unfold Un_iff, elim disjE)
  fix L K
  assume "L \<in> set Ls" and "K \<in> set Ls" and "L \<noteq> K"
  then obtain i j where "i < length Ls" "Ls ! i = L" "j < length Ls" "Ls ! j = K"
    unfolding in_set_conv_nth by auto
  thus "trail_less Ls L K \<or> trail_less Ls K L"
    using \<open>L \<noteq> K\<close> less_linear[of i j]
    by (meson trail_less_def trail_less_id_id_def)
next
  fix L K
  assume "L \<in> set Ls" and "K \<in> uminus ` set Ls" and "L \<noteq> K"
  then obtain i j where "i < length Ls" "Ls ! i = L" "j < length Ls" "- (Ls ! j) = K"
    unfolding in_set_conv_nth image_set length_map by auto
  thus "trail_less Ls L K \<or> trail_less Ls K L"
    using  less_linear[of i j]
    by (metis le_eq_less_or_eq trail_less_comp_id_def trail_less_def trail_less_id_comp_def)
next
  fix L K
  assume "L \<in> uminus ` set Ls" and "K \<in> set Ls" and "L \<noteq> K"
  then obtain i j where "i < length Ls" "- (Ls ! i) = L" "j < length Ls" "Ls ! j = K"
    unfolding in_set_conv_nth image_set length_map by auto
  thus "trail_less Ls L K \<or> trail_less Ls K L"
    using less_linear[of i j]
    by (metis le_eq_less_or_eq trail_less_comp_id_def trail_less_def trail_less_id_comp_def)
next
  fix L K
  assume "L \<in> uminus ` set Ls" and "K \<in> uminus ` set Ls" and "L \<noteq> K"
  then obtain i j where "i < length Ls" "- (Ls ! i) = L" "j < length Ls" "- (Ls ! j) = K"
    unfolding in_set_conv_nth image_set length_map by auto
  thus "trail_less Ls L K \<or> trail_less Ls K L"
    using \<open>L \<noteq> K\<close> less_linear[of i j]
    by (metis trail_less_comp_comp_def trail_less_def)
qed


subsection \<open>Well-Founded\<close>

lemma not_trail_less_Cons_id_comp:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length (L # Ls). \<forall>j < length (L # Ls). i \<noteq> j \<longrightarrow>
        (L # Ls) ! i \<noteq> (L # Ls) ! j \<and> (L # Ls) ! i \<noteq> - ((L # Ls) ! j)"
  shows "\<not> trail_less (L # Ls) (- L) L"
proof (rule notI, unfold trail_less_def, elim disjE)
  show "trail_less_id_id (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_id_id_def
    using pairwise_distinct uminus_not_id by metis
next
  show "trail_less_comp_id (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_comp_id_def
    using pairwise_distinct uminus_uminus_id
    by (metis less_not_refl)
next
  show "trail_less_id_comp (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_id_comp_def
    using pairwise_distinct uminus_not_id
    by (metis length_pos_if_in_set nth_Cons_0 nth_mem)
next
  show "trail_less_comp_comp (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_comp_comp_def
    using pairwise_distinct uminus_not_id uminus_uminus_id by metis
qed

lemma not_trail_less_if_undefined:
  fixes L :: "'a :: uminus"
  assumes
    undefined: "L \<notin> set Ls" "- L \<notin> set Ls" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "\<not> trail_less Ls L K" "\<not> trail_less Ls K L"
  using undefined[unfolded in_set_conv_nth] uminus_uminus_id
  unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
    trail_less_id_comp_def trail_less_comp_comp_def
  by (smt (verit))+

lemma trail_less_ConsD:
  fixes L H K :: "'a :: uminus"
  assumes uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    L_neq_K: "L \<noteq> K" and L_neq_minus_K: "L \<noteq> - K" and
    less_Cons: "trail_less (L # Ls) H K"
  shows "trail_less Ls H K"
  using less_Cons[unfolded trail_less_def]
proof (elim disjE)
  assume "trail_less_id_id (L # Ls) H K"
  hence "trail_less_id_id Ls H K"
    unfolding trail_less_id_id_def
    using L_neq_K less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
next
  assume "trail_less_comp_id (L # Ls) H K"
  hence "trail_less_comp_id Ls H K"
    unfolding trail_less_comp_id_def
    using L_neq_K less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
next
  assume "trail_less_id_comp (L # Ls) H K"
  hence "trail_less_id_comp Ls H K"
    unfolding trail_less_id_comp_def
    using L_neq_minus_K uminus_uminus_id less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
next
  assume "trail_less_comp_comp (L # Ls) H K"
  hence "trail_less_comp_comp Ls H K"
    unfolding trail_less_comp_comp_def
    using L_neq_minus_K uminus_uminus_id less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
qed

lemma trail_subset_empty_or_ex_smallest:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "Q \<subseteq> set Ls \<union> uminus ` set Ls \<Longrightarrow> Q = {} \<or> (\<exists>z \<in> Q. \<forall>y. trail_less Ls y z \<longrightarrow> y \<notin> Q)"
  using pairwise_distinct
proof (induction Ls arbitrary: Q)
  case Nil
  thus ?case by simp
next
  case Cons_ind: (Cons L Ls)
  from Cons_ind.prems have pairwise_distinct_L_Ls:
    "\<forall>i<length (L # Ls). \<forall>j<length (L # Ls). i \<noteq> j \<longrightarrow>
      (L # Ls) ! i \<noteq> (L # Ls) ! j \<and> (L # Ls) ! i \<noteq> - (L # Ls) ! j"
    by simp
  hence pairwise_distinct_Ls:
    "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
    by (metis distinct.simps(2) distinct_conv_nth length_Cons not_less_eq nth_Cons_Suc)
  show ?case
  proof (cases "Q = {}")
    case True
    thus ?thesis by simp
  next
    case Q_neq_empty: False
    have Q_minus_subset: "Q - {L, - L} \<subseteq> set Ls \<union> uminus ` set Ls" using Cons_ind.prems(1) by auto

    have irreflp_gt_L_Ls: "irreflp (trail_less (L # Ls))"
      by (rule irreflp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct_L_Ls])

    have "\<exists>z\<in>Q. \<forall>y. trail_less (L # Ls) y z \<longrightarrow> y \<notin> Q"
      using Cons_ind.IH[OF Q_minus_subset pairwise_distinct_Ls]
    proof (elim disjE bexE)
      assume "Q - {L, -L} = {}"
      with Q_neq_empty have "Q \<subseteq> {L, -L}" by simp
      have ?thesis if "L \<in> Q"
        apply (intro bexI[OF _ \<open>L \<in> Q\<close>] allI impI)
        apply (erule contrapos_pn)
        apply (drule set_rev_mp[OF _ \<open>Q \<subseteq> {L, -L}\<close>])
        apply simp
        using irreflp_gt_L_Ls[THEN irreflpD, of L]
        using not_trail_less_Cons_id_comp[OF uminus_not_id uminus_uminus_id
            pairwise_distinct_L_Ls]
        by fastforce
      moreover have ?thesis if "L \<notin> Q"
      proof -
        from \<open>L \<notin> Q\<close> have "Q = {- L}"
          using Q_neq_empty \<open>Q \<subseteq> {L, -L}\<close> by auto
        thus ?thesis
          using irreflp_gt_L_Ls[THEN irreflpD, of "- L"] by auto
      qed
      ultimately show ?thesis by metis
    next
      fix K
      assume K_in_Q_minus: "K \<in> Q - {L, -L}" and "\<forall>y. trail_less Ls y K \<longrightarrow> y \<notin> Q - {L, -L}"
      from K_in_Q_minus have "L \<noteq> K" "- L \<noteq> K" by auto
      from K_in_Q_minus have "L \<noteq> - K" using \<open>- L \<noteq> K\<close> uminus_uminus_id by blast
      show ?thesis
      proof (intro bexI allI impI)
        show "K \<in> Q"
          using K_in_Q_minus by simp
      next
        fix H
        assume "trail_less (L # Ls) H K"
        hence "trail_less Ls H K"
          by (rule trail_less_ConsD[OF uminus_uminus_id \<open>L \<noteq> K\<close> \<open>L \<noteq> - K\<close>])
        hence "H \<notin> Q - {L, -L}"
          using \<open>\<forall>y. trail_less Ls y K \<longrightarrow> y \<notin> Q - {L, -L}\<close> by simp
        moreover have "H \<noteq> L \<and>  H \<noteq> - L"
          using uminus_uminus_id pairwise_distinct_L_Ls \<open>trail_less Ls H K\<close>
          by (metis (no_types, lifting) distinct.simps(2) distinct_conv_nth in_set_conv_nth
              list.set_intros(1,2) not_trail_less_if_undefined(1))
        ultimately show "H \<notin> Q"
          by simp
      qed
    qed
    thus ?thesis by simp
  qed
qed

lemma wfP_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "wfP (trail_less Ls)"
  unfolding wfP_eq_minimal
proof (intro allI impI)
  fix M :: "'a set" and L :: 'a
  assume "L \<in> M"
  show "\<exists>z \<in> M. \<forall>y. trail_less Ls y z \<longrightarrow> y \<notin> M"
  proof (cases "M \<inter> (set Ls \<union> uminus ` set Ls) = {}")
    case True
    with \<open>L \<in> M\<close> have L_not_in_Ls: "L \<notin> set Ls \<and> - L \<notin> set Ls"
      unfolding disjoint_iff by (metis UnCI image_eqI uminus_uminus_id)
    then show ?thesis
    proof (intro bexI[OF _ \<open>L \<in> M\<close>] allI impI)
      fix K
      assume "trail_less Ls K L"
      hence False
        using L_not_in_Ls not_trail_less_if_undefined[OF _ _ uminus_uminus_id] by simp
      thus "K \<notin> M" ..
    qed
  next
    case False
    hence "M \<inter> (set Ls \<union> uminus ` set Ls) \<subseteq> set Ls \<union> uminus ` set Ls"
      by simp
    with False obtain H where
      H_in: "H \<in> M \<inter> (set Ls \<union> uminus ` set Ls)" and
      all_lt_H_no_in: "\<forall>y. trail_less Ls y H \<longrightarrow> y \<notin> M \<inter> (set Ls \<union> uminus ` set Ls)"
      using trail_subset_empty_or_ex_smallest[OF uminus_not_id uminus_uminus_id pairwise_distinct]
      by meson
    show ?thesis
    proof (rule bexI)
      show "H \<in> M" using H_in by simp
    next
      show "\<forall>y. trail_less Ls y H \<longrightarrow> y \<notin> M"
        using all_lt_H_no_in uminus_uminus_id
        by (metis Int_iff Un_iff image_eqI not_trail_less_if_undefined(1))
    qed
  qed
qed


subsection \<open>Extension on All Literals\<close>

definition trail_less_ex where
  "trail_less_ex lt Ls L K \<longleftrightarrow>
    (if L \<in> set Ls \<or> - L \<in> set Ls then
      if K \<in> set Ls \<or> - K \<in> set Ls then
        trail_less Ls L K
      else
        True
    else
      if K \<in> set Ls \<or> - K \<in> set Ls then
        False
      else
        lt L K)"

lemma
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "K \<in> set Ls \<or> - K \<in> set Ls \<Longrightarrow> trail_less_ex lt Ls L K \<longleftrightarrow> trail_less Ls L K"
  using not_less_if_undefined[OF uminus_uminus_id]
  by (simp add: trail_less_ex_def)

lemma trail_less_ex_if_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "trail_less Ls L K \<Longrightarrow> trail_less_ex lt Ls L K"
  unfolding trail_less_ex_def
  using defined_if_trail_less[THEN defined_conv[OF uminus_uminus_id, THEN iffD1]]
  by auto

lemma
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "L \<in> set Ls \<union> uminus ` set Ls \<Longrightarrow> K \<notin> set Ls \<union> uminus ` set Ls \<Longrightarrow> trail_less_ex lt Ls L K"
  using defined_conv uminus_uminus_id
  by (auto simp add: trail_less_ex_def)
  

lemma irreflp_trail_ex_less:
  fixes Ls :: "('a :: uminus) list" and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    irreflp_lt: "irreflp lt"
  shows "irreflp (trail_less_ex lt Ls)"
  unfolding trail_less_ex_def
  using irreflp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct] irreflp_lt
  by (simp add: irreflpD irreflpI)

lemma transp_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    transp_lt: "transp lt"
  shows "transp (trail_less_ex lt Ls)"
  unfolding trail_less_ex_def
  using transp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct] transp_lt
  by (smt (verit, ccfv_SIG) transp_def)

lemma asymp_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    asymp_lt: "asymp lt"
  shows "asymp (trail_less_ex lt Ls)"
  unfolding trail_less_ex_def
  using asymp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct] asymp_lt
  by (auto dest: asympD)

lemma totalp_on_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    totalp_on_lt: "totalp_on A lt"
  shows "totalp_on (A \<union> set Ls \<union> uminus ` set Ls) (trail_less_ex lt Ls)"
  using totalp_on_trail_less[of Ls]
  using totalp_on_lt
  unfolding trail_less_ex_def
  by (smt (verit, best) Un_iff defined_conv totalp_on_def uminus_uminus_id)


subsubsection \<open>Well-Founded\<close>

lemma wfP_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    wfP_lt: "wfP lt"
  shows "wfP (trail_less_ex lt Ls)"
  unfolding wfP_eq_minimal
proof (intro allI impI)
  fix Q :: "'a set" and x :: 'a
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. trail_less_ex lt Ls y z \<longrightarrow> y \<notin> Q "
  proof (cases "Q \<inter> (set Ls \<union> uminus ` set Ls) = {}")
    case True
    then show ?thesis
      using wfP_lt[unfolded wfP_eq_minimal, rule_format, OF \<open>x \<in> Q\<close>]
      by (metis (no_types, lifting) defined_conv disjoint_iff trail_less_ex_def uminus_uminus_id)
  next
    case False
    then show ?thesis
      using trail_subset_empty_or_ex_smallest[OF uminus_not_id uminus_uminus_id pairwise_distinct,
        unfolded wfP_eq_minimal, of "Q \<inter> (set Ls \<union> uminus ` set Ls)", simplified]
      by (metis (no_types, lifting) IntD1 IntD2 UnE defined_conv trail_less_ex_def uminus_uminus_id)
  qed
qed


subsection \<open>Alternative only for terms\<close>


(* definition trail_term_less where
  "trail_term_less ts = (\<lambda>t1 t2. \<exists>i. Suc i < length ts \<and> t1 = ts ! Suc i \<and> t2 = ts ! i)\<^sup>+\<^sup>+"

lemma transp_trail_term_less: "transp (trail_term_less ts)"
proof (rule transpI)
  fix t1 t2 t3
  assume "trail_term_less ts t1 t2" and "trail_term_less ts t2 t3"
  then show "trail_term_less ts t1 t3"
    by (simp add: trail_term_less_def)
qed *)

definition trail_term_less where
  "trail_term_less ts t1 t2 \<longleftrightarrow> (\<exists>i < length ts. \<exists>j < i. t1 = ts ! i \<and> t2 = ts ! j)"

lemma transp_trail_term_less:
  assumes "distinct ts"
  shows "transp (trail_term_less ts)"
  by (rule transpI)
    (smt (verit, ccfv_SIG) Suc_lessD assms less_trans_Suc nth_eq_iff_index_eq trail_term_less_def)

lemma asymp_trail_term_less:
  assumes "distinct ts"
  shows "asymp (trail_term_less ts)"
  by (rule asympI)
    (metis assms distinct_Ex1 dual_order.strict_trans nth_mem order_less_imp_not_less
      trail_term_less_def)

lemma irreflp_trail_term_less:
  assumes "distinct ts"
  shows "irreflp (trail_term_less ts)"
  using assms irreflp_on_if_asymp_on[OF asymp_trail_term_less] by metis

lemma totalp_on_trail_term_less:
  shows "totalp_on (set ts) (trail_term_less ts)"
  by (rule totalp_onI) (metis in_set_conv_nth nat_neq_iff trail_term_less_def)

lemma wfP_trail_term_less:
  assumes "distinct ts"
  shows "wfP (trail_term_less ts)"
proof (rule wfP_if_convertible_to_nat)
  fix t1 t2 assume "trail_term_less ts t1 t2"
  then obtain i j where "i<length ts" and "j<i" and "t1 = ts ! i" and "t2 = ts ! j"
    unfolding trail_term_less_def by auto
  then show "index (rev ts) t1 < index (rev ts) t2"
    using assms diff_commute index_nth_id index_rev by fastforce
qed

lemma trail_term_less_Cons_if_mem:
  assumes "y \<in> set xs"
  shows "trail_term_less (x # xs) y x"
proof -
  from assms obtain i where "i < length xs" and "xs ! i = y"
    by (meson in_set_conv_nth)
  thus ?thesis
    unfolding trail_term_less_def
  proof (intro exI conjI)
    show "Suc i < length (x # xs)"
      using \<open>i < length xs\<close> by simp
  next
    show "0 < Suc i"
      by simp
  next
    show "y = (x # xs) ! Suc i"
      using \<open>xs ! i = y\<close> by simp
  next
    show "x = (x # xs) ! 0"
      by simp
  qed
qed

end