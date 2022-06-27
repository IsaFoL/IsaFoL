theory Trail_Induced_Ordering
  imports
    (* Isabelle theories *)
    Main

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
  shows "L \<in> set Ls \<union> uminus ` set Ls" "L \<in> set Ls \<union> uminus ` set Ls"
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
  using asymp_if_irreflp_and_transp
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
  by (simp add: asymp.simps)

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

end