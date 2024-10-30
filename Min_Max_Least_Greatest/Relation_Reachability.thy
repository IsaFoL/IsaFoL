theory Relation_Reachability
  imports Main
begin


section \<open>Definitions\<close>

text \<open>When a binary relation hold for two values, i.e., \<^term>\<open>R x y\<close>, we say that \<^term>\<open>x\<close> reaches
\<^term>\<open>y\<close> and, conversely, that \<^term>\<open>y\<close> is reachable by \<^term>\<open>x\<close>.\<close>

definition non_reachable_wrt where
  "non_reachable_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R y x))"

definition non_reaching_wrt where
  "non_reaching_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R x y))"

definition reaching_all_wrt where
  "reaching_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R x y)"

definition reachable_by_all_wrt where
  "reachable_by_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R y x)"


section \<open>Conversions\<close>

lemma non_reachable_wrt_iff:
  "non_reachable_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R y x)"
  unfolding non_reachable_wrt_def by blast

lemma non_reaching_wrt_iff:
  "non_reaching_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  unfolding non_reaching_wrt_def by blast

lemma reaching_all_wrt_iff:
  "reaching_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R x y)"
  unfolding reaching_all_wrt_def by blast

lemma reachable_by_all_wrt_iff:
  "reachable_by_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R y x)"
  unfolding reachable_by_all_wrt_def by blast

lemma non_reachable_wrt_filter_iff:
  "non_reachable_wrt R {y \<in> X. P y} x \<longleftrightarrow> x \<in> X \<and> P x \<and> (\<forall>y \<in> X - {x}. P y \<longrightarrow> \<not> R y x)"
  by (auto simp: non_reachable_wrt_def)

lemma non_reachable_wrt_conversep[simp]:
  "non_reachable_wrt R\<inverse>\<inverse> = non_reaching_wrt R"
  unfolding non_reaching_wrt_def non_reachable_wrt_def by simp

lemma non_reaching_wrt_conversep[simp]:
  "non_reaching_wrt R\<inverse>\<inverse> = non_reachable_wrt R"
  unfolding non_reaching_wrt_def non_reachable_wrt_def by simp

lemma reaching_all_wrt_conversep[simp]:
  "reaching_all_wrt R\<inverse>\<inverse> = reachable_by_all_wrt R"
  unfolding reaching_all_wrt_def reachable_by_all_wrt_def by simp

lemma reachable_by_all_wrt_conversep[simp]:
  "reachable_by_all_wrt R\<inverse>\<inverse> = reaching_all_wrt R"
  unfolding reaching_all_wrt_def reachable_by_all_wrt_def by simp


lemma non_reachable_wrt_eq_reaching_all_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "non_reachable_wrt R X = reaching_all_wrt R X"
proof (intro ext iffI)
  fix x
  from tot show "non_reachable_wrt R X x \<Longrightarrow> reaching_all_wrt R X x"
    unfolding non_reachable_wrt_def reaching_all_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  fix x
  from asym show "reaching_all_wrt R X x \<Longrightarrow> non_reachable_wrt R X x"
    unfolding reaching_all_wrt_def non_reachable_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma non_reaching_wrt_eq_reachable_by_all_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "non_reaching_wrt R X = reachable_by_all_wrt R X"
proof (intro ext iffI)
  fix x
  from tot show "non_reaching_wrt R X x \<Longrightarrow> reachable_by_all_wrt R X x"
    unfolding non_reaching_wrt_def reachable_by_all_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  fix x
  from asym show "reachable_by_all_wrt R X x \<Longrightarrow> non_reaching_wrt R X x"
    unfolding reachable_by_all_wrt_def non_reaching_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma non_reachable_wrt_reflclp[simp]:
  "non_reachable_wrt R\<^sup>=\<^sup>= = non_reachable_wrt R"
  by (intro ext iffI) (simp_all add: non_reachable_wrt_iff)

lemma non_reaching_wrt_reflclp[simp]:
  "non_reaching_wrt R\<^sup>=\<^sup>= = non_reaching_wrt R"
  by (intro ext iffI) (simp_all add: non_reaching_wrt_iff)

lemma reaching_all_wrt_reflclp[simp]:
  "reaching_all_wrt R\<^sup>=\<^sup>= = reaching_all_wrt R"
  by (intro ext iffI) (simp_all add: reaching_all_wrt_iff)

lemma reachable_by_all_wrt_reflclp[simp]:
  "reachable_by_all_wrt R\<^sup>=\<^sup>= = reachable_by_all_wrt R"
  by (intro ext iffI) (simp_all add: reachable_by_all_wrt_iff)


section \<open>Existence\<close>

lemma ex_non_reachable_wrt:
  "transp_on A R \<Longrightarrow> asymp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. non_reachable_wrt R A m"
  using Finite_Set.bex_min_element
  by (metis non_reachable_wrt_iff)

lemma ex_non_reaching_wrt:
  "transp_on A R \<Longrightarrow> asymp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. non_reaching_wrt R A m"
  using Finite_Set.bex_max_element
  by (metis non_reaching_wrt_iff)

lemma ex_reaching_all_wrt:
  "transp_on A R \<Longrightarrow> totalp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>g. reaching_all_wrt R A g"
  using Finite_Set.bex_least_element[of A R]
  by (metis reaching_all_wrt_iff)

lemma ex_reachable_by_all_wrt:
  "transp_on A R \<Longrightarrow> totalp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>g. reachable_by_all_wrt R A g"
  using Finite_Set.bex_greatest_element[of A R]
  by (metis reachable_by_all_wrt_iff)

lemma not_ex_greatest_element_doubleton_if:
  assumes "x \<noteq> y" and "\<not> R x y" and "\<not> R y x"
  shows "\<nexists>g. reachable_by_all_wrt R {x, y} g"
proof (rule notI)
  assume "\<exists>g. reachable_by_all_wrt R {x, y} g"
  then obtain g where "reachable_by_all_wrt R {x, y} g" ..
  then show False
    unfolding reachable_by_all_wrt_def
    using assms(1) assms(2) assms(3) by blast
qed


section \<open>Uniqueness\<close>

lemma Uniq_non_reachable_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. non_reachable_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff non_reachable_wrt_def totalp_onD)

lemma Uniq_non_reaching_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. non_reaching_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff non_reaching_wrt_def totalp_onD)

lemma Uniq_reaching_all_wrt:
  "asymp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. reaching_all_wrt R X x"
  by (rule Uniq_I)
    (metis antisymp_onD antisymp_on_if_asymp_on insertE insert_Diff reaching_all_wrt_def)

lemma Uniq_reachable_by_all_wrt:
  "asymp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. reachable_by_all_wrt R X x"
  by (rule Uniq_I)
    (metis antisymp_onD antisymp_on_if_asymp_on insertE insert_Diff reachable_by_all_wrt_def)


section \<open>Existence of unique element\<close>

lemma ex1_reaching_all_wrt:
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow> finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    \<exists>!x. reaching_all_wrt R X x"
  using ex1_iff_ex_Uniq ex_reaching_all_wrt Uniq_reaching_all_wrt by metis

lemma ex1_reachable_by_all_wrt:
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow> finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    \<exists>!x. reachable_by_all_wrt R X x"
  using ex1_iff_ex_Uniq ex_reachable_by_all_wrt Uniq_reachable_by_all_wrt by metis


section \<open>Transformations\<close>

lemma non_reachable_wrt_insert_wrtI:
  assumes
    trans: "transp_on (insert y X) R" and
    asym: "asymp_on (insert y X) R" and
    "R y x" and
    x_non_reachable: "non_reachable_wrt R X x"
  shows "non_reachable_wrt R (insert y X) y"
proof -
  from x_non_reachable have x_in: "x \<in> X" and x_min': "\<forall>y\<in>X - {x}. \<not> R y x"
    by (simp_all add: non_reachable_wrt_iff)

  have "\<not> R z y" if "z \<in> insert y X - {y}" for z
  proof -
    from that have "z \<in> X" and "z \<noteq> y"
      by simp_all

    show "\<not> R z y"
    proof (cases "z = x")
      case True
      thus ?thesis
        using \<open>R y x\<close> asym x_in
        by (metis asymp_onD insertI1 insertI2)
    next
      case False
      hence "\<not> R z x"
        using x_min'[rule_format, of z, simplified] \<open>z \<in> X\<close> by metis
      then show ?thesis
        using \<open>R y x\<close> trans \<open>z \<in> X\<close> x_in
        by (meson insertCI transp_onD)
    qed
  qed
  thus ?thesis
    by (simp add: non_reachable_wrt_def)
qed

end