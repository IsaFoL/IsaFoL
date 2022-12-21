theory Relation_Extra
  imports Main
begin

lemma irrefl_on_if_asym_on: "asym_on A r \<Longrightarrow> irrefl_on A r"
  by (auto intro: irrefl_onI dest: asym_onD)

lemma totalp_on_insert:
  "totalp_on (insert a A) R \<longleftrightarrow> (\<forall>b \<in> A. a \<noteq> b \<longrightarrow> R a b \<or> R b a) \<and> totalp_on A R"
  by (auto simp add: totalp_on_def)

lemma antisymp_reflcp: "antisymp R \<Longrightarrow> antisymp R\<^sup>=\<^sup>="
  by (simp add: antisymp_def)

abbreviation strict_orderp where
  "strict_orderp R \<equiv> irreflp R \<and> transp R \<and> asymp R"

abbreviation partial_orderp where
  "partial_orderp R \<equiv> reflp R \<and> transp R \<and> antisymp R"

lemma partial_orderp_reflclp_if_strict_orderp:
  assumes "strict_orderp R"
  shows "partial_orderp R\<^sup>=\<^sup>="
proof -
  have "reflp R\<^sup>=\<^sup>="
    by (rule reflp_on_reflclp)
  moreover have "transp R\<^sup>=\<^sup>="
    using assms transp_on_reflclp by blast
  moreover have "antisymp R\<^sup>=\<^sup>="
    using assms antisymp_on_if_asymp_on antisymp_reflcp by blast
  ultimately show ?thesis
    by simp
qed

inductive exhaustive_order for R where
  "(\<And>y. \<not> R y x) \<Longrightarrow> exhaustive_order R x []" |
  "exhaustive_order R x xs \<Longrightarrow> R x y \<Longrightarrow> (\<nexists>z. R x z \<and> R z y) \<Longrightarrow> exhaustive_order R y (x # xs)"

lemma "exhaustive_order (<) (0 :: nat) []"
  by (auto intro: exhaustive_order.intros)

lemma "exhaustive_order (<) (1 :: nat) [0]"
  by (auto intro: exhaustive_order.intros)

lemma "exhaustive_order (<) (2 :: nat) [1, 0]"
  by (auto intro!: exhaustive_order.intros)

lemma "exhaustive_order (<) (3 :: nat) [2, 1, 0]"
  by (auto intro!: exhaustive_order.intros)

lemma exhaustive_order_all_smaller:
  assumes "transp R"
  shows "exhaustive_order R x xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> R y x"
proof (induction x xs rule: exhaustive_order.induct)
  case (1 x)
  thus ?case by simp
next
  case (2 x xs z)
  thus ?case
    using \<open>transp R\<close> by (metis set_ConsD transpE)
qed

lemma exhaustive_order_successively_smaller:
  "exhaustive_order R x xs \<Longrightarrow> successively R\<inverse>\<inverse> (x # xs)"
  by (induction x xs rule: exhaustive_order.induct) simp_all

lemma exhaustive_order_distinct:
  assumes "irreflp R" and "transp R" and "asymp R"
  shows "exhaustive_order R x xs \<Longrightarrow> distinct (x # xs)"
proof (induction x xs rule: exhaustive_order.induct)
  case (1 x)
  show ?case by simp
next
  case (2 x xs y)
  have "y \<noteq> x"
    using \<open>R x y\<close> \<open>irreflp R\<close>[THEN irreflpD] by auto
  moreover have "distinct (y # xs)"
    using 2 \<open>asymp R\<close>
    using exhaustive_order_all_smaller[OF \<open>transp R\<close> \<open>exhaustive_order R x xs\<close>]
    by (metis asympD distinct.simps(2))
  ultimately show ?case
    using \<open>distinct (x # xs)\<close>
    unfolding distinct_length_2_or_more
    by simp
qed

lemma exhaustive_order_complete:
  assumes "totalp R"
  shows "exhaustive_order R x xs \<Longrightarrow> R y x \<Longrightarrow> y \<in> set xs"
proof (induction x xs rule: exhaustive_order.induct)
  case (1 x)
  thus ?case by simp
next
  case (2 x xs y)
  then show ?case
    using \<open>totalp R\<close>[THEN totalpD]
    by (metis list.set_intros(1) list.set_intros(2))
qed

lemma exhaustive_order_set_conv:
  assumes "totalp R" and "transp R" and "exhaustive_order R x xs"
  shows "set xs = {y. R y x}"
proof (rule Set.equalityI; rule Set.subsetI)
  show "\<And>z. z \<in> set xs \<Longrightarrow> z \<in> {y. R y x}"
    using exhaustive_order_all_smaller[OF \<open>transp R\<close> \<open>exhaustive_order R x xs\<close>]
    by simp
next
  show "\<And>z. z \<in> {y. R y x} \<Longrightarrow> z \<in> set xs"
    using exhaustive_order_complete[OF \<open>totalp R\<close> \<open>exhaustive_order R x xs\<close>]
    by simp
qed

end