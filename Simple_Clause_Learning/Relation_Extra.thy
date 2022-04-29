theory Relation_Extra
  imports Main
begin

lemma irreflpD: "irreflp R \<Longrightarrow> \<not> R x x"
  unfolding irreflp_def by simp

lemma asymp_if_irreflp_and_transp: "irreflp R \<Longrightarrow> transp R \<Longrightarrow> asymp R"
  by (rule asympI) (metis irreflp_def transpD)

definition totalp where
  "totalp R \<longleftrightarrow> (\<forall>x. \<forall>y. x \<noteq> y \<longrightarrow> R x y \<or> R y x)"

lemma totalpI: "(\<And>x y. x \<noteq> y \<Longrightarrow> R x y \<or> R y x) \<Longrightarrow> totalp R"
  unfolding totalp_def by simp

lemma totalpD: "totalp R \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<or> R y x"
  unfolding totalp_def by simp

end