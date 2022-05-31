theory Relation_Extra
  imports Main
begin

lemma irreflpD: "irreflp R \<Longrightarrow> \<not> R x x"
  unfolding irreflp_def by simp

lemma asymp_if_irreflp_and_transp: "irreflp R \<Longrightarrow> transp R \<Longrightarrow> asymp R"
  by (rule asympI) (metis irreflp_def transpD)

end