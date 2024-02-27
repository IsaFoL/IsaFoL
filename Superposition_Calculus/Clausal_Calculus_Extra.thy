theory Clausal_Calculus_Extra
  imports
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "Uprod_Extra"
begin

lemma map_literal_inverse: 
  "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>literal. map_literal f (map_literal g literal) = literal)"
  by (simp add: literal.map_comp literal.map_ident_strong)

lemma map_literal_comp: 
  "map_literal f (map_literal g literal) = map_literal (\<lambda>atom. f (g atom)) literal"
  unfolding comp_def[symmetric]
  by (simp add: literal.map_comp)

lemma literals_distinct [simp]: "Neg \<noteq> Pos" "Pos \<noteq> Neg"
  by(metis literal.distinct(1))+

primrec mset_lit :: "'a uprod literal \<Rightarrow> 'a multiset" where
  "mset_lit (Pos A) = mset_uprod A" |
  "mset_lit (Neg A) = mset_uprod A + mset_uprod A"

lemma mset_lit_image_mset: "mset_lit (map_literal (map_uprod f) l) = image_mset f (mset_lit l)"
  by(induction l) (simp_all add: mset_uprod_image_mset)

end
