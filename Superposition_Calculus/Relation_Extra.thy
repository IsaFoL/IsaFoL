theory Relation_Extra
  imports HOL.Relation
begin

lemma transp_on_empty[simp]: "transp_on {} R"
  by (auto intro: transp_onI)

lemma asymp_on_empty[simp]: "asymp_on {} R"
  by (auto intro: asymp_onI)

lemma partition_set_around_element:
  assumes tot: "totalp_on N R" and x_in: "x \<in> N"
  shows "N = {y \<in> N. R y x} \<union> {x} \<union> {y \<in> N. R x y}"
proof (intro Set.equalityI Set.subsetI)
  fix z assume "z \<in> N"
  hence "R z x \<or> z = x \<or> R x z"
    using tot[THEN totalp_onD] x_in by auto
  thus "z \<in> {y \<in> N. R y x} \<union> {x} \<union> {y \<in> N. R x y}" 
    using \<open>z \<in> N\<close> by auto
next
  fix z assume "z \<in> {y \<in> N. R y x} \<union> {x} \<union> {y \<in> N. R x y}"
  hence "z \<in> N \<or> z = x"
    by auto
  thus "z \<in> N"
    using x_in by auto
qed

end
