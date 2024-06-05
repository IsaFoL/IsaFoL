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

lemma reflp_on_image: "reflp_on (f ` A) R \<longleftrightarrow> reflp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: reflp_on_def)

lemma irreflp_on_image: "irreflp_on (f ` A) R \<longleftrightarrow> irreflp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: irreflp_on_def)

lemma symp_on_image: "symp_on (f ` A) R \<longleftrightarrow> symp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: symp_on_def)

lemma asymp_on_image: "asymp_on (f ` A) R \<longleftrightarrow> asymp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: asymp_on_def)

lemma antisymp_on_image:
  assumes "inj_on f A"
  shows "antisymp_on (f ` A) R \<longleftrightarrow> antisymp_on A (\<lambda>a b. R (f a) (f b))"
  using assms by (auto simp: antisymp_on_def inj_on_def)

lemma transp_on_image: "transp_on (f ` A) R \<longleftrightarrow> transp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: transp_on_def)

lemma totalp_on_image:
  assumes "inj_on f A"
  shows "totalp_on (f ` A) R \<longleftrightarrow> totalp_on A (\<lambda>a b. R (f a) (f b))"
  using assms by (auto simp: totalp_on_def inj_on_def)

end
