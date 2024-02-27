theory Relation_Extra
  imports "HOL.Relation"  "Open_Induction.Restricted_Predicates"
begin

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

lemma totalp_on_image:
 assumes "inj f"
 shows "totalp_on (f ` domain) R \<longleftrightarrow> totalp_on domain (\<lambda>a b. R (f a) (f b))"
  using assms
  unfolding totalp_on_def inj_def
  by auto

(* TODO: Other direction? *)
lemma wfp_on_image:
 assumes "inj f"
 shows "wfp_on R (f ` domain) \<Longrightarrow> wfp_on (\<lambda>a b. R (f a) (f b)) domain"
  using assms
  unfolding wfp_on_def inj_def
  apply(auto)
  by (meson image_eqI)

end
