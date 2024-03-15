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
  assumes "inj_on f A"
  shows "totalp_on (f ` A) R \<longleftrightarrow> totalp_on A (\<lambda>a b. R (f a) (f b))"
  using assms
  unfolding totalp_on_def inj_on_def by auto

lemma wfp_on_image: "wfp_on R (f ` A) \<longleftrightarrow> wfp_on (\<lambda>a b. R (f a) (f b)) A"
proof (rule iffI)
  show "wfp_on R (f ` A) \<Longrightarrow> wfp_on (\<lambda>a b. R (f a) (f b)) A"
    unfolding wfp_on_def
    by (metis imageI o_apply)
next
  assume hyp: "wfp_on (\<lambda>a b. R (f a) (f b)) A"
  show "wfp_on R (f ` A)"
    unfolding wfp_on_iff_minimal
  proof (intro allI impI, elim conjE)
    fix Q x
    assume "x \<in> Q" and "Q \<subseteq> f ` A"
    then obtain A' x' where "x' \<in> A'" and "A' \<subseteq> A" and "x = f x'" and "Q = f ` A'"
      by (smt (verit) image_iff subset_image_iff)
    with hyp show "\<exists>z\<in>Q. \<forall>y. R y z \<longrightarrow> y \<notin> Q "
      unfolding wfp_on_iff_minimal
      by (metis imageE imageI)
  qed
qed

end
