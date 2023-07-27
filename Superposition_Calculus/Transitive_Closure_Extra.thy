theory Transitive_Closure_Extra
  imports Main
begin

lemma reflclp_iff: "\<And>R x y. R\<^sup>=\<^sup>= x y \<longleftrightarrow> R x y \<or> x = y"
  by (metis (full_types) sup2CI sup2E)

lemma reflclp_refl: "R\<^sup>=\<^sup>= x x"
  by simp

lemma transpD_strict_non_strict:
  assumes "transp R"
  shows "\<And>x y z. R x y \<Longrightarrow> R\<^sup>=\<^sup>= y z \<Longrightarrow> R x z"
  using \<open>transp R\<close>[THEN transpD] by blast

lemma transpD_non_strict_strict:
  assumes "transp R"
  shows "\<And>x y z. R\<^sup>=\<^sup>= x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  using \<open>transp R\<close>[THEN transpD] by blast

lemma mem_rtrancl_union_iff_mem_rtrancl_lhs:
  assumes "\<And>z. (x, z) \<in> A\<^sup>* \<Longrightarrow> z \<notin> Domain B"
  shows "(x, y) \<in> (A \<union> B)\<^sup>* \<longleftrightarrow> (x, y) \<in> A\<^sup>*"
  using assms
  by (meson Domain.DomainI in_rtrancl_UnI rtrancl_Un_separatorE)

lemma mem_rtrancl_union_iff_mem_rtrancl_rhs:
  assumes
    "\<And>z. (x, z) \<in> B\<^sup>* \<Longrightarrow> z \<notin> Domain A"
  shows "(x, y) \<in> (A \<union> B)\<^sup>* \<longleftrightarrow> (x, y) \<in> B\<^sup>*"
  using assms
  by (metis mem_rtrancl_union_iff_mem_rtrancl_lhs sup_commute)

end