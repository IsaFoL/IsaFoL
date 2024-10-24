theory HOL_Extra
  imports Main
begin

lemmas UniqI = Uniq_I

lemma Uniq_prodI:
  assumes "\<And>x1 y1 x2 y2. P x1 y1 \<Longrightarrow> P x2 y2 \<Longrightarrow> (x1, y1) = (x2, y2)"
  shows "\<exists>\<^sub>\<le>\<^sub>1(x, y). P x y"
  using assms
  by (metis UniqI case_prodE)

lemma Uniq_implies_ex1: "\<exists>\<^sub>\<le>\<^sub>1x. P x \<Longrightarrow> P y \<Longrightarrow> \<exists>!x. P x"
  by (iprover intro: ex1I dest: Uniq_D)

lemma Uniq_antimono: "Q \<le> P \<Longrightarrow> Uniq Q \<ge> Uniq P"
  unfolding le_fun_def le_bool_def
  by (rule impI) (simp only: Uniq_I Uniq_D)

lemma Uniq_antimono': "(\<And>x. Q x \<Longrightarrow> P x) \<Longrightarrow> Uniq P \<Longrightarrow> Uniq Q"
  by (fact Uniq_antimono[unfolded le_fun_def le_bool_def, rule_format])

lemma Collect_eq_if_Uniq: "(\<exists>\<^sub>\<le>\<^sub>1x. P x) \<Longrightarrow> {x. P x} = {} \<or> (\<exists>x. {x. P x} = {x})"
  using Uniq_D by fastforce

lemma Collect_eq_if_Uniq_prod: 
  "(\<exists>\<^sub>\<le>\<^sub>1(x, y). P x y) \<Longrightarrow> {(x, y). P x y} = {} \<or> (\<exists>x y. {(x, y). P x y} = {(x, y)})"
  using Collect_eq_if_Uniq by fastforce

lemma Ball_Ex_comm: 
  "(\<forall>x \<in> X. \<exists>f. P (f x) x) \<Longrightarrow> (\<exists>f. \<forall>x \<in> X. P (f x) x)"
  "(\<exists>f. \<forall>x \<in> X. P (f x) x) \<Longrightarrow> (\<forall>x \<in> X. \<exists>f. P (f x) x)"
  by meson+

lemma set_map_id:
  assumes "x \<in> set X" "f x \<notin> set X"  "map f X = X"
  shows False
  using assms
  by(induction X) auto

end
