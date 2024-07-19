theory Clausal_Calculus_Extra
  imports
    "Saturation_Framework_Extensions.Clausal_Calculus"
    Uprod_Extra
begin

lemma map_literal_inverse: 
  "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>literal. map_literal f (map_literal g literal) = literal)"
  by (simp add: literal.map_comp literal.map_ident_strong)

lemma map_literal_comp: 
  "map_literal f (map_literal g literal) = map_literal (\<lambda>atom. f (g atom)) literal"
  using literal.map_comp
  unfolding comp_def.

lemma literals_distinct [simp]: "Neg \<noteq> Pos" "Pos \<noteq> Neg"
  by(metis literal.distinct(1))+

primrec mset_lit :: "'a uprod literal \<Rightarrow> 'a multiset" where
  "mset_lit (Pos A) = mset_uprod A" |
  "mset_lit (Neg A) = mset_uprod A + mset_uprod A"

lemma mset_lit_image_mset: "mset_lit (map_literal (map_uprod f) l) = image_mset f (mset_lit l)"
  by(induction l) (simp_all add: mset_uprod_image_mset)

lemma uprod_mem_image_iff_prod_mem[simp]:
  assumes "sym I"
  shows "(Upair t t') \<in> (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<longleftrightarrow> (t, t') \<in> I"
  using \<open>sym I\<close>[THEN symD] by auto

lemma true_lit_uprod_iff_true_lit_prod[simp]:
  assumes "sym I"
  shows
    "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>l Pos (Upair t t') \<longleftrightarrow> I \<TTurnstile>l Pos (t, t')"
    "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>l Neg (Upair t t') \<longleftrightarrow> I \<TTurnstile>l Neg (t, t')"
  unfolding true_lit_simps uprod_mem_image_iff_prod_mem[OF \<open>sym I\<close>]
  by simp_all

end
