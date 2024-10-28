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

abbreviation Pos_Upair (infix "\<approx>" 66) where
  "Pos_Upair x y \<equiv> Pos (Upair x y)"

abbreviation Neg_Upair (infix "!\<approx>" 66) where
  "Neg_Upair x y \<equiv> Neg (Upair x y)"

lemma exists_atom_for_term: "\<exists>a. t \<in> set_uprod a"
  by (metis insertI1 set_uprod_simps)

lemma exists_literal_for_atom: "\<exists>l. a \<in> set_literal l"
  by (meson literal.set_intros(1))

lemma exists_literal_for_term: "\<exists>l. t \<in># mset_lit l"
  by (metis exists_atom_for_term mset_lit.simps(1) set_mset_mset_uprod)

lemma exists_clause_for_literal: "\<exists>c. l \<in> set_mset c"
  by (meson union_single_eq_member)

lemma finite_set_literal: "\<And>l. finite (set_literal l)"
  unfolding set_literal_atm_of
  by simp

lemma map_literal_map_uprod_cong: 
  assumes "\<And>t. t \<in># mset_lit l \<Longrightarrow> f t = g t"  
  shows "map_literal (map_uprod f) l = map_literal (map_uprod g) l"
  using assms
  by(cases l)(auto cong: uprod.map_cong0)

lemma set_mset_set_uprod: "set_mset (mset_lit l) = set_uprod (atm_of l)"
  by(cases l) simp_all

lemma mset_lit_set_literal: "t \<in># mset_lit l \<longleftrightarrow> t \<in> \<Union>(set_uprod ` set_literal l)"
  unfolding set_literal_atm_of
  by(simp add: set_mset_set_uprod)
 
end
