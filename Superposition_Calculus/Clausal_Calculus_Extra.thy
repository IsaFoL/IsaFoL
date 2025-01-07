theory Clausal_Calculus_Extra
  imports
    Saturation_Framework_Extensions.Clausal_Calculus
    Uprod_Extra
begin

lemma map_literal_inverse: 
  "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>literal. map_literal f (map_literal g literal) = literal)"
  by (simp add: literal.map_comp literal.map_ident_strong)

lemma map_literal_comp: 
  "map_literal f (map_literal g literal) = map_literal (\<lambda>atom. f (g atom)) literal"
  using literal.map_comp
  unfolding comp_def.

lemma literals_distinct [simp]: "Pos \<noteq> Neg" "Neg \<noteq> Pos"
  by (metis literal.distinct(1))+

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

lemma exists_literal_for_atom [intro]: "\<exists>l. a \<in> set_literal l"
  by (meson literal.set_intros(1))

lemma exists_literal_for_term [intro]: "\<exists>l. t \<in># mset_lit l"
  by (metis exists_uprod mset_lit.simps(1) set_mset_mset_uprod)

lemma finite_set_literal [intro]: "\<And>l. finite (set_literal l)"
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

lemma inj_mset_lit: "inj mset_lit"
proof(unfold inj_def, intro allI impI)
  fix l l' :: "'a uprod literal"
  assume mset_lit: "mset_lit l = mset_lit l'"
  
  show "l = l'"
  proof(cases l)
    case l: (Pos a)
    show ?thesis
    proof(cases l')
      case l': (Pos a')

      show ?thesis
        using mset_lit inj_mset_uprod
        unfolding l l' inj_def
        by auto
    next
      case l': (Neg a')

      show ?thesis
        using mset_lit mset_uprod_plus_neq
        unfolding l l' 
        by auto
    qed
  next
    case l: (Neg a)
    then show ?thesis
     proof(cases l')
      case l': (Pos a')

      show ?thesis
        using mset_lit mset_uprod_plus_neq
        unfolding l l'
        by (metis mset_lit.simps)
    next
      case l': (Neg a')

      show ?thesis
        using mset_lit inj_mset_plus_same inj_mset_uprod
        unfolding l l' inj_def
        by auto
    qed
  qed
qed

global_interpretation literal_functor: finite_natural_functor where
  map = map_literal and to_set = set_literal
  by
    unfold_locales 
    (auto simp: literal.map_comp literal.map_ident literal.set_map intro: literal.map_cong)

global_interpretation literal_functor: natural_functor_conversion where 
  map = map_literal and to_set = set_literal and map_to = map_literal and map_from = map_literal and 
  map' = map_literal and to_set' = set_literal
  by unfold_locales
    (auto simp: literal.set_map Clausal_Logic.literal.map_comp)

abbreviation uprod_literal_to_set where "uprod_literal_to_set l \<equiv> set_mset (mset_lit l)"

abbreviation map_uprod_literal where "map_uprod_literal f \<equiv> map_literal (map_uprod f)"

global_interpretation uprod_literal_functor: finite_natural_functor where 
  map = map_uprod_literal and to_set = uprod_literal_to_set
  by unfold_locales (auto simp: mset_lit_image_mset intro: map_literal_map_uprod_cong)

global_interpretation uprod_literal_functor: natural_functor_conversion where 
  map = map_uprod_literal and to_set = uprod_literal_to_set and map_to = map_uprod_literal and 
  map_from = map_uprod_literal and map' = map_uprod_literal and to_set' = uprod_literal_to_set
  by unfold_locales (auto simp: mset_lit_image_mset)
 
end
