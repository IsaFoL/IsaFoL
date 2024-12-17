theory Uprod_Extra
  imports
    "HOL-Library.Uprod"
    Multiset_Extra
    Abstract_Substitution.Natural_Functor
begin

abbreviation upair where
  "upair \<equiv> \<lambda>(x, y). Upair x y"

lemma Upair_sym: "Upair x y = Upair y x"
  by (metis Upair_inject)

lemma upair_in_sym [simp]:
  assumes "sym I"
  shows "Upair a b \<in> upair ` I \<longleftrightarrow> (a, b) \<in> I \<and> (b, a) \<in> I"
  using assms
  by (auto dest: symD)

lemma ex_ordered_Upair:
  assumes tot: "totalp_on (set_uprod p) R"
  shows "\<exists>x y. p = Upair x y \<and> R\<^sup>=\<^sup>= x y"
proof -
  obtain x y where "p = Upair x y"
    by (metis uprod_exhaust)

  show ?thesis
  proof (cases "R\<^sup>=\<^sup>= x y")
    case True
    show ?thesis
    proof (intro exI conjI)
      show "p = Upair x y"
        using \<open>p = Upair x y\<close> .
    next
      show "R\<^sup>=\<^sup>= x y"
        using True by simp
    qed
  next
    case False
    then show ?thesis
    proof (intro exI conjI)
      show "p = Upair y x"
        using \<open>p = Upair x y\<close> by simp
    next
      from tot have "R y x"
        using False
        by (simp add: \<open>p = Upair x y\<close> totalp_on_def)
      thus "R\<^sup>=\<^sup>= y x"
        by simp
    qed
  qed
qed

definition mset_uprod :: "'a uprod \<Rightarrow> 'a multiset" where
  "mset_uprod = case_uprod (Abs_commute (\<lambda>x y. {#x, y#}))"

lemma Abs_commute_inverse_mset[simp]:
  "apply_commute (Abs_commute (\<lambda>x y. {#x, y#})) = (\<lambda>x y. {#x, y#})"
  by (simp add: Abs_commute_inverse)

lemma set_mset_mset_uprod[simp]: "set_mset (mset_uprod up) = set_uprod up"
  by (simp add: mset_uprod_def case_uprod.rep_eq set_uprod.rep_eq case_prod_beta)

lemma mset_uprod_Upair[simp]: "mset_uprod (Upair x y) = {#x, y#}"
  by (simp add: mset_uprod_def)

lemma map_uprod_inverse: "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>y. map_uprod f (map_uprod g y) = y)"
  by (simp add: uprod.map_comp uprod.map_ident_strong)

lemma mset_uprod_image_mset: "mset_uprod (map_uprod f p) = image_mset f (mset_uprod p)"
proof-
  obtain x y where [simp]: "p = Upair x y"
    using uprod_exhaust by blast

  have "mset_uprod (map_uprod f p) = {# f x, f y #}"
    by simp

  then show "mset_uprod (map_uprod f p) = image_mset f (mset_uprod p)"
    by simp
qed

lemma ball_set_uprod [simp]: "(\<forall>t\<in>set_uprod (Upair t\<^sub>1 t\<^sub>2). P t) \<longleftrightarrow> P t\<^sub>1 \<and> P t\<^sub>2"
  by auto

lemma inj_mset_uprod: "inj mset_uprod"
proof(unfold inj_def, intro allI impI)
  fix a b :: "'a uprod"
  assume "mset_uprod a = mset_uprod b"
  then show "a = b"
    by(cases a; cases b)(auto simp: add_mset_eq_add_mset)
qed

lemma mset_uprod_plus_neq: "mset_uprod a \<noteq> mset_uprod b + mset_uprod b"
  by(cases a; cases b)(auto simp: add_mset_eq_add_mset)

lemma set_uprod_not_empty: "set_uprod a \<noteq> {}"
  by(cases a) simp

lemma exists_uprod [intro]: "\<exists>a. x \<in> set_uprod a"
  by (metis insertI1 set_uprod_simps)

global_interpretation uprod_functor: finite_natural_functor where map = map_uprod and to_set = set_uprod
  by
    unfold_locales 
    (auto simp: uprod.map_comp uprod.map_ident uprod.set_map intro: uprod.map_cong)

global_interpretation uprod_functor: natural_functor_conversion where 
  map = map_uprod and to_set = set_uprod and map_to = map_uprod and map_from = map_uprod and 
  map' = map_uprod and to_set' = set_uprod
  by unfold_locales (auto simp: uprod.set_map uprod.map_comp)
  
end
