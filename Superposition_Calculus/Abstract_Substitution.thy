theory Abstract_Substitution
  imports Main
begin

locale basic_substitution_ops =
  fixes
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 67) and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) and
    is_ground :: "'x \<Rightarrow> bool"
begin

definition subst_set :: "'x set \<Rightarrow> 's \<Rightarrow> 'x set" (infixl "\<cdot>s" 67) where
  "subst_set X \<sigma> = (\<lambda>x. subst x \<sigma>) ` X"

definition is_ground_set :: "'x set \<Rightarrow> bool" where
  "is_ground_set X \<longleftrightarrow> (\<forall>x \<in> X. is_ground x)"

definition is_ground_subst :: "'s \<Rightarrow> bool" where
  "is_ground_subst \<gamma> \<longleftrightarrow> (\<forall>x. is_ground (x \<cdot> \<gamma>))"

definition generalizes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "generalizes x y \<longleftrightarrow> (\<exists>\<sigma>. x \<cdot> \<sigma> = y)"

definition specializes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "specializes x y \<equiv> generalizes y x"

definition strictly_generalizes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "strictly_generalizes x y \<longleftrightarrow> generalizes x y \<and> \<not> generalizes y x"

definition strictly_specializes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "strictly_specializes x y \<equiv> strictly_generalizes y x"

definition instances_of :: "'x \<Rightarrow> 'x set" where
  "instances_of x = {y. generalizes x y}"

definition instances_of_set :: "'x set \<Rightarrow> 'x set" where
  "instances_of_set X = (\<Union>x \<in> X. instances_of x)"

definition ground_instances_of :: "'x \<Rightarrow> 'x set" where
  "ground_instances_of x = {x\<^sub>\<G> \<in> instances_of x. is_ground x\<^sub>\<G>}"

definition ground_instances_of_set :: "'x set \<Rightarrow> 'x set" where
  "ground_instances_of_set X = {x\<^sub>\<G> \<in> instances_of_set X. is_ground x\<^sub>\<G>}"

lemma ground_instances_of_set_eq_Union_ground_instances_of:
  "ground_instances_of_set X = (\<Union>x \<in> X. ground_instances_of x)"
  unfolding ground_instances_of_set_def ground_instances_of_def
  unfolding instances_of_set_def
  by auto

lemma ground_instances_of_eq_Collect_subst_grounding:
  "ground_instances_of x = {x \<cdot> \<gamma> | \<gamma>. is_ground (x \<cdot> \<gamma>)}"
  by (auto simp: ground_instances_of_def instances_of_def generalizes_def)

definition is_renaming :: "'s \<Rightarrow> bool" where
  "is_renaming \<rho> \<longleftrightarrow> (\<exists>\<sigma>. \<rho> \<odot> \<sigma> = id_subst)"

definition is_unifier :: "'s \<Rightarrow> 'x set \<Rightarrow> bool" where
  "is_unifier \<upsilon> X \<longleftrightarrow> card (X \<cdot>s \<upsilon>) \<le> 1"

definition is_unifier_set :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_unifier_set \<upsilon> XX \<longleftrightarrow> (\<forall>X \<in> XX. is_unifier \<upsilon> X)"

definition is_mgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_mgu \<mu> XX \<longleftrightarrow> is_unifier_set \<mu> XX \<and> (\<forall>\<upsilon>. is_unifier_set \<upsilon> XX \<longrightarrow> (\<exists>\<sigma>. \<upsilon> = \<mu> \<odot> \<sigma>))"

definition is_imgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_imgu \<mu> XX \<longleftrightarrow> is_unifier_set \<mu> XX \<and> (\<forall>\<tau>. is_unifier_set \<tau> XX \<longrightarrow> \<tau> = \<mu> \<odot> \<tau>)"

definition is_idem :: "'s \<Rightarrow> bool" where
  "is_idem \<sigma> \<longleftrightarrow> \<sigma> \<odot> \<sigma> = \<sigma>"

lemma is_unifier_iff_if_finite:
  assumes "finite X"
  shows "is_unifier \<sigma> X \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. x \<cdot> \<sigma> = y \<cdot> \<sigma>)"
proof (rule iffI)
  show "is_unifier \<sigma> X \<Longrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. x \<cdot> \<sigma> = y \<cdot> \<sigma>)"
    using assms
    unfolding is_unifier_def
    by (metis One_nat_def card_le_Suc0_iff_eq finite_imageI image_eqI subst_set_def)
next
  show "(\<forall>x\<in>X. \<forall>y\<in>X. x \<cdot> \<sigma> = y \<cdot> \<sigma>) \<Longrightarrow> is_unifier \<sigma> X"
    unfolding is_unifier_def
    by (smt (verit, del_insts) One_nat_def basic_substitution_ops.subst_set_def card_eq_0_iff
        card_le_Suc0_iff_eq dual_order.eq_iff imageE le_Suc_eq)
qed

lemma is_unifier_singleton[simp]: "is_unifier \<upsilon> {x}"
  by (simp add: is_unifier_iff_if_finite)

lemma is_unifier_set_insert_singleton[simp]:
  "is_unifier_set \<sigma> (insert {x} XX) \<longleftrightarrow> is_unifier_set \<sigma> XX"
  by (simp add: is_unifier_set_def)

lemma is_mgu_insert_singleton[simp]: "is_mgu \<mu> (insert {x} XX) \<longleftrightarrow> is_mgu \<mu> XX"
  by (simp add: is_mgu_def)

lemma is_imgu_insert_singleton[simp]: "is_imgu \<mu> (insert {x} XX) \<longleftrightarrow> is_imgu \<mu> XX"
  by (simp add: is_imgu_def)

lemma subst_set_empty[simp]: "{} \<cdot>s \<sigma> = {}"
  by (simp only: subst_set_def image_empty)

lemma subst_set_insert[simp]: "(insert x X) \<cdot>s \<sigma> = insert (x \<cdot> \<sigma>) (X \<cdot>s \<sigma>)"
  by (simp only: subst_set_def image_insert)

lemma subst_set_union[simp]: "(X1 \<union> X2) \<cdot>s \<sigma> = X1 \<cdot>s \<sigma> \<union> X2 \<cdot>s \<sigma>"
  by (simp only: subst_set_def image_Un)

lemma is_unifier_set_union: "is_unifier_set \<upsilon> (XX\<^sub>1 \<union> XX\<^sub>2) \<longleftrightarrow> is_unifier_set \<upsilon> XX\<^sub>1 \<and> is_unifier_set \<upsilon> XX\<^sub>2"
  by (auto simp add: is_unifier_set_def)

lemma is_unifier_subset: "is_unifier \<upsilon> A \<Longrightarrow> finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_unifier \<upsilon> B"
  by (smt (verit, best) card_mono dual_order.trans finite_imageI image_mono is_unifier_def
      subst_set_def)

lemma is_ground_set_subset: "is_ground_set A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_ground_set B"
  by (auto simp: is_ground_set_def)

lemma is_ground_set_ground_instances_of[simp]: "is_ground_set (ground_instances_of x)"
  by (simp add: ground_instances_of_def is_ground_set_def)

lemma is_ground_set_ground_instances_of_set[simp]: "is_ground_set (ground_instances_of_set x)"
  by (simp add: ground_instances_of_set_def is_ground_set_def)

end


(* Rename to abstract substitution *)
locale basic_substitution =
  basic_substitution_ops subst id_subst comp_subst is_ground +
  comp_subst: monoid comp_subst id_subst
  for
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) and
    id_subst :: 's and
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 67) and
    is_ground :: "'x \<Rightarrow> bool" +
  assumes
    subst_id_subst[simp]: "x \<cdot> id_subst = x" and
    subst_comp_subst[simp]: "x \<cdot> (\<sigma> \<odot> \<tau>) = (x \<cdot> \<sigma>) \<cdot> \<tau>" and
    all_subst_ident_if_ground: "is_ground x \<Longrightarrow> (\<forall>\<sigma>. x \<cdot> \<sigma> = x)"
begin


subsection \<open>Identity Substitution\<close>

lemma subst_set_id_subst[simp]: "X \<cdot>s id_subst = X"
  by (simp add: subst_set_def)

lemma is_renaming_id_subst[simp]: "is_renaming id_subst"
  by (simp add: is_renaming_def)

lemma is_unifier_id_subst_empty[simp]: "is_unifier id_subst {}"
  by (simp add: is_unifier_def)

lemma is_unifier_set_id_subst_empty[simp]: "is_unifier_set id_subst {}"
  by (simp add: is_unifier_set_def)

lemma is_mgu_id_subst_empty[simp]: "is_mgu id_subst {}"
  by (simp add: is_mgu_def)

lemma is_imgu_id_subst_empty[simp]: "is_imgu id_subst {}"
  by (simp add: is_imgu_def)

lemma is_idem_id_subst[simp]: "is_idem id_subst"
  by (simp add: is_idem_def)

lemma is_unifier_id_subst: "is_unifier id_subst X \<longleftrightarrow> card X \<le> 1"
  by (simp add: is_unifier_def)

lemma is_unifier_set_id_subst: "is_unifier_set id_subst XX \<longleftrightarrow> (\<forall>X \<in> XX. card X \<le> 1)"
  by (simp add: is_unifier_set_def is_unifier_id_subst)

lemma is_mgu_id_subst: "is_mgu id_subst XX \<longleftrightarrow> (\<forall>X \<in> XX. card X \<le> 1)"
  by (simp add: is_mgu_def is_unifier_set_id_subst)

lemma is_imgu_id_subst: "is_imgu id_subst XX \<longleftrightarrow> (\<forall>X \<in> XX. card X \<le> 1)"
  by (simp add: is_imgu_def is_unifier_set_id_subst)


subsection \<open>Generalization\<close>

sublocale generalizes: preorder generalizes strictly_generalizes
proof unfold_locales
  show "\<And>x y. strictly_generalizes x y = (generalizes x y \<and> \<not> generalizes y x)"
    unfolding strictly_generalizes_def generalizes_def by blast
next
  show "\<And>x. generalizes x x"
    unfolding generalizes_def using subst_id_subst by metis
next
  show "\<And>x y z. generalizes x y \<Longrightarrow> generalizes y z \<Longrightarrow> generalizes x z"
    unfolding generalizes_def using subst_comp_subst by metis
qed


subsection \<open>Substituting on Ground Expressions\<close>

lemma subst_ident_if_ground[simp]: "is_ground x \<Longrightarrow> x \<cdot> \<sigma> = x"
  using all_subst_ident_if_ground by simp

lemma subst_set_ident_if_ground[simp]: "is_ground_set X \<Longrightarrow> X \<cdot>s \<sigma> = X"
  unfolding is_ground_set_def subst_set_def by simp

subsection \<open>Instances of Ground Expressions\<close>

lemma instances_of_ident_if_ground[simp]: "is_ground x \<Longrightarrow> instances_of x = {x}"
  unfolding instances_of_def generalizes_def by simp

lemma instances_of_set_ident_if_ground[simp]: "is_ground_set X \<Longrightarrow> instances_of_set X = X"
  unfolding instances_of_set_def is_ground_set_def by simp

lemma ground_instances_of_ident_if_ground[simp]: "is_ground x \<Longrightarrow> ground_instances_of x = {x}"
  unfolding ground_instances_of_def by auto

lemma ground_instances_of_set_ident_if_ground[simp]: "is_ground_set X \<Longrightarrow> ground_instances_of_set X = X"
  unfolding is_ground_set_def ground_instances_of_set_eq_Union_ground_instances_of by simp


subsection \<open>Unifier of Ground Expressions\<close>

lemma ground_eq_ground_if_unifiable:
  assumes "is_unifier \<upsilon> {t\<^sub>1, t\<^sub>2}" and "is_ground t\<^sub>1" and "is_ground t\<^sub>2"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms by (simp add: card_Suc_eq is_unifier_def le_Suc_eq subst_set_def)

lemma ball_eq_constant_if_unifier:
  assumes "finite X" and "x \<in> X" and "is_unifier \<upsilon> X" and "is_ground_set X"
  shows "\<forall>y \<in> X. y = x"
  using assms
proof (induction X rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert z F)
  then show ?case
    by (metis is_ground_set_def finite.insertI is_unifier_iff_if_finite subst_ident_if_ground)
qed

lemma subst_mgu_eq_subst_mgu: 
  assumes "is_mgu \<mu> {{t\<^sub>1, t\<^sub>2}}" 
  shows "t\<^sub>1 \<cdot> \<mu> = t\<^sub>2 \<cdot> \<mu>"
  using assms is_unifier_iff_if_finite[of "{t\<^sub>1, t\<^sub>2}"]
  unfolding is_mgu_def is_unifier_set_def
  by blast

lemma subst_imgu_eq_subst_imgu: 
  assumes "is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}" 
  shows "t\<^sub>1 \<cdot> \<mu> = t\<^sub>2 \<cdot> \<mu>"
  using assms is_unifier_iff_if_finite[of "{t\<^sub>1, t\<^sub>2}"]
  unfolding is_imgu_def is_unifier_set_def
  by blast


subsection \<open>Ground Substitutions\<close>

lemma is_ground_subst_comp_left: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_subst (\<sigma> \<odot> \<tau>)"
  by (simp add: is_ground_subst_def)

lemma is_ground_subst_comp_right: "is_ground_subst \<tau> \<Longrightarrow> is_ground_subst (\<sigma> \<odot> \<tau>)"
  by (simp add: is_ground_subst_def)


subsection \<open>IMGU is Idempotent and an MGU\<close>

lemma is_imgu_iff_is_idem_and_is_mgu: "is_imgu \<mu> XX \<longleftrightarrow> is_idem \<mu> \<and> is_mgu \<mu> XX"
  by (auto simp add: is_imgu_def is_idem_def is_mgu_def simp flip: comp_subst.assoc)


subsection \<open>Groundings Idempotence\<close>

lemma image_ground_instances_of_ground_instances_of:
  "ground_instances_of ` ground_instances_of x = (\<lambda>x. {x}) ` ground_instances_of x"
proof (rule image_cong)
  show "\<And>x\<^sub>\<G>. x\<^sub>\<G> \<in> ground_instances_of x \<Longrightarrow> ground_instances_of x\<^sub>\<G> = {x\<^sub>\<G>}"
    using ground_instances_of_ident_if_ground ground_instances_of_def by auto
qed simp

lemma grounding_of_set_grounding_of_set_idem[simp]:
  "ground_instances_of_set (ground_instances_of_set X) = ground_instances_of_set X"
  unfolding ground_instances_of_set_eq_Union_ground_instances_of UN_UN_flatten
  unfolding image_ground_instances_of_ground_instances_of
  by simp


subsection \<open>Instances of Substitution\<close>

lemma instances_of_subst:
  "instances_of (x \<cdot> \<sigma>) \<subseteq> instances_of x"
proof (rule subsetI)
  fix x\<^sub>\<sigma> assume "x\<^sub>\<sigma> \<in> instances_of (x \<cdot> \<sigma>)"
  thus "x\<^sub>\<sigma> \<in> instances_of x"
    by (metis CollectD CollectI generalizes_def instances_of_def subst_comp_subst)
qed

lemma instances_of_set_subst_set:
  "instances_of_set (X \<cdot>s \<sigma>) \<subseteq> instances_of_set X"
  unfolding instances_of_set_def subst_set_def
  using instances_of_subst by auto

lemma ground_instances_of_subst:
  "ground_instances_of (x \<cdot> \<sigma>) \<subseteq> ground_instances_of x"
  unfolding ground_instances_of_def
  using instances_of_subst by auto

lemma ground_instances_of_set_subst_set:
  "ground_instances_of_set (X \<cdot>s \<sigma>) \<subseteq> ground_instances_of_set X"
  unfolding ground_instances_of_set_def
  using instances_of_set_subst_set by auto


subsection \<open>Instances of Renamed Expressions\<close>

lemma instances_of_subst_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> instances_of (x \<cdot> \<rho>) = instances_of x"
  by (metis instances_of_subst is_renaming_def subset_antisym subst_comp_subst subst_id_subst)

lemma instances_of_set_subst_set_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> instances_of_set (X \<cdot>s \<rho>) = instances_of_set X"
  by (simp add: instances_of_set_def subst_set_def)

lemma ground_instances_of_subst_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> ground_instances_of (x \<cdot> \<rho>) = ground_instances_of x"
  by (simp add: ground_instances_of_def)

lemma ground_instances_of_set_subst_set_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> ground_instances_of_set (X \<cdot>s \<rho>) = ground_instances_of_set X"
  by (simp add: ground_instances_of_set_def)

end

end