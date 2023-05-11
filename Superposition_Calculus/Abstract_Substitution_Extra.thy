theory Abstract_Substitution_Extra
  imports Main
begin

locale basic_substitution_ops =
  fixes
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 67) and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67)
begin

definition subst_set :: "'x set \<Rightarrow> 's \<Rightarrow> 'x set" (infixl "\<cdot>s" 67) where
  "subst_set X \<sigma> = (\<lambda>x. subst x \<sigma>) ` X"

definition is_ground :: "'x \<Rightarrow> bool" where
  "is_ground x \<longleftrightarrow> (\<forall>\<sigma>. x = x \<cdot> \<sigma>)"

definition is_ground_set :: "'x set \<Rightarrow> bool" where
  "is_ground_set X \<longleftrightarrow> (\<forall>x \<in> X. is_ground x)"

definition is_ground_subst :: "'s \<Rightarrow> bool" where
  "is_ground_subst \<gamma> \<longleftrightarrow> (\<forall>x. is_ground (x \<cdot> \<gamma>))"

definition generalizes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "generalizes x y \<longleftrightarrow> (\<exists>\<sigma>. x \<cdot> \<sigma> = y)"

definition strictly_generalizes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "strictly_generalizes x y \<longleftrightarrow> generalizes x y \<and> \<not> generalizes y x"

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
  "is_unifier \<sigma> X \<longleftrightarrow> card (X \<cdot>s \<sigma>) \<le> 1"

definition is_unifiers :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_unifiers \<sigma> XX \<longleftrightarrow> (\<forall>X \<in> XX. is_unifier \<sigma> X)"

definition is_mgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_mgu \<sigma> XX \<longleftrightarrow> is_unifiers \<sigma> XX \<and> (\<forall>\<tau>. is_unifiers \<tau> XX \<longrightarrow> (\<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>))"

definition is_imgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_imgu \<sigma> XX \<longleftrightarrow> is_unifiers \<sigma> XX \<and> (\<forall>\<tau>. is_unifiers \<tau> XX \<longrightarrow> \<tau> = \<sigma> \<odot> \<tau>)"

definition is_idem :: "'s \<Rightarrow> bool" where
  "is_idem \<sigma> \<longleftrightarrow> (\<sigma> \<odot> \<sigma>) = \<sigma>"

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

lemma subst_set_empty[simp]: "{} \<cdot>s \<sigma> = {}"
  by (simp only: subst_set_def image_empty)

lemma subst_set_insert[simp]: "(insert x X) \<cdot>s \<sigma> = insert (x \<cdot> \<sigma>) (X \<cdot>s \<sigma>)"
  by (simp only: subst_set_def image_insert)

lemma subst_set_union[simp]: "(X1 \<union> X2) \<cdot>s \<sigma> = X1 \<cdot>s \<sigma> \<union> X2 \<cdot>s \<sigma>"
  by (simp only: subst_set_def image_Un)

lemma is_unifiers_union: "is_unifiers \<upsilon> (XX\<^sub>1 \<union> XX\<^sub>2) \<longleftrightarrow> is_unifiers \<upsilon> XX\<^sub>1 \<and> is_unifiers \<upsilon> XX\<^sub>2"
  by (auto simp add: is_unifiers_def)


subsection \<open>Substituting on Ground Expressions\<close>

lemma subst_ident_if_ground[simp]: "is_ground x \<Longrightarrow> x \<cdot> \<sigma> = x"
  unfolding is_ground_def by simp

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

lemma
  assumes "is_unifier \<upsilon> {t\<^sub>1, t\<^sub>2}" and "is_ground t\<^sub>1" and "is_ground t\<^sub>2"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms by (simp add: card_Suc_eq is_unifier_def le_Suc_eq subst_set_def)

lemma is_unifier_subset: "is_unifier \<upsilon> A \<Longrightarrow> finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_unifier \<upsilon> B"
  by (smt (verit, best) card_mono dual_order.trans finite_imageI image_mono is_unifier_def
      subst_set_def)

lemma is_ground_set_subset: "is_ground_set A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_ground_set B"
  by (auto simp: is_ground_set_def)

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

end


locale basic_substitution = basic_substitution_ops subst id_subst comp_subst for
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 67) and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) +
  assumes
    subst_id_subst[simp]: "x \<cdot> id_subst = x" and
    subst_comp_subst[simp]: "x \<cdot> (\<sigma> \<odot> \<tau>) = (x \<cdot> \<sigma>) \<cdot> \<tau>" and
    subst_ext: "(\<And>x. x \<cdot> \<sigma> = x \<cdot> \<tau>) \<Longrightarrow> \<sigma> = \<tau>" (* and
    make_ground_subst: "is_ground_set (X \<cdot>s \<sigma>) \<Longrightarrow> \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>x \<in> X. x \<cdot> \<tau> = x \<cdot> \<sigma>)" *)
begin

subsection \<open>Identity Substitution\<close>

lemma subst_set_id_subst[simp]: "X \<cdot>s id_subst = X"
  by (simp add: subst_set_def)

lemma id_subst_comp_subst[simp]: "id_subst \<odot> \<sigma> = \<sigma>"
  by (rule subst_ext) simp

lemma comp_subst_id_subst[simp]: "\<sigma> \<odot> id_subst = \<sigma>"
  by (rule subst_ext) simp

lemma is_renaming_id_subst[simp]: "is_renaming id_subst"
  by (simp add: is_renaming_def)

lemma is_unifier_id_subst_empty[simp]: "is_unifier id_subst {}"
  by (simp add: is_unifier_def)

lemma is_unifiers_id_subst_empty[simp]: "is_unifiers id_subst {}"
  by (simp add: is_unifiers_def)

lemma is_mgu_id_subst_empty[simp]: "is_mgu id_subst {}"
  by (simp add: is_mgu_def)

lemma is_imgu_id_subst_empty[simp]: "is_imgu id_subst {}"
  by (simp add: is_imgu_def)

lemma is_idem_id_subst[simp]: "is_idem id_subst"
  by (simp add: is_idem_def)

lemma is_unifier_id_subst: "is_unifier id_subst X \<longleftrightarrow> card X \<le> 1"
  by (simp add: is_unifier_def)

lemma is_unifiers_id_subst: "is_unifiers id_subst XX \<longleftrightarrow> (\<forall>X \<in> XX. card X \<le> 1)"
  by (simp add: is_unifiers_def is_unifier_id_subst)

lemma is_mgu_id_subst: "is_mgu id_subst XX \<longleftrightarrow> (\<forall>X \<in> XX. card X \<le> 1)"
  by (simp add: is_mgu_def is_unifiers_id_subst)

lemma is_imgu_id_subst: "is_imgu id_subst XX \<longleftrightarrow> (\<forall>X \<in> XX. card X \<le> 1)"
  by (simp add: is_imgu_def is_unifiers_id_subst)

lemma is_unifiers_id_subst_insert_singleton[simp]:
  "is_unifiers id_subst (insert {x} XX) \<longleftrightarrow> is_unifiers id_subst XX"
  by (simp add: is_unifiers_id_subst)

lemma is_mgu_id_subst_insert_singleton[simp]:
  "is_mgu id_subst (insert {x} XX) \<longleftrightarrow> is_mgu id_subst XX"
  by (simp add: is_mgu_id_subst)

lemma is_imgu_id_subst_insert_singleton[simp]:
  "is_imgu id_subst (insert {x} XX) \<longleftrightarrow> is_imgu id_subst XX"
  by (simp add: is_imgu_id_subst)


subsection \<open>Associativity of Composition\<close>

lemma comp_subst_assoc[simp]: "\<sigma> \<odot> (\<tau> \<odot> \<gamma>) = \<sigma> \<odot> \<tau> \<odot> \<gamma>"
  by (rule subst_ext) simp


subsection \<open>IMGU is Idempotent and an MGU\<close>

lemma is_imgu_iff_is_idem_and_is_mgu: "is_imgu \<mu> XX \<longleftrightarrow> is_idem \<mu> \<and> is_mgu \<mu> XX"
  by (auto simp: is_imgu_def is_idem_def is_mgu_def)


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