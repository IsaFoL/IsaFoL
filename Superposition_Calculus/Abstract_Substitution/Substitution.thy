theory Substitution
  imports Main
begin

section \<open>General Results on Groups\<close>

lemma (in monoid) right_inverse_idem:
  fixes inv
  assumes right_inverse:  "\<And>a. a \<^bold>* inv a = \<^bold>1"
  shows "\<And>a. inv (inv a) = a"
    by (metis assoc right_inverse right_neutral)

lemma (in monoid) left_inverse_if_right_inverse:
  fixes inv
  assumes
    right_inverse:  "\<And>a. a \<^bold>* inv a = \<^bold>1"
  shows "inv a \<^bold>* a = \<^bold>1"
  by (metis right_inverse_idem right_inverse)

lemma (in monoid) group_wrt_right_inverse:
  fixes inv
  assumes right_inverse:  "\<And>a. a \<^bold>* inv a = \<^bold>1"
  shows "group (\<^bold>*) \<^bold>1 inv"
proof unfold_locales
  show "\<And>a. \<^bold>1 \<^bold>* a = a"
    by simp
next
  show "\<And>a. inv a \<^bold>* a = \<^bold>1"
    by (metis left_inverse_if_right_inverse right_inverse)
qed


section \<open>Semigroup Action\<close>

text \<open>We define both left and right semigroup actions. Left semigroup actions seem to be prevalent
in algebra, but right semigroup actions directly uses the usual notation of term/atom/literal/clause
substitution.\<close>

locale left_semigroup_action = semigroup +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infix "\<cdot>" 70)
  assumes action_compatibility[simp]: "\<And>a b x. (a \<^bold>* b) \<cdot> x = a \<cdot> (b \<cdot> x)"

locale right_semigroup_action = semigroup +
  fixes action :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infix "\<cdot>" 70)
  assumes action_compatibility[simp]: "\<And>x a b. x \<cdot> (a \<^bold>* b) = (x \<cdot> a) \<cdot> b"

text \<open>We then instantiate the right action in the context of the left action in order to get access
to any lemma proven in the context of the other locale. We do analogously in the context of the
right locale.\<close>

sublocale left_semigroup_action \<subseteq> right: right_semigroup_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
proof unfold_locales
  show "\<And>a b c. c \<^bold>* (b \<^bold>* a) = c \<^bold>* b \<^bold>* a"
    by (simp only: assoc)
next
  show "\<And>x a b. (b \<^bold>* a) \<cdot> x = b \<cdot> (a \<cdot> x)"
    by simp
qed

sublocale right_semigroup_action \<subseteq> left: left_semigroup_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
proof unfold_locales
  show "\<And>a b c. c \<^bold>* (b \<^bold>* a) = c \<^bold>* b \<^bold>* a"
    by (simp only: assoc)
next
  show "\<And>a b x. x \<cdot> (b \<^bold>* a) = (x \<cdot> b) \<cdot> a"
    by simp
qed

lemma (in right_semigroup_action) lifting_semigroup_action_to_set:
  "right_semigroup_action (\<^bold>*) (\<lambda>X a. (\<lambda>x. action x a) ` X)"
proof unfold_locales
  show "\<And>x a b. (\<lambda>x. x \<cdot> (a \<^bold>* b)) ` x = (\<lambda>x. x \<cdot> b) ` (\<lambda>x. x \<cdot> a) ` x"
    by (simp add: image_comp)
qed

lemma (in right_semigroup_action) lifting_semigroup_action_to_list:
  "right_semigroup_action (\<^bold>*) (\<lambda>xs a. map (\<lambda>x. action x a) xs)"
proof unfold_locales
  show "\<And>x a b. map (\<lambda>x. x \<cdot> (a \<^bold>* b)) x = map (\<lambda>x. x \<cdot> b) (map (\<lambda>x. x \<cdot> a) x)"
    by (simp add: image_comp)
qed


section \<open>Monoid Action\<close>

locale left_monoid_action = monoid +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infix "\<cdot>" 70)
  assumes
    monoid_action_compatibility: "\<And>a b x. (a \<^bold>* b) \<cdot> x = a \<cdot> (b \<cdot> x)" and
    action_neutral[simp]: "\<And>x. \<^bold>1 \<cdot> x = x"

locale right_monoid_action = monoid +
  fixes action :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infix "\<cdot>" 70)
  assumes
    monoid_action_compatibility: "\<And>x a b. x \<cdot> (a \<^bold>* b) = (x \<cdot> a) \<cdot> b" and
    action_neutral[simp]: "\<And>x. x \<cdot> \<^bold>1 = x"

sublocale left_monoid_action \<subseteq> left_semigroup_action
  by unfold_locales (fact monoid_action_compatibility)

sublocale right_monoid_action \<subseteq> right_semigroup_action
  by unfold_locales (fact monoid_action_compatibility)

sublocale left_monoid_action \<subseteq> right: right_monoid_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

sublocale right_monoid_action \<subseteq> left: left_monoid_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

lemma (in right_monoid_action) lifting_monoid_action_to_set:
  "right_monoid_action (\<^bold>*) \<^bold>1 (\<lambda>X a. (\<lambda>x. action x a) ` X)"
proof (unfold_locales)
  show "\<And>x a b. (\<lambda>x. x \<cdot> (a \<^bold>* b)) ` x = (\<lambda>x. x \<cdot> b) ` (\<lambda>x. x \<cdot> a) ` x"
    by (simp add: image_comp)
next
  show "\<And>x. (\<lambda>x. x \<cdot> \<^bold>1) ` x = x"
    by simp
qed

lemma (in right_monoid_action) lifting_monoid_action_to_list:
  "right_monoid_action (\<^bold>*) \<^bold>1 (\<lambda>xs a. map (\<lambda>x. action x a) xs)"
proof unfold_locales
  show "\<And>x a b. map (\<lambda>x. x \<cdot> (a \<^bold>* b)) x = map (\<lambda>x. x \<cdot> b) (map (\<lambda>x. x \<cdot> a) x)"
    by simp
next
  show "\<And>x. map (\<lambda>x. x \<cdot> \<^bold>1) x = x"
    by simp
qed


section \<open>Group Action\<close>

locale left_group_action = group +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infix "\<cdot>" 70)
  assumes
    group_action_compatibility: "\<And>a b x. (a \<^bold>* b) \<cdot> x = a \<cdot> (b \<cdot> x)" and
    group_action_neutral: "\<And>x. \<^bold>1 \<cdot> x = x"

locale right_group_action = group +
  fixes action :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<cdot>" 70)
  assumes
    group_action_compatibility: "\<And>x a b. x \<cdot> (a \<^bold>* b) = (x \<cdot> a) \<cdot> b" and
    group_action_neutral: "\<And>x. x \<cdot> \<^bold>1 = x"

sublocale left_group_action \<subseteq> left_monoid_action
  by unfold_locales (fact group_action_compatibility group_action_neutral)+

sublocale right_group_action \<subseteq> right_monoid_action
  by unfold_locales (fact group_action_compatibility group_action_neutral)+

sublocale left_group_action \<subseteq> right: right_group_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

sublocale right_group_action \<subseteq> left: left_group_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all


section \<open>Assumption-free Substitution\<close>

locale substitution_ops =
  fixes
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 67) and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) and
    is_ground :: "'x \<Rightarrow> bool"
begin

definition subst_set :: "'x set \<Rightarrow> 's \<Rightarrow> 'x set" where
  "subst_set X \<sigma> = (\<lambda>x. subst x \<sigma>) ` X"

definition subst_list :: "'x list \<Rightarrow> 's \<Rightarrow> 'x list" where
  "subst_list xs \<sigma> = map (\<lambda>x. subst x \<sigma>) xs"

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

definition instances :: "'x \<Rightarrow> 'x set" where
  "instances x = {y. generalizes x y}"

definition instances_set :: "'x set \<Rightarrow> 'x set" where
  "instances_set X = (\<Union>x \<in> X. instances x)"

definition ground_instances :: "'x \<Rightarrow> 'x set" where
  "ground_instances x = {x\<^sub>\<G> \<in> instances x. is_ground x\<^sub>\<G>}"

definition ground_instances_set :: "'x set \<Rightarrow> 'x set" where
  "ground_instances_set X = {x\<^sub>\<G> \<in> instances_set X. is_ground x\<^sub>\<G>}"

lemma ground_instances_set_eq_Union_ground_instances:
  "ground_instances_set X = (\<Union>x \<in> X. ground_instances x)"
  unfolding ground_instances_set_def ground_instances_def
  unfolding instances_set_def
  by auto

lemma ground_instances_eq_Collect_subst_grounding:
  "ground_instances x = {x \<cdot> \<gamma> | \<gamma>. is_ground (x \<cdot> \<gamma>)}"
  by (auto simp: ground_instances_def instances_def generalizes_def)

(* This corresponds to the maximal subgroup of the monoid on (\<odot>) and id_subst *)
definition is_renaming :: "'s \<Rightarrow> bool" where
  "is_renaming \<rho> \<longleftrightarrow> (\<exists>\<rho>_inv. \<rho> \<odot> \<rho>_inv = id_subst)"

definition renaming_inverse where
  "is_renaming \<rho> \<Longrightarrow> renaming_inverse \<rho> = (SOME \<rho>_inv. \<rho> \<odot> \<rho>_inv = id_subst)"

lemma renaming_comp_renaming_inverse[simp]:
  "is_renaming \<rho> \<Longrightarrow> \<rho> \<odot> renaming_inverse \<rho> = id_subst"
  by (auto simp: is_renaming_def renaming_inverse_def intro: someI_ex)

definition is_unifier :: "'s \<Rightarrow> 'x set \<Rightarrow> bool" where
  "is_unifier \<upsilon> X \<longleftrightarrow> card (subst_set X \<upsilon>) \<le> 1"

definition is_unifier_set :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_unifier_set \<upsilon> XX \<longleftrightarrow> (\<forall>X \<in> XX. is_unifier \<upsilon> X)"

definition is_mgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_mgu \<mu> XX \<longleftrightarrow> is_unifier_set \<mu> XX \<and> (\<forall>\<upsilon>. is_unifier_set \<upsilon> XX \<longrightarrow> (\<exists>\<sigma>. \<mu> \<odot> \<sigma> = \<upsilon>))"

definition is_imgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_imgu \<mu> XX \<longleftrightarrow> is_unifier_set \<mu> XX \<and> (\<forall>\<tau>. is_unifier_set \<tau> XX \<longrightarrow> \<mu> \<odot> \<tau> = \<tau>)"

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
    by (smt (verit, del_insts) One_nat_def substitution_ops.subst_set_def card_eq_0_iff
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

lemma subst_set_empty[simp]: "subst_set {} \<sigma> = {}"
  by (simp only: subst_set_def image_empty)

lemma subst_set_insert[simp]: "subst_set (insert x X) \<sigma> = insert (x \<cdot> \<sigma>) (subst_set X \<sigma>)"
  by (simp only: subst_set_def image_insert)

lemma subst_set_union[simp]: "subst_set (X1 \<union> X2) \<sigma> = subst_set X1 \<sigma> \<union> subst_set X2 \<sigma>"
  by (simp only: subst_set_def image_Un)

lemma subst_list_Nil[simp]: "subst_list [] \<sigma> = []"
  by (simp only: subst_list_def list.map)

lemma subst_list_insert[simp]: "subst_list (x # xs) \<sigma> = (x \<cdot> \<sigma>) # (subst_list xs \<sigma>)"
  by (simp only: subst_list_def list.map)

lemma subst_list_append[simp]: "subst_list (xs\<^sub>1 @ xs\<^sub>2) \<sigma> = subst_list xs\<^sub>1 \<sigma> @ subst_list xs\<^sub>2 \<sigma>"
  by (simp only: subst_list_def map_append)

lemma is_unifier_set_union:
  "is_unifier_set \<upsilon> (XX\<^sub>1 \<union> XX\<^sub>2) \<longleftrightarrow> is_unifier_set \<upsilon> XX\<^sub>1 \<and> is_unifier_set \<upsilon> XX\<^sub>2"
  by (auto simp add: is_unifier_set_def)

lemma is_unifier_subset: "is_unifier \<upsilon> A \<Longrightarrow> finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_unifier \<upsilon> B"
  by (smt (verit, best) card_mono dual_order.trans finite_imageI image_mono is_unifier_def
      subst_set_def)

lemma is_ground_set_subset: "is_ground_set A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_ground_set B"
  by (auto simp: is_ground_set_def)

lemma is_ground_set_ground_instances[simp]: "is_ground_set (ground_instances x)"
  by (simp add: ground_instances_def is_ground_set_def)

lemma is_ground_set_ground_instances_set[simp]: "is_ground_set (ground_instances_set x)"
  by (simp add: ground_instances_set_def is_ground_set_def)

end


section \<open>Basic Substitution\<close>

(* Rename to abstract substitution *)
locale substitution =
  comp_subst: right_monoid_action comp_subst id_subst subst +
  substitution_ops subst id_subst comp_subst is_ground
  for
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 70) and
    id_subst :: 's and
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 70) and

    \<comment> \<open>Predicate identifying the fixed elements w.r.t. the monoid action\<close>
    is_ground :: "'x \<Rightarrow> bool" +
  assumes
    all_subst_ident_if_ground: "is_ground x \<Longrightarrow> (\<forall>\<sigma>. x \<cdot> \<sigma> = x)"
begin

sublocale comp_subst_set: right_monoid_action comp_subst id_subst subst_set
  using comp_subst.lifting_monoid_action_to_set unfolding subst_set_def .

sublocale comp_subst_list: right_monoid_action comp_subst id_subst subst_list
  using comp_subst.lifting_monoid_action_to_list unfolding subst_list_def .


subsection \<open>Substitution Composition\<close>

lemmas subst_comp_subst = comp_subst.action_compatibility
lemmas subst_set_comp_subst = comp_subst_set.action_compatibility
lemmas subst_list_comp_subst = comp_subst_list.action_compatibility


subsection \<open>Substitution Identity\<close>

lemmas subst_id_subst = comp_subst.action_neutral
lemmas subst_set_id_subst = comp_subst_set.action_neutral
lemmas subst_list_id_subst = comp_subst_list.action_neutral

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

lemma subst_set_ident_if_ground[simp]: "is_ground_set X \<Longrightarrow> subst_set X \<sigma> = X"
  unfolding is_ground_set_def subst_set_def by simp


subsection \<open>Instances of Ground Expressions\<close>

lemma instances_ident_if_ground[simp]: "is_ground x \<Longrightarrow> instances x = {x}"
  unfolding instances_def generalizes_def by simp

lemma instances_set_ident_if_ground[simp]: "is_ground_set X \<Longrightarrow> instances_set X = X"
  unfolding instances_set_def is_ground_set_def by simp

lemma ground_instances_ident_if_ground[simp]: "is_ground x \<Longrightarrow> ground_instances x = {x}"
  unfolding ground_instances_def by auto

lemma ground_instances_set_ident_if_ground[simp]: "is_ground_set X \<Longrightarrow> ground_instances_set X = X"
  unfolding is_ground_set_def ground_instances_set_eq_Union_ground_instances by simp


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

lemma is_ground_subst_is_ground: 
  assumes "is_ground_subst \<gamma>" 
  shows "is_ground (t \<cdot> \<gamma>)"
  using assms is_ground_subst_def by blast


subsection \<open>IMGU is Idempotent and an MGU\<close>

lemma is_imgu_iff_is_idem_and_is_mgu: "is_imgu \<mu> XX \<longleftrightarrow> is_idem \<mu> \<and> is_mgu \<mu> XX"
  by (auto simp add: is_imgu_def is_idem_def is_mgu_def simp flip: comp_subst.assoc)


subsection \<open>IMGU can be used before unification\<close>

lemma subst_imgu_subst_unifier:
  assumes unif: "is_unifier \<upsilon> X" and imgu: "is_imgu \<mu> {X}" and "x \<in> X"
  shows "x \<cdot> \<mu> \<cdot> \<upsilon> = x \<cdot> \<upsilon>"
proof -
  have "x \<cdot> \<mu> \<cdot> \<upsilon> = x \<cdot> (\<mu> \<odot> \<upsilon>)"
    by simp

  also have "\<dots> = x \<cdot> \<upsilon>"
    using imgu unif by (simp add: is_imgu_def is_unifier_set_def)

  finally show ?thesis .
qed


subsection \<open>Groundings Idempotence\<close>

lemma image_ground_instances_ground_instances:
  "ground_instances ` ground_instances x = (\<lambda>x. {x}) ` ground_instances x"
proof (rule image_cong)
  show "\<And>x\<^sub>\<G>. x\<^sub>\<G> \<in> ground_instances x \<Longrightarrow> ground_instances x\<^sub>\<G> = {x\<^sub>\<G>}"
    using ground_instances_ident_if_ground ground_instances_def by auto
qed simp

lemma grounding_of_set_grounding_of_set_idem[simp]:
  "ground_instances_set (ground_instances_set X) = ground_instances_set X"
  unfolding ground_instances_set_eq_Union_ground_instances UN_UN_flatten
  unfolding image_ground_instances_ground_instances
  by simp


subsection \<open>Instances of Substitution\<close>

lemma instances_subst:
  "instances (x \<cdot> \<sigma>) \<subseteq> instances x"
proof (rule subsetI)
  fix x\<^sub>\<sigma> assume "x\<^sub>\<sigma> \<in> instances (x \<cdot> \<sigma>)"
  thus "x\<^sub>\<sigma> \<in> instances x"
    by (metis CollectD CollectI generalizes_def instances_def subst_comp_subst)
qed

lemma instances_set_subst_set:
  "instances_set (subst_set X \<sigma>) \<subseteq> instances_set X"
  unfolding instances_set_def subst_set_def
  using instances_subst by auto

lemma ground_instances_subst:
  "ground_instances (x \<cdot> \<sigma>) \<subseteq> ground_instances x"
  unfolding ground_instances_def
  using instances_subst by auto

lemma ground_instances_set_subst_set:
  "ground_instances_set (subst_set X \<sigma>) \<subseteq> ground_instances_set X"
  unfolding ground_instances_set_def
  using instances_set_subst_set by auto


subsection \<open>Instances of Renamed Expressions\<close>

lemma instances_subst_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> instances (x \<cdot> \<rho>) = instances x"
  by (metis instances_subst is_renaming_def subset_antisym subst_comp_subst subst_id_subst)

lemma instances_set_subst_set_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> instances_set (subst_set X \<rho>) = instances_set X"
  by (simp add: instances_set_def subst_set_def)

lemma ground_instances_subst_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> ground_instances (x \<cdot> \<rho>) = ground_instances x"
  by (simp add: ground_instances_def)

lemma ground_instances_set_subst_set_ident_if_renaming[simp]:
  "is_renaming \<rho> \<Longrightarrow> ground_instances_set (subst_set X \<rho>) = ground_instances_set X"
  by (simp add: ground_instances_set_def)

end

end
