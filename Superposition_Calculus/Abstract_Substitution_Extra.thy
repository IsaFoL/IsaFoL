theory Abstract_Substitution_Extra
  imports
    Main
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
  "is_ground_subst \<sigma> \<longleftrightarrow> (\<forall>x. is_ground (x \<cdot> \<sigma>))"

definition generalizes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "generalizes x y \<longleftrightarrow> (\<exists>\<sigma>. x \<cdot> \<sigma> = y)"

definition strictly_generalizes :: "'x \<Rightarrow> 'x \<Rightarrow> bool" where
  "strictly_generalizes x y \<longleftrightarrow> generalizes x y \<and> \<not> generalizes y x"

definition is_unifier :: "'s \<Rightarrow> 'x set \<Rightarrow> bool" where
  "is_unifier \<sigma> X \<longleftrightarrow> card (X \<cdot>s \<sigma>) \<le> 1"

definition is_unifiers :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_unifiers \<sigma> XX \<longleftrightarrow> (\<forall>X \<in> XX. is_unifier \<sigma> X)"

definition is_mgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_mgu \<sigma> XX \<longleftrightarrow> is_unifiers \<sigma> XX \<and> (\<forall>\<tau>. is_unifiers \<tau> XX \<longrightarrow> (\<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>))"

definition is_imgu :: "'s \<Rightarrow> 'x set set \<Rightarrow> bool" where
  "is_imgu \<sigma> XX \<longleftrightarrow> is_unifiers \<sigma> XX \<and> (\<forall>\<tau>. is_unifiers \<tau> XX \<longrightarrow> \<tau> = \<sigma> \<odot> \<tau>)"

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

end

locale basic_substitution = basic_substitution_ops subst id_subst comp_subst for
    subst :: "'x \<Rightarrow> 's \<Rightarrow> 'x" (infixl "\<cdot>" 67) and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) +
  assumes
    subst_id_subst[simp]: "x \<cdot> id_subst = x" and
    subst_comp_subst[simp]: "x \<cdot> (\<sigma> \<odot> \<tau>) = (x \<cdot> \<sigma>) \<cdot> \<tau>" and
    subst_ext: "(\<And>x. x \<cdot> \<sigma> = x \<cdot> \<tau>) \<Longrightarrow> \<sigma> = \<tau>" and
    make_ground_subst: "is_ground_set (X \<cdot>s \<sigma>) \<Longrightarrow> \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>x \<in> X. x \<cdot> \<tau> = x \<cdot> \<sigma>)"
begin

subsection \<open>Identity Substitution\<close>

lemma id_subst_comp_subst[simp]: "id_subst \<odot> \<sigma> = \<sigma>"
  by (rule subst_ext) simp

lemma comp_subst_id_subst[simp]: "\<sigma> \<odot> id_subst = \<sigma>"
  by (rule subst_ext) simp


subsection \<open>Associativity of Composition\<close>

lemma comp_subst_assoc[simp]: "\<sigma> \<odot> (\<tau> \<odot> \<gamma>) = \<sigma> \<odot> \<tau> \<odot> \<gamma>"
  by (rule subst_ext) simp


subsection \<open>Substituting on Ground Expression\<close>

lemma is_ground_subst_ident[simp]: "is_ground x \<Longrightarrow> x \<cdot> \<sigma> = x"
  unfolding is_ground_def by simp

subsection \<open>Unifier of Ground Expressions\<close>

lemma
  assumes "is_unifier \<mu> {t\<^sub>1, t\<^sub>2}" and "is_ground t\<^sub>1" and "is_ground t\<^sub>2"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms by (simp add: card_Suc_eq is_unifier_def le_Suc_eq subst_set_def)

lemma is_unifier_subset: "is_unifier \<mu> A \<Longrightarrow> finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_unifier \<mu> B"
  by (smt (verit, best) card_mono dual_order.trans finite_imageI image_mono is_unifier_def
      subst_set_def)

lemma is_ground_set_subset: "is_ground_set A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_ground_set B"
  by (auto simp: is_ground_set_def)

lemma ball_eq_constant_if_unifier:
  assumes fin: "finite X" and unif: "is_unifier \<upsilon> (insert x X)" and "is_ground_set (insert x X)"
  shows "\<forall>y \<in> X. y = x"
  using assms
proof (induction X rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert z F)

  have "\<forall>y\<in>F. y = x"
  proof (rule insert.IH)
    show "is_unifier \<upsilon> (insert x F)"
      using insert.hyps insert.prems(1)
      by (auto elim: is_unifier_subset)
  next
    show "is_ground_set (insert x F)"
      using insert.prems(2)
      by (simp_all add: is_ground_set_def)
  qed

  moreover have "z = x"
  proof -
    have "x \<cdot> \<upsilon> = z \<cdot> \<upsilon>"
      using insert.hyps insert.prems(1)
      using is_unifier_iff_if_finite
      by (meson finite.insertI insertCI)
    then show ?thesis
      by (metis is_ground_set_def insert.prems(2) insertCI is_ground_subst_ident)
  qed

  ultimately show ?case
    by simp
qed

end
  
end