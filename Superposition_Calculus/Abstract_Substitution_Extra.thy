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

end
  
end