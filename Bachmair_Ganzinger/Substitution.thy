(*  Title:       Abstract Substitutions
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Maintainer:  Anders Schlichtkrull
*)

section {* Abstract Substitutions *}

theory Substitution
imports Clauses Map2
begin

text {*
  Conventions:
    's substitution
    'a atoms
*}

locale substitution_ops =
  fixes
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's"
begin

abbreviation subst_atm_syntax (infixl "\<cdot>a" 67) where
  "subst_atm_syntax \<equiv> subst_atm"

abbreviation comp_subst_syntax (infixl "\<odot>" 67) where
  "comp_subst_syntax \<equiv> comp_subst"

definition comp_substs(infixl "\<odot>s" 67) where
  "\<sigma>s \<odot>s \<tau>s = map2 comp_subst \<sigma>s \<tau>s"

definition subst_atms :: "'a set \<Rightarrow> 's \<Rightarrow> 'a set" (infixl "\<cdot>as" 67) where
  "AA \<cdot>as \<sigma> = (\<lambda>A. A \<cdot>a \<sigma>) ` AA"
  
definition subst_atmss :: "'a set set \<Rightarrow> 's \<Rightarrow> 'a set set" (infixl "\<cdot>ass" 67) where
  "AAA \<cdot>ass \<sigma> = (\<lambda>AA. AA \<cdot>as \<sigma>) ` AAA"
  
definition subst_atm_list :: "'a list \<Rightarrow> 's \<Rightarrow> 'a list" (infixl "\<cdot>al" 67) where
  "As \<cdot>al \<sigma> = map (\<lambda>A. A \<cdot>a \<sigma>) As"

definition subst_atm_mset :: "'a multiset \<Rightarrow> 's \<Rightarrow> 'a multiset" (infixl "\<cdot>am" 67) where
  "AA \<cdot>am \<sigma> = image_mset (\<lambda>A. A \<cdot>a \<sigma>) AA"
  
definition subst_atm_mset_list :: "'a multiset list \<Rightarrow> 's \<Rightarrow> 'a multiset list" (infix "\<cdot>aml" 67) where
  "AAA \<cdot>aml \<sigma> = map (\<lambda>AA. AA \<cdot>am \<sigma>) AAA"

definition subst_lit :: "'a literal \<Rightarrow> 's \<Rightarrow> 'a literal" (infixl "\<cdot>l" 67) where
  "L \<cdot>l \<sigma> = map_literal (\<lambda>A. A \<cdot>a \<sigma>) L"

definition subst_cls :: "'a clause \<Rightarrow> 's \<Rightarrow> 'a clause" (infixl "\<cdot>" 67) where
  "AA \<cdot> \<sigma> = image_mset (\<lambda>A. A \<cdot>l \<sigma>) AA"

definition subst_clss :: "'a clause set \<Rightarrow> 's \<Rightarrow> 'a clause set" (infixl "\<cdot>cs" 67) where
  "AA \<cdot>cs \<sigma> = (\<lambda>A. A \<cdot> \<sigma>) ` AA"

definition subst_cls_list :: "'a clause list \<Rightarrow> 's \<Rightarrow> 'a clause list" (infixl "\<cdot>cl" 67) where
  "CC \<cdot>cl \<sigma> = map (\<lambda>A. A \<cdot> \<sigma>) CC"

definition subst_cls_lists :: "'a clause list \<Rightarrow> 's list \<Rightarrow> 'a clause list" (infixl "\<cdot>\<cdot>cl" 67) where
  "CC \<cdot>\<cdot>cl \<sigma>s = map2 subst_cls CC \<sigma>s"

definition subst_cls_mset :: "'a clause multiset \<Rightarrow> 's \<Rightarrow> 'a clause multiset" (infixl "\<cdot>cm" 67) where
  "CC \<cdot>cm \<sigma> = image_mset (\<lambda>A. A \<cdot> \<sigma>) CC"

lemma subst_cls_mset_add_mset[iff]:
  "add_mset C CC \<cdot>cm \<sigma> = add_mset (C \<cdot> \<sigma>) (CC \<cdot>cm \<sigma>)"
  unfolding subst_cls_mset_def by auto

definition is_renaming :: "'s \<Rightarrow> bool" where
  "is_renaming \<sigma> = (\<exists>\<tau>. \<sigma> \<odot> \<tau> = id_subst)"

definition is_ground_atm :: "'a \<Rightarrow> bool" where
  "is_ground_atm A \<longleftrightarrow> (\<forall>\<sigma>. A = A \<cdot>a \<sigma>)"

definition is_ground_atms :: "'a set \<Rightarrow> bool" where
  "is_ground_atms AA = (\<forall>A \<in> AA. is_ground_atm A)"
  
definition is_ground_atm_list :: "'a list \<Rightarrow> bool" where
  "is_ground_atm_list As = (\<forall>A \<in> set As. is_ground_atm A)"

definition is_ground_atm_mset :: "'a multiset \<Rightarrow> bool" where
  "is_ground_atm_mset AA = (\<forall>A. A \<in># AA \<longrightarrow> is_ground_atm A)"

definition is_ground_lit :: "'a literal \<Rightarrow> bool" where
  "is_ground_lit L \<longleftrightarrow> is_ground_atm (atm_of L)"

definition is_ground_cls :: "'a clause \<Rightarrow> bool" where
  "is_ground_cls C \<longleftrightarrow> (\<forall>L. L \<in># C \<longrightarrow> is_ground_lit L)"
  
definition is_ground_clss :: "'a clause set \<Rightarrow> bool" where
  "is_ground_clss CC \<longleftrightarrow> (\<forall>C \<in> CC. is_ground_cls C)"

definition is_ground_cls_list :: "'a clause list \<Rightarrow> bool" where
  "is_ground_cls_list CC \<longleftrightarrow> (\<forall>C \<in> set CC. is_ground_cls C)"

definition is_ground_cls_mset :: "'a clause multiset \<Rightarrow> bool" where
  "is_ground_cls_mset CC \<longleftrightarrow> (\<forall>C. C \<in># CC \<longrightarrow> is_ground_cls C)"
  
definition is_ground_subst :: "'s \<Rightarrow> bool" where
  "is_ground_subst \<sigma> \<longleftrightarrow> (\<forall>A. is_ground_atm (A \<cdot>a \<sigma>))"

definition grounding_of_cls :: "'a clause \<Rightarrow> 'a clause set" where
  "grounding_of_cls C = {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}"

definition grounding_of_clss :: "'a clause set \<Rightarrow> 'a clause set" where
  "grounding_of_clss CC = (\<Union>C \<in> CC. grounding_of_cls C)"

definition is_unifier :: "'s \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_unifier \<sigma> AA \<longleftrightarrow> card (AA \<cdot>as \<sigma>) \<le> 1"

definition is_unifiers :: "'s \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_unifiers \<sigma> AAA \<longleftrightarrow> (\<forall>AA \<in> AAA. is_unifier \<sigma> AA)"

definition is_mgu :: "'s \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_mgu \<sigma> AAA \<longleftrightarrow> is_unifiers \<sigma> AAA \<and> (\<forall>\<tau>. is_unifiers \<tau> AAA \<longrightarrow> (\<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>))"

definition var_disjoint :: "'a clause list \<Rightarrow> bool" where
  "var_disjoint Cs = (\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> (\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>))" 

end

locale substitution = substitution_ops subst_atm id_subst comp_subst
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" +
  assumes
    subst_atm_id_subst[simp]: "subst_atm A id_subst = A" and
    subst_atm_comp_subst[simp]: "subst_atm A (comp_subst \<tau> \<sigma>) = subst_atm (subst_atm A \<tau>) \<sigma>" and
    subst_ext: "(\<And>A. subst_atm A \<sigma> = subst_atm A \<tau>) \<Longrightarrow> \<sigma> = \<tau>" and
    make_ground_subst: "is_ground_cls_list (CC \<cdot>cl \<sigma>) \<Longrightarrow>
       \<exists>\<tau>. is_ground_subst \<tau> \<and> CC \<cdot>cl \<sigma> = CC \<cdot>cl \<tau>" and
    make_var_disjoint: "\<And>Cs. \<exists>\<rho>s. length \<rho>s = length Cs \<and> (\<forall>\<rho> \<in> set \<rho>s. is_renaming \<rho>) \<and>
       var_disjoint (Cs \<cdot>\<cdot>cl \<rho>s)"
begin

lemma var_disjoint_ground:
  assumes "var_disjoint Cs" "length \<sigma>s = length Cs"
  and "is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  shows "\<exists>\<tau>. is_ground_subst \<tau> \<and> Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
proof -
  from assms(1,2) obtain \<tau> where *: "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    unfolding var_disjoint_def by auto
  with assms(3) have "is_ground_cls_list (Cs \<cdot>cl \<tau>)"
    by simp
  then obtain \<tau>' where "is_ground_subst \<tau>'" "Cs \<cdot>cl \<tau> = Cs \<cdot>cl \<tau>'"
    using make_ground_subst by blast
  with assms(2) * have "is_ground_subst \<tau>' \<and> Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>'"
    by simp
  then show ?thesis ..
qed

lemma ex_ground_subst: "\<exists>\<sigma>. is_ground_subst \<sigma>"
  using make_ground_subst[of "[]"] by (auto simp: subst_cls_list_def is_ground_cls_list_def)

lemma id_subst_comp_subst[simp]: "id_subst \<odot> \<sigma> = \<sigma>"
  by (rule subst_ext) simp

lemma comp_subst_id_subst[simp]: "\<sigma> \<odot> id_subst = \<sigma>"
  by (rule subst_ext) simp

lemma comp_subst_assoc[simp]: "\<sigma> \<odot> (\<tau> \<odot> \<gamma>) = \<sigma> \<odot> \<tau> \<odot> \<gamma>"
  by (rule subst_ext) simp

lemma Melem_subst_atm_mset[simp]: "A \<in># AA \<cdot>am \<sigma> \<longleftrightarrow> (\<exists>B. B \<in># AA \<and> A = B \<cdot>a \<sigma>)"
  unfolding subst_atm_mset_def by auto

lemma Melem_subst_cls[simp]: "L \<in># C \<cdot> \<sigma> \<longleftrightarrow> (\<exists>M. M \<in># C \<and> L = M \<cdot>l \<sigma>)"
  unfolding subst_cls_def by auto

lemma Melem_subst_cls_mset[simp]: "AA \<in># CC \<cdot>cm \<sigma> \<longleftrightarrow> (\<exists>BB. BB \<in># CC \<and> AA = BB \<cdot> \<sigma>)"
  unfolding subst_cls_mset_def by auto

lemma subst_lit_is_neg[simp]: "is_neg (L \<cdot>l \<sigma>) = is_neg L"
  unfolding subst_lit_def by auto

lemma subst_lit_is_pos[simp]: "is_pos (L \<cdot>l \<sigma>) = is_pos L"
  unfolding subst_lit_def by auto

lemma subst_cls_negs[simp]: "(negs AA) \<cdot> \<sigma> = negs (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

lemma subst_cls_poss[simp]: "(poss AA) \<cdot> \<sigma> = poss (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

(* Another nice lemma maybe... *)
lemma subst_cls_lists_nth[simp]: "length CC = length \<sigma>s \<Longrightarrow> i < length CC \<Longrightarrow> (CC \<cdot>\<cdot>cl \<sigma>s) ! i = (CC ! i) \<cdot> \<sigma>s ! i"
  unfolding subst_cls_lists_def by auto  
    
(* Another nice lemma *)
lemma subst_cls_len[simp]: "length CC = length \<sigma>s \<Longrightarrow> length (CC \<cdot>\<cdot>cl \<sigma>s) = length CC"
  unfolding subst_cls_lists_def by auto

lemma subst_atms_empty[simp]: "{} \<cdot>as \<sigma> = {}"
  unfolding subst_atms_def by auto

lemma subst_atms_union[simp]: "(A \<union> B) \<cdot>as \<sigma> = A \<cdot>as \<sigma> \<union> B \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atms_single[simp]: "{A} \<cdot>as \<sigma> = {A \<cdot>a \<sigma>}"
  unfolding subst_atms_def by auto

lemma subst_atm_list_length[simp]: "length (As \<cdot>al \<sigma>) = length As"
  unfolding subst_atm_list_def by auto

lemma subst_atm_list_empty[simp]: "[] \<cdot>al \<sigma> = []"
  unfolding subst_atm_list_def by auto

lemma subst_atm_list_Cons[simp]: "(A # As) \<cdot>al \<sigma> = A \<cdot>a \<sigma> # As \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_empty[simp]: "{#} \<cdot>am \<sigma> = {#}"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_union[simp]: "(AA + BB) \<cdot>am \<sigma> = AA \<cdot>am \<sigma> + BB \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_single[simp]: "{#A#} \<cdot>am \<sigma> = {#A \<cdot>a \<sigma>#}"
  unfolding subst_atm_mset_def by auto

lemma subst_cls_empty[simp]: "{#} \<cdot> \<sigma> = {#}"
  unfolding subst_cls_def by auto
                                                                          
lemma subst_cls_union[simp]: "(C + D) \<cdot> \<sigma> = C \<cdot> \<sigma> + D \<cdot> \<sigma>"
  unfolding subst_cls_def by auto

lemma subst_cls_single[simp]: "{#A#} \<cdot> \<sigma> = {#A \<cdot>l \<sigma>#}"
  unfolding subst_cls_def by auto

lemma subst_clss_empty[simp]: "{} \<cdot>cs \<sigma> = {}"
  unfolding subst_clss_def by auto

lemma subst_clss_union[simp]: "(CC \<union> DD) \<cdot>cs \<sigma> = CC \<cdot>cs \<sigma> \<union> DD \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto

lemma subst_clss_single[simp]: "{C} \<cdot>cs \<sigma> = {C \<cdot> \<sigma>}"
  unfolding subst_clss_def by auto

lemma subst_clss_image[simp]: "image f A \<cdot>cs \<sigma> = {f x \<cdot> \<sigma> | x. x \<in> A }"
  unfolding subst_clss_def by auto

lemma subst_cls_list_length[simp]: "length (CC \<cdot>cl \<sigma>) = length CC"
  unfolding subst_cls_list_def by auto

lemma subst_cls_list_Nil[simp]: "[] \<cdot>cl \<sigma> = []"
  unfolding subst_cls_list_def by auto

lemma subst_cls_list_Cons[simp]: "(C # CC) \<cdot>cl \<sigma> = C \<cdot> \<sigma> # CC \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma comp_substs_length[simp]: "length (\<tau>s \<odot>s \<sigma>s) = min (length \<tau>s) (length \<sigma>s)"
  unfolding comp_substs_def by auto

lemma subst_cls_lists_length[simp]: "length (CC \<cdot>\<cdot>cl \<sigma>s) = min (length CC) (length \<sigma>s)"
  unfolding subst_cls_lists_def by auto

lemma subst_cls_lists_Nil[simp]: "[] \<cdot>\<cdot>cl \<sigma>s = []"
  unfolding subst_cls_lists_def by auto

lemma subst_cls_lists_Cons[simp]: "(C # CC) \<cdot>\<cdot>cl (\<sigma> # \<sigma>s) = C \<cdot> \<sigma> # CC \<cdot>\<cdot>cl \<sigma>s"
  unfolding subst_cls_lists_def by auto

lemma subst_scls_mset_empty[simp]: "{#} \<cdot>cm \<sigma> = {#}"
  unfolding subst_cls_mset_def by auto

lemma subst_cls_mset_union[simp]: "(CC + DD) \<cdot>cm \<sigma> = CC \<cdot>cm \<sigma> + DD \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto

lemma subst_cls_mset_single[simp]: "{#C#} \<cdot>cm \<sigma> = {#C \<cdot> \<sigma>#}"
  unfolding subst_cls_mset_def by auto

lemma subst_cls_mset_image_mset[simp]: "image_mset f A \<cdot>cm \<sigma> = {# f x \<cdot> \<sigma>. x \<in># A #}"
  unfolding subst_cls_mset_def by auto

lemma subst_cls_mono: "set_mset C \<subseteq> set_mset D \<Longrightarrow> set_mset (C \<cdot> \<sigma>) \<subseteq> set_mset (D \<cdot> \<sigma>)"
  unfolding subst_cls_def by auto

lemma subst_cls_mono_mset: "C \<le># D \<Longrightarrow> C \<cdot> \<sigma> \<le># D \<cdot> \<sigma>"
  unfolding subst_clss_def by (metis mset_subset_eq_exists_conv subst_cls_union)

lemma subst_atms_id_subst[simp]: "AA \<cdot>as id_subst = AA"
  unfolding subst_atms_def by simp

lemma subst_atm_list_id_subst[simp]: "As \<cdot>al id_subst = As"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_id_subst[simp]: "AA \<cdot>am id_subst = AA"
  unfolding subst_atm_mset_def by simp

lemma subst_lit_id_subst[simp]: "L \<cdot>l id_subst = L"
  unfolding subst_lit_def by (simp add: literal.map_ident)

lemma subst_cls_id_subst[simp]: "C \<cdot> id_subst = C"
  unfolding subst_cls_def by simp

lemma subst_clss_id_subst[simp]: "CC \<cdot>cs id_subst = CC"
  unfolding subst_clss_def by simp

lemma subst_cls_list_id_subst[simp]: "CC \<cdot>cl id_subst = CC"
  unfolding subst_cls_list_def by simp

lemma subst_cls_lists_id_subst[simp]: "length CC = n \<Longrightarrow> CC \<cdot>\<cdot>cl replicate n id_subst = CC"
  unfolding subst_cls_lists_def by (induct CC arbitrary: n) auto

lemma subst_cls_mset_id_subst[simp]: "CC \<cdot>cm id_subst = CC"
  unfolding subst_cls_mset_def by simp

lemma subst_atms_comp_subst[simp]: "AA \<cdot>as (\<tau> \<odot> \<sigma>) = AA \<cdot>as \<tau> \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atm_mset_comp_subst[simp]: "AA \<cdot>am (\<tau> \<odot> \<sigma>) = AA \<cdot>am \<tau> \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_list_comp_subst[simp]: "AA \<cdot>al (\<tau> \<odot> \<sigma>) = AA \<cdot>al \<tau> \<cdot>al \<sigma>"
  unfolding subst_atm_list_def 
  apply (rule nth_equalityI) 
   apply auto
  done

lemma subst_lit_comp_subst[simp]: "L \<cdot>l (\<tau> \<odot> \<sigma>) = L \<cdot>l \<tau> \<cdot>l \<sigma>"
  unfolding subst_lit_def by (auto simp: literal.map_comp o_def)

lemma subst_cls_comp_subst[simp]: "C \<cdot> (\<tau> \<odot> \<sigma>) = C \<cdot> \<tau> \<cdot> \<sigma>"
  unfolding subst_cls_def by auto

lemma map_zip_assoc: "map f (zip (zip xs ys) zs) = map (\<lambda>(x,y,z). f ((x,y),z)) (zip xs (zip ys zs))"
  by (induct zs arbitrary: xs ys) (auto simp add: zip.simps(2) split: list.splits)

lemma subst_cls_lists_comp_substs[simp]: "Cs \<cdot>\<cdot>cl (\<tau>s \<odot>s \<sigma>s) = Cs \<cdot>\<cdot>cl \<tau>s \<cdot>\<cdot>cl \<sigma>s"
  unfolding map2_def subst_cls_lists_def comp_substs_def map_zip_map map_zip_map2 map_zip_assoc   
     by (simp add: split_def)

lemma subst_clsscomp_subst[simp]: "CC \<cdot>cs (\<tau> \<odot> \<sigma>) = CC \<cdot>cs \<tau> \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto

lemma subst_cls_mset_comp_subst[simp]: "CC \<cdot>cm (\<tau> \<odot> \<sigma>) = CC \<cdot>cm \<tau> \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto

lemma is_renaming_id_subst[simp]: "is_renaming id_subst"
  unfolding is_renaming_def by simp

lemma is_ground_cls_as_atms: "is_ground_cls C \<longleftrightarrow> (\<forall>A \<in> atms_of C. is_ground_atm A)"
  by (auto simp: atms_of_def is_ground_cls_def is_ground_lit_def)

lemma is_ground_atms_union[simp]:
  "is_ground_atms (A \<union> B) \<longleftrightarrow> is_ground_atms A \<and> is_ground_atms B"
  unfolding is_ground_atms_def by auto

lemma is_ground_atm_mset_union[simp]:
  "is_ground_atm_mset (A + B) \<longleftrightarrow> is_ground_atm_mset A \<and> is_ground_atm_mset B"
  unfolding is_ground_atm_mset_def by auto

lemma is_ground_cls_union[simp]:
  "is_ground_cls (C + D) \<longleftrightarrow> is_ground_cls C \<and> is_ground_cls D"
  unfolding is_ground_cls_def by auto

lemma is_ground_clss_union[simp]:
  "is_ground_clss (AA \<union> BB) \<longleftrightarrow> is_ground_clss AA \<and> is_ground_clss BB"
  unfolding is_ground_clss_def by auto

lemma is_ground_cls_mset_union[simp]: "is_ground_cls_mset (AA + BB) \<longleftrightarrow>
  is_ground_cls_mset AA \<and> is_ground_cls_mset BB"
  unfolding is_ground_cls_mset_def by auto

lemma is_ground_cls_mono: "C \<le># D \<Longrightarrow> is_ground_cls D \<Longrightarrow> is_ground_cls C"
  unfolding is_ground_cls_def by (metis set_mset_mono subsetD)

lemma is_ground_clss_mono: "CC \<le> DD \<Longrightarrow> is_ground_clss DD \<Longrightarrow> is_ground_clss CC"
  unfolding is_ground_clss_def by blast

lemma is_ground_cls_mset_mono: "CC \<le># DD \<Longrightarrow> is_ground_cls_mset DD \<Longrightarrow> is_ground_cls_mset CC"
  unfolding is_ground_cls_mset_def by (metis mset_subset_eqD)

lemma is_ground_cls_imp_is_ground_lit: "L \<in># C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_lit L"
  unfolding is_ground_cls_def by auto

lemma is_ground_cls_imp_is_ground_atm: "A \<in> atms_of C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_atm A"
  using is_ground_cls_as_atms by auto

lemma is_ground_cls_Union_mset[iff]: "is_ground_cls (\<Union># CC) \<longleftrightarrow> is_ground_cls_mset CC"
  unfolding is_ground_cls_mset_def is_ground_cls_def by blast

lemma is_ground_subst_atm[simp]: "is_ground_atm A \<Longrightarrow> A \<cdot>a \<sigma> = A"
  unfolding is_ground_atm_def by simp

lemma is_ground_subst_atms[simp]: "is_ground_atms AA \<Longrightarrow> AA \<cdot>as \<sigma> = AA"
  unfolding is_ground_atms_def subst_atms_def image_def by auto

lemma is_ground_subst_atm_mset[simp]: "is_ground_atm_mset AA \<Longrightarrow> AA \<cdot>am \<sigma> = AA"
  unfolding is_ground_atm_mset_def subst_atm_mset_def by auto

lemma is_ground_subst_atm_list[simp]: "is_ground_atm_list As \<Longrightarrow> As \<cdot>al \<sigma> = As"
  apply (rule nth_equalityI)
  unfolding is_ground_atm_list_def subst_atm_list_def by auto

lemma is_ground_subst_lit[simp]: "is_ground_lit L \<Longrightarrow> L \<cdot>l \<sigma> = L"
  unfolding is_ground_lit_def subst_lit_def by (cases L) simp_all
  
lemma is_ground_subst_cls[simp]: "is_ground_cls C \<Longrightarrow> C \<cdot> \<sigma> = C"
  unfolding is_ground_cls_def subst_cls_def by simp

lemma is_ground_subst_clss[simp]: "is_ground_clss CC \<Longrightarrow> CC \<cdot>cs \<sigma> = CC"
  unfolding is_ground_clss_def subst_clss_def image_def by auto
  
lemma is_ground_subst_cls_mset[simp]: "is_ground_cls_mset CC \<Longrightarrow> CC \<cdot>cm \<sigma> = CC"
  unfolding is_ground_cls_mset_def subst_cls_mset_def by auto

lemma is_ground_comp_subst[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_subst (\<tau> \<odot> \<sigma>)"
  unfolding is_ground_subst_def is_ground_atm_def by auto

lemma ground_subst_ground_atm[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_atm (A \<cdot>a \<sigma>)"
  unfolding is_ground_subst_def by auto

lemma ground_subst_ground_lit[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_lit (L \<cdot>l \<sigma>)"
  unfolding is_ground_lit_def subst_lit_def by (cases L) auto

lemma ground_subst_ground_cls[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls (C \<cdot> \<sigma>)"
  unfolding is_ground_cls_def by auto

lemma ground_subst_ground_clss[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_clss (CC \<cdot>cs \<sigma>)"
  unfolding is_ground_clss_def subst_clss_def by auto

lemma ground_subst_ground_cls_list[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_list (CC \<cdot>cl \<sigma>)"
  unfolding is_ground_cls_list_def subst_cls_list_def by auto

lemma ground_subst_ground_cls_lists[simp]:
  "\<forall>\<sigma> \<in> set \<sigma>s. is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_list (CC \<cdot>\<cdot>cl \<sigma>s)"
  unfolding  is_ground_cls_list_def subst_cls_lists_def map2_def by (auto simp: set_zip)

lemma ground_subst_ground_cls_mset[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_mset (CC \<cdot>cm \<sigma>)"
  unfolding is_ground_cls_mset_def subst_cls_mset_def by auto

lemma is_ground_cls_list_Cons[simp]:
  "is_ground_cls_list (C # CC) = (is_ground_cls C \<and> is_ground_cls_list CC)"
  unfolding is_ground_cls_list_def by auto

lemma card_le_one_alt: "finite X \<Longrightarrow> card X \<le> 1 \<longleftrightarrow> X = {} \<or> (\<exists>x. X = {x})"
  by (induct rule: finite_induct) auto

lemma is_unifier_subst_atm_eqI:
  assumes "finite AA"
  shows "is_unifier \<sigma> AA \<Longrightarrow> A \<in> AA \<Longrightarrow> B \<in> AA \<Longrightarrow> A \<cdot>a \<sigma> = B \<cdot>a \<sigma>"
  unfolding is_unifier_def subst_atms_def card_le_one_alt[OF finite_imageI[OF assms]]
  by (metis equals0D imageI insert_iff)

lemma is_unifier_alt:
  assumes "finite AA"
  shows "is_unifier \<sigma> AA \<longleftrightarrow> (\<forall>A \<in> AA. \<forall>B \<in> AA. A \<cdot>a \<sigma> = B \<cdot>a \<sigma>)"
  unfolding is_unifier_def subst_atms_def card_le_one_alt[OF finite_imageI[OF assms(1)]]
  by (cases "AA = {}") (auto, metis equals0D imageI insert_iff)

lemma is_unifiers_subst_atm_eqI:
  assumes "finite AA" "is_unifiers \<sigma> AAA" "AA \<in> AAA" "A \<in> AA" "B \<in> AA"
  shows "A \<cdot>a \<sigma> = B \<cdot>a \<sigma>"
  by (metis assms is_unifiers_def is_unifier_subst_atm_eqI)

lemma subst_ext_iff: "\<sigma> = \<tau> \<longleftrightarrow> (\<forall>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>)"
  by (auto intro: subst_ext)

(* Put these in the appropriate place above: *)
  
(* similar to, but stronger than is_ground_subst_lit *)
lemma is_ground_subst_lit_iff: "is_ground_lit L \<longleftrightarrow> (\<forall>\<sigma>. L = L \<cdot>l \<sigma>)"
  using is_ground_atm_def is_ground_lit_def subst_lit_def by (cases L) auto

(* similar to but stronger than is_ground_subst_cls *)
thm is_ground_subst_cls
lemma is_ground_subst_cls_iff: "is_ground_cls C \<longleftrightarrow> (\<forall>\<sigma>. C = C \<cdot> \<sigma>)"
  apply rule
  using is_ground_subst_lit_iff apply (auto simp add: is_ground_cls_def subst_cls_def)[]
  apply (metis ex_ground_subst ground_subst_ground_cls)
  done
lemma is_ground_subst_cls_list[simp]:
  assumes "length P = length CAi"
  assumes "is_ground_cls_list CAi"
  shows "CAi \<cdot>\<cdot>cl P = CAi"
proof -
  {
    fix i
    assume "i < length P"
    then have "(CAi \<cdot>\<cdot>cl P) ! i = CAi !i "
      using assms unfolding is_ground_cls_list_def by auto
  }
  then show ?thesis using nth_equalityI[of _ CAi] assms by auto
qed
   
    
(* similar to but stronger than is_ground_subst_cls_list *)
  
lemma "is_ground_cls_list CAi \<longleftrightarrow> (\<forall>P. length P = length CAi \<longrightarrow> CAi \<cdot>\<cdot>cl P = CAi)"
  oops (* This should be proved *)

lemma[simp]: "i < length Ai \<Longrightarrow> ((Ai \<cdot>al \<tau>) ! i) = (Ai ! i) \<cdot>a \<tau>"
  unfolding subst_atm_list_def using less_Suc_eq_0_disj nth_map by (induction Ai) auto
    
lemma[simp]: "i < length Ci \<Longrightarrow> ((Ci \<cdot>cl \<tau>) ! i) = (Ci ! i) \<cdot> \<tau>"
  unfolding subst_cls_list_def using less_Suc_eq_0_disj nth_map by (induction Ci) auto
    
lemma[simp]: "mset (Ai \<cdot>al \<sigma>) = mset (Ai) \<cdot>am \<sigma>"
  unfolding subst_atm_list_def subst_atm_mset_def by auto
    
lemma[simp]: "sum_list (Ci' \<cdot>cl \<eta>) = sum_list Ci' \<cdot> \<eta>" 
    unfolding subst_cls_list_def by (induction Ci') auto
end

locale unification = substitution subst_atm id_subst comp_subst
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and 
    id_subst :: 's and 
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" +
  fixes
    mgu :: "'a set set \<Rightarrow> 's option"
  assumes
    mgu_sound: "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA) \<Longrightarrow> mgu AAA = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> AAA" and
    mgu_complete: "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA) \<Longrightarrow> is_unifiers \<sigma> AAA \<Longrightarrow> \<exists>\<tau>. mgu AAA = Some \<tau>"
begin

lemmas is_unifiers_mgu = mgu_sound[unfolded is_mgu_def, THEN conjunct1]
lemmas is_mgu_most_general = mgu_sound[unfolded is_mgu_def, THEN conjunct2]

lemma mgu_empty: "mgu {} = Some \<rho> \<Longrightarrow> is_renaming \<rho>"
  using mgu_sound[of "{}", unfolded is_mgu_def is_unifiers_def, simplified]
  by (metis is_renaming_def)

lemma mgu_singleton: "mgu {{x}} = Some \<rho> \<Longrightarrow> is_renaming \<rho>"
  using is_unifier_def[simp]
    mgu_sound[of "{{x}}", unfolded is_mgu_def is_unifiers_def, simplified]
  by (metis is_renaming_def)

lemma mgu_eq_id_subst:
  "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA \<and> card AA \<le> 1) \<Longrightarrow> \<exists>\<rho>. mgu AAA = Some \<rho> \<and> is_renaming \<rho>"
proof (induct AAA rule: finite_induct)
  case empty
  have "is_unifiers id_subst {}"
    unfolding is_unifiers_def by simp
  then show ?case
    using mgu_complete mgu_empty by blast
next
  case (insert AA AAA)
  then obtain \<rho> where "mgu AAA = Some \<rho>" "is_renaming \<rho>"
    by auto
  then have "is_mgu \<rho> AAA"
    using mgu_sound insert(1,4) by blast
  moreover have "is_unifier \<rho> AA"
    using bspec[OF insert(4), of AA] card_le_one_alt[of AA] by (auto simp: is_unifier_def)
  ultimately have "is_mgu \<rho> (insert AA AAA)"
    unfolding is_mgu_def is_unifiers_def by simp
  then obtain \<rho>' where "mgu (insert AA AAA) = Some \<rho>'"
    using mgu_complete insert(1,4) is_mgu_def by force
  moreover then have "is_mgu \<rho>' (insert AA AAA)"
    using mgu_sound insert(1,4) by force
  with \<open>is_mgu \<rho> (insert AA AAA)\<close> \<open>is_renaming \<rho>\<close>  have "is_renaming \<rho>'"
    unfolding is_mgu_def is_renaming_def by (metis comp_subst_assoc)
  ultimately show ?case
    by blast
qed                                                                  

  
end
  
end
