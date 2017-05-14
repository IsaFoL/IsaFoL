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

subsection {* Substitution operators *}
  
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
  "is_renaming \<sigma> = (\<exists>\<tau>. \<sigma> \<odot> \<tau> = id_subst \<and> \<tau> \<odot> \<sigma> = id_subst)"
  
definition is_renaming_list :: "'s list \<Rightarrow> bool" where
  "is_renaming_list \<sigma>s = (\<forall>\<sigma> \<in> set \<sigma>s. is_renaming \<sigma>)"
  
definition inv_ren :: "'s \<Rightarrow> 's" where
  "inv_ren \<sigma> = (SOME \<tau>. \<sigma> \<odot> \<tau> = id_subst)"

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
  "var_disjoint Cs = (\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> 
      (\<exists>\<tau>. 
        (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>)
      ))"  
  
end

subsection {* Substitution theorems *}
  
locale substitution = substitution_ops subst_atm id_subst comp_subst
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" +
  assumes
    subst_atm_id_subst[simp]: "subst_atm A id_subst = A" and
    subst_atm_comp_subst[simp]: "subst_atm A (comp_subst \<tau> \<sigma>) = subst_atm (subst_atm A \<tau>) \<sigma>" and
    subst_ext: "(\<And>A. subst_atm A \<sigma> = subst_atm A \<tau>) \<Longrightarrow> \<sigma> = \<tau>" and
    make_ground_subst: "\<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>i < length CC. \<forall>S. S \<subseteq># CC ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)" and
    make_var_disjoint: "\<And>Cs. \<exists>\<rho>s. length \<rho>s = length Cs \<and> (\<forall>\<rho> \<in> set \<rho>s. is_renaming \<rho>) \<and>
       var_disjoint (Cs \<cdot>\<cdot>cl \<rho>s)"
begin
  
lemma subst_ext_iff: "\<sigma> = \<tau> \<longleftrightarrow> (\<forall>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>)"
  by (auto intro: subst_ext)

subsubsection {* Identity substitution *}

thm subst_atm_id_subst

lemma id_subst_comp_subst[simp]: "id_subst \<odot> \<sigma> = \<sigma>"
  by (rule subst_ext) simp

lemma comp_subst_id_subst[simp]: "\<sigma> \<odot> id_subst = \<sigma>"
  by (rule subst_ext) simp
    
lemma id_subst_comp_substs[simp]: "replicate (length \<sigma>s) id_subst \<odot>s \<sigma>s = \<sigma>s"
  using comp_substs_def by (induction \<sigma>s) auto
    
lemma comp_substs_id_subst[simp]: "\<sigma>s \<odot>s replicate (length \<sigma>s) id_subst = \<sigma>s"
  using comp_substs_def by (induction \<sigma>s) auto
    
lemma subst_atms_id_subst[simp]: "AA \<cdot>as id_subst = AA"
  unfolding subst_atms_def by simp
    
lemma subst_atmss_id_subst[simp]: "AA \<cdot>ass id_subst = AA"
  unfolding subst_atmss_def by simp

lemma subst_atm_list_id_subst[simp]: "As \<cdot>al id_subst = As"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_id_subst[simp]: "AA \<cdot>am id_subst = AA"
  unfolding subst_atm_mset_def by simp
    
lemma subst_atm_mset_list_id_subst[simp]: "AA \<cdot>aml id_subst = AA"
  unfolding subst_atm_mset_list_def by simp

lemma subst_lit_id_subst[simp]: "L \<cdot>l id_subst = L"
  unfolding subst_lit_def by (simp add: literal.map_ident)

lemma subst_cls_id_subst[simp]: "C \<cdot> id_subst = C"
  unfolding subst_cls_def by simp

lemma subst_clss_id_subst[simp]: "CC \<cdot>cs id_subst = CC"
  unfolding subst_clss_def by simp

lemma subst_cls_list_id_subst[simp]: "CC \<cdot>cl id_subst = CC"
  unfolding subst_cls_list_def by simp

lemma subst_cls_lists_id_subst[simp]: "CC \<cdot>\<cdot>cl replicate (length CC) id_subst = CC"
  unfolding subst_cls_lists_def by (induct CC) auto

lemma subst_cls_mset_id_subst[simp]: "CC \<cdot>cm id_subst = CC"
  unfolding subst_cls_mset_def by simp
    
subsubsection {* Composition is associative *}

lemma comp_subst_assoc[simp]: "\<sigma> \<odot> (\<tau> \<odot> \<gamma>) = \<sigma> \<odot> \<tau> \<odot> \<gamma>"
  by (rule subst_ext) simp
    
subsubsection {* Substitution and composition are compatible *}
  
thm subst_atm_comp_subst
  
lemma subst_atms_comp_subst[simp]: "AA \<cdot>as (\<tau> \<odot> \<sigma>) = AA \<cdot>as \<tau> \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto
    
lemma subst_atmss_comp_subst[simp]: "AA \<cdot>ass (\<tau> \<odot> \<sigma>) = AA \<cdot>ass \<tau> \<cdot>ass \<sigma>"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_comp_subst[simp]: "AA \<cdot>al (\<tau> \<odot> \<sigma>) = AA \<cdot>al \<tau> \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto
    
lemma subst_atm_mset_comp_subst[simp]: "AA \<cdot>am (\<tau> \<odot> \<sigma>) = AA \<cdot>am \<tau> \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto
    
lemma subst_atm_mset_list_comp_subst[simp]: "AA \<cdot>aml (\<tau> \<odot> \<sigma>) = (AA \<cdot>aml \<tau>) \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_lit_comp_subst[simp]: "L \<cdot>l (\<tau> \<odot> \<sigma>) = L \<cdot>l \<tau> \<cdot>l \<sigma>"
  unfolding subst_lit_def by (auto simp: literal.map_comp o_def)

lemma subst_cls_comp_subst[simp]: "C \<cdot> (\<tau> \<odot> \<sigma>) = C \<cdot> \<tau> \<cdot> \<sigma>"
  unfolding subst_cls_def by auto
    
lemma subst_clsscomp_subst[simp]: "CC \<cdot>cs (\<tau> \<odot> \<sigma>) = CC \<cdot>cs \<tau> \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto
    
lemma subst_cls_list_comp_subst[simp]: "CC \<cdot>cl (\<tau> \<odot> \<sigma>) = CC \<cdot>cl \<tau> \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma map_zip_assoc: "map f (zip (zip xs ys) zs) = map (\<lambda>(x,y,z). f ((x,y),z)) (zip xs (zip ys zs))"
  by (induct zs arbitrary: xs ys) (auto simp add: zip.simps(2) split: list.splits)

lemma subst_cls_lists_comp_substs[simp]: "Cs \<cdot>\<cdot>cl (\<tau>s \<odot>s \<sigma>s) = Cs \<cdot>\<cdot>cl \<tau>s \<cdot>\<cdot>cl \<sigma>s"
  unfolding map2_def subst_cls_lists_def comp_substs_def map_zip_map map_zip_map2 map_zip_assoc   
     by (simp add: split_def)

lemma subst_cls_mset_comp_subst[simp]: "CC \<cdot>cm (\<tau> \<odot> \<sigma>) = CC \<cdot>cm \<tau> \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto

    
subsubsection {* \<^text>\<open>Melem_subst_set\<close> *}

lemma Melem_subst_atm_mset[simp]: "A \<in># AA \<cdot>am \<sigma> \<longleftrightarrow> (\<exists>B. B \<in># AA \<and> A = B \<cdot>a \<sigma>)"
  unfolding subst_atm_mset_def by auto

lemma Melem_subst_cls[simp]: "L \<in># C \<cdot> \<sigma> \<longleftrightarrow> (\<exists>M. M \<in># C \<and> L = M \<cdot>l \<sigma>)"
  unfolding subst_cls_def by auto

lemma Melem_subst_cls_mset[simp]: "AA \<in># CC \<cdot>cm \<sigma> \<longleftrightarrow> (\<exists>BB. BB \<in># CC \<and> AA = BB \<cdot> \<sigma>)"
  unfolding subst_cls_mset_def by auto

    
subsubsection {* Sign of substitution *}
  
lemma subst_lit_is_neg[simp]: "is_neg (L \<cdot>l \<sigma>) = is_neg L"
  unfolding subst_lit_def by auto

lemma subst_lit_is_pos[simp]: "is_pos (L \<cdot>l \<sigma>) = is_pos L"
  unfolding subst_lit_def by auto
    
    
subsubsection {* Substitute on literal or literals *}
  
lemma eql_neg_lit_eql_atm[simp]: "(Neg A' \<cdot>l \<eta>) = Neg A \<longleftrightarrow> A' \<cdot>a \<eta> = A"
  by (simp add: subst_lit_def)

lemma eql_pos_lit_eql_atm[simp]: "(Pos A' \<cdot>l \<eta>) = Pos A \<longleftrightarrow> A' \<cdot>a \<eta> = A"
  by (simp add: subst_lit_def)
    
lemma subst_cls_negs[simp]: "(negs AA) \<cdot> \<sigma> = negs (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

lemma subst_cls_poss[simp]: "(poss AA) \<cdot> \<sigma> = poss (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

subsubsection {* Substitute on empty *}
    
lemma subst_atms_empty[simp]: "{} \<cdot>as \<sigma> = {}"
  unfolding subst_atms_def by auto
    
lemma subst_atmss_empty[simp]: "{} \<cdot>ass \<sigma> = {}"
  unfolding subst_atmss_def by auto
    
lemma comp_substs_empty_iff[simp]: "\<sigma>s \<odot>s \<eta>s = [] \<longleftrightarrow> (\<sigma>s = [] \<or> \<eta>s = [])"
  unfolding comp_substs_def by auto
    
lemma subst_atm_list_empty[simp]: "[] \<cdot>al \<sigma> = []"
  unfolding subst_atm_list_def by auto
    
lemma subst_atm_mset_empty[simp]: "{#} \<cdot>am \<sigma> = {#}"
  unfolding subst_atm_mset_def by auto
    
lemma subst_atm_mset_list_empty[simp]: "[] \<cdot>aml \<sigma> = []"
  unfolding subst_atm_mset_list_def by auto
    
lemma subst_cls_empty[simp]: "{#} \<cdot> \<sigma> = {#}"
  unfolding subst_cls_def by auto
    
lemma subst_clss_empty[simp]: "{} \<cdot>cs \<sigma> = {}"
  unfolding subst_clss_def by auto
    
lemma subst_cls_list_empty[simp]: "[] \<cdot>cl \<sigma> = []"
  unfolding subst_cls_list_def by auto
    
lemma subst_cls_lists_empty[simp]: "[] \<cdot>\<cdot>cl \<sigma>s = []"
  unfolding subst_cls_lists_def by auto
    
lemma subst_scls_mset_empty[simp]: "{#} \<cdot>cm \<sigma> = {#}"
  unfolding subst_cls_mset_def by auto

lemma subst_atms_empty_iff[simp]: "AA \<cdot>as \<eta> = {} \<longleftrightarrow> AA = {}"
  unfolding subst_atms_def by auto
    
lemma subst_atmss_empty_iff[simp]: "AAA \<cdot>ass \<eta> = {} \<longleftrightarrow> AAA = {}"
  unfolding subst_atmss_def by auto
    
lemma subst_atm_list_empty_iff[simp]: "AA \<cdot>al \<eta> = [] \<longleftrightarrow> AA = []"
  unfolding subst_atm_list_def by auto
    
lemma subst_atm_mset_empty_iff[simp]: "A \<cdot>am \<eta> = {#} \<longleftrightarrow> A = {#}"  
  unfolding subst_atm_mset_def by auto
    
lemma subst_atm_mset_list_empty_iff[simp]: "C \<cdot>aml \<eta> = [] \<longleftrightarrow> C = []"
  unfolding subst_atm_mset_list_def by auto
    
lemma subst_cls_empty_iff[simp]: "C \<cdot> \<eta> = {#} \<longleftrightarrow> C = {#}"
  unfolding subst_cls_def by auto
    
lemma subst_clss_empty_iff[simp]: "CC \<cdot>cs \<eta> = {} \<longleftrightarrow> CC = {}"
  unfolding subst_clss_def by auto
    
lemma subst_cls_list_empty_iff[simp]: "CC \<cdot>cl \<eta> = [] \<longleftrightarrow> CC = []"
  unfolding subst_cls_list_def by auto
    
lemma subst_cls_lists_empty_iff[simp]: "C \<cdot>\<cdot>cl \<eta>s = [] \<longleftrightarrow> (C = [] \<or> \<eta>s = [])"
  unfolding subst_cls_lists_def by auto
    
lemma subst_cls_mset_empty_iff[simp]: "C \<cdot>cm \<eta> = {#} \<longleftrightarrow> C = {#}"
  unfolding subst_cls_mset_def by auto 
    
    
subsubsection {* Substitute on a union *}
  
lemma subst_atms_union[simp]: "(A \<union> B) \<cdot>as \<sigma> = A \<cdot>as \<sigma> \<union> B \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atmss_union[simp]: "(A \<union> B) \<cdot>ass \<sigma> = A \<cdot>ass \<sigma> \<union> B \<cdot>ass \<sigma>"
  unfolding subst_atmss_def by auto
    
lemma subst_atm_list_append[simp]: "(A @ B) \<cdot>al \<sigma> = A \<cdot>al \<sigma> @ B \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_union[simp]: "(AA + BB) \<cdot>am \<sigma> = AA \<cdot>am \<sigma> + BB \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto  
    
lemma subst_atm_mset_list_append[simp]: "(A @ B) \<cdot>aml \<sigma> = A \<cdot>aml \<sigma> @ B \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto
  
lemma subst_cls_union[simp]: "(C + D) \<cdot> \<sigma> = C \<cdot> \<sigma> + D \<cdot> \<sigma>"
  unfolding subst_cls_def by auto
    
lemma subst_clss_union[simp]: "(CC \<union> DD) \<cdot>cs \<sigma> = CC \<cdot>cs \<sigma> \<union> DD \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto
    
lemma subst_cls_list_append[simp]: "(CC @ DD) \<cdot>cl \<sigma> = CC \<cdot>cl \<sigma> @ DD \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto
    
lemma subst_cls_mset_union[simp]: "(CC + DD) \<cdot>cm \<sigma> = CC \<cdot>cm \<sigma> + DD \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto
    

subsubsection {* Substitute on a singleton *}

lemma subst_atms_single[simp]: "{A} \<cdot>as \<sigma> = {A \<cdot>a \<sigma>}"
  unfolding subst_atms_def by auto
    
lemma subst_atmss_single[simp]: "{AA} \<cdot>ass \<sigma> = {AA \<cdot>as \<sigma>}"
  unfolding subst_atmss_def by auto
    
lemma subst_atm_list_single[simp]: "[A] \<cdot>al \<sigma> = [A \<cdot>a \<sigma>]"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_single[simp]: "{#A#} \<cdot>am \<sigma> = {#A \<cdot>a \<sigma>#}"
  unfolding subst_atm_mset_def by auto
    
lemma subst_atm_mset_list[simp]: "[AA] \<cdot>aml \<sigma> = [AA \<cdot>am \<sigma>]"
  unfolding subst_atm_mset_list_def by auto
    
lemma subst_cls_single[simp]: "{#A#} \<cdot> \<sigma> = {#A \<cdot>l \<sigma>#}"
  unfolding subst_cls_def by auto

lemma subst_clss_single[simp]: "{C} \<cdot>cs \<sigma> = {C \<cdot> \<sigma>}"
  unfolding subst_clss_def by auto
    
lemma subst_cls_list_single[simp]: "[C] \<cdot>cl \<sigma> = [C \<cdot> \<sigma>]"
  unfolding subst_cls_list_def by auto
    
lemma subst_cls_mset_single[simp]: "{#C#} \<cdot>cm \<sigma> = {#C \<cdot> \<sigma>#}"
  unfolding subst_cls_mset_def by auto
    

subsubsection {* Substitute on Cons *}

lemma subst_atm_list_Cons[simp]: "(A # As) \<cdot>al \<sigma> = A \<cdot>a \<sigma> # As \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto
    
lemma subst_atm_mset_list_Cons[simp]: "(A # As) \<cdot>aml \<sigma> = A \<cdot>am \<sigma> # As \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_list_Cons[simp]: "(C # CC) \<cdot>cl \<sigma> = C \<cdot> \<sigma> # CC \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_Cons[simp]: "(C # CC) \<cdot>\<cdot>cl (\<sigma> # \<sigma>s) = C \<cdot> \<sigma> # CC \<cdot>\<cdot>cl \<sigma>s"
  unfolding subst_cls_lists_def by auto
    
    
subsubsection {* Substitute on nth *}
  
lemma comp_substs_nth[simp]: "length \<tau>s = length \<sigma>s \<Longrightarrow> i < length \<tau>s \<Longrightarrow> (\<tau>s \<odot>s \<sigma>s) ! i = (\<tau>s ! i) \<odot> (\<sigma>s ! i)"
  unfolding comp_substs_def 
  by auto
  
lemma subst_atm_list_nth[simp]: "i < length Ai \<Longrightarrow> ((Ai \<cdot>al \<tau>) ! i) = (Ai ! i) \<cdot>a \<tau>"
  unfolding subst_atm_list_def using less_Suc_eq_0_disj nth_map by (induction Ai) auto
    
lemma subst_atm_mset_list_nth[simp]: "i < length Aij' \<Longrightarrow> (Aij' \<cdot>aml \<eta>) ! i = (Aij' ! i) \<cdot>am \<eta>"
  unfolding subst_atm_mset_list_def
    by auto
    
lemma subst_cls_list_nth[simp]: "i < length Ci \<Longrightarrow> ((Ci \<cdot>cl \<tau>) ! i) = (Ci ! i) \<cdot> \<tau>"
  unfolding subst_cls_list_def using less_Suc_eq_0_disj nth_map by (induction Ci) auto
  
lemma subst_cls_lists_nth[simp]: "length CC = length \<sigma>s \<Longrightarrow> i < length CC \<Longrightarrow> (CC \<cdot>\<cdot>cl \<sigma>s) ! i = (CC ! i) \<cdot> \<sigma>s ! i"
  unfolding subst_cls_lists_def by auto  

    
subsubsection {* Substitute on an image *}

lemma subst_clss_image[simp]: "image f A \<cdot>cs \<sigma> = {f x \<cdot> \<sigma> | x. x \<in> A }"
  unfolding subst_clss_def by auto
    
lemma subst_cls_mset_image_mset[simp]: "image_mset f A \<cdot>cm \<sigma> = {# f x \<cdot> \<sigma>. x \<in># A #}"
  unfolding subst_cls_mset_def by auto
    
subsubsection {* Substitute on the mset function*}
  
    
lemma[simp]: "mset (Ai \<cdot>al \<sigma>) = mset (Ai) \<cdot>am \<sigma>"
  unfolding subst_atm_list_def subst_atm_mset_def by auto
    
subsubsection {* Substitute on @{term sum_list} *}
    
lemma[simp]: "sum_list (Ci' \<cdot>cl \<eta>) = sum_list Ci' \<cdot> \<eta>" 
  unfolding subst_cls_list_def by (induction Ci') auto
    
subsubsection {* Renamings *}
  
lemma is_renaming_id_subst[simp]: "is_renaming id_subst"
  unfolding is_renaming_def by simp
   
lemma is_renaming_inj:
   "is_renaming \<sigma> \<Longrightarrow> (\<forall>x y. x \<cdot>a \<sigma> = y \<cdot>a \<sigma> \<longrightarrow> x = y)" (* I don't think the other direction is true *)
  by (metis is_renaming_def subst_atm_comp_subst subst_atm_id_subst)
    
lemma "is_renaming \<sigma> \<Longrightarrow> range (\<lambda>x. x \<cdot>a \<sigma>) = UNIV"
  by (metis subst_atm_comp_subst subst_atm_id_subst substitution_ops.is_renaming_def surj_def)
    
lemma "is_renaming r1 \<Longrightarrow> is_renaming r2 \<Longrightarrow> \<tau> \<odot> r1 = r2 \<Longrightarrow> is_renaming \<tau>"
  by (metis comp_subst_assoc comp_subst_id_subst is_renaming_def)
    
lemma "is_renaming r1 \<Longrightarrow> is_renaming r2 \<Longrightarrow> r1 \<odot> \<tau> = r2 \<Longrightarrow> is_renaming \<tau>"
  by (metis comp_subst_assoc id_subst_comp_subst is_renaming_def)
  

(* The substitutions, and renamings in particular,  form a semigroup: *)
thm comp_subst_assoc
  
(* The renamings form a group I think, but I have not been able to prove it. *) 
thm id_subst_comp_subst
  
lemma inv_ren_cancel_r[simp]: "is_renaming s \<Longrightarrow> s \<odot> (inv_ren s) = id_subst"
  unfolding inv_ren_def is_renaming_def by (metis (mono_tags, lifting) someI_ex)
    
lemma inv_ren_cancel_r_list[simp]: "is_renaming_list s \<Longrightarrow> s \<odot>s (map inv_ren s) = replicate (length s) id_subst" 
  unfolding is_renaming_list_def
  by (induction s) (auto simp add: comp_substs_def)
    
lemma inv_ren_cancel_l[simp]: "is_renaming s \<Longrightarrow> (inv_ren s) \<odot> s = id_subst"
  by (metis comp_subst_assoc id_subst_comp_subst inv_ren_cancel_r is_renaming_def substitution.comp_subst_id_subst substitution_axioms)
    
lemma inv_ren_cancel_l_list[simp]: "is_renaming_list s \<Longrightarrow> (map inv_ren s) \<odot>s s = replicate (length s) id_subst"
  unfolding is_renaming_list_def by (induction s) (auto simp add: comp_substs_def)
    
    
lemma[simp]: "[] \<odot>s s = []"
  unfolding comp_substs_def by auto
    
lemma[simp]: "s \<odot>s [] = []"
  unfolding comp_substs_def by auto
  
    
lemma xxid: "is_renaming x \<Longrightarrow> x \<odot> x = x \<Longrightarrow> x = id_subst"
  by (metis comp_subst_assoc comp_subst_id_subst inv_ren_cancel_r) 

lemma xyidyxid: "is_renaming x \<Longrightarrow> is_renaming y \<Longrightarrow> x \<odot> y = id_subst \<Longrightarrow> y \<odot> x = id_subst"
  by (metis comp_subst_assoc comp_subst_id_subst is_renaming_def)  
    
(* Closure *)
lemma "is_renaming a \<Longrightarrow> is_renaming b \<Longrightarrow> is_renaming (a \<odot> b)"
  unfolding is_renaming_def by (metis comp_subst_assoc comp_subst_id_subst)
    
(* Associativity *)    
  (* Holds in general for substitutions and thus in particular for renamings. *)
thm comp_subst_assoc

(* Identity element *)
thm is_renaming_id_subst
  
  (* We can remove id_subst on lhs for substitutions and thus in particular for renamings *)
thm id_subst_comp_subst
  
  (* We can remove id_subst on rhs for substitutions and thus in particular for renamings *)
thm comp_subst_id_subst

(* inverse element *)      
  
  (* s and (inv_ren s) cancel out *)

 
lemma inv_ren_is_renaming[simp]:
  assumes "is_renaming s"
  shows "is_renaming (inv_ren s)"
  using assms
  using inv_ren_cancel_l inv_ren_cancel_r is_renaming_def by blast
     
   
thm Groups.Let_0
      
thm inv_ren_cancel_l
  

  
lemma[simp]: "is_renaming \<rho> \<Longrightarrow> C  \<cdot> \<rho> \<cdot> (inv_ren \<rho>) = C"
  by (metis inv_ren_cancel_r subst_cls_comp_subst subst_cls_id_subst)
    
lemma drdrdrdrdrdrdrdrdrdrdrdr[simp]: "length CC = length \<rho>s \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> CC \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl (map inv_ren \<rho>s) = CC"
  apply (induction \<rho>s)
    unfolding is_renaming_list_def
     apply auto
    by (metis Suc_length_conv inv_ren_cancel_r_list is_renaming_list_def list.simps(9) set_ConsD subst_cls_lists_comp_substs subst_cls_lists_id_subst)

lemma drdrdrdr[simp]: "is_renaming \<rho> \<Longrightarrow> C  \<cdot> (inv_ren \<rho>) \<cdot> \<rho> = C"
  by (metis inv_ren_cancel_l subst_cls_comp_subst subst_cls_id_subst)
  
    
lemma drdrdrdrdrdrdrdr[simp]: "length CC = length \<rho>s \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> CC \<cdot>\<cdot>cl (map inv_ren \<rho>s) \<cdot>\<cdot>cl \<rho>s = CC"
  apply (induction \<rho>s)
    unfolding is_renaming_list_def
     apply auto
    by (metis inv_ren_cancel_l_list is_renaming_list_def length_Cons list.simps(9) set_ConsD subst_cls_lists_comp_substs subst_cls_lists_id_subst)
      
    
subsubsection {* Monotonicity *}

lemma subst_cls_mono: "set_mset C \<subseteq> set_mset D \<Longrightarrow> set_mset (C \<cdot> \<sigma>) \<subseteq> set_mset (D \<cdot> \<sigma>)"
  unfolding subst_cls_def by auto

lemma subst_cls_mono_mset: "C \<le># D \<Longrightarrow> C \<cdot> \<sigma> \<le># D \<cdot> \<sigma>"
  unfolding subst_clss_def by (metis mset_subset_eq_exists_conv subst_cls_union)


subsubsection {* Length after substitution *}    

lemma subst_atm_list_length[simp]: "length (As \<cdot>al \<sigma>) = length As"
  unfolding subst_atm_list_def by auto
         
lemma subst_cls_list_length[simp]: "length (CC \<cdot>cl \<sigma>) = length CC"
  unfolding subst_cls_list_def by auto

lemma comp_substs_length[simp]: "length (\<tau>s \<odot>s \<sigma>s) = min (length \<tau>s) (length \<sigma>s)"
  unfolding comp_substs_def by auto

lemma subst_cls_lists_length[simp]: "length (CC \<cdot>\<cdot>cl \<sigma>s) = min (length CC) (length \<sigma>s)"
  unfolding subst_cls_lists_def by auto
    
subsubsection {* Variable disjointness *}
  
lemma var_disjoint_clauses:
  assumes "var_disjoint Cs"
  shows "\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> (\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>)"
proof (rule, rule)
  fix \<sigma>s :: "'s list"
  assume a: "length \<sigma>s = length Cs"  
  then obtain \<tau> where "\<forall>i<length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>" 
    using assms unfolding var_disjoint_def by blast
  then have "\<forall>i<length Cs. (Cs ! i) \<cdot> \<sigma>s ! i = (Cs ! i) \<cdot> \<tau>" 
    by auto
  then have "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    using a by (simp add: nth_equalityI) 
  then show "\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>" by auto
qed
  
    
subsubsection {* Ground expressions and substitutions *}
    
lemma is_ground_cls_list_Cons[simp]:
  "is_ground_cls_list (C # CC) = (is_ground_cls C \<and> is_ground_cls_list CC)"
  unfolding is_ground_cls_list_def by auto
    
lemma make_ground_subst_clauses:
  assumes "is_ground_cls_list (CC \<cdot>cl \<sigma>)"
  shows "\<exists>\<tau>. is_ground_subst \<tau> \<and> CC \<cdot>cl \<sigma> = CC \<cdot>cl \<tau>"
proof -
  from assms obtain \<tau> where "is_ground_subst \<tau> \<and> (\<forall>i<length CC. \<forall>S. S \<subseteq># CC ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)" 
    using make_ground_subst by blast
  then have "is_ground_subst \<tau> \<and> (\<forall>i<length CC. (CC ! i) \<cdot> \<sigma> = (CC ! i) \<cdot> \<tau>)"
    by auto
  then have "is_ground_subst \<tau> \<and> CC \<cdot>cl \<sigma> = CC \<cdot>cl \<tau>"
    by (simp add: list_eq_iff_nth_eq) 
  then show ?thesis 
    by blast
qed  

lemma var_disjoint_ground:
  assumes "var_disjoint Cs" "length \<sigma>s = length Cs"
  and "is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  shows "\<exists>\<tau>. is_ground_subst \<tau> \<and> Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
proof -
  from assms(1,2) obtain \<tau> where *: "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    using var_disjoint_clauses by auto
  with assms(3) have "is_ground_cls_list (Cs \<cdot>cl \<tau>)"
    by simp
  then obtain \<tau>' where "is_ground_subst \<tau>'" "Cs \<cdot>cl \<tau> = Cs \<cdot>cl \<tau>'"
    using make_ground_subst_clauses by blast
  with assms(2) * have "is_ground_subst \<tau>' \<and> Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>'"
    by simp
  then show ?thesis ..
qed

lemma ex_ground_subst: "\<exists>\<sigma>. is_ground_subst \<sigma>"
  using make_ground_subst[of "[]"] by (auto simp: subst_cls_list_def is_ground_cls_list_def)
  
paragraph {* Ground union *}
  
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

lemma is_ground_cls_Union_mset[iff]: "is_ground_cls (\<Union># CC) \<longleftrightarrow> is_ground_cls_mset CC"
  unfolding is_ground_cls_mset_def is_ground_cls_def by blast
    
    
paragraph {* Ground mono *}
  
lemma is_ground_cls_mono: "C \<le># D \<Longrightarrow> is_ground_cls D \<Longrightarrow> is_ground_cls C"
  unfolding is_ground_cls_def by (metis set_mset_mono subsetD)

lemma is_ground_clss_mono: "CC \<le> DD \<Longrightarrow> is_ground_clss DD \<Longrightarrow> is_ground_clss CC"
  unfolding is_ground_clss_def by blast

lemma is_ground_cls_mset_mono: "CC \<le># DD \<Longrightarrow> is_ground_cls_mset DD \<Longrightarrow> is_ground_cls_mset CC"
  unfolding is_ground_cls_mset_def by (metis mset_subset_eqD)
    
    
paragraph {* Members of ground expressions are ground *}
  
lemma is_ground_cls_as_atms: "is_ground_cls C \<longleftrightarrow> (\<forall>A \<in> atms_of C. is_ground_atm A)"
  by (auto simp: atms_of_def is_ground_cls_def is_ground_lit_def)

lemma is_ground_cls_imp_is_ground_lit: "L \<in># C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_lit L"
  unfolding is_ground_cls_def by auto

lemma is_ground_cls_imp_is_ground_atm: "A \<in> atms_of C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_atm A"
  using is_ground_cls_as_atms by auto
    
    
paragraph {* Substituting on ground expression preserves ground *}


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
    

paragraph {* Substituting on ground expression has no effect *}  
  
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
    
lemma is_ground_subst_cls_list[simp]:
  assumes "length P = length CAi"
  assumes "is_ground_cls_list CAi"
  shows "CAi \<cdot>\<cdot>cl P = CAi"
proof -
  {
    fix i
    assume "i < length P"
    then have "(CAi \<cdot>\<cdot>cl P) ! i = CAi !i "
      using assms unfolding is_ground_cls_list_def
      using subst_cls_lists_def by auto 
  }
  then show ?thesis using nth_equalityI[of _ CAi] assms by auto
qed
    
lemma is_ground_subst_lit_iff: "is_ground_lit L \<longleftrightarrow> (\<forall>\<sigma>. L = L \<cdot>l \<sigma>)"
  using is_ground_atm_def is_ground_lit_def subst_lit_def by (cases L) auto
    
lemma is_ground_subst_cls_iff: "is_ground_cls C \<longleftrightarrow> (\<forall>\<sigma>. C = C \<cdot> \<sigma>)"
  apply rule
  using is_ground_subst_lit_iff apply (auto simp add: is_ground_cls_def subst_cls_def)[]
  apply (metis ex_ground_subst ground_subst_ground_cls)
  done    

paragraph {* \<^text>\<open>make_single_ground_subst\<close> *}
lemma make_single_ground_subst: 
  (* Makes me wonder if I can also prove \<^text>\<open>make_ground_subst\<close>... But do I really want to?  *)
  assumes "is_ground_cls C"
  assumes "C' \<cdot> \<sigma> = C"
  obtains \<tau> where
    "is_ground_subst \<tau>"
    "C' \<cdot> \<tau> = C"
using assms
  by (metis ex_ground_subst is_ground_comp_subst is_ground_subst_cls subst_cls_comp_subst) (* I'm very impressed sledgehammer managed to do this... *)

    
subsubsection {* Unifiers *}

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
    
theorem is_unifiers_comp: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset Ai' Aij') \<cdot>ass \<eta>) \<longleftrightarrow> is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset Ai' Aij'))"
  unfolding is_unifiers_def is_unifier_def subst_atmss_def
  by auto    
    
end

subsection {* Unification *}
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
  using mgu_sound is_mgu_def is_unifiers_def 
  oops (* Proof broke when I changed is_renaming_def *)

lemma mgu_singleton: "mgu {{x}} = Some \<rho> \<Longrightarrow> is_renaming \<rho>"
  using is_unifier_def
    mgu_sound  is_mgu_def is_unifiers_def
  oops (* Proof broke when I changed is_renaming_def *)
lemma mgu_eq_id_subst:
  "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA \<and> card AA \<le> 1) \<Longrightarrow> \<exists>\<rho>. mgu AAA = Some \<rho> \<and> is_renaming \<rho>"
proof (induct AAA rule: finite_induct)
  case empty
  have "is_unifiers id_subst {}"
    unfolding is_unifiers_def by simp
  then show ?case
    using mgu_complete 
      sorry
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
    unfolding is_mgu_def is_renaming_def 
      sorry
  ultimately show ?case
    by blast
  oops (* Proof broke when I changed \<^text>\<open>is_renaming_def\<close> *)

end
  
end
