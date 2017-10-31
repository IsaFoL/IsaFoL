(*  Title:       Abstract Substitutions
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Abstract Substitutions\<close>

theory Abstract_Substitution
  imports "../lib/Clausal_Logic" Map2
begin

text \<open>
  Conventions:
    's substitution
    'a atoms
\<close>


subsection \<open>Substitution operators\<close>

locale substitution_ops =
  fixes
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's"
begin

abbreviation subst_atm_abbrev :: "'a \<Rightarrow> 's \<Rightarrow> 'a" (infixl "\<cdot>a" 67) where
  "op \<cdot>a \<equiv> subst_atm"

abbreviation comp_subst_abbrev :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) where
  "op \<odot> \<equiv> comp_subst"

definition comp_substs :: "'s list \<Rightarrow> 's list \<Rightarrow> 's list" (infixl "\<odot>s" 67) where
  "\<sigma>s \<odot>s \<tau>s = map2 comp_subst \<sigma>s \<tau>s"

definition subst_atms :: "'a set \<Rightarrow> 's \<Rightarrow> 'a set" (infixl "\<cdot>as" 67) where
  "AA \<cdot>as \<sigma> = (\<lambda>A. A \<cdot>a \<sigma>) ` AA"

definition subst_atmss :: "'a set set \<Rightarrow> 's \<Rightarrow> 'a set set" (infixl "\<cdot>ass" 67) where
  "AAA \<cdot>ass \<sigma> = (\<lambda>AA. AA \<cdot>as \<sigma>) ` AAA"

definition subst_atm_list :: "'a list \<Rightarrow> 's \<Rightarrow> 'a list" (infixl "\<cdot>al" 67) where
  "As \<cdot>al \<sigma> = map (\<lambda>A. A \<cdot>a \<sigma>) As"

definition subst_atm_mset :: "'a multiset \<Rightarrow> 's \<Rightarrow> 'a multiset" (infixl "\<cdot>am" 67) where
  "AA \<cdot>am \<sigma> = image_mset (\<lambda>A. A \<cdot>a \<sigma>) AA"

definition
  subst_atm_mset_list :: "'a multiset list \<Rightarrow> 's \<Rightarrow> 'a multiset list" (infix "\<cdot>aml" 67)
where
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

lemma subst_cls_add_mset[simp]: "add_mset L C \<cdot> \<sigma> = add_mset (L \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding subst_cls_def by auto

lemma subst_cls_mset_add_mset[simp]: "add_mset C CC \<cdot>cm \<sigma> = add_mset (C \<cdot> \<sigma>) (CC \<cdot>cm \<sigma>)"
  unfolding subst_cls_mset_def by auto

definition generalizes_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "generalizes_atm A B \<longleftrightarrow> (\<exists>\<sigma>. A \<cdot>a \<sigma> = B)"

definition strictly_generalizes_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "strictly_generalizes_atm A B \<longleftrightarrow> generalizes_atm A B \<and> \<not> generalizes_atm B A"

definition generalizes_lit :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "generalizes_lit L M \<longleftrightarrow> (\<exists>\<sigma>. L \<cdot>l \<sigma> = M)"

definition strictly_generalizes_lit :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "strictly_generalizes_lit L M \<longleftrightarrow> generalizes_lit L M \<and> \<not> generalizes_lit M L"

definition generalizes_cls :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "generalizes_cls C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> = D)"

definition strictly_generalizes_cls :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "strictly_generalizes_cls C D \<longleftrightarrow> generalizes_cls C D \<and> \<not> generalizes_cls D C"

definition is_renaming :: "'s \<Rightarrow> bool" where
  "is_renaming \<sigma> \<longleftrightarrow> (\<exists>\<tau>. \<sigma> \<odot> \<tau> = id_subst \<and> \<tau> \<odot> \<sigma> = id_subst)"

definition is_renaming_list :: "'s list \<Rightarrow> bool" where
  "is_renaming_list \<sigma>s \<longleftrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. is_renaming \<sigma>)"

definition inv_ren :: "'s \<Rightarrow> 's" where
  "inv_ren \<sigma> = (SOME \<tau>. \<sigma> \<odot> \<tau> = id_subst)"

definition is_ground_atm :: "'a \<Rightarrow> bool" where
  "is_ground_atm A \<longleftrightarrow> (\<forall>\<sigma>. A = A \<cdot>a \<sigma>)"

definition is_ground_atms :: "'a set \<Rightarrow> bool" where
  "is_ground_atms AA = (\<forall>A \<in> AA. is_ground_atm A)"

definition is_ground_atm_list :: "'a list \<Rightarrow> bool" where
  "is_ground_atm_list As \<longleftrightarrow> (\<forall>A \<in> set As. is_ground_atm A)"

definition is_ground_atm_mset :: "'a multiset \<Rightarrow> bool" where
  "is_ground_atm_mset AA \<longleftrightarrow> (\<forall>A. A \<in># AA \<longrightarrow> is_ground_atm A)"

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

definition is_ground_subst_list :: "'s list \<Rightarrow> bool" where
  "is_ground_subst_list \<sigma>s \<longleftrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. is_ground_subst \<sigma>)"

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
  "var_disjoint Cs \<longleftrightarrow>
   (\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> (\<exists>\<tau>. \<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>))"


subsubsection \<open>Generalization of\<close>

lemma generalizes_cls_size: "generalizes_cls C D \<Longrightarrow> size C = size D"
  unfolding generalizes_cls_def subst_cls_def by fastforce

end


subsection \<open>Substitution lemmas\<close>

locale substitution = substitution_ops subst_atm id_subst comp_subst
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" +
  fixes
    renamings_apart :: "'a clause list \<Rightarrow> 's list"
  assumes
    subst_atm_id_subst[simp]: "A \<cdot>a id_subst = A" and
    subst_atm_comp_subst[simp]: "A \<cdot>a (\<tau> \<odot> \<sigma>) = (A \<cdot>a \<tau>) \<cdot>a \<sigma>" and
    subst_ext: "(\<And>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>) \<Longrightarrow> \<sigma> = \<tau>" and
    make_ground_subst:
      "is_ground_cls_list (Cs \<cdot>cl \<sigma>) \<Longrightarrow>
       \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)" and
    renames_apart:
      "\<And>Cs. length (renamings_apart Cs) = length Cs \<and>
         (\<forall>\<rho> \<in> set (renamings_apart Cs). is_renaming \<rho>) \<and>
         var_disjoint (Cs \<cdot>\<cdot>cl (renamings_apart Cs))" and
    wf_strictly_generalizes_cls: "wfP strictly_generalizes_cls"
begin

lemma subst_ext_iff: "\<sigma> = \<tau> \<longleftrightarrow> (\<forall>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>)"
  by (blast intro: subst_ext)


subsubsection \<open>Identity substitution\<close>

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

lemma subst_atmss_id_subst[simp]: "AAA \<cdot>ass id_subst = AAA"
  unfolding subst_atmss_def by simp

lemma subst_atm_list_id_subst[simp]: "As \<cdot>al id_subst = As"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_id_subst[simp]: "AA \<cdot>am id_subst = AA"
  unfolding subst_atm_mset_def by simp

lemma subst_atm_mset_list_id_subst[simp]: "AAs \<cdot>aml id_subst = AAs"
  unfolding subst_atm_mset_list_def by simp

lemma subst_lit_id_subst[simp]: "L \<cdot>l id_subst = L"
  unfolding subst_lit_def by (simp add: literal.map_ident)

lemma subst_cls_id_subst[simp]: "C \<cdot> id_subst = C"
  unfolding subst_cls_def by simp

lemma subst_clss_id_subst[simp]: "CC \<cdot>cs id_subst = CC"
  unfolding subst_clss_def by simp

lemma subst_cls_list_id_subst[simp]: "Cs \<cdot>cl id_subst = Cs"
  unfolding subst_cls_list_def by simp

lemma subst_cls_lists_id_subst[simp]: "Cs \<cdot>\<cdot>cl replicate (length Cs) id_subst = Cs"
  unfolding subst_cls_lists_def by (induct Cs) auto

lemma subst_cls_mset_id_subst[simp]: "CC \<cdot>cm id_subst = CC"
  unfolding subst_cls_mset_def by simp


subsubsection \<open>Composition is associative\<close>

lemma comp_subst_assoc[simp]: "\<sigma> \<odot> (\<tau> \<odot> \<gamma>) = \<sigma> \<odot> \<tau> \<odot> \<gamma>"
  by (rule subst_ext) simp


subsubsection \<open>Substitution and composition are compatible\<close>

lemma subst_atms_comp_subst[simp]: "AA \<cdot>as (\<tau> \<odot> \<sigma>) = AA \<cdot>as \<tau> \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atmss_comp_subst[simp]: "AAA \<cdot>ass (\<tau> \<odot> \<sigma>) = AAA \<cdot>ass \<tau> \<cdot>ass \<sigma>"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_comp_subst[simp]: "As \<cdot>al (\<tau> \<odot> \<sigma>) = As \<cdot>al \<tau> \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_comp_subst[simp]: "AA \<cdot>am (\<tau> \<odot> \<sigma>) = AA \<cdot>am \<tau> \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_comp_subst[simp]: "AAs \<cdot>aml (\<tau> \<odot> \<sigma>) = (AAs \<cdot>aml \<tau>) \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_lit_comp_subst[simp]: "L \<cdot>l (\<tau> \<odot> \<sigma>) = L \<cdot>l \<tau> \<cdot>l \<sigma>"
  unfolding subst_lit_def by (auto simp: literal.map_comp o_def)

lemma subst_cls_comp_subst[simp]: "C \<cdot> (\<tau> \<odot> \<sigma>) = C \<cdot> \<tau> \<cdot> \<sigma>"
  unfolding subst_cls_def by auto

lemma subst_clsscomp_subst[simp]: "CC \<cdot>cs (\<tau> \<odot> \<sigma>) = CC \<cdot>cs \<tau> \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto

lemma subst_cls_list_comp_subst[simp]: "Cs \<cdot>cl (\<tau> \<odot> \<sigma>) = Cs \<cdot>cl \<tau> \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_comp_substs[simp]: "Cs \<cdot>\<cdot>cl (\<tau>s \<odot>s \<sigma>s) = Cs \<cdot>\<cdot>cl \<tau>s \<cdot>\<cdot>cl \<sigma>s"
  unfolding subst_cls_lists_def comp_substs_def map_zip_map map_zip_map2 map_zip_assoc
  by (simp add: split_def)

lemma subst_cls_mset_comp_subst[simp]: "CC \<cdot>cm (\<tau> \<odot> \<sigma>) = CC \<cdot>cm \<tau> \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>``Commutativity'' of membership and substitution\<close>

lemma Melem_subst_atm_mset[simp]: "A \<in># AA \<cdot>am \<sigma> \<longleftrightarrow> (\<exists>B. B \<in># AA \<and> A = B \<cdot>a \<sigma>)"
  unfolding subst_atm_mset_def by auto

lemma Melem_subst_cls[simp]: "L \<in># C \<cdot> \<sigma> \<longleftrightarrow> (\<exists>M. M \<in># C \<and> L = M \<cdot>l \<sigma>)"
  unfolding subst_cls_def by auto

lemma Melem_subst_cls_mset[simp]: "AA \<in># CC \<cdot>cm \<sigma> \<longleftrightarrow> (\<exists>BB. BB \<in># CC \<and> AA = BB \<cdot> \<sigma>)"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Signs and substitutions\<close>

lemma subst_lit_is_neg[simp]: "is_neg (L \<cdot>l \<sigma>) = is_neg L"
  unfolding subst_lit_def by auto

lemma subst_lit_is_pos[simp]: "is_pos (L \<cdot>l \<sigma>) = is_pos L"
  unfolding subst_lit_def by auto

lemma subst_minus[simp]: "(- L) \<cdot>l \<mu> = - (L  \<cdot>l \<mu>)"
  by (simp add: literal.map_sel subst_lit_def uminus_literal_def)


subsubsection \<open>Substitute on literal or literals\<close>

lemma eql_neg_lit_eql_atm[simp]: "(Neg A' \<cdot>l \<eta>) = Neg A \<longleftrightarrow> A' \<cdot>a \<eta> = A"
  by (simp add: subst_lit_def)

lemma eql_pos_lit_eql_atm[simp]: "(Pos A' \<cdot>l \<eta>) = Pos A \<longleftrightarrow> A' \<cdot>a \<eta> = A"
  by (simp add: subst_lit_def)

lemma subst_cls_negs[simp]: "(negs AA) \<cdot> \<sigma> = negs (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

lemma subst_cls_poss[simp]: "(poss AA) \<cdot> \<sigma> = poss (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

lemma atms_of_subst_atms: "atms_of C \<cdot>as \<sigma> = atms_of (C \<cdot> \<sigma>)"
proof -
  have "atms_of (C \<cdot> \<sigma>) = set_mset (image_mset atm_of (image_mset (map_literal (\<lambda>A. A \<cdot>a \<sigma>)) C))"
    unfolding subst_cls_def subst_atms_def subst_lit_def atms_of_def by auto
  also have "... = set_mset (image_mset (\<lambda>A. A \<cdot>a \<sigma>) (image_mset atm_of C))"
    by simp (meson literal.map_sel)
  finally show "atms_of C \<cdot>as \<sigma> = atms_of (C \<cdot> \<sigma>)"
    unfolding subst_atms_def atms_of_def by auto
qed

lemma in_image_Neg_is_neg[simp]: "L \<cdot>l \<sigma> \<in> Neg ` AA \<Longrightarrow> is_neg L"
  by (metis bex_imageD literal.disc(2) literal.map_disc_iff subst_lit_def)

lemma subst_lit_in_negs_subst_is_neg: "L \<cdot>l \<sigma> \<in># (negs AA) \<cdot> \<tau> \<Longrightarrow> is_neg L"
  by simp

lemma subst_lit_in_negs_is_neg: "L \<cdot>l \<sigma> \<in># negs AA \<Longrightarrow> is_neg L"
  by simp


subsubsection \<open>Substitute on empty\<close>

lemma subst_atms_empty[simp]: "{} \<cdot>as \<sigma> = {}"
  unfolding subst_atms_def by auto

lemma subst_atmss_empty[simp]: "{} \<cdot>ass \<sigma> = {}"
  unfolding subst_atmss_def by auto

lemma comp_substs_empty_iff[simp]: "\<sigma>s \<odot>s \<eta>s = [] \<longleftrightarrow> \<sigma>s = [] \<or> \<eta>s = []"
  using comp_substs_def map2_empty_iff by auto

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

lemma subst_atm_list_empty_iff[simp]: "As \<cdot>al \<eta> = [] \<longleftrightarrow> As = []"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_empty_iff[simp]: "AA \<cdot>am \<eta> = {#} \<longleftrightarrow> AA = {#}"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_empty_iff[simp]: "AAs \<cdot>aml \<eta> = [] \<longleftrightarrow> AAs = []"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_empty_iff[simp]: "C \<cdot> \<eta> = {#} \<longleftrightarrow> C = {#}"
  unfolding subst_cls_def by auto

lemma subst_clss_empty_iff[simp]: "CC \<cdot>cs \<eta> = {} \<longleftrightarrow> CC = {}"
  unfolding subst_clss_def by auto

lemma subst_cls_list_empty_iff[simp]: "Cs \<cdot>cl \<eta> = [] \<longleftrightarrow> Cs = []"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_empty_iff[simp]: "Cs \<cdot>\<cdot>cl \<eta>s = [] \<longleftrightarrow> (Cs = [] \<or> \<eta>s = [])"
  using map2_empty_iff subst_cls_lists_def by auto

lemma subst_cls_mset_empty_iff[simp]: "CC \<cdot>cm \<eta> = {#} \<longleftrightarrow> CC = {#}"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Substitute on a union\<close>

lemma subst_atms_union[simp]: "(AA \<union> BB) \<cdot>as \<sigma> = AA \<cdot>as \<sigma> \<union> BB \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atmss_union[simp]: "(AAA \<union> BBB) \<cdot>ass \<sigma> = AAA \<cdot>ass \<sigma> \<union> BBB \<cdot>ass \<sigma>"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_append[simp]: "(As @ Bs) \<cdot>al \<sigma> = As \<cdot>al \<sigma> @ Bs \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_union[simp]: "(AA + BB) \<cdot>am \<sigma> = AA \<cdot>am \<sigma> + BB \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_append[simp]: "(AAs @ BBs) \<cdot>aml \<sigma> = AAs \<cdot>aml \<sigma> @ BBs \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_union[simp]: "(C + D) \<cdot> \<sigma> = C \<cdot> \<sigma> + D \<cdot> \<sigma>"
  unfolding subst_cls_def by auto

lemma subst_clss_union[simp]: "(CC \<union> DD) \<cdot>cs \<sigma> = CC \<cdot>cs \<sigma> \<union> DD \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto

lemma subst_cls_list_append[simp]: "(Cs @ Ds) \<cdot>cl \<sigma> = Cs \<cdot>cl \<sigma> @ Ds \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_mset_union[simp]: "(CC + DD) \<cdot>cm \<sigma> = CC \<cdot>cm \<sigma> + DD \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Substitute on a singleton\<close>

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

lemma subst_cls_single[simp]: "{#L#} \<cdot> \<sigma> = {#L \<cdot>l \<sigma>#}"
  by simp

lemma subst_clss_single[simp]: "{C} \<cdot>cs \<sigma> = {C \<cdot> \<sigma>}"
  unfolding subst_clss_def by auto

lemma subst_cls_list_single[simp]: "[C] \<cdot>cl \<sigma> = [C \<cdot> \<sigma>]"
  unfolding subst_cls_list_def by auto

lemma subst_cls_mset_single[simp]: "{#C#} \<cdot>cm \<sigma> = {#C \<cdot> \<sigma>#}"
  by simp


subsubsection \<open>Substitute on Cons\<close>

lemma subst_atm_list_Cons[simp]: "(A # As) \<cdot>al \<sigma> = A \<cdot>a \<sigma> # As \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_list_Cons[simp]: "(A # As) \<cdot>aml \<sigma> = A \<cdot>am \<sigma> # As \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_list_Cons[simp]: "(C # Cs) \<cdot>cl \<sigma> = C \<cdot> \<sigma> # Cs \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_Cons[simp]: "(C # Cs) \<cdot>\<cdot>cl (\<sigma> # \<sigma>s) = C \<cdot> \<sigma> # Cs \<cdot>\<cdot>cl \<sigma>s"
  unfolding subst_cls_lists_def by auto


subsubsection \<open>Substitution on tl\<close>

lemma subst_atm_list_tl[simp]: "(tl (As \<cdot>al \<eta>)) = (tl As \<cdot>al \<eta>)"
  by (induction As) auto

lemma subst_atm_mset_list_tl[simp]:"(tl (AAs \<cdot>aml \<eta>)) = (tl AAs \<cdot>aml \<eta>)"
  by (induction AAs) auto


subsubsection \<open>Substitute on nth\<close>

lemma comp_substs_nth[simp]:
  "length \<tau>s = length \<sigma>s \<Longrightarrow> i < length \<tau>s \<Longrightarrow> (\<tau>s \<odot>s \<sigma>s) ! i = (\<tau>s ! i) \<odot> (\<sigma>s ! i)"
  by (simp add: comp_substs_def)

lemma subst_atm_list_nth[simp]: "i < length As \<Longrightarrow> (As \<cdot>al \<tau>) ! i = As ! i \<cdot>a \<tau>"
  unfolding subst_atm_list_def using less_Suc_eq_0_disj nth_map by force

lemma subst_atm_mset_list_nth[simp]: "i < length AAs \<Longrightarrow> (AAs \<cdot>aml \<eta>) ! i = (AAs ! i) \<cdot>am \<eta>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_list_nth[simp]: "i < length Cs \<Longrightarrow> ((Cs \<cdot>cl \<tau>) ! i) = (Cs ! i) \<cdot> \<tau>"
  unfolding subst_cls_list_def using less_Suc_eq_0_disj nth_map by (induction Cs) auto

lemma subst_cls_lists_nth[simp]:
  "length Cs = length \<sigma>s \<Longrightarrow> i < length Cs \<Longrightarrow> (Cs \<cdot>\<cdot>cl \<sigma>s) ! i = (Cs ! i) \<cdot> (\<sigma>s ! i)"
  unfolding subst_cls_lists_def by auto


subsubsection \<open>Substitute on an image\<close>

lemma subst_clss_image[simp]: "image f X \<cdot>cs \<sigma> = {f x \<cdot> \<sigma> | x. x \<in> X}"
  unfolding subst_clss_def by auto

lemma subst_cls_mset_image_mset[simp]: "image_mset f X \<cdot>cm \<sigma> = {# f x \<cdot> \<sigma>. x \<in># X #}"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Substitute on the mset function\<close>

lemma mset_subst_atm_list_subst_atm_mset[simp]: "mset (As \<cdot>al \<sigma>) = mset (As) \<cdot>am \<sigma>"
  unfolding subst_atm_list_def subst_atm_mset_def by auto

lemma mset_subst_cls_list_subst_cls_mset: "mset (Cs \<cdot>cl \<sigma>) = (mset Cs) \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def subst_cls_list_def by auto


subsubsection \<open>Substitute on @{term sum_list}\<close>

lemma sum_list_subst_cls_list_subst_cls[simp]: "sum_list (Cs \<cdot>cl \<eta>) = sum_list Cs \<cdot> \<eta>"
  unfolding subst_cls_list_def by (induction Cs) auto


subsubsection \<open>Substitute on @{term set_mset}\<close>

lemma set_mset_subst_cls_mset_subst_clss: "set_mset (CC \<cdot>cm \<mu>) = (set_mset CC) \<cdot>cs \<mu>"
  by (simp add: subst_cls_mset_def subst_clss_def)


subsubsection \<open>Substitute on an mset and its member\<close>

lemma Neg_Melem_subst_atm_subst_cls[simp]: "Neg A \<in># C \<Longrightarrow> Neg (A \<cdot>a \<sigma>) \<in># C \<cdot> \<sigma> "
  by (metis Melem_subst_cls eql_neg_lit_eql_atm)

lemma Pos_Melem_subst_atm_subst_cls[simp]: "Pos A \<in># C \<Longrightarrow> Pos (A \<cdot>a \<sigma>) \<in># C \<cdot> \<sigma> "
  by (metis Melem_subst_cls eql_pos_lit_eql_atm)


subsubsection \<open>Substitute on a set and its member\<close>

lemma in_atms_of_subst[simp]: "B \<in> atms_of C \<Longrightarrow> B \<cdot>a \<sigma> \<in> atms_of (C \<cdot> \<sigma>)"
  by (metis atms_of_subst_atms image_iff subst_atms_def)


subsubsection \<open>Renamings\<close>

lemma is_renaming_id_subst[simp]: "is_renaming id_subst"
  unfolding is_renaming_def by simp

lemma is_renamingD: "is_renaming \<sigma> \<Longrightarrow> (\<forall>A1 A2. A1 \<cdot>a \<sigma> = A2 \<cdot>a \<sigma> \<longleftrightarrow> A1 = A2)"
  by (metis is_renaming_def subst_atm_comp_subst subst_atm_id_subst)

lemma "is_renaming \<sigma> \<Longrightarrow> range (\<lambda>A. A \<cdot>a \<sigma>) = UNIV"
  by (metis subst_atm_comp_subst subst_atm_id_subst substitution_ops.is_renaming_def surj_def)

lemma "is_renaming r1 \<Longrightarrow> is_renaming r2 \<Longrightarrow> \<tau> \<odot> r1 = r2 \<Longrightarrow> is_renaming \<tau>"
  by (metis comp_subst_assoc comp_subst_id_subst is_renaming_def)

lemma "is_renaming r1 \<Longrightarrow> is_renaming r2 \<Longrightarrow> r1 \<odot> \<tau> = r2 \<Longrightarrow> is_renaming \<tau>"
  by (metis comp_subst_assoc id_subst_comp_subst is_renaming_def)

lemma inv_ren_cancel_r[simp]: "is_renaming r \<Longrightarrow> r \<odot> (inv_ren r) = id_subst"
  unfolding inv_ren_def is_renaming_def by (metis (mono_tags) someI_ex)

lemma inv_ren_cancel_r_list[simp]:
  "is_renaming_list rs \<Longrightarrow> rs \<odot>s (map inv_ren rs) = replicate (length rs) id_subst"
  unfolding is_renaming_list_def by (induction rs) (auto simp add: comp_substs_def)

lemma inv_ren_cancel_l[simp]: "is_renaming r \<Longrightarrow> (inv_ren r) \<odot> r = id_subst"
  by (metis comp_subst_assoc id_subst_comp_subst inv_ren_cancel_r is_renaming_def
      substitution.comp_subst_id_subst substitution_axioms)

lemma inv_ren_cancel_l_list[simp]:
  "is_renaming_list rs \<Longrightarrow> (map inv_ren rs) \<odot>s rs = replicate (length rs) id_subst"
  unfolding is_renaming_list_def by (induction rs) (auto simp add: comp_substs_def)

lemma Nil_comp_substs[simp]: "[] \<odot>s s = []"
  unfolding comp_substs_def by auto

lemma comp_substs_Nil[simp]: "s \<odot>s [] = []"
  unfolding comp_substs_def by auto

lemma is_renaming_idempotent_id_subst: "is_renaming r \<Longrightarrow> r \<odot> r = r \<Longrightarrow> r = id_subst"
  by (metis comp_subst_assoc comp_subst_id_subst inv_ren_cancel_r)

lemma is_renaming_left_id_subst_right_id_subst: "is_renaming r \<Longrightarrow> s \<odot> r = id_subst \<Longrightarrow> r \<odot> s = id_subst"
  by (metis comp_subst_assoc comp_subst_id_subst is_renaming_def)

lemma is_renaming_closure: "is_renaming r1 \<Longrightarrow> is_renaming r2 \<Longrightarrow> is_renaming (r1 \<odot> r2)"
  unfolding is_renaming_def by (metis comp_subst_assoc comp_subst_id_subst)

lemma inv_ren_is_renaming[simp]: "is_renaming r \<Longrightarrow> is_renaming (inv_ren r)"
  using inv_ren_cancel_l inv_ren_cancel_r is_renaming_def by blast

lemma inv_ren_is_renaming_list[simp]: "is_renaming_list rs \<Longrightarrow> is_renaming_list (map inv_ren rs)"
  unfolding is_renaming_list_def by (induction rs) auto

lemma is_renaming_inv_ren_cancel[simp]: "is_renaming \<rho> \<Longrightarrow> C  \<cdot> \<rho> \<cdot> (inv_ren \<rho>) = C"
  by (metis inv_ren_cancel_r subst_cls_comp_subst subst_cls_id_subst)

lemma is_renaming_inv_ren_cancel2[simp]: "is_renaming \<rho> \<Longrightarrow> C  \<cdot> (inv_ren \<rho>) \<cdot> \<rho> = C"
  by (metis inv_ren_cancel_l subst_cls_comp_subst subst_cls_id_subst)

lemma is_renaming_list_inv_ren_cancel[simp]:
  "length Cs = length \<rho>s \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> Cs \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl map inv_ren \<rho>s = Cs"
  by (metis inv_ren_cancel_r_list subst_cls_lists_comp_substs subst_cls_lists_id_subst)

lemma is_renaming_list_inv_ren_cancel2[simp]:
  "length Cs = length \<rho>s \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> Cs \<cdot>\<cdot>cl map inv_ren \<rho>s \<cdot>\<cdot>cl \<rho>s = Cs"
  by (metis inv_ren_cancel_l_list subst_cls_lists_comp_substs subst_cls_lists_id_subst)


subsubsection \<open>Monotonicity\<close>

lemma subst_cls_mono: "set_mset C \<subseteq> set_mset D \<Longrightarrow> set_mset (C \<cdot> \<sigma>) \<subseteq> set_mset (D \<cdot> \<sigma>)"
  by force

lemma subst_cls_mono_mset: "C \<subseteq># D \<Longrightarrow> C \<cdot> \<sigma> \<subseteq># D \<cdot> \<sigma>"
  unfolding subst_clss_def by (metis mset_subset_eq_exists_conv subst_cls_union)

lemma subst_subset_mono: "D \<subset># C \<Longrightarrow> D \<cdot> \<sigma> \<subset># C \<cdot> \<sigma>"
  unfolding subst_cls_def
  by (simp add: image_mset_subset_mono)


subsubsection \<open>Length after substitution\<close>

lemma subst_atm_list_length[simp]: "length (As \<cdot>al \<sigma>) = length As"
  unfolding subst_atm_list_def by auto

lemma length_subst_atm_mset_list[simp]: "length (AAs \<cdot>aml \<eta>) = length AAs"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_list_length[simp]: "length (Cs \<cdot>cl \<sigma>) = length Cs"
  unfolding subst_cls_list_def by auto

lemma comp_substs_length[simp]: "length (\<tau>s \<odot>s \<sigma>s) = min (length \<tau>s) (length \<sigma>s)"
  unfolding comp_substs_def by auto

lemma subst_cls_lists_length[simp]: "length (Cs \<cdot>\<cdot>cl \<sigma>s) = min (length Cs) (length \<sigma>s)"
  unfolding subst_cls_lists_def by auto


subsubsection \<open>Variable disjointness\<close>

lemma var_disjoint_clauses:
  assumes "var_disjoint Cs"
  shows "\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> (\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>)"
proof clarify
  fix \<sigma>s :: "'s list"
  assume a: "length \<sigma>s = length Cs"
  then obtain \<tau> where "\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>"
    using assms unfolding var_disjoint_def by blast
  then have "\<forall>i < length Cs. (Cs ! i) \<cdot> \<sigma>s ! i = (Cs ! i) \<cdot> \<tau>"
    by auto
  then have "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    using a by (simp add: nth_equalityI)
  then show "\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    by auto
qed


subsubsection \<open>Ground expressions and substitutions\<close>

lemma ex_ground_subst: "\<exists>\<sigma>. is_ground_subst \<sigma>"
  using make_ground_subst[of "[]"] by (auto simp: subst_cls_list_def is_ground_cls_list_def)

lemma is_ground_cls_list_Cons[simp]:
  "is_ground_cls_list (C # Cs) = (is_ground_cls C \<and> is_ground_cls_list Cs)"
  unfolding is_ground_cls_list_def by auto

lemma make_single_ground_subst:
  assumes "is_ground_cls (C \<cdot> \<sigma>)"
  obtains \<tau> where
    "is_ground_subst \<tau>"
    "\<forall>S. S \<subseteq># C \<longrightarrow> S \<cdot> \<tau> = S \<cdot> \<sigma>"
  using assms make_ground_subst[of "[C]" \<sigma>] unfolding is_ground_cls_list_def by auto

lemma make_ground_subst_clauses:
  assumes "is_ground_cls_list (Cs \<cdot>cl \<sigma>)"
  shows "\<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>i < length Cs. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)"
  using assms make_ground_subst by blast

lemma make_ground_subst_clauses':
  assumes "is_ground_cls_list (Cs \<cdot>cl \<sigma>)"
  shows "\<exists>\<tau>. is_ground_subst \<tau> \<and> Cs \<cdot>cl \<sigma> = Cs \<cdot>cl \<tau>"
proof -
  from assms obtain \<tau> where
    "is_ground_subst \<tau> \<and> (\<forall>i<length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)"
    using make_ground_subst by blast
  then have "is_ground_subst \<tau> \<and> (\<forall>i<length Cs. (Cs ! i) \<cdot> \<sigma> = (Cs ! i) \<cdot> \<tau>)"
    by auto
  then have "is_ground_subst \<tau> \<and> Cs \<cdot>cl \<sigma> = Cs \<cdot>cl \<tau>"
    by (simp add: list_eq_iff_nth_eq)
  then show ?thesis
    by blast
qed

lemma make_ground_subst_list_clauses:
  assumes "length Cs = length \<sigma>s" and "is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  shows "\<exists>\<tau>s. is_ground_subst_list \<tau>s \<and> length \<tau>s = length Cs \<and>
    (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>s ! i)"
proof -
  have "\<forall>i < length Cs. \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<tau> = S \<cdot> \<sigma>s ! i)"
    using assms make_single_ground_subst[of "Cs ! _" "\<sigma>s ! _"] unfolding is_ground_cls_list_def
    by (metis min.idem nth_mem subst_cls_lists_length subst_cls_lists_nth)
  then obtain f where
    f_p: "\<forall>i < length Cs. is_ground_subst (f i) \<and> (\<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> f i = S \<cdot> \<sigma>s ! i)"
    by metis

  let ?\<tau>s = "map f [0 ..< length Cs]"

  have \<tau>s_p: "\<forall>i < length Cs. is_ground_subst (?\<tau>s ! i) \<and>
    (\<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> ?\<tau>s ! i = S \<cdot> \<sigma>s ! i)"
    using f_p by auto
  then have "is_ground_subst_list ?\<tau>s \<and> length ?\<tau>s = length Cs \<and>
    (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> ?\<tau>s ! i)"
    unfolding is_ground_subst_list_def by auto
  then show ?thesis
    by metis
qed

lemma make_ground_subst_list_clauses':
  assumes "length Cs = length \<sigma>s" and "is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  shows "\<exists>\<tau>s. is_ground_subst_list \<tau>s \<and> Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>\<cdot>cl \<tau>s"
proof -
  have "\<forall>i < length Cs. \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>S. S \<subseteq># (Cs ! i) \<longrightarrow> S \<cdot> \<tau> = S \<cdot> \<sigma>s ! i)"
    using assms make_single_ground_subst[of "Cs ! _" "\<sigma>s ! _"] unfolding is_ground_cls_list_def
    by (metis min.idem nth_mem subst_cls_lists_length subst_cls_lists_nth)
  then obtain f where f_p:
    "\<forall>i < length Cs. is_ground_subst (f i) \<and> (\<forall>S. S \<subseteq># (Cs ! i) \<longrightarrow> S \<cdot> (f i) = S \<cdot> \<sigma>s ! i)"
    by moura
  let ?\<tau>s = "map f [0 ..< length Cs]"
  have \<tau>s_p: "\<forall>i < length Cs. is_ground_subst (?\<tau>s ! i) \<and>
    (\<forall>S. S \<subseteq># (Cs ! i) \<longrightarrow> S \<cdot> (?\<tau>s ! i) = S \<cdot> \<sigma>s ! i)"
    using f_p by auto
  then have "is_ground_subst_list ?\<tau>s"
    unfolding is_ground_subst_list_def by auto
  moreover from \<tau>s_p have "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>\<cdot>cl ?\<tau>s"
    by (simp add: assms(1) nth_equalityI)
  ultimately show ?thesis
    by auto
qed

lemma var_disjoint_ground:
  assumes "var_disjoint Cs" and "length \<sigma>s = length Cs" and "is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  shows "\<exists>\<tau>. is_ground_subst \<tau> \<and> Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
  using assms make_ground_subst_clauses' var_disjoint_clauses by force


paragraph \<open>Ground union\<close>

lemma is_ground_atms_union[simp]: "is_ground_atms (AA \<union> BB) \<longleftrightarrow> is_ground_atms AA \<and> is_ground_atms BB"
  unfolding is_ground_atms_def by auto

lemma is_ground_atm_mset_union[simp]:
  "is_ground_atm_mset (AA + BB) \<longleftrightarrow> is_ground_atm_mset AA \<and> is_ground_atm_mset BB"
  unfolding is_ground_atm_mset_def by auto

lemma is_ground_cls_union[simp]: "is_ground_cls (C + D) \<longleftrightarrow> is_ground_cls C \<and> is_ground_cls D"
  unfolding is_ground_cls_def by auto

lemma is_ground_clss_union[simp]:
  "is_ground_clss (CC \<union> DD) \<longleftrightarrow> is_ground_clss CC \<and> is_ground_clss DD"
  unfolding is_ground_clss_def by auto

lemma is_ground_cls_mset_union[simp]:
  "is_ground_cls_mset (CC + DD) \<longleftrightarrow> is_ground_cls_mset CC \<and> is_ground_cls_mset DD"
  unfolding is_ground_cls_mset_def by auto

lemma is_ground_cls_Union_mset[iff]: "is_ground_cls (\<Union># CC) \<longleftrightarrow> is_ground_cls_mset CC"
  unfolding is_ground_cls_mset_def is_ground_cls_def by blast

lemma is_ground_cls_list_is_ground_cls_sum_list[simp]:
  "is_ground_cls_list Cs \<Longrightarrow> is_ground_cls (sum_list Cs)"
  by (meson in_mset_sum_list2 is_ground_cls_def is_ground_cls_list_def)


paragraph \<open>Ground mono\<close>

lemma is_ground_cls_mono: "C \<subseteq># D \<Longrightarrow> is_ground_cls D \<Longrightarrow> is_ground_cls C"
  unfolding is_ground_cls_def by (metis set_mset_mono subsetD)

lemma is_ground_clss_mono: "CC \<subseteq> DD \<Longrightarrow> is_ground_clss DD \<Longrightarrow> is_ground_clss CC"
  unfolding is_ground_clss_def by blast

lemma is_ground_cls_mset_mono: "CC \<subseteq># DD \<Longrightarrow> is_ground_cls_mset DD \<Longrightarrow> is_ground_cls_mset CC"
  unfolding is_ground_cls_mset_def by (metis mset_subset_eqD)

lemma grounding_of_clss_mono: "CC \<subseteq> DD \<Longrightarrow> grounding_of_clss CC \<subseteq> grounding_of_clss DD"
  using grounding_of_clss_def by auto

lemma sum_list_subseteq_mset_is_ground_cls_list[simp]:
  "sum_list Cs \<subseteq># sum_list Ds \<Longrightarrow> is_ground_cls_list Ds \<Longrightarrow> is_ground_cls_list Cs"
  by (metis is_ground_cls_Union_mset is_ground_cls_list_def is_ground_cls_mono
      is_ground_cls_mset_def set_mset_mset sum_mset_sum_list)


paragraph \<open>Substituting on ground expression preserves ground\<close>

lemma is_ground_comp_subst[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_subst (\<tau> \<odot> \<sigma>)"
  unfolding is_ground_subst_def is_ground_atm_def by auto

lemma ground_subst_ground_atm[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_atm (A \<cdot>a \<sigma>)"
  by (simp add: is_ground_subst_def)

lemma ground_subst_ground_lit[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_lit (L \<cdot>l \<sigma>)"
  unfolding is_ground_lit_def subst_lit_def by (cases L) auto

lemma ground_subst_ground_cls[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls (C \<cdot> \<sigma>)"
  unfolding is_ground_cls_def by auto

lemma ground_subst_ground_clss[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_clss (CC \<cdot>cs \<sigma>)"
  unfolding is_ground_clss_def subst_clss_def by auto

lemma ground_subst_ground_cls_list[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_list (Cs \<cdot>cl \<sigma>)"
  unfolding is_ground_cls_list_def subst_cls_list_def by auto

lemma ground_subst_ground_cls_lists[simp]:
  "\<forall>\<sigma> \<in> set \<sigma>s. is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  unfolding is_ground_cls_list_def subst_cls_lists_def by (auto simp: set_zip)

lemma ground_subst_ground_cls_mset[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_mset (CC \<cdot>cm \<sigma>)"
  unfolding is_ground_cls_mset_def subst_cls_mset_def by auto


paragraph \<open>Substituting on ground expression has no effect\<close>

lemma is_ground_subst_atm[simp]: "is_ground_atm A \<Longrightarrow> A \<cdot>a \<sigma> = A"
  unfolding is_ground_atm_def by simp

lemma is_ground_subst_atms[simp]: "is_ground_atms AA \<Longrightarrow> AA \<cdot>as \<sigma> = AA"
  unfolding is_ground_atms_def subst_atms_def image_def by auto

lemma is_ground_subst_atm_mset[simp]: "is_ground_atm_mset AA \<Longrightarrow> AA \<cdot>am \<sigma> = AA"
  unfolding is_ground_atm_mset_def subst_atm_mset_def by auto

lemma is_ground_subst_atm_list[simp]: "is_ground_atm_list As \<Longrightarrow> As \<cdot>al \<sigma> = As"
  unfolding is_ground_atm_list_def subst_atm_list_def by (auto intro: nth_equalityI)

lemma is_ground_subst_atm_list_member[simp]:
  "is_ground_atm_list As \<Longrightarrow> i < length As \<Longrightarrow> As ! i \<cdot>a \<sigma> = As ! i"
  unfolding is_ground_atm_list_def by auto

lemma is_ground_subst_lit[simp]: "is_ground_lit L \<Longrightarrow> L \<cdot>l \<sigma> = L"
  unfolding is_ground_lit_def subst_lit_def by (cases L) simp_all

lemma is_ground_subst_cls[simp]: "is_ground_cls C \<Longrightarrow> C \<cdot> \<sigma> = C"
  unfolding is_ground_cls_def subst_cls_def by simp

lemma is_ground_subst_clss[simp]: "is_ground_clss CC \<Longrightarrow> CC \<cdot>cs \<sigma> = CC"
  unfolding is_ground_clss_def subst_clss_def image_def by auto

lemma is_ground_subst_cls_mset[simp]: "is_ground_cls_mset CC \<Longrightarrow> CC \<cdot>cm \<sigma> = CC"
  unfolding is_ground_cls_mset_def subst_cls_mset_def by auto

lemma is_ground_subst_cls_list[simp]:
  assumes "length P = length Cs" and "is_ground_cls_list Cs"
  shows "Cs \<cdot>\<cdot>cl P = Cs"
  by (metis assms is_ground_cls_list_def is_ground_subst_cls min.idem nth_equalityI nth_mem
      subst_cls_lists_nth subst_cls_lists_length)

lemma is_ground_subst_lit_iff: "is_ground_lit L \<longleftrightarrow> (\<forall>\<sigma>. L = L \<cdot>l \<sigma>)"
  using is_ground_atm_def is_ground_lit_def subst_lit_def by (cases L) auto

lemma is_ground_subst_cls_iff: "is_ground_cls C \<longleftrightarrow> (\<forall>\<sigma>. C = C \<cdot> \<sigma>)"
  by (metis ex_ground_subst ground_subst_ground_cls is_ground_subst_cls)


paragraph \<open>Members of ground expressions are ground\<close>

lemma is_ground_cls_as_atms: "is_ground_cls C \<longleftrightarrow> (\<forall>A \<in> atms_of C. is_ground_atm A)"
  by (auto simp: atms_of_def is_ground_cls_def is_ground_lit_def)

lemma is_ground_cls_imp_is_ground_lit: "L \<in># C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_lit L"
  by (simp add: is_ground_cls_def)

lemma is_ground_cls_imp_is_ground_atm: "A \<in> atms_of C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_atm A"
  by (simp add: is_ground_cls_as_atms)

lemma is_ground_cls_is_ground_atms_atms_of[simp]: "is_ground_cls C \<Longrightarrow> is_ground_atms (atms_of C)"
  by (simp add: is_ground_cls_imp_is_ground_atm is_ground_atms_def)

lemma grounding_ground: "C \<in> grounding_of_clss M \<Longrightarrow> is_ground_cls C"
  unfolding grounding_of_clss_def grounding_of_cls_def by auto

lemma in_subset_eq_grounding_of_clss_is_ground_cls[simp]:
  "C \<in> CC \<Longrightarrow> CC \<subseteq> grounding_of_clss DD \<Longrightarrow> is_ground_cls C"
  unfolding grounding_of_clss_def grounding_of_cls_def by auto


subsubsection \<open>Unifiers\<close>

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
  by (rule iffI, metis empty_iff insert_iff insert_image, blast)

lemma is_unifiers_subst_atm_eqI:
  assumes "finite AA" "is_unifiers \<sigma> AAA" "AA \<in> AAA" "A \<in> AA" "B \<in> AA"
  shows "A \<cdot>a \<sigma> = B \<cdot>a \<sigma>"
  by (metis assms is_unifiers_def is_unifier_subst_atm_eqI)

theorem is_unifiers_comp:
  "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As Bs) \<cdot>ass \<eta>) \<longleftrightarrow>
   is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset As Bs))"
  unfolding is_unifiers_def is_unifier_def subst_atmss_def by auto


subsubsection \<open>Most general unifier\<close>

lemma is_mgu_is_unifiers: "is_mgu \<sigma> AAA \<Longrightarrow> is_unifiers \<sigma> AAA"
  using is_mgu_def by blast

lemma is_mgu_is_more_general: "is_mgu \<sigma> AAA \<Longrightarrow> is_unifiers \<tau> AAA \<Longrightarrow> (\<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>)"
  using is_mgu_def by blast

lemma is_unifiers_is_unifier: "is_unifiers \<sigma> AAA \<Longrightarrow> AA \<in> AAA \<Longrightarrow> is_unifier \<sigma> AA"
  using is_unifiers_def by auto

end


subsection \<open>Most general unifiers\<close>

locale mgu = substitution subst_atm id_subst comp_subst renamings_apart
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" +
  fixes
    mgu :: "'a set set \<Rightarrow> 's option"
  assumes
    mgu_sound: "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA) \<Longrightarrow> mgu AAA = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> AAA" and
    mgu_complete:
      "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA) \<Longrightarrow> is_unifiers \<sigma> AAA \<Longrightarrow> \<exists>\<tau>. mgu AAA = Some \<tau>"
begin

lemmas is_unifiers_mgu = mgu_sound[unfolded is_mgu_def, THEN conjunct1]
lemmas is_mgu_most_general = mgu_sound[unfolded is_mgu_def, THEN conjunct2]

lemma mgu_unifier:
  assumes
    aslen: "length As = n" and
    aaslen: "length AAs = n" and
    mgu: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs))"
  shows "\<forall>i < n. \<forall>A \<in># AAs ! i. A \<cdot>a \<sigma> = As ! i \<cdot>a \<sigma>"
proof (intro allI impI)
  fix i
  assume i: "i < n"

  from mgu have "is_mgu \<sigma> (set_mset ` set (map2 add_mset As AAs))"
    using mgu_sound by auto
  then have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As AAs))"
    using is_mgu_is_unifiers by auto
  then have "is_unifier \<sigma> (set_mset (add_mset (As ! i) (AAs ! i)))"
    using i aslen aaslen unfolding is_unifiers_def is_unifier_def
    by simp (metis length_zip min.idem nth_mem nth_zip old.prod.case set_mset_add_mset_insert)
  then show "\<forall>A \<in># AAs ! i. A \<cdot>a \<sigma> = As ! i \<cdot>a \<sigma>"
    using aslen aaslen is_unifier_subst_atm_eqI
    by (metis finite_set_mset insertCI set_mset_add_mset_insert)
qed

end

end
