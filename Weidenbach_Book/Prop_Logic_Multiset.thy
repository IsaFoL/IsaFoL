theory Prop_Logic_Multiset
imports "$AFP/Nested_Multisets_Ordinals/Multiset_More" Prop_Normalisation Partial_Clausal_Logic
begin

section \<open>Link with Multiset Version\<close>

subsection \<open>Transformation to Multiset\<close>

fun mset_of_conj :: "'a propo \<Rightarrow> 'a literal multiset" where
"mset_of_conj (FOr \<phi> \<psi>) = mset_of_conj \<phi> + mset_of_conj \<psi>" |
"mset_of_conj (FVar v) = {# Pos v #}" |
"mset_of_conj (FNot (FVar v)) = {# Neg v #}" |
"mset_of_conj FF = {#}"

fun mset_of_formula :: "'a propo \<Rightarrow> 'a literal multiset set" where
"mset_of_formula (FAnd \<phi> \<psi>) = mset_of_formula \<phi> \<union> mset_of_formula \<psi>" |
"mset_of_formula (FOr \<phi> \<psi>) = {mset_of_conj (FOr \<phi> \<psi>)}" |
"mset_of_formula (FVar \<psi>) = {mset_of_conj (FVar \<psi>)}" |
"mset_of_formula (FNot \<psi>) = {mset_of_conj (FNot \<psi>)}" |
"mset_of_formula FF = {{#}}" |
"mset_of_formula FT = {}"

subsection \<open>Equisatisfiability of the two Version\<close>

lemma is_conj_with_TF_FNot: 
  "is_conj_with_TF (FNot \<phi>) \<longleftrightarrow> (\<exists>v. \<phi> = FVar v \<or> \<phi> = FF \<or> \<phi> = FT)"
  unfolding is_conj_with_TF_def apply (rule iffI)
  apply (induction "FNot \<phi>" rule: super_grouped_by.induct)
  apply (induction "FNot \<phi>" rule: grouped_by.induct)
     apply simp
    apply (cases \<phi>; simp)
  apply auto
  done

lemma grouped_by_COr_FNot: 
  "grouped_by COr (FNot \<phi>) \<longleftrightarrow> (\<exists>v. \<phi> = FVar v \<or> \<phi> = FF \<or> \<phi> = FT)"
  unfolding is_conj_with_TF_def apply (rule iffI)
  apply (induction "FNot \<phi>" rule: grouped_by.induct)
     apply simp
    apply (cases \<phi>; simp)
  apply auto
  done

lemma 
  shows no_T_F_FF[simp]: "\<not>no_T_F FF" and
    no_T_F_FT[simp]: "\<not>no_T_F FT"
  unfolding no_T_F_def all_subformula_st_def by auto

lemma grouped_by_CAnd_FAnd:
  "grouped_by CAnd (FAnd \<phi>1 \<phi>2) \<longleftrightarrow> grouped_by CAnd \<phi>1 \<and> grouped_by CAnd \<phi>2"
  apply (rule iffI)
  apply (induction "FAnd \<phi>1 \<phi>2" rule: grouped_by.induct)
  using connected_is_group[of CAnd \<phi>1 \<phi>2] by auto

lemma grouped_by_COr_FOr:
  "grouped_by COr (FOr \<phi>1 \<phi>2) \<longleftrightarrow> grouped_by COr \<phi>1 \<and> grouped_by COr \<phi>2"
  apply (rule iffI)
  apply (induction "FOr \<phi>1 \<phi>2" rule: grouped_by.induct)
  using connected_is_group[of COr \<phi>1 \<phi>2] by auto

  
lemma grouped_by_COr_FAnd[simp]: "\<not> grouped_by COr (FAnd \<phi>1 \<phi>2)"
  apply clarify
   apply (induction "FAnd \<phi>1 \<phi>2" rule: grouped_by.induct)
   apply auto
  done

lemma grouped_by_COr_FEq[simp]: "\<not> grouped_by COr (FEq \<phi>1 \<phi>2)"
  apply clarify
   apply (induction "FEq \<phi>1 \<phi>2" rule: grouped_by.induct)
   apply auto
  done

lemma [simp]: "\<not>grouped_by COr (FImp \<phi> \<psi>)"
  apply clarify
  by (induction "FImp \<phi> \<psi>" rule: grouped_by.induct) simp_all

lemma [simp]: "\<not> is_conj_with_TF (FImp \<phi> \<psi>)"
  unfolding is_conj_with_TF_def apply clarify
  by (induction "FImp \<phi> \<psi>" rule: super_grouped_by.induct) simp_all

lemma [simp]: "\<not>grouped_by COr (FEq \<phi> \<psi>)"
  apply clarify
  by (induction "FEq \<phi> \<psi>" rule: grouped_by.induct) simp_all

lemma [simp]: "\<not> is_conj_with_TF (FEq \<phi> \<psi>)"
  unfolding is_conj_with_TF_def apply clarify
  by (induction "FEq \<phi> \<psi>" rule: super_grouped_by.induct) simp_all

lemma is_conj_with_TF_Fand:
  "is_conj_with_TF (FAnd \<phi>1 \<phi>2) \<Longrightarrow>  is_conj_with_TF \<phi>1 \<and>  is_conj_with_TF \<phi>2"
  unfolding is_conj_with_TF_def
  apply (induction "FAnd \<phi>1 \<phi>2" rule: super_grouped_by.induct)
   apply (auto simp: grouped_by_CAnd_FAnd intro: grouped_is_super_grouped)[]
  apply auto[]
  done

lemma is_conj_with_TF_FOr:
  "is_conj_with_TF (FOr \<phi>1 \<phi>2) \<Longrightarrow> grouped_by COr \<phi>1 \<and> grouped_by COr \<phi>2"
  unfolding is_conj_with_TF_def
  apply (induction "FOr \<phi>1 \<phi>2" rule: super_grouped_by.induct)
   apply (auto simp: grouped_by_COr_FOr)[]
  apply auto[]
  done

lemma grouped_by_COr_mset_of_formula:
  "grouped_by COr \<phi> \<Longrightarrow> mset_of_formula \<phi> = (if \<phi> = FT then {} else {mset_of_conj \<phi>})"
  by (induction \<phi>) (auto simp add: grouped_by_COr_FNot)

text \<open>When a formula is in CNF form, then there is equisatisfiability between the multiset version 
  and the CNF form. Remark that the definition for the entailment are slightly different: 
  @{term eval} uses a function assigning @{term True} or @{term False}, while 
  @{term Partial_Clausal_Logic.true_clss} uses a set where being in the list means entailment of a 
  literal.
  \<close>
theorem 
  fixes \<phi> :: "'v propo"
  assumes "is_cnf \<phi>"
  shows "eval A \<phi> \<longleftrightarrow> Partial_Clausal_Logic.true_clss ({Pos v|v. A v} \<union> {Neg v|v. \<not>A v})
    (mset_of_formula \<phi>)"
  using assms 
proof (induction \<phi>)
  case FF
  then show ?case by auto
next
  case FT
  then show ?case by auto
next
  case (FVar v)
  then show ?case by auto
next
  case (FAnd \<phi> \<psi>)
  then show ?case
  unfolding is_cnf_def by (auto simp: is_conj_with_TF_FNot dest: is_conj_with_TF_Fand
    dest!:is_conj_with_TF_FOr)
next
  case (FOr \<phi> \<psi>)
  then have [simp]: "mset_of_formula \<phi> = {mset_of_conj \<phi>}" "mset_of_formula \<psi> = {mset_of_conj \<psi>}"
    unfolding is_cnf_def by (auto dest!:is_conj_with_TF_FOr simp: grouped_by_COr_mset_of_formula 
      split: if_splits)
  have "is_conj_with_TF \<phi>" "is_conj_with_TF \<psi>"
    using FOr(3) unfolding is_cnf_def no_T_F_def
    by (metis grouped_is_super_grouped is_conj_with_TF_FOr is_conj_with_TF_def)+
  then show ?case using FOr
    unfolding is_cnf_def by simp
next
  case (FImp \<phi> \<psi>)
  then show ?case
    unfolding is_cnf_def by auto
next
  case (FEq \<phi> \<psi>)
  then show ?case
    unfolding is_cnf_def by auto
next
  case (FNot \<phi>)
  then show ?case 
    unfolding is_cnf_def by (auto simp: is_conj_with_TF_FNot)
qed

end
