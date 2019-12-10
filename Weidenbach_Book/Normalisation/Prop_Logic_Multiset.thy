theory Prop_Logic_Multiset
imports Nested_Multisets_Ordinals.Multiset_More Prop_Normalisation
  Entailment_Definition.Partial_Herbrand_Interpretation
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

subsection \<open>Equisatisfiability of the two Versions\<close>

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

lemma [simp]: "\<not> is_conj_with_TF (FEq \<phi> \<psi>)"
  unfolding is_conj_with_TF_def apply clarify
  by (induction "FEq \<phi> \<psi>" rule: super_grouped_by.induct) simp_all

lemma is_conj_with_TF_Fand:
  "is_conj_with_TF (FAnd \<phi>1 \<phi>2) \<Longrightarrow> is_conj_with_TF \<phi>1 \<and>  is_conj_with_TF \<phi>2"
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
  @{term Partial_Herbrand_Interpretation.true_clss} uses a set where being in the list means entailment of a
  literal.
  \<close>
theorem cnf_eval_true_clss:
  fixes \<phi> :: "'v propo"
  assumes "is_cnf \<phi>"
  shows "eval A \<phi> \<longleftrightarrow> Partial_Herbrand_Interpretation.true_clss ({Pos v|v. A v} \<union> {Neg v|v. \<not>A v})
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
    dest!: is_conj_with_TF_FOr)
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

function formula_of_mset :: "'a clause \<Rightarrow> 'a propo" where
  \<open>formula_of_mset \<phi> =
     (if \<phi> = {#} then FF
      else
         let v = (SOME v. v \<in># \<phi>);
             v' = (if is_pos v then FVar (atm_of v) else FNot (FVar (atm_of v))) in
         if remove1_mset v \<phi> = {#} then v'
         else FOr v' (formula_of_mset (remove1_mset v \<phi>)))\<close>
  by auto
termination
  apply (relation \<open>measure size\<close>)
   apply (auto simp: size_mset_remove1_mset_le_iff)
  by (meson multiset_nonemptyE someI_ex)

lemma formula_of_mset_empty[simp]: \<open>formula_of_mset {#} = FF\<close>
  by (auto simp: Let_def)

lemma formula_of_mset_empty_iff[iff]: \<open>formula_of_mset \<phi> = FF \<longleftrightarrow> \<phi> = {#}\<close>
  by (induction \<phi>) (auto simp: Let_def)

declare formula_of_mset.simps[simp del]

function formula_of_msets :: "'a literal multiset set \<Rightarrow> 'a propo" where
  \<open>formula_of_msets \<phi>s =
     (if \<phi>s = {} \<or> infinite \<phi>s then FT
      else
         let v = (SOME v. v \<in> \<phi>s);
             v' = formula_of_mset v in
         if \<phi>s - {v} = {} then v'
         else FAnd v' (formula_of_msets (\<phi>s - {v})))\<close>
  by auto
termination
  apply (relation \<open>measure card\<close>)
   apply (auto simp: some_in_eq)
  by (metis all_not_in_conv card_gt_0_iff diff_less lessI)

declare formula_of_msets.simps[simp del]

lemma remove1_mset_empty_iff:
  \<open>remove1_mset v \<phi> = {#} \<longleftrightarrow> (\<phi> = {#} \<or> \<phi> = {#v#})\<close>
  using remove1_mset_eqE by force

definition fun_of_set where
  \<open>fun_of_set A x = (if Pos x \<in> A then True else if Neg x \<in> A then False else undefined)\<close>

lemma grouped_by_COr_formula_of_mset: \<open>grouped_by COr (formula_of_mset \<phi>)\<close>
proof (induction \<open>size \<phi>\<close> arbitrary: \<phi>)
  case 0
  then show ?case by (subst formula_of_mset.simps) (auto simp: Let_def)
next
  case (Suc n) note IH = this(1) and s = this(2)
  then have \<open>n = size (remove1_mset (SOME v. v \<in># \<phi>) \<phi>)\<close> if \<open>\<phi> \<noteq> {#}\<close>
    using that by (auto simp: size_Diff_singleton_if some_in_eq)
  then show ?case
    using IH[of \<open>remove1_mset (SOME v. v \<in># \<phi>) \<phi>\<close>]
    by(subst formula_of_mset.simps) (auto simp: Let_def grouped_by_COr_FOr)
qed
lemma no_T_F_formula_of_mset: \<open>no_T_F (formula_of_mset \<phi>)\<close> if \<open>formula_of_mset \<phi> \<noteq> FF\<close> for \<phi>
  using that
proof (induction \<open>size \<phi>\<close> arbitrary: \<phi>)
  case 0
  then show ?case by (subst formula_of_mset.simps) (auto simp: Let_def no_T_F_def
        all_subformula_st_def)
next
  case (Suc n) note IH = this(1) and s = this(2) and FF = this(3)
  then have \<open>n = size (remove1_mset (SOME v. v \<in># \<phi>) \<phi>)\<close> if \<open>\<phi> \<noteq> {#}\<close>
    using that by (auto simp: size_Diff_singleton_if some_in_eq)
  moreover have \<open>no_T_F (FVar (atm_of (SOME v. v \<in># \<phi>)))\<close>
    by (auto simp: no_T_F_def)
  ultimately show ?case
    using IH[of \<open>remove1_mset (SOME v. v \<in># \<phi>) \<phi>\<close>] FF
    by(subst formula_of_mset.simps) (auto simp: Let_def grouped_by_COr_FOr)
qed

lemma mset_of_conj_formula_of_mset[simp]: \<open>mset_of_conj(formula_of_mset \<phi>) = \<phi>\<close> for \<phi>
proof (induction \<open>size \<phi>\<close> arbitrary: \<phi>)
  case 0
  then show ?case by (subst formula_of_mset.simps) (auto simp: Let_def no_T_F_def
        all_subformula_st_def)
next
  case (Suc n) note IH = this(1) and s = this(2)
  then have \<open>n = size (remove1_mset (SOME v. v \<in># \<phi>) \<phi>)\<close> if \<open>\<phi> \<noteq> {#}\<close>
    using that by (auto simp: size_Diff_singleton_if some_in_eq)
  moreover have \<open>no_T_F (FVar (atm_of (SOME v. v \<in># \<phi>)))\<close>
    by (auto simp: no_T_F_def)
  ultimately show ?case
    using IH[of \<open>remove1_mset (SOME v. v \<in># \<phi>) \<phi>\<close>]
    by(subst formula_of_mset.simps) (auto simp: some_in_eq Let_def grouped_by_COr_FOr remove1_mset_empty_iff)
qed

lemma mset_of_formula_formula_of_mset [simp]: \<open>mset_of_formula (formula_of_mset \<phi>) = {\<phi>}\<close> for \<phi>
proof (induction \<open>size \<phi>\<close> arbitrary: \<phi>)
  case 0
  then show ?case by (subst formula_of_mset.simps) (auto simp: Let_def no_T_F_def
        all_subformula_st_def)
next
  case (Suc n) note IH = this(1) and s = this(2)
  then have \<open>n = size (remove1_mset (SOME v. v \<in># \<phi>) \<phi>)\<close> if \<open>\<phi> \<noteq> {#}\<close>
    using that by (auto simp: size_Diff_singleton_if some_in_eq)
  moreover have \<open>no_T_F (FVar (atm_of (SOME v. v \<in># \<phi>)))\<close>
    by (auto simp: no_T_F_def)
  ultimately show ?case
    using IH[of \<open>remove1_mset (SOME v. v \<in># \<phi>) \<phi>\<close>]
    by(subst formula_of_mset.simps) (auto simp: some_in_eq Let_def grouped_by_COr_FOr remove1_mset_empty_iff)
qed

lemma formula_of_mset_is_cnf: \<open>is_cnf (formula_of_mset \<phi>)\<close>
  by (auto simp: is_cnf_def is_conj_with_TF_def grouped_by_COr_formula_of_mset no_T_F_formula_of_mset
        intro!: grouped_is_super_grouped)

lemma eval_clss_iff:
  assumes \<open>consistent_interp A\<close> and \<open>total_over_set A UNIV\<close>
  shows \<open>eval (fun_of_set A) (formula_of_mset \<phi>) \<longleftrightarrow> Partial_Herbrand_Interpretation.true_clss A {\<phi>}\<close>
  apply (subst cnf_eval_true_clss[OF formula_of_mset_is_cnf])
  using assms
  apply (auto simp add: true_cls_def fun_of_set_def consistent_interp_def total_over_set_def)
  apply (case_tac L)
  by (fastforce simp add: true_cls_def fun_of_set_def consistent_interp_def total_over_set_def)+

lemma is_conj_with_TF_Fand_iff:
  "is_conj_with_TF (FAnd \<phi>1 \<phi>2) \<longleftrightarrow> is_conj_with_TF \<phi>1 \<and> is_conj_with_TF \<phi>2 "
  unfolding is_conj_with_TF_def by (subst super_grouped_by.simps) auto

lemma is_CNF_Fand:
  \<open>is_cnf (FAnd \<phi> \<psi>) \<longleftrightarrow> (is_cnf \<phi> \<and> no_T_F \<phi>) \<and> is_cnf \<psi> \<and> no_T_F \<psi>\<close>
  by (auto simp: is_cnf_def is_conj_with_TF_Fand_iff)

lemma no_T_F_formula_of_mset_iff: \<open>no_T_F (formula_of_mset \<phi>) \<longleftrightarrow> \<phi> \<noteq> {#}\<close>
proof (induction \<open>size \<phi>\<close> arbitrary: \<phi>)
  case 0
  then show ?case by (subst formula_of_mset.simps) (auto simp: Let_def no_T_F_def
        all_subformula_st_def)
next
  case (Suc n) note IH = this(1) and s = this(2)
  then have \<open>n = size (remove1_mset (SOME v. v \<in># \<phi>) \<phi>)\<close> if \<open>\<phi> \<noteq> {#}\<close>
    using that by (auto simp: size_Diff_singleton_if some_in_eq)
  moreover have \<open>no_T_F (FVar (atm_of (SOME v. v \<in># \<phi>)))\<close>
    by (auto simp: no_T_F_def)
  ultimately show ?case
    using IH[of \<open>remove1_mset (SOME v. v \<in># \<phi>) \<phi>\<close>]
    by(subst formula_of_mset.simps) (auto simp: some_in_eq Let_def grouped_by_COr_FOr remove1_mset_empty_iff)
qed

lemma no_T_F_formula_of_msets:
  assumes \<open>finite \<phi>\<close> and \<open>{#} \<notin> \<phi>\<close> and \<open>\<phi> \<noteq> {}\<close>
  shows \<open>no_T_F (formula_of_msets (\<phi>))\<close>
  using assms apply (induction \<open>card \<phi>\<close> arbitrary: \<phi>)
  subgoal by (subst formula_of_msets.simps) (auto simp: no_T_F_def all_subformula_st_def)[]
  subgoal
    apply (subst formula_of_msets.simps)
    apply (auto split:  simp: Let_def formula_of_mset_is_cnf is_CNF_Fand
        no_T_F_formula_of_mset_iff some_in_eq)
    apply (metis (mono_tags, lifting) some_eq_ex)
    done
  done

lemma is_cnf_formula_of_msets:
  assumes \<open>finite \<phi>\<close> and \<open>{#} \<notin> \<phi>\<close>
  shows \<open>is_cnf (formula_of_msets \<phi>)\<close>
  using assms apply (induction \<open>card \<phi>\<close> arbitrary: \<phi>)
  subgoal by (subst formula_of_msets.simps) (auto simp: is_cnf_def is_conj_with_TF_def)[]
  subgoal
    apply (subst formula_of_msets.simps)
    apply (auto split:  simp: Let_def formula_of_mset_is_cnf is_CNF_Fand
        no_T_F_formula_of_mset_iff some_in_eq intro: no_T_F_formula_of_msets)
    apply (metis (mono_tags, lifting) some_eq_ex)
    done
  done

lemma mset_of_formula_formula_of_msets:
  assumes \<open>finite \<phi>\<close>
  shows \<open>mset_of_formula (formula_of_msets \<phi>) = \<phi>\<close>
  using assms apply (induction \<open>card \<phi>\<close> arbitrary: \<phi>)
  subgoal by (subst formula_of_msets.simps) (auto simp: is_cnf_def is_conj_with_TF_def)[]
  subgoal
    apply (subst formula_of_msets.simps)
    apply (auto split:  simp: Let_def formula_of_mset_is_cnf is_CNF_Fand
        no_T_F_formula_of_mset_iff some_in_eq intro: no_T_F_formula_of_msets)
    done
  done

lemma
  assumes \<open>consistent_interp A\<close> and \<open>total_over_set A UNIV\<close> and \<open>finite \<phi>\<close> and \<open>{#} \<notin> \<phi>\<close>
  shows \<open>eval (fun_of_set A) (formula_of_msets \<phi>) \<longleftrightarrow> Partial_Herbrand_Interpretation.true_clss A \<phi>\<close>
  apply (subst cnf_eval_true_clss[OF is_cnf_formula_of_msets[OF assms(3-4)]])
  using assms(3) unfolding mset_of_formula_formula_of_msets[OF assms(3)]
  by (induction \<phi>)
    (use eval_clss_iff[OF assms(1,2)] in \<open>simp_all add: cnf_eval_true_clss formula_of_mset_is_cnf\<close>)

end
