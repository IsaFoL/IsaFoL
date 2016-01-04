(*  Title:       Clausal Logic
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2014 
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* Clausal Logic *}

theory Clausal_Logic
imports "../lib/Multiset_More"
begin

text {*
Resolution operates of clauses, which are disjunctions of literals. The material formalized here
corresponds roughly to Sections 2.1 (``Formulas and Clauses'')  of Bachmair and Ganzinger, excluding the formula and term syntax.
*}


subsection {* Literals *}

text {*
Literals consist of a polarity (positive or negative) and an atom, of type @{typ 'a}.
*}

datatype 'a literal =
  is_pos: Pos (atm_of: 'a)
| Neg (atm_of: 'a)

abbreviation is_neg :: "'a literal \<Rightarrow> bool" where "is_neg L \<equiv> \<not> is_pos L"

lemma Pos_atm_of_iff[simp]: "Pos (atm_of L) = L \<longleftrightarrow> is_pos L"
  by auto (metis literal.disc(1))

lemma Neg_atm_of_iff[simp]: "Neg (atm_of L) = L \<longleftrightarrow> is_neg L"
  by auto (metis literal.disc(2))

lemma ex_lit_cases: "(\<exists>L. P L) \<longleftrightarrow> (\<exists>A. P (Pos A) \<or> P (Neg A))"
  by (metis literal.exhaust)

instantiation literal :: (type) uminus
begin

definition uminus_literal :: "'a literal \<Rightarrow> 'a literal" where
  "uminus L = (if is_pos L then Neg else Pos) (atm_of L)"

instance ..

end

lemma
  uminus_Pos[simp]: "- Pos A = Neg A" and
  uminus_Neg[simp]: "- Neg A = Pos A"
  unfolding uminus_literal_def by simp_all

lemma atm_of_uminus[simp]:
  "atm_of (-L) = atm_of L"
  by (case_tac L, auto)

lemma uminus_of_uminus_id[simp]:
  "- (- (x:: 'v literal)) = x"
  by (simp add: uminus_literal_def)

lemma uminus_not_id[simp]:
  "x \<noteq> - (x:: 'v literal)"
  by (case_tac x, auto)

lemma uminus_not_id'[simp]:
  "- x \<noteq> (x:: 'v literal)"
  by (case_tac x, auto)

lemma uminus_eq_inj[iff]:
  "-(a::'v literal) = -b \<longleftrightarrow> a = b"
  by (case_tac a; case_tac b) auto+

instantiation literal :: (preorder) preorder
begin

definition less_literal :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "less_literal L M \<longleftrightarrow> atm_of L < atm_of M \<or> atm_of L \<le> atm_of M \<and> is_neg L < is_neg M"

definition less_eq_literal :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "less_eq_literal L M \<longleftrightarrow> atm_of L < atm_of M \<or> atm_of L \<le> atm_of M \<and> is_neg L \<le> is_neg M"

instance
  apply intro_classes
  unfolding less_literal_def less_eq_literal_def by (auto intro: order_trans simp: less_le_not_le)

end

instantiation literal :: (order) order
begin

instance
  apply intro_classes
  unfolding less_eq_literal_def by (auto intro: literal.expand)

end

lemma pos_less_neg[simp]: "Pos A < Neg A"
  unfolding less_literal_def by simp

lemma pos_less_pos_iff[simp]: "Pos A < Pos B \<longleftrightarrow> A < B"
  unfolding less_literal_def by simp

lemma pos_less_neg_iff[simp]: "Pos A < Neg B \<longleftrightarrow> A \<le> B"
  unfolding less_literal_def by (auto simp: less_le_not_le)

lemma neg_less_pos_iff[simp]: "Neg A < Pos B \<longleftrightarrow> A < B"
  unfolding less_literal_def by simp

lemma neg_less_neg_iff[simp]: "Neg A < Neg B \<longleftrightarrow> A < B"
  unfolding less_literal_def by simp

lemma pos_le_neg[simp]: "Pos A \<le> Neg A"
  unfolding less_eq_literal_def by simp

lemma pos_le_pos_iff[simp]: "Pos A \<le> Pos B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_literal_def by (auto simp: less_le_not_le)

lemma pos_le_neg_iff[simp]: "Pos A \<le> Neg B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_literal_def by (auto simp: less_imp_le)

lemma neg_le_pos_iff[simp]: "Neg A \<le> Pos B \<longleftrightarrow> A < B"
  unfolding less_eq_literal_def by simp

lemma neg_le_neg_iff[simp]: "Neg A \<le> Neg B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_literal_def by (auto simp: less_imp_le)

lemma leq_imp_less_eq_atm_of: "L \<le> M \<Longrightarrow> atm_of L \<le> atm_of M"
  by (metis less_eq_literal_def less_le_not_le)

instantiation literal :: (linorder) linorder
begin

instance
  apply intro_classes
  unfolding less_eq_literal_def less_literal_def by auto

end

instantiation literal :: (wellorder) wellorder
begin

instance
proof intro_classes
  fix P :: "'a literal \<Rightarrow> bool" and L :: "'a literal"
  assume ih: "\<And>L. (\<And>M. M < L \<Longrightarrow> P M) \<Longrightarrow> P L"
  have "\<And>x. (\<And>y. y < x \<Longrightarrow> P (Pos y) \<and> P (Neg y)) \<Longrightarrow> P (Pos x) \<and> P (Neg x)"
    by (rule conjI[OF ih ih])
      (auto simp: less_literal_def atm_of_def split: literal.splits intro: ih)
  hence "\<And>A. P (Pos A) \<and> P (Neg A)"
    by (rule less_induct) blast
  thus "P L"
    by (cases L) simp+
qed

end


subsection {* Clauses *}

text {*
Clauses are (finite) multisets of literals.
*}

type_synonym 'a clause = "'a literal multiset"

abbreviation poss :: "'a multiset \<Rightarrow> 'a clause" where "poss AA \<equiv> {#Pos A. A \<in># AA#}"
abbreviation negs :: "'a multiset \<Rightarrow> 'a clause" where "negs AA \<equiv> {#Neg A. A \<in># AA#}"

lemma image_replicate_mset[simp]: "{#f A. A \<in># replicate_mset n A#} = replicate_mset n (f A)"
  by (induct n) (simp, subst replicate_mset_Suc, simp)

lemma Max_in_lits: "C \<noteq> {#} \<Longrightarrow> Max (set_mset C) \<in># C"
  by (rule Max_in[OF finite_set_mset, unfolded mem_set_mset_iff set_mset_eq_empty_iff])

lemma Max_atm_of_set_mset_commute: "C \<noteq> {#} \<Longrightarrow> Max (atm_of ` set_mset C) = atm_of (Max (set_mset C))"
  by (rule mono_Max_commute[symmetric])
    (auto simp: mono_def atm_of_def less_eq_literal_def less_literal_def)

lemma Max_pos_neg_less_multiset:
  assumes max: "Max (set_mset C) = Pos A" and neg: "Neg A \<in># D"
  shows "C #\<subset># D"
proof -
  have "Max (set_mset C) < Neg A"
    using max by simp
  thus ?thesis
    using neg by (metis (no_types) ex_gt_imp_less_multiset Max_less_iff[OF finite_set_mset]
      all_not_in_conv mem_set_mset_iff)
qed

lemma pos_Max_imp_neg_notin: "Max (set_mset C) = Pos A \<Longrightarrow> \<not> Neg A \<in># C"
  using Max_pos_neg_less_multiset[unfolded multiset_linorder.not_le[symmetric]] by blast

lemma less_eq_Max_lit: "C \<noteq> {#} \<Longrightarrow> C #\<subseteq># D \<Longrightarrow> Max (set_mset C) \<le> Max (set_mset D)"
proof (unfold le_multiset\<^sub>H\<^sub>O)
  assume ne: "C \<noteq> {#}" and ex_gt: "\<forall>x. count D x < count C x \<longrightarrow> (\<exists>y > x. count C y < count D y)"
  from ne have "Max (set_mset C) \<in># C"
    by (fast intro: Max_in_lits)
  hence "\<exists>l. l \<in># D \<and> \<not> l < Max (set_mset C)"
    using ex_gt by (metis not_less0 not_less_iff_gr_or_eq)
  hence "\<not> Max (set_mset D) < Max (set_mset C)"
    by (metis Max.coboundedI[OF finite_set_mset] le_less_trans mem_set_mset_iff)
  thus ?thesis
    by simp
qed

definition atms_of :: "'a clause \<Rightarrow> 'a set" where
  "atms_of C = atm_of ` set_mset C"

lemma atms_of_empty[simp]: "atms_of {#} = {}"
  unfolding atms_of_def by simp

lemma atms_of_singleton[simp]: "atms_of {#L#} = {atm_of L}"
  unfolding atms_of_def by auto

lemma finite_atms_of[iff]: "finite (atms_of C)"
  unfolding atms_of_def by simp

lemma atm_of_lit_in_atms_of: "L \<in># C \<Longrightarrow> atm_of L \<in> atms_of C"
  unfolding atms_of_def by simp

lemma atms_of_plus[simp]: "atms_of (C + D) = atms_of C \<union> atms_of D"
  unfolding atms_of_def image_def by auto

lemma pos_lit_in_atms_of: "Pos A \<in># C \<Longrightarrow> A \<in> atms_of C"
  unfolding atms_of_def by (metis image_iff literal.sel(1) mem_set_mset_iff)

lemma neg_lit_in_atms_of: "Neg A \<in># C \<Longrightarrow> A \<in> atms_of C"
  unfolding atms_of_def by (metis image_iff literal.sel(2) mem_set_mset_iff)

lemma atm_imp_pos_or_neg_lit: "A \<in> atms_of C \<Longrightarrow> Pos A \<in># C \<or> Neg A \<in># C"
  unfolding atms_of_def image_def mem_Collect_eq
  by (metis Neg_atm_of_iff Pos_atm_of_iff mem_set_mset_iff)

lemma atm_iff_pos_or_neg_lit: "A \<in> atms_of L \<longleftrightarrow> Pos A \<in># L \<or> Neg A \<in># L"
  by (auto intro: pos_lit_in_atms_of neg_lit_in_atms_of dest: atm_imp_pos_or_neg_lit)

lemma atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set:
  "atm_of L \<in> atm_of ` I \<longleftrightarrow> (L \<in> I \<or> -L \<in> I)"
  apply (auto intro: rev_image_eqI)
  by (cases L; case_tac x) (auto intro: rev_image_eqI)

lemma lits_subseteq_imp_atms_subseteq: "set_mset C \<subseteq> set_mset D \<Longrightarrow> atms_of C \<subseteq> atms_of D"
  unfolding atms_of_def by blast

lemma atms_empty_iff_empty[iff]: "atms_of C = {} \<longleftrightarrow> C = {#}"
  unfolding atms_of_def image_def Collect_empty_eq
  by (metis all_not_in_conv set_mset_eq_empty_iff)

lemma
  atms_of_poss[simp]: "atms_of (poss AA) = set_mset AA" and
  atms_of_negg[simp]: "atms_of (negs AA) = set_mset AA"
  unfolding atms_of_def image_def by auto

lemma less_eq_Max_atms_of: "C \<noteq> {#} \<Longrightarrow> C #\<subseteq># D \<Longrightarrow> Max (atms_of C) \<le> Max (atms_of D)"
  unfolding atms_of_def
  by (metis Max_atm_of_set_mset_commute le_multiset_empty_right leq_imp_less_eq_atm_of
    less_eq_Max_lit)

lemma le_multiset_Max_in_imp_Max:
  "Max (atms_of D) = A \<Longrightarrow> C #\<subseteq># D \<Longrightarrow> A \<in> atms_of C \<Longrightarrow> Max (atms_of C) = A"
  by (metis Max.coboundedI[OF finite_atms_of] atms_of_def empty_iff eq_iff image_subsetI
    less_eq_Max_atms_of set_mset_empty subset_Compl_self_eq)

lemma atm_of_Max_lit[simp]: "C \<noteq> {#} \<Longrightarrow> atm_of (Max (set_mset C)) = Max (atms_of C)"
  unfolding atms_of_def Max_atm_of_set_mset_commute ..

lemma Max_lit_eq_pos_or_neg_Max_atm:
  "C \<noteq> {#} \<Longrightarrow> Max (set_mset C) = Pos (Max (atms_of C)) \<or> Max (set_mset C) = Neg (Max (atms_of C))"
  by (metis Neg_atm_of_iff Pos_atm_of_iff atm_of_Max_lit)

lemma atms_less_imp_lit_less_pos: "(\<And>B. B \<in> atms_of C \<Longrightarrow> B < A) \<Longrightarrow> L \<in># C \<Longrightarrow> L < Pos A"
  unfolding atms_of_def less_literal_def by force

lemma atms_less_eq_imp_lit_less_eq_neg: "(\<And>B. B \<in> atms_of C \<Longrightarrow> B \<le> A) \<Longrightarrow> L \<in># C \<Longrightarrow> L \<le> Neg A"
  unfolding less_eq_literal_def by (simp add: atm_of_lit_in_atms_of)

end
