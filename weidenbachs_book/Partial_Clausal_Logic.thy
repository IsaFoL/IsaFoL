(*

    Title: Partial Clausal Logic
    Author: Mathias Fleury

Based on
    Title:       Clausal Logic
    Author:      Jasmin Blanchette <blanchette at in.tum.de>, 2014
    Author:      Dmitriy Traytel <traytel at in.tum.de>, 2014


*)

section {* Partial Clausal Logic *}

theory Partial_Clausal_Logic
imports Clausal_Logic
begin

text {*
Resolution operates of clauses, which are disjunctions of literals. The material formalized here
corresponds roughly to Sections 2.1 (``Formulas and Clauses'') and 2.2 (``Herbrand
Interpretations'') of Bachmair and Ganzinger, excluding the formula and term syntax.
*}

subsection {* Clauses *}

text {*
Clauses are (finite) multisets of literals.
*}

type_synonym 'a clause = "'a literal multiset"
type_synonym 'v clauses = "'v clause set"

subsection {* Partial Interpretations *}

type_synonym 'a interp = "'a literal set"

definition true_lit :: "'a interp \<Rightarrow> 'a literal \<Rightarrow> bool" (infix "\<Turnstile>l" 50) where
  "I \<Turnstile>l L \<longleftrightarrow> L \<in> I"

declare true_lit_def[simp]


subsubsection \<open>Consistency\<close>
definition consistent_interp :: "'a literal set \<Rightarrow> bool" where
"consistent_interp I = (\<forall>L. \<not>(L \<in> I \<and> - L \<in> I))"

lemma consistent_interp_empty[simp]:
  "consistent_interp {}" unfolding consistent_interp_def by auto

lemma consistent_interp_single[simp]:
  "consistent_interp {L}" unfolding consistent_interp_def by auto

lemma consistent_interp_subset:
  assumes "A \<subseteq> B"
  and "consistent_interp B"
  shows "consistent_interp A"
  using assms unfolding consistent_interp_def by auto

lemma consistent_interp_change_insert:
  "a \<notin> A \<Longrightarrow> -a \<notin> A \<Longrightarrow> consistent_interp (insert (-a) A) \<longleftrightarrow> consistent_interp (insert a A)"
  unfolding consistent_interp_def by fastforce

lemma consistent_interp_insert_pos  [simp]:
  "a \<notin> A \<Longrightarrow> consistent_interp (insert a A) \<longleftrightarrow> consistent_interp A \<and> a \<notin> A \<and> -a \<notin> A"
  unfolding consistent_interp_def by auto

lemma consistent_interp_insert_not_in:
  "consistent_interp A \<Longrightarrow> a \<notin> A \<Longrightarrow> -a \<notin> A \<Longrightarrow> consistent_interp (insert a A)"
  unfolding consistent_interp_def by auto

subsubsection \<open>Atoms\<close>
definition atms_of_m :: "'a literal multiset set \<Rightarrow> 'a set" where
"atms_of_m \<psi>s = \<Union>(atms_of ` \<psi>s)"

definition atms_of_s :: "'a literal set \<Rightarrow> 'a set" where
  "atms_of_s C = atm_of ` C"

lemma atms_of_m_emtpy_set[simp]:
  "atms_of_m {} = {}"
  unfolding atms_of_m_def by auto

lemma atms_of_m_memtpy[simp]:
  "atms_of_m {{#}} = {}"
  unfolding atms_of_m_def by auto

lemma atms_of_m_mono:
  "A \<subseteq> B \<Longrightarrow> atms_of_m A \<subseteq> atms_of_m B"
  unfolding atms_of_m_def by auto

lemma atms_of_m_finite[simp]:
  "finite \<psi>s \<Longrightarrow> finite (atms_of_m \<psi>s)"
  unfolding atms_of_m_def by auto

lemma atms_of_m_union[simp]:
  "atms_of_m (\<psi>s \<union> \<chi>s) = atms_of_m \<psi>s \<union> atms_of_m \<chi>s"
  unfolding atms_of_m_def by auto

lemma atms_of_m_insert[simp]:
  "atms_of_m (insert \<psi>s \<chi>s) = atms_of \<psi>s \<union> atms_of_m \<chi>s"
  unfolding atms_of_m_def by auto

lemma atms_of_m_plus[simp]:
  fixes C D :: "'a literal multiset"
  shows "atms_of_m {C + D} = atms_of_m {C} \<union> atms_of_m {D}"
  unfolding atms_of_m_def by auto

lemma atms_of_m_singleton[simp]: "atms_of_m {L} = atms_of L"
  unfolding atms_of_m_def by auto

(*TODO intro/simp/nothing?*)
lemma atms_of_atms_of_m_mono[intro]:
  "A \<in> \<psi> \<Longrightarrow> atms_of A \<subseteq> atms_of_m \<psi>"
  unfolding atms_of_m_def by fastforce

lemma in_m_in_literals:
  assumes "{#A#} + D \<in> \<psi>s"
  shows "atm_of A \<in> atms_of_m \<psi>s"
  using assms by (auto dest: atms_of_atms_of_m_mono)

lemma atms_of_s_union[simp]:
  "atms_of_s (Ia \<union> Ib) = atms_of_s Ia \<union> atms_of_s Ib"
  unfolding atms_of_s_def by auto

lemma atms_of_s_single[simp]:
  "atms_of_s {L} = {atm_of L}"
  unfolding atms_of_s_def by auto

lemma atms_of_s_insert[simp]:
  "atms_of_s (insert L Ib) = {atm_of L} \<union> atms_of_s Ib"
  unfolding atms_of_s_def by auto

lemma in_atms_of_s_decomp[iff]:
  "P \<in> atms_of_s I \<longleftrightarrow> (Pos P \<in> I \<or> Neg P \<in> I)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  thus ?Q unfolding atms_of_s_def by (metis image_iff literal.exhaust_sel)
next
  assume ?Q
  thus ?P unfolding atms_of_s_def by force
qed

lemma atm_of_in_atm_of_set_in_uminus:
  "atm_of L' \<in> atm_of ` B \<Longrightarrow> L' \<in> B \<or> - L' \<in> B"
  using atms_of_s_def by (cases L')  fastforce+

subsubsection \<open>Totality\<close>
definition total_over_set :: "'a interp \<Rightarrow> 'a set \<Rightarrow> bool" where
"total_over_set I S = (\<forall>l\<in>S. Pos l \<in> I \<or> Neg l \<in> I)"

definition total_over_m  :: "'a literal set \<Rightarrow> 'a clause set \<Rightarrow> bool" where
"total_over_m I \<psi>s = total_over_set I (atms_of_m \<psi>s)"

lemma total_over_set_empty[simp]:
  "total_over_set I {}"
  unfolding total_over_set_def by auto

lemma total_over_m_empty[simp]:
  "total_over_m I {}"
  unfolding total_over_m_def by auto

lemma total_over_set_single[iff]:
  "total_over_set I {L} \<longleftrightarrow> (Pos L \<in> I \<or> Neg L \<in> I)"
  unfolding total_over_set_def by auto

lemma total_over_set_insert[iff]:
  "total_over_set I (insert L Ls) \<longleftrightarrow> ((Pos L \<in> I \<or> Neg L \<in> I) \<and> total_over_set I Ls)"
  unfolding total_over_set_def by auto

lemma total_over_set_union[iff]:
  "total_over_set I (Ls \<union> Ls') \<longleftrightarrow> (total_over_set I Ls \<and> total_over_set I Ls')"
  unfolding total_over_set_def by auto

lemma total_over_m_subset:
  "A \<subseteq> B \<Longrightarrow> total_over_m I B \<Longrightarrow> total_over_m I A"
  using atms_of_m_mono[of A] unfolding total_over_m_def total_over_set_def by auto

lemma total_over_m_sum[iff]:
  shows "total_over_m I {C + D} \<longleftrightarrow> (total_over_m I {C} \<and> total_over_m I {D})"
  using assms unfolding total_over_m_def total_over_set_def by auto

lemma total_over_m_union[iff]:
  "total_over_m I (A \<union> B) \<longleftrightarrow> (total_over_m I A \<and> total_over_m I B)"
  unfolding total_over_m_def total_over_set_def by auto

lemma total_over_m_insert[iff]:
  "total_over_m I (insert a A) \<longleftrightarrow> (total_over_set I (atms_of a) \<and> total_over_m I A)"
  unfolding total_over_m_def total_over_set_def by fastforce

lemma atms_of_m_remove_incl:
  shows "atms_of_m (Set.remove a \<psi>) \<subseteq> atms_of_m \<psi>"
  unfolding atms_of_m_def by auto

lemma atms_of_m_remove_subset:
  "atms_of_m (\<phi> - \<psi>) \<subseteq> atms_of_m \<phi>"
  unfolding atms_of_m_def by auto

lemma total_over_m_extension:
  fixes I :: "'v literal set" and A :: "'v clauses"
  assumes total: "total_over_m I A"
  shows "\<exists>I'. total_over_m (I \<union> I') (A\<union>B) \<and> (\<forall>x\<in>I'. atm_of x \<in> atms_of_m B \<and> atm_of x \<notin> atms_of_m A)"
proof -
  let ?I' = "{Pos v |v. v\<in> atms_of_m B \<and> v \<notin> atms_of_m A}"
  have "(\<forall>x\<in>?I'. atm_of x \<in> atms_of_m B \<and> atm_of x \<notin> atms_of_m A)" by auto
  also have "total_over_m (I \<union> ?I') (A\<union>B)"
    using total unfolding total_over_m_def total_over_set_def by auto
  ultimately show ?thesis by blast
qed

lemma total_over_m_consistent_extension:
  fixes I :: "'v literal set" and A :: "'v clauses"
  assumes total: "total_over_m I A"
  and cons: "consistent_interp I"
  shows "\<exists>I'. total_over_m (I \<union> I') (A \<union> B) \<and> (\<forall>x\<in>I'. atm_of x \<in> atms_of_m B \<and> atm_of x \<notin> atms_of_m A) \<and> consistent_interp (I \<union> I')"
proof -
  let ?I' = "{Pos v |v. v\<in> atms_of_m B \<and> v \<notin> atms_of_m A \<and> Pos v \<notin> I \<and> Neg v \<notin> I}"
  have "(\<forall>x\<in>?I'. atm_of x \<in> atms_of_m B \<and> atm_of x \<notin> atms_of_m A)" by auto
  also have "total_over_m (I \<union> ?I') (A\<union>B)"
    using total unfolding total_over_m_def total_over_set_def by auto
  moreover have "consistent_interp (I \<union> ?I')"
    using cons unfolding consistent_interp_def by (intro allI) (case_tac L, auto)
  ultimately show ?thesis by blast
qed

lemma total_over_set_atms_of[simp]:
  "total_over_set Ia (atms_of_s Ia)"
  unfolding total_over_set_def atms_of_s_def by (metis image_iff literal.exhaust_sel)


lemma total_over_set_literal_defined:
  assumes "{#A#} + D \<in> \<psi>s"
  and "total_over_set I (atms_of_m \<psi>s)"
  shows "A \<in> I \<or> -A \<in> I"
  using assms unfolding total_over_set_def by (metis (no_types) Neg_atm_of_iff in_m_in_literals literal.collapse(1) uminus_Neg uminus_Pos)

lemma tot_over_m_remove:
  assumes "total_over_m (I \<union> {L}) {\<psi>}"
  and L: "\<not> L \<in># \<psi>""-L \<notin># \<psi>"
  shows "total_over_m I {\<psi>}"
  unfolding total_over_m_def total_over_set_def
proof
  fix l
  assume l: "l \<in> atms_of_m {\<psi>}"
  hence "Pos l \<in> I \<or> Neg l \<in> I \<or> l = atm_of L"
     using assms unfolding total_over_m_def total_over_set_def by auto
  also have "atm_of L \<notin> atms_of_m {\<psi>}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "atm_of L \<in> atms_of \<psi>" by auto
      hence "Pos (atm_of L) \<in># \<psi> \<or> Neg (atm_of L) \<in># \<psi>"
        using atm_imp_pos_or_neg_lit by metis
      hence "L \<in># \<psi> \<or> - L \<in># \<psi>" by (case_tac L) auto
      thus False using L by auto
    qed
  ultimately show  "Pos l \<in> I \<or> Neg l \<in> I" using l by metis
qed

lemma total_union:
  assumes "total_over_m I \<psi>"
  shows "total_over_m (I \<union> I') \<psi>"
  using assms unfolding total_over_m_def total_over_set_def by auto

lemma total_union_2:
  assumes "total_over_m I \<psi>"
  and "total_over_m I' \<psi>'"
  shows "total_over_m (I \<union> I') (\<psi> \<union> \<psi>')"
  using assms unfolding total_over_m_def total_over_set_def by auto

subsubsection \<open>Interpretations\<close>
definition true_cls :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "I \<Turnstile> C \<longleftrightarrow> (\<exists>L. L \<in># C \<and> I \<Turnstile>l L)"

lemma true_cls_empty[iff]: "\<not> I \<Turnstile> {#}"
  unfolding true_cls_def by simp

lemma true_cls_singleton[iff]: "I \<Turnstile> {#L#} \<longleftrightarrow> I \<Turnstile>l L"
  unfolding true_cls_def by simp

lemma true_cls_union[iff]: "I \<Turnstile> C + D \<longleftrightarrow> I \<Turnstile> C \<or> I \<Turnstile> D"
  unfolding true_cls_def by auto

lemma true_cls_mono: "set_mset C \<subseteq> set_mset D \<Longrightarrow> I \<Turnstile> C \<Longrightarrow> I \<Turnstile> D"
  unfolding true_cls_def subset_eq by (metis mem_set_mset_iff)

lemma
  assumes "I \<Turnstile> \<psi>"
  shows true_cls_union_increase[simp]: "I \<union> I' \<Turnstile> \<psi>"
  and true_cls_union_increase'[simp]: "I' \<union> I \<Turnstile> \<psi>"
  using assms unfolding true_cls_def by auto

lemma true_cls_mono_l:
  assumes "A \<Turnstile> \<psi>"
  and "A \<subseteq> B"
  shows "B \<Turnstile> \<psi>"
  using assms unfolding true_cls_def by auto

lemma true_cls_replicate_mset[iff]: "I \<Turnstile> replicate_mset n L \<longleftrightarrow> n \<noteq> 0 \<and> I \<Turnstile>l L"
  by (induct n) auto

lemma true_cls_empty_entails[iff]: "\<not> {} \<Turnstile> N"
  by (auto simp add: true_cls_def)

lemma true_cls_not_in_remove:
  assumes "L \<notin># \<chi>"
  and " I \<union> {L} \<Turnstile> \<chi>"
  shows "I \<Turnstile> \<chi>"
  using assms unfolding true_cls_def by auto

definition true_clss :: "'a interp \<Rightarrow> 'a clauses \<Rightarrow> bool" (infix "\<Turnstile>s" 50) where
  "I \<Turnstile>s CC \<longleftrightarrow> (\<forall>C \<in> CC. I \<Turnstile> C)"

lemma true_clss_empty[simp]: "I \<Turnstile>s {}"
  unfolding true_clss_def by blast

lemma true_clss_singleton[iff]: "I \<Turnstile>s {C} \<longleftrightarrow> I \<Turnstile> C"
  unfolding true_clss_def by blast

lemma true_clss_empty_entails_empty[iff]: "{} \<Turnstile>s N \<longleftrightarrow> N = {}"
  unfolding true_clss_def by (auto simp add: true_cls_def)
lemma true_cls_insert_l [simp]:
  "M \<Turnstile> A \<Longrightarrow> insert L M \<Turnstile> A"
  unfolding true_cls_def by auto

lemma true_clss_union[iff]: "I \<Turnstile>s CC \<union> DD \<longleftrightarrow> I \<Turnstile>s CC \<and> I \<Turnstile>s DD"
  unfolding true_clss_def by blast

lemma true_clss_insert[iff]: "I \<Turnstile>s insert C DD \<longleftrightarrow> I \<Turnstile> C \<and> I \<Turnstile>s DD"
  unfolding true_clss_def by blast

lemma true_clss_mono: "DD \<subseteq> CC \<Longrightarrow> I \<Turnstile>s CC \<Longrightarrow> I \<Turnstile>s DD"
  unfolding true_clss_def by blast

lemma true_clss_union_increase[simp]:
 assumes "I \<Turnstile>s \<psi>"
 shows "I \<union> I' \<Turnstile>s \<psi>"
 using assms unfolding true_clss_def by auto

lemma true_clss_union_increase'[simp]:
 assumes "I' \<Turnstile>s \<psi>"
 shows "I \<union> I' \<Turnstile>s \<psi>"
 using assms by (auto simp add: true_clss_def)

lemma true_clss_commute_l:
  "(I \<union> I' \<Turnstile>s \<psi>) \<longleftrightarrow> (I' \<union> I \<Turnstile>s \<psi>)"
  by (simp add: Un_commute)

lemma model_remove[simp]: "I \<Turnstile>s N \<Longrightarrow> I \<Turnstile>s Set.remove a N"
  by (simp add: true_clss_def)

lemma model_remove_minus[simp]: "I \<Turnstile>s N \<Longrightarrow> I \<Turnstile>s N - A"
  by (simp add: true_clss_def)

lemma notin_vars_union_true_cls_true_cls:
  assumes "\<forall>x\<in>I'. atm_of x \<notin> atms_of_m A"
  and "atms_of L \<subseteq> atms_of_m A"
  and "I \<union> I' \<Turnstile> L"
  shows "I \<Turnstile> L"
  using assms unfolding true_cls_def true_lit_def by (metis Un_iff atm_of_lit_in_atms_of contra_subsetD)

lemma notin_vars_union_true_clss_true_clss:
  assumes "\<forall>x\<in>I'. atm_of x \<notin> atms_of_m A"
  and "atms_of_m L \<subseteq> atms_of_m A"
  and "I \<union> I' \<Turnstile>s L"
  shows "I \<Turnstile>s L"
  using assms unfolding true_clss_def true_lit_def Ball_def by (meson atms_of_atms_of_m_mono notin_vars_union_true_cls_true_cls subset_trans)

subsubsection \<open>Satisfiability\<close>
definition satisfiable :: "'a clause set \<Rightarrow> bool" where
  "satisfiable CC \<equiv> \<exists>I. (I \<Turnstile>s CC \<and> consistent_interp I \<and> total_over_m I CC)"

lemma satisfiable_single[simp]:
  "satisfiable {{#L#}}"
  unfolding satisfiable_def by fastforce

abbreviation unsatisfiable :: "'a clause set \<Rightarrow> bool" where
  "unsatisfiable CC \<equiv> \<not> satisfiable CC"

subsubsection \<open>Multiset of clauses\<close>
definition true_cls_mset :: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<Turnstile>m" 50) where
  "I \<Turnstile>m CC \<longleftrightarrow> (\<forall>C \<in># CC. I \<Turnstile> C)"

lemma true_cls_mset_empty[simp]: "I \<Turnstile>m {#}"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_singleton[iff]: "I \<Turnstile>m {#C#} \<longleftrightarrow> I \<Turnstile> C"
  unfolding true_cls_mset_def by (auto split: split_if_asm)

lemma true_cls_mset_union[iff]: "I \<Turnstile>m CC + DD \<longleftrightarrow> I \<Turnstile>m CC \<and> I \<Turnstile>m DD"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_image_mset[iff]: "I \<Turnstile>m image_mset f A \<longleftrightarrow> (\<forall>x \<in># A. I \<Turnstile> f x)"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_mono: "set_mset DD \<subseteq> set_mset CC \<Longrightarrow> I \<Turnstile>m CC \<Longrightarrow> I \<Turnstile>m DD"
  unfolding true_cls_mset_def subset_iff by auto

lemma true_clss_set_mset[iff]: "I \<Turnstile>s set_mset CC \<longleftrightarrow> I \<Turnstile>m CC"
  unfolding true_clss_def true_cls_mset_def by auto

theorem true_cls_remove_unused:
  assumes "I \<Turnstile> \<psi>"
  shows "{v \<in> I. atm_of v \<in> atms_of \<psi>} \<Turnstile> \<psi>"
  using assms unfolding true_cls_def atms_of_def by auto

text \<open>A simple application of the previous theorem:\<close>
lemma true_clss_union_decrease:
  assumes II': "I \<union> I' \<Turnstile> \<psi>"
  and H: "\<forall>v \<in> I'. atm_of v \<notin> atms_of \<psi>"
  shows "I \<Turnstile> \<psi>"
proof -
  let ?I = "{v \<in> I \<union> I'. atm_of v \<in> atms_of \<psi>}"
  have "?I \<Turnstile> \<psi>" using true_cls_remove_unused II' by blast
  also have "?I \<subseteq> I" using H by auto
  ultimately show ?thesis using true_cls_mono_l by blast
qed

lemma multiset_not_empty:
  assumes "M \<noteq> {#}"
  and "x \<in># M"
  shows "\<exists>A. x = Pos A \<or> x = Neg A"
  using assms literal.exhaust_sel by blast

lemma atms_of_m_empty:
  fixes \<psi> :: "'v clauses"
  assumes "atms_of_m \<psi> = {}"
  shows "\<psi> = {} \<or> \<psi> = {{#}}"
  using assms by (auto simp add: atms_of_m_def)

lemma consistent_interp_disjoint:
 assumes consI: "consistent_interp I"
 and disj: "atms_of_s A \<inter> atms_of_s I = {}"
 and consA: "consistent_interp A"
 shows "consistent_interp (A \<union> I)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  also have "\<And>L. \<not> (L \<in> A \<and> -L \<in> I)"
    using disj unfolding atms_of_s_def by (auto simp add: rev_image_eqI)
  ultimately show False
    using consA consI unfolding consistent_interp_def by (metis (full_types) Un_iff literal.exhaust_sel uminus_Neg uminus_Pos)
qed

lemma total_remove_unused:
  assumes "total_over_m I \<psi>"
  shows "total_over_m {v \<in> I. atm_of v \<in> atms_of_m \<psi>} \<psi>"
  by (metis (no_types, lifting) assms literal.sel(1) literal.sel(2) mem_Collect_eq  total_over_m_def total_over_set_def)

lemma true_cls_remove_hd_if_notin_vars:
  assumes "insert a M'\<Turnstile> D"
  and "atm_of a \<notin> atms_of D"
  shows "M' \<Turnstile> D"
  using assms unfolding true_cls_def by (auto simp add: atm_of_lit_in_atms_of)

lemma total_over_set_atm_of:
  fixes I :: "'v interp" and K :: "'v set"
  shows "total_over_set I K  \<longleftrightarrow> (\<forall>l \<in> K. l \<in> (atm_of ` I))"
  unfolding total_over_set_def by (metis atms_of_s_def in_atms_of_s_decomp)

subsubsection \<open>Tautologies\<close>
definition "tautology (\<psi>:: 'v clause) \<equiv> \<forall>I. total_over_set I (atms_of \<psi>) \<longrightarrow> I \<Turnstile> \<psi>"

lemma tautology_Pos_Neg[intro]:
  assumes "Pos p \<in># A" and "Neg p \<in># A"
  shows "tautology A"
  using assms unfolding tautology_def total_over_set_def true_cls_def
  by (meson atm_iff_pos_or_neg_lit true_lit_def)

lemma tautology_minus[simp]:
  assumes "L \<in># A" and "-L \<in># A"
  shows  "tautology A"
  by (metis assms literal.exhaust tautology_Pos_Neg uminus_Neg uminus_Pos)

lemma tautology_exists_Pos_Neg:
  assumes "tautology \<psi>"
  shows "\<exists>p. Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>"
proof (rule ccontr)
  assume p: "\<not> (\<exists>p. Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>)"
  let ?I = "{-L | L. L \<in># \<psi>}"
  have "total_over_set ?I (atms_of \<psi>)"
    unfolding total_over_set_def using atm_imp_pos_or_neg_lit by force
  also have "\<not> ?I \<Turnstile> \<psi>"
    unfolding true_cls_def true_lit_def apply clarify
    using p by (case_tac La) fastforce+
  ultimately show False using assms unfolding tautology_def by auto
qed

lemma tautology_decomp:
  "tautology \<psi> \<longleftrightarrow> (\<exists>p. Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>)"
  using tautology_exists_Pos_Neg by auto

lemma tautology_false[simp]: "\<not>tautology {#}"
  unfolding tautology_def by auto

lemma minus_interp_tautology:
  assumes "{-L | L. L\<in># \<chi>} \<Turnstile> \<chi>"
  shows "tautology \<chi>"
proof -
  obtain L where "L \<in># \<chi> \<and> -L \<in># \<chi>"
    using assms unfolding true_cls_def by auto
  thus ?thesis using tautology_decomp literal.exhaust uminus_Neg uminus_Pos by metis
qed

lemma remove_literal_in_model_tautology:
  assumes "I \<union> {Pos P} \<Turnstile> \<phi>"
  and "I \<union> {Neg P} \<Turnstile> \<phi>"
  shows "I \<Turnstile> \<phi> \<or> tautology \<phi>"
  using assms unfolding true_cls_def by auto

lemma satisfiable_decreasing:
  assumes "satisfiable (\<psi> \<union> \<psi>')"
  shows "satisfiable \<psi>"
  using assms total_over_m_union unfolding satisfiable_def by blast

lemma tautology_imp_tautology:
  fixes \<chi> \<chi>' :: "'v clause"
  assumes "\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> \<chi>'" and "tautology \<chi>"
  shows "tautology \<chi>'" unfolding tautology_def
proof (intro allI HOL.impI)
  fix I ::"'v literal set"
  assume totI: "total_over_set I (atms_of \<chi>')"
  let ?I' = "{Pos v |v. v\<in> atms_of \<chi> \<and> v \<notin> atms_of_s I}"
  have totI': "total_over_m (I \<union> ?I') {\<chi>}" unfolding total_over_m_def total_over_set_def by auto
  hence \<chi>: "I \<union> ?I' \<Turnstile> \<chi>" using assms(2) unfolding total_over_m_def tautology_def by simp
  hence "I \<union> (?I'- I) \<Turnstile> \<chi>'" using assms(1) totI' by auto
  also have "\<And>L. L \<in># \<chi>' \<Longrightarrow> L \<notin> ?I'"
    proof -
      fix L :: "'v literal"
      assume a1: "L \<in># \<chi>'"
      have "\<forall>v. v \<notin> atms_of \<chi>' \<or> Pos v \<in> I \<or> Neg v \<in> I"
        by (meson totI total_over_set_def)
      thus "L \<notin> ?I'"
        using a1 pos_lit_in_atms_of by force
    qed
  ultimately show "I \<Turnstile> \<chi>'" unfolding true_cls_def by auto
qed

subsubsection \<open>Clause and propositions\<close>
definition true_cls_cls :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>f" 49) where
"\<psi> \<Turnstile>f \<chi> \<longleftrightarrow> (\<forall>I. total_over_m I ({\<psi>} \<union> {\<chi>}) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile> \<psi> \<longrightarrow> I \<Turnstile> \<chi>)"

definition true_cls_clss :: "'a clause \<Rightarrow> 'a clauses \<Rightarrow> bool" (infix "\<Turnstile>fs" 49) where
"\<psi> \<Turnstile>fs \<chi> \<longleftrightarrow> (\<forall>I. total_over_m I ({\<psi>} \<union> \<chi>) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile> \<psi> \<longrightarrow> I \<Turnstile>s \<chi>)"

definition true_clss_cls :: "'a clauses \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>p" 49) where
"N \<Turnstile>p \<chi> \<longleftrightarrow> (\<forall>I. total_over_m I (N \<union> {\<chi>}) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile> \<chi>)"

definition true_clss_clss :: "'a clauses \<Rightarrow> 'a clauses \<Rightarrow> bool" (infix "\<Turnstile>ps" 49) where
"N \<Turnstile>ps N' \<longleftrightarrow> (\<forall>I. total_over_m I (N \<union> N') \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile>s N')"

lemma true_cls_cls_refl[simp]:
  "A \<Turnstile>f A"
  unfolding true_cls_cls_def by auto

lemma true_cls_cls_insert_l[simp]:
  "a \<Turnstile>f C \<Longrightarrow> insert a A \<Turnstile>p C"
  unfolding true_cls_cls_def true_clss_cls_def true_clss_def using total_over_m_union by fastforce

lemma true_cls_clss_empty[iff]:
  "N \<Turnstile>fs {}"
  unfolding true_cls_clss_def by auto

lemma true_prop_true_clause[iff]:
  "{\<phi>} \<Turnstile>p \<psi> \<longleftrightarrow> \<phi> \<Turnstile>f \<psi>"
  unfolding true_cls_cls_def true_clss_cls_def by auto

lemma true_clss_clss_true_clss_cls[iff]:
  "N \<Turnstile>ps {\<psi>} \<longleftrightarrow> N \<Turnstile>p \<psi>"
  unfolding true_clss_clss_def true_clss_cls_def by auto

lemma true_clss_clss_true_cls_clss[iff]:
  "{\<chi>} \<Turnstile>ps \<psi> \<longleftrightarrow> \<chi> \<Turnstile>fs \<psi>"
  unfolding true_clss_clss_def true_cls_clss_def by auto

lemma true_clss_clss_empty[simp]:
  "N \<Turnstile>ps {}"
  unfolding true_clss_clss_def by auto

lemma true_clss_cls_subset:
  "A \<subseteq> B \<Longrightarrow> A \<Turnstile>p CC \<Longrightarrow> B \<Turnstile>p CC"
  unfolding true_clss_cls_def total_over_m_union by (simp add: total_over_m_subset true_clss_mono)

lemma true_clss_cs_mono_l[simp]:
  "A \<Turnstile>p CC \<Longrightarrow> A \<union> B  \<Turnstile>p CC"
  by (auto intro: true_clss_cls_subset)

lemma true_clss_cs_mono_l2[simp]:
  "B \<Turnstile>p CC \<Longrightarrow> A \<union> B  \<Turnstile>p CC"
  by (auto intro: true_clss_cls_subset)

lemma true_clss_cls_mono_r[simp]:
  "A \<Turnstile>p CC \<Longrightarrow> A \<Turnstile>p CC + CC'"
  unfolding true_clss_cls_def total_over_m_union total_over_m_sum by blast

lemma true_clss_cls_mono_r'[simp]:
  "A \<Turnstile>p CC' \<Longrightarrow> A \<Turnstile>p CC + CC'"
  unfolding true_clss_cls_def total_over_m_union total_over_m_sum by blast

lemma true_clss_clss_union_l[simp]:
  "A \<Turnstile>ps CC \<Longrightarrow> A \<union> B  \<Turnstile>ps CC"
  unfolding true_clss_clss_def total_over_m_union by fastforce

lemma true_clss_clss_union_l_r[simp]:
  "B \<Turnstile>ps CC \<Longrightarrow> A \<union> B \<Turnstile>ps CC"
  unfolding true_clss_clss_def total_over_m_union by fastforce

lemma true_clss_cls_in[simp]:
  "CC \<in> A \<Longrightarrow> A \<Turnstile>p CC"
  unfolding true_clss_cls_def true_clss_def total_over_m_union by fastforce

lemma true_clss_cls_insert_l[simp]:
  "A \<Turnstile>p C \<Longrightarrow> insert a A \<Turnstile>p C"
  unfolding true_clss_cls_def true_clss_def using total_over_m_union by (metis Un_iff insert_is_Un sup.commute)

lemma true_clss_clss_insert_l[simp]:
  "A \<Turnstile>ps C \<Longrightarrow> insert a A \<Turnstile>ps C"
  unfolding true_clss_cls_def true_clss_clss_def true_clss_def by blast

lemma true_clss_clss_union_and[iff]:
  "A \<Turnstile>ps C \<union> D \<longleftrightarrow> (A \<Turnstile>ps C \<and> A \<Turnstile>ps D)"
proof
  {
    fix A C D :: "'a clauses"
    assume A: "A \<Turnstile>ps C \<union> D"
    have "A \<Turnstile>ps C"
        unfolding true_clss_clss_def true_clss_cls_def insert_def total_over_m_insert
      proof (clarify)
        fix I
        assume tot: "total_over_m I A" and tot': "total_over_m I  C"
        and cons: "consistent_interp I"
        and I: "I \<Turnstile>s A"
        obtain I' where tot': "total_over_m (I \<union> I') (A \<union> C \<union> D)"
        and cons': "consistent_interp (I \<union> I')"
        and H: "\<forall>x\<in>I'. atm_of x \<in> atms_of_m D \<and> atm_of x \<notin> atms_of_m (A \<union> C)"
          using total_over_m_consistent_extension[OF _ cons, of "A \<union> C"] tot tot' by auto
        also have "I \<union> I' \<Turnstile>s A" using I by simp
        ultimately have "I \<union> I' \<Turnstile>s C \<union> D" using A unfolding true_clss_clss_def true_clss_cls_def insert_def by auto
        hence "I \<union> I' \<Turnstile>s C \<union> D" unfolding Ball_def true_cls_def true_clss_def by auto
        thus "I \<Turnstile>s C" using notin_vars_union_true_clss_true_clss[of I'] H unfolding atms_of_m_union by auto
      qed
   } note H = this
  assume "A \<Turnstile>ps C \<union> D"
  thus "A \<Turnstile>ps C \<and> A \<Turnstile>ps D" using H[of A] Un_commute[of C D] by metis
next
  assume "A \<Turnstile>ps C \<and> A \<Turnstile>ps D"
  thus "A \<Turnstile>ps C \<union> D"
    unfolding true_clss_clss_def by auto
qed


lemma true_clss_clss_insert[iff]:
  "A \<Turnstile>ps insert L Ls \<longleftrightarrow> (A \<Turnstile>p L \<and> A \<Turnstile>ps Ls)"
  using true_clss_clss_union_and[of A "{L}" "Ls"] by auto

lemma true_clss_clss_subset:
  "A \<subseteq> B \<Longrightarrow> A \<Turnstile>ps CC \<Longrightarrow> B \<Turnstile>ps CC"
  by (metis subset_Un_eq true_clss_clss_union_l)

lemma true_clss_clss_in_imp_true_clss_cls:
  assumes "N \<Turnstile>ps U"
  and "A \<in> U"
  shows "N \<Turnstile>p A"
  using assms mk_disjoint_insert by fastforce

lemma all_in_true_clss_clss: "\<forall>x \<in> B. x \<in> A \<Longrightarrow> A \<Turnstile>ps B"
  unfolding true_clss_clss_def true_clss_def by auto

lemma true_clss_clss_left_right:
  assumes "A \<Turnstile>ps B"
  and "A \<union> B \<Turnstile>ps M"
  shows "A \<Turnstile>ps M \<union> B"
  using assms unfolding true_clss_clss_def by auto

lemma true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or:
  assumes D: "N \<Turnstile>p D + {#- L#}"
  and C: "N \<Turnstile>p C + {#L#}"
  shows "N \<Turnstile>p D + C"
  unfolding true_clss_cls_def
proof (intro allI impI)
  fix I
  assume tot: "total_over_m I (N \<union> {D + C})"
  and "consistent_interp I"
  and "I \<Turnstile>s N"
  {
    assume L: "L \<in> I \<or> -L \<in> I"
    hence "total_over_m I {D + {#- L#}}"
      using tot by (cases L) auto
    hence "I \<Turnstile> D + {#- L#}" using D `I \<Turnstile>s N` tot `consistent_interp I`
      unfolding true_clss_cls_def by auto
    also
      have "total_over_m I {C + {#L#}}"
        using L tot by (cases L) auto
      hence "I \<Turnstile> C + {#L#}"
        using C `I \<Turnstile>s N` tot `consistent_interp I` unfolding true_clss_cls_def by auto
    ultimately have "I \<Turnstile> D + C" using `consistent_interp I` consistent_interp_def by fastforce
  }
  also {
    assume L: "L \<notin> I \<and> -L \<notin> I"
    let ?I' = "I \<union> {L}"
    have "consistent_interp ?I'" using L `consistent_interp I` by auto
    also have "total_over_m ?I' {D + {#- L#}}" using tot unfolding total_over_m_def total_over_set_def by (auto simp add: atms_of_def)
    moreover have "total_over_m ?I' N" using tot using total_union by blast
    moreover have "?I' \<Turnstile>s N" using `I \<Turnstile>s N` using true_clss_union_increase by blast
    ultimately have "?I' \<Turnstile> D + {#- L#}"
      using D unfolding true_clss_cls_def by blast
    hence "?I' \<Turnstile> D" using L by auto
    also
      have "total_over_set I (atms_of (D + C))" using tot by auto
      hence "L \<notin># D \<and> -L \<notin># D"
        using L unfolding total_over_set_def atms_of_def by (cases L) force+
    ultimately have "I \<Turnstile> D + C" unfolding true_cls_def by auto
  }
  ultimately show "I \<Turnstile> D + C" by blast
qed

lemma satisfiable_carac[iff]:
  "(\<exists>I. consistent_interp I \<and> I \<Turnstile>s \<phi>) \<longleftrightarrow> satisfiable \<phi>" (is "(\<exists>I. ?Q I) \<longleftrightarrow> ?S")
proof
  assume "?S"
  thus "\<exists>I. ?Q I" unfolding satisfiable_def by auto
next
  assume "\<exists>I. ?Q I"
  then obtain I where cons: "consistent_interp I" and I: "I \<Turnstile>s \<phi>" by metis
  let ?I' = "{Pos v |v. v \<notin> atms_of_s I \<and> v \<in> atms_of_m \<phi>}"
  have "consistent_interp (I \<union> ?I')"
    using cons unfolding consistent_interp_def by (intro allI) (case_tac L, auto)
  also have "total_over_m (I \<union> ?I') \<phi>"
    unfolding total_over_m_def total_over_set_def by auto
  moreover have "I \<union> ?I' \<Turnstile>s \<phi>"
    using I unfolding Ball_def true_clss_def true_cls_def by auto
  ultimately show ?S unfolding satisfiable_def by blast
qed

lemma satisfiable_carac'[simp]: "(consistent_interp I \<and> I \<Turnstile>s \<phi>) \<longrightarrow> satisfiable \<phi>"
  using satisfiable_carac by metis


subsection \<open>Subsumptions\<close>
lemma subsumption_total_over_m:
  assumes "A \<subseteq># B"
  shows "total_over_m I {B} \<Longrightarrow> total_over_m I {A}"
  using assms atms_of_m_plus unfolding subset_mset_def total_over_m_def total_over_set_def by (auto simp add: mset_le_exists_conv)

lemma subsumption_imp_eval:
  assumes "A \<subseteq># B"
  shows "I \<Turnstile> A \<Longrightarrow> I \<Turnstile> B"
  using assms by (metis mset_le_exists_conv true_cls_union)

lemma atm_of_eq_atm_of:
  "atm_of L = atm_of L' \<longleftrightarrow> (L = L' \<or> L = -L')"
  by (metis atm_of_uminus literal.exhaust_sel uminus_Neg uminus_Pos)

lemma atms_of_replicate_mset_replicate_mset_uminus[simp]:
  "atms_of (D - replicate_mset (count D L) L  - replicate_mset (count D (-L)) (-L)) = atms_of D - {atm_of L}"
  by (auto split: split_if_asm simp add: atm_of_eq_atm_of atms_of_def)

lemma subsumption_chained:
  assumes "\<forall>I. total_over_m I {D} \<longrightarrow> I \<Turnstile> D \<longrightarrow> I \<Turnstile> \<phi>"
  and "C \<subseteq># D"
  shows "(\<forall>I. total_over_m I {C} \<longrightarrow> I \<Turnstile> C \<longrightarrow> I \<Turnstile> \<phi>) \<or> tautology \<phi>"
  using assms
proof (induct "card {Pos v | v. v \<in> atms_of D \<and> v \<notin> atms_of C}" arbitrary: D rule: nat_less_induct)
  case (1 D) note IH = this(1) and H = this(2) and incl = this(3)
  {
    assume "card {Pos v |v. v \<in> atms_of D \<and> v \<notin> atms_of C} = 0"
    hence "atms_of D \<subseteq> atms_of C" by auto
    hence "\<forall>I. total_over_m I {C} \<longrightarrow> total_over_m I {D}" unfolding total_over_m_def total_over_set_def by auto
    also have "\<forall>I. I \<Turnstile> C \<longrightarrow> I \<Turnstile> D" using incl subsumption_imp_eval by blast
    ultimately have ?case using H by auto

  }
  also {
    assume card: "card {Pos v |v. v \<in> atms_of D \<and> v \<notin> atms_of C} > 0"
    let ?atms = "{Pos v |v. v \<in> atms_of D \<and> v \<notin> atms_of C}"
    have "finite ?atms" by auto
    then obtain L where  L: "L \<in> ?atms"
      by (induct ?atms rule: finite.induct, metis card card_gt_0_iff, auto)
    let ?D' = "D - replicate_mset (count D L) L - replicate_mset (count D (-L)) (-L)"
    have atms_of_D: "atms_of_m {D} \<subseteq> atms_of_m {?D'} \<union> {atm_of L}" by auto

    {
      fix I
      assume "total_over_m I {?D'}"
      hence tot: "total_over_m (I \<union> {L}) {D}" unfolding total_over_m_def total_over_set_def using atms_of_D by auto

      assume IDL: "I \<Turnstile> ?D'"
      hence "I \<union> {L} \<Turnstile> D" unfolding true_cls_def by force
      hence "I \<union> {L} \<Turnstile> \<phi>" using H tot by auto

      also
        have tot': "total_over_m (I \<union> {-L}) {D}" using tot unfolding total_over_m_def total_over_set_def by auto
        have "I \<union> {-L} \<Turnstile> D" using IDL unfolding true_cls_def by force
        hence "I \<union> {-L} \<Turnstile> \<phi>" using H tot' by auto
      ultimately have "I \<Turnstile> \<phi> \<or> tautology \<phi>"
        using L remove_literal_in_model_tautology by force
    } note H' = this

    have "L \<notin># C \<and> -L \<notin># C" using L atm_iff_pos_or_neg_lit by force
    then have C_in_D': "C \<subseteq># ?D'" using `C \<subseteq># D` by (auto simp add: subseteq_mset_def)
    have "card {Pos v |v. v \<in> atms_of ?D' \<and> v \<notin> atms_of C} < card {Pos v |v. v \<in> atms_of D \<and> v \<notin> atms_of C}"
      using L by (auto intro!: psubset_card_mono)
    hence "(\<forall>I. total_over_m I {C} \<longrightarrow> I \<Turnstile> C \<longrightarrow> I \<Turnstile> \<phi>) \<or> tautology \<phi>"
      using IH C_in_D' H' by blast
  }
  ultimately show ?case by blast
qed

(*TODO Move it to multiset_more/multiset_more_more or something like that*)
subsection \<open>No duplicates\<close>
definition remdups_mset :: "'v multiset \<Rightarrow> 'v multiset" where
"remdups_mset S = mset_set (set_mset S)"

lemma remdups_mset_in[iff]: "a \<in># remdups_mset A \<longleftrightarrow> a \<in># A"
  unfolding remdups_mset_def by auto

lemma count_remdups_mset_eq_1: "a \<in># remdups_mset A \<longleftrightarrow> count (remdups_mset A) a = 1"
  unfolding remdups_mset_def by fastforce

lemma remdups_mset_empty[simp]:
  "remdups_mset {#} = {#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_singleton[simp]:
  "remdups_mset {#a#} = {#a#}"
  unfolding remdups_mset_def by auto

lemma set_mset_remdups[simp]: "set_mset (remdups_mset (D + C)) = set_mset (D + C) " by auto

lemma remdups_mset_eq_empty[iff]:
  "remdups_mset D = {#} \<longleftrightarrow> D = {#}"
  unfolding remdups_mset_def by blast

lemma remdups_mset_singleton_sum[simp]:
  "remdups_mset ({#a#} + A) = (if a \<in># A then remdups_mset A else {#a#} + remdups_mset A)"
  unfolding remdups_mset_def by (simp add: insert_absorb)

(*TODO problem in the if the order changes like here, but otherwise the rule seem to be a good idea*)
lemma "remdups_mset {#1::nat, 1, 2, 3, 1#} = {#1, 2, 3#}"
  by (auto simp add: multiset_eq_iff)

definition "distinct_mset S \<longleftrightarrow> (\<forall>a. a \<in># S \<longrightarrow> count S a = 1)"

lemma distinct_mset_empty[simp]: "distinct_mset {#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_singleton[simp]: "distinct_mset {#a#}"
  unfolding distinct_mset_def by auto

definition "distinct_mset_set \<Sigma> \<longleftrightarrow> (\<forall>S \<in>\<Sigma>. distinct_mset S)"
lemma distinct_mset_set_empty[simp]:
  "distinct_mset_set {}"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_singleton[iff]:
  "distinct_mset_set {A} \<longleftrightarrow> distinct_mset A"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_insert[iff]:
  "distinct_mset_set (insert S \<Sigma>) \<longleftrightarrow> (distinct_mset S \<and> distinct_mset_set \<Sigma>)"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_union[iff]:
  "distinct_mset_set (\<Sigma> \<union> \<Sigma>') \<longleftrightarrow> (distinct_mset_set \<Sigma> \<and> distinct_mset_set \<Sigma>')"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_union:
  "distinct_mset (A + B) \<Longrightarrow> distinct_mset A"
  by (simp add: add_is_1 distinct_mset_def)

lemma distinct_mset_minus[simp]:
  "distinct_mset A \<Longrightarrow> distinct_mset (A - B)"
  by (metis Multiset.diff_le_self mset_le_exists_conv distinct_mset_union)

lemma in_distinct_mset_set_distinct_mset:
  "a \<in> \<Sigma> \<Longrightarrow> distinct_mset_set \<Sigma> \<Longrightarrow> distinct_mset a"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_remdups_mset[simp]: "distinct_mset (remdups_mset S)"
  using count_remdups_mset_eq_1 unfolding distinct_mset_def by metis

text \<open>Another characterisation of @{term distinct_mset}\<close>
lemma distinct_mset_count_less_1:
  "distinct_mset S \<longleftrightarrow> (\<forall>a. count S a \<le> 1)"
  unfolding distinct_mset_def by (metis le_neq_implies_less less_one less_or_eq_imp_le not_gr0)

lemma atms_of_remdups_mset[simp]: "atms_of (remdups_mset C) = atms_of C"
  unfolding atms_of_def by auto

lemma true_cls_remdups_mset[iff]: "I \<Turnstile> remdups_mset C \<longleftrightarrow> I \<Turnstile> C"
  unfolding true_cls_def by auto

lemma [iff]: "A \<Turnstile>p remdups_mset C \<longleftrightarrow> A \<Turnstile>p C"
  unfolding true_clss_cls_def total_over_m_def by auto

subsection \<open>Build all simple clauses\<close>

function build_all_simple_clss :: "'v :: linorder set \<Rightarrow> 'v clause set" where
"build_all_simple_clss vars =
  (if \<not>finite vars \<or> vars= {}
  then {{#}}
  else
    let cls' = build_all_simple_clss (vars - {Min vars}) in
    {{#Pos (Min vars)#} + \<chi> |\<chi> . \<chi> \<in> cls'} \<union>
    {{#Neg (Min vars)#} + \<chi> |\<chi>. \<chi> \<in> cls'} \<union>
    cls')"
  by auto
termination by (relation "measure card") (auto simp add: card_gt_0_iff)

text \<open>To avoid infinite simplifier loops:\<close>
declare build_all_simple_clss.simps[simp del]

lemma build_all_simple_clss_simps_if[simp]:
  "\<not>finite vars \<or> vars = {} \<Longrightarrow> build_all_simple_clss vars = {{#}}"
  by (simp add: build_all_simple_clss.simps)

lemma build_all_simple_clss_simps_else[simp]:
  fixes vars::"'v ::linorder set"
  defines "cls \<equiv> build_all_simple_clss (vars - {Min vars}) "
  shows
  "finite vars \<and> vars \<noteq> {} \<Longrightarrow> build_all_simple_clss (vars::'v ::linorder set) =
    {{#Pos (Min vars)#} + \<chi> |\<chi>. \<chi> \<in> cls}
    \<union> {{#Neg (Min vars)#} + \<chi> |\<chi>. \<chi> \<in> cls}
    \<union> cls"
  using build_all_simple_clss.simps[of vars] unfolding Let_def cls_def by metis

lemma build_all_simple_clss_finite:
  fixes atms :: "'v::linorder set"
  shows "finite (build_all_simple_clss atms)"
proof (induct "card atms" arbitrary: atms rule: nat_less_induct)
  case (1 atms) note IH = this
  {
    assume "atms = {} \<or> \<not>finite atms"
    hence "finite (build_all_simple_clss atms)" by auto
  }
  also {
    assume atms: "atms \<noteq> {}" and fin: "finite atms"
    hence "Min atms \<in> atms" using Min_in by auto
    hence "card (atms - {Min atms}) < card atms" using fin atms by (meson card_Diff1_less)
    hence "finite (build_all_simple_clss (atms - {Min atms}))" using IH by auto
    hence "finite (build_all_simple_clss atms)" by (simp add: atms fin)
  }
  ultimately show "finite (build_all_simple_clss atms)" by blast
qed

lemma cls_in_build_all_simple_clss:
  shows "{#} \<in> build_all_simple_clss s"
  apply (induct rule: build_all_simple_clss.induct)
   apply simp
  by (metis (no_types, lifting) UnCI build_all_simple_clss.simps insertI1)

lemma build_all_simple_clss_card:
  fixes atms :: "'v :: linorder set"
  assumes "finite atms"
  shows "card (build_all_simple_clss atms) \<le> 3 ^(card atms)"
  using assms
proof (induct "card atms" arbitrary: atms rule: nat_less_induct)
  case (1 atms) note IH = this(1) and finite = this(2)
  {
    assume "atms = {}"
    hence "card (build_all_simple_clss atms) \<le> 3 ^(card atms)" by auto
  }
  also {
    let ?P = "{{#Pos (Min atms)#} + \<chi> |\<chi>. \<chi> \<in> build_all_simple_clss (atms - {Min atms})}"
    let ?N = "{{#Neg (Min atms)#} + \<chi> |\<chi>. \<chi> \<in> build_all_simple_clss (atms - {Min atms})}"
    let ?Z = "build_all_simple_clss (atms - {Min atms})"
    assume atms: "atms \<noteq> {}"
    hence min: "Min atms \<in> atms" using Min_in finite by auto
    hence card_atms_1: "card atms \<ge>  1" by (simp add: Suc_leI atms card_gt_0_iff local.finite)
    have "card (build_all_simple_clss atms) =  card (?P \<union> ?N \<union> ?Z)" using atms finite by simp
    also
      have "\<And>M Ma. card ((M::'v literal multiset set) \<union> Ma) \<le> card Ma + card M"
          by (simp add: add.commute card_Un_le)
      hence "card (?P \<union> ?N \<union> ?Z) \<le> card ?Z + (card ?P + card ?N)"
        by (meson Nat.le_trans card_Un_le nat_add_left_cancel_le)
      hence "card (?P \<union> ?N \<union> ?Z) \<le> card ?P + card ?N + card ?Z"
        by presburger
    also
      have PZ: "card ?P \<le> card ?Z"
        by (simp add: Setcompr_eq_image build_all_simple_clss_finite card_image_le)
      have NZ: "card ?N \<le> card ?Z"
        by (simp add: Setcompr_eq_image build_all_simple_clss_finite card_image_le)
      have "card ?P + card ?N + card ?Z \<le> card ?Z + card ?Z + card ?Z"
        using PZ NZ by linarith
    finally have "card (build_all_simple_clss atms) \<le> card ?Z + card ?Z + card ?Z" .
    moreover
      have finite': "finite (atms - {Min atms})" and
        card: "card (atms - {Min atms}) = card atms - 1"
        using finite min by auto
      have card_inf: "card (atms - {Min atms}) < card atms "
        using card `card atms \<ge>  1` min by auto
      hence "card ?Z \<le> 3 ^ (card atms - 1)" using IH finite' card by metis
    moreover
      have "(3::nat) ^ (card atms - 1) + 3 ^ (card atms - 1) + 3 ^ (card atms - 1) = 3 * 3 ^ (card atms - 1)" by simp
      hence "(3::nat) ^ (card atms - 1) + 3 ^ (card atms - 1) + 3 ^ (card atms - 1) = 3 ^ (card atms)" by (metis card card_Suc_Diff1 local.finite min power_Suc)
    ultimately have "card (build_all_simple_clss atms) \<le> 3 ^ (card atms)" by linarith
  }
  ultimately show "card (build_all_simple_clss atms) \<le> 3 ^ (card atms)" by metis
qed

lemma build_all_simple_clss_mono_disj:
  assumes "atms \<inter> atms'= {}" and "finite atms" and  "finite atms'"
  shows "build_all_simple_clss atms \<subseteq> build_all_simple_clss (atms \<union> atms')"
  using assms
proof (induct "card (atms \<union> atms')" arbitrary: atms atms')
  case (0 atms' atms)
  thus ?case by auto
next
  case (Suc n atms atms') note IH = this(1) and c = this(2) and disj = this(3) and finite = this(4) and finite' = this(5)
  let ?min = "Min (atms \<union> atms')"
  have "?min \<in> atms \<or> ?min \<in> atms'" by (metis Min_in Un_iff c card_eq_0_iff nat.distinct(1))

  also {
    assume min: "?min \<in> atms'"
    hence min': "?min \<notin> atms" using disj by auto
    have "atms = atms - {?min}"
      using min' by fastforce
    hence "n = card (atms \<union> (atms' - {?min}))"
      using c min finite by (metis Min_in Un_Diff card_Diff_singleton_if diff_Suc_1 finite' finite_UnI sup_eq_bot_iff)
    also have "atms \<inter> (atms' - {?min}) = {}" using disj by auto
    moreover have "finite (atms' - {?min})" using finite' by auto
    ultimately have "build_all_simple_clss atms \<subseteq> build_all_simple_clss (atms \<union> (atms' - {?min}))" using IH[of atms "atms' - {?min}"] finite by metis
    also have "atms \<union> (atms' - {?min}) = (atms \<union> atms') - {?min}" using min min' by auto
    ultimately have ?case by (metis (no_types, lifting) build_all_simple_clss.simps c card_0_eq finite' finite_UnI le_supI2 local.finite nat.distinct(1))
  }
  moreover {
    let ?atms' = "atms - {Min atms}"
    assume min: "?min \<in> atms"
    also have min': "?min \<notin> atms'" using disj min by auto
    moreover have "atms' - {?min} = atms'"
      using `?min \<notin> atms'` by fastforce
    ultimately have "n = card (atms - {?min} \<union> atms')"
      by (metis Min_in Un_Diff c card_0_eq card_Diff_singleton_if diff_Suc_1 finite' finite_Un local.finite nat.distinct(1))
    also have "finite (atms - {?min})" using finite by auto
    moreover have "(atms - {?min}) \<inter> atms' = {}" using disj by auto
    ultimately have "build_all_simple_clss (atms - {?min}) \<subseteq> build_all_simple_clss ((atms- {?min}) \<union> atms' )" using IH[of "atms - {?min}" atms'] finite' by metis
    also have "build_all_simple_clss atms = {{#Pos (Min atms)#} + \<chi> |\<chi>. \<chi> \<in> build_all_simple_clss (?atms')} \<union> {{#Neg (Min atms)#} + \<chi> |\<chi>. \<chi> \<in> build_all_simple_clss (?atms')} \<union> build_all_simple_clss (?atms')" using build_all_simple_clss_simps_else[of "atms"] finite min by (metis emptyE)
    moreover
      let ?mcls = "build_all_simple_clss (atms \<union> atms' - {?min})"
      have "build_all_simple_clss (atms \<union> atms') = {{#Pos (?min)#} + \<chi> |\<chi>. \<chi> \<in> ?mcls} \<union> {{#Neg (?min)#} + \<chi> |\<chi>. \<chi> \<in> ?mcls} \<union> ?mcls" using build_all_simple_clss_simps_else[of "atms \<union> atms'"] finite' min by (metis c card_eq_0_iff nat.distinct(1))
    moreover have "atms \<union> atms' - {?min} = atms - {?min} \<union> atms'" using min min' by (simp add: Un_Diff)
    moreover have "Min atms = ?min" using min min' by (simp add: Min_eqI finite' local.finite)
    ultimately have ?case by auto
  }
  ultimately show ?case by metis
qed

lemma build_all_simple_clss_mono:
  assumes finite: "finite atms'" and incl: "atms \<subseteq> atms'"
  shows "build_all_simple_clss atms \<subseteq> build_all_simple_clss atms'"
proof -
  have "atms' = atms \<union> (atms' - atms)" using incl by auto
  also have "finite (atms' - atms)" using finite by auto
  moreover have "atms \<inter> (atms' - atms) = {}" by auto
  ultimately show ?thesis
    using rev_finite_subset[OF assms] build_all_simple_clss_mono_disj by (metis (no_types))
qed

lemma distinct_mset_not_tautology_implies_in_build_all_simple_clss:
  assumes "distinct_mset \<chi>" and "\<not>tautology \<chi>"
  shows "\<chi> \<in> build_all_simple_clss (atms_of \<chi>)"
  using assms
proof (induct "card (atms_of \<chi>)" arbitrary: \<chi>)
  case 0
  thus ?case by simp
next
  case (Suc n) note IH = this(1) and simp = this(3) and c = this(2) and no_dup = this(4)
  have finite: "finite (atms_of \<chi>)" by simp

  with no_dup atm_iff_pos_or_neg_lit obtain L where
    L\<chi>: "L \<in># \<chi>" and
    L_min: "atm_of L = Min (atms_of \<chi>)" and
    mL\<chi>: "\<not> -L \<in># \<chi>"
    by (metis Min_in c card_0_eq literal.sel(1,2) nat.distinct(1) tautology_minus)
  hence \<chi>L: "\<chi> = (\<chi> - {#L#}) + {#L#}" by auto
  have atm\<chi>: "atms_of \<chi> = atms_of (\<chi> - {#L#}) \<union> {atm_of L}"
    using arg_cong[OF \<chi>L, of atms_of] by simp

  have a\<chi>: "atms_of (\<chi> - {#L#}) = (atms_of \<chi>) - {atm_of L}"
    proof
      show "atms_of (\<chi> - {#L#}) \<subseteq> atms_of \<chi> - {atm_of L}"
        proof
          fix v
          assume a: "v \<in> atms_of (\<chi> - {#L#})"
          then obtain l where l: "v = atm_of l" and l': "l \<in># \<chi> - {#L#}"
            unfolding atms_of_def by auto
          also {
            assume "v = atm_of L"
            hence "L \<in># \<chi> - {#L#} \<or> -L \<in># \<chi> - {#L#}"
              using l' l by (auto simp add: atm_of_eq_atm_of)
            also have "L \<notin># \<chi> - {#L#}" using ` L \<in># \<chi>` simp unfolding distinct_mset_def by auto
            ultimately have False using mL\<chi> by auto
          }
          ultimately show "v \<in> atms_of \<chi> - {atm_of L}"
            using atm_of_lit_in_atms_of by force
        qed
    next
      show "atms_of \<chi> - {atm_of L} \<subseteq> atms_of (\<chi> - {#L#})" using atm\<chi> by auto
    qed

  let ?s' = "build_all_simple_clss (atms_of (\<chi> - {#L#}))"
  have "card (atms_of (\<chi> - {#L#})) = n"
    using c finite a\<chi> by (metis L\<chi> atm_of_lit_in_atms_of card_Diff_singleton_if diff_Suc_1)
  also have "distinct_mset (\<chi> - {#L#})" using simp by auto
  moreover have "\<not>tautology (\<chi> - {#L#})"
    by (meson Multiset.diff_le_self mset_leD no_dup tautology_decomp)
  ultimately have \<chi>in: "\<chi> - {#L#} \<in> build_all_simple_clss (atms_of (\<chi> - {#L#}))"
    using IH by simp
  have "\<chi> =  {#L#} + (\<chi> - {#L#})" using \<chi>L by (simp add: add.commute)
  thus ?case
    using \<chi>in L_min a\<chi>
    by (cases L)
       (auto simp add: build_all_simple_clss.simps[of "atms_of \<chi>"] Let_def)
qed

lemma simplified_in_build_all:
  assumes "finite \<psi>" and "distinct_mset_set \<psi>" and "\<forall>\<chi> \<in> \<psi>. \<not>tautology \<chi>"
  shows "\<psi> \<subseteq> build_all_simple_clss (atms_of_m \<psi>)"
  using assms
proof (induct rule: finite.induct)
  case emptyI
  thus ?case by simp
next
  case (insertI \<psi> \<chi>) note finite = this(1) and IH = this(2) and simp = this(3) and tauto = this(4)
  have "distinct_mset \<chi>" and "\<not>tautology \<chi>" using simp tauto unfolding distinct_mset_set_def by auto
  from distinct_mset_not_tautology_implies_in_build_all_simple_clss[OF this] have \<chi>: "\<chi> \<in> build_all_simple_clss (atms_of \<chi>)" .
  hence "\<psi> \<subseteq> build_all_simple_clss (atms_of_m \<psi>)" using IH simp tauto by auto
  also have "atms_of_m \<psi> \<subseteq> atms_of_m (insert \<chi> \<psi>)" unfolding atms_of_m_def atms_of_def by force
  ultimately have "\<psi> \<subseteq> build_all_simple_clss (atms_of_m (insert \<chi> \<psi>))"
    by (metis atms_of_m_finite build_all_simple_clss_mono finite.insertI finite order_trans)
  moreover
    have "\<chi> \<in> build_all_simple_clss (atms_of_m (insert \<chi> \<psi>))"
      using \<chi> finite build_all_simple_clss_mono[of "atms_of_m (insert \<chi> \<psi>)"] by auto
  ultimately show ?case by auto
qed

(* Maybe should become locales at some point of time ?
Shared prop of \<Turnstile>:
* I + I' \<Turnstile> A \<longleftrightarrow> I' + I \<Turnstile> A

Shared by the formula version of \<Turnstile>:
* N \<subseteq> N' \<Longrightarrow> N' \<Turnstile> \<psi> \<Longrightarrow> N \<Turnstile> \<psi>
* A \<subseteq> B \<Longrightarrow> N \<Turnstile> B \<Longrightarrow> N \<Turnstile> A

Shared by the other \<Turnstile> symbols:
* I \<Turnstile> A \<Longrightarrow> I + I' \<Turnstile> A
* I \<Turnstile> A \<star> B \<Longrightarrow> I \<Turnstile> B \<star> A
* I \<Turnstile> A \<Longrightarrow> I \<Turnstile> B \<Longrightarrow> I \<Turnstile> A \<star> B

Shared by the first layer 'a \<Rightarrow> 'b set \<Rightarrow> bool:
* A \<subseteq> B \<Longrightarrow> I \<Turnstile> A \<Longrightarrow> I \<Turnstile> B
* I \<Turnstile> A \<star> B \<longleftrightarrow> I \<Turnstile>s A \<or> I \<Turnstile>s B

Shared by the second layer of type 'a \<Rightarrow> 'b set \<Rightarrow> bool:
* definition: I \<Turnstile>s A \<longleftrightarrow> \<forall>a \<in> A. I \<Turnstile> a
* I \<Turnstile>s {A} \<longleftrightarrow> I \<Turnstile> A
* I \<Turnstile>s A \<star> B \<longleftrightarrow> I \<Turnstile>s A \<and> I \<Turnstile>s B
* A \<subseteq> B \<Longrightarrow> I \<Turnstile>s B \<Longrightarrow> I \<Turnstile>s A
* I \<Turnstile>s {}

*   true_lit      \<Turnstile>   'a interp \<Rightarrow> 'a literal \<Rightarrow> bool
*   true_cls      \<Turnstile>l  'a interp \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_clss     \<Turnstile>s  'a interp \<Rightarrow> 'a clauses \<Rightarrow> bool

*   true_annot    \<Turnstile>a   annoted_lits \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_annots   \<Turnstile>as  annoted_lits \<Rightarrow> 'a clauses \<Rightarrow> bool

Formula version :
*   true_cls_cls   \<Turnstile>f  'a clause \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_cls_clss  \<Turnstile>fs 'a clause \<Rightarrow> 'a clauses \<Rightarrow> bool

*   true_clss_cls  \<Turnstile>p  'a clauses \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_clss_clss \<Turnstile>ps 'a clauses \<Rightarrow> 'a clauses \<Rightarrow> bool
*)

locale entail =
  fixes entail :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<Turnstile>e" 50)
  assumes entail_insert[simp]: "I \<noteq> {} \<Longrightarrow> insert L I \<Turnstile>e x \<longleftrightarrow> {L} \<Turnstile>e x \<or> I \<Turnstile>e x"
  assumes entail_union[simp]: "I \<Turnstile>e A \<Longrightarrow> I \<union> I' \<Turnstile>e A"
begin


definition entails :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infix "\<Turnstile>es" 50) where
  "I \<Turnstile>es A \<longleftrightarrow> (\<forall>a \<in> A. I \<Turnstile>e a)"

lemma entails_empty[simp]:
  "I \<Turnstile>es {}"
  unfolding entails_def by auto

lemma entails_single[iff]:
  "I \<Turnstile>es {a} \<longleftrightarrow> I \<Turnstile>e a"
  unfolding entails_def by auto

lemma entails_insert_l[simp]:
  "M \<Turnstile>es A \<Longrightarrow> insert L M \<Turnstile>es A"
  unfolding entails_def by (metis Un_commute entail_union insert_is_Un)

lemma entails_union[iff]: "I \<Turnstile>es CC \<union> DD \<longleftrightarrow> I \<Turnstile>es CC \<and> I \<Turnstile>es DD"
  unfolding entails_def by blast

lemma entails_insert[iff]: "I \<Turnstile>es insert C DD \<longleftrightarrow> I \<Turnstile>e C \<and> I \<Turnstile>es DD"
  unfolding entails_def by blast

lemma entails_insert_mono: "DD \<subseteq> CC \<Longrightarrow> I \<Turnstile>es CC \<Longrightarrow> I \<Turnstile>es DD"
  unfolding entails_def by blast

lemma entails_union_increase[simp]:
 assumes "I \<Turnstile>es \<psi>"
 shows "I \<union> I' \<Turnstile>es \<psi>"
 using assms unfolding entails_def by auto

lemma true_clss_commute_l:
  "(I \<union> I' \<Turnstile>es \<psi>) \<longleftrightarrow> (I' \<union> I \<Turnstile>es \<psi>)"
  by (simp add: Un_commute)

lemma entails_remove[simp]: "I \<Turnstile>es N \<Longrightarrow> I \<Turnstile>es Set.remove a N"
  by (simp add: entails_def)

lemma entails_remove_minus[simp]: "I \<Turnstile>es N \<Longrightarrow> I \<Turnstile>es N - A"
  by (simp add: entails_def)

end

interpretation true_cls!: entail "true_cls"
  by standard (auto simp add: true_cls_def)

thm true_cls.entails_def
thm true_clss_def
end
