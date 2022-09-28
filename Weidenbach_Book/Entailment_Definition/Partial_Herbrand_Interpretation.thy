(* Title: Partial Clausal Logic
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>

This theory is based on Blanchette's and Traytel's Clausal logic
*)
section \<open>Partial Herbrand Interpretation\<close>

theory Partial_Herbrand_Interpretation
  imports
    Weidenbach_Book_Base.WB_List_More
    Ordered_Resolution_Prover.Clausal_Logic
begin

subsection \<open>More Literals\<close>

text \<open>The following lemma is very useful when in the goal appears an axioms like @{term \<open>-L = K\<close>}:
  this lemma allows the simplifier to rewrite L.\<close>
lemma in_image_uminus_uminus: \<open>a \<in> uminus ` A \<longleftrightarrow> -a \<in> A\<close> for a :: \<open>'v literal\<close>
  using uminus_lit_swap by auto

lemma uminus_lit_swap: "- a = b \<longleftrightarrow> (a::'a literal) = - b"
  by auto

lemma atm_of_notin_atms_of_iff: \<open>atm_of L \<notin> atms_of C' \<longleftrightarrow> L \<notin># C' \<and> -L \<notin># C'\<close> for L C'
  by (cases L) (auto simp: atm_iff_pos_or_neg_lit)

lemma atm_of_notin_atms_of_iff_Pos_Neg:
   \<open>L \<notin> atms_of C' \<longleftrightarrow> Pos L \<notin># C' \<and> Neg L \<notin># C'\<close> for L C'
  by (auto simp: atm_iff_pos_or_neg_lit)

lemma atms_of_uminus[simp]: \<open>atms_of (uminus `# C) = atms_of C\<close>
  by (auto simp: atms_of_def image_image)

lemma distinct_mset_atm_ofD:
  \<open>distinct_mset (atm_of `# mset xc) \<Longrightarrow> distinct xc\<close>
  by (induction xc) auto

lemma atms_of_cong_set_mset:
  \<open>set_mset D = set_mset D' \<Longrightarrow> atms_of D = atms_of D'\<close>
  by (auto simp: atms_of_def)

lemma lit_in_set_iff_atm:
  \<open>NO_MATCH (Pos x) l \<Longrightarrow> NO_MATCH (Neg x) l \<Longrightarrow>
    l \<in> M \<longleftrightarrow> (\<exists>l'. (l = Pos l' \<and> Pos l' \<in> M) \<or> (l = Neg l' \<and> Neg l' \<in> M))\<close>
  by (cases l) auto


text \<open>We define here entailment by a set of literals. This is an Herbrand interpretation, but not
  the same as used for the resolution prover. Both has different properties.
  One key difference is that such a set can be inconsistent (i.e.\
  containing both @{term "L::'a literal"} and @{term "-L::'a literal"}).

  Satisfiability is defined by the existence of a total and consistent model.
\<close>

lemma lit_eq_Neg_Pos_iff:
  \<open>x \<noteq> Neg (atm_of x) \<longleftrightarrow> is_pos x\<close>
  \<open>x \<noteq> Pos (atm_of x) \<longleftrightarrow> is_neg x\<close>
  \<open>-x \<noteq> Neg (atm_of x) \<longleftrightarrow> is_neg x\<close>
  \<open>-x \<noteq> Pos (atm_of x) \<longleftrightarrow> is_pos x\<close>
  \<open>Neg (atm_of x) \<noteq> x \<longleftrightarrow> is_pos x\<close>
  \<open>Pos (atm_of x) \<noteq> x \<longleftrightarrow> is_neg x\<close>
  \<open>Neg (atm_of x) \<noteq> -x \<longleftrightarrow> is_neg x\<close>
  \<open>Pos (atm_of x) \<noteq> -x \<longleftrightarrow> is_pos x\<close>
  by (cases x; auto; fail)+


subsection \<open>Clauses\<close>

text \<open>
Clauses are set of literals or (finite) multisets of literals.
\<close>
type_synonym 'v clause_set = "'v clause set"
type_synonym 'v clauses = "'v clause multiset"

lemma is_neg_neg_not_is_neg: "is_neg (- L) \<longleftrightarrow> \<not> is_neg L"
  by (cases L) auto


subsection \<open>Partial Interpretations\<close>

type_synonym 'a partial_interp = "'a literal set"

definition true_lit :: "'a partial_interp \<Rightarrow> 'a literal \<Rightarrow> bool" (infix "\<Turnstile>l" 50) where
  "I \<Turnstile>l L \<longleftrightarrow> L \<in> I"

declare true_lit_def[simp]


subsubsection \<open>Consistency\<close>

definition consistent_interp :: "'a literal set \<Rightarrow> bool" where
"consistent_interp I \<longleftrightarrow> (\<forall>L. \<not>(L \<in> I \<and> - L \<in> I))"

lemma consistent_interp_empty[simp]:
  "consistent_interp {}" unfolding consistent_interp_def by auto

lemma consistent_interp_single[simp]:
  "consistent_interp {L}" unfolding consistent_interp_def by auto

lemma Ex_consistent_interp: \<open>Ex consistent_interp\<close>
  by (auto simp: consistent_interp_def)

lemma consistent_interp_subset:
  assumes
    "A \<subseteq> B" and
    "consistent_interp B"
  shows "consistent_interp A"
  using assms unfolding consistent_interp_def by auto

lemma consistent_interp_change_insert:
  "a \<notin> A \<Longrightarrow> -a \<notin> A \<Longrightarrow> consistent_interp (insert (-a) A) \<longleftrightarrow> consistent_interp (insert a A)"
  unfolding consistent_interp_def by fastforce

lemma consistent_interp_insert_pos[simp]:
  "a \<notin> A \<Longrightarrow> consistent_interp (insert a A) \<longleftrightarrow> consistent_interp A \<and> -a \<notin> A"
  unfolding consistent_interp_def by auto

lemma consistent_interp_insert_not_in:
  "consistent_interp A \<Longrightarrow> a \<notin> A \<Longrightarrow> -a \<notin> A \<Longrightarrow> consistent_interp (insert a A)"
  unfolding consistent_interp_def by auto

lemma consistent_interp_unionD: \<open>consistent_interp (I \<union> I') \<Longrightarrow> consistent_interp I'\<close>
  unfolding consistent_interp_def by auto

lemma consistent_interp_insert_iff:
  \<open>consistent_interp (insert L C) \<longleftrightarrow> consistent_interp C \<and> -L \<notin> C\<close>
  by (metis consistent_interp_def consistent_interp_insert_pos insert_absorb)


lemma (in -) distinct_consistent_distinct_atm:
  \<open>distinct M \<Longrightarrow> consistent_interp (set M) \<Longrightarrow> distinct_mset (atm_of `# mset M)\<close>
  by (induction M) (auto simp: atm_of_eq_atm_of)


subsubsection \<open>Atoms\<close>

text \<open>We define here various lifting of @{term atm_of} (applied to a single literal) to set and
  multisets of literals.\<close>
definition atms_of_ms :: "'a clause set \<Rightarrow> 'a set" where
"atms_of_ms \<psi>s = \<Union>(atms_of ` \<psi>s)"

lemma atms_of_mmltiset[simp]:
  "atms_of (mset a) = atm_of ` set a"
  by (induct a) auto

lemma atms_of_ms_mset_unfold:
  "atms_of_ms (mset ` b) = (\<Union>x\<in>b. atm_of ` set x)"
  unfolding atms_of_ms_def by simp

definition atms_of_s :: "'a literal set \<Rightarrow> 'a set" where
  "atms_of_s C = atm_of ` C"

lemma atms_of_ms_emtpy_set[simp]:
  "atms_of_ms {} = {}"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_memtpy[simp]:
  "atms_of_ms {{#}} = {}"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_mono:
  "A \<subseteq> B \<Longrightarrow> atms_of_ms A \<subseteq> atms_of_ms B"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_finite[simp]:
  "finite \<psi>s \<Longrightarrow> finite (atms_of_ms \<psi>s)"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_union[simp]:
  "atms_of_ms (\<psi>s \<union> \<chi>s) = atms_of_ms \<psi>s \<union> atms_of_ms \<chi>s"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_insert[simp]:
  "atms_of_ms (insert \<psi>s \<chi>s) = atms_of \<psi>s \<union> atms_of_ms \<chi>s"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_singleton[simp]: "atms_of_ms {L} = atms_of L"
  unfolding atms_of_ms_def by auto

lemma atms_of_atms_of_ms_mono[simp]:
  "A \<in> \<psi> \<Longrightarrow> atms_of A \<subseteq> atms_of_ms \<psi>"
  unfolding atms_of_ms_def by fastforce

lemma atms_of_ms_remove_incl:
  shows "atms_of_ms (Set.remove a \<psi>) \<subseteq> atms_of_ms \<psi>"
  unfolding atms_of_ms_def by auto

lemma atms_of_ms_remove_subset:
  "atms_of_ms (\<phi> - \<psi>) \<subseteq> atms_of_ms \<phi>"
  unfolding atms_of_ms_def by auto

lemma finite_atms_of_ms_remove_subset[simp]:
  "finite (atms_of_ms A) \<Longrightarrow> finite (atms_of_ms (A - C))"
  using atms_of_ms_remove_subset[of A C] finite_subset by blast

lemma atms_of_ms_empty_iff:
  "atms_of_ms A = {} \<longleftrightarrow> A = {{#}} \<or> A = {}"
  apply (rule iffI)
   apply (metis (no_types, lifting) atms_empty_iff_empty atms_of_atms_of_ms_mono insert_absorb
    singleton_iff singleton_insert_inj_eq' subsetI subset_empty)
  apply (auto; fail)
  done

lemma in_implies_atm_of_on_atms_of_ms:
  assumes "L \<in># C" and "C \<in> N"
  shows "atm_of L \<in> atms_of_ms N"
  using atms_of_atms_of_ms_mono[of C N] assms by (simp add: atm_of_lit_in_atms_of subset_iff)

lemma in_plus_implies_atm_of_on_atms_of_ms:
  assumes "C+{#L#} \<in> N"
  shows "atm_of L \<in> atms_of_ms N"
  using in_implies_atm_of_on_atms_of_ms[of _ "C +{#L#}"] assms by auto

lemma in_m_in_literals:
  assumes "add_mset A D \<in> \<psi>s"
  shows "atm_of A \<in> atms_of_ms \<psi>s"
  using assms by (auto dest: atms_of_atms_of_ms_mono)

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
  then show ?Q unfolding atms_of_s_def by (metis image_iff literal.exhaust_sel)
next
  assume ?Q
  then show ?P unfolding atms_of_s_def by force
qed

lemma atm_of_in_atm_of_set_in_uminus:
  "atm_of L' \<in> atm_of ` B \<Longrightarrow> L' \<in> B \<or> - L' \<in> B"
  using atms_of_s_def by (cases L') fastforce+

lemma finite_atms_of_s[simp]:
  \<open>finite M \<Longrightarrow> finite (atms_of_s M)\<close>
  by (auto simp: atms_of_s_def)

lemma
  atms_of_s_empty [simp]:
    \<open>atms_of_s {} = {}\<close> and
  atms_of_s_empty_iff[simp]:
    \<open>atms_of_s x = {} \<longleftrightarrow> x = {}\<close>
  by (auto simp: atms_of_s_def)


subsubsection \<open>Totality\<close>

definition total_over_set :: "'a partial_interp \<Rightarrow> 'a set \<Rightarrow> bool" where
"total_over_set I S = (\<forall>l\<in>S. Pos l \<in> I \<or> Neg l \<in> I)"

definition total_over_m :: "'a literal set \<Rightarrow> 'a clause set \<Rightarrow> bool" where
"total_over_m I \<psi>s = total_over_set I (atms_of_ms \<psi>s)"

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
  using atms_of_ms_mono[of A] unfolding total_over_m_def total_over_set_def by auto

lemma total_over_m_sum[iff]:
  shows "total_over_m I {C + D} \<longleftrightarrow> (total_over_m I {C} \<and> total_over_m I {D})"
  unfolding total_over_m_def total_over_set_def by auto

lemma total_over_m_union[iff]:
  "total_over_m I (A \<union> B) \<longleftrightarrow> (total_over_m I A \<and> total_over_m I B)"
  unfolding total_over_m_def total_over_set_def by auto

lemma total_over_m_insert[iff]:
  "total_over_m I (insert a A) \<longleftrightarrow> (total_over_set I (atms_of a) \<and> total_over_m I A)"
  unfolding total_over_m_def total_over_set_def by fastforce

lemma total_over_m_extension:
  fixes I :: "'v literal set" and A :: "'v clause_set"
  assumes total: "total_over_m I A"
  shows "\<exists>I'. total_over_m (I \<union> I') (A\<union>B)
    \<and> (\<forall>x\<in>I'. atm_of x \<in> atms_of_ms B \<and> atm_of x \<notin> atms_of_ms A)"
proof -
  let ?I' = "{Pos v |v. v\<in> atms_of_ms B \<and> v \<notin> atms_of_ms A}"
  have "\<forall>x\<in>?I'. atm_of x \<in> atms_of_ms B \<and> atm_of x \<notin> atms_of_ms A" by auto
  moreover have "total_over_m (I \<union> ?I') (A\<union>B)"
    using total unfolding total_over_m_def total_over_set_def by auto
  ultimately show ?thesis by blast
qed

lemma total_over_m_consistent_extension:
  fixes I :: "'v literal set" and A :: "'v clause_set"
  assumes
    total: "total_over_m I A" and
    cons: "consistent_interp I"
  shows "\<exists>I'. total_over_m (I \<union> I') (A \<union> B)
    \<and> (\<forall>x\<in>I'. atm_of x \<in> atms_of_ms B \<and> atm_of x \<notin> atms_of_ms A) \<and> consistent_interp (I \<union> I')"
proof -
  let ?I' = "{Pos v |v. v\<in> atms_of_ms B \<and> v \<notin> atms_of_ms A \<and> Pos v \<notin> I \<and> Neg v \<notin> I}"
  have "\<forall>x\<in>?I'. atm_of x \<in> atms_of_ms B \<and> atm_of x \<notin> atms_of_ms A" by auto
  moreover have "total_over_m (I \<union> ?I') (A\<union>B)"
    using total unfolding total_over_m_def total_over_set_def by auto
  moreover have "consistent_interp (I \<union> ?I')"
    using cons unfolding consistent_interp_def by (intro allI) (rename_tac L, case_tac L, auto)
  ultimately show ?thesis by blast
qed

lemma total_over_set_atms_of_m[simp]:
  "total_over_set Ia (atms_of_s Ia)"
  unfolding total_over_set_def atms_of_s_def by (metis image_iff literal.exhaust_sel)

lemma total_over_set_literal_defined:
  assumes "add_mset A D \<in> \<psi>s"
  and "total_over_set I (atms_of_ms \<psi>s)"
  shows "A \<in> I \<or> -A \<in> I"
  using assms unfolding total_over_set_def by (metis (no_types) Neg_atm_of_iff in_m_in_literals
    literal.collapse(1) uminus_Neg uminus_Pos)

lemma tot_over_m_remove:
  assumes "total_over_m (I \<union> {L}) {\<psi>}"
  and L: "L \<notin># \<psi>" "-L \<notin># \<psi>"
  shows "total_over_m I {\<psi>}"
  unfolding total_over_m_def total_over_set_def
proof
  fix l
  assume l: "l \<in> atms_of_ms {\<psi>}"
  then have "Pos l \<in> I \<or> Neg l \<in> I \<or> l = atm_of L"
    using assms unfolding total_over_m_def total_over_set_def by auto
  moreover have "atm_of L \<notin> atms_of_ms {\<psi>}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "atm_of L \<in> atms_of \<psi>" by auto
      then have "Pos (atm_of L) \<in># \<psi> \<or> Neg (atm_of L) \<in># \<psi>"
        using atm_imp_pos_or_neg_lit by metis
      then have "L \<in># \<psi> \<or> - L \<in># \<psi>" by (cases L) auto
      then show False using L by auto
    qed
  ultimately show "Pos l \<in> I \<or> Neg l \<in> I" using l by metis
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

lemma total_over_m_alt_def: \<open>total_over_m I S \<longleftrightarrow> atms_of_ms S \<subseteq> atms_of_s I\<close>
  by (auto simp: total_over_m_def total_over_set_def)

lemma total_over_set_alt_def: \<open>total_over_set M A \<longleftrightarrow> A \<subseteq> atms_of_s M\<close>
  by (auto simp: total_over_set_def)


subsubsection \<open>Interpretations\<close>

definition true_cls :: "'a partial_interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "I \<Turnstile> C \<longleftrightarrow> (\<exists>L \<in># C. I \<Turnstile>l L)"

lemma true_cls_empty[iff]: "\<not> I \<Turnstile> {#}"
  unfolding true_cls_def by auto

lemma true_cls_singleton[iff]: "I \<Turnstile> {#L#} \<longleftrightarrow> I \<Turnstile>l L"
  unfolding true_cls_def by (auto split:if_split_asm)

lemma true_cls_add_mset[iff]: "I \<Turnstile> add_mset a D \<longleftrightarrow> a \<in> I \<or> I \<Turnstile> D"
  unfolding true_cls_def by auto

lemma true_cls_union[iff]: "I \<Turnstile> C + D \<longleftrightarrow> I \<Turnstile> C \<or> I \<Turnstile> D"
  unfolding true_cls_def by auto

lemma true_cls_mono_set_mset: "set_mset C \<subseteq> set_mset D \<Longrightarrow> I \<Turnstile> C \<Longrightarrow> I \<Turnstile> D"
  unfolding true_cls_def subset_eq Bex_def by metis

lemma true_cls_mono_leD[dest]: "A \<subseteq># B \<Longrightarrow> I \<Turnstile> A \<Longrightarrow> I \<Turnstile> B"
  unfolding true_cls_def by auto

lemma
  assumes "I \<Turnstile> \<psi>"
  shows
    true_cls_union_increase[simp]: "I \<union> I' \<Turnstile> \<psi>" and
    true_cls_union_increase'[simp]: "I' \<union> I \<Turnstile> \<psi>"
  using assms unfolding true_cls_def by auto

lemma true_cls_mono_set_mset_l:
  assumes "A \<Turnstile> \<psi>"
  and "A \<subseteq> B"
  shows "B \<Turnstile> \<psi>"
  using assms unfolding true_cls_def by auto

lemma true_cls_replicate_mset[iff]: "I \<Turnstile> replicate_mset n L \<longleftrightarrow> n \<noteq> 0 \<and> I \<Turnstile>l L"
  by (induct n) auto

lemma true_cls_empty_entails[iff]: "\<not> {} \<Turnstile> N"
  by (auto simp add: true_cls_def)

lemma true_cls_not_in_remove:
  assumes "L \<notin># \<chi>" and "I \<union> {L} \<Turnstile> \<chi>"
  shows "I \<Turnstile> \<chi>"
  using assms unfolding true_cls_def by auto

definition true_clss :: "'a partial_interp \<Rightarrow> 'a clause_set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) where
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
  assumes "\<forall>x\<in>I'. atm_of x \<notin> atms_of_ms A"
  and "atms_of L \<subseteq> atms_of_ms A"
  and "I \<union> I' \<Turnstile> L"
  shows "I \<Turnstile> L"
  using assms unfolding true_cls_def true_lit_def Bex_def
  by (metis Un_iff atm_of_lit_in_atms_of contra_subsetD)

lemma notin_vars_union_true_clss_true_clss:
  assumes "\<forall>x\<in>I'. atm_of x \<notin> atms_of_ms A"
  and "atms_of_ms L \<subseteq> atms_of_ms A"
  and "I \<union> I' \<Turnstile>s L"
  shows "I \<Turnstile>s L"
  using assms unfolding true_clss_def true_lit_def Ball_def
  by (meson atms_of_atms_of_ms_mono notin_vars_union_true_cls_true_cls subset_trans)

lemma true_cls_def_set_mset_eq:
  \<open>set_mset A = set_mset B \<Longrightarrow> I \<Turnstile> A \<longleftrightarrow> I \<Turnstile> B\<close>
  by (auto simp: true_cls_def)

lemma true_cls_add_mset_strict: \<open>I \<Turnstile> add_mset L C \<longleftrightarrow> L \<in> I \<or> I \<Turnstile> (removeAll_mset L C)\<close>
  using true_cls_mono_set_mset[of \<open>removeAll_mset L C\<close> C I]
  apply (cases \<open>L \<in># C\<close>)
  apply (auto dest: multi_member_split simp: removeAll_notin)
  apply (metis (mono_tags, lifting) in_multiset_minus_notin_snd in_replicate_mset true_cls_def true_lit_def)
  done


subsubsection \<open>Satisfiability\<close>

definition satisfiable :: "'a clause set \<Rightarrow> bool" where
  "satisfiable CC \<longleftrightarrow> (\<exists>I. (I \<Turnstile>s CC \<and> consistent_interp I \<and> total_over_m I CC))"

lemma satisfiable_single[simp]:
  "satisfiable {{#L#}}"
  unfolding satisfiable_def by fastforce

lemma satisfiable_empty[simp]: \<open>satisfiable {}\<close>
  by (auto simp: satisfiable_def Ex_consistent_interp)

abbreviation unsatisfiable :: "'a clause set \<Rightarrow> bool" where
  "unsatisfiable CC \<equiv> \<not> satisfiable CC"

lemma satisfiable_decreasing:
  assumes "satisfiable (\<psi> \<union> \<psi>')"
  shows "satisfiable \<psi>"
  using assms total_over_m_union unfolding satisfiable_def by blast

lemma satisfiable_def_min:
  "satisfiable CC
    \<longleftrightarrow> (\<exists>I. I \<Turnstile>s CC \<and> consistent_interp I \<and> total_over_m I CC \<and> atm_of`I = atms_of_ms CC)"
    (is "?sat \<longleftrightarrow> ?B")
proof
  assume ?B then show ?sat by (auto simp add: satisfiable_def)
next
  assume ?sat
  then obtain I where
    I_CC: "I \<Turnstile>s CC" and
    cons: "consistent_interp I" and
    tot: "total_over_m I CC"
    unfolding satisfiable_def by auto
  let ?I = "{P. P \<in> I \<and> atm_of P \<in> atms_of_ms CC}"

  have I_CC: "?I \<Turnstile>s CC"
    using I_CC in_implies_atm_of_on_atms_of_ms unfolding true_clss_def Ball_def true_cls_def
    Bex_def true_lit_def
    by blast

  moreover have cons: "consistent_interp ?I"
    using cons unfolding consistent_interp_def by auto
  moreover have "total_over_m ?I CC"
    using tot unfolding total_over_m_def total_over_set_def by auto
  moreover
    have atms_CC_incl: "atms_of_ms CC \<subseteq> atm_of`I"
      using tot unfolding total_over_m_def total_over_set_def atms_of_ms_def
      by (auto simp add: atms_of_def atms_of_s_def[symmetric])
    have "atm_of ` ?I = atms_of_ms CC"
      using atms_CC_incl unfolding atms_of_ms_def by force
  ultimately show ?B by auto
qed

lemma satisfiable_carac:
  "(\<exists>I. consistent_interp I \<and> I \<Turnstile>s \<phi>) \<longleftrightarrow> satisfiable \<phi>" (is "(\<exists>I. ?Q I) \<longleftrightarrow> ?S")
proof
  assume "?S"
  then show "\<exists>I. ?Q I" unfolding satisfiable_def by auto
next
  assume "\<exists>I. ?Q I"
  then obtain I where cons: "consistent_interp I" and I: "I \<Turnstile>s \<phi>" by metis
  let ?I' = "{Pos v |v. v \<notin> atms_of_s I \<and> v \<in> atms_of_ms \<phi>}"
  have "consistent_interp (I \<union> ?I')"
    using cons unfolding consistent_interp_def by (intro allI) (rename_tac L, case_tac L, auto)
  moreover have "total_over_m (I \<union> ?I') \<phi>"
    unfolding total_over_m_def total_over_set_def by auto
  moreover have "I \<union> ?I' \<Turnstile>s \<phi>"
    using I unfolding Ball_def true_clss_def true_cls_def by auto
  ultimately show ?S unfolding satisfiable_def by blast
qed

lemma satisfiable_carac'[simp]: "consistent_interp I \<Longrightarrow> I \<Turnstile>s \<phi> \<Longrightarrow> satisfiable \<phi>"
  using satisfiable_carac by metis

lemma unsatisfiable_mono:
  \<open>N \<subseteq> N' \<Longrightarrow> unsatisfiable N \<Longrightarrow> unsatisfiable N'\<close>
  by (metis (full_types) satisfiable_decreasing subset_Un_eq)


subsubsection \<open>Entailment for Multisets of Clauses\<close>

definition true_cls_mset :: "'a partial_interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<Turnstile>m" 50) where
  "I \<Turnstile>m CC \<longleftrightarrow> (\<forall>C \<in># CC. I \<Turnstile> C)"

lemma true_cls_mset_empty[simp]: "I \<Turnstile>m {#}"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_singleton[iff]: "I \<Turnstile>m {#C#} \<longleftrightarrow> I \<Turnstile> C"
  unfolding true_cls_mset_def by (auto split: if_split_asm)

lemma true_cls_mset_union[iff]: "I \<Turnstile>m CC + DD \<longleftrightarrow> I \<Turnstile>m CC \<and> I \<Turnstile>m DD"
  unfolding true_cls_mset_def by fastforce

lemma true_cls_mset_add_mset[iff]: "I \<Turnstile>m add_mset C CC \<longleftrightarrow> I \<Turnstile> C \<and> I \<Turnstile>m CC"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_image_mset[iff]: "I \<Turnstile>m image_mset f A \<longleftrightarrow> (\<forall>x \<in># A. I \<Turnstile> f x)"
  unfolding true_cls_mset_def by fastforce

lemma true_cls_mset_mono: "set_mset DD \<subseteq> set_mset CC \<Longrightarrow> I \<Turnstile>m CC \<Longrightarrow> I \<Turnstile>m DD"
  unfolding true_cls_mset_def subset_iff by auto

lemma true_clss_set_mset[iff]: "I \<Turnstile>s set_mset CC \<longleftrightarrow> I \<Turnstile>m CC"
  unfolding true_clss_def true_cls_mset_def by auto

lemma true_cls_mset_increasing_r[simp]:
  "I \<Turnstile>m CC \<Longrightarrow> I \<union> J \<Turnstile>m CC"
  unfolding true_cls_mset_def by auto

theorem true_cls_remove_unused:
  assumes "I \<Turnstile> \<psi>"
  shows "{v \<in> I. atm_of v \<in> atms_of \<psi>} \<Turnstile> \<psi>"
  using assms unfolding true_cls_def atms_of_def by auto

theorem true_clss_remove_unused:
  assumes "I \<Turnstile>s \<psi>"
  shows "{v \<in> I. atm_of v \<in> atms_of_ms \<psi>} \<Turnstile>s \<psi>"
  unfolding true_clss_def atms_of_def Ball_def
proof (intro allI impI)
  fix x
  assume "x \<in> \<psi>"
  then have "I \<Turnstile> x"
    using assms unfolding true_clss_def atms_of_def Ball_def by auto

  then have "{v \<in> I. atm_of v \<in> atms_of x} \<Turnstile> x"
    by (simp only: true_cls_remove_unused[of I])
  moreover have "{v \<in> I. atm_of v \<in> atms_of x} \<subseteq> {v \<in> I. atm_of v \<in> atms_of_ms \<psi>}"
    using \<open>x \<in> \<psi>\<close> by (auto simp add: atms_of_ms_def)
  ultimately show "{v \<in> I. atm_of v \<in> atms_of_ms \<psi>} \<Turnstile> x"
    using true_cls_mono_set_mset_l by blast
qed

text \<open>A simple application of the previous theorem:\<close>
lemma true_clss_union_decrease:
  assumes II': "I \<union> I' \<Turnstile> \<psi>"
  and H: "\<forall>v \<in> I'. atm_of v \<notin> atms_of \<psi>"
  shows "I \<Turnstile> \<psi>"
proof -
  let ?I = "{v \<in> I \<union> I'. atm_of v \<in> atms_of \<psi>}"
  have "?I \<Turnstile> \<psi>" using true_cls_remove_unused II' by blast
  moreover have "?I \<subseteq> I" using H by auto
  ultimately show ?thesis using true_cls_mono_set_mset_l by blast
qed

lemma multiset_not_empty:
  assumes "M \<noteq> {#}"
  and "x \<in># M"
  shows "\<exists>A. x = Pos A \<or> x = Neg A"
  using assms literal.exhaust_sel by blast

lemma atms_of_ms_empty:
  fixes \<psi> :: "'v clause_set"
  assumes "atms_of_ms \<psi> = {}"
  shows "\<psi> = {} \<or> \<psi> = {{#}}"
  using assms by (auto simp add: atms_of_ms_def)

lemma consistent_interp_disjoint:
 assumes consI: "consistent_interp I"
 and disj: "atms_of_s A \<inter> atms_of_s I = {}"
 and consA: "consistent_interp A"
 shows "consistent_interp (A \<union> I)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  moreover have "\<And>L. \<not> (L \<in> A \<and> -L \<in> I)"
    using disj unfolding atms_of_s_def by (auto simp add: rev_image_eqI)
  ultimately show False
    using consA consI unfolding consistent_interp_def by (metis (full_types) Un_iff
      literal.exhaust_sel uminus_Neg uminus_Pos)
qed

lemma total_remove_unused:
  assumes "total_over_m I \<psi>"
  shows "total_over_m {v \<in> I. atm_of v \<in> atms_of_ms \<psi>} \<psi>"
  using assms unfolding total_over_m_def total_over_set_def
  by (metis (lifting) literal.sel(1,2) mem_Collect_eq)

lemma true_cls_remove_hd_if_notin_vars:
  assumes "insert a M'\<Turnstile> D"
  and "atm_of a \<notin> atms_of D"
  shows "M' \<Turnstile> D"
  using assms by (auto simp add: atm_of_lit_in_atms_of true_cls_def)

lemma total_over_set_atm_of:
  fixes I :: "'v partial_interp" and K :: "'v set"
  shows "total_over_set I K \<longleftrightarrow> (\<forall>l \<in> K. l \<in> (atm_of ` I))"
  unfolding total_over_set_def by (metis atms_of_s_def in_atms_of_s_decomp)

lemma true_cls_mset_true_clss_iff:
  \<open>finite C \<Longrightarrow> I \<Turnstile>m mset_set C \<longleftrightarrow> I \<Turnstile>s C\<close>
  \<open>I \<Turnstile>m D \<longleftrightarrow> I \<Turnstile>s set_mset D\<close>
  by (auto simp: true_clss_def true_cls_mset_def Ball_def
    dest: multi_member_split)


subsubsection \<open>Tautologies\<close>

text \<open>We define tautologies as clause entailed by every total model and show later that is
  equivalent to containing a literal and its negation.\<close>
definition "tautology (\<psi>:: 'v clause) \<equiv> \<forall>I. total_over_set I (atms_of \<psi>) \<longrightarrow> I \<Turnstile> \<psi>"

lemma tautology_Pos_Neg[intro]:
  assumes "Pos p \<in># A" and "Neg p \<in># A"
  shows "tautology A"
  using assms unfolding tautology_def total_over_set_def true_cls_def Bex_def
  by (meson atm_iff_pos_or_neg_lit true_lit_def)

lemma tautology_minus[simp]:
  assumes "L \<in># A" and "-L \<in># A"
  shows "tautology A"
  by (metis assms literal.exhaust tautology_Pos_Neg uminus_Neg uminus_Pos)

lemma tautology_exists_Pos_Neg:
  assumes "tautology \<psi>"
  shows "\<exists>p. Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>"
proof (rule ccontr)
  assume p: "\<not> (\<exists>p. Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>)"
  let ?I = "{-L | L. L \<in># \<psi>}"
  have "total_over_set ?I (atms_of \<psi>)"
    unfolding total_over_set_def using atm_imp_pos_or_neg_lit by force
  moreover have "\<not> ?I \<Turnstile> \<psi>"
    unfolding true_cls_def true_lit_def Bex_def apply clarify
    using p by (rename_tac x L, case_tac L) fastforce+
  ultimately show False using assms unfolding tautology_def by auto
qed

lemma tautology_decomp:
  "tautology \<psi> \<longleftrightarrow> (\<exists>p. Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>)"
  using tautology_exists_Pos_Neg by auto

lemma tautology_union_add_iff[simp]:
  \<open>tautology (A \<union># B) \<longleftrightarrow> tautology (A + B)\<close>
  by (auto simp: tautology_decomp)
lemma tautology_add_mset_union_add_iff[simp]:
  \<open>tautology (add_mset L (A \<union># B)) \<longleftrightarrow> tautology (add_mset L (A + B))\<close>
  by (auto simp: tautology_decomp)

lemma not_tautology_minus:
  \<open>\<not>tautology A \<Longrightarrow> \<not>tautology (A - B)\<close>
  by (auto simp: tautology_decomp dest: in_diffD)

lemma tautology_false[simp]: "\<not>tautology {#}"
  unfolding tautology_def by auto

lemma tautology_add_mset:
  "tautology (add_mset a L) \<longleftrightarrow> tautology L \<or> -a \<in># L"
  unfolding tautology_decomp by (cases a) auto

lemma tautology_single[simp]: \<open>\<not>tautology {#L#}\<close>
  by (simp add: tautology_add_mset)

lemma tautology_union:
  \<open>tautology (A + B) \<longleftrightarrow> tautology A \<or> tautology B \<or> (\<exists>a. a \<in># A \<and> -a \<in># B)\<close>
  by (metis tautology_decomp tautology_minus uminus_Neg uminus_Pos union_iff)

lemma
  tautology_poss[simp]: \<open>\<not>tautology (poss A)\<close> and
  tautology_negs[simp]: \<open>\<not>tautology (negs A)\<close>
  by (auto simp: tautology_decomp)

lemma tautology_uminus[simp]:
  \<open>tautology (uminus `# w) \<longleftrightarrow> tautology w\<close>
  by (auto 5 5 simp: tautology_decomp add_mset_eq_add_mset eq_commute[of \<open>Pos _\<close> \<open>-_\<close>]
     eq_commute[of \<open>Neg _\<close> \<open>-_\<close>]
    simp flip: uminus_lit_swap
    dest!: multi_member_split)

lemma minus_interp_tautology:
  assumes "{-L | L. L\<in># \<chi>} \<Turnstile> \<chi>"
  shows "tautology \<chi>"
proof -
  obtain L where "L \<in># \<chi> \<and> -L \<in># \<chi>"
    using assms unfolding true_cls_def by auto
  then show ?thesis using tautology_decomp literal.exhaust uminus_Neg uminus_Pos by metis
qed

lemma remove_literal_in_model_tautology:
  assumes "I \<union> {Pos P} \<Turnstile> \<phi>"
  and "I \<union> {Neg P} \<Turnstile> \<phi>"
  shows "I \<Turnstile> \<phi> \<or> tautology \<phi>"
  using assms unfolding true_cls_def by auto

lemma tautology_imp_tautology:
  fixes \<chi> \<chi>' :: "'v clause"
  assumes "\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> \<chi>'" and "tautology \<chi>"
  shows "tautology \<chi>'" unfolding tautology_def
proof (intro allI HOL.impI)
  fix I ::"'v literal set"
  assume totI: "total_over_set I (atms_of \<chi>')"
  let ?I' = "{Pos v |v. v\<in> atms_of \<chi> \<and> v \<notin> atms_of_s I}"
  have totI': "total_over_m (I \<union> ?I') {\<chi>}" unfolding total_over_m_def total_over_set_def by auto
  then have \<chi>: "I \<union> ?I' \<Turnstile> \<chi>" using assms(2) unfolding total_over_m_def tautology_def by simp
  then have "I \<union> (?I'- I) \<Turnstile> \<chi>'" using assms(1) totI' by auto
  moreover have "\<And>L. L \<in># \<chi>' \<Longrightarrow> L \<notin> ?I'"
    using totI unfolding total_over_set_def by (auto dest: pos_lit_in_atms_of)
  ultimately show "I \<Turnstile> \<chi>'" unfolding true_cls_def by auto
qed

lemma not_tautology_mono: \<open>D' \<subseteq># D \<Longrightarrow> \<not>tautology D \<Longrightarrow> \<not>tautology D'\<close>
  by (meson tautology_imp_tautology true_cls_add_mset true_cls_mono_leD)

lemma tautology_decomp':
  \<open>tautology C \<longleftrightarrow> (\<exists>L. L \<in># C \<and> - L \<in># C)\<close>
  unfolding tautology_decomp
  apply auto
  apply (case_tac L)
   apply auto
  done

lemma consistent_interp_tautology:
  \<open>consistent_interp (set M') \<longleftrightarrow> \<not>tautology (mset M')\<close>
  by (auto simp: consistent_interp_def tautology_decomp lit_in_set_iff_atm)

lemma consistent_interp_tuatology_mset_set:
  \<open>finite x \<Longrightarrow> consistent_interp x  \<longleftrightarrow> \<not>tautology (mset_set x)\<close>
  using ex_mset[of \<open>mset_set x\<close>]
  by (auto simp: consistent_interp_tautology eq_commute[of \<open>mset _\<close>] mset_set_eq_mset_iff
      mset_set_set)

lemma tautology_distinct_atm_iff:
  \<open>distinct_mset C \<Longrightarrow> tautology C \<longleftrightarrow> \<not>distinct_mset (atm_of `# C)\<close>
  by (induction C)
    (auto simp: tautology_add_mset atm_of_eq_atm_of
      dest: multi_member_split)

lemma not_tautology_minusD:
  \<open>tautology (A - B) \<Longrightarrow> tautology A\<close>
  by (auto simp: tautology_decomp dest: in_diffD)

lemma tautology_length_ge2: \<open>tautology C \<Longrightarrow> size C \<ge> 2\<close>
  by (auto simp: tautology_decomp add_mset_eq_add_mset dest!: multi_member_split)

lemma tautology_add_subset: \<open>A \<subseteq># Aa \<Longrightarrow> tautology (A + Aa) \<longleftrightarrow> tautology Aa\<close> for A Aa
  by (metis mset_subset_eqD subset_mset.add_diff_inverse tautology_minus tautology_union)



subsubsection \<open>Entailment for clauses and propositions\<close>

text \<open>We also need entailment of clauses by other clauses.\<close>
definition true_cls_cls :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>f" 49) where
"\<psi> \<Turnstile>f \<chi> \<longleftrightarrow> (\<forall>I. total_over_m I ({\<psi>} \<union> {\<chi>}) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile> \<psi> \<longrightarrow> I \<Turnstile> \<chi>)"

definition true_cls_clss :: "'a clause \<Rightarrow> 'a clause_set \<Rightarrow> bool" (infix "\<Turnstile>fs" 49) where
"\<psi> \<Turnstile>fs \<chi> \<longleftrightarrow> (\<forall>I. total_over_m I ({\<psi>} \<union> \<chi>) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile> \<psi> \<longrightarrow> I \<Turnstile>s \<chi>)"

definition true_clss_cls :: "'a clause_set \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>p" 49) where
"N \<Turnstile>p \<chi> \<longleftrightarrow> (\<forall>I. total_over_m I (N \<union> {\<chi>}) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile> \<chi>)"

definition true_clss_clss :: "'a clause_set \<Rightarrow> 'a clause_set \<Rightarrow> bool" (infix "\<Turnstile>ps" 49) where
"N \<Turnstile>ps N' \<longleftrightarrow> (\<forall>I. total_over_m I (N \<union> N') \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile>s N')"

lemma true_cls_cls_refl[simp]:
  "A \<Turnstile>f A"
  unfolding true_cls_cls_def by auto

lemma true_clss_cls_empty_empty[iff]:
  \<open>{} \<Turnstile>p {#} \<longleftrightarrow> False\<close>
  unfolding true_clss_cls_def consistent_interp_def by auto

lemma true_cls_cls_insert_l[simp]:
  "a \<Turnstile>f C \<Longrightarrow> insert a A \<Turnstile>p C"
  unfolding true_cls_cls_def true_clss_cls_def true_clss_def by fastforce

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

text \<open>This version of @{thm true_clss_cls_subset} is useful as intro rule.\<close>
lemma (in -)true_clss_cls_subsetI: \<open>I \<Turnstile>p A \<Longrightarrow> I \<subseteq> I' \<Longrightarrow> I' \<Turnstile>p A\<close>
  by (simp add: true_clss_cls_subset)

lemma true_clss_cs_mono_l[simp]:
  "A \<Turnstile>p CC \<Longrightarrow> A \<union> B \<Turnstile>p CC"
  by (auto intro: true_clss_cls_subset)

lemma true_clss_cs_mono_l2[simp]:
  "B \<Turnstile>p CC \<Longrightarrow> A \<union> B \<Turnstile>p CC"
  by (auto intro: true_clss_cls_subset)

lemma true_clss_cls_mono_r[simp]:
  "A \<Turnstile>p CC \<Longrightarrow> A \<Turnstile>p CC + CC'"
  unfolding true_clss_cls_def total_over_m_union total_over_m_sum by blast

lemma true_clss_cls_mono_r'[simp]:
  "A \<Turnstile>p CC' \<Longrightarrow> A \<Turnstile>p CC + CC'"
  unfolding true_clss_cls_def total_over_m_union total_over_m_sum by blast

lemma true_clss_cls_mono_add_mset[simp]:
  "A \<Turnstile>p CC \<Longrightarrow> A \<Turnstile>p add_mset L CC"
   using true_clss_cls_mono_r[of A CC "add_mset L {#}"] by simp

lemma true_clss_clss_union_l[simp]:
  "A \<Turnstile>ps CC \<Longrightarrow> A \<union> B \<Turnstile>ps CC"
  unfolding true_clss_clss_def total_over_m_union by fastforce

lemma true_clss_clss_union_l_r[simp]:
  "B \<Turnstile>ps CC \<Longrightarrow> A \<union> B \<Turnstile>ps CC"
  unfolding true_clss_clss_def total_over_m_union by fastforce

lemma true_clss_cls_in[simp]:
  "CC \<in> A \<Longrightarrow> A \<Turnstile>p CC"
  unfolding true_clss_cls_def true_clss_def total_over_m_union by fastforce

lemma true_clss_cls_insert_l[simp]:
  "A \<Turnstile>p C \<Longrightarrow> insert a A \<Turnstile>p C"
  unfolding true_clss_cls_def true_clss_def using total_over_m_union
  by (metis Un_iff insert_is_Un sup.commute)

lemma true_clss_clss_insert_l[simp]:
  "A \<Turnstile>ps C \<Longrightarrow> insert a A \<Turnstile>ps C"
  unfolding true_clss_cls_def true_clss_clss_def true_clss_def by blast

lemma true_clss_clss_union_and[iff]:
  "A \<Turnstile>ps C \<union> D \<longleftrightarrow> (A \<Turnstile>ps C \<and> A \<Turnstile>ps D)"
proof
  {
    fix A C D :: "'a clause_set"
    assume A: "A \<Turnstile>ps C \<union> D"
    have "A \<Turnstile>ps C"
        unfolding true_clss_clss_def true_clss_cls_def insert_def total_over_m_insert
      proof (intro allI impI)
        fix I
        assume
          totAC: "total_over_m I (A \<union> C)" and
          cons: "consistent_interp I" and
          I: "I \<Turnstile>s A"
        then have tot: "total_over_m I A" and tot': "total_over_m I C" by auto
        obtain I' where
          tot': "total_over_m (I \<union> I') (A \<union> C \<union> D)" and
          cons': "consistent_interp (I \<union> I')" and
          H: "\<forall>x\<in>I'. atm_of x \<in> atms_of_ms D \<and> atm_of x \<notin> atms_of_ms (A \<union> C)"
          using total_over_m_consistent_extension[OF _ cons, of "A \<union> C"] tot tot' by blast
        moreover have "I \<union> I' \<Turnstile>s A" using I by simp
        ultimately have "I \<union> I' \<Turnstile>s C \<union> D" using A unfolding true_clss_clss_def by auto
        then have "I \<union> I' \<Turnstile>s C \<union> D" by auto
        then show "I \<Turnstile>s C" using notin_vars_union_true_clss_true_clss[of I'] H by auto
      qed
   } note H = this
  assume "A \<Turnstile>ps C \<union> D"
  then show "A \<Turnstile>ps C \<and> A \<Turnstile>ps D" using H[of A] Un_commute[of C D] by metis
next
  assume "A \<Turnstile>ps C \<and> A \<Turnstile>ps D"
  then show "A \<Turnstile>ps C \<union> D"
    unfolding true_clss_clss_def by auto
qed

lemma true_clss_clss_insert[iff]:
  "A \<Turnstile>ps insert L Ls \<longleftrightarrow> (A \<Turnstile>p L \<and> A \<Turnstile>ps Ls)"
  using true_clss_clss_union_and[of A "{L}" "Ls"] by auto

lemma true_clss_clss_subset:
  "A \<subseteq> B \<Longrightarrow> A \<Turnstile>ps CC \<Longrightarrow> B \<Turnstile>ps CC"
  by (metis subset_Un_eq true_clss_clss_union_l)

text \<open>Better suited as intro rule:\<close>
lemma true_clss_clss_subsetI:
  "A \<Turnstile>ps CC \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<Turnstile>ps CC"
  by (metis subset_Un_eq true_clss_clss_union_l)

lemma union_trus_clss_clss[simp]: "A \<union> B \<Turnstile>ps B"
  unfolding true_clss_clss_def by auto

lemma true_clss_clss_remove[simp]:
  "A \<Turnstile>ps B \<Longrightarrow> A \<Turnstile>ps B - C"
  by (metis Un_Diff_Int true_clss_clss_union_and)

lemma true_clss_clss_subsetE:
  "N \<Turnstile>ps B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> N \<Turnstile>ps A"
  by (metis sup.orderE true_clss_clss_union_and)

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

lemma true_clss_clss_generalise_true_clss_clss:
  "A \<union> C \<Turnstile>ps D \<Longrightarrow> B \<Turnstile>ps C \<Longrightarrow> A \<union> B \<Turnstile>ps D"
proof -
  assume a1: "A \<union> C \<Turnstile>ps D"
  assume "B \<Turnstile>ps C"
  then have f2: "\<And>M. M \<union> B \<Turnstile>ps C"
    by (meson true_clss_clss_union_l_r)
  have "\<And>M. C \<union> (M \<union> A) \<Turnstile>ps D"
    using a1 by (simp add: Un_commute sup_left_commute)
  then show ?thesis
    using f2 by (metis (no_types) Un_commute true_clss_clss_left_right true_clss_clss_union_and)
qed

lemma true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or:
  assumes D: "N \<Turnstile>p add_mset (-L) D"
  and C: "N \<Turnstile>p add_mset L C"
  shows "N \<Turnstile>p D + C"
  unfolding true_clss_cls_def
proof (intro allI impI)
  fix I
  assume
    tot: "total_over_m I (N \<union> {D + C})" and
    "consistent_interp I" and
    "I \<Turnstile>s N"
  {
    assume L: "L \<in> I \<or> -L \<in> I"
    then have "total_over_m I {D + {#- L#}}"
      using tot by (cases L) auto
    then have "I \<Turnstile> D + {#- L#}" using D \<open>I \<Turnstile>s N\<close> tot \<open>consistent_interp I\<close>
      unfolding true_clss_cls_def by auto
    moreover
      have "total_over_m I {C + {#L#}}"
        using L tot by (cases L) auto
      then have "I \<Turnstile> C + {#L#}"
        using C \<open>I \<Turnstile>s N\<close> tot \<open>consistent_interp I\<close> unfolding true_clss_cls_def by auto
    ultimately have "I \<Turnstile> D + C" using \<open>consistent_interp I\<close> consistent_interp_def by fastforce
  }
  moreover {
    assume L: "L \<notin> I \<and> -L \<notin> I"
    let ?I' = "I \<union> {L}"
    have "consistent_interp ?I'" using L \<open>consistent_interp I\<close> by auto
    moreover have "total_over_m ?I' {add_mset (-L) D}"
      using tot unfolding total_over_m_def total_over_set_def by (auto simp add: atms_of_def)
    moreover have "total_over_m ?I' N" using tot using total_union by blast
    moreover have "?I' \<Turnstile>s N" using \<open>I \<Turnstile>s N\<close> using true_clss_union_increase by blast
    ultimately have "?I' \<Turnstile> add_mset (-L) D"
      using D unfolding true_clss_cls_def by blast
    then have "?I' \<Turnstile> D" using L by auto
    moreover
      have "total_over_set I (atms_of (D + C))" using tot by auto
      then have "L \<notin># D \<and> -L \<notin># D"
        using L unfolding total_over_set_def atms_of_def by (cases L) force+
    ultimately have "I \<Turnstile> D + C" unfolding true_cls_def by auto
  }
  ultimately show "I \<Turnstile> D + C" by blast
qed

lemma true_cls_union_mset[iff]: "I \<Turnstile> C \<union># D \<longleftrightarrow> I \<Turnstile> C \<or> I \<Turnstile> D"
  unfolding true_cls_def by force

lemma true_clss_cls_sup_iff_add: "N \<Turnstile>p C \<union># D \<longleftrightarrow> N \<Turnstile>p C + D"
  by (auto simp: true_clss_cls_def)

lemma true_clss_cls_union_mset_true_clss_cls_or_not_true_clss_cls_or:
  assumes
    D: "N \<Turnstile>p add_mset (-L) D" and
    C: "N \<Turnstile>p add_mset L C"
  shows "N \<Turnstile>p D \<union># C"
  using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF assms]
  by (subst true_clss_cls_sup_iff_add)


lemma true_clss_cls_tautology_iff:
  \<open>{} \<Turnstile>p a \<longleftrightarrow> tautology a\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then have H: \<open>total_over_set I (atms_of a) \<Longrightarrow> consistent_interp I \<Longrightarrow> I \<Turnstile> a\<close> for I
    by (auto simp: true_clss_cls_def tautology_decomp add_mset_eq_add_mset
      dest!: multi_member_split)
  show ?B
    unfolding tautology_def
  proof (intro allI impI)
    fix I
    assume tot: \<open>total_over_set I (atms_of a)\<close>
    let ?Iinter = \<open>I \<inter> uminus ` I\<close>
    let ?I = \<open>I - ?Iinter \<union> Pos ` atm_of ` ?Iinter\<close>
    have \<open>total_over_set ?I (atms_of a)\<close>
      using tot by (force simp: total_over_set_def image_image Clausal_Logic.uminus_lit_swap
        simp: image_iff)
    moreover have \<open>consistent_interp ?I\<close>
      unfolding consistent_interp_def image_iff
      apply clarify
      subgoal for L
        apply (cases L)
        apply (auto simp: consistent_interp_def uminus_lit_swap image_iff)
	apply (case_tac xa; auto; fail)+
	done
      done
    ultimately have \<open>?I \<Turnstile> a\<close>
      using H[of ?I] by fast
    moreover have \<open>?I \<subseteq> I\<close>
      apply (rule)
      subgoal for x by (cases x; auto; rename_tac xb; case_tac xb; auto)
      done
    ultimately show \<open>I \<Turnstile> a\<close>
      by (blast intro: true_cls_mono_set_mset_l)
  qed
next
  assume ?B
  then show \<open>?A\<close>
    by (auto simp: true_clss_cls_def tautology_decomp add_mset_eq_add_mset
      dest!: multi_member_split)
qed

lemma true_cls_mset_empty_iff[simp]: \<open>{} \<Turnstile>m C \<longleftrightarrow> C = {#}\<close>
  by (cases C)  auto

lemma true_clss_mono_left:
  \<open>I \<Turnstile>s A \<Longrightarrow> I \<subseteq> J \<Longrightarrow> J \<Turnstile>s A\<close>
  by (metis sup.orderE true_clss_union_increase')

lemma true_cls_remove_alien:
  \<open>I \<Turnstile> N \<longleftrightarrow> {L. L \<in> I \<and> atm_of L \<in> atms_of N} \<Turnstile> N\<close>
  by (auto simp: true_cls_def dest: multi_member_split)

lemma true_clss_remove_alien:
  \<open>I \<Turnstile>s N \<longleftrightarrow> {L. L \<in> I \<and> atm_of L \<in> atms_of_ms N} \<Turnstile>s N\<close>
  by (auto simp: true_clss_def true_cls_def in_implies_atm_of_on_atms_of_ms
    dest: multi_member_split)

lemma true_clss_alt_def:
  \<open>N \<Turnstile>p \<chi> \<longleftrightarrow>
    (\<forall>I. atms_of_s I = atms_of_ms (N \<union> {\<chi>}) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile> \<chi>)\<close>
  apply (rule iffI)
  subgoal
    unfolding total_over_set_alt_def true_clss_cls_def total_over_m_alt_def
    by auto
  subgoal
    unfolding total_over_set_alt_def true_clss_cls_def total_over_m_alt_def
    apply (intro conjI impI allI)
    subgoal for I
      using consistent_interp_subset[of \<open>{L \<in> I. atm_of L \<in> atms_of_ms (N \<union> {\<chi>})}\<close> I]
      true_clss_mono_left[of  \<open>{L \<in> I. atm_of L \<in> atms_of_ms N}\<close> N
         \<open>{L \<in> I. atm_of L \<in> atms_of_ms (N \<union> {\<chi>})}\<close>]
      true_clss_remove_alien[of I N]
    by (drule_tac x = \<open>{L \<in> I. atm_of L \<in> atms_of_ms (N \<union> {\<chi>})}\<close> in spec)
      (auto dest: true_cls_mono_set_mset_l)
    done
  done

lemma true_clss_alt_def2:
  assumes \<open>\<not>tautology \<chi>\<close>
  shows \<open>N \<Turnstile>p \<chi> \<longleftrightarrow> (\<forall>I. atms_of_s I = atms_of_ms N \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile> \<chi>)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof (rule iffI)
  assume ?A
  then have H:
      \<open>\<And>I. atms_of_ms (N \<union> {\<chi>}) \<subseteq> atms_of_s I \<longrightarrow>
	   consistent_interp I \<longrightarrow> I \<Turnstile>s N \<longrightarrow> I \<Turnstile> \<chi>\<close>
    unfolding total_over_set_alt_def total_over_m_alt_def true_clss_cls_def by blast
  show ?B
    unfolding total_over_set_alt_def total_over_m_alt_def true_clss_cls_def
  proof (intro conjI impI allI)
    fix I :: \<open>'a literal set\<close>
    assume
      atms: \<open>atms_of_s I = atms_of_ms N\<close> and
      cons: \<open>consistent_interp I\<close> and
      \<open>I \<Turnstile>s N\<close>
    let ?I1 = \<open>I \<union> uminus ` {L \<in> set_mset \<chi>. atm_of L \<notin> atms_of_s I}\<close>
    have \<open>atms_of_ms (N \<union> {\<chi>}) \<subseteq> atms_of_s ?I1\<close>
      by (auto simp add: atms in_image_uminus_uminus atm_iff_pos_or_neg_lit)
    moreover have \<open>consistent_interp ?I1\<close>
      using cons assms by (auto simp: consistent_interp_def)
        (rename_tac x; case_tac x; auto; fail)+
    moreover have \<open>?I1 \<Turnstile>s N\<close>
      using \<open>I \<Turnstile>s N\<close> by auto
    ultimately have \<open>?I1 \<Turnstile> \<chi>\<close>
      using H[of ?I1] by auto
    then show \<open>I \<Turnstile> \<chi>\<close>
      using assms by (auto simp: true_cls_def)
  qed
next
  assume ?B
  show ?A
    unfolding total_over_m_alt_def true_clss_alt_def
  proof (intro conjI impI allI)
    fix I :: \<open>'a literal set\<close>
    assume
      atms: \<open>atms_of_s I = atms_of_ms (N \<union> {\<chi>})\<close> and
      cons: \<open>consistent_interp I\<close> and
      \<open>I \<Turnstile>s N\<close>
    let ?I1 = \<open>{L \<in> I. atm_of L \<in> atms_of_ms N}\<close>
    have \<open>atms_of_s ?I1 = atms_of_ms N\<close>
      using atms by (auto simp add: in_image_uminus_uminus atm_iff_pos_or_neg_lit)
    moreover have \<open>consistent_interp ?I1\<close>
      using cons assms by (auto simp: consistent_interp_def)
    moreover have \<open>?I1 \<Turnstile>s N\<close>
      using \<open>I \<Turnstile>s N\<close> by (subst (asm)true_clss_remove_alien)
    ultimately have \<open>?I1 \<Turnstile> \<chi>\<close>
      using \<open>?B\<close> by auto
    then show \<open>I \<Turnstile> \<chi>\<close>
      using assms by (auto simp: true_cls_def)
  qed
qed

lemma true_clss_restrict_iff:
  assumes \<open>\<not>tautology \<chi>\<close>
  shows \<open>N \<Turnstile>p \<chi> \<longleftrightarrow> N \<Turnstile>p {#L \<in># \<chi>. atm_of L \<in> atms_of_ms N#}\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
  apply (subst true_clss_alt_def2[OF assms])
  apply (subst true_clss_alt_def2)
  subgoal using not_tautology_mono[OF _ assms] by (auto dest: not_tautology_minus)
  apply (rule HOL.iff_allI)
  apply (auto 5 5 simp: true_cls_def atms_of_s_def dest!: multi_member_split)
  done


text \<open>This is a slightly restrictive theorem, that encompasses most useful cases.
  The assumption \<^term>\<open>\<not>tautology C\<close> can be removed if the model \<^term>\<open>I\<close> is total
  over the clause.
\<close>
lemma true_clss_cls_true_clss_true_cls:
  assumes \<open>N \<Turnstile>p C\<close>
    \<open>I \<Turnstile>s N\<close> and
    cons: \<open>consistent_interp I\<close> and
    tauto: \<open>\<not>tautology C\<close>
  shows \<open>I \<Turnstile> C\<close>
proof -
  let ?I = \<open>I \<union> uminus ` {L \<in> set_mset C. atm_of L \<notin> atms_of_s I}\<close>
  let ?I2 = \<open>?I \<union> Pos ` {L \<in> atms_of_ms N. L \<notin> atms_of_s ?I}\<close>
  have \<open>total_over_m ?I2 (N \<union> {C})\<close>
    by (auto simp: total_over_m_alt_def atms_of_def in_image_uminus_uminus
      dest!: multi_member_split)
  moreover have \<open>consistent_interp ?I2\<close>
    using cons tauto unfolding consistent_interp_def
    apply (intro allI)
    apply (case_tac L)
    by (auto simp: uminus_lit_swap eq_commute[of \<open>Pos _\<close> \<open>- _\<close>]
      eq_commute[of \<open>Neg _\<close> \<open>- _\<close>])
  moreover have \<open>?I2 \<Turnstile>s N\<close>
    using \<open>I \<Turnstile>s N\<close> by auto
  ultimately have \<open>?I2 \<Turnstile> C\<close>
    using assms(1) unfolding true_clss_cls_def by fast
  then show ?thesis
    using tauto
    by (subst (asm) true_cls_remove_alien)
      (auto simp: true_cls_def in_image_uminus_uminus)
qed


subsection \<open>Subsumptions\<close>

lemma subsumption_total_over_m:
  assumes "A \<subseteq># B"
  shows "total_over_m I {B} \<Longrightarrow> total_over_m I {A}"
  using assms unfolding subset_mset_def total_over_m_def total_over_set_def
  by (auto simp add: mset_subset_eq_exists_conv)

lemma atms_of_replicate_mset_replicate_mset_uminus[simp]:
  "atms_of (D - replicate_mset (count D L) L - replicate_mset (count D (-L)) (-L))
 = atms_of D - {atm_of L}"
  by (auto simp: atm_of_eq_atm_of atms_of_def in_diff_count dest: in_diffD)

lemma subsumption_chained:
  assumes
    "\<forall>I. total_over_m I {D} \<longrightarrow> I \<Turnstile> D \<longrightarrow> I \<Turnstile> \<phi>" and
    "C \<subseteq># D"
  shows "(\<forall>I. total_over_m I {C} \<longrightarrow> I \<Turnstile> C \<longrightarrow> I \<Turnstile> \<phi>) \<or> tautology \<phi>"
  using assms
proof (induct "card {Pos v | v. v \<in> atms_of D \<and> v \<notin> atms_of C}" arbitrary: D
    rule: nat_less_induct_case)
  case 0 note n = this(1) and H = this(2) and incl = this(3)
  then have "atms_of D \<subseteq> atms_of C" by auto
  then have "\<forall>I. total_over_m I {C} \<longrightarrow> total_over_m I {D}"
    unfolding total_over_m_def total_over_set_def by auto
  moreover have "\<forall>I. I \<Turnstile> C \<longrightarrow> I \<Turnstile> D" using incl true_cls_mono_leD by blast
  ultimately show ?case using H by auto
next
  case (Suc n D) note IH = this(1) and card = this(2) and H = this(3) and incl = this(4)
  let ?atms = "{Pos v |v. v \<in> atms_of D \<and> v \<notin> atms_of C}"
  have "finite ?atms" by auto
  then obtain L where L: "L \<in> ?atms"
    using card by (metis (no_types, lifting) Collect_empty_eq card_0_eq mem_Collect_eq
      nat.simps(3))
  let ?D' = "D - replicate_mset (count D L) L - replicate_mset (count D (-L)) (-L)"
  have atms_of_D: "atms_of_ms {D} \<subseteq> atms_of_ms {?D'} \<union> {atm_of L}"
    using atms_of_replicate_mset_replicate_mset_uminus by force

  {
    fix I
    assume "total_over_m I {?D'}"
    then have tot: "total_over_m (I \<union> {L}) {D}"
      unfolding total_over_m_def total_over_set_def using atms_of_D by auto

    assume IDL: "I \<Turnstile> ?D'"
    then have "insert L I \<Turnstile> D" unfolding true_cls_def by (fastforce dest: in_diffD)
    then have "insert L I \<Turnstile> \<phi>" using H tot by auto

    moreover
      have tot': "total_over_m (I \<union> {-L}) {D}"
        using tot unfolding total_over_m_def total_over_set_def by auto
      have "I \<union> {-L} \<Turnstile> D" using IDL unfolding true_cls_def by (force dest: in_diffD)
      then have "I \<union> {-L} \<Turnstile> \<phi>" using H tot' by auto
    ultimately have "I \<Turnstile> \<phi> \<or> tautology \<phi>"
      using L remove_literal_in_model_tautology by force
  } note H' = this

  have "L \<notin># C " and "-L \<notin># C" using L atm_iff_pos_or_neg_lit by force+
  then have C_in_D': "C \<subseteq># ?D'" using \<open>C \<subseteq># D\<close> by (auto simp: subseteq_mset_def not_in_iff)
  have "card {Pos v |v. v \<in> atms_of ?D' \<and> v \<notin> atms_of C} <
    card {Pos v |v. v \<in> atms_of D \<and> v \<notin> atms_of C}"
    using L unfolding atms_of_replicate_mset_replicate_mset_uminus[of D L]
    by (auto intro!: psubset_card_mono)
  then show ?case
    using IH C_in_D' H' unfolding card[symmetric] by blast
qed


subsection \<open>Removing Duplicates\<close>

lemma tautology_remdups_mset[iff]:
  "tautology (remdups_mset C) \<longleftrightarrow> tautology C"
  unfolding tautology_decomp by auto

lemma atms_of_remdups_mset[simp]: "atms_of (remdups_mset C) = atms_of C"
  unfolding atms_of_def by auto

lemma true_cls_remdups_mset[iff]: "I \<Turnstile> remdups_mset C \<longleftrightarrow> I \<Turnstile> C"
  unfolding true_cls_def by auto

lemma true_clss_cls_remdups_mset[iff]: "A \<Turnstile>p remdups_mset C \<longleftrightarrow> A \<Turnstile>p C"
  unfolding true_clss_cls_def total_over_m_def by auto


subsection \<open>Set of all Simple Clauses\<close>

text \<open>A simple clause with respect to a set of atoms is such that
  \<^enum> its atoms are included in the considered set of atoms;
  \<^enum> it is not a tautology;
  \<^enum> it does not contains duplicate literals.

  It corresponds to the clauses that cannot be simplified away in a calculus without considering
  the other clauses.\<close>
definition simple_clss :: "'v set \<Rightarrow> 'v clause set" where
"simple_clss atms = {C. atms_of C \<subseteq> atms \<and> \<not>tautology C \<and> distinct_mset C}"

lemma simple_clss_empty[simp]:
  "simple_clss {} = {{#}}"
  unfolding simple_clss_def by auto

lemma simple_clss_insert:
  assumes "l \<notin> atms"
  shows "simple_clss (insert l atms) =
    ((+) {#Pos l#}) ` (simple_clss atms)
    \<union> ((+) {#Neg l#}) ` (simple_clss atms)
    \<union> simple_clss atms"(is "?I = ?U")
proof (standard; standard)
  fix C
  assume "C \<in> ?I"
  then have
    atms: "atms_of C \<subseteq> insert l atms" and
    taut: "\<not>tautology C" and
    dist: "distinct_mset C"
    unfolding simple_clss_def by auto
  have H: "\<And>x. x \<in># C \<Longrightarrow> atm_of x \<in> insert l atms"
    using atm_of_lit_in_atms_of atms by blast
  consider
      (Add) L where "L \<in># C" and "L = Neg l \<or> L = Pos l"
    | (No) "Pos l \<notin># C" "Neg l \<notin># C"
    by auto
  then show "C \<in> ?U"
    proof cases
      case Add
      then have LCL: "L \<notin># C - {#L#}"
        using dist unfolding distinct_mset_def by (auto simp: not_in_iff)
      have LC: "-L \<notin># C"
        using taut Add by auto
      obtain aa :: 'a where
        f4: "(aa \<in> atms_of (remove1_mset L C) \<longrightarrow> aa \<in> atms) \<longrightarrow> atms_of (remove1_mset L C) \<subseteq> atms"
        by (meson subset_iff)
      obtain ll :: "'a literal" where
        "aa \<notin> atm_of ` set_mset (remove1_mset L C) \<or> aa = atm_of ll \<and> ll \<in># remove1_mset L C"
        by blast
      then have "atms_of (C - {#L#}) \<subseteq> atms"
        using f4 Add LCL LC H unfolding atms_of_def by (metis H in_diffD insertE
          literal.exhaust_sel uminus_Neg uminus_Pos)
      moreover have "\<not> tautology (C - {#L#})"
        using taut by (metis Add(1) insert_DiffM tautology_add_mset)
      moreover have "distinct_mset (C - {#L#})"
        using dist by auto
      ultimately have "(C - {#L#}) \<in> simple_clss atms"
        using Add unfolding simple_clss_def by auto
      moreover have "C = {#L#} + (C - {#L#})"
        using Add by (auto simp: multiset_eq_iff)
      ultimately show ?thesis using Add by blast
    next
      case No
      then have "C \<in> simple_clss atms"
        using taut atms dist unfolding simple_clss_def
        by (auto simp: atm_iff_pos_or_neg_lit split: if_split_asm dest!: H)
      then show ?thesis by blast
    qed
next
  fix C
  assume "C \<in> ?U"
  then consider
      (Add) L C' where "C = {#L#} + C'" and "C' \<in> simple_clss atms" and
        "L = Pos l \<or> L = Neg l"
    | (No) "C \<in> simple_clss atms"
    by auto
  then show "C \<in> ?I"
    proof cases
      case No
      then show ?thesis unfolding simple_clss_def by auto
    next
      case (Add L C') note C' = this(1) and C = this(2) and L = this(3)
      then have
        atms: "atms_of C' \<subseteq> atms" and
        taut: "\<not>tautology C'" and
        dist: "distinct_mset C'"
        unfolding simple_clss_def by auto
      have "atms_of C \<subseteq> insert l atms"
        using atms C' L by auto
      moreover have "\<not> tautology C"
        using taut C' L assms atms by (metis union_mset_add_mset_left add.left_neutral
            neg_lit_in_atms_of pos_lit_in_atms_of subsetCE tautology_add_mset
            uminus_Neg uminus_Pos)
      moreover have "distinct_mset C"
        using dist C' L by (metis union_mset_add_mset_left add.left_neutral assms atms
            distinct_mset_add_mset neg_lit_in_atms_of pos_lit_in_atms_of subsetCE)
      ultimately show ?thesis unfolding simple_clss_def by blast
    qed
qed

lemma simple_clss_finite:
  fixes atms :: "'v set"
  assumes "finite atms"
  shows "finite (simple_clss atms)"
  using assms by (induction rule: finite_induct) (auto simp: simple_clss_insert)

lemma simple_clssE:
  assumes
    "x \<in> simple_clss atms"
  shows "atms_of x \<subseteq> atms \<and> \<not>tautology x \<and> distinct_mset x"
  using assms unfolding simple_clss_def by auto

lemma cls_in_simple_clss:
  shows "{#} \<in> simple_clss s"
  unfolding simple_clss_def by auto

lemma simple_clss_card:
  fixes atms :: "'v set"
  assumes "finite atms"
  shows "card (simple_clss atms) \<le> (3::nat) ^ (card atms)"
  using assms
proof (induct atms rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert l C) note fin = this(1) and l = this(2) and IH = this(3)
  have notin:
    "\<And>C'. add_mset (Pos l) C' \<notin> simple_clss C"
    "\<And>C'. add_mset (Neg l) C' \<notin> simple_clss C"
    using l unfolding simple_clss_def by auto
  have H: "\<And>C' D. {#Pos l#} + C' = {#Neg l#} + D \<Longrightarrow> D \<in> simple_clss C \<Longrightarrow> False"
    proof -
      fix C' D
      assume C'D: "{#Pos l#} + C' = {#Neg l#} + D" and D: "D \<in> simple_clss C"
      then have "Pos l \<in># D"
        by (auto simp: add_mset_eq_add_mset_ne)
      then have "l \<in> atms_of D"
        by (simp add: atm_iff_pos_or_neg_lit)
      then show False using D l unfolding simple_clss_def by auto
    qed
  let ?P = "((+) {#Pos l#}) ` (simple_clss C)"
  let ?N = "((+) {#Neg l#}) ` (simple_clss C)"
  let ?O = "simple_clss C"
  have "card (?P \<union> ?N \<union> ?O) = card (?P \<union> ?N) + card ?O"
    apply (subst card_Un_disjoint)
    using l fin by (auto simp: simple_clss_finite notin)
  moreover have "card (?P \<union> ?N) = card ?P + card ?N"
    apply (subst card_Un_disjoint)
    using l fin H by (auto simp: simple_clss_finite notin)
  moreover
    have "card ?P = card ?O"
      using inj_on_iff_eq_card[of ?O "(+) {#Pos l#}"]
      by (auto simp: fin simple_clss_finite inj_on_def)
  moreover have "card ?N = card ?O"
      using inj_on_iff_eq_card[of ?O "(+) {#Neg l#}"]
      by (auto simp: fin simple_clss_finite inj_on_def)
  moreover have "(3::nat) ^ card (insert l C) = 3 ^ (card C) + 3 ^ (card C) + 3 ^ (card C)"
    using l by (simp add: fin mult_2_right numeral_3_eq_3)
  ultimately show ?case using IH l by (auto simp: simple_clss_insert)
qed

lemma simple_clss_mono:
  assumes incl: "atms \<subseteq> atms'"
  shows "simple_clss atms \<subseteq> simple_clss atms'"
  using assms unfolding simple_clss_def by auto

lemma distinct_mset_not_tautology_implies_in_simple_clss:
  assumes "distinct_mset \<chi>" and "\<not>tautology \<chi>"
  shows "\<chi> \<in> simple_clss (atms_of \<chi>)"
  using assms unfolding simple_clss_def by auto

lemma simplified_in_simple_clss:
  assumes "distinct_mset_set \<psi>" and "\<forall>\<chi> \<in> \<psi>. \<not>tautology \<chi>"
  shows "\<psi> \<subseteq> simple_clss (atms_of_ms \<psi>)"
  using assms unfolding simple_clss_def
  by (auto simp: distinct_mset_set_def atms_of_ms_def)

lemma simple_clss_element_mono:
  \<open>x \<in> simple_clss A \<Longrightarrow> y \<subseteq># x \<Longrightarrow> y \<in> simple_clss A\<close>
  by (auto simp: simple_clss_def atms_of_def intro: distinct_mset_mono
    dest: not_tautology_mono)


subsection \<open>Experiment: Expressing the Entailments as Locales\<close>
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

*   true_lit  \<Turnstile>   'a partial_interp \<Rightarrow> 'a literal \<Rightarrow> bool
*   true_cls  \<Turnstile>l 'a partial_interp \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_clss \<Turnstile>s 'a partial_interp \<Rightarrow> 'a clause_set \<Rightarrow> bool

*   true_annot \<Turnstile>a ann_lits \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_annots \<Turnstile>as ann_lits \<Rightarrow> 'a clause_set \<Rightarrow> bool

Formula version :
*   true_cls_cls \<Turnstile>f 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_cls_clss \<Turnstile>fs 'a clause \<Rightarrow> 'a clause_set \<Rightarrow> bool

*   true_clss_cls \<Turnstile>p 'a clause_set \<Rightarrow> 'a clause \<Rightarrow> bool
\<longrightarrow> true_clss_clss \<Turnstile>ps 'a clause_set \<Rightarrow> 'a clause_set \<Rightarrow> bool
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
  "I \<union> I' \<Turnstile>es \<psi> \<longleftrightarrow> I' \<union> I \<Turnstile>es \<psi>"
  by (simp add: Un_commute)

lemma entails_remove[simp]: "I \<Turnstile>es N \<Longrightarrow> I \<Turnstile>es Set.remove a N"
  by (simp add: entails_def)

lemma entails_remove_minus[simp]: "I \<Turnstile>es N \<Longrightarrow> I \<Turnstile>es N - A"
  by (simp add: entails_def)

end

interpretation true_cls: entail true_cls
  by standard (auto simp add: true_cls_def)


subsection \<open>Entailment to be extended\<close>

text \<open>In some cases we want a more general version of entailment to have for example
  @{term "{} \<Turnstile> {#L, -L#}"}. This is useful when the model we are building might not be total (the
  literal @{term L} might have been definitely removed from the set of clauses), but we still want
  to have a property of entailment considering that theses removed literals are not important.

  We can given a model @{term I} consider all the natural extensions: @{term C} is entailed
  by an extended @{term I}, if for all total extension of @{term I}, this model entails @{term C}.
  \<close>
definition true_clss_ext :: "'a literal set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>sext" 49)
where
"I \<Turnstile>sext N \<longleftrightarrow> (\<forall>J. I \<subseteq> J \<longrightarrow> consistent_interp J \<longrightarrow> total_over_m J N \<longrightarrow> J \<Turnstile>s N)"

lemma true_clss_imp_true_cls_ext:
  "I\<Turnstile>s N \<Longrightarrow> I \<Turnstile>sext N"
  unfolding true_clss_ext_def by (metis sup.orderE true_clss_union_increase')

lemma true_clss_ext_decrease_right_remove_r:
  assumes "I \<Turnstile>sext N"
  shows "I \<Turnstile>sext N - {C}"
  unfolding true_clss_ext_def
proof (intro allI impI)
  fix J
  assume
    "I \<subseteq> J" and
    cons: "consistent_interp J" and
    tot: "total_over_m J (N - {C})"
  let ?J = "J \<union> {Pos (atm_of P)|P. P \<in># C \<and> atm_of P \<notin> atm_of ` J}"
  have "I \<subseteq> ?J" using \<open>I \<subseteq> J\<close> by auto
  moreover have "consistent_interp ?J"
    using cons unfolding consistent_interp_def apply (intro allI)
    by (rename_tac L, case_tac L) (fastforce simp add: image_iff)+
  moreover have "total_over_m ?J N"
    using tot unfolding total_over_m_def total_over_set_def atms_of_ms_def
    apply clarify
    apply (rename_tac l a, case_tac "a \<in> N - {C}")
      apply (auto; fail)
    using atms_of_s_def atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
    by (fastforce simp: atms_of_def)
  ultimately have "?J \<Turnstile>s N"
    using assms unfolding true_clss_ext_def by blast
  then have "?J \<Turnstile>s N - {C}" by auto
  have "{v \<in> ?J. atm_of v \<in> atms_of_ms (N - {C})} \<subseteq> J"
    using tot unfolding total_over_m_def total_over_set_def
    by (auto intro!: rev_image_eqI)
  then show "J \<Turnstile>s N - {C}"
    using true_clss_remove_unused[OF \<open>?J \<Turnstile>s N - {C}\<close>] unfolding true_clss_def
    by (meson true_cls_mono_set_mset_l)
qed

lemma consistent_true_clss_ext_satisfiable:
  assumes "consistent_interp I" and "I \<Turnstile>sext A"
  shows "satisfiable A"
  by (metis Un_empty_left assms satisfiable_carac subset_Un_eq sup.left_idem
    total_over_m_consistent_extension total_over_m_empty true_clss_ext_def)

lemma not_consistent_true_clss_ext:
  assumes "\<not>consistent_interp I"
  shows "I \<Turnstile>sext A"
  by (meson assms consistent_interp_subset true_clss_ext_def)


(*Move in the theories*)
lemma inj_on_Pos: \<open>inj_on Pos A\<close> and
  inj_on_Neg: \<open>inj_on Neg A\<close>
  by (auto simp: inj_on_def)

lemma inj_on_uminus_lit: \<open>inj_on uminus A\<close> for A :: \<open>'a literal set\<close>
  by (auto simp: inj_on_def)

end
