theory Simulation
  imports
    (* Simple_Clause_Learning.SCL_FOL *)
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Superposition_Calculus.Ground_Ordered_Resolution
begin

section \<open>Move to HOL\<close>

syntax
  "_FFilter" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> 'a fset" ("(1{|_ |\<in>| _./ _|})")
translations
  "{|x |\<in>| X. P|}" == "CONST ffilter (\<lambda>x. P) X"

lemma rtranclp_rtranclp_compose_if_right_unique:
  assumes runique: "right_unique R" and "R\<^sup>*\<^sup>* a b" and "R\<^sup>*\<^sup>* a c"
  shows "R\<^sup>*\<^sup>* a b \<and> R\<^sup>*\<^sup>* b c \<or> R\<^sup>*\<^sup>* a c \<and> R\<^sup>*\<^sup>* c b"
  using assms(2,3)
proof (induction b arbitrary: c rule: rtranclp_induct)
  case base
  thus ?case
    by simp
next
  case (step a' b)
  with runique show ?case
    by (metis converse_rtranclpE right_uniqueD rtranclp.rtrancl_into_rtrancl)
qed

lemma right_unique_terminating_rtranclp:
  assumes "right_unique R"
  shows "right_unique (\<lambda>x y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z))"
  unfolding right_unique_def
  using rtranclp_rtranclp_compose_if_right_unique[OF \<open>right_unique R\<close>]
  by (metis converse_rtranclpE)

lemma ex_terminating_rtranclp:
  assumes wf: "wfP R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
proof (cases "\<exists>y. R x y")
  case True
  with wf show ?thesis
    by (induction rule: wfP_induct_rule)
      (metis converse_rtranclp_into_rtranclp conversep_iff r_into_rtranclp)
next
  case False
  thus ?thesis 
    by blast
qed

lemma ex1_subset_eq_image_if_bij_betw:
  fixes f :: "'a \<Rightarrow> 'b" and X :: "'a set" and Y :: "'b set"
  assumes "bij_betw f X Y" and "Y' \<subseteq> Y"
  shows "\<exists>!X'. X' \<subseteq> X \<and> Y' = f ` X'"
  using assms
  by (metis bij_betw_def inv_into_image_cancel subset_image_iff)

lemma Collect_eq_image_filter_Collect_if_bij_betw:
  fixes f :: "'a \<Rightarrow> 'b" and X :: "'a set" and Y :: "'b set"
  assumes bij: "bij_betw f X Y" and sub: "{y. P y} \<subseteq> Y"
  shows "{y. P y} = f ` {x. x \<in> X \<and> P (f x)}"
  using ex1_subset_eq_image_if_bij_betw[OF bij sub]
  by (smt (verit, best) Collect_cong image_def in_mono mem_Collect_eq)

subsection \<open>Minimal, maximal, least, and greatest element of a set\<close>

definition is_minimal_in_set_wrt where
  "is_minimal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R y x))"

definition is_maximal_in_set_wrt where
  "is_maximal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R x y))"

definition is_least_in_set_wrt where
  "is_least_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R x y)"

definition is_greatest_in_set_wrt where
  "is_greatest_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R y x)"


subsubsection \<open>Conversions\<close>

lemma is_minimal_in_set_wrt_conversep[simp]:
  "is_minimal_in_set_wrt R\<inverse>\<inverse> = is_maximal_in_set_wrt R"
  unfolding is_maximal_in_set_wrt_def is_minimal_in_set_wrt_def by simp

lemma is_maximal_in_set_wrt_conversep[simp]:
  "is_maximal_in_set_wrt R\<inverse>\<inverse> = is_minimal_in_set_wrt R"
  unfolding is_maximal_in_set_wrt_def is_minimal_in_set_wrt_def by simp

lemma is_least_set_wrt_conversep[simp]:
  "is_least_in_set_wrt R\<inverse>\<inverse> = is_greatest_in_set_wrt R"
  unfolding is_least_in_set_wrt_def is_greatest_in_set_wrt_def by simp

lemma is_greatest_in_set_wrt_conversep[simp]:
  "is_greatest_in_set_wrt R\<inverse>\<inverse> = is_least_in_set_wrt R"
  unfolding is_least_in_set_wrt_def is_greatest_in_set_wrt_def by simp

lemma is_minimal_in_set_wrt_iff:
  "is_minimal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R y x)"
  unfolding is_minimal_in_set_wrt_def by blast

lemma is_maximal_in_set_wrt_iff:
  "is_maximal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  unfolding is_maximal_in_set_wrt_def by blast

lemma is_least_in_set_wrt_iff:
  "is_least_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R x y)"
  unfolding is_least_in_set_wrt_def by blast

lemma is_greatest_in_set_wrt_iff:
  "is_greatest_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R y x)"
  unfolding is_greatest_in_set_wrt_def
  by blast

lemma is_minimal_in_set_wrt_eq_is_least_in_set_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_minimal_in_set_wrt R X = is_least_in_set_wrt R X"
proof (intro ext iffI)
  fix x
  from tot show "is_minimal_in_set_wrt R X x \<Longrightarrow> is_least_in_set_wrt R X x"
    unfolding is_minimal_in_set_wrt_def is_least_in_set_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  fix x
  from asym show "is_least_in_set_wrt R X x \<Longrightarrow> is_minimal_in_set_wrt R X x"
    unfolding is_least_in_set_wrt_def is_minimal_in_set_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma is_maximal_in_set_wrt_eq_is_greatest_in_set_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_maximal_in_set_wrt R X = is_greatest_in_set_wrt R X"
proof (intro ext iffI)
  fix x
  from tot show "is_maximal_in_set_wrt R X x \<Longrightarrow> is_greatest_in_set_wrt R X x"
    unfolding is_maximal_in_set_wrt_def is_greatest_in_set_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  fix x
  from asym show "is_greatest_in_set_wrt R X x \<Longrightarrow> is_maximal_in_set_wrt R X x"
    unfolding is_maximal_in_set_wrt_def is_greatest_in_set_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma is_minimal_in_set_wrt_filter_iff:
  "is_minimal_in_set_wrt R {y \<in> X. P y} x \<longleftrightarrow> x \<in> X \<and> P x \<and> (\<forall>y \<in> X - {x}. P y \<longrightarrow> \<not> R y x)"
  by (auto simp: is_minimal_in_set_wrt_def)


subsubsection \<open>Existence\<close>

lemma bex_minimal_element:
  "asymp_on A R \<Longrightarrow> transp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. is_minimal_in_set_wrt R A m"
  using Finite_Set.bex_min_element
  by (metis is_minimal_in_set_wrt_iff)

lemma bex_maximal_element:
  "asymp_on A R \<Longrightarrow> transp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. is_maximal_in_set_wrt R A m"
  using Finite_Set.bex_max_element
  by (metis is_maximal_in_set_wrt_iff)

lemma bex_greatest_element:
  "transp_on A R \<Longrightarrow> totalp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>g. is_greatest_in_set_wrt R A g"
  using Finite_Set.bex_greatest_element[of A R]
  by (metis is_greatest_in_set_wrt_iff)

lemma bex_least_element:
  "transp_on A R \<Longrightarrow> totalp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>g. is_least_in_set_wrt R A g"
  using Finite_Set.bex_least_element[of A R]
  by (metis is_least_in_set_wrt_iff)

lemma not_bex_greatest_element_doubleton:
  assumes "x \<noteq> y" and "\<not> R x y" and "\<not> R y x"
  shows "\<nexists>g. is_greatest_in_set_wrt R {x, y} g"
proof (rule notI)
  assume "\<exists>g. is_greatest_in_set_wrt R {x, y} g"
  then obtain g where "is_greatest_in_set_wrt R {x, y} g" ..
  then show False
    unfolding is_greatest_in_set_wrt_def
    using assms(1) assms(2) assms(3) by blast
qed


subsubsection \<open>Uniqueness\<close>

lemma Uniq_is_minimal_in_set_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. is_minimal_in_set_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff is_minimal_in_set_wrt_def totalp_onD)

lemma Uniq_is_maximal_in_set_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. is_maximal_in_set_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff is_maximal_in_set_wrt_def totalp_onD)

lemma Uniq_is_least_in_set_wrt:
  "asymp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. is_least_in_set_wrt R X x"
  by (rule Uniq_I)
    (metis antisymp_onD antisymp_on_if_asymp_on insertE insert_Diff is_least_in_set_wrt_def)

lemma Uniq_is_greatest_in_set_wrt:
  "asymp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. is_greatest_in_set_wrt R X x"
  by (rule Uniq_I)
    (metis antisymp_onD antisymp_on_if_asymp_on insertE insert_Diff is_greatest_in_set_wrt_def)


subsubsection \<open>Function\<close>

definition Greatest_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a option" where
  "Greatest_in_set_wrt R X = (if X = {} then None else Some (THE x. is_greatest_in_set_wrt R X x))"

lemma Greatest_in_set_wrt_empty[simp]: "Greatest_in_set_wrt R {} = None"
  by (simp add: Greatest_in_set_wrt_def)

lemma Greatest_in_set_wrt_singleton[simp]: "Greatest_in_set_wrt R {x} = Some x"
  by (metis (mono_tags, opaque_lifting) Greatest_in_set_wrt_def Uniq_I empty_iff
      is_greatest_in_set_wrt_iff singletonD singletonI the1_equality')

lemma Greatest_in_set_wrt_eq_None[simp]: "Greatest_in_set_wrt R X = None \<longleftrightarrow> X = {}"
  by (simp add: Greatest_in_set_wrt_def)

lemma Greatest_in_set_wrt_eq_Some_if_is_greatest_in_set_wrt:
  assumes asymp: "asymp_on X R"
  shows "is_greatest_in_set_wrt R X x \<Longrightarrow> Greatest_in_set_wrt R X = Some x"
  using the1_equality'[OF Uniq_is_greatest_in_set_wrt[OF asymp]]
  by (metis Greatest_in_set_wrt_def empty_iff is_greatest_in_set_wrt_iff)

lemma is_greatest_in_set_wrt_if_Greatest_in_set_wrt_eq_Some:
  assumes
    trans: "transp_on X R" and
    asym: "asymp_on X R" and
    tot: "totalp_on X R" and
    fin: "finite X" and
    greatest: "Greatest_in_set_wrt R X = Some x"
  shows "is_greatest_in_set_wrt R X x"
proof -
  from greatest have "X \<noteq> {}" and "(THE x. is_greatest_in_set_wrt R X x) = x"
    unfolding atomize_conj Greatest_in_set_wrt_def
    by (metis option.discI option.inject)

  obtain y where "is_greatest_in_set_wrt R X y"
    using bex_greatest_element[OF trans tot fin \<open>X \<noteq> {}\<close>] ..

  moreover have "\<exists>\<^sub>\<le>\<^sub>1x. is_greatest_in_set_wrt R X x"
    using Uniq_is_greatest_in_set_wrt[OF asym] .

  ultimately have "\<exists>!x. is_greatest_in_set_wrt R X x"
    by (intro Uniq_implies_ex1)
  hence "is_greatest_in_set_wrt R X (THE x. is_greatest_in_set_wrt R X x)"
    by (rule theI')
  thus ?thesis
    unfolding \<open>(THE x. is_greatest_in_set_wrt R X x) = x\<close> .
qed

lemma Greatest_in_set_wrt_eq_Some[simp]:
  assumes
    trans: "transp_on X R" and
    asym: "asymp_on X R" and
    tot: "totalp_on X R" and
    fin: "finite X"
  shows "Greatest_in_set_wrt R X = Some x \<longleftrightarrow> is_greatest_in_set_wrt R X x"
  using assms is_greatest_in_set_wrt_if_Greatest_in_set_wrt_eq_Some
    Greatest_in_set_wrt_eq_Some_if_is_greatest_in_set_wrt
  by metis


section \<open>Move to @{theory "HOL-Library.FSet"}\<close>

syntax
  "_FFilter" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> 'a fset" ("(1{|_ |\<in>| _./ _|})")

translations
  "{|x |\<in>| X. P|}" == "CONST ffilter (\<lambda>x. P) X"

abbreviation is_minimal_in_fset_wrt where
  "is_minimal_in_fset_wrt R X \<equiv> is_minimal_in_set_wrt R (fset X)"

abbreviation is_maximal_in_fset_wrt where
  "is_maximal_in_fset_wrt R X \<equiv> is_maximal_in_set_wrt R (fset X)"

abbreviation is_least_in_fset_wrt where
  "is_least_in_fset_wrt R X \<equiv> is_least_in_set_wrt R (fset X)"

abbreviation is_greatest_in_fset_wrt where
  "is_greatest_in_fset_wrt R X \<equiv> is_greatest_in_set_wrt R (fset X)"

lemma is_minimal_in_fset_wrt_ffilter_iff:
  "is_minimal_in_fset_wrt R {|y |\<in>| X. P y|} x \<longleftrightarrow>
    (x |\<in>| X \<and> P x \<and> (\<forall>y|\<in>| X - {|x|}. P y \<longrightarrow> \<not> R y x))"
  using is_minimal_in_set_wrt_filter_iff[of _ "fset _"]
  by (smt (verit, best) bot_fset.rep_eq empty_iff ffmember_filter finsert_iff fminus_iff
      is_minimal_in_set_wrt_iff)

lemma bex_minimal_element_in_fset_wrt:
  "asymp_on (fset X) R \<Longrightarrow> transp_on (fset X) R \<Longrightarrow> X \<noteq> {||} \<Longrightarrow> \<exists>m. is_minimal_in_fset_wrt R X m"
  using bex_minimal_element[of "fset X" R] by auto


section \<open>Move to Superposition_Calculus\<close>

lemma (in ground_ordered_resolution_calculus) unique_ground_resolution:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_resolution P1 P2 C"
proof (intro Uniq_I)
  fix C C'
  assume "ground_resolution P1 P2 C" and "ground_resolution P1 P2 C'"
  thus "C = C'"
    unfolding ground_resolution.simps
    apply (elim exE conjE)
    apply simp
    using Uniq_is_maximal_wrt[OF totalp_on_less_lit]
    using Uniq_is_maximal_wrt_reflclp[OF totalp_on_less_lit]
    by (metis Uniq_D add_mset_add_mset_same_iff literal.inject(1))
qed

lemma (in ground_ordered_resolution_calculus) unique_ground_factoring:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_factoring P C"
proof (intro Uniq_I)
  fix P C C'
  assume "ground_factoring P C" and "ground_factoring P C'"
  thus "C = C'"
    unfolding ground_factoring.simps
    apply (elim exE conjE)
    apply simp
    using Uniq_is_maximal_wrt[OF totalp_on_less_lit]
    by (metis Uniq_D add_mset_add_mset_same_iff)
qed

lemma (in ground_ordered_resolution_calculus) termination_ground_factoring:
  "wfP ground_factoring\<inverse>\<inverse>"
proof (rule wfP_if_convertible_to_wfP)
  show "\<And>x y. ground_factoring\<inverse>\<inverse> x y \<Longrightarrow> x \<prec>\<^sub>c y"
    using ground_factoring_smaller_conclusion by simp
next
  show "wfP (\<prec>\<^sub>c)"
    by simp
qed


section \<open>Move somewhere?\<close>

definition Max_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a option" where
  "Max_mset_wrt R M = (if M = {#} then None else Some (THE x. is_maximal_wrt R x M))"

lemma Max_mset_wrt_eq_None[simp]: "Max_mset_wrt R M = None \<longleftrightarrow> M = {#}"
  by (simp add: Max_mset_wrt_def)

lemma Max_mset_wrt_eq_Some_if_is_maximal_wrt:
  assumes tot: "totalp_on (set_mset M) R"
  shows "is_maximal_wrt R x M \<Longrightarrow> Max_mset_wrt R M = Some x"
  using the1_equality'[OF Uniq_is_maximal_wrt[OF tot]]
  by (metis Max_mset_wrt_def empty_iff is_maximal_wrt_def set_mset_empty)

lemma is_maximal_wrt_if_Max_mset_wrt_eq_Some:
  assumes
    trans: "transp_on (set_mset M) R" and
    asym: "asymp_on (set_mset M) R" and
    tot: "totalp_on (set_mset M) R" and
    max: "Max_mset_wrt R M = Some x"
  shows "is_maximal_wrt R x M"
proof -
  from max have "M \<noteq> {#}" and "(THE x. is_maximal_wrt R x M) = x"
    unfolding atomize_conj Max_mset_wrt_def
    by (metis option.discI option.inject)

  obtain y where "is_maximal_wrt R y M"
    using ex_is_maximal_wrt_if_not_empty[OF trans asym \<open>M \<noteq> {#}\<close>] by metis

  moreover have "\<exists>\<^sub>\<le>\<^sub>1L. is_maximal_wrt R L M"
    using Uniq_is_maximal_wrt[OF tot] by assumption

  ultimately have "\<exists>!L. is_maximal_wrt R L M"
    by (intro Uniq_implies_ex1)
  hence "is_maximal_wrt R (THE x. is_maximal_wrt R x M) M"
    by (rule theI')
  thus ?thesis
    unfolding \<open>(THE x. is_maximal_wrt R x M) = x\<close>
    by assumption
qed

lemma Max_mset_wrt_eq_Some[simp]:
  assumes
    trans: "transp_on (set_mset M) R" and
    asym: "asymp_on (set_mset M) R" and
    tot: "totalp_on (set_mset M) R"
  shows "Max_mset_wrt R M = Some x \<longleftrightarrow> is_maximal_wrt R x M"
  using assms Max_mset_wrt_eq_Some_if_is_maximal_wrt is_maximal_wrt_if_Max_mset_wrt_eq_Some
  by metis


lemma ground_iff_vars_term_empty: "ground t \<longleftrightarrow> vars_term t = {}"
proof (rule iffI)
  show "ground t \<Longrightarrow> vars_term t = {}"
    by (rule ground_vars_term_empty)
next
  show "vars_term t = {} \<Longrightarrow> ground t"
    by (induction t) simp_all
qed

lemma is_ground_atm_eq_ground[iff]: "is_ground_atm = ground"
proof (rule ext)
  fix t :: "('v, 'f) Term.term"
  show "is_ground_atm t = ground t"
    by (simp only: is_ground_atm_iff_vars_empty ground_iff_vars_term_empty)
qed

definition lit_of_glit where
  "lit_of_glit = map_literal term_of_gterm"

definition glit_of_lit where
  "glit_of_lit = map_literal gterm_of_term"

definition cls_of_gcls where
  "cls_of_gcls = image_mset lit_of_glit"

definition gcls_of_cls where
  "gcls_of_cls = image_mset glit_of_lit"

lemma inj_lit_of_glit: "inj lit_of_glit"
proof (rule injI)
  fix L K
  show "lit_of_glit L = lit_of_glit K \<Longrightarrow> L = K"
    by (metis lit_of_glit_def literal.expand literal.map_disc_iff literal.map_sel term_of_gterm_inv)
qed

lemma atm_of_lit_of_glit_conv: "atm_of (lit_of_glit L) = term_of_gterm (atm_of L)"
  by (cases L) (simp_all add: lit_of_glit_def)

lemma is_ground_lit_lit_of_glit[simp]: "is_ground_lit (lit_of_glit L)"
  by (simp add: is_ground_lit_def atm_of_lit_of_glit_conv)

lemma lit_of_glit_glit_of_lit_ident[simp]: "is_ground_lit L \<Longrightarrow> lit_of_glit (glit_of_lit L) = L"
  by (simp add: is_ground_lit_def lit_of_glit_def glit_of_lit_def literal.map_comp literal.expand
      literal.map_sel)

lemma cls_of_gcls_gcls_of_cls_ident[simp]: "is_ground_cls D \<Longrightarrow> cls_of_gcls (gcls_of_cls D) = D"
  by (simp add: is_ground_cls_def cls_of_gcls_def gcls_of_cls_def)

definition atms_of_clss where
  "atms_of_clss N = (\<Union>C \<in> N. atms_of C)"

definition lit_occures_in_clss where
  "lit_occures_in_clss L N \<longleftrightarrow> fBex N (\<lambda>C. L \<in># C)"


section \<open>Simulation\<close>

type_synonym ('f, 'v) scl_fol_sim_state =
  "('f, 'v) SCL_FOL.state \<times> nat \<times> 'f gterm clause \<times> ('f gterm clause \<Rightarrow> 'f gterm clause)"

locale simulation_SCLFOL_ground_ordered_resolution =
  renaming_apart renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    finite_less_trm: "\<And>\<beta>. finite {x. x \<prec>\<^sub>t \<beta>}" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
begin

subsection \<open>Ground ordered resolution for ground terms\<close>

interpretation ord_res: ground_ordered_resolution_calculus "(\<prec>\<^sub>t)" "\<lambda>_. {#}"
  by unfold_locales auto

interpretation linorder_trm: linorder "(\<preceq>\<^sub>t)" "(\<prec>\<^sub>t)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>t y) = (x \<preceq>\<^sub>t y \<and> \<not> y \<preceq>\<^sub>t x)"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>t x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t z \<Longrightarrow> x \<preceq>\<^sub>t z"
    by (meson transpE transp_less_trm transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<or> y \<preceq>\<^sub>t x"
    by (metis reflclp_iff totalpD totalp_less_trm)
qed

interpretation linorder_lit: linorder "(\<preceq>\<^sub>l)" "(\<prec>\<^sub>l)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = (x \<preceq>\<^sub>l y \<and> \<not> y \<preceq>\<^sub>l x)"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>l x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l z \<Longrightarrow> x \<preceq>\<^sub>l z"
    by (meson transpE ord_res.transp_less_lit transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_lit)
qed

interpretation linorder_cls: linorder "(\<preceq>\<^sub>c)" "(\<prec>\<^sub>c)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = (x \<preceq>\<^sub>c y \<and> \<not> y \<preceq>\<^sub>c x)"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>c x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c z \<Longrightarrow> x \<preceq>\<^sub>c z"
    by (meson transpE ord_res.transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_cls)
qed

subsection \<open>Lemmas about going between ground and first-order terms\<close>

lemma ex1_gterm_of_term:
  fixes t :: "'f gterm"
  shows "\<exists>!(t' :: ('f, 'v) term). ground t' \<and> t = gterm_of_term t'"
proof (rule ex1I)
  show "ground (term_of_gterm t) \<and> t = gterm_of_term (term_of_gterm t)"
    by simp
next
  fix t' :: "('f, 'v) term"
  show "ground t' \<and> t = gterm_of_term t' \<Longrightarrow> t' = term_of_gterm t"
    by (induction t') (simp_all add: map_idI)
qed

lemma binj_betw_gterm_of_term: "bij_betw gterm_of_term {t. ground t} UNIV"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on gterm_of_term {t. ground t}"
    by (metis gterm_of_term_inj mem_Collect_eq)
next
  show "gterm_of_term ` {t. ground t} = UNIV"
  proof (rule Set.subset_antisym)
    show "gterm_of_term ` {t. Term_Context.ground t} \<subseteq> UNIV"
      by simp
  next
    show "UNIV \<subseteq> gterm_of_term ` {t. Term_Context.ground t}"
      by (metis (mono_tags, opaque_lifting) ground_term_of_gterm image_iff mem_Collect_eq subsetI
          term_of_gterm_inv)
  qed
qed


subsection \<open>SCL(FOL) for first-order terms\<close>

interpretation scl_fol: scl_fol_calculus renaming_vars
  "\<lambda>x y. ground x \<and> ground y \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term y"
proof unfold_locales
  fix \<beta> :: "('f, 'v) term"

  have Collect_gterms_eq: "\<And>P. {y. P y} = gterm_of_term ` {t. ground t \<and> P (gterm_of_term t)}"
    using Collect_eq_image_filter_Collect_if_bij_betw[OF binj_betw_gterm_of_term subset_UNIV]
    by auto

  have "{t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>} = gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using Collect_gterms_eq[of "\<lambda>t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>"] .
  hence "finite (gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>})"
    using finite_less_trm[of "gterm_of_term \<beta>"] by metis
  moreover have "inj_on gterm_of_term {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    by (rule gterm_of_term_inj) simp
  ultimately have "finite {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using finite_imageD by blast
  thus "finite {x. ground x \<and> ground \<beta> \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using not_finite_existsD by force
qed


subsection \<open>Strategy for ground ordered resolution\<close>

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

definition is_min_false_clause :: "'f gterm clause fset \<Rightarrow> 'f gterm clause \<Rightarrow> bool" where
  "is_min_false_clause N C \<longleftrightarrow>
    is_minimal_in_fset_wrt (\<prec>\<^sub>c)
      {|C |\<in>| N. \<not> (\<Union>D \<in> {D \<in> fset N. D \<preceq>\<^sub>c C}. ord_res.production (fset N) D) \<TTurnstile> C|} C"

definition ord_res_mod_op_strategy :: "'f gterm clause fset \<Rightarrow> 'f gterm clause fset \<Rightarrow> bool" where
  "ord_res_mod_op_strategy N N' \<longleftrightarrow> (\<exists>C L.
    is_min_false_clause N C \<and> ord_res.is_maximal_lit L C \<and>
      (case L of
        Neg A \<Rightarrow> \<comment> \<open>Case 3\<close>
        fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
          (\<exists>CD. ord_res.ground_resolution C D CD \<and> N' = finsert CD N))
      | Pos A \<Rightarrow> \<comment> \<open>Case 4\<close>
        \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
          (\<exists>C'. ord_res.ground_factoring C C')))"

lemma
  assumes
    C_min_false: "is_min_false_clause N C" and
    Neg_A_max: "ord_res.is_maximal_lit (Neg A) C"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D)"
proof -
  from C_min_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C" and
    C_min: "fBall {|C |\<in>| N. \<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C|}
      (\<lambda>y. C \<noteq> y \<longrightarrow> C \<prec>\<^sub>c y)"
    unfolding atomize_conj is_min_false_clause_def
    unfolding is_minimal_in_fset_wrt_ffilter_iff
    by (simp add: linorder_cls.not_less_iff_gr_or_eq)

  from C_false have "\<nexists>A. A \<in> ord_res.production (fset N) C"
    apply (intro notI)
    apply (elim exE)
    by (metis (no_types, lifting) SUP_absorb UnI1 is_maximal_wrt_def linorder_cls.order_eq_iff
        mem_Collect_eq ord_res.mem_productionE pos_literal_in_imp_true_cls)
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  from Neg_A_max have "Neg A \<in># C"
    by (simp add: is_maximal_wrt_def)

  from C_false have "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile>l Neg A"
    using true_cls_if_true_lit_in[OF \<open>Neg A \<in># C\<close>]
    by meson
  hence "A \<in> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C})"
    by simp
  with C_unproductive have "A \<in> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<prec>\<^sub>c C})"
    by blast
  then obtain D where
    D_in: "D |\<in>| N" and D_lt_C: "D \<prec>\<^sub>c C" and D_productive: "A \<in> ord_res.production (fset N) D"
    by auto

  from D_productive have "ord_res.is_strictly_maximal_lit (Pos A) D"
    using ord_res.mem_productionE by metis
  thus ?thesis
    using D_in D_lt_C by metis
qed

lemma
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_in: "D |\<in>| N" and
    D_lt: "D \<prec>\<^sub>c C" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D"
  shows "\<exists>CD. ord_res.ground_resolution C D CD"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Neg A) C'"
    by (meson is_maximal_wrt_def mset_add)

  from D_max_lit obtain D' where D_def: "D = add_mset (Pos A) D'"
    by (meson is_maximal_wrt_def mset_add)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_resolution C D (C' + D')"
      using ord_res.ground_resolutionI[of C A C' D D']
      using C_def D_def D_lt C_max_lit D_max_lit by metis
  qed
qed

lemma
  assumes
    C_min_false: "is_min_false_clause N C" and
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
  shows "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Pos A) C'"
    by (meson is_maximal_wrt_def mset_add)

  from C_min_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C" and
    C_min: "fBall {|C |\<in>| N. \<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C|}
      (\<lambda>y. C \<noteq> y \<longrightarrow> C \<prec>\<^sub>c y)"
    unfolding atomize_conj is_min_false_clause_def
    unfolding is_minimal_in_fset_wrt_ffilter_iff
    by (simp add: linorder_cls.not_less_iff_gr_or_eq)

  from C_false have "\<nexists>A. A \<in> ord_res.production (fset N) C"
    apply (intro notI)
    apply (elim exE)
    by (metis (no_types, lifting) SUP_absorb UnI1 is_maximal_wrt_def linorder_cls.order_eq_iff
        mem_Collect_eq ord_res.mem_productionE pos_literal_in_imp_true_cls)
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  have "{D \<in> fset N. D \<preceq>\<^sub>c C} = {D \<in> fset N. D \<prec>\<^sub>c C} \<union> {D \<in> fset N. D = C}"
    by fastforce
  with C_unproductive have
    "\<Union> (ord_res.production (fset N) ` {D \<in> fset N. D \<preceq>\<^sub>c C}) =
     \<Union> (ord_res.production (fset N) ` {D \<in> fset N. D \<prec>\<^sub>c C})"
    by simp
  with C_false have C_false': "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<prec>\<^sub>c C}) \<TTurnstile> C"
    by simp

  from C_unproductive have "A \<notin> ord_res.production (fset N) C"
    by simp
  thus ?thesis
  proof (rule contrapos_nn)
    assume "ord_res.is_strictly_maximal_lit (Pos A) C"
    then show "A \<in> ord_res.production (fset N) C"
      unfolding ord_res.production.simps[of "fset N" C] mem_Collect_eq
      using C_in C_def C_false' by metis
  qed
qed

lemma
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C" and
    C_not_max_lit: "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
proof -
  from C_max_lit C_not_max_lit have "count C (Pos A) > 1"
    by (simp add: in_diff_count is_maximal_wrt_def)
  then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
    by (metis C_max_lit C_not_max_lit count_greater_zero_iff dual_order.strict_trans insert_DiffM
        less_numeral_extra(1) lift_is_maximal_wrt_to_is_maximal_wrt_reflclp)
  
  show ?thesis
  proof (rule exI)
    show "ord_res.ground_factoring C (add_mset (Pos A) C')"
      using ord_res.ground_factoringI[of C A C']
      using C_def C_max_lit by metis
  qed
qed

subsection \<open>Strategy for SCL(FOL)\<close>

definition sfac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "sfac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

lemma
  shows "sfac C = C \<or> (\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"
proof -
  have "right_unique (\<lambda>x y. ord_res.ground_factoring\<^sup>*\<^sup>* x y \<and> (\<nexists>z. ord_res.ground_factoring y z))"
    using ord_res.unique_ground_factoring right_unique_terminating_rtranclp right_unique_iff
    by blast

  moreover obtain C' where "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex_terminating_rtranclp[OF ord_res.termination_ground_factoring]
    by metis

  ultimately have "sfac C = C'"
    by (simp add: sfac_def right_unique_def the_equality)

  then show ?thesis
    using \<open>ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')\<close> by blast
qed

term "propagate_lit L D Var"
term "trail_propagate \<Gamma> L D' Var"

term "{#K \<in># D. K \<noteq> L#}"
term "ord_res_mod_op_strategy ^^ 2"

inductive scl_reso1 for N\<^sub>0 \<beta> where
  scl_reso1I: "\<F> C \<prec>\<^sub>c \<F> D \<Longrightarrow>
  \<not> fBex (N\<^sub>0 |\<union>| fimage gcls_of_cls U) (\<lambda>D'. \<F> C \<prec>\<^sub>c \<F> D' \<and> \<F> D' \<prec>\<^sub>c \<F> D) \<Longrightarrow>
  D |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U \<Longrightarrow>
  ord_res.is_maximal_lit L D \<Longrightarrow>
  sorted_wrt (\<prec>\<^sub>l) Ks \<Longrightarrow> (\<forall>K \<in> set Ks. is_neg K \<and> K \<prec>\<^sub>l L \<and>
    \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and>
    lit_occures_in_clss K N\<^sub>0) \<Longrightarrow>
  \<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks) \<Longrightarrow>
  S1 = ((\<Gamma>\<^sub>1, U, None :: ('f, 'v) closure option), i, D, \<F>) \<Longrightarrow>
  (ord_res_mod_op_strategy ^^ i) N\<^sub>0 N\<^sub>i \<Longrightarrow>
  \<F> D |\<in>| N\<^sub>i \<Longrightarrow>
  sfac D = sfac (\<F> D) \<Longrightarrow>
  \<F> D = add_mset L D' \<Longrightarrow>
  S2 =
    (let
      \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
      \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls (sfac D - {#L#})) Var;
      E = (THE x. is_least_in_fset_wrt (\<prec>\<^sub>c)
        {|C |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} x);
      j\<^sub>0 = count D' L;
      j = i + j\<^sub>0;
      \<F>' = \<F>(D := sfac D)
    in
      (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and> \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D) then
        (if (\<nexists>S'. scl_fol.conflict (cls_of_gcls |`| N\<^sub>0) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) S') then
          \<comment> \<open>2a\<close>
          ((\<Gamma>\<^sub>2\<^sub>a, U, None :: ('f, 'v) closure option), j, D, \<F>')
        else
          \<comment> \<open>2b\<close>
          ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>'))
      else
        \<comment> \<open>2c\<close>
        S1)) \<Longrightarrow>
  scl_reso1 N\<^sub>0 \<beta> ((\<Gamma>, U, None :: ('f, 'v) closure option), i, C, \<F>) S1 S2"


lemma grounding_lits_of_clss_fset_fimage_cls_of_gcls[simp]:
  fixes N :: "'f gterm clause fset"
  defines "N' \<equiv> fimage cls_of_gcls N"
  shows "grounding_lits_of_clss (fset N') = \<Union>(set_mset ` fset N')"
proof (intro Set.subset_antisym Set.subsetI)
  fix L
  assume "L \<in> grounding_lits_of_clss (fset N')"
  then obtain L' \<gamma> where
    "L = L' \<cdot>l \<gamma>" and L'_in: "L' \<in> \<Union> (set_mset ` fset N')" and "is_ground_lit (L' \<cdot>l \<gamma>)"
    by blast
  moreover have "is_ground_lit L'"
    using L'_in by (auto simp: N'_def cls_of_gcls_def)
  ultimately show "L \<in> \<Union>(set_mset ` fset N')"
    by simp
next
  fix L
  assume L_in: "L \<in> \<Union>(set_mset ` fset N')"
  hence "is_ground_lit L"
    by (auto simp: N'_def cls_of_gcls_def)
  thus "L \<in> grounding_lits_of_clss (fset N')"
    using L_in is_ground_subst_lit_iff by fastforce
qed

lemma undefined_in_trail_decide_if_undefined_in_trail_and_less_lit_pos:
  assumes "is_pos L" and "K \<prec>\<^sub>l L" and undef: "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
  shows "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L)"
proof -
  from \<open>is_pos L\<close> \<open>K \<prec>\<^sub>l L\<close> have "atm_of L \<noteq> atm_of K"
    by (cases L; cases K) simp_all

  with undef show ?thesis
    using inj_term_of_gterm[of UNIV, THEN inj_onD, simplified]
    by (auto simp add: trail_defined_lit_iff atm_of_lit_of_glit_conv decide_lit_def)
qed

lemma trail_undefined_if_trail_undefined_trail_decide:
  assumes "\<not> trail_defined_lit (trail_decide \<Gamma> K) L"
  shows "\<not> trail_defined_lit \<Gamma> L"
  using assms
  by (simp add: trail_defined_lit_iff)

lemma correctness_scl_reso1:
  fixes N :: "'f gterm clause fset" and \<beta> :: "'f gterm"
  defines "N' \<equiv> fimage cls_of_gcls N" and "\<beta>' \<equiv> term_of_gterm \<beta>"
  assumes
    \<beta>_greatest: "is_greatest_in_set_wrt (\<prec>\<^sub>t) (atms_of_clss (fset N)) \<beta>" and
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    invars:
      "scl_fol.trail_lits_from_clauses N' S\<^sub>0"
      "scl_fol.initial_lits_generalize_learned_trail_conflict N' S\<^sub>0"
  shows
    "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
    "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2 \<or>
      S\<^sub>1 = S\<^sub>2"
  using step
  unfolding atomize_conj
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I D U L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')

  from hyps have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
  proof (induction Ks arbitrary: S\<^sub>0 \<Gamma>)
    case Nil
    hence "S\<^sub>1 = S\<^sub>0"
      by simp
    thus ?case
      by simp
  next
    case (Cons K Ks)
    note ball_K_Ks = \<open>\<forall>K\<in>set (K # Ks). is_neg K \<and> K \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and> lit_occures_in_clss K N\<close>

    from ball_K_Ks have
      "K \<prec>\<^sub>l L" "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)" "lit_occures_in_clss K N"
      by simp_all

    from Cons have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* (trail_decide \<Gamma> (lit_of_glit K), U, None) S\<^sub>1"
    proof (intro Cons.IH[OF refl] ballI)
      show "\<Gamma>\<^sub>1 = foldl trail_decide (trail_decide \<Gamma> (lit_of_glit K)) (map lit_of_glit Ks)"
        by (simp add: \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>)
    next
      show "sorted_wrt (\<prec>\<^sub>l) Ks"
        using \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> by simp
    next
      from \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> have "distinct (K # Ks)"
        using linorder_lit.strict_sorted_iff by blast

      fix Ka assume "Ka \<in> set Ks"
      hence "\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)"
        using ball_K_Ks by simp

      from \<open>Ka \<in> set Ks\<close> have "is_neg K" and "is_neg Ka"
        using ball_K_Ks by simp_all
      hence "atm_of K \<noteq> atm_of Ka"
        using \<open>distinct (K # Ks)\<close>
        by (metis \<open>Ka \<in> set Ks\<close> distinct.simps(2) literal.expand)
      hence "term_of_gterm (atm_of Ka) \<noteq> term_of_gterm (atm_of K)"
        using inj_term_of_gterm[of UNIV, THEN injD] by metis
      hence "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)\<close>
        by (simp add: trail_defined_lit_iff decide_lit_def atm_of_lit_of_glit_conv)
      thus "is_neg Ka \<and> Ka \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka) \<and>
        lit_occures_in_clss Ka N"
        using ball_K_Ks \<open>Ka \<in> set Ks\<close>
        by simp
    next
      assume hyp: "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (let
          \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
          \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls (remove1_mset L (sfac D))) Var;
          E = The (is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|});
          j\<^sub>0 = count D' L;
          j = i\<^sub>0 + j\<^sub>0;
          \<F>' = \<F>\<^sub>0(D := sfac D)
        in
          if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and> \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D) then
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
          else
            (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
      show "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (let
          \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
          \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls (remove1_mset L (sfac D))) Var;
          E = The (is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|});
          j\<^sub>0 = count D' L;
          j = i\<^sub>0 + j\<^sub>0;
          \<F>' = \<F>\<^sub>0(D := sfac D)
        in
          if is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
            \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D) then
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
         else
          (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
        unfolding hyp
        unfolding Let_def
      proof (intro if_weak_cong iffI)
        assume "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and> \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D)"
        thus "is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
          \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D)"
          using undefined_in_trail_decide_if_undefined_in_trail_and_less_lit_pos[OF _ \<open>K \<prec>\<^sub>l L\<close>]
          by metis
      next
        assume "is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
          \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D)"
        thus "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and> \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D)"
          using trail_undefined_if_trail_undefined_trail_decide
          by metis
      qed
    qed

    moreover have "scl_fol.decide N' \<beta>' (\<Gamma>, U, None) (trail_decide \<Gamma> (lit_of_glit K), U, None)"
    proof (intro scl_fol.decideI[of _ _ Var, simplified])
      show "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> .
    next
      show "is_ground_lit (lit_of_glit K)"
        by (cases K) (simp_all add: is_ground_lit_def atm_of_lit_of_glit_conv)
    next
      show "fBex N' ((\<in>#) (lit_of_glit K))"
        using \<open>lit_occures_in_clss K N\<close>
        unfolding lit_occures_in_clss_def N'_def
        by (metis cls_of_gcls_def finsertI1 finsert_fimage imageI multiset.set_map)
    next
      have "atm_of K \<in> atms_of_clss (fset N)"
        using \<open>lit_occures_in_clss K N\<close>
        unfolding lit_occures_in_clss_def atms_of_clss_def
        by (metis Union_iff atms_of_def image_eqI)
      thus "ground (atm_of (lit_of_glit K)) \<and> ground \<beta>' \<and>
        gterm_of_term (atm_of (lit_of_glit K)) \<prec>\<^sub>t gterm_of_term \<beta>' \<or>
        atm_of (lit_of_glit K) = \<beta>'"
        using \<beta>_greatest \<beta>'_def
        by (auto simp add: atm_of_lit_of_glit_conv is_greatest_in_set_wrt_iff)
    qed

    ultimately show ?case
      unfolding \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close> \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close>
        \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>
      by simp
  qed

  from hyps have S\<^sub>1_def: "S\<^sub>1 = (\<Gamma>\<^sub>1, U, None)"
    by simp

  from hyps(6,7) have "distinct (map atm_of Ks)"
  proof (induction Ks)
    case Nil
    show ?case
      by simp
  next
    case (Cons Ka Ks)
    have "atm_of Ka \<notin> set (map atm_of Ks)"
      using Cons.prems literal.expand by fastforce
    moreover have "distinct (map atm_of Ks)"
      using Cons.prems by (intro Cons.IH) simp_all
    ultimately show ?case
      by simp
  qed

  show "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1 \<and>
    (scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2 \<or>
      S\<^sub>1 = S\<^sub>2)"
  proof (rule conjI)
    show "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
      using \<open>(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1\<close> .
  next
    let ?\<Gamma>\<^sub>2\<^sub>a = "trail_decide \<Gamma>\<^sub>1 (lit_of_glit L)"

    have
      (* "scl_fol.trail_lits_from_clauses N' S\<^sub>1" *)
      "scl_fol.initial_lits_generalize_learned_trail_conflict N' S\<^sub>1"
      unfolding atomize_conj
      using \<open>(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1\<close> invars
      by (induction S\<^sub>1 rule: rtranclp_induct)
        (simp_all add: scl_fol.decide_preserves_trail_lits_from_clauses
          scl_fol.decide_preserves_initial_lits_generalize_learned_trail_conflict)

    have "\<Union>(set_mset ` fset U) \<subseteq> \<Union>(set_mset ` fset N')"
    proof (intro Set.subsetI)
      fix L assume "L \<in> \<Union>(set_mset ` fset U)"
      moreover have "\<forall>L \<in> \<Union> (set_mset ` fset U). \<exists>K \<in> \<Union> (set_mset ` fset N'). generalizes_lit K L"
        using \<open>scl_fol.initial_lits_generalize_learned_trail_conflict N' S\<^sub>1\<close>
        by (simp add: S\<^sub>1_def scl_fol.initial_lits_generalize_learned_trail_conflict_def
            scl_fol.clss_lits_generalize_clss_lits_def)
      ultimately obtain K where K_in: "K \<in> \<Union> (set_mset ` fset N')" and "generalizes_lit K L"
        by metis

      from K_in have "is_ground_lit K"
        by (auto simp: N'_def cls_of_gcls_def)

      with \<open>generalizes_lit K L\<close> have "K = L"
        by (simp add: generalizes_lit_def)

      with K_in show "L \<in> \<Union>(set_mset ` fset N')"
        by argo
    qed

    have ground_cls_if_in_U: "is_ground_cls C" if C_in: "C |\<in>| U" for C
      unfolding is_ground_cls_def
    proof (intro allI impI)
      fix L assume "L \<in># C"
      with C_in obtain D where D_in: "D |\<in>| N'" "L \<in># D"
        using \<open>\<Union>(set_mset ` fset U) \<subseteq> \<Union>(set_mset ` fset N')\<close> by auto
      then show "is_ground_lit L"
        by (auto simp add: N'_def cls_of_gcls_def)
    qed

    have "L \<in># D"
      using \<open>ord_res.is_maximal_lit L D\<close>
      by (simp add: is_maximal_wrt_def)
    hence "lit_of_glit L \<in># cls_of_gcls D"
      by (simp add: cls_of_gcls_def)

    moreover have "cls_of_gcls D |\<in>| N' |\<union>| U"
      using \<open>D |\<in>| N |\<union>| gcls_of_cls |`| U\<close>[unfolded funion_iff]
    proof (elim disjE)
      assume "D |\<in>| N"
      then show ?thesis
        by (simp add: N'_def)
    next
      assume "D |\<in>| gcls_of_cls |`| U"
      then obtain D' where "D' |\<in>| U" and "D = gcls_of_cls D'"
        unfolding fimage_iff by metis
      then show ?thesis
        using ground_cls_if_in_U[OF \<open>D' |\<in>| U\<close>] by simp
    qed

    ultimately have "lit_of_glit L \<in> \<Union> (set_mset ` fset (N' |\<union>| U))"
      by blast
    hence "lit_of_glit L \<in> \<Union> (set_mset ` fset N')"
      using \<open>\<Union>(set_mset ` fset U) \<subseteq> \<Union>(set_mset ` fset N')\<close> by blast
    hence "L \<in> \<Union> (set_mset ` fset N)"
      unfolding N'_def
      by (simp add: cls_of_gcls_def inj_image_mem_iff[OF inj_lit_of_glit])

    show "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2 \<or>
      S\<^sub>1 = S\<^sub>2"
    proof (cases "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
      \<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D)")
      case pos_L_and_undef_L_and_false_D: True
      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (?\<Gamma>\<^sub>2\<^sub>a, U, None))")
        case ex_conflict: True
        hence "(scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2"
          sorry
        thus ?thesis
          by simp
      next
        case False
        hence " (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = ((?\<Gamma>\<^sub>2\<^sub>a, U, None), i\<^sub>0 + count D' L, D, \<F>\<^sub>0(D := sfac D))"
          using hyps(14) pos_L_and_undef_L_and_false_D by simp
        moreover have "scl_fol.decide N' \<beta>' (\<Gamma>\<^sub>1, U, None) (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L \<cdot>l Var), U, None)"
        proof (rule scl_fol.decideI)
          show "lit_of_glit L \<in> \<Union> (set_mset ` fset N')"
            using \<open>lit_of_glit L \<in> \<Union> (set_mset ` fset N')\<close> .
        next
          show "is_ground_lit (lit_of_glit L \<cdot>l Var)"
            by simp
        next
          have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
            using pos_L_and_undef_L_and_false_D by argo
          have "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)"
            unfolding \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks)\<close>
            using hyps(7) pos_L_and_undef_L_and_false_D \<open>distinct (map atm_of Ks)\<close>
          proof (induction Ks arbitrary: \<Gamma>)
            case Nil
            thus ?case
              by simp
          next
            case (Cons K Ks)
            show ?case
              unfolding list.map foldl_Cons
            proof (intro Cons.IH ballI conjI)
              show "is_pos L"
                "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L)"
                "\<not> trail_true_cls \<Gamma>\<^sub>1 (cls_of_gcls D)"
                using Cons.prems undefined_in_trail_decide_if_undefined_in_trail_and_less_lit_pos
                by auto
            next
              show "distinct (map atm_of Ks)"
                using Cons.prems by simp
            next
              fix Ka assume Ka_in: "Ka \<in> set Ks"

              from Ka_in show "is_neg Ka" "Ka \<prec>\<^sub>l L" "lit_occures_in_clss Ka N"
                using Cons.prems(1) by simp_all

              from Ka_in have "atm_of K \<noteq> atm_of Ka"
                using Cons.prems(3) by auto
              hence "term_of_gterm (atm_of Ka) \<noteq> term_of_gterm (atm_of K)"
                using inj_term_of_gterm[of UNIV, THEN inj_onD, simplified] by metis
              moreover from Ka_in have "\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)"
                using Cons.prems(1) by simp
              ultimately show "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)"
                unfolding trail_defined_lit_iff
                by (simp add: decide_lit_def atm_of_lit_of_glit_conv)
            qed
          qed
          thus "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L \<cdot>l Var)"
            by simp
        next
          have "atm_of L \<in> atms_of_clss (fset N)"
            using \<open>L \<in> \<Union> (set_mset ` fset N)\<close>
            by (auto simp: atms_of_clss_def intro: atm_of_lit_in_atms_of)
          with \<beta>_greatest show "scl_fol.lesseq_B (atm_of (lit_of_glit L) \<cdot>a Var) \<beta>'"
            by (auto simp add: atm_of_lit_of_glit_conv \<beta>'_def is_greatest_in_set_wrt_iff)
        qed

        ultimately have "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2"
          using hyps(9) by fastforce
        thus ?thesis
          by simp
      qed
    next
      case False
      hence "S\<^sub>1 = S\<^sub>2"
        using hyps(14) by auto
      thus ?thesis
        by simp
    qed
  qed
qed

end
 
end