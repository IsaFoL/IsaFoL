theory Simulation
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Superposition_Calculus.Ground_Ordered_Resolution
    VeriComp.Simulation
begin

section \<open>Move to HOL\<close>

lemma transp_on_singleton[simp]: "transp_on {x} R"
  by (simp add: transp_on_def)

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

text \<open>When a binary relation hold for two values, i.e., \<^term>\<open>R x y\<close>, we say that \<^term>\<open>x\<close> reaches
\<^term>\<open>y\<close> and, conversely, that \<^term>\<open>y\<close> is reachable by \<^term>\<open>x\<close>.\<close>

definition non_reachable_wrt where
  "non_reachable_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R y x))"

definition non_reaching_wrt where
  "non_reaching_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R x y))"

definition reaching_all_wrt where
  "reaching_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R x y)"

definition reachable_by_all_wrt where
  "reachable_by_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R y x)"

text \<open>If the binary relation is a strict partial order, then non-reachability corresponds to
minimality and non-reaching correspond to maximality.\<close>

definition is_minimal_in_set_wrt where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> is_minimal_in_set_wrt R X = non_reachable_wrt R X"

definition is_maximal_in_set_wrt where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> is_maximal_in_set_wrt R X = non_reaching_wrt R X"

text \<open>If the binary relation is a strict total ordering, then an element reaching all others is a
least element and an element reachable by all others is a greatest element.\<close>

definition is_least_in_set_wrt where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow>
    is_least_in_set_wrt R X = reaching_all_wrt R X"

definition is_greatest_in_set_wrt where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow>
    is_greatest_in_set_wrt R X = reachable_by_all_wrt R X"


subsubsection \<open>Conversions\<close>

lemma non_reachable_wrt_conversep[simp]:
  "non_reachable_wrt R\<inverse>\<inverse> = non_reaching_wrt R"
  unfolding non_reaching_wrt_def non_reachable_wrt_def by simp

lemma non_reaching_wrt_conversep[simp]:
  "non_reaching_wrt R\<inverse>\<inverse> = non_reachable_wrt R"
  unfolding non_reaching_wrt_def non_reachable_wrt_def by simp

lemma reaching_all_wrt_conversep[simp]:
  "reaching_all_wrt R\<inverse>\<inverse> = reachable_by_all_wrt R"
  unfolding reaching_all_wrt_def reachable_by_all_wrt_def by simp

lemma reachable_by_all_wrt_conversep[simp]:
  "reachable_by_all_wrt R\<inverse>\<inverse> = reaching_all_wrt R"
  unfolding reaching_all_wrt_def reachable_by_all_wrt_def by simp

lemma non_reachable_wrt_iff:
  "non_reachable_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R y x)"
  unfolding non_reachable_wrt_def by blast

lemma non_reaching_wrt_iff:
  "non_reaching_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  unfolding non_reaching_wrt_def by blast

lemma reaching_all_wrt_iff:
  "reaching_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R x y)"
  unfolding reaching_all_wrt_def by blast

lemma reachable_by_all_wrt_iff:
  "reachable_by_all_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R y x)"
  unfolding reachable_by_all_wrt_def by blast

corollary is_minimal_in_set_wrt_iff:
  assumes trans: "transp_on X R" and asym: "asymp_on X R"
  shows "is_minimal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R y x)"
  using assms is_minimal_in_set_wrt_def[unfolded non_reachable_wrt_iff] by metis

corollary is_maximal_in_set_wrt_iff:
  assumes trans: "transp_on X R" and asym: "asymp_on X R"
  shows "is_maximal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  using assms is_maximal_in_set_wrt_def[unfolded non_reaching_wrt_iff] by metis

corollary is_least_in_set_wrt_iff:
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_least_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R x y)"
  using assms is_least_in_set_wrt_def[unfolded reaching_all_wrt_iff] by metis

corollary is_greatest_in_set_wrt_iff:
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_greatest_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R y x)"
  using assms is_greatest_in_set_wrt_def[unfolded reachable_by_all_wrt_iff] by metis

lemma non_reachable_wrt_eq_reaching_all_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "non_reachable_wrt R X = reaching_all_wrt R X"
proof (intro ext iffI)
  fix x
  from tot show "non_reachable_wrt R X x \<Longrightarrow> reaching_all_wrt R X x"
    unfolding non_reachable_wrt_def reaching_all_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  fix x
  from asym show "reaching_all_wrt R X x \<Longrightarrow> non_reachable_wrt R X x"
    unfolding reaching_all_wrt_def non_reachable_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma non_reaching_wrt_eq_reachable_by_all_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "non_reaching_wrt R X = reachable_by_all_wrt R X"
proof (intro ext iffI)
  fix x
  from tot show "non_reaching_wrt R X x \<Longrightarrow> reachable_by_all_wrt R X x"
    unfolding non_reaching_wrt_def reachable_by_all_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  fix x
  from asym show "reachable_by_all_wrt R X x \<Longrightarrow> non_reaching_wrt R X x"
    unfolding reachable_by_all_wrt_def non_reaching_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma is_minimal_in_set_wrt_eq_is_least_in_set_wrt:
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_minimal_in_set_wrt R X = is_least_in_set_wrt R X"
  using assms non_reachable_wrt_eq_reaching_all_wrt
    is_minimal_in_set_wrt_def is_least_in_set_wrt_def
  by metis

lemma is_maximal_in_set_wrt_eq_is_greatest_in_set_wrt:
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_maximal_in_set_wrt R X = is_greatest_in_set_wrt R X"
  using assms non_reaching_wrt_eq_reachable_by_all_wrt
    is_maximal_in_set_wrt_def is_greatest_in_set_wrt_def
  by metis

lemma non_reachable_wrt_filter_iff:
  "non_reachable_wrt R {y \<in> X. P y} x \<longleftrightarrow> x \<in> X \<and> P x \<and> (\<forall>y \<in> X - {x}. P y \<longrightarrow> \<not> R y x)"
  by (auto simp: non_reachable_wrt_def)

(* TODO: See theory file IsaFOL/Splitting_Framework.FOL_Compactness for lemmas about
Set.filter and co. *)


subsubsection \<open>Existence\<close>

lemma ex_non_reachable_wrt:
  "transp_on A R \<Longrightarrow> asymp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. non_reachable_wrt R A m"
  using Finite_Set.bex_min_element
  by (metis non_reachable_wrt_iff)

lemma ex_non_reaching_wrt:
  "transp_on A R \<Longrightarrow> asymp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. non_reaching_wrt R A m"
  using Finite_Set.bex_max_element
  by (metis non_reaching_wrt_iff)

lemma ex_reaching_all_wrt:
  "transp_on A R \<Longrightarrow> totalp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>g. reaching_all_wrt R A g"
  using Finite_Set.bex_least_element[of A R]
  by (metis reaching_all_wrt_iff)

lemma ex_reachable_by_all_wrt:
  "transp_on A R \<Longrightarrow> totalp_on A R \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>g. reachable_by_all_wrt R A g"
  using Finite_Set.bex_greatest_element[of A R]
  by (metis reachable_by_all_wrt_iff)

corollary ex_minimal_element:
  assumes trans: "transp_on X R" and asym: "asymp_on X R"
  shows "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_minimal_in_set_wrt R X x"
  using assms ex_non_reachable_wrt is_minimal_in_set_wrt_def by metis

corollary ex_maximal_element:
  assumes trans: "transp_on X R" and asym: "asymp_on X R"
  shows "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>m. is_maximal_in_set_wrt R X m"
  using assms is_maximal_in_set_wrt_def ex_non_reaching_wrt by metis

corollary ex_least_element:
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_least_in_set_wrt R X x"
  using assms is_least_in_set_wrt_def ex_reaching_all_wrt by metis

corollary ex_greatest_element:
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_greatest_in_set_wrt R X x"
  using assms is_greatest_in_set_wrt_def ex_reachable_by_all_wrt by metis

lemma not_bex_greatest_element_doubleton:
  assumes "x \<noteq> y" and "\<not> R x y" and "\<not> R y x"
  shows "\<nexists>g. reachable_by_all_wrt R {x, y} g"
proof (rule notI)
  assume "\<exists>g. reachable_by_all_wrt R {x, y} g"
  then obtain g where "reachable_by_all_wrt R {x, y} g" ..
  then show False
    unfolding reachable_by_all_wrt_def
    using assms(1) assms(2) assms(3) by blast
qed


subsubsection \<open>Uniqueness\<close>

lemma Uniq_non_reachable_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. non_reachable_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff non_reachable_wrt_def totalp_onD)

lemma Uniq_non_reaching_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. non_reaching_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff non_reaching_wrt_def totalp_onD)

lemma Uniq_reaching_all_wrt:
  "asymp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. reaching_all_wrt R X x"
  by (rule Uniq_I)
    (metis antisymp_onD antisymp_on_if_asymp_on insertE insert_Diff reaching_all_wrt_def)

lemma Uniq_reachable_by_all_wrt:
  "asymp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. reachable_by_all_wrt R X x"
  by (rule Uniq_I)
    (metis antisymp_onD antisymp_on_if_asymp_on insertE insert_Diff reachable_by_all_wrt_def)

context
  fixes X R
  assumes trans: "transp_on X R" and asym: "asymp_on X R" and tot: "totalp_on X R"
begin

corollary Uniq_is_least_in_set_wrt:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_least_in_set_wrt R X x"
  using trans asym tot is_least_in_set_wrt_def Uniq_reaching_all_wrt by metis

corollary Uniq_is_greatest_in_set_wrt:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_greatest_in_set_wrt R X x"
  using trans asym tot is_greatest_in_set_wrt_def Uniq_reachable_by_all_wrt by metis

end


subsubsection \<open>Existence of unique element\<close>

lemma ex1_least_in_set_wrt:
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow> finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    \<exists>!x. is_least_in_set_wrt R X x"
  using is_least_in_set_wrt_def ex1_iff_ex_Uniq
  using ex_reaching_all_wrt Uniq_reaching_all_wrt by metis

lemma ex1_greatest_in_set_wrt:
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow> finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
    \<exists>!x. is_greatest_in_set_wrt R X x"
  using is_greatest_in_set_wrt_def ex1_iff_ex_Uniq
  using ex_reachable_by_all_wrt Uniq_reachable_by_all_wrt by metis


subsubsection \<open>Transformations\<close>

lemma is_minimal_in_insert_wrtI:
  assumes
    trans: "transp_on (insert y X) R" and
    asym: "asymp_on (insert y X) R" and
    "R y x" and
    x_min: "non_reachable_wrt R X x"
  shows "non_reachable_wrt R (insert y X) y"
proof -
  from x_min have x_in: "x \<in> X" and x_min': "\<forall>y\<in>X - {x}. \<not> R y x"
    by (simp_all add: non_reachable_wrt_iff)

  have "\<not> R z y" if "z \<in> insert y X - {y}" for z
  proof -
    from that have "z \<in> X" and "z \<noteq> y"
      by simp_all

    show "\<not> R z y"
    proof (cases "z = x")
      case True
      thus ?thesis
        using \<open>R y x\<close> asym x_in
        by (metis asymp_onD insertI1 insertI2)
    next
      case False
      hence "\<not> R z x"
        using x_min'[rule_format, of z, simplified] \<open>z \<in> X\<close> by metis
      then show ?thesis
        using \<open>R y x\<close> trans \<open>z \<in> X\<close> x_in
        by (meson insertCI transp_onD)
    qed
  qed
  thus ?thesis
    by (simp add: non_reachable_wrt_def)
qed


subsubsection \<open>Function\<close>

definition Greatest_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a option" where
  "Greatest_in_set_wrt R X = (if X = {} then None else Some (THE x. is_greatest_in_set_wrt R X x))"

lemma Greatest_in_set_wrt_empty[simp]: "Greatest_in_set_wrt R {} = None"
  by (simp add: Greatest_in_set_wrt_def)

lemma Greatest_in_set_wrt_singleton[simp]:
  "asymp_on {x} R \<Longrightarrow> Greatest_in_set_wrt R {x} = Some x"
  unfolding Greatest_in_set_wrt_def
  using is_greatest_in_set_wrt_def[of "{x}" R, simplified]
    ex_reachable_by_all_wrt[of "{x}" R, simplified]
    Uniq_reachable_by_all_wrt[of "{x}" R]
  by (simp add:  the1_equality' reachable_by_all_wrt_iff)

lemma Greatest_in_set_wrt_eq_None[simp]: "Greatest_in_set_wrt R X = None \<longleftrightarrow> X = {}"
  by (simp add: Greatest_in_set_wrt_def)

lemma Greatest_in_set_wrt_eq_Some_if_is_greatest_in_set_wrt:
  assumes
    trans: "transp_on X R" and
    asym: "asymp_on X R" and
    tot: "totalp_on X R"
  shows "is_greatest_in_set_wrt R X x \<Longrightarrow> Greatest_in_set_wrt R X = Some x"
  unfolding Greatest_in_set_wrt_def is_greatest_in_set_wrt_def[OF trans asym tot]
  using Uniq_reachable_by_all_wrt[OF asym] the1_equality'
  by (metis empty_iff reachable_by_all_wrt_iff)

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

  have "is_greatest_in_set_wrt R X (THE x. is_greatest_in_set_wrt R X x)"
    using ex1_greatest_in_set_wrt trans asym tot fin \<open>X \<noteq> {}\<close> by (metis theI')
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

declare wfP_pfsubset[intro]

syntax
  "_FFilter" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> 'a fset" ("(1{|_ |\<in>| _./ _|})")

translations
  "{|x |\<in>| X. P|}" == "CONST ffilter (\<lambda>x. P) X"

lemma fimage_ffUnion: "f |`| ffUnion SS = ffUnion ((|`|) f |`| SS)"
proof (intro fsubset_antisym fsubsetI)
  fix x assume "x |\<in>| f |`| ffUnion SS"
  then obtain y where "y |\<in>| ffUnion SS" and "x = f y"
    by auto
  thus "x |\<in>| ffUnion ((|`|) f |`| SS)"
    unfolding fmember_ffUnion_iff
    by (metis UN_E ffUnion.rep_eq fimage_eqI)
next
  fix x assume "x |\<in>| ffUnion ((|`|) f |`| SS)"
  then obtain S where "S |\<in>| SS" and "x |\<in>| f |`| S"
    unfolding fmember_ffUnion_iff by auto
  then show "x |\<in>| f |`| ffUnion SS"
    by (metis ffUnion_fsubset_iff fimage_mono fin_mono fsubsetI)
qed

abbreviation is_minimal_in_fset_wrt where
  "is_minimal_in_fset_wrt R X \<equiv> is_minimal_in_set_wrt R (fset X)"

abbreviation is_maximal_in_fset_wrt where
  "is_maximal_in_fset_wrt R X \<equiv> is_maximal_in_set_wrt R (fset X)"

abbreviation is_least_in_fset_wrt where
  "is_least_in_fset_wrt R X \<equiv> is_least_in_set_wrt R (fset X)"

abbreviation is_greatest_in_fset_wrt where
  "is_greatest_in_fset_wrt R X \<equiv> is_greatest_in_set_wrt R (fset X)"

lemma is_minimal_in_fset_wrt_ffilter_iff:
  assumes
    tran: "transp_on (fset {|y |\<in>| X. P y|}) R" and
    asym: "asymp_on (fset {|y |\<in>| X. P y|}) R"
  shows "is_minimal_in_fset_wrt R {|y |\<in>| X. P y|} x \<longleftrightarrow>
    (x |\<in>| X \<and> P x \<and> (\<forall>y|\<in>| X - {|x|}. P y \<longrightarrow> \<not> R y x))"
  unfolding is_minimal_in_set_wrt_def[OF tran asym]
  using non_reachable_wrt_filter_iff[of _ "fset _"]
  by (smt (verit, best) bot_fset.rep_eq empty_iff ffmember_filter finsert_iff fminus_iff
      non_reachable_wrt_iff)

lemma bex_minimal_element_in_fset_wrt:
  "asymp_on (fset X) R \<Longrightarrow> transp_on (fset X) R \<Longrightarrow> X \<noteq> {||} \<Longrightarrow> \<exists>m. is_minimal_in_fset_wrt R X m"
  using ex_minimal_element[of "fset X" R] by auto

lemma is_minimal_in_finsert_wrtI:
  "transp_on (fset (finsert y X)) R \<Longrightarrow> asymp_on (fset (finsert y X)) R \<Longrightarrow> R y x \<Longrightarrow>
  is_minimal_in_fset_wrt R X x \<Longrightarrow> is_minimal_in_fset_wrt R (finsert y X) y"
  using is_minimal_in_insert_wrtI[of _ "fset _", folded fset_simps]
  by (smt (verit, ccfv_threshold) asymp_on_subset fsubset_finsertI is_minimal_in_set_wrt_def
      less_eq_fset.rep_eq transp_on_subset)


section \<open>Move to \<^theory>\<open>VeriComp.Simulation\<close>\<close>

locale forward_simulation_with_measuring_function =
  L1: semantics step1 final1 +
  L2: semantics step2 final2 +
  well_founded "(\<sqsubset>)"
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70) +
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state1 \<Rightarrow> 'index"
  assumes
    match_final:
      "match s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2" and
    simulation:
      "match s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
        (\<exists>s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match s1' s2') \<or> (match s1' s2 \<and> measure s1' \<sqsubset> measure s1)"
begin

sublocale forward_simulation where
  step1 = step1 and step2 = step2 and final1 = final1 and final2 = final2 and order = order and
  match = "\<lambda>i x y. i = measure x \<and> match x y"
proof unfold_locales
  show "\<And>i s1 s2. i = measure s1 \<and> match s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2"
    using match_final by metis
next
  show "\<And>i s1 s2 s1'. i = measure s1 \<and> match s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
    (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> i' = measure s1' \<and> match s1' s2') \<or>
    (\<exists>i'. (i' = measure s1' \<and> match s1' s2) \<and> i' \<sqsubset> i)"
    using simulation by metis
qed

end

locale backward_simulation_with_measuring_function =
  L1: semantics step1 final1 +
  L2: semantics step2 final2 +
  well_founded "(\<sqsubset>)"
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70) +
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state2 \<Rightarrow> 'index"
  assumes
    match_final:
      "match s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1" and
    simulation:
      "match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
        (\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2') \<or> (match s1 s2' \<and> measure s2' \<sqsubset> measure s2)"
begin

sublocale backward_simulation where
  step1 = step1 and step2 = step2 and final1 = final1 and final2 = final2 and order = order and
  match = "\<lambda>i x y. i = measure y \<and> match x y"
proof unfold_locales
  show "\<And>i s1 s2. i = measure s2 \<and> match s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1"
    using match_final by metis
next
  show "\<And>i1 s1 s2 s2'. i1 = measure s2 \<and> match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
    (\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> i2 = measure s2' \<and> match s1' s2') \<or>
    (\<exists>i2. (i2 = measure s2' \<and> match s1 s2') \<and> i2 \<sqsubset> i1)"
    using simulation by metis
qed

end

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
  shows "wfP ground_factoring\<inverse>\<inverse>"
proof (rule wfP_if_convertible_to_wfP)
  show "\<And>x y. ground_factoring\<inverse>\<inverse> x y \<Longrightarrow> x \<prec>\<^sub>c y"
    using ground_factoring_smaller_conclusion by simp
next
  show "wfP (\<prec>\<^sub>c)"
    by simp
qed

lemma (in ground_ordered_resolution_calculus) atms_of_concl_subset_if_ground_resolution:
  assumes "ground_resolution P\<^sub>1 P\<^sub>2 C"
  shows "atms_of C \<subseteq> atms_of P\<^sub>1 \<union> atms_of P\<^sub>2"
  using assms by (cases P\<^sub>1 P\<^sub>2 C rule: ground_resolution.cases) (auto simp add: atms_of_def)

lemma (in ground_ordered_resolution_calculus) strict_subset_mset_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "C \<subset># P"
  using assms by (cases P C rule: ground_factoring.cases) simp

lemma (in ground_ordered_resolution_calculus) atms_of_concl_eq_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "atms_of C = atms_of P"
  using assms by (cases P C rule: ground_factoring.cases) simp


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

lemma is_ground_cls_cls_of_gcls[simp]: "is_ground_cls (cls_of_gcls C)"
  by (auto simp add: is_ground_cls_def cls_of_gcls_def)

lemma glit_of_lit_lit_of_glit[simp]: "glit_of_lit (lit_of_glit L) = L"
  by (simp add: glit_of_lit_def lit_of_glit_def literal.map_comp comp_def literal.map_ident)

lemma gcls_of_cls_cls_of_gcls[simp]: "gcls_of_cls (cls_of_gcls L) = L"
  by (simp add: gcls_of_cls_def cls_of_gcls_def multiset.map_comp comp_def multiset.map_ident)

lemma lit_of_glit_glit_of_lit_ident[simp]: "is_ground_lit L \<Longrightarrow> lit_of_glit (glit_of_lit L) = L"
  by (simp add: is_ground_lit_def lit_of_glit_def glit_of_lit_def literal.map_comp literal.expand
      literal.map_sel)

lemma cls_of_gcls_gcls_of_cls_ident[simp]: "is_ground_cls D \<Longrightarrow> cls_of_gcls (gcls_of_cls D) = D"
  by (simp add: is_ground_cls_def cls_of_gcls_def gcls_of_cls_def)

definition atms_of_cls :: "'a clause \<Rightarrow> 'a fset" where
  "atms_of_cls C = atm_of |`| fset_mset C"

definition atms_of_clss :: "'a clause fset \<Rightarrow> 'a fset" where
  "atms_of_clss N = ffUnion (atms_of_cls |`| N)"

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

definition less_B where
  "less_B x y \<longleftrightarrow> ground x \<and> ground y \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term y"

interpretation scl_fol: scl_fol_calculus renaming_vars less_B
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
  thus "finite {x. less_B x \<beta>}"
    unfolding less_B_def
    using not_finite_existsD by force
qed


subsection \<open>Strategy for model-driven ground ordered resolution\<close>

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

definition is_min_false_clause :: "'f gterm clause fset \<Rightarrow> 'f gterm clause \<Rightarrow> bool" where
  "is_min_false_clause N C \<longleftrightarrow>
    is_minimal_in_fset_wrt (\<prec>\<^sub>c)
      {|C |\<in>| N. \<not> (\<Union>D \<in> {D \<in> fset N. D \<preceq>\<^sub>c C}. ord_res.production (fset N) D) \<TTurnstile> C|} C"

lemma Uniq_is_min_false_clause: "\<exists>\<^sub>\<le>\<^sub>1C. is_min_false_clause N C"
  unfolding is_min_false_clause_def
  using Uniq_non_reachable_wrt
  by (smt (verit, ccfv_SIG) is_minimal_in_set_wrt_def linorder_cls.asymp_on_less
      linorder_cls.totalp_on_less linorder_cls.transp_on_less)

definition ord_res_mod_op_strategy :: "'f gterm clause fset \<Rightarrow> 'f gterm clause fset \<Rightarrow> bool" where
  "ord_res_mod_op_strategy N N' \<longleftrightarrow> (\<exists>C L.
    is_min_false_clause N C \<and> ord_res.is_maximal_lit L C \<and>
      (case L of
        Neg A \<Rightarrow> \<comment> \<open>Case 3\<close>
        fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
          (\<exists>CD. ord_res.ground_resolution C D CD \<and> N' = finsert CD N))
      | Pos A \<Rightarrow> \<comment> \<open>Case 4\<close>
        \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
          (\<exists>C'. ord_res.ground_factoring C C' \<and> N' = finsert C' N)))"

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
    unfolding is_minimal_in_fset_wrt_ffilter_iff[OF linorder_cls.transp_on_less
        linorder_cls.asymp_on_less]
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
    unfolding is_minimal_in_fset_wrt_ffilter_iff[OF linorder_cls.transp_on_less
        linorder_cls.asymp_on_less]
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

subsection \<open>Strategy for resolution-driven SCL(FOL)\<close>

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

inductive scl_reso1
  :: "_ \<Rightarrow> _ \<Rightarrow>
    ('f, 'v) state \<times> _ \<Rightarrow>
    ('f, 'v) state \<times> _ \<Rightarrow>
    ('f, 'v) state \<times> _ \<Rightarrow> bool" for N\<^sub>0 \<beta> where
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
      \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
      E = (THE x. is_least_in_fset_wrt (\<prec>\<^sub>c)
        {|C |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} x);
      j\<^sub>0 = count D' L;
      j = i + j\<^sub>0;
      \<F>' = \<F>(D := add_mset L {#K \<in># D. K \<noteq> L#})
    in
      (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
        trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
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

lemma scl_reso1_clause2_eq_clause_3:
  assumes "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)"
  shows "C\<^sub>1 = C\<^sub>2"
  using assms
proof (cases rule: scl_reso1.cases)
  case hyps: (scl_reso1I D U L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')
  have "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp
  also have "D = C\<^sub>2"
  proof (cases "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
    trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})")
    case True1: True
    show ?thesis
    proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L), U, None))")
      case True2: True
      show ?thesis 
        using hyps(14)
        unfolding Let_def
        unfolding HOL.if_P[OF True1]
        unfolding if_not_P[of "\<not> _", simplified, OF True2]
        by simp
    next
      case False
      show ?thesis
        using hyps(14)
        unfolding Let_def
        unfolding HOL.if_P[OF True1]
        unfolding if_P[of "\<not> _", simplified, OF False]
        by simp
    qed
  next
    case False
    show ?thesis
      using hyps(14)
      unfolding Let_def
      unfolding HOL.if_not_P[OF False]
      by (simp add: \<open>C\<^sub>1 = D\<close>)
  qed
  finally show ?thesis .
qed

lemma scl_reso1_\<F>_eq:
  assumes "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)"
  shows
    "\<F>\<^sub>1 = \<F>\<^sub>0"
    "\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#}))"
  unfolding atomize_conj
  using assms
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I D U L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')

  have "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp

  have "\<F>\<^sub>1 = \<F>\<^sub>0"
    using hyps(9) by simp
  thus "\<F>\<^sub>1 = \<F>\<^sub>0 \<and>
    (\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#})))"
  proof (intro conjI)
    show "\<F>\<^sub>2 = \<F>\<^sub>1 \<or>
      (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#}))"
    proof (cases "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
    trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})")
      case True1: True
      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L), U, None))")
        case True2: True
        show ?thesis
          using hyps(5,14)
          unfolding Let_def
          unfolding HOL.if_P[OF True1]
          unfolding if_not_P[of "\<not> _", simplified, OF True2]
          unfolding \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>
          by blast
      next
        case False
        then show ?thesis
          using hyps(5,14)
          unfolding Let_def
          unfolding HOL.if_P[OF True1]
          unfolding if_P[of "\<not> _", simplified, OF False]
          unfolding \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>
          by blast
      qed
    next
      case False
      show ?thesis
        using hyps(14)
        unfolding Let_def
        unfolding HOL.if_not_P[OF False]
        by simp
    qed
  qed
qed

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

lemma lits_of_learned_subset_lits_of_initial:
  fixes N :: "'f gterm clause fset" and \<beta> :: "'f gterm"
  defines "N' \<equiv> fimage cls_of_gcls N" and "\<beta>' \<equiv> term_of_gterm \<beta>"
  assumes N'_generalizes: "scl_fol.initial_lits_generalize_learned_trail_conflict N' S"
  shows "\<Union>(set_mset ` fset (state_learned S)) \<subseteq> \<Union>(set_mset ` fset N')"
proof (intro Set.subsetI)
  fix L assume "L \<in> \<Union>(set_mset ` fset (state_learned S))"
  moreover have "\<forall>L \<in> \<Union> (set_mset ` fset (state_learned S)). \<exists>K \<in> \<Union> (set_mset ` fset N'). generalizes_lit K L"
    using N'_generalizes
    by (simp add: scl_fol.initial_lits_generalize_learned_trail_conflict_def
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

lemma glits_subset_if_lits_subset:
  assumes "\<Union> (set_mset ` fset U) \<subseteq> \<Union> (set_mset ` fset (cls_of_gcls |`| N))"
  shows "\<Union> (set_mset ` fset (gcls_of_cls |`| U)) \<subseteq> \<Union> (set_mset ` fset N)"
proof (intro Set.subsetI)
  fix L\<^sub>G assume "L\<^sub>G \<in> \<Union> (set_mset ` fset (gcls_of_cls |`| U))"
  then obtain C\<^sub>G where "L\<^sub>G \<in># C\<^sub>G" and "C\<^sub>G |\<in>| gcls_of_cls |`| U"
    by blast
  then obtain C where "C\<^sub>G = gcls_of_cls C" and "C |\<in>| U"
    by blast
  then obtain L where "L\<^sub>G = glit_of_lit L" and "L \<in># C"
    using \<open>L\<^sub>G \<in># C\<^sub>G\<close> by (metis gcls_of_cls_def image_iff multiset.set_map)
  hence "L \<in> \<Union> (set_mset ` fset U)"
    using \<open>C |\<in>| U\<close> by blast
  hence "L \<in> \<Union> (set_mset ` fset (cls_of_gcls |`| N))"
    using assms by fast
  hence "L \<in> \<Union> (image lit_of_glit ` set_mset ` fset N)"
    by (simp add: cls_of_gcls_def)
  then show "L\<^sub>G \<in> \<Union> (set_mset ` fset N)"
    by (auto simp: \<open>L\<^sub>G = glit_of_lit L\<close>)
qed

lemma correctness_scl_reso1:
  fixes N :: "'f gterm clause fset" and \<beta> :: "'f gterm"
  defines "N' \<equiv> fimage cls_of_gcls N" and "\<beta>' \<equiv> term_of_gterm \<beta>"
  assumes
    \<beta>_greatest: "is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta>" and
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    invars:
      "scl_fol.initial_lits_generalize_learned_trail_conflict N' S\<^sub>0"
  shows
    "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
    "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2 \<or>
      (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)"
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
          \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
          E = The (is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|});
          j\<^sub>0 = count D' L;
          j = i\<^sub>0 + j\<^sub>0;
          \<F>' = \<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})
        in
          if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
            trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
          else
            (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
      show "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (let
          \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
          \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
          E = The (is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|});
          j\<^sub>0 = count D' L;
          j = i\<^sub>0 + j\<^sub>0;
          \<F>' = \<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})
        in
          if is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
            trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
         else
          (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
        unfolding hyp
        unfolding Let_def
      proof (intro if_weak_cong iffI)
        assume "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
        thus "is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
          using undefined_in_trail_decide_if_undefined_in_trail_and_less_lit_pos[OF _ \<open>K \<prec>\<^sub>l L\<close>]
          by metis
      next
        assume "is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
        thus "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
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
      have "atm_of K |\<in>| atms_of_clss N"
        using \<open>lit_occures_in_clss K N\<close>
        unfolding lit_occures_in_clss_def atms_of_clss_def
        by (metis atms_of_cls_def fimage_eqI fmember_ffUnion_iff fmember_fset_mset_iff)
      thus "less_B (atm_of (lit_of_glit K)) \<beta>' \<or> atm_of (lit_of_glit K) = \<beta>'"
        unfolding less_B_def
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
      (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
  proof (rule conjI)
    show "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
      using \<open>(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1\<close> .
  next
    have
      "scl_fol.initial_lits_generalize_learned_trail_conflict N' S\<^sub>1"
      unfolding atomize_conj
      using \<open>(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1\<close> invars
      by (induction S\<^sub>1 rule: rtranclp_induct)
        (simp_all add: scl_fol.decide_preserves_trail_lits_from_clauses
          scl_fol.decide_preserves_initial_lits_generalize_learned_trail_conflict)
    hence "\<Union>(set_mset ` fset U) \<subseteq> \<Union>(set_mset ` fset N')"
      using lits_of_learned_subset_lits_of_initial
      by (metis N'_def S\<^sub>1_def state_proj_simp(2))

    have ground_cls_if_in_U: "is_ground_cls C" if C_in: "C |\<in>| U" for C
      unfolding is_ground_cls_def
    proof (intro allI impI)
      fix L assume "L \<in># C"
      with C_in obtain D where D_in: "D |\<in>| N'" "L \<in># D"
        using \<open>\<Union>(set_mset ` fset U) \<subseteq> \<Union>(set_mset ` fset N')\<close> by auto
      then show "is_ground_lit L"
        by (auto simp add: N'_def cls_of_gcls_def)
    qed

    have "cls_of_gcls D |\<in>| N' |\<union>| U"
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

    have lit_in_N_if_in_D: "L \<in> \<Union> (set_mset ` fset N)" if "L \<in># D" for L
    proof -
      from that have "lit_of_glit L \<in># cls_of_gcls D"
        by (simp add: cls_of_gcls_def)
      hence "lit_of_glit L \<in> \<Union> (set_mset ` fset (N' |\<union>| U))"
        using \<open>cls_of_gcls D |\<in>| N' |\<union>| U\<close> by blast
      hence "lit_of_glit L \<in> \<Union> (set_mset ` fset N')"
        using \<open>\<Union>(set_mset ` fset U) \<subseteq> \<Union>(set_mset ` fset N')\<close> by blast
      thus "L \<in> \<Union> (set_mset ` fset N)"
        unfolding N'_def
        by (simp add: cls_of_gcls_def inj_image_mem_iff[OF inj_lit_of_glit])
    qed
    hence "L \<in> \<Union> (set_mset ` fset N)"
      using \<open>ord_res.is_maximal_lit L D\<close>
      by (simp add: is_maximal_wrt_def)

    show "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2 \<or>
      (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)"
    proof (cases "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
      trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})")
      case pos_L_and_undef_L_and_false_D: True

      let ?\<Gamma>\<^sub>2\<^sub>a = "trail_decide \<Gamma>\<^sub>1 (lit_of_glit L)"
      let ?\<Gamma>\<^sub>2\<^sub>b = "trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var"
      let ?E = "The (is_least_in_fset_wrt (\<prec>\<^sub>c)
        {|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|})"
      let ?\<F>' = "\<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})"
      let ?j = "i\<^sub>0 + count D' L"

      obtain D' :: "('f, 'v) term clause" where
        "cls_of_gcls D = add_mset (lit_of_glit L) D'"
        by (metis cls_of_gcls_def hyps(5) image_mset_add_mset is_maximal_wrt_def multi_member_split)

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
            "trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
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

      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (?\<Gamma>\<^sub>2\<^sub>a, U, None))")
        case ex_conflict: True
        have "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = ((?\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls ?E, Var)), ?j, D, ?\<F>')"
          using hyps(14)
          unfolding Let_def
          unfolding if_P[OF pos_L_and_undef_L_and_false_D]
          unfolding if_not_P[of "\<not> _", unfolded not_not, OF ex_conflict]
          by simp

        moreover have "scl_fol.propagate N' \<beta>' (\<Gamma>\<^sub>1, U, None) (?\<Gamma>\<^sub>2\<^sub>b, U, None)"
        proof (rule scl_fol.propagateI[of _ _ _ _ _ Var _ _ _ _ Var,
              unfolded subst_lit_id_subst subst_cls_id_subst])
          show "cls_of_gcls D |\<in>| N' |\<union>| U"
            using \<open>cls_of_gcls D |\<in>| N' |\<union>| U\<close> by force
        next
          show "\<forall>K\<in>#cls_of_gcls D. less_B\<^sup>=\<^sup>= (atm_of K) \<beta>'"
          proof (intro ballI)
            fix K :: "('f, 'v) Term.term literal"
            assume "K \<in># cls_of_gcls D"
            then obtain K' where "K = lit_of_glit K'" and "K' \<in># D"
              by (metis cls_of_gcls_def image_iff multiset.set_map)

            have "atm_of K' |\<in>| atms_of_clss N"
              using lit_in_N_if_in_D[OF \<open>K' \<in># D\<close>]
              using atm_of_lit_in_atms_of
              by (smt (verit, del_insts) UN_E atms_of_cls_def atms_of_clss_def atms_of_def
                  fmember_ffUnion_iff fset.set_map fset_fset_mset)
            thus "less_B\<^sup>=\<^sup>= (atm_of K) \<beta>'"
              unfolding N'_def \<beta>'_def reflclp_iff less_B_def
              using \<beta>_greatest
              by (auto simp add: \<open>K = lit_of_glit K'\<close> atm_of_lit_of_glit_conv is_greatest_in_set_wrt_iff)
          qed
        next
          show "cls_of_gcls D = add_mset (lit_of_glit L) D'"
            using \<open>cls_of_gcls D = add_mset (lit_of_glit L) D'\<close> .
        next
          have 1: "cls_of_gcls {#K \<in># D. K \<noteq> L#} =
            {#K \<in># cls_of_gcls D. glit_of_lit K \<noteq> glit_of_lit (lit_of_glit L)#}"
            by (simp add: image_mset_filter_mset_swap[of lit_of_glit, folded cls_of_gcls_def, symmetric])
          hence "cls_of_gcls {#K \<in># D. K \<noteq> L#} = {#K \<in># cls_of_gcls D. K \<noteq> lit_of_glit L#}"
            by (smt (verit, best) cls_of_gcls_def filter_mset_cong0 glit_of_lit_lit_of_glit
                image_mset_filter_swap2)
          thus "cls_of_gcls {#K \<in># D. K \<noteq> L#} = {#K \<in># D'. K \<noteq> lit_of_glit L#}"
            using \<open>cls_of_gcls D = add_mset (lit_of_glit L) D'\<close>
            by (smt (verit, del_insts) filter_mset_add_mset)
        next
          show "trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
            using pos_L_and_undef_L_and_false_D by simp
        next
          have "is_imgu Var {{atm_of (lit_of_glit L)}}"
            by (simp add: is_imgu_def is_unifiers_def is_unifier_alt)
          moreover have "atm_of ` set_mset (add_mset (lit_of_glit L) {#K \<in># D'. K = lit_of_glit L#}) = {atm_of (lit_of_glit L)}"
            by auto
          ultimately show "is_imgu Var {atm_of ` set_mset
            (add_mset (lit_of_glit L) {#K \<in># D'. K = lit_of_glit L#})}"
            by metis
        next
          show "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)"
            using \<open>\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)\<close> .
        qed simp_all

        moreover have "scl_fol.conflict N' \<beta>' (?\<Gamma>\<^sub>2\<^sub>b, U, None) (?\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls ?E, Var))"
        proof -
          have "\<exists>E. is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} E"
          proof (rule ex_least_element)
            from ex_conflict obtain E \<gamma> where
              E_in: "E |\<in>| (cls_of_gcls |`| N) |\<union>| U" and
              "is_ground_cls (E \<cdot> \<gamma>)" and
              "trail_false_cls ?\<Gamma>\<^sub>2\<^sub>a (E \<cdot> \<gamma>)"
              by (auto elim!: scl_fol.conflict.cases)

            from E_in obtain E\<^sub>G where
              "E\<^sub>G |\<in>| N |\<union>| gcls_of_cls |`| U" and "E = cls_of_gcls E\<^sub>G"
              by (metis cls_of_gcls_gcls_of_cls_ident fimage_iff funion_iff ground_cls_if_in_U)
            moreover have "trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls E\<^sub>G)"
              using \<open>trail_false_cls ?\<Gamma>\<^sub>2\<^sub>a (E \<cdot> \<gamma>)\<close>[unfolded \<open>E = cls_of_gcls E\<^sub>G\<close>]
              by (simp add: trail_false_cls_def trail_false_lit_def decide_lit_def propagate_lit_def)
            ultimately show "fset {|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} \<noteq> {}"
              by auto
          qed simp_all
          then obtain E where
            E_least: "is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
              trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} E"
            by metis
          hence "?E = E"
            by (simp add: the1_equality' Uniq_is_least_in_set_wrt)

          show ?thesis
          proof (rule scl_fol.conflictI)
            have "E |\<in>| N |\<union>| gcls_of_cls |`| U"
              using E_least by (simp add: is_least_in_set_wrt_iff)
            thus "cls_of_gcls ?E |\<in>| N' |\<union>| U"
              unfolding \<open>?E = E\<close> N'_def
              using ground_cls_if_in_U by auto
          next
            show "is_ground_cls (cls_of_gcls ?E \<cdot> Var)"
              by simp
          next
            have "trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls E)"
              using E_least by (simp add: is_least_in_set_wrt_iff)
            thus "trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls ?E \<cdot> Var)"
              unfolding \<open>?E = E\<close>
              by simp
          qed
        qed

        ultimately have "(scl_fol.propagate N' \<beta>' OO scl_fol.conflict N' \<beta>') S\<^sub>1 S\<^sub>2"
          by (auto simp: S\<^sub>1_def)
        thus ?thesis
          by simp
      next
        case False
        hence "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = ((?\<Gamma>\<^sub>2\<^sub>a, U, None), ?j, D, ?\<F>')"
          using hyps(14) pos_L_and_undef_L_and_false_D by simp
        moreover have "scl_fol.decide N' \<beta>'
          (\<Gamma>\<^sub>1, U, None) (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L \<cdot>l Var), U, None)"
        proof (rule scl_fol.decideI)
          show "lit_of_glit L \<in> \<Union> (set_mset ` fset N')"
            using \<open>L \<in> \<Union> (set_mset ` fset N)\<close>
            by (simp add: N'_def cls_of_gcls_def inj_image_mem_iff[OF inj_lit_of_glit])
        next
          show "is_ground_lit (lit_of_glit L \<cdot>l Var)"
            by simp
        next
          show "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L \<cdot>l Var)"
            using \<open>\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)\<close> by simp
        next
          have "atm_of L |\<in>| atms_of_clss N"
            using \<open>L \<in> \<Union> (set_mset ` fset N)\<close>
            by (smt (verit, del_insts) UN_E atms_of_cls_def atms_of_clss_def fimage_eqI
                fmember_ffUnion_iff fset_fset_mset)
          with \<beta>_greatest show "scl_fol.lesseq_B (atm_of (lit_of_glit L) \<cdot>a Var) \<beta>'"
            by (auto simp add: less_B_def atm_of_lit_of_glit_conv \<beta>'_def is_greatest_in_set_wrt_iff)
        qed

        ultimately have "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2"
          using hyps(9) by fastforce
        thus ?thesis
          by simp
      qed
    next
      case False
      hence "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)"
        using hyps(14) by auto
      thus ?thesis
        by simp
    qed
  qed
qed


subsection \<open>Sematincs of ORD-RES, ORD-RES++, SCL(FOL)++, and SCL(FOL)\<close>

inductive ord_reso_step where
  factoring: "{#} |\<notin>| N \<Longrightarrow> P |\<in>| N \<Longrightarrow> ord_res.ground_factoring P C \<Longrightarrow>
    ord_reso_step N (finsert C N)" |
  resolution: "{#} |\<notin>| N \<Longrightarrow> P1 |\<in>| N \<Longrightarrow> P2 |\<in>| N \<Longrightarrow> ord_res.ground_resolution P1 P2 C \<Longrightarrow>
    ord_reso_step N (finsert C N)"

interpretation ord_reso_semantics: semantics where
  step = ord_reso_step and
  final = "\<lambda>N. {#} |\<in>| N"
proof unfold_locales
  show "\<And>N. {#} |\<in>| N \<Longrightarrow> finished ord_reso_step N"
    by (simp add: finished_def ord_reso_step.simps)
qed

interpretation ord_reso_extended_semantics: semantics where
  step = ord_res_mod_op_strategy and
  final = "\<lambda>N. {#} |\<in>| N"
proof unfold_locales
  fix N :: "'f gterm clause fset" assume "{#} |\<in>| N"
  show "finished ord_res_mod_op_strategy N"
    unfolding finished_def
  proof (intro notI, elim exE)
    fix N' assume "ord_res_mod_op_strategy N N'"
    then obtain L C where C_min: "is_min_false_clause N C" and L_max: "ord_res.is_maximal_lit L C"
      unfolding ord_res_mod_op_strategy_def by metis

    have "is_min_false_clause N {#}"
      unfolding is_min_false_clause_def
      unfolding is_minimal_in_set_wrt_def[OF linorder_cls.transp_on_less linorder_cls.asymp_on_less]
      unfolding non_reachable_wrt_def
    proof (intro conjI ballI)
      show "{#} |\<in>| {|C |\<in>| N. \<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C|}"
        using \<open>{#} |\<in>| N\<close> by auto
    next
      show "\<And>y. \<not> y \<prec>\<^sub>c {#}"
        by (metis add.left_neutral empty_iff linorder_cls.less_irrefl
            linorder_cls.order.strict_trans one_step_implies_multp set_mset_empty)
    qed
    with C_min have "C = {#}"
      using Uniq_is_min_false_clause by (metis Uniq_D)
    with L_max show False
      by (simp add: is_maximal_wrt_def)
  qed
qed

interpretation scl_reso_semantics: semantics where
  step = "\<lambda>S\<^sub>0 S\<^sub>2. \<exists>S\<^sub>1. scl_reso1 N \<beta> S\<^sub>0 S\<^sub>1 S\<^sub>2" and
  final = "\<lambda>S. \<exists>\<gamma>. state_trail (fst S) = [] \<and> state_conflict (fst S) = Some ({#}, \<gamma>)"
proof unfold_locales
  show "\<And>S. \<exists>\<gamma>. state_trail (fst S) = [] \<and> state_conflict (fst S) = Some ({#}, \<gamma>) \<Longrightarrow>
    finished (\<lambda>S\<^sub>0 S\<^sub>2. \<exists>S\<^sub>1. scl_reso1 N \<beta> S\<^sub>0 S\<^sub>1 S\<^sub>2) S"
    unfolding finished_def scl_reso1.simps
    by force
qed

interpretation scl_fol_semantics: semantics where
  step = "scl_fol.scl N \<beta>" and
  final = "\<lambda>S. \<exists>\<gamma>. state_trail S = [] \<and> state_conflict S = Some ({#}, \<gamma>)"
proof unfold_locales
  show "\<And>S. \<exists>\<gamma>. state_trail S = [] \<and> state_conflict S = Some ({#}, \<gamma>) \<Longrightarrow>
    finished (scl_fol.scl N \<beta>) S"
    using scl_fol.no_more_step_if_conflict_mempty
    by (auto simp: finished_def)
qed


subsection \<open>Backward simulation between ORD-RES and ORD-RES++\<close>

interpretation backward_simulation_with_measuring_function where
  step1 = ord_reso_step and
  step2 = ord_res_mod_op_strategy and
  final1 = "\<lambda>N. {#} |\<in>| N" and
  final2 = "\<lambda>N. {#} |\<in>| N" and
  order = "\<lambda>_ _. False" and
  match = "(=)" and
  measure = "\<lambda>_. ()"
proof unfold_locales
  show "wfP (\<lambda>_ _. False)"
    by auto
next
  show "\<And>N1 N2. N1 = N2 \<Longrightarrow> {#} |\<in>| N2 \<Longrightarrow> {#} |\<in>| N1"
    by metis
next
  fix N1 N2 N2' assume "N1 = N2" and "ord_res_mod_op_strategy N2 N2'"
  then obtain L C where
    C_min: "is_min_false_clause N2 C" and
    L_max: "ord_res.is_maximal_lit L C" and
    fact_or_reso: "(case L of
       Pos A \<Rightarrow> \<not> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos A) C \<and>
       (\<exists>C'. ord_res.ground_factoring C C' \<and> N2' = finsert C' N2)
     | Neg A \<Rightarrow> \<exists>D|\<in>|N2. D \<prec>\<^sub>c C \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos A) D \<and>
       (\<exists>CD. ord_res.ground_resolution C D CD \<and> N2' = finsert CD N2))"
    unfolding ord_res_mod_op_strategy_def by blast

  from C_min have "C |\<in>| N2"
    by (simp add: is_min_false_clause_def is_minimal_in_set_wrt_iff)

  from C_min L_max have "{#} |\<notin>| N2"
    using Uniq_is_min_false_clause
    by (meson \<open>ord_res_mod_op_strategy N2 N2'\<close> ord_reso_extended_semantics.final_finished
        ord_reso_extended_semantics.semantics_axioms semantics.finished_step)

  have "\<exists>N1'. ord_reso_step\<^sup>+\<^sup>+ N1 N1' \<and> N1' = N2'"
  proof (cases L)
    case (Pos A)
    with fact_or_reso obtain C' where "ord_res.ground_factoring C C'" and "N2' = finsert C' N2"
      by auto
    hence "ord_reso_step N1 N2'"
      using ord_reso_step.factoring \<open>{#} |\<notin>| N2\<close> \<open>C |\<in>| N2\<close> \<open>N1 = N2\<close> by metis
    thus ?thesis
      by simp
  next
    case (Neg A)
    with fact_or_reso obtain D CD where
      "D |\<in>| N2" and
      "ord_res.ground_resolution C D CD" and
      "N2' = finsert CD N2"
      by auto
    hence "ord_reso_step N1 N2'"
      using ord_reso_step.resolution \<open>{#} |\<notin>| N2\<close> \<open>C |\<in>| N2\<close> \<open>N1 = N2\<close> by metis
    thus ?thesis
      by simp
  qed
  thus "(\<exists>N1'. ord_reso_step\<^sup>+\<^sup>+ N1 N1' \<and> N1' = N2') \<or> N1 = N2' \<and> False"
    by metis
qed

subsection \<open>Backward simulation between ORD-RES++ and SCL(FOL)++\<close>

lemma atms_of_eq_fset_atms_of_cls: "atms_of C = fset (atms_of_cls C)"
  by (simp add: atms_of_cls_def atms_of_def)

lemma ord_res_mod_op_strategy_preserves_atms_of_clss:
  assumes step: "ord_res_mod_op_strategy N N'"
  shows "atms_of_clss N = atms_of_clss N'"
proof -
  from step obtain L C where
    C_min: "is_min_false_clause N C" and
    L_max: "ord_res.is_maximal_lit L C" and
    case_L: "case L of
       Pos A \<Rightarrow> \<not> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos A) C \<and> (\<exists>C'. ord_res.ground_factoring C C' \<and> N' = finsert C' N)
     | Neg A \<Rightarrow> \<exists>D|\<in>|N. D \<prec>\<^sub>c C \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos A) D \<and>
       (\<exists>CD. ord_res.ground_resolution C D CD \<and> N' = finsert CD N)"
    unfolding ord_res_mod_op_strategy_def
    by auto

  from C_min have "C |\<in>| N"
    by (simp add: is_min_false_clause_def is_minimal_in_set_wrt_def non_reachable_wrt_iff)

  show ?thesis
  proof (cases L)
    case (Pos A)
    with case_L obtain C' where
      "ord_res.ground_factoring C C'" and
      "N' = finsert C' N"
      by auto
    moreover have "atms_of_cls C' = atms_of_cls C"
      using ord_res.atms_of_concl_eq_if_ground_factoring[OF \<open>ord_res.ground_factoring C C'\<close>]
      by (simp add: atms_of_eq_fset_atms_of_cls fset_cong)
    ultimately show ?thesis
      using \<open>C |\<in>| N\<close>
      by (simp add: atms_of_clss_def)
  next
    case (Neg A)
    with case_L obtain D CD where
      "D |\<in>| N" and
      "ord_res.ground_resolution C D CD" and
      "N' = finsert CD N"
      by auto

    have "atms_of_clss N' = atms_of_clss (finsert CD N)"
      unfolding \<open>N' = finsert CD N\<close> ..
    also have "\<dots> = atms_of_cls CD |\<union>| atms_of_clss N"
      by (simp add: atms_of_clss_def)
    also have "\<dots> |\<subseteq>| atms_of_cls C |\<union>| atms_of_cls D |\<union>| atms_of_clss N"
      using \<open>ord_res.ground_resolution C D CD\<close> ord_res.atms_of_concl_subset_if_ground_resolution
      by (metis atms_of_eq_fset_atms_of_cls fsubsetI less_eq_fset.rep_eq sup_mono union_fset)
    also have "\<dots> = atms_of_clss N"
      using \<open>C |\<in>| N\<close> \<open>D |\<in>| N\<close>
      by (auto simp: atms_of_clss_def fmember_ffUnion_iff)
    finally show "atms_of_clss N = atms_of_clss N'"
      unfolding \<open>N' = finsert CD N\<close>
      using \<open>atms_of_clss (finsert CD N) = atms_of_cls CD |\<union>| atms_of_clss N\<close> by blast
  qed
qed

lemma compower_ord_res_mod_op_strategy_preserves_atms_of_clss:
  "(ord_res_mod_op_strategy ^^ i) N N\<^sub>i \<Longrightarrow> atms_of_clss N = atms_of_clss N\<^sub>i"
proof (induction i arbitrary: N\<^sub>i)
  case 0
  then show ?case
    by simp
next
  case (Suc i')
  from Suc.prems obtain N\<^sub>i\<^sub>' where
    "(ord_res_mod_op_strategy ^^ i') N N\<^sub>i\<^sub>'" and "ord_res_mod_op_strategy N\<^sub>i\<^sub>' N\<^sub>i"
    by auto

  have "atms_of_clss N = atms_of_clss N\<^sub>i\<^sub>'"
    using Suc.IH[OF \<open>(ord_res_mod_op_strategy ^^ i') N N\<^sub>i\<^sub>'\<close>] .
  also have "\<dots> = atms_of_clss N\<^sub>i"
    using ord_res_mod_op_strategy_preserves_atms_of_clss[OF \<open>ord_res_mod_op_strategy N\<^sub>i\<^sub>' N\<^sub>i\<close>] .
  finally show ?case .
qed

lemma atoms_of_learn_clauses_already_in_initial_clauses:
  assumes
    \<beta>_greatest: "is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta>" and
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    N_generalizes: "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>0" and
    "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>0) |\<subseteq>| atms_of_clss N"
  shows
    "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| atms_of_clss N"
    "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| atms_of_clss N"
  using step
  unfolding atomize_conj
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case (scl_reso1I D U L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')
  have "(scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
    using \<beta>_greatest step N_generalizes correctness_scl_reso1(1) by metis
  hence N_generalizes_S\<^sub>1:
    "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>1"
    using N_generalizes
    by (induction S\<^sub>1 rule: rtranclp_induct)
      (simp_all add: scl_fol.decide_preserves_initial_lits_generalize_learned_trail_conflict)

  have "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| atms_of_clss N"
  proof -
    have "\<Union> (set_mset ` fset (state_learned S\<^sub>1)) \<subseteq> \<Union> (set_mset ` fset (cls_of_gcls |`| N))"
      using N_generalizes_S\<^sub>1[THEN lits_of_learned_subset_lits_of_initial] by metis
    hence "\<Union> (set_mset ` fset (gcls_of_cls |`| state_learned S\<^sub>1)) \<subseteq> \<Union> (set_mset ` fset N)"
      using glits_subset_if_lits_subset by metis
    hence "ffUnion (fset_mset |`| gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| ffUnion (fset_mset |`| N)"
      by (smt (verit, best) UN_E UN_I basic_trans_rules(31) fmember_ffUnion_iff fset_fset_mset
          fsubsetI)
    thus ?thesis
      unfolding atms_of_clss_def atms_of_cls_def
      by (metis fimage_ffUnion fimage_fimage fimage_mono)
  qed

  moreover have "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| atms_of_clss N"
  proof -
    have "scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>) S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.propagate (cls_of_gcls |`| N) (term_of_gterm \<beta>) OO
        scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>)) S\<^sub>1 S\<^sub>2 \<or>
      S\<^sub>2 = S\<^sub>1"
      using \<beta>_greatest step N_generalizes correctness_scl_reso1(2) by blast
    hence "scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) S\<^sub>1 S\<^sub>2 \<or>
      (scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) OO
        scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>)) S\<^sub>1 S\<^sub>2 \<or>
      S\<^sub>2 = S\<^sub>1"
      by (auto simp add: scl_fol.scl_def)
    hence "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>*\<^sup>* S\<^sub>1 S\<^sub>2"
      by auto
    hence "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>2"
      using N_generalizes_S\<^sub>1
      by (induction S\<^sub>2 rule: rtranclp_induct)
        (simp_all add: scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict)
    hence "\<Union> (set_mset ` fset (state_learned S\<^sub>2)) \<subseteq> \<Union> (set_mset ` fset (cls_of_gcls |`| N))"
      using N_generalizes_S\<^sub>1 lits_of_learned_subset_lits_of_initial by metis
    hence "\<Union> (set_mset ` fset (gcls_of_cls |`| state_learned S\<^sub>2)) \<subseteq> \<Union> (set_mset ` fset N)"
      using glits_subset_if_lits_subset by metis
    hence "ffUnion (fset_mset |`| gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| ffUnion (fset_mset |`| N)"
      by (smt (verit, del_insts) UN_E UN_I fmember_ffUnion_iff fmember_fset_mset_iff fsubsetI
          subsetD)
    thus ?thesis
      unfolding atms_of_clss_def atms_of_cls_def
      by (metis fimage_ffUnion fimage_fimage fimage_mono)
  qed

  ultimately show "
    atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| atms_of_clss N \<and>
    atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| atms_of_clss N"
    by (intro conjI)
qed

subsection \<open>Forward simulation between SCL(FOL)++ and SCL(FOL)\<close>

fun \<M> :: "'f gterm clause fset \<Rightarrow>
  ('f, 'v) state \<times> nat \<times> 'f gterm clause \<times> ('f gterm clause \<Rightarrow> 'f gterm clause) \<Rightarrow>
  'f gterm clause fset" where
  "\<M> N (S, _, C, \<F>) = {|D |\<in>| N |\<union>| gcls_of_cls |`| state_learned S. \<F> C \<prec>\<^sub>c \<F> D|}"

interpretation forward_simulation_with_measuring_function where
  step1 = "\<lambda>S\<^sub>0 S\<^sub>2. \<exists>S\<^sub>1. scl_reso1 N \<beta> S\<^sub>0 S\<^sub>1 S\<^sub>2" and
  step2 = "scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>)" and
  final1 = "\<lambda>S. \<exists>\<gamma>. state_trail (fst S) = [] \<and> state_conflict (fst S) = Some ({#}, \<gamma>)" and
  final2 = "\<lambda>S. \<exists>\<gamma>. state_trail S = [] \<and> state_conflict S = Some ({#}, \<gamma>)" and
  order = "(|\<subset>|)" and
  match = "\<lambda>S1 S2. fst S1 = S2 \<and> is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta> \<and>
    scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2" and
  measure = "\<M> N"
proof unfold_locales
  show "wfP (|\<subset>|)"
    by auto
next
  show "\<And>n s1 s2. fst s1 = s2 \<and> is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta> \<and>
    scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) s2 \<Longrightarrow>
    \<exists>\<gamma>. state_trail (fst s1) = [] \<and> state_conflict (fst s1) = Some ({#}, \<gamma>) \<Longrightarrow>
    \<exists>\<gamma>. state_trail s2 = [] \<and> state_conflict s2 = Some ({#}, \<gamma>)"
    by simp
next
  fix S1 S2 S1'
  assume
    match: "fst S1 = S2 \<and> is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta> \<and>
      scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2" and
    step: "\<exists>S1''. scl_reso1 N \<beta> S1 S1'' S1'"
  from match have
    "fst S1 = S2" and
    \<beta>_greatest: "is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta>" and
    init_geneneralize: "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2"
    by simp_all
  from step obtain S\<^sub>0 i\<^sub>0 C\<^sub>0 \<F>\<^sub>0 S\<^sub>1 i\<^sub>1 C\<^sub>1 \<F>\<^sub>1 S\<^sub>2 i\<^sub>2 C\<^sub>2 \<F>\<^sub>2 where
    "S1 = (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" and
    "S1' = (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    step': "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)"
    by (metis prod_cases3)

  have init_geneneralize': "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>0"
    using init_geneneralize
    unfolding \<open>fst S1 = S2\<close>[symmetric] \<open>S1 = (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)\<close> prod.sel .

  have 1: "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
    using correctness_scl_reso1(1)[OF \<beta>_greatest step' init_geneneralize']
    by (metis mono_rtranclp scl_fol.scl_def)

  show "
    (\<exists>S2'. (scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S2 S2' \<and>
      fst S1' = S2' \<and> is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta> \<and>
      scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2') \<or>
    ((fst S1' = S2 \<and> is_greatest_in_fset_wrt (\<prec>\<^sub>t) (atms_of_clss N) \<beta> \<and>
      scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2) \<and>
      \<M> N S1' |\<subset>| \<M> N S1)"
    using correctness_scl_reso1(2)[OF \<beta>_greatest step' init_geneneralize']
  proof (elim disjE)
    assume "scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>) S\<^sub>1 S\<^sub>2"
    hence 2: "scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) S\<^sub>1 S\<^sub>2"
      by (simp add: scl_fol.scl_def)

    from 1 2 have "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S\<^sub>0 S\<^sub>2"
      by simp
    moreover hence "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>2"
      using init_geneneralize'
      by (induction S\<^sub>2 rule: tranclp_induct)
        (simp_all add: scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict)
    ultimately show ?thesis
      unfolding \<open>fst S1 = S2\<close>[symmetric] \<open>S1 = (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)\<close> \<open>S1' = (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)\<close> prod.sel
      using \<beta>_greatest by metis
  next
    assume "(scl_fol.propagate (cls_of_gcls |`| N) (term_of_gterm \<beta>) OO
      scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>)) S\<^sub>1 S\<^sub>2"
    hence "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) OO
      scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>)) S\<^sub>1 S\<^sub>2"
      using relcompp_mono[of "scl_fol.propagate _ _" "scl_fol.scl _ _" "scl_fol.conflict _ _"
          "scl_fol.scl _ _"]
      by (smt (verit) relcompp.simps scl_fol.scl_def)
    hence 2: "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S\<^sub>1 S\<^sub>2"
      by auto

    from 1 2 have "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S\<^sub>0 S\<^sub>2"
      by simp
    moreover hence "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>2"
      using init_geneneralize'
      by (induction S\<^sub>2 rule: tranclp_induct)
        (simp_all add: scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict)
    ultimately show ?thesis
      unfolding \<open>fst S1 = S2\<close>[symmetric] \<open>S1 = (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)\<close> \<open>S1' = (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)\<close> prod.sel
      using \<beta>_greatest by metis
  next
    assume "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)"
    hence "S\<^sub>1 = S\<^sub>2" "i\<^sub>2 = i\<^sub>1" "C\<^sub>2 = C\<^sub>1" "\<F>\<^sub>2 = \<F>\<^sub>1"
      by simp_all
    with 1 show ?thesis
      unfolding prod.inject
      unfolding \<open>fst S1 = S2\<close>[symmetric] \<open>S1 = (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)\<close> \<open>S1' = (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)\<close> prod.sel
      using init_geneneralize'
    proof (induction S\<^sub>1 rule: rtranclp_induct)
      case base
      moreover have "\<M> N (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) |\<subset>| \<M> N (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)"
        unfolding \<open>S\<^sub>0 = S\<^sub>2\<close>[symmetric] \<M>.simps
      proof (rule pfsubset_ffilter)
        have "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1"
          using step' by (auto elim: scl_reso1.cases)
        moreover have "C\<^sub>1 = C\<^sub>2"
          using step'[THEN scl_reso1_clause2_eq_clause_3] .
        ultimately have "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1"
          by metis
        show "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 x"
          if x_in: "x |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0" and
            "\<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>2 x"
          for x
        proof (cases "x = C\<^sub>1")
          case True
          hence False
            using \<open>\<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>2 x\<close>
            unfolding True \<open>C\<^sub>1 = C\<^sub>2\<close>
            by order
          thus ?thesis ..
        next
          case False
          show ?thesis
            using scl_reso1_\<F>_eq(2)[OF step']
          proof (elim disjE exE conjE)
            assume "\<F>\<^sub>2 = \<F>\<^sub>1"
            have "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>2"
              using \<open>\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1\<close>
              by (simp only: \<open>C\<^sub>1 = C\<^sub>2\<close>)
            also have "\<dots> \<prec>\<^sub>c \<F>\<^sub>0 x"
              using \<open>\<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>2 x\<close>
              by (simp only: \<open>\<F>\<^sub>2 = \<F>\<^sub>1\<close> scl_reso1_\<F>_eq(1)[OF step'])
            finally show "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 x" .
          next
            fix L'
            assume
              L'_max: "ord_res.is_maximal_lit L' C\<^sub>1" and
              \<F>\<^sub>2_eq: "\<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L' {#K \<in># C\<^sub>1. K \<noteq> L'#})"

            have "\<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>0 x"
              using \<open>\<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>2 x\<close>
              unfolding \<F>\<^sub>2_eq fun_upd_other[OF False] scl_reso1_\<F>_eq(1)[OF step'] .

            have "\<not> (\<exists>D'|\<in>|N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0.
                \<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 D' \<and> \<F>\<^sub>0 D' \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1)"
              using step' by (auto elim: scl_reso1.cases)
            hence "\<not> (\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 x \<and> \<F>\<^sub>0 x \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1)"
              using x_in by metis
            hence "\<F>\<^sub>0 x \<preceq>\<^sub>c \<F>\<^sub>0 C\<^sub>0 \<or> \<F>\<^sub>0 C\<^sub>1 \<preceq>\<^sub>c \<F>\<^sub>0 x"
              using \<open>\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1\<close> by auto
            then show "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 x"
              using \<open>\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1\<close>[unfolded \<open>C\<^sub>1 = C\<^sub>2\<close>] \<open>\<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>0 x\<close>
              unfolding \<open>\<F>\<^sub>2 = \<F>\<^sub>1\<close> scl_reso1_\<F>_eq(1)[OF step']
              by order
          qed
        qed
        let ?x = "C\<^sub>1"
        show "?x |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0 \<and> \<not> \<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>2 ?x \<and> \<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 ?x"
        proof (intro conjI)
          show "?x |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0"
            using step' by (auto elim: scl_reso1.cases)
        next
          show "\<not> \<F>\<^sub>2 C\<^sub>2 \<prec>\<^sub>c \<F>\<^sub>2 C\<^sub>1"
            unfolding \<open>C\<^sub>1 = C\<^sub>2\<close> by order
        next
          show "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1"
            using \<open>\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 C\<^sub>1\<close> .
        qed
      qed
      ultimately show ?case
        apply -
        apply (rule disjI2)
        using \<beta>_greatest
        by simp
    next
      case (step y z)
      have "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S\<^sub>0 S\<^sub>2"
        using step.hyps step.prems(1) by simp
      moreover hence "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>2"
        apply (induction S\<^sub>2 rule: tranclp_induct)
        apply (simp add: scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict step.prems(5))
        using scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict by blast
      ultimately show ?case
        apply -
        apply (rule disjI1)
        using \<beta>_greatest
        by fastforce
    qed
  qed
qed

end
 
end