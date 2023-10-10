theory Min_Max_Least_Greatest_FSet
  imports
    Min_Max_Least_Greatest_Set
    "HOL-Library.FSet"
begin

section \<open>Minimal and maximal elements\<close>

definition is_minimal_in_fset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (fset X) R \<Longrightarrow> asymp_on (fset X) R \<Longrightarrow>
    is_minimal_in_fset_wrt R X = is_minimal_in_set_wrt R (fset X)"

definition is_maximal_in_fset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (fset X) R \<Longrightarrow> asymp_on (fset X) R \<Longrightarrow>
    is_maximal_in_fset_wrt R X = is_maximal_in_set_wrt R (fset X)"

context
  fixes X R
  assumes
    trans: "transp_on (fset X) R" and
    asym: "asymp_on (fset X) R"
begin


subsection \<open>Conversions\<close>

lemma is_minimal_in_fset_wrt_iff:
  "is_minimal_in_fset_wrt R X x \<longleftrightarrow> x |\<in>| X \<and> fBall X (\<lambda>y. y \<noteq> x \<longrightarrow> \<not> R y x)"
  using is_minimal_in_set_wrt_iff[OF trans asym]
  using is_minimal_in_fset_wrt_def[OF trans asym]
  by simp

lemma is_maximal_in_fset_wrt_iff:
  "is_maximal_in_fset_wrt R X x \<longleftrightarrow> x |\<in>| X \<and> fBall X (\<lambda>y. y \<noteq> x \<longrightarrow> \<not> R x y)"
  using is_maximal_in_set_wrt_iff[OF trans asym]
  using is_maximal_in_fset_wrt_def[OF trans asym]
  by simp


subsection \<open>Existence\<close>

lemma ex_minimal_in_fset_wrt:
  "X \<noteq> {||} \<Longrightarrow> \<exists>m. is_minimal_in_fset_wrt R X m"
  using trans asym ex_minimal_in_set_wrt[of "fset X" R] is_minimal_in_fset_wrt_def
  by (metis all_not_fin_conv empty_iff finite_fset)

lemma ex_maximal_in_fset_wrt:
  "X \<noteq> {||} \<Longrightarrow> \<exists>m. is_maximal_in_fset_wrt R X m"
  using trans asym ex_maximal_in_set_wrt[of "fset X" R] is_maximal_in_fset_wrt_def
  by (metis all_not_fin_conv empty_iff finite_fset)

end


section \<open>Least and greatest elements\<close>

definition is_least_in_fset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (fset X) R \<Longrightarrow> asymp_on (fset X) R \<Longrightarrow> totalp_on (fset X) R \<Longrightarrow>
    is_least_in_fset_wrt R X = is_least_in_set_wrt R (fset X)"

definition is_greatest_in_fset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (fset X) R \<Longrightarrow> asymp_on (fset X) R \<Longrightarrow> totalp_on (fset X) R \<Longrightarrow>
    is_greatest_in_fset_wrt R X = is_greatest_in_set_wrt R (fset X)"

context
  fixes X R
  assumes
    trans: "transp_on (fset X) R" and
    asym: "asymp_on (fset X) R" and
    tot: "totalp_on (fset X) R"
begin

subsection \<open>Conversions\<close>

lemma is_least_in_fset_wrt_iff:
  "is_least_in_fset_wrt R X x \<longleftrightarrow> x |\<in>| X \<and> fBall X (\<lambda>y. y \<noteq> x \<longrightarrow> R x y)"
  using is_least_in_set_wrt_iff[OF trans asym tot]
  using is_least_in_fset_wrt_def[OF trans asym tot]
  by simp

lemma is_greatest_in_fset_wrt:
  "is_greatest_in_fset_wrt R X x \<longleftrightarrow> x |\<in>| X \<and> fBall X (\<lambda>y. y \<noteq> x \<longrightarrow> R y x)"
  using is_greatest_in_set_wrt_iff[OF trans asym tot]
  using is_greatest_in_fset_wrt_def[OF trans asym tot]
  by simp

lemma is_minimal_in_fset_wrt_eq_is_least_in_fset_wrt:
  "is_minimal_in_fset_wrt R X = is_least_in_fset_wrt R X"
  using trans asym tot is_minimal_in_set_wrt_eq_is_least_in_set_wrt
  by (metis is_least_in_fset_wrt_def is_minimal_in_fset_wrt_def)

lemma is_maximal_in_fset_wrt_eq_is_greatest_in_fset_wrt:
  "is_maximal_in_fset_wrt R X = is_greatest_in_fset_wrt R X"
  using trans asym tot is_maximal_in_set_wrt_eq_is_greatest_in_set_wrt
  by (metis is_greatest_in_fset_wrt_def is_maximal_in_fset_wrt_def)


subsection \<open>Uniqueness\<close>

lemma Uniq_is_least_in_fset_wrt:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_least_in_fset_wrt R X x"
  using trans asym tot Uniq_is_least_in_set_wrt
  by (metis is_least_in_fset_wrt_def)

lemma Uniq_is_greatest_in_fset_wrt:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_greatest_in_fset_wrt R X x"
  using trans asym tot Uniq_is_greatest_in_set_wrt
  by (metis is_greatest_in_fset_wrt_def)


subsection \<open>Existence\<close>

lemma ex_least_in_fset_wrt:
  "X \<noteq> {||} \<Longrightarrow> \<exists>x. is_least_in_fset_wrt R X x"
  using trans asym tot ex_least_in_set_wrt
  by (metis bot_fset.rep_eq finite_fset fset_cong is_least_in_fset_wrt_def)

lemma ex_greatest_in_fset_wrt:
  "X \<noteq> {||} \<Longrightarrow> \<exists>x. is_greatest_in_fset_wrt R X x"
  using trans asym tot ex_greatest_in_set_wrt
  by (metis bot_fset.rep_eq finite_fset fset_cong is_greatest_in_fset_wrt_def)

lemma ex1_least_in_fset_wrt:
  "X \<noteq> {||} \<Longrightarrow> \<exists>!x. is_least_in_fset_wrt R X x"
  using Uniq_is_least_in_fset_wrt ex_least_in_fset_wrt
  by (metis Uniq_def)

lemma ex1_greatest_in_fset_wrt:
  "X \<noteq> {||} \<Longrightarrow> \<exists>!x. is_greatest_in_fset_wrt R X x"
  using Uniq_is_greatest_in_fset_wrt ex_greatest_in_fset_wrt
  by (metis Uniq_def)

end

end