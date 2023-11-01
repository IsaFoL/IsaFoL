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


subsection \<open>Miscellaneous\<close>

lemma is_minimal_in_fset_wrt_ffilter_iff:
  assumes
    tran: "transp_on (fset (ffilter P X)) R" and
    asym: "asymp_on (fset (ffilter P X)) R"
  shows "is_minimal_in_fset_wrt R (ffilter P X) x \<longleftrightarrow>
    (x |\<in>| X \<and> P x \<and> fBall (X - {|x|}) (\<lambda>y. P y \<longrightarrow> \<not> R y x))"
proof -
  have "is_minimal_in_fset_wrt R (ffilter P X) x \<longleftrightarrow> is_minimal_in_set_wrt R ({y \<in> fset X. P y}) x"
    using is_minimal_in_fset_wrt_iff[OF tran asym]
    using is_minimal_in_set_wrt_iff[OF tran asym]
    by (simp only: ffilter.rep_eq Set.filter_def)
  also have "\<dots> \<longleftrightarrow> x |\<in>| X \<and> P x \<and> (\<forall>y\<in>fset X - {x}. P y \<longrightarrow> \<not> R y x)"
  proof (rule is_minimal_in_set_wrt_filter_iff)
    show "transp_on {y. y |\<in>| X \<and> P y} R"
      using tran ffilter.rep_eq Set.filter_def by metis
  next
    show "asymp_on {y. y |\<in>| X \<and> P y} R"
      using asym ffilter.rep_eq Set.filter_def by metis
  qed
  finally show ?thesis
    by simp
qed

lemma is_minimal_in_fset_wrt_finsertI:
  assumes trans: "transp_on (fset (finsert y X)) R" and asym: "asymp_on (fset (finsert y X)) R"
  shows "R y x \<Longrightarrow> is_minimal_in_fset_wrt R X x \<Longrightarrow> is_minimal_in_fset_wrt R (finsert y X) y"
  using trans asym is_minimal_in_set_wrt_insertI[of _ "fset _", folded fset_simps]
  by (smt (verit) asymp_on_def finsertCI finsertE is_minimal_in_fset_wrt_iff transp_on_def)


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

lemma is_greatest_in_fset_wrt_iff:
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

lemma Uniq_is_least_in_fset_wrt[intro]:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_least_in_fset_wrt R X x"
  using trans asym tot Uniq_is_least_in_set_wrt
  by (metis is_least_in_fset_wrt_def)

lemma Uniq_is_greatest_in_fset_wrt[intro]:
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


subsection \<open>Miscellaneous\<close>

lemma is_least_in_ffilter_wrt_iff:
  assumes
    trans: "transp_on (fset (ffilter P X)) R" and
    asym: "asymp_on (fset (ffilter P X)) R" and
    tot: "totalp_on (fset (ffilter P X)) R"
  shows "is_least_in_fset_wrt R (ffilter P X) x \<longleftrightarrow>
    (x |\<in>| X \<and> P x \<and> fBall X (\<lambda>y. y \<noteq> x \<longrightarrow> P y \<longrightarrow> R x y))"
  unfolding is_least_in_fset_wrt_iff[OF trans asym tot] by auto


section \<open>Hide stuff\<close>

text \<open>We restrict the public interface to ease future internal changes.\<close>

hide_fact is_minimal_in_fset_wrt_def is_maximal_in_fset_wrt_def
hide_fact is_least_in_fset_wrt_def is_greatest_in_fset_wrt_def


section \<open>Integration in type classes\<close>

abbreviation (in order) is_minimal_in_fset where
  "is_minimal_in_fset \<equiv> is_minimal_in_fset_wrt (<)"

abbreviation (in order) is_maximal_in_fset where
  "is_maximal_in_fset \<equiv> is_maximal_in_fset_wrt (<)"

lemmas (in order) is_minimal_in_fset_iff =
  is_minimal_in_fset_wrt_iff[OF transp_on_less asymp_on_less]

lemmas (in order) is_maximal_in_fset_iff =
  is_maximal_in_fset_wrt_iff[OF transp_on_less asymp_on_less]

lemmas (in order) ex_minimal_in_fset =
  ex_minimal_in_fset_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) ex_maximal_in_fset =
  ex_maximal_in_fset_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) is_minimal_in_fset_ffilter_iff =
  is_minimal_in_fset_wrt_ffilter_iff[OF transp_on_less asymp_on_less]

lemmas (in order) is_minimal_in_fset_finsertI =
  is_minimal_in_fset_wrt_finsertI[OF transp_on_less asymp_on_less]


abbreviation (in linorder) is_least_in_fset where
  "is_least_in_fset \<equiv> is_least_in_fset_wrt (<)"

abbreviation (in linorder) is_greatest_in_fset where
  "is_greatest_in_fset \<equiv> is_greatest_in_fset_wrt (<)"

lemmas (in linorder) is_least_in_fset_iff =
  is_least_in_fset_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_greatest_in_fset_iff =
  is_greatest_in_fset_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_minimal_in_fset_eq_is_least_in_fset =
  is_minimal_in_fset_wrt_eq_is_least_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_maximal_in_fset_eq_is_greatest_in_fset =
  is_maximal_in_fset_wrt_eq_is_greatest_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_least_in_fset[intro] =
  Uniq_is_least_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_greatest_in_fset[intro] =
  Uniq_is_greatest_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex_least_in_fset =
  ex_least_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex_greatest_in_fset =
  ex_greatest_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex1_least_in_fset =
  ex1_least_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex1_greatest_in_fset =
  ex1_greatest_in_fset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_least_in_ffilter_iff =
  is_least_in_ffilter_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

end