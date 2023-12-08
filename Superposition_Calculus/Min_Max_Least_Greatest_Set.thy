theory Min_Max_Least_Greatest_Set
  imports
    Relation_Reachability
begin

section \<open>Minimal and maximal elements\<close>

text \<open>If the binary relation is a strict partial order, then non-reachability corresponds to
minimality and non-reaching correspond to maximality.\<close>

definition is_minimal_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> is_minimal_in_set_wrt R X = non_reachable_wrt R X"

definition is_maximal_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> is_maximal_in_set_wrt R X = non_reaching_wrt R X"

context
  fixes X R
  assumes
    trans: "transp_on X R" and
    asym: "asymp_on X R"
begin


subsection \<open>Conversions\<close>

lemma is_minimal_in_set_wrt_iff:
  "is_minimal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R y x)"
  using trans asym is_minimal_in_set_wrt_def[unfolded non_reachable_wrt_iff] by metis

lemma is_maximal_in_set_wrt_iff:
  "is_maximal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  using trans asym is_maximal_in_set_wrt_def[unfolded non_reaching_wrt_iff] by metis

subsection \<open>Existence\<close>

lemma ex_minimal_in_set_wrt:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_minimal_in_set_wrt R X x"
  using trans asym ex_non_reachable_wrt is_minimal_in_set_wrt_def by metis

lemma ex_maximal_in_set_wrt:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>m. is_maximal_in_set_wrt R X m"
  using trans asym is_maximal_in_set_wrt_def ex_non_reaching_wrt by metis

end


subsection \<open>Miscellaneous\<close>

lemma is_minimal_in_set_wrt_filter_iff:
  fixes X R
  assumes trans: "transp_on {y \<in> X. P y} R" and asym: "asymp_on {y \<in> X. P y} R"
  shows "is_minimal_in_set_wrt R {y \<in> X. P y} x \<longleftrightarrow> x \<in> X \<and> P x \<and> (\<forall>y \<in> X - {x}. P y \<longrightarrow> \<not> R y x)"
proof -
  have "is_minimal_in_set_wrt R {y \<in> X. P y} x \<longleftrightarrow> non_reachable_wrt R {y \<in> X. P y} x"
    using trans asym is_minimal_in_set_wrt_def by metis
  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> P x \<and> (\<forall>y \<in> X - {x}. P y \<longrightarrow> \<not> R y x)"
    unfolding non_reachable_wrt_filter_iff ..
  finally show ?thesis .
qed

lemma is_minimal_in_set_wrt_insertI:
  assumes
    trans: "transp_on (insert y X) R" and
    asym: "asymp_on (insert y X) R" and
    "R y x" and
    x_min: "is_minimal_in_set_wrt R X x"
  shows "is_minimal_in_set_wrt R (insert y X) y"
  by (metis assms(3) asym asymp_on_subset is_minimal_in_set_wrt_def trans
      non_reachable_wrt_insert_wrtI subset_insertI transp_on_subset x_min)


section \<open>Least and greatest elements\<close>

text \<open>If the binary relation is a strict total ordering, then an element reaching all others is a
least element and an element reachable by all others is a greatest element.\<close>

definition is_least_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow>
    is_least_in_set_wrt R X = reaching_all_wrt R X"

definition is_greatest_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow> totalp_on X R \<Longrightarrow>
    is_greatest_in_set_wrt R X = reachable_by_all_wrt R X"

context
  fixes X R
  assumes
    trans: "transp_on X R" and
    asym: "asymp_on X R" and
    tot: "totalp_on X R"
begin


subsection \<open>Conversions\<close>

lemma is_least_in_set_wrt_iff:
  "is_least_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R x y)"
  using trans asym tot is_least_in_set_wrt_def[unfolded reaching_all_wrt_iff] by metis

lemma is_greatest_in_set_wrt_iff:
  "is_greatest_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R y x)"
  using trans asym tot is_greatest_in_set_wrt_def[unfolded reachable_by_all_wrt_iff] by metis

lemma is_minimal_in_set_wrt_eq_is_least_in_set_wrt:
  "is_minimal_in_set_wrt R X = is_least_in_set_wrt R X"
  using trans asym tot non_reachable_wrt_eq_reaching_all_wrt
    is_minimal_in_set_wrt_def is_least_in_set_wrt_def
  by metis

lemma is_maximal_in_set_wrt_eq_is_greatest_in_set_wrt:
  "is_maximal_in_set_wrt R X = is_greatest_in_set_wrt R X"
  using trans asym tot non_reaching_wrt_eq_reachable_by_all_wrt
    is_maximal_in_set_wrt_def is_greatest_in_set_wrt_def
  by metis

subsection \<open>Uniqueness\<close>

lemma Uniq_is_least_in_set_wrt:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_least_in_set_wrt R X x"
  using trans asym tot is_least_in_set_wrt_def Uniq_reaching_all_wrt by metis

lemma Uniq_is_greatest_in_set_wrt:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_greatest_in_set_wrt R X x"
  using trans asym tot is_greatest_in_set_wrt_def Uniq_reachable_by_all_wrt by metis


subsection \<open>Existence\<close>

lemma ex_least_in_set_wrt:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_least_in_set_wrt R X x"
  using trans asym tot is_least_in_set_wrt_def ex_reaching_all_wrt by metis

lemma ex_greatest_in_set_wrt:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_greatest_in_set_wrt R X x"
  using trans asym tot is_greatest_in_set_wrt_def ex_reachable_by_all_wrt by metis

lemma ex1_least_in_set_wrt:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>!x. is_least_in_set_wrt R X x"
  using Uniq_is_least_in_set_wrt ex_least_in_set_wrt by (metis Uniq_def)

lemma ex1_greatest_in_set_wrt:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>!x. is_greatest_in_set_wrt R X x"
  using Uniq_is_greatest_in_set_wrt ex_greatest_in_set_wrt by (metis Uniq_def)

end


section \<open>Hide stuff\<close>

text \<open>We restrict the public interface to ease future internal changes.\<close>

hide_fact is_minimal_in_set_wrt_def is_maximal_in_set_wrt_def
hide_fact is_least_in_set_wrt_def is_greatest_in_set_wrt_def


section \<open>Integration in type classes\<close>

abbreviation (in order) is_minimal_in_set where
  "is_minimal_in_set \<equiv> is_minimal_in_set_wrt (<)"

abbreviation (in order) is_maximal_in_set where
  "is_maximal_in_set \<equiv> is_maximal_in_set_wrt (<)"

lemmas (in order) is_minimal_in_set_iff =
  is_minimal_in_set_wrt_iff[OF transp_on_less asymp_on_less]

lemmas (in order) is_maximal_in_set_iff =
  is_maximal_in_set_wrt_iff[OF transp_on_less asymp_on_less]

lemmas (in order) ex_minimal_in_set =
  ex_minimal_in_set_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) ex_maximal_in_set =
  ex_maximal_in_set_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) is_minimal_in_set_filter_iff =
  is_minimal_in_set_wrt_filter_iff[OF transp_on_less asymp_on_less]


abbreviation (in linorder) is_least_in_set where
  "is_least_in_set \<equiv> is_least_in_set_wrt (<)"

abbreviation (in linorder) is_greatest_in_set where
  "is_greatest_in_set \<equiv> is_greatest_in_set_wrt (<)"

lemmas (in linorder) is_least_in_set_iff =
  is_least_in_set_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_greatest_in_set_iff =
  is_greatest_in_set_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_minimal_in_set_eq_is_least_in_set =
  is_minimal_in_set_wrt_eq_is_least_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_maximal_in_set_eq_is_greatest_in_set =
  is_maximal_in_set_wrt_eq_is_greatest_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_least_in_set[intro] =
  Uniq_is_least_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_greatest_in_set[intro] =
  Uniq_is_greatest_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex_least_in_set =
  ex_least_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex_greatest_in_set =
  ex_greatest_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex1_least_in_set =
  ex1_least_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) ex1_greatest_in_set =
  ex1_greatest_in_set_wrt[OF transp_on_less asymp_on_less totalp_on_less]

end