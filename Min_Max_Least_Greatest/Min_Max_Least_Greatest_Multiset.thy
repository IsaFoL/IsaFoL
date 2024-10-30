theory Min_Max_Least_Greatest_Multiset
  imports
    Relation_Reachability
    Min_Max_Least_Greatest_Set
    "HOL-Library.Multiset"
    "HOL-Library.Multiset_Order"
begin

section \<open>Minimal and maximal elements\<close>

definition is_minimal_in_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (set_mset X) R \<Longrightarrow> asymp_on (set_mset X) R \<Longrightarrow>
    is_minimal_in_mset_wrt R X = is_minimal_in_set_wrt R (set_mset X)"

definition is_maximal_in_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (set_mset X) R \<Longrightarrow> asymp_on (set_mset X) R \<Longrightarrow>
    is_maximal_in_mset_wrt R X = is_maximal_in_set_wrt R (set_mset X)"

definition is_strictly_minimal_in_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (set_mset X) R \<Longrightarrow> asymp_on (set_mset X) R \<Longrightarrow>
    is_strictly_minimal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {# x #}. \<not> (R\<^sup>=\<^sup>= y x))"

definition is_strictly_maximal_in_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (set_mset X) R \<Longrightarrow> asymp_on (set_mset X) R \<Longrightarrow>
    is_strictly_maximal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {# x #}. \<not> (R\<^sup>=\<^sup>= x y))"

context
  fixes X R
  assumes
    trans: "transp_on (set_mset X) R" and
    asym: "asymp_on (set_mset X) R"
begin


subsection \<open>Conversions\<close>

lemma is_minimal_in_mset_wrt_iff:
  "is_minimal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X. y \<noteq> x \<longrightarrow> \<not> R y x)"
  using is_minimal_in_set_wrt_iff[OF trans asym]
  using is_minimal_in_mset_wrt_def[OF trans asym]
  by simp

lemma "is_minimal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X. \<not> R y x)"
  unfolding is_minimal_in_mset_wrt_iff
proof (rule refl_conj_eq, rule ball_cong)
  show "set_mset X = set_mset X" ..
next
  show "\<And>y. y \<in># X \<Longrightarrow> (y \<noteq> x \<longrightarrow> \<not> R y x) = (\<not> R y x)"
    using asym[THEN asymp_onD] by metis
qed

lemma is_maximal_in_mset_wrt_iff:
  "is_maximal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  using is_maximal_in_set_wrt_iff[OF trans asym]
  using is_maximal_in_mset_wrt_def[OF trans asym]
  by simp

lemma "is_maximal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X. \<not> R x y)"
  unfolding is_maximal_in_mset_wrt_iff
proof (rule refl_conj_eq, rule ball_cong)
  show "set_mset X = set_mset X" ..
next
  show "\<And>y. y \<in># X \<Longrightarrow> (y \<noteq> x \<longrightarrow> \<not> R x y) = (\<not> R x y)"
    using asym[THEN asymp_onD] by metis
qed

lemma is_strictly_minimal_in_mset_wrt_iff:
  "is_strictly_minimal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X- {# x #}. \<not> R\<^sup>=\<^sup>= y x)"
  unfolding is_strictly_minimal_in_mset_wrt_def[OF trans asym]
  by(rule refl)

lemma is_strictly_maximal_in_mset_wrt_iff:
  "is_strictly_maximal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X- {# x #}. \<not> R\<^sup>=\<^sup>= x y)"
  unfolding is_strictly_maximal_in_mset_wrt_def[OF trans asym]
  by(rule refl)

lemma is_minimal_in_mset_wrt_if_is_strictly_minimal_in_mset_wrt: 
  "is_strictly_minimal_in_mset_wrt R X x \<Longrightarrow> is_minimal_in_mset_wrt R X x"
  unfolding is_minimal_in_mset_wrt_iff is_strictly_minimal_in_mset_wrt_iff
  using multi_member_split by fastforce 

lemma is_maximal_in_mset_wrt_if_is_strictly_maximal_in_mset_wrt:
  "is_strictly_maximal_in_mset_wrt R X x \<Longrightarrow> is_maximal_in_mset_wrt R X x"
  unfolding is_maximal_in_mset_wrt_iff is_strictly_maximal_in_mset_wrt_iff
  using multi_member_split by fastforce


subsection \<open>Existence\<close>

lemma ex_minimal_in_mset_wrt:
  "X \<noteq> {#} \<Longrightarrow> \<exists>m. is_minimal_in_mset_wrt R X m"
  using trans asym ex_minimal_in_set_wrt[of "set_mset X" R] is_minimal_in_mset_wrt_def
  by (metis finite_set_mset set_mset_eq_empty_iff)

lemma ex_maximal_in_mset_wrt:
  "X \<noteq> {#} \<Longrightarrow> \<exists>m. is_maximal_in_mset_wrt R X m"
  using trans asym ex_maximal_in_set_wrt[of "set_mset X" R] is_maximal_in_mset_wrt_def
  by (metis finite_set_mset set_mset_eq_empty_iff)


subsection \<open>Miscellaneous\<close>

lemma explode_maximal_in_mset_wrt:
  assumes max: "is_maximal_in_mset_wrt R X x"
  obtains n :: nat where "replicate_mset (Suc n) x + {#y \<in># X. y \<noteq> x#} = X"
  using max[unfolded is_maximal_in_mset_wrt_iff]
  by (metis filter_eq_replicate_mset in_countE multiset_partition)

lemma explode_strictly_maximal_in_mset_wrt:
  assumes max: "is_strictly_maximal_in_mset_wrt R X x"
  shows "add_mset x {#y \<in># X. y \<noteq> x#} = X"
proof -
  have "x \<in># X" and "\<forall>y \<in># X - {#x#}. x \<noteq> y"
    using max unfolding is_strictly_maximal_in_mset_wrt_iff by simp_all

  have "add_mset x (X - {#x#}) = X"
    using \<open>x \<in># X\<close> by (metis insert_DiffM)

  moreover have "{#y \<in># X. y \<noteq> x#} = X - {#x#}"
    using \<open>\<forall>y \<in># X - {#x#}. x \<noteq> y\<close>
    by (smt (verit, best) \<open>x \<in># X\<close> add_diff_cancel_left' diff_subset_eq_self filter_mset_eq_conv
        insert_DiffM2 set_mset_add_mset_insert set_mset_empty singletonD)

  ultimately show ?thesis
    by (simp only:)
qed

end

lemma is_minimal_in_filter_mset_wrt_iff:
  assumes
    tran: "transp_on (set_mset (filter_mset P X)) R" and
    asym: "asymp_on (set_mset (filter_mset P X)) R"
  shows "is_minimal_in_mset_wrt R (filter_mset P X) x \<longleftrightarrow>
    (x \<in># X \<and> P x \<and> (\<forall>y \<in># X - {#x#}. P y \<longrightarrow> \<not> R y x))"
proof -
  have "is_minimal_in_mset_wrt R (filter_mset P X) x \<longleftrightarrow>
    is_minimal_in_set_wrt R ({y \<in> set_mset X. P y}) x"
    using is_minimal_in_mset_wrt_iff[OF tran asym]
    using is_minimal_in_set_wrt_iff[OF tran asym]
    by auto
  also have "\<dots> \<longleftrightarrow> x \<in># X \<and> P x \<and> (\<forall>y \<in> set_mset X - {x}. P y \<longrightarrow> \<not> R y x)"
  proof (rule is_minimal_in_set_wrt_filter_iff)
    show "transp_on {y. y \<in># X \<and> P y} R"
      using tran by simp
  next
    show "asymp_on {y. y \<in># X \<and> P y} R"
      using asym by simp
  qed
  finally show ?thesis
    by (metis (no_types, lifting) DiffD1 asym asymp_onD at_most_one_mset_mset_diff insertE
        insert_Diff is_minimal_in_mset_wrt_iff more_than_one_mset_mset_diff tran)
qed

lemma multp_if_maximal_of_lhs_is_less:
  assumes
    trans: "transp R" and
    asym: "asymp_on (set_mset M1) R" and
    tot: "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    "x1 \<in># M1" and "x2 \<in># M2" and
    "is_maximal_in_mset_wrt R M1 x1" and "R x1 x2"
  shows "multp R M1 M2"
proof (rule one_step_implies_multp[of _ _ _ "{#}", simplified])
  show "M2 \<noteq> {#}"
    using \<open>x2 \<in># M2\<close> by auto
next
  show "\<forall>k\<in>#M1. \<exists>j\<in>#M2. R k j"
    using assms
    using is_maximal_in_mset_wrt_iff[OF transp_on_subset[OF trans subset_UNIV] asym]
    by (metis Un_iff totalp_onD transpE)
qed


subsection \<open>Nonuniqueness\<close>

lemma
  fixes x :: 'a and y :: 'a
  assumes "x \<noteq> y"
  shows
    not_Uniq_is_minimal_in_mset_if_two_distinct_elements:
      "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
        transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
        (\<exists>\<^sub>\<le>\<^sub>1x. is_minimal_in_mset_wrt R X x))" and
    not_Uniq_is_maximal_in_mset_wrt_if_two_distinct_elements:
      "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
        transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
        (\<exists>\<^sub>\<le>\<^sub>1x. is_maximal_in_mset_wrt R X x))" and
    not_Uniq_is_strictly_minimal_in_mset_if_two_distinct_elements:
      "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
        transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
        (\<exists>\<^sub>\<le>\<^sub>1x. is_strictly_minimal_in_mset_wrt R X x))" and
    not_Uniq_is_strictly_maximal_in_mset_wrt_if_two_distinct_elements:
      "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
        transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
        (\<exists>\<^sub>\<le>\<^sub>1x. is_strictly_maximal_in_mset_wrt R X x))"
proof -
  let ?R = "\<lambda>_ _. False"
  let ?X = "{#x, y#}"

  have trans: "transp_on (set_mset ?X) ?R" and asym: "asymp_on (set_mset ?X) ?R"
    by (simp_all add: transp_onI asymp_onI)

  have "is_minimal_in_mset_wrt ?R ?X x" and "is_minimal_in_mset_wrt ?R ?X y"
    using is_minimal_in_mset_wrt_iff[OF trans asym] by simp_all

  thus "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
    transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
    (\<exists>\<^sub>\<le>\<^sub>1x. is_minimal_in_mset_wrt R X x))"
    using \<open>x \<noteq> y\<close> trans asym
    by (metis Uniq_D)

  have "is_maximal_in_mset_wrt ?R ?X x" and "is_maximal_in_mset_wrt ?R ?X y"
    using is_maximal_in_mset_wrt_iff[OF trans asym] by simp_all

  thus "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
    transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
    (\<exists>\<^sub>\<le>\<^sub>1x. is_maximal_in_mset_wrt R X x))"
    using \<open>x \<noteq> y\<close> trans asym
    by (metis Uniq_D)

  have "is_strictly_minimal_in_mset_wrt ?R ?X x" and "is_strictly_minimal_in_mset_wrt ?R ?X y"
    using \<open>x \<noteq> y\<close> is_strictly_minimal_in_mset_wrt_iff[OF trans asym] by simp_all

  thus "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
    transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
    (\<exists>\<^sub>\<le>\<^sub>1x. is_strictly_minimal_in_mset_wrt R X x))"
    using \<open>x \<noteq> y\<close> trans asym
    by (metis Uniq_D)

  have "is_strictly_maximal_in_mset_wrt ?R ?X x" and "is_strictly_maximal_in_mset_wrt ?R ?X y"
    using \<open>x \<noteq> y\<close> is_strictly_maximal_in_mset_wrt_iff[OF trans asym] by simp_all

  thus "\<not> (\<forall>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (X :: 'a multiset).
    transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
    (\<exists>\<^sub>\<le>\<^sub>1x. is_strictly_maximal_in_mset_wrt R X x))"
    using \<open>x \<noteq> y\<close> trans asym
    by (metis Uniq_D)
qed


section \<open>Least and greatest elements\<close>

definition is_least_in_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (set_mset X) R \<Longrightarrow> asymp_on (set_mset X) R \<Longrightarrow> totalp_on (set_mset X) R \<Longrightarrow>
    is_least_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {#x#}. R x y)"

definition is_greatest_in_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "transp_on (set_mset X) R \<Longrightarrow> asymp_on (set_mset X) R \<Longrightarrow> totalp_on (set_mset X) R \<Longrightarrow>
    is_greatest_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {#x#}. R y x)"

context
  fixes X R
  assumes
    trans: "transp_on (set_mset X) R" and
    asym: "asymp_on (set_mset X) R" and
    tot: "totalp_on (set_mset X) R"
begin

subsection \<open>Conversions\<close>

lemma is_least_in_mset_wrt_iff:
  "is_least_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {#x#}. R x y)"
  using is_least_in_mset_wrt_def[OF trans asym tot] .

lemma is_greatest_in_mset_wrt_iff:
  "is_greatest_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {#x#}. R y x)"
  using is_greatest_in_mset_wrt_def[OF trans asym tot] .

lemma is_minimal_in_mset_wrt_if_is_least_in_mset_wrt[intro]:
  "is_least_in_mset_wrt R X x \<Longrightarrow> is_minimal_in_mset_wrt R X x"
  unfolding is_minimal_in_mset_wrt_iff[OF trans asym]
  unfolding is_least_in_mset_wrt_def[OF trans asym tot]
  by (metis add_mset_remove_trivial_eq asym asymp_onD insert_noteq_member)

lemma is_maximal_in_mset_wrt_if_is_greatest_in_mset_wrt[intro]:
  "is_greatest_in_mset_wrt R X x \<Longrightarrow> is_maximal_in_mset_wrt R X x"
  unfolding is_maximal_in_mset_wrt_iff[OF trans asym]
  unfolding is_greatest_in_mset_wrt_def[OF trans asym tot]
  by (metis add_mset_remove_trivial_eq asym asymp_onD insert_noteq_member)

lemma is_strictly_minimal_in_mset_wrt_iff_is_least_in_mset_wrt: 
  "is_strictly_minimal_in_mset_wrt R X = is_least_in_mset_wrt R X"
  unfolding is_strictly_minimal_in_mset_wrt_iff[OF trans asym] is_least_in_mset_wrt_iff 
proof(intro ext iffI)
  fix x
  show "x \<in># X \<and> (\<forall>y\<in>#X - {#x#}. \<not> R\<^sup>=\<^sup>= y x) \<Longrightarrow> x \<in># X \<and> (\<forall>y \<in># X - {#x#}. R x y)"
    by (metis (mono_tags, lifting) in_diffD sup2CI tot totalp_onD)
next 
  fix x
  show "x \<in># X \<and> (\<forall>y \<in># X - {#x#}. R x y) \<Longrightarrow> x \<in># X \<and> (\<forall>y\<in>#X - {#x#}. \<not> R\<^sup>=\<^sup>= y x)"
    by (metis (full_types) asym asymp_onD in_diffD sup2E)
qed

lemma is_strictly_maximal_in_mset_wrt_iff_is_greatest_in_mset_wrt: 
  "is_strictly_maximal_in_mset_wrt R X = is_greatest_in_mset_wrt R X"
  unfolding is_strictly_maximal_in_mset_wrt_iff[OF trans asym] is_greatest_in_mset_wrt_iff 
proof(intro ext iffI)
  fix x
  show "x \<in># X \<and> (\<forall>y\<in>#X - {#x#}. \<not> R\<^sup>=\<^sup>= x y) \<Longrightarrow> x \<in># X \<and> (\<forall>y\<in>#X - {#x#}. R y x)"
    by (metis (mono_tags, lifting) in_diffD sup2CI tot totalp_onD)
next 
  fix x
  show "x \<in># X \<and> (\<forall>y\<in>#X - {#x#}. R y x) \<Longrightarrow> x \<in># X \<and> (\<forall>y\<in>#X - {#x#}. \<not> R\<^sup>=\<^sup>= x y)"
    by (metis (full_types) asym asymp_onD in_diffD sup2E)
qed

subsection \<open>Uniqueness\<close>

lemma Uniq_is_minimal_in_mset_wrt[intro]:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_minimal_in_mset_wrt R X x"
  unfolding is_minimal_in_mset_wrt_iff[OF trans asym]
  by (smt (verit, best) Uniq_I tot totalp_onD)

lemma Uniq_is_maximal_in_mset_wrt[intro]:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_maximal_in_mset_wrt R X x"
  unfolding is_maximal_in_mset_wrt_iff[OF trans asym]
  by (smt (verit, best) Uniq_I tot totalp_onD)

lemma Uniq_is_least_in_mset_wrt[intro]:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_least_in_mset_wrt R X x"
  using is_least_in_mset_wrt_iff
  by (smt (verit, best) Uniq_I asym asymp_onD insert_DiffM insert_noteq_member)

lemma Uniq_is_greatest_in_mset_wrt[intro]:
  "\<exists>\<^sub>\<le>\<^sub>1x. is_greatest_in_mset_wrt R X x"
  unfolding is_greatest_in_mset_wrt_iff
  by (smt (verit, best) Uniq_I asym asymp_onD insert_DiffM insert_noteq_member)


subsection \<open>Miscellaneous\<close>

lemma is_least_in_mset_wrt_iff_is_minimal_and_count_eq_one:
  "is_least_in_mset_wrt R X x \<longleftrightarrow> is_minimal_in_mset_wrt R X x \<and> count X x = 1"
proof (rule iffI)
  assume "is_least_in_mset_wrt R X x"
  thus "is_minimal_in_mset_wrt R X x \<and> count X x = 1"
    unfolding is_least_in_mset_wrt_iff is_minimal_in_mset_wrt_iff[OF trans asym]
    by (metis One_nat_def add_mset_remove_trivial_eq asym asymp_onD count_add_mset not_in_iff)
next
  assume "is_minimal_in_mset_wrt R X x \<and> count X x = 1"
  then show "is_least_in_mset_wrt R X x"
    unfolding is_least_in_mset_wrt_iff is_minimal_in_mset_wrt_iff[OF trans asym]
    by (metis count_single in_diffD in_diff_count nat_less_le tot totalp_onD)
qed

lemma is_greatest_in_mset_wrt_iff_is_maximal_and_count_eq_one:
  "is_greatest_in_mset_wrt R X x \<longleftrightarrow> is_maximal_in_mset_wrt R X x \<and> count X x = 1"
proof (rule iffI)
  assume "is_greatest_in_mset_wrt R X x"
  thus "is_maximal_in_mset_wrt R X x \<and> count X x = 1"
    unfolding is_greatest_in_mset_wrt_iff is_maximal_in_mset_wrt_iff[OF trans asym]
    by (metis One_nat_def add_mset_remove_trivial_eq asym asymp_onD count_add_mset not_in_iff)
next
  assume "is_maximal_in_mset_wrt R X x \<and> count X x = 1"
  then show "is_greatest_in_mset_wrt R X x"
    unfolding is_greatest_in_mset_wrt_iff is_maximal_in_mset_wrt_iff[OF trans asym]
    by (metis count_single in_diffD in_diff_count nat_less_le tot totalp_onD)
qed

lemma count_ge_2_if_minimal_in_mset_wrt_and_not_least_in_mset_wrt:
  assumes "is_minimal_in_mset_wrt R X x" and "\<not> is_least_in_mset_wrt R X x"
  shows "count X x \<ge> 2"
  using assms
  unfolding is_least_in_mset_wrt_iff_is_minimal_and_count_eq_one
  by (metis Suc_1 Suc_le_eq antisym_conv1 asym count_greater_eq_one_iff is_minimal_in_mset_wrt_iff
      trans)

lemma count_ge_2_if_maximal_in_mset_wrt_and_not_greatest_in_mset_wrt:
  assumes "is_maximal_in_mset_wrt R X x" and "\<not> is_greatest_in_mset_wrt R X x"
  shows "count X x \<ge> 2"
  using assms
  unfolding is_greatest_in_mset_wrt_iff_is_maximal_and_count_eq_one
  by (metis Suc_1 Suc_le_eq antisym_conv1 asym count_greater_eq_one_iff is_maximal_in_mset_wrt_iff
      trans)

lemma explode_greatest_in_mset_wrt:
  assumes max: "is_greatest_in_mset_wrt R X x"
  shows "add_mset x {#y \<in># X. y \<noteq> x#} = X"
  using max[folded is_strictly_maximal_in_mset_wrt_iff_is_greatest_in_mset_wrt]
  using explode_strictly_maximal_in_mset_wrt[OF trans asym]
  by metis

end


lemma multp\<^sub>H\<^sub>O_if_maximal_wrt_less_that_maximal_wrt:
  assumes
    trans: "transp_on (set_mset M1 \<union> set_mset M2) R" and
    asym: "asymp_on (set_mset M1 \<union> set_mset M2) R" and
    tot: "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    x1_maximal: "is_maximal_in_mset_wrt R M1 x1" and
    x2_maximal: "is_maximal_in_mset_wrt R M2 x2" and
    "R x1 x2"
  shows "multp\<^sub>H\<^sub>O R M1 M2"
proof -
  have
    trans1: "transp_on (set_mset M1) R" and trans2: "transp_on (set_mset M2) R" and
    asym1: "asymp_on (set_mset M1) R" and asym2: "asymp_on (set_mset M2) R" and
    tot1: "totalp_on (set_mset M1) R" and tot2: "totalp_on (set_mset M2) R"
    using trans[THEN transp_on_subset] asym[THEN asymp_on_subset] tot[THEN totalp_on_subset]
    by simp_all

  have x1_in: "x1 \<in># M1" and x1_gr: "\<forall>y\<in>#M1. y \<noteq> x1 \<longrightarrow> \<not> R x1 y"
    using x1_maximal[unfolded is_maximal_in_mset_wrt_iff[OF trans1 asym1]] by argo+

  have x2_in: "x2 \<in># M2" and x2_gr: "\<forall>y\<in>#M2. y \<noteq> x2 \<longrightarrow> \<not> R x2 y"
    using x2_maximal[unfolded is_maximal_in_mset_wrt_iff[OF trans2 asym2]] by argo+

  show "multp\<^sub>H\<^sub>O R M1 M2"
    unfolding multp\<^sub>H\<^sub>O_def
  proof (intro conjI)
    show "M1 \<noteq> M2"
      using x1_in x2_in x1_gr
      by (metis \<open>R x1 x2\<close> asym2 asymp_onD)
  next
    show "\<forall>y. count M2 y < count M1 y \<longrightarrow> (\<exists>x. R y x \<and> count M1 x < count M2 x)"
      using x1_in x2_in x1_gr x2_gr
      by (smt (verit, best) assms(6) asym1 asymp_onD count_greater_zero_iff count_inI
          dual_order.strict_trans local.trans subsetD sup_ge1 sup_ge2 tot1 totalp_onD transp_onD)
  qed
qed

lemma multp\<^sub>D\<^sub>M_if_maximal_wrt_less_that_maximal_wrt:
  assumes
    trans: "transp_on (set_mset M1 \<union> set_mset M2) R" and
    asym: "asymp_on (set_mset M1 \<union> set_mset M2) R" and
    tot: "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    x1_maximal: "is_maximal_in_mset_wrt R M1 x1" and
    x2_maximal: "is_maximal_in_mset_wrt R M2 x2" and
    "R x1 x2"
  shows "multp\<^sub>D\<^sub>M R M1 M2"
  using multp\<^sub>H\<^sub>O_if_maximal_wrt_less_that_maximal_wrt[OF assms, THEN multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M] .

lemma multp_if_maximal_wrt_less_that_maximal_wrt:
  assumes
    trans: "transp_on (set_mset M1 \<union> set_mset M2) R" and
    asym: "asymp_on (set_mset M1 \<union> set_mset M2) R" and
    tot: "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    x1_maximal: "is_maximal_in_mset_wrt R M1 x1" and
    x2_maximal: "is_maximal_in_mset_wrt R M2 x2" and
    "R x1 x2"
  shows "multp R M1 M2"
  using multp\<^sub>D\<^sub>M_if_maximal_wrt_less_that_maximal_wrt[OF assms, THEN multp\<^sub>D\<^sub>M_imp_multp] .


lemma multp\<^sub>H\<^sub>O_if_same_maximal_wrt_and_count_lt:
  assumes
    trans: "transp_on (set_mset M1 \<union> set_mset M2) R" and
    asym: "asymp_on (set_mset M1 \<union> set_mset M2) R" and
    tot: "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    x1_maximal: "is_maximal_in_mset_wrt R M1 x" and
    x2_maximal: "is_maximal_in_mset_wrt R M2 x" and
    "count M1 x < count M2 x"
  shows "multp\<^sub>H\<^sub>O R M1 M2"
  by (metis assms(6) asym asymp_on_subset count_inI is_greatest_in_set_wrt_iff
      is_maximal_in_mset_wrt_def is_maximal_in_set_wrt_eq_is_greatest_in_set_wrt less_zeroE
      local.trans multp\<^sub>H\<^sub>O_def order_less_imp_not_less sup_ge1 tot totalp_on_subset transp_on_subset
      x1_maximal)

lemma multp_if_same_maximal_wrt_and_count_lt:
  assumes
    trans: "transp_on (set_mset M1 \<union> set_mset M2) R" and
    asym: "asymp_on (set_mset M1 \<union> set_mset M2) R" and
    tot: "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    x1_maximal: "is_maximal_in_mset_wrt R M1 x" and
    x2_maximal: "is_maximal_in_mset_wrt R M2 x" and
    "count M1 x < count M2 x"
  shows "multp R M1 M2"
  using multp\<^sub>H\<^sub>O_if_same_maximal_wrt_and_count_lt[
      OF assms, THEN multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M, THEN multp\<^sub>D\<^sub>M_imp_multp] .

lemma less_than_maximal_wrt_if_multp\<^sub>H\<^sub>O:
  assumes
    trans: "transp_on (set_mset M1 \<union> set_mset M2) R" and
    asym: "asymp_on (set_mset M2) R" and
    tot: "totalp_on (set_mset M2) R" and
    x2_maximal: "is_maximal_in_mset_wrt R M2 x2" and
    "multp\<^sub>H\<^sub>O R M1 M2" and
    "x1 \<in># M1"
  shows "R\<^sup>=\<^sup>= x1 x2"
proof -
  have
    trans2: "transp_on (set_mset M2) R" and
    asym2: "asymp_on (set_mset M2) R" and
    tot2: "totalp_on (set_mset M2) R"
    using trans[THEN transp_on_subset] asym[THEN asymp_on_subset] tot[THEN totalp_on_subset]
    by simp_all

  have x2_in: "x2 \<in># M2" and x2_gr: "\<forall>y\<in>#M2. y \<noteq> x2 \<longrightarrow> \<not> R x2 y"
    using x2_maximal[unfolded is_maximal_in_mset_wrt_iff[OF trans2 asym2]] by argo+

  show ?thesis
  proof (cases "x1 \<in># M2")
    case True
    thus ?thesis
      using x2_gr by (metis (mono_tags) sup2CI tot2 totalp_onD x2_in)
  next
    case False

    hence "x1 \<in># M1 - M2"
      using \<open>x1 \<in># M1\<close> by (simp add: in_diff_count not_in_iff)

    moreover have "\<forall>k\<in>#M1 - M2. \<exists>x\<in>#M2 - M1. R k x"
      using multp\<^sub>H\<^sub>O_implies_one_step_strong(2)[OF \<open>multp\<^sub>H\<^sub>O R M1 M2\<close>] .

    ultimately obtain x where "x \<in># M2 - M1" and "R x1 x"
      by metis

    hence "x \<noteq> x2 \<longrightarrow> \<not> R x2 x"
      using x2_gr by (metis in_diffD)

    hence "x \<noteq> x2 \<longrightarrow> R x x2"
      by (metis \<open>x \<in># M2 - M1\<close> in_diffD tot2 totalp_onD x2_in)

    thus ?thesis
      using \<open>R x1 x\<close>
      by (meson Un_iff \<open>x \<in># M2 - M1\<close> assms(6) in_diffD local.trans sup2I1 transp_onD x2_in)
  qed
qed


section \<open>Examples of duplicate handling in set and multiset definitions\<close>

lemma
  fixes M :: "nat multiset"
  defines "M \<equiv> {#0, 0, 1, 1, 2, 2#}"
  shows
    "is_minimal_in_set_wrt (<) (set_mset M) 0"
    "is_minimal_in_mset_wrt (<) M 0"
    "is_least_in_set_wrt (<) (set_mset M) 0"
    "\<nexists>y. is_least_in_mset_wrt (<) M y"
  by (auto simp: M_def is_minimal_in_set_wrt_iff is_minimal_in_mset_wrt_def
      is_least_in_set_wrt_iff is_least_in_mset_wrt_def)

lemma
  fixes x y :: 'a and M :: "'a multiset"
  defines "M \<equiv> {#x, y, y#}"
  defines "R \<equiv> \<lambda>_ _. False"
  assumes "x \<noteq> y"
  shows
    "is_maximal_in_mset_wrt R M x"
    "is_maximal_in_mset_wrt R M y"
    "is_strictly_maximal_in_mset_wrt R M x"
    "\<not> is_strictly_maximal_in_mset_wrt R M y"
proof -
  have transp_on_False[simp]: "\<And>A. transp_on A (\<lambda>_ _. False)"
    by (simp add: transp_onI)

  have asymp_on_False[simp]: "\<And>A. asymp_on A (\<lambda>_ _. False)"
    by (simp add: asymp_onI)

  show
    "is_maximal_in_mset_wrt R M x"
    "is_maximal_in_mset_wrt R M y"
    "is_strictly_maximal_in_mset_wrt R M x"
    "\<not> is_strictly_maximal_in_mset_wrt R M y"
    unfolding is_maximal_in_mset_wrt_iff[of M R, unfolded R_def, simplified, folded R_def]
    unfolding is_strictly_maximal_in_mset_wrt_iff[of M R, unfolded R_def, simplified, folded R_def]
    unfolding atomize_conj
    using \<open>x \<noteq> y\<close>
    by (simp add: M_def)
qed


section \<open>Hide stuff\<close>

text \<open>We restrict the public interface to ease future internal changes.\<close>

hide_fact is_minimal_in_mset_wrt_def is_maximal_in_mset_wrt_def
hide_fact is_strictly_minimal_in_mset_wrt_def is_strictly_maximal_in_mset_wrt_def
hide_fact is_least_in_mset_wrt_def is_greatest_in_mset_wrt_def


section \<open>Integration in type classes\<close>

abbreviation (in order) is_minimal_in_mset where
  "is_minimal_in_mset \<equiv> is_minimal_in_mset_wrt (<)"

abbreviation (in order) is_maximal_in_mset where
  "is_maximal_in_mset \<equiv> is_maximal_in_mset_wrt (<)"

lemmas (in order) is_minimal_in_mset_iff =
  is_minimal_in_mset_wrt_iff[OF transp_on_less asymp_on_less]

lemmas (in order) is_maximal_in_mset_iff =
  is_maximal_in_mset_wrt_iff[OF transp_on_less asymp_on_less]

lemmas (in order) ex_minimal_in_mset =
  ex_minimal_in_mset_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) ex_maximal_in_mset =
  ex_maximal_in_mset_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) explode_maximal_in_mset =
  explode_maximal_in_mset_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) explode_strictly_maximal_in_mset =
  explode_strictly_maximal_in_mset_wrt[OF transp_on_less asymp_on_less]

lemmas (in order) is_minimal_in_filter_mset_iff =
  is_minimal_in_filter_mset_wrt_iff[OF transp_on_less asymp_on_less]


abbreviation (in linorder) is_least_in_mset where
  "is_least_in_mset \<equiv> is_least_in_mset_wrt (<)"

abbreviation (in linorder) is_greatest_in_mset where
  "is_greatest_in_mset \<equiv> is_greatest_in_mset_wrt (<)"

lemmas (in linorder) is_least_in_mset_iff =
  is_least_in_mset_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_greatest_in_mset_iff =
  is_greatest_in_mset_wrt_iff[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_minimal_in_mset_if_is_least_in_mset[intro] =
  is_minimal_in_mset_wrt_if_is_least_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_maximal_in_mset_if_is_greatest_in_mset[intro] =
  is_maximal_in_mset_wrt_if_is_greatest_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_minimal_in_mset[intro] =
  Uniq_is_minimal_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_maximal_in_mset[intro] =
  Uniq_is_maximal_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_least_in_mset[intro] =
  Uniq_is_least_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) Uniq_is_greatest_in_mset[intro] =
  Uniq_is_greatest_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) is_least_in_mset_iff_is_minimal_and_count_eq_one =
  is_least_in_mset_wrt_iff_is_minimal_and_count_eq_one[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) is_greatest_in_mset_iff_is_maximal_and_count_eq_one =
  is_greatest_in_mset_wrt_iff_is_maximal_and_count_eq_one[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) count_ge_2_if_minimal_in_mset_and_not_least_in_mset =
  count_ge_2_if_minimal_in_mset_wrt_and_not_least_in_mset_wrt[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset =
  count_ge_2_if_maximal_in_mset_wrt_and_not_greatest_in_mset_wrt[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) explode_greatest_in_mset =
  explode_greatest_in_mset_wrt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal =
  multp\<^sub>H\<^sub>O_if_maximal_wrt_less_that_maximal_wrt[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) multp\<^sub>D\<^sub>M_if_maximal_less_that_maximal =
  multp\<^sub>D\<^sub>M_if_maximal_wrt_less_that_maximal_wrt[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) multp_if_maximal_less_that_maximal =
  multp_if_maximal_wrt_less_that_maximal_wrt[OF transp_on_less asymp_on_less
    totalp_on_less]

lemmas (in linorder) multp\<^sub>H\<^sub>O_if_same_maximal_and_count_lt =
  multp\<^sub>H\<^sub>O_if_same_maximal_wrt_and_count_lt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) multp_if_same_maximal_and_count_lt =
  multp_if_same_maximal_wrt_and_count_lt[OF transp_on_less asymp_on_less totalp_on_less]

lemmas (in linorder) less_than_maximal_if_multp\<^sub>H\<^sub>O =
  less_than_maximal_wrt_if_multp\<^sub>H\<^sub>O[OF transp_on_less asymp_on_less totalp_on_less]

lemma (in linorder)
  assumes"is_greatest_in_mset C L"
  shows "C - {#L#} = {#K \<in># C. K \<noteq> L#}"
  using assms
  by (smt (verit, del_insts) add_diff_cancel_left' diff_subset_eq_self diff_zero filter_empty_mset
      filter_mset_add_mset filter_mset_eq_conv insert_DiffM2 local.is_greatest_in_mset_iff
      local.not_less_iff_gr_or_eq)

end