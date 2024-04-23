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

lemma is_maximal_in_mset_wrt_iff:
  "is_maximal_in_mset_wrt R X x \<longleftrightarrow> x \<in># X \<and> (\<forall>y \<in># X. y \<noteq> x \<longrightarrow> \<not> R x y)"
  using is_maximal_in_set_wrt_iff[OF trans asym]
  using is_maximal_in_mset_wrt_def[OF trans asym]
  by simp

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

end


subsection \<open>Miscellaneous\<close>

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

lemma not_Uniq_is_minimal_in_mset_wrt:
  "\<not> (\<forall>R (X :: nat multiset). transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
    (\<exists>\<^sub>\<le>\<^sub>1x. is_minimal_in_mset_wrt R X x))"
proof (intro notI)
  let ?R = "\<lambda>_ _. False"
  let ?X = "{#0 :: nat, 1 :: nat#}"

  assume
    "\<forall>R (X :: nat multiset). transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
      (\<exists>\<^sub>\<le>\<^sub>1 x. is_minimal_in_mset_wrt R X x)"

  moreover have trans: "transp_on (set_mset ?X) ?R"
    by (simp add: transp_onI)

  moreover have asym: "asymp_on (set_mset ?X) ?R"
    by (simp add: asymp_onI)

  ultimately have "\<exists>\<^sub>\<le>\<^sub>1 x. is_minimal_in_mset_wrt ?R ?X x"
    by metis

  moreover have "is_minimal_in_mset_wrt ?R ?X 0"
    using is_minimal_in_mset_wrt_iff[OF trans asym] by simp

  moreover have "is_minimal_in_mset_wrt ?R ?X 1"
    using is_minimal_in_mset_wrt_iff[OF trans asym] by simp

  ultimately have "(0 :: nat) = (1 :: nat)"
    using Uniq_D by fastforce
  thus False
    by presburger
qed

lemma not_Uniq_is_maximal_in_mset_wrt:
  "\<not> (\<forall>R (X :: nat multiset). transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
    (\<exists>\<^sub>\<le>\<^sub>1x. is_maximal_in_mset_wrt R X x))"
proof (intro notI)
  let ?R = "\<lambda>_ _. False"
  let ?X = "{#0 :: nat, 1 :: nat#}"

  assume
    "\<forall>R (X :: nat multiset). transp_on (set_mset X) R \<longrightarrow> asymp_on (set_mset X) R \<longrightarrow>
      (\<exists>\<^sub>\<le>\<^sub>1 x. is_maximal_in_mset_wrt R X x)"

  moreover have trans: "transp_on (set_mset ?X) ?R"
    by (simp add: transp_onI)

  moreover have asym: "asymp_on (set_mset ?X) ?R"
    by (simp add: asymp_onI)

  ultimately have "\<exists>\<^sub>\<le>\<^sub>1 x. is_maximal_in_mset_wrt ?R ?X x"
    by metis

  moreover have "is_maximal_in_mset_wrt ?R ?X 0"
    using is_maximal_in_mset_wrt_iff[OF trans asym] by simp

  moreover have "is_maximal_in_mset_wrt ?R ?X 1"
    using is_maximal_in_mset_wrt_iff[OF trans asym] by simp

  ultimately have "(0 :: nat) = (1 :: nat)"
    using Uniq_D by fastforce
  thus False
    by presburger
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


section \<open>Hide stuff\<close>

text \<open>We restrict the public interface to ease future internal changes.\<close>

hide_fact is_minimal_in_mset_wrt_def is_maximal_in_mset_wrt_def
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

end