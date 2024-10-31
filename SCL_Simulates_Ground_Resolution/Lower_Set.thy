theory Lower_Set
  imports Main
begin

definition is_lower_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow>
    is_lower_set_wrt R L X \<longleftrightarrow> L \<subseteq> X \<and> (\<forall>l \<in> L. \<forall>x \<in> X. R x l \<longrightarrow> x \<in> L)"

definition is_strict_lower_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "transp_on X R \<Longrightarrow> asymp_on X R \<Longrightarrow>
    is_strict_lower_set_wrt R L X \<longleftrightarrow> L \<subset> X \<and> (\<forall>l \<in> L. \<forall>x \<in> X. R x l \<longrightarrow> x \<in> L)"

lemma is_lower_set_wrt_empty:
  fixes X :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "transp_on X R" and "asymp_on X R"
  shows "is_lower_set_wrt R {} X"
  unfolding is_lower_set_wrt_def[OF assms] by simp

lemma is_lower_set_wrt_refl:
  fixes X :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "transp_on X R" and "asymp_on X R"
  shows "is_lower_set_wrt R X X"
  unfolding is_lower_set_wrt_def[OF assms] by simp

lemma is_lower_set_wrt_trans:
  fixes X Y Z :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    "transp_on Z R" and "asymp_on Z R" and
    "is_lower_set_wrt R X Y" and "is_lower_set_wrt R Y Z"
  shows "is_lower_set_wrt R X Z"
proof -
  have "Y \<subseteq> Z" and Y_lower: "\<forall>l\<in>Y. \<forall>x\<in>Z. R x l \<longrightarrow> x \<in> Y"
    using \<open>is_lower_set_wrt R Y Z\<close>
    unfolding is_lower_set_wrt_def[OF \<open>transp_on Z R\<close> \<open>asymp_on Z R\<close>]
    unfolding atomize_conj .

  have "transp_on Y R" and "asymp_on Y R"
    unfolding atomize_conj
    using \<open>transp_on Z R\<close> \<open>asymp_on Z R\<close> \<open>Y \<subseteq> Z\<close>
    by (metis asymp_on_subset transp_on_subset)

  have "X \<subseteq> Y" and X_lower: "\<forall>l\<in>X. \<forall>x\<in>Y. R x l \<longrightarrow> x \<in> X"
    using \<open>is_lower_set_wrt R X Y\<close>
    unfolding is_lower_set_wrt_def[OF \<open>transp_on Y R\<close> \<open>asymp_on Y R\<close>]
    unfolding atomize_conj .

  have "X \<subseteq> Z"
    using \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> Z\<close> by order

  moreover have "(\<forall>l\<in>X. \<forall>x\<in>Z. R x l \<longrightarrow> x \<in> X)"
    using \<open>X \<subseteq> Y\<close> X_lower Y_lower by blast

  ultimately show ?thesis
    unfolding is_lower_set_wrt_def[OF \<open>transp_on Z R\<close> \<open>asymp_on Z R\<close>] .. 
qed

lemma is_lower_set_wrt_antisym:
  fixes X Y :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    "transp_on Y R" and "asymp_on Y R" and
    "is_lower_set_wrt R X Y" and "is_lower_set_wrt R Y X"
  shows "X = Y"
proof -
  have "X \<subseteq> Y"
    using \<open>is_lower_set_wrt R X Y\<close>
    unfolding is_lower_set_wrt_def[OF \<open>transp_on Y R\<close> \<open>asymp_on Y R\<close>] ..

  have "transp_on X R" and "asymp_on X R"
    unfolding atomize_conj
    using \<open>transp_on Y R\<close> \<open>asymp_on Y R\<close> \<open>X \<subseteq> Y\<close>
    by (metis asymp_on_subset transp_on_subset)

  have "Y \<subseteq> X"
    using \<open>is_lower_set_wrt R Y X\<close>
    unfolding is_lower_set_wrt_def[OF \<open>transp_on X R\<close> \<open>asymp_on X R\<close>] ..

  show "X = Y"
    using \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> X\<close> by (metis subset_antisym)
qed 

lemma order_is_lower_set_wrt:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "transp R" and "asymp R"
  shows "class.order (is_lower_set_wrt R) (is_strict_lower_set_wrt R)"
proof unfold_locales
  have trans: "\<And>A. transp_on A R"
    using \<open>transp R\<close> by (metis subset_UNIV transp_on_subset)

  have asym: "\<And>A. asymp_on A R"
    using \<open>asymp R\<close> by (metis subset_UNIV asymp_on_subset)

  show "\<And>x y. is_strict_lower_set_wrt R x y = (is_lower_set_wrt R x y \<and> \<not> is_lower_set_wrt R y x)"
    unfolding is_lower_set_wrt_def[OF trans asym]
    unfolding is_strict_lower_set_wrt_def[OF trans asym]
    by (metis order_le_less subset_not_subset_eq)

  show "\<And>x. is_lower_set_wrt R x x"
    using is_lower_set_wrt_refl[OF trans asym] .

  show "\<And>x y z. is_lower_set_wrt R x y \<Longrightarrow> is_lower_set_wrt R y z \<Longrightarrow> is_lower_set_wrt R x z"
    using is_lower_set_wrt_trans[OF trans asym] .

  show "\<And>x y. is_lower_set_wrt R x y \<Longrightarrow> is_lower_set_wrt R y x \<Longrightarrow> x = y"
    using is_lower_set_wrt_antisym[OF trans asym] .
qed

lemma is_lower_set_wrt_insertI:
  assumes "transp_on (insert x X) R" and "asymp_on (insert x X) R" and
    "x \<in> X" and "\<forall>w \<in> X. R w x \<longrightarrow> w \<in> L" and "is_lower_set_wrt R L X"
  shows "is_lower_set_wrt R (insert x L) X"
proof -
  have "transp_on X R" and "asymp_on X R"
    unfolding atomize_conj
    using \<open>transp_on (insert x X) R\<close> \<open>asymp_on (insert x X) R\<close>
    by (metis asymp_on_subset subset_insertI transp_on_subset)

  have "is_lower_set_wrt R (insert x L) X \<longleftrightarrow>
    insert x L \<subseteq> X \<and> (\<forall>l\<in>insert x L. \<forall>xa\<in>X. R xa l \<longrightarrow> xa \<in> insert x L)"
    unfolding is_lower_set_wrt_def[OF \<open>transp_on X R\<close> \<open>asymp_on X R\<close>] ..

  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> L \<subseteq> X \<and> (\<forall>l\<in>insert x L. \<forall>xa\<in>X. R xa l \<longrightarrow> xa \<in> insert x L)"
    by simp

  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> L \<subseteq> X \<and> (\<forall>w\<in>X. R w x \<longrightarrow> w \<in> insert x L) \<and>
    (\<forall>l\<in>L. \<forall>xa\<in>X. R xa l \<longrightarrow> xa \<in> insert x L)"
    by simp

  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> L \<subseteq> X \<and> (\<forall>w\<in>X. R w x \<longrightarrow> w \<in> L) \<and>
    (\<forall>l\<in>L. \<forall>y\<in>X. R y l \<longrightarrow> y \<in> insert x L)"
    using \<open>asymp_on (insert x X) R\<close> by (smt (verit) asymp_onD insertCI insertE)

  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> (\<forall>w\<in>X. R w x \<longrightarrow> w \<in> L) \<and> is_lower_set_wrt R L X"
    using \<open>is_lower_set_wrt R L X\<close>
    unfolding is_lower_set_wrt_def[OF \<open>transp_on X R\<close> \<open>asymp_on X R\<close>]
    by blast

  finally show ?thesis
    using assms(3-) by argo
qed

lemma lower_set_wrt_appendI:
  assumes
    trans: "transp_on (set (xs @ ys)) R" and
    asym: "asymp_on (set (xs @ ys)) R" and
    sorted: "sorted_wrt R (xs @ ys)"
  shows "is_lower_set_wrt R (set xs) (set (xs @ ys))"
  unfolding is_lower_set_wrt_def[OF trans asym]
proof (intro conjI)
  show "set xs \<subseteq> set (xs @ ys)"
    by simp
next
  show "\<forall>l\<in>set xs. \<forall>x\<in>set (xs @ ys). R x l \<longrightarrow> x \<in> set xs"
    using sorted
    by (metis Un_iff asym asymp_on_def set_append sorted_wrt_append)
qed

lemma sorted_and_lower_set_wrt_appendD_left:
  assumes "transp_on A R" and "asymp_on A R" and
    "sorted_wrt R (xs @ ys)" and "is_lower_set_wrt R (set (xs @ ys)) A"
  shows "sorted_wrt R xs" and "is_lower_set_wrt R (set xs) A"
  unfolding atomize_conj
  using assms
  by (smt (verit) Un_iff asymp_on_def is_lower_set_wrt_def le_sup_iff set_append sorted_wrt_append
      subsetD)

lemma sorted_and_lower_set_wrt_appendD_right:
  assumes "transp_on A R" and "asymp_on A R" and
    "sorted_wrt (\<lambda>x y. R y x) (xs @ ys)" and "is_lower_set_wrt R (set (xs @ ys)) A"
  shows "sorted_wrt (\<lambda>x y. R y x) ys" and "is_lower_set_wrt R (set ys) A"
  unfolding atomize_conj
  using assms
  by (smt (verit, ccfv_threshold) Un_iff asymp_onD is_lower_set_wrt_def le_sup_iff set_append
      sorted_wrt_append subsetD)

lemma not_in_lower_set_wrtI:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes trans: "transp_on Y R" and asym: "asymp_on Y R"
  shows "is_lower_set_wrt R X Y \<Longrightarrow> y \<notin> X \<Longrightarrow> y \<in> Y \<Longrightarrow> R y z \<Longrightarrow> z \<notin> X"
  unfolding is_lower_set_wrt_def[OF trans asym]
  by blast


abbreviation (in preorder) is_lower_set where
  "is_lower_set \<equiv> is_lower_set_wrt (<)"

lemmas (in preorder) is_lower_set_iff =
  is_lower_set_wrt_def[OF transp_on_less asymp_on_less]

context linorder begin

sublocale is_lower_set: order "is_lower_set_wrt (<)" "is_strict_lower_set_wrt (<)"
proof (rule order_is_lower_set_wrt)
  show "transp (<)"
    using transp_on_less .
next
  show "asymp (<)"
    using asymp_on_less .
qed

end

lemmas (in preorder) is_lower_set_empty[simp] =
  is_lower_set_wrt_empty[OF transp_on_less asymp_on_less]

lemmas (in preorder) is_lower_set_insertI =
  is_lower_set_wrt_insertI[OF transp_on_less asymp_on_less]

lemmas (in preorder) lower_set_appendI =
  lower_set_wrt_appendI[OF transp_on_less asymp_on_less]

lemmas (in preorder) sorted_and_lower_set_appendD_left =
  sorted_and_lower_set_wrt_appendD_left[OF transp_on_less asymp_on_less]

lemmas (in preorder) sorted_and_lower_set_appendD_right =
  sorted_and_lower_set_wrt_appendD_right[OF transp_on_less asymp_on_less]

lemmas (in preorder) not_in_lower_setI =
  not_in_lower_set_wrtI[OF transp_on_less asymp_on_less]


end