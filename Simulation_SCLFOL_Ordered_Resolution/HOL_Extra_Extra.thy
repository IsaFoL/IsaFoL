theory HOL_Extra_Extra
  imports Superposition_Calculus.HOL_Extra
begin

no_notation restrict_map (infixl "|`"  110)

lemma
  assumes "\<exists>\<^sub>\<le>\<^sub>1x. P x"
  shows "finite {x. P x}"
  using assms Collect_eq_if_Uniq by fastforce

lemma finite_if_Uniq_Uniq:
  assumes
    "\<exists>\<^sub>\<le>\<^sub>1x. P x"
    "\<forall>x. \<exists>\<^sub>\<le>\<^sub>1y. Q x y"
  shows "finite {y. \<exists>x. P x \<and> Q x y}"
  using assms
  by (smt (verit, best) Collect_eq_if_Uniq UniqI Uniq_D finite.emptyI finite_insert)

lemma finite_if_finite_finite:
  assumes
    "finite {x. P x}"
    "\<forall>x. finite {y. Q x y}"
  shows "finite {y. \<exists>x. P x \<and> Q x y}"
  using assms by auto

lemma strict_partial_order_wfp_on_finite_set:
  assumes "transp_on \<X> R" and "asymp_on \<X> R"
  shows "finite \<X> \<Longrightarrow> Wellfounded.wfp_on \<X> R"
  unfolding Wellfounded.wfp_on_iff_ex_minimal
  using assms
  by (metis (no_types, opaque_lifting) Finite_Set.bex_min_element asymp_onD asymp_on_subset
      finite_subset transp_on_subset)

lemma (in order) greater_wfp_on_finite_set: "finite \<X> \<Longrightarrow> Wellfounded.wfp_on \<X> (>)"
  using strict_partial_order_wfp_on_finite_set[OF transp_on_greater asymp_on_greater] .

lemma (in order) less_wfp_on_finite_set: "finite \<X> \<Longrightarrow> Wellfounded.wfp_on \<X> (<)"
  using strict_partial_order_wfp_on_finite_set[OF transp_on_less asymp_on_less] .


lemma sorted_wrt_dropWhile: "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (dropWhile P xs)"
  by (auto dest: sorted_wrt_drop simp: dropWhile_eq_drop)

lemma sorted_wrt_takeWhile: "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (takeWhile P xs)"
  by (subst takeWhile_eq_take) (auto dest: sorted_wrt_take)

lemma distinct_if_sorted_wrt_asymp:
  assumes "asymp_on (set xs) R" and "sorted_wrt R xs"
  shows "distinct xs"
  using assms
proof (induction xs)
  case Nil
  show ?case
    unfolding distinct.simps ..
next
  case (Cons x xs)

  have R_x_asym: "\<forall>y \<in> set xs. R x y \<longrightarrow> \<not> R y x" and "asymp_on (set xs) R"
    using Cons.prems(1)
    unfolding atomize_conj
    by (metis asymp_on_def list.set_intros(1) list.set_intros(2))

  have R_x: "\<forall>y \<in> set xs. R x y" and "sorted_wrt R xs"
    using Cons.prems(2)
    unfolding atomize_conj sorted_wrt.simps
    by argo

  have "x \<notin> set xs"
  proof (intro notI)
    assume x_in: "x \<in> set xs"

    have "R x x"
      using R_x x_in by metis

    moreover hence "\<not> R x x"
      using R_x_asym x_in by metis

    ultimately show False
      by contradiction
  qed

  moreover have "distinct xs"
    using Cons.IH \<open>asymp_on (set xs) R\<close> \<open>sorted_wrt R xs\<close> by argo

  ultimately show ?case
    unfolding distinct.simps by argo
qed

lemma dropWhile_append_eq_rhs:
  fixes xs ys :: "'a list" and P :: "'a \<Rightarrow> bool"
  assumes
    "\<And>x. x \<in> set xs \<Longrightarrow> P x" and
    "\<And>y. y \<in> set ys \<Longrightarrow> \<not> P y"
  shows "dropWhile P (xs @ ys) = ys"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by (metis append_Nil dropWhile_eq_self_iff hd_in_set)
next
  case (Cons x xs)
  then show ?case
    by (metis dropWhile_append dropWhile_cong dropWhile_eq_self_iff member_rec(2))
qed

lemma mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xs :: "'a list" and P :: "'a \<Rightarrow> bool"
  assumes "sorted_wrt R xs" and "monotone_on (set xs) R (\<ge>) P"
  shows "x \<in> set (dropWhile P xs) \<longleftrightarrow> \<not> P x \<and> x \<in> set xs"
  using assms
proof (induction xs)
  case Nil
  show ?case
    by simp
next
  case (Cons y xs)
  have "\<forall>z \<in> set xs. R y z" and "sorted_wrt R xs"
    using \<open>sorted_wrt R (y # xs)\<close> by simp_all

  moreover have "monotone_on (set xs) R (\<ge>) P"
    using \<open>monotone_on (set (y # xs)) R (\<ge>) P\<close>
    by (metis monotone_on_subset set_subset_Cons)

  ultimately have IH: "(x \<in> set (dropWhile P xs)) = (\<not> P x \<and> x \<in> set xs)"
    using Cons.IH \<open>sorted_wrt R xs\<close> by metis

  show ?case
  proof (cases "P y")
    case True
    thus ?thesis
      unfolding dropWhile.simps
      unfolding if_P[OF True]
      using IH by auto
  next
    case False
    then show ?thesis
      unfolding dropWhile.simps
      unfolding if_not_P[OF False]
      by (metis (full_types) Cons.prems(1) Cons.prems(2) le_boolD list.set_intros(1) monotone_on_def
          set_ConsD sorted_wrt.simps(2))
  qed
qed

lemma ball_set_dropWhile_if_sorted_wrt_and_monotone_on:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xs :: "'a list" and P :: "'a \<Rightarrow> bool"
  assumes "sorted_wrt R xs" and "monotone_on (set xs) R (\<ge>) P"
  shows "\<forall>x \<in> set (dropWhile P xs). \<not> P x"
  using assms
proof (induction xs)
  case Nil
  show ?case
    by simp
next
  case (Cons x xs)
  have "\<forall>y \<in> set xs. R x y" and "sorted_wrt R xs"
    using \<open>sorted_wrt R (x # xs)\<close> by simp_all

  moreover have "monotone_on (set xs) R (\<ge>) P"
    using \<open>monotone_on (set (x # xs)) R (\<ge>) P\<close>
    by (metis monotone_on_subset set_subset_Cons)

  ultimately have "\<forall>x\<in>set (dropWhile P xs). \<not> P x"
    using Cons.IH \<open>sorted_wrt R xs\<close> by metis

  moreover have "\<not> P x \<Longrightarrow> \<not> P y" if "y \<in> set xs" for y
  proof -
    have "x \<in> set (x # xs)"
      by simp
    moreover have "y \<in> set (x # xs)"
      using \<open>y \<in> set xs\<close> by simp
    moreover have "R x y"
      using \<open>\<forall>y\<in>set xs. R x y\<close> \<open>y \<in> set xs\<close> by metis
    ultimately have "P y \<le> P x"
      using \<open>monotone_on (set (x # xs)) R (\<ge>) P\<close>[unfolded monotone_on_def] by metis
    thus "\<not> P x \<Longrightarrow> \<not> P y"
      by simp
  qed

  ultimately show ?case
    by simp
qed

lemma filter_set_eq_filter_set_minus_singleton:
  assumes "\<not> P y"
  shows "{x \<in> X. P x} = {x \<in> X - {y}. P x}"
  using assms by blast

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

lemma (in linorder) ex1_sorted_list_for_set_if_finite:
  "finite X \<Longrightarrow> \<exists>!xs. sorted_wrt (<) xs \<and> set xs = X"
  by (metis local.sorted_list_of_set.finite_set_strict_sorted local.strict_sorted_equal)

lemma restrict_map_ident_if_dom_subset: "dom \<M> \<subseteq> A \<Longrightarrow> restrict_map \<M> A = \<M>"
  by (metis domIff ext in_mono restrict_map_def)

lemma dropWhile_ident_if_pred_always_false:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<not> P x"
  shows "dropWhile P xs = xs"
  using assms dropWhile_eq_self_iff hd_in_set by auto


subsection \<open>Move to \<^theory>\<open>HOL.Transitive_Closure\<close>\<close>

lemma relpowp_right_unique:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and n :: nat and x y z :: 'a
  assumes runique: "\<And>x y z. R x y \<Longrightarrow> R x z \<Longrightarrow> y = z"
  shows "(R ^^ n) x y \<Longrightarrow> (R ^^ n) x z \<Longrightarrow> y = z"
proof (induction n arbitrary: x y z)
  case 0
  thus ?case
    by simp
next
  case (Suc n')
  then obtain x' :: 'a where
    "(R ^^ n') x x'" and "R x' y" and "R x' z"
    by auto
  thus "y = z"
    using runique by simp
qed

lemma Uniq_relpowp:
  fixes n :: nat and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes runiq: "\<forall>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y"
  shows "\<exists>\<^sub>\<le>\<^sub>1y. (R ^^ n) x y"
proof (rule Uniq_I)
  fix y z
  assume "(R ^^ n) x y" and "(R ^^ n) x z"
  show "y = z"
  proof (rule relpowp_right_unique)
    show "\<And>x y z. R x y \<Longrightarrow> R x z \<Longrightarrow> y = z"
      using runiq by (auto dest: Uniq_D)
  next
    show "(R ^^ n) x y"
      using \<open>(R ^^ n) x y\<close> .
  next
    show "(R ^^ n) x z"
      using \<open>(R ^^ n) x z\<close> .
  qed
qed

lemma relpowp_plus_of_right_unique:
  assumes
    "right_unique R"
    "(R ^^ m) x y" and
    "(R ^^ (m + n)) x z"
  shows "(R ^^ n) y z"
  using assms(2,3)
proof (induction m arbitrary: x)
  case 0
  thus ?case
    by simp
next
  case (Suc m)
  then show ?case
    by (metis add_Suc assms(1) relpowp_Suc_E2 right_uniqueD)
qed

lemma relpowp_plusD:
  assumes "(R ^^ (m + n)) x z"
  shows "\<exists>y. (R ^^ m) x y \<and> (R ^^ n) y z"
  using assms
proof (induction m arbitrary: x)
  case 0
  thus ?case
    by simp
next
  case (Suc m)

  obtain y where "R x y" and "(R ^^ (m + n)) y z"
    using Suc.prems by (metis add_Suc relpowp_Suc_D2)

  obtain y' where "(R ^^ m) y y'" and "(R ^^ n) y' z"
    using Suc.IH[OF \<open>(R ^^ (m + n)) y z\<close>] by metis

  show ?case
  proof (intro exI conjI)
    show "(R ^^ Suc m) x y'"
      using \<open>R x y\<close> \<open>(R ^^ m) y y'\<close> by (metis relpowp_Suc_I2)
  next
    show "(R ^^ n) y' z"
      using \<open>(R ^^ n) y' z\<close> .
  qed
qed

lemma relpowp_Suc_of_right_unique:
  assumes
    "right_unique R"
    "R x y" and
    "(R ^^ Suc n) x z"
  shows "(R ^^ n) y z"
  using assms
  by (metis relpowp_Suc_D2 right_uniqueD)

lemma relpowp_trans[trans]:
  "(R ^^ i) x y \<Longrightarrow> (R ^^ j) y z \<Longrightarrow> (R ^^ (i + j)) x z"
proof (induction i arbitrary: x)
  case 0
  thus ?case by simp
next
  case (Suc i)
  thus ?case
  by (metis add_Suc relpowp_Suc_D2 relpowp_Suc_I2)
qed

lemma tranclp_if_relpowp: "n \<noteq> 0 \<Longrightarrow> (R ^^ n) x y \<Longrightarrow> R\<^sup>+\<^sup>+ x y"
  by (meson bot_nat_0.not_eq_extremum tranclp_power)

lemma ex_terminating_rtranclp_strong:
  assumes wf: "Wellfounded.wfp_on {x'. R\<^sup>*\<^sup>* x x'} R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
proof (cases "\<exists>y. R x y")
  case True
  with wf show ?thesis
  proof (induction rule: Wellfounded.wfp_on_induct)
    case in_set
    thus ?case
      by simp
  next
    case (less x)
    then show ?case
      by (metis (full_types) conversepI mem_Collect_eq r_into_rtranclp rtranclp_trans)
  qed
next
  case False
  thus ?thesis
    by blast
qed

lemma transp_on_singleton[simp]: "transp_on {x} R"
  by (simp add: transp_on_def)

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
  assumes wf: "wfp R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
  using ex_terminating_rtranclp_strong Wellfounded.wfp_on_subset subset_UNIV wf by metis

end