theory Background
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Correct_Termination
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Simple_Clause_Learning.Termination
    Superposition_Calculus.Ground_Ordered_Resolution
    Superposition_Calculus.Min_Max_Least_Greatest_FSet
    Superposition_Calculus.Multiset_Extra
    VeriComp.Compiler
    "HOL-ex.Sketch_and_Explore"
    "HOL-Library.FuncSet"
    "Try1.Try1_HOL"
    Lower_Set
begin

no_notation restrict_map (infixl "|`"  110)


section \<open>Move to HOL\<close>

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

(* find_theorems "dropWhile _ (_ @ _)"

lemma
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xs ys :: "'a list" and P :: "'a \<Rightarrow> bool"
  assumes "sorted_wrt R xs" and "monotone_on (set xs) R (\<ge>) P"  
  assumes "P y"
  shows "dropWhile P (xs @ y # ys) = dropWhile P ys"
  sorry *)


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

lemma ex_terminating_rtranclp:
  assumes wf: "wfp R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
  using ex_terminating_rtranclp_strong Wellfounded.wfp_on_subset subset_UNIV wf by metis

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

lemma (in linorder) ex1_sorted_list_for_fset:
  "\<exists>!xs. sorted_wrt (<) xs \<and> fset_of_list xs = X"
  using ex1_sorted_list_for_set_if_finite
  by (metis finite_fset fset_cong fset_of_list.rep_eq)

lemma restrict_map_ident_if_dom_subset: "dom \<M> \<subseteq> A \<Longrightarrow> restrict_map \<M> A = \<M>"
  by (metis domIff ext in_mono restrict_map_def)


subsection \<open>Minimal, maximal, least, and greatest element of a set\<close>

subsubsection \<open>Function\<close>

definition Greatest_in_set_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a option" where
  "Greatest_in_set_wrt R X = (if X = {} then None else Some (THE x. is_greatest_in_set_wrt R X x))"

lemma Greatest_in_set_wrt_empty[simp]: "Greatest_in_set_wrt R {} = None"
  by (simp add: Greatest_in_set_wrt_def)

lemma Greatest_in_set_wrt_singleton[simp]:
  "asymp_on {x} R \<Longrightarrow> Greatest_in_set_wrt R {x} = Some x"
  unfolding Greatest_in_set_wrt_def
  using is_greatest_in_set_wrt_iff[of "{x}" R, simplified]
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
  unfolding Greatest_in_set_wrt_def (* is_greatest_in_set_wrt_iff[OF trans asym tot] *)
  using Uniq_is_greatest_in_set_wrt[OF trans asym tot] the1_equality'
  by (metis asym bex_empty is_greatest_in_set_wrt_iff trans tot)

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


subsubsection \<open>Integration in type classes\<close>

lemma (in linorder) is_least_in_fset_ffilterD:
  assumes "is_least_in_fset_wrt (<) (ffilter P X) x"
  shows "x |\<in>| X" "P x"
  using assms
  by (simp_all add: is_least_in_fset_wrt_iff)

lemma (in linorder) ex_least_in_fset:
  "X \<noteq> {||} \<Longrightarrow> \<exists>x. is_least_in_fset X x"
  by (simp add: ex_least_in_fset_wrt)


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


section \<open>Move to \<^theory>\<open>HOL-Library.Multiset\<close>\<close>

lemmas strict_subset_implies_multp = subset_implies_multp
hide_fact subset_implies_multp

lemma subset_implies_reflclp_multp: "A \<subseteq># B \<Longrightarrow> (multp R)\<^sup>=\<^sup>= A B"
  by (metis reflclp_iff strict_subset_implies_multp subset_mset.le_imp_less_or_eq)

lemma member_mset_repeat_msetD: "L \<in># repeat_mset n M \<Longrightarrow> L \<in># M"
  by (induction n) auto

lemma member_mset_repeat_mset_Suc[simp]: "L \<in># repeat_mset (Suc n) M \<longleftrightarrow> L \<in># M"
  by (metis member_mset_repeat_msetD repeat_mset_Suc union_iff)

lemma image_msetI: "x \<in># M \<Longrightarrow> f x \<in># image_mset f M"
  by (metis imageI in_image_mset)

lemma inj_image_mset_mem_iff: "inj f \<Longrightarrow> f x \<in># image_mset f M \<longleftrightarrow> x \<in># M"
  by (simp add: inj_image_mem_iff)


section \<open>Move to \<^theory>\<open>HOL-Library.FSet\<close>\<close>

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

lemma ffilter_eq_ffilter_minus_singleton:
  assumes "\<not> P y"
  shows "{|x |\<in>| X. P x|} = {|x |\<in>| X - {|y|}. P x|}"
  using assms by (induction X) auto

lemma fun_upd_fimage: "f(x := y) |`| A = (if x |\<in>| A then finsert y (f |`| (A - {|x|})) else f |`| A)"
  using fun_upd_image
  by (smt (verit) bot_fset.rep_eq finsert.rep_eq fset.set_map fset_cong minus_fset.rep_eq)

lemma ffilter_fempty[simp]: "ffilter P {||} = {||}"
  by (metis ex_fin_conv ffmember_filter)

lemma fstrict_subset_iff_fset_strict_subset_fset:
  fixes \<X> \<Y> :: "_ fset"
  shows "\<X> |\<subset>| \<Y> \<longleftrightarrow> fset \<X> \<subset> fset \<Y>"
    by blast


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

locale semantics' =
  fixes
    step :: "'const \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<rightarrow>" 50) and
    final :: "'const \<Rightarrow> 'state \<Rightarrow> bool"
  assumes
    final_finished: "final \<C> s \<Longrightarrow> finished (step \<C>) s"
begin

sublocale semantics where
  step = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step \<C> s s'" and
  final = "\<lambda>(\<C>, s). final \<C> s"
proof unfold_locales
  let ?step = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step \<C> s s'"
  let ?final = "\<lambda>(\<C>, s). final \<C> s"
  show "\<And>s. ?final s \<Longrightarrow> finished ?step s"
    using final_finished
    by (simp add: finished_def split_beta)
qed

end

locale forward_simulation_with_measuring_function' =
  L1: semantics' step1 final1 +
  L2: semantics' step2 final2 +
  well_founded "(\<sqsubset>)"
  for
    step1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    final2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70) +
  fixes
    match :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'const2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'index"
  assumes
    match_final:
      "match \<C>1 s1 \<C>2 s2 \<Longrightarrow> final1 \<C>1 s1 \<Longrightarrow> final2 \<C>2 s2" and
    simulation:
      "match \<C>1 s1 \<C>2 s2 \<Longrightarrow> step1 \<C>1 s1 s1' \<Longrightarrow>
        (\<exists>s2'. (step2 \<C>2)\<^sup>+\<^sup>+ s2 s2' \<and> match \<C>1 s1' \<C>2 s2') \<or>
        (match \<C>1 s1' \<C>2 s2 \<and> measure \<C>1 s1' \<sqsubset> measure \<C>1 s1)"
begin

sublocale forward_simulation where
  step1 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step1 \<C> s s'" and
  step2 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step2 \<C> s s'" and
  final1 = "\<lambda>(\<C>, s). final1 \<C> s" and
  final2 = "\<lambda>(\<C>, s). final2 \<C> s" and
  order = order and
  match = "\<lambda>i (\<C>1, s1) (\<C>2, s2). i = measure \<C>1 s1 \<and> match \<C>1 s1 \<C>2 s2"
proof unfold_locales
  let ?step1 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step1 \<C> s s'"
  let ?step2 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step2 \<C> s s'"
  let ?final1 = "\<lambda>(\<C>, s). final1 \<C> s"
  let ?final2 = "\<lambda>(\<C>, s). final2 \<C> s"
  let ?order = order
  let ?match = "\<lambda>i (\<C>1, s1) (\<C>2, s2). i = measure \<C>1 s1 \<and> match \<C>1 s1 \<C>2 s2"

  show "\<And>i S1 S2. ?match i S1 S2 \<Longrightarrow> ?final1 S1 \<Longrightarrow> ?final2 S2"
    using match_final by auto
next
  let ?step1 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step1 \<C> s s'"
  let ?step2 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step2 \<C> s s'"
  let ?final1 = "\<lambda>(\<C>, s). final1 \<C> s"
  let ?final2 = "\<lambda>(\<C>, s). final2 \<C> s"
  let ?order = order
  let ?match = "\<lambda>i (\<C>1, s1) (\<C>2, s2). i = measure \<C>1 s1 \<and> match \<C>1 s1 \<C>2 s2"

  fix i and S1 S1' :: "'const1 \<times> 'state1" and S2 :: "'const2 \<times> 'state2"

  obtain \<C>1 s1 \<C>2 s2 where
    S1_def: "S1 = (\<C>1, s1)" and S2_def: "S2 = (\<C>2, s2)"
    by fastforce

  assume "?match i S1 S2" and "?step1 S1 S1'"

  from \<open>?match i S1 S2\<close> have "i = measure \<C>1 s1 " and "match \<C>1 s1 \<C>2 s2"
    unfolding S1_def S2_def prod.case by simp_all

  from \<open>?step1 S1 S1'\<close> obtain s1' where
    S1'_def: "S1' = (\<C>1, s1')" and "step1 \<C>1 s1 s1'"
    unfolding S1_def prod.case by blast

  show "(\<exists>i' S2'. ?step2\<^sup>+\<^sup>+ S2 S2' \<and> ?match i' S1' S2') \<or> (\<exists>i'. ?match i' S1' S2 \<and> ?order i' i)"
    using simulation[OF \<open>match \<C>1 s1 \<C>2 s2\<close> \<open>step1 \<C>1 s1 s1'\<close>]
  proof (elim disjE exE conjE)
    fix s2'
    assume "(step2 \<C>2)\<^sup>+\<^sup>+ s2 s2'" and "match \<C>1 s1' \<C>2 s2'"
    let ?S2' = "(\<C>2, s2')"
    let ?i' = "measure \<C>1 s1'"
    have "?step2\<^sup>+\<^sup>+ S2 ?S2'"
      using \<open>(step2 \<C>2)\<^sup>+\<^sup>+ s2 s2'\<close>
    proof (induction s2' rule: tranclp_induct)
      case (base y)
      thus ?case
        by (auto simp add: S2_def)
    next
      case (step y z)
      thus ?case
        using tranclp.trancl_into_trancl by force
    qed
    moreover have "?match ?i' S1' ?S2'"
      using \<open>match \<C>1 s1' \<C>2 s2'\<close>
      by (simp add: S1'_def)
    ultimately show ?thesis
      by auto
  next
    assume "match \<C>1 s1' \<C>2 s2" and "measure \<C>1 s1' \<sqsubset> measure \<C>1 s1"
    then have "\<exists>i'. ?match i' S1' S2 \<and> ?order i' i"
      using \<open>i = measure \<C>1 s1\<close> by (simp add: S1'_def S2_def)
    thus ?thesis
      by argo
  qed
qed

end

locale backward_simulation_with_measuring_function' =
  L1: semantics' step1 final1 +
  L2: semantics' step2 final2 +
  well_founded "(\<sqsubset>)"
  for
    step1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    final2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70) +
  fixes
    match :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'const2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> 'index"
  assumes
    match_final:
      "match \<C>1 s1 \<C>2 s2 \<Longrightarrow> final2 \<C>2 s2 \<Longrightarrow> final1 \<C>1 s1" and
    simulation:
      "match \<C>1 s1 \<C>2 s2 \<Longrightarrow> step2 \<C>2 s2 s2' \<Longrightarrow>
        (\<exists>s1'. (step1 \<C>1)\<^sup>+\<^sup>+ s1 s1' \<and> match \<C>1 s1' \<C>2 s2') \<or>
        (match \<C>1 s1 \<C>2 s2' \<and> measure \<C>2 s2' \<sqsubset> measure \<C>2 s2)"
begin

sublocale backward_simulation where
  step1 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step1 \<C> s s'" and
  step2 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step2 \<C> s s'" and
  final1 = "\<lambda>(\<C>, s). final1 \<C> s" and
  final2 = "\<lambda>(\<C>, s). final2 \<C> s" and
  order = order and
  match = "\<lambda>i (\<C>1, s1) (\<C>2, s2). i = measure \<C>2 s2 \<and> match \<C>1 s1 \<C>2 s2"
proof unfold_locales
  let ?step1 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step1 \<C> s s'"
  let ?step2 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step2 \<C> s s'"
  let ?final1 = "\<lambda>(\<C>, s). final1 \<C> s"
  let ?final2 = "\<lambda>(\<C>, s). final2 \<C> s"
  let ?order = order
  let ?match = "\<lambda>i (\<C>1, s1) (\<C>2, s2). i = measure \<C>2 s2 \<and> match \<C>1 s1 \<C>2 s2"

  show "\<And>i S1 S2. ?match i S1 S2 \<Longrightarrow> ?final2 S2 \<Longrightarrow> ?final1 S1"
    using match_final by auto
next
  let ?step1 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step1 \<C> s s'"
  let ?step2 = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step2 \<C> s s'"
  let ?final1 = "\<lambda>(\<C>, s). final1 \<C> s"
  let ?final2 = "\<lambda>(\<C>, s). final2 \<C> s"
  let ?order = order
  let ?match = "\<lambda>i (\<C>1, s1) (\<C>2, s2). i = measure \<C>2 s2 \<and> match \<C>1 s1 \<C>2 s2"

  fix i and S1 :: "'const1 \<times> 'state1" and S2 S2' :: "'const2 \<times> 'state2"

  obtain \<C>1 s1 \<C>2 s2 where
    S1_def: "S1 = (\<C>1, s1)" and S2_def: "S2 = (\<C>2, s2)"
    by fastforce

  assume "?match i S1 S2" and "?step2 S2 S2'"

  from \<open>?match i S1 S2\<close> have "i = measure \<C>2 s2 " and "match \<C>1 s1 \<C>2 s2"
    unfolding S1_def S2_def prod.case by simp_all

  from \<open>?step2 S2 S2'\<close> obtain s2' where
    S2'_def: "S2' = (\<C>2, s2')" and "step2 \<C>2 s2 s2'"
    unfolding S2_def prod.case by blast

  show "(\<exists>i' S1'. ?step1\<^sup>+\<^sup>+ S1 S1' \<and> ?match i' S1' S2') \<or> (\<exists>i'. ?match i' S1 S2' \<and> ?order i' i)"
    using simulation[OF \<open>match \<C>1 s1 \<C>2 s2\<close> \<open>step2 \<C>2 s2 s2'\<close>]
  proof (elim disjE exE conjE)
    fix s1'
    assume "(step1 \<C>1)\<^sup>+\<^sup>+ s1 s1'" and "match \<C>1 s1' \<C>2 s2'"
    let ?S1' = "(\<C>1, s1')"
    let ?i' = "measure \<C>2 s2'"
    have "?step1\<^sup>+\<^sup>+ S1 ?S1'"
      using \<open>(step1 \<C>1)\<^sup>+\<^sup>+ s1 s1'\<close>
    proof (induction s1' rule: tranclp_induct)
      case (base y)
      thus ?case
        by (auto simp add: S1_def)
    next
      case (step y z)
      thus ?case
        using tranclp.trancl_into_trancl by force
    qed
    moreover have "?match ?i' ?S1' S2'"
      using \<open>match \<C>1 s1' \<C>2 s2'\<close>
      by (simp add: S2'_def)
    ultimately show ?thesis
      by auto
  next
    assume "match \<C>1 s1 \<C>2 s2'" and "measure \<C>2 s2' \<sqsubset> measure \<C>2 s2"
    then have "\<exists>i'. ?match i' S1 S2' \<and> ?order i' i"
      using \<open>i = measure \<C>2 s2\<close> by (simp add: S1_def S2'_def)
    thus ?thesis
      by argo
  qed
qed

end


locale bisimulation_with_measuring_function' =
  forward_simulation_with_measuring_function' step1 step2 final1 final2 order1 match measure1 +
  backward_simulation_with_measuring_function' step1 step2 final1 final2 order2 match measure2
  for
    step1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    final2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    match :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'const2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    order1 :: "'index1 \<Rightarrow> 'index1 \<Rightarrow> bool" and
    order2 :: "'index2 \<Rightarrow> 'index2 \<Rightarrow> bool" and
    measure1 :: "'const1 \<Rightarrow> 'state1 \<Rightarrow> 'index1" and
    measure2 :: "'const2 \<Rightarrow> 'state2 \<Rightarrow> 'index2"

locale language' =
  semantics' step final
  for
    step :: "'const \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" and
    final :: "'const \<Rightarrow> 'state \<Rightarrow> bool" +
  fixes
    load :: "'prog \<Rightarrow> 'const \<Rightarrow> 'state \<Rightarrow> bool"
begin

sublocale language where
  step = "\<lambda>(\<C>, s) (\<C>', s'). \<C> = \<C>' \<and> step \<C> s s'" and
  final = "\<lambda>(\<C>, s). final \<C> s" and
  load = "\<lambda>p (\<C>, s). load p \<C> s"
  by unfold_locales

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
    by (metis asymp_on_less_lit is_maximal_in_mset_wrt_if_is_greatest_in_mset_wrt
        is_maximal_in_mset_wrt_iff literal.inject(1) totalpD totalp_on_less_lit transp_on_less_lit
        union_single_eq_diff)
qed

lemma (in ground_ordered_resolution_calculus) unique_ground_factoring:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_factoring P C"
proof (intro Uniq_I)
  fix P C C'
  assume "ground_factoring P C" and "ground_factoring P C'"
  thus "C = C'"
    unfolding ground_factoring.simps
    by (metis asymp_on_less_lit is_maximal_in_mset_wrt_iff totalpD totalp_less_lit
        transp_on_less_lit union_single_eq_diff)
qed

lemma (in ground_ordered_resolution_calculus) termination_ground_factoring:
  shows "wfP ground_factoring\<inverse>\<inverse>"
proof (rule wfp_if_convertible_to_wfp)
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

lemma (in ground_ordered_resolution_calculus) set_mset_eq_set_mset_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "set_mset P = set_mset C"
  using assms by (cases P C rule: ground_factoring.cases) simp

lemma (in ground_ordered_resolution_calculus) atms_of_concl_eq_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "atms_of C = atms_of P"
  using assms by (cases P C rule: ground_factoring.cases) simp

lemma (in ground_ordered_resolution_calculus) ground_factoring_preserves_maximal_literal:
  assumes "ground_factoring P C"
  shows "is_maximal_lit L P = is_maximal_lit L C"
  using assms by (cases P C rule: ground_factoring.cases) (simp add: is_maximal_in_mset_wrt_iff)

lemma (in ground_ordered_resolution_calculus) ground_factorings_preserves_maximal_literal:
  assumes "ground_factoring\<^sup>*\<^sup>* P C"
  shows "is_maximal_lit L P = is_maximal_lit L C"
  using assms
  by (induction P rule: converse_rtranclp_induct)
    (simp_all add: ground_factoring_preserves_maximal_literal)

lemma (in ground_ordered_resolution_calculus) ground_factoring_reduces_maximal_pos_lit:
  assumes "ground_factoring P C" and "is_pos L" and
    "is_maximal_lit L P" and "count P L = Suc (Suc n)"
  shows "is_maximal_lit L C" and "count C L = Suc n"
  unfolding atomize_conj
  using \<open>ground_factoring P C\<close>
proof (cases P C rule: ground_factoring.cases)
  case (ground_factoringI t P')
  then show "is_maximal_lit L C \<and> count C L = Suc n"
    by (metis assms(1) assms(3) assms(4) asymp_on_less_lit count_add_mset
        ground_factoring_preserves_maximal_literal is_maximal_in_mset_wrt_iff nat.inject totalpD
        totalp_less_lit transp_on_less_lit)
qed

lemma (in ground_ordered_resolution_calculus) ground_factorings_reduces_maximal_pos_lit:
  assumes "(ground_factoring ^^ m) P C" and "m \<le> Suc n" and "is_pos L" and
    "is_maximal_lit L P" and "count P L = Suc (Suc n)"
  shows "is_maximal_lit L C" and "count C L = Suc (Suc n - m)"
  unfolding atomize_conj
  using \<open>(ground_factoring ^^ m) P C\<close> \<open>m \<le> Suc n\<close>
proof (induction m arbitrary: C)
  case 0
  hence "P = C"
    by simp
  then show ?case
    using assms(4,5) by simp
next
  case (Suc m')
  then show ?case
    by (metis Suc_diff_le Suc_leD assms(3) diff_Suc_Suc ground_factoring_reduces_maximal_pos_lit(2)
        ground_factorings_preserves_maximal_literal relpowp_Suc_E relpowp_imp_rtranclp)
qed

lemma (in ground_ordered_resolution_calculus) full_ground_factorings_reduces_maximal_pos_lit:
  assumes steps: "(ground_factoring ^^ Suc n) P C" and L_pos: "is_pos L" and
    L_max: "is_maximal_lit L P" and L_count: "count P L = Suc (Suc n)"
  shows "is_maximal_lit L C" and "count C L = Suc 0"
  unfolding atomize_conj
  using steps L_max L_count
proof (induction n arbitrary: P)
  case 0
  then show ?case
    using L_pos ground_factorings_reduces_maximal_pos_lit[of "Suc 0" P C 0] by simp
next
  case (Suc n)
  from Suc.prems obtain P' where
    "ground_factoring P P'" and "(ground_factoring ^^ Suc n) P' C"
    by (metis relpowp_Suc_D2)

  from Suc.prems have "is_maximal_lit L P'" and "count P' L = Suc (Suc n)"
    using ground_factoring_reduces_maximal_pos_lit[OF \<open>ground_factoring P P'\<close> L_pos] by simp_all

  thus ?case
    using Suc.IH[OF \<open>(ground_factoring ^^ Suc n) P' C\<close>] by metis
qed


section \<open>Move somewhere?\<close>

lemma lift_tranclp_to_pairs_with_constant_fst:
  "(R x)\<^sup>+\<^sup>+ y z \<Longrightarrow> (\<lambda>(x, y) (x', z). x = x' \<and> R x y z)\<^sup>+\<^sup>+ (x, y) (x, z)"
  by (induction z arbitrary: rule: tranclp_induct) (auto simp: tranclp.trancl_into_trancl)

abbreviation (in preorder) is_lower_fset where
  "is_lower_fset X Y \<equiv> is_lower_set_wrt (<) (fset X) (fset Y)"

lemma trail_false_cls_ignores_duplicates:
  "set_mset C = set_mset D \<Longrightarrow> trail_true_cls \<Gamma> C \<longleftrightarrow> trail_true_cls \<Gamma> D"
  by (simp add: trail_true_cls_def)

lemma not_trail_true_cls_and_trail_false_cls:
  fixes \<Gamma> :: "('a literal \<times> 'a clause option) list" and C :: "'a clause"
  shows "trail_consistent \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
proof (induction \<Gamma> rule: trail_consistent.induct)
  case Nil
  show ?case
    by simp
next
  case (Cons \<Gamma> L u)
  then show ?case
    by (metis trail_consistent.Cons trail_defined_lit_iff_true_or_false trail_false_cls_def
        trail_false_cls_iff_not_trail_interp_entails trail_interp_cls_if_trail_true)
qed

lemma trail_true_lit_if_trail_true_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma>' K \<Longrightarrow> trail_true_lit \<Gamma> K"
  by (meson image_mono set_mono_suffix subsetD trail_true_lit_def)

lemma trail_true_cls_if_trail_true_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_true_cls \<Gamma>' C \<Longrightarrow> trail_true_cls \<Gamma> C"
  using trail_true_cls_def trail_true_lit_if_trail_true_suffix by metis

lemma not_lit_and_comp_lit_false_if_trail_consistent:
  assumes "trail_consistent \<Gamma>"
  shows "\<not> (trail_false_lit \<Gamma> L \<and> trail_false_lit \<Gamma> (- L))"
  using assms
proof (induction \<Gamma>)
  case Nil
  show ?case
    by simp
next
  case (Cons \<Gamma> K u)
  show ?case
  proof (cases "K = L \<or> K = - L")
    case True
    thus ?thesis
      unfolding trail_false_lit_def uminus_of_uminus_id
      unfolding de_Morgan_conj list.set image_insert prod.sel
      by (metis Cons.hyps(1) insertE trail_defined_lit_def uminus_not_id' uminus_of_uminus_id)
  next
    case False
    thus ?thesis
      unfolding trail_false_lit_def uminus_of_uminus_id
      by (metis (no_types, lifting) Cons.IH fst_conv image_iff set_ConsD trail_false_lit_def
          uminus_of_uminus_id)
  qed
qed

lemma not_both_lit_and_comp_lit_in_false_clause_if_trail_consistent:
  assumes \<Gamma>_consistent: "trail_consistent \<Gamma>" and C_false: "trail_false_cls \<Gamma> C"
  shows "\<not> (L \<in># C \<and> - L \<in># C)"
proof (rule notI)
  assume "L \<in># C \<and> - L \<in># C"

  hence "trail_false_lit \<Gamma> L \<and> trail_false_lit \<Gamma> (- L)"
    using C_false unfolding trail_false_cls_def by metis

  thus False
    using \<Gamma>_consistent not_lit_and_comp_lit_false_if_trail_consistent by metis
qed

lemma lower_set_wrt_prefixI:
  assumes
    trans: "transp_on (set zs) R" and
    asym: "asymp_on (set zs) R" and
    sorted: "sorted_wrt R zs" and
    prefix: "prefix xs zs"
  shows "is_lower_set_wrt R (set xs) (set zs)"
proof -
  obtain ys where "zs = xs @ ys"
    using prefix by (auto elim: prefixE)

  show ?thesis
    using trans asym sorted
    unfolding \<open>zs = xs @ ys\<close>
    by (metis lower_set_wrt_appendI)
qed

lemmas (in preorder) lower_set_prefixI =
  lower_set_wrt_prefixI[OF transp_on_less asymp_on_less]

lemma lower_set_wrt_suffixI:
  assumes
    trans: "transp_on (set zs) R" and
    asym: "asymp_on (set zs) R" and
    sorted: "sorted_wrt R\<inverse>\<inverse> zs" and
    suffix: "suffix ys zs"
  shows "is_lower_set_wrt R (set ys) (set zs)"
proof -
  obtain xs where "zs = xs @ ys"
    using suffix by (auto elim: suffixE)

  show ?thesis
    using trans asym sorted
    unfolding \<open>zs = xs @ ys\<close>
    by (smt (verit, del_insts) Un_iff \<open>zs = xs @ ys\<close> asymp_onD asymp_on_conversep conversepI
        is_lower_set_wrt_def set_append set_mono_suffix sorted_wrt_append suffix)
qed

lemmas (in preorder) lower_set_suffixI =
  lower_set_wrt_suffixI[OF transp_on_less asymp_on_less]


lemma true_cls_repeat_mset_Suc[simp]: "I \<TTurnstile> repeat_mset (Suc n) C \<longleftrightarrow> I \<TTurnstile> C"
  by (induction n) simp_all

lemma (in backward_simulation)
  assumes "match i S1 S2" and "\<not> L1.inf_step S1"
  shows "\<not> L2.inf_step S2"
  using assms match_inf by metis

lemma (in scl_fol_calculus) grounding_of_clss_ground:
  assumes "is_ground_clss N"
  shows "grounding_of_clss N = N"
proof -
  have "grounding_of_clss N = (\<Union> C \<in> N. grounding_of_cls C)"
    unfolding grounding_of_clss_def by simp
  also have "\<dots> = (\<Union> C \<in> N. {C})"
    using \<open>is_ground_clss N\<close>
    by (simp add: is_ground_clss_def grounding_of_cls_ground)
  also have "\<dots> = N"
    by simp
  finally show ?thesis .
qed

lemma (in scl_fol_calculus) propagateI':
  "C |\<in>| N |\<union>| U \<Longrightarrow> C = add_mset L C' \<Longrightarrow> is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow>
    \<forall>K \<in># C \<cdot> \<gamma>. atm_of K \<preceq>\<^sub>B \<beta> \<Longrightarrow>
    C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#} \<Longrightarrow> C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#} \<Longrightarrow>
    trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<Longrightarrow>
    \<Gamma>' = trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma> \<Longrightarrow>
    propagate N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)"
  using propagateI by metis

lemma (in scl_fol_calculus) decideI':
  "is_ground_lit (L \<cdot>l \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow> atm_of L \<cdot>a \<gamma> \<preceq>\<^sub>B \<beta> \<Longrightarrow>
    \<Gamma>' = trail_decide \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    decide N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)"
  by (auto intro!: decideI)

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

definition lit_of_glit :: "'f gterm literal \<Rightarrow> ('f, 'v) term literal" where
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

lemma ground_atm_of_lit_of_glit[simp]: "Term_Context.ground (atm_of (lit_of_glit L))"
  by (simp add: atm_of_lit_of_glit_conv)

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

lemma vars_lit_lit_of_glit[simp]: "vars_lit (lit_of_glit L) = {}"
  by simp

lemma vars_cls_cls_of_gcls[simp]: "vars_cls (cls_of_gcls C) = {}"
  by (metis is_ground_cls_cls_of_gcls is_ground_cls_iff_vars_empty)

definition atms_of_cls :: "'a clause \<Rightarrow> 'a fset" where
  "atms_of_cls C = atm_of |`| fset_mset C"

definition atms_of_clss :: "'a clause fset \<Rightarrow> 'a fset" where
  "atms_of_clss N = ffUnion (atms_of_cls |`| N)"

lemma atms_of_clss_fempty[simp]: "atms_of_clss {||} = {||}"
  unfolding atms_of_clss_def by simp

definition lits_of_clss :: "'a clause fset \<Rightarrow> 'a literal fset" where
  "lits_of_clss N = ffUnion (fset_mset |`| N)"

definition lit_occures_in_clss where
  "lit_occures_in_clss L N \<longleftrightarrow> fBex N (\<lambda>C. L \<in># C)"

inductive constant_context for R where
  "R \<C> \<D> \<D>' \<Longrightarrow> constant_context R (\<C>, \<D>) (\<C>, \<D>')"

lemma rtranclp_constant_context: "(R \<C>)\<^sup>*\<^sup>* \<D> \<D>' \<Longrightarrow> (constant_context R)\<^sup>*\<^sup>* (\<C>, \<D>) (\<C>, \<D>')"
  by (induction \<D>' rule: rtranclp_induct) (auto intro: constant_context.intros rtranclp.intros)

lemma tranclp_constant_context: "(R \<C>)\<^sup>+\<^sup>+ \<D> \<D>' \<Longrightarrow> (constant_context R)\<^sup>+\<^sup>+ (\<C>, \<D>) (\<C>, \<D>')"
  by (induction \<D>' rule: tranclp_induct) (auto intro: constant_context.intros tranclp.intros)

lemma right_unique_constant_context:
  assumes R_ru: "\<And>\<C>. right_unique (R \<C>)"
  shows "right_unique (constant_context R)"
proof (rule right_uniqueI)
  fix x y z
  show "constant_context R x y \<Longrightarrow> constant_context R x z \<Longrightarrow> y = z"
    using R_ru[THEN right_uniqueD]
    by (elim constant_context.cases) (metis prod.inject)
qed

lemma safe_state_if_invars:
  fixes N s
  assumes
    \<R>_preserves_\<I>:
      "\<And>N s s'. \<R> N s s' \<Longrightarrow> \<I> N s \<Longrightarrow> \<I> N s'" and
    ex_\<R>_if_not_final:
      "\<And>N s. \<not> \<F> (N, s) \<Longrightarrow> \<I> N s \<Longrightarrow> \<exists>s'. \<R> N s s'"
  assumes invars: "\<I> N s"
  shows "safe_state (constant_context \<R>) \<F> (N, s)"
  unfolding safe_state_def
proof (intro allI impI)
  fix S'
  assume "(constant_context \<R>)\<^sup>*\<^sup>* (N, s) S'"
  then obtain s' where "S' = (N, s')" and "(\<R> N)\<^sup>*\<^sup>* s s'" and "\<I> N s'"
    using invars
  proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
    case base
    thus ?case by simp
  next
    case (step z)
    thus ?case
      by (metis (no_types, opaque_lifting) Pair_inject \<R>_preserves_\<I> constant_context.cases
          converse_rtranclp_into_rtranclp)
  qed
  hence "\<not> \<F> (N, s') \<Longrightarrow> \<exists>s''. \<R> N s' s''"
    using ex_\<R>_if_not_final[of N s'] by argo
  hence "\<not> \<F> S' \<Longrightarrow> \<exists>S''. constant_context \<R> S' S''"
    unfolding \<open>S' = (N, s')\<close> using constant_context.intros by metis
  thus "\<F> S' \<or> Ex (constant_context \<R> S')"
    by argo
qed


definition The_optional :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "The_optional P = (if \<exists>!x. P x then Some (THE x. P x) else None)"

lemma The_optional_eq_SomeD: "The_optional P = Some x \<Longrightarrow> P x"
  unfolding The_optional_def
  by (metis option.discI option.inject theI_unique)

lemma Some_eq_The_optionalD: "Some x = The_optional P \<Longrightarrow> P x"
  using The_optional_eq_SomeD by metis

lemma The_optional_eq_NoneD: "The_optional P = None \<Longrightarrow> \<nexists>!x. P x"
  unfolding The_optional_def
  by (metis option.discI)

lemma None_eq_The_optionalD: "None = The_optional P \<Longrightarrow> \<nexists>!x. P x"
  unfolding The_optional_def
  by (metis option.discI)

lemma The_optional_eq_SomeI:
  assumes "\<exists>\<^sub>\<le>\<^sub>1x. P x" and "P x"
  shows "The_optional P = Some x"
  using assms by (metis The_optional_def the1_equality')

definition full_run where
  "full_run \<R> x y \<longleftrightarrow> \<R>\<^sup>*\<^sup>* x y \<and> (\<nexists>z. \<R> y z)"

lemma Uniq_full_run:
  assumes Uniq_R: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y"
  shows "\<exists>\<^sub>\<le>\<^sub>1y. full_run R x y"
  unfolding full_run_def
  using assms
  by (smt (verit, best) UniqI right_unique_iff rtranclp_complete_run_right_unique)

lemma ex1_full_run:
  assumes Uniq_R: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y" and wfP_R: "wfP R\<inverse>\<inverse>"
  shows "\<exists>!y. full_run R x y"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1 y. full_run R x y"
    using Uniq_full_run[of R x] Uniq_R by argo

  moreover have "\<exists>y. full_run R x y"
    using ex_terminating_rtranclp[OF wfP_R, of x, folded full_run_def] .

  ultimately show ?thesis
    using Uniq_implies_ex1 by metis
qed

lemma full_run_preserves_invariant:
  assumes
    run: "full_run R x y" and
    P_init: "P x" and
    R_preserves_P: "\<And>x y. R x y \<Longrightarrow> P x \<Longrightarrow> P y"
  shows "P y"
proof -
  from run have "R\<^sup>*\<^sup>* x y"
    unfolding full_run_def by simp
  thus "P y"
    using P_init
  proof (induction x rule: converse_rtranclp_induct)
    case base
    thus ?case
      by assumption
  next
    case (step x x')
    then show ?case
      using R_preserves_P by metis
  qed
qed


type_synonym 'f gliteral = "'f gterm literal"
type_synonym 'f gclause = "'f gterm clause"



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



section \<open>Ground ordered resolution for ground terms\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

sublocale ord_res: ground_ordered_resolution_calculus "(\<prec>\<^sub>t)" "\<lambda>_. {#}"
  by unfold_locales auto

sublocale linorder_trm: linorder "(\<preceq>\<^sub>t)" "(\<prec>\<^sub>t)"
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

sublocale linorder_lit: linorder "(\<preceq>\<^sub>l)" "(\<prec>\<^sub>l)"
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

sublocale linorder_cls: linorder "(\<preceq>\<^sub>c)" "(\<prec>\<^sub>c)"
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

declare linorder_trm.is_least_in_fset_ffilterD[no_atp]
declare linorder_lit.is_least_in_fset_ffilterD[no_atp]
declare linorder_cls.is_least_in_fset_ffilterD[no_atp]

end


section \<open>Common definitions and lemmas\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

abbreviation ord_res_Interp where
  "ord_res_Interp N C \<equiv> ord_res.interp N C \<union> ord_res.production N C"

definition is_least_false_clause where
  "is_least_false_clause N C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"

lemma is_least_false_clause_finsert_smaller_false_clause:
  assumes
    D_least: "is_least_false_clause N D" and
    "C \<prec>\<^sub>c D" and
    C_false: "\<not> ord_res_Interp (fset (finsert C N)) C \<TTurnstile> C"
  shows "is_least_false_clause (finsert C N) C"
  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "C |\<in>| finsert C N"
    by simp
next
  show "\<not> ord_res_Interp (fset (finsert C N)) C \<TTurnstile> C"
    using assms by metis
next
  fix y
  assume "y |\<in>| finsert C N" and "y \<noteq> C" and y_false: "\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y"
  hence "y |\<in>| N"
    by simp

  have "\<not> (y \<prec>\<^sub>c C)"
  proof (rule notI)
    assume "y \<prec>\<^sub>c C"
    hence "ord_res_Interp (fset (finsert C N)) y = ord_res_Interp (fset N) y"
      using ord_res.Interp_insert_greater_clause by simp

    hence "\<not> ord_res_Interp (fset N) y \<TTurnstile> y"
      using y_false by argo

    moreover have "y \<prec>\<^sub>c D"
      using \<open>y \<prec>\<^sub>c C\<close> \<open>C \<prec>\<^sub>c D\<close> by order

    ultimately show False
      using D_least
      by (metis (mono_tags, lifting) \<open>y |\<in>| N\<close> linorder_cls.is_least_in_ffilter_iff
          linorder_cls.less_asym' is_least_false_clause_def)
  qed
  thus "C \<prec>\<^sub>c y"
    using \<open>y \<noteq> C\<close> by order
qed

lemma is_least_false_clause_swap_swap_compatible_fsets:
  assumes "{|x |\<in>| N1. x \<preceq>\<^sub>c C|} = {|x |\<in>| N2. x \<preceq>\<^sub>c C|}"
  shows "is_least_false_clause N1 C \<longleftrightarrow> is_least_false_clause N2 C"
proof -
  have "is_least_false_clause N2 C" if
    subsets_agree: "{|x |\<in>| N1. x \<preceq>\<^sub>c C|} = {|x |\<in>| N2. x \<preceq>\<^sub>c C|}" and
    C_least: "is_least_false_clause N1 C" for N1 N2 C
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    have "C |\<in>| N1"
      using C_least
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by argo
    thus "C |\<in>| N2"
      using subsets_agree by auto
  next
    have "\<not> ord_res_Interp (fset N1) C \<TTurnstile> C"
      using C_least
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by argo
    moreover have "ord_res_Interp (fset N1) C = ord_res_Interp (fset N2) C"
      using subsets_agree by (auto intro!: ord_res.Interp_swap_clause_set) 
    ultimately show "\<not> ord_res_Interp (fset N2) C \<TTurnstile> C"
      by argo
  next
    fix y assume "y |\<in>| N2" and "y \<noteq> C"
    show "\<not> ord_res_Interp (fset N2) y \<TTurnstile> y \<Longrightarrow> C \<prec>\<^sub>c y"
    proof (erule contrapos_np)
      assume "\<not> C \<prec>\<^sub>c y"
      hence "y \<preceq>\<^sub>c C"
        by order
      hence "y |\<in>| N1"
        using \<open>y |\<in>| N2\<close> using subsets_agree by auto
      hence "\<not> ord_res_Interp (fset N1) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
        using \<open>is_least_false_clause N1 C\<close> \<open>y \<noteq> C\<close>
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
        by metis
      moreover have "ord_res_Interp (fset N1) y = ord_res_Interp (fset N2) y"
      proof (rule ord_res.Interp_swap_clause_set)
        show "{D. D |\<in>| N1 \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D y} = {D. D |\<in>| N2 \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D y}"
          using subsets_agree \<open>y \<preceq>\<^sub>c C\<close> by fastforce
      qed simp_all
      ultimately show "ord_res_Interp (fset N2) y \<TTurnstile> y"
        using \<open>y \<preceq>\<^sub>c C\<close> by auto
    qed
  qed
  thus ?thesis
    using assms by metis
qed

lemma Uniq_is_least_false_clause: "\<exists>\<^sub>\<le>\<^sub>1 C. is_least_false_clause N C"
proof (rule Uniq_I)
  show "\<And>x y z. is_least_false_clause x y \<Longrightarrow> is_least_false_clause x z \<Longrightarrow> y = z"
    unfolding is_least_false_clause_def
    by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
qed

lemma mempty_lesseq_cls[simp]: "{#} \<preceq>\<^sub>c C" for C
  by (cases C) (simp_all add: strict_subset_implies_multp)

lemma is_least_false_clause_mempty: "{#} |\<in>| N \<Longrightarrow> is_least_false_clause N {#}"
  using is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff mempty_lesseq_cls
  by fastforce

lemma production_union_unproductive_strong:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2 - N1. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using ord_res.wfP_less_cls C_in
proof (induction C rule: wfp_induct_rule)
  case (less C)
  hence C_in_iff: "C \<in> N1 \<union> N2 \<longleftrightarrow> C \<in> N1"
    by simp

  have interp_eq: "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C"
  proof -
    have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
      unfolding ord_res.interp_def ..
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2 - N1. D \<prec>\<^sub>c C})"
      by auto
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C})"
      using N2_unproductive by simp
    also have "\<dots> = \<Union> (ord_res.production N1 ` {D \<in> N1. D \<prec>\<^sub>c C})"
      using less.IH by simp
    also have "\<dots> = ord_res.interp N1 C"
      unfolding ord_res.interp_def ..
    finally show "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C" .
  qed

  show ?case
    unfolding ord_res.production_unfold C_in_iff interp_eq by argo
qed

lemma production_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using production_union_unproductive_strong assms by simp

lemma interp_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}"
  shows "ord_res.interp (N1 \<union> N2) = ord_res.interp N1"
proof (rule ext)
  fix C
  have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
    unfolding ord_res.interp_def ..
  also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2. D \<prec>\<^sub>c C})"
    by auto
  also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C})"
    using N2_unproductive by simp
  also have "\<dots> = \<Union> (ord_res.production N1 ` {D \<in> N1. D \<prec>\<^sub>c C})"
    using production_union_unproductive[OF fin N2_unproductive] by simp
  also have "\<dots> = ord_res.interp N1 C"
    unfolding ord_res.interp_def ..
  finally show "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C" .
qed

lemma Interp_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}"
  shows "ord_res_Interp (N1 \<union> N2) C = ord_res_Interp N1 C"
  unfolding interp_union_unproductive[OF assms]
  using production_union_unproductive[OF assms]
  using N2_unproductive[rule_format]
  by (metis (no_types, lifting) Un_iff empty_Collect_eq ord_res.production_unfold)

lemma Interp_insert_unproductive:
  assumes
    fin: "finite N1" and
    x_unproductive: "ord_res.production (insert x N1) x = {}"
  shows "ord_res_Interp (insert x N1) C = ord_res_Interp N1 C"
  using assms Interp_union_unproductive
  by (metis Un_commute finite.emptyI finite.insertI insert_is_Un singletonD)

lemma extended_partial_model_entails_iff_partial_model_entails:
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N"
  shows "ord_res_Interp (N \<union> N') C \<TTurnstile> C \<longleftrightarrow> ord_res_Interp N C \<TTurnstile> C"
  using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  by metis

lemma nex_strictly_maximal_pos_lit_if_factorizable:
  assumes "ord_res.ground_factoring C C'"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  by (metis Uniq_D add_mset_remove_trivial assms linorder_lit.Uniq_is_maximal_in_mset
      linorder_lit.dual_order.order_iff_strict linorder_lit.is_greatest_in_mset_iff
      linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.not_less
      ord_res.ground_factoring.cases union_single_eq_member)

lemma unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "ord_res.production N C = {}"
  using assms by (simp add: ord_res.production_unfold)

lemma ball_unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<forall>C \<in> N'. \<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "\<forall>C \<in> N'. ord_res.production (N \<union> N') C = {}"
  using assms unproductive_if_nex_strictly_maximal_pos_lit by metis

lemma is_least_false_clause_finsert_cancel:
  assumes
    C_unproductive: "ord_res.production (fset (finsert C N)) C = {}" and
    C_entailed_by_smaller: "\<exists>D |\<in>| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (finsert C N) = is_least_false_clause N"
proof (intro ext iffI)
  fix E
  assume E_least: "is_least_false_clause (finsert C N) E"
  hence
    E_in: "E |\<in>| finsert C N" and
    E_false: "\<not> ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E" and
    E_least: "(\<forall>y |\<in>| finsert C N. y \<noteq> E \<longrightarrow> \<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y \<longrightarrow> E \<prec>\<^sub>c y)"
    unfolding atomize_conj is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  obtain D where
    "D |\<in>| N" and "D \<prec>\<^sub>c C" and "{D} \<TTurnstile>e {C}"
    using C_entailed_by_smaller by metis

  show "is_least_false_clause N E"
  proof (cases "C = E")
    case True

    have "E \<prec>\<^sub>c D"
    proof (rule E_least[rule_format])
      show "D |\<in>| finsert C N"
        using \<open>D |\<in>| N\<close> by simp
    next
      show "D \<noteq> E"
        using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> by order
    next
      show "\<not> ord_res_Interp (fset (finsert C N)) D \<TTurnstile> D"
        using E_false
      proof (rule contrapos_nn)
        assume "ord_res_Interp (fset (finsert C N)) D \<TTurnstile> D"
        thus "ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E"
          using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> \<open>{D} \<TTurnstile>e {C}\<close> ord_res.entailed_clause_stays_entailed by auto
      qed
    qed
    hence False
      using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> by order
    thus ?thesis ..
  next
    case False
    show ?thesis
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "E |\<in>| N"
        using E_in \<open>C \<noteq> E\<close> by simp
    next
      have "ord_res_Interp (fset (finsert C N)) E = ord_res_Interp (fset N) E"
        using C_unproductive Interp_insert_unproductive by simp
      thus "\<not> ord_res_Interp (fset N) E \<TTurnstile> E"
        using E_false by argo
    next
      show "\<And>y. y |\<in>| N \<Longrightarrow> y \<noteq> E \<Longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<Longrightarrow> E \<prec>\<^sub>c y"
        using E_least C_unproductive Interp_insert_unproductive by auto
    qed
  qed
next
  fix E
  assume "is_least_false_clause N E"
  hence
    E_in: "E |\<in>| N" and
    E_false: "\<not> ord_res_Interp (fset N) E \<TTurnstile> E" and
    E_least: "(\<forall>y |\<in>| N. y \<noteq> E \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> E \<prec>\<^sub>c y)"
    unfolding atomize_conj is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  show "is_least_false_clause (finsert C N) E"
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    show "E |\<in>| finsert C N"
      using E_in by simp
  next
    show "\<not> ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E"
      using E_least E_false C_unproductive Interp_insert_unproductive by simp
  next
    fix y
    assume "y |\<in>| finsert C N" and "y \<noteq> E" and "\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y"
    show "E \<prec>\<^sub>c y"
    proof (cases "y = C")
      case True
      thus ?thesis
      using E_least \<open>\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y\<close>
      by (metis (no_types, lifting) C_entailed_by_smaller C_unproductive Interp_insert_unproductive
          finite_fset fset_simps(2) linorder_cls.dual_order.strict_trans
          ord_res.entailed_clause_stays_entailed true_clss_singleton)
    next
      case False
      thus ?thesis
        using E_least \<open>y |\<in>| finsert C N\<close> \<open>y \<noteq> E\<close> \<open>\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y\<close>
        using C_unproductive Interp_insert_unproductive by auto
    qed
  qed
qed

lemma is_least_false_clause_funion_cancel_right_strong:
  assumes
    "\<forall>C |\<in>| N2 - N1. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2 - N1. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms
proof (induction N2)
  case empty
  thus ?case
    by simp
next
  case (insert C N2)

  have IH: "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  proof (rule insert.IH)
    show "\<forall>C|\<in>|N2 |-| N1. \<forall>U. ord_res.production U C = {}"
      using insert.prems(1) by auto
  next
    show "\<forall>C|\<in>|N2 |-| N1. \<exists>D|\<in>|N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
      using insert.prems(2) by auto
  qed

  show ?case
  proof (cases "C |\<in>| N1")
    case True
    hence "is_least_false_clause (N1 |\<union>| finsert C N2) = is_least_false_clause (N1 |\<union>| N2)"
      by (simp add: finsert_absorb)
    also have "\<dots> = is_least_false_clause N1"
      using IH .
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using is_least_false_clause_finsert_cancel IH
      by (metis finsertCI fminusI funionI1 funion_finsert_right insert.prems(1) insert.prems(2))
  qed
qed

lemma is_least_false_clause_funion_cancel_right:
  assumes
    "\<forall>C |\<in>| N2. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms is_least_false_clause_funion_cancel_right_strong by simp

definition ex_false_clause where
  "ex_false_clause N = (\<exists>C \<in> N. \<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C)"

lemma obtains_least_false_clause_if_ex_false_clause:
  assumes "ex_false_clause (fset N)"
  obtains C where "is_least_false_clause N C"
  using assms
  by (metis (mono_tags, lifting) bot_fset.rep_eq emptyE ex_false_clause_def ffmember_filter
      linorder_cls.ex_least_in_fset is_least_false_clause_def)

lemma ex_false_clause_if_least_false_clause:
  assumes "is_least_false_clause N C"
  shows "ex_false_clause (fset N)"
  using assms
  by (metis (no_types, lifting) ex_false_clause_def is_least_false_clause_def
      linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2))

lemma ex_false_clause_iff: "ex_false_clause (fset N) \<longleftrightarrow> (\<exists>C. is_least_false_clause N C)"
  using obtains_least_false_clause_if_ex_false_clause ex_false_clause_if_least_false_clause by metis

definition ord_res_model where
  "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"

lemma ord_res_model_eq_interp_union_production_of_greatest_clause:
  assumes C_greatest: "linorder_cls.is_greatest_in_set N C"
  shows "ord_res_model N = ord_res.interp N C \<union> ord_res.production N C"
proof -
  have "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"
    unfolding ord_res_model_def ..
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<preceq>\<^sub>c C}. ord_res.production N D)"
    using C_greatest linorder_cls.is_greatest_in_set_iff by auto
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<union> {C}. ord_res.production N D)"
    using C_greatest linorder_cls.is_greatest_in_set_iff by auto
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. ord_res.production N D) \<union> ord_res.production N C"
    by auto
  also have "\<dots> = ord_res.interp N C \<union> ord_res.production N C"
    unfolding ord_res.interp_def ..
  finally show ?thesis .
qed

lemma ord_res_model_entails_clauses_if_nex_false_clause:
  assumes "finite N" and "N \<noteq> {}" and "\<not> ex_false_clause N"
  shows "ord_res_model N \<TTurnstile>s N"
  unfolding true_clss_def
proof (intro ballI)
  from \<open>\<not> ex_false_clause N\<close> have ball_true:
    "\<forall>C \<in> N. ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    by (simp add: ex_false_clause_def)

  from \<open>finite N\<close> \<open>N \<noteq> {}\<close> obtain D where
    D_greatest: "linorder_cls.is_greatest_in_set N D"
    using linorder_cls.ex_greatest_in_set by metis

  fix C assume "C \<in> N"
  hence "ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    using ball_true by metis

  moreover have "C \<preceq>\<^sub>c D"
    using \<open>C \<in> N\<close> D_greatest[unfolded linorder_cls.is_greatest_in_set_iff] by auto

  ultimately have "ord_res.interp N D \<union> ord_res.production N D \<TTurnstile> C"
    using ord_res.entailed_clause_stays_entailed by auto

  thus "ord_res_model N \<TTurnstile> C"
    using ord_res_model_eq_interp_union_production_of_greatest_clause[OF D_greatest] by argo
qed

lemma pos_lit_not_greatest_if_maximal_in_least_false_clause:
  assumes
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C" and
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
  shows "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Pos A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

  from C_least have
    C_in: "C |\<in>| N" and
    C_false: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_lt: "\<forall>y |\<in>| N. y \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
    unfolding linorder_cls.is_least_in_ffilter_iff by auto

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> ord_res_Interp (fset N) C"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  have "{D \<in> fset N. D \<preceq>\<^sub>c C} = {D \<in> fset N. D \<prec>\<^sub>c C} \<union> {D \<in> fset N. D = C}"
    by fastforce
  with C_unproductive have
    "ord_res_Interp (fset N) C = ord_res.interp (fset N) C"
    by simp
  with C_false have C_false': "\<not> ord_res.interp (fset N) C \<TTurnstile> C"
    by simp

  from C_unproductive have "A \<notin> ord_res.production (fset N) C"
    by simp
  thus ?thesis
  proof (rule contrapos_nn)
    assume "ord_res.is_strictly_maximal_lit (Pos A) C"
    then show "A \<in> ord_res.production (fset N) C"
      unfolding ord_res.production_unfold[of "fset N" C] mem_Collect_eq
      using C_in C_def C_false'
      by metis
  qed
qed

lemma ex_ground_factoringI:
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C" and
    C_not_max_lit: "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
proof -
  from C_max_lit C_not_max_lit have "count C (Pos A) \<ge> 2"
    using linorder_lit.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset by metis
  then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
    by (metis two_le_countE)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_factoring C (add_mset (Pos A) C')"
      using ord_res.ground_factoringI[of C A C']
      using C_def C_max_lit by metis
  qed
qed

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

lemma bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit:
  assumes
    C_least_false: "is_least_false_clause N C" and
    Neg_A_max: "ord_res.is_maximal_lit (Neg A) C"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
    ord_res.production (fset N) D = {A})"
proof -
  from C_least_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_min: "\<forall>y |\<in>| N. y \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
    unfolding atomize_conj is_least_false_clause_def
    unfolding linorder_cls.is_least_in_ffilter_iff
    by argo

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> ord_res_Interp (fset N) C"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  from Neg_A_max have "Neg A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

  from C_false have "\<not> ord_res_Interp (fset N) C \<TTurnstile>l Neg A"
    using true_cls_if_true_lit_in[OF \<open>Neg A \<in># C\<close>]
    by meson
  hence "A \<in> ord_res_Interp (fset N) C"
    by simp
  with C_unproductive have "A \<in> ord_res.interp (fset N) C"
    by blast
  then obtain D where
    D_in: "D |\<in>| N" and D_lt_C: "D \<prec>\<^sub>c C" and D_productive: "A \<in> ord_res.production (fset N) D"
    unfolding ord_res.interp_def by auto

  from D_productive have "ord_res.is_strictly_maximal_lit (Pos A) D"
    using ord_res.mem_productionE by metis

  moreover have "ord_res.production (fset N) D = {A}"
    using D_productive ord_res.production_eq_empty_or_singleton by fastforce

  ultimately show ?thesis
    using D_in D_lt_C by metis
qed

lemma bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit':
  assumes
    C_least_false: "is_least_false_clause N C" and
    L_max: "ord_res.is_maximal_lit L C" and
    L_neg: "is_neg L"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (- L) D \<and>
    ord_res.production (fset N) D = {atm_of L})"
  using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit[OF C_least_false]
  by (simp add: L_max L_neg uminus_literal_def)

lemma ex_ground_resolutionI:
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_lt: "D \<prec>\<^sub>c C" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D"
  shows "\<exists>CD. ord_res.ground_resolution C D CD"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Neg A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

  from D_max_lit obtain D' where D_def: "D = add_mset (Pos A) D'"
    by (meson linorder_lit.is_greatest_in_mset_iff mset_add)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_resolution C D (C' + D')"
      using ord_res.ground_resolutionI[of C A C' D D']
      using C_def D_def D_lt C_max_lit D_max_lit by metis
  qed
qed



lemma
  fixes N N'
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N" and
    C_not_entailed: "\<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
  shows "\<not> ord_res.interp (N \<union> N') C \<union> ord_res.production (N \<union> N') C \<TTurnstile> C"
  using C_not_entailed
proof (rule contrapos_nn)
  assume "ord_res.interp (N \<union> N') C \<union> ord_res.production (N \<union> N') C \<TTurnstile> C"
  then show "ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
    using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
    by metis
qed

end


section \<open>Function for full factorization\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition efac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "efac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

text \<open>The function \<^const>\<open>efac\<close> performs exhaustive factorization of its input clause.\<close>

lemma ex1_efac_eq_factoring_chain:
  "\<exists>!C'. efac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
proof -
  have "right_unique (\<lambda>x y. ord_res.ground_factoring\<^sup>*\<^sup>* x y \<and> (\<nexists>z. ord_res.ground_factoring y z))"
    using ord_res.unique_ground_factoring right_unique_terminating_rtranclp right_unique_iff
    by blast

  moreover obtain C' where "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex_terminating_rtranclp[OF ord_res.termination_ground_factoring]
    by metis

  ultimately have "efac C = C'"
    by (simp add: efac_def right_unique_def the_equality)

  then show ?thesis
    using \<open>ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')\<close> by blast
qed

lemma efac_eq_disj:
  "efac C = C \<or> (\<exists>!C'. efac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"
  using ex1_efac_eq_factoring_chain
  by (metis is_pos_def)

lemma member_mset_if_count_eq_Suc: "count X x = Suc n \<Longrightarrow> x \<in># X"
  by (simp add: count_inI)

lemmas member_fsetE = mset_add

lemma ord_res_ground_factoring_iff: "ord_res.ground_factoring C C' \<longleftrightarrow>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and> C' = C - {#Pos A#}))"
proof (rule iffI)
  assume "ord_res.ground_factoring C C'"
  thus "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and> C' = C - {#Pos A#})"
  proof (cases C C' rule: ord_res.ground_factoring.cases)
    case (ground_factoringI A P')
    show ?thesis
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (Pos A) C"
        using \<open>ord_res.is_maximal_lit (Pos A) C\<close> .
    next
      show "count C (Pos A) = Suc (Suc (count P' (Pos A)))"
        unfolding \<open>C = add_mset (Pos A) (add_mset (Pos A) P')\<close> by simp
    next
      show "C' = remove1_mset (Pos A) C"
        unfolding \<open>C = add_mset (Pos A) (add_mset (Pos A) P')\<close> \<open>C' = add_mset (Pos A) P'\<close> by simp
    qed
  qed
next
  assume "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and>
    (\<exists>n. count C (Pos A) = Suc (Suc n) \<and> C' = C - {#Pos A#})"
  then obtain A n where
    "ord_res.is_maximal_lit (Pos A) C" and
    "count C (Pos A) = Suc (Suc n)" and
    "C' = C - {#Pos A#}"
    by metis

  have "Pos A \<in># C"
    using \<open>count C (Pos A) = Suc (Suc n)\<close> member_mset_if_count_eq_Suc by metis
  then obtain C'' where "C = add_mset (Pos A) C''"
    by (auto elim: member_fsetE)
  with \<open>count C (Pos A) = Suc (Suc n)\<close> have "count C'' (Pos A) = Suc n"
    by simp
  hence "Pos A \<in># C''"
    using member_mset_if_count_eq_Suc by metis
  then obtain C''' where "C'' = add_mset (Pos A) C'''"
    by (auto elim: member_fsetE)

  show "ord_res.ground_factoring C C'"
  proof (rule ord_res.ground_factoringI)
    show "C = add_mset (Pos A) (add_mset (Pos A) C''')"
      using \<open>C = add_mset (Pos A) C''\<close> \<open>C'' = add_mset (Pos A) C'''\<close> by metis
  next
    show "ord_res.is_maximal_lit (Pos A) C"
      using \<open>ord_res.is_maximal_lit (Pos A) C\<close> .
  next
    show "C' = add_mset (Pos A) C'''"
      using \<open>C' = C - {#Pos A#}\<close> \<open>C = add_mset (Pos A) C''\<close> \<open>C'' = add_mset (Pos A) C'''\<close> by simp
  qed simp_all
qed

lemma tranclp_ord_res_ground_factoring_iff:
  "ord_res.ground_factoring\<^sup>+\<^sup>+ C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'') \<longleftrightarrow>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and>
    C' = C - replicate_mset (Suc n) (Pos A)))"
proof (intro iffI; elim exE conjE)
  assume "ord_res.ground_factoring\<^sup>+\<^sup>+ C C'" and "(\<nexists>C''. ord_res.ground_factoring C' C'')"
  then show "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> (\<exists>n. count C (Pos A) = Suc (Suc n) \<and>
    C' = C - replicate_mset (Suc n) (Pos A))"
  proof (induction C rule: converse_tranclp_induct)
    case (base C)
    from base.hyps obtain A n where
      "ord_res.is_maximal_lit (Pos A) C" and
      "count C (Pos A) = Suc (Suc n)" and
      "C' = remove1_mset (Pos A) C"
      unfolding ord_res_ground_factoring_iff by auto

    moreover have "n = 0"
    proof (rule ccontr)
      assume "n \<noteq> 0"
      then obtain C'' where "C' = add_mset (Pos A) (add_mset (Pos A) C'')"
        by (metis (no_types, lifting) Zero_not_Suc calculation(2,3) count_add_mset count_inI
            diff_Suc_1 insert_DiffM)
      hence "ord_res.ground_factoring C' (add_mset (Pos A) C'')"
        using ord_res.ground_factoringI
        by (metis calculation(1,3) linorder_lit.is_maximal_in_mset_iff more_than_one_mset_mset_diff
            union_single_eq_member)
      with base.prems show False
        by metis
    qed

    ultimately show ?case
      by (metis replicate_mset_0 replicate_mset_Suc)
  next
    case (step C C'')
    from step.IH step.prems obtain A n where
      "ord_res.is_maximal_lit (Pos A) C''" and
      "count C'' (Pos A) = Suc (Suc n)" and
      "C' = C'' - replicate_mset (Suc n) (Pos A)"
      by metis

    from step.hyps(1) obtain A' m where
      "ord_res.is_maximal_lit (Pos A') C" and
      "count C (Pos A') = Suc (Suc m)" and
      "C'' = remove1_mset (Pos A') C"
      unfolding ord_res_ground_factoring_iff by metis

    have "A' = A"
      using \<open>ord_res.is_maximal_lit (Pos A) C''\<close> \<open>ord_res.is_maximal_lit (Pos A') C\<close>
      by (metis \<open>C'' = remove1_mset (Pos A') C\<close> \<open>count C (Pos A') = Suc (Suc m)\<close>
          add_mset_remove_trivial_eq count_add_mset count_greater_zero_iff diff_Suc_1
          linorder_lit.antisym_conv3 linorder_lit.is_maximal_in_mset_iff literal.inject(1)
          zero_less_Suc)

    have "m = Suc n"
      using \<open>count C'' (Pos A) = Suc (Suc n)\<close> \<open>count C (Pos A') = Suc (Suc m)\<close>
      unfolding \<open>C'' = remove1_mset (Pos A') C\<close> \<open>A' = A\<close>
      by simp

    show ?case
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (Pos A) C"
        using \<open>ord_res.is_maximal_lit (Pos A') C\<close> \<open>A' = A\<close> by metis
    next
      show "count C (Pos A) = Suc (Suc m)"
        using \<open>count C (Pos A') = Suc (Suc m)\<close> \<open>A' = A\<close> by metis
    next
      show "C' = C - replicate_mset (Suc m) (Pos A)"
        unfolding \<open>C' = C'' - replicate_mset (Suc n) (Pos A)\<close> \<open>C'' = remove1_mset (Pos A') C\<close>
          \<open>A' = A\<close> \<open>m = Suc n\<close>
        by simp
    qed
  qed
next
  fix A n assume "ord_res.is_maximal_lit (Pos A) C"
  thus "count C (Pos A) = Suc (Suc n) \<Longrightarrow> C' = C - replicate_mset (Suc n) (Pos A) \<Longrightarrow>
    ord_res.ground_factoring\<^sup>+\<^sup>+ C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
  proof (induction n arbitrary: C)
    case 0
    hence "(ord_res.is_maximal_lit (Pos A) C \<and>
         (count C (Pos A) = Suc (Suc 0) \<and>
              C' = remove1_mset (Pos A) C))"
      by (metis replicate_mset_0 replicate_mset_Suc)
    hence "ord_res.ground_factoring C C' \<and> (\<nexists>a. ord_res.ground_factoring C' a)"
      unfolding ord_res_ground_factoring_iff
      by (metis Zero_not_Suc add_mset_remove_trivial_eq count_add_mset count_inI
          linorder_lit.antisym_conv3 linorder_lit.is_maximal_in_mset_iff nat.inject)
    thus ?case
      by blast
  next
    case (Suc n)
    have "ord_res.ground_factoring\<^sup>+\<^sup>+ (C - {#Pos A#}) C' \<and> (\<nexists>a. ord_res.ground_factoring C' a)"
    proof (rule Suc.IH)
      show "count (remove1_mset (Pos A) C) (Pos A) = Suc (Suc n)"
        using Suc.prems by simp
    next
      show "C' = remove1_mset (Pos A) C - replicate_mset (Suc n) (Pos A)"
        using Suc.prems by simp
    next
      show "ord_res.is_maximal_lit (Pos A) (remove1_mset (Pos A) C)"
        using Suc.prems
        by (smt (verit, ccfv_SIG) Zero_not_Suc add_diff_cancel_left' add_mset_remove_trivial_eq
            count_add_mset count_inI linorder_lit.is_maximal_in_mset_iff plus_1_eq_Suc)
    qed

    moreover have "ord_res.ground_factoring C (C - {#Pos A#})"
      unfolding ord_res_ground_factoring_iff
    proof (intro exI conjI)
      show "ord_res.is_maximal_lit (Pos A) C"
        using Suc.prems by metis
    next
      show "count C (Pos A) = Suc (Suc (Suc n))"
        using Suc.prems by metis
    next
      show "remove1_mset (Pos A) C = remove1_mset (Pos A) C" ..
    qed

    ultimately show ?case
      by auto
  qed
qed

lemma minus_mset_replicate_mset_eq_add_mset_filter_mset:
  assumes "count X x = Suc n"
  shows "X - replicate_mset n x = add_mset x {#y \<in># X. y \<noteq> x#}"
  using assms
  by (metis add_diff_cancel_left' add_mset_diff_bothsides filter_mset_eq filter_mset_neq
      multiset_partition replicate_mset_Suc union_mset_add_mset_right)

lemma minus_mset_replicate_mset_eq_add_mset_add_mset_filter_mset:
  assumes "count X x = Suc (Suc n)"
  shows "X - replicate_mset n x = add_mset x (add_mset x {#y \<in># X. y \<noteq> x#})"
  using assms
  by (metis add_diff_cancel_left' add_mset_diff_bothsides filter_mset_eq filter_mset_neq
      multiset_partition replicate_mset_Suc union_mset_add_mset_right)

lemma rtrancl_ground_factoring_iff:
  shows "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'') \<longleftrightarrow>
  ((\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> count C (Pos A) \<ge> 2) \<and> C = C' \<or>
   (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}))"
proof (intro iffI; elim exE conjE disjE)
  show "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<Longrightarrow> \<nexists>C''. ord_res.ground_factoring C' C'' \<Longrightarrow>
    (\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> 2 \<le> count C (Pos A)) \<and> C = C' \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
  proof (induction C rule: converse_rtranclp_induct)
    case base
    thus ?case
      by (metis add_2_eq_Suc le_Suc_ex ord_res_ground_factoring_iff)
  next
    case (step y z)
    hence "ord_res.ground_factoring\<^sup>+\<^sup>+ y C' \<and> (\<nexists>x. ord_res.ground_factoring C' x)"
      by simp
    thus ?case
      unfolding tranclp_ord_res_ground_factoring_iff
      by (metis minus_mset_replicate_mset_eq_add_mset_filter_mset)
  qed
next
  assume "\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> 2 \<le> count C (Pos A)" and "C = C'"
  thus "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    by (metis One_nat_def Suc_1 Suc_le_eq Suc_le_mono ord_res_ground_factoring_iff
        rtranclp.rtrancl_refl zero_less_Suc)
next
  fix A assume "ord_res.is_maximal_lit (Pos A) C"
  then obtain n where "count C (Pos A) = Suc n"
    by (meson in_countE linorder_lit.is_maximal_in_mset_iff)
  with \<open>ord_res.is_maximal_lit (Pos A) C\<close> show "C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#} \<Longrightarrow>
    ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
  proof (induction n arbitrary: C)
    case 0

    have "(\<nexists>a. ord_res.ground_factoring C a)"
    proof (intro notI, elim exE)
      fix D assume "ord_res.ground_factoring C D"
      thus False
      proof (cases rule: ord_res.ground_factoring.cases)
        case (ground_factoringI A' P')
        hence "A' = A"
          using \<open>ord_res.is_maximal_lit (Pos A) C\<close>
          using linorder_lit.Uniq_is_maximal_in_mset
          by (metis Uniq_D literal.inject(1))
        thus False
          using \<open>count C (Pos A) = Suc 0\<close> \<open>C = add_mset (Pos A') (add_mset (Pos A') P')\<close> by simp
      qed
    qed
    thus ?case
      by (metis "0.prems"(1) "0.prems"(3) diff_zero
          minus_mset_replicate_mset_eq_add_mset_filter_mset replicate_mset_0 rtranclp.rtrancl_refl)
  next
    case (Suc x)
    then show ?case
      by (metis minus_mset_replicate_mset_eq_add_mset_filter_mset tranclp_into_rtranclp
          tranclp_ord_res_ground_factoring_iff)
  qed
qed

lemma efac_spec: "efac C = C \<or>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
  using efac_eq_disj[of C]
proof (elim disjE)
  assume "efac C = C"
  thus "efac C = C \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
    by metis
next
  assume "\<exists>!C'. efac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and>
    (\<nexists>C''. ord_res.ground_factoring C' C'')"
  then obtain C' where
    "efac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    by metis
  thus "efac C = C \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
    unfolding rtrancl_ground_factoring_iff
    by metis
qed

lemma efac_spec_if_pos_lit_is_maximal:
  assumes L_pos: "is_pos L" and L_max: "ord_res.is_maximal_lit L C"
  shows "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
proof -
  from assms obtain C' where
    "efac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex1_efac_eq_factoring_chain by metis
  thus ?thesis
    unfolding rtrancl_ground_factoring_iff
  proof (elim disjE conjE)
    assume hyps: "\<nexists>A. ord_res.is_maximal_lit (Pos A) C \<and> 2 \<le> count C (Pos A)" "C = C'"
    with assms have "count C L = 1"
      by (metis One_nat_def in_countE is_pos_def le_less_linear less_2_cases_iff
          linorder_lit.is_maximal_in_mset_iff nat_less_le zero_less_Suc)
    hence "C = add_mset L {#K \<in># C. K \<noteq> L#}"
      by (metis One_nat_def diff_zero minus_mset_replicate_mset_eq_add_mset_filter_mset
          replicate_mset_0)
    thus "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      using \<open>efac C = C'\<close> \<open>C = C'\<close> by argo
  next
    assume "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
    thus "efac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      by (metis L_max Uniq_D \<open>efac C = C'\<close> linorder_lit.Uniq_is_maximal_in_mset)
  qed
qed

lemma efac_mempty[simp]: "efac {#} = {#}"
  by (metis empty_iff linorder_lit.is_maximal_in_mset_iff set_mset_empty efac_spec)

lemma set_mset_efac[simp]: "set_mset (efac C) = set_mset C"
  using efac_spec[of C]
proof (elim disjE exE conjE)
  show "efac C = C \<Longrightarrow> set_mset (efac C) = set_mset C"
    by simp
next
  fix A
  assume "ord_res.is_maximal_lit (Pos A) C"
  hence "Pos A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

  assume efac_C_eq: "efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
  show "set_mset (efac C) = set_mset C"
  proof (intro Set.subset_antisym Set.subsetI)
    fix L assume "L \<in># efac C"
    then show "L \<in># C"
      unfolding efac_C_eq
      using \<open>Pos A \<in># C\<close> by auto
  next
    fix L assume "L \<in># C"
    then show "L \<in># efac C"
      unfolding efac_C_eq
      by simp
  qed
qed

lemma efac_subset: "efac C \<subseteq># C"
  using efac_spec[of C]
proof (elim disjE exE conjE)
  show "efac C = C \<Longrightarrow> efac C \<subseteq># C"
    by simp
next
  fix A
  assume "ord_res.is_maximal_lit (Pos A) C" and
    efac_C_eq: "efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
  then show "efac C \<subseteq># C"
    by (smt (verit, ccfv_SIG) filter_mset_add_mset insert_DiffM insert_subset_eq_iff
        linorder_lit.is_maximal_in_mset_iff multiset_filter_subset)
qed

lemma true_cls_efac_iff[simp]:
  fixes \<I> :: "'f gterm set" and C :: "'f gclause"
  shows "\<I> \<TTurnstile> efac C \<longleftrightarrow> \<I> \<TTurnstile> C"
  by (metis set_mset_efac true_cls_iff_set_mset_eq)

lemma obtains_positive_greatest_lit_if_efac_not_ident:
  assumes "efac C \<noteq> C"
  obtains L where "is_pos L" and "linorder_lit.is_greatest_in_mset (efac C) L"
proof -
  from \<open>efac C \<noteq> C\<close> obtain A where
    Pos_A_maximal: "linorder_lit.is_maximal_in_mset C (Pos A)" and
    efac_C_eq: "efac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
    using efac_spec by metis

  assume hyp: "\<And>L. is_pos L \<Longrightarrow> linorder_lit.is_greatest_in_mset (efac C) L \<Longrightarrow> thesis"
  show thesis
  proof (rule hyp)
    show "is_pos (Pos A)"
      by simp
  next
    show "linorder_lit.is_greatest_in_mset(efac C) (Pos A)"
      unfolding efac_C_eq linorder_lit.is_greatest_in_mset_iff
      using Pos_A_maximal[unfolded linorder_lit.is_maximal_in_mset_iff]
      by auto
  qed
qed

lemma mempty_in_image_efac_iff[simp]: "{#} \<in> efac ` N \<longleftrightarrow> {#} \<in> N"
  by (metis empty_iff imageE image_eqI linorder_lit.is_maximal_in_mset_iff set_mset_empty set_mset_efac efac_spec)

lemma greatest_literal_in_efacI:
  assumes "is_pos L" and C_max_lit: "linorder_lit.is_maximal_in_mset C L"
  shows "linorder_lit.is_greatest_in_mset (efac C) L"
  unfolding efac_spec_if_pos_lit_is_maximal[OF assms] linorder_lit.is_greatest_in_mset_iff
proof (intro conjI ballI)
  show "L \<in># add_mset L {#K \<in># C. K \<noteq> L#}"
    by simp
next
  fix y :: "'f gterm literal"
  assume "y \<in># remove1_mset L (add_mset L {#K \<in># C. K \<noteq> L#})"
  then show "y \<prec>\<^sub>l L"
    using C_max_lit[unfolded linorder_lit.is_maximal_in_mset_iff]
    by  auto
qed

lemma factorizable_if_neq_efac:
  assumes "C \<noteq> efac C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
  using assms
  by (metis converse_rtranclpE ex1_efac_eq_factoring_chain)

lemma nex_strictly_maximal_pos_lit_if_neq_efac:
  assumes "C \<noteq> efac C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms factorizable_if_neq_efac nex_strictly_maximal_pos_lit_if_factorizable by metis

lemma efac_properties_if_not_ident:
  assumes "efac C \<noteq> C"
  shows "efac C \<prec>\<^sub>c C" and "{efac C} \<TTurnstile>e {C}"
proof -
  have "efac C \<subseteq># C"
    using efac_subset .
  hence "efac C \<preceq>\<^sub>c C"
    using subset_implies_reflclp_multp by blast
  thus "efac C \<prec>\<^sub>c C"
    using \<open>efac C \<noteq> C\<close> by order

  show "{efac C} \<TTurnstile>e {C}"
    using \<open>efac C \<subseteq># C\<close> true_clss_subclause by metis
qed


end

section \<open>Function for implicit full factorization\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition iefac where
  "iefac \<F> C = (if C |\<in>| \<F> then efac C else C)"

lemma iefac_mempty[simp]:
  fixes \<F> :: "'f gclause fset"
  shows "iefac \<F> {#} = {#}"
  by (metis efac_mempty iefac_def)

lemma fset_mset_iefac[simp]: 
  fixes \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "fset_mset (iefac \<F> C) = fset_mset C"
proof (cases "C |\<in>| \<F>")
  case True
  hence "iefac \<F> C = efac C"
    unfolding iefac_def by simp
  thus ?thesis
    by auto
next
  case False
  hence "iefac \<F> C = C"
    unfolding iefac_def by simp
  thus ?thesis by simp
qed

lemma atms_of_cls_iefac[simp]:
  fixes \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "atms_of_cls (iefac \<F> C) = atms_of_cls C"
  by (simp add: atms_of_cls_def)

lemma iefac_le:
  fixes \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "iefac \<F> C \<preceq>\<^sub>c C"
  by (metis efac_subset iefac_def reflclp_iff subset_implies_reflclp_multp)

lemma true_cls_iefac_iff[simp]:
  fixes \<I> :: "'f gterm set" and \<F> :: "'f gclause fset" and C :: "'f gclause"
  shows "\<I> \<TTurnstile> iefac \<F> C \<longleftrightarrow> \<I> \<TTurnstile> C"
  by (metis iefac_def true_cls_efac_iff)

(*
ifac |`| (N |\<union>| U\<^sub>e\<^sub>r) |\<subseteq>| (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = (ifac |`| (N |\<union>| U\<^sub>e\<^sub>r)) |\<union>| N |\<union>| U\<^sub>e\<^sub>r
*)
lemma funion_funion_eq_funion_funion_fimage_iefac_if:
  assumes U\<^sub>e\<^sub>f_eq: "U\<^sub>e\<^sub>f = iefac \<F> |`| {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|}"
  shows "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f = N |\<union>| U\<^sub>e\<^sub>r |\<union>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
proof (intro fsubset_antisym fsubsetI)
  fix C :: "'f gterm clause"
  assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  hence "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<or> C |\<in>| U\<^sub>e\<^sub>f"
    by simp
  thus "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
  proof (elim disjE)
    assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    thus ?thesis
      by simp
  next
    assume "C |\<in>| U\<^sub>e\<^sub>f"
    hence "C |\<in>| iefac \<F> |`| {|C |\<in>| N |\<union>| U\<^sub>e\<^sub>r. iefac \<F> C \<noteq> C|}"
      using U\<^sub>e\<^sub>f_eq by argo
    then obtain C\<^sub>0 :: "'f gterm clause" where
      "C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "iefac \<F> C\<^sub>0 \<noteq> C\<^sub>0" and "C = iefac \<F> C\<^sub>0"
      by auto
    thus ?thesis
      by simp
  qed
next
  fix C :: "'f gterm clause"
  assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
  hence "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r \<or> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    by simp
  thus "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (elim disjE)
    assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    thus ?thesis
      by simp
  next
    assume "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    then obtain C\<^sub>0 :: "'f gterm clause" where
      "C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r" and "C = iefac \<F> C\<^sub>0"
      by auto

    show ?thesis
    proof (cases "iefac \<F> C\<^sub>0 = C\<^sub>0")
      case True
      hence "C = C\<^sub>0"
        using \<open>C = iefac \<F> C\<^sub>0\<close> by argo
      thus ?thesis
        using \<open>C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> by simp
    next
      case False
      hence "C |\<in>| U\<^sub>e\<^sub>f"
        unfolding U\<^sub>e\<^sub>f_eq
        using \<open>C\<^sub>0 |\<in>| N |\<union>| U\<^sub>e\<^sub>r\<close> \<open>C = iefac \<F> C\<^sub>0\<close> by simp
      thus ?thesis
        by simp
    qed
  qed
qed


lemma clauses_for_iefac_are_unproductive:
  "\<forall>C |\<in>| N |-| iefac \<F> |`| N. \<forall>U. ord_res.production U C = {}"
proof (intro ballI allI)
  fix C U
  assume "C |\<in>| N |-| iefac \<F> |`| N"
  hence "C |\<in>| N" and "C |\<notin>| iefac \<F> |`| N"
    by simp_all
  hence "iefac \<F> C \<noteq> C"
    by (metis fimage_iff)
  hence "efac C \<noteq> C"
    by (metis iefac_def)
  hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
    using nex_strictly_maximal_pos_lit_if_neq_efac by metis
  thus "ord_res.production U C = {}"
    using unproductive_if_nex_strictly_maximal_pos_lit by metis
qed

lemma clauses_for_iefac_have_smaller_entailing_clause:
  "\<forall>C |\<in>| N |-| iefac \<F> |`| N. \<exists>D |\<in>| iefac \<F> |`| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
proof (intro ballI allI)
  fix C
  assume "C |\<in>| N |-| iefac \<F> |`| N"
  hence "C |\<in>| N" and "C |\<notin>| iefac \<F> |`| N"
    by simp_all
  hence "iefac \<F> C \<noteq> C"
    by (metis fimage_iff)
  hence "efac C \<noteq> C"
    by (metis iefac_def)

  show "\<exists>D |\<in>| iefac \<F> |`| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  proof (intro bexI conjI)
    show "efac C \<prec>\<^sub>c C" and "{efac C} \<TTurnstile>e {C}"
      using efac_properties_if_not_ident[OF \<open>efac C \<noteq> C\<close>] by simp_all
  next
    show "efac C |\<in>| iefac \<F> |`| N"
      using \<open>C |\<in>| N\<close> \<open>iefac \<F> C \<noteq> C\<close> by (metis fimageI iefac_def)
  qed
qed

lemma is_least_false_clause_with_iefac_conv:
  "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) =
    is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"
  using is_least_false_clause_funion_cancel_right_strong[OF clauses_for_iefac_are_unproductive
    clauses_for_iefac_have_smaller_entailing_clause]
  by (simp add: sup_commute)


end


section \<open>Function for full resolution\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition ground_resolution where
  "ground_resolution D C CD = ord_res.ground_resolution C D CD"

lemma Uniq_ground_resolution: "\<exists>\<^sub>\<le>\<^sub>1DC. ground_resolution D C DC"
  by (simp add: ground_resolution_def ord_res.unique_ground_resolution)

lemma ground_resolution_terminates: "wfP (ground_resolution D)\<inverse>\<inverse>"
proof (rule wfp_if_convertible_to_wfp)
  show "wfP (\<prec>\<^sub>c)"
    using ord_res.wfP_less_cls .
next
  show "\<And>x y. (ground_resolution D)\<inverse>\<inverse> x y \<Longrightarrow> x \<prec>\<^sub>c y"
  unfolding ground_resolution_def conversep_iff
  using ord_res.ground_resolution_smaller_conclusion by metis
qed

lemma not_ground_resolution_mempty_left: "\<not> ground_resolution {#} C x"
  by (auto simp: ground_resolution_def elim: ord_res.ground_resolution.cases)

lemma not_ground_resolution_mempty_right: "\<not> ground_resolution C {#} x"
  by (auto simp: ground_resolution_def elim: ord_res.ground_resolution.cases)

lemma not_tranclp_ground_resolution_mempty_left: "\<not> (ground_resolution {#})\<^sup>+\<^sup>+ C x"
  by (metis not_ground_resolution_mempty_left tranclpD)

lemma not_tranclp_ground_resolution_mempty_right: "\<not> (ground_resolution C)\<^sup>+\<^sup>+ {#} x"
  by (metis not_ground_resolution_mempty_right tranclpD)

lemma left_premise_lt_right_premise_if_ground_resolution:
  "ground_resolution D C DC \<Longrightarrow> D \<prec>\<^sub>c C"
  by (auto simp: ground_resolution_def elim: ord_res.ground_resolution.cases)

lemma left_premise_lt_right_premise_if_tranclp_ground_resolution:
  "(ground_resolution D)\<^sup>+\<^sup>+ C DC \<Longrightarrow> D \<prec>\<^sub>c C"
  by (induction DC rule: tranclp_induct)
    (auto simp add: left_premise_lt_right_premise_if_ground_resolution)

lemma resolvent_lt_right_premise_if_ground_resolution:
  "ground_resolution D C DC \<Longrightarrow> DC \<prec>\<^sub>c C"
  by (simp add: ground_resolution_def ord_res.ground_resolution_smaller_conclusion)

lemma resolvent_lt_right_premise_if_tranclp_ground_resolution:
  "(ground_resolution D)\<^sup>+\<^sup>+ C DC \<Longrightarrow> DC \<prec>\<^sub>c C"
proof (induction DC rule: tranclp_induct)
  case (base y)
  thus ?case
    by (simp add: resolvent_lt_right_premise_if_ground_resolution)
next
  case (step y z)
  have "z \<prec>\<^sub>c y"
    using step.hyps resolvent_lt_right_premise_if_ground_resolution by metis
  thus ?case
    using step.IH by order
qed


text \<open>Exhaustive resolution\<close>

definition eres where
  "eres D C = (THE DC. full_run (ground_resolution D) C DC)"

text \<open>The function \<^const>\<open>eres\<close> performs exhaustive resolution between its two input clauses. The
  first clause is repeatedly used, while the second clause is only use to start the resolution
  chain.\<close>

lemma eres_ident_iff: "eres D C = C \<longleftrightarrow> (\<nexists>DC. ground_resolution D C DC)"
proof (rule iffI)
  assume "eres D C = C"
  thus "\<nexists>DC. ground_resolution D C DC"
    unfolding eres_def
    by (metis Uniq_full_run Uniq_ground_resolution full_run_def ground_resolution_terminates
        ex1_full_run the1_equality')
next
  assume stuck: "\<nexists>DC. ground_resolution D C DC"
  have "(ground_resolution D)\<^sup>*\<^sup>* C C"
    by auto

  with stuck have "full_run (ground_resolution D) C C"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show "eres D C = C"
    unfolding eres_def by (metis the1_equality')
qed

lemma
  assumes
    step1: "ground_resolution D C DC" and
    stuck: "\<nexists>DDC. ground_resolution D DC DDC"
  shows "eres D C = DC"
proof -
  from step1 have "(ground_resolution D)\<^sup>*\<^sup>* C DC"
    by auto

  with stuck have "full_run (ground_resolution D) C DC"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
    unfolding eres_def by (metis the1_equality')
qed

lemma
  assumes
    step1: "ground_resolution D C DC" and
    step2: "ground_resolution D DC DDC" and
    stuck: "\<nexists>DDDC. ground_resolution D DDC DDDC"
  shows "eres D C = DDC"
proof -
  from step1 have "(ground_resolution D)\<^sup>*\<^sup>* C DC"
    by auto

  with step2 have "(ground_resolution D)\<^sup>*\<^sup>* C DDC"
    by (metis rtranclp.simps)

  with stuck have "full_run (ground_resolution D) C DDC"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
    unfolding eres_def by (metis the1_equality')
qed

lemma
  assumes
    step1: "ground_resolution D C DC" and
    step2: "ground_resolution D DC DDC" and
    step3: "ground_resolution D DDC DDDC" and
    stuck: "\<nexists>DDDDC. ground_resolution D DDDC DDDDC"
  shows "eres D C = DDDC"
proof -
  from step1 have "(ground_resolution D)\<^sup>*\<^sup>* C DC"
    by auto

  with step2 have "(ground_resolution D)\<^sup>*\<^sup>* C DDC"
    by (metis rtranclp.simps)

  with step3 have "(ground_resolution D)\<^sup>*\<^sup>* C DDDC"
    by (metis rtranclp.simps)

  with stuck have "full_run (ground_resolution D) C DDDC"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
    unfolding eres_def by (metis the1_equality')
qed

lemma eres_mempty_left[simp]: "eres {#} C = C"
  unfolding eres_def
  by (metis Uniq_full_run Uniq_ground_resolution full_run_def not_ground_resolution_mempty_left
      rtranclp.rtrancl_refl the1_equality')

lemma eres_mempty_right[simp]: "eres C {#} = {#}"
  unfolding eres_def
  by (metis Uniq_full_run Uniq_ground_resolution full_run_def not_ground_resolution_mempty_right
      rtranclp.rtrancl_refl the1_equality')

lemma ex1_eres_eq_full_run_ground_resolution: "\<exists>!DC. eres D C = DC \<and> full_run (ground_resolution D) C DC"
  using ex1_full_run[of "ground_resolution D" C]
  by (metis Uniq_ground_resolution eres_def ground_resolution_terminates theI')

lemma eres_le: "eres D C \<preceq>\<^sub>c C"
proof -
  have "full_run (ground_resolution D) C (eres D C)"
    using ex1_eres_eq_full_run_ground_resolution by metis
  thus ?thesis
  proof (rule full_run_preserves_invariant)
    show "C \<preceq>\<^sub>c C"
      by simp
  next
    show "\<And>x y. ground_resolution D x y \<Longrightarrow> x \<preceq>\<^sub>c C \<Longrightarrow> y \<preceq>\<^sub>c C"
      unfolding ground_resolution_def
      using ord_res.ground_resolution_smaller_conclusion by fastforce
  qed
qed

lemma clause_lt_clause_if_max_lit_comp:
  assumes E_max_lit: "linorder_lit.is_maximal_in_mset E L" and L_neg: "is_neg L" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D (- L)"
  shows "D \<prec>\<^sub>c E"
proof -
  have "- L \<prec>\<^sub>l L"
    using L_neg by (cases L) simp_all

  thus ?thesis
    using D_max_lit E_max_lit
    by (metis linorder_lit.multp_if_maximal_less_that_maximal)
qed

lemma eres_lt_if:
  assumes E_max_lit: "ord_res.is_maximal_lit L E" and L_neg: "is_neg L" and
    D_max_lit: "linorder_lit.is_greatest_in_mset D (- L)"
  shows "eres D E \<prec>\<^sub>c E"
proof -
  have "eres D E \<noteq> E"
    unfolding eres_ident_iff not_not ground_resolution_def
  proof (rule ex_ground_resolutionI)
    show "ord_res.is_maximal_lit (Neg (atm_of L)) E"
      using E_max_lit L_neg by (cases L) simp_all
  next
    show "D \<prec>\<^sub>c E"
      using E_max_lit D_max_lit L_neg
      by (metis clause_lt_clause_if_max_lit_comp
          linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
  next
    show "ord_res.is_strictly_maximal_lit (Pos (atm_of L)) D"
      using D_max_lit \<open>is_neg L\<close>
      by (cases L) simp_all
  qed

  thus "eres D E \<prec>\<^sub>c E"
    using eres_le[of D E] by order
qed

lemma eres_eq_after_ground_resolution:
  assumes "ground_resolution D C DC"
  shows "eres D C = eres D DC"
  using assms
  by (metis (no_types, opaque_lifting) Uniq_def Uniq_full_run Uniq_ground_resolution
      converse_rtranclpE ex1_eres_eq_full_run_ground_resolution full_run_def)

lemma eres_eq_after_rtranclp_ground_resolution:
  assumes "(ground_resolution D)\<^sup>*\<^sup>* C DC"
  shows "eres D C = eres D DC"
  using assms
  by (induction DC rule: rtranclp_induct) (simp_all add: eres_eq_after_ground_resolution)

lemma eres_eq_after_tranclp_ground_resolution:
  assumes "(ground_resolution D)\<^sup>+\<^sup>+ C DC"
  shows "eres D C = eres D DC"
  using assms
  by (induction DC rule: tranclp_induct) (simp_all add: eres_eq_after_ground_resolution)

lemma resolvable_if_neq_eres:
  assumes "C \<noteq> eres D C"
  shows "\<exists>!DC. ground_resolution D C DC"
  using assms ex1_eres_eq_full_run_ground_resolution
  by (metis (no_types, opaque_lifting) Uniq_def Uniq_full_run Uniq_ground_resolution full_run_def
      rtranclp.rtrancl_refl)

lemma nex_maximal_pos_lit_if_resolvable:
  assumes "ground_resolution D C DC"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
  using assms unfolding ground_resolution_def
  by (metis Uniq_D empty_iff is_pos_def linorder_lit.Uniq_is_maximal_in_mset
      literal.simps(4) ord_res.ground_resolution.cases set_mset_empty)

corollary nex_strictly_maximal_pos_lit_if_resolvable:
  assumes "ground_resolution D C DC"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms nex_maximal_pos_lit_if_resolvable by blast

corollary nex_maximal_pos_lit_if_neq_eres:
  assumes "C \<noteq> eres D C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
  using assms resolvable_if_neq_eres nex_maximal_pos_lit_if_resolvable by metis

corollary nex_strictly_maximal_pos_lit_if_neq_eres:
  assumes "C \<noteq> eres D C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms resolvable_if_neq_eres nex_strictly_maximal_pos_lit_if_resolvable by metis

lemma ground_resolutionD:
  assumes "ground_resolution D C DC"
  shows "\<exists>m A D' C'.
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DC = D' + replicate_mset m (Neg A) + C'"
  using assms
  unfolding ground_resolution_def
proof (cases C D DC rule: ord_res.ground_resolution.cases)
  case (ground_resolutionI A C' D')

  then obtain m where "count C (Neg A) = Suc m"
    by simp

  define C'' where
    "C'' = {#L \<in># C. L \<noteq> Neg A#}"

  have "C = replicate_mset (Suc m) (Neg A) + C''"
    using \<open>count C (Neg A) = Suc m\<close> C''_def
    by (metis filter_eq_replicate_mset union_filter_mset_complement)

  show ?thesis
  proof (intro exI conjI)
    show "linorder_lit.is_greatest_in_mset D (Pos A)"
      using \<open>linorder_lit.is_greatest_in_mset D (Pos A)\<close> .
  next
    show "linorder_lit.is_maximal_in_mset C (Neg A)"
      using ground_resolutionI by simp
  next
    show "D = add_mset (Pos A) D'"
      using \<open>D = add_mset (Pos A) D'\<close> .
  next
    show "C = replicate_mset (Suc m) (Neg A) + C''"
      using \<open>C = replicate_mset (Suc m) (Neg A) + C''\<close> .
  next
    show "Neg A \<notin># C''"
      by (simp add: C''_def)
  next
    show "DC = D' + replicate_mset m (Neg A) + C''"
      using \<open>DC = C' + D'\<close> \<open>C = add_mset (Neg A) C'\<close> \<open>C = replicate_mset (Suc m) (Neg A) + C''\<close>
      by simp
  qed
qed

lemma relpowp_ground_resolutionD:
  assumes "n \<noteq> 0" and "(ground_resolution D ^^ n) C DnC"
  shows "\<exists>m A D' C'. Suc m \<ge> n \<and>
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DnC = repeat_mset n D' + replicate_mset (Suc m - n) (Neg A) + C'"
  using assms
proof (induction n arbitrary: C)
  case 0
  hence False
    by simp
  thus ?case ..
next
  case (Suc n')
  then obtain DC where
    "ground_resolution D C DC" and "(ground_resolution D ^^ n') DC DnC"
    by (metis relpowp_Suc_E2)

  then obtain m A D' C' where
    "linorder_lit.is_greatest_in_mset D (Pos A)" and
    "linorder_lit.is_maximal_in_mset C (Neg A)"
    "D = add_mset (Pos A) D'" and
    "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "DC = D' + replicate_mset m (Neg A) + C'"
    using \<open>ground_resolution D C DC\<close>[THEN ground_resolutionD] by metis

  have "Neg A \<notin># D'"
    using \<open>linorder_lit.is_greatest_in_mset D (Pos A)\<close>
    unfolding \<open>D = add_mset (Pos A) D'\<close>
    unfolding linorder_lit.is_greatest_in_mset_iff
    by auto

  show ?case
  proof (cases n')
    case 0
    hence "DnC = DC"
      using \<open>(ground_resolution D ^^ n') DC DnC\<close> by simp

    show ?thesis
      unfolding 0 \<open>DnC = DC\<close>
      unfolding repeat_mset_Suc repeat_mset_0 empty_neutral
      unfolding diff_Suc_Suc minus_nat.diff_0
      using \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> \<open>D = add_mset (Pos A) D'\<close>
        \<open>DC = D' + replicate_mset m (Neg A) + C'\<close> \<open>Neg A \<notin># C'\<close>
        \<open>linorder_lit.is_greatest_in_mset D (Pos A)\<close> \<open>linorder_lit.is_maximal_in_mset C (Neg A)\<close>
      using linorder_lit.is_greatest_in_mset_iff
      by blast
  next
    case (Suc n'')
    hence "n' \<noteq> 0"
      by presburger
    then obtain m' A' D'' DC' where "n' \<le> Suc m'" and
       "ord_res.is_strictly_maximal_lit (Pos A') D" and
       "ord_res.is_maximal_lit (Neg A') DC" and
       "D = add_mset (Pos A') D''" and
       "DC = replicate_mset (Suc m') (Neg A') + DC'" and
       "Neg A' \<notin># DC'" and
       "DnC = repeat_mset n' D'' + replicate_mset (Suc m' - n') (Neg A') + DC'"
      using Suc.IH[OF _ \<open>(ground_resolution D ^^ n') DC DnC\<close>]
      by metis

    have "A' = A"
      using \<open>ord_res.is_strictly_maximal_lit (Pos A') D\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
      by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset
          linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.inject(1))

    hence "D'' = D'"
      using \<open>D = add_mset (Pos A') D''\<close> \<open>D = add_mset (Pos A) D'\<close> by auto

    have "m = Suc m'"
      using \<open>DC = D' + replicate_mset m (Neg A) + C'\<close> \<open>DC = replicate_mset (Suc m') (Neg A') + DC'\<close>
        \<open>Neg A \<notin># D'\<close> \<open>Neg A \<notin># C'\<close> \<open>Neg A' \<notin># DC'\<close>
      unfolding \<open>A' = A\<close>
      by (metis add_0 count_eq_zero_iff count_replicate_mset count_union union_commute)

    hence "DC' = D' + C'"
      using \<open>DC = D' + replicate_mset m (Neg A) + C'\<close> \<open>DC = replicate_mset (Suc m') (Neg A') + DC'\<close>
      by (simp add: \<open>A' = A\<close>)

    show ?thesis
    proof (intro exI conjI)
      show "Suc n' \<le> Suc (Suc m')"
        using \<open>n' \<le> Suc m'\<close> by presburger
    next
      show "ord_res.is_strictly_maximal_lit (Pos A) D"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> .
    next
      show "ord_res.is_maximal_lit (Neg A) C"
        using \<open>ord_res.is_maximal_lit (Neg A) C\<close> by metis
    next
      show "D = add_mset (Pos A) D'"
        using \<open>D = add_mset (Pos A) D'\<close> .
    next
      show "C = replicate_mset (Suc (Suc m')) (Neg A) + C'"
        using \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> \<open>m = Suc m'\<close> by argo
    next
      show "Neg A \<notin># C'"
        using \<open>Neg A \<notin># C'\<close> .
    next
      show "DnC = repeat_mset (Suc n') D' + replicate_mset (Suc (Suc m') - Suc n') (Neg A) + C'"
        using \<open>DnC = repeat_mset n' D'' + replicate_mset (Suc m' - n') (Neg A') + DC'\<close>
        unfolding \<open>A' = A\<close> \<open>D'' = D'\<close> diff_Suc_Suc \<open>DC' = D' + C'\<close>
        by simp
    qed
  qed
qed


lemma tranclp_ground_resolutionD:
  assumes "(ground_resolution D)\<^sup>+\<^sup>+ C DnC"
  shows "\<exists>n m A D' C'. Suc m \<ge> Suc n \<and>
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DnC = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'"
proof -
  from assms obtain n :: nat where
    "(ground_resolution D ^^ Suc n) C DnC"
    by (metis Suc_pred tranclp_power)
  thus ?thesis
    using assms relpowp_ground_resolutionD
    by (meson nat.discI)
qed

lemma eres_not_identD:
  assumes "eres D C \<noteq> C"
  shows "\<exists>m A D' C'.
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    eres D C = repeat_mset (Suc m) D' + C'"
proof -
  have "\<And>n. Suc n \<noteq> 0"
    by presburger

  obtain n where
    steps: "(ground_resolution D ^^ Suc n) C (eres D C)" and
    stuck: "\<nexists>x. ground_resolution D (eres D C) x"
    using \<open>eres D C \<noteq> C\<close> ex1_eres_eq_full_run_ground_resolution
    by (metis full_run_def gr0_conv_Suc rtranclpD tranclp_power)

  obtain m A D' C' where
    "Suc n \<le> Suc m" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D" and
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_eq: "D = add_mset (Pos A) D'" and
    C_eq: "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    eres_eq: "eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'"
    using relpowp_ground_resolutionD[of "Suc n", OF \<open>Suc n \<noteq> 0\<close> steps] by metis

  from stuck have "count (eres D C) (Neg A) = 0"
  proof (rule contrapos_np)
    assume "count (eres D C) (Neg A) \<noteq> 0"
    then obtain ERES' where "eres D C = add_mset (Neg A) ERES'"
      by (meson count_eq_zero_iff mset_add)

    moreover have "ord_res.is_maximal_lit (Neg A) (eres D C)"
      unfolding linorder_lit.is_maximal_in_mset_iff
    proof (intro conjI ballI impI)
      show "Neg A \<in># eres D C"
        unfolding \<open>eres D C = add_mset (Neg A) ERES'\<close> by simp
    next
      fix L
      assume "L \<in># eres D C" and "L \<noteq> Neg A"
      hence "L \<in># repeat_mset (Suc n) D' \<or> L \<in># C'"
        unfolding eres_eq
        by (metis Zero_not_Suc count_replicate_mset in_countE union_iff)
      thus "\<not> Neg A \<prec>\<^sub>l L"
      proof (elim disjE)
        assume "L \<in># repeat_mset (Suc n) D'"
        hence "L \<in># D'"
          using member_mset_repeat_msetD by metis
        hence "L \<prec>\<^sub>l Pos A"
          using D_max_lit
          unfolding D_eq linorder_lit.is_greatest_in_mset_iff by simp
        also have "Pos A \<prec>\<^sub>l Neg A"
          by simp
        finally show ?thesis
          by order
      next
        assume "L \<in># C'"
        thus ?thesis
          using C_eq \<open>L \<noteq> Neg A\<close> C_max_lit linorder_lit.is_maximal_in_mset_iff by auto
      qed
    qed

    moreover have "D \<prec>\<^sub>c eres D C"
      using D_max_lit
      using \<open>ord_res.is_maximal_lit (Neg A) (eres D C)\<close>
      using linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal[of D "Pos A" "eres D C" "Neg A", simplified]
      using multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M by blast

    ultimately show "\<exists>x. ground_resolution D (eres D C) x"
      unfolding ground_resolution_def
      using D_eq D_max_lit
      using ord_res.ground_resolutionI[of "eres D C" A ERES' D D' "ERES' + D'"]
      by metis
  qed

  hence "m = n"
    using \<open>eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'\<close>
    using \<open>Suc n \<le> Suc m\<close> by auto

  show ?thesis
  proof (intro exI conjI)
    show "ord_res.is_strictly_maximal_lit (Pos A) D"
      using D_max_lit .
  next
    show "ord_res.is_maximal_lit (Neg A) C"
      using C_max_lit .
  next
    show "D = add_mset (Pos A) D'"
      using D_eq .
  next
    show "C = replicate_mset (Suc m) (Neg A) + C'"
      using C_eq .
  next
    show "Neg A \<notin># C'"
      using \<open>Neg A \<notin># C'\<close> .
  next
    show "eres D C = repeat_mset (Suc m) D' + C'"
      using eres_eq unfolding \<open>m = n\<close> by simp
  qed
qed

lemma lit_in_one_of_resolvents_if_in_eres:
  fixes L :: "'f gterm literal" and C D :: "'f gclause"
  assumes "L \<in># eres C D"
  shows "L \<in># C \<or> L \<in># D"
proof (cases "eres C D = D")
  assume "eres C D = D"
  thus "L \<in># C \<or> L \<in># D"
    using \<open>L \<in># eres C D\<close> by argo
next
  assume "eres C D \<noteq> D"
  thus "L \<in># C \<or> L \<in># D"
    using \<open>L \<in># eres C D\<close>
    by (metis eres_not_identD member_mset_repeat_msetD repeat_mset_distrib_add_mset union_iff)
qed

lemma strong_lit_in_one_of_resolvents_if_in_eres:
  fixes L :: "'f gterm literal" and C D :: "'f gclause"
  assumes
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    K_in: "K \<in># eres C D"
  shows "K \<in># C \<and> K \<noteq> -L \<or> K \<in># D"
proof (cases "eres C D = D")
  assume "eres C D = D"
  thus "K \<in># C \<and> K \<noteq> -L \<or> K \<in># D"
    using K_in by argo
next
  assume "eres C D \<noteq> D"
  then obtain m :: nat and A :: "'f gterm" and C' D' :: "'f gterm literal multiset" where
    C_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) C" and
    D_max_lit': "ord_res.is_maximal_lit (Neg A) D" and
    C_eq: "C = add_mset (Pos A) C'" and
    D_eq: "D = replicate_mset (Suc m) (Neg A) + D'" and
    "Neg A \<notin># D'" and
    "eres C D = repeat_mset (Suc m) C' + D'"
    using eres_not_identD by metis

  have L_eq: "L = Neg A"
    using D_max_lit D_max_lit' by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

  have "K \<in># repeat_mset (Suc m) C' + D'"
    using K_in unfolding \<open>eres C D = repeat_mset (Suc m) C' + D'\<close> .

  hence "K \<in># repeat_mset (Suc m) C' \<or> K \<in># D'"
    unfolding Multiset.union_iff .

  hence "K \<in># C' \<or> K \<in># D'"
    unfolding member_mset_repeat_mset_Suc .

  thus "K \<in># C \<and> K \<noteq> -L \<or> K \<in># D"
  proof (elim disjE)
    assume "K \<in># C'"

    hence "K \<in># C \<and> K \<noteq> - L"
      using C_max_lit
      unfolding C_eq L_eq linorder_lit.is_greatest_in_mset_iff by auto

    thus "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D" ..
  next
    assume "K \<in># D'"

    hence "K \<in># D"
      unfolding D_eq by simp

    thus "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D" ..
  qed
qed

lemma stronger_lit_in_one_of_resolvents_if_in_eres:
  fixes K L :: "'f gterm literal" and C D :: "'f gclause"
  assumes "eres C D \<noteq> D" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    K_in_eres: "K \<in># eres C D"
  shows "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D \<and> K \<noteq> L "
proof -
  obtain m :: nat and A :: "'f gterm" and C' D' :: "'f gterm literal multiset" where
    C_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) C" and
    C_def: "C = add_mset (Pos A) C'" and
    "D = replicate_mset (Suc m) (Neg A) + D'" and
    "Neg A \<notin># D'" and
    "eres C D = repeat_mset (Suc m) C' + D'"
    using \<open>eres C D \<noteq> D\<close>[THEN eres_not_identD] by metis

  have "L = Neg A"
    using assms(1) D_max_lit C_max_lit
    by (metis ground_resolutionD linorder_lit.Uniq_is_greatest_in_mset
        linorder_lit.Uniq_is_maximal_in_mset resolvable_if_neq_eres the1_equality' uminus_Pos)

  have "K \<in># repeat_mset (Suc m) C' + D'"
    using K_in_eres unfolding \<open>eres C D = repeat_mset (Suc m) C' + D'\<close> .

  hence "K \<in># repeat_mset (Suc m) C' \<or> K \<in># D'"
    unfolding Multiset.union_iff .

  hence "K \<in># C' \<or> K \<in># D'"
    unfolding member_mset_repeat_mset_Suc .

  thus "K \<in># C \<and> K \<noteq> - L \<or> K \<in># D \<and> K \<noteq> L "
  proof (elim disjE)
    assume "K \<in># C'"

    hence "K \<in># C \<and> K \<noteq> - L"
      using C_max_lit[unfolded linorder_lit.is_greatest_in_mset_iff]
      unfolding \<open>C = add_mset (Pos A) C'\<close> \<open>L = Neg A\<close>
      by auto

    thus ?thesis
      by argo
  next
    assume "K \<in># D'"

    hence "K \<in># D \<and> K \<noteq> L "
      unfolding \<open>D = replicate_mset (Suc m) (Neg A) +  D'\<close> \<open>L = Neg A\<close>
      using \<open>Neg A \<notin># D'\<close>
      by auto

    thus ?thesis
      by argo
  qed
qed

lemma lit_in_eres_lt_greatest_lit_in_grestest_resolvant:
  fixes K L :: "'f gterm literal" and C D :: "'f gclause"
  assumes "eres C D \<noteq> D" and
    D_max_lit: "linorder_lit.is_maximal_in_mset D L" and
    "- L \<notin># D" and
    K_in_eres: "K \<in># eres C D"
  shows "atm_of K \<prec>\<^sub>t atm_of L"
proof -
  obtain m :: nat and A :: "'f gterm" and C' D' :: "'f gterm literal multiset" where
    C_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) C" and
    C_def: "C = add_mset (Pos A) C'" and
    "D = replicate_mset (Suc m) (Neg A) + D'" and
    "Neg A \<notin># D'" and
    "eres C D = repeat_mset (Suc m) C' + D'"
    using \<open>eres C D \<noteq> D\<close>[THEN eres_not_identD] by metis

  have "L = Neg A"
    using assms(1) D_max_lit C_max_lit
    by (metis ground_resolutionD linorder_lit.Uniq_is_greatest_in_mset
        linorder_lit.Uniq_is_maximal_in_mset resolvable_if_neq_eres the1_equality' uminus_Pos)

  have "K \<in># repeat_mset (Suc m) C' + D'"
    using K_in_eres unfolding \<open>eres C D = repeat_mset (Suc m) C' + D'\<close> .

  hence "K \<in># repeat_mset (Suc m) C' \<or> K \<in># D'"
    unfolding Multiset.union_iff .

  hence "K \<in># C' \<or> K \<in># D'"
    unfolding member_mset_repeat_mset_Suc .

  thus "atm_of K \<prec>\<^sub>t atm_of L"
  proof (elim disjE)
    assume "K \<in># C'"
    hence "K \<prec>\<^sub>l Pos A"
      using C_max_lit C_def \<open>L = Neg A\<close>
      unfolding linorder_lit.is_greatest_in_mset_iff
      by simp
    thus "atm_of K \<prec>\<^sub>t atm_of L"
      unfolding \<open>L = Neg A\<close> literal.sel
      by (cases K) simp_all
  next
    assume "K \<in># D'"
    hence "K \<prec>\<^sub>l Neg A"
      by (metis D_max_lit \<open>D = replicate_mset (Suc m) (Neg A) + D'\<close> \<open>L = Neg A\<close> \<open>Neg A \<notin># D'\<close>
          linorder_lit.is_maximal_in_mset_iff linorder_lit.neqE union_iff)

    moreover have "K \<noteq> Pos A"
      using \<open>- L \<notin># D\<close>
      using \<open>D = replicate_mset (Suc m) (Neg A) + D'\<close> \<open>K \<in># D'\<close> \<open>L = Neg A\<close> by fastforce

    ultimately have "K \<prec>\<^sub>l Pos A"
      by (metis linorder_lit.less_asym linorder_lit.less_linear literal.exhaust
          ord_res.less_lit_simps(1) ord_res.less_lit_simps(3) ord_res.less_lit_simps(4))

    thus "atm_of K \<prec>\<^sub>t atm_of L"
      unfolding \<open>L = Neg A\<close> literal.sel
      by (cases K) simp_all
  qed
qed

lemma eres_entails_resolvent:
  fixes C D :: "'f gterm clause"
  assumes "(ground_resolution C)\<^sup>+\<^sup>+ D\<^sub>0 D"
  shows "{eres C D\<^sub>0} \<TTurnstile>e {D}"
  unfolding true_clss_singleton
proof (intro allI impI)
  have "eres C D\<^sub>0 = eres C D"
    using assms eres_eq_after_tranclp_ground_resolution by metis

  obtain n m :: nat and A :: "'f gterm" and C' D\<^sub>0' :: "'f gterm clause" where
    "Suc n \<le> Suc m" and
    "ord_res.is_strictly_maximal_lit (Pos A) C" and
    "ord_res.is_maximal_lit (Neg A) D\<^sub>0" and
    "C = add_mset (Pos A) C'" and
    "D\<^sub>0 = replicate_mset (Suc m) (Neg A) + D\<^sub>0'" and
    "Neg A \<notin># D\<^sub>0'" and
    "D = repeat_mset (Suc n) C' + replicate_mset (Suc m - Suc n) (Neg A) + D\<^sub>0'"
    using \<open>(ground_resolution C)\<^sup>+\<^sup>+ D\<^sub>0 D\<close>[THEN tranclp_ground_resolutionD] by metis

  fix I :: "'f gterm set"
  assume "I \<TTurnstile> eres C D\<^sub>0"
  show "I \<TTurnstile> D"
  proof (cases "eres C D\<^sub>0 = D")
    case True
    thus ?thesis
      using \<open>I \<TTurnstile> eres C D\<^sub>0\<close> by argo
  next
    case False
    then obtain k :: nat and D' :: "'f gterm clause" where
      "ord_res.is_strictly_maximal_lit (Pos A) C" and
      "C = add_mset (Pos A) C'" and
      "D = replicate_mset (Suc k) (Neg A) + D'" and
      "Neg A \<notin># D'" and
      "eres C D = repeat_mset (Suc k) C' + D'"
      unfolding \<open>eres C D\<^sub>0 = eres C D\<close>
      using eres_not_identD
      using \<open>ord_res.is_strictly_maximal_lit (Pos A) C\<close> \<open>C = add_mset (Pos A) C'\<close>
      by (metis Uniq_D add_mset_remove_trivial linorder_lit.Uniq_is_greatest_in_mset literal.sel(1))

    have "I \<TTurnstile> repeat_mset (Suc k) C' + D'"
      using \<open>I \<TTurnstile> eres C D\<^sub>0\<close>
      unfolding \<open>eres C D\<^sub>0 = eres C D\<close> \<open>eres C D = repeat_mset (Suc k) C' + D'\<close> .

    hence "I \<TTurnstile> D' \<or> I \<TTurnstile> repeat_mset (Suc k) C'"
      by auto

    thus "I \<TTurnstile> D"
    proof (elim disjE)
      assume "I \<TTurnstile> D'"
      thus "I \<TTurnstile> D"
        unfolding \<open>D = replicate_mset (Suc k) (Neg A) + D'\<close>
        by simp
    next
      assume "I \<TTurnstile> repeat_mset (Suc k) C'"
      thus "I \<TTurnstile> D"
        using \<open>D = replicate_mset (Suc k) (Neg A) + D'\<close>
        using \<open>D = repeat_mset (Suc n) C' + replicate_mset (Suc m - Suc n) (Neg A) + D\<^sub>0'\<close>
        by (metis member_mset_repeat_msetD repeat_mset_Suc true_cls_def true_cls_union)
    qed
  qed
qed



lemma clause_true_if_resolved_true:
  assumes
    "(ground_resolution D)\<^sup>+\<^sup>+ C DC" and
    D_productive: "ord_res.production N D \<noteq> {}" and
    C_true: "ord_res_Interp N DC \<TTurnstile> DC"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof -
  obtain n where
    steps: "(ground_resolution D ^^ Suc n) C DC"
    using \<open>(ground_resolution D)\<^sup>+\<^sup>+ C DC\<close>
    by (metis less_not_refl not0_implies_Suc tranclp_power)

  obtain m A D' C' where
    "n \<le> m" and
    "ord_res.is_strictly_maximal_lit (Pos A) D" and
    "ord_res.is_maximal_lit (Neg A) C" and
    "D = add_mset (Pos A) D'" and
    "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'"
    using relpowp_ground_resolutionD[OF Suc_not_Zero steps]
    by (metis diff_Suc_Suc Suc_le_mono)

  have "Neg A \<notin># D'"
    by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
        ord_res.less_lit_simps(4) linorder_lit.is_greatest_in_mset_iff linorder_trm.eq_refl
        linorder_trm.leD remove1_mset_add_mset_If)

  have "DC \<prec>\<^sub>c C"
  proof (cases "m = n")
    case True
    show ?thesis
    proof (intro one_step_implies_multp[of _ _ _ "{#}", simplified] ballI)
      show "C \<noteq> {#}"
        by (simp add: \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>)
    next
      fix L
      assume "L \<in># DC"
      hence "L \<in># D' \<or> L \<in># C'"
        unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close> \<open>m = n\<close>
        using member_mset_repeat_msetD by fastforce
      hence "L \<prec>\<^sub>l Neg A"
        using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> \<open>ord_res.is_maximal_lit (Neg A) C\<close>
        unfolding \<open>D = add_mset (Pos A) D'\<close> \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>
        unfolding linorder_lit.is_maximal_in_mset_iff linorder_lit.is_greatest_in_mset_iff
        by (metis \<open>Neg A \<notin># C'\<close> add_mset_remove_trivial ord_res.less_lit_simps(4)
            linorder_lit.antisym_conv3 linorder_lit.dual_order.strict_trans
            linorder_trm.dual_order.asym union_iff)

      moreover have "Neg A \<in># C"
        by (simp add: \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>)

      ultimately show "\<exists>K \<in># C. L \<prec>\<^sub>l K"
        by metis
    qed
  next
    case False
    hence "n < m"
      using \<open>n \<le> m\<close> by presburger

    have "multp\<^sub>H\<^sub>O (\<prec>\<^sub>l) DC C"
    proof (rule linorder_lit.multp\<^sub>H\<^sub>O_if_same_maximal_and_count_lt)
      show "ord_res.is_maximal_lit (Neg A) DC"
        unfolding linorder_lit.is_maximal_in_mset_iff
      proof (intro conjI ballI impI)
        show "Neg A \<in># DC"
          unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
          using \<open>n < m\<close> by simp
      next
        fix L
        assume "L \<in># DC" and "L \<noteq> Neg A"
        hence "L \<in># D' \<or> L \<in># C'"
          unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
          by (metis in_replicate_mset member_mset_repeat_msetD union_iff)
        thus "\<not> Neg A \<prec>\<^sub>l L"
          using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> \<open>ord_res.is_maximal_lit (Neg A) C\<close>
          unfolding \<open>D = add_mset (Pos A) D'\<close> \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close>
          unfolding linorder_lit.is_maximal_in_mset_iff linorder_lit.is_greatest_in_mset_iff
          by (metis \<open>L \<noteq> Neg A\<close> add_mset_diff_bothsides diff_zero
              linorder_lit.dual_order.strict_trans linorder_trm.less_irrefl
              ord_res.less_lit_simps(4) union_iff)
      qed
    next
      show "ord_res.is_maximal_lit (Neg A) C"
        using \<open>ord_res.is_maximal_lit (Neg A) C\<close> .
    next
      have "count DC (Neg A) = count (repeat_mset (Suc n) D') (Neg A) +
      count (replicate_mset (m - n) (Neg A)) (Neg A) + count C' (Neg A)"
        unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close> by simp
      also have "\<dots> = count D' (Neg A) * Suc n + count {#Neg A#} (Neg A) * (m - n) + count C' (Neg A)"
        by simp
      also have "\<dots> = 0 * Suc n + 1 * (m - n) + 0"
        by (simp add: \<open>Neg A \<notin># C'\<close> \<open>Neg A \<notin># D'\<close> count_eq_zero_iff)
      also have "\<dots> = m - n"
        by presburger
      also have "\<dots> < Suc m"
        by presburger
      also have "\<dots> = 1 * Suc m + 0"
        by presburger
      also have "\<dots> = count {#Neg A#} (Neg A) * Suc m + count C' (Neg A)"
        by (simp add: \<open>Neg A \<notin># C'\<close> count_eq_zero_iff)
      also have "\<dots> = count (replicate_mset (Suc m) (Neg A)) (Neg A) + count C' (Neg A)"
        by simp
      also have "\<dots> = count C (Neg A)"
        unfolding \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> by simp
      finally show "count DC (Neg A) < count C (Neg A)" .
    qed
    thus ?thesis
      by (simp add: multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M)
  qed

  with C_true have "ord_res_Interp N C \<TTurnstile> DC"
    using ord_res.entailed_clause_stays_entailed by metis

  thus "ord_res_Interp N C \<TTurnstile> C"
    unfolding true_cls_def
  proof (elim bexE)
    fix L
    assume
      L_in: "L \<in># DC" and
      L_true: "ord_res_Interp N C \<TTurnstile>l L"

    from L_in have "L \<in># D' \<or> L = Neg A \<or> L \<in># C'"
      unfolding \<open>DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
      by (metis in_replicate_mset member_mset_repeat_msetD union_iff)

    moreover have "L \<notin># D'"
    proof (rule notI)
      assume "L \<in># D'"

      moreover have "\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile> add_mset (Pos A) D'"
        using D_productive[unfolded \<open>D = add_mset (Pos A) D'\<close>]
        unfolding ord_res.production_unfold
        by fast

      ultimately have "\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile>l L"
        by auto

      have "L \<prec>\<^sub>l Pos A"
        using \<open>D = add_mset (Pos A) D'\<close> \<open>L \<in># D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
          linorder_lit.is_greatest_in_mset_iff by fastforce

      have "\<not> ord_res_Interp N C \<TTurnstile>l L"
      proof (cases L)
        case (Pos B)
        hence "B \<notin> ord_res.interp N (add_mset (Pos A) D')"
          using \<open>\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile>l L\<close> by simp

        moreover have "add_mset (Pos A) D' \<prec>\<^sub>c C"
          by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>\<And>thesis. (\<And>m A D' C'. \<lbrakk>n \<le> m; ord_res.is_strictly_maximal_lit (Pos A) D; ord_res.is_maximal_lit (Neg A) C; D = add_mset (Pos A) D'; C = replicate_mset (Suc m) (Neg A) + C'; Neg A \<notin># C'; DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M ord_res.less_lit_simps(2) reflclp_iff)

        ultimately have "B \<notin> ord_res.interp N C"
          using \<open>L \<prec>\<^sub>l Pos A\<close>[unfolded Pos, simplified]
          using ord_res.interp_fixed_for_smaller_literals
          by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.sel(1))

        moreover have "B \<notin> ord_res.production N C"
          by (metis Uniq_D \<open>ord_res.is_maximal_lit (Neg A) C\<close> ground_ordered_resolution_calculus.mem_productionE linorder_lit.Uniq_is_maximal_in_mset linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset literal.simps(4) ord_res.ground_ordered_resolution_calculus_axioms)

        ultimately show ?thesis
          unfolding Pos by simp
      next
        case (Neg B)
        hence "B \<in> ord_res.interp N (add_mset (Pos A) D')"
          using \<open>\<not> ord_res.interp N (add_mset (Pos A) D') \<TTurnstile>l L\<close> by simp

        moreover have "add_mset (Pos A) D' \<prec>\<^sub>c C"
          by (metis \<open>D = add_mset (Pos A) D'\<close> \<open>\<And>thesis. (\<And>m A D' C'. \<lbrakk>n \<le> m; ord_res.is_strictly_maximal_lit (Pos A) D; ord_res.is_maximal_lit (Neg A) C; D = add_mset (Pos A) D'; C = replicate_mset (Suc m) (Neg A) + C'; Neg A \<notin># C'; DC = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M ord_res.less_lit_simps(2) reflclp_iff)

        ultimately have "B \<in> ord_res.interp N C"
          by (metis Un_iff ord_res.not_interp_to_Interp_imp_le linorder_cls.leD)

        then show ?thesis
          unfolding Neg
          by simp
      qed

      with L_true show False
        by contradiction
    qed

    ultimately have "L \<in># C"
      unfolding \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> by simp

    with L_true show "\<exists>L \<in># C. ord_res_Interp N C \<TTurnstile>l L"
      by metis
  qed
qed

lemma clause_true_if_eres_true:
  assumes
    "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
    "C \<noteq> eres D1 C" and
    eres_C_true: "ord_res_Interp N (eres D1 C) \<TTurnstile> eres D1 C"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof -
  obtain n where
    steps: "(ground_resolution D1 ^^ Suc n) D2 C"
    using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close>
    by (metis less_not_refl not0_implies_Suc tranclp_power)

  obtain m A D' C' where
    "n \<le> m" and
    "ord_res.is_strictly_maximal_lit (Pos A) D1" and
    "ord_res.is_maximal_lit (Neg A) D2" and
    "D1 = add_mset (Pos A) D'" and
    "D2 = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'"
    using relpowp_ground_resolutionD[OF Suc_not_Zero steps]
    by (metis diff_Suc_Suc Suc_le_mono)

  have "Neg A \<notin># D'"
    by (metis \<open>D1 = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D1\<close>
        ord_res.less_lit_simps(4) linorder_lit.is_greatest_in_mset_iff linorder_trm.eq_refl
        linorder_trm.leD remove1_mset_add_mset_If)

  obtain m' C'' where
    "C = replicate_mset (Suc m') (Neg A) + C''" and
    "Neg A \<notin># C''" and
    "eres D1 C = repeat_mset (Suc m') D' + C''"
    using \<open>C \<noteq> eres D1 C\<close> eres_not_identD
    using \<open>ord_res.is_strictly_maximal_lit (Pos A) D1\<close> linorder_lit.Uniq_is_greatest_in_mset
    using \<open>D1 = add_mset (Pos A) D'\<close>
    by (metis Uniq_D add_mset_remove_trivial literal.inject(1))

  have "m - n = Suc m'"
  proof -
    have "count C (Neg A) = count (repeat_mset (Suc n) D') (Neg A) +
              count (replicate_mset (m - n) (Neg A)) (Neg A) + count C' (Neg A)"
      using \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close> by simp
    also have "\<dots> = count D' (Neg A) * Suc n + count {#Neg A#} (Neg A) * (m - n) +
              count C' (Neg A)"
      by simp
    also have "\<dots> = 0 * Suc n + 1 * (m - n) + 0"
      using \<open>Neg A \<notin># D'\<close> \<open>Neg A \<notin># C'\<close> by (simp add: count_eq_zero_iff)
    also have "\<dots> = m - n"
      by presburger
    finally have "count C (Neg A) = m - n" .

    have "count C (Neg A) = count (replicate_mset (Suc m') (Neg A)) (Neg A) +
              count C'' (Neg A)"
      using \<open>C = replicate_mset (Suc m') (Neg A) + C''\<close> by simp
    also have "\<dots> = count {#Neg A#} (Neg A) * Suc m' + count C'' (Neg A)"
      by simp
    also have "\<dots> = 1 * Suc m' + 0"
      using \<open>Neg A \<notin># C''\<close> by (simp add: count_eq_zero_iff)
    also have "\<dots> = Suc m'"
      by presburger
    finally have "count C (Neg A) = Suc m'" .

    show ?thesis
      using \<open>count C (Neg A) = m - n\<close> \<open>count C (Neg A) = Suc m'\<close> by argo
  qed

  hence "C'' = repeat_mset (Suc n) D' + C'"
    using \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>
      \<open>C = replicate_mset (Suc m') (Neg A) + C''\<close>
    by simp

  hence eres_D1_C_eq: "eres D1 C = repeat_mset (Suc m' + Suc n) D' + C'"
    using \<open>eres D1 C = repeat_mset (Suc m') D' + C''\<close> by simp

  have "ord_res_Interp N (eres D1 C) \<TTurnstile> eres D1 C"
    using eres_C_true .

  moreover have "eres D1 C \<prec>\<^sub>c C"
    using eres_le[of D1 C] \<open>C \<noteq> eres D1 C\<close> by order

  ultimately have "ord_res_Interp N C \<TTurnstile> eres D1 C"
    using ord_res.entailed_clause_stays_entailed by metis

  thus "ord_res_Interp N C \<TTurnstile> C"
    unfolding true_cls_def
  proof (elim bexE)
    fix L
    assume
      L_in: "L \<in># eres D1 C" and
      L_true: "ord_res_Interp N C \<TTurnstile>l L"

    from L_in have "L \<in># D' \<or> L \<in># C'"
      unfolding eres_D1_C_eq
      using member_mset_repeat_msetD by fastforce
    hence "L \<in># C"
      by (auto simp: \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>)
    with L_true show "\<exists>L \<in># C. ord_res_Interp N C \<TTurnstile>l L"
      by metis
  qed
qed

end


section \<open>Lemmas about going between ground and first-order terms\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

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

end


section \<open>SCL(FOL) for first-order terms\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition less_B where
  "less_B x y \<longleftrightarrow> ground x \<and> ground y \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term y"

sublocale order_less_B: order "less_B\<^sup>=\<^sup>=" less_B
  by unfold_locales (auto simp add: less_B_def)

sublocale scl_fol: scl_fol_calculus renaming_vars less_B
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

end

end