theory Background
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Correct_Termination
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Superposition_Calculus.Ground_Ordered_Resolution
    Superposition_Calculus.Min_Max_Least_Greatest_FSet
    Superposition_Calculus.Multiset_Extra
    VeriComp.Compiler
    "HOL-ex.Sketch_and_Explore"
    "HOL-Library.FuncSet"

    Lower_Set
begin

no_notation restrict_map (infixl "|`"  110)


section \<open>Move to HOL\<close>

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

lemma restrict_map_ident_if_dom_subset: "dom \<M> \<subseteq> A \<Longrightarrow> restrict_map \<M> A = \<M>"
  by (metis domIff ext in_mono restrict_map_def)


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

end