theory Simulation
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Superposition_Calculus.Ground_Ordered_Resolution
    Superposition_Calculus.Min_Max_Least_Greatest_FSet
    VeriComp.Compiler
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

lemma Uniq_relpowp:
  fixes n :: nat and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes uniq: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y"
  shows "(R ^^ n) x y \<Longrightarrow> (R ^^ n) x z \<Longrightarrow> y = z"
proof (induction n arbitrary: x y z)
  case 0
  thus ?case
    by simp
next
  case (Suc n')
  then obtain x' where "(R ^^ n') x x'" and "R x' y" and "R x' z"
    by auto
  thus "y = z"
    using uniq[THEN Uniq_D] by simp
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

lemma relpowp_Suc_of_right_unique:
  assumes
    "right_unique R"
    "R x y" and
    "(R ^^ Suc n) x z"
  shows "(R ^^ n) y z"
  using assms
  by (metis relpowp_Suc_D2 right_uniqueD)


section \<open>Move to \<^theory>\<open>HOL-Library.Multiset\<close>\<close>

lemmas strict_subset_implies_multp = subset_implies_multp
hide_fact subset_implies_multp

lemma subset_implies_reflclp_multp: "A \<subseteq># B \<Longrightarrow> (multp R)\<^sup>=\<^sup>= A B"
  by (metis reflclp_iff strict_subset_implies_multp subset_mset.le_imp_less_or_eq)

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

lemma (in backward_simulation)
  assumes "match i S1 S2" and "\<not> L1.inf_step S1"
  shows "\<not> L2.inf_step S2"
  using assms match_inf by metis

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

definition atms_of_cls :: "'a clause \<Rightarrow> 'a fset" where
  "atms_of_cls C = atm_of |`| fset_mset C"

definition atms_of_clss :: "'a clause fset \<Rightarrow> 'a fset" where
  "atms_of_clss N = ffUnion (atms_of_cls |`| N)"

definition lits_of_clss :: "'a clause fset \<Rightarrow> 'a literal fset" where
  "lits_of_clss N = ffUnion (fset_mset |`| N)"

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

subsection \<open>Function for full factorization\<close>

definition sfac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "sfac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

lemma ex1_sfac_eq_factoring_chain:
  "\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
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

lemma sfac_eq_disj:
  "sfac C = C \<or> (\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"
  using ex1_sfac_eq_factoring_chain
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

lemma sfac_spec: "sfac C = C \<or>
  (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> sfac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
  using sfac_eq_disj[of C]
proof (elim disjE)
  assume "sfac C = C"
  thus "sfac C = C \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> sfac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
    by metis
next
  assume "\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and>
    (\<nexists>C''. ord_res.ground_factoring C' C'')"
  then obtain C' where
    "sfac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    by metis
  thus "sfac C = C \<or>
    (\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> sfac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#})"
    unfolding rtrancl_ground_factoring_iff
    by metis
qed

lemma sfac_spec_if_pos_lit_is_maximal:
  assumes L_pos: "is_pos L" and L_max: "ord_res.is_maximal_lit L C"
  shows "sfac C = add_mset L {#K \<in># C. K \<noteq> L#}"
proof -
  from assms obtain C' where
    "sfac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex1_sfac_eq_factoring_chain by metis
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
    thus "sfac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      using \<open>sfac C = C'\<close> \<open>C = C'\<close> by argo
  next
    assume "\<exists>A. ord_res.is_maximal_lit (Pos A) C \<and> C' = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
    thus "sfac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      by (metis L_max Uniq_D \<open>sfac C = C'\<close> linorder_lit.Uniq_is_maximal_in_mset)
  qed
qed

lemma sfac_mempty[simp]: "sfac {#} = {#}"
  by (metis empty_iff linorder_lit.is_maximal_in_mset_iff set_mset_empty sfac_spec)

lemma set_mset_sfac[simp]: "set_mset (sfac C) = set_mset C"
  using sfac_spec[of C]
proof (elim disjE exE conjE)
  show "sfac C = C \<Longrightarrow> set_mset (sfac C) = set_mset C"
    by simp
next
  fix A
  assume "ord_res.is_maximal_lit (Pos A) C"
  hence "Pos A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

  assume sfac_C_eq: "sfac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
  show "set_mset (sfac C) = set_mset C"
  proof (intro Set.subset_antisym Set.subsetI)
    fix L assume "L \<in># sfac C"
    then show "L \<in># C"
      unfolding sfac_C_eq
      using \<open>Pos A \<in># C\<close> by auto
  next
    fix L assume "L \<in># C"
    then show "L \<in># sfac C"
      unfolding sfac_C_eq
      by simp
  qed
qed

lemma sfac_subset: "sfac C \<subseteq># C"
  using sfac_spec[of C]
proof (elim disjE exE conjE)
  show "sfac C = C \<Longrightarrow> sfac C \<subseteq># C"
    by simp
next
  fix A
  assume "ord_res.is_maximal_lit (Pos A) C" and
    sfac_C_eq: "sfac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
  then show "sfac C \<subseteq># C"
    by (smt (verit, ccfv_SIG) filter_mset_add_mset insert_DiffM insert_subset_eq_iff
        linorder_lit.is_maximal_in_mset_iff multiset_filter_subset)
qed

lemma obtains_positive_greatest_lit_if_sfac_not_ident:
  assumes "sfac C \<noteq> C"
  obtains L where "is_pos L" and "linorder_lit.is_greatest_in_mset (sfac C) L"
proof -
  from \<open>sfac C \<noteq> C\<close> obtain A where
    Pos_A_maximal: "linorder_lit.is_maximal_in_mset C (Pos A)" and
    sfac_C_eq: "sfac C = add_mset (Pos A) {#L \<in># C. L \<noteq> Pos A#}"
    using sfac_spec by metis

  assume hyp: "\<And>L. is_pos L \<Longrightarrow> linorder_lit.is_greatest_in_mset (sfac C) L \<Longrightarrow> thesis"
  show thesis
  proof (rule hyp)
    show "is_pos (Pos A)"
      by simp
  next
    show "linorder_lit.is_greatest_in_mset(sfac C) (Pos A)"
      unfolding sfac_C_eq linorder_lit.is_greatest_in_mset_iff
      using Pos_A_maximal[unfolded linorder_lit.is_maximal_in_mset_iff]
      by auto
  qed
qed

lemma mempty_in_image_sfac_iff[simp]: "{#} \<in> sfac ` N \<longleftrightarrow> {#} \<in> N"
  by (metis empty_iff imageE image_eqI linorder_lit.is_maximal_in_mset_iff set_mset_empty set_mset_sfac sfac_spec)


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


subsection \<open>New try\<close>

abbreviation ord_res_Interp where
  "ord_res_Interp N C \<equiv> ord_res.interp N C \<union> ord_res.production N C"

definition is_least_false_clause where
  "is_least_false_clause N C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"

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


subsubsection \<open>ORD-RES-0\<close>

definition ord_res_final where
  "ord_res_final N \<longleftrightarrow> {#} |\<in>| N \<or> \<not> ex_false_clause (fset N)"

inductive ord_res where
  factoring: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    \<comment> \<open>Maybe write \<^term>\<open>\<not> ord_res_final N\<close> instead?\<close>
    P |\<in>| N \<Longrightarrow> ord_res.ground_factoring P C \<Longrightarrow>
    N' = finsert C N \<Longrightarrow>
    ord_res N N'" |

  resolution: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    P1 |\<in>| N \<Longrightarrow> P2 |\<in>| N \<Longrightarrow> ord_res.ground_resolution P1 P2 C \<Longrightarrow>
    N' = finsert C N \<Longrightarrow>
    ord_res N N'"

inductive ord_res_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_load N N"

interpretation ord_res_semantics: semantics where
  step = ord_res and
  final = ord_res_final
proof unfold_locales
  fix N :: "'f gterm clause fset"
  assume "ord_res_final N"
  thus "finished ord_res N"
    unfolding ord_res_final_def
  proof (elim disjE)
    show "{#} |\<in>| N \<Longrightarrow> finished ord_res N"
      by (simp add: finished_def ord_res.simps)
  next
    show "\<not> ex_false_clause (fset N) \<Longrightarrow> finished ord_res N"
      by (simp add: finished_def ord_res.simps)
  qed
qed

interpretation ord_res_language: language where
  step = ord_res and
  final = ord_res_final and
  load = ord_res_load
  by unfold_locales


subsubsection \<open>ORD-RES-1 (deterministic)\<close>

inductive ord_res_1 where
  factoring: "
    linorder_cls.is_least_in_fset
      {|C |\<in>| N. \<not> ord_res.interp (fset N) C \<union> ord_res.production (fset N) C \<TTurnstile> C|} C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    ord_res.ground_factoring C C' \<Longrightarrow>
    N' = finsert C' N \<Longrightarrow>
    ord_res_1 N N'" |

  resolution: "
    linorder_cls.is_least_in_fset
      {|C |\<in>| N. \<not> ord_res.interp (fset N) C \<union> ord_res.production (fset N) C \<TTurnstile> C|} C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset N) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    N' = finsert CD N \<Longrightarrow>
    ord_res_1 N N'"

lemma right_unique_res_mo_strategy: "right_unique ord_res_1"
proof (rule right_uniqueI)
  fix N N' N'' :: "'f gterm clause fset"
  assume step1: "ord_res_1 N N'" and step2: "ord_res_1 N N''"
  from step1 show "N' = N''"
  proof (cases N N' rule: ord_res_1.cases)
    case hyps1: (factoring C1 L1 C1')
    from step2 show ?thesis
    proof (cases N N'' rule: ord_res_1.cases)
      case hyps2: (factoring C2 L2 C2')
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
      with hyps1 hyps2 have "C1' = C2'"
        by (metis (no_types, lifting) Uniq_D ord_res.unique_ground_factoring)
      with hyps1 hyps2 show ?thesis
        by argo
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution C1 L1 D1 CD1)
    from step2 show ?thesis
    proof (cases N N'' rule: ord_res_1.cases)
      case hyps2: (factoring C2 L2 C2')
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have "D1 = D2"
        by (metis (mono_tags) Uniq_D ord_res.Uniq_production_eq_singleton)
      with hyps1 hyps2 have "CD1 = CD2"
        by (metis (no_types, lifting) Uniq_D \<open>C1 = C2\<close> ord_res.unique_ground_resolution)
      with hyps1 hyps2 show ?thesis
        by argo
    qed
  qed
qed

definition ord_res_1_final where
  "ord_res_1_final N \<longleftrightarrow> ord_res_final N"

inductive ord_res_1_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_1_load N N"

interpretation ord_res_1_semantics: semantics where
  step = ord_res_1 and
  final = ord_res_1_final
proof unfold_locales
  fix N :: "'f gterm clause fset"
  assume "ord_res_1_final N"
  thus "finished ord_res_1 N"
    unfolding ord_res_1_final_def ord_res_final_def
  proof (elim disjE)
    assume "{#} |\<in>| N"
    have False if "ord_res_1 N N'" for N'
      using that
    proof (cases N N' rule: ord_res_1.cases)
      case hyps: (factoring C L C')
      from hyps \<open>{#} |\<in>| N\<close> have "C = {#}"
        by (metis (no_types, lifting) emptyE ffmember_filter linorder_cls.dual_order.strict_trans
            linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl
            ord_res.multp_if_all_left_smaller set_mset_empty true_cls_empty)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    next
      case hyps: (resolution C L D CD)
      from hyps \<open>{#} |\<in>| N\<close> have "C = {#}"
        by (metis (no_types, lifting) emptyE ffmember_filter linorder_cls.dual_order.strict_trans
            linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl
            ord_res.multp_if_all_left_smaller set_mset_empty true_cls_empty)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    qed
    thus "finished ord_res_1 N"
      unfolding finished_def by metis
  next
    assume "\<not> ex_false_clause (fset N)"
    have False if "ord_res_1 N N'" for N'
      using that
    proof (cases N N' rule: ord_res_1.cases)
      case (factoring C L C')
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    next
      case (resolution C L D CD)
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    qed
    thus "finished ord_res_1 N"
      unfolding finished_def by metis
  qed
qed

interpretation ord_res_1_language: language where
  step = ord_res_1 and
  final = ord_res_1_final and
  load = ord_res_1_load
  by unfold_locales

interpretation backward_simulation_with_measuring_function where
  step1 = ord_res and
  step2 = ord_res_1 and
  final1 = ord_res_final and
  final2 = ord_res_1_final and
  order = "\<lambda>_ _. False" and
  match = "(=)" and
  measure = "\<lambda>_. ()"
proof unfold_locales
  show "wfP (\<lambda>_ _. False)"
    by simp
next
  show "\<And>N1 N2. N1 = N2 \<Longrightarrow> ord_res_1_final N2 \<Longrightarrow> ord_res_final N1"
    unfolding ord_res_1_final_def by metis
next
  fix N1 N2 N2' :: "'f gterm clause fset"
  assume match: "N1 = N2" and step2: "ord_res_1 N2 N2'"
  show "(\<exists>N1'. ord_res\<^sup>+\<^sup>+ N1 N1' \<and> N1' = N2') \<or> N1 = N2' \<and> False"
  proof (intro disjI1 exI conjI)
    
    have mempty_no_in: "{#} |\<notin>| N2"
      if C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N2.
        \<not> ord_res.interp (fset N2) C \<union> ord_res.production (fset N2) C \<TTurnstile> C|} C" and
        L_max: "linorder_lit.is_maximal_in_mset C L"
      for C L
    proof (rule notI)
      assume "{#} |\<in>| N2"
      moreover have "\<not> ord_res.interp (fset N2) {#} \<union> ord_res.production (fset N2) {#} \<TTurnstile> {#}"
        by simp
      moreover have "\<And>C. {#} \<preceq>\<^sub>c C"
        using mempty_lesseq_cls by metis
      ultimately have "C = {#}"
        using C_least
        by (metis (no_types, lifting) ffmember_filter linorder_cls.is_least_in_fset_iff
            linorder_cls.less_le_not_le)
      moreover have "L \<in># C"
        using L_max by (simp add: linorder_lit.is_maximal_in_mset_iff)
      ultimately show "False"
        by simp
    qed

    have "ord_res N2 N2'"
      using step2
    proof (cases N2 N2' rule: ord_res_1.cases)
      case hyps: (factoring C L C')
      show ?thesis
      proof (rule ord_res.factoring)
        show "{#} |\<notin>| N2"
          using hyps mempty_no_in by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps linorder_cls.is_least_in_fset_ffilterD
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps linorder_cls.is_least_in_fset_ffilterD(1) by blast
      next
        show "ord_res.ground_factoring C C'"
          using hyps by argo
      next
        show "N2' = finsert C' N2"
          using hyps by argo
      qed
    next
      case hyps: (resolution C L D CD)
      show ?thesis
      proof (rule ord_res.resolution)
        show "{#} |\<notin>| N2"
          using hyps mempty_no_in by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps linorder_cls.is_least_in_fset_ffilterD
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps linorder_cls.is_least_in_fset_ffilterD(1) by blast
      next
        show "D |\<in>| N2"
          using hyps by argo
      next
        show "ord_res.ground_resolution C D CD"
          using hyps by argo
      next
        show "N2' = finsert CD N2"
          using hyps by argo
      qed
    qed
    thus "ord_res\<^sup>+\<^sup>+ N1 N2'"
      unfolding match by simp
  next
    show "N2' = N2'" ..
  qed
qed


subsubsection \<open>ORD-RES-2 (full factorization)\<close>

inductive ord_res_2 where
  factoring: "
    is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    U\<^sub>f\<^sub>f' = finsert (sfac C) U\<^sub>f\<^sub>f \<Longrightarrow>
    ord_res_2 N (U\<^sub>r, U\<^sub>f\<^sub>f) (U\<^sub>r, U\<^sub>f\<^sub>f')" |

  resolution: "
    is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    U\<^sub>r' = finsert CD U\<^sub>r \<Longrightarrow>
    ord_res_2 N (U\<^sub>r, U\<^sub>f\<^sub>f) (U\<^sub>r', U\<^sub>f\<^sub>f)"

fun ord_res_2_final where
  "ord_res_2_final N (U\<^sub>r, U\<^sub>f\<^sub>f) \<longleftrightarrow> ord_res_final (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)"

inductive ord_res_2_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_2_load N N ({||}, {||})"

interpretation ord_res_2_semantics: semantics' where
  step = ord_res_2 and
  final = ord_res_2_final
proof unfold_locales
  fix N :: "'f gterm clause fset" and S :: "'f gterm clause fset \<times> 'f gterm clause fset"

  obtain U\<^sub>r U\<^sub>f\<^sub>f where S_def: "S = (U\<^sub>r, U\<^sub>f\<^sub>f)"
    by fastforce

  assume "ord_res_2_final N S"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    by (simp add: S_def ord_res_final_def)
  thus "finished (ord_res_2 N) S"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
    have False if "ord_res_2 N S S'" for S'
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>f\<^sub>f)" S' rule: ord_res_2.cases)
      case hyps: (factoring C L U\<^sub>f\<^sub>f')
      from hyps have "C = {#}"
        using is_least_false_clause_mempty[OF \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close>]
        by (metis Uniq_D Uniq_is_least_false_clause)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    next
      case hyps: (resolution C L D CD U\<^sub>f\<^sub>f')
      from hyps \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> have "C = {#}"
        using is_least_false_clause_mempty[OF \<open>{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close>]
        by (metis Uniq_D Uniq_is_least_false_clause)
      moreover from hyps have "L \<in># C"
        using linorder_lit.is_maximal_in_mset_iff by blast
      ultimately show False
        by simp
    qed
    thus "finished (ord_res_2 N) S"
      unfolding finished_def by metis
  next
    assume no_false_cls: "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    have False if "ord_res_2 N S S'" for S'
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>f\<^sub>f)" S' rule: ord_res_2.cases)
      case hyps: (factoring C L U\<^sub>f\<^sub>f')
      thus False
        using no_false_cls[unfolded ex_false_clause_def]
        using is_least_false_clause_def linorder_cls.is_least_in_fset_iff by auto
    next
      case hyps: (resolution C L D CD U\<^sub>f\<^sub>f')
      thus False
        using no_false_cls[unfolded ex_false_clause_def]
        using is_least_false_clause_def linorder_cls.is_least_in_fset_iff by auto
    qed
    thus "finished (ord_res_2 N) S"
      unfolding finished_def by metis
  qed
qed

interpretation ord_res_2_language: language' where
  step = ord_res_2 and
  final = ord_res_2_final and
  load = ord_res_2_load
  by unfold_locales

fun ord_res_1_matches_ord_res_2 where
  "ord_res_1_matches_ord_res_2 S1 N (U\<^sub>r, U\<^sub>f\<^sub>f) \<longleftrightarrow> (\<exists>U\<^sub>f.
      S1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f \<and>
      (\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
        (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)))"

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


lemma production_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using ord_res.wfP_less_cls C_in
proof (induction C rule: wfP_induct_rule)
  case (less C)
  hence C_in_iff: "C \<in> N1 \<union> N2 \<longleftrightarrow> C \<in> N1"
    by simp
  
  have interp_eq: "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C"
  proof -
    have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
      unfolding ord_res.interp_def ..
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2. D \<prec>\<^sub>c C})"
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

lemma extended_partial_model_entails_iff_partial_model_entails:
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N"
  shows "ord_res_Interp (N \<union> N') C \<TTurnstile> C \<longleftrightarrow> ord_res_Interp N C \<TTurnstile> C"
  using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  by metis


lemma factorizable_if_neq_sfac:
  assumes "C \<noteq> sfac C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
  using assms
  by (metis converse_rtranclpE ex1_sfac_eq_factoring_chain)

lemma nex_strictly_maximal_pos_lit_if_factorizable:
  assumes "ord_res.ground_factoring C C'"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  by (metis Uniq_D add_mset_remove_trivial assms linorder_lit.Uniq_is_maximal_in_mset
      linorder_lit.dual_order.order_iff_strict linorder_lit.is_greatest_in_mset_iff
      linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.not_less
      ord_res.ground_factoring.cases union_single_eq_member)

lemma nex_strictly_maximal_pos_lit_if_neq_sfac:
  assumes "C \<noteq> sfac C"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  using assms factorizable_if_neq_sfac nex_strictly_maximal_pos_lit_if_factorizable by metis

lemma unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "ord_res.production N C = {}"
  using assms by (simp add: ord_res.production_unfold)

lemma ball_unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<forall>C \<in> N'. \<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "\<forall>C \<in> N'. ord_res.production (N \<union> N') C = {}"
  using assms unproductive_if_nex_strictly_maximal_pos_lit by metis

lemma is_least_in_fset_with_irrelevant_clauses_if_is_least_in_fset:
  assumes
    irrelevant: "\<forall>D |\<in>| N'. \<exists>E |\<in>| N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"
  shows "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| N'. \<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C|} C"
proof -
  have
    C_in: "C |\<in>| N" and
    C_not_entailed: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_lt: "\<forall>x |\<in>| N. x \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) x \<TTurnstile> x \<longrightarrow> C \<prec>\<^sub>c x"
    using C_least linorder_cls.is_least_in_ffilter_iff by simp_all

  have "C |\<in>| N |\<union>| N'"
    using C_in by simp

  moreover have "\<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C"
    using extended_partial_model_entails_iff_partial_model_entails[
        of "fset N" "fset N'", OF finite_fset finite_fset irrelevant]
    using C_in C_not_entailed
    by simp

  moreover have "C \<prec>\<^sub>c x"
    if
      x_in: "x |\<in>| N |\<union>| N'" and
      x_neq: "x \<noteq> C" and
      x_not_entailed: "\<not> ord_res_Interp (fset (N |\<union>| N')) x \<TTurnstile> x"
    for x
  proof -

    from x_in have "x |\<in>| N \<or> x |\<in>| N'"
      by simp
    thus "C \<prec>\<^sub>c x"
    proof (elim disjE)
      assume x_in: "x |\<in>| N"

      moreover have "\<not> ord_res_Interp (fset N) x \<TTurnstile> x"
        using extended_partial_model_entails_iff_partial_model_entails[
            of "fset N" "fset N'", OF finite_fset finite_fset irrelevant x_in]
        using x_not_entailed by simp

      ultimately show "C \<prec>\<^sub>c x"
        using C_lt[rule_format, of x] x_neq by argo
    next
      assume "x |\<in>| N'"
      then obtain x' where "x' |\<in>| N" and "x' \<subset># x" "set_mset x' = set_mset x"
        using irrelevant by metis

      have "x' \<prec>\<^sub>c x"
        using \<open>x' \<subset># x\<close> by (metis strict_subset_implies_multp)

      moreover have "C \<preceq>\<^sub>c x'"
      proof (cases "x' = C")
        case True
        thus ?thesis
          by order
      next
        case False

        have "C \<prec>\<^sub>c x'"
        proof (rule C_lt[rule_format])
          show "x' |\<in>| N"
            using \<open>x' |\<in>| N\<close> .
        next
          show "x' \<noteq> C"
            using False .
        next
          have "\<not> ord_res_Interp (fset (N |\<union>| N')) x \<TTurnstile> x'"
            using x_not_entailed \<open>set_mset x' = set_mset x\<close>
            by (metis true_cls_def)
          hence "\<not> ord_res_Interp (fset (N |\<union>| N')) x' \<TTurnstile> x'"
            by (metis \<open>x' \<prec>\<^sub>c x\<close> ord_res.entailed_clause_stays_entailed)
          thus "\<not> ord_res_Interp (fset N) x' \<TTurnstile> x'"
            using extended_partial_model_entails_iff_partial_model_entails[
                of "fset N" "fset N'" x', OF finite_fset finite_fset irrelevant]
            using \<open>x' |\<in>| N\<close> by simp
        qed
        thus ?thesis
          by order
      qed

      ultimately show "C \<prec>\<^sub>c x"
        by order
    qed
  qed

  ultimately show "linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| N'.
    \<not> ord_res_Interp (fset (N |\<union>| N')) C \<TTurnstile> C|} C"
    using C_in C_not_entailed
    unfolding linorder_cls.is_least_in_ffilter_iff by metis
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

thm List.upto.simps

primrec fset_upto :: "nat \<Rightarrow> nat \<Rightarrow> nat fset" where
  "fset_upto i 0 = (if i = 0 then {|0|} else {||})" |
  "fset_upto i (Suc n) = (if i \<le> Suc n then finsert (Suc n) (fset_upto i n) else {||})"

lemma
  "fset_upto 0 0 = {|0|}"
  "fset_upto 0 1 = {|0, 1|}"
  "fset_upto 0 2 = {|0, 1, 2|}"
  "fset_upto 0 3 = {|0, 1, 2, 3|}"
  "fset_upto 1 3 = {|1, 2, 3|}"
  "fset_upto 2 3 = {|2, 3|}"
  "fset_upto 3 3 = {|3|}"
  "fset_upto 4 3 = {||}"
  unfolding numeral_2_eq_2 numeral_3_eq_3
  by auto

lemma "i \<le> 1 + j \<Longrightarrow> List.upto i (1 + j) = List.upto i j @ [1 + j]"
  using upto_rec2 by simp

lemma fset_of_append_singleton: "fset_of_list (xs @ [x]) = finsert x (fset_of_list xs)"
  by simp

lemma "fset_of_list (List.upto (int i) (int j)) = int |`| fset_upto i j"
proof (induction j)
  case 0
  show ?case
    by simp
next
  case (Suc j)
  show ?case
  proof (cases "i \<le> Suc j")
    case True
    hence AAA: "int i \<le> 1 + int j"
      by presburger

    from True show ?thesis
      apply simp
      unfolding Suc.IH[symmetric]
      unfolding upto_rec2[OF AAA] fset_of_append_singleton
      by simp
  next
    case False
    thus ?thesis
      by simp
  qed
qed

lemma fset_fset_upto[simp]: "fset (fset_upto 0 n) = {0..n}"
  apply (induction n)
  apply simp
  apply simp
  using atLeast0_atMost_Suc by presburger

lemma minus_mset_replicate_strict_subset_minus_msetI:
  assumes "m < n" and "n < count C L"
  shows "C - replicate_mset n L \<subset># C - replicate_mset m L"
proof -
  from \<open>m < n\<close> obtain k1 where n_def: "n = m + Suc k1"
    using less_natE by auto

  with \<open>n < count C L\<close> obtain k2 where
    count_eq: "count C L = m + Suc k1 + Suc k2"
    by (metis add.commute add_Suc group_cancel.add1 less_natE)

  define C\<^sub>0 where
    "C\<^sub>0 = {#K \<in># C. K \<noteq> L#}"

  have C_eq: "C = C\<^sub>0 + replicate_mset m L + replicate_mset (Suc k1) L + replicate_mset (Suc k2) L"
    using C\<^sub>0_def count_eq
    by (metis (mono_tags, lifting) filter_mset_eq group_cancel.add1 replicate_mset_plus
        union_filter_mset_complement)

  have "C - replicate_mset n L = C\<^sub>0 + replicate_mset (Suc k2) L"
    unfolding C_eq n_def
    by (simp add: replicate_mset_plus)
  also have "\<dots> \<subset># C\<^sub>0 + replicate_mset (Suc k1) L + replicate_mset (Suc k2) L"
    by simp
  also have "\<dots> = C - replicate_mset m L"
    unfolding C_eq
    by (simp add: replicate_mset_plus)
  finally show ?thesis .
qed

lemma factoring_all_is_between_sfac_and_original_clause:
  fixes z
  assumes
    "is_pos L" and "ord_res.is_maximal_lit L C" and "count C L = Suc (Suc n)"
    "m' \<le> n" and
    z_in: "z |\<in>| (\<lambda>i. C - replicate_mset i L) |`| fset_upto 0 m'"
  shows "sfac C \<subset># z" and "z \<subseteq># C"
proof -
  from z_in obtain i where
    "i \<le> m'" and
    z_def: "z = C - replicate_mset i L"
    by auto

  have "i \<le> n"
    using \<open>i \<le> m'\<close> \<open>m' \<le> n\<close> by presburger
  hence "i < count C L"
    using \<open>count C L = Suc (Suc n)\<close> by presburger
  thus "z \<subseteq># C"
    unfolding z_def by simp

  show "sfac C \<subset># z"
  proof -
    have "sfac C = add_mset L {#K \<in># C. K \<noteq> L#}"
      using sfac_spec_if_pos_lit_is_maximal[OF \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L C\<close>] .
    also have "\<dots> \<subset># add_mset L (add_mset L {#K \<in># C. K \<noteq> L#})"
      by simp
    also have "\<dots> = C - replicate_mset n L"
      using minus_mset_replicate_mset_eq_add_mset_add_mset_filter_mset[
          OF \<open>count C L = Suc (Suc n)\<close>] ..
    also have "\<dots> \<subseteq># C - replicate_mset i L"
      using \<open>i \<le> n\<close> by (simp add: subseteq_mset_def)
    also have "\<dots> = z"
      using z_def ..
    finally show ?thesis .
  qed
qed

lemma FOO:
  assumes
    "linorder_cls.is_least_in_fset {|x |\<in>| N1. P N1 x|} x" and
    "linorder_cls.is_least_in_fset N2 y" and
    "\<forall>z |\<in>| N2. z \<preceq>\<^sub>c x" and
    "P (N1 |\<union>| N2) y" and
    "\<forall>z |\<in>| N1. z \<prec>\<^sub>c x \<longrightarrow> \<not> P (N1 |\<union>| N2) z"
  shows "linorder_cls.is_least_in_fset {|x |\<in>| N1 |\<union>| N2. P (N1 |\<union>| N2) x|} y"
proof -
  show ?thesis
    unfolding linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    from assms(2) show "y |\<in>| N1 |\<union>| N2"
      unfolding linorder_cls.is_least_in_fset_iff by simp
  next
    from assms(4) show "P (N1 |\<union>| N2) y"
      by argo
  next
    fix z
    assume z_in: "z |\<in>| N1 |\<union>| N2" and "z \<noteq> y" and "P (N1 |\<union>| N2) z"
    show "y \<prec>\<^sub>c z"
      using z_in[unfolded funion_iff]
    proof (elim disjE)
      from assms(2,3,5) show "z |\<in>| N1 \<Longrightarrow> y \<prec>\<^sub>c z"
        by (metis \<open>P (N1 |\<union>| N2) z\<close> \<open>z \<noteq> y\<close> linorder_cls.dual_order.not_eq_order_implies_strict
            linorder_cls.is_least_in_fset_iff linorder_cls.less_linear
            linorder_cls.order.strict_trans)
    next
      from assms(2) show "z |\<in>| N2 \<Longrightarrow> y \<prec>\<^sub>c z"
        using \<open>z \<noteq> y\<close> linorder_cls.is_least_in_fset_iff by blast
    qed
  qed
qed


lemma ground_factoring_preserves_sfac:
  assumes "ord_res.ground_factoring P C"
  shows "sfac P = sfac C"
  using assms
  by (smt (verit, ccfv_threshold) filter_mset_add_mset is_pos_def ord_res.ground_factoring.cases
      ord_res.ground_factoring_preserves_maximal_literal sfac_spec_if_pos_lit_is_maximal)

lemma ground_factorings_preserves_sfac:
  assumes "ord_res.ground_factoring\<^sup>*\<^sup>* P C"
  shows "sfac P = sfac C"
  using assms
  by (induction P rule: converse_rtranclp_induct)
    (simp_all add: ground_factoring_preserves_sfac)

lemma ord_res_1_final_iff_ord_res_2_final:
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 N (U\<^sub>r, U\<^sub>f\<^sub>f)"
  shows "ord_res_1_final S\<^sub>1 \<longleftrightarrow> ord_res_2_final N (U\<^sub>r, U\<^sub>f\<^sub>f)"
proof -
  from match obtain U\<^sub>f where
    S\<^sub>1_def: "S\<^sub>1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
      (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)"
    by auto

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> sfac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_sfac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  have "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> {#} |\<in>| U\<^sub>f"
      by simp
    thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
      thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
        by assumption
    next
      assume "{#} |\<in>| U\<^sub>f"
      hence "{#} \<noteq> sfac {#}"
        using U\<^sub>f_spec[rule_format, of "{#}"] by metis
      hence False
        by simp
      thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" ..
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
    thus "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
      by simp
  qed

  moreover have "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) \<longleftrightarrow>
    \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
  proof (rule iffI; erule contrapos_nn)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f))"
      unfolding ex_false_clause_def Interp_eq by auto
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f))"
    then obtain C where
      "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f" and
      C_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> C"
      unfolding ex_false_clause_def Interp_eq by metis
    hence "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    proof (elim disjE)
      assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
      thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
        unfolding ex_false_clause_def using C_false by metis
    next
      assume "C |\<in>| U\<^sub>f"
      then obtain C' where "C' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
       "ord_res.ground_factoring\<^sup>+\<^sup>+ C' C" and
       "C \<noteq> sfac C" and
       "sfac C |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C'"
        using U\<^sub>f_spec[rule_format, of C] by metis
      thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
      proof (elim disjE exE conjE)
        assume "sfac C |\<in>| U\<^sub>f\<^sub>f"

        show "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
        proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) (sfac C) \<TTurnstile> sfac C")
          case sfac_C_true: True
          have "sfac C \<subseteq># C"
            using sfac_subset[of C] .
          hence "sfac C \<preceq>\<^sub>c C"
            using subset_implies_reflclp_multp by metis
          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> sfac C"
            using sfac_C_true ord_res.entailed_clause_stays_entailed by auto
          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> C"
            using sfac_C_true by (simp add: true_cls_def)
          with C_false have False
            by contradiction
          thus ?thesis ..
        next
          case False

          moreover have "sfac C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
            using \<open>sfac C |\<in>| U\<^sub>f\<^sub>f\<close> by simp

          ultimately show "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
            unfolding ex_false_clause_def by metis
        qed
      next
        assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C'"
        hence "C' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C' \<TTurnstile> C'"
          using linorder_cls.is_least_in_ffilter_iff is_least_false_clause_def by simp_all
        thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
          unfolding ex_false_clause_def by metis
      qed
    qed
  qed

  ultimately show ?thesis
    by (simp add: S\<^sub>1_def ord_res_1_final_def ord_res_final_def)
qed

definition ord_res_1_measure where
  "ord_res_1_measure s1 =
    (if \<exists>C. is_least_false_clause s1 C then
      The (is_least_false_clause s1)
    else
      {#})"

lemma is_least_false_clause_if_is_least_false_clause_in_union_unproductive:
  assumes
    N2_unproductive: "\<forall>C |\<in>| N2. ord_res.production (fset (N1 |\<union>| N2)) C = {}" and
    C_in: "C |\<in>| N1" and
    C_least_false: "is_least_false_clause (N1 |\<union>| N2) C"
  shows "is_least_false_clause N1 C"
  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "C |\<in>| N1"
    using C_in .
next
  have "\<not> ord_res_Interp (fset (N1 |\<union>| N2)) C \<TTurnstile> C"
    using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
    by argo
  thus "\<not> ord_res.interp (fset N1) C \<union> ord_res.production (fset N1) C \<TTurnstile> C"
    unfolding Interp_union_unproductive[of "fset N1" "fset N2", folded union_fset,
        OF finite_fset finite_fset N2_unproductive] .
next
  fix D
  have "\<forall>D |\<in>| N1 |\<union>| N2. D \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset (N1 |\<union>| N2)) D \<TTurnstile> D \<longrightarrow> C \<prec>\<^sub>c D"
    using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
    by argo

  moreover assume "D |\<in>| N1" and "D \<noteq> C" and "\<not> ord_res_Interp (fset N1) D \<TTurnstile> D"

  ultimately show "C \<prec>\<^sub>c D"
    using Interp_union_unproductive[of "fset N1" "fset N2", folded union_fset,
        OF finite_fset finite_fset N2_unproductive]
    by simp
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


lemma ground_factoring_replicate_max_pos_lit:
  "ord_res.ground_factoring
    (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))
    (C\<^sub>0 + replicate_mset (Suc n) (Pos A))"
  if "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
  for A C\<^sub>0 n
proof (rule ord_res.ground_factoringI)
  show "C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A) =
            add_mset (Pos A) (add_mset (Pos A) (C\<^sub>0 + replicate_mset n (Pos A)))"
    by simp
next
  show "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
    using that .
next
  show "C\<^sub>0 + replicate_mset (Suc n) (Pos A) =
            add_mset (Pos A) (C\<^sub>0 + replicate_mset n (Pos A))"
    by simp
qed simp

(*
  m \<le> Suc n
*)

thm ord_res.ground_factorings_reduces_maximal_pos_lit[no_vars]

lemma ground_factorings_replicate_max_pos_lit:
  assumes
    "ord_res.is_maximal_lit (Pos A) (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))"
  shows "m \<le> Suc n \<Longrightarrow> (ord_res.ground_factoring ^^ m)
    (C\<^sub>0 + replicate_mset (Suc (Suc n)) (Pos A))
    (C\<^sub>0 + replicate_mset (Suc (Suc n - m)) (Pos A))"
proof (induction m)
  case 0
  show ?case
    by simp
next
  case (Suc m')
  then show ?case
    apply (cases m')
    using assms ground_factoring_replicate_max_pos_lit apply auto[1]
    by (metis (no_types, lifting) Suc_diff_le Suc_leD assms diff_Suc_Suc
        ground_factoring_replicate_max_pos_lit ord_res.ground_factorings_preserves_maximal_literal
        relpowp_Suc_I relpowp_imp_rtranclp)
qed

lemma ord_res_Interp_entails_if_greatest_lit_is_pos:
  assumes C_in: "C \<in> N" and L_greatest: "linorder_lit.is_greatest_in_mset C L" and L_pos: "is_pos L"
  shows "ord_res_Interp N C \<TTurnstile> C"
proof (cases "ord_res.interp N C \<TTurnstile> C")
  case True
  hence "ord_res.production N C = {}"
    by (simp add: ord_res.production_unfold)
  with True show ?thesis
    by simp
next
  case False

  from L_pos obtain A where L_def: "L = Pos A"
    by (cases L) simp_all

  from L_greatest obtain C' where C_def: "C = add_mset L C'"
    unfolding linorder_lit.is_greatest_in_mset_iff
    by (metis insert_DiffM)

  with C_in L_greatest have "A \<in> ord_res.production N C"
    unfolding L_def ord_res.production_unfold
    using False
    by (simp add: linorder_lit.is_greatest_in_mset_iff multi_member_split)
  thus ?thesis
    by (simp add: true_cls_def C_def L_def)
qed

interpretation bisimulation_with_measuring_function' where
  step1 = "\<lambda>_. ord_res_1" and final1 = "\<lambda>_. ord_res_1_final" and
  step2 = ord_res_2 and final2 = ord_res_2_final and
  match = "\<lambda>_. ord_res_1_matches_ord_res_2" and
  measure1 = "\<lambda>_. ord_res_1_measure" and order1 = "(\<subset>#)" and
  measure2 = "\<lambda>_ _. ()" and order2 = "\<lambda>_ _. False"
proof unfold_locales
  show "\<And>\<C> s. ord_res_1_final s \<Longrightarrow> finished ord_res_1 s"
    using ord_res_1_semantics.final_finished by force
next
  show "wfP (\<subset>#)"
    by simp
next
  fix
    s1 :: "'f gterm clause fset" and
    N :: "'f gterm clause fset" and
    s2 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  obtain U\<^sub>r U\<^sub>f\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (U\<^sub>r, U\<^sub>f\<^sub>f)"
    by fastforce

  assume "ord_res_1_matches_ord_res_2 s1 N s2" and "ord_res_2_final N s2"
  thus "ord_res_1_final s1"
    unfolding s2_def
    using ord_res_1_final_iff_ord_res_2_final by metis
next
  fix
    s1 :: "'f gterm clause fset" and
    N :: "'f gterm clause fset" and
    s2 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  obtain U\<^sub>r U\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (U\<^sub>r, U\<^sub>f)"
    by fastforce

  assume "ord_res_1_matches_ord_res_2 s1 N s2" and "ord_res_1_final s1"
  thus "ord_res_2_final N s2"
    unfolding s2_def
    using ord_res_1_final_iff_ord_res_2_final by metis
next
  let
    ?match = "\<lambda>_. ord_res_1_matches_ord_res_2" and
    ?measure1 = "\<lambda>_. ord_res_1_measure" and ?order1 = "(\<subset>#)"

  fix
    \<C>1 :: unit and
    s1 s1' :: "'f gterm clause fset" and
    N :: "'f gterm clause fset" and
    s2 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  obtain U\<^sub>r U\<^sub>f\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (U\<^sub>r, U\<^sub>f\<^sub>f)"
    by fastforce

  assume "?match \<C>1 s1 N s2"
  then obtain U\<^sub>f where
    s1_def: "s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
      (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)"
    unfolding s2_def ord_res_1_matches_ord_res_2.simps by metis

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> sfac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_sfac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  assume step1: "ord_res_1 s1 s1'"
  thus "(\<exists>s2'. (ord_res_2 N)\<^sup>+\<^sup>+ s2 s2' \<and> ?match \<C>1 s1' N s2') \<or>
       ?match \<C>1 s1' N s2 \<and> ?order1 (?measure1 \<C>1 s1') (?measure1 \<C>1 s1)"
  proof (cases s1 s1' rule: ord_res_1.cases)
    case (factoring C L C')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f) C"
      using factoring
      unfolding is_least_false_clause_def s1_def by argo

    have C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
      using factoring unfolding linorder_cls.is_least_in_ffilter_iff s1_def by argo
    hence C_in_disj: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp

    show ?thesis
    proof (cases "C' = sfac C'")
      case True
      let ?s2' = "(U\<^sub>r, finsert C' U\<^sub>f\<^sub>f)"

      have "(ord_res_2 N)\<^sup>+\<^sup>+ s2 ?s2'"
      proof (rule tranclp.r_into_trancl)
        show "ord_res_2 N s2 (U\<^sub>r, finsert C' U\<^sub>f\<^sub>f)"
          using C_in_disj
        proof (elim disjE)
          assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
          show ?thesis
            unfolding s2_def
          proof (rule ord_res_2.factoring)
            show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
              using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                  OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> C_least_false]
              unfolding is_least_false_clause_def .
          next
            show "ord_res.is_maximal_lit L C"
              using \<open>ord_res.is_maximal_lit L C\<close> .
          next
            show "is_pos L"
              using \<open>is_pos L\<close> .
          next
            show "finsert C' U\<^sub>f\<^sub>f = finsert (sfac C) U\<^sub>f\<^sub>f"
              using True factoring ground_factoring_preserves_sfac by metis
          qed
        next
          assume "C |\<in>| U\<^sub>f"
          then obtain x where
            "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
            "ord_res.ground_factoring\<^sup>+\<^sup>+ x C" and
            "C \<noteq> sfac C" and
            "sfac C |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
            using U\<^sub>f_spec by metis

          show ?thesis
            unfolding s2_def
          proof (rule ord_res_2.factoring)
            have \<open>sfac C |\<notin>| U\<^sub>f\<^sub>f\<close>
            proof (rule notI)
              have "sfac C \<preceq>\<^sub>c C"
                using sfac_subset[of C] subset_implies_reflclp_multp by metis
              hence "sfac C \<prec>\<^sub>c C"
                using \<open>C \<noteq> sfac C\<close> by order

              moreover assume "sfac C |\<in>| U\<^sub>f\<^sub>f"

              ultimately show False
                using C_least_false[unfolded is_least_false_clause_def
                    linorder_cls.is_least_in_ffilter_iff]
                by (metis \<open>C \<noteq> sfac C\<close> funionCI linorder_cls.not_less_iff_gr_or_eq
                    ord_res.entailed_clause_stays_entailed set_mset_sfac true_cls_def)
            qed
            thus "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
              using \<open>sfac C |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close> by argo
          next
            show "ord_res.is_maximal_lit L x"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.is_maximal_lit L C\<close>
              using ord_res.ground_factorings_preserves_maximal_literal
              by (metis tranclp_into_rtranclp)
          next
            show "is_pos L"
              using \<open>is_pos L\<close> .
          next
            show "finsert C' U\<^sub>f\<^sub>f = finsert (sfac x) U\<^sub>f\<^sub>f"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.ground_factoring C C'\<close>
              using True ground_factorings_preserves_sfac ground_factoring_preserves_sfac
              by (metis tranclp_into_rtranclp)
          qed
        qed
      qed

      moreover have "?match \<C>1 s1' N ?s2'"
      proof -
        have "s1' = N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
          unfolding \<open>s1' = finsert C' s1\<close> s1_def by simp

        moreover have "\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>f\<^sub>f.
          ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
          (sfac C\<^sub>f |\<in>| finsert C' U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>f\<^sub>f) C)"
          if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
        proof -
          obtain x where
            "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
            "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
            "C\<^sub>f \<noteq> sfac C\<^sub>f" and
            "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
            using \<open>C\<^sub>f |\<in>| U\<^sub>f\<close> U\<^sub>f_spec by metis

          show ?thesis
          proof (intro bexI conjI)
            show "x |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>f\<^sub>f"
              using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> by simp
          next
            show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
          next
            show "C\<^sub>f \<noteq> sfac C\<^sub>f"
              using \<open>C\<^sub>f \<noteq> sfac C\<^sub>f\<close> .
          next
            show "sfac C\<^sub>f |\<in>| finsert C' U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert C' U\<^sub>f\<^sub>f) x"
              using \<open>sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close>
            proof (elim disjE)
              assume "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f"
              thus ?thesis
                by simp
            next
              assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
              show ?thesis
              proof (cases "C' = sfac x")
                case True
                moreover have "sfac x = sfac C\<^sub>f"
                  using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> ground_factorings_preserves_sfac
                  by (metis tranclp_into_rtranclp)
                ultimately show ?thesis
                  by simp
              next
                case False
                show ?thesis
                  using C_in_disj
                proof (elim disjE)
                  assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
                  then show ?thesis
                    by (smt (verit) C_least_false True U\<^sub>f_unproductive
                        \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close> \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close>
                        finsert_iff ground_factoring_preserves_sfac ground_factorings_preserves_sfac
                        linorder_cls.Uniq_is_least_in_fset local.factoring(4)
                        is_least_false_clause_def
                        is_least_false_clause_if_is_least_false_clause_in_union_unproductive
                        the1_equality' tranclp_into_rtranclp)
                next
                  assume "C |\<in>| U\<^sub>f"
                  then show ?thesis
                    using C_least_false
                    using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                        OF U\<^sub>f_unproductive]
                    by (smt (z3) True U\<^sub>f_spec \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close>
                        \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> finsert_absorb finsert_iff
                        ground_factoring_preserves_sfac ground_factorings_preserves_sfac
                        linorder_cls.Uniq_is_least_in_fset local.factoring(4)
                        is_least_false_clause_def the1_equality' tranclp_into_rtranclp)
                qed
              qed
            qed
          qed
        qed

        ultimately show ?thesis
          by auto
      qed

      ultimately show ?thesis
        by metis
    next
      case False
      let ?U\<^sub>f' = "finsert C' U\<^sub>f"

      have "?match \<C>1 s1' N s2"
      proof -
        have "finsert C' s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| ?U\<^sub>f'"
          unfolding s1_def by simp

        moreover have "\<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f.
          ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
          (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)"
          if "C\<^sub>f |\<in>| ?U\<^sub>f'" for C\<^sub>f 
        proof -
          from \<open>C\<^sub>f |\<in>| ?U\<^sub>f'\<close> have "C\<^sub>f = C' \<or> C\<^sub>f |\<in>| U\<^sub>f"
            by simp
          thus ?thesis
          proof (elim disjE)
            assume "C\<^sub>f = C'"
            thus ?thesis
              using C_in_disj
            proof (elim disjE)
              assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
              show ?thesis
              proof (intro bexI conjI)
                show "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
                  using \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> .
              next
                show "ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f"
                  using \<open>ord_res.ground_factoring C C'\<close> \<open>C\<^sub>f = C'\<close> by simp
              next
                show "C\<^sub>f \<noteq> sfac C\<^sub>f"
                  using False \<open>C\<^sub>f = C'\<close> by argo
              next
                have "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
                  using factoring
                  using Interp_eq \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> linorder_cls.is_least_in_ffilter_iff
                  by (simp add: s1_def is_least_false_clause_def)
                thus "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C" ..
              qed
            next
              assume "C |\<in>| U\<^sub>f"
              then obtain x where
                "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
                "ord_res.ground_factoring\<^sup>+\<^sup>+ x C" and
                "C \<noteq> sfac C" and
                "sfac C |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
                using U\<^sub>f_spec by metis

              show ?thesis
              proof (intro bexI conjI)
                show "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
                  using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> .
              next
                show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
                  using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<close> \<open>ord_res.ground_factoring C C'\<close> \<open>C\<^sub>f = C'\<close>
                  by simp
              next
                show "C\<^sub>f \<noteq> sfac C\<^sub>f"
                  using False \<open>C\<^sub>f = C'\<close> by argo
              next
                show "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
                  using \<open>sfac C |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close>
                proof (elim disjE)
                  assume "sfac C |\<in>| U\<^sub>f\<^sub>f"

                  moreover have "sfac C = sfac C\<^sub>f"
                    unfolding \<open>C\<^sub>f = C'\<close>
                    using \<open>ord_res.ground_factoring C C'\<close> ground_factoring_preserves_sfac by metis

                  ultimately show ?thesis
                    by argo
                next
                  assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
                  thus ?thesis
                    by argo
                qed
              qed
            qed
          next
            assume "C\<^sub>f |\<in>| U\<^sub>f"
            thus ?thesis
              using U\<^sub>f_spec by metis
          qed
        qed

        ultimately have "ord_res_1_matches_ord_res_2 (finsert C' s1) N (U\<^sub>r, U\<^sub>f\<^sub>f)"
          unfolding ord_res_1_matches_ord_res_2.simps by metis
        thus ?thesis
          unfolding s2_def \<open>s1' = finsert C' s1\<close> by simp
      qed

      moreover have "?order1 (?measure1 \<C>1 s1') (?measure1 \<C>1 s1)"
      proof -
        have "?measure1 \<C>1 s1 = C"
          unfolding ord_res_1_measure_def
          using C_least_false[folded s1_def]
          by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
              is_least_false_clause_def the1_equality' the_equality)

        moreover have "?measure1 \<C>1 s1' = C'"
        proof -
          have "C' \<prec>\<^sub>c C"
            using factoring ord_res.ground_factoring_smaller_conclusion by metis

          have unproductive: "\<forall>x\<in>{C'}. ord_res.production (fset s1 \<union> {C'}) x = {}"
            using \<open>C' \<noteq> sfac C'\<close>
            by (simp add: nex_strictly_maximal_pos_lit_if_neq_sfac
                unproductive_if_nex_strictly_maximal_pos_lit)

          have Interp_eq: "\<And>D. ord_res_Interp (fset s1) D = ord_res_Interp (fset (finsert C' s1)) D"
            using Interp_union_unproductive[of "fset s1" "{C'}", folded union_fset,
                OF finite_fset _ unproductive]
            by simp

          have "is_least_false_clause (finsert C' s1) C'"
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            have "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C"
              using local.factoring(1) linorder_cls.is_least_in_ffilter_iff by simp
            thus "\<not> ord_res_Interp (fset (finsert C' s1)) C' \<TTurnstile> C'"
              by (metis Interp_eq \<open>C' \<prec>\<^sub>c C\<close> local.factoring(4)
                  ord_res.entailed_clause_stays_entailed
                  ord_res.set_mset_eq_set_mset_if_ground_factoring subset_refl true_cls_mono)
          next
            fix y
            assume "y |\<in>| finsert C' s1" and "y \<noteq> C'" and
              y_false: "\<not> ord_res_Interp (fset (finsert C' s1)) y \<TTurnstile> y"
            hence "y |\<in>| s1"
              by simp

            moreover have "\<not> ord_res_Interp (fset s1) y \<TTurnstile> y"
              using y_false
              unfolding Interp_eq .

            ultimately have "C \<preceq>\<^sub>c y"
              using C_least_false[folded s1_def, unfolded is_least_false_clause_def]
              unfolding linorder_cls.is_least_in_ffilter_iff
              by force
            thus "C' \<prec>\<^sub>c y"
              using \<open>C' \<prec>\<^sub>c C\<close> by order
          qed simp
          thus ?thesis
            unfolding ord_res_1_measure_def \<open>s1' = finsert C' s1\<close>
            by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
                is_least_false_clause_def the1_equality' the_equality)
        qed

        moreover have "C' \<subset># C"
          using factoring ord_res.strict_subset_mset_if_ground_factoring by metis

        ultimately show ?thesis
          unfolding s1_def  by simp
      qed

      ultimately show ?thesis
        by argo
    qed
  next
    case (resolution C L D CD)

    have "is_least_false_clause s1 C"
      using resolution unfolding is_least_false_clause_def by argo 
    hence
      "C |\<in>| s1" and
      "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C" and
      "\<forall>x |\<in>| s1. \<not> ord_res_Interp (fset s1) x \<TTurnstile> x \<longrightarrow> x \<noteq> C \<longrightarrow> C \<prec>\<^sub>c x"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by simp_all

    have "C |\<notin>| U\<^sub>f"
    proof (rule notI)
      assume "C |\<in>| U\<^sub>f"
      then show False
        by (metis U\<^sub>f_spec Uniq_D is_pos_def linorder_lit.Uniq_is_maximal_in_mset local.resolution(2)
            local.resolution(3) sfac_spec)
    qed
    hence "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
      using \<open>C |\<in>| s1\<close> by (simp add: s1_def)

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f) C"
      unfolding is_least_false_clause_def
      using resolution s1_def by metis
    hence C_least_false': "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
      using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
          OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close>] by argo

    define s2' where
      "s2' = (finsert CD U\<^sub>r, U\<^sub>f\<^sub>f)"

    have "(ord_res_2 N)\<^sup>+\<^sup>+ s2 s2'"
    proof -
      have "D |\<notin>| U\<^sub>f"
      proof (rule notI)
        assume "D |\<in>| U\<^sub>f"
        thus False
          using \<open>ord_res.production (fset s1) D = {atm_of L}\<close>
          using U\<^sub>f_unproductive s1_def by simp
      qed
      hence D_in: "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
        using \<open>D |\<in>| s1\<close>[unfolded s1_def] by simp

      have "ord_res_2 N (U\<^sub>r, U\<^sub>f\<^sub>f) (finsert CD U\<^sub>r, U\<^sub>f\<^sub>f)"
      proof (rule ord_res_2.resolution)
        show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
          using C_least_false' .
      next
        show "ord_res.is_maximal_lit L C"
          using resolution by argo
      next
        show "is_neg L"
          using resolution by argo
      next
        show "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
          using D_in .
      next
        show "D \<prec>\<^sub>c C"
          using resolution by argo
      next
        show "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) D = {atm_of L}"
          using resolution
          unfolding s1_def
          using production_union_unproductive[OF finite_fset finite_fset _ D_in] U\<^sub>f_unproductive
          by (metis (no_types, lifting) union_fset)
      next
        show "ord_res.ground_resolution C D CD"
          using resolution by argo
      qed simp_all
      thus ?thesis
        by (simp add: s2_def s2'_def)
    qed

    moreover have "?match \<C>1 s1' N s2'"
    proof -
      have "finsert CD (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f) = N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
        by simp

      moreover have "\<exists>C |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f.
        ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
        (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)"
        if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
      proof -
        obtain x where
          "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
          "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
          "C\<^sub>f \<noteq> sfac C\<^sub>f" and
          "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
          using \<open>C\<^sub>f |\<in>| U\<^sub>f\<close> U\<^sub>f_spec by metis
        show ?thesis
        proof (intro bexI conjI)
          show "x |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
            using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> by simp
        next
          show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
            using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
        next
          show "C\<^sub>f \<noteq> sfac C\<^sub>f"
            using \<open>C\<^sub>f \<noteq> sfac C\<^sub>f\<close> .
        next
          show \<open>sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close>
            using \<open>sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close> \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close>
            by (metis (no_types, lifting) C_least_false' Uniq_D \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close>
                is_least_false_clause_def is_pos_def linorder_cls.Uniq_is_least_in_fset
                linorder_lit.Uniq_is_maximal_in_mset local.resolution(2) local.resolution(3)
                ord_res.ground_factoring.cases tranclpD)
        qed
      qed

      ultimately show ?thesis
        unfolding s1_def resolution s2'_def by auto
    qed

    ultimately show ?thesis
      by metis
  qed
next
  let
    ?match = "\<lambda>_. ord_res_1_matches_ord_res_2" and
    ?measure2 = "\<lambda>_ _. ()" and ?order2 = "\<lambda>_ _. False"

  fix
    \<C>1 :: unit and
    s1 :: "'f gterm clause fset" and
    N :: "'f gterm clause fset" and
    s2 s2' :: "'f gterm clause fset \<times> 'f gterm clause fset"

  obtain U\<^sub>r U\<^sub>f\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (U\<^sub>r, U\<^sub>f\<^sub>f)"
    by fastforce

  assume "?match \<C>1 s1 N s2"
  then obtain U\<^sub>f where
    s1_def: "s1 = N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f" and
    U\<^sub>f_spec: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. \<exists>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f. ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
      (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)"
    unfolding s2_def ord_res_1_matches_ord_res_2.simps by metis

  have U\<^sub>f_unproductive: "\<forall>C\<^sub>f |\<in>| U\<^sub>f. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
  proof (intro ballI)
    fix C\<^sub>f
    assume "C\<^sub>f |\<in>| U\<^sub>f"
    hence "C\<^sub>f \<noteq> sfac C\<^sub>f"
      using U\<^sub>f_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>f"
      using nex_strictly_maximal_pos_lit_if_neq_sfac by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C\<^sub>f = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  have Interp_eq: "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C"
    using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)" "fset U\<^sub>f", folded union_fset,
        OF finite_fset finite_fset U\<^sub>f_unproductive] .

  assume step2: "ord_res_2 N s2 s2'"

  show "(\<exists>s1'. ord_res_1\<^sup>+\<^sup>+ s1 s1' \<and> ?match \<C>1 s1' N s2') \<or>
       ?match \<C>1 s1 N s2' \<and> ?order2 (?measure2 N s2') (?measure2 N s2)"
    using step2[unfolded s2_def]
  proof (cases N "(U\<^sub>r, U\<^sub>f\<^sub>f)" s2' rule: ord_res_2.cases)
    case (factoring C L U\<^sub>f\<^sub>f')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
      using factoring by metis

    hence
      C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
      C_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> C" and
      C_least: "\<forall>y|\<in>|N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f. y \<noteq> C \<longrightarrow>
        \<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by simp_all

    have C_false_in_s1: "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C"
      unfolding s1_def Interp_eq
      using C_false .

    obtain A :: "'f gterm" where
      L_def: "L = Pos A"
      using \<open>is_pos L\<close> by (metis Pos_atm_of_iff)

    define C\<^sub>0 where
      "C\<^sub>0 = {#K \<in># C. K \<noteq> L#}"

    obtain n where "count C L = Suc (Suc n)"
      using pos_lit_not_greatest_if_maximal_in_least_false_clause[of "N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" C]
      using C_least_false[unfolded is_least_false_clause_def]
      using \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L C\<close>
      by (metis Suc_n_not_le_n count_eq_zero_iff is_pos_def
          linorder_lit.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset
          linorder_lit.is_maximal_in_mset_iff not0_implies_Suc numeral_2_eq_2)

    hence C_eq: "C = C\<^sub>0 + replicate_mset (Suc (Suc n)) L"
      by (metis C\<^sub>0_def add.commute filter_mset_eq filter_mset_neq multiset_partition
          removeAll_mset_filter_mset)

    have "\<exists>!m. is_greatest_in_set
      {m. \<exists>C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f} m"
    proof (rule ex1_greatest_in_set)
      have "finite {m. m \<le> n \<and> (\<exists>C\<^sub>f|\<in>|N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f)}"
        by simp
      
      have "(ord_res.ground_factoring ^^ m) C C'' \<Longrightarrow> m \<le> size C" for m C C''
      proof (induction "size C" arbitrary: m C C'')
        case 0
        then show ?case
          apply (cases m)
          apply simp_all
          by (metis ex1_sfac_eq_factoring_chain relpowp.simps(2) relpowp_Suc_D2 sfac_mempty)
      next
        case (Suc x)
        note prems = Suc.prems

        obtain L C' where C_def: "C = add_mset L C'"
          using \<open>Suc x = size C\<close> by (metis size_eq_Suc_imp_eq_union)
        hence "x = size C'"
          using \<open>Suc x = size C\<close> by simp

        show ?case
        proof (cases m)
          case 0
          then show ?thesis
            by simp
        next
          case (Suc nat)
          show ?thesis
            using Suc
            by (smt (verit, ccfv_SIG) Suc.hyps(1) Suc.hyps(2) Suc_leI \<open>x = size C'\<close> diff_Suc_1
                le_imp_less_Suc ord_res.ground_factoring.cases prems relpowp_Suc_D2 size_add_mset)
        qed
      qed
      hence "
        {m. \<exists>C\<^sub>f|\<in>|N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f} =
        {m. \<exists>C\<^sub>f|\<in>|N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f \<and> m \<le> size C}"
        by blast
      thus "finite {m. \<exists>C\<^sub>f|\<in>|N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f}"
        using finite_nat_set_iff_bounded_le by auto
    next
      have "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f \<and> (ord_res.ground_factoring ^^ 0) C C"
        using C_in by simp
      thus "{m. \<exists>C\<^sub>f|\<in>|N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f} \<noteq> {}"
        by blast
    qed

    then obtain m :: nat where
      m_greatest: "is_greatest_in_set
        {m. \<exists>C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f. (ord_res.ground_factoring ^^ m) C C\<^sub>f} m"
      by blast

    then obtain C\<^sub>f where
      "C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f" and
      "(ord_res.ground_factoring ^^ m) C C\<^sub>f"
      by (smt (verit, best) is_greatest_in_set_iff mem_Collect_eq)

    have "\<not> (Suc n < m)"
    proof (rule notI)
      assume "Suc n < m"
      then obtain m' :: nat where m_def: "m = Suc n + Suc m'"
        using less_natE by (metis add_Suc_right)

      moreover have "(ord_res.ground_factoring ^^ Suc n) C (add_mset L C\<^sub>0)"
      proof -
        have "(ord_res.ground_factoring ^^ Suc n) C (C\<^sub>0 + replicate_mset (Suc 0) L)"
          using \<open>ord_res.is_maximal_lit L C\<close>
          unfolding C_eq L_def
          using ground_factorings_replicate_max_pos_lit by fastforce
        thus ?thesis
          by simp
      qed

      ultimately have "(ord_res.ground_factoring ^^ Suc m') (add_mset L C\<^sub>0) C\<^sub>f"
        using \<open>(ord_res.ground_factoring ^^ m) C C\<^sub>f\<close>
        using relpowp_plus_of_right_unique
        by (metis ord_res.unique_ground_factoring right_unique_iff)

      hence "\<exists>x. ord_res.ground_factoring (add_mset L C\<^sub>0) x"
        by (metis relpowp_Suc_D2)

      thus False
        using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
        by (metis C\<^sub>0_def ex1_sfac_eq_factoring_chain sfac_spec_if_pos_lit_is_maximal)
    qed
    hence "m \<le> Suc n"
      by presburger

    moreover have "m \<noteq> Suc n"
    proof (rule notI)
      assume "m = Suc n"
      hence "(ord_res.ground_factoring ^^ Suc n) C C\<^sub>f"
        using \<open>(ord_res.ground_factoring ^^ m) C C\<^sub>f\<close> by argo

      hence "ord_res.is_maximal_lit L C\<^sub>f" and "count C\<^sub>f L = Suc 0"
        using ord_res.full_ground_factorings_reduces_maximal_pos_lit[
            OF _ \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L C\<close> \<open>count C L = Suc (Suc n)\<close>]
        by simp_all

      hence "\<nexists>C\<^sub>f'. ord_res.ground_factoring C\<^sub>f C\<^sub>f'"
        using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
        by (metis Suc_n_not_le_n linorder_lit.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset
            nex_strictly_maximal_pos_lit_if_factorizable numeral_2_eq_2)

      hence "C\<^sub>f = sfac C\<^sub>f"
        using factorizable_if_neq_sfac by metis

      have "C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> C\<^sub>f |\<in>| U\<^sub>f"
        using \<open>C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f\<close> by simp
      thus False
      proof (elim disjE)
        assume "C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"

        have "C\<^sub>f \<noteq> C"
          using \<open>count C L = Suc (Suc n)\<close> \<open>count C\<^sub>f L = Suc 0\<close> by auto

        have "multp\<^sub>H\<^sub>O (\<prec>\<^sub>l) C\<^sub>f C"
          using \<open>ord_res.is_maximal_lit L C\<^sub>f\<close> \<open>count C\<^sub>f L = Suc 0\<close>
          using \<open>ord_res.is_maximal_lit L C\<close> \<open>count C L = Suc (Suc n)\<close>
          using linorder_lit.multp\<^sub>H\<^sub>O_if_same_maximal_and_count_lt
          by simp
        hence "C\<^sub>f \<prec>\<^sub>c C"
          by (simp add: multp_eq_multp\<^sub>H\<^sub>O)

        hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C\<^sub>f \<TTurnstile> C\<^sub>f"
          using C_least_false \<open>C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> \<open>C\<^sub>f \<noteq> C\<close>
          by (auto simp: is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff)

        hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> C\<^sub>f"
          using \<open>C\<^sub>f \<prec>\<^sub>c C\<close> ord_res.entailed_clause_stays_entailed by metis

        moreover have "set_mset C\<^sub>f = set_mset C"
          using \<open>(ord_res.ground_factoring ^^ m) C C\<^sub>f\<close>
          by (metis ground_factorings_preserves_sfac relpowp_imp_rtranclp set_mset_sfac)

        ultimately have "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> C"
          by (simp add: true_cls_def)

        with C_false show False
          by contradiction
      next
        assume "C\<^sub>f |\<in>| U\<^sub>f"
        hence "C\<^sub>f \<noteq> sfac C\<^sub>f"
          using U\<^sub>f_spec by metis
        thus False
          using \<open>C\<^sub>f = sfac C\<^sub>f\<close> by contradiction
      qed
    qed

    ultimately have "m \<le> n"
      by presburger

    then obtain k where n_def: "n = m + k"
      using le_Suc_ex by blast

    thm ord_res_1.factoring[of s1 C\<^sub>f L]

    thm ground_factorings_replicate_max_pos_lit[of C\<^sub>0 n A m, simplified, unfolded n_def, simplified]

    have "C\<^sub>f = C\<^sub>0 + replicate_mset (Suc (Suc k)) (Pos A)"
    proof -
      have  "(ord_res.ground_factoring ^^ m) C (C\<^sub>0 + replicate_mset (Suc (Suc k)) (Pos A))"
        using \<open>ord_res.is_maximal_lit L C\<close> ground_factorings_replicate_max_pos_lit[of C\<^sub>0 n A m]
        by (simp add: C_eq L_def n_def)
      thus ?thesis
        using \<open>(ord_res.ground_factoring ^^ m) C C\<^sub>f\<close>
        by (metis ord_res.unique_ground_factoring Uniq_relpowp)
    qed

    hence "C\<^sub>0 + replicate_mset (Suc (Suc k)) (Pos A) |\<in>| s1"
      using \<open>C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f\<close> s1_def by argo

    define factorized_C where
      "factorized_C = (\<lambda>m. C\<^sub>0 + replicate_mset (Suc (Suc n - m)) (Pos A))"

    have factorized_C_spec: "\<And>m. m \<le> Suc n \<Longrightarrow> (ord_res.ground_factoring ^^ m) C (factorized_C m)"
      using \<open>ord_res.is_maximal_lit L C\<close> ground_factorings_replicate_max_pos_lit[of C\<^sub>0 n A]
      by (simp add: C_eq L_def n_def factorized_C_def)

    have set_mset_factorized_C: "\<And>i. set_mset (factorized_C i) = set_mset C"
      by (simp add: factorized_C_def C_eq L_def)

    have factorized_C_strict_subset:
      "\<And>i1 i2. i1 \<le> Suc n \<Longrightarrow> i2 \<le> Suc n \<Longrightarrow> factorized_C i1 \<subset># factorized_C i2 \<longleftrightarrow> i1 > i2"
      unfolding factorized_C_def by auto
    hence factorized_C_less_cls:
      "\<And>i1 i2. i1 \<le> Suc n \<Longrightarrow> i2 \<le> Suc n \<Longrightarrow> factorized_C i1 \<prec>\<^sub>c factorized_C i2 \<longleftrightarrow> i1 > i2"
      by (metis linorder_cls.not_less_iff_gr_or_eq linorder_neqE_nat strict_subset_implies_multp)

    have factorized_C_0: "factorized_C 0 = C"
      unfolding factorized_C_def C_eq L_def by simp

    have factorized_C_Suc_lt_C: "\<And>i. factorized_C (Suc i) \<prec>\<^sub>c C"
      unfolding factorized_C_def C_eq L_def
      by (metis add_diff_cancel_right' diff_diff_left not_less_eq replicate_mset_subset_iff_lt
          strict_subset_implies_multp subset_mset.add_strict_left_mono zero_less_Suc zero_less_diff)

    have factorized_C_true_iff_C_true: "\<And>I i. I \<TTurnstile> factorized_C i \<longleftrightarrow> I \<TTurnstile> C"
      by (simp add: set_mset_factorized_C true_cls_def)

    have factorized_C_le_C: "\<And>i. factorized_C i \<preceq>\<^sub>c C"
      by (metis factorized_C_0 factorized_C_Suc_lt_C linorder_cls.le_less_linear
          linorder_cls.not_less_iff_gr_or_eq not0_implies_Suc)

    have factorized_C_Suc_not_in: "factorized_C (Suc i) |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" for i
    proof (rule notI)
      assume "factorized_C (Suc i) |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
      thus False
        using C_least_false
        by (metis (no_types, lifting) factorized_C_Suc_lt_C is_least_false_clause_def
            linorder_cls.is_least_in_ffilter_iff linorder_cls.not_less_iff_gr_or_eq
            ord_res.entailed_clause_stays_entailed set_mset_factorized_C true_cls_def)
    qed

    have "factorized_C m = C\<^sub>f"
    proof -
      have  "(ord_res.ground_factoring ^^ m) C (C\<^sub>0 + replicate_mset (Suc (Suc k)) (Pos A))"
        using \<open>ord_res.is_maximal_lit L C\<close> ground_factorings_replicate_max_pos_lit[of C\<^sub>0 n A m]
        by (simp add: C_eq L_def n_def)
      moreover have "C\<^sub>0 + replicate_mset (Suc (Suc k)) (Pos A) = factorized_C m"
        unfolding factorized_C_def n_def by simp
      ultimately show ?thesis
        using \<open>(ord_res.ground_factoring ^^ m) C C\<^sub>f\<close>
        by (metis ord_res.unique_ground_factoring Uniq_relpowp)
    qed

    hence "factorized_C m |\<in>| s1"
      using \<open>C\<^sub>f |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f\<close> s1_def by argo

    define factorized_Cs where
      "factorized_Cs = (\<lambda>k. (\<lambda>i. factorized_C (m + i)) |`| fset_upto 0 k)"

    have steps1: "kk \<le> Suc k \<Longrightarrow> (ord_res_1 ^^ kk) s1 (s1 |\<union>| factorized_Cs kk)" for kk
    proof (induction kk)
      case 0
      show ?case
        using \<open>factorized_C m |\<in>| s1\<close> by (auto simp: factorized_Cs_def)
    next
      case (Suc kk')
      hence "kk' \<le> k"
        by presburger
      hence "m + kk' \<le> Suc n"
        using n_def by presburger

      have "factorized_C (m + kk') |\<in>| (\<lambda>i. factorized_C (m + i)) |`| fset_upto 0 kk'"
        by simp

      have "ord_res.is_maximal_lit L (factorized_C (m + kk'))"
        using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
        by (metis \<open>count C L = Suc (Suc n)\<close> diff_is_0_eq factorized_C_def factorized_C_spec
             nat_le_linear
            ord_res.ground_factorings_reduces_maximal_pos_lit(1))

      have factorized_Cs_unproductive:
        "ord_res.production (fset (s1 |\<union>| factorized_Cs kk')) x = {}"
        if "x |\<in>| factorized_Cs kk'" for x
      proof -
        from that obtain i where "i \<le> kk'" and x_def: "x = factorized_C (m + i)"
          unfolding factorized_Cs_def by force
        with \<open>kk' \<le> k\<close> have "i \<le> k"
          by presburger
        hence x_eq: "x = C\<^sub>0 + replicate_mset (Suc (Suc (k - i))) (Pos A)"
          unfolding factorized_C_def n_def x_def
          apply simp
          by (simp add: Suc_diff_le)

        moreover have "ord_res.is_maximal_lit (Pos A) x"
          using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
          by (smt (verit, ccfv_SIG) L_def Suc_diff_le Suc_leD Suc_le_mono
              \<open>(ord_res.ground_factoring ^^ m) C C\<^sub>f\<close>
              \<open>C\<^sub>f = C\<^sub>0 + replicate_mset (Suc (Suc k)) (Pos A)\<close>
              \<open>count C L = Suc (Suc n)\<close> \<open>i \<le> k\<close> \<open>m \<le> n\<close> add_diff_cancel_left' n_def
              ord_res.ground_factorings_reduces_maximal_pos_lit(1)
              ord_res.ground_factorings_reduces_maximal_pos_lit(2)
              ground_factorings_replicate_max_pos_lit x_eq)

        ultimately have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L x"
          using ground_factoring_replicate_max_pos_lit
            nex_strictly_maximal_pos_lit_if_factorizable
          by metis

        then show ?thesis
          using unproductive_if_nex_strictly_maximal_pos_lit by metis
      qed

      have "ord_res_1 (s1 |\<union>| factorized_Cs kk') (s1 |\<union>| factorized_Cs (Suc kk'))"
      proof (rule ord_res_1.factoring)
        show "linorder_cls.is_least_in_fset {|C |\<in>| s1 |\<union>| factorized_Cs kk'.
            \<not> ord_res_Interp (fset (s1 |\<union>| factorized_Cs kk')) C \<TTurnstile> C|} (factorized_C (m + kk'))"
          unfolding linorder_cls.is_least_in_ffilter_iff
        proof (intro conjI ballI impI)
          show "factorized_C (m + kk') |\<in>| s1 |\<union>| factorized_Cs kk'"
            unfolding factorized_Cs_def by simp
        next
          show "\<not> ord_res_Interp (fset (s1 |\<union>| factorized_Cs kk')) (factorized_C (m + kk')) \<TTurnstile>
            factorized_C (m + kk')"
          proof (rule notI)
            assume "ord_res_Interp (fset (s1 |\<union>| factorized_Cs kk')) (factorized_C (m + kk')) \<TTurnstile>
              factorized_C (m + kk')"
            hence "ord_res_Interp (fset s1) (factorized_C (m + kk')) \<TTurnstile> factorized_C (m + kk')"
              using Interp_union_unproductive factorized_Cs_unproductive by simp

            moreover have "\<not> ord_res_Interp (fset s1) (factorized_C (m + kk')) \<TTurnstile>
              factorized_C (m + kk')"
              unfolding factorized_C_true_iff_C_true
              by (metis C_false_in_s1 factorized_C_le_C factorized_C_true_iff_C_true
                  ord_res.entailed_clause_stays_entailed
                  linorder_cls.dual_order.not_eq_order_implies_strict)

            ultimately show False
              by contradiction
          qed
        next
          fix y
          assume
            y_in: "y |\<in>| s1 |\<union>| factorized_Cs kk'" and
            y_neq: "y \<noteq> factorized_C (m + kk')" and
            y_false: "\<not> ord_res_Interp (fset (s1 |\<union>| factorized_Cs kk')) y \<TTurnstile> y"

          from y_false have y_false': "\<not> ord_res_Interp (fset s1) y \<TTurnstile> y"
            using Interp_union_unproductive factorized_Cs_unproductive by simp
          hence y_false'': "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> y"
            using Interp_union_unproductive U\<^sub>f_unproductive s1_def by simp

          from y_in have "y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> y |\<in>| U\<^sub>f \<or> y |\<in>| factorized_Cs kk'"
            unfolding s1_def by simp
          thus "factorized_C (m + kk') \<prec>\<^sub>c y"
          proof (elim disjE)
            assume "y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
            have "C \<preceq>\<^sub>c y"
              using C_least \<open>y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> y_false'' by force

            moreover have "factorized_C (m + kk') \<preceq>\<^sub>c C"
              using factorized_C_le_C by metis

            ultimately show ?thesis
              using y_neq by order
          next
            assume "y |\<in>| U\<^sub>f"
            then obtain y' where "y' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
              "ord_res.ground_factoring\<^sup>+\<^sup>+ y' y" and
              "y \<noteq> sfac y" and
              "sfac y |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) y'"
              using U\<^sub>f_spec[rule_format, of y] by metis

            have "y \<prec>\<^sub>c y'"
              using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ y' y\<close>
              by (smt (verit, ccfv_SIG) converse_tranclp_induct linorder_cls.dual_order.strict_trans
                  ord_res.ground_factoring_smaller_conclusion)

            show ?thesis
              using \<open>sfac y |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) y'\<close>
            proof (elim disjE)
              assume "sfac y |\<in>| U\<^sub>f\<^sub>f"

              hence "sfac y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
                by simp

              moreover obtain L where "is_pos L" and "ord_res.is_strictly_maximal_lit L (sfac y)"
                using \<open>y \<noteq> sfac y\<close> obtains_positive_greatest_lit_if_sfac_not_ident by metis

              ultimately have "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) (sfac y) \<TTurnstile> sfac y"
                using ord_res_Interp_entails_if_greatest_lit_is_pos by metis
                
              hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> sfac y"
                by (metis ord_res.entailed_clause_stays_entailed sfac_subset
                    strict_subset_implies_multp subset_mset.less_le)

              hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> y"
                by (simp add: true_cls_def)

              with y_false'' have False
                by contradiction

              thus ?thesis ..
            next
              assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) y'"
              hence "y' = C"
                using C_least_false by (metis Uniq_D Uniq_is_least_false_clause)

              then obtain i where "(ord_res.ground_factoring ^^ Suc i) C y"
                using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ y' y\<close>
                by (metis not0_implies_Suc not_gr_zero tranclp_power)

              hence "Suc i \<le> m"
                using m_greatest[unfolded is_greatest_in_set_iff, THEN conjunct2, simplified,
                    rule_format, of "Suc i"]
                using \<open>y |\<in>| U\<^sub>f\<close> le_eq_less_or_eq
                by auto

              hence "Suc i \<le> Suc n"
                using \<open>m \<le> Suc n\<close> by presburger

              hence "(ord_res.ground_factoring ^^ Suc i) C (factorized_C (Suc i))"
                using factorized_C_spec[of "Suc i"] by argo

              hence "y = factorized_C (Suc i)"
                using \<open>(ord_res.ground_factoring ^^ Suc i) C y\<close>
                by (metis Uniq_relpowp ord_res.unique_ground_factoring)

              thus ?thesis
                using factorized_C_less_cls[OF \<open>m + kk' \<le> Suc n\<close> \<open>Suc i \<le> Suc n\<close>] 
                by (metis \<open>Suc i \<le> m\<close> nless_le trans_le_add1 y_neq)
            qed
          next
            assume "y |\<in>| factorized_Cs kk'"
            then obtain i where
              "i \<le> kk'" and
              y_def: "y = factorized_C (m + i)"
              unfolding factorized_Cs_def by force
            hence "factorized_C (m + kk') \<subset># y"
              using \<open>i \<le> kk'\<close> y_neq
              by (simp add: factorized_C_def)
            thus ?thesis
              by (rule strict_subset_implies_multp)
          qed
        qed
      next
        show "ord_res.is_maximal_lit L (factorized_C (m + kk'))"
          using \<open>ord_res.is_maximal_lit L (factorized_C (m + kk'))\<close> .
      next
        show "is_pos L"
          using \<open>is_pos L\<close> .
      next
        show "ord_res.ground_factoring (factorized_C (m + kk')) (factorized_C (m + Suc kk'))"
          using ord_res.ground_factoringI[
              of "factorized_C (m + kk')" A _ "factorized_C (m + Suc kk')",
              OF _ _ \<open>ord_res.is_maximal_lit L (factorized_C (m + kk'))\<close>[unfolded L_def],
              simplified]
          unfolding factorized_C_def
          using \<open>kk' \<le> k\<close>
          by (simp add: Suc_diff_le n_def)
      next
        show "s1 |\<union>| factorized_Cs (Suc kk') =
          finsert (factorized_C (m + Suc kk')) (s1 |\<union>| factorized_Cs kk')"
          by (simp add: factorized_Cs_def)
      qed
        
      with Suc.IH show ?case
        using \<open>kk' \<le> k\<close> by auto
    qed

    define s1' where
      "s1' = s1 |\<union>| factorized_Cs (Suc k)"

    have "ord_res_1\<^sup>+\<^sup>+ s1 s1'"
      using steps1[of "Suc k", unfolded n_def, OF le_refl]
      by (metis s1'_def tranclp_power zero_less_Suc)

    moreover have "ord_res_1_matches_ord_res_2 s1' N s2'"
    proof -
      let ?U\<^sub>f' = "U\<^sub>f |\<union>| (\<lambda>i. factorized_C (m + i)) |`| fset_upto 1 k"

      have "sfac C = add_mset L C\<^sub>0"
        unfolding C\<^sub>0_def
        using sfac_spec_if_pos_lit_is_maximal \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L C\<close> by metis

      also have "\<dots> = factorized_C (m + Suc k)"
        unfolding factorized_C_def L_def n_def by simp

      finally have "sfac C = factorized_C (m + Suc k)" .

      moreover have "fset_upto 0 (Suc k) = finsert 0 (fset_upto 1 (Suc k))"
        by (induction k) auto

      ultimately have "s1' = N |\<union>| U\<^sub>r |\<union>| finsert (sfac C) U\<^sub>f\<^sub>f |\<union>| ?U\<^sub>f'"
        using \<open>factorized_C m |\<in>| s1\<close>
        unfolding s1'_def s1_def factorized_Cs_def
        by auto

      moreover have "\<exists>Ca |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert (sfac C) U\<^sub>f\<^sub>f.
        ord_res.ground_factoring\<^sup>+\<^sup>+ Ca C\<^sub>f \<and>
        C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
        (sfac C\<^sub>f |\<in>| finsert (sfac C) U\<^sub>f\<^sub>f \<or>
          is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert (sfac C) U\<^sub>f\<^sub>f) Ca)"
        if "C\<^sub>f |\<in>| ?U\<^sub>f'" for C\<^sub>f
      proof -
        from \<open>C\<^sub>f |\<in>| ?U\<^sub>f'\<close> have "C\<^sub>f |\<in>| U\<^sub>f \<or> C\<^sub>f |\<in>| (\<lambda>i. factorized_C (m + i)) |`| fset_upto 1 k"
          by simp
        thus ?thesis
        proof (elim disjE)
          assume "C\<^sub>f |\<in>| U\<^sub>f"
          thus ?thesis
            using U\<^sub>f_spec
            by (metis (mono_tags, lifting) C_least_false Uniq_D Uniq_is_least_false_clause
                finsert_iff funion_finsert_right ground_factorings_preserves_sfac
                tranclp_into_rtranclp)
        next
          assume "C\<^sub>f |\<in>| (\<lambda>i. factorized_C (m + i)) |`| fset_upto 1 k"
          then obtain i where i_in: "i |\<in>| fset_upto 1 k" and C\<^sub>f_def: "C\<^sub>f = factorized_C (m + i)"
            by auto

          from i_in have "1 \<le> i" and "i \<le> k"
            unfolding atomize_conj
            by (induction k) auto

          have "m + i \<le> Suc n"
            using \<open>i \<le> k\<close> n_def by presburger
          hence "(ord_res.ground_factoring ^^ (m + i)) C C\<^sub>f"
            using factorized_C_spec C\<^sub>f_def by metis

          show ?thesis
          proof (intro bexI conjI)
            show "C |\<in>| N |\<union>| U\<^sub>r |\<union>| finsert (sfac C) U\<^sub>f\<^sub>f"
              using C_in by simp
          next
            show "ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f"
              using \<open>1 \<le> i\<close> \<open>(ord_res.ground_factoring ^^ (m + i)) C C\<^sub>f\<close>
              by (metis One_nat_def Suc_le_eq add_gr_0 tranclp_power)
          next
            show "C\<^sub>f \<noteq> sfac C\<^sub>f"
              using \<open>(ord_res.ground_factoring ^^ (m + i)) C C\<^sub>f\<close>
              using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close>
              by (smt (z3) Suc_mono \<open>add_mset L C\<^sub>0 = factorized_C (m + Suc k)\<close>
                  \<open>count C L = Suc (Suc n)\<close> \<open>i \<le> k\<close> \<open>m + i \<le> Suc n\<close> \<open>sfac C = add_mset L C\<^sub>0\<close>
                  add_Suc_right add_diff_cancel_left' diff_is_0_eq factorized_C_spec
                  ground_factorings_preserves_sfac group_cancel.add1 le_antisym
                  mono_nat_linear_lb n_def not_less_eq_eq
                  ord_res.ground_factorings_reduces_maximal_pos_lit(2) plus_1_eq_Suc
                  relpowp_imp_rtranclp)
          next
            have "ord_res.ground_factoring\<^sup>*\<^sup>* C C\<^sub>f"
              using \<open>(ord_res.ground_factoring ^^ (m + i)) C C\<^sub>f\<close>
              by (metis relpowp_imp_rtranclp)
            hence "sfac C = sfac C\<^sub>f"
              using ground_factorings_preserves_sfac by metis
            hence "sfac C\<^sub>f |\<in>| finsert (sfac C) U\<^sub>f\<^sub>f"
              by simp
            thus "sfac C\<^sub>f |\<in>| finsert (sfac C) U\<^sub>f\<^sub>f \<or>
              is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| finsert (sfac C) U\<^sub>f\<^sub>f) C" ..
          qed
        qed
      qed

      ultimately show ?thesis
        unfolding factoring ord_res_1_matches_ord_res_2.simps by metis
    qed

    ultimately show ?thesis
      by metis
  next
    case (resolution C L D CD U\<^sub>r')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
      using resolution by argo
    hence
      C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
      C_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) C \<TTurnstile> C" and
      C_least: "\<forall>y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f. y \<noteq> C \<longrightarrow>
        \<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by simp_all

    define s1' where
      "s1' = finsert CD s1"

    have "ord_res_1\<^sup>+\<^sup>+ s1 s1'"
    proof (rule tranclp.r_into_trancl)
      show "ord_res_1 s1 s1'"
      proof (rule ord_res_1.resolution)
        show "linorder_cls.is_least_in_fset {|C |\<in>| s1. \<not> ord_res_Interp  (fset s1) C \<TTurnstile> C|} C"
          unfolding linorder_cls.is_least_in_ffilter_iff
        proof (intro conjI ballI impI)
          show "C |\<in>| s1"
            using C_in by (simp add: s1_def)
        next
          show "\<not> ord_res_Interp (fset s1) C \<TTurnstile> C"
            unfolding s1_def Interp_eq
            using C_false .
        next
          fix y assume "y |\<in>| s1" and "y \<noteq> C" and y_false: "\<not> ord_res_Interp (fset s1) y \<TTurnstile> y"

          have y_false': "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> y"
            using y_false unfolding s1_def Interp_eq .

          have "y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> y |\<in>| U\<^sub>f"
            using \<open>y |\<in>| s1\<close> by (simp add: s1_def)

          thus "C \<prec>\<^sub>c y"
          proof (elim disjE)
            assume "y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
            thus "C \<prec>\<^sub>c y"
              using \<open>y \<noteq> C\<close> y_false' C_least by metis
          next
            assume "y |\<in>| U\<^sub>f"
            then obtain y' where
              "y' |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
              "ord_res.ground_factoring\<^sup>+\<^sup>+ y' y" and
              "y \<noteq> sfac y" and
              "sfac y |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) y'"
              using U\<^sub>f_spec by metis

            show "C \<prec>\<^sub>c y"
              using \<open>sfac y |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) y'\<close>
            proof (elim disjE)
              assume "sfac y |\<in>| U\<^sub>f\<^sub>f"
              hence "sfac y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
                by simp

              have "sfac y \<prec>\<^sub>c y"
                using \<open>y \<noteq> sfac y\<close> sfac_subset[of y]
                by (simp add: strict_subset_implies_multp)

              moreover have "C \<preceq>\<^sub>c sfac y"
              proof (cases "sfac y = C")
                case True
                thus ?thesis
                  by simp
              next
                case False

                have sfac_y_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) (sfac y) \<TTurnstile> sfac y"
                proof (rule notI)
                  assume "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) (sfac y) \<TTurnstile> sfac y"
                  hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> sfac y"
                    using \<open>sfac y \<prec>\<^sub>c y\<close> ord_res.entailed_clause_stays_entailed by metis
                  hence "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) y \<TTurnstile> y"
                    by (simp add: true_cls_def)
                  with y_false' show False
                    by contradiction
                qed

                show ?thesis
                  using C_least[rule_format, OF \<open>sfac y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> False sfac_y_false]
                  by order
              qed

              ultimately show "C \<prec>\<^sub>c y"
                by order
            next
              assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) y'"
              hence "y' = C"
                using C_least_false by (metis Uniq_is_least_false_clause Uniq_D)

              moreover have "\<exists>L. ord_res.is_maximal_lit L y' \<and> is_pos L"
                using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ y' y\<close>
                by (metis is_pos_def ord_res.ground_factoring.cases tranclpD)

              moreover have "\<nexists>L. ord_res.is_maximal_lit L C \<and> is_pos L"
                using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_neg L\<close>
                by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)

              ultimately have False
                by metis

              thus "C \<prec>\<^sub>c y" ..
            qed
          qed
        qed
      next
        show "ord_res.is_maximal_lit L C"
          using resolution by argo
      next
        show "is_neg L"
          using resolution by argo
      next
        show "D |\<in>| s1"
          using resolution s1_def by simp
      next
        show "D \<prec>\<^sub>c C"
          using resolution by argo
      next
        have "ord_res.production (fset s1) D = ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) D"
          unfolding s1_def
          using production_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f)" "fset U\<^sub>f"]
          using U\<^sub>f_unproductive \<open>D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close>
          by (metis finite_fset sup_fset.rep_eq)
        thus "ord_res.production (fset s1) D = {atm_of L}"
          using resolution by argo
      next
        show "ord_res.ground_resolution C D CD"
          using resolution by argo
      next
        show "s1' = finsert CD s1"
          unfolding s1'_def ..
      qed
    qed

    moreover have "ord_res_1_matches_ord_res_2 s1' N s2'"
    proof -
      have "finsert CD (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f) = N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
        by simp

      moreover have "\<exists>C |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f.
        ord_res.ground_factoring\<^sup>+\<^sup>+ C C\<^sub>f \<and> C\<^sub>f \<noteq> sfac C\<^sub>f \<and>
        (sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C)"
        if "C\<^sub>f |\<in>| U\<^sub>f" for C\<^sub>f
      proof -
        from that obtain x where
          "x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f" and
          "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f" and
          "C\<^sub>f \<noteq> sfac C\<^sub>f" and
          "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
          using U\<^sub>f_spec by metis

        show ?thesis
        proof (intro bexI conjI)
          show "x |\<in>| N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
            using \<open>x |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close> by simp
        next
          show "ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f"
            using \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> .
        next
          show "C\<^sub>f \<noteq> sfac C\<^sub>f"
            using \<open>C\<^sub>f \<noteq> sfac C\<^sub>f\<close> .
        next
          show "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| finsert CD U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
            using \<open>sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f \<or> is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x\<close>
          proof (elim disjE)
            assume "sfac C\<^sub>f |\<in>| U\<^sub>f\<^sub>f"
            thus ?thesis
              by argo
          next
            assume "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) x"
            hence "x = C"
              using C_least_false
              by (metis Uniq_D Uniq_is_least_false_clause)
            hence False
              by (metis \<open>C\<^sub>f \<noteq> sfac C\<^sub>f\<close> \<open>ord_res.ground_factoring\<^sup>+\<^sup>+ x C\<^sub>f\<close> is_pos_def
                  linorder_lit.Uniq_is_maximal_in_mset local.resolution(3) local.resolution(4)
                  ord_res.ground_factorings_preserves_maximal_literal sfac_spec the1_equality'
                  tranclp_into_rtranclp)
            thus ?thesis ..
          qed
        qed
      qed

      ultimately show ?thesis
        unfolding s1'_def s1_def resolution
        unfolding ord_res_1_matches_ord_res_2.simps
        by metis
    qed

    ultimately show ?thesis
      by metis
  qed
qed


subsubsection \<open>ORD-RES-3 (full resolve)\<close>

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

definition ground_resolution where
  "ground_resolution D C CD = ord_res.ground_resolution C D CD"

lemma Uniq_ground_resolution: "\<exists>\<^sub>\<le>\<^sub>1DC. ground_resolution D C DC"
  by (simp add: ground_resolution_def ord_res.unique_ground_resolution)

lemma ground_resolution_terminates: "wfP (ground_resolution D)\<inverse>\<inverse>"
proof (rule wfP_if_convertible_to_wfP)
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


text \<open>Exhaustive resolution\<close>

definition eres where
  "eres D C = (THE DC. full_run (ground_resolution D) C DC)"

lemma
  assumes
    stuck: "\<nexists>DC. ground_resolution D C DC"
  shows "eres D C = C"
proof -
  have "(ground_resolution D)\<^sup>*\<^sup>* C C"
    by auto

  with stuck have "full_run (ground_resolution D) C C"
    unfolding full_run_def by argo

  moreover have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 y. full_run (ground_resolution D) C y"
    by (metis Uniq_ground_resolution Uniq_full_run)

  ultimately show ?thesis
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

lemma eres_eq_after_ground_resolution:
  assumes "ground_resolution D C DC"
  shows "eres D C = eres D DC"
  using assms
  by (metis (no_types, opaque_lifting) Uniq_def Uniq_full_run Uniq_ground_resolution
      converse_rtranclpE ex1_eres_eq_full_run_ground_resolution full_run_def)

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
  shows "\<exists>n m A D' C'. Suc m \<ge> n \<and>
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
    linorder_lit.is_maximal_in_mset C (Neg A) \<and>
    D = add_mset (Pos A) D' \<and>
    C = replicate_mset (Suc m) (Neg A) + C' \<and> Neg A \<notin># C' \<and>
    DnC = repeat_mset n D' + replicate_mset (Suc m - n) (Neg A) + C'"
proof -
  from assms obtain n where "n > 0" and "(ground_resolution D ^^ n) C DnC"
    by (meson tranclp_power)
  thus ?thesis
    using assms relpowp_ground_resolutionD by fast
qed

lemma member_mset_repeat_msetD: "L \<in># repeat_mset n M \<Longrightarrow> L \<in># M"
  by (induction n) auto

lemma eres_not_identD:
  assumes "eres D C \<noteq> C"
  shows "\<exists>m A D' C'.
    linorder_lit.is_greatest_in_mset D (Pos A) \<and>
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
    "ord_res.is_strictly_maximal_lit (Pos A) D" and
    "ord_res.is_maximal_lit (Neg A) C" and
    "D = add_mset (Pos A) D'" and
    "C = replicate_mset (Suc m) (Neg A) + C'" and
    "Neg A \<notin># C'" and
    "eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'"
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
        unfolding \<open>eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'\<close>
        by (metis Zero_not_Suc count_replicate_mset in_countE union_iff)
      thus "\<not> Neg A \<prec>\<^sub>l L"
      proof (elim disjE)
        assume "L \<in># repeat_mset (Suc n) D'"
        hence "L \<in># D'"
          using member_mset_repeat_msetD by metis
        hence "L \<prec>\<^sub>l Pos A"
          using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
          unfolding \<open>D = add_mset (Pos A) D'\<close> linorder_lit.is_greatest_in_mset_iff
          by simp
        also have "Pos A \<prec>\<^sub>l Neg A"
          by simp
        finally show ?thesis
          by order
      next
        assume "L \<in># C'"
        then show ?thesis
          using \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> \<open>L \<noteq> Neg A\<close>
            \<open>ord_res.is_maximal_lit (Neg A) C\<close> linorder_lit.is_maximal_in_mset_iff by auto
      qed
    qed

    moreover have "D \<prec>\<^sub>c eres D C"
      using \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
      using \<open>ord_res.is_maximal_lit (Neg A) (eres D C)\<close>
      using linorder_lit.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal[of D "Pos A" "eres D C" "Neg A", simplified]
      using multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M by blast

    ultimately show "\<exists>x. ground_resolution D (eres D C) x"
      unfolding ground_resolution_def
      using \<open>D = add_mset (Pos A) D'\<close> \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
      using ord_res.ground_resolutionI[of "eres D C" A ERES' D D' "ERES' + D'"]
      by metis
  qed

  then have "m = n"
    using \<open>eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'\<close>
    using \<open>Suc n \<le> Suc m\<close> by auto

  then show ?thesis
    by (metis \<open>C = replicate_mset (Suc m) (Neg A) + C'\<close> \<open>D = add_mset (Pos A) D'\<close> \<open>Neg A \<notin># C'\<close>
        \<open>eres D C = repeat_mset (Suc n) D' + replicate_mset (Suc m - Suc n) (Neg A) + C'\<close>
        \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close> add.right_neutral add_0 add_diff_cancel_right'
        replicate_mset_0)
qed


inductive ord_res_3 where
  factoring: "
    is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    U\<^sub>f\<^sub>f' = finsert (sfac C) U\<^sub>f\<^sub>f \<Longrightarrow>
    ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f) (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f')" |

  resolution: "
    is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f)) D = {atm_of L} \<Longrightarrow>
    full_run (ground_resolution D) C DC \<Longrightarrow>
    U\<^sub>r\<^sub>r' = finsert DC U\<^sub>r\<^sub>r \<Longrightarrow>
    ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f) (U\<^sub>r\<^sub>r', U\<^sub>f\<^sub>f)"

fun ord_res_3_final where
  "ord_res_3_final N (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f) \<longleftrightarrow> ord_res_final (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f)"

inductive ord_res_3_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_3_load N N ({||}, {||})"

interpretation ord_res_3_semantics: semantics' where
  step = ord_res_3 and
  final = ord_res_3_final
proof unfold_locales
  fix N :: "'f gterm clause fset" and S3 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  obtain U\<^sub>r\<^sub>r U\<^sub>f\<^sub>f where S3_def: "S3 = (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f)"
    by force

  assume "ord_res_3_final N S3"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    by (simp add: S3_def ord_res_final_def)
  thus "finished (ord_res_3 N) S3"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
    hence "is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) {#}"
      using is_least_false_clause_mempty by metis
    hence "\<nexists>C L. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C \<and> linorder_lit.is_maximal_in_mset C L"
      by (metis Uniq_D Uniq_is_least_false_clause bot_fset.rep_eq fBex_fempty
          linorder_lit.is_maximal_in_mset_iff set_mset_empty)
    hence "\<nexists>S3'. ord_res_3 N S3 S3'"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def)
  next
    assume "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    hence "\<nexists>C. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
      unfolding ex_false_clause_def is_least_false_clause_def
      by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
          linorder_cls.is_least_in_fset_ffilterD(2))
    hence "\<nexists>S3'. ord_res_3 N S3 S3'"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def)
  qed
qed

interpretation ord_res_3_language: language' where
  step = ord_res_3 and
  final = ord_res_3_final and
  load = ord_res_3_load
  by unfold_locales

thm ord_res_1_matches_ord_res_2.simps

fun ord_res_2_matches_ord_res_3 where
  "ord_res_2_matches_ord_res_3 N\<^sub>2 (U\<^sub>r\<^sub>2, U\<^sub>e\<^sub>f\<^sub>2) N\<^sub>3 (U\<^sub>e\<^sub>r\<^sub>3, U\<^sub>e\<^sub>f\<^sub>3) \<longleftrightarrow>
    N\<^sub>2 = N\<^sub>3 \<and> U\<^sub>e\<^sub>f\<^sub>2 = U\<^sub>e\<^sub>f\<^sub>3 \<and> (\<exists>U\<^sub>p\<^sub>r\<^sub>3. U\<^sub>r\<^sub>2 = U\<^sub>p\<^sub>r\<^sub>3 |\<union>| U\<^sub>e\<^sub>r\<^sub>3 \<and>
    (\<forall>C\<^sub>r\<^sub>r |\<in>| U\<^sub>e\<^sub>r\<^sub>3. \<exists>C |\<in>| N\<^sub>3 |\<union>| U\<^sub>e\<^sub>r\<^sub>3 |\<union>| U\<^sub>e\<^sub>f\<^sub>3. \<exists>D |\<in>| N\<^sub>3 |\<union>| U\<^sub>e\<^sub>r\<^sub>3 |\<union>| U\<^sub>e\<^sub>f\<^sub>3.
      eres D C = C\<^sub>r\<^sub>r) \<comment> \<open>Is this specification of \<^term>\<open>C\<^sub>r\<^sub>r\<close> really necessary?\<close> \<and>
    (\<forall>C\<^sub>r |\<in>| U\<^sub>p\<^sub>r\<^sub>3. \<exists>C |\<in>| N\<^sub>3 |\<union>| U\<^sub>e\<^sub>r\<^sub>3 |\<union>| U\<^sub>e\<^sub>f\<^sub>3. \<exists>D |\<in>| N\<^sub>3 |\<union>| U\<^sub>e\<^sub>r\<^sub>3 |\<union>| U\<^sub>e\<^sub>f\<^sub>3.
      (ground_resolution D)\<^sup>+\<^sup>+ C C\<^sub>r \<and> C\<^sub>r \<noteq> eres D C\<^sub>r \<and>
      (eres D C\<^sub>r |\<in>| U\<^sub>e\<^sub>r\<^sub>3 \<longleftrightarrow> \<not> is_least_false_clause (N\<^sub>3 |\<union>| U\<^sub>e\<^sub>r\<^sub>3 |\<union>| U\<^sub>e\<^sub>f\<^sub>3) C)))"

lemma ord_res_2_final_iff_ord_res_3_final:
  assumes match: "ord_res_2_matches_ord_res_3 \<C>\<^sub>2 S\<^sub>2 \<C>\<^sub>3 S\<^sub>3"
  shows "ord_res_2_final \<C>\<^sub>2 S\<^sub>2 \<longleftrightarrow> ord_res_3_final \<C>\<^sub>3 S\<^sub>3"
proof -
  from match obtain N U\<^sub>r U\<^sub>p\<^sub>r U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f where
    state_simps: "\<C>\<^sub>2 = N" "\<C>\<^sub>3 = N" "S\<^sub>2 = (U\<^sub>r, U\<^sub>e\<^sub>f)" "S\<^sub>3 = (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" and
    U\<^sub>r_def: "U\<^sub>r = U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r" and
    U\<^sub>p\<^sub>r_spec: "\<forall>C\<^sub>r |\<in>| U\<^sub>p\<^sub>r. \<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
      (ground_resolution D)\<^sup>+\<^sup>+ C C\<^sub>r \<and> C\<^sub>r \<noteq> eres D C\<^sub>r \<and>
      (eres D C\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    by (elim ord_res_2_matches_ord_res_3.elims(2)) blast

  have U\<^sub>p\<^sub>r_unproductive: "\<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
  proof (intro ballI)
    fix C\<^sub>p\<^sub>r
    assume "C\<^sub>p\<^sub>r |\<in>| U\<^sub>p\<^sub>r"
    hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. C\<^sub>p\<^sub>r \<noteq> eres D C\<^sub>p\<^sub>r"
      using U\<^sub>p\<^sub>r_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>p\<^sub>r"
      using nex_strictly_maximal_pos_lit_if_neq_eres by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C\<^sub>p\<^sub>r = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f: "\<And>C.
    ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: U\<^sub>r_def funion_left_commute sup_commute)

  have "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) \<longleftrightarrow> ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
  proof (rule iffI)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    then obtain C where
      C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      C_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
      unfolding ex_false_clause_def by metis

    have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>p\<^sub>r"
      using C_in U\<^sub>r_def by auto
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    proof (elim disjE)
      assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      show ?thesis
        unfolding ex_false_clause_def
      proof (rule bexI)
        show "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          using \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
      next
        show "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
          using C_false unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f by argo
      qed
    next
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      then obtain D2 D1 where
        "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
        "C \<noteq> eres D1 C" and
        "eres D1 C |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2"
        using U\<^sub>p\<^sub>r_spec by metis

      show ?thesis
      proof (cases "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2")
        assume "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2"
        thus ?thesis
          using ex_false_clause_if_least_false_clause by metis
      next
        assume "\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2"
        hence "eres D1 C |\<in>| U\<^sub>e\<^sub>r"
          using \<open>(eres D1 C |\<in>| U\<^sub>e\<^sub>r) = (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2)\<close> by blast
        show ?thesis
        proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (eres D1 C) \<TTurnstile> eres D1 C")
          case eres_C_true: True

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

          have "ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (eres D1 C) \<TTurnstile> eres D1 C"
            using eres_C_true unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f .

          moreover have "eres D1 C \<prec>\<^sub>c C"
            using eres_le[of D1 C] \<open>C \<noteq> eres D1 C\<close> by order

          ultimately have "ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> eres D1 C"
            using ord_res.entailed_clause_stays_entailed by metis

          hence "ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
            unfolding true_cls_def
          proof (elim bexE)
            fix L
            assume
              L_in: "L \<in># eres D1 C" and
              L_true: "ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile>l L"

            from L_in have "L \<in># D' \<or> L \<in># C'"
              unfolding eres_D1_C_eq
              using member_mset_repeat_msetD by fastforce
            hence "L \<in># C"
              by (auto simp: \<open>C = repeat_mset (Suc n) D' + replicate_mset (m - n) (Neg A) + C'\<close>)
            with L_true show "\<exists>L \<in># C. ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile>l L"
              by metis
          qed

          with C_false have False
            unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f by contradiction

          thus ?thesis ..
        next
          case False

          moreover have "eres D1 C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>eres D1 C |\<in>| U\<^sub>e\<^sub>r\<close> by simp

          ultimately show "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
            unfolding ex_false_clause_def by metis
        qed
      qed
    qed
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      unfolding ex_false_clause_def
      unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f
      by (auto simp: U\<^sub>r_def)
  qed

  moreover have "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f \<or> {#} |\<in>| U\<^sub>r"
      by auto
    thus "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f"
      thus ?thesis
        by auto
    next
      have "{#} |\<notin>| U\<^sub>p\<^sub>r"
        using U\<^sub>p\<^sub>r_spec[rule_format, of "{#}"] not_tranclp_ground_resolution_mempty_right by auto
      moreover assume "{#} |\<in>| U\<^sub>r"
      ultimately show ?thesis
        by (simp add: U\<^sub>r_def)
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    then show "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      using U\<^sub>r_def by auto
  qed

  ultimately have "ord_res_final (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = ord_res_final (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    unfolding ord_res_final_def by argo

  thus "ord_res_2_final \<C>\<^sub>2 S\<^sub>2 \<longleftrightarrow> ord_res_3_final \<C>\<^sub>3 S\<^sub>3"
    unfolding state_simps by simp
qed

definition ord_res_2_measure where
  "ord_res_2_measure N s1 =
    (let (U\<^sub>r, U\<^sub>e\<^sub>f) = s1 in
    (if \<exists>C. is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C then
      The (is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))
    else
      {#}))"

lemma tranclp_if_relpowp: "n \<noteq> 0 \<Longrightarrow> (R ^^ n) x y \<Longrightarrow> R\<^sup>+\<^sup>+ x y"
  by (meson bot_nat_0.not_eq_extremum tranclp_power)

interpretation bisimulation_with_measuring_function' where
  step1 = ord_res_2 and final1 = ord_res_2_final and
  step2 = ord_res_3 and final2 = ord_res_3_final and
  match = ord_res_2_matches_ord_res_3 and
  measure1 = ord_res_2_measure and order1 = "(\<prec>\<^sub>c)" and
  measure2 = "\<lambda>_ _. ()" and order2 = "\<lambda>_ _. False"
proof unfold_locales
  show "wfP (\<prec>\<^sub>c)"
    using ord_res.wfP_less_cls .
next
  fix
    N2 N3 :: "'f gterm clause fset" and
    s2 s3 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  assume "ord_res_2_matches_ord_res_3 N2 s2 N3 s3" and "ord_res_2_final N2 s2"
  thus "ord_res_3_final N3 s3"
    using ord_res_2_final_iff_ord_res_3_final by metis
next
  fix
    N2 N3 :: "'f gterm clause fset" and
    s2 s3 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  assume "ord_res_2_matches_ord_res_3 N2 s2 N3 s3" and "ord_res_3_final N3 s3"
  thus "ord_res_2_final N2 s2"
    using ord_res_2_final_iff_ord_res_3_final by metis
next
  let
    ?match = ord_res_2_matches_ord_res_3 and
    ?measure = ord_res_2_measure and ?order = "(\<prec>\<^sub>c)"

  fix
    N2 N3 :: "'f gterm clause fset" and
    s2 s2' s3 :: "'f gterm clause fset \<times> 'f gterm clause fset"

  assume "?match N2 s2 N3 s3"
  then obtain N U\<^sub>r U\<^sub>p\<^sub>r U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f where
    Ns_def: "N2 = N" "N3 = N" and s2_def: "s2 = (U\<^sub>r, U\<^sub>e\<^sub>f)" and s3_def: "s3 = (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" and
    U\<^sub>r_def: "U\<^sub>r = U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r" and
    U\<^sub>e\<^sub>r_spec: "\<forall>C\<^sub>e\<^sub>r |\<in>| U\<^sub>e\<^sub>r. \<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. eres D C = C\<^sub>e\<^sub>r" and
    U\<^sub>p\<^sub>r_spec: "\<forall>C\<^sub>p\<^sub>r |\<in>| U\<^sub>p\<^sub>r. \<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
      (ground_resolution D)\<^sup>+\<^sup>+ C C\<^sub>p\<^sub>r \<and> C\<^sub>p\<^sub>r \<noteq> eres D C\<^sub>p\<^sub>r \<and>
      (eres D C\<^sub>p\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    by (elim ord_res_2_matches_ord_res_3.elims(2)) blast

  have U\<^sub>p\<^sub>r_unproductive: "\<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
  proof (intro ballI)
    fix C\<^sub>p\<^sub>r
    assume "C\<^sub>p\<^sub>r |\<in>| U\<^sub>p\<^sub>r"
    hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. C\<^sub>p\<^sub>r \<noteq> eres D C\<^sub>p\<^sub>r"
      using U\<^sub>p\<^sub>r_spec by metis
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C\<^sub>p\<^sub>r"
      using nex_strictly_maximal_pos_lit_if_neq_eres by metis
    thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C\<^sub>p\<^sub>r = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f:
    "ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) = ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: U\<^sub>r_def funion_left_commute sup_commute)

  have production_N_U\<^sub>r_U\<^sub>e\<^sub>f_production_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f:
    "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) = ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    apply (rule ext)
    using production_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f", OF U\<^sub>p\<^sub>r_unproductive]
    by (smt (z3) Collect_empty_eq U\<^sub>p\<^sub>r_unproductive U\<^sub>r_def Un_iff ord_res.production_unfold
        sup_commute sup_fset.rep_eq sup_left_commute)

  have "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    unfolding U\<^sub>r_def by auto

  assume "ord_res_2 N2 s2 s2'"
  hence "ord_res_2 N (U\<^sub>r, U\<^sub>e\<^sub>f) s2'"
    unfolding Ns_def s2_def .
  thus "(\<exists>s3'. (ord_res_3 N3)\<^sup>+\<^sup>+ s3 s3' \<and> ?match N2 s2' N3 s3') \<or>
    ?match N2 s2' N3 s3 \<and> ?order (?measure N2 s2') (?measure N2 s2)"
  proof (cases N "(U\<^sub>r, U\<^sub>e\<^sub>f)" s2' rule: ord_res_2.cases)
    case (factoring C L U\<^sub>e\<^sub>f')
    define s3' where
      "s3' = (U\<^sub>e\<^sub>r, finsert (sfac C) U\<^sub>e\<^sub>f)"

    have "(ord_res_3 N3)\<^sup>+\<^sup>+ s3 s3'"
    proof (rule tranclp.r_into_trancl)
      show "ord_res_3 N3 s3 s3'"
        unfolding Ns_def s3_def s3'_def
      proof (rule ord_res_3.factoring)
        show "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
        proof (rule is_least_false_clause_if_is_least_false_clause_in_union_unproductive)
          show "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r) C"
            using \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
            unfolding U\<^sub>r_def by (metis sup_assoc sup_commute)
        next
          show "\<forall>C|\<in>|U\<^sub>p\<^sub>r. ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
            using U\<^sub>p\<^sub>r_unproductive .
        next
          have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r"
            using \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff U\<^sub>r_def by auto

          moreover have "C |\<notin>| U\<^sub>p\<^sub>r"
          proof (rule notI)
            assume "C |\<in>| U\<^sub>p\<^sub>r"
            hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. C \<noteq> eres D C"
              using U\<^sub>p\<^sub>r_spec by metis
            hence "\<nexists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
              using nex_maximal_pos_lit_if_neq_eres by metis
            moreover have "\<exists>L. is_pos L \<and> ord_res.is_maximal_lit L C"
              using \<open>ord_res.is_maximal_lit L C\<close> \<open>is_pos L\<close> by metis
            ultimately show False
              by contradiction
          qed

          ultimately show "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            by simp
        qed
      next
        show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
      next
        show "is_pos L"
          using \<open>is_pos L\<close> .
      next
        show "finsert (sfac C) U\<^sub>e\<^sub>f = finsert (sfac C) U\<^sub>e\<^sub>f" ..
      qed
    qed

    moreover have "?match N2 s2' N3 s3'"
    proof -
      have "
        \<exists>Ca|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f. \<exists>D|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f.
          eres D Ca = C\<^sub>r\<^sub>r"
        if "C\<^sub>r\<^sub>r |\<in>| U\<^sub>e\<^sub>r" for C\<^sub>r\<^sub>r
        using U\<^sub>e\<^sub>r_spec[rule_format, OF that] by blast

      moreover have "
        \<exists>Ca|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f. \<exists>D|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f.
          (ground_resolution D)\<^sup>+\<^sup>+ Ca C\<^sub>r \<and> C\<^sub>r \<noteq> eres D C\<^sub>r \<and>
          (eres D C\<^sub>r |\<in>| U\<^sub>e\<^sub>r) = (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f) Ca)"
        if "C\<^sub>r |\<in>| U\<^sub>p\<^sub>r" for C\<^sub>r
      proof -
        from that obtain D1 D2 where
          "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>r" and
          "C\<^sub>r \<noteq> eres D1 C\<^sub>r" and
          "eres D1 C\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2)"
          using U\<^sub>p\<^sub>r_spec by metis

        show ?thesis
        proof (intro bexI conjI)
          show "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>r"
            using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>r\<close> .
        next
          show "C\<^sub>r \<noteq> eres D1 C\<^sub>r"
            using \<open>C\<^sub>r \<noteq> eres D1 C\<^sub>r\<close> .
        next
          show "eres D1 C\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f) D2"
            \<comment> \<open>This should be provable using the same argument as for
              \<^term>\<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close> above.\<close>
            sorry
        next
          show "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f"
            using \<open>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        next
          show "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f"
            using \<open>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        qed
      qed

      ultimately show ?thesis
        unfolding Ns_def \<open>s2' = (U\<^sub>r, U\<^sub>e\<^sub>f')\<close> U\<^sub>r_def \<open>U\<^sub>e\<^sub>f' = finsert (sfac C) U\<^sub>e\<^sub>f\<close> s3'_def
        unfolding ord_res_2_matches_ord_res_3.simps
        by blast
    qed

    ultimately show ?thesis
      by metis
  next
    case (resolution C L D DC U\<^sub>r')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      using resolution by argo

    hence C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by argo

    have "ground_resolution D C DC"
      using resolution by (simp add: ground_resolution_def)

    have "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof -
      have "D |\<notin>| U\<^sub>p\<^sub>r"
        using resolution U\<^sub>p\<^sub>r_unproductive \<open>N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by fastforce
      thus ?thesis
        using \<open>D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
        unfolding U\<^sub>r_def by simp
    qed

    obtain A :: "'f gterm" where
      L_def: "L = Neg A"
      using \<open>is_neg L\<close> by (cases L) simp_all

    show ?thesis
    proof (cases "eres D C = DC")
      case True

      define s3' where
        "s3' = (finsert (eres D C) U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)"

      have "(ord_res_3 N3)\<^sup>+\<^sup>+ s3 s3'"
      proof (rule tranclp.r_into_trancl)
        from C_in have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>p\<^sub>r"
          using U\<^sub>r_def by auto
        thus "ord_res_3 N3 s3 s3'"
        proof (elim disjE)
          assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          show ?thesis
            unfolding Ns_def s3_def s3'_def
          proof (rule ord_res_3.resolution)
            show "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
              using C_least_false U\<^sub>p\<^sub>r_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
                \<open>N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r = N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
                is_least_false_clause_if_is_least_false_clause_in_union_unproductive
              by metis
          next
            show "ord_res.is_maximal_lit L C"
              using \<open>ord_res.is_maximal_lit L C\<close> .
          next
            show "is_neg L"
              using \<open>is_neg L\<close> .
          next
            show "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
          next
            show "D \<prec>\<^sub>c C"
              using \<open>D \<prec>\<^sub>c C\<close> .
          next
            show "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}"
              using \<open>ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}\<close>
              unfolding production_N_U\<^sub>r_U\<^sub>e\<^sub>f_production_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f .
          next
            show "full_run (ground_resolution D) C (eres D C)"
              using ex1_eres_eq_full_run_ground_resolution by blast
          next
            show "finsert (eres D C) U\<^sub>e\<^sub>r = finsert (eres D C) U\<^sub>e\<^sub>r"
              by argo
          qed
        next
          assume "C |\<in>| U\<^sub>p\<^sub>r"
          show ?thesis
            unfolding Ns_def s3_def s3'_def
            apply (rule ord_res_3.resolution)
            \<comment> \<open>Find original resolvants using @{thm U\<^sub>p\<^sub>r_spec} as done under and prove assumptions
              w.r.t. to said resolvants.\<close>
            sorry
        qed
      qed

      moreover have "?match N2 s2' N3 s3'"
        unfolding Ns_def \<open>s2' = (U\<^sub>r', U\<^sub>e\<^sub>f)\<close> s3'_def ord_res_2_matches_ord_res_3.simps
      proof (intro conjI exI ballI)
        show "U\<^sub>r' = U\<^sub>p\<^sub>r |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r"
          unfolding \<open>U\<^sub>r' = finsert DC U\<^sub>r\<close> U\<^sub>r_def \<open>eres D C = DC\<close> by simp
      next
        fix C\<^sub>e\<^sub>r
        assume "C\<^sub>e\<^sub>r |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r"
        thus "\<exists>Ca |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          \<exists>D |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. eres D Ca = C\<^sub>e\<^sub>r"
          \<comment> \<open>Prove this only at the end if this specification from the matching relation is useful,
            otherwise, just delete it.\<close>
          sorry
      next
        fix C\<^sub>p\<^sub>r
        assume "C\<^sub>p\<^sub>r |\<in>| U\<^sub>p\<^sub>r"
        then obtain D1 D2 where
          "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>p\<^sub>r" and
          "C\<^sub>p\<^sub>r \<noteq> eres D1 C\<^sub>p\<^sub>r" and
          "eres D1 C\<^sub>p\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2)"
          using U\<^sub>p\<^sub>r_spec by metis

        show "\<exists>D2 |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          \<exists>D1 |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
            (ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>p\<^sub>r \<and> C\<^sub>p\<^sub>r \<noteq> eres D1 C\<^sub>p\<^sub>r \<and>
            (eres D1 C\<^sub>p\<^sub>r |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r \<longleftrightarrow>
              \<not> is_least_false_clause (N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2)"
        proof (intro bexI conjI)
          show "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>p\<^sub>r"
            using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>p\<^sub>r\<close> .
        next
          show "C\<^sub>p\<^sub>r \<noteq> eres D1 C\<^sub>p\<^sub>r"
            using \<open>C\<^sub>p\<^sub>r \<noteq> eres D1 C\<^sub>p\<^sub>r\<close> .
        next
          show "eres D1 C\<^sub>p\<^sub>r |\<in>| finsert (eres D C) U\<^sub>e\<^sub>r \<longleftrightarrow>
            \<not> is_least_false_clause (N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2"
            using \<open>eres D1 C\<^sub>p\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2)\<close>
            apply (cases "eres D1 C\<^sub>p\<^sub>r |\<in>| U\<^sub>e\<^sub>r")
            subgoal
              apply simp
              sorry
            subgoal
              apply (cases "eres D1 C\<^sub>p\<^sub>r = eres D C")
              apply simp_all
              sorry
            done
        next
          show "D1 |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        next
          show "D2 |\<in>| N |\<union>| finsert (eres D C) U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        qed
      qed simp_all

      ultimately show ?thesis
        by metis
    next
      case False

      have "?match N2 s2' N3 s3"
        unfolding Ns_def \<open>s2' = (U\<^sub>r', U\<^sub>e\<^sub>f)\<close> s3_def ord_res_2_matches_ord_res_3.simps
      proof (intro conjI exI ballI)
        show "U\<^sub>r' = finsert DC U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
          unfolding \<open>U\<^sub>r' = finsert DC U\<^sub>r\<close> U\<^sub>r_def by simp
      next
        fix C\<^sub>e\<^sub>r
        assume "C\<^sub>e\<^sub>r|\<in>|U\<^sub>e\<^sub>r"
        thus "\<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D |\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. eres D C = C\<^sub>e\<^sub>r"
          using U\<^sub>e\<^sub>r_spec by metis
      next
        fix C\<^sub>p\<^sub>r
        assume "C\<^sub>p\<^sub>r |\<in>| finsert DC U\<^sub>p\<^sub>r"
        hence "C\<^sub>p\<^sub>r = DC \<or> C\<^sub>p\<^sub>r |\<in>| U\<^sub>p\<^sub>r"
          by simp
        thus "\<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          (ground_resolution D)\<^sup>+\<^sup>+ C C\<^sub>p\<^sub>r \<and> C\<^sub>p\<^sub>r \<noteq> eres D C\<^sub>p\<^sub>r \<and>
          (eres D C\<^sub>p\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
        proof (elim disjE)
          assume "C\<^sub>p\<^sub>r = DC"

          from C_in have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> C |\<in>| U\<^sub>p\<^sub>r"
            using U\<^sub>r_def by auto
          thus ?thesis
          proof (elim disjE)
            assume "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"

            have "is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
              using \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>[unfolded U\<^sub>r_def]
              using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
                  OF U\<^sub>p\<^sub>r_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>]
              by (simp add: sup_commute sup_left_commute)

            show ?thesis
              apply (rule bexI[OF _ \<open>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>])
              apply (rule bexI[OF _ \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>])
              apply (intro conjI)
              subgoal
                using \<open>ground_resolution D C DC\<close>
                unfolding \<open>C\<^sub>p\<^sub>r = DC\<close>
                by simp
              subgoal
                using \<open>eres D C \<noteq> DC\<close>
                unfolding \<open>C\<^sub>p\<^sub>r = DC\<close> eres_eq_after_ground_resolution[OF \<open>ground_resolution D C DC\<close>]
                by argo
              subgoal
                using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
                apply simp
                sorry
              done
          next
            assume "C |\<in>| U\<^sub>p\<^sub>r"
            then obtain D1 D2 where
              "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
              "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
              "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
              "C \<noteq> eres D1 C" and
              "eres D1 C |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2"
              using U\<^sub>p\<^sub>r_spec by metis

            have "ord_res.is_maximal_lit L D2"
              using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> \<open>C \<noteq> eres D1 C\<close> \<open>ord_res.is_maximal_lit L C\<close>
              by (smt (verit, ccfv_threshold) ground_resolutionD
                  linorder_lit.Uniq_is_greatest_in_mset linorder_lit.Uniq_is_maximal_in_mset
                  literal.sel(1) resolvable_if_neq_eres tranclp_ground_resolutionD the1_equality')

            hence "linorder_lit.is_greatest_in_mset D1 (- L)"
              using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close>
              by (smt (verit, ccfv_threshold) linorder_lit.Uniq_is_maximal_in_mset
                  tranclp_ground_resolutionD the1_equality' uminus_Neg)

            have "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D1 \<noteq> {}"
              \<comment> \<open>This will need to be added to @{thm U\<^sub>p\<^sub>r_spec}\<close>
              sorry

            hence "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D1 = {atm_of L}"
              using \<open>linorder_lit.is_greatest_in_mset D1 (- L)\<close>
              unfolding L_def uminus_Neg literal.sel
              using ord_res.production_eq_empty_or_singleton
              by (metis (mono_tags, lifting) Uniq_D insert_iff linorder_lit.Uniq_is_greatest_in_mset
                  literal.inject(1) mem_Collect_eq ord_res.production_unfold)

            hence "D1 = D"
              using \<open>ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}\<close>
              unfolding production_N_U\<^sub>r_U\<^sub>e\<^sub>f_production_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f
              by (metis (mono_tags, lifting) Uniq_D ord_res.Uniq_production_eq_singleton)

            show ?thesis
            proof (intro bexI conjI)
              show "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>p\<^sub>r"
                using \<open>ground_resolution D C DC\<close> \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close>
                unfolding \<open>D1 = D\<close> \<open>C\<^sub>p\<^sub>r = DC\<close>
                by simp
            next
              show "C\<^sub>p\<^sub>r \<noteq> eres D1 C\<^sub>p\<^sub>r"
                using \<open>eres D C \<noteq> DC\<close>
                unfolding \<open>D1 = D\<close> \<open>C\<^sub>p\<^sub>r = DC\<close>
                  eres_eq_after_ground_resolution[OF \<open>ground_resolution D C DC\<close>]
                by argo
            next
              show "eres D1 C\<^sub>p\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2"
                using \<open>eres D1 C |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2\<close>
                unfolding \<open>D1 = D\<close> \<open>C\<^sub>p\<^sub>r = DC\<close>
                  eres_eq_after_ground_resolution[OF \<open>ground_resolution D C DC\<close>] .
            next
              show "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using \<open>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
            next
              show "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using \<open>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
            qed
          qed
        next
          assume "C\<^sub>p\<^sub>r |\<in>| U\<^sub>p\<^sub>r"
          then show ?thesis
            using U\<^sub>p\<^sub>r_spec by metis
        qed
      qed simp_all

      moreover have "?order (?measure N2 s2') (?measure N2 s2)"
      proof -
        have "?measure N2 s2 = C"
          unfolding Ns_def s2_def ord_res_2_measure_def Let_def prod.case
          using \<open>is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
          by (meson Uniq_is_least_false_clause the1_equality')

        moreover have "?measure N2 s2' = DC"
        proof -
          have "is_least_false_clause (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f) DC"
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            show "DC |\<in>| N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f"
              unfolding \<open>U\<^sub>r' = finsert DC U\<^sub>r\<close> by simp
          next
            have "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
              using C_least_false
              unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
              by argo

            moreover have "ord_res_Interp (fset (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f)) x =
              ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x" for x
            proof -
              have "ord_res.production (insert DC (fset N \<union> fset U\<^sub>r \<union> fset U\<^sub>e\<^sub>f)) DC = {}"
                by (metis False \<open>ground_resolution D C DC\<close> eres_eq_after_ground_resolution
                    nex_strictly_maximal_pos_lit_if_neq_eres
                    unproductive_if_nex_strictly_maximal_pos_lit)
              thus ?thesis
                unfolding \<open>U\<^sub>r' = finsert DC U\<^sub>r\<close>
                using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
                    of "{|DC|}" "N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f", simplified]
                by simp
            qed

            ultimately have "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
              by metis

            thus "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f)) DC \<TTurnstile> DC"
            proof (rule contrapos_nn)
              assume "ord_res_Interp (fset (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f)) DC \<TTurnstile> DC"
              then show "ord_res_Interp (fset (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f)) C \<TTurnstile> C"
                \<comment> \<open>DC is not exhaustively factorized, hence it is not productive. We know by
                definition of resolution that DC consists only of false literals from D or literals
                from C, which are all false because we know C to be the least false clause.\<close>
                sorry
            qed
          next
            fix y
            assume
              y_in: "y |\<in>| N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f" and
              y_neq: "y \<noteq> DC" and
              y_false: "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r' |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"

            have "y |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              using y_in y_neq \<open>U\<^sub>r' = finsert DC U\<^sub>r\<close> by simp

            moreover have "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
            proof -
              have "ord_res.production (insert DC (fset N \<union> fset U\<^sub>r \<union> fset U\<^sub>e\<^sub>f)) DC = {}"
                by (metis False \<open>ground_resolution D C DC\<close> eres_eq_after_ground_resolution
                    nex_strictly_maximal_pos_lit_if_neq_eres
                    unproductive_if_nex_strictly_maximal_pos_lit)
              hence "\<forall>x|\<in>|{|DC|}. ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset {|DC|}) x = {}"
                by simp
              thus ?thesis
                using y_false \<open>U\<^sub>r' = finsert DC U\<^sub>r\<close>
                using Interp_union_unproductive[of "fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)" "fset {|DC|}",
                    OF finite_fset finite_fset]
                by simp
            qed

            moreover have "DC \<prec>\<^sub>c C"
              using \<open>ord_res.ground_resolution C D DC\<close> ord_res.ground_resolution_smaller_conclusion
              by metis

            ultimately show "DC \<prec>\<^sub>c y"
              using C_least_false[unfolded is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff]
              by auto
          qed

          thus ?thesis
            unfolding Ns_def \<open>s2' = (U\<^sub>r', U\<^sub>e\<^sub>f)\<close> ord_res_2_measure_def Let_def prod.case
            by (metis Uniq_is_least_false_clause the1_equality')
        qed

        moreover have "DC \<prec>\<^sub>c C"
          using \<open>ord_res.ground_resolution C D DC\<close>
          using ord_res.ground_resolution_smaller_conclusion by metis

        ultimately show ?thesis
          by argo
      qed

      ultimately show ?thesis
        by metis
    qed
  qed
next
  let
    ?match = ord_res_2_matches_ord_res_3 and
    ?measure = "\<lambda>_ _. ()" and ?order = "\<lambda>_ _. False"

  fix
    N2 N3 :: "'f gterm clause fset" and
    s2 s3 s3' :: "'f gterm clause fset \<times> 'f gterm clause fset"

  assume "?match N2 s2 N3 s3"
  then obtain N U\<^sub>r U\<^sub>p\<^sub>r U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f where
    Ns_def: "N2 = N" "N3 = N" and s2_def: "s2 = (U\<^sub>r, U\<^sub>e\<^sub>f)" and s3_def: "s3 = (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" and
    U\<^sub>r_def: "U\<^sub>r = U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r" and
    U\<^sub>e\<^sub>r_spec: "\<forall>C\<^sub>e\<^sub>r |\<in>| U\<^sub>e\<^sub>r. \<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. eres D C = C\<^sub>e\<^sub>r" and
    U\<^sub>p\<^sub>r_spec: "\<forall>C\<^sub>r |\<in>| U\<^sub>p\<^sub>r. \<exists>C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
      (ground_resolution D)\<^sup>+\<^sup>+ C C\<^sub>r \<and> C\<^sub>r \<noteq> eres D C\<^sub>r \<and>
      (eres D C\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C)"
    by (elim ord_res_2_matches_ord_res_3.elims(2)) blast

  assume "ord_res_3 N3 s3 s3'"
  hence "ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'"
    unfolding Ns_def s3_def .
  thus "(\<exists>s2'. (ord_res_2 N2)\<^sup>+\<^sup>+ s2 s2' \<and> ?match N2 s2' N3 s3') \<or>
    ?match N2 s2 N3 s3' \<and> ?order (?measure N3 s3') (?measure N3 s3)"
  proof (cases N "(U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" s3' rule: ord_res_3.cases)
    case (factoring C L U\<^sub>e\<^sub>f')

    define s2' where
      "s2' = (U\<^sub>r, finsert (sfac C) U\<^sub>e\<^sub>f)"

    have "(ord_res_2 N2)\<^sup>+\<^sup>+ s2 s2'"
    proof (rule tranclp.r_into_trancl)
      show "ord_res_2 N2 s2 s2'"
        unfolding Ns_def s2_def s2'_def
      proof (rule ord_res_2.factoring)
        show "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
          sorry
      next
        show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
      next
        show "is_pos L"
          using \<open>is_pos L\<close> .
      next
        show "finsert (sfac C) U\<^sub>e\<^sub>f = finsert (sfac C) U\<^sub>e\<^sub>f" ..
      qed
    qed

    moreover have "?match N2 s2' N3 s3'"
    proof -
      have "
        \<exists>Ca|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f. \<exists>D|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f.
          eres D Ca = C\<^sub>r\<^sub>r"
        if "C\<^sub>r\<^sub>r |\<in>| U\<^sub>e\<^sub>r" for C\<^sub>r\<^sub>r
        using U\<^sub>e\<^sub>r_spec[rule_format, OF that] by blast

      moreover have "
        \<exists>Ca|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f. \<exists>D|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f.
          (ground_resolution D)\<^sup>+\<^sup>+ Ca C\<^sub>r \<and> C\<^sub>r \<noteq> eres D C\<^sub>r \<and>
          (eres D C\<^sub>r |\<in>| U\<^sub>e\<^sub>r) = (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f) Ca)"
        if "C\<^sub>r |\<in>| U\<^sub>p\<^sub>r" for C\<^sub>r
      proof -
        from that obtain D1 D2 where
          "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
          "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>r" and
          "C\<^sub>r \<noteq> eres D1 C\<^sub>r" and
          "eres D1 C\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> (\<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) D2)"
          using U\<^sub>p\<^sub>r_spec by metis

        show ?thesis
        proof (intro bexI conjI)
          show "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>r"
            using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<^sub>r\<close> .
        next
          show "C\<^sub>r \<noteq> eres D1 C\<^sub>r"
            using \<open>C\<^sub>r \<noteq> eres D1 C\<^sub>r\<close> .
        next
          show "eres D1 C\<^sub>r |\<in>| U\<^sub>e\<^sub>r \<longleftrightarrow> \<not> is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f) D2"
            \<comment> \<open>This should be provable using the same argument as for
              \<^term>\<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close> above.\<close>
            sorry
        next
          show "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f"
            using \<open>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        next
          show "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f"
            using \<open>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by simp
        qed
      qed

      ultimately show ?thesis
        unfolding Ns_def s2'_def U\<^sub>r_def \<open>U\<^sub>e\<^sub>f' = finsert (sfac C) U\<^sub>e\<^sub>f\<close> \<open>s3' = (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f')\<close>
        unfolding ord_res_2_matches_ord_res_3.simps
        by blast
    qed

    ultimately show ?thesis
      by metis
  next
    case (resolution C L D DC U\<^sub>e\<^sub>r')

    obtain m where
      "(ground_resolution D ^^ Suc m) C DC"
      sorry

    obtain n m' DnC where
      "(ground_resolution D ^^ Suc n) C DnC" and "(ground_resolution D ^^ Suc m') DnC DC"
      sorry

    have "Suc m = Suc n + Suc m'"
      sorry

    define stuff where
      "stuff = {|DC|}" \<comment> \<open>and more...\<close>

    define s2' where
      "s2' = (U\<^sub>r |\<union>| stuff, U\<^sub>e\<^sub>f)"

    have "(ord_res_2 N2)\<^sup>+\<^sup>+ s2 s2'"
    proof (rule tranclp_if_relpowp)
      show "Suc m' \<noteq> 0"
        by presburger
    next
      show "(ord_res_2 N2 ^^ Suc m') s2 s2'"
        sorry
    qed

    moreover have "?match N2 s2' N3 s3'"
      sorry

    ultimately show ?thesis
      by metis
  qed
qed

subsubsection \<open>ORD-RES-4 (full resolve)\<close>


subsubsection \<open>ORD-RES-5 (explicit model construction)\<close>


subsubsection \<open>ORD-RES-6 (model backjump)\<close>


subsubsection \<open>SCL(FOL)-1 (strategy)\<close>


subsubsection \<open>SCL(FOL)-2 (regular SCL)\<close>


subsection \<open>Strategy for model-driven ground ordered resolution\<close>

definition is_min_false_clause :: "'f gterm clause fset \<Rightarrow> 'f gterm clause \<Rightarrow> bool" where
  "is_min_false_clause N C \<longleftrightarrow>
    is_minimal_in_fset_wrt (\<prec>\<^sub>c)
      {|C |\<in>| N. \<not> (\<Union>D \<in> {D \<in> fset N. D \<preceq>\<^sub>c C}. ord_res.production (fset N) D) \<TTurnstile> C|} C"

lemma Uniq_is_min_false_clause: "\<exists>\<^sub>\<le>\<^sub>1C. is_min_false_clause N C"
  unfolding is_min_false_clause_def
  using Uniq_is_least_in_fset_wrt is_minimal_in_fset_wrt_eq_is_least_in_fset_wrt
  by (metis (no_types, lifting) linorder_cls.asymp_on_less linorder_cls.totalp_on_less
      linorder_cls.transp_on_less)

definition res_mo_strategy :: "'f gterm clause fset \<Rightarrow> 'f gterm clause fset \<Rightarrow> bool" where
  "res_mo_strategy N N' \<longleftrightarrow> (\<exists>C L.
    is_min_false_clause N C \<and> ord_res.is_maximal_lit L C \<and>
      (case L of
        Neg A \<Rightarrow> \<comment> \<open>Case 3\<close>
        fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
          ord_res.production (fset N) D = {A} \<and>
          (\<exists>CD. ord_res.ground_resolution C D CD \<and> N' = finsert CD N))
      | Pos A \<Rightarrow> \<comment> \<open>Case 4\<close>
        \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
          (\<exists>C'. ord_res.ground_factoring C C' \<and> N' = finsert C' N)))"

lemma Unique_is_maximal_lit: "\<exists>\<^sub>\<le>\<^sub>1L. ord_res.is_maximal_lit L C"
  using linorder_lit.Uniq_is_maximal_in_mset .

lemma right_unique_res_mo_strategy: "right_unique res_mo_strategy"
proof (rule right_uniqueI)
  fix N1 N2 N3
  assume "res_mo_strategy N1 N2" and "res_mo_strategy N1 N3"
  then obtain C L where
    C_min: "is_min_false_clause N1 C" and
    L_max: "ord_res.is_maximal_lit L C" and
    fact_or_res2: "(case L of
           Pos A \<Rightarrow>
             \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
             (\<exists>C'. ord_res.ground_factoring C C' \<and> N2 = finsert C' N1)
           | Neg A \<Rightarrow>
               \<exists>D|\<in>|N1.
                  D \<prec>\<^sub>c C \<and>
                  ord_res.is_strictly_maximal_lit (Pos A) D \<and> ord_res.production (fset N1) D = {A} \<and>
                  (\<exists>CD. ord_res.ground_resolution C D CD \<and>
                        N2 = finsert CD N1))" and
    fact_or_res3: "(case L of
           Pos A \<Rightarrow>
             \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
             (\<exists>C'. ord_res.ground_factoring C C' \<and> N3 = finsert C' N1)
           | Neg A \<Rightarrow>
               \<exists>D|\<in>|N1.
                  D \<prec>\<^sub>c C \<and>
                  ord_res.is_strictly_maximal_lit (Pos A) D \<and> ord_res.production (fset N1) D = {A} \<and>
                  (\<exists>CD. ord_res.ground_resolution C D CD \<and>
                        N3 = finsert CD N1))"
    unfolding atomize_conj res_mo_strategy_def
    using Uniq_is_min_false_clause[of N1] Unique_is_maximal_lit
    by (smt (verit, best) Uniq_D)
  show "N2 = N3"
  proof (cases L)
    case (Pos A)
    then show ?thesis
      using fact_or_res2 fact_or_res3
      apply simp
      by (metis Uniq_D ord_res.unique_ground_factoring)
  next
    case (Neg A)

    from fact_or_res2 Neg obtain D2 where
      D2_prod: "ord_res.production (fset N1) D2 = {A}" and
      D2_reso: "(\<exists>CD. ord_res.ground_resolution C D2 CD \<and> N2 = finsert CD N1)"
      by auto

    from fact_or_res3 Neg obtain D3 where
      D3_prod: "ord_res.production (fset N1) D3 = {A}" and
      D3_reso: "(\<exists>CD. ord_res.ground_resolution C D3 CD \<and> N3 = finsert CD N1)"
      by auto

    from D2_prod D3_prod have "D2 = D3"
      using ord_res.Uniq_production_eq_singleton by (meson Uniq_D)
    with D2_reso D3_reso show ?thesis
      using ord_res.unique_ground_resolution by (metis Uniq_D)
  qed
qed

lemma
  assumes
    C_min_false: "is_min_false_clause N C" and
    Neg_A_max: "ord_res.is_maximal_lit (Neg A) C"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
    ord_res.production (fset N) D = {A})"
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

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C})"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  from Neg_A_max have "Neg A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

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

  moreover have "ord_res.production (fset N) D = {A}"
    using D_productive ord_res.production_eq_empty_or_singleton by fastforce

  ultimately show ?thesis
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


subsection \<open>More explicit strategy for model-driven ground ordered resolution\<close>

fun learned where
  "learned (U, \<I>, C) = U"

fun interp where
  "interp (U, \<I>, C) = \<I>"

fun interp_upto where
  "interp_upto (U, \<I>, C) = C"

inductive ord_res_strategy for N where
  expand_modelI: "
    fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<Longrightarrow>
    linorder_cls.is_least_in_fset {|D |\<in>| N |\<union>| U. C \<prec>\<^sub>c D|} D \<Longrightarrow>
    ord_res_strategy N (U, \<I>, C) (U, \<I> |\<union>| Abs_fset (ord_res.production (fset (N |\<union>| U)) C), D)" |

  factoringI: "
    \<not> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    ord_res.ground_factoring C C' \<Longrightarrow>
    linorder_cls.is_least_in_fset (N |\<union>| finsert C' U) D \<Longrightarrow>
    ord_res_strategy N (U, \<I>, C) (finsert C' U, {||}, D)" |

  resolution: "
    \<not> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    E |\<in>| N \<Longrightarrow>
    E \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset (N |\<union>| U)) E = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C E CE \<Longrightarrow>
    linorder_cls.is_least_in_fset (N |\<union>| finsert CE U) D \<Longrightarrow>
    ord_res_strategy N (U, \<I>, C) (finsert CE U, {||}, D)"

lemma ord_res_strategy_expand_modelI':
  "fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<Longrightarrow>
    \<I>' = \<I> |\<union>| Abs_fset (ord_res.production (fset (N |\<union>| U)) C) \<Longrightarrow>
    linorder_cls.is_least_in_fset {|D |\<in>| N |\<union>| U. C \<prec>\<^sub>c D|} D \<Longrightarrow>
    ord_res_strategy N (U, \<I>, C) (U, \<I>', D)"
  using ord_res_strategy.expand_modelI by metis

lemma right_unique_sup_iff:
  assumes disj: "\<And>x. \<not> ((\<exists>y. R1 x y) \<and> (\<exists>y. R2 x y))"
  shows "right_unique (R1 \<squnion> R2) \<longleftrightarrow> right_unique R1 \<and> right_unique R2"
proof (rule iffI)
  show "right_unique (R1 \<squnion> R2) \<Longrightarrow> right_unique R1 \<and> right_unique R2"
    by (simp add: right_unique_def)
next
  from disj show "right_unique R1 \<and> right_unique R2 \<Longrightarrow> right_unique (R1 \<squnion> R2)"
    by (metis right_unique_def sup2E)
qed

lemma right_unique_ord_res_strategy: "right_unique (ord_res_strategy N)"
proof (rule right_uniqueI)
  fix S S' S''
  assume step1: "ord_res_strategy N S S'" and step2: "ord_res_strategy N S S''"
  from step1 show "S' = S''"
  proof (cases N S S' rule: ord_res_strategy.cases)
    case hyps1: (expand_modelI \<I> U C D1)
    from step2 show ?thesis
      unfolding \<open>S = (U, \<I>, C)\<close>
    proof (cases N "(U, \<I>, C)" S'' rule: ord_res_strategy.cases)
      case (expand_modelI D2)
      with hyps1 show ?thesis
        by (metis Uniq_D linorder_cls.Uniq_is_least_in_fset)
    next
      case (factoringI L2 C2' D2)
      with hyps1 show ?thesis
        by argo
    next
      case (resolution L2 E2 CE2 D2)
      with hyps1 show ?thesis
        by argo
    qed
  next
    case hyps1: (factoringI \<I> U C L1 C1' D1)
    from step2 show ?thesis
      unfolding \<open>S = (U, \<I>, C)\<close>
    proof (cases N "(U, \<I>, C)" S'' rule: ord_res_strategy.cases)
      case (expand_modelI D2)
      with hyps1 show ?thesis
        by argo
    next
      case (factoringI L2 C2' D2)
      with hyps1 show ?thesis
        by (metis Uniq_D linorder_cls.Uniq_is_least_in_fset ord_res.unique_ground_factoring)
    next
      case (resolution L2 E2 CE2 D2)
      with hyps1 show ?thesis
        by (metis linorder_lit.antisym_conv3 linorder_lit.is_maximal_in_mset_iff)
    qed
  next
    case hyps1: (resolution \<I> U C L1 E1 CE1 D1)
    from step2 show ?thesis
      unfolding \<open>S = (U, \<I>, C)\<close>
    proof (cases N "(U, \<I>, C)" S'' rule: ord_res_strategy.cases)
      case (expand_modelI D2)
      with hyps1 show ?thesis
        by argo
    next
      case (factoringI L2 C2' D2)
      with hyps1 show ?thesis
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
    next
      case (resolution L2 E2 CE2 D2)
      with hyps1 show ?thesis
        by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
            linorder_lit.Uniq_is_maximal_in_mset ord_res.Uniq_production_eq_singleton
            ord_res.unique_ground_resolution the1_equality')
    qed
  qed
qed

definition ord_res_strategy_init where
  "N \<noteq> {||} \<Longrightarrow> ord_res_strategy_init N = ({||}, {||}, The (linorder_cls.is_least_in_fset N))"

lemma initial_state_interp_upto_fmember_clauses:
  assumes "N \<noteq> {||}" 
  shows "interp_upto (ord_res_strategy_init N) |\<in>| N |\<union>| learned (ord_res_strategy_init N)"
proof -
  from \<open>N \<noteq> {||}\<close> have "\<exists>!D. linorder_cls.is_least_in_fset N D"
    using linorder_cls.ex1_least_in_fset by metis
  thus ?thesis
    unfolding ord_res_strategy_init_def[OF \<open>N \<noteq> {||}\<close>]
    apply simp
    by (metis linorder_cls.is_least_in_fset_iff theI')
qed

lemma ord_res_strategy_preserves_interp_upto_fmember_clauses:
  assumes step: "ord_res_strategy N S S'"
  shows "interp_upto S' |\<in>| N |\<union>| learned S'"
  using step
proof (cases N S S' rule: ord_res_strategy.cases)
  case hyps: (expand_modelI \<I> U C D)
  hence "D |\<in>| N |\<union>| U"
    using linorder_cls.is_least_in_fset_ffilterD(1) by metis
  thus ?thesis
    unfolding hyps by simp
next
  case hyps: (factoringI \<I> U C L C' D)
  hence "D |\<in>| N |\<union>| finsert C' U"
    using linorder_cls.is_least_in_fset_iff by metis
  thus ?thesis
    unfolding hyps by simp
next
  case hyps: (resolution \<I> U C L E CE D)
  hence "D |\<in>| N |\<union>| finsert CE U"
    using linorder_cls.is_least_in_fset_iff by metis
  thus ?thesis
    unfolding hyps by simp
qed

lemma initial_state_interp_upto_eq_fempty_iff_fempty_in_clauses:
  assumes "N \<noteq> {||}" 
  shows "interp_upto (ord_res_strategy_init N) = {#} \<longleftrightarrow>
    {#} |\<in>| N |\<union>| learned (ord_res_strategy_init N)"
proof -
  from \<open>N \<noteq> {||}\<close> obtain D where D_least: "linorder_cls.is_least_in_fset N D"
    using linorder_cls.ex_least_in_fset by metis
  moreover have "The (linorder_cls.is_least_in_fset N) = D"
    using D_least linorder_cls.Uniq_is_least_in_fset
    by (simp add: the1_equality')
  ultimately show ?thesis
    unfolding ord_res_strategy_init_def[OF \<open>N \<noteq> {||}\<close>]
    apply simp
    by (metis linorder_cls.is_least_in_fset_iff linorder_cls.less_le_not_le mempty_lesseq_cls)
qed

lemma ord_res_strategy_preserves_interp_upto_eq_fempty_iff_fempty_in_clauses:
  assumes
    step: "ord_res_strategy N S S'" and
    invar: "interp_upto S = {#} \<longleftrightarrow> {#} |\<in>| N |\<union>| learned S"
  shows "interp_upto S' = {#} \<longleftrightarrow> {#} |\<in>| N |\<union>| learned S'"
  using step
proof (cases N S S' rule: ord_res_strategy.cases)
  case (expand_modelI \<I> C U D)
  with invar show ?thesis
    using linorder_cls.is_least_in_fset_iff by auto
next
  case (factoringI \<I> U C L C' D)
  with invar show ?thesis
    by (metis empty_iff fset_simps(2) funionE funionI1 funionI2 insertE interp_upto.simps
        learned.simps linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
        linorder_cls.is_minimal_in_fset_iff ord_res.ground_factoring.simps set_mset_empty
        union_single_eq_member)
next
  case hyps: (resolution \<I> U C L E CE D)
  hence "C \<noteq> {#}"
    using linorder_lit.is_maximal_in_mset_iff by force
  with invar have "{#} |\<notin>| N |\<union>| U"
    unfolding hyps by simp
  then show ?thesis
    unfolding hyps interp_upto.simps learned.simps
    using mempty_lesseq_cls
    apply simp
    using \<open>linorder_cls.is_least_in_fset (N |\<union>| finsert CE U) D\<close>
    by (metis finsert_iff funion_iff linorder_cls.dual_order.strict_trans
        linorder_cls.is_least_in_fset_iff linorder_cls.less_irrefl)
qed

lemma initial_state_interp_correct:
  assumes "N \<noteq> {||}" 
  defines "init \<equiv> ord_res_strategy_init N"
  shows "fset (interp init) = ord_res.interp (fset N) (interp_upto init)"
proof -
  from \<open>N \<noteq> {||}\<close> obtain D where D_least: "linorder_cls.is_least_in_fset N D"
    using linorder_cls.ex_least_in_fset by metis
  moreover have "The (linorder_cls.is_least_in_fset N) = D"
    using D_least linorder_cls.Uniq_is_least_in_fset
    by (simp add: the1_equality')
  ultimately show ?thesis
    unfolding init_def
    unfolding ord_res_strategy_init_def[OF \<open>N \<noteq> {||}\<close>]
    apply simp
    using linorder_cls.is_minimal_in_fset_eq_is_least_in_fset linorder_cls.is_minimal_in_fset_iff
      ord_res.interp_def by force
qed

lemma finite_ord_res_production[simp]: "finite (ord_res.production N C)"
  by (metis finite.emptyI finite_insert ord_res.production_eq_empty_or_singleton)

lemma ord_res_interp_eq_empty_if_least:
  "linorder_cls.is_least_in_fset N C \<Longrightarrow> ord_res.interp (fset N) C = {}"
  using linorder_cls.is_least_in_fset_iff ord_res.interp_def by auto

lemma ord_res_strategy_preserves_interp_correct:
  assumes
    step: "ord_res_strategy N S S'" and
    invars: "fset (interp S) = ord_res.interp (fset (N |\<union>| learned S)) (interp_upto S)"
      "interp_upto S |\<in>| N |\<union>| learned S"
  shows "fset (interp S') = ord_res.interp (fset (N |\<union>| learned S')) (interp_upto S')"
  using step
proof (cases N S S' rule: ord_res_strategy.cases)
  case (expand_modelI \<I> U C D)

  from invars(2-) have C_in: "C |\<in>| N |\<union>| U"
    unfolding expand_modelI by simp

  have "C \<prec>\<^sub>c D"
    using linorder_cls.is_least_in_fset_ffilterD(2) expand_modelI(4) by blast

  have "{E \<in> fset (N |\<union>| U). E \<prec>\<^sub>c D} = insert C {D \<in> fset (N |\<union>| U). D \<prec>\<^sub>c C}"
  proof (intro subset_antisym subsetI)
    show "\<And>x. x \<in> {E. E |\<in>| N |\<union>| U \<and> E \<prec>\<^sub>c D} \<Longrightarrow> x \<in> insert C {D. D |\<in>| N |\<union>| U \<and> D \<prec>\<^sub>c C}"
      using \<open>C \<prec>\<^sub>c D\<close>
      using linorder_cls.is_minimal_in_fset_eq_is_least_in_fset linorder_cls.is_minimal_in_fset_iff
        linorder_cls.neq_iff local.expand_modelI(4) by force
  next
    fix x
    assume "x \<in> insert C {D. D |\<in>| N |\<union>| U \<and> D \<prec>\<^sub>c C}"
    hence "x = C \<or> x |\<in>| N |\<union>| U \<and> x \<prec>\<^sub>c C"
      by simp
    thus "x \<in> {E. E |\<in>| N |\<union>| U \<and> E \<prec>\<^sub>c D}"
    proof (elim disjE)
      assume "x = C"
      thus ?thesis
        using \<open>C \<prec>\<^sub>c D\<close> C_in by simp
    next
      assume "x |\<in>| N |\<union>| U \<and> x \<prec>\<^sub>c C"
      then show ?thesis
        using \<open>C \<prec>\<^sub>c D\<close> linorder_cls.less_trans by blast
    qed
  qed
  hence "ord_res.interp (fset (N |\<union>| U)) C \<union> ord_res.production (fset (N |\<union>| U)) C =
    ord_res.interp (fset (N |\<union>| U)) D"
    unfolding ord_res.interp_def by auto
  with invars(1) show ?thesis
    unfolding expand_modelI by (simp add: Abs_fset_inverse)
next
  case (factoringI \<I> U C L C' D)
  with invars(1) show ?thesis
    unfolding factoringI using ord_res_interp_eq_empty_if_least by fastforce
next
  case (resolution \<I> U C L E CE D)
  with invars(1) show ?thesis
    unfolding factoringI using ord_res_interp_eq_empty_if_least by fastforce
qed

lemma interp_entails_clauses_lt_interp_upto:
  assumes
    step: "ord_res_strategy N S S'" and
    invars:
      "\<forall>C |\<in>| N |\<union>| learned S. C \<prec>\<^sub>c interp_upto S \<longrightarrow> fset (interp S) \<TTurnstile> C"
      "fset (interp S) = ord_res.interp (fset (N |\<union>| learned S)) (interp_upto S)"
      "interp_upto S |\<in>| N |\<union>| learned S"
  shows "\<forall>C |\<in>| N |\<union>| learned S'. C \<prec>\<^sub>c interp_upto S' \<longrightarrow> fset (interp S') \<TTurnstile> C"
  using step
proof (cases N S S' rule: ord_res_strategy.cases)
  case (expand_modelI \<I> U C D)

  from invars(3) have C_in: "C |\<in>| N |\<union>| U"
    unfolding expand_modelI by simp

  show ?thesis
  proof (intro ballI impI)
    fix E
    assume "E |\<in>| N |\<union>| local.learned S'" and "E \<prec>\<^sub>c interp_upto S'"
    hence "E |\<in>| N |\<union>| U" and "E \<prec>\<^sub>c D"
      unfolding expand_modelI by simp_all

    have "ord_res.interp (fset (N |\<union>| U)) C \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> E"
      using invars(1)[unfolded expand_modelI interp.simps learned.simps interp_upto.simps,
          rule_format, OF \<open>E |\<in>| N |\<union>| U\<close>]
      unfolding invars(2)[unfolded expand_modelI interp.simps learned.simps interp_upto.simps]
      using ord_res.lift_interp_entails_to_interp_production_entails[OF \<open>C |\<in>| N |\<union>| U\<close>
          \<open>E |\<in>| N |\<union>| U\<close>]
      by (metis \<open>E \<prec>\<^sub>c D\<close> \<open>E |\<in>| N |\<union>| U\<close> \<open>fset \<I> = ord_res.interp (fset (N |\<union>| U)) C\<close>
          ffmember_filter linorder_cls.is_least_in_fset_iff linorder_cls.less_imp_triv
          linorder_cls.neq_iff local.expand_modelI(3) local.expand_modelI(4))
    thus "fset (interp S') \<TTurnstile> E"
      unfolding expand_modelI interp.simps learned.simps interp_upto.simps union_fset
      unfolding invars(2)[unfolded expand_modelI interp.simps learned.simps interp_upto.simps]
      by (simp add: Abs_fset_inverse)
  qed
next
  case (factoringI \<I> U C L C' D)
  thus ?thesis
    by (metis interp_upto.simps learned.simps linorder_cls.is_least_in_fset_iff
        linorder_cls.less_asym')
next
  case (resolution \<I> U C L E CE D)
  then show ?thesis
    by (metis interp_upto.simps learned.simps linorder_cls.is_least_in_fset_iff
        linorder_cls.less_asym')
qed

lemma interp_entails_clauses_lt_interp_upto':
  assumes
    step: "ord_res_strategy N S S'" and
    invars:
      "\<forall>C |\<in>| N |\<union>| learned S. C \<prec>\<^sub>c interp_upto S \<longrightarrow>
        ord_res.interp (fset (N |\<union>| learned S)) C \<union>
        ord_res.production (fset (N |\<union>| learned S)) C \<TTurnstile> C"
      "fset (interp S) = ord_res.interp (fset (N |\<union>| learned S)) (interp_upto S)"
  shows "\<forall>C |\<in>| N |\<union>| learned S'. C \<prec>\<^sub>c interp_upto S' \<longrightarrow>
    ord_res.interp (fset (N |\<union>| learned S')) C \<union>
    ord_res.production (fset (N |\<union>| learned S')) C \<TTurnstile> C"
  using step
proof (cases N S S' rule: ord_res_strategy.cases)
  case (expand_modelI \<I> U C D)
  then show ?thesis
    by (metis (no_types, lifting) asympD ffmember_filter interp.simps invars(1) invars(2)
        linorder_cls.antisym_conv3 linorder_cls.is_least_in_fset_iff ord_res.asymp_less_cls
        interp_upto.simps learned.simps)
next
  case (factoringI \<I> U C L C' D)
  then show ?thesis
    by (metis interp_upto.simps learned.simps linorder_cls.is_least_in_fset_iff
        linorder_cls.less_imp_triv)
next
  case (resolution \<I> U C L E CE D)
  then show ?thesis
    by (metis interp_upto.simps learned.simps linorder_cls.is_least_in_fset_iff
        linorder_cls.less_imp_triv)
qed

lemma
  assumes
    step: "ord_res_strategy N S S'" and
    invars:
      "\<forall>C |\<in>| N |\<union>| learned S. C \<prec>\<^sub>c interp_upto S \<longrightarrow>
        fset (interp S) \<union> ord_res.production (fset (N |\<union>| learned S)) (interp_upto S) \<TTurnstile> C"
      "fset (interp S) = ord_res.interp (fset (N |\<union>| learned S)) (interp_upto S)"
      "interp_upto S |\<in>| N |\<union>| learned S"
  shows "\<forall>C |\<in>| N |\<union>| learned S'. C \<prec>\<^sub>c interp_upto S' \<longrightarrow>
      fset (interp S') \<union> ord_res.production (fset (N |\<union>| learned S')) (interp_upto S') \<TTurnstile> C"
  using step
proof (cases N S S' rule: ord_res_strategy.cases)
  case (expand_modelI \<I> U C D)

  from invars(3) have C_in: "C |\<in>| N |\<union>| U"
    unfolding expand_modelI by simp

  show ?thesis
  proof (intro ballI impI)
    fix E
    assume "E |\<in>| N |\<union>| local.learned S'" and "E \<prec>\<^sub>c interp_upto S'"
    hence "E |\<in>| N |\<union>| U" and "E \<prec>\<^sub>c D"
      unfolding expand_modelI by simp_all

    have "ord_res.interp (fset (N |\<union>| U)) C \<union> ord_res.production (fset (N |\<union>| U)) C =
      \<Union> (ord_res.production (fset (N |\<union>| U)) ` {D. D |\<in>| N |\<union>| U \<and> D \<prec>\<^sub>c C}) \<union>
      ord_res.production (fset (N |\<union>| U)) C"
      unfolding ord_res.interp_def ..
    also have "\<dots> = \<Union> (ord_res.production (fset (N |\<union>| U)) ` insert C {D. D |\<in>| N |\<union>| U \<and> D \<prec>\<^sub>c C})"
      by blast
    also have "\<dots> = \<Union> (ord_res.production (fset (N |\<union>| U)) ` {x. x |\<in>| N |\<union>| U \<and> x \<prec>\<^sub>c D})"
    proof -
      have "insert C {D. D |\<in>| N |\<union>| U \<and> D \<prec>\<^sub>c C} = {D. D |\<in>| N |\<union>| U \<and> D \<preceq>\<^sub>c C}"
        using C_in by blast
      also have "\<dots> = {x. x |\<in>| N |\<union>| U \<and> x \<prec>\<^sub>c D}"
        using \<open>linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (N |\<union>| U)) D\<close>
        by (metis (mono_tags, lifting) ffmember_filter linorder_cls.dual_order.strict_trans2
            linorder_cls.is_minimal_in_fset_eq_is_least_in_fset linorder_cls.is_minimal_in_fset_iff
            linorder_cls.leI linorder_cls.neq_iff)
      finally show ?thesis
        by argo
    qed
    also have "\<dots> = ord_res.interp (fset (N |\<union>| U)) D"
      unfolding ord_res.interp_def ..
    finally have AAA: "ord_res.interp (fset (N |\<union>| U)) C \<union> ord_res.production (fset (N |\<union>| U)) C =
      ord_res.interp (fset (N |\<union>| U)) D " .

    have "ord_res.interp (fset (N |\<union>| U)) C \<union> ord_res.production (fset (N |\<union>| U)) C \<union>
      ord_res.production (fset (N |\<union>| U)) D \<TTurnstile> E"
      using invars(1)[unfolded expand_modelI interp.simps learned.simps interp_upto.simps,
          rule_format, OF \<open>E |\<in>| N |\<union>| U\<close>]
      unfolding invars(2)[unfolded expand_modelI interp.simps learned.simps interp_upto.simps]
      unfolding AAA
      using ord_res.lift_interp_entails_to_interp_production_entails
      by (metis AAA \<open>E \<prec>\<^sub>c D\<close> \<open>E |\<in>| N |\<union>| U\<close> \<open>fset \<I> = ord_res.interp (fset (N |\<union>| U)) C\<close>
          ffmember_filter linorder_cls.is_least_in_fset_iff linorder_cls.less_imp_triv
          linorder_cls.neq_iff local.expand_modelI(3) local.expand_modelI(4))
    thus "fset (interp S') \<union> ord_res.production (fset (N |\<union>| local.learned S')) (interp_upto S') \<TTurnstile> E"
      unfolding expand_modelI interp.simps learned.simps interp_upto.simps union_fset
      unfolding invars(2)[unfolded expand_modelI interp.simps learned.simps interp_upto.simps]
      by (simp add: Abs_fset_inverse)
  qed
next
  case (factoringI \<I> U C L C' D)
  thus ?thesis
    by (metis interp_upto.simps learned.simps linorder_cls.is_least_in_fset_iff
        linorder_cls.less_asym')
next
  case (resolution \<I> U C L E CE D)
  then show ?thesis
    by (metis interp_upto.simps learned.simps linorder_cls.is_least_in_fset_iff
        linorder_cls.less_asym')
qed


subsection \<open>Strategy for resolution-driven SCL(FOL)\<close>

definition lits where
  "lits N = ffUnion (fimage fset_mset N)"

inductive scl_strategy :: "'f gterm clause fset \<Rightarrow> 'f gterm \<Rightarrow> ('f, 'v) SCL_FOL.state \<Rightarrow>
  ('f, 'v) SCL_FOL.state \<Rightarrow> bool" for N \<beta> where
  expand_model_for_neg_lit: "
    NU = N |\<union>| gcls_of_cls |`| U \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| NU. \<not> trail_true_cls \<Gamma> (cls_of_gcls C)|} C \<Longrightarrow>
    linorder_lit.is_minimal_in_mset {#L \<in># C. \<not> trail_defined_lit \<Gamma> (lit_of_glit L)#} L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<Gamma>' = trail_decide \<Gamma> (lit_of_glit L) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)" |

  expand_model_for_pos_lit_when_not_max: "
    NU = N |\<union>| gcls_of_cls |`| U \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| NU. \<not> trail_true_cls \<Gamma> (cls_of_gcls C)|} C \<Longrightarrow>
    linorder_lit.is_minimal_in_mset {#L \<in># C. \<not> trail_defined_lit \<Gamma> (lit_of_glit L)#} L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<Gamma>' = trail_decide \<Gamma> (lit_of_glit (-L)) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)" |

  expand_model_for_pos_lit_when_max: "
    NU = N |\<union>| gcls_of_cls |`| U \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| NU. \<not> trail_true_cls \<Gamma> (cls_of_gcls C)|} C \<Longrightarrow>
    linorder_lit.is_minimal_in_mset {#L \<in># C. \<not> trail_defined_lit \<Gamma> (lit_of_glit L)#} L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    \<Gamma>' =
      (if \<exists>D |\<in>| NU. trail_false_cls (trail_decide \<Gamma> (lit_of_glit L)) (cls_of_gcls D) then
        trail_propagate \<Gamma> (lit_of_glit L) (cls_of_gcls {#K \<in># C. K \<noteq> L#}) Var
      else
        trail_decide \<Gamma> (lit_of_glit L)) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)" |

  conflict: "
    NU = N |\<union>| gcls_of_cls |`| U \<Longrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| NU. \<not> trail_true_cls \<Gamma> (cls_of_gcls C)|} C \<Longrightarrow>
    trail_false_cls \<Gamma> (cls_of_gcls C) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (cls_of_gcls C, Var))" |

  resolve: "
    scl_fol.resolve (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (\<Gamma>, U, Some (C, Var)) (\<Gamma>, U, Some (C', Var)) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, Some (C, Var)) (\<Gamma>, U, Some (C', Var))" |

  skip: "
    scl_fol.skip (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (\<Gamma>, U, Some (C, Var)) (\<Gamma>', U, Some (C, Var)) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, Some (C, Var)) (\<Gamma>', U, Some (C, Var))" |

  backtrack: "
    scl_fol.backtrack (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (\<Gamma>, U, Some (C, Var)) ([], U', None) \<Longrightarrow>
    scl_strategy N \<beta> (\<Gamma>, U, Some (C, Var)) ([], U', None)"

lemma lit_in_lhs_if_lhs_generalises_rhs:
  "L \<in> \<Union> (set_mset ` fset N)"
  if
    L_in: \<open>L \<in># C\<close> and
    C_in: "C |\<in>| N |\<union>| gcls_of_cls |`| U" and
    N_lits_generalize_U_lits:
      "scl_fol.clss_lits_generalize_clss_lits (fset (cls_of_gcls |`| N)) (fset U)"
  for L N
  using C_in[unfolded funion_iff]
proof (elim disjE)
  show "C |\<in>| N \<Longrightarrow> L \<in> \<Union> (set_mset ` fset N)"
    using \<open>L \<in># C\<close> by auto
next
  assume "C |\<in>| gcls_of_cls |`| U"
  then obtain C\<^sub>f where "C = gcls_of_cls C\<^sub>f" and "C\<^sub>f |\<in>| U"
    by auto
  then obtain L\<^sub>f where L_def: "L = glit_of_lit L\<^sub>f" and "L\<^sub>f \<in># C\<^sub>f"
    unfolding gcls_of_cls_def
    using L_in by auto

  have "L\<^sub>f \<in> \<Union> (set_mset ` fset U)"
    using \<open>L\<^sub>f \<in># C\<^sub>f\<close> \<open>C\<^sub>f |\<in>| U\<close> by auto

  moreover have "\<forall>L \<in> \<Union> (set_mset ` fset U). L \<in> \<Union> (set_mset ` fset (cls_of_gcls |`| N))"
    using N_lits_generalize_U_lits
    unfolding scl_fol.clss_lits_generalize_clss_lits_def generalizes_lit_def
    by (simp add: is_ground_cls_imp_is_ground_lit)

  ultimately have "L\<^sub>f \<in> \<Union> (set_mset ` fset (cls_of_gcls |`| N))"
    by metis
  thus "L \<in> \<Union> (set_mset ` fset N)"
    unfolding L_def by (auto simp: cls_of_gcls_def)
qed

lemma ball_ground_cls_if_lits_generalized_from_ground_clauses:
  assumes "scl_fol.clss_lits_generalize_clss_lits (fset (cls_of_gcls |`| N)) (fset U)"
  shows "\<forall>C |\<in>| U. is_ground_cls C"
  using assms
  unfolding scl_fol.clss_lits_generalize_clss_lits_def
  apply (simp add: is_ground_cls_def)
  by (metis generalizes_lit_def is_ground_cls_cls_of_gcls is_ground_cls_imp_is_ground_lit
      is_ground_subst_lit)

lemma scl_strategy_restricts_scl:
  assumes
    step: "scl_strategy N \<beta> s s'" and
    bounded: "\<forall>L \<in> \<Union> (set_mset ` fset N). atm_of L \<preceq>\<^sub>t \<beta>" and
    initial_lits_generalize_learned_lits:
      "scl_fol.clss_lits_generalize_clss_lits (fset (fimage cls_of_gcls N)) (fset (state_learned s))"
  shows "scl_fol.scl (fimage cls_of_gcls N) (term_of_gterm \<beta>) s s'"
  using step
proof (cases N \<beta> s s' rule: scl_strategy.cases)
  case hyps: (expand_model_for_neg_lit NU U \<Gamma> C L \<Gamma>')

  have learned_ground: "\<forall>C |\<in>| state_learned s. is_ground_cls C"
    using initial_lits_generalize_learned_lits
      ball_ground_cls_if_lits_generalized_from_ground_clauses
    by metis

  have C_in: "C |\<in>| N |\<union>| gcls_of_cls |`| U"
    using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis
  hence lit_from_N_if_in_C: "\<And>L. L \<in># C \<Longrightarrow> L \<in> \<Union> (set_mset ` fset N)"
    using lit_in_lhs_if_lhs_generalises_rhs
    using initial_lits_generalize_learned_lits[unfolded hyps(1,2), unfolded state_proj_simp]
    by metis

  have L_in: "L \<in># C" and L_undef: "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
    using hyps(3-)
    by (simp_all add: linorder_lit.is_minimal_in_mset_iff)
  hence L_from_N: "L \<in> \<Union> (set_mset ` fset N)"
    using lit_from_N_if_in_C by metis

  have "scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>) s s'"
    unfolding hyps(1,2)
  proof (rule scl_fol.decideI')
    show "is_ground_lit (lit_of_glit L \<cdot>l Var)"
      by simp
  next
    show "\<not> trail_defined_lit \<Gamma> (lit_of_glit L \<cdot>l Var)"
      using L_undef by simp
  next
    show "less_B\<^sup>=\<^sup>= (atm_of (lit_of_glit L) \<cdot>a Var) (term_of_gterm \<beta>)"
      using bounded L_from_N
      by (auto simp add: less_B_def atm_of_lit_of_glit_conv cls_of_gcls_def
          inj_image_mem_iff[OF inj_lit_of_glit])
  next
    show "\<Gamma>' = trail_decide \<Gamma> (lit_of_glit L \<cdot>l Var)"
      using hyps(3-) by simp
  qed
  thus ?thesis
    by (simp add: scl_fol.scl_def)
next
  case hyps: (expand_model_for_pos_lit_when_not_max NU U \<Gamma> C L \<Gamma>')

  have C_in: "C |\<in>| N |\<union>| gcls_of_cls |`| U"
    using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis
  hence lit_from_N_if_in_C: "\<And>L. L \<in># C \<Longrightarrow> L \<in> \<Union> (set_mset ` fset N)"
    using lit_in_lhs_if_lhs_generalises_rhs
    using initial_lits_generalize_learned_lits[unfolded hyps(1,2), unfolded state_proj_simp]
    by metis

  have L_in: "L \<in># C" and L_undef: "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
    using hyps(3-)
    by (simp_all add: linorder_lit.is_minimal_in_mset_iff)
  hence L_from_N: "L \<in> \<Union> (set_mset ` fset N)"
    using lit_from_N_if_in_C by metis

  have "scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>) s s'"
    unfolding hyps(1,2)
  proof (rule scl_fol.decideI')
    show "is_ground_lit (lit_of_glit (- L) \<cdot>l Var)"
      by simp
  next
    have  "\<not> trail_defined_lit \<Gamma> (lit_of_glit (- L))"
      using L_undef
      by (cases L) (simp_all add: lit_of_glit_def trail_defined_lit_def)
    thus "\<not> trail_defined_lit \<Gamma> (lit_of_glit (- L) \<cdot>l Var)"
      by simp
  next
    show "less_B\<^sup>=\<^sup>= (atm_of (lit_of_glit (- L)) \<cdot>a Var) (term_of_gterm \<beta>)"
      using bounded L_from_N
      by (auto simp add: less_B_def atm_of_lit_of_glit_conv cls_of_gcls_def
          inj_image_mem_iff[OF inj_lit_of_glit])
  next
    show "\<Gamma>' = trail_decide \<Gamma> (lit_of_glit (- L) \<cdot>l Var)"
      using hyps(3-) by simp
  qed
  thus ?thesis
    by (simp add: scl_fol.scl_def)
next
  case hyps: (expand_model_for_pos_lit_when_max NU U \<Gamma> C L \<Gamma>')

  have learned_ground: "\<forall>C |\<in>| state_learned s. is_ground_cls C"
    using initial_lits_generalize_learned_lits
      ball_ground_cls_if_lits_generalized_from_ground_clauses
    by metis

  have C_in: "C |\<in>| N |\<union>| gcls_of_cls |`| U"
    using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis
  hence lit_from_N_if_in_C: "\<And>L. L \<in># C \<Longrightarrow> L \<in> \<Union> (set_mset ` fset N)"
    using lit_in_lhs_if_lhs_generalises_rhs
    using initial_lits_generalize_learned_lits[unfolded hyps(1,2), unfolded state_proj_simp]
    by metis

  have L_in: "L \<in># C" and L_undef: "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
    using hyps(3-)
    by (simp_all add: linorder_lit.is_minimal_in_mset_iff)
  hence L_from_N: "L \<in> \<Union> (set_mset ` fset N)"
    using lit_from_N_if_in_C by metis

  show ?thesis
  proof (cases "\<exists>D|\<in>|NU. trail_false_cls (trail_decide \<Gamma> (lit_of_glit L)) (cls_of_gcls D)")
    case True
    have "scl_fol.propagate (cls_of_gcls |`| N) (term_of_gterm \<beta>) s s'"
      unfolding hyps(1,2)
    proof (rule scl_fol.propagateI')
      have "C |\<in>| N |\<union>| gcls_of_cls |`| U"
        using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by blast
      thus "cls_of_gcls C |\<in>| cls_of_gcls |`| N |\<union>| U"
        using learned_ground hyps(1) by auto
    next
      show "cls_of_gcls C = add_mset (lit_of_glit L) (cls_of_gcls (C - {#L#}))"
        using hyps(3-)
        by (metis cls_of_gcls_def image_mset_add_mset insert_DiffM
            linorder_lit.is_maximal_in_mset_iff)
    next
      show "is_ground_cls (cls_of_gcls C \<cdot> Var)"
        by simp
    next
      show "\<forall>K\<in>#cls_of_gcls C \<cdot> Var. less_B\<^sup>=\<^sup>= (atm_of K) (term_of_gterm \<beta>)"
        using bounded lit_from_N_if_in_C
        by (auto simp add: less_B_def atm_of_lit_of_glit_conv cls_of_gcls_def
            inj_image_mem_iff[OF inj_lit_of_glit])
    next
      show "
        {#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var \<noteq> lit_of_glit L \<cdot>l Var#} =
        {#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var \<noteq> lit_of_glit L \<cdot>l Var#}"
        ..
    next
      show "
        {#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var = lit_of_glit L \<cdot>l Var#} =
        {#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var = lit_of_glit L \<cdot>l Var#}"
        ..
    next
      have "\<not> trail_true_cls \<Gamma> (cls_of_gcls C)"
        using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(2) by blast
      hence "\<forall>K \<in># C. \<not> trail_true_lit \<Gamma> (lit_of_glit K)"
        unfolding trail_true_cls_def by (simp add: cls_of_gcls_def)
      hence "\<forall>K \<in># C. trail_false_lit \<Gamma> (lit_of_glit K) \<or> \<not> trail_defined_lit \<Gamma> (lit_of_glit K)"
        using trail_defined_lit_iff_true_or_false by blast

      moreover have "\<forall>K \<in># C. K \<prec>\<^sub>l L \<longrightarrow> trail_defined_lit \<Gamma> (lit_of_glit K)"
        using hyps(3-) linorder_lit.is_minimal_in_mset_iff by auto

      moreover have "\<forall>K \<in># C. K \<preceq>\<^sub>l L"
        using hyps(3-) linorder_lit.is_maximal_in_mset_iff by auto

      ultimately have "\<forall>K \<in># C. K \<noteq> L \<longrightarrow> trail_false_lit \<Gamma> (lit_of_glit K)"
        by auto
      hence "trail_false_cls \<Gamma> (cls_of_gcls {#K \<in># C. K \<noteq> L#})"
        by (simp add: trail_false_cls_def cls_of_gcls_def)

      moreover have "{#K \<in># cls_of_gcls (remove1_mset L C). K \<noteq> lit_of_glit L#} =
        cls_of_gcls {#K \<in># C. K \<noteq> L#}"
        by (smt (verit, ccfv_SIG) cls_of_gcls_def filter_mset_add_mset filter_mset_cong0
            glit_of_lit_lit_of_glit hyps(7) image_mset_filter_mset_swap insert_DiffM
            linorder_lit.is_maximal_in_mset_iff)

      ultimately show "trail_false_cls \<Gamma>
        ({#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var \<noteq> lit_of_glit L \<cdot>l Var#} \<cdot> Var)"
        by (smt (verit, best) filter_mset_cong0 subst_cls_id_subst subst_lit_id_subst)
    next
      show "\<not> trail_defined_lit \<Gamma> (lit_of_glit L \<cdot>l Var)"
        using hyps(3-) linorder_lit.is_minimal_in_mset_iff by simp
    next
      have AAA: "atm_of ` set_mset (add_mset (lit_of_glit L)
        {#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var = lit_of_glit L \<cdot>l Var#}) =
        {atm_of (lit_of_glit L)}"
        by auto
      show "SCL_FOL.is_imgu Var {atm_of ` set_mset (add_mset (lit_of_glit L)
        {#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var = lit_of_glit L \<cdot>l Var#})}"
        unfolding AAA
        using is_imgu_if_mgu_eq_Some mgu_same by fastforce
    next
      have AAA: "{#K \<in># image_mset lit_of_glit (remove1_mset L C). K \<noteq> lit_of_glit L#} =
        image_mset lit_of_glit {#K \<in># C. K \<noteq> L#}"
        by (smt (verit, ccfv_SIG) filter_mset_add_mset filter_mset_cong0 glit_of_lit_lit_of_glit
            hyps(7) image_mset_filter_mset_swap insert_DiffM linorder_lit.is_maximal_in_mset_iff)
      show "\<Gamma>' = trail_propagate \<Gamma> (lit_of_glit L \<cdot>l Var)
        ({#K \<in># cls_of_gcls (remove1_mset L C). K \<cdot>l Var \<noteq> lit_of_glit L \<cdot>l Var#} \<cdot> Var) Var"
        using hyps(3-) True
        by (simp add: cls_of_gcls_def AAA)
    qed
    thus ?thesis
      by (simp add: scl_fol.scl_def)
  next
    case False
    have "scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>) s s'"
      unfolding hyps(1,2)
    proof (rule scl_fol.decideI')
      show "is_ground_lit (lit_of_glit L \<cdot>l Var)"
        by simp
    next
      show "\<not> trail_defined_lit \<Gamma> (lit_of_glit L \<cdot>l Var)"
        using hyps(3-) linorder_lit.is_minimal_in_mset_iff by simp
    next
      show "less_B\<^sup>=\<^sup>= (atm_of (lit_of_glit L) \<cdot>a Var) (term_of_gterm \<beta>)"
        using bounded L_from_N
        by (auto simp add: less_B_def atm_of_lit_of_glit_conv cls_of_gcls_def
            inj_image_mem_iff[OF inj_lit_of_glit])
    next
      show "\<Gamma>' = trail_decide \<Gamma> (lit_of_glit L \<cdot>l Var)"
        using hyps(3-) False by simp
    qed
    thus ?thesis
      by (simp add: scl_fol.scl_def)
  qed
next
  case hyps: (conflict NU U \<Gamma> C)

  have learned_ground: "\<forall>C |\<in>| state_learned s. is_ground_cls C"
    using initial_lits_generalize_learned_lits
      ball_ground_cls_if_lits_generalized_from_ground_clauses
    by metis

  have "scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) s s'"
    unfolding hyps(1,2)
  proof (rule scl_fol.conflictI)
    have "C |\<in>| N |\<union>| gcls_of_cls |`| U"
      using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis
    thus "cls_of_gcls C |\<in>| cls_of_gcls |`| N |\<union>| U"
      using learned_ground hyps(1) by auto
  next
    show "is_ground_cls (cls_of_gcls C \<cdot> Var)"
      by simp
  next
    show "trail_false_cls \<Gamma> (cls_of_gcls C \<cdot> Var)"
      using hyps(3-) by simp
  qed
  thus ?thesis
    by (simp add: scl_fol.scl_def)
next
  case (resolve \<Gamma> U C C')
  thus ?thesis
    by (simp add: scl_fol.scl_def)
next
  case (skip \<Gamma> U C \<Gamma>')
  thus ?thesis
    by (simp add: scl_fol.scl_def)
next
  case (backtrack \<Gamma> U C U')
  thus ?thesis
    by (simp add: scl_fol.scl_def)
qed


definition less_cls_sfac where
  "less_cls_sfac \<F> C D \<longleftrightarrow> \<F> C \<prec>\<^sub>c \<F> D \<or> (\<F> C = \<F> D \<and> C \<prec>\<^sub>c D)"

lemma transp_on_apply_closed_function:
  assumes trans: "transp_on X R" and closed: "\<And>x. x \<in> X \<Longrightarrow> \<F> x \<in> X"
  shows "transp_on X (\<lambda>x y. R (\<F> x) (\<F> y) \<or> (\<F> x = \<F> y \<and> R x y))"
proof (rule transp_onI)
  fix x y z
  assume "x \<in> X" "y \<in> X" "z \<in> X"
  then show "R (\<F> x) (\<F> y) \<or> \<F> x = \<F> y \<and> R x y \<Longrightarrow>
       R (\<F> y) (\<F> z) \<or> \<F> y = \<F> z \<and> R y z \<Longrightarrow>
       R (\<F> x) (\<F> z) \<or> \<F> x = \<F> z \<and> R x z"
    using trans[THEN transp_onD] closed by metis
qed

lemma asymp_on_apply_closed_function:
  assumes asym: "asymp_on X R" and closed: "\<And>x. x \<in> X \<Longrightarrow> \<F> x \<in> X"
  shows "asymp_on X (\<lambda>x y. R (\<F> x) (\<F> y) \<or> (\<F> x = \<F> y \<and> R x y))"
proof (rule asymp_onI)
  fix x y
  assume "x \<in> X" "y \<in> X"
  then show "R (\<F> x) (\<F> y) \<or> \<F> x = \<F> y \<and> R x y \<Longrightarrow> \<not> (R (\<F> y) (\<F> x) \<or> \<F> y = \<F> x \<and> R y x)"
    using asym[THEN asymp_onD] closed by metis
qed

lemma totalp_on_iff: "totalp_on X R \<longleftrightarrow> (\<forall>x y. x \<in> X \<longrightarrow> y \<in> X \<longrightarrow> R x y \<or> x = y \<or> R y x)"
proof (intro iffI allI impI)
  assume total: "totalp_on X R"
  show "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> R x y \<or> x = y \<or> R y x"
    using total[THEN totalp_onD] by metis
next
  assume "\<forall>x y. x \<in> X \<longrightarrow> y \<in> X \<longrightarrow> R x y \<or> x = y \<or> R y x"
  thus "totalp_on X R"
    by (metis totalp_onI)
qed

lemma totalp_on_apply_closed_function:
  assumes total: "totalp_on X R" and closed: "\<And>x. x \<in> X \<Longrightarrow> \<F> x \<in> X"
  shows "totalp_on X (\<lambda>x y. R (\<F> x) (\<F> y) \<or> (\<F> x = \<F> y \<and> R x y))"
  using assms
  unfolding totalp_on_iff
  by metis

lemma less_cls_sfac_total_order:
  fixes \<F> :: "'f gterm clause \<Rightarrow> 'f gterm clause"
  shows
    "transp_on X (less_cls_sfac \<F>)" and
    "asymp_on X (less_cls_sfac \<F>)" and
    "totalp_on X (less_cls_sfac \<F>)"
  using transp_on_apply_closed_function[of UNIV "(\<prec>\<^sub>c)" \<F>, THEN transp_on_subset, of X, simplified]
  using asymp_on_apply_closed_function[of UNIV "(\<prec>\<^sub>c)" \<F>, THEN asymp_on_subset, of X, simplified]
  using totalp_on_apply_closed_function[of UNIV "(\<prec>\<^sub>c)" \<F>, THEN totalp_on_subset, of X, simplified]
  unfolding less_cls_sfac_def
  by argo+

interpretation linorder_cls_sfac: linorder "(less_cls_sfac \<F>)\<^sup>=\<^sup>=" "less_cls_sfac \<F>"
proof unfold_locales
  show "\<And>x y. less_cls_sfac \<F> x y = ((less_cls_sfac \<F>)\<^sup>=\<^sup>= x y \<and> \<not> (less_cls_sfac \<F>)\<^sup>=\<^sup>= y x)"
    by (metis asympD less_cls_sfac_total_order(2) reflclp_iff)
next
  show "\<And>x. (less_cls_sfac \<F>)\<^sup>=\<^sup>= x x"
    by simp
next
  show "\<And>x y z. (less_cls_sfac \<F>)\<^sup>=\<^sup>= x y \<Longrightarrow> (less_cls_sfac \<F>)\<^sup>=\<^sup>= y z \<Longrightarrow> (less_cls_sfac \<F>)\<^sup>=\<^sup>= x z"
    by (meson transpE less_cls_sfac_total_order(1) transp_on_reflclp)
next
  show "\<And>x y. (less_cls_sfac \<F>)\<^sup>=\<^sup>= x y \<Longrightarrow> (less_cls_sfac \<F>)\<^sup>=\<^sup>= y x \<Longrightarrow> x = y"
    by (metis asympD less_cls_sfac_total_order(2) reflclp_iff)
next
  show "\<And>x y. (less_cls_sfac \<F>)\<^sup>=\<^sup>= x y \<or> (less_cls_sfac \<F>)\<^sup>=\<^sup>= y x"
    by (metis less_cls_sfac_total_order(3) reflclp_iff totalpD)
qed

lemma
  fixes \<F> :: "'f gterm clause \<Rightarrow> 'f gterm clause"
  shows "less_cls_sfac \<F> C D \<and> \<not> fBex N (\<lambda>D'. less_cls_sfac \<F> C D' \<and> less_cls_sfac \<F> D' D) \<and>
    D |\<in>| N \<longleftrightarrow> is_least_in_fset_wrt (less_cls_sfac \<F>) {|D |\<in>| N. less_cls_sfac \<F> C D|} D"
proof (intro iffI; (elim conjE)?)
  assume C_lt_D: "less_cls_sfac \<F> C D" and
    no_middle: "\<not> (\<exists>D' |\<in>| N. less_cls_sfac \<F> C D' \<and> less_cls_sfac \<F> D' D)" and
    D_in: "D |\<in>| N"

  have "D |\<in>| {|D |\<in>| N. less_cls_sfac \<F> C D|}"
    using C_lt_D D_in by simp

  moreover have "\<forall>y |\<in>| {|D |\<in>| N. less_cls_sfac \<F> C D|}. y \<noteq> D \<longrightarrow> less_cls_sfac \<F> D y"
  proof (intro ballI impI)
    fix D' assume "D' |\<in>| {|D |\<in>| N. less_cls_sfac \<F> C D|}"
    hence "D' |\<in>| N" "less_cls_sfac \<F> C D'"
      by simp_all
    hence "\<not> less_cls_sfac \<F> D' D"
      using no_middle by metis
    then show "D' \<noteq> D \<Longrightarrow> less_cls_sfac \<F> D D'"
      using less_cls_sfac_def by order
  qed

  ultimately show "is_least_in_fset_wrt (less_cls_sfac \<F>) {|D |\<in>| N. less_cls_sfac \<F> C D|} D"
    using is_least_in_fset_wrt_iff[OF less_cls_sfac_total_order] by metis
next
  assume "is_least_in_fset_wrt (less_cls_sfac \<F>) {|D |\<in>| N. less_cls_sfac \<F> C D|} D"
  thus "less_cls_sfac \<F> C D \<and> \<not> (\<exists>D'|\<in>|N. less_cls_sfac \<F> C D' \<and> less_cls_sfac \<F> D' D) \<and> D |\<in>| N"
    using is_least_in_fset_wrt_iff[OF less_cls_sfac_total_order]
    by (metis ffmember_filter linorder_cls_sfac.dual_order.asym)
qed

thm linorder_lit.ex1_sorted_list_for_set_if_finite
  linorder_lit.ex1_sorted_list_for_fset
find_theorems "(The ?P) = _"
find_theorems "Ex1 ?P \<longleftrightarrow> _ (Uniq ?P)"

find_consts "_ set \<Rightarrow> _ list"
find_theorems "sorted_key_list_of_set"

term "THE xs. sorted_wrt (\<prec>\<^sub>l) xs \<and> fset_of_list xs =
  {|K |\<in>| lits_of_clss N. is_neg K \<and> K \<prec>\<^sub>l L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit K)|}"

inductive scl_reso1
  :: "_ \<Rightarrow> _ \<Rightarrow>
    ('f, 'v) scl_fol_sim_state \<Rightarrow>
    ('f, 'v) scl_fol_sim_state \<Rightarrow>
    ('f, 'v) scl_fol_sim_state \<Rightarrow> bool" for N\<^sub>0 \<beta> where
  scl_reso1I: "
  is_least_in_fset_wrt (less_cls_sfac \<F>)
    {|D |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. less_cls_sfac \<F> C D|} D \<Longrightarrow>
  ord_res.is_maximal_lit L D \<Longrightarrow>
  sorted_wrt (\<prec>\<^sub>l) Ks \<Longrightarrow>
  fset_of_list Ks = {|K |\<in>| lits_of_clss N\<^sub>0. is_neg K \<and> K \<prec>\<^sub>l L \<and>
    \<not> trail_defined_lit \<Gamma> (lit_of_glit K)|} \<Longrightarrow>
  \<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks) \<Longrightarrow>
  S1 = ((\<Gamma>\<^sub>1, U, None :: ('f, 'v) closure option), i, D, \<F>) \<Longrightarrow>
  (res_mo_strategy ^^ i) N\<^sub>0 N\<^sub>i \<Longrightarrow>
  \<F> D |\<in>| N\<^sub>i \<Longrightarrow>
  sfac D = sfac (\<F> D) \<Longrightarrow>
  S2 =
    (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
      trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
      (let
        \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
        \<F>' = \<F>(D := add_mset L {#K \<in># D. K \<noteq> L#});
        j = i + count (\<F> D - {#L#}) L
      in
        if (\<nexists>S'. scl_fol.conflict (cls_of_gcls |`| N\<^sub>0) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) S') then
          \<comment> \<open>2a\<close>
          ((\<Gamma>\<^sub>2\<^sub>a, U, None :: ('f, 'v) closure option), j, D, \<F>')
        else
          \<comment> \<open>2b\<close>
          (let
            \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
            E = (THE E. is_least_in_fset_wrt (\<prec>\<^sub>c)
              {|C |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} E)
          in
            ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')))
    else
      \<comment> \<open>2c\<close>
      S1) \<Longrightarrow>
  scl_reso1 N\<^sub>0 \<beta> ((\<Gamma>, U, None :: ('f, 'v) closure option), i, C, \<F>) S1 S2"

lemma scl_reso1_step2_cases[case_names case2a case2b case2c]:
  fixes \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2\<^sub>a Ks L
  defines
    "\<Gamma>\<^sub>1 \<equiv> foldl trail_decide \<Gamma> (map lit_of_glit Ks)" and
    "\<Gamma>\<^sub>2\<^sub>a \<equiv> trail_decide \<Gamma>\<^sub>1 (lit_of_glit L)"
  assumes
    case2a: "is_pos L \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<Longrightarrow>
      trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) \<Longrightarrow>
      (\<nexists>S'. scl_fol.conflict (cls_of_gcls |`| N\<^sub>0) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) S')\<Longrightarrow> thesis" and
    case2b: "is_pos L \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<Longrightarrow>
      trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) \<Longrightarrow>
      (\<exists>S'. scl_fol.conflict (cls_of_gcls |`| N\<^sub>0) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) S')\<Longrightarrow> thesis" and
    case2c: "\<not> is_pos L \<or> trail_defined_lit \<Gamma> (lit_of_glit L) \<or>
      \<not> trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) \<Longrightarrow> thesis"
  shows thesis
  using assms by argo

lemma scl_reso1_simple_destroy:
  assumes "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)"
  shows
    "state_learned S\<^sub>1 = state_learned S\<^sub>0"
    "state_learned S\<^sub>2 = state_learned S\<^sub>1" and
    "i\<^sub>1 = i\<^sub>0" and
    "i\<^sub>2 \<ge> i\<^sub>1" and
    "C\<^sub>2 = C\<^sub>1"
  unfolding atomize_conj conj_assoc
  using assms
proof (cases rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  note \<Gamma>\<^sub>1_def = \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks)\<close>
  note state2_eq = hyps(11)

  have "state_learned S\<^sub>0 = U"
    using \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close> by simp

  moreover have "state_learned S\<^sub>1 = U" and "i\<^sub>1 = i\<^sub>0" and "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp_all

  moreover have "state_learned S\<^sub>2 = U \<and> i\<^sub>0 \<le> i\<^sub>2 \<and> C\<^sub>2 = D"
  proof (cases rule: scl_reso1_step2_cases[of L \<Gamma> Ks D N \<beta> U])
    case case2a
    then show ?thesis
      using state2_eq
      unfolding Let_def
      by (simp add: \<Gamma>\<^sub>1_def)
  next
    case case2b
    then show ?thesis
      using state2_eq
      unfolding Let_def
      by (simp add: \<Gamma>\<^sub>1_def)
  next
    case case2c
    then show ?thesis
      using state2_eq
      by (auto simp: \<Gamma>\<^sub>1_def \<open>state_learned S\<^sub>1 = U\<close> \<open>i\<^sub>1 = i\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>)
  qed

  ultimately show "state_learned S\<^sub>1 = state_learned S\<^sub>0 \<and> state_learned S\<^sub>2 = state_learned S\<^sub>1 \<and>
    i\<^sub>1 = i\<^sub>0 \<and> i\<^sub>2 \<ge> i\<^sub>1 \<and> C\<^sub>2 = C\<^sub>1"
    by metis
qed

lemma scl_reso1_\<F>_eq:
  assumes "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)"
  shows
    "\<F>\<^sub>1 = \<F>\<^sub>0"
    "\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#}))"
  unfolding atomize_conj
  using assms
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  note \<Gamma>\<^sub>1_def = \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks)\<close>
  note state2_eq = hyps(11)

  have "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp

  have "\<F>\<^sub>1 = \<F>\<^sub>0"
    using hyps(7) by simp
  thus "\<F>\<^sub>1 = \<F>\<^sub>0 \<and>
    (\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#})))"
  proof (intro conjI)
    show "\<F>\<^sub>2 = \<F>\<^sub>1 \<or>
      (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#}))"
    proof (cases rule: scl_reso1_step2_cases[of L \<Gamma> Ks D N \<beta> U])
      case case2a
      then show ?thesis
        using state2_eq
        unfolding Let_def
        unfolding \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>
        using hyps(3) hyps(6) by auto
    next
      case case2b
      then show ?thesis
        using state2_eq
        unfolding Let_def
        using hyps(3) hyps(6) hyps(7) by auto
    next
      case case2c
      then show ?thesis
        using \<Gamma>\<^sub>1_def hyps(11) by auto
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

lemma ffilter_neq_constant_eq: "{|x |\<in>| X. x \<noteq> y|} = X - {|y|}"
  by auto

lemma ffilter_ffilter:"ffilter P (ffilter Q X) = ffilter (\<lambda>x. P x \<and> Q x) X"
  by auto

lemma trail_undefined_lit_and_atm_neq_iff:
  "\<not> trail_defined_lit \<Gamma> L \<and> atm_of L \<noteq> atm_of K \<longleftrightarrow> \<not> trail_defined_lit (trail_decide \<Gamma> K) L"
  unfolding decide_lit_def
  unfolding trail_defined_lit_def
  apply simp
  by (metis atm_of_eq_atm_of)

lemma atm_of_lit_of_glit_eq_atm_of_lit_of_glit:
  "(atm_of (lit_of_glit L) :: ('f, 'v) Term.term) = atm_of (lit_of_glit K) \<longleftrightarrow>
    atm_of L = atm_of K"
  by (metis atm_of_lit_of_glit_conv term_of_gterm_inv)

lemma fset_of_list_Cons_eq_ffilterD:
  assumes
    sorted: "sorted_wrt (\<prec>\<^sub>l) (K # Ks)" and
    fset_eq: "fset_of_list (K # Ks) = {|K |\<in>| lits_of_clss N. is_neg K \<and> K \<prec>\<^sub>l L \<and>
      \<not> trail_defined_lit \<Gamma> (lit_of_glit K)|}"
  shows "fset_of_list Ks = {|Ka |\<in>| lits_of_clss N. is_neg Ka \<and> Ka \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)|}"
proof -
  have "is_neg K"
    using fset_eq
    by (metis (no_types, lifting) ffmember_filter fset_of_list.rep_eq list.set_intros(1))

  have "fset_of_list Ks = {|K |\<in>| lits_of_clss N. is_neg K \<and> K \<prec>\<^sub>l L \<and>
          \<not> trail_defined_lit \<Gamma> (lit_of_glit K)|} - {|K|}"
    using sorted fset_eq
    by (metis fminus_finsert_absorb fset_of_list.rep_eq fset_of_list_simps(2)
        linorder_lit.dual_order.strict_implies_not_eq linorder_lit.strict_sorted_simps(2))
  also have "\<dots> = {|x |\<in>| lits_of_clss N. is_neg x \<and> x \<prec>\<^sub>l L \<and>
          \<not> trail_defined_lit \<Gamma> (lit_of_glit x) \<and> x \<noteq> K|}"
    unfolding ffilter_neq_constant_eq[symmetric]
    unfolding ffilter_ffilter
    unfolding eq_ffilter
    by auto
  also have "\<dots> = {|x |\<in>| lits_of_clss N. is_neg x \<and> x \<prec>\<^sub>l L \<and>
          \<not> trail_defined_lit \<Gamma> (lit_of_glit x) \<and> atm_of x \<noteq> atm_of K|}"
    using \<open>is_neg K\<close>
    by (metis literal.expand)
  also have "\<dots> = {|x |\<in>| lits_of_clss N. is_neg x \<and> x \<prec>\<^sub>l L \<and>
          \<not> trail_defined_lit \<Gamma> (lit_of_glit x) \<and>
          (atm_of (lit_of_glit x) :: ('f, 'v) Term.term) \<noteq> atm_of (lit_of_glit K)|}"
    unfolding atm_of_lit_of_glit_eq_atm_of_lit_of_glit
    by argo
  also have "\<dots> = {|x |\<in>| lits_of_clss N. is_neg x \<and> x \<prec>\<^sub>l L \<and>
          \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit x)|}"
    using trail_undefined_lit_and_atm_neq_iff[of \<Gamma>]
    by (smt (verit) atm_of_lit_of_glit_conv eq_ffilter term_of_gterm_inv)
  finally show ?thesis
    by metis
qed

lemma correctness_scl_reso1:
  fixes N :: "'f gterm clause fset" and \<beta> :: "'f gterm"
  defines "N' \<equiv> fimage cls_of_gcls N" and "\<beta>' \<equiv> term_of_gterm \<beta>"
  assumes
    \<beta>_greatereq: "\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>" and
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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)

  from hyps have D_least: "is_least_in_fset_wrt (less_cls_sfac \<F>\<^sub>0)
    (ffilter (less_cls_sfac \<F>\<^sub>0 C\<^sub>0) (N |\<union>| gcls_of_cls |`| U)) D"
    by argo

  from hyps have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
  proof (induction Ks arbitrary: S\<^sub>0 \<Gamma>)
    case Nil
    hence "S\<^sub>1 = S\<^sub>0"
      by simp
    thus ?case
      by simp
  next
    case (Cons K Ks)
    note ball_K_Ks = \<open>fset_of_list (K # Ks) = {|K |\<in>| lits_of_clss N. is_neg K \<and> K \<prec>\<^sub>l L \<and>
      \<not> trail_defined_lit \<Gamma> (lit_of_glit K)|}\<close>

    from ball_K_Ks have
      "is_neg K" "K \<prec>\<^sub>l L" "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)" "K |\<in>| lits_of_clss N"
      by auto

    from Cons.prems have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* (trail_decide \<Gamma> (lit_of_glit K), U, None) S\<^sub>1"
    proof (intro Cons.IH[OF refl] ballI)
      show "sorted_wrt (\<prec>\<^sub>l) Ks"
        using \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> by simp
    next
      show "fset_of_list Ks = {|Ka |\<in>| lits_of_clss N. is_neg Ka \<and> Ka \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)|}"
        using Cons.prems(4) ball_K_Ks fset_of_list_Cons_eq_ffilterD by blast
    next
      show "\<Gamma>\<^sub>1 = foldl trail_decide (trail_decide \<Gamma> (lit_of_glit K)) (map lit_of_glit Ks)"
        by (simp add: \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>)
    next
      assume hyp: "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and> trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
          let \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
              \<F>' = \<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#});
              j = i\<^sub>0 + count (remove1_mset L (\<F>\<^sub>0 D)) L
          in
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              let
                \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
                E = THE a. linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} a
              in
                ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
        else
          (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
      show "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (if is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and> trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
          let
            \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
            \<F>' = \<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#});
            j = i\<^sub>0 + count (remove1_mset L (\<F>\<^sub>0 D)) L
          in
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              let
                \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
                E = THE a. linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} a
              in
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
    proof (intro scl_fol.decideI[of _ Var, simplified])
      show "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> .
    next
      show "is_ground_lit (lit_of_glit K)"
        by (cases K) (simp_all add: is_ground_lit_def atm_of_lit_of_glit_conv)
    next
      have "atm_of K |\<in>| atms_of_clss N"
        using \<open>K |\<in>| lits_of_clss N\<close>
        by (metis (no_types, opaque_lifting) atms_of_cls_def atms_of_clss_def fimage_eqI
            fmember_ffUnion_iff lits_of_clss_def)
      thus "less_B (atm_of (lit_of_glit K)) \<beta>' \<or> atm_of (lit_of_glit K) = \<beta>'"
        unfolding less_B_def
        using \<beta>_greatereq \<beta>'_def
        by (auto simp add: atm_of_lit_of_glit_conv)
    qed

    ultimately show ?case
      unfolding \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close> \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close>
        \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>
      by simp
  qed

  from hyps have S\<^sub>1_def: "S\<^sub>1 = (\<Gamma>\<^sub>1, U, None)"
    by simp

  have "distinct Ks"
    using \<open>sorted_wrt (\<prec>\<^sub>l) Ks\<close> linorder_lit.strict_sorted_iff by metis
  moreover have "\<And>x. x \<in> set Ks \<Longrightarrow> is_neg x"
    using hyps(5)
    by (metis (no_types, lifting) ffmember_filter fset_of_list.rep_eq)
  ultimately have "distinct (map atm_of Ks)"
  proof (induction Ks)
    case Nil
    show ?case
      by simp
  next
    case (Cons Ka Ks)
    have "atm_of Ka \<notin> set (map atm_of Ks)"
      by (metis Cons.prems(1) Cons.prems(2) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          distinct.simps(2) insert_iff is_pos_neg_not_is_pos list.set_map list.simps(15))
    moreover have "distinct (map atm_of Ks)"
      using Cons.IH Cons.prems by simp
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
      using \<open>(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1\<close> invars
      by (induction S\<^sub>1 rule: rtranclp_induct)
        (simp_all add: scl_fol.decide_preserves_initial_lits_generalize_learned_trail_conflict)
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

    from D_least have "D |\<in>| N \<or> D |\<in>| gcls_of_cls |`| U"
      using linorder_cls_sfac.is_least_in_fset_ffilterD(1) by fast
    hence "cls_of_gcls D |\<in>| N' |\<union>| U"
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
      by (simp only: linorder_lit.is_maximal_in_mset_iff)

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
      let ?j = "i\<^sub>0 + count (\<F>\<^sub>0 D - {#L#}) L"

      obtain D' :: "('f, 'v) term clause" where
        "cls_of_gcls D = add_mset (lit_of_glit L) D'"
        by (metis cls_of_gcls_def hyps(3) image_mset_add_mset insert_DiffM
            linorder_lit.is_maximal_in_mset_iff)

      have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
        using pos_L_and_undef_L_and_false_D by argo
      have "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)"
        unfolding \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks)\<close>
        using hyps(4,5) pos_L_and_undef_L_and_false_D \<open>distinct (map atm_of Ks)\<close>
      proof (induction Ks arbitrary: \<Gamma>)
        case Nil
        thus ?case
          by simp
      next
        case (Cons K Ks)
        show ?case
          unfolding list.map foldl_Cons
        proof (intro Cons.IH ballI conjI)
          show "sorted_wrt (\<prec>\<^sub>l) Ks"
            using Cons.prems by simp
        next
          show "is_pos L"
            "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L)"
            "trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
            unfolding atomize_conj
            using Cons.prems undefined_in_trail_decide_if_undefined_in_trail_and_less_lit_pos
            by (metis (no_types, lifting) ffmember_filter fset_of_list.rep_eq list.set_intros(1))
        next
          show "distinct (map atm_of Ks)"
            using Cons.prems by simp
        next
          show "fset_of_list Ks = {|Ka |\<in>| lits_of_clss N. is_neg Ka \<and> Ka \<prec>\<^sub>l L \<and>
            \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)|}"
            using Cons.prems fset_of_list_Cons_eq_ffilterD by blast
        qed
      qed

      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (?\<Gamma>\<^sub>2\<^sub>a, U, None))")
        case ex_conflict: True
        have "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = ((?\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls ?E, Var)), ?j, D, ?\<F>')"
          using hyps(11)
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
              using \<beta>_greatereq
              by (auto simp add: \<open>K = lit_of_glit K'\<close> atm_of_lit_of_glit_conv)
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
          proof (rule linorder_cls.ex_least_in_fset)
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
            ultimately show "{|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} \<noteq> {||}"
              by fastforce
          qed
          then obtain E where
            E_least: "is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
              trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} E"
            by metis
          hence "?E = E"
            by (simp add: the1_equality' Uniq_is_least_in_fset_wrt)

          show ?thesis
          proof (rule scl_fol.conflictI)
            have "E |\<in>| N |\<union>| gcls_of_cls |`| U"
              using E_least by (simp add: is_least_in_fset_wrt_iff)
            thus "cls_of_gcls ?E |\<in>| N' |\<union>| U"
              unfolding \<open>?E = E\<close> N'_def
              using ground_cls_if_in_U by auto
          next
            show "is_ground_cls (cls_of_gcls ?E \<cdot> Var)"
              by simp
          next
            have "trail_false_cls ?\<Gamma>\<^sub>2\<^sub>b (cls_of_gcls E)"
              using E_least by (simp add: is_least_in_fset_wrt_iff)
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
          using hyps(11) pos_L_and_undef_L_and_false_D by simp
        moreover have "scl_fol.decide N' \<beta>'
          (\<Gamma>\<^sub>1, U, None) (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L \<cdot>l Var), U, None)"
        proof (rule scl_fol.decideI)
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
          with \<beta>_greatereq show "scl_fol.lesseq_B (atm_of (lit_of_glit L) \<cdot>a Var) \<beta>'"
            by (auto simp add: less_B_def atm_of_lit_of_glit_conv \<beta>'_def)
        qed

        ultimately have "scl_fol.decide N' \<beta>' S\<^sub>1 S\<^sub>2"
          using hyps(7) by fastforce
        thus ?thesis
          by simp
      qed
    next
      case False
      hence "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)"
        using hyps(11) by auto
      thus ?thesis
        by simp
    qed
  qed
qed


subsection \<open>Sematincs of ORD-RES, ORD-RES++, SCL(FOL)++, and SCL(FOL)\<close>

definition ord_res_model where
  "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"

definition ex_false_clause where
  "ex_false_clause N = (\<exists>C \<in> N. \<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C)"

inductive ord_reso_step where
  factoring: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    P |\<in>| N \<Longrightarrow> ord_res.ground_factoring P C \<Longrightarrow>
    ord_reso_step N (finsert C N)" |

  resolution: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    P1 |\<in>| N \<Longrightarrow> P2 |\<in>| N \<Longrightarrow> ord_res.ground_resolution P1 P2 C \<Longrightarrow>
    ord_reso_step N (finsert C N)"

definition ord_reso_final where
  "ord_reso_final N \<longleftrightarrow> {#} |\<in>| N \<or> \<not> ex_false_clause (fset N)"

interpretation ord_reso_semantics: semantics where
  step = ord_reso_step and
  final = ord_reso_final
proof unfold_locales
  fix N
  assume "ord_reso_final N"
  thus "finished ord_reso_step N"
    unfolding ord_reso_final_def
  proof (elim disjE)
    show "{#} |\<in>| N \<Longrightarrow> finished ord_reso_step N"
      by (simp add: finished_def ord_reso_step.simps)
  next
    show "\<not> ex_false_clause (fset N) \<Longrightarrow> finished ord_reso_step N"
      by (simp add: finished_def ord_reso_step.simps)
  qed
qed

definition ord_reso_strategy_step where
  "ord_reso_strategy_step = (\<lambda>(N, s) (N', s').
    N = N' \<and> ord_res_strategy N s s')"

definition ord_reso_strategy_final where
  "ord_reso_strategy_final = (\<lambda>(N, (U, \<I>, C)).
    C = {#} \<or> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<and> \<not> (\<exists>D |\<in>| N |\<union>| U. C \<prec>\<^sub>c D))"

interpretation ord_reso_strategy_semantics: semantics where
  step = ord_reso_strategy_step and
  final = ord_reso_strategy_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm fset \<times> 'f gterm clause"
  obtain N U \<I> C where S_def: "S = (N, U, \<I>, C)"
    by (metis surj_pair)
  assume final: "ord_reso_strategy_final S"
  hence "C = {#} \<or> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<and> \<not> fBex (N |\<union>| U) ((\<prec>\<^sub>c) C)"
    unfolding ord_reso_strategy_final_def by (simp add: S_def)
  thus "finished ord_reso_strategy_step S"
  proof (elim disjE conjE)
    assume "C = {#}"
    hence "\<nexists>s'. ord_res_strategy N (U, \<I>, C) s'"
      by (auto simp: linorder_lit.is_maximal_in_mset_iff elim: ord_res_strategy.cases)
    hence "\<nexists>S'. ord_reso_strategy_step S S'"
      unfolding ord_reso_strategy_step_def by (simp add: S_def)
    thus "finished ord_reso_strategy_step S"
      unfolding finished_def by simp
  next
    assume "fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C" and "\<not> fBex (N |\<union>| U) ((\<prec>\<^sub>c) C)"
    hence "\<nexists>s'. ord_res_strategy N (U, \<I>, C) s'"
      apply (intro notI)
      apply (elim exE ord_res_strategy.cases)
      subgoal for s' U' \<I>' C' D
        using linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2)
        by blast
      subgoal
        by simp
      subgoal
        by simp
      done
    hence "\<nexists>S'. ord_reso_strategy_step S S'"
      unfolding ord_reso_strategy_step_def by (simp add: S_def)
    thus "finished ord_reso_strategy_step S"
      unfolding finished_def by simp
  qed
qed

definition scl_strategy_step where
  "scl_strategy_step = (\<lambda>(N, \<beta>, s) (N', \<beta>', s').
    N = N' \<and> \<beta> = \<beta>' \<and> scl_strategy N \<beta> s s')"

definition scl_strategy_final where
  "scl_strategy_final = (\<lambda>(N, \<beta>, (\<Gamma>, U, \<C>)).
    (case \<C> of
      None \<Rightarrow> (\<forall>C |\<in>| fimage cls_of_gcls N |\<union>| U. trail_true_cls \<Gamma> C)
    | Some (C, \<gamma>) \<Rightarrow> \<Gamma> = [] \<and> C = {#}))"

interpretation scl_strategy_semantics: semantics where
  step = scl_strategy_step and
  final = scl_strategy_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state"
  obtain N \<beta> \<Gamma> U \<C> where S_def: "S = (N, \<beta>, (\<Gamma>, U, \<C>))"
    using prod_cases5 by blast

  have ball_le_\<beta>: "\<forall>L\<in>\<Union> (set_mset ` fset N). atm_of L \<preceq>\<^sub>t \<beta>"
    sorry

  have init_lits_generalize_learned_lits:
    "scl_fol.clss_lits_generalize_clss_lits (fset (cls_of_gcls |`| N))
      (fset (state_learned (\<Gamma>, U, \<C>)))"
    sorry
  hence ball_ground: "\<forall>C |\<in>| U. is_ground_cls C"
    using ball_ground_cls_if_lits_generalized_from_ground_clauses by auto

  assume final: "scl_strategy_final S"
  show "finished scl_strategy_step S"
  proof (cases \<C>)
    case None
    with final have "fBall (cls_of_gcls |`| N |\<union>| U) (trail_true_cls \<Gamma>)"
      unfolding S_def scl_strategy_final_def prod.case by simp
    hence ball_trail_true: "\<forall> C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_true_cls \<Gamma> (cls_of_gcls C)"
      using ball_ground by auto

    have "\<nexists>S'. scl_strategy_step S S'"
    proof (intro notI)
      assume "\<exists>S'. scl_strategy_step S S'"
      then obtain s' where step: "scl_strategy N \<beta> (\<Gamma>, U, \<C>) s'"
        unfolding S_def scl_strategy_step_def by auto
      thus "False"
      proof (cases N \<beta> "(\<Gamma>, U, \<C>)" s' rule: scl_strategy.cases)
        case (expand_model_for_neg_lit NU C L \<Gamma>')
        thus False
          using ball_trail_true
          by (metis linorder_cls.is_least_in_fset_ffilterD(1)
              linorder_cls.is_least_in_fset_ffilterD(2))
      next
        case (expand_model_for_pos_lit_when_not_max NU C L \<Gamma>')
        thus False
          using ball_trail_true
          by (metis linorder_cls.is_least_in_fset_ffilterD(1)
              linorder_cls.is_least_in_fset_ffilterD(2))
      next
        case (expand_model_for_pos_lit_when_max NU C L \<Gamma>')
        thus False
          using ball_trail_true
          by (metis linorder_cls.is_least_in_fset_ffilterD(1)
              linorder_cls.is_least_in_fset_ffilterD(2))
      next
        case (conflict NU C)
        thus False
          using ball_trail_true
          by (metis linorder_cls.is_least_in_fset_ffilterD(1)
              linorder_cls.is_least_in_fset_ffilterD(2))
      next
        case (resolve C C')
        thus False
          using None by simp
      next
        case (skip C \<Gamma>')
        then show ?thesis
          using None by simp
      next
        case (backtrack C U')
        then show ?thesis
          using None by simp
      qed
    qed
    thus "finished scl_strategy_step S"
      unfolding finished_def by argo
  next
    case (Some closure)
    with final obtain C \<gamma> where "closure = (C, \<gamma>)" and "\<Gamma> = []" and "C = {#}"
      unfolding S_def scl_strategy_final_def prod.case by auto
    hence "\<nexists>s'. scl_fol.scl (fimage cls_of_gcls N) (term_of_gterm \<beta>) (\<Gamma>, U, \<C>) s'"
      using Some scl_fol.no_more_step_if_conflict_mempty by simp
    hence "\<nexists>S'. scl_strategy_step S S'"
      unfolding scl_strategy_step_def S_def prod.case
      using scl_strategy_restricts_scl ball_le_\<beta> init_lits_generalize_learned_lits
      by fastforce
    thus "finished scl_strategy_step S"
      unfolding finished_def by argo
  qed
qed

interpretation ord_reso_extended_semantics: semantics where
  step = res_mo_strategy and
  final = "\<lambda>N. {#} |\<in>| N"
proof unfold_locales
  fix N :: "'f gterm clause fset" assume "{#} |\<in>| N"
  show "finished res_mo_strategy N"
    unfolding finished_def
  proof (intro notI, elim exE)
    fix N' assume "res_mo_strategy N N'"
    then obtain L C where C_min: "is_min_false_clause N C" and L_max: "ord_res.is_maximal_lit L C"
      unfolding res_mo_strategy_def by metis

    have "is_min_false_clause N {#}"
      unfolding is_min_false_clause_def
      unfolding linorder_cls.is_minimal_in_fset_iff
    proof (intro conjI ballI impI)
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
      by (simp add: linorder_lit.is_maximal_in_mset_iff)
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


subsection \<open>Backward simulation between ORD-RES and ORD-RES strategy\<close>

definition ord_reso_invars where
  "ord_reso_invars S \<longleftrightarrow> True"

lemma ord_reso_step_preserves_invars[intro]:
  "ord_reso_step S S' \<Longrightarrow> ord_reso_invars S \<Longrightarrow> ord_reso_invars S'"
  unfolding ord_reso_invars_def .

definition ord_reso_strategy_invars where
  "ord_reso_strategy_invars = (\<lambda>(N, s).
    (interp_upto s |\<in>| N |\<union>| learned s) \<and>
    (interp_upto s = {#} \<longleftrightarrow> {#} |\<in>| N |\<union>| learned s) \<and>
    (fset (interp s) = ord_res.interp (fset (N |\<union>| learned s)) (interp_upto s)) \<and>
    (\<forall>C|\<in>|N |\<union>| learned s. C \<prec>\<^sub>c interp_upto s \<longrightarrow>
      ord_res.interp (fset (N |\<union>| learned s)) C \<union>
      ord_res.production (fset (N |\<union>| learned s)) C \<TTurnstile> C))"

lemma ord_reso_strategy_step_preserves_invars[intro]:
  "ord_reso_strategy_step S S' \<Longrightarrow> ord_reso_strategy_invars S \<Longrightarrow> ord_reso_strategy_invars S'"
  unfolding ord_reso_strategy_invars_def ord_reso_strategy_step_def
  using ord_res_strategy_preserves_interp_upto_fmember_clauses
  using ord_res_strategy_preserves_interp_upto_eq_fempty_iff_fempty_in_clauses
  using ord_res_strategy_preserves_interp_correct
  using interp_entails_clauses_lt_interp_upto'
  by force

definition match_ord_reso_and_ord_reso_strategy where
  "match_ord_reso_and_ord_reso_strategy = (\<lambda>N1 (N2, (U, \<I>, C)). N1 = N2 |\<union>| U)"

interpretation backward_simulation_with_measuring_function where
  step1 = ord_reso_step and
  step2 = ord_reso_strategy_step and
  final1 = ord_reso_final and
  final2 = ord_reso_strategy_final and
  order = "(|\<subset>|)" and
  match = "\<lambda>S S'. ord_reso_invars S \<and> ord_reso_strategy_invars S' \<and>
    match_ord_reso_and_ord_reso_strategy S S'" and
  measure = "\<lambda>(N, (U, \<I>, C)). {|D |\<in>| N |\<union>| U. C \<prec>\<^sub>c D|}"
proof unfold_locales
  show "wfP (|\<subset>|)"
    by auto
next
  let ?final1 = ord_reso_final
  let ?final2 = ord_reso_strategy_final
  let ?match = "\<lambda>S S'. ord_reso_invars S \<and> ord_reso_strategy_invars S' \<and>
    match_ord_reso_and_ord_reso_strategy S S'"
  fix
    S1 :: "'f gterm clause fset" and
    S2 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm fset \<times> 'f gterm clause"

  obtain N U \<I> C where
    S2_def: "S2 = (N, U, \<I>, C)"
    by (metis prod.exhaust)

  assume "?match S1 S2"
  hence
    invars1: "ord_reso_invars S1" and
    invars2: "ord_reso_strategy_invars S2" and
    match: "match_ord_reso_and_ord_reso_strategy S1 S2"
    by simp_all

  from invars2 have
    C_in: "C |\<in>| N |\<union>| U" and
    \<I>_eq_interp: "fset \<I> = ord_res.interp (fset (N |\<union>| U)) C" and
    ball_interp_prod_entails: "\<forall>x |\<in>| N |\<union>| U. x \<prec>\<^sub>c C \<longrightarrow>
      ord_res.interp (fset (N |\<union>| U)) x \<union> ord_res.production (fset (N |\<union>| U)) x \<TTurnstile> x"
    unfolding ord_reso_strategy_invars_def
    by (auto simp: S2_def)

  from match have S1_def: "S1 = N |\<union>| U"
    unfolding S2_def match_ord_reso_and_ord_reso_strategy_def by auto

  assume "?final2 S2"
  hence "C = {#} \<or> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C \<and> \<not> fBex (N |\<union>| U) ((\<prec>\<^sub>c) C)"
    unfolding ord_reso_strategy_final_def by (simp add: S2_def)
  thus "?final1 S1"
  proof (elim disjE conjE)
    assume "C = {#}"
    hence "{#} |\<in>| S1"
      unfolding S1_def
      using C_in by argo
    thus ?thesis
      unfolding ord_reso_final_def by simp
  next
    assume
      "fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C" and
      "\<not> fBex (N |\<union>| U) ((\<prec>\<^sub>c) C)"
    hence "\<not> ex_false_clause (fset (N |\<union>| U))"
      unfolding ex_false_clause_def
      using ball_interp_prod_entails
      by (metis \<I>_eq_interp linorder_cls.linorder_cases)
    thus ?thesis
      unfolding ord_reso_final_def by (simp add: S1_def)
  qed
next
  let ?step1 = ord_reso_step
  let ?step2 = ord_reso_strategy_step
  let ?less = "(|\<subset>|)"
  let ?match = "\<lambda>S S'. ord_reso_invars S \<and> ord_reso_strategy_invars S' \<and>
    match_ord_reso_and_ord_reso_strategy S S'"
  let ?measure = "\<lambda>(N, (U, \<I>, C)). {|D |\<in>| N |\<union>| U. C \<prec>\<^sub>c D|}"
  fix
    S1 :: "'f gterm clause fset" and
    S2 S2' :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm fset \<times> 'f gterm clause"
  assume "?match S1 S2"
  hence
    invars1: "ord_reso_invars S1" and
    invars2: "ord_reso_strategy_invars S2" and
    match: "match_ord_reso_and_ord_reso_strategy S1 S2"
    by simp_all

  assume step2: "?step2 S2 S2'"
  then obtain N s2 s2' where
    S2_def: "S2 = (N, s2)" and S2'_def: "S2' = (N, s2')" and step2': "ord_res_strategy N s2 s2'"
    unfolding ord_reso_strategy_step_def by blast


  from match have S1_eq: "S1 = N |\<union>| learned s2"
    unfolding S2_def match_ord_reso_and_ord_reso_strategy_def by auto

  from invars2 step2 have invars2': "ord_reso_strategy_invars S2'"
    by auto

  from step2' show "(\<exists>S1'. ?step1\<^sup>+\<^sup>+ S1 S1' \<and> ?match S1' S2') \<or>
    (?match S1 S2' \<and> ?less (?measure S2') (?measure S2))"
  proof (cases N s2 s2' rule: ord_res_strategy.cases)
    case (expand_modelI \<I> U C D)
    hence "C \<prec>\<^sub>c D"
      using linorder_cls.is_least_in_fset_ffilterD(2) by metis
    have "?match S1 S2'"
    proof -
      have "match_ord_reso_and_ord_reso_strategy S1 S2'"
        unfolding match_ord_reso_and_ord_reso_strategy_def
        unfolding S2'_def \<open>s2' = (U, \<I> |\<union>| Abs_fset (ord_res.production (fset (N |\<union>| U)) C), D)\<close>
        using S1_eq[unfolded \<open>s2 = (U, \<I>, C)\<close>]
        by simp
      with invars1 invars2' show ?thesis
        by simp
    qed
    moreover have "?less (?measure S2') (?measure S2)"
      unfolding S2_def S2'_def expand_modelI
      apply simp
      using \<open>C \<prec>\<^sub>c D\<close>
      by (smt (verit, best) linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.less_irrefl
          linorder_cls.order.strict_trans local.expand_modelI(4) pfsubset_ffilter)
    ultimately show ?thesis
      by argo
  next
    case (factoringI \<I> U C L C' D)
    
    from invars2 have "interp_upto s2 |\<in>| N |\<union>| learned s2"
      unfolding ord_reso_strategy_invars_def
      by (simp add: S2_def)
    hence "C |\<in>| S1"
      using S1_eq by (simp add: S2_def \<open>s2 = (U, \<I>, C)\<close>)

    let ?S1' = "finsert C' S1"
    have "?step1 S1 ?S1'"
    proof (rule ord_reso_step.factoring)
      from invars2 have "interp_upto s2 = {#} \<longleftrightarrow> {#} |\<in>| N |\<union>| learned s2"
        unfolding ord_reso_strategy_invars_def
        by (simp add: S2_def)
      moreover have "interp_upto s2 \<noteq> {#}"
        unfolding \<open>s2 = (U, \<I>, C)\<close>
        using \<open>ord_res.is_maximal_lit L C\<close> linorder_lit.is_maximal_in_mset_iff by fastforce
      ultimately show "{#} |\<notin>| S1"
        using S1_eq
        unfolding \<open>s2 = (U, \<I>, C)\<close>
        by argo
    next
      from invars2 have
        "fset \<I> = ord_res.interp (fset N \<union> fset U) C"
        unfolding ord_reso_strategy_invars_def
        by (simp add: S2_def \<open>s2 = (U, \<I>, C)\<close>)
      then show "ex_false_clause (fset S1)"
        unfolding ex_false_clause_def
        using \<open>C |\<in>| S1\<close> \<open>\<not> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C\<close>
        unfolding S1_eq \<open>s2 = (U, \<I>, C)\<close> learned.simps
        by auto
    next
      show "C |\<in>| S1"
        using \<open>C |\<in>| S1\<close> .
    next
      show "ord_res.ground_factoring C C'"
        using \<open>ord_res.ground_factoring C C'\<close> .
    qed
    hence "?step1\<^sup>+\<^sup>+ S1 ?S1'"
      by simp
    moreover have "?match ?S1' S2'"
    proof -
      have "ord_reso_invars S1'" if \<open>?step1\<^sup>+\<^sup>+ S1 S1'\<close> for S1'
        using that invars1
        by (induction S1' rule: tranclp_induct) auto
      hence "ord_reso_invars ?S1'"
        using \<open>?step1\<^sup>+\<^sup>+ S1 ?S1'\<close> by metis
      moreover have "match_ord_reso_and_ord_reso_strategy ?S1' S2'"
        unfolding match_ord_reso_and_ord_reso_strategy_def
        using S1_eq[unfolded \<open>s2 = (U, \<I>, C)\<close>]
        unfolding S2'_def \<open>s2' = (finsert C' U, {||}, D)\<close>
        by simp
      ultimately show ?thesis
        using invars2' by simp
    qed
    ultimately show ?thesis
      by metis
  next
    case (resolution \<I> U C L E CE D)
    
    from invars2 have "interp_upto s2 |\<in>| N |\<union>| learned s2"
      unfolding ord_reso_strategy_invars_def
      by (simp add: S2_def)
    hence "C |\<in>| S1"
      using S1_eq by (simp add: S2_def \<open>s2 = (U, \<I>, C)\<close>)

    let ?S1' = "finsert CE S1"
    have "?step1 S1 ?S1'"
    proof (rule ord_reso_step.resolution)
      from invars2 have "interp_upto s2 = {#} \<longleftrightarrow> {#} |\<in>| N |\<union>| learned s2"
        unfolding ord_reso_strategy_invars_def
        by (simp add: S2_def)
      moreover have "interp_upto s2 \<noteq> {#}"
        unfolding \<open>s2 = (U, \<I>, C)\<close>
        using \<open>ord_res.is_maximal_lit L C\<close> linorder_lit.is_maximal_in_mset_iff by fastforce
      ultimately show "{#} |\<notin>| S1"
        using S1_eq
        unfolding \<open>s2 = (U, \<I>, C)\<close>
        by argo
    next
      from invars2 have
        "fset \<I> = ord_res.interp (fset N \<union> fset U) C"
        unfolding ord_reso_strategy_invars_def
        by (simp add: S2_def \<open>s2 = (U, \<I>, C)\<close>)
      then show "ex_false_clause (fset S1)"
        unfolding ex_false_clause_def
        using \<open>C |\<in>| S1\<close> \<open>\<not> fset \<I> \<union> ord_res.production (fset (N |\<union>| U)) C \<TTurnstile> C\<close>
        unfolding S1_eq \<open>s2 = (U, \<I>, C)\<close> learned.simps
        by auto
    next
      show "C |\<in>| S1"
        using \<open>C |\<in>| S1\<close> .
    next
      show "E |\<in>| S1"
        using S1_eq[unfolded \<open>s2 = (U, \<I>, C)\<close>]
        using \<open>E |\<in>| N\<close>
        by simp
    next
      show "ord_res.ground_resolution C E CE"
        using \<open>ord_res.ground_resolution C E CE\<close> .
    qed
    hence "?step1\<^sup>+\<^sup>+ S1 ?S1'"
      by simp
    moreover have "?match ?S1' S2'"
    proof -
      have "ord_reso_invars S1'" if \<open>?step1\<^sup>+\<^sup>+ S1 S1'\<close> for S1'
        using that invars1
        by (induction S1' rule: tranclp_induct) auto
      hence "ord_reso_invars ?S1'"
        using \<open>?step1\<^sup>+\<^sup>+ S1 ?S1'\<close> by metis
      moreover have "match_ord_reso_and_ord_reso_strategy ?S1' S2'"
        unfolding match_ord_reso_and_ord_reso_strategy_def
        using S1_eq[unfolded \<open>s2 = (U, \<I>, C)\<close>]
        unfolding S2'_def \<open>s2' = (finsert CE U, {||}, D)\<close>
        by simp
      ultimately show ?thesis
        using invars2' by simp
    qed
    ultimately show ?thesis
      by metis
  qed
qed

definition scl_strategy_invars where
  "scl_strategy_invars \<equiv> \<lambda>(N, \<beta>, s). scl_fol.trail_atoms_lt (term_of_gterm \<beta>) s"

lemma scl_strategy_invars_step_preserves_invars[intro]:
  "scl_strategy_step S S' \<Longrightarrow> scl_strategy_invars S \<Longrightarrow> scl_strategy_invars S'"
  sorry

definition match_ord_reso_strategy_and_scl_strategy where
  "match_ord_reso_strategy_and_scl_strategy = (\<lambda>(N1, (U1, \<I>, C)) (N2, \<beta>, (\<Gamma>, U2, \<C>)).
    N1 = N2 \<and> term_of_gterm ` fset \<I> = trail_interp \<Gamma>)"

lemma minus_pfsubset_minusI:
  assumes "C |\<subset>| B" and "B |\<subseteq>| A"
  shows "(A |-| B |\<subset>| A |-| C)"
proof (rule FSet.pfsubsetI)
  show "A |-| B |\<subseteq>| A |-| C"
    using assms(1) by blast
next
  show "A |-| B \<noteq> A |-| C"
    using assms by blast
qed

interpretation backward_simulation_with_measuring_function where
  step1 = ord_reso_strategy_step and
  step2 = scl_strategy_step and
  final1 = ord_reso_strategy_final and
  final2 = scl_strategy_final and
  order = "(|\<subset>|)" and
  match = "\<lambda>S1 S2. ord_reso_strategy_invars S1 \<and> scl_strategy_invars S2 \<and>
    match_ord_reso_strategy_and_scl_strategy S1 S2" and
  measure = "\<lambda>(N, \<beta>, (\<Gamma>, U, \<C>)).
    Abs_fset {L. less_B\<^sup>=\<^sup>= (atm_of L) (term_of_gterm \<beta>)} |-| (fst |`| fset_of_list \<Gamma>)"
proof unfold_locales
  show "wfP (|\<subset>|)"
    by auto
next
  let ?final1 = ord_reso_strategy_final
  let ?final2 = scl_strategy_final
  let ?match = "\<lambda>S1 S2. ord_reso_strategy_invars S1 \<and> scl_strategy_invars S2 \<and>
    match_ord_reso_strategy_and_scl_strategy S1 S2"
  fix
    S1 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm fset \<times> 'f gterm clause" and
    S2 :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state"

  assume "?match S1 S2"
  hence
    invars1: "ord_reso_strategy_invars S1" and
    invars2: "scl_strategy_invars S2" and
    match: "match_ord_reso_strategy_and_scl_strategy S1 S2"
    by simp_all

  from match obtain N U1 \<I> C \<beta> \<Gamma> U2 \<C> where
    S1_def: "S1 = (N, U1, \<I>, C)" and
    S2_def: "S2 = (N, \<beta>, \<Gamma>, U2, \<C>)"
    unfolding match_ord_reso_strategy_and_scl_strategy_def
    by auto

  from invars1 have
    C_in: "C |\<in>| N |\<union>| U1" and
    \<I>_eq_interp: "fset \<I> = ord_res.interp (fset (N |\<union>| U1)) C" and
    ball_interp_prod_entails: "\<forall>x |\<in>| N |\<union>| U1. x \<prec>\<^sub>c C \<longrightarrow>
      ord_res.interp (fset (N |\<union>| U1)) x \<union> ord_res.production (fset (N |\<union>| U1)) x \<TTurnstile> x"
    unfolding ord_reso_strategy_invars_def
    by (auto simp: S1_def)

  assume final2: "?final2 S2"
  show "?final1 S1"
  proof (cases \<C>)
    case None
    with final2 have "fBall (cls_of_gcls |`| N |\<union>| U2) (trail_true_cls \<Gamma>)"
      unfolding scl_strategy_final_def ord_reso_strategy_final_def
      unfolding S1_def S2_def prod.case by simp
    hence "fset \<I> \<union> ord_res.production (fset (N |\<union>| U1)) C \<TTurnstile> C \<and> \<not> fBex (N |\<union>| U1) ((\<prec>\<^sub>c) C)"
      sorry
    thus ?thesis
      unfolding ord_reso_strategy_final_def S1_def prod.case by simp
  next
    case (Some closure)
    with final2 obtain D \<gamma> where "closure = (D, \<gamma>)" and "\<Gamma> = [] \<and> D = {#}"
      unfolding scl_strategy_final_def ord_reso_strategy_final_def
      unfolding S1_def S2_def prod.case by auto
    hence "C = {#}"
      sorry
    thus ?thesis
      unfolding ord_reso_strategy_final_def S1_def prod.case by simp
  qed
next
  let ?step1 = ord_reso_strategy_step
  let ?step2 = scl_strategy_step
  let ?less = "(|\<subset>|)"
  let ?match = "\<lambda>S1 S2. ord_reso_strategy_invars S1 \<and> scl_strategy_invars S2 \<and>
    match_ord_reso_strategy_and_scl_strategy S1 S2"
  let ?measure = "\<lambda>(N, \<beta>, (\<Gamma>, U, \<C>)).
    Abs_fset {L. less_B\<^sup>=\<^sup>= (atm_of L) (term_of_gterm \<beta>)} |-| (fst |`| fset_of_list \<Gamma>)"
  fix
    S1 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm fset \<times> 'f gterm clause" and
    S2 S2' :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state"
  assume "?match S1 S2"
  hence
    invars1: "ord_reso_strategy_invars S1" and
    invars2: "scl_strategy_invars S2" and
    match: "match_ord_reso_strategy_and_scl_strategy S1 S2"
    by simp_all

  from match obtain N U\<^sub>1 \<I> C\<^sub>1 \<beta> \<Gamma> U\<^sub>2 \<C> where
    S1_def: "S1 = (N, U\<^sub>1, \<I>, C\<^sub>1)" and
    S2_def: "S2 = (N, \<beta>, \<Gamma>, U\<^sub>2, \<C>)" and
    \<I>_and_\<Gamma>_agree: "term_of_gterm ` fset \<I> = trail_interp \<Gamma>"
    unfolding match_ord_reso_strategy_and_scl_strategy_def
    by auto

  from invars2 have
    trail_atoms_lt_\<beta>: "scl_fol.trail_atoms_lt (term_of_gterm \<beta>) (\<Gamma>, U\<^sub>2, \<C>)"
    unfolding scl_strategy_invars_def S2_def by simp


  have N_lits_generalize_U\<^sub>2_lits:
    "scl_fol.clss_lits_generalize_clss_lits (fset (cls_of_gcls |`| N)) (fset U\<^sub>2)"
    sorry
  hence ball_ground: "\<forall>C |\<in>| U\<^sub>2. is_ground_cls C"
    using ball_ground_cls_if_lits_generalized_from_ground_clauses by auto

  note lit_from_N_if_from_N_funion_U =
    lit_in_lhs_if_lhs_generalises_rhs[OF _ _ N_lits_generalize_U\<^sub>2_lits]

  have ball_le_\<beta>: "\<forall>L \<in> \<Union> (set_mset ` fset N). atm_of L \<preceq>\<^sub>t \<beta>"
    sorry

  assume step2: "?step2 S2 S2'"
  then obtain s' where S2'_def: "S2' = (N, \<beta>, s')" and "scl_strategy N \<beta> (\<Gamma>, U\<^sub>2, \<C>) s'"
    unfolding scl_strategy_step_def S2_def prod.case
    by auto

  have invars2': "scl_strategy_invars S2'"
    using scl_strategy_invars_step_preserves_invars[OF step2 invars2] .

  show "(\<exists>S1'. ?step1\<^sup>+\<^sup>+ S1 S1' \<and> ?match S1' S2') \<or>
    (?match S1 S2' \<and> ?less (?measure S2') (?measure S2))"
    using \<open>scl_strategy N \<beta> (\<Gamma>, U\<^sub>2, \<C>) s'\<close>
  proof (cases N \<beta> "(\<Gamma>, U\<^sub>2, \<C>)" s' rule: scl_strategy.cases)
    case hyps: (expand_model_for_neg_lit NU C\<^sub>2 L \<Gamma>')

    have C\<^sub>2_in: "C\<^sub>2 |\<in>| N |\<union>| gcls_of_cls |`| U\<^sub>2"
      using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis

    have L_in: "L \<in># C\<^sub>2"
      using hyps(3-) by (simp add: linorder_lit.is_minimal_in_mset_iff)

    have "?match S1 S2'"
    proof -
      have "term_of_gterm ` fset \<I> = trail_interp \<Gamma>'"
      proof -
        from \<open>is_neg L\<close> obtain A where "L = Neg A"
          by (metis literal.collapse(2))
        have "trail_interp \<Gamma>' = trail_interp \<Gamma>"
          unfolding \<open>\<Gamma>' = trail_decide \<Gamma> (lit_of_glit L)\<close> \<open>L = Neg A\<close>
          by (simp add: decide_lit_def trail_interp_def lit_of_glit_def)
        thus ?thesis
          using \<I>_and_\<Gamma>_agree by argo
      qed
      hence "match_ord_reso_strategy_and_scl_strategy S1 S2'"
        unfolding match_ord_reso_strategy_and_scl_strategy_def
        unfolding S1_def prod.case S2'_def hyps(1,2)
        by simp
      with invars1 invars2' show ?thesis
        by argo
    qed

    moreover have "?less (?measure S2') (?measure S2)"
      unfolding S2_def S2'_def hyps(1,2) prod.case
    proof (intro minus_pfsubset_minusI fsubsetI)
      have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
        using hyps(3-) linorder_lit.is_minimal_in_mset_iff by simp
      hence "lit_of_glit L |\<notin>| fst |`| fset_of_list \<Gamma>"
        by (simp add: fset_of_list.rep_eq trail_defined_lit_def)
      thus "fst |`| fset_of_list \<Gamma> |\<subset>| fst |`| fset_of_list \<Gamma>'"
        unfolding hyps(3-) by (auto simp: decide_lit_def)
    next
      fix x
      assume "x |\<in>| fst |`| fset_of_list \<Gamma>'"
      hence "x = lit_of_glit L \<or> x |\<in>| fst |`| fset_of_list \<Gamma>"
        unfolding hyps(3-) fset_of_list_simps
        by (simp add: decide_lit_def)
      hence "less_B\<^sup>=\<^sup>= (atm_of x) (term_of_gterm \<beta>)"
      proof (elim disjE)
        have "atm_of L \<preceq>\<^sub>t \<beta>"
          using ball_le_\<beta> L_in C\<^sub>2_in lit_from_N_if_from_N_funion_U by metis
        thus "x = lit_of_glit L \<Longrightarrow> ?thesis"
          by (auto simp: less_B_def atm_of_lit_of_glit_conv)
      next
        show "x |\<in>| fst |`| fset_of_list \<Gamma> \<Longrightarrow> ?thesis"
          using trail_atoms_lt_\<beta>[unfolded scl_fol.trail_atoms_lt_def state_proj_simp]
          by (metis fset.set_map fset_of_list.rep_eq image_eqI)
      qed
      thus "x |\<in>| Abs_fset {L. less_B\<^sup>=\<^sup>= (atm_of L) (term_of_gterm \<beta>)}"
        using scl_fol.finite_lits_less_eq_B Abs_fset_inverse by blast
    qed

    ultimately show ?thesis
      by argo
  next
    case hyps: (expand_model_for_pos_lit_when_not_max NU C\<^sub>2 L \<Gamma>')

    have C\<^sub>2_in: "C\<^sub>2 |\<in>| N |\<union>| gcls_of_cls |`| U\<^sub>2"
      using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis

    have L_in: "L \<in># C\<^sub>2"
      using hyps(3-) by (simp add: linorder_lit.is_minimal_in_mset_iff)
    
    have "?match S1 S2'"
    proof -
      have "term_of_gterm ` fset \<I> = trail_interp \<Gamma>'"
      proof -
        from \<open>is_pos L\<close> obtain A where "L = Pos A"
          by (meson is_pos_def)
        have "trail_interp \<Gamma>' = trail_interp \<Gamma>"
          unfolding \<open>\<Gamma>' = trail_decide \<Gamma> (lit_of_glit (- L))\<close> \<open>L = Pos A\<close>
          by (simp add: decide_lit_def trail_interp_def lit_of_glit_def)
        thus ?thesis
          using \<I>_and_\<Gamma>_agree by argo
      qed
      hence "match_ord_reso_strategy_and_scl_strategy S1 S2'"
        unfolding match_ord_reso_strategy_and_scl_strategy_def
        unfolding S1_def prod.case S2'_def hyps(1,2)
        by simp
      with invars1 invars2' show ?thesis
        by argo
    qed

    moreover have "?less (?measure S2') (?measure S2)"
      unfolding S2_def S2'_def hyps(1,2) prod.case
    proof (intro minus_pfsubset_minusI fsubsetI)
      have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
        using hyps(3-) linorder_lit.is_minimal_in_mset_iff by simp
      hence "lit_of_glit (- L) |\<notin>| fst |`| fset_of_list \<Gamma>"
        by (metis (mono_tags, opaque_lifting) atm_of_eq_uminus_if_lit_eq
            atm_of_lit_of_glit_eq_atm_of_lit_of_glit fset_of_list.rep_eq fset_of_list_map image_set
            trail_defined_lit_def trail_defined_lit_iff)
      thus "fst |`| fset_of_list \<Gamma> |\<subset>| fst |`| fset_of_list \<Gamma>'"
        unfolding hyps(3-) by (auto simp: decide_lit_def)
    next
      fix x
      assume "x |\<in>| fst |`| fset_of_list \<Gamma>'"
      hence "x = lit_of_glit (- L) \<or> x |\<in>| fst |`| fset_of_list \<Gamma>"
        unfolding hyps(3-) fset_of_list_simps
        by (simp add: decide_lit_def)
      hence "less_B\<^sup>=\<^sup>= (atm_of x) (term_of_gterm \<beta>)"
      proof (elim disjE)
        have "atm_of L \<preceq>\<^sub>t \<beta>"
          using ball_le_\<beta> L_in C\<^sub>2_in lit_from_N_if_from_N_funion_U by metis
        thus "x = lit_of_glit (- L) \<Longrightarrow> ?thesis"
          by (auto simp: less_B_def atm_of_lit_of_glit_conv)
      next
        show "x |\<in>| fst |`| fset_of_list \<Gamma> \<Longrightarrow> ?thesis"
          using trail_atoms_lt_\<beta>[unfolded scl_fol.trail_atoms_lt_def state_proj_simp]
          by (metis fset.set_map fset_of_list.rep_eq image_eqI)
      qed
      thus "x |\<in>| Abs_fset {L. less_B\<^sup>=\<^sup>= (atm_of L) (term_of_gterm \<beta>)}"
        using scl_fol.finite_lits_less_eq_B Abs_fset_inverse by blast
    qed

    ultimately show ?thesis
      by argo
  next
    case hyps: (expand_model_for_pos_lit_when_max NU C\<^sub>2 L \<Gamma>')
    \<comment> \<open>All literals except \<^term>\<open>L\<close> are false.\<close>

    have C\<^sub>2_in: "C\<^sub>2 |\<in>| N |\<union>| gcls_of_cls |`| U\<^sub>2"
      using hyps(3-) linorder_cls.is_least_in_fset_ffilterD(1) by metis

    have L_in: "L \<in># C\<^sub>2"
      using hyps(3-) by (simp add: linorder_lit.is_minimal_in_mset_iff)

    show ?thesis
    proof (cases "ord_res.is_strictly_maximal_lit L C\<^sub>2")
      case True
      \<comment> \<open>There is only one \<^term>\<open>L\<close>, so the clause is productive and true under the partial model
        of ordered resolution.\<close>
      show ?thesis
      proof (cases "\<exists>D\<^sub>1. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C\<^sub>1) (N |\<union>| U\<^sub>1)) D\<^sub>1")
        case True
        then obtain D\<^sub>1 where
          D\<^sub>1_least: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C\<^sub>1) (N |\<union>| U\<^sub>1)) D\<^sub>1"
          by metis

        let ?S1' = "(N, U\<^sub>1, finsert (atm_of L) \<I>, D\<^sub>1)"

        have "?step1\<^sup>+\<^sup>+ S1 ?S1'"
        proof -
          have "ord_res_strategy N (U\<^sub>1, \<I>, C\<^sub>1) (U\<^sub>1, finsert (atm_of L) \<I>, D\<^sub>1)"
          proof (rule ord_res_strategy_expand_modelI')
            show "fset \<I> \<union> ord_res.production (fset (N |\<union>| U\<^sub>1)) C\<^sub>1 \<TTurnstile> C\<^sub>1"
              sorry
          next
            show "finsert (atm_of L) \<I> = \<I> |\<union>| Abs_fset (ord_res.production (fset (N |\<union>| U\<^sub>1)) C\<^sub>1)"
              sorry
          next
            show "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C\<^sub>1) (N |\<union>| U\<^sub>1)) D\<^sub>1"
              using D\<^sub>1_least .
          qed
          hence "?step1 S1 ?S1'"
            unfolding ord_reso_strategy_step_def S1_def prod.case by argo
          thus ?thesis
            by simp
        qed
        moreover have "?match ?S1' S2'"
          sorry
        ultimately show ?thesis
          by metis
      next
        case False

        have fimage_fst_fset_of_\<Gamma>':
          "fst |`| fset_of_list \<Gamma>' = finsert (lit_of_glit L) (fst |`| fset_of_list \<Gamma>)"
          unfolding hyps(3-)
          by (cases "\<exists>D|\<in>|N |\<union>| gcls_of_cls |`| U\<^sub>2.
                  trail_false_cls (trail_decide \<Gamma> (lit_of_glit L)) (cls_of_gcls D)")
              (simp_all add: propagate_lit_def decide_lit_def)

        have "?match S1 S2'"
        proof -
          have "match_ord_reso_strategy_and_scl_strategy S1 S2'"
            unfolding match_ord_reso_strategy_and_scl_strategy_def
            sorry
          thus ?thesis
            using invars1 invars2' by argo
        qed

        moreover have "?less (?measure S2') (?measure S2)"
          unfolding S2_def S2'_def hyps(1,2) prod.case
        proof (intro minus_pfsubset_minusI fsubsetI)
          have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
            using hyps(3-) linorder_lit.is_minimal_in_mset_iff by simp
          hence "lit_of_glit L |\<notin>| fst |`| fset_of_list \<Gamma>"
            by (metis (mono_tags, opaque_lifting) fset_of_list.rep_eq fset_of_list_map image_set
                trail_defined_lit_def)
          thus "fst |`| fset_of_list \<Gamma> |\<subset>| fst |`| fset_of_list \<Gamma>'"
            unfolding fimage_fst_fset_of_\<Gamma>' by auto
        next
          fix x
          assume "x |\<in>| fst |`| fset_of_list \<Gamma>'"
          hence "x = lit_of_glit L \<or> x |\<in>| fst |`| fset_of_list \<Gamma>"
            unfolding fimage_fst_fset_of_\<Gamma>' by simp
          hence "less_B\<^sup>=\<^sup>= (atm_of x) (term_of_gterm \<beta>)"
          proof (elim disjE)
            have "atm_of L \<preceq>\<^sub>t \<beta>"
              using ball_le_\<beta> L_in C\<^sub>2_in lit_from_N_if_from_N_funion_U by metis
            thus "x = lit_of_glit L \<Longrightarrow> ?thesis"
              by (auto simp: less_B_def atm_of_lit_of_glit_conv)
          next
            show "x |\<in>| fst |`| fset_of_list \<Gamma> \<Longrightarrow> ?thesis"
              using trail_atoms_lt_\<beta>[unfolded scl_fol.trail_atoms_lt_def state_proj_simp]
              by (metis fset.set_map fset_of_list.rep_eq image_eqI)
          qed
          thus "x |\<in>| Abs_fset {L. less_B\<^sup>=\<^sup>= (atm_of L) (term_of_gterm \<beta>)}"
            using scl_fol.finite_lits_less_eq_B Abs_fset_inverse by blast
        qed

        ultimately show ?thesis
          by argo
      qed
    next
      case False
      \<comment> \<open>There are multiple \<^term>\<open>L\<close>, so the clause is non productive and false under the partial
        model of ordered resolution; it the ord. res. strategy will use the factorization rule until
        all duplicates were removed.\<close>
      term "replicate_mset 1 L"

      let ?S1' = "(N, U\<^sub>1, \<I> |\<union>| {||}, C\<^sub>1)"
      have "?step1\<^sup>+\<^sup>+ S1 ?S1'"
        unfolding S1_def
        sorry
      moreover have "?match ?S1' S2'"
        sorry
      ultimately show ?thesis
        by metis
    qed
  next
    case (conflict NU C)
    then show ?thesis sorry
  next
    case (resolve C C')
    then show ?thesis sorry
  next
    case (skip C \<Gamma>')
    then show ?thesis sorry
  next
    case (backtrack C U')
    then show ?thesis sorry
  qed
qed
  


subsection \<open>Backward simulation between ORD-RES and ORD-RES++\<close>

interpretation backward_simulation_with_measuring_function where
  step1 = ord_reso_step and
  step2 = res_mo_strategy and
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
  fix N1 N2 N2' assume "N1 = N2" and "res_mo_strategy N2 N2'"
  then obtain L C where
    C_min: "is_min_false_clause N2 C" and
    L_max: "ord_res.is_maximal_lit L C" and
    fact_or_reso: "(case L of
       Pos A \<Rightarrow> \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
       (\<exists>C'. ord_res.ground_factoring C C' \<and> N2' = finsert C' N2)
     | Neg A \<Rightarrow> \<exists>D|\<in>|N2. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
       ord_res.production (fset N2) D = {A} \<and>
       (\<exists>CD. ord_res.ground_resolution C D CD \<and> N2' = finsert CD N2))"
    unfolding res_mo_strategy_def by blast

  from C_min have "C |\<in>| N2"
    by (simp add: is_min_false_clause_def is_minimal_in_fset_wrt_iff)

  from C_min L_max have "{#} |\<notin>| N2"
    using Uniq_is_min_false_clause
    by (meson \<open>res_mo_strategy N2 N2'\<close> ord_reso_extended_semantics.final_finished
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

lemma res_mo_strategy_preserves_atms_of_clss:
  assumes step: "res_mo_strategy N N'"
  shows "atms_of_clss N = atms_of_clss N'"
proof -
  from step obtain L C where
    C_min: "is_min_false_clause N C" and
    L_max: "ord_res.is_maximal_lit L C" and
    case_L: "case L of
       Pos A \<Rightarrow> \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and> (\<exists>C'. ord_res.ground_factoring C C' \<and> N' = finsert C' N)
     | Neg A \<Rightarrow> \<exists>D|\<in>|N. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
        ord_res.production (fset N) D = {A} \<and>
        (\<exists>CD. ord_res.ground_resolution C D CD \<and> N' = finsert CD N)"
    unfolding res_mo_strategy_def
    by auto

  from C_min have "C |\<in>| N"
    by (simp add: is_min_false_clause_def is_minimal_in_fset_wrt_iff)

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

lemma compower_res_mo_strategy_preserves_atms_of_clss:
  "(res_mo_strategy ^^ i) N N\<^sub>i \<Longrightarrow> atms_of_clss N = atms_of_clss N\<^sub>i"
proof (induction i arbitrary: N\<^sub>i)
  case 0
  then show ?case
    by simp
next
  case (Suc i')
  from Suc.prems obtain N\<^sub>i\<^sub>' where
    "(res_mo_strategy ^^ i') N N\<^sub>i\<^sub>'" and "res_mo_strategy N\<^sub>i\<^sub>' N\<^sub>i"
    by auto

  have "atms_of_clss N = atms_of_clss N\<^sub>i\<^sub>'"
    using Suc.IH[OF \<open>(res_mo_strategy ^^ i') N N\<^sub>i\<^sub>'\<close>] .
  also have "\<dots> = atms_of_clss N\<^sub>i"
    using res_mo_strategy_preserves_atms_of_clss[OF \<open>res_mo_strategy N\<^sub>i\<^sub>' N\<^sub>i\<close>] .
  finally show ?case .
qed

lemma atoms_of_learn_clauses_already_in_initial_clauses:
  assumes
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    \<beta>_greatereq: "\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>" and
    N_generalizes: "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>0" and
    "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>0) |\<subseteq>| atms_of_clss N"
  shows
    "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| atms_of_clss N"
    "atms_of_clss (gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| atms_of_clss N"
  using step
  unfolding atomize_conj
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  have "(scl_fol.decide (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
    using \<beta>_greatereq step N_generalizes correctness_scl_reso1(1) by metis
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
      using \<beta>_greatereq step N_generalizes correctness_scl_reso1(2) by blast
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

lemma clause_anotation_in_initial_or_learned:
  assumes
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    invar: "C\<^sub>0 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0)"
  shows
    "C\<^sub>1 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1)"
    "C\<^sub>2 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2)"
  using step
  unfolding atomize_conj
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  hence "D |\<in>| N |\<union>| gcls_of_cls |`| U"
    using linorder_cls_sfac.is_least_in_fset_ffilterD by metis
  hence "C\<^sub>1 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1)"
    unfolding \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close>
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close>
    by simp

  moreover have "C\<^sub>2 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2)"
    using calculation scl_reso1_simple_destroy[OF step] by metis

  ultimately show "
    C\<^sub>1 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1) \<and>
    C\<^sub>2 |\<in>| finsert {#} (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2)"
    by (intro conjI)
qed

lemma fsubset_if_res_mo_strategy:
  assumes "res_mo_strategy N N'"
  shows "N |\<subseteq>| N'"
  using assms
  unfolding res_mo_strategy_def
  apply (elim exE conjE)
  subgoal for C L
    apply (cases L)
    by (auto simp add: fsubset_finsertI)
  done

lemma fsubset_if_relpow_le_relpow:
  fixes i j :: nat
  assumes "i \<le> j" and
    N_to_N\<^sub>i: "(res_mo_strategy ^^ i) N N\<^sub>i" and
    N_to_N\<^sub>j: "(res_mo_strategy ^^ j) N N\<^sub>j"
  shows "N\<^sub>i |\<subseteq>| N\<^sub>j"
proof -
  from \<open>i \<le> j\<close> obtain k where "j = i + k"
    using le_Suc_ex by metis
  hence "(res_mo_strategy ^^ (i + k)) N N\<^sub>j"
    using N_to_N\<^sub>j by argo
  hence "(res_mo_strategy ^^ i OO res_mo_strategy ^^ k) N N\<^sub>j"
    by (metis relpowp_add)
  hence "(res_mo_strategy ^^ k) N\<^sub>i N\<^sub>j"
    using right_unique_res_mo_strategy N_to_N\<^sub>i
    by (metis Uniq_relpowp relcomppE right_unique_iff)
  thus "N\<^sub>i |\<subseteq>| N\<^sub>j"
    using fsubset_if_res_mo_strategy
    by (metis mono_rtranclp relpowp_imp_rtranclp rtranclp_less_eq)
qed

lemma sfac_initial_and_learned_clauses_subset:
  assumes
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    N_to_N\<^sub>i\<^sub>0: "(res_mo_strategy ^^ i\<^sub>0) N N\<^sub>i\<^sub>0" and
    N_to_N\<^sub>i\<^sub>1: "(res_mo_strategy ^^ i\<^sub>1) N N\<^sub>i\<^sub>1" and
    N_to_N\<^sub>i\<^sub>2: "(res_mo_strategy ^^ i\<^sub>2) N N\<^sub>i\<^sub>2" and
    invar: "sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>0"
  shows
    "sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>1"
    "sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>2"
  unfolding atomize_conj
  using step
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)

  from hyps have "state_learned S\<^sub>0 = U" and "state_learned S\<^sub>1 = U"
    by simp_all
  hence "state_learned S\<^sub>2 = U"
    using scl_reso1_simple_destroy[OF step] by metis

  have "i\<^sub>0 = i\<^sub>1"
    using scl_reso1_simple_destroy[OF step] by metis
  hence "N\<^sub>i\<^sub>0 = N\<^sub>i\<^sub>1"
    using right_unique_res_mo_strategy N_to_N\<^sub>i\<^sub>0 N_to_N\<^sub>i\<^sub>1
    by (metis Uniq_relpowp right_unique_iff)

  from step have "i\<^sub>1 \<le> i\<^sub>2"
    using scl_reso1_simple_destroy[OF step] by metis
  with N_to_N\<^sub>i\<^sub>1 N_to_N\<^sub>i\<^sub>2 have "N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2"
    by (metis fsubset_if_relpow_le_relpow)

  from invar have "sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>1"
    unfolding \<open>state_learned S\<^sub>0 = U\<close> \<open>state_learned S\<^sub>1 = U\<close>
    using \<open>N\<^sub>i\<^sub>0 = N\<^sub>i\<^sub>1\<close> by simp

  moreover hence "sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>2"
    unfolding \<open>state_learned S\<^sub>1 = U\<close> \<open>state_learned S\<^sub>2 = U\<close>
    using \<open>N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2\<close> by (meson fimage_mono order_trans)

  ultimately show "sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>1 \<and>
       sfac |`| (N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2) |\<subseteq>| sfac |`| N\<^sub>i\<^sub>2"
    by (intro conjI)
qed

lemma
  assumes
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    N_to_N\<^sub>i\<^sub>0: "(res_mo_strategy ^^ i\<^sub>0) N N\<^sub>i\<^sub>0" and
    N_to_N\<^sub>i\<^sub>1: "(res_mo_strategy ^^ i\<^sub>1) N N\<^sub>i\<^sub>1" and
    N_to_N\<^sub>i\<^sub>2: "(res_mo_strategy ^^ i\<^sub>2) N N\<^sub>i\<^sub>2" and
    invar: "\<forall>C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0. \<F>\<^sub>0 C |\<in>| N\<^sub>i\<^sub>0"
  shows
    "\<forall>C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1. \<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1"
    "\<forall>C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2. \<F>\<^sub>2 C |\<in>| N\<^sub>i\<^sub>2"
  unfolding atomize_conj
  using step
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  have "N\<^sub>i\<^sub>0 = N\<^sub>i"
    by (metis N_to_N\<^sub>i\<^sub>0 Uniq_relpowp hyps(8) right_unique_iff right_unique_res_mo_strategy)

  have "state_learned S\<^sub>1 = state_learned S\<^sub>0" and "i\<^sub>1 = i\<^sub>0" and "C\<^sub>2 = C\<^sub>1" and "\<F>\<^sub>1 = \<F>\<^sub>0"
    using scl_reso1_simple_destroy[OF step] scl_reso1_\<F>_eq[OF step] by simp_all

  have "N\<^sub>i\<^sub>1 = N\<^sub>i\<^sub>0"
    using N_to_N\<^sub>i\<^sub>0 N_to_N\<^sub>i\<^sub>1 \<open>i\<^sub>1 = i\<^sub>0\<close>
    by (metis Uniq_relpowp right_unique_iff right_unique_res_mo_strategy)

  have "state_learned S\<^sub>2 = state_learned S\<^sub>1" and
    \<F>\<^sub>2_eq_disj: "\<F>\<^sub>2 = \<F>\<^sub>1 \<or>
      (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#}))"
    using scl_reso1_simple_destroy[OF step] scl_reso1_\<F>_eq[OF step] by simp_all

  from step have "i\<^sub>1 \<le> i\<^sub>2"
    using scl_reso1_simple_destroy[OF step] by metis
  with N_to_N\<^sub>i\<^sub>1 N_to_N\<^sub>i\<^sub>2 have "N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2"
    by (metis fsubset_if_relpow_le_relpow)

  let ?D\<^sub>0 = "{#K \<in># D. K \<noteq> L#}"
  let ?\<Gamma>\<^sub>2\<^sub>a = "trail_decide \<Gamma>\<^sub>1 (lit_of_glit L)"
  let ?\<F>' = "\<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})"
  let ?j = "count (\<F>\<^sub>0 D - {#L#}) L"

  thm ord_res.production_unfold

  have "D = ?D\<^sub>0 + replicate_mset (count D L) L"
    by (metis add.commute filter_mset_eq filter_mset_neq multiset_partition
        removeAll_mset_filter_mset)

  have "D - replicate_mset n L |\<in>| N\<^sub>n"
    if "(res_mo_strategy ^^ (i\<^sub>0 + n)) N N\<^sub>n"
    for n N\<^sub>n
    using that
  proof (induction n)
    case 0
    with N_to_N\<^sub>i\<^sub>0 have "N\<^sub>i\<^sub>0 = N\<^sub>n"
      by (metis Nat.add_0_right Uniq_relpowp right_unique_iff right_unique_res_mo_strategy)
    then show ?case
      apply simp
      sorry
  next
    case (Suc n)
    then show ?case sorry
  qed

  have "sfac D |\<in>| N\<^sub>i\<^sub>2"
    sorry

  have 1: "\<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1"
    if "C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1"
    for C
    using invar that
    unfolding \<open>state_learned S\<^sub>1 = state_learned S\<^sub>0\<close> \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>N\<^sub>i\<^sub>1 = N\<^sub>i\<^sub>0\<close> by metis

  moreover have "\<F>\<^sub>2 C |\<in>| N\<^sub>i\<^sub>2"
    if "C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2"
    for C
  proof (cases rule: scl_reso1_step2_cases[of L \<Gamma> Ks D N \<beta> U])
    case case2a
    hence "S\<^sub>2 = (?\<Gamma>\<^sub>2\<^sub>a, U, None)" "i\<^sub>2 = i\<^sub>0 + ?j" "C\<^sub>2 = D" "\<F>\<^sub>2 = ?\<F>'"
      using hyps by simp_all

    show ?thesis
    proof (cases "C = C\<^sub>1")
      case True
      hence "\<F>\<^sub>2 C = add_mset L {#K \<in># D. K \<noteq> L#}"
        using \<open>\<F>\<^sub>2 = ?\<F>'\<close> \<open>C\<^sub>2 = C\<^sub>1\<close> \<open>C\<^sub>2 = D\<close> by simp
      also have "\<dots> = sfac D"
        using sfac_spec_if_pos_lit_is_maximal[OF \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L D\<close>] by argo
      finally show ?thesis
        using \<open>sfac D |\<in>| N\<^sub>i\<^sub>2\<close> by argo
    next
      case False
      with \<F>\<^sub>2_eq_disj have "\<F>\<^sub>2 C = \<F>\<^sub>1 C"
        by force
      then show ?thesis
        using that \<open>N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2\<close> 1
        unfolding \<open>state_learned S\<^sub>2 = state_learned S\<^sub>1\<close>
        by auto
    qed
  next
    case case2b
    hence "C\<^sub>2 = D" "\<F>\<^sub>2 = ?\<F>'"
      using hyps(11)
      unfolding Let_def \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks)\<close>
      by simp_all

    show ?thesis
    proof (cases "C = C\<^sub>1")
      case True
      hence "\<F>\<^sub>2 C = add_mset L {#K \<in># D. K \<noteq> L#}"
        using \<open>\<F>\<^sub>2 = ?\<F>'\<close> \<open>C\<^sub>2 = C\<^sub>1\<close> \<open>C\<^sub>2 = D\<close> by simp
      also have "\<dots> = sfac D"
        using sfac_spec_if_pos_lit_is_maximal[OF \<open>is_pos L\<close> \<open>ord_res.is_maximal_lit L D\<close>] by argo
      finally show ?thesis
        using \<open>sfac D |\<in>| N\<^sub>i\<^sub>2\<close> by argo
    next
      case False
      with \<F>\<^sub>2_eq_disj have "\<F>\<^sub>2 C = \<F>\<^sub>1 C"
        by force
      then show ?thesis
        using that \<open>N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2\<close> 1
        unfolding \<open>state_learned S\<^sub>2 = state_learned S\<^sub>1\<close>
        by auto
    qed
  next
    case case2c
    then show ?thesis
      by (smt (verit) N_to_N\<^sub>i\<^sub>1 N_to_N\<^sub>i\<^sub>2 Uniq_relpowp \<open>state_learned S\<^sub>2 = state_learned S\<^sub>1\<close> calculation
          hyps(11) hyps(6) local.step right_unique_iff right_unique_res_mo_strategy
          scl_reso1_\<F>_eq(1) scl_reso1_simple_destroy(3) that)
  qed

  ultimately show "
    (\<forall>C|\<in>|N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1. \<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1) \<and>
    (\<forall>C|\<in>|N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2. \<F>\<^sub>2 C |\<in>| N\<^sub>i\<^sub>2)"
    by metis
qed

definition simulation ::
  "'f gterm literal multiset fset \<Rightarrow>
  ('f, 'v) state \<times> nat \<times> 'f gterm clause \<times> ('f gterm clause \<Rightarrow> 'f gterm clause) \<Rightarrow>
  bool" where
  "simulation _ _ = False"

interpretation backward_simulation_with_measuring_function where
  step1 = res_mo_strategy and
  step2 = "\<lambda>S\<^sub>0 S\<^sub>2. \<exists>S\<^sub>1. scl_reso1 N \<beta> S\<^sub>0 S\<^sub>1 S\<^sub>2" and
  final1 = "\<lambda>N. {#} |\<in>| N" and
  final2 = "\<lambda>S. \<exists>\<gamma>. state_trail (fst S) = [] \<and> state_conflict (fst S) = Some ({#}, \<gamma>)" and
  order = "\<lambda>_ _. False" and
  match = "simulation" and
  measure = "\<lambda>_. ()"
proof unfold_locales
  fix s1 s2
  assume
    match: "simulation s1 s2" and
    final2: "\<exists>\<gamma>. state_trail (fst s2) = [] \<and> state_conflict (fst s2) = Some ({#}, \<gamma>)"
  show "{#} |\<in>| s1"
    sorry
next
  fix s1 s2a s2c
  assume
    match: "simulation s1 s2a" and
    step2: "\<exists>s2b. scl_reso1 N \<beta> s2a s2b s2c"
  then obtain s2b where "scl_reso1 N \<beta> s2a s2b s2c"
    by metis

  thus "(\<exists>s1'. res_mo_strategy\<^sup>+\<^sup>+ s1 s1' \<and> simulation s1' s2c) \<or>
    simulation s1 s2c \<and> False"
  proof (cases N \<beta> s2a s2b s2c rule: scl_reso1.cases)
    case (scl_reso1I \<F> C D U L Ks \<Gamma> \<Gamma>\<^sub>1 i N\<^sub>i)
    then show ?thesis
      sorry
  qed
qed


subsection \<open>Forward simulation between SCL(FOL)++ and SCL(FOL)\<close>

fun \<M> :: "'f gterm clause fset \<Rightarrow>
  ('f, 'v) state \<times> nat \<times> 'f gterm clause \<times> ('f gterm clause \<Rightarrow> 'f gterm clause) \<Rightarrow>
  'f gterm clause fset" where
  "\<M> N (S, _, C, \<F>) = {|D |\<in>| N |\<union>| gcls_of_cls |`| state_learned S. less_cls_sfac \<F> C D|}"

interpretation forward_simulation_with_measuring_function where
  step1 = "\<lambda>S\<^sub>0 S\<^sub>2. \<exists>S\<^sub>1. scl_reso1 N \<beta> S\<^sub>0 S\<^sub>1 S\<^sub>2" and
  step2 = "scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>)" and
  final1 = "\<lambda>S. \<exists>\<gamma>. state_trail (fst S) = [] \<and> state_conflict (fst S) = Some ({#}, \<gamma>)" and
  final2 = "\<lambda>S. \<exists>\<gamma>. state_trail S = [] \<and> state_conflict S = Some ({#}, \<gamma>)" and
  order = "(|\<subset>|)" and
  match = "\<lambda>S1 S2. fst S1 = S2 \<and> (\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>) \<and>
    scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2" and
  measure = "\<M> N"
proof unfold_locales
  show "wfP (|\<subset>|)"
    by auto
next
  show "\<And>n s1 s2. fst s1 = s2 \<and> (\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>) \<and>
    scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) s2 \<Longrightarrow>
    \<exists>\<gamma>. state_trail (fst s1) = [] \<and> state_conflict (fst s1) = Some ({#}, \<gamma>) \<Longrightarrow>
    \<exists>\<gamma>. state_trail s2 = [] \<and> state_conflict s2 = Some ({#}, \<gamma>)"
    by simp
next
  fix S1 S2 S1'
  assume
    match: "fst S1 = S2 \<and> (\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>) \<and>
      scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2" and
    step: "\<exists>S1''. scl_reso1 N \<beta> S1 S1'' S1'"
  from match have
    "fst S1 = S2" and
    \<beta>_greatereq: "\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>" and
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
    using correctness_scl_reso1(1)[OF \<beta>_greatereq step' init_geneneralize']
    by (metis mono_rtranclp scl_fol.scl_def)

  show "
    (\<exists>S2'. (scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S2 S2' \<and>
      fst S1' = S2' \<and> (\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>) \<and>
      scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2') \<or>
    ((fst S1' = S2 \<and> (\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>) \<and>
      scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S2) \<and>
      \<M> N S1' |\<subset>| \<M> N S1)"
    using correctness_scl_reso1(2)[OF \<beta>_greatereq step' init_geneneralize']
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
      using \<beta>_greatereq by metis
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
      using \<beta>_greatereq by metis
  next
    assume "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)"
    hence "S\<^sub>1 = S\<^sub>2" "i\<^sub>2 = i\<^sub>1" "C\<^sub>2 = C\<^sub>1" "\<F>\<^sub>2 = \<F>\<^sub>1"
      by simp_all
    with 1 show ?thesis
      unfolding \<open>fst S1 = S2\<close>[symmetric] \<open>S1 = (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)\<close> \<open>S1' = (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)\<close> prod.sel
      using init_geneneralize'
    proof (induction S\<^sub>1 rule: rtranclp_induct)
      case base
      moreover have "\<M> N (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) |\<subset>| \<M> N (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)"
        unfolding \<open>S\<^sub>0 = S\<^sub>2\<close>[symmetric] \<M>.simps
      proof (rule pfsubset_ffilter)
        have C\<^sub>0_lt_C\<^sub>1: "less_cls_sfac \<F>\<^sub>0 C\<^sub>0 C\<^sub>1"
          using step'
          by (auto elim!: scl_reso1.cases dest: linorder_cls_sfac.is_least_in_fset_ffilterD)

        have "C\<^sub>1 = C\<^sub>2"
          using scl_reso1_simple_destroy[OF step'] by metis

        show "less_cls_sfac \<F>\<^sub>2 C\<^sub>2 x \<Longrightarrow> less_cls_sfac \<F>\<^sub>0 C\<^sub>0 x" for x
          using C\<^sub>0_lt_C\<^sub>1
          unfolding \<open>\<F>\<^sub>2 = \<F>\<^sub>1\<close> base.prems(3) scl_reso1_\<F>_eq(1)[OF step']
          by order

        let ?x = "C\<^sub>1"
        show "C\<^sub>1 |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0 \<and> \<not> less_cls_sfac \<F>\<^sub>2 C\<^sub>2 C\<^sub>1 \<and>
          less_cls_sfac \<F>\<^sub>0 C\<^sub>0 C\<^sub>1"
        proof (intro conjI)
          show "C\<^sub>1 |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0"
            using step' by (auto elim!: scl_reso1.cases
                dest: linorder_cls_sfac.is_least_in_fset_ffilterD)
        next
          show "\<not> less_cls_sfac \<F>\<^sub>2 C\<^sub>2 C\<^sub>1"
            unfolding \<open>C\<^sub>1 = C\<^sub>2\<close> by simp
        next
          show "less_cls_sfac \<F>\<^sub>0 C\<^sub>0 C\<^sub>1"
            using C\<^sub>0_lt_C\<^sub>1 .
        qed
      qed
      ultimately show ?case
        apply -
        apply (rule disjI2)
        using \<beta>_greatereq
        by simp
    next
      case (step y z)
      have "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>+\<^sup>+ S\<^sub>0 S\<^sub>2"
        using step.hyps step.prems(1) by simp
      moreover hence "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>2"
        apply (induction S\<^sub>2 rule: tranclp_induct)
        apply (simp add: scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict
            step.prems(5))
        using scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict by blast
      ultimately show ?case
        apply -
        apply (rule disjI1)
        using \<beta>_greatereq
        by fastforce
    qed
  qed
qed

end
 
end