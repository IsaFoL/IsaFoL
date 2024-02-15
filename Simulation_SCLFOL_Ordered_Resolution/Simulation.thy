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


section \<open>Move to \<^theory>\<open>HOL-Library.Multiset\<close>\<close>

lemmas strict_subset_implies_multp = subset_implies_multp
hide_fact subset_implies_multp

lemma subset_implies_reflclp_multp: "A \<subseteq># B \<Longrightarrow> (multp R)\<^sup>=\<^sup>= A B"
  by (metis reflclp_iff strict_subset_implies_multp subset_mset.le_imp_less_or_eq)

lemma member_mset_repeat_msetD: "L \<in># repeat_mset n M \<Longrightarrow> L \<in># M"
  by (induction n) auto

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


subsection \<open>Common definitions and lemmas\<close>

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


subsection \<open>ORD-RES-0\<close>

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


subsection \<open>ORD-RES-1 (deterministic)\<close>

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

inductive ord_res_1 where
  factoring: "
    is_least_false_clause N C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    ord_res.ground_factoring C C' \<Longrightarrow>
    N' = finsert C' N \<Longrightarrow>
    ord_res_1 N N'" |

  resolution: "
    is_least_false_clause N C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    D |\<in>| N \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    ord_res.production (fset N) D = {atm_of L} \<Longrightarrow>
    ord_res.ground_resolution C D CD \<Longrightarrow>
    N' = finsert CD N \<Longrightarrow>
    ord_res_1 N N'"

lemma right_unique_ord_res_1: "right_unique ord_res_1"
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
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "C1' = C2'"
        by (metis (no_types, lifting) Uniq_D ord_res.unique_ground_factoring)
      with hyps1 hyps2 show ?thesis
        by argo
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
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
        by (meson Uniq_D Uniq_is_least_false_clause)
      with hyps1 hyps2 have "L1 = L2"
        by (meson Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      with hyps1 hyps2 have False
        by metis
      thus ?thesis ..
    next
      case hyps2: (resolution C2 L2 D2 CD2)
      from hyps1 hyps2 have "C1 = C2"
        by (meson Uniq_D Uniq_is_least_false_clause)
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
        unfolding is_least_false_clause_def
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
        unfolding is_least_false_clause_def
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
        unfolding ex_false_clause_def is_least_false_clause_def
        using linorder_cls.is_least_in_fset_iff by force
    next
      case (resolution C L D CD)
      with \<open>\<not> ex_false_clause (fset N)\<close> show False
        unfolding ex_false_clause_def is_least_false_clause_def
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
          using hyps mempty_no_in is_least_false_clause_def by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps is_least_false_clause_def
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(1) by blast
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
          using hyps mempty_no_in is_least_false_clause_def by simp
      next
        show "ex_false_clause (fset N2)"
          unfolding ex_false_clause_def
          using hyps is_least_false_clause_def
          by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD)
      next
        show "C |\<in>| N2"
          using hyps is_least_false_clause_def linorder_cls.is_least_in_fset_ffilterD(1) by blast
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

lemma ex_ord_res_1_if_not_final:
  assumes "\<not> ord_res_1_final N"
  shows "\<exists>N'. ord_res_1 N N'"
proof -
  from assms have "{#} |\<notin>| N" and "ex_false_clause (fset N)"
    unfolding ord_res_1_final_def ord_res_final_def by argo+

  obtain C where C_least_false: "is_least_false_clause N C"
    using \<open>ex_false_clause (fset N)\<close> obtains_least_false_clause_if_ex_false_clause by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)

    hence "\<not> linorder_lit.is_greatest_in_mset C L"
      using pos_lit_not_greatest_if_maximal_in_least_false_clause
      using C_least_false is_least_false_clause_def by blast

    then obtain C' where "ord_res.ground_factoring C C'"
      using ex_ground_factoringI C_max Pos by metis

    thus ?thesis
      using ord_res_1.factoring
      by (metis \<open>is_least_false_clause N C\<close> is_pos_def ord_res.ground_factoring.cases)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset N) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain CD where
      "ord_res.ground_resolution C D CD"
      using ex_ground_resolutionI C_max Neg by metis

    ultimately show ?thesis
      using ord_res_1.resolution[of N C L D CD "finsert CD N"]
      using C_least_false C_max Neg by auto
  qed
qed

corollary ord_res_1_safe: "ord_res_1_final N \<or> (\<exists>N'. ord_res_1 N N')"
  using ex_ord_res_1_if_not_final by metis


subsection \<open>ORD-RES-2 (full factorization)\<close>

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

inductive ord_res_2_step where
  "ord_res_2 N S S' \<Longrightarrow> ord_res_2_step (N, S) (N, S')"

inductive ord_res_2_final where
  "ord_res_final (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<Longrightarrow> ord_res_2_final (N, (U\<^sub>r, U\<^sub>e\<^sub>f))"

inductive ord_res_2_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_2_load N (N, ({||}, {||}))"

interpretation ord_res_2_semantics: semantics where
  step = ord_res_2_step and
  final = ord_res_2_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>r U\<^sub>f\<^sub>f :: "'f gterm clause fset" where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>f\<^sub>f))"
    by (metis prod.exhaust)

  assume "ord_res_2_final S"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    by (simp add: S_def ord_res_2_final.simps ord_res_final_def)
  thus "finished ord_res_2_step S"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
    have False if "ord_res_2 N (U\<^sub>r, U\<^sub>f\<^sub>f) x" for x
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>f\<^sub>f)" x rule: ord_res_2.cases)
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
    thus "finished ord_res_2_step S"
      unfolding finished_def ord_res_2_step.simps S_def
      by (metis prod.inject)
  next
    assume no_false_cls: "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    have False if "ord_res_2 N (U\<^sub>r, U\<^sub>f\<^sub>f) x" for x
      using that[unfolded S_def]
    proof (cases N "(U\<^sub>r, U\<^sub>f\<^sub>f)" x rule: ord_res_2.cases)
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
    thus "finished ord_res_2_step S"
      unfolding finished_def ord_res_2_step.simps S_def
      by (metis prod.inject)
  qed
qed

interpretation ord_res_2_language: language where
  step = ord_res_2_step and
  final = ord_res_2_final and
  load = ord_res_2_load
  by unfold_locales

fun ord_res_1_matches_ord_res_2 where
  "ord_res_1_matches_ord_res_2 S1 (N, (U\<^sub>r, U\<^sub>f\<^sub>f)) \<longleftrightarrow> (\<exists>U\<^sub>f.
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

lemma fset_fset_upto[simp]: "fset (fset_upto m n) = {m..n}"
  apply (induction n)
  apply simp
  apply simp
  using atLeastAtMostSuc_conv by presburger

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
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 S\<^sub>2"
  shows "ord_res_1_final S\<^sub>1 \<longleftrightarrow> ord_res_2_final S\<^sub>2"
proof -
  obtain N U\<^sub>r U\<^sub>f\<^sub>f where "S\<^sub>2 = (N, (U\<^sub>r, U\<^sub>f\<^sub>f))"
    by (metis prod.exhaust)
  with match obtain U\<^sub>f where
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
    by (simp add: S\<^sub>1_def \<open>S\<^sub>2 = (N, U\<^sub>r, U\<^sub>f\<^sub>f)\<close> ord_res_1_final_def ord_res_2_final.simps
        ord_res_final_def)
qed


lemma ex_ord_res_2_if_not_final:
  assumes "\<not> ord_res_2_final S"
  shows "\<exists>S'. ord_res_2_step S S'"
proof -
  from assms obtain N U\<^sub>r U\<^sub>e\<^sub>f where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))" and
    "{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
    "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (metis ord_res_2_final.intros ord_res_final_def surj_pair)

  obtain C where C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    using \<open>ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))\<close> obtains_least_false_clause_if_ex_false_clause
    by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using ord_res_2.factoring[OF C_least_false C_max] S_def is_pos_def
      by (metis ord_res_2_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain CD where
      "ord_res.ground_resolution C D CD"
      using ex_ground_resolutionI C_max Neg by metis

    ultimately show ?thesis
      using ord_res_2.resolution[OF C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_2_step.intros)
  qed
qed

corollary ord_res_2_safe: "ord_res_2_final S \<or> (\<exists>S'. ord_res_2_step S S')"
  using ex_ord_res_2_if_not_final by metis

lemma safe_states_if_ord_res_1_matches_ord_res_2:
  assumes match: "ord_res_1_matches_ord_res_2 S\<^sub>1 S\<^sub>2"
  shows "safe_state ord_res_1 ord_res_1_final S\<^sub>1 \<and> safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
proof -
  have "safe_state ord_res_1 ord_res_1_final S\<^sub>1"
    using safe_state_if_all_states_safe ord_res_1_safe by metis

  moreover have "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    using safe_state_if_all_states_safe ord_res_2_safe by metis

  ultimately show ?thesis
    by argo
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

lemma right_unique_ord_res_2: "right_unique (ord_res_2 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_2 N s s'" and step2: "ord_res_2 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_2.cases)
    case hyps1: (factoring U\<^sub>r1 U\<^sub>f\<^sub>f1 C1 L1 U\<^sub>f\<^sub>f'1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_2.cases)
      case (factoring U\<^sub>r2 U\<^sub>f\<^sub>f2 C2 L2 U\<^sub>f\<^sub>f'2)
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution U\<^sub>r U\<^sub>f\<^sub>f C L D CD U\<^sub>r')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution U\<^sub>r1 U\<^sub>f\<^sub>f1 C1 L1 D1 CD1 U\<^sub>r'1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_2.cases)
      case (factoring U\<^sub>r2 U\<^sub>f\<^sub>f2 C2 L2 U\<^sub>f\<^sub>f'2)
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    next
      case (resolution U\<^sub>r U\<^sub>f\<^sub>f C L D CD U\<^sub>r')
      with hyps1 show ?thesis
        by (metis (mono_tags, lifting) Uniq_is_least_false_clause
            linorder_lit.Uniq_is_maximal_in_mset ord_res.Uniq_production_eq_singleton
            ord_res.unique_ground_resolution prod.inject the1_equality')
    qed
  qed
qed

lemma right_unique_ord_res_2_step: "right_unique ord_res_2_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_2_step x y \<Longrightarrow> ord_res_2_step x z \<Longrightarrow> y = z"
    apply (cases x; cases y; cases z)
    apply (simp add: ord_res_2_step.simps)
    using right_unique_ord_res_2[THEN right_uniqueD]
    by blast
qed

lemma forward_simulation:
  assumes match: "ord_res_1_matches_ord_res_2 s1 s2" and
    step1: "ord_res_1 s1 s1'"
  shows "(\<exists>s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> ord_res_1_matches_ord_res_2 s1' s2') \<or>
    ord_res_1_matches_ord_res_2 s1' s2 \<and> ord_res_1_measure s1' \<subset># ord_res_1_measure s1"
proof -
  let
    ?match = "ord_res_1_matches_ord_res_2" and
    ?measure = "ord_res_1_measure" and
    ?order = "(\<subset>#)"

  obtain N U\<^sub>r U\<^sub>f\<^sub>f :: "'f gterm clause fset" where
    s2_def: "s2 = (N, (U\<^sub>r, U\<^sub>f\<^sub>f))"
    by (metis prod.exhaust)

  from match obtain U\<^sub>f where
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

  show "(\<exists>s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> ?match s1' s2') \<or>
    ?match s1' s2 \<and> ?order (?measure s1') (?measure s1)"
    using step1
  proof (cases s1 s1' rule: ord_res_1.cases)
    case (factoring C L C')

    have C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f) C"
      using factoring
      unfolding is_least_false_clause_def s1_def by argo

    hence C_in: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f |\<union>| U\<^sub>f"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff s1_def by argo
    hence C_in_disj: "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> C |\<in>| U\<^sub>f"
      by simp

    show ?thesis
    proof (cases "C' = sfac C'")
      case True
      let ?s2' = "(N, (U\<^sub>r, finsert C' U\<^sub>f\<^sub>f))"

      have "ord_res_2_step\<^sup>+\<^sup>+ s2 ?s2'"
      proof (rule tranclp.r_into_trancl)
        show "ord_res_2_step s2 (N, U\<^sub>r, finsert C' U\<^sub>f\<^sub>f)"
          using C_in_disj
        proof (elim disjE)
          assume "C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
          show ?thesis
            unfolding s2_def
          proof (intro ord_res_2_step.intros ord_res_2.factoring)
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
          proof (intro ord_res_2_step.intros ord_res_2.factoring)
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

      moreover have "?match s1' ?s2'"
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

      have "?match s1' s2"
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

        ultimately have "ord_res_1_matches_ord_res_2 (finsert C' s1) (N, (U\<^sub>r, U\<^sub>f\<^sub>f))"
          unfolding ord_res_1_matches_ord_res_2.simps by metis
        thus ?thesis
          unfolding s2_def \<open>s1' = finsert C' s1\<close> by simp
      qed

      moreover have "?order (?measure s1') (?measure s1)"
      proof -
        have "?measure s1 = C"
          unfolding ord_res_1_measure_def
          using C_least_false[folded s1_def]
          by (metis (mono_tags, lifting) linorder_cls.Uniq_is_least_in_fset
              is_least_false_clause_def the1_equality' the_equality)

        moreover have "?measure s1' = C'"
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
              using C_least_false s1_def is_least_false_clause_def
                linorder_cls.is_least_in_ffilter_iff by simp
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
      using resolution s1_def by metis
    hence C_least_false': "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
      using is_least_false_clause_if_is_least_false_clause_in_union_unproductive[
          OF U\<^sub>f_unproductive \<open>C |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>f\<^sub>f\<close>] by argo

    define s2' where
      "s2' = (N, (finsert CD U\<^sub>r, U\<^sub>f\<^sub>f))"

    have "ord_res_2_step\<^sup>+\<^sup>+ s2 s2'"
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
        by (auto simp: s2_def s2'_def ord_res_2_step.simps)
    qed

    moreover have "?match s1' s2'"
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
qed

lemma lift_tranclp_to_pairs_with_constant_fst:
  "(R x)\<^sup>+\<^sup>+ y z \<Longrightarrow> (\<lambda>(x, y) (x', z). x = x' \<and> R x y z)\<^sup>+\<^sup>+ (x, y) (x, z)"
  by (induction z arbitrary: rule: tranclp_induct) (auto simp: tranclp.trancl_into_trancl)

theorem bisimulation_ord_res_1_ord_res_2:
  defines "match \<equiv> \<lambda>i s1 s2. i = ord_res_1_measure s1 \<and> ord_res_1_matches_ord_res_2 s1 s2"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'f gterm clause fset \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow> bool) ORDER.
    bisimulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final ORDER MATCH"
proof (rule ex_bisimulation_from_forward_simulation)
  show "right_unique ord_res_1"
    using right_unique_ord_res_1 .
next
  show "right_unique ord_res_2_step"
    using right_unique_ord_res_2_step .
next
  show "\<forall>s1. ord_res_1_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_1 s1 s1')"
    using ord_res_1_semantics.final_finished
    by (simp add: finished_def)
next
  show "\<forall>s2. ord_res_2_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_2_step s2 s2')"
    using ord_res_2_semantics.final_finished
    by (simp add: finished_def)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_1_final s1 = ord_res_2_final s2"
    using ord_res_1_final_iff_ord_res_2_final
    by (simp add: match_def)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_1 ord_res_1_final s1 \<and>
    safe_state ord_res_2_step ord_res_2_final s2"
  proof (intro allI impI)
    fix i s1 S2
    assume "match i s1 S2"

    then obtain N s2 where
      S2_def: "S2 = (N, s2)" and
      "i = ord_res_1_measure s1" and
      match: "ord_res_1_matches_ord_res_2 s1 S2"
      unfolding match_def
      by (metis prod.exhaust)

    show "safe_state ord_res_1 ord_res_1_final s1 \<and> safe_state ord_res_2_step ord_res_2_final S2"
      using safe_states_if_ord_res_1_matches_ord_res_2[OF match] .
  qed
next
  show "wfP (\<subset>#)"
    using wfP_subset_mset .
next
  show "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> ord_res_1 s1 s1' \<longrightarrow>
    (\<exists>i' s2'. ord_res_2_step\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> i' \<subset># i)"
  proof (intro allI impI)
    fix i s1 S2 s1'
    assume "match i s1 S2"
    then obtain N s2 where
      S2_def: "S2 = (N, s2)" and "i = ord_res_1_measure s1" and "ord_res_1_matches_ord_res_2 s1 S2"
      unfolding match_def
      by (metis prod.exhaust)

    moreover assume "ord_res_1 s1 s1'"

    ultimately have "(\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> ord_res_1_matches_ord_res_2 s1' S2') \<or>
    ord_res_1_matches_ord_res_2 s1' S2 \<and> ord_res_1_measure s1' \<subset># ord_res_1_measure s1"
      using forward_simulation by metis

    thus "(\<exists>i' S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match i' s1' S2') \<or> (\<exists>i'. match i' s1' S2 \<and> i' \<subset># i)"
      unfolding S2_def prod.case
      using lift_tranclp_to_pairs_with_constant_fst[of ord_res_2 N s2]
      by (metis (mono_tags, lifting) \<open>i = ord_res_1_measure s1\<close> match_def)
  qed
qed


subsection \<open>ORD-RES-3 (full resolve)\<close>

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

inductive ord_res_3_step where
  "ord_res_3 N s s' \<Longrightarrow> ord_res_3_step (N, s) (N, s')"

inductive ord_res_3_final where
  "ord_res_final (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) \<Longrightarrow> ord_res_3_final (N, (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f))"

inductive ord_res_3_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_3_load N (N, ({||}, {||}))"

interpretation ord_res_3_semantics: semantics where
  step = ord_res_3_step and
  final = ord_res_3_final
proof unfold_locales
  fix S3 :: "'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset"

  obtain N U\<^sub>r\<^sub>r U\<^sub>f\<^sub>f :: "'f gterm clause fset" where
    S3_def: "S3 = (N, (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f))"
    by (metis prod.exhaust)

  assume "ord_res_3_final S3"
  hence "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f \<or> \<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    by (simp add: S3_def ord_res_3_final.simps ord_res_final_def)
  thus "finished ord_res_3_step S3"
  proof (elim disjE)
    assume "{#} |\<in>| N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f"
    hence "is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) {#}"
      using is_least_false_clause_mempty by metis
    hence "\<nexists>C L. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C \<and> linorder_lit.is_maximal_in_mset C L"
      by (metis Uniq_D Uniq_is_least_false_clause bot_fset.rep_eq fBex_fempty
          linorder_lit.is_maximal_in_mset_iff set_mset_empty)
    hence "\<nexists>x. ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f) x"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def ord_res_3_step.simps S3_def)
  next
    assume "\<not> ex_false_clause (fset (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f))"
    hence "\<nexists>C. is_least_false_clause (N |\<union>| U\<^sub>r\<^sub>r |\<union>| U\<^sub>f\<^sub>f) C"
      unfolding ex_false_clause_def is_least_false_clause_def
      by (metis (no_types, lifting) linorder_cls.is_least_in_fset_ffilterD(1)
          linorder_cls.is_least_in_fset_ffilterD(2))
    hence "\<nexists>x. ord_res_3 N (U\<^sub>r\<^sub>r, U\<^sub>f\<^sub>f) x"
      by (auto simp: S3_def elim: ord_res_3.cases)
    thus ?thesis
      by (simp add: finished_def ord_res_3_step.simps S3_def)
  qed
qed

interpretation ord_res_3_language: language where
  step = ord_res_3_step and
  final = ord_res_3_final and
  load = ord_res_3_load
  by unfold_locales

inductive ord_res_2_matches_ord_res_3 where
  "(\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
      (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r) \<Longrightarrow>
  ord_res_2_matches_ord_res_3 (N, (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)) (N, (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f))"

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

lemma is_least_false_clause_funion_cancel_right:
  assumes
    "\<forall>C |\<in>| N2. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms
proof (induction N2)
  case empty
  thus ?case
    by simp
next
  case (insert x N2)
  thus ?case
    using is_least_false_clause_finsert_cancel
    by (metis finsertCI funionI1 funion_finsert_right)
qed

lemma is_least_false_clause_conv_if_partial_resolution_invariant:
  assumes "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
  shows "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
proof -
  have "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)"
    by (simp add: sup_commute sup_left_commute)
  also have "\<dots> = is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
  proof (rule is_least_false_clause_funion_cancel_right)
    show "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<forall>U. ord_res.production U C = {}"
    proof (intro ballI)
      fix C
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. (\<exists>C'. ground_resolution D C C')"
        using assms by (metis eres_eq_after_tranclp_ground_resolution resolvable_if_neq_eres)
      hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
        using nex_strictly_maximal_pos_lit_if_resolvable by metis
      thus "\<forall>U. ord_res.production U C = {}"
        using unproductive_if_nex_strictly_maximal_pos_lit by metis
    qed
  next
    show "\<forall>C |\<in>| U\<^sub>p\<^sub>r. \<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
    proof (intro ballI)
      fix C
      assume "C |\<in>| U\<^sub>p\<^sub>r"
      then obtain D1 D2 where
        "D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
        "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
        "C \<noteq> eres D1 D2" and
        "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using assms by metis
  
      have "eres D1 D2 = eres D1 C"
        using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_eq_after_tranclp_ground_resolution by metis
  
      show "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
      proof (intro bexI conjI)
        have "eres D1 C \<preceq>\<^sub>c C"
          using eres_le .
        thus "eres D1 D2 \<prec>\<^sub>c C"
          using \<open>C \<noteq> eres D1 D2\<close> \<open>eres D1 D2 = eres D1 C\<close> by order
      next
        show "{eres D1 D2} \<TTurnstile>e {C}"
          using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_entails_resolvent by metis
      next
        show "eres D1 D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
          using \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> by simp
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma ord_res_2_final_iff_ord_res_3_final:
  assumes match: "ord_res_2_matches_ord_res_3 S\<^sub>2 S\<^sub>3"
  shows "ord_res_2_final S\<^sub>2 \<longleftrightarrow> ord_res_3_final S\<^sub>3"
  using match
proof (cases S\<^sub>2 S\<^sub>3 rule: ord_res_2_matches_ord_res_3.cases)
  case match_hyps: (1 U\<^sub>p\<^sub>r N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)

  note invars = match_hyps(3-)
  
  have U\<^sub>p\<^sub>r_spec: "\<forall>C|\<in>|U\<^sub>p\<^sub>r. \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
    using invars by argo

  have least_false_spec: "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) =
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    using invars is_least_false_clause_conv_if_partial_resolution_invariant by metis

  have U\<^sub>p\<^sub>r_unproductive: "\<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
  proof (intro ballI)
    fix C
    assume "C |\<in>| U\<^sub>p\<^sub>r"
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
      using U\<^sub>p\<^sub>r_spec
      by (metis eres_eq_after_tranclp_ground_resolution nex_strictly_maximal_pos_lit_if_neq_eres)
    thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f |\<union>| U\<^sub>p\<^sub>r)) C = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f: "\<And>C.
    ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C =
    ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: funion_left_commute sup_commute)

  have "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) \<longleftrightarrow>
    ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
  proof (rule iffI)
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    then obtain C where "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
      using obtains_least_false_clause_if_ex_false_clause by metis
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      using least_false_spec ex_false_clause_iff by metis
  next
    assume "ex_false_clause (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    thus "ex_false_clause (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
      unfolding ex_false_clause_def
      unfolding Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f
      by auto
  qed

  moreover have "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<longleftrightarrow> {#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
  proof (rule iffI)
    assume "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    hence "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f \<or> {#} |\<in>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
      by auto
    thus "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    proof (elim disjE)
      assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>f"
      thus ?thesis
        by auto
    next
      have "{#} |\<notin>| U\<^sub>p\<^sub>r"
        using U\<^sub>p\<^sub>r_spec[rule_format, of "{#}"]
        by (metis eres_eq_after_tranclp_ground_resolution eres_mempty_right)
      moreover assume "{#} |\<in>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r"
      ultimately show ?thesis
        by simp
    qed
  next
    assume "{#} |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
    then show "{#} |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
      by auto
  qed

  ultimately have "ord_res_final (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) = ord_res_final (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    unfolding ord_res_final_def by argo

  thus "ord_res_2_final S\<^sub>2 \<longleftrightarrow> ord_res_3_final S\<^sub>3"
    unfolding match_hyps(1,2)
    by (simp add: ord_res_2_final.simps ord_res_3_final.simps sup_assoc)
qed

definition ord_res_2_measure where
  "ord_res_2_measure S1 =
    (let (N, (U\<^sub>r, U\<^sub>e\<^sub>f)) = S1 in
    (if \<exists>C. is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C then
      The (is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))
    else
      {#}))"

lemma tranclp_if_relpowp: "n \<noteq> 0 \<Longrightarrow> (R ^^ n) x y \<Longrightarrow> R\<^sup>+\<^sup>+ x y"
  by (meson bot_nat_0.not_eq_extremum tranclp_power)

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

definition resolvent_at where
  "resolvent_at C D i = (THE CD. (ground_resolution C ^^ i) D CD)"

lemma resolvent_at_0[simp]: "resolvent_at C D 0 = D"
  by (simp add: resolvent_at_def)

lemma resolvent_at_less_cls_resolvent_at:
  assumes reso_at: "(ground_resolution C ^^ n) D CD"
  assumes "i < j" and "j \<le> n"
  shows "resolvent_at C D j \<prec>\<^sub>c resolvent_at C D i"
proof -
  obtain j' where
    "j = i + Suc j'"
    using \<open>i < j\<close> by (metis less_iff_Suc_add nat_arith.suc1)

  obtain n' where
    "n = j + n'"
    using \<open>j \<le> n\<close> by (metis le_add_diff_inverse)

  obtain CD\<^sub>i CD\<^sub>j CD\<^sub>n where
    "(ground_resolution C ^^ i) D CD\<^sub>i" and
    "(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j"
    "(ground_resolution C ^^ n') CD\<^sub>j CD\<^sub>n"
    using reso_at \<open>n = j + n'\<close> \<open>j = i + Suc j'\<close> by (metis relpowp_plusD)

  have *: "resolvent_at C D i = CD\<^sub>i"
    unfolding resolvent_at_def
    using \<open>(ground_resolution C ^^ i) D CD\<^sub>i\<close>
    by (metis Uniq_ground_resolution Uniq_relpowp theI')

  have "(ground_resolution C ^^ j) D CD\<^sub>j"
    unfolding \<open>j = i + Suc j'\<close>
    using \<open>(ground_resolution C ^^ i) D CD\<^sub>i\<close> \<open>(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j\<close>
    by (metis relpowp_trans)
  hence **: "resolvent_at C D j = CD\<^sub>j"
    unfolding resolvent_at_def
    by (metis Uniq_ground_resolution Uniq_relpowp theI')

  have "(ground_resolution C)\<^sup>+\<^sup>+ CD\<^sub>i CD\<^sub>j"
    using \<open>(ground_resolution C ^^ Suc j') CD\<^sub>i CD\<^sub>j\<close>
    by (metis Zero_not_Suc tranclp_if_relpowp)
  hence "CD\<^sub>j \<prec>\<^sub>c CD\<^sub>i"
    using resolvent_lt_right_premise_if_tranclp_ground_resolution by metis
  thus ?thesis
    unfolding * ** .
qed

lemma
  assumes reso_at: "(ground_resolution C ^^ n) D CD" and "i < n"
  shows
    left_premisse_lt_resolvent_at: "C \<prec>\<^sub>c resolvent_at C D i" and
    max_lit_resolvent_at:
      "ord_res.is_maximal_lit L D \<Longrightarrow> ord_res.is_maximal_lit L (resolvent_at C D i)" and
    nex_pos_strictly_max_lit_in_resolvent_at:
      "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at C D i)" and
    ground_resolution_resolvent_at_resolvent_at_Suc:
      "ground_resolution C (resolvent_at C D i) (resolvent_at C D (Suc i))" and
    relpowp_to_resolvent_at: "(ground_resolution C ^^ i) D (resolvent_at C D i)"
proof -
  obtain j where n_def: "n = i + Suc j"
    using \<open>i < n\<close> less_natE by auto

  obtain CD' where "(ground_resolution C ^^ i) D CD'" and "(ground_resolution C ^^ Suc j) CD' CD"
    using reso_at n_def by (metis relpowp_plusD)

  have "resolvent_at C D i = CD'"
    unfolding resolvent_at_def
    using \<open>(ground_resolution C ^^ i) D CD'\<close>
    by (metis Uniq_ground_resolution Uniq_relpowp theI')

  have "C \<prec>\<^sub>c CD'"
  proof (rule left_premise_lt_right_premise_if_tranclp_ground_resolution)
    show "(ground_resolution C)\<^sup>+\<^sup>+ CD' CD"
      using \<open>(ground_resolution C ^^ Suc j) CD' CD\<close>
      by (metis Zero_not_Suc tranclp_if_relpowp)
  qed
  thus "C \<prec>\<^sub>c resolvent_at C D i"
    unfolding \<open>resolvent_at C D i = CD'\<close> by argo

  show "ord_res.is_maximal_lit L (resolvent_at C D i)" if "ord_res.is_maximal_lit L D"
    unfolding \<open>resolvent_at C D i = CD'\<close>
    using that
    using \<open>(ground_resolution C ^^ i) D CD'\<close>
    by (smt (verit, ccfv_SIG) Uniq_ground_resolution Uniq_relpowp Zero_not_Suc
        \<open>\<And>thesis. (\<And>CD'. \<lbrakk>(ground_resolution C ^^ i) D CD'; (ground_resolution C ^^ Suc j) CD' CD\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        linorder_lit.Uniq_is_greatest_in_mset linorder_lit.Uniq_is_maximal_in_mset literal.sel(1)
        n_def relpowp_ground_resolutionD reso_at the1_equality' zero_eq_add_iff_both_eq_0)

  show "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at C D i)"
    unfolding \<open>resolvent_at C D i = CD'\<close>
    by (metis Zero_not_Suc \<open>(ground_resolution C ^^ Suc j) CD' CD\<close>
        nex_strictly_maximal_pos_lit_if_resolvable tranclpD tranclp_if_relpowp)

  show "ground_resolution C (resolvent_at C D i) (resolvent_at C D (Suc i))"
  proof -
    obtain CD'' where "ground_resolution C CD' CD''" and "(ground_resolution C ^^ j) CD'' CD"
      using \<open>(ground_resolution C ^^ Suc j) CD' CD\<close> by (metis relpowp_Suc_D2)
    hence "(ground_resolution C ^^ Suc i) D CD''"
      using \<open>(ground_resolution C ^^ i) D CD'\<close> by auto
    hence "resolvent_at C D (Suc i) = CD''"
      unfolding resolvent_at_def
      by (metis Uniq_ground_resolution Uniq_relpowp theI')

    show ?thesis
      unfolding \<open>resolvent_at C D i = CD'\<close> \<open>resolvent_at C D (Suc i) = CD''\<close>
      using \<open>ground_resolution C CD' CD''\<close> .
  qed

  show "(ground_resolution C ^^ i) D (resolvent_at C D i)"
    using \<open>(ground_resolution C ^^ i) D CD'\<close> \<open>resolvent_at C D i = CD'\<close> by argo
qed

definition resolvents_upto where
  "resolvents_upto C D n = resolvent_at C D |`| fset_upto (Suc 0) n"

lemma resolvents_upto_0[simp]:
  "resolvents_upto C D 0 = {||}"
  by (simp add: resolvents_upto_def)

lemma resolvents_upto_Suc[simp]:
  "resolvents_upto C D (Suc n) = finsert (resolvent_at C D (Suc n)) (resolvents_upto C D n)"
  by (simp add: resolvents_upto_def)

lemma resolvent_at_fmember_resolvents_upto:
  assumes "k \<noteq> 0"
  shows "resolvent_at C D k |\<in>| resolvents_upto C D k"
  unfolding resolvents_upto_def
proof (rule fimageI)
  show "k |\<in>| fset_upto (Suc 0) k"
    using assms by simp
qed

lemma backward_simulation_2_to_3:
  fixes match measure less
  defines "match \<equiv> ord_res_2_matches_ord_res_3"
  assumes
    match: "match S2 S3" and
    step2: "ord_res_3_step S3 S3'"
  shows "(\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match S2' S3')"
  using match[unfolded match_def]
proof (cases S2 S3 rule: ord_res_2_matches_ord_res_3.cases)
  case match_hyps: (1 U\<^sub>p\<^sub>r N U\<^sub>e\<^sub>r U\<^sub>e\<^sub>f)
  note invars = match_hyps(3-)

  have U\<^sub>p\<^sub>r_spec: "\<forall>C|\<in>|U\<^sub>p\<^sub>r. \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
    (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
    using invars by argo

  hence C_not_least_with_partial: "\<not> is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    if C_in: "C |\<in>| U\<^sub>p\<^sub>r" for C
  proof -
    obtain D1 D2 where
      "D1 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D2 |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "(ground_resolution D1)\<^sup>+\<^sup>+ D2 C" and
      "C \<noteq> eres D1 D2" and
      "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
      using U\<^sub>p\<^sub>r_spec C_in by metis

    have "eres D1 C = eres D1 D2"
      using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> eres_eq_after_tranclp_ground_resolution by metis
    hence "eres D1 C \<prec>\<^sub>c C"
      using eres_le[of D1 C] \<open>C \<noteq> eres D1 D2\<close> by order

    show ?thesis
    proof (cases "ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) (eres D1 D2) \<TTurnstile> eres D1 D2")
      case True
      then show ?thesis
        by (metis (no_types, lifting) \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 C\<close> \<open>eres D1 C = eres D1 D2\<close>
            clause_true_if_eres_true is_least_false_clause_def
            linorder_cls.is_least_in_fset_ffilterD(2))
    next
      case False
      then show ?thesis
        by (metis (mono_tags, lifting) Un_iff \<open>eres D1 C = eres D1 D2\<close> \<open>eres D1 C \<prec>\<^sub>c C\<close>
            \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
            linorder_cls.not_less_iff_gr_or_eq sup_fset.rep_eq)
    qed
  qed

  have least_false_conv: "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) =
    is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)"
    using invars is_least_false_clause_conv_if_partial_resolution_invariant by metis

  have U\<^sub>p\<^sub>r_unproductive: "\<And>N. \<forall>C |\<in>| U\<^sub>p\<^sub>r. ord_res.production N C = {}"
  proof (intro ballI)
    fix C
    assume "C |\<in>| U\<^sub>p\<^sub>r"
    hence "\<exists>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. (\<exists>C'. ground_resolution D C C')"
      using U\<^sub>p\<^sub>r_spec by (metis eres_eq_after_tranclp_ground_resolution resolvable_if_neq_eres)
    hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
      using nex_strictly_maximal_pos_lit_if_resolvable by metis
    thus "\<And>N. ord_res.production N C = {}"
      using unproductive_if_nex_strictly_maximal_pos_lit by metis
  qed

  hence Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f:
    "\<And>C. ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C = ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) C"
    using Interp_union_unproductive[OF finite_fset finite_fset, folded union_fset,
        of U\<^sub>p\<^sub>r "N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"]
    by (simp add: funion_left_commute sup_commute)

  have U\<^sub>p\<^sub>r_have_generalization: "\<forall>Ca |\<in>| U\<^sub>p\<^sub>r. \<exists>D |\<in>| U\<^sub>e\<^sub>r. D \<prec>\<^sub>c Ca \<and> {D} \<TTurnstile>e {Ca}"
  proof (intro ballI)
    fix Ca
    assume "Ca |\<in>| U\<^sub>p\<^sub>r"
    then obtain D1 D2 where
      "D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca" and
      "Ca \<noteq> eres D1 D2" and
      "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
      using U\<^sub>p\<^sub>r_spec by metis

    have "eres D1 D2 = eres D1 Ca"
      using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca\<close> eres_eq_after_tranclp_ground_resolution by metis

    show "\<exists>D |\<in>| U\<^sub>e\<^sub>r. D \<prec>\<^sub>c Ca \<and> {D} \<TTurnstile>e {Ca}"
    proof (intro bexI conjI)
      have "eres D1 Ca \<preceq>\<^sub>c Ca"
        using eres_le .
      thus "eres D1 D2 \<prec>\<^sub>c Ca"
        using \<open>Ca \<noteq> eres D1 D2\<close> \<open>eres D1 D2 = eres D1 Ca\<close> by order
    next
      show "{eres D1 D2} \<TTurnstile>e {Ca}"
        using \<open>(ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca\<close> eres_entails_resolvent by metis
    next
      show "eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using \<open>eres D1 D2 |\<in>| U\<^sub>e\<^sub>r\<close> by simp
    qed
  qed

  from step2 obtain s3' where S3'_def: "S3' = (N, s3')" and "ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'"
    by (auto simp: match_hyps(1,2) elim: ord_res_3_step.cases)

  show ?thesis
    using \<open>ord_res_3 N (U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) s3'\<close>
  proof (cases N "(U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)" s3' rule: ord_res_3.cases)
    case (factoring C L U\<^sub>f\<^sub>f')

    define S2' where
      "S2' = (N, (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, finsert (sfac C) U\<^sub>e\<^sub>f))"

    have "ord_res_2_step\<^sup>+\<^sup>+ S2 S2'"
      unfolding match_hyps(1,2) S2'_def
    proof (intro tranclp.r_into_trancl ord_res_2_step.intros ord_res_2.factoring)
      show "is_least_false_clause (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r) |\<union>| U\<^sub>e\<^sub>f) C"
        using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
        using least_false_conv
        by (metis sup_assoc)
    next
      show "ord_res.is_maximal_lit L C"
        using factoring by metis
    next
      show "is_pos L"
        using factoring by metis
    next
      show "finsert (sfac C) U\<^sub>e\<^sub>f = finsert (sfac C) U\<^sub>e\<^sub>f"
        by argo
    qed

    moreover have "match S2' S3'"
      unfolding S2'_def S3'_def
      unfolding factoring
      unfolding match_def
    proof (rule ord_res_2_matches_ord_res_3.intros)
      show "\<forall>Ca|\<in>|U\<^sub>p\<^sub>r.
        \<exists>D1|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (sfac C) U\<^sub>e\<^sub>f.
        (ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca \<and> Ca \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| U\<^sub>e\<^sub>r"
        using U\<^sub>p\<^sub>r_spec by auto
    qed

    ultimately show ?thesis
      by metis
  next
    case (resolution C L D DC U\<^sub>r\<^sub>r')

    have "(ground_resolution D)\<^sup>*\<^sup>* C DC" "\<nexists>x. ground_resolution D DC x"
      using resolution by (simp_all add: full_run_def)

    moreover have "\<exists>x. ground_resolution D C x"
      unfolding ground_resolution_def
      using resolution
      by (metis Neg_atm_of_iff ex_ground_resolutionI ord_res.mem_productionE singletonI)

    ultimately have "(ground_resolution D)\<^sup>+\<^sup>+ C DC"
      by (metis rtranclpD)

    then obtain n where "(ground_resolution D ^^ Suc n) C DC"
      by (metis not0_implies_Suc not_gr_zero tranclp_power)

    hence "resolvent_at D C (Suc n) = DC"
      by (metis Uniq_ground_resolution Uniq_relpowp resolvent_at_def the_equality)

    have "eres D C = DC"
      by (metis \<open>(ground_resolution D)\<^sup>*\<^sup>* C DC\<close> \<open>\<nexists>x. ground_resolution D DC x\<close>
        eres_eq_after_rtranclp_ground_resolution resolvable_if_neq_eres)

    have steps: "k \<le> Suc n \<Longrightarrow> (ord_res_2_step ^^ k)
      (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f) (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)" for k
    proof (induction k)
      case 0
      show ?case
        by simp
    next
      case (Suc k)
      have "k < Suc n"
        using \<open>Suc k \<le> Suc n\<close> by presburger
      hence "k \<le> Suc n"
        by presburger
      hence "(ord_res_2_step ^^ k) (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)"
        using Suc.IH by metis

      moreover have "ord_res_2_step
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k, U\<^sub>e\<^sub>f)
        (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k), U\<^sub>e\<^sub>f)"
        unfolding resolvents_upto_Suc
      proof (intro ord_res_2_step.intros ord_res_2.resolution)
        show "is_least_false_clause (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)
          (resolvent_at D C k)"
          using \<open>k < Suc n\<close>
        proof (induction k)
          case 0
          have "is_least_false_clause (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
            using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
            unfolding least_false_conv .
          thus ?case
            unfolding funion_fempty_right funion_assoc[symmetric]
            by simp
        next
          case (Suc k')

          have "\<And>x. ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) x =
              ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) x"
            by (simp add: funion_left_commute sup_assoc sup_commute)
          also have "\<And>x. ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) x =
            ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x"
          proof (intro Interp_union_unproductive ballI)
            fix x y assume "y |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k')"
            hence "y |\<in>| U\<^sub>p\<^sub>r \<or> y |\<in>| resolvents_upto D C (Suc k')"
              by blast
            thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C (Suc k'))) y = {}"
            proof (elim disjE)
              assume "y |\<in>| U\<^sub>p\<^sub>r"
              thus ?thesis
                using U\<^sub>p\<^sub>r_unproductive by metis
            next
              assume "y |\<in>| resolvents_upto D C (Suc k')"
              then obtain i where "i |\<in>| fset_upto (Suc 0) (Suc k')" and "y = resolvent_at D C i"
                unfolding resolvents_upto_def by blast

              have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L (resolvent_at D C i)"
              proof (rule nex_pos_strictly_max_lit_in_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C DC"
                  using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
              next
                have "i \<le> Suc k'"
                  using \<open>i |\<in>| fset_upto (Suc 0) (Suc k')\<close> by auto
                thus "i < Suc n"
                  using \<open>Suc k' < Suc n\<close> by presburger
              qed

              then show ?thesis
                using \<open>y = resolvent_at D C i\<close> unproductive_if_nex_strictly_maximal_pos_lit
                by metis
            qed
          qed simp_all
          finally have Interp_simp: "\<And>x.
            ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) x =
            ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) x" .

          show ?case
            unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
          proof (intro conjI ballI impI)
            have "resolvent_at D C (Suc k') |\<in>| resolvents_upto D C (Suc k')"
              using resolvent_at_fmember_resolvents_upto by simp
            thus "resolvent_at D C (Suc k') |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f"
              by simp
          next

            show "\<not> ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f))
              (resolvent_at D C (Suc k')) \<TTurnstile> resolvent_at D C (Suc k')"
              unfolding Interp_simp
              by (metis (no_types, lifting) Suc.prems Zero_not_Suc
                  \<open>(ground_resolution D ^^ Suc n) C DC\<close> clause_true_if_resolved_true
                  insert_not_empty is_least_false_clause_def
                  linorder_cls.is_least_in_fset_ffilterD(2) local.resolution(2) local.resolution(7)
                  relpowp_to_resolvent_at tranclp_if_relpowp)
          next
            fix y
            assume "y \<noteq> resolvent_at D C (Suc k')"
            assume "\<not> ord_res_Interp (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
            hence "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
              unfolding Interp_simp .
            hence "\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y"
              using Interp_N_U\<^sub>r_U\<^sub>e\<^sub>f_eq_Interp_N_U\<^sub>e\<^sub>r_U\<^sub>e\<^sub>f by metis

            assume "y |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc k')) |\<union>| U\<^sub>e\<^sub>f"
            hence "y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f \<or> y |\<in>| resolvents_upto D C (Suc k')"
              by auto
            thus "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
            proof (elim disjE)
              assume "y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
              have "C \<preceq>\<^sub>c y"
              proof (cases "y = C")
                case True
                thus ?thesis
                  by order
              next
                case False
                thus ?thesis
                  using \<open>y |\<in>| N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
                  using \<open>\<not> ord_res_Interp (fset (N |\<union>| U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) y \<TTurnstile> y\<close>
                  using \<open>is_least_false_clause (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C\<close>
                  unfolding least_false_conv[symmetric]
                  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
                  by simp
              qed

              moreover have "resolvent_at D C (Suc k') \<prec>\<^sub>c C"
                by (metis Suc.prems \<open>(ground_resolution D ^^ Suc n) C DC\<close> less_or_eq_imp_le
                    resolvent_at_less_cls_resolvent_at resolvent_at_0 zero_less_Suc)

              ultimately show "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
                by order
            next
              assume "y |\<in>| resolvents_upto D C (Suc k')"
              then obtain i where
                i_in: "i |\<in>| fset_upto (Suc 0) (Suc k')" and y_def: "y = resolvent_at D C i"
                unfolding resolvents_upto_def by blast

              hence "i < Suc k'"
                using \<open>y \<noteq> resolvent_at D C (Suc k')\<close>
                by auto

              show "resolvent_at D C (Suc k') \<prec>\<^sub>c y"
                unfolding y_def
              proof (rule resolvent_at_less_cls_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C DC"
                  using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
              next
                show "i < Suc k'"
                  using \<open>y \<noteq> resolvent_at D C (Suc k')\<close> i_in y_def by auto
              next
                show "Suc k' \<le> Suc n"
                  using \<open>Suc k' < Suc n\<close> by presburger
              qed
            qed
          qed
        qed
      next
        show "ord_res.is_maximal_lit L (resolvent_at D C k)"
        proof (rule max_lit_resolvent_at)
          show "(ground_resolution D ^^ Suc n) C DC"
            using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        next
          show "ord_res.is_maximal_lit L C"
          using \<open>ord_res.is_maximal_lit L C\<close> .
        qed
      next
        show "is_neg L"
          using \<open>is_neg L\<close> .
      next
        show "D |\<in>| N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f"
          using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> by auto
      next
        show "D \<prec>\<^sub>c resolvent_at D C k"
        proof (rule left_premisse_lt_resolvent_at)
          show "(ground_resolution D ^^ Suc n) C DC"
            using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        qed
      next
        have "ord_res.production (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)) D =
          ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union> fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k)) D"
          by (simp add: funion_left_commute sup_assoc sup_commute)
        also have "\<dots> = ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D"
        proof (intro production_union_unproductive ballI)
          fix x
          assume "x |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k"
          hence "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L x"
            unfolding funion_iff
          proof (elim disjE)
            assume "x |\<in>| U\<^sub>p\<^sub>r"
            thus ?thesis
              using U\<^sub>p\<^sub>r_spec
              by (metis eres_eq_after_tranclp_ground_resolution nex_strictly_maximal_pos_lit_if_neq_eres)
          next
            assume "x |\<in>| resolvents_upto D C k"
            then obtain i where "i |\<in>| fset_upto (Suc 0) k" and x_def: "x = resolvent_at D C i"
              unfolding resolvents_upto_def by auto

            have "0 < i" and "i \<le> k"
              using \<open>i |\<in>| fset_upto (Suc 0) k\<close> by simp_all

            show ?thesis
              unfolding x_def
            proof (rule nex_pos_strictly_max_lit_in_resolvent_at)
              show "(ground_resolution D ^^ Suc n) C DC"
                using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
            next
              show "i < Suc n"
                using \<open>i \<le> k\<close> \<open>k < Suc n\<close> by presburger
            qed
          qed
          thus "ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f) \<union>
            fset (U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C k)) x = {}"
            using unproductive_if_nex_strictly_maximal_pos_lit by metis
        next
          show "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
            using \<open>D |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close> .
        qed simp_all
        finally show "ord_res.production (fset (N |\<union>| (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k) |\<union>| U\<^sub>e\<^sub>f)) D =
          {atm_of L}"
          using \<open>ord_res.production (fset (N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {atm_of L}\<close> by argo
      next
        show "ord_res.ground_resolution (resolvent_at D C k) D (resolvent_at D C (Suc k))"
          unfolding ground_resolution_def[symmetric]
        proof (rule ground_resolution_resolvent_at_resolvent_at_Suc)
          show "(ground_resolution D ^^ Suc n) C DC"
            using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
        next
          show "k < Suc n"
            using \<open>k < Suc n\<close> .
        qed
      next
        show "U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| finsert (resolvent_at D C (Suc k)) (resolvents_upto D C k) =
          finsert (resolvent_at D C (Suc k)) (U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C k)"
          by simp
      qed

      ultimately show ?case
        by (meson relpowp_Suc_I)
    qed

    hence "(ord_res_2_step ^^ Suc n) S2 (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n), U\<^sub>e\<^sub>f)"
      unfolding match_hyps(1,2) by blast

    moreover have "match (N, U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n), U\<^sub>e\<^sub>f) S3'"
    proof -
      have 1: "S3' = (N, finsert DC U\<^sub>e\<^sub>r, U\<^sub>e\<^sub>f)"
        unfolding S3'_def \<open>s3' = (U\<^sub>r\<^sub>r', U\<^sub>e\<^sub>f)\<close> \<open>U\<^sub>r\<^sub>r' = finsert DC U\<^sub>e\<^sub>r\<close> ..

      have 2: "U\<^sub>p\<^sub>r |\<union>| U\<^sub>e\<^sub>r |\<union>| resolvents_upto D C (Suc n) =
        U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n |\<union>| finsert DC U\<^sub>e\<^sub>r"
        by (auto simp: \<open>resolvent_at D C (Suc n) = DC\<close>)

      show ?thesis
        unfolding match_def 1 2
      proof (rule ord_res_2_matches_ord_res_3.intros)
        show "\<forall>C|\<in>|U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n.
          \<exists>D1|\<in>|N |\<union>| finsert DC U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| finsert DC U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
          (ground_resolution D1)\<^sup>+\<^sup>+ D2 C \<and> C \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| finsert DC U\<^sub>e\<^sub>r"
        proof (intro ballI)
          fix Ca
          assume "Ca |\<in>| U\<^sub>p\<^sub>r |\<union>| resolvents_upto D C n"
          hence "Ca |\<in>| U\<^sub>p\<^sub>r \<or> Ca |\<in>| resolvents_upto D C n"
            by simp
          thus "\<exists>D1|\<in>|N |\<union>| finsert DC U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f. \<exists>D2|\<in>|N |\<union>| finsert DC U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f.
            (ground_resolution D1)\<^sup>+\<^sup>+ D2 Ca \<and> Ca \<noteq> eres D1 D2 \<and> eres D1 D2 |\<in>| finsert DC U\<^sub>e\<^sub>r"
          proof (elim disjE)
            show "Ca |\<in>| U\<^sub>p\<^sub>r \<Longrightarrow> ?thesis"
              using U\<^sub>p\<^sub>r_spec by auto
          next
            assume "Ca |\<in>| resolvents_upto D C n"
            then obtain i where i_in: "i |\<in>| fset_upto (Suc 0) n" and Ca_def:"Ca = resolvent_at D C i"
              unfolding resolvents_upto_def by auto

            from i_in have "0 < i" "i \<le> n"
              by simp_all

            show "?thesis"
            proof (intro bexI conjI)
              have "(ground_resolution D ^^ i) C Ca"
                unfolding \<open>Ca = resolvent_at D C i\<close>
              proof (rule relpowp_to_resolvent_at)
                show "(ground_resolution D ^^ Suc n) C DC"
                  using \<open>(ground_resolution D ^^ Suc n) C DC\<close> .
              next
                show "i < Suc n"
                  using \<open>i \<le> n\<close> by presburger
              qed
              thus "(ground_resolution D)\<^sup>+\<^sup>+ C Ca"
                using \<open>0 < i\<close> by (simp add: tranclp_if_relpowp)
            next
              show "Ca \<noteq> eres D C"
                by (metis Ca_def \<open>(ground_resolution D ^^ Suc n) C DC\<close>
                  \<open>(ground_resolution D)\<^sup>*\<^sup>* C DC\<close> \<open>\<nexists>x. ground_resolution D DC x\<close> \<open>i \<le> n\<close>
                  eres_eq_after_rtranclp_ground_resolution
                  ground_resolution_resolvent_at_resolvent_at_Suc less_Suc_eq_le
                  resolvable_if_neq_eres)
            next
              show "eres D C |\<in>| finsert DC U\<^sub>e\<^sub>r"
                by (metis Uniq_full_run finsertCI local.resolution(8) Uniq_ground_resolution
                  eres_def the1_equality')
            next
              show "D |\<in>| N |\<union>| finsert DC U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using resolution by simp
            next
              have "C |\<in>| N |\<union>| U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                using resolution
                by (simp add: is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff)
              thus "C |\<in>| N |\<union>| finsert DC U\<^sub>e\<^sub>r |\<union>| U\<^sub>e\<^sub>f"
                by simp
            qed
          qed
        qed
      qed
    qed

    ultimately have "\<exists>S2'. (ord_res_2_step ^^ Suc n) S2 S2' \<and> match S2' S3'"
      by metis

    thus "\<exists>S2'. ord_res_2_step\<^sup>+\<^sup>+ S2 S2' \<and> match S2' S3'"
      by (metis Zero_neq_Suc tranclp_if_relpowp)
  qed
qed

lemma right_unique_ord_res_3: "right_unique (ord_res_3 N)"
proof (rule right_uniqueI)
  fix s s' s'' :: "'f gterm clause fset \<times> 'f gterm clause fset"
  assume step1: "ord_res_3 N s s'" and step2: "ord_res_3 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_3.cases)
    case hyps1: (factoring U\<^sub>r\<^sub>r1 U\<^sub>f\<^sub>f1 C1 L1 U\<^sub>f\<^sub>f1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_3.cases)
      case (factoring U\<^sub>r\<^sub>r2 U\<^sub>f\<^sub>f2 C2 L2 U\<^sub>f\<^sub>f2')
      with hyps1 show ?thesis
        by (metis Uniq_D Uniq_is_least_false_clause prod.inject)
    next
      case (resolution U\<^sub>r\<^sub>r2 U\<^sub>f\<^sub>f2 C2 L2 D2 DC2 U\<^sub>r\<^sub>r2')
      with hyps1 have False
        by (metis Pair_inject Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset
            the1_equality')
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution U\<^sub>r\<^sub>r1 U\<^sub>f\<^sub>f1 C1 L1 D1 DC1 U\<^sub>r\<^sub>r1')
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_3.cases)
      case (factoring U\<^sub>r\<^sub>r2 U\<^sub>f\<^sub>f2 C2 L2 U\<^sub>f\<^sub>f2')
      with hyps1 have False
        by (metis Uniq_is_least_false_clause linorder_lit.Uniq_is_maximal_in_mset prod.inject the1_equality')
      thus ?thesis ..
    next
      case hyps2: (resolution U\<^sub>r\<^sub>r2 U\<^sub>f\<^sub>f2 C2 L2 D2 DC2 U\<^sub>r\<^sub>r2')

      have *: "U\<^sub>r\<^sub>r1 = U\<^sub>r\<^sub>r2" "U\<^sub>f\<^sub>f1 = U\<^sub>f\<^sub>f2"
        using hyps1 hyps2 by  simp_all

      have **: "C1 = C2"
        using hyps1 hyps2
        unfolding *
        by (metis Uniq_is_least_false_clause the1_equality')

      have ***: "L1 = L2"
        using hyps1 hyps2
        unfolding * **
        by (metis linorder_lit.Uniq_is_maximal_in_mset the1_equality')

      have ****: "D1 = D2"
        using hyps1 hyps2
        unfolding * ** ***
        by (metis linorder_cls.less_irrefl linorder_cls.linorder_cases
            ord_res.less_trm_iff_less_cls_if_mem_production singletonI)

      have *****: "DC1 = DC2"
        using hyps1 hyps2
        unfolding * ** *** ****
        by (metis (no_types, opaque_lifting) Uniq_full_run Uniq_ground_resolution the1_equality')

      show ?thesis
        using hyps1 hyps2
        unfolding * ** *** **** *****
        by argo
    qed
  qed
qed

lemma right_unique_ord_res_3_step: "right_unique ord_res_3_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_3_step x y \<Longrightarrow> ord_res_3_step x z \<Longrightarrow> y = z"
    apply (cases x; cases y; cases z)
    apply (simp add: ord_res_3_step.simps)
    using right_unique_ord_res_3[THEN right_uniqueD]
    by blast
qed

lemma ex_ord_res_3_if_not_final:
  assumes "\<not> ord_res_3_final S"
  shows "\<exists>S'. ord_res_3_step S S'"
proof -
  from assms obtain N U\<^sub>r U\<^sub>e\<^sub>f where
    S_def: "S = (N, (U\<^sub>r, U\<^sub>e\<^sub>f))" and
    "{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
    "ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))"
    by (metis ord_res_3_final.intros ord_res_final_def surj_pair)

  obtain C where C_least_false: "is_least_false_clause (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f) C"
    using \<open>ex_false_clause (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f))\<close> obtains_least_false_clause_if_ex_false_clause
    by metis

  hence "C \<noteq> {#}"
    using \<open>{#} |\<notin>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  then obtain L where C_max: "linorder_lit.is_maximal_in_mset C L"
    using linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using ord_res_3.factoring[OF C_least_false C_max] S_def is_pos_def
      by (metis ord_res_3_step.intros)
  next
    case (Neg A)
    then obtain D where
      "D |\<in>| N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      "ord_res.production (fset (N |\<union>| U\<^sub>r |\<union>| U\<^sub>e\<^sub>f)) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
      using C_least_false C_max by metis

    moreover then obtain DC where
      "full_run (ground_resolution D) C DC"
      using ex_ground_resolutionI C_max Neg
      using ex1_eres_eq_full_run_ground_resolution by blast

    ultimately show ?thesis
      using ord_res_3.resolution[OF C_least_false C_max]
      by (metis Neg S_def literal.disc(2) literal.sel(2) ord_res_3_step.intros)
  qed
qed

corollary ord_res_3_step_safe: "ord_res_3_final S \<or> (\<exists>S'. ord_res_3_step S S')"
  using ex_ord_res_3_if_not_final by metis

lemma safe_states_if_ord_res_2_matches_ord_res_3:
  assumes match: "ord_res_2_matches_ord_res_3 S\<^sub>2 S\<^sub>3"
  shows
    "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    "safe_state ord_res_3_step ord_res_3_final S\<^sub>3"
proof -
  show "safe_state ord_res_2_step ord_res_2_final S\<^sub>2"
    using safe_state_if_all_states_safe ord_res_2_safe by metis

  show "safe_state ord_res_3_step ord_res_3_final S\<^sub>3"
    using safe_state_if_all_states_safe ord_res_3_step_safe by metis
qed

theorem bisimulation_ord_res_2_ord_res_3:
  defines "match \<equiv> \<lambda>_ S2 S3. ord_res_2_matches_ord_res_3 S2 S3"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow>
    'f gterm clause fset \<times> 'f gterm clause fset \<times> 'f gterm clause fset \<Rightarrow> bool) ORDER.
    bisimulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final ORDER MATCH"
proof (rule ex_bisimulation_from_backward_simulation)
  show "right_unique ord_res_2_step"
    using right_unique_ord_res_2_step .
next
  show "right_unique ord_res_3_step"
    using right_unique_ord_res_3_step .
next
  show "\<forall>s1. ord_res_2_final s1 \<longrightarrow> (\<nexists>s1'. ord_res_2_step s1 s1')"
    by (metis finished_def ord_res_2_semantics.final_finished)
next
  show "\<forall>s2. ord_res_3_final s2 \<longrightarrow> (\<nexists>s2'. ord_res_3_step s2 s2')"
    by (metis finished_def ord_res_3_semantics.final_finished)
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> ord_res_2_final s1 = ord_res_3_final s2"
    unfolding match_def
    using ord_res_2_final_iff_ord_res_3_final by metis
next
  show "\<forall>i s1 s2. match i s1 s2 \<longrightarrow>
    safe_state ord_res_2_step ord_res_2_final s1 \<and> safe_state ord_res_3_step ord_res_3_final s2"
    unfolding match_def
    using safe_states_if_ord_res_2_matches_ord_res_3 by metis
next
  show "wfP (\<lambda>_ _. False)"
    by simp
next
  show "\<forall>i s1 s2 s2'.
       match i s1 s2 \<longrightarrow>
       ord_res_3_step s2 s2' \<longrightarrow>
       (\<exists>i' s1'. ord_res_2_step\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> False)"
    unfolding match_def
    using backward_simulation_2_to_3 by metis
qed

corollary backward_simulation_ord_res_1_ord_res_3:
  shows "\<exists>MATCH (ORDER :: (nat \<times> nat) \<times> (nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<times> (nat \<times> nat) \<Rightarrow> bool).
    backward_simulation ord_res_1 ord_res_3_step ord_res_1_final ord_res_3_final ORDER MATCH"
proof -
  obtain
    MATCH12 :: "nat \<times> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" and
    ORDER12 :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
    "bisimulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final ORDER12 MATCH12"
    using bisimulation_ord_res_1_ord_res_2 by metis
  hence bsim12: "backward_simulation ord_res_1 ord_res_2_step ord_res_1_final ord_res_2_final ORDER12 MATCH12"
    by (simp add: bisimulation_def)

  obtain
    MATCH23 :: "nat \<times> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" and
    ORDER23 :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
    "bisimulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final ORDER23 MATCH23"
    using bisimulation_ord_res_2_ord_res_3 by metis
  hence bsim23: "backward_simulation ord_res_2_step ord_res_3_step ord_res_2_final ord_res_3_final ORDER23 MATCH23"
    by (simp add: bisimulation_def)

  show ?thesis
    using backward_simulation_composition[OF bsim12 bsim23] by metis
qed


subsection \<open>ORD-RES-4 (full resolve)\<close>


subsection \<open>ORD-RES-5 (explicit model construction)\<close>


subsection \<open>ORD-RES-6 (model backjump)\<close>


subsection \<open>SCL(FOL)-1 (resolution-driven strategy)\<close>

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
  sorted_wrt (\<prec>\<^sub>t) As \<Longrightarrow>
  fset_of_list As = {|A |\<in>| atms_of_clss N\<^sub>0. A \<prec>\<^sub>t atm_of L \<and>
    \<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm A))|} \<Longrightarrow>
  \<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) As) \<Longrightarrow>
  S1 = ((\<Gamma>\<^sub>1, U, None :: ('f, 'v) closure option), i, D, \<F>) \<Longrightarrow>
  (ord_res_1 ^^ i) N\<^sub>0 N\<^sub>i \<Longrightarrow>
  \<F> D |\<in>| N\<^sub>i \<Longrightarrow>
  sfac D = sfac (\<F> D) \<Longrightarrow>
  S2 =
    (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
      trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
      (let
        \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
        \<F>' = \<F>(D := sfac D);
        j = i + count (\<F> D - {#L#}) L
      in
        if (\<exists>S'. scl_fol.conflict (cls_of_gcls |`| N\<^sub>0) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) S') then
          \<comment> \<open>2b\<close>
          (let
            \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
            E = (THE E. is_least_in_fset_wrt (\<prec>\<^sub>c)
              {|C |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} E)
          in
            ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>'))
        else
          \<comment> \<open>2a\<close>
          ((\<Gamma>\<^sub>2\<^sub>a, U, None :: ('f, 'v) closure option), j, D, \<F>'))
    else
      \<comment> \<open>2c\<close>
      S1) \<Longrightarrow>
  scl_reso1 N\<^sub>0 \<beta> ((\<Gamma>, U, None :: ('f, 'v) closure option), i, C, \<F>) S1 S2"

inductive scl_fol_1_step where
  "scl_reso1 N \<beta> S S' S'' \<Longrightarrow> scl_fol_1_step (N, \<beta>, S) (N, \<beta>, S'')"

fun scl_fol_1_final :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) scl_fol_sim_state \<Rightarrow> bool" where
  "scl_fol_1_final (N, \<beta>, (\<Gamma>, U, \<C>), ann) \<longleftrightarrow>
    (\<exists>\<gamma>. \<C> = Some ({#}, \<gamma>)) \<or> (\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C))"

interpretation scl_reso_semantics: semantics where
  step = scl_fol_1_step and
  final = scl_fol_1_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) scl_fol_sim_state"

  obtain N \<beta> \<Gamma> U \<C> ann where
    S_def: "S = (N, \<beta>, (\<Gamma>, U, \<C>), ann)"
    by (metis prod.exhaust)

  assume "scl_fol_1_final S"
  hence "(\<exists>\<gamma>. \<C> = Some ({#}, \<gamma>)) \<or> (\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C))"
    unfolding S_def by simp
  thus "finished scl_fol_1_step S"
  proof (elim disjE exE)
    show "\<And>\<gamma>. \<C> = Some ({#}, \<gamma>) \<Longrightarrow> finished scl_fol_1_step S"
      sorry
  next
    assume "\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C)"
    hence "\<forall>C |\<in>| cls_of_gcls |`| N. trail_true_cls \<Gamma> C"
      by simp
    hence "\<forall>C |\<in>| cls_of_gcls |`| N |\<union>| U. trail_true_cls \<Gamma> C"
      sorry
    hence "\<nexists>s' s''. scl_reso1 N \<beta> ((\<Gamma>, U, \<C>), ann) s' s''"
      sorry
    hence "\<nexists>S'. scl_fol_1_step S S'"
      by (simp add: S_def scl_fol_1_step.simps)
    then show "finished scl_fol_1_step S"
      by (simp add: finished_def)
  qed
qed


lemma scl_reso1_step2_cases[case_names case2a case2b case2c]:
  fixes \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2\<^sub>a As L
  defines
    "\<Gamma>\<^sub>1 \<equiv> foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) As)" and
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
  case hyps: (scl_reso1I U D L As \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  note \<Gamma>\<^sub>1_def = \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) As)\<close>
  note state2_eq = hyps(11)

  have "state_learned S\<^sub>0 = U"
    using \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close> by simp

  moreover have "state_learned S\<^sub>1 = U" and "i\<^sub>1 = i\<^sub>0" and "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp_all

  moreover have "state_learned S\<^sub>2 = U \<and> i\<^sub>0 \<le> i\<^sub>2 \<and> C\<^sub>2 = D"
  proof (cases rule: scl_reso1_step2_cases[of L \<Gamma> As D N \<beta> U])
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
    "\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := sfac C\<^sub>1))"
  unfolding atomize_conj
  using assms
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L As \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  note \<Gamma>\<^sub>1_def = \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) As)\<close>
  note state2_eq = hyps(11)

  have "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp

  have "\<F>\<^sub>1 = \<F>\<^sub>0"
    using hyps(7) by simp
  thus "\<F>\<^sub>1 = \<F>\<^sub>0 \<and>
    (\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := sfac C\<^sub>1)))"
  proof (intro conjI)
    show "\<F>\<^sub>2 = \<F>\<^sub>1 \<or>
      (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := sfac C\<^sub>1))"
    proof (cases rule: scl_reso1_step2_cases[of L \<Gamma> As D N \<beta> U])
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
  case hyps: (scl_reso1I U D L As \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)

  from hyps have D_least: "is_least_in_fset_wrt (less_cls_sfac \<F>\<^sub>0)
    (ffilter (less_cls_sfac \<F>\<^sub>0 C\<^sub>0) (N |\<union>| gcls_of_cls |`| U)) D"
    by argo

  from hyps have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
  proof (induction As arbitrary: S\<^sub>0 \<Gamma>)
    case Nil
    hence "S\<^sub>1 = S\<^sub>0"
      by simp
    thus ?case
      by simp
  next
    case (Cons A As)
    note set_A_As_eq = \<open>fset_of_list (A # As) = {|A |\<in>| atms_of_clss N.
      A \<prec>\<^sub>t atm_of L \<and> \<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm A))|}\<close>

    from set_A_As_eq have
      "A \<prec>\<^sub>t atm_of L" "\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm A))" "A |\<in>| atms_of_clss N"
      by auto

    from Cons.prems have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* (trail_decide \<Gamma> (Neg (term_of_gterm A)), U, None) S\<^sub>1"
    proof (intro Cons.IH[OF refl] ballI)
      show "sorted_wrt (\<prec>\<^sub>t) As"
        using \<open>sorted_wrt (\<prec>\<^sub>t) (A # As)\<close> by simp
    next
      show "fset_of_list As = {|B |\<in>| atms_of_clss N. B \<prec>\<^sub>t atm_of L \<and>
        \<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (Neg (term_of_gterm B))|}"
      proof (intro fsubset_antisym fsubsetI)
        fix B
        assume B_in: "B |\<in>| fset_of_list As"
        hence "A \<prec>\<^sub>t B"
          using \<open>sorted_wrt (\<prec>\<^sub>t) (A # As)\<close>
          by (simp add: fset_of_list_elem)
        hence "A \<noteq> B"
          by order

        have "B |\<in>| atms_of_clss N" and "B \<prec>\<^sub>t atm_of L" and
          B_undef: "\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm B))"
          using B_in set_A_As_eq by auto

        moreover have "\<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A)))
         (Neg (term_of_gterm B))"
          using \<open>A \<noteq> B\<close> B_undef
          apply (simp add: trail_defined_lit_def decide_lit_def)
          by (metis term_of_gterm_inv)

        ultimately show "B |\<in>| {|B |\<in>| atms_of_clss N. B \<prec>\<^sub>t atm_of L \<and>
          \<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (Neg (term_of_gterm B))|}"
          by simp
      next
        fix B
        assume "B |\<in>| {|B |\<in>| atms_of_clss N. B \<prec>\<^sub>t atm_of L \<and>
          \<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (Neg (term_of_gterm B))|}"
        hence "B |\<in>| atms_of_clss N" and "B \<prec>\<^sub>t atm_of L" and
          "\<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (Neg (term_of_gterm B))"
          by simp_all
        moreover hence "A \<noteq> B" and "\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm B))"
          by (auto simp add: trail_defined_lit_def decide_lit_def)

        ultimately show "B |\<in>| fset_of_list As"
          using set_A_As_eq by auto
      qed
    next
      show "\<Gamma>\<^sub>1 = foldl trail_decide (trail_decide \<Gamma> (Neg (term_of_gterm A))) (map (Neg \<circ> term_of_gterm) As)"
        using \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) (A # As))\<close> by simp
    next
      assume hyp: "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and> trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
          let \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
              \<F>' = \<F>\<^sub>0(D := sfac D);
              j = i\<^sub>0 + count (remove1_mset L (\<F>\<^sub>0 D)) L
          in
            if \<exists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              let
                \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
                E = THE a. linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} a
              in
                ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
        else
          (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
      show "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (if is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (lit_of_glit L) \<and> trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
          let
            \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
            \<F>' = \<F>\<^sub>0(D := sfac D);
            j = i\<^sub>0 + count (remove1_mset L (\<F>\<^sub>0 D)) L
          in
            if \<exists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              let
                \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
                E = THE a. linorder_cls.is_least_in_fset {|C |\<in>| N |\<union>| gcls_of_cls |`| U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} a
              in
                ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
        else
          (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
        unfolding hyp
        unfolding Let_def
      proof (intro if_weak_cong iffI)
        assume "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
        thus "is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
          by (metis \<open>A \<prec>\<^sub>t atm_of L\<close> atm_of_lit_of_glit_conv linorder_trm.neq_iff literal.sel(2)
              term_of_gterm_inv trail_undefined_lit_and_atm_neq_iff)
      next
        assume "is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A))) (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
        thus "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
          trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
          using trail_undefined_if_trail_undefined_trail_decide
          by metis
      qed
    qed

    moreover have "scl_fol.decide N' \<beta>' (\<Gamma>, U, None) ((trail_decide \<Gamma> (Neg (term_of_gterm A))), U, None)"
    proof (intro scl_fol.decideI[of _ Var, simplified])
      show "is_ground_lit (Neg (term_of_gterm A))"
        by (simp add: is_ground_lit_def atm_of_lit_of_glit_conv)
    next
      show "\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm A))"
        using \<open>\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm A))\<close> .
    next
      show "less_B (atm_of (Neg (term_of_gterm A))) \<beta>' \<or> atm_of (Neg (term_of_gterm A)) = \<beta>'"
        unfolding less_B_def
        using \<open>A |\<in>| atms_of_clss N\<close> \<beta>_greatereq \<beta>'_def
        by (auto simp add: atm_of_lit_of_glit_conv)
    qed

    ultimately show ?case
      unfolding \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close> \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp
  qed

  from hyps have S\<^sub>1_def: "S\<^sub>1 = (\<Gamma>\<^sub>1, U, None)"
    by simp

  have "distinct As"
    using \<open>sorted_wrt (\<prec>\<^sub>t) As\<close> linorder_trm.strict_sorted_iff by metis

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
      let ?\<F>' = "\<F>\<^sub>0(D := sfac D)"
      let ?j = "i\<^sub>0 + count (\<F>\<^sub>0 D - {#L#}) L"

      obtain D' :: "('f, 'v) term clause" where
        "cls_of_gcls D = add_mset (lit_of_glit L) D'"
        by (metis cls_of_gcls_def hyps(3) image_mset_add_mset insert_DiffM
            linorder_lit.is_maximal_in_mset_iff)

      have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
        using pos_L_and_undef_L_and_false_D by argo
      have "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)"
        unfolding \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) As)\<close>
        using hyps(4,5) pos_L_and_undef_L_and_false_D \<open>distinct As\<close>
      proof (induction As arbitrary: \<Gamma>)
        case Nil
        thus ?case
          by simp
      next
        case (Cons A As)
        show ?case
          unfolding list.map foldl_Cons
        proof (intro Cons.IH ballI conjI)
          show "sorted_wrt (\<prec>\<^sub>t) As"
            using Cons.prems by simp
        next
          show "is_pos L"
            "\<not> trail_defined_lit (trail_decide \<Gamma> ((Neg \<circ> term_of_gterm) A)) (lit_of_glit L)"
            "trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
            unfolding atomize_conj
            using Cons.prems
            by (metis (no_types, lifting) atm_of_lit_of_glit_conv comp_apply ffmember_filter
                fset_of_list.rep_eq linorder_trm.dual_order.strict_implies_not_eq list.set_intros(1)
                literal.sel(2) term_of_gterm_inv trail_undefined_lit_and_atm_neq_iff)
        next
          show "distinct As"
            using Cons.prems by simp
        next
          show "fset_of_list As = {|B |\<in>| atms_of_clss N. B \<prec>\<^sub>t atm_of L \<and>
            \<not> trail_defined_lit (trail_decide \<Gamma> ((Neg \<circ> term_of_gterm) A)) (Neg (term_of_gterm B))|}"
          proof (intro fsubset_antisym fsubsetI)
            fix B
            assume B_in: "B |\<in>| fset_of_list As"
            hence "A \<prec>\<^sub>t B"
              using \<open>sorted_wrt (\<prec>\<^sub>t) (A # As)\<close>
              by (simp add: fset_of_list_elem)
            hence "A \<noteq> B"
              by order

            have "B |\<in>| atms_of_clss N" and "B \<prec>\<^sub>t atm_of L" and
              B_undef: "\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm B))"
              using B_in Cons.prems by auto

            moreover have "\<not> trail_defined_lit (trail_decide \<Gamma> (Neg (term_of_gterm A)))
              (Neg (term_of_gterm B))"
              using \<open>A \<noteq> B\<close> B_undef
              apply (simp add: trail_defined_lit_def decide_lit_def)
              by (metis term_of_gterm_inv)

            ultimately show "B |\<in>| {|B |\<in>| atms_of_clss N. B \<prec>\<^sub>t atm_of L \<and>
              \<not> trail_defined_lit (trail_decide \<Gamma> ((Neg \<circ> term_of_gterm) A)) (Neg (term_of_gterm B))|}"
              by simp
          next
            fix B
            assume "B |\<in>| {|B |\<in>| atms_of_clss N. B \<prec>\<^sub>t atm_of L \<and>
              \<not> trail_defined_lit (trail_decide \<Gamma> ((Neg \<circ> term_of_gterm) A)) (Neg (term_of_gterm B))|}"
            hence "B |\<in>| atms_of_clss N" and "B \<prec>\<^sub>t atm_of L" and
              "\<not> trail_defined_lit (trail_decide \<Gamma> ((Neg \<circ> term_of_gterm) A)) (Neg (term_of_gterm B))"
              by simp_all
            moreover hence "A \<noteq> B" and "\<not> trail_defined_lit \<Gamma> (Neg (term_of_gterm B))"
              by (auto simp add: trail_defined_lit_def decide_lit_def)

            ultimately show "B |\<in>| fset_of_list As"
              using Cons.prems by auto
          qed
        qed
      qed

      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (?\<Gamma>\<^sub>2\<^sub>a, U, None))")
        case ex_conflict: True
        have "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = ((?\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls ?E, Var)), ?j, D, ?\<F>')"
          using hyps(11)
          unfolding Let_def
          unfolding if_P[OF pos_L_and_undef_L_and_false_D]
          unfolding if_P[OF ex_conflict]
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

subsection \<open>Backward simulation between ORD-RES-1 and SCL(FOL)-1\<close>

lemma atms_of_eq_fset_atms_of_cls: "atms_of C = fset (atms_of_cls C)"
  by (simp add: atms_of_cls_def atms_of_def)

lemma ord_res_1_preserves_atms_of_clss:
  assumes step: "ord_res_1 N N'"
  shows "atms_of_clss N = atms_of_clss N'"
  using step
proof (cases N N' rule: ord_res_1.cases)
  case (factoring C L C')

  moreover have "C |\<in>| N"
    using \<open>is_least_false_clause N C\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by simp

  moreover have "atms_of_cls C' = atms_of_cls C"
    using ord_res.atms_of_concl_eq_if_ground_factoring[OF \<open>ord_res.ground_factoring C C'\<close>]
    by (simp add: atms_of_eq_fset_atms_of_cls fset_cong)

  ultimately show ?thesis
    by (simp add: atms_of_clss_def)
next
  case (resolution C L D CD)

  have "atms_of_clss N' = atms_of_clss (finsert CD N)"
    unfolding \<open>N' = finsert CD N\<close> ..
  also have "\<dots> = atms_of_cls CD |\<union>| atms_of_clss N"
    by (simp add: atms_of_clss_def)
  also have "\<dots> |\<subseteq>| atms_of_cls C |\<union>| atms_of_cls D |\<union>| atms_of_clss N"
    using \<open>ord_res.ground_resolution C D CD\<close> ord_res.atms_of_concl_subset_if_ground_resolution
    by (metis atms_of_eq_fset_atms_of_cls fsubsetI less_eq_fset.rep_eq sup_mono union_fset)
  also have "\<dots> = atms_of_clss N"
    using \<open>is_least_false_clause N C\<close> \<open>D |\<in>| N\<close>
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by (auto simp: atms_of_clss_def fmember_ffUnion_iff)
  finally show "atms_of_clss N = atms_of_clss N'"
    unfolding \<open>N' = finsert CD N\<close>
    using \<open>atms_of_clss (finsert CD N) = atms_of_cls CD |\<union>| atms_of_clss N\<close> by blast
qed

lemma compower_ord_res_1_preserves_atms_of_clss:
  "(ord_res_1 ^^ i) N N\<^sub>i \<Longrightarrow> atms_of_clss N = atms_of_clss N\<^sub>i"
proof (induction i arbitrary: N\<^sub>i)
  case 0
  then show ?case
    by simp
next
  case (Suc i')
  from Suc.prems obtain N\<^sub>i\<^sub>' where
    "(ord_res_1 ^^ i') N N\<^sub>i\<^sub>'" and "ord_res_1 N\<^sub>i\<^sub>' N\<^sub>i"
    by auto

  have "atms_of_clss N = atms_of_clss N\<^sub>i\<^sub>'"
    using Suc.IH[OF \<open>(ord_res_1 ^^ i') N N\<^sub>i\<^sub>'\<close>] .
  also have "\<dots> = atms_of_clss N\<^sub>i"
    using ord_res_1_preserves_atms_of_clss[OF \<open>ord_res_1 N\<^sub>i\<^sub>' N\<^sub>i\<close>] .
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

lemma fsubset_if_ord_res_1:
  assumes "ord_res_1 N N'"
  shows "N |\<subseteq>| N'"
  using assms by (auto elim: ord_res_1.cases)

lemma fsubset_if_relpow_le_relpow:
  fixes i j :: nat
  assumes "i \<le> j" and
    N_to_N\<^sub>i: "(ord_res_1 ^^ i) N N\<^sub>i" and
    N_to_N\<^sub>j: "(ord_res_1 ^^ j) N N\<^sub>j"
  shows "N\<^sub>i |\<subseteq>| N\<^sub>j"
proof -
  from \<open>i \<le> j\<close> obtain k where "j = i + k"
    using le_Suc_ex by metis
  hence "(ord_res_1 ^^ (i + k)) N N\<^sub>j"
    using N_to_N\<^sub>j by argo
  hence "(ord_res_1 ^^ i OO ord_res_1 ^^ k) N N\<^sub>j"
    by (metis relpowp_add)
  hence "(ord_res_1 ^^ k) N\<^sub>i N\<^sub>j"
    using right_unique_ord_res_1 N_to_N\<^sub>i
    by (metis Uniq_relpowp relcomppE right_unique_iff)
  thus "N\<^sub>i |\<subseteq>| N\<^sub>j"
    using fsubset_if_ord_res_1
    by (metis mono_rtranclp relpowp_imp_rtranclp rtranclp_less_eq)
qed

lemma sfac_initial_and_learned_clauses_subset:
  assumes
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    N_to_N\<^sub>i\<^sub>0: "(ord_res_1 ^^ i\<^sub>0) N N\<^sub>i\<^sub>0" and
    N_to_N\<^sub>i\<^sub>1: "(ord_res_1 ^^ i\<^sub>1) N N\<^sub>i\<^sub>1" and
    N_to_N\<^sub>i\<^sub>2: "(ord_res_1 ^^ i\<^sub>2) N N\<^sub>i\<^sub>2" and
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
    using right_unique_ord_res_1 N_to_N\<^sub>i\<^sub>0 N_to_N\<^sub>i\<^sub>1
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
    invar: "\<forall>C. \<F>\<^sub>0 C = C \<or> \<F>\<^sub>0 C = sfac C"
  shows
    "\<forall>C. \<F>\<^sub>1 C = C \<or> \<F>\<^sub>1 C = sfac C"
    "\<forall>C. \<F>\<^sub>2 C = C \<or> \<F>\<^sub>2 C = sfac C"
  unfolding atomize_conj
  using step
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L As \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  show "(\<forall>C. \<F>\<^sub>1 C = C \<or> \<F>\<^sub>1 C = sfac C) \<and> (\<forall>C. \<F>\<^sub>2 C = C \<or> \<F>\<^sub>2 C = sfac C)"
  proof (cases rule: scl_reso1_step2_cases[of L \<Gamma> As D N \<beta> U])
    case case2a
    thus ?thesis
      using hyps invar by simp
  next
    case case2b
    thus ?thesis
      using hyps invar by (simp add: Let_def)
  next
    case case2c
    thus ?thesis
      using hyps invar by auto
  qed
qed

(* lemma
  assumes "finite N"
  shows "ord_res.interp N = ord_res.interp (sfac ` N)"
proof (intro ext Set.subset_antisym Set.subsetI)
  fix C A
  assume "A \<in> ord_res.interp N C"
  then show "A \<in> ord_res.interp (sfac ` N) C"
    find_theorems  *)

lemma
  assumes
    step: "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    N_to_N\<^sub>i\<^sub>0: "(ord_res_1 ^^ i\<^sub>0) N N\<^sub>i\<^sub>0" and
    N_to_N\<^sub>i\<^sub>1: "(ord_res_1 ^^ i\<^sub>1) N N\<^sub>i\<^sub>1" and
    N_to_N\<^sub>i\<^sub>2: "(ord_res_1 ^^ i\<^sub>2) N N\<^sub>i\<^sub>2" and
    invars:
      "\<forall>C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>0. \<F>\<^sub>0 C |\<in>| N\<^sub>i\<^sub>0"
      "\<forall>C. \<F>\<^sub>0 C = C \<or> \<F>\<^sub>0 C = sfac C"
  shows
    "\<forall>C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1. \<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1"
    "\<forall>C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2. \<F>\<^sub>2 C |\<in>| N\<^sub>i\<^sub>2"
  unfolding atomize_conj
  using step
proof (cases N \<beta> "(S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" "(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1)" "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" rule: scl_reso1.cases)
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i)
  have "N\<^sub>i\<^sub>0 = N\<^sub>i"
    by (metis N_to_N\<^sub>i\<^sub>0 Uniq_relpowp hyps(8) right_unique_iff right_unique_ord_res_1)

  have "state_learned S\<^sub>1 = state_learned S\<^sub>0" and "i\<^sub>1 = i\<^sub>0" and "C\<^sub>2 = C\<^sub>1" and "\<F>\<^sub>1 = \<F>\<^sub>0"
    using scl_reso1_simple_destroy[OF step] scl_reso1_\<F>_eq[OF step] by simp_all

  have "N\<^sub>i\<^sub>1 = N\<^sub>i\<^sub>0"
    using N_to_N\<^sub>i\<^sub>0 N_to_N\<^sub>i\<^sub>1 \<open>i\<^sub>1 = i\<^sub>0\<close>
    by (metis Uniq_relpowp right_unique_iff right_unique_ord_res_1)

  have "state_learned S\<^sub>2 = state_learned S\<^sub>1" and
    \<F>\<^sub>2_eq_disj: "\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := sfac C\<^sub>1))"
    using scl_reso1_simple_destroy[OF step] scl_reso1_\<F>_eq[OF step] by simp_all

  from step have "i\<^sub>1 \<le> i\<^sub>2"
    using scl_reso1_simple_destroy[OF step] by metis
  with N_to_N\<^sub>i\<^sub>1 N_to_N\<^sub>i\<^sub>2 have "N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2"
    by (metis fsubset_if_relpow_le_relpow)

  let ?\<Gamma>\<^sub>2\<^sub>a = "trail_decide \<Gamma>\<^sub>1 (lit_of_glit L)"
  let ?\<F>' = "\<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})"
  let ?j = "count (\<F>\<^sub>0 D - {#L#}) L"

  thm ord_res.production_unfold

  define D\<^sub>0 where
    "D\<^sub>0 = {#K \<in># D. K \<noteq> L#}"

  have "\<forall>K \<in># D. K \<preceq>\<^sub>l L"
    using \<open>ord_res.is_maximal_lit L D\<close>
    unfolding linorder_lit.is_maximal_in_mset_iff by fastforce
  hence "\<forall>K \<in># D\<^sub>0. K \<prec>\<^sub>l L"
    unfolding D\<^sub>0_def by auto

  obtain j\<^sub>0 where
    "\<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc j\<^sub>0) L"
    using invars(2)[rule_format, of D]
  proof -
    assume a1: "\<And>j\<^sub>0. \<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc j\<^sub>0) L \<Longrightarrow> thesis"
    have f2: "add_mset L (remove1_mset L D) = D"
      by (metis (no_types) hyps(3) insert_DiffM linorder_lit.is_maximal_in_mset_iff)
    obtain gg :: "'f gterm literal multiset \<Rightarrow> 'f gterm" where
      f3: "sfac D = D \<or> ord_res.is_maximal_lit (Pos (gg D)) D \<and> sfac D = add_mset (Pos (gg D)) {#l \<in># D. l \<noteq> Pos (gg D)#}"
      using sfac_spec by moura
    { assume "replicate_mset (Suc (count (remove1_mset L D) (Pos (gg D)))) (Pos (gg D)) = add_mset (Pos (gg D)) (replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))) \<and> \<F>\<^sub>0 D \<noteq> D\<^sub>0 + replicate_mset (Suc 0) L"
      { assume "replicate_mset (Suc (count (remove1_mset L D) (Pos (gg D)))) (Pos (gg D)) = add_mset (Pos (gg D)) (replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))) \<and> \<F>\<^sub>0 D \<noteq> {#l \<in># D. l \<noteq> L#} + {#Pos (gg D)#}"
        moreover
        { assume "replicate_mset (Suc (count (remove1_mset L D) (Pos (gg D)))) (Pos (gg D)) = add_mset (Pos (gg D)) (replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))) \<and> \<F>\<^sub>0 D \<noteq> add_mset L {#l \<in># D. l \<noteq> L#}"
          moreover
          { assume "replicate_mset (Suc (count (remove1_mset L D) (Pos (gg D)))) (Pos (gg D)) = add_mset (Pos (gg D)) (replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))) \<and> \<F>\<^sub>0 D \<noteq> add_mset (Pos (gg D)) ({#l \<in># D. l \<noteq> L#} + replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))) - replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))"
            { assume "\<F>\<^sub>0 D \<noteq> add_mset (Pos (gg D)) {#l \<in># D. l \<noteq> Pos (gg D)#}"
              then have "(\<not> ord_res.is_maximal_lit (Pos (gg D)) D \<or> sfac D \<noteq> add_mset (Pos (gg D)) {#l \<in># D. l \<noteq> Pos (gg D)#}) \<or> filter_mset ((=) L) D = replicate_mset (count D L) L \<and> \<F>\<^sub>0 D = D"
                by (metis (no_types) \<open>\<F>\<^sub>0 D = D \<or> \<F>\<^sub>0 D = sfac D\<close> filter_mset_eq) }
            then have "L = Pos (gg D) \<and> add_mset L {#l \<in># D. l \<noteq> L#} + replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D)) = add_mset (Pos (gg D)) ({#l \<in># D. l \<noteq> L#} + replicate_mset (count (remove1_mset L D) (Pos (gg D))) (Pos (gg D))) \<and> add_mset (Pos (gg D)) ({#l \<in># D. l \<noteq> L#} + {#}) = add_mset L {#l \<in># D. l \<noteq> L#} \<and> D\<^sub>0 + replicate_mset (Suc 0) L = {#l \<in># D. l \<noteq> L#} + {#Pos (gg D)#} \<longrightarrow> (\<exists>n. \<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc n) L) \<or> filter_mset ((=) L) D = replicate_mset (count D L) L \<and> \<F>\<^sub>0 D = D \<or> \<not> ord_res.is_maximal_lit (Pos (gg D)) D \<or> sfac D \<noteq> add_mset (Pos (gg D)) {#l \<in># D. l \<noteq> Pos (gg D)#}"
              by (metis (no_types) union_mset_add_mset_right) }
          ultimately have "L = Pos (gg D) \<and> add_mset (Pos (gg D)) ({#l \<in># D. l \<noteq> L#} + {#}) = add_mset L {#l \<in># D. l \<noteq> L#} \<and> D\<^sub>0 + replicate_mset (Suc 0) L = {#l \<in># D. l \<noteq> L#} + {#Pos (gg D)#} \<longrightarrow> (\<exists>n. \<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc n) L) \<or> filter_mset ((=) L) D = replicate_mset (count D L) L \<and> \<F>\<^sub>0 D = D \<or> \<not> ord_res.is_maximal_lit (Pos (gg D)) D \<or> sfac D \<noteq> add_mset (Pos (gg D)) {#l \<in># D. l \<noteq> Pos (gg D)#}"
            by (smt (z3) add_diff_cancel_right' union_mset_add_mset_left) }
        ultimately have "L = Pos (gg D) \<and> D\<^sub>0 + replicate_mset (Suc 0) L = {#l \<in># D. l \<noteq> L#} + {#Pos (gg D)#} \<longrightarrow> (\<exists>n. \<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc n) L) \<or> filter_mset ((=) L) D = replicate_mset (count D L) L \<and> \<F>\<^sub>0 D = D \<or> \<not> ord_res.is_maximal_lit (Pos (gg D)) D \<or> sfac D \<noteq> add_mset (Pos (gg D)) {#l \<in># D. l \<noteq> Pos (gg D)#}"
          by (metis (no_types) add.right_neutral union_mset_add_mset_right) }
      then have "\<exists>n. \<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc n) L"
        using f3 f2 by (smt (z3) D\<^sub>0_def Uniq_D \<open>\<F>\<^sub>0 D = D \<or> \<F>\<^sub>0 D = sfac D\<close> count_add_mset filter_mset_eq hyps(3) linorder_lit.Uniq_is_maximal_in_mset replicate_mset_0 replicate_mset_Suc union_filter_mset_complement) }
    then show ?thesis
      using a1 by (meson replicate_mset_Suc)
  qed

  define D\<^sub>m where
    "D\<^sub>m \<equiv> \<lambda>m :: nat. D\<^sub>0 + replicate_mset (Suc j\<^sub>0 - m) L"

  have "D\<^sub>m 0 = \<F>\<^sub>0 D"
    by (simp add: D\<^sub>m_def \<open>\<F>\<^sub>0 D = D\<^sub>0 + replicate_mset (Suc j\<^sub>0) L\<close>)

  have "D\<^sub>m j\<^sub>0 = add_mset L D\<^sub>0"
    by (simp add: D\<^sub>m_def)

  have "\<forall>m \<le> j\<^sub>0. D\<^sub>m (Suc m) \<subset># D\<^sub>m m"
    by (auto simp: D\<^sub>m_def)
  hence a: "\<forall>m \<le> j\<^sub>0. D\<^sub>m (Suc m) \<prec>\<^sub>c D\<^sub>m m"
    using strict_subset_implies_multp by metis

  have "less_cls_sfac \<F>\<^sub>0 C\<^sub>0 D"
    using hyps(2) linorder_cls_sfac.is_least_in_fset_ffilterD(2) by blast
  hence "\<F>\<^sub>0 C\<^sub>0 \<preceq>\<^sub>c \<F>\<^sub>0 D"
    unfolding less_cls_sfac_def by auto

  moreover have "\<F>\<^sub>0 C\<^sub>0 \<noteq> \<F>\<^sub>0 D"
    \<comment> \<open>Should this be an assumption?\<close>
    sorry

  ultimately have "\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 D"
    by order

  have "\<forall>m < j\<^sub>0. linorder_lit.is_maximal_in_mset (D\<^sub>m m) L \<and> count (D\<^sub>m m) L > 1"
    unfolding linorder_lit.is_maximal_in_mset_iff
    using \<open>\<forall>K \<in># D\<^sub>0. K \<prec>\<^sub>l L\<close> by (auto simp: D\<^sub>m_def D\<^sub>0_def)
  hence "\<forall>m < j\<^sub>0. \<nexists>L. linorder_lit.is_greatest_in_mset (D\<^sub>m m) L"
    unfolding linorder_lit.is_greatest_in_mset_iff_is_maximal_and_count_eq_one
    by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset nat_less_le)
  hence b: "\<forall>m < j\<^sub>0. ord_res.production N (D\<^sub>m m) = {}" for N
    by (simp add: unproductive_if_nex_strictly_maximal_pos_lit)

  have "\<forall>m < j\<^sub>0. \<forall>N\<^sub>m. (ord_res_1 ^^ m) N\<^sub>i\<^sub>0 N\<^sub>m \<longrightarrow> ord_res.interp (fset N\<^sub>m) (D\<^sub>m m) =
    ord_res.interp (fset N\<^sub>i\<^sub>0) (\<F>\<^sub>0 C\<^sub>0) \<union> ord_res.production (fset N\<^sub>i\<^sub>0) (\<F>\<^sub>0 C\<^sub>0)"
  proof (intro allI impI)
    fix m N\<^sub>m
    assume "m < j\<^sub>0" and N_to_N\<^sub>m: "(ord_res_1 ^^ m) N\<^sub>i\<^sub>0 N\<^sub>m"
    thus "ord_res.interp (fset N\<^sub>m) (D\<^sub>m m) =
      ord_res.interp (fset N\<^sub>i\<^sub>0) (\<F>\<^sub>0 C\<^sub>0) \<union> ord_res.production (fset N\<^sub>i\<^sub>0) (\<F>\<^sub>0 C\<^sub>0)"
    proof (induction m arbitrary: N\<^sub>m)
      case 0
      then show ?case
        unfolding \<open>D\<^sub>m 0 = \<F>\<^sub>0 D\<close>
        apply simp
        using \<open>\<F>\<^sub>0 C\<^sub>0 \<preceq>\<^sub>c \<F>\<^sub>0 D\<close> \<open>\<F>\<^sub>0 C\<^sub>0 \<noteq> \<F>\<^sub>0 D\<close> \<open>\<F>\<^sub>0 C\<^sub>0 \<prec>\<^sub>c \<F>\<^sub>0 D\<close>
        sorry
    next
      case (Suc m')
      then show ?case
        using a[rule_format]
        using b[rule_format]
        using N_to_N\<^sub>m
        sorry
    qed
  qed

  have "sfac D |\<in>| N\<^sub>i\<^sub>2"
    sorry

  have 1: "\<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1"
    if "C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1"
    for C
    using invars that
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
      unfolding Let_def \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map (Neg \<circ> term_of_gterm) Ks)\<close>
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
          hyps(11) hyps(6) local.step right_unique_iff right_unique_ord_res_1
          scl_reso1_\<F>_eq(1) scl_reso1_simple_destroy(3) that)
  qed

  ultimately show "
    (\<forall>C|\<in>|N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1. \<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1) \<and>
    (\<forall>C|\<in>|N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2. \<F>\<^sub>2 C |\<in>| N\<^sub>i\<^sub>2)"
    by metis
qed

definition ord_res_1_matches_scl_fol_1 where
  "ord_res_1_matches_scl_fol_1 _ _ = False"

interpretation backward_simulation_with_measuring_function where
  step1 = ord_res_1 and
  step2 = scl_fol_1_step and
  final1 = ord_res_1_final and
  final2 = scl_fol_1_final and
  order = "\<lambda>_ _. False" and
  match = "ord_res_1_matches_scl_fol_1" and
  measure = "\<lambda>_. ()"
proof unfold_locales
  fix S1 S2
  show "ord_res_1_matches_scl_fol_1 S1 S2 \<Longrightarrow> scl_fol_1_final S2 \<Longrightarrow> ord_res_1_final S1"
    sorry
next
  show "\<And>s1 s2 s2'.
    ord_res_1_matches_scl_fol_1 s1 s2 \<Longrightarrow>
    scl_fol_1_step s2 s2' \<Longrightarrow>
    (\<exists>s1'. ord_res_1\<^sup>+\<^sup>+ s1 s1' \<and> ord_res_1_matches_scl_fol_1 s1' s2') \<or>
    ord_res_1_matches_scl_fol_1 s1 s2' \<and> False"
    sorry
qed


subsection \<open>SCL(FOL)-0\<close>

inductive scl_fol_0 where
  "\<nexists>\<gamma>. state_conflict S = Some ({#}, \<gamma>) \<Longrightarrow>
    \<exists>C |\<in>| N. \<not> trail_true_cls (state_trail S) (cls_of_gcls C) \<Longrightarrow>
    scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>) S S' \<Longrightarrow>
    scl_fol_0 (N, \<beta>, S) (N, \<beta>, S')"

fun scl_fol_0_final :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state \<Rightarrow> bool" where
  "scl_fol_0_final (N, \<beta>, \<Gamma>, U, \<C>) \<longleftrightarrow>
    (\<exists>\<gamma>. \<C> = Some ({#}, \<gamma>)) \<or> (\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C))"

interpretation scl_fol_semantics: semantics where
  step = scl_fol_0 and
  final = scl_fol_0_final
proof unfold_locales
  fix S :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state"
  obtain N \<beta> \<Gamma> U \<C> where
    S_def: "S = (N, \<beta>, \<Gamma>, U, \<C>)"
    by (metis prod.exhaust)
  
  assume "scl_fol_0_final S"
  hence "(\<exists>\<gamma>. \<C> = Some ({#}, \<gamma>)) \<or> (\<forall>C |\<in>| N. trail_true_cls \<Gamma> (cls_of_gcls C))"
    unfolding S_def by simp
  hence "\<nexists>S'. scl_fol_0 S S'"
  proof (elim disjE exE conjE)
    fix \<gamma>
    assume "\<C> = Some ({#}, \<gamma>)"
    thus ?thesis
      by (auto simp: S_def elim: scl_fol_0.cases)
  next
    assume "\<forall>C|\<in>|N. trail_true_cls \<Gamma> (cls_of_gcls C)"
    then show ?thesis
      by (auto simp: S_def elim: scl_fol_0.cases)
  qed
  thus "finished scl_fol_0 S"
    by (simp add: finished_def)
qed

fun measure_scl_fol_1 :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) scl_fol_sim_state \<Rightarrow>
  'f gterm clause fset" where
  "measure_scl_fol_1 (N, \<beta>, (S, _, C, \<F>)) =
    {|D |\<in>| N |\<union>| gcls_of_cls |`| state_learned S. less_cls_sfac \<F> C D|}"

fun scl_fol_0_matches_scl_fol_1 where
  "scl_fol_0_matches_scl_fol_1 (N\<^sub>0, \<beta>\<^sub>0, (\<Gamma>\<^sub>0, U\<^sub>0, \<C>\<^sub>0)) (N\<^sub>1, \<beta>\<^sub>1, (\<Gamma>\<^sub>1, U\<^sub>1, \<C>\<^sub>1), ann) \<longleftrightarrow>
    N\<^sub>0 = N\<^sub>1 \<and> \<beta>\<^sub>0 = \<beta>\<^sub>1 \<and> \<Gamma>\<^sub>0 = \<Gamma>\<^sub>1 \<and> U\<^sub>0 = U\<^sub>1 \<and> \<C>\<^sub>0 = \<C>\<^sub>1 \<and>
    (\<forall>A |\<in>| atms_of_clss N\<^sub>0. A \<preceq>\<^sub>t \<beta>\<^sub>0) \<and>
    scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N\<^sub>0) (\<Gamma>\<^sub>0, U\<^sub>0, \<C>\<^sub>0)"

interpretation backward_simulation_with_measuring_function where
  step1 = scl_fol_0 and
  step2 = scl_fol_1_step and
  final1 = scl_fol_0_final and
  final2 = scl_fol_1_final and
  match = scl_fol_0_matches_scl_fol_1 and
  measure = measure_scl_fol_1 and
  order = "(|\<subset>|)"
proof unfold_locales
  show "wfP (|\<subset>|)"
    by auto
next
  fix
    S0 :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state" and
    S1 :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) scl_fol_sim_state"

  assume "scl_fol_0_matches_scl_fol_1 S0 S1"
  then obtain N \<beta> \<Gamma> U \<C> ann where
    S0_def: "S0 = (N, \<beta>, \<Gamma>, U, \<C>)" and S1_def: "S1 = (N, \<beta>, (\<Gamma>, U, \<C>), ann)" 
    by (cases "(S0, S1)" rule: scl_fol_0_matches_scl_fol_1.cases) simp

  thus "scl_fol_1_final S1 \<Longrightarrow> scl_fol_0_final S0"
    by simp
next
  let
    ?match = scl_fol_0_matches_scl_fol_1 and
    ?measure = measure_scl_fol_1 and
    ?order = "(|\<subset>|)"

  fix
    S0 :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) SCL_FOL.state" and
    S1 S1' :: "'f gterm clause fset \<times> 'f gterm \<times> ('f, 'v) scl_fol_sim_state"

  assume "scl_fol_0_matches_scl_fol_1 S0 S1"
  then obtain N \<beta> \<Gamma> U \<C> ann where
    S0_def: "S0 = (N, \<beta>, \<Gamma>, U, \<C>)" and S1_def: "S1 = (N, \<beta>, (\<Gamma>, U, \<C>), ann)" and
    \<beta>_greatereq: "\<forall>A |\<in>| atms_of_clss N. A \<preceq>\<^sub>t \<beta>" and
    init_geneneralize:
      "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) (\<Gamma>, U, \<C>)"
    by (cases "(S0, S1)" rule: scl_fol_0_matches_scl_fol_1.cases) simp

  assume "scl_fol_1_step S1 S1'"
  then obtain S\<^sub>0 i\<^sub>0 C\<^sub>0 \<F>\<^sub>0 S\<^sub>1 i\<^sub>1 C\<^sub>1 \<F>\<^sub>1 S\<^sub>2 i\<^sub>2 C\<^sub>2 \<F>\<^sub>2 where
    "S1 = (N, \<beta>, S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)" and
    "S1' = (N, \<beta>, S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    step': "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)"
    by (auto simp: S1_def elim: scl_fol_1_step.cases)

  have init_geneneralize': "scl_fol.initial_lits_generalize_learned_trail_conflict (cls_of_gcls |`| N) S\<^sub>0"
    using init_geneneralize
    using \<open>S1 = (N, \<beta>, S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0)\<close> S1_def by simp

  have 1: "(scl_fol.scl (cls_of_gcls |`| N) (term_of_gterm \<beta>))\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1"
    using correctness_scl_reso1(1)[OF \<beta>_greatereq step' init_geneneralize']
    by (metis mono_rtranclp scl_fol.scl_def)

  show "(\<exists>S0'. scl_fol_0\<^sup>+\<^sup>+ S0 S0' \<and> ?match S0' S1') \<or>
    (?match S0 S1' \<and> ?order (?measure S1') (?measure S1))"
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

    define S0' where
      "S0' = (N, \<beta>, S\<^sub>2)"

    have "scl_fol_0\<^sup>+\<^sup>+ S0 S0'"
      sorry

    moreover have "?match S0' S1'"
      sorry

    ultimately show ?thesis
      by metis
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