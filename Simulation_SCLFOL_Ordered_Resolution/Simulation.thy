theory Simulation
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Superposition_Calculus.Ground_Ordered_Resolution
    Superposition_Calculus.Min_Max_Least_Greatest_FSet
    VeriComp.Simulation
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


section \<open>Move to @{theory "HOL-Library.FSet"}\<close>

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

lemma (in ground_ordered_resolution_calculus) atms_of_concl_eq_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "atms_of C = atms_of P"
  using assms by (cases P C rule: ground_factoring.cases) simp


section \<open>Move somewhere?\<close>

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


subsection \<open>Strategy for model-driven ground ordered resolution\<close>

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

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
    C_min_false: "is_min_false_clause N C" and
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
  shows "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Pos A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

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

  have "{D \<in> fset N. D \<preceq>\<^sub>c C} = {D \<in> fset N. D \<prec>\<^sub>c C} \<union> {D \<in> fset N. D = C}"
    by fastforce
  with C_unproductive have
    "\<Union> (ord_res.production (fset N) ` {D \<in> fset N. D \<preceq>\<^sub>c C}) =
     \<Union> (ord_res.production (fset N) ` {D \<in> fset N. D \<prec>\<^sub>c C})"
    by simp
  with C_false have C_false': "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<prec>\<^sub>c C}) \<TTurnstile> C"
    by simp

  from C_unproductive have "A \<notin> ord_res.production (fset N) C"
    by simp
  thus ?thesis
  proof (rule contrapos_nn)
    assume "ord_res.is_strictly_maximal_lit (Pos A) C"
    then show "A \<in> ord_res.production (fset N) C"
      unfolding ord_res.production.simps[of "fset N" C] mem_Collect_eq
      using C_in C_def C_false' by metis
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


subsection \<open>Strategy for resolution-driven SCL(FOL)\<close>

definition sfac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "sfac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

lemma sfac_eq_disj:
  shows "sfac C = C \<or> (\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"
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

term "THE xs. sorted_wrt (\<prec>\<^sub>l) xs \<and> fset_of_list xs =
  {|K |\<in>| lits_of_clss N. is_neg K \<and> K \<prec>\<^sub>l L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit K)|}"

inductive scl_reso1
  :: "_ \<Rightarrow> _ \<Rightarrow>
    ('f, 'v) state \<times> _ \<Rightarrow>
    ('f, 'v) state \<times> _ \<Rightarrow>
    ('f, 'v) state \<times> _ \<Rightarrow> bool" for N\<^sub>0 \<beta> where
  scl_reso1I: "
  is_least_in_fset_wrt (less_cls_sfac \<F>)
    {|D |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. less_cls_sfac \<F> C D|} D \<Longrightarrow>
  ord_res.is_maximal_lit L D \<Longrightarrow>
  sorted_wrt (\<prec>\<^sub>l) Ks \<Longrightarrow> (\<forall>K \<in> set Ks. is_neg K \<and> K \<prec>\<^sub>l L \<and>
    \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and>
    lit_occures_in_clss K N\<^sub>0) \<Longrightarrow>
  \<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks) \<Longrightarrow>
  S1 = ((\<Gamma>\<^sub>1, U, None :: ('f, 'v) closure option), i, D, \<F>) \<Longrightarrow>
  (res_mo_strategy ^^ i) N\<^sub>0 N\<^sub>i \<Longrightarrow>
  \<F> D |\<in>| N\<^sub>i \<Longrightarrow>
  sfac D = sfac (\<F> D) \<Longrightarrow>
  \<F> D = add_mset L D' \<Longrightarrow>
  S2 =
    (let
      \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
      \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
      E = (THE x. is_least_in_fset_wrt (\<prec>\<^sub>c)
        {|C |\<in>| N\<^sub>0 |\<union>| fimage gcls_of_cls U. trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|} x);
      j\<^sub>0 = count D' L;
      j = i + j\<^sub>0;
      \<F>' = \<F>(D := add_mset L {#K \<in># D. K \<noteq> L#})
    in
      (if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
        trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
        (if (\<nexists>S'. scl_fol.conflict (cls_of_gcls |`| N\<^sub>0) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) S') then
          \<comment> \<open>2a\<close>
          ((\<Gamma>\<^sub>2\<^sub>a, U, None :: ('f, 'v) closure option), j, D, \<F>')
        else
          \<comment> \<open>2b\<close>
          ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>'))
      else
        \<comment> \<open>2c\<close>
        S1)) \<Longrightarrow>
  scl_reso1 N\<^sub>0 \<beta> ((\<Gamma>, U, None :: ('f, 'v) closure option), i, C, \<F>) S1 S2"

lemma
  assumes "scl_reso1 N \<beta> (S\<^sub>0, i\<^sub>0, C\<^sub>0, \<F>\<^sub>0) (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) (S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2)" and
    scl_reso1_2a: "\<And>\<Gamma> U D L Ks. S\<^sub>0 = (\<Gamma>, U, None) \<Longrightarrow>
      is_least_in_fset_wrt (less_cls_sfac \<F>\<^sub>0) {|D |\<in>| N |\<union>| gcls_of_cls |`| U. less_cls_sfac \<F>\<^sub>0 C\<^sub>0 D|} D \<Longrightarrow>
      ord_res.is_maximal_lit L D \<Longrightarrow>
      sorted_wrt (\<prec>\<^sub>l) Ks \<Longrightarrow>
      (\<forall>K \<in> set Ks. is_neg K \<and> K \<prec>\<^sub>l L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and> lit_occures_in_clss K N\<^sub>0) \<Longrightarrow>
      
      thesis"
  shows thesis
  oops

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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')
  have "state_learned S\<^sub>0 = U"
    using \<open>S\<^sub>0 = (\<Gamma>, U, None)\<close> by simp

  moreover have "state_learned S\<^sub>1 = U" and "i\<^sub>1 = i\<^sub>0" and "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp_all

  moreover have "state_learned S\<^sub>2 = U \<and> i\<^sub>0 \<le> i\<^sub>2 \<and> C\<^sub>2 = D"
  proof (cases "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
    trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})")
    case True1: True
    show ?thesis
    proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L), U, None))")
      case True2: True
      show ?thesis 
        using hyps(12)
        unfolding Let_def
        unfolding HOL.if_P[OF True1]
        unfolding if_not_P[of "\<not> _", simplified, OF True2]
        by simp
    next
      case False
      show ?thesis
        using hyps(12)
        unfolding Let_def
        unfolding HOL.if_P[OF True1]
        unfolding if_P[of "\<not> _", simplified, OF False]
        by simp
    qed
  next
    case False
    show ?thesis
      using hyps(12)
      unfolding Let_def
      unfolding HOL.if_not_P[OF False]
      by (simp add: \<open>state_learned S\<^sub>1 = U\<close> \<open>i\<^sub>1 = i\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>)
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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')

  have "C\<^sub>1 = D"
    using \<open>(S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1) = ((\<Gamma>\<^sub>1, U, None), i\<^sub>0, D, \<F>\<^sub>0)\<close> by simp

  have "\<F>\<^sub>1 = \<F>\<^sub>0"
    using hyps(7) by simp
  thus "\<F>\<^sub>1 = \<F>\<^sub>0 \<and>
    (\<F>\<^sub>2 = \<F>\<^sub>1 \<or> (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#})))"
  proof (intro conjI)
    show "\<F>\<^sub>2 = \<F>\<^sub>1 \<or>
      (\<exists>L. ord_res.is_maximal_lit L C\<^sub>1 \<and> \<F>\<^sub>2 = \<F>\<^sub>1(C\<^sub>1 := add_mset L {#K \<in># C\<^sub>1. K \<noteq> L#}))"
    proof (cases "is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
    trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})")
      case True1: True
      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>)
      (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L), U, None))")
        case True2: True
        show ?thesis
          using hyps
          unfolding Let_def
          unfolding HOL.if_P[OF True1]
          unfolding if_not_P[of "\<not> _", simplified, OF True2]
          unfolding \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>
          by blast
      next
        case False
        then show ?thesis
          using hyps
          unfolding Let_def
          unfolding HOL.if_P[OF True1]
          unfolding if_P[of "\<not> _", simplified, OF False]
          unfolding \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>C\<^sub>1 = D\<close>
          by blast
      qed
    next
      case False
      show ?thesis
        using hyps
        unfolding Let_def
        unfolding HOL.if_not_P[OF False]
        by simp
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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')

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
    note ball_K_Ks = \<open>\<forall>K\<in>set (K # Ks). is_neg K \<and> K \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and> lit_occures_in_clss K N\<close>

    from ball_K_Ks have
      "K \<prec>\<^sub>l L" "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)" "lit_occures_in_clss K N"
      by simp_all

    from Cons have "(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* (trail_decide \<Gamma> (lit_of_glit K), U, None) S\<^sub>1"
    proof (intro Cons.IH[OF refl] ballI)
      show "\<Gamma>\<^sub>1 = foldl trail_decide (trail_decide \<Gamma> (lit_of_glit K)) (map lit_of_glit Ks)"
        by (simp add: \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>)
    next
      show "sorted_wrt (\<prec>\<^sub>l) Ks"
        using \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> by simp
    next
      from \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> have "distinct (K # Ks)"
        using linorder_lit.strict_sorted_iff by blast

      fix Ka assume "Ka \<in> set Ks"
      hence "\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)"
        using ball_K_Ks by simp

      from \<open>Ka \<in> set Ks\<close> have "is_neg K" and "is_neg Ka"
        using ball_K_Ks by simp_all
      hence "atm_of K \<noteq> atm_of Ka"
        using \<open>distinct (K # Ks)\<close>
        by (metis \<open>Ka \<in> set Ks\<close> distinct.simps(2) literal.expand)
      hence "term_of_gterm (atm_of Ka) \<noteq> term_of_gterm (atm_of K)"
        using inj_term_of_gterm[of UNIV, THEN injD] by metis
      hence "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)\<close>
        by (simp add: trail_defined_lit_iff decide_lit_def atm_of_lit_of_glit_conv)
      thus "is_neg Ka \<and> Ka \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka) \<and>
        lit_occures_in_clss Ka N"
        using ball_K_Ks \<open>Ka \<in> set Ks\<close>
        by simp
    next
      assume hyp: "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (let
          \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
          \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
          E = The (is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|});
          j\<^sub>0 = count D' L;
          j = i\<^sub>0 + j\<^sub>0;
          \<F>' = \<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})
        in
          if is_pos L \<and> \<not> trail_defined_lit \<Gamma> (lit_of_glit L) \<and>
            trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
              ((\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls E, Var)), j, D, \<F>')
          else
            (S\<^sub>1, i\<^sub>1, C\<^sub>1, \<F>\<^sub>1))"
      show "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) =
        (let
          \<Gamma>\<^sub>2\<^sub>a = trail_decide \<Gamma>\<^sub>1 (lit_of_glit L);
          \<Gamma>\<^sub>2\<^sub>b = trail_propagate \<Gamma>\<^sub>1 (lit_of_glit L) (cls_of_gcls {#K \<in># D. K \<noteq> L#}) Var;
          E = The (is_least_in_fset_wrt (\<prec>\<^sub>c) {|C |\<in>| N |\<union>| gcls_of_cls |`| U.
            trail_false_cls \<Gamma>\<^sub>2\<^sub>b (cls_of_gcls C)|});
          j\<^sub>0 = count D' L;
          j = i\<^sub>0 + j\<^sub>0;
          \<F>' = \<F>\<^sub>0(D := add_mset L {#K \<in># D. K \<noteq> L#})
        in
          if is_pos L \<and> \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L) \<and>
            trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#}) then
            if \<nexists>a. scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (\<Gamma>\<^sub>2\<^sub>a, U, None) a then
              ((\<Gamma>\<^sub>2\<^sub>a, U, None), j, D, \<F>')
            else
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
    proof (intro scl_fol.decideI[of _ _ Var, simplified])
      show "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> .
    next
      show "is_ground_lit (lit_of_glit K)"
        by (cases K) (simp_all add: is_ground_lit_def atm_of_lit_of_glit_conv)
    next
      show "fBex N' ((\<in>#) (lit_of_glit K))"
        using \<open>lit_occures_in_clss K N\<close>
        unfolding lit_occures_in_clss_def N'_def
        by (metis cls_of_gcls_def finsertI1 finsert_fimage imageI multiset.set_map)
    next
      have "atm_of K |\<in>| atms_of_clss N"
        using \<open>lit_occures_in_clss K N\<close>
        unfolding lit_occures_in_clss_def atms_of_clss_def
        by (metis atms_of_cls_def fimage_eqI fmember_ffUnion_iff fmember_fset_mset_iff)
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

  from hyps(4,5) have "distinct (map atm_of Ks)"
  proof (induction Ks)
    case Nil
    show ?case
      by simp
  next
    case (Cons Ka Ks)
    have "atm_of Ka \<notin> set (map atm_of Ks)"
      using Cons.prems literal.expand by fastforce
    moreover have "distinct (map atm_of Ks)"
      using Cons.prems by (intro Cons.IH) simp_all
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
      unfolding atomize_conj
      using \<open>(scl_fol.decide N' \<beta>')\<^sup>*\<^sup>* S\<^sub>0 S\<^sub>1\<close> invars
      by (induction S\<^sub>1 rule: rtranclp_induct)
        (simp_all add: scl_fol.decide_preserves_trail_lits_from_clauses
          scl_fol.decide_preserves_initial_lits_generalize_learned_trail_conflict)
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
      let ?j = "i\<^sub>0 + count D' L"

      obtain D' :: "('f, 'v) term clause" where
        "cls_of_gcls D = add_mset (lit_of_glit L) D'"
        by (metis cls_of_gcls_def hyps(3) image_mset_add_mset insert_DiffM
            linorder_lit.is_maximal_in_mset_iff)

      have "\<not> trail_defined_lit \<Gamma> (lit_of_glit L)"
        using pos_L_and_undef_L_and_false_D by argo
      have "\<not> trail_defined_lit \<Gamma>\<^sub>1 (lit_of_glit L)"
        unfolding \<open>\<Gamma>\<^sub>1 = foldl trail_decide \<Gamma> (map lit_of_glit Ks)\<close>
        using hyps(5) pos_L_and_undef_L_and_false_D \<open>distinct (map atm_of Ks)\<close>
      proof (induction Ks arbitrary: \<Gamma>)
        case Nil
        thus ?case
          by simp
      next
        case (Cons K Ks)
        show ?case
          unfolding list.map foldl_Cons
        proof (intro Cons.IH ballI conjI)
          show "is_pos L"
            "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit L)"
            "trail_false_cls \<Gamma>\<^sub>1 (cls_of_gcls {#K \<in># D. K \<noteq> L#})"
            using Cons.prems undefined_in_trail_decide_if_undefined_in_trail_and_less_lit_pos
            by auto
        next
          show "distinct (map atm_of Ks)"
            using Cons.prems by simp
        next
          fix Ka assume Ka_in: "Ka \<in> set Ks"

          from Ka_in show "is_neg Ka" "Ka \<prec>\<^sub>l L" "lit_occures_in_clss Ka N"
            using Cons.prems(1) by simp_all

          from Ka_in have "atm_of K \<noteq> atm_of Ka"
            using Cons.prems(3) by auto
          hence "term_of_gterm (atm_of Ka) \<noteq> term_of_gterm (atm_of K)"
            using inj_term_of_gterm[of UNIV, THEN inj_onD, simplified] by metis
          moreover from Ka_in have "\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)"
            using Cons.prems(1) by simp
          ultimately show "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)"
            unfolding trail_defined_lit_iff
            by (simp add: decide_lit_def atm_of_lit_of_glit_conv)
        qed
      qed

      show ?thesis
      proof (cases "Ex (scl_fol.conflict (cls_of_gcls |`| N) (term_of_gterm \<beta>) (?\<Gamma>\<^sub>2\<^sub>a, U, None))")
        case ex_conflict: True
        have "(S\<^sub>2, i\<^sub>2, C\<^sub>2, \<F>\<^sub>2) = ((?\<Gamma>\<^sub>2\<^sub>b, U, Some (cls_of_gcls ?E, Var)), ?j, D, ?\<F>')"
          using hyps(12)
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
          using hyps(12) pos_L_and_undef_L_and_false_D by simp
        moreover have "scl_fol.decide N' \<beta>'
          (\<Gamma>\<^sub>1, U, None) (trail_decide \<Gamma>\<^sub>1 (lit_of_glit L \<cdot>l Var), U, None)"
        proof (rule scl_fol.decideI)
          show "lit_of_glit L \<in> \<Union> (set_mset ` fset N')"
            using \<open>L \<in> \<Union> (set_mset ` fset N)\<close>
            by (simp add: N'_def cls_of_gcls_def inj_image_mem_iff[OF inj_lit_of_glit])
        next
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
        using hyps(12) by auto
      thus ?thesis
        by simp
    qed
  qed
qed


subsection \<open>Sematincs of ORD-RES, ORD-RES++, SCL(FOL)++, and SCL(FOL)\<close>

inductive ord_reso_step where
  factoring: "{#} |\<notin>| N \<Longrightarrow> P |\<in>| N \<Longrightarrow> ord_res.ground_factoring P C \<Longrightarrow>
    ord_reso_step N (finsert C N)" |
  resolution: "{#} |\<notin>| N \<Longrightarrow> P1 |\<in>| N \<Longrightarrow> P2 |\<in>| N \<Longrightarrow> ord_res.ground_resolution P1 P2 C \<Longrightarrow>
    ord_reso_step N (finsert C N)"

interpretation ord_reso_semantics: semantics where
  step = ord_reso_step and
  final = "\<lambda>N. {#} |\<in>| N"
proof unfold_locales
  show "\<And>N. {#} |\<in>| N \<Longrightarrow> finished ord_reso_step N"
    by (simp add: finished_def ord_reso_step.simps)
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
  case (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')
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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')
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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')

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
  case hyps: (scl_reso1I U D L Ks \<Gamma> \<Gamma>\<^sub>1 N\<^sub>i D')

  have "state_learned S\<^sub>1 = state_learned S\<^sub>0" and "i\<^sub>1 = i\<^sub>0" and "\<F>\<^sub>1 = \<F>\<^sub>0"
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

  have 1: "\<F>\<^sub>1 C |\<in>| N\<^sub>i\<^sub>1"
    if "C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>1"
    for C
    using invar that
    unfolding \<open>state_learned S\<^sub>1 = state_learned S\<^sub>0\<close> \<open>\<F>\<^sub>1 = \<F>\<^sub>0\<close> \<open>N\<^sub>i\<^sub>1 = N\<^sub>i\<^sub>0\<close> by metis

  moreover have "\<F>\<^sub>2 C |\<in>| N\<^sub>i\<^sub>2"
    if "C |\<in>| N |\<union>| gcls_of_cls |`| state_learned S\<^sub>2"
    for C
  proof (cases "C = C\<^sub>1")
    case True
    then show ?thesis
      using \<F>\<^sub>2_eq_disj
      sorry
  next
    case False
    with \<F>\<^sub>2_eq_disj have "\<F>\<^sub>2 C = \<F>\<^sub>1 C"
      by force
    then show ?thesis
      using that \<open>N\<^sub>i\<^sub>1 |\<subseteq>| N\<^sub>i\<^sub>2\<close> 1
      unfolding \<open>state_learned S\<^sub>2 = state_learned S\<^sub>1\<close>
      by auto
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
    case (scl_reso1I \<F> C D U L Ks \<Gamma> \<Gamma>\<^sub>1 i N\<^sub>i D')
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
        apply (simp add: scl_fol.scl_preserves_initial_lits_generalize_learned_trail_conflict step.prems(5))
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