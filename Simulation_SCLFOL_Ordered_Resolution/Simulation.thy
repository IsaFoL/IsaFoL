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


subsection \<open>More explicit strategy for model-driven ground ordered resolution\<close>


lemma mempty_lesseq_cls[simp]: "{#} \<preceq>\<^sub>c C" for C
  by (cases C) (simp_all add: subset_implies_multp)

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

definition sfac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "sfac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

lemma ex1_sfac_eq_if_pos_lit_is_maximal:
  assumes L_pos: "is_pos L" and L_max: "ord_res.is_maximal_lit L D"
  shows "\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
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
  using ex1_sfac_eq_if_pos_lit_is_maximal
  by (metis cancel_comm_monoid_add_class.diff_cancel empty_iff is_pos_def
      linorder_lit.is_greatest_in_mset_iff linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset
      set_mset_empty union_single_eq_member)

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

lemma sfac_spec_if_pos_lit_is_maximal:
  assumes L_pos: "is_pos L" and L_max: "ord_res.is_maximal_lit L C"
  shows "sfac C = add_mset L {#K \<in># C. K \<noteq> L#}"
proof -
  from assms obtain C' where
    "sfac C = C'" and
    "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex1_sfac_eq_if_pos_lit_is_maximal by metis
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