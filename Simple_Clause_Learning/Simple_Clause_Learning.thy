theory Simple_Clause_Learning
  imports
    Main
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Clausal_Calculus
    Ordered_Resolution_Prover.Clausal_Logic
    Ordered_Resolution_Prover.Abstract_Substitution
    Ordered_Resolution_Prover.Herbrand_Interpretation
    First_Order_Terms.Unification
    First_Order_Terms.Subsumption
    Abstract_Renaming_Apart
    Open_Induction.Restricted_Predicates
begin

section \<open>Extra Lemmas\<close>


subsection \<open>Relation_Extra\<close>

lemma irreflpD: "irreflp R \<Longrightarrow> \<not> R x x"
  unfolding irreflp_def by simp

lemma asymp_if_irreflp_and_transp: "irreflp R \<Longrightarrow> transp R \<Longrightarrow> asymp R"
  by (rule asympI) (metis irreflp_def transpD)

definition totalp where
  "totalp R \<longleftrightarrow> (\<forall>x. \<forall>y. x \<noteq> y \<longrightarrow> R x y \<or> R y x)"

lemma totalpI: "(\<And>x y. x \<noteq> y \<Longrightarrow> R x y \<or> R y x) \<Longrightarrow> totalp R"
  unfolding totalp_def by simp

lemma totalpD: "totalp R \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<or> R y x"
  unfolding totalp_def by simp


subsection \<open>Set_Extra\<close>

lemma not_in_iff: "L \<notin> xs \<longleftrightarrow> (\<forall>y\<in>xs. L \<noteq> y)"
  by auto


subsection \<open>List_Extra\<close>

lemma lt_lengthD:
  assumes i_lt_xs: "i < length xs"
  shows "\<exists>xs1 xi xs2. xs = xs1 @ xi # xs2 \<and> length xs1 = i"
  using assms
  by (metis Cons_nth_drop_Suc add_diff_cancel_left' add_diff_cancel_right'
      canonically_ordered_monoid_add_class.lessE id_take_nth_drop length_append length_drop)

lemma lt_lt_lengthD:
  assumes i_lt_xs: "i < length xs" and j_lt_xs: "j < length xs" and
    i_lt_j: "i < j"
  shows "\<exists>xs1 xi xs2 xj xs3. xs = xs1 @ xi # xs2 @ xj # xs3 \<and> length xs1 = i \<and>
    length (xs1 @ xi # xs2) = j"
proof -
  from i_lt_xs obtain xs1 xi xs' where "xs = xs1 @ xi # xs'" and "length xs1 = i"
    using lt_lengthD by blast
  with j_lt_xs obtain xs2 xj xs3 where "xs = xs1 @ xi # xs2 @ xj # xs3" and "length (xs1 @ xi # xs2) = j"
    using lt_lengthD
    by (smt (verit, del_insts) append.assoc append_Cons append_eq_append_conv i_lt_j list.inject)
  thus ?thesis
    using \<open>length xs1 = i\<close> by blast
qed


subsection \<open>Restricted_Predicates_Extra\<close>

lemma total_on_conv:
  shows "Restricted_Predicates.total_on R S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. x \<noteq> y \<longrightarrow> R x y \<or> R y x)"
  by (metis Restricted_Predicates.total_on_def)


subsection \<open>Multiset_Extra\<close>

lemma Multiset_Bex_plus_iff: "(\<exists>x \<in># (M1 + M2). P x) \<longleftrightarrow> (\<exists>x \<in># M1. P x) \<or> (\<exists>x \<in># M2. P x)"
  by auto

lemma multiset_is_empty_or_bex_greatest_element_if_trans_and_total:
  assumes
    transp_R: "Restricted_Predicates.transp_on R (set_mset M)" and
    total_on_R: "Restricted_Predicates.total_on R (set_mset M)"
  shows "M = {#} \<or> (\<exists>x \<in># M. \<forall>y \<in># M. x \<noteq> y \<longrightarrow> R y x)"
  using transp_R total_on_R
proof (induction M rule: multiset_induct)
  case empty
  thus ?case by simp
next
  case (add x M)
  from add.prems have transp_on_x_M_raw: "\<forall>y\<in>#M. \<forall>z\<in>#M. R x y \<and> R y z \<longrightarrow> R x z"
    by (metis transp_on_def insert_iff set_mset_add_mset_insert)

  from add.prems have transp_on_R_M: "Restricted_Predicates.transp_on R (set_mset M)"
    by (simp add: Restricted_Predicates.transp_on_subset[OF subset_insertI])

  from add.prems have
    total_on_x_M_raw: "\<forall>y \<in># M. x \<noteq> y \<longrightarrow> R x y \<or> R y x" and
    total_on_R_M: "Restricted_Predicates.total_on R (set_mset M)"
    by (simp_all add: total_on_conv)

  from add.IH[OF transp_on_R_M total_on_R_M] have "M = {#} \<or> (\<exists>x\<in>#M. \<forall>y\<in>#M. x \<noteq> y \<longrightarrow> R y x)"
    by simp
  hence "\<exists>xa\<in>#add_mset x M. \<forall>y\<in>#add_mset x M. xa \<noteq> y \<longrightarrow> R y xa"
  proof (elim disjE bexE)
    assume "M = {#}"
    thus ?thesis by simp
  next
    fix y
    assume "y \<in># M" and y_greatest: "\<forall>z\<in>#M. y \<noteq> z \<longrightarrow> R z y"
    show ?thesis
    proof (cases "x = y")
      case True
      thus ?thesis
        using y_greatest by auto
    next
      case False
      with \<open>y \<in># M\<close> show ?thesis
        using y_greatest
        by (metis total_on_x_M_raw transp_on_x_M_raw insert_iff set_mset_add_mset_insert)
    qed
  qed
  thus ?case by simp
qed


subsubsection \<open>Calculus_Extra\<close>

lemma (in consequence_relation) entails_one_formula: "N \<Turnstile> U \<Longrightarrow> D \<in> U \<Longrightarrow> N \<Turnstile> {D}"
  using entail_set_all_formulas by blast


subsection \<open>Clausal_Calculus_Extra\<close>

lemma true_cls_iff_set_mset_eq: "set_mset C = set_mset D \<Longrightarrow> I \<TTurnstile> C \<longleftrightarrow> I \<TTurnstile> D"
  by (simp add: true_cls_def)

lemma true_clss_if_set_mset_eq: "(\<forall>D \<in> \<D>. \<exists>C \<in> \<C>. set_mset D = set_mset C) \<Longrightarrow> I \<TTurnstile>s \<C> \<Longrightarrow> I \<TTurnstile>s \<D>"
  using true_cls_iff_set_mset_eq by (metis true_clss_def)

lemma entails_clss_insert: "N \<TTurnstile>e insert C U \<longleftrightarrow> N \<TTurnstile>e {C} \<and> N \<TTurnstile>e U"
  by auto


subsection \<open>Abstract_Substitution_Extra\<close>

lemma (in substitution_ops) grounding_of_clss_empty[simp]: "grounding_of_clss {} = {}"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) grounding_of_clss_singleton[simp]:
  "grounding_of_clss {C} = grounding_of_cls C"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) subst_atm_of_eqI:
  "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma> \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: subst_lit_def)

lemma (in substitution_ops) subst_atm_of_eq_compI:
  "L \<cdot>l \<sigma> = - (L' \<cdot>l \<sigma>) \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: uminus_literal_def subst_lit_def)

lemma (in substitution) is_ground_clss_grounding_of_clss[simp]:
  "is_ground_clss (grounding_of_clss N)"
  using grounding_of_clss_def union_grounding_of_cls_ground by presburger

lemma (in substitution) is_ground_cls_if_in_grounding_of_cls:
  "C' \<in> grounding_of_cls C \<Longrightarrow> is_ground_cls C'"
  using grounding_ground grounding_of_clss_singleton by blast


subsection \<open>First_Order_Terms Extra\<close>


subsubsection \<open>First_Order_Terms Only\<close>

lemma mgu_ball_codom_is_Var:
  assumes mgu_\<mu>: "is_mgu \<mu> E"
  shows "\<forall>x \<in> - (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)). is_Var (\<mu> x)"
proof (rule ballI)
  fix x
  assume x_in: "x \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))"

  from mgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>"
    by (simp_all add: is_mgu_def)

  define \<tau> where
    "\<tau> = (\<lambda>x. if x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)) then \<mu> x else Var x)"

  have \<open>\<tau> \<in> unifiers E\<close>
    unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e
    assume "e \<in> E"
    with unif_\<mu> have "fst e \<cdot> \<mu> = snd e \<cdot> \<mu>" by blast
    moreover from \<open>e \<in> E\<close> have "fst e \<cdot> \<tau> = fst e \<cdot> \<mu>" and "snd e \<cdot> \<tau> = snd e \<cdot> \<mu>"
      unfolding term_subst_eq_conv by (auto simp: \<tau>_def)
    ultimately show "fst e \<cdot> \<tau> = snd e \<cdot> \<tau>" by simp
  qed
  with minimal_\<mu> obtain \<gamma> where "\<tau> = \<mu> \<circ>\<^sub>s \<gamma>" by auto
  then show "is_Var (\<mu> x)"
    using x_in[THEN ComplD]
    by (metis (no_types, lifting) \<tau>_def subst_apply_eq_Var subst_compose_def term.disc(1))
qed

lemma mgu_inj_on:
  assumes mgu_\<mu>: "is_mgu \<mu> E"
  shows "inj_on \<mu> (- (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)))"
proof (rule inj_onI)
  fix x y
  assume
    x_in: "x \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))" and
    y_in: "y \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))" and
    "\<mu> x = \<mu> y"

  from mgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>"
    by (simp_all add: is_mgu_def)

  define \<tau> where
    "\<tau> = (\<lambda>x. if x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)) then \<mu> x else Var x)"

  have \<open>\<tau> \<in> unifiers E\<close>
    unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e
    assume "e \<in> E"
    with unif_\<mu> have "fst e \<cdot> \<mu> = snd e \<cdot> \<mu>" by blast
    moreover from \<open>e \<in> E\<close> have "fst e \<cdot> \<tau> = fst e \<cdot> \<mu>" and "snd e \<cdot> \<tau> = snd e \<cdot> \<mu>"
      unfolding term_subst_eq_conv by (auto simp: \<tau>_def)
    ultimately show "fst e \<cdot> \<tau> = snd e \<cdot> \<tau>" by simp
  qed
  with minimal_\<mu> obtain \<gamma> where "\<tau> = \<mu> \<circ>\<^sub>s \<gamma>" by auto
  then show "x = y"
    using ComplD[OF x_in] ComplD[OF y_in] \<open>\<mu> x = \<mu> y\<close>
    by (metis (no_types, lifting) \<tau>_def subst_compose_def term.inject(1))
qed

lemma inv_renaming_sound:
  assumes is_var_\<sigma>: "\<And>x. is_Var (\<sigma> x)" and inj_\<sigma>: "inj \<sigma>"
  shows "\<sigma> \<circ>\<^sub>s (Var \<circ> (inv (the_Var \<circ> \<sigma>))) = Var"
proof -
  define \<sigma>' where "\<sigma>' = the_Var \<circ> \<sigma>"
  have \<sigma>_def: "\<sigma> = Var \<circ> \<sigma>'"
    unfolding \<sigma>'_def using is_var_\<sigma> by auto

  from is_var_\<sigma> inj_\<sigma> have "inj \<sigma>'"
    unfolding inj_on_def \<sigma>_def comp_def by fast
  hence "inv \<sigma>' \<circ> \<sigma>' = id"
    using inv_o_cancel[of \<sigma>'] by simp
  hence "Var \<circ> (inv \<sigma>' \<circ> \<sigma>') = Var"
    by simp
  hence "\<forall>x. (Var \<circ> (inv \<sigma>' \<circ> \<sigma>')) x = Var x"
    by metis
  hence "\<forall>x. ((Var \<circ> \<sigma>') \<circ>\<^sub>s (Var \<circ> (inv \<sigma>'))) x = Var x"
    unfolding subst_compose_def by auto
  thus "\<sigma> \<circ>\<^sub>s (Var \<circ> (inv \<sigma>')) = Var"
    using \<sigma>_def by auto
qed

lemma ex_inv_subst:
  assumes is_var_\<sigma>: "\<And>x. is_Var (\<sigma> x)" and inj_\<sigma>: "inj \<sigma>"
  shows "\<exists>\<tau>. \<sigma> \<circ>\<^sub>s \<tau> = Var"
  using inv_renaming_sound[OF assms] by blast

lemma vars_subst_term_subset_weak: "vars_term (t \<cdot> \<sigma>) \<subseteq> vars_term t \<union> range_vars \<sigma>"
proof (induction t)
  case (Var x)
  show ?case
    apply (simp add: range_vars_def subst_domain_def)
    by force
next
  case (Fun f xs)
  thus ?case by auto
qed

lemma vars_subst_term_subset: "vars_term (t \<cdot> \<sigma>) \<subseteq> vars_term t - subst_domain \<sigma> \<union> range_vars \<sigma>"
proof (induction t)
  case (Var x)
  show ?case
    apply (simp add: range_vars_def subst_domain_def)
    by (smt (verit, best) SUP_upper Term.term.simps(17) empty_Diff insert_Diff_if le_supI1
        mem_Collect_eq sup_bot_left sup_ge2)
next
  case (Fun f xs)
  thus ?case by auto
qed

lemma vars_subst_term_eq:
  "vars_term (t \<cdot> \<sigma>) = vars_term t - subst_domain \<sigma> \<union> (\<Union>x \<in> vars_term t. vars_term (\<sigma> x))"
proof (induction t)
  case (Var x)
  show ?case
    by (simp add: insert_Diff_if subst_domain_def)
next
  case (Fun f xs)
  thus ?case
    apply simp by blast
qed

lemma mgu_subst_range_vars:
  assumes "Unification.mgu s t = Some \<sigma>"
  shows "range_vars \<sigma> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where *: "unify [(s, t)] [] = Some xs" and [simp]: "subst_of xs = \<sigma>"
    using assms by (simp split: option.splits)
  from unify_Some_UNIF [OF *] obtain ss
    where "compose ss = \<sigma>" and "UNIF ss {#(s, t)#} {#}" by auto
  with UNIF_range_vars_subset [of ss "{#(s, t)#}" "{#}"]
  show ?thesis using vars_mset_singleton by force
qed

lemma subst_term_eq_if_mgu:
  assumes mgu_t_u: "Unification.mgu t u = Some \<mu>"
  shows "t \<cdot> \<mu> = u \<cdot> \<mu>"
  using mgu_sound[OF mgu_t_u]
  unfolding Unifiers.is_imgu_def unifiers_def mem_Collect_eq
  by simp

lemma unify_subst_domain:
  assumes "unify E [] = Some xs"
  shows "subst_domain (subst_of xs) \<subseteq> (\<Union>e \<in> set E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  from unify_Some_UNIF[OF \<open>unify E [] = Some xs\<close>] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_subst_domain_subset
    by (metis (mono_tags, lifting) multiset.set_map set_mset_mset vars_mset_def)
qed


subsubsection \<open>First_Order_Terms And Abstract_Substitution\<close>

no_notation subst_apply_term (infixl "\<cdot>" 67)
no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)

global_interpretation substitution_ops subst_apply_term Var subst_compose .

notation subst_atm_abbrev (infixl "\<cdot>a" 67)
notation subst_atm_list (infixl "\<cdot>al" 67)
notation subst_lit (infixl "\<cdot>l" 67)
notation subst_cls (infixl "\<cdot>" 67)
notation subst_clss (infixl "\<cdot>cs" 67)
notation subst_cls_list (infixl "\<cdot>cl" 67)
notation subst_cls_lists (infixl "\<cdot>\<cdot>cl" 67)
notation comp_subst_abbrev (infixl "\<odot>" 67)

abbreviation vars_lit :: "('f, 'v) Term.term literal \<Rightarrow> 'v set" where
  "vars_lit L \<equiv> vars_term (atm_of L)"

definition vars_cls :: "('f, 'v) term clause \<Rightarrow> 'v set" where
  "vars_cls C = Union (set_mset (image_mset vars_lit C))"

definition vars_clss :: "('f, 'v) term clause set \<Rightarrow> 'v set" where
  "vars_clss N = (\<Union>C \<in> N. vars_cls C)"

lemma vars_cls_empty[simp]: "vars_cls {#} = {}"
  unfolding vars_cls_def by simp

lemma finite_vars_cls[simp]: "finite (vars_cls C)"
  unfolding vars_cls_def by simp

lemma vars_cls_plus_iff: "vars_cls (C + D) = vars_cls C \<union> vars_cls D"
  unfolding vars_cls_def by simp

lemma is_ground_atm_iff_vars_empty: "is_ground_atm t \<longleftrightarrow> vars_term t = {}"
  by (metis (mono_tags, opaque_lifting) equals0D equals0I is_ground_atm_def subst_apply_term_empty
      subst_def subst_simps(1) term.distinct(1) term_subst_eq term_subst_eq_rev)

lemma is_ground_atm_is_ground_on_var:
  assumes "is_ground_atm (A \<cdot>a \<sigma>)" and "v \<in> vars_term A"
  shows "is_ground_atm (\<sigma> v)"
using assms proof (induction A)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ts)
  then show ?case unfolding is_ground_atm_def
    by auto
qed

lemma is_ground_lit_is_ground_on_var:
  assumes ground_lit: "is_ground_lit (subst_lit L \<sigma>)" and v_in_L: "v \<in> vars_lit L"
  shows "is_ground_atm (\<sigma> v)"
proof -
  let ?A = "atm_of L"
  from v_in_L have A_p: "v \<in> vars_term ?A"
    by auto
  then have "is_ground_atm (?A \<cdot>a \<sigma>)"
    using ground_lit unfolding is_ground_lit_def by auto
  then show ?thesis
    using A_p is_ground_atm_is_ground_on_var by metis
qed

lemma is_ground_cls_is_ground_on_var:
  assumes
    ground_clause: "is_ground_cls (subst_cls C \<sigma>)" and
    v_in_C: "v \<in> vars_cls C"
  shows "is_ground_atm (\<sigma> v)"
proof -
  from v_in_C obtain L where L_p: "L \<in># C" "v \<in> vars_lit L"
    unfolding vars_cls_def by auto
  then have "is_ground_lit (subst_lit L \<sigma>)"
    using ground_clause unfolding is_ground_cls_def subst_cls_def by auto
  then show ?thesis
    using L_p is_ground_lit_is_ground_on_var by metis
qed

lemma same_on_vars_lit:
  assumes "\<forall>v \<in> vars_lit L. \<sigma> v = \<tau> v"
  shows "subst_lit L \<sigma> = subst_lit L \<tau>"
  using assms
proof (induction L)
  case (Pos x)
  then have "\<forall>v \<in> vars_term x. \<sigma> v = \<tau> v \<Longrightarrow> subst_atm_abbrev x \<sigma> = subst_atm_abbrev x \<tau>"
    using term_subst_eq by metis+
  then show ?case
    unfolding subst_lit_def using Pos by auto
next
  case (Neg x)
  then have "\<forall>v \<in> vars_term x. \<sigma> v = \<tau> v \<Longrightarrow> subst_atm_abbrev x \<sigma> = subst_atm_abbrev x \<tau>"
    using term_subst_eq by metis+
  then show ?case
    unfolding subst_lit_def using Neg by auto
qed

lemma same_on_vars_clause:
  assumes "\<forall>v \<in> vars_cls S. \<sigma> v = \<tau> v"
  shows "subst_cls S \<sigma> = subst_cls S \<tau>"
  by (smt assms image_eqI image_mset_cong2 mem_simps(9) same_on_vars_lit set_image_mset
      subst_cls_def vars_cls_def)

global_interpretation substitution "(\<cdot>a)" "Var :: _ \<Rightarrow> ('f, 'v) term" "(\<odot>)"
proof unfold_locales
  show "\<And>A. A \<cdot>a Var = A"
    by auto
next
  show "\<And>A \<tau> \<sigma>. A \<cdot>a (\<tau> \<odot> \<sigma>) = A \<cdot>a \<tau> \<cdot>a \<sigma>"
    by auto
next
  show "\<And>\<sigma> \<tau>. (\<And>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (simp add: subst_term_eqI)
next
  fix C :: "('f, 'v) term clause" and \<sigma> :: "('f, 'v) subst"
  assume "is_ground_cls (subst_cls C \<sigma>)"
  hence ground_atms_\<sigma>: "\<And>v. v \<in> vars_cls C \<Longrightarrow> is_ground_atm (\<sigma> v)"
    by (meson is_ground_cls_is_ground_on_var)

  define some_ground_trm :: "('f, 'v) term" where "some_ground_trm = (Fun undefined [])"
  have ground_trm: "is_ground_atm some_ground_trm"
    unfolding is_ground_atm_def some_ground_trm_def by auto
  define \<tau> where "\<tau> = (\<lambda>v. if v \<in> vars_cls C then \<sigma> v else some_ground_trm)"
  then have \<tau>_\<sigma>: "\<forall>v \<in> vars_cls C. \<sigma> v = \<tau> v"
    unfolding \<tau>_def by auto

  have all_ground_\<tau>: "is_ground_atm (\<tau> v)" for v
  proof (cases "v \<in> vars_cls C")
    case True
    then show ?thesis
      using ground_atms_\<sigma> \<tau>_\<sigma> by auto
  next
    case False
    then show ?thesis
      unfolding \<tau>_def using ground_trm by auto
  qed
  have "is_ground_subst \<tau>"
    unfolding is_ground_subst_def
  proof
    fix A
    show "is_ground_atm (A \<cdot>a \<tau>)"
    proof (induction A)
      case (Var v)
      thus ?case using all_ground_\<tau> by auto
    next
      case (Fun f As)
      thus ?case using all_ground_\<tau> by (simp add: is_ground_atm_def)
    qed
  qed
  moreover with \<tau>_\<sigma> have "C \<cdot> \<sigma> = C \<cdot> \<tau>"
    using same_on_vars_clause by auto
  ultimately show "\<exists>\<tau>. is_ground_subst \<tau> \<and> C \<cdot> \<tau> = C \<cdot> \<sigma>"
    by auto
next
  show "wfP (strictly_generalizes_atm :: ('f, 'v) term \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfP_def
    by (rule wf_subset[OF wf_subsumes])
      (auto simp: strictly_generalizes_atm_def generalizes_atm_def term_subsumable.subsumes_def
        subsumeseq_term.simps)
qed

definition disjoint_vars where
  "disjoint_vars C D \<longleftrightarrow> vars_cls C \<inter> vars_cls D = {}"

lemma disjoint_vars_iff_inter_empty: "disjoint_vars C D \<longleftrightarrow> vars_cls C \<inter> vars_cls D = {}"
  by (rule disjoint_vars_def)

hide_fact disjoint_vars_def

lemma disjoint_vars_sym: "disjoint_vars C D \<longleftrightarrow> disjoint_vars D C"
  unfolding disjoint_vars_iff_inter_empty by blast

lemma disjoint_vars_plus_iff: "disjoint_vars (C + D) E \<longleftrightarrow> disjoint_vars C E \<and> disjoint_vars D E"
  unfolding disjoint_vars_iff_inter_empty vars_cls_plus_iff
  by (simp add: Int_Un_distrib2)

definition disjoint_vars_set where
  "disjoint_vars_set N \<longleftrightarrow> (\<forall>C \<in> N. \<forall>D \<in> N. C \<noteq> D \<longrightarrow> disjoint_vars C D)"

lemma disjoint_vars_set_substetI[intro]: "disjoint_vars_set N \<Longrightarrow> M \<subseteq> N \<Longrightarrow> disjoint_vars_set M"
  unfolding disjoint_vars_set_def by auto

lemma is_renaming_iff: "is_renaming \<rho> \<longleftrightarrow> (\<forall>x. is_Var (\<rho> x)) \<and> inj \<rho>"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding is_renaming_def
    apply safe
     apply (metis subst_apply_eq_Var subst_compose term.disc(1))
    by (metis injI subst_compose_def term.sel(1))
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp: is_renaming_def intro: ex_inv_subst)
qed

lemma vars_subst_lit_eq:
  "vars_lit (L \<cdot>l \<sigma>) = vars_lit L - subst_domain \<sigma> \<union> (\<Union>x \<in> vars_lit L. vars_term (\<sigma> x))"
  using vars_subst_term_eq by (metis atm_of_subst_lit)

lemma vars_subst_cls_eq:
  "vars_cls (C \<cdot> \<sigma>) = vars_cls C - subst_domain \<sigma> \<union> (\<Union>x \<in> vars_cls C. vars_term (\<sigma> x))"
  unfolding vars_cls_def subst_cls_def
  apply simp
proof -
  have f1: "\<forall>l f. vars_lit (l \<cdot>l f) = vars_lit l - subst_domain f \<union> (\<Union>a\<in>vars_lit l. vars_term (f a::('b, 'a) Term.term))"
    by (smt (verit) vars_subst_lit_eq)
  obtain AA :: "('a \<Rightarrow> ('b, 'a) Term.term) \<Rightarrow> 'a \<Rightarrow> 'a set" where
    f2: "\<forall>X1 X2. AA X1 X2 = vars_term (X1 X2)"
    by moura
  obtain AAa :: "(('b, 'a) Term.term literal \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> ('b, 'a) Term.term literal \<Rightarrow> 'a set" where
    f3: "\<forall>X0 X2 X3. AAa X0 X2 X3 = X0 X3 - X2"
    by moura
  obtain AAb :: "(('b, 'a) Term.term literal \<Rightarrow> 'a set) \<Rightarrow> (('b, 'a) Term.term literal \<Rightarrow> 'a set) \<Rightarrow> ('b, 'a) Term.term literal \<Rightarrow> 'a set" where
    f4: "\<forall>X0 X1 X3. AAb X0 X1 X3 = X0 X3 \<union> X1 X3"
    by moura
  obtain AAc :: "('b, 'a) Term.term literal \<Rightarrow> 'a set" where
    f5: "\<forall>X3. AAc X3 = \<Union> (AA \<sigma> ` vars_lit X3)"
    by moura
  obtain AAd :: "('b, 'a) Term.term literal \<Rightarrow> 'a set" where
    f6: "\<forall>X2. AAd X2 = vars_lit X2"
    by moura
  obtain AAe :: "('b, 'a) Term.term literal \<Rightarrow> 'a set" where
    f7: "\<forall>X1. AAe X1 = vars_term (atm_of X1 \<cdot>a \<sigma>)"
    by moura
  then have "\<Union> (AAe ` set_mset C) = \<Union> (AAb (AAa AAd (subst_domain \<sigma>)) AAc ` set_mset C)"
    using f6 f5 f4 f3 f2 f1 by simp
  then have "\<Union> (AAe ` set_mset C) = \<Union> (AAa AAd (subst_domain \<sigma>) ` set_mset C) \<union> \<Union> (AAc ` set_mset C)"
    using f4 by (simp add: complete_lattice_class.SUP_sup_distrib)
  then show "(\<Union>l\<in>set_mset C. vars_term (atm_of l \<cdot>a \<sigma>)) = \<Union> (vars_lit ` set_mset C) - subst_domain \<sigma> \<union> (\<Union>l\<in>set_mset C. \<Union>a\<in>vars_lit l. vars_term (\<sigma> a))"
    using f7 f6 f5 f3 f2 by simp
qed

lemma vars_subst_lit_subset: "vars_lit (L \<cdot>l \<sigma>) \<subseteq> vars_lit L - subst_domain \<sigma> \<union> range_vars \<sigma>"
  using vars_subst_term_subset[of "atm_of L"] by simp

lemma vars_subst_cls_subset: "vars_cls (C \<cdot> \<sigma>) \<subseteq> vars_cls C - subst_domain \<sigma> \<union> range_vars \<sigma>"
  unfolding vars_cls_def subst_cls_def
  apply simp
  using vars_subst_lit_subset
  by fastforce

lemma vars_subst_lit_subset_weak: "vars_lit (L \<cdot>l \<sigma>) \<subseteq> vars_lit L \<union> range_vars \<sigma>"
  using vars_subst_term_subset_weak[of "atm_of L"] by simp

lemma vars_subst_cls_subset_weak: "vars_cls (C \<cdot> \<sigma>) \<subseteq> vars_cls C \<union> range_vars \<sigma>"
  unfolding vars_cls_def subst_cls_def
  apply simp
  using vars_subst_lit_subset_weak
  by fastforce

lemma vars_cls_plus[simp]: "vars_cls (C + D) = vars_cls C \<union> vars_cls D"
  unfolding vars_cls_def by simp

lemma vars_cls_add_mset[simp]: "vars_cls (add_mset L C) = vars_lit L \<union> vars_cls C"
  by (simp add: vars_cls_def)

lemma vars_cls_subst_mgu_subset:
  assumes mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<eta>"
  shows "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L, L'#})"
proof -
  have "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L#}) - subst_domain \<eta> \<union> range_vars \<eta>"
    by (rule vars_subst_cls_subset[of "(D + {#L#})" \<eta>])
  also have "... \<subseteq> vars_cls (D + {#L#}) - (vars_lit L \<union> vars_lit L') \<union> vars_lit L \<union> vars_lit L'"
    using mgu_subst_range_vars[OF mgu_L_L'] mgu_subst_domain[OF mgu_L_L'] by blast
  also have "... \<subseteq> vars_cls (D + {#L#}) \<union> vars_lit L \<union> vars_lit L'"
    by fast
  also have "... \<subseteq> vars_cls D \<union> vars_lit L \<union> vars_lit L'"
    unfolding vars_cls_plus unfolding vars_cls_def by simp
  also have "... \<subseteq> vars_cls (D + {#L, L'#})"
    by auto
  finally show ?thesis
    by assumption
qed

lemma disjoint_vars_set_mgu:
  assumes
    disj_N_D_L_L': "disjoint_vars_set N" and
    D_L_L'_in: "D + {#L, L'#} \<in> N" and
    mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<eta>"
  shows "disjoint_vars_set (N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>})"
proof -
  have vars_D_L_\<eta>_subset: "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L, L'#})"
    by (rule vars_cls_subst_mgu_subset[OF mgu_L_L'])

  have disj_D_L_\<eta>: "disjoint_vars ((D + {#L#}) \<cdot> \<eta>) C" if C_in: "C \<in> N - {D + {#L, L'#}}" for C
  proof -
    from C_in have "C \<noteq> D + {#L, L'#}" by force
    hence "disjoint_vars C (D + {#L, L'#})"
        by (meson D_L_L'_in DiffD1 \<open>C \<in> N - {D + {#L, L'#}}\<close> disj_N_D_L_L' disjoint_vars_set_def)
    thus ?thesis
      unfolding disjoint_vars_iff_inter_empty
      using vars_D_L_\<eta>_subset by blast
  qed

  show ?thesis
    unfolding disjoint_vars_set_def
  proof (intro ballI impI)
    fix C E
    assume
      C_D_in:
        "C \<in> N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>}"
        "E \<in> N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>}" and
      C_neq_E: "C \<noteq> E"

    from C_D_in[unfolded Un_iff] show "disjoint_vars C E"
    proof (elim disjE)
      assume "C \<in> N - {D + {#L, L'#}}" and "E \<in> N - {D + {#L, L'#}}"
      thus "disjoint_vars C E" by (meson C_neq_E DiffE disj_N_D_L_L' disjoint_vars_set_def)
    next
      assume "C \<in> {(D + {#L#}) \<cdot> \<eta>}" and "E \<in> {(D + {#L#}) \<cdot> \<eta>}"
      with \<open>C \<noteq> E\<close> have False by blast
      thus "disjoint_vars C E" by (rule FalseE)
    next
      assume C_in: "C \<in> N - {D + {#L, L'#}}" and E_in: "E \<in> {(D + {#L#}) \<cdot> \<eta>}"
      thus ?thesis using disj_D_L_\<eta> disjoint_vars_sym by blast
    next
      assume C_in: "C \<in> {(D + {#L#}) \<cdot> \<eta>}" and E_in: "E \<in> N - {D + {#L, L'#}}"
      thus ?thesis using disj_D_L_\<eta> by blast
    qed
  qed
qed

lemma disjoint_vars_set_minus_empty_vars:
  assumes "vars_cls C = {}"
  shows "disjoint_vars_set (N - {C}) \<longleftrightarrow> disjoint_vars_set N"
  using assms unfolding disjoint_vars_set_def disjoint_vars_iff_inter_empty by blast

lemma grounding_of_subst_cls_subset:
  shows "grounding_of_cls (C \<cdot> \<mu>) \<subseteq> grounding_of_cls C"
    (is "?lhs \<subseteq> ?rhs")
proof (rule subsetI)
  fix D
  assume "D \<in> ?lhs"
  then obtain \<gamma> where D_def: "D = C \<cdot> \<mu> \<cdot> \<gamma>" and gr_\<gamma>: "is_ground_subst \<gamma>"
    unfolding grounding_of_cls_def mem_Collect_eq by auto

  show "D \<in> ?rhs"
    unfolding grounding_of_cls_def mem_Collect_eq
    unfolding D_def
    using is_ground_comp_subst[OF gr_\<gamma>, of \<mu>]
    by force
qed

lemma subst_cls_idem_if_disj_vars: "subst_domain \<sigma> \<inter> vars_cls C = {} \<Longrightarrow> C \<cdot> \<sigma> = C"
  by (metis (mono_tags, lifting) Int_iff empty_iff mem_Collect_eq same_on_vars_clause
      subst_cls_id_subst subst_domain_def)

lemma subst_lit_idem_if_disj_vars: "subst_domain \<sigma> \<inter> vars_lit L = {} \<Longrightarrow> L \<cdot>l \<sigma> = L"
  by (rule subst_cls_idem_if_disj_vars[of _ "{#L#}", simplified])

definition restrict_subst where
  "restrict_subst V \<sigma> x \<equiv> (if x \<in> V then \<sigma> x else Var x)"

lemma subst_domain_restrict_subst: "subst_domain (restrict_subst V \<sigma>) \<subseteq> V"
  unfolding restrict_subst_def subst_domain_def
  by auto

lemma subst_cls_restrict_subst_idem: "vars_cls C \<subseteq> V \<Longrightarrow> C \<cdot> restrict_subst V \<sigma> = C \<cdot> \<sigma>"
  by (simp add: restrict_subst_def same_on_vars_clause subsetD)

lemma subst_clss_insert[simp]: "insert C U \<cdot>cs \<eta> = insert (C \<cdot> \<eta>) (U \<cdot>cs \<eta>)"
  by (simp add: subst_clss_def)

lemma valid_grounding_of_renaming:
  assumes "is_renaming \<rho>"
  shows "I \<TTurnstile>s grounding_of_cls (C \<cdot> \<rho>) \<longleftrightarrow> I \<TTurnstile>s grounding_of_cls C"
proof -
  have "grounding_of_cls (C \<cdot> \<rho>) = grounding_of_cls C" (is "?lhs = ?rhs")
    by (metis (no_types, lifting) assms subset_antisym subst_cls_comp_subst
        subst_cls_eq_grounding_of_cls_subset_eq subst_cls_id_subst substitution_ops.is_renaming_def)
  thus ?thesis
    by simp
qed


subsubsection \<open>Renaming Extra\<close>

context renaming_apart begin

lemma inj_Var_renaming: "finite V \<Longrightarrow> inj (Var \<circ> renaming V)"
  using inj_compose inj_renaming by (metis inj_def term.inject(1))

lemma is_renaming_Var_comp_renaming: "finite V \<Longrightarrow> Term.is_renaming (Var \<circ> renaming V)"
  unfolding Term.is_renaming_def
  using inj_Var_renaming by (metis comp_apply inj_on_subset term.disc(1) top_greatest)

lemma vars_term_subst_term_Var_comp_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_term (t \<cdot>a (Var \<circ> renaming V)) \<inter> V = {}"
  using is_renaming_Var_comp_renaming[OF fin_V] renaming_correct[OF fin_V]
  by (induction t) auto

lemma vars_lit_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_lit (L \<cdot>l (Var \<circ> renaming V)) \<inter> V = {}"
  using vars_term_subst_term_Var_comp_renaming_disj[OF fin_V] by auto

lemma vars_cls_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_cls (C \<cdot> (Var \<circ> renaming V)) \<inter> V = {}"
  unfolding vars_cls_def
  apply simp
  using vars_lit_subst_renaming_disj[OF fin_V]
  by (smt (verit, best) UN_iff UN_simps(10) disjoint_iff multiset.set_map subst_cls_def)

abbreviation renaming_wrt where
  "renaming_wrt N \<equiv> Var \<circ> renaming (\<Union> (vars_cls ` N))"

abbreviation inv_renaming_wrt where
  "inv_renaming_wrt N \<equiv> Var \<circ> inv_renaming (\<Union> (vars_cls ` N))"

definition inv_renaming' :: "('v \<Rightarrow> ('f, 'v) Term.term) \<Rightarrow> 'v \<Rightarrow> ('f, 'v) Term.term" where
  "inv_renaming' \<rho> \<equiv> Var \<circ> inv (the_Var \<circ> \<rho>)"

lemma inv_renaming'_sound: "is_renaming \<rho> \<Longrightarrow> \<rho> \<odot> inv_renaming' \<rho> = Var"
  unfolding is_renaming_iff inv_renaming'_def
  by (auto intro: inv_renaming_sound)

lemma subst_cls_renaming_inv_renaming_idem: "is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<cdot> inv_renaming' \<rho> = C"
  using inv_renaming'_sound
  by (metis subst_cls_comp_subst subst_cls_id_subst)

lemma is_renaming_renaming_wrt: "finite N \<Longrightarrow> is_renaming (renaming_wrt N)"
  by (simp add: inj_Var_renaming is_renaming_iff)

lemma range_vars_renaming_subset_domain_inv:
  "is_renaming \<rho> \<Longrightarrow> range_vars \<rho> \<subseteq> subst_domain (inv_renaming' \<rho>)"
  apply (rule subsetI)
  subgoal for x
  unfolding range_vars_def subst_range.simps subst_domain_def
  apply simp
  by (metis is_renaming_iff local.inv_renaming'_sound subst_apply_eq_Var subst_compose term.disc(2)
      term.sel(1) term.set_cases(2))
  done

definition rename_clause ::
  "('f, 'a) term clause set \<Rightarrow> ('f, 'a) term clause \<Rightarrow> ('f, 'a) term clause" where
  "rename_clause N C = C \<cdot> renaming_wrt N"

lemma disjoint_vars_set_insert_rename_clause:
  assumes fin_N: "finite N" and disj_N: "disjoint_vars_set N"
  shows "disjoint_vars_set (insert (rename_clause N C) N)"
  unfolding disjoint_vars_set_def
proof (intro ballI impI)
  fix D E
  assume D_in: "D \<in> insert (rename_clause N C) N" and E_in: "E \<in> insert (rename_clause N C) N" and
    D_neq_E: "D \<noteq> E"
  from fin_N have fin_vars_N: "finite (\<Union> (vars_cls ` N))" by simp
  show "disjoint_vars D E"
    using D_in E_in D_neq_E
    apply simp
    apply safe
    unfolding rename_clause_def disjoint_vars_iff_inter_empty
    using vars_cls_subst_renaming_disj[OF fin_vars_N]
    using disj_N[unfolded disjoint_vars_set_def disjoint_vars_iff_inter_empty, rule_format]
    by auto
qed

lemma ex_inv_rename_clause: "finite N \<Longrightarrow> \<exists>\<rho>. rename_clause N C \<cdot> \<rho> = C"
  unfolding rename_clause_def
  using ex_inv_subst[OF _ inj_Var_renaming]
  by (metis comp_apply finite_UN finite_vars_cls subst_cls_comp_subst subst_cls_id_subst
      term.disc(1))

lemma grounding_of_cls_rename_clause:
  "finite N \<Longrightarrow> grounding_of_cls (rename_clause N C) = grounding_of_cls C"
  unfolding grounding_of_cls_def
  apply (rule Set.equalityI; rule subsetI)
   apply (metis (no_types) grounding_of_cls_def rename_clause_def subsetD
      subst_cls_eq_grounding_of_cls_subset_eq)
  using ex_inv_rename_clause
  by (smt (verit, ccfv_threshold) Collect_mono_iff grounding_of_cls_def mem_Collect_eq
      subst_cls_eq_grounding_of_cls_subset_eq)

end


section \<open>SCL State\<close>

type_synonym ('f, 'v) closure = "('f, 'v) term clause \<times> ('f, 'v) subst"
type_synonym ('f, 'v) closure_with_lit =
  "('f, 'v) term clause \<times> ('f, 'v) term literal \<times> ('f, 'v) subst"
type_synonym ('f, 'v) trail = "(('f, 'v) term literal \<times> ('f, 'v) closure_with_lit option) list"
type_synonym ('f, 'v) state =
  "('f, 'v) trail \<times> ('f, 'v) term clause set \<times> ('f, 'v) closure option"

text \<open>Note that, in contrast to Bromberger, Schwarz, and Weidenbach, the level is not part of the
state. It would be redundant because it can always be computed from the trail.\<close>

definition state_trail :: "('f, 'v) state \<Rightarrow> ('f, 'v) trail" where
  "state_trail S = fst S"

lemma state_trail_simp[simp]: "state_trail (\<Gamma>, U, u) = \<Gamma>"
  by (simp add: state_trail_def)

definition state_learned :: "('f, 'v) state \<Rightarrow> ('f, 'v) term clause set" where
  "state_learned S = fst (snd S)"

lemma state_learned_simp[simp]: "state_learned (\<Gamma>, U, u) = U"
  by (simp add: state_learned_def)

definition state_conflict :: "('f, 'v) state \<Rightarrow> ('f, 'v) closure option" where
  "state_conflict S = snd (snd S)"

lemma state_conflict_simp[simp]: "state_conflict (\<Gamma>, U, u) = u"
  by (simp add: state_conflict_def)

definition clss_of_trail :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause set" where
  "clss_of_trail \<Gamma> = (\<Union>Ln \<in> set \<Gamma>. case snd Ln of None \<Rightarrow> {} | Some (C, L, _) \<Rightarrow> {C + {#L#}})"

lemma clss_of_trail_Nil[simp]: "clss_of_trail [] = {}"
  by (simp add: clss_of_trail_def)

lemma clss_of_trail_Cons: "clss_of_trail (Ln # \<Gamma>) = clss_of_trail [Ln] \<union> clss_of_trail \<Gamma>"
  by (simp add: clss_of_trail_def)

lemma finite_clss_of_trail[simp]: "finite (clss_of_trail \<Gamma>)"
  unfolding clss_of_trail_def
proof (induction \<Gamma>)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  then show ?case by (simp add: option.case_eq_if prod.case_eq_if)
qed

definition trail_propagate ::
  "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) term clause \<Rightarrow> ('f, 'v) subst \<Rightarrow>
    ('f, 'v) trail" where
  "trail_propagate \<Gamma> L C \<gamma> = (L \<cdot>l \<gamma>, Some (C, L, \<gamma>)) # \<Gamma>"

lemma clss_of_trail_trail_propagate[simp]:
  "clss_of_trail (trail_propagate \<Gamma> L C \<gamma>) = clss_of_trail \<Gamma> \<union> {C + {#L#}}"
  unfolding trail_propagate_def clss_of_trail_def by simp

definition trail_decide :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) trail" where
  "trail_decide \<Gamma> L = (L, None) # \<Gamma>"

lemma clss_of_trail_trail_decide[simp]:
  "clss_of_trail (trail_decide \<Gamma> L) = clss_of_trail \<Gamma>"
  unfolding trail_decide_def clss_of_trail_def by simp

definition is_decision_lit
  :: "('f, 'v) term literal \<times> ('f, 'v) closure_with_lit option \<Rightarrow> bool" where
  "is_decision_lit Ln \<longleftrightarrow> snd Ln = None"

primrec trail_level :: "('f, 'v) trail \<Rightarrow> nat" where
  "trail_level [] = 0" |
  "trail_level (Ln # \<Gamma>) = (if is_decision_lit Ln then Suc else id) (trail_level \<Gamma>)"

primrec trail_level_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> nat" where
  "trail_level_lit [] _ = 0" |
  "trail_level_lit (Ln # \<Gamma>) L =
    (if fst Ln = L \<or> fst Ln = -L then trail_level (Ln # \<Gamma>) else trail_level_lit \<Gamma> L)"

lemma trail_level_lit_le: "trail_level_lit \<Gamma> L \<le> trail_level \<Gamma>"
  by (induction \<Gamma>) simp_all

definition trail_level_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> nat" where
  "trail_level_cls \<Gamma> C = (if C = {#} then 0 else Max_mset {#trail_level_lit \<Gamma> L. L \<in># C#})"

lemma trail_level_cls_le: "trail_level_cls \<Gamma> C \<le> trail_level \<Gamma>"
  unfolding trail_level_cls_def
  using all_lt_Max_imp_lt_mset[of "image_mset (trail_level_lit \<Gamma>) C", simplified]
  using trail_level_lit_le
  by auto

primrec trail_backtrack :: "('f, 'v) trail \<Rightarrow> nat \<Rightarrow> ('f, 'v) trail" where
  "trail_backtrack [] _ = []" |
  "trail_backtrack (Lc # \<Gamma>) level =
    (if is_decision_lit Lc \<and> trail_level (Lc # \<Gamma>) = level then
      Lc # \<Gamma>
    else
      trail_backtrack \<Gamma> level)"

lemma trail_backtrack_inv: "trail_level \<Gamma> < level \<Longrightarrow> trail_backtrack \<Gamma> level = []"
proof (induction \<Gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons Lc \<Gamma>)
  thus ?case
    by (metis (mono_tags, lifting) trail_backtrack.simps(2) trail_level.simps(2) not_less_eq
        not_less_iff_gr_or_eq of_nat_eq_id of_nat_id)
qed

lemma trail_backtrack_suffix: "suffix (trail_backtrack \<Gamma> level) \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons Lc \<Gamma>)
  thus ?case
    by (cases "is_decision_lit Lc") (simp_all add: suffix_ConsI)
qed

lemma clss_of_trail_trail_decide_subset:
  "clss_of_trail (trail_backtrack \<Gamma> n) \<subseteq> clss_of_trail \<Gamma>"
  unfolding trail_decide_def clss_of_trail_def
  by (simp add: SUP_subset_mono set_mono_suffix trail_backtrack_suffix)

lemma ball_set_trail_backtrackI: "\<forall>x \<in> set \<Gamma>. P x \<Longrightarrow> \<forall>x \<in> set (trail_backtrack \<Gamma> level). P x"
  by (meson set_mono_suffix subset_eq trail_backtrack_suffix)

lemma trail_backtrack_hd:
  "trail_backtrack \<Gamma> level = [] \<or> is_decision_lit (hd (trail_backtrack \<Gamma> level))"
  by (induction \<Gamma>) simp_all

lemma trail_backtrack_level:
  "trail_level (trail_backtrack \<Gamma> level) = 0 \<or> trail_level (trail_backtrack \<Gamma> level) = level"
  by (induction \<Gamma>) simp_all

lemma trail_backtrack_level_eq:
  "level \<le> trail_level \<Gamma> \<Longrightarrow> trail_level (trail_backtrack \<Gamma> level) = level"
  by (induction \<Gamma>) auto

definition trail_interp :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term interp" where
  "trail_interp \<Gamma> = \<Union>((\<lambda>L. case L of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) ` fst ` set \<Gamma>)"

definition trail_true_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_true_lit \<Gamma> L \<longleftrightarrow> L \<in> fst ` set \<Gamma>"

definition trail_false_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_false_lit \<Gamma> L \<longleftrightarrow> - L \<in> fst ` set \<Gamma>"

definition trail_true_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_true_cls \<Gamma> C \<longleftrightarrow> (\<exists>L \<in># C. trail_true_lit \<Gamma> L)"

definition trail_false_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_false_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_false_lit \<Gamma> L)"

definition trail_true_clss :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause set \<Rightarrow> bool" where
  "trail_true_clss \<Gamma> N \<longleftrightarrow> (\<forall>C \<in> N. trail_true_cls \<Gamma> C)"

definition trail_defined_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> (L \<in> fst ` set \<Gamma> \<or> - L \<in> fst ` set \<Gamma>)"

lemma trail_defined_lit_iff_true_or_false:
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> trail_true_lit \<Gamma> L \<or> trail_false_lit \<Gamma> L"
  unfolding trail_defined_lit_def trail_false_lit_def trail_true_lit_def by (rule refl)

lemma ball_trail_backtrackI:
  assumes "\<forall>x \<in> set \<Gamma>. P (fst x)"
  shows "\<forall>x \<in> set (trail_backtrack \<Gamma> i). P (fst x)"
  using assms trail_backtrack_suffix[THEN set_mono_suffix]
  by blast

lemma trail_interp_Cons: "trail_interp (Ln # \<Gamma>) = trail_interp [Ln] \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def by simp

lemma trail_interp_Cons': "trail_interp (Ln # \<Gamma>) = (case fst Ln of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def by simp

lemma true_lit_thick_unionD: "(I1 \<union> I2) \<TTurnstile>l L \<Longrightarrow> I1 \<TTurnstile>l L \<or> I2 \<TTurnstile>l L"
  by auto

lemma trail_false_cls_ConsD:
  assumes tr_false: "trail_false_cls ((L, Some Cl) # \<Gamma>) C" and L_not_in: "-L \<notin># C"
  shows "trail_false_cls \<Gamma> C"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix M
  assume M_in: "M \<in># C"

  from M_in L_not_in have M_neq_L: "M \<noteq> -L" by auto

  from M_in tr_false have tr_false_lit_M: "trail_false_lit ((L, Some Cl) # \<Gamma>) M"
    unfolding trail_false_cls_def by simp
  thus "trail_false_lit \<Gamma> M"
    unfolding trail_false_lit_def
    using M_neq_L
    by (cases L; cases M) (simp_all add: trail_interp_def trail_false_lit_def)
qed

lemma ball_trail_propagate_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit (L \<cdot>l \<sigma>)"
  shows "\<forall>x\<in>set (trail_propagate \<Gamma> L C \<sigma>). is_ground_lit (fst x)"
  unfolding trail_propagate_def
  using assms by simp

lemma ball_trail_decide_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit L"
  shows "\<forall>x\<in>set (trail_decide \<Gamma> L). is_ground_lit (fst x)"
  unfolding trail_decide_def
  using assms
  by simp


section \<open>SCL Calculus\<close>

locale scl = renaming_apart renaming_vars inv_renaming_vars
  for renaming_vars inv_renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v"
begin

inductive propagate :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  propagateI: "C \<in> N \<union> U \<Longrightarrow> C'' + {#L#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C \<Longrightarrow>
    subst_domain \<gamma> \<subseteq> vars_cls C'' \<union> vars_lit L \<Longrightarrow> is_ground_cls ((C'' + {#L#}) \<cdot> \<gamma>) \<Longrightarrow>
    trail_false_cls \<Gamma> (C'' \<cdot> \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    propagate N (\<Gamma>, U, None) (trail_propagate \<Gamma> L C'' \<gamma>, U, None)"

inductive decide :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  decideI: "is_ground_lit L \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    decide N (\<Gamma>, U, None) (trail_decide \<Gamma> L, U, None)"

inductive conflict :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  conflictI: "D \<in> N \<union> U \<Longrightarrow> D' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D \<Longrightarrow>
    subst_domain \<sigma> \<subseteq> vars_cls D' \<Longrightarrow> is_ground_cls (D' \<cdot> \<sigma>) \<Longrightarrow> trail_false_cls \<Gamma> (D' \<cdot> \<sigma>) \<Longrightarrow>
    conflict N (\<Gamma>, U, None) (\<Gamma>, U, Some (D', \<sigma>))"

inductive skip :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  skipI: "-(L \<cdot>l \<delta>) \<notin># D \<cdot> \<sigma> \<Longrightarrow>
    skip N (trail_propagate \<Gamma> L C \<delta>, U, Some (D, \<sigma>)) (\<Gamma>, U, Some (D, \<sigma>))"

inductive factorize :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  factorizeI: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma> \<Longrightarrow> Unification.mgu (atm_of L) (atm_of L') = Some \<mu> \<Longrightarrow>
    \<sigma>' = restrict_subst (vars_cls ((D + {#L#}) \<cdot> \<mu>)) \<sigma> \<Longrightarrow>
    factorize N (\<Gamma>, U, Some (D + {#L,L'#}, \<sigma>)) (\<Gamma>, U, Some ((D + {#L#}) \<cdot> \<mu>, \<sigma>'))"

inductive resolve :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  resolveI: "\<Gamma> = trail_propagate \<Gamma>' L C \<delta> \<Longrightarrow> trail_level_cls \<Gamma> (D \<cdot> \<sigma>) = trail_level \<Gamma> \<Longrightarrow>
    \<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}}) \<Longrightarrow>
    (L \<cdot>l \<delta>) = -(L' \<cdot>l \<sigma>) \<Longrightarrow> Unification.mgu (atm_of L) (atm_of L') = Some \<mu> \<Longrightarrow>
    resolve N (\<Gamma>, U, Some (D + {#L'#}, \<sigma>)) (\<Gamma>, U, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>,
      restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)))"

inductive backtrack :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool"
  for N where
  backtrackI: "trail_level_lit \<Gamma> (L \<cdot>l \<sigma>) = trail_level \<Gamma> \<Longrightarrow>
    backtrack N (\<Gamma>, U, Some (D + {#L#}, \<sigma>))
      (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)), U \<union> {D + {#L#}}, None)"

definition scl :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) state \<Rightarrow> bool" where
  "scl N S S' \<longleftrightarrow> propagate N S S' \<or> decide N S S' \<or> conflict N S S' \<or> skip N S S' \<or>
    factorize N S S' \<or> resolve N S S' \<or> backtrack N S S'"

text \<open>Note that, in contrast to Fiori and Weidenbach (CADE 2019), the set of clauses @{term N} is a
parameter of the relation instead of being repeated twice in the state. This is to highlight the
fact that it is a constant.\<close>


subsection \<open>Well-Defined\<close>

lemma propagate_well_defined:
  assumes "propagate N S S'"
  shows
    "\<not> decide N S S'"
    "\<not> conflict N S S'"
    "\<not> skip N S S'"
    "\<not> factorize N S S'"
    "\<not> resolve N S S'"
    "\<not> backtrack N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma decide_well_defined:
  assumes "decide N S S'"
  shows
    "\<not> propagate N S S'"
    "\<not> conflict N S S'"
    "\<not> skip N S S'"
    "\<not> factorize N S S'"
    "\<not> resolve N S S'"
    "\<not> backtrack N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma conflict_well_defined:
  assumes "conflict N S S'"
  shows
    "\<not> propagate N S S'"
    "\<not> decide N S S'"
    "\<not> skip N S S'"
    "\<not> factorize N S S'"
    "\<not> resolve N S S'"
    "\<not> backtrack N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma skip_well_defined:
  assumes "skip N S S'"
  shows
    "\<not> propagate N S S'"
    "\<not> decide N S S'"
    "\<not> conflict N S S'"
    "\<not> factorize N S S'"
    "\<not> resolve N S S'"
    "\<not> backtrack N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma factorize_well_defined:
  assumes "factorize N S S'"
  shows
    "\<not> propagate N S S'"
    "\<not> decide N S S'"
    "\<not> conflict N S S'"
    "\<not> skip N S S'"
    (* "\<not> resolve N S S'" *)
    "\<not> backtrack N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma resolve_well_defined:
  assumes "resolve N S S'"
  shows
    "\<not> propagate N S S'"
    "\<not> decide N S S'"
    "\<not> conflict N S S'"
    "\<not> skip N S S'"
    (* "\<not> factorize N S S'" *)
    "\<not> backtrack N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma backtrack_well_defined:
  assumes "backtrack N S S'"
  shows
    "\<not> propagate N S S'"
    "\<not> decide N S S'"
    "\<not> conflict N S S'"
    "\<not> skip N S S'"
    "\<not> factorize N S S'"
    "\<not> resolve N S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)


section \<open>Soundness\<close>

inductive sound_trail for N U where
  Nil[simp]: "sound_trail N U []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> is_ground_lit L \<Longrightarrow>
    (case u of
      None \<Rightarrow> True |
      Some (C, L', \<gamma>) \<Rightarrow> L = L' \<cdot>l \<gamma> \<and> subst_domain \<gamma> \<subseteq> vars_cls C \<union> vars_lit L' \<and>
        is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and>
        (\<exists>D \<in> N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L'#} = D \<cdot> \<rho>)) \<Longrightarrow>
    sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U ((L, u) # \<Gamma>)"

lemma sound_trail_supersetI: "sound_trail N U \<Gamma> \<Longrightarrow> N \<subseteq> NN \<Longrightarrow> U \<subseteq> UU \<Longrightarrow> sound_trail NN UU \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  thus ?case by simp
next
  case (Cons \<Gamma> L u)
  show ?case
  proof (intro sound_trail.Cons)
    from Cons show
      "case u of
        None \<Rightarrow> True
      | Some (C, L', \<gamma>) \<Rightarrow> L = L' \<cdot>l \<gamma> \<and> subst_domain \<gamma> \<subseteq> vars_cls C \<union> vars_lit L' \<and>
          is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and>
          (\<exists>D \<in> NN \<union> UU. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L'#} = D \<cdot> \<rho>)"
      by (cases u) auto
  qed (use Cons in simp_all)
qed

lemma sound_trail_backtrackI: "sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U (trail_backtrack \<Gamma> level)"
  by (induction \<Gamma> rule: sound_trail.induct) (auto intro: sound_trail.intros)

lemma sound_trail_propagate:
  assumes
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    not_tr_def_\<Gamma>_L_\<sigma>: "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>)" and
    domain_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls C \<union> vars_lit L" and
    gr_C_L_\<sigma>: "is_ground_cls ((C + {#L#}) \<cdot> \<sigma>)" and
    tr_false_\<Gamma>_C_\<sigma>: "trail_false_cls \<Gamma> (C \<cdot> \<sigma>)" and
    ex_renaming: "\<exists>D\<in>N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L#} = D \<cdot> \<rho>"
  shows "sound_trail N U (trail_propagate \<Gamma> L C \<sigma>)"
  unfolding trail_propagate_def
proof (rule sound_trail.Cons; (unfold option.case prod.case)?)
  show "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>)"
    by (rule not_tr_def_\<Gamma>_L_\<sigma>)
next
  show "is_ground_lit (L \<cdot>l \<sigma>)"
    using gr_C_L_\<sigma>
    by (metis Melem_subst_cls is_ground_cls_def mset_subset_eq_add_right single_subset_iff)
next
  show "sound_trail N U \<Gamma>"
    by (rule sound_\<Gamma>)
next
  show "L \<cdot>l \<sigma> = L \<cdot>l \<sigma> \<and> subst_domain \<sigma> \<subseteq> vars_cls C \<union> vars_lit L \<and> is_ground_cls ((C + {#L#}) \<cdot> \<sigma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<sigma>) \<and>
    (\<exists>D\<in>N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L#} = D \<cdot> \<rho>)"
    using domain_\<sigma> gr_C_L_\<sigma> tr_false_\<Gamma>_C_\<sigma> ex_renaming by auto
qed

lemma sound_trail_decide:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow> is_ground_lit L \<Longrightarrow>
  sound_trail N U (trail_decide \<Gamma> L)"
  unfolding trail_decide_def
  by (auto intro: sound_trail.Cons)

abbreviation entails_\<G> (infix "\<TTurnstile>\<G>e" 50) where
  "entails_\<G> N U \<equiv> grounding_of_clss N \<TTurnstile>e grounding_of_clss U"

definition sound_state :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> bool" where
  "sound_state N S \<longleftrightarrow> (\<exists>\<Gamma> U u.
    S = (\<Gamma>, U, u) \<and>
    finite N \<and> finite U \<and>
    disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>) \<and>
    (case u of None \<Rightarrow> True | Some (C, _) \<Rightarrow> \<forall>D \<in> N \<union> U  \<union> clss_of_trail \<Gamma>. disjoint_vars C D) \<and>
    sound_trail N U \<Gamma> \<and>
    N \<TTurnstile>\<G>e U \<and>
    (case u of None \<Rightarrow> True
    | Some (C, \<gamma>) \<Rightarrow> subst_domain \<gamma> \<subseteq> vars_cls C \<and> is_ground_cls (C \<cdot> \<gamma>) \<and>
      trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and> N \<TTurnstile>\<G>e {C}))"

abbreviation initial_state :: "('f, 'v) state" where
  "initial_state \<equiv> ([], {}, None)"

lemma sound_initial_state[simp]: "finite N \<Longrightarrow> disjoint_vars_set N \<Longrightarrow> sound_state N initial_state"
  by (simp add: sound_state_def)

lemma trail_level_propagate[simp]:
  "trail_level (trail_propagate \<Gamma> L C \<gamma>) = trail_level \<Gamma>"
  by (simp add: trail_propagate_def is_decision_lit_def)

lemma trail_level_decide[simp]:
  "trail_level (trail_decide \<Gamma> L) = Suc (trail_level \<Gamma>)"
  by (simp add: trail_decide_def is_decision_lit_def)

lemma propagate_sound_state: "propagate N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: propagate.induct)
  case (propagateI C U C'' L \<Gamma> \<gamma>)
  from propagateI.prems have
    fin: "finite N" "finite U" and
    disj_N_U_\<Gamma>: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto

  from propagateI.hyps have
    C_in: "C \<in> N \<union> U" and
    rename_C: "C'' + {#L#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C" and
    domain_\<gamma>: "subst_domain \<gamma> \<subseteq> vars_cls C'' \<union> vars_lit L" and
    gr_C''_L_\<gamma>: "is_ground_cls ((C'' + {#L#}) \<cdot> \<gamma>)"
    by simp_all

  have "disjoint_vars_set (N \<union> U \<union> clss_of_trail (trail_propagate \<Gamma> L C'' \<gamma>))"
    using fin disj_N_U_\<Gamma> C_in rename_C
    by (auto intro: disjoint_vars_set_insert_rename_clause)

  moreover have "sound_trail N U (trail_propagate \<Gamma> L C'' \<gamma>)"
  proof (rule sound_trail_propagate)
    show "\<exists>D\<in>N \<union> U. \<exists>\<rho>. Simple_Clause_Learning.is_renaming \<rho> \<and> C'' + {#L#} = D \<cdot> \<rho>"
      unfolding rename_C unfolding rename_clause_def
      using fin C_in by (metis finite_UnI finite_clss_of_trail is_renaming_renaming_wrt)
  qed (use propagateI.hyps sound_\<Gamma> in simp_all)

  ultimately show ?case
    unfolding sound_state_def
    using fin N_entails_U by simp
qed

lemma decide_sound_state: "decide N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: decide.induct)
  case (decideI L \<Gamma> U)
  from decideI.prems have
    fin: "finite N" "finite U" and
    disj_N_U_\<Gamma>: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto
  with decideI.hyps show ?case
    unfolding sound_state_def
    using ball_trail_decide_is_ground_lit[of \<Gamma> L]
    by (auto intro: sound_trail_decide)
qed

lemma conflict_sound_state: "conflict N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: conflict.induct)
  case (conflictI D U D' \<Gamma> \<sigma>)
  from conflictI.prems have
    fin_N: "finite N" and
    fin_U: "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto

  from conflictI.hyps have D_in: "D \<in> N \<union> U" by simp
  from conflictI.hyps have D'_def: "D' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D" by simp

  from fin_N fin_U have fin_N_U: "finite (N \<union> U)" by simp
  with disj_N_U D'_def have disj_N_U_D': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars D' C"
    using disjoint_vars_set_insert_rename_clause
    by (smt (verit) UN_I Un_iff disjoint_iff disjoint_vars_iff_inter_empty finite_UN finite_UnI
        finite_clss_of_trail finite_vars_cls rename_clause_def vars_cls_subst_renaming_disj)

  from conflictI.hyps have "is_ground_cls (D' \<cdot> \<sigma>)" by simp

  moreover have N_entails_D': "N \<TTurnstile>\<G>e {D'}"
  proof (intro allI impI)
    fix I
    assume valid_N: "I \<TTurnstile>s grounding_of_clss N"
    moreover have "grounding_of_cls D' = grounding_of_cls D"
      unfolding D'_def
      using grounding_of_cls_rename_clause fin_N_U
      by (metis finite_UnI finite_clss_of_trail)
    ultimately show "I \<TTurnstile>s grounding_of_clss {D'}"
      using D_in
      by (metis (mono_tags, lifting) N_entails_U UN_I UnE grounding_of_clss_def
          grounding_of_clss_singleton true_clss_def)
  qed

  ultimately show ?case
    unfolding sound_state_def
    using fin_N fin_U disj_N_U disj_N_U_D' sound_\<Gamma> N_entails_U conflictI.hyps by simp
qed

lemma skip_sound_state: "skip N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: skip.induct)
  case (skipI L \<delta> D \<sigma> \<Gamma> C U)
  thus ?case
    unfolding sound_state_def
    by (auto simp: trail_propagate_def clss_of_trail_Cons[of _ \<Gamma>] is_decision_lit_def
        elim: sound_trail.cases dest!: trail_false_cls_ConsD)
qed

lemma factorize_sound_state: "factorize N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: factorize.induct)
  case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
  from factorizeI.prems have
    fin_N: "finite N" and fin_U: "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    disj_N_U_D_L_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L, L'#}) C" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L, L'#})" and
    gr_D_L_L'_\<sigma>: "is_ground_cls ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    N_entails_D_L_L': "N \<TTurnstile>\<G>e {D + {#L, L'#}}"
    unfolding sound_state_def by simp_all

  from factorizeI.hyps have mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<mu>" by simp
  from factorizeI.hyps have L_eq_L'_\<sigma>: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma>" by simp
  from factorizeI.hyps have \<sigma>'_def: "\<sigma>' = restrict_subst (vars_cls ((D + {#L#}) \<cdot> \<mu>)) \<sigma>" by simp

  from L_eq_L'_\<sigma> have \<sigma>_unif: "\<sigma> \<in> Unifiers.unifiers {(atm_of L, atm_of L')}"
    unfolding Unifiers.unifiers_def by (auto intro: subst_atm_of_eqI)

  have is_imgu_\<mu>_full:
    "Unifiers.is_imgu \<mu> (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset D))"
    using mgu_sound[OF mgu_L_L']
    by (smt (verit, best) Unifiers.is_imgu_def imageE insert_iff mem_Collect_eq prod.sel singletonD
        unifiers_def)

  have \<sigma>_unif_full:
    "\<sigma> \<in> unifiers (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset D))"
    unfolding unifiers_def mem_Collect_eq
    using L_eq_L'_\<sigma> by (auto intro: subst_atm_of_eqI)

  from mgu_L_L' have L_eq_L'_\<mu>: "L \<cdot>l \<mu> = L' \<cdot>l \<mu>"
    using subst_term_eq_if_mgu
    by (metis (mono_tags, lifting) L_eq_L'_\<sigma> atm_of_subst_lit literal.expand subst_lit_is_neg)

  have "disjoint_vars ((D + {#L#}) \<cdot> \<mu>) C" if C_in: "C \<in> N \<union> U \<union> clss_of_trail \<Gamma>" for C
    using disj_N_U_D_L_L'[rule_format, OF C_in]
    unfolding _disjoint_vars_iff_inter_empty
    using vars_cls_subst_mgu_subset[OF mgu_L_L']
    by fast

  moreover have "subst_domain \<sigma>' \<subseteq> vars_cls ((D + {#L#}) \<cdot> \<mu>)"
    unfolding \<sigma>'_def using subst_domain_restrict_subst by metis

  moreover have "is_ground_cls ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
  proof -
    have "is_ground_cls ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
      using gr_D_L_L'_\<sigma>
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_unif_full add_mset_add_single
          is_ground_cls_union is_imgu_\<mu>_full subst_cls_comp_subst subst_cls_union)
    thus ?thesis
      unfolding \<sigma>'_def using subst_cls_restrict_subst_idem by (metis subsetI)
  qed

  moreover have "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
  proof -
    have "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
      unfolding trail_false_cls_def
    proof (rule ballI)
      fix K
      assume "K \<in># (D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>"
      hence "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<or> K = L  \<cdot>l \<mu> \<cdot>l \<sigma>" by force
      thus "trail_false_lit \<Gamma> K"
      proof (elim disjE)
        show "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
          apply (rule tr_false_cls[unfolded trail_false_cls_def, rule_format])
          using is_imgu_\<mu>_full \<sigma>_unif_full
          by (metis (no_types, lifting) Unifiers.is_imgu_def subst_cls_comp_subst subst_cls_union
              union_iff)
      next
        have "L \<cdot>l \<mu> \<cdot>l \<sigma> = L \<cdot>l \<sigma>"
          using mgu_sound[OF mgu_L_L'] \<sigma>_unif
          unfolding Unifiers.is_imgu_def
          by (metis subst_lit_comp_subst)
        thus "K = L \<cdot>l \<mu> \<cdot>l \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
          by (auto intro: tr_false_cls[unfolded trail_false_cls_def, rule_format])
      qed
    qed
    thus ?thesis
      unfolding \<sigma>'_def using subst_cls_restrict_subst_idem by (metis subsetI)
  qed

  moreover have "N \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
  proof (rule entails_trans)
    show "N \<TTurnstile>\<G>e {D + {#L, L'#}}"
      by (rule N_entails_D_L_L')
  next
    have *: "{(D + {#L, L'#}) \<cdot> \<mu>} = {D \<cdot> \<mu> + {#L \<cdot>l \<mu>, L \<cdot>l \<mu>#}}"
      by (simp add: L_eq_L'_\<mu>)

    have "{D + {#L, L'#}} \<TTurnstile>\<G>e {(D + {#L, L'#}) \<cdot> \<mu>}"
      using subst_cls_eq_grounding_of_cls_subset_eq true_clss_mono
      by (metis (mono_tags, lifting) grounding_of_clss_singleton)

    moreover have "{(D + {#L, L'#}) \<cdot> \<mu>} \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
      apply (intro allI impI)
      by (erule true_clss_if_set_mset_eq[rotated]) (auto simp add: L_eq_L'_\<mu> grounding_of_cls_def)

    ultimately show "{D + {#L, L'#}} \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
      by simp
  qed

  ultimately show ?case
    unfolding sound_state_def
    using fin_N fin_U disj_N_U sound_\<Gamma> N_entails_U by simp
qed

lemma resolve_sound_state: "resolve N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: resolve.induct)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu>)
  from resolveI.prems have
    fin: "finite N" "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    disj_N_U_\<Gamma>_D_L_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L'#}) C" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})" and
    gr_D_L'_\<sigma>: "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L'#}) \<cdot> \<sigma>)" and
    N_entails_D_L': "N \<TTurnstile>\<G>e {D + {#L'#}}"
    unfolding sound_state_def by simp_all

  from resolveI.hyps have L_eq_comp_L': "L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)" by simp
  from resolveI.hyps have mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<mu>" by simp
  from resolveI.hyps have \<Gamma>_def: "\<Gamma> = trail_propagate \<Gamma>' L C \<delta>" by simp
  from resolveI.hyps fin have is_renaming_\<rho>: "is_renaming \<rho>"
    using is_renaming_renaming_wrt
    by (metis finite.emptyI finite.insertI finite_UnI finite_clss_of_trail)

  have "C + {#L#} \<in> clss_of_trail \<Gamma>"
    unfolding \<Gamma>_def by simp

  from sound_\<Gamma> \<Gamma>_def have tr_undef_\<Gamma>'_L_\<delta>: "\<not> trail_defined_lit \<Gamma>' (L \<cdot>l \<delta>)"
    by (auto simp: trail_propagate_def elim: sound_trail.cases)

  have vars_D_L'_vars_C_L_disj: "vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}"
    apply(rule disj_N_U_\<Gamma>_D_L_L'[unfolded disjoint_vars_iff_inter_empty,
          rule_format, of "C + {#L#}"])
    by (simp add: \<Gamma>_def)

  from sound_\<Gamma> have
    gr_C_L_\<delta>: "is_ground_cls ((C + {#L#}) \<cdot> \<delta>)" and
    tr_false_cls_C: "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)" and
    ex_renamed_in_N_U: "\<exists>CC \<in> N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L#} = CC \<cdot> \<rho>" and
    dom_\<delta>: "subst_domain \<delta> \<subseteq> vars_cls (C + {#L#})"
    unfolding sound_trail.simps[of _ _ \<Gamma>]
    unfolding \<Gamma>_def trail_propagate_def
    by auto

  have is_imgu_\<mu>_full:
    "Unifiers.is_imgu \<mu> (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset (C + D)))"
    using mgu_sound[OF mgu_L_L']
    by (smt (verit, best) Unifiers.is_imgu_def imageE insert_iff mem_Collect_eq prod.sel singletonD
        unifiers_def)

  from L_eq_comp_L' have "L \<cdot>l \<sigma> \<cdot>l \<delta> = - (L' \<cdot>l \<sigma> \<cdot>l \<delta>)"
    using dom_\<sigma> dom_\<delta>
    using subst_lit_idem_if_disj_vars[of \<sigma> L]
    by (smt (verit) Un_Int_eq(4) add_mset_eq_single gr_D_L'_\<sigma> inf.commute inf.orderE inf_bot_right
        inf_sup_aci(2) is_ground_cls_union is_ground_subst_cls subst_cls_single subst_cls_union
        sup_bot.right_neutral vars_D_L'_vars_C_L_disj vars_cls_add_mset vars_cls_empty
        vars_cls_plus_iff)

  hence \<sigma>_\<delta>_in_unif:"\<sigma> \<odot> \<delta> \<in> unifiers
    (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset (C + D)))"
    unfolding unifiers_def mem_Collect_eq
    by (auto intro: subst_atm_of_eq_compI[of _ "\<sigma> \<odot> \<delta>", simplified])

  have "disjoint_vars ((D + C) \<cdot> \<mu> \<cdot> \<rho>) E" if E_in: "E \<in> N \<union> U \<union> clss_of_trail \<Gamma>" for E
  proof -
    have
      inter_D_E: "vars_cls D \<inter> vars_cls E = {}" and
      inter_L'_E: "vars_cls {#L'#} \<inter> vars_cls E = {}"
        using disj_N_U_\<Gamma>_D_L_L'[rule_format, OF E_in]
        unfolding disjoint_vars_plus_iff
        unfolding disjoint_vars_iff_inter_empty
        by simp_all

    have inter_L_\<rho>_E: "vars_term (atm_of L \<cdot>a \<rho>) \<inter> vars_cls E = {}"
        by (smt (verit, ccfv_threshold) E_in UN_I UN_Un Un_empty disjoint_iff fin finite.intros
            finite_UN finite_UnI finite_clss_of_trail finite_vars_cls inf_sup_distrib1
            vars_lit_subst_renaming_disj resolveI.hyps(3) atm_of_subst_lit)

    show ?thesis
      unfolding subst_cls_union disjoint_vars_plus_iff
    proof (rule conjI)
      show "disjoint_vars (D \<cdot> \<mu> \<cdot> \<rho>) E"
        unfolding disjoint_vars_iff_inter_empty
        by (smt (verit) E_in UN_I Un_iff disjoint_iff fin finite.intros finite_UN finite_UnI
            finite_clss_of_trail finite_vars_cls vars_cls_subst_renaming_disj resolveI.hyps(3))
    next
      show "disjoint_vars (C \<cdot> \<mu> \<cdot> \<rho>) E"
        unfolding disjoint_vars_iff_inter_empty
        by (smt (verit) E_in UN_I Un_iff disjoint_iff fin finite.intros finite_UN finite_UnI
            finite_clss_of_trail finite_vars_cls vars_cls_subst_renaming_disj resolveI.hyps(3))
    qed
  qed

  moreover have
    "subst_domain (restrict_subst (vars_cls (D \<cdot> \<mu> \<cdot> \<rho>) \<union> vars_cls (C \<cdot> \<mu> \<cdot> \<rho>))
      (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)) \<subseteq> vars_cls (D \<cdot> \<mu> \<cdot> \<rho>) \<union> vars_cls (C \<cdot> \<mu> \<cdot> \<rho>)"
    by (meson subst_domain_restrict_subst)

  moreover have
    "is_ground_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>))
      (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
    unfolding subst_cls_restrict_subst_idem[OF subset_refl]
    unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
    unfolding subst_cls_union is_ground_cls_union
  proof (rule conjI)
    from gr_D_L'_\<sigma> have "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_subst_cls)
    hence "is_ground_cls ((D + {#L'#}) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_\<delta>_in_unif is_imgu_\<mu>_full
          subst_cls_comp_subst)
    thus "is_ground_cls (D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  next
    from gr_C_L_\<delta> have "is_ground_cls ((C + {#L#}) \<cdot> \<sigma> \<cdot> \<delta>)"
      using subst_cls_idem_if_disj_vars[of \<sigma> C]
      using dom_\<sigma> vars_D_L'_vars_C_L_disj
      by (smt (verit, best) Int_assoc inf.orderE inf_bot_right subst_cls_idem_if_disj_vars)
    hence "is_ground_cls ((C + {#L#}) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_\<delta>_in_unif is_imgu_\<mu>_full
          subst_cls_comp_subst)
    thus "is_ground_cls (C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  qed

  moreover have "trail_false_cls \<Gamma>
    ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
    unfolding subst_cls_restrict_subst_idem[OF subset_refl]
    unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
    unfolding subst_cls_union trail_false_cls_def
  proof (rule ballI)
    fix K
    assume "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta> + C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
    thus "trail_false_lit \<Gamma> K"
      unfolding union_iff
    proof (elim disjE)
      assume K_in: "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
      hence "K \<in># D \<cdot> \<sigma> \<cdot> \<delta>"
        using is_imgu_\<mu>_full[unfolded Unifiers.is_imgu_def, THEN conjunct2, rule_format,
            OF \<sigma>_\<delta>_in_unif]
        by (metis subst_cls_comp_subst)
      hence "K \<in># D \<cdot> \<sigma>"
        using gr_D_L'_\<sigma> is_ground_subst_cls by (metis is_ground_cls_union subst_cls_union)
      then show ?thesis
        by (auto intro!: tr_false_cls[unfolded trail_false_cls_def, rule_format])
    next
      have tr_false_cls_C: "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
        using sound_\<Gamma>
        unfolding sound_trail.simps[of _ _ \<Gamma>]
        unfolding \<Gamma>_def trail_propagate_def
        by simp

      assume "K \<in># C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
      hence "K \<in># C \<cdot> \<sigma> \<cdot> \<delta>"
        using is_imgu_\<mu>_full[unfolded Unifiers.is_imgu_def, THEN conjunct2, rule_format,
            OF \<sigma>_\<delta>_in_unif]
        by (metis subst_cls_comp_subst)
      have "K \<in># C \<cdot> \<delta>"
      proof -
        have "subst_domain \<sigma> \<inter> vars_cls C = {}"
          using dom_\<sigma> vars_D_L'_vars_C_L_disj
          by auto
        thus ?thesis
          using \<open>K \<in># C \<cdot> \<sigma> \<cdot> \<delta>\<close> subst_cls_idem_if_disj_vars[of \<sigma> C] by simp
      qed
      hence tr_false_\<Gamma>'_K:"trail_false_lit \<Gamma>' K"
        using tr_false_cls_C[unfolded trail_false_cls_def, rule_format, of K] by simp
      show ?thesis
      proof (cases "L \<cdot>l \<delta>")
        case L_Pos: (Pos t)
        show ?thesis
        proof (cases K)
          case K_Pos: (Pos u)
          then show ?thesis
            using L_Pos tr_false_\<Gamma>'_K tr_undef_\<Gamma>'_L_\<delta>
            unfolding \<Gamma>_def trail_false_lit_def trail_propagate_def trail_defined_lit_def
              trail_true_lit_def trail_interp_Cons'
            by simp
        next
          case (Neg u)
          then show ?thesis
            using L_Pos tr_false_\<Gamma>'_K
            unfolding \<Gamma>_def trail_false_lit_def trail_propagate_def
            unfolding trail_interp_Cons' prod.sel
            by simp
        qed
      next
        case (Neg t)
        then show ?thesis
          using tr_false_\<Gamma>'_K
          unfolding \<Gamma>_def trail_false_lit_def trail_propagate_def
          unfolding trail_interp_Cons' prod.sel
          by simp
      qed
    qed
  qed

  moreover have "N \<TTurnstile>\<G>e {(D + C) \<cdot> \<mu> \<cdot> \<rho>}"
  proof -
    from ex_renamed_in_N_U obtain CC' \<rho>\<^sub>C\<^sub>C where
      CC'_in: "CC' \<in> N \<union> U" and ren_\<rho>\<^sub>C\<^sub>C: "is_renaming \<rho>\<^sub>C\<^sub>C" and CC'_conv: "C + {#L#} = CC' \<cdot> \<rho>\<^sub>C\<^sub>C"
      by auto

    have "N \<TTurnstile>\<G>e {CC'}"
      using CC'_in
      by (metis (no_types, opaque_lifting) N_entails_U UnE emptyE grounding_of_clss_mono
          insert_subset subset_eq true_clss_mono)
    hence "N \<TTurnstile>\<G>e {CC' \<cdot> \<rho>\<^sub>C\<^sub>C}"
      using ren_\<rho>\<^sub>C\<^sub>C by (metis valid_grounding_of_renaming grounding_of_clss_singleton)
    hence "N \<TTurnstile>\<G>e {C + {#L#}}"
      using CC'_conv by simp
    hence *: "N \<TTurnstile>\<G>e {(C + {#L#}) \<cdot> \<mu>}"
      using grounding_of_subst_cls_subset
      by (metis (no_types, lifting) grounding_of_clss_singleton true_clss_mono)

    have **: "N \<TTurnstile>\<G>e {(D + {#L'#}) \<cdot> \<mu>}"
      using N_entails_D_L' grounding_of_subst_cls_subset
      by (metis (no_types, lifting) grounding_of_clss_singleton true_clss_mono)

    have "N \<TTurnstile>\<G>e {(D + C) \<cdot> \<mu>}"
      unfolding true_clss_def
    proof (intro allI impI ballI)
      fix I E
      assume I_entails: "\<forall>E \<in> grounding_of_clss N. I \<TTurnstile> E" and
        E_in: "E \<in> grounding_of_clss {(D + C) \<cdot> \<mu>}"

      from E_in have E_in': "E \<in> grounding_of_cls ((D + C) \<cdot> \<mu>)"
        unfolding grounding_of_clss_def by simp
      then obtain \<gamma> where E_def: "E = (D + C) \<cdot> \<mu> \<cdot> \<gamma>" and gr_\<gamma>: "is_ground_subst \<gamma>"
        unfolding grounding_of_cls_def by auto

      have "(D + {#L'#}) \<cdot> \<mu> \<cdot> \<gamma> \<in> grounding_of_clss {(D + {#L'#}) \<cdot> \<mu>}"
        using gr_\<gamma> unfolding grounding_of_clss_def grounding_of_cls_def by auto
      hence AA: "\<exists>K \<in># (D + {#L'#}) \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K"
        using **[rule_format, unfolded true_clss_def, OF I_entails]
        by (metis true_cls_def)

      have "(C + {#L#}) \<cdot> \<mu> \<cdot> \<gamma> \<in> grounding_of_clss {(C + {#L#}) \<cdot> \<mu>}"
        using gr_\<gamma> unfolding grounding_of_clss_def grounding_of_cls_def by auto
      hence BB: "\<exists>K \<in># (C + {#L#}) \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K"
        using *[rule_format, unfolded true_clss_def, OF I_entails]
        by (metis true_cls_def)

      show "I \<TTurnstile> E"
        unfolding E_def true_cls_def
        using AA[unfolded subst_cls_union Multiset_Bex_plus_iff]
        using BB[unfolded subst_cls_union Multiset_Bex_plus_iff]
        unfolding subst_cls_union Multiset_Bex_plus_iff
      proof (elim disjE)
        assume "\<exists>K \<in># {#L'#} \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K" and "\<exists>K \<in># {#L#} \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K"
        hence False
          using L_eq_comp_L'
          using subst_term_eq_if_mgu[OF mgu_L_L']
          by (cases L; cases L'; simp add: uminus_literal_def subst_lit_def)
        thus "(\<exists>K \<in># D \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K) \<or> (\<exists>K \<in># C \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K)"
          by simp
      qed simp_all
    qed
    thus ?thesis
      by (metis (no_types, lifting) grounding_of_clss_singleton grounding_of_subst_cls_subset
          true_clss_mono)
  qed

  ultimately show ?case
    unfolding sound_state_def
    using fin disj_N_U sound_\<Gamma> N_entails_U by simp
qed

lemma backtrack_sound_state: "backtrack N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: backtrack.induct)
  case (backtrackI \<Gamma> L \<sigma> U D)
  from backtrackI.prems have
    fin: "finite N" "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    disj_N_U_\<Gamma>_D_L_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L#}) C" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L#})" and
    gr_D_L_\<sigma>: "is_ground_cls ((D + {#L#}) \<cdot> \<sigma>)" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<sigma>)" and
    N_entails_D_L_L': "N \<TTurnstile>\<G>e {D + {#L#}}"
    unfolding sound_state_def by simp_all

  have "disjoint_vars_set (N \<union> U \<union>
    clss_of_trail (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>))) \<union> {D + {#L#}})"
    unfolding disjoint_vars_set_def
  proof (intro ballI impI)
    fix C E
    assume
      C_in: "C \<in> N \<union> U \<union> clss_of_trail (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>))) \<union>
        {D + {#L#}}" and
      E_in: "E \<in> N \<union> U \<union> clss_of_trail (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>))) \<union>
        {D + {#L#}}" and
      C_neq_E: "C \<noteq> E"
    from C_in have C_in': "C \<in> N \<union> U \<union> clss_of_trail \<Gamma> \<or> C = D + {#L#}"
      using clss_of_trail_trail_decide_subset by blast
    from E_in have E_in': "E \<in> N \<union> U \<union> clss_of_trail \<Gamma> \<or> E = D + {#L#}"
      using clss_of_trail_trail_decide_subset by blast

    from C_in' E_in' C_neq_E show "disjoint_vars C E"
      using disj_N_U[unfolded disjoint_vars_set_def, rule_format]
      using disj_N_U_\<Gamma>_D_L_L' disjoint_vars_sym by blast
  qed

  moreover have
    "sound_trail N (insert (add_mset L D) U) (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
    using backtrackI
    by (auto simp: sound_state_def intro: sound_trail_backtrackI sound_trail_supersetI)

  moreover have "N \<TTurnstile>\<G>e (U \<union> {D + {#L#}})"
    using N_entails_U N_entails_D_L_L' by (metis UN_Un grounding_of_clss_def true_clss_union)

  ultimately show ?case
    unfolding sound_state_def
    using fin by simp
qed

theorem scl_sound_state:
  fixes N :: "('f, 'v) Term.term clause set"
  shows "scl N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  unfolding scl_def
  using propagate_sound_state decide_sound_state conflict_sound_state skip_sound_state
    factorize_sound_state resolve_sound_state backtrack_sound_state
  by metis


section \<open>Reasonable And Regular Runs\<close>

definition reasonable_scl where
  "reasonable_scl N S S' \<longleftrightarrow> scl N S S' \<and> (decide N S S' \<longrightarrow> \<not>(\<exists>S''. conflict N S' S''))"

lemma scl_if_reasonable: "reasonable_scl N S S' \<Longrightarrow> scl N S S'"
  unfolding reasonable_scl_def scl_def by simp

definition regular_scl where
  "regular_scl N S S' \<longleftrightarrow> conflict N S S' \<or> \<not> conflict N S S' \<and> reasonable_scl N S S'"

lemma reasonable_if_regular:
  "regular_scl N S S' \<Longrightarrow> reasonable_scl N S S'"
  unfolding regular_scl_def (* reasonable_scl_def scl_def *)
proof (elim disjE conjE)
  assume "conflict N S S'"
  hence "scl N S S'"
    by (simp add: scl_def)
  moreover have "decide N S S' \<longrightarrow> \<not>(\<exists>S''. conflict N S' S'')"
    by (smt (verit, best) \<open>conflict N S S'\<close> conflict.cases option.distinct(1) snd_conv)
  ultimately show "reasonable_scl N S S'"
    by (simp add: reasonable_scl_def)
next
  assume "\<not> conflict N S S'" and "reasonable_scl N S S'"
  thus ?thesis by simp
qed

lemma reasonable_scl_sound_state: "reasonable_scl N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  using scl_sound_state reasonable_scl_def by blast

lemma regular_scl_sound_state: "regular_scl N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  by (rule reasonable_scl_sound_state[OF reasonable_if_regular])

lemma reasonable_run_sound_state:
  "(reasonable_scl N)\<^sup>*\<^sup>* S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  by (smt (verit, best) reasonable_scl_sound_state rtranclp_induct)

lemma regular_run_sound_state:
  "(regular_scl N)\<^sup>*\<^sup>* S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  by (smt (verit, best) regular_scl_sound_state rtranclp_induct)

lemma not_satisfiable_if_sound_state_conflict_bottom:
  assumes sound_S: "sound_state N S" and conflict_S: "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> satisfiable (grounding_of_clss N)"
proof -
  from sound_S conflict_S have "N \<TTurnstile>\<G>e {{#}}"
    unfolding sound_state_def state_conflict_def by auto
  thus ?thesis by simp
qed


section \<open>Clause Redundancy\<close>

definition ground_redundant where
  "ground_redundant lt N C \<longleftrightarrow> is_ground_clss N \<and> is_ground_cls C \<and> {D \<in> N. lt\<^sup>=\<^sup>= D C} \<TTurnstile>e {C}"

definition redundant where
  "redundant lt N C \<longleftrightarrow> (\<forall>C' \<in> grounding_of_cls C. ground_redundant lt (grounding_of_clss N) C')"


section \<open>Trail-Induced Ordering\<close>

definition trail_less_id_id where
  "trail_less_id_id Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i > j \<and> L = Ls ! i \<and> K = Ls ! j)"

definition trail_less_comp_id where
  "trail_less_comp_id Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i > j \<and> L = - (Ls ! i) \<and> K = Ls ! j)"

definition trail_less_id_comp where
  "trail_less_id_comp Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i \<ge> j \<and> L = Ls ! i \<and> K = - (Ls ! j))"

definition trail_less_comp_comp where
  "trail_less_comp_comp Ls L K \<longleftrightarrow>
    (\<exists>i < length Ls. \<exists>j < length Ls. i > j \<and> L = - (Ls ! i) \<and> K = - (Ls ! j))"

definition trail_less where
  "trail_less Ls L K \<longleftrightarrow> trail_less_id_id Ls L K \<or> trail_less_comp_id Ls L K \<or>
    trail_less_id_comp Ls L K \<or> trail_less_comp_comp Ls L K"


subsection \<open>Examples\<close>

context
  fixes L0 L1 L2 :: "'a :: uminus"
begin

lemma "trail_less_id_comp [L2, L1, L0] L2 (- L2)"
  unfolding trail_less_id_comp_def
proof (intro exI conjI)
  show "(0 :: nat) \<le> 0" by presburger
qed simp_all

lemma "trail_less_comp_id [L2, L1, L0] (- L1) L2"
  unfolding trail_less_comp_id_def
proof (intro exI conjI)
  show "(0 :: nat) < 1" by presburger
qed simp_all

lemma "trail_less_id_comp [L2, L1, L0] L1 (- L1)"
  unfolding trail_less_id_comp_def
proof (intro exI conjI)
  show "(1 :: nat) \<le> 1" by presburger
qed simp_all

lemma "trail_less_comp_id [L2, L1, L0] (- L0) L1"
  unfolding trail_less_comp_id_def
proof (intro exI conjI)
  show "(1 :: nat) < 2" by presburger
qed simp_all

lemma "trail_less_id_comp [L2, L1, L0] L0 (- L0)"
  unfolding trail_less_id_comp_def
proof (intro exI conjI)
  show "(2 :: nat) \<le> 2" by presburger
qed simp_all

lemma "trail_less_id_id [L2, L1, L0] L1 L2"
  unfolding trail_less_id_id_def
proof (intro exI conjI)
  show "(0 :: nat) < 1" by presburger
qed simp_all

lemma "trail_less_id_id [L2, L1, L0] L0 L1"
  unfolding trail_less_id_id_def
proof (intro exI conjI)
  show "(1 :: nat) < 2" by presburger
qed simp_all

lemma "trail_less_comp_comp [L2, L1, L0] (- L1) (- L2)"
  unfolding trail_less_comp_comp_def
proof (intro exI conjI)
  show "(0 :: nat) < 1" by presburger
qed simp_all

lemma "trail_less_comp_comp [L2, L1, L0] (- L0) (- L1)"
  unfolding trail_less_comp_comp_def
proof (intro exI conjI)
  show "(1 :: nat) < 2" by presburger
qed simp_all

end


subsection \<open>Miscellaneous Lemmas\<close>

lemma not_trail_less_Nil: "\<not> trail_less [] L K"
  unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
    trail_less_id_comp_def trail_less_comp_comp_def
  by simp

lemma pairwise_distinct_if_sound_trail:
  fixes \<Gamma>
  defines "Ls \<equiv> (map fst \<Gamma>)"
  shows "sound_trail N U \<Gamma> \<Longrightarrow>
    \<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  unfolding Ls_def
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  show ?case by simp
next
  case (Cons \<Gamma> L u)
  from Cons.hyps have L_distinct:
    "\<forall>x < length (map fst \<Gamma>). map fst \<Gamma> ! x \<noteq> L"
    "\<forall>x < length (map fst \<Gamma>). map fst \<Gamma> ! x \<noteq> - L"
    unfolding trail_defined_lit_def de_Morgan_disj
    unfolding image_set in_set_conv_nth not_ex de_Morgan_conj disj_not1
    by simp_all
  show ?case
    unfolding list.map prod.sel
  proof (intro allI impI)
    fix i j :: nat
    assume i_lt: "i < length (L # map fst \<Gamma>)" and j_lt: "j < length (L # map fst \<Gamma>)" and "i \<noteq> j"
    show
      "(L # map fst \<Gamma>) ! i \<noteq> (L # map fst \<Gamma>) ! j \<and>
       (L # map fst \<Gamma>) ! i \<noteq> - (L # map fst \<Gamma>) ! j"
    proof (cases i)
      case 0
      thus ?thesis
        using L_distinct \<open>i \<noteq> j\<close> \<open>j < length (L # map fst \<Gamma>)\<close>
        using gr0_conv_Suc by auto
    next
      case (Suc k)
      then show ?thesis
        apply simp
        using i_lt j_lt \<open>i \<noteq> j\<close> L_distinct Cons.IH[rule_format]
        using less_Suc_eq_0_disj by force
    qed
  qed
qed

lemma defined_if_trail_less:
  assumes "trail_less Ls L K"
  shows "L \<in> set Ls \<union> uminus ` set Ls" "L \<in> set Ls \<union> uminus ` set Ls"
   apply (atomize (full))
  using assms unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
    trail_less_id_comp_def trail_less_comp_comp_def
  by (elim disjE exE conjE) simp_all

lemma not_less_if_undefined:
  fixes L :: "'a :: uminus"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    "L \<notin> set Ls" "- L \<notin> set Ls"
  shows "\<not> trail_less Ls L K" "\<not> trail_less Ls K L"
  using assms
  unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  by auto

lemma defined_conv:
  fixes L :: "'a :: uminus"
  assumes uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "L \<in> set Ls \<union> uminus ` set Ls \<longleftrightarrow> L \<in> set Ls \<or> - L \<in> set Ls"
  by (auto simp: rev_image_eqI uminus_uminus_id)


subsection \<open>Well-Defined\<close>

lemma trail_less_id_id_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_id_id Ls L K"
  shows
    "\<not> trail_less_id_comp Ls L K"
    "\<not> trail_less_comp_id Ls L K"
    "\<not> trail_less_comp_comp Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+

lemma trail_less_id_comp_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_id_comp Ls L K"
  shows
    "\<not> trail_less_id_id Ls L K"
    "\<not> trail_less_comp_id Ls L K"
    "\<not> trail_less_comp_comp Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+

lemma trail_less_comp_id_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_comp_id Ls L K"
  shows
    "\<not> trail_less_id_id Ls L K"
    "\<not> trail_less_id_comp Ls L K"
    "\<not> trail_less_comp_comp Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+

lemma trail_less_comp_comp_well_defined:
  assumes
    pairwise_distinct: "\<forall>x \<in> set Ls. \<forall>y \<in> set Ls. x \<noteq> - y" and
    L_le_K: "trail_less_comp_comp Ls L K"
  shows
    "\<not> trail_less_id_id Ls L K"
    "\<not> trail_less_id_comp Ls L K"
    "\<not> trail_less_comp_id Ls L K"
  using L_le_K
  unfolding trail_less_id_id_def trail_less_comp_id_def trail_less_id_comp_def
    trail_less_comp_comp_def
  using pairwise_distinct[rule_format, OF nth_mem nth_mem]
  by metis+


subsection \<open>Strict Partial Order\<close>

lemma irreflp_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "irreflp (trail_less Ls)"
proof (rule irreflpI, rule notI)
  fix L :: 'a
  assume "trail_less Ls L L"
  then show False
    unfolding trail_less_def
  proof (elim disjE)
    show "trail_less_id_id Ls L L \<Longrightarrow> False"
      unfolding trail_less_id_id_def
      using pairwise_distinct by fastforce
  next
    show "trail_less_comp_id Ls L L \<Longrightarrow> False"
      unfolding trail_less_comp_id_def
      by (metis pairwise_distinct uminus_not_id)
  next
    show "trail_less_id_comp Ls L L \<Longrightarrow> False"
      unfolding trail_less_id_comp_def
      by (metis pairwise_distinct uminus_not_id)
  next
    show "trail_less_comp_comp Ls L L \<Longrightarrow> False"
      unfolding trail_less_comp_comp_def
      by (metis pairwise_distinct uminus_uminus_id nat_less_le)
  qed
qed

lemma irreflp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> irreflp (trail_less (map fst \<Gamma>))"
  using irreflp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma transp_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "transp (trail_less Ls)"
proof (rule transpI)
  fix L K H :: 'a
  show "trail_less Ls L K \<Longrightarrow> trail_less Ls K H \<Longrightarrow> trail_less Ls L H"
    using pairwise_distinct[rule_format] uminus_not_id uminus_uminus_id
    unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
      trail_less_id_comp_def trail_less_comp_comp_def
    (* Approximately 3 seconds on AMD Ryzen 7 PRO 5850U CPU. *)
    by (smt (verit, best) le_eq_less_or_eq order.strict_trans)
qed

lemma transp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> transp (trail_less (map fst \<Gamma>))"
  using transp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "asymp (trail_less Ls)"
  using irreflp_trail_less[OF assms] transp_trail_less[OF assms]
  using asymp_if_irreflp_and_transp
  by auto

lemma asymp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> asymp (trail_less (map fst \<Gamma>))"
  using asymp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Strict Total (w.r.t. Elements in Trail) Order\<close>

lemma total_on_trail_less:
  "Restricted_Predicates.total_on (trail_less Ls) (set Ls \<union> uminus ` set Ls)"
proof (rule Restricted_Predicates.total_onI, unfold Un_iff, elim disjE)
  fix L K
  assume "L \<in> set Ls" and "K \<in> set Ls"
  then obtain i j where "i < length Ls" "Ls ! i = L" "j < length Ls" "Ls ! j = K"
    unfolding in_set_conv_nth by auto
  thus "L = K \<or> trail_less Ls L K \<or> trail_less Ls K L"
    using less_linear[of i j]
    by (meson trail_less_def trail_less_id_id_def)
next
  fix L K
  assume "L \<in> set Ls" and "K \<in> uminus ` set Ls"
  then obtain i j where "i < length Ls" "Ls ! i = L" "j < length Ls" "- (Ls ! j) = K"
    unfolding in_set_conv_nth image_set length_map by auto
  then show "L = K \<or> trail_less Ls L K \<or> trail_less Ls K L"
    using less_linear[of i j]
    by (metis le_eq_less_or_eq trail_less_comp_id_def trail_less_def trail_less_id_comp_def)
next
  fix L K
  assume "L \<in> uminus ` set Ls" and "K \<in> set Ls"
  then obtain i j where "i < length Ls" "- (Ls ! i) = L" "j < length Ls" "Ls ! j = K"
    unfolding in_set_conv_nth image_set length_map by auto
  then show "L = K \<or> trail_less Ls L K \<or> trail_less Ls K L"
    using less_linear[of i j]
    by (metis le_eq_less_or_eq trail_less_comp_id_def trail_less_def trail_less_id_comp_def)
next
  fix L K
  assume "L \<in> uminus ` set Ls" and "K \<in> uminus ` set Ls"
  then obtain i j where "i < length Ls" "- (Ls ! i) = L" "j < length Ls" "- (Ls ! j) = K"
    unfolding in_set_conv_nth image_set length_map by auto
  then show "L = K \<or> trail_less Ls L K \<or> trail_less Ls K L"
    using less_linear[of i j]
    by (metis trail_less_comp_comp_def trail_less_def)
qed


subsection \<open>Well-Founded\<close>

lemma not_trail_less_Cons_id_comp:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length (L # Ls). \<forall>j < length (L # Ls). i \<noteq> j \<longrightarrow>
        (L # Ls) ! i \<noteq> (L # Ls) ! j \<and> (L # Ls) ! i \<noteq> - ((L # Ls) ! j)"
  shows "\<not> trail_less (L # Ls) (- L) L"
proof (rule notI, unfold trail_less_def, elim disjE)
  show "trail_less_id_id (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_id_id_def
    using pairwise_distinct uminus_not_id by metis
next
  show "trail_less_comp_id (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_comp_id_def
    using pairwise_distinct uminus_uminus_id
    by (metis less_not_refl)
next
  show "trail_less_id_comp (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_id_comp_def
    using pairwise_distinct uminus_not_id
    by (metis length_pos_if_in_set nth_Cons_0 nth_mem)
next
  show "trail_less_comp_comp (L # Ls) (- L) L \<Longrightarrow> False"
    unfolding trail_less_comp_comp_def
    using pairwise_distinct uminus_not_id uminus_uminus_id by metis
qed

lemma not_trail_less_if_undefined:
  fixes L :: "'a :: uminus"
  assumes
    undefined: "L \<notin> set Ls" "- L \<notin> set Ls" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "\<not> trail_less Ls L K" "\<not> trail_less Ls K L"
  using undefined[unfolded in_set_conv_nth] uminus_uminus_id
  unfolding trail_less_def trail_less_id_id_def trail_less_comp_id_def
    trail_less_id_comp_def trail_less_comp_comp_def
  by (smt (verit))+

lemma trail_less_ConsD:
  fixes L H K :: "'a :: uminus"
  assumes uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    L_neq_K: "L \<noteq> K" and L_neq_minus_K: "L \<noteq> - K" and
    less_Cons: "trail_less (L # Ls) H K"
  shows "trail_less Ls H K"
  using less_Cons[unfolded trail_less_def]
proof (elim disjE)
  assume "trail_less_id_id (L # Ls) H K"
  hence "trail_less_id_id Ls H K"
    unfolding trail_less_id_id_def
    using L_neq_K less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
next
  assume "trail_less_comp_id (L # Ls) H K"
  hence "trail_less_comp_id Ls H K"
    unfolding trail_less_comp_id_def
    using L_neq_K less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
next
  assume "trail_less_id_comp (L # Ls) H K"
  hence "trail_less_id_comp Ls H K"
    unfolding trail_less_id_comp_def
    using L_neq_minus_K uminus_uminus_id less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
next
  assume "trail_less_comp_comp (L # Ls) H K"
  hence "trail_less_comp_comp Ls H K"
    unfolding trail_less_comp_comp_def
    using L_neq_minus_K uminus_uminus_id less_Suc_eq_0_disj by fastforce
  thus ?thesis
    unfolding trail_less_def by simp
qed

lemma trail_subset_empty_or_ex_smallest:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "Q \<subseteq> set Ls \<union> uminus ` set Ls \<Longrightarrow> Q = {} \<or> (\<exists>z \<in> Q. \<forall>y. trail_less Ls y z \<longrightarrow> y \<notin> Q)"
  using pairwise_distinct
proof (induction Ls arbitrary: Q)
  case Nil
  thus ?case by simp
next
  case Cons_ind: (Cons L Ls)
  from Cons_ind.prems have pairwise_distinct_L_Ls:
    "\<forall>i<length (L # Ls). \<forall>j<length (L # Ls). i \<noteq> j \<longrightarrow>
      (L # Ls) ! i \<noteq> (L # Ls) ! j \<and> (L # Ls) ! i \<noteq> - (L # Ls) ! j"
    by simp
  hence pairwise_distinct_Ls:
    "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
    by (metis distinct.simps(2) distinct_conv_nth length_Cons not_less_eq nth_Cons_Suc)
  show ?case
  proof (cases "Q = {}")
    case True
    thus ?thesis by simp
  next
    case Q_neq_empty: False
    have Q_minus_subset: "Q - {L, - L} \<subseteq> set Ls \<union> uminus ` set Ls" using Cons_ind.prems(1) by auto

    have irreflp_gt_L_Ls: "irreflp (trail_less (L # Ls))"
      by (rule irreflp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct_L_Ls])

    have "\<exists>z\<in>Q. \<forall>y. trail_less (L # Ls) y z \<longrightarrow> y \<notin> Q"
      using Cons_ind.IH[OF Q_minus_subset pairwise_distinct_Ls]
    proof (elim disjE bexE)
      assume "Q - {L, -L} = {}"
      with Q_neq_empty have "Q \<subseteq> {L, -L}" by simp
      have ?thesis if "L \<in> Q"
        apply (intro bexI[OF _ \<open>L \<in> Q\<close>] allI impI)
        apply (erule contrapos_pn)
        apply (drule set_rev_mp[OF _ \<open>Q \<subseteq> {L, -L}\<close>])
        apply simp
        using irreflp_gt_L_Ls[THEN irreflpD, of L]
        using not_trail_less_Cons_id_comp[OF uminus_not_id uminus_uminus_id
            pairwise_distinct_L_Ls]
        by fastforce
      moreover have ?thesis if "L \<notin> Q"
      proof -
        from \<open>L \<notin> Q\<close> have "Q = {- L}"
          using Q_neq_empty \<open>Q \<subseteq> {L, -L}\<close> by auto
        thus ?thesis
          using irreflp_gt_L_Ls[THEN irreflpD, of "- L"] by auto
      qed
      ultimately show ?thesis by metis
    next
      fix K
      assume K_in_Q_minus: "K \<in> Q - {L, -L}" and "\<forall>y. trail_less Ls y K \<longrightarrow> y \<notin> Q - {L, -L}"
      from K_in_Q_minus have "L \<noteq> K" "- L \<noteq> K" by auto
      from K_in_Q_minus have "L \<noteq> - K" using \<open>- L \<noteq> K\<close> uminus_uminus_id by blast
      show ?thesis
      proof (intro bexI allI impI)
        show "K \<in> Q"
          using K_in_Q_minus by simp
      next
        fix H
        assume "trail_less (L # Ls) H K"
        hence "trail_less Ls H K"
          by (rule trail_less_ConsD[OF uminus_uminus_id \<open>L \<noteq> K\<close> \<open>L \<noteq> - K\<close>])
        hence "H \<notin> Q - {L, -L}"
          using \<open>\<forall>y. trail_less Ls y K \<longrightarrow> y \<notin> Q - {L, -L}\<close> by simp
        moreover have "H \<noteq> L \<and>  H \<noteq> - L"
          using uminus_uminus_id pairwise_distinct_L_Ls \<open>trail_less Ls H K\<close>
          by (metis (no_types, lifting) distinct.simps(2) distinct_conv_nth in_set_conv_nth
              list.set_intros(1,2) not_trail_less_if_undefined(1))
        ultimately show "H \<notin> Q"
          by simp
      qed
    qed
    thus ?thesis by simp
  qed
qed

lemma wfP_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  shows "wfP (trail_less Ls)"
  unfolding wfP_eq_minimal
proof (intro allI impI)
  fix M :: "'a set" and L :: 'a
  assume "L \<in> M"
  show "\<exists>z \<in> M. \<forall>y. trail_less Ls y z \<longrightarrow> y \<notin> M"
  proof (cases "M \<inter> (set Ls \<union> uminus ` set Ls) = {}")
    case True
    with \<open>L \<in> M\<close> have L_not_in_Ls: "L \<notin> set Ls \<and> - L \<notin> set Ls"
      unfolding disjoint_iff by (metis UnCI image_eqI uminus_uminus_id)
    then show ?thesis
    proof (intro bexI[OF _ \<open>L \<in> M\<close>] allI impI)
      fix K
      assume "trail_less Ls K L"
      hence False
        using L_not_in_Ls not_trail_less_if_undefined[OF _ _ uminus_uminus_id] by simp
      thus "K \<notin> M" ..
    qed
  next
    case False
    hence "M \<inter> (set Ls \<union> uminus ` set Ls) \<subseteq> set Ls \<union> uminus ` set Ls"
      by simp
    with False obtain H where
      H_in: "H \<in> M \<inter> (set Ls \<union> uminus ` set Ls)" and
      all_lt_H_no_in: "\<forall>y. trail_less Ls y H \<longrightarrow> y \<notin> M \<inter> (set Ls \<union> uminus ` set Ls)"
      using trail_subset_empty_or_ex_smallest[OF uminus_not_id uminus_uminus_id pairwise_distinct]
      by meson
    show ?thesis
    proof (rule bexI)
      show "H \<in> M" using H_in by simp
    next
      show "\<forall>y. trail_less Ls y H \<longrightarrow> y \<notin> M"
        using all_lt_H_no_in uminus_uminus_id
        by (metis Int_iff Un_iff image_eqI not_trail_less_if_undefined(1))
    qed
  qed
qed


subsection \<open>Extension on All Literals\<close>

definition trail_less_ex where
  "trail_less_ex lt Ls L K \<longleftrightarrow>
    (if L \<in> set Ls \<or> - L \<in> set Ls then
      if K \<in> set Ls \<or> - K \<in> set Ls then
        trail_less Ls L K
      else
        True
    else
      if K \<in> set Ls \<or> - K \<in> set Ls then
        False
      else
        lt L K)"

lemma trail_less_ex_if_trail_less:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x"
  shows "trail_less Ls L K \<Longrightarrow> trail_less_ex lt Ls L K"
  unfolding trail_less_ex_def
  using defined_if_trail_less[THEN defined_conv[OF uminus_uminus_id, THEN iffD1]]
  by auto

lemma irreflp_trail_ex_less:
  fixes Ls :: "('a :: uminus) list" and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    irreflp_lt: "irreflp lt"
  shows "irreflp (trail_less_ex lt Ls)"
  unfolding trail_less_ex_def
  using irreflp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct] irreflp_lt
  by (simp add: irreflpD irreflpI)

lemma transp_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    transp_lt: "transp lt"
  shows "transp (trail_less_ex lt Ls)"
  unfolding trail_less_ex_def
  using transp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct] transp_lt
  by (smt (verit, ccfv_SIG) transp_def)

lemma transp_trail_less_ex_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> transp lt \<Longrightarrow> transp (trail_less_ex lt (map fst \<Gamma>))"
  using transp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    asymp_lt: "asymp lt"
  shows "asymp (trail_less_ex lt Ls)"
  unfolding trail_less_ex_def
  using asymp_trail_less[OF uminus_not_id uminus_uminus_id pairwise_distinct] asymp_lt
  by (simp add: asymp.simps)

lemma asymp_trail_less_ex_if_sound:
  "sound_trail N U \<Gamma> \<Longrightarrow> asymp lt \<Longrightarrow> asymp (trail_less_ex lt (map fst \<Gamma>))"
  using asymp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma total_on_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    total_on_lt: "Restricted_Predicates.total_on lt S"
  shows "Restricted_Predicates.total_on (trail_less_ex lt Ls) S"
  using total_on_trail_less[of Ls, unfolded Restricted_Predicates.total_on_def]
  using total_on_lt
  unfolding trail_less_ex_def
  by (smt (verit, ccfv_threshold) Restricted_Predicates.total_on_def defined_conv
      uminus_uminus_id)

lemma wfP_trail_less_ex:
  fixes Ls :: "('a :: uminus) list"
  assumes
    uminus_not_id: "\<And>x :: 'a. - x \<noteq> x" and
    uminus_uminus_id: "\<And>x :: 'a. - (- x) = x" and
    pairwise_distinct:
      "\<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)" and
    wfP_lt: "wfP lt"
  shows "wfP (trail_less_ex lt Ls)"
  unfolding wfP_eq_minimal
proof (intro allI impI)
  fix Q :: "'a set" and x :: 'a
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. trail_less_ex lt Ls y z \<longrightarrow> y \<notin> Q "
  proof (cases "Q \<inter> (set Ls \<union> uminus ` set Ls) = {}")
    case True
    then show ?thesis
      using wfP_lt[unfolded wfP_eq_minimal, rule_format, OF \<open>x \<in> Q\<close>]
      by (metis (no_types, lifting) defined_conv disjoint_iff trail_less_ex_def uminus_uminus_id)
  next
    case False
    then show ?thesis
      using trail_subset_empty_or_ex_smallest[OF uminus_not_id uminus_uminus_id pairwise_distinct,
        unfolded wfP_eq_minimal, of "Q \<inter> (set Ls \<union> uminus ` set Ls)", simplified]
      by (metis (no_types, lifting) IntD1 IntD2 UnE defined_conv trail_less_ex_def uminus_uminus_id)
  qed
qed

end

end