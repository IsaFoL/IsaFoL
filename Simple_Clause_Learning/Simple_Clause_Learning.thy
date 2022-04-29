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
    Open_Induction.Restricted_Predicates
    Abstract_Renaming_Apart
    Trail_Induced_Ordering
    Relation_Extra
begin

sledgehammer_params

section \<open>Extra Lemmas\<close>


subsection \<open>Set_Extra\<close>

lemma not_in_iff: "L \<notin> xs \<longleftrightarrow> (\<forall>y\<in>xs. L \<noteq> y)"
  by auto

lemma disjoint_iff': "A \<inter> B = {} \<longleftrightarrow> (\<forall>a \<in> A. a \<notin> B) \<and> (\<forall>b \<in> B. b \<notin> A)"
  by blast


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

lemma total_on_unionD:
  assumes "Restricted_Predicates.total_on R (S1 \<union> S2)"
  shows
    total_on_unionD1: "Restricted_Predicates.total_on R S1" and
    total_on_unionD2: "Restricted_Predicates.total_on R S2"
  by (metis Un_iff assms total_on_conv)+


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

lemma atm_of_eq_uminus_if_lit_eq: "L = - K \<Longrightarrow> atm_of L = atm_of K"
  by (cases L; cases K) simp_all

term subst_domain

lemma mem_range_varsI:
  assumes "\<sigma> x = Var y" "x \<noteq> y"
  shows "y \<in> range_vars \<sigma>"
  unfolding range_vars_def UN_iff
proof (rule bexI[of _ "Var y"])
  show "y \<in> vars_term (Var y)" by simp
next
  from assms show "Var y \<in> subst_range \<sigma>"
    by (simp_all add: subst_domain_def)
qed

lemma subst_apply_term_eq_subst_apply_term_composeI:
  assumes
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
    "x \<notin> subst_domain \<delta>"
  shows "\<sigma> x = (\<sigma> \<circ>\<^sub>s \<delta>) x"
proof (cases "\<sigma> x")
  case (Var y)
  show ?thesis
  proof (cases "x = y")
    case True
    with Var have \<open>\<sigma> x = Var x\<close> by simp
    moreover from \<open>x \<notin> subst_domain \<delta>\<close> have "\<delta> x = Var x"
      by (simp add: disjoint_iff subst_domain_def)
    ultimately show ?thesis
      by (simp add: subst_compose_def)
  next
    case False
    with Var have "y \<in> range_vars \<sigma>"
      by (auto intro: mem_range_varsI)
    hence "y \<notin> subst_domain \<delta>"
      using \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
      by (simp add: disjoint_iff)
    with Var show ?thesis
      unfolding subst_compose_def
      by (simp add: subst_domain_def)
  qed
next
  case (Fun f ys)
  hence "Fun f ys \<in> subst_range \<sigma> \<or> (\<forall>y\<in>set ys. y \<in> subst_range \<sigma>)"
    using subst_domain_def by fastforce
  hence " \<forall>x\<in>vars_term (Fun f ys). x \<in> range_vars \<sigma>"
    by (metis UN_I range_vars_def term.distinct(1) term.sel(4) term.set_cases(2))
  hence "Fun f ys \<cdot> \<delta> = Fun f ys \<cdot> Var"
    unfolding term_subst_eq_conv
    using \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
    by (simp add: disjoint_iff subst_domain_def)
  hence "Fun f ys \<cdot> \<delta> = Fun f ys"
    by simp
  with Fun show ?thesis
    by (simp add: subst_compose_def)
qed

lemma subst_comp_in_unifiersI:
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    "vars_term t \<inter> subst_domain \<delta> = {}" and
    "vars_term u \<inter> subst_domain \<sigma> = {}" and
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
  shows "\<sigma> \<circ>\<^sub>s \<delta> \<in> unifiers {(t, u)}"
proof -
  have "t \<cdot> \<sigma> = t \<cdot> \<sigma> \<cdot> \<delta>"
    unfolding term_subst_eq_conv[of t \<sigma> "\<sigma> \<circ>\<^sub>s \<delta>", simplified]
    using \<open>vars_term t \<inter> subst_domain \<delta> = {}\<close> \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
    by (auto intro: subst_apply_term_eq_subst_apply_term_composeI)
  moreover have "u \<cdot> \<delta> = u \<cdot> \<sigma> \<cdot> \<delta>"
    unfolding term_subst_eq_conv[of u \<delta> "\<sigma> \<circ>\<^sub>s \<delta>", simplified]
    using \<open>vars_term u \<inter> subst_domain \<sigma> = {}\<close>
    by (simp add: disjoint_iff subst_compose_def subst_domain_def)
  ultimately show ?thesis
    using \<open>t \<cdot> \<sigma> = u \<cdot> \<delta>\<close> by (simp add: unifiers_def)
qed

lemma subst_comp_in_unifiersI':
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    "vars_term t \<inter> subst_domain \<delta> = {}" and
    "vars_term u \<inter> subst_domain \<sigma> = {}" and
    "range_vars \<delta> \<inter> subst_domain \<sigma> = {}"
  shows "\<delta> \<circ>\<^sub>s \<sigma> \<in> unifiers {(t, u)}"
proof -
  have "t \<cdot> \<sigma> = t \<cdot> \<delta> \<cdot> \<sigma>"
    unfolding term_subst_eq_conv[of t \<sigma> "\<delta> \<circ>\<^sub>s \<sigma>", simplified]
    using \<open>vars_term t \<inter> subst_domain \<delta> = {}\<close>
    by (simp add: disjoint_iff subst_compose_def subst_domain_def)
  moreover have "u \<cdot> \<delta> = u \<cdot> \<delta> \<cdot> \<sigma>"
    unfolding term_subst_eq_conv[of u \<delta> "\<delta> \<circ>\<^sub>s \<sigma>", simplified]
    using \<open>vars_term u \<inter> subst_domain \<sigma> = {}\<close> \<open>range_vars \<delta> \<inter> subst_domain \<sigma> = {}\<close>
    by (auto intro: subst_apply_term_eq_subst_apply_term_composeI)
  ultimately show ?thesis
    using \<open>t \<cdot> \<sigma> = u \<cdot> \<delta>\<close> by (simp add: unifiers_def)
qed

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

lemma subst_ident_if_not_in_domain: "x \<notin> subst_domain \<mu> \<Longrightarrow> \<mu> x = Var x"
  by (simp add: subst_domain_def)

lemma is_imgu_subst_inj_renaming_if_is_imgu:
  assumes mgu_\<mu>: "is_imgu \<mu> {(t, u)}" and ren_\<rho>: "is_renaming \<rho>" and inj_\<rho>: "inj \<rho>"
  defines "\<mu>' \<equiv> (\<lambda>x.
    if x \<in> the_Var ` \<rho> ` subst_domain \<mu> then
      ((Var o the_inv \<rho>) \<circ>\<^sub>s \<mu> \<circ>\<^sub>s \<rho>) (Var x)
    else
      Var x)"
  shows "is_imgu \<mu>' {(t \<cdot> \<rho>, u \<cdot> \<rho>)}"
proof (unfold is_imgu_def, intro conjI ballI)
  have *: "t \<cdot> \<rho> \<cdot> \<mu>' = t \<cdot> \<mu> \<cdot> \<rho>" for t
    unfolding subst_subst
  proof (rule term_subst_eq)
    fix x
    assume "x \<in> vars_term t"
    obtain x' where "\<rho> x = Var x'"
      using ren_\<rho> by (meson is_Var_def is_renaming_def)
    hence inv_\<rho>_x': "the_inv \<rho> (Var x') = x"
      using inj_\<rho> by (metis the_inv_f_f)
      
    show "(\<rho> \<circ>\<^sub>s \<mu>') x = (\<mu> \<circ>\<^sub>s \<rho>) x"
    proof (cases "x \<in> subst_domain \<mu>")
      case True
      hence "x' \<in> the_Var ` \<rho> ` subst_domain \<mu>"
        using \<open>\<rho> x = Var x'\<close> by (metis imageI term.sel(1))
      then show ?thesis
        by (simp add: \<open>\<rho> x = Var x'\<close> \<mu>'_def subst_compose_def inv_\<rho>_x')
    next
      case False
      moreover hence "x' \<notin> the_Var ` \<rho> ` subst_domain \<mu>"
        by (smt (verit, best) \<open>\<rho> x = Var x'\<close> image_iff inj_\<rho> inj_image_mem_iff is_renaming_def ren_\<rho>
            term.collapse(1))
      ultimately show ?thesis
        by (simp add: subst_compose_def subst_ident_if_not_in_domain[of x \<mu>] \<mu>'_def \<open>\<rho> x = Var x'\<close>)
    qed
  qed

  from mgu_\<mu> have "t \<cdot> \<mu> = u \<cdot> \<mu>"
    using is_imgu_def by fastforce
  then show "\<mu>' \<in> unifiers {(t \<cdot> \<rho>, u \<cdot> \<rho>)}"
    unfolding unifiers_def mem_Collect_eq
    by (simp add: *)
next
  fix \<upsilon>
  assume "\<upsilon> \<in> unifiers {(t \<cdot> \<rho>, u \<cdot> \<rho>)}"
  hence "t \<cdot> \<rho> \<cdot> \<upsilon> = u \<cdot> \<rho> \<cdot> \<upsilon>"
    by fastforce

  with mgu_\<mu> have "\<rho> \<circ>\<^sub>s \<upsilon> = \<mu> \<circ>\<^sub>s \<rho> \<circ>\<^sub>s \<upsilon>"
    unfolding is_imgu_def
    by (simp add: subst_monoid_mult.mult_assoc unifiers_insert)

  show "\<upsilon> = \<mu>' \<circ>\<^sub>s \<upsilon>"
  proof (rule ext)
    fix x
    show "\<upsilon> x = (\<mu>' \<circ>\<^sub>s \<upsilon>) x"
      apply (cases " x \<in> the_Var ` \<rho> ` subst_domain \<mu>")
      apply (simp_all add: \<mu>'_def subst_compose_def)
      using \<open>\<rho> \<circ>\<^sub>s \<upsilon> = \<mu> \<circ>\<^sub>s \<rho> \<circ>\<^sub>s \<upsilon>\<close>
      by (smt (verit, del_insts) imageE inj_\<rho> is_renaming_def ren_\<rho> subst_compose
          subst_monoid_mult.mult.left_neutral term.collapse(1) the_inv_f_f)
  qed
qed

(* lemma fixes \<upsilon> :: "'a \<Rightarrow> ('b, 'a) Term.term" assumes "\<upsilon> \<in> unifiers E" shows "\<exists>\<mu>. is_mgu \<mu> E"
  unfolding is_mgu_def
proof (rule ccontr)
  assume "\<nexists>\<mu>. \<mu> \<in> unifiers E \<and> (\<forall>\<tau>\<in>unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>)"
  fix epred5_5 :: "('b, 'a) Term.term set \<Rightarrow> ('a \<Rightarrow> ('b, 'a) Term.term) \<Rightarrow> ('b, 'a) Term.term set \<Rightarrow> ('a \<Rightarrow> ('b, 'a) Term.term) \<Rightarrow>  ('b, 'a) Term.term set \<Rightarrow> bool"
  have "\<And>(X1 :: 'a \<Rightarrow> ('b, 'a) Term.term) (X2 :: ('b, 'a) Term.term set)
    (X3 :: 'a \<Rightarrow> ('b, 'a) Term.term)  (X4 :: ('b, 'a) Term.term set) (X5 :: ('b, 'a) Term.term set).
    epred5_5 X5 X3 X4 X1 X2 \<longleftrightarrow> \<not> (X3 \<in> X4 \<longrightarrow> True)"
(* thf(c_0_5, plain,
![X1:a > term_b_a, X2:set_a_term_b_a, X3:a > term_b_a, X4:set_a_term_b_a, X5:set_a_term_b_a]:
  (((epred5_5 @ X5 @ X3 @ X4 @ X1 @ X2)<=>
  (~(member_a_term_b_a @ X3 @ X4)=>
    (((insert_a_term_b_a @ X1 @ X2)=(insert_a_term_b_a @ X3 @ X4))<=>
      ((((X1)!=(X3))|(((X2)=(X4))))&
        (((X1)=(X3))|((~((((X2)=(insert_a_term_b_a @ X3 @ X5))&
          (~(member_a_term_b_a @ X3 @ X5)&
          (((X4)=(insert_a_term_b_a @ X1 @ X5))&~(member_a_term_b_a @ X1 @ X5)))))
          |(?[X5:set_a_term_b_a]:($true)))&
      ((((X2)=(insert_a_term_b_a @ X3 @ X5))&
      (~(member_a_term_b_a @ X3 @ X5)&
        (((X4)=(insert_a_term_b_a @ X1 @ X5))&~(member_a_term_b_a @ X1 @ X5))))|
        (?[X5:set_a_term_b_a]:($false)))))))))), introduced(definition)). *)
  show False
  using insert_eq_iff mk_disjoint_insert subst_monoid_mult.mult.right_neutral
  (* sledgehammer [e, slices = 1, dont_minimize, isar_proof, compress = 1, timeout = 30, preplay_timeout = 10, overlord] (insert_eq_iff mk_disjoint_insert subst_monoid_mult.mult.right_neutral) *)
  (* by (metis insert_eq_iff mk_disjoint_insert subst_monoid_mult.mult.right_neutral) *)
  using ex_in_conv insertI1 insert_absorb insert_commute insert_eq_iff insert_iff
    insert_not_empty is_mgu_def mk_disjoint_insert subst_monoid_mult.mult.right_neutral
  (* by (smt (verit) ex_in_conv insertI1 insert_absorb insert_commute insert_eq_iff insert_iff
      insert_not_empty is_mgu_def mk_disjoint_insert subst_monoid_mult.mult.right_neutral) *) *)

lemma "is_renaming (Var(x := Var x'))"
proof (unfold is_renaming_def, intro conjI allI)
  fix y show "is_Var ((Var(x := Var x')) y)"
    by simp
next
  show "inj_on (Var(x := Var x')) (subst_domain (Var(x := Var x')))"
    apply (rule inj_onI)
    apply (simp add: subst_domain_def)
    by presburger
qed

lemma zip_option_same: "zip_option xs xs = Some (zip xs xs)"
  by (induction xs)  (simp_all add: zip_option.simps)

lemma decompose_same:
  "\<And>f. decompose (Fun f ss) (Fun f ss) = Some (zip ss ss)"
  by (simp add: decompose_def zip_option_same)

lemma unify_append_eq_unify_if_prefix_same:
  "(\<forall>e \<in> set es1. fst e = snd e) \<Longrightarrow> unify (es1 @ es2) bs = unify es2 bs"
proof (induction "es1 @ es2" bs arbitrary: es1 es2 bs rule: unify.induct)
  case (1 bs)
  thus ?case by simp
next
  case (2 f ss g ts E bs)
  show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Fun f ss, Fun g ts)" and E_def: "E = es1' @ es2"
      using "2" by simp_all
    hence "f = g" and "ss = ts"
      using "2.prems" local.Cons by auto
    then show ?thesis
      apply (simp add: Cons e_def decompose_same)
      apply (rule "2"(1)[of _ "zip ts ts @ es1'" es2, simplified])
      apply simp
        apply (rule decompose_same)
      unfolding E_def apply simp
      by (metis "2.prems" UnE in_set_zip list.set_intros(2) local.Cons)
    qed
next
  case (3 x t E bs)
  show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Var x, t)" and E_def: "E = es1' @ es2"
      using 3 by simp_all
    show ?thesis
    proof (cases "t = Var x")
      case True
      show ?thesis
        using 3(1)[OF True E_def]
        using "3.hyps"(3) "3.prems" local.Cons by fastforce
    next
      case False
      then show ?thesis
        using "3.prems" e_def local.Cons by force
    qed
  qed
next
  case (4 v va x E bs)
  then show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Fun v va, Var x)" and E_def: "E = es1' @ es2"
      using 4 by simp_all
    then show ?thesis
      using "4.prems" local.Cons by fastforce
  qed
qed

lemma unify_eq_Some_if_same:
  "(\<forall>e \<in> set es. fst e = snd e) \<Longrightarrow> unify es bs = Some bs"
  by (rule unify_append_eq_unify_if_prefix_same[of _ "[]", simplified])

lemma mgu_same: "Unification.mgu t t = Some Var"
  unfolding Unification.mgu.simps
  unfolding unify_eq_Some_if_same[of "[(t, t)]" for t, simplified]
  by simp



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

lemma is_ground_lit_iff_vars_empty: "is_ground_lit L \<longleftrightarrow> vars_lit L = {}"
  by (simp add: is_ground_atm_iff_vars_empty is_ground_lit_def)

lemma is_ground_cls_iff_vars_empty: "is_ground_cls C \<longleftrightarrow> vars_cls C = {}"
  by (auto simp: is_ground_cls_def is_ground_lit_iff_vars_empty vars_cls_def)

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

lemma restrict_subst_empty[simp]: "restrict_subst {} \<sigma> = Var"
  unfolding restrict_subst_def by auto

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

lemma rename_clause_mempty[simp]: "rename_clause N {#} = {#}"
  by (simp add: rename_clause_def)

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

lemma suffix_trail_propagate[simp]: "suffix \<Gamma> (trail_propagate \<Gamma> L C \<delta>)"
  unfolding suffix_def trail_propagate_def
  by simp

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

lemma trail_backtrack_propagate[simp]:
  "trail_backtrack (trail_propagate \<Gamma> L C \<gamma>) n = trail_backtrack \<Gamma> n"
  by (simp add: trail_propagate_def is_decision_lit_def)

definition trail_interp :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term interp" where
  "trail_interp \<Gamma> = \<Union>((\<lambda>L. case L of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) ` fst ` set \<Gamma>)"

primrec trail_grounding :: "('f, 'v) trail \<Rightarrow> ('f, 'v) subst" where
  "trail_grounding [] = (Var :: ('f, 'v) subst)" |
  "trail_grounding (Ln # \<Gamma>) = (case snd Ln of None \<Rightarrow> Var | Some _ \<Rightarrow> Var) \<odot> trail_grounding \<Gamma>"

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

definition trail_defined_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_defined_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_defined_lit \<Gamma> L)"

lemma trail_defined_lit_iff_true_or_false:
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> trail_true_lit \<Gamma> L \<or> trail_false_lit \<Gamma> L"
  unfolding trail_defined_lit_def trail_false_lit_def trail_true_lit_def by (rule refl)

lemma trail_false_cls_mempty[simp]: "trail_false_cls \<Gamma> {#}"
  by (simp add: trail_false_cls_def)

lemma not_trail_true_Nil[simp]:
  "\<not> trail_true_lit [] L"
  "\<not> trail_true_cls [] C"
  "N \<noteq> {} \<Longrightarrow> \<not> trail_true_clss [] N"
  by (simp_all add: trail_true_lit_def trail_true_cls_def trail_true_clss_def)

lemma not_trail_false_Nil[simp]:
  "\<not> trail_false_lit [] L"
  "C \<noteq> {#} \<Longrightarrow> \<not> trail_false_cls [] C"
  by (simp_all add: trail_false_lit_def trail_false_cls_def)

lemma ball_trail_backtrackI:
  assumes "\<forall>x \<in> set \<Gamma>. P (fst x)"
  shows "\<forall>x \<in> set (trail_backtrack \<Gamma> i). P (fst x)"
  using assms trail_backtrack_suffix[THEN set_mono_suffix]
  by blast

lemma trail_false_lit_if_trail_false_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_false_lit \<Gamma>' K \<Longrightarrow> trail_false_lit \<Gamma> K"
  by (meson image_mono set_mono_suffix subsetD trail_false_lit_def)

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

lemma trail_false_cls_subst_mgu_before_grounding:
  assumes tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    mgu_L_L': "Unifiers.is_imgu \<mu> {(atm_of L, atm_of L')}" and
    \<sigma>_unif: "\<sigma> \<in> Unifiers.unifiers {(atm_of L, atm_of L')}"
  shows "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix K
  assume "K \<in># (D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>"
  hence "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<or> K = L  \<cdot>l \<mu> \<cdot>l \<sigma>" by force
  thus "trail_false_lit \<Gamma> K"
  proof (elim disjE)
    show "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
      using mgu_L_L' \<sigma>_unif
      by (metis Unifiers.is_imgu_def subst_cls_comp_subst subst_cls_union tr_false_cls
          trail_false_cls_def union_iff)
  next
    have "L \<cdot>l \<mu> \<cdot>l \<sigma> = L \<cdot>l \<sigma>"
      using mgu_L_L' \<sigma>_unif
      unfolding Unifiers.is_imgu_def
      by (metis subst_lit_comp_subst)
    thus "K = L \<cdot>l \<mu> \<cdot>l \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
      by (auto intro: tr_false_cls[unfolded trail_false_cls_def, rule_format])
  qed
qed


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

lemma ball_ground_lit_if_sound_trail: "sound_trail N U \<Gamma> \<Longrightarrow> \<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  show ?case by simp
next
  case (Cons \<Gamma> L u)
  thus ?case by auto
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
    show ?thesis
      unfolding \<sigma>'_def
      using subst_cls_restrict_subst_idem
      using trail_false_cls_subst_mgu_before_grounding[OF tr_false_cls mgu_sound[OF mgu_L_L'] \<sigma>_unif]
      by (metis subsetI)
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


lemma trail_false_cls_plus_subst_mgu_before_groundings:
  assumes
    tr_false_\<Gamma>_D_L'_\<sigma>: "trail_false_cls \<Gamma> ((D + {#L'#}) \<cdot> \<sigma>)" and
    tr_false_\<Gamma>'_C_\<delta>: "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)" and
    "suffix \<Gamma>' \<Gamma>" and
    gr_D_L'_\<sigma>: "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)" and
    vars_D_L'_vars_C_L_disj: "vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}" and
    dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})" and
    is_imgu_\<mu>: "Unifiers.is_imgu \<mu> {(atm_of L, atm_of L')}" and
    \<sigma>_\<delta>_in_unif: "\<sigma> \<odot> \<delta> \<in> unifiers {(atm_of L, atm_of L')}"
  shows "trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
  unfolding subst_cls_union trail_false_cls_def
proof (rule ballI)
  fix K
  assume "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta> + C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
  thus "trail_false_lit \<Gamma> K"
    unfolding union_iff
  proof (elim disjE)
    assume K_in: "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
    hence "K \<in># D \<cdot> \<sigma> \<cdot> \<delta>"
      using is_imgu_\<mu> \<sigma>_\<delta>_in_unif
      by (metis Unifiers.is_imgu_def subst_cls_comp_subst)
    hence "K \<in># D \<cdot> \<sigma>"
      using gr_D_L'_\<sigma> is_ground_subst_cls by (metis is_ground_cls_union subst_cls_union)
    then show ?thesis
      by (auto intro!: tr_false_\<Gamma>_D_L'_\<sigma>[unfolded trail_false_cls_def, rule_format])
  next
    assume "K \<in># C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
    hence "K \<in># C \<cdot> \<sigma> \<cdot> \<delta>"
      using is_imgu_\<mu> \<sigma>_\<delta>_in_unif
      by (metis Unifiers.is_imgu_def subst_cls_comp_subst)
    have "K \<in># C \<cdot> \<delta>"
    proof -
      have "subst_domain \<sigma> \<inter> vars_cls C = {}"
        using dom_\<sigma> vars_D_L'_vars_C_L_disj
        by auto
      thus ?thesis
        using \<open>K \<in># C \<cdot> \<sigma> \<cdot> \<delta>\<close> subst_cls_idem_if_disj_vars[of \<sigma> C] by simp
    qed
    hence tr_false_\<Gamma>'_K:"trail_false_lit \<Gamma>' K"
      using tr_false_\<Gamma>'_C_\<delta>[unfolded trail_false_cls_def, rule_format, of K] by simp
    show ?thesis
      by (rule trail_false_lit_if_trail_false_suffix[OF \<open>suffix \<Gamma>' \<Gamma>\<close> tr_false_\<Gamma>'_K])
  qed
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

  have \<sigma>_\<delta>_in_unif: "\<sigma> \<odot> \<delta> \<in> unifiers {(atm_of L, atm_of L')}"
  proof (rule subst_comp_in_unifiersI')
    show "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
      using L_eq_comp_L' by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
  next
    show "vars_lit L \<inter> subst_domain \<sigma> = {}"
      using dom_\<sigma> vars_D_L'_vars_C_L_disj by auto
  next
    show "vars_lit L' \<inter> subst_domain \<delta> = {}"
      using dom_\<delta> vars_D_L'_vars_C_L_disj by auto
  next
    have "range_vars \<sigma> = {}"
      unfolding range_vars_def UNION_empty_conv subst_range.simps
      using dom_\<sigma> gr_D_L'_\<sigma> is_ground_cls_is_ground_on_var is_ground_atm_iff_vars_empty
      by fast
    thus "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
      by simp
  qed

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
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_\<delta>_in_unif mgu_sound[OF mgu_L_L']
          subst_cls_comp_subst)
    thus "is_ground_cls (D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  next
    from gr_C_L_\<delta> have "is_ground_cls ((C + {#L#}) \<cdot> \<sigma> \<cdot> \<delta>)"
      using subst_cls_idem_if_disj_vars[of \<sigma> C]
      using dom_\<sigma> vars_D_L'_vars_C_L_disj
      by (smt (verit, best) Int_assoc inf.orderE inf_bot_right subst_cls_idem_if_disj_vars)
    hence "is_ground_cls ((C + {#L#}) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_\<delta>_in_unif mgu_sound[OF mgu_L_L']
          subst_cls_comp_subst)
    thus "is_ground_cls (C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  qed

  moreover have "trail_false_cls \<Gamma>
    ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
    unfolding subst_cls_restrict_subst_idem[OF subset_refl]
    unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
  proof -
    have tr_false_cls_C: "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
      using sound_\<Gamma>
      unfolding sound_trail.simps[of _ _ \<Gamma>]
      unfolding \<Gamma>_def trail_propagate_def
      by simp

    show "trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
    proof (rule trail_false_cls_plus_subst_mgu_before_groundings[OF tr_false_cls tr_false_cls_C _
          gr_D_L'_\<sigma> vars_D_L'_vars_C_L_disj dom_\<sigma> mgu_sound[OF mgu_L_L'] \<sigma>_\<delta>_in_unif])
      show "suffix \<Gamma>' \<Gamma>"
        by (simp add: \<Gamma>_def suffix_ConsI trail_propagate_def)
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

lemma assumes "sound_state N S" and "conflict N S S'"
  shows "(\<exists>\<gamma>. state_conflict S' = Some ({#}, \<gamma>)) \<or> (\<exists>S''. backtrack N S' S'')"
proof -
  from \<open>conflict N S S'\<close> obtain D U D' \<Gamma> \<sigma> where
       "S = (\<Gamma>, U, None)" and
       S'_def: "S' = (\<Gamma>, U, Some (D', \<sigma>))" and
       "D \<in> N \<union> U"
       "D' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D"
       "subst_domain \<sigma> \<subseteq> vars_cls D'"
       "is_ground_cls (D' \<cdot> \<sigma>)"
       "trail_false_cls \<Gamma> (D' \<cdot> \<sigma>)"
    by (auto elim: conflict.cases)

  then show ?thesis
  proof (cases "D' = {#}")
    assume "D' = {#}"
    with S'_def show ?thesis by simp
  next
    assume "D' \<noteq> {#}"
    then obtain D'' L where "D' = D'' + {#L#}"
      by (metis add_mset_add_single multi_nonempty_split)
    have "(\<exists>S''. backtrack N S' S'')"
      unfolding S'_def \<open>D' = D'' + {#L#}\<close>
    proof (rule exI)
      show "backtrack N (\<Gamma>, U, Some (D'' + {#L#}, \<sigma>))
        (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D'' \<cdot> \<sigma>)), U \<union> {D'' + {#L#}}, None)"
        apply (rule backtrackI)
        
        sorry
    qed
    thus ?thesis ..
  qed
  oops


section \<open>Reasonable And Regular Runs\<close>

definition reasonable_scl where
  "reasonable_scl N S S' \<longleftrightarrow> scl N S S' \<and> (decide N S S' \<longrightarrow> \<not>(\<exists>S''. conflict N S' S''))"

lemma scl_if_reasonable: "reasonable_scl N S S' \<Longrightarrow> scl N S S'"
  unfolding reasonable_scl_def scl_def by simp

definition regular_scl where
  "regular_scl N S S' \<longleftrightarrow> conflict N S S' \<or> \<not> conflict N S S' \<and> reasonable_scl N S S'"

context
  fixes a b c d e f g :: "('f, 'v) term"
  assumes distinct_terms: "distinct [a, b, c, d, e, f, g]" and
    ball_is_ground_atm: "\<forall>t \<in> {a, b, c, d, e, f, g}. is_ground_atm t"
begin

private definition C1 where
  "C1 = {#Neg a, Pos b#}"

private definition C2 where
  "C2 = {#Neg a, Pos c#}"

private definition C3 where
  "C3 = {#Neg b, Pos d#}"

private definition C4 where
  "C4 = {#Neg c, Neg d#}"

private definition C5 where
  "C5 = {#Pos e, Pos f, Pos g#}"

private definition N where
  "N = {C1, C2, C3, C4, C5}"


lemma ball_is_ground_cls: "\<forall>C \<in> N. is_ground_cls C"
  using ball_is_ground_atm
  by (simp add: N_def C1_def C2_def C3_def C4_def C5_def is_ground_cls_def is_ground_lit_def)

lemma rename_clause_ident_if_ground[simp]:
  fixes N C
  shows "is_ground_cls C \<Longrightarrow> rename_clause N C = C"
  by (simp add: rename_clause_def)

lemma is_ground_lit_Pos[simp]: "is_ground_atm L \<Longrightarrow> is_ground_lit (Pos L)"
  by (simp add: is_ground_lit_def)

lemma is_ground_lit_Neg[simp]: "is_ground_atm L \<Longrightarrow> is_ground_lit (Neg L)"
  by (simp add: is_ground_lit_def)


private definition S1 where
  "S1 = ([(Pos a, None)], {}, None)"

lemma "regular_scl N initial_state S1"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N initial_state S1"
    unfolding S1_def
    by (simp add: conflict.simps)
next
  have "decide N initial_state (trail_decide [] (Pos a), {}, None)"
    by (rule decideI)
      (simp_all add: ball_is_ground_atm is_ground_lit_def trail_defined_lit_iff_true_or_false)
  hence "scl N initial_state (trail_decide [] (Pos a), {}, None)"
    by (simp add: scl_def)
  moreover have "\<nexists>S. conflict N (trail_decide [] (Pos a), {}, None) S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp: N_def C1_def C2_def C3_def C4_def C5_def
        trail_decide_def trail_false_cls_def trail_false_lit_def)
  ultimately show "reasonable_scl N initial_state S1"
    unfolding reasonable_scl_def by (simp add: S1_def trail_decide_def)
qed


private definition S2 where
  "S2 = ([
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S1 S2"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S1 S2"
    unfolding S1_def S2_def
    by (simp add: conflict.simps)
next
  have "decide N S1 S2"
    unfolding S1_def S2_def
    using distinct_terms ball_is_ground_atm
    by (auto simp: decide.simps trail_decide_def trail_defined_lit_def)
  hence "scl N S1 S2"
    unfolding scl_def by simp
  moreover have "\<nexists>S. conflict N S2 S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp add: N_def S2_def C1_def C2_def C3_def C4_def C5_def trail_false_cls_def
        trail_false_lit_def)
  ultimately show "reasonable_scl N S1 S2"
    unfolding reasonable_scl_def by simp
qed


private definition S3 :: "('f, 'v) state" where
  "S3 = ([
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S2 S3"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S2 S3"
    unfolding S2_def S3_def
    by (simp add: conflict.simps)
next
  have "propagate N S2 S3"
    unfolding S2_def S3_def
    unfolding propagate.simps
    apply (rule exI[of _ C1])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C1_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  hence "scl N S2 S3"
    unfolding scl_def by simp
  moreover have "\<nexists>S. conflict N S3 S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp add: N_def S3_def C1_def C2_def C3_def C4_def C5_def trail_false_cls_def
        trail_false_lit_def)
  ultimately show "reasonable_scl N S2 S3"
    unfolding reasonable_scl_def by simp
qed


private definition S4 :: "('f, 'v) state" where
  "S4 = ([
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S3 S4"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S3 S4"
    unfolding S3_def S4_def
    by (simp add: conflict.simps)
next
  have "propagate N S3 S4"
    unfolding S3_def S4_def
    unfolding propagate.simps
    apply (rule exI[of _ C2])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C2_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  hence "scl N S3 S4"
    unfolding scl_def by simp
  moreover have "decide N S3 S4 \<Longrightarrow> \<nexists>S. conflict N S4 S"
    using \<open>propagate N S3 S4\<close> decide_well_defined(1) by blast
  ultimately show "reasonable_scl N S3 S4"
    unfolding reasonable_scl_def by simp
qed


private definition S5 :: "('f, 'v) state" where
  "S5 = ([
    (Pos d, Some ({#Neg b#}, Pos d, Var)),
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S4 S5"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S4 S5"
    unfolding S4_def S5_def
    by (simp add: conflict.simps)
next
  have "propagate N S4 S5"
    unfolding S4_def S5_def
    unfolding propagate.simps
    apply (rule exI[of _ C3])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C3_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  hence "scl N S4 S5"
    unfolding scl_def by simp
  moreover have "decide N S4 S5 \<Longrightarrow> \<nexists>S. conflict N S5 S"
    using \<open>propagate N S4 S5\<close> decide_well_defined(1) by blast
  ultimately show "reasonable_scl N S4 S5"
    unfolding reasonable_scl_def by simp
qed


private definition S6 :: "('f, 'v) state" where
  "S6 = ([
    (Pos d, Some ({#Neg b#}, Pos d, Var)),
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some (C4, Var))"

lemma "regular_scl N S5 S6"
proof (unfold regular_scl_def, rule disjI1)
  show "conflict N S5 S6"
    unfolding S5_def S6_def
    using ball_is_ground_cls
    apply (simp add: conflict.simps N_def)
    apply (rule exI[of _ C4])
    by (simp add: C4_def trail_false_cls_def trail_false_lit_def)
qed


definition S7 :: "('f, 'v) state" where
  "S7 = ([
    (Pos d, Some ({#Neg b#}, Pos d, Var)),
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg c, Neg b#}, Var))"

lemma "regular_scl N S6 S7"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S6 S7"
    unfolding S6_def S7_def
    by (simp add: conflict.simps)
next
  have "resolve N S6 S7"
    unfolding S6_def S7_def C4_def
    unfolding resolve.simps
    apply (rule exI[of _ "state_trail S6"])
    apply (rule exI[of _ "state_trail S4"])
    apply (rule exI[of _ "Pos d"])
    apply (rule exI[of _ "{#Neg b#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "{#Neg c#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "renaming_wrt
        (N \<union> clss_of_trail (state_trail S6) \<union>
         {{#Neg c#} + {#Neg d#}})"])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "Neg d"])
    apply (rule exI[of _ Var])
    apply (intro conjI)
          apply (simp add: S6_def)
         apply (simp add: S6_def)
         apply (rule conjI)
    using ball_is_ground_atm apply simp
    using ball_is_ground_atm apply (simp add: is_ground_atm_iff_vars_empty)
        apply (simp add: S4_def S6_def trail_propagate_def)
       apply (simp add: S6_def trail_propagate_def is_decision_lit_def trail_level_cls_def)
      apply simp
     apply simp
    by (simp del: Unification.mgu.simps add: mgu_same)
  hence "scl N S6 S7"
    unfolding scl_def by simp
  moreover have "decide N S6 S7 \<Longrightarrow> \<nexists>S. conflict N S7 S"
    using \<open>resolve N S6 S7\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S6 S7"
    unfolding reasonable_scl_def by simp
qed


definition S8 :: "('f, 'v) state" where
  "S8 = ([
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg c, Neg b#}, Var))"

lemma "regular_scl N S7 S8"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S7 S8"
    unfolding S7_def S8_def
    by (simp add: conflict.simps)
next
  have "skip N S7 S8"
    unfolding S7_def S8_def
    using distinct_terms
    by (auto simp add: skip.simps trail_propagate_def)
  hence "scl N S7 S8"
    unfolding scl_def by simp
  moreover have "decide N S7 S8 \<Longrightarrow> \<nexists>S. conflict N S8 S"
    using \<open>skip N S7 S8\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S7 S8"
    unfolding reasonable_scl_def by simp
qed


definition S9 :: "('f, 'v) state" where
  "S9 = ([
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg a, Neg b#}, Var))"

lemma "regular_scl N S8 S9"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S8 S9"
    unfolding S8_def S9_def
    by (simp add: conflict.simps)
next
  have "resolve N S8 S9"
    unfolding S8_def S9_def
    unfolding resolve.simps
    apply (rule exI[of _ "state_trail S4"])
    apply (rule exI[of _ "state_trail S3"])
    apply (rule exI[of _ "Pos c"])
    apply (rule exI[of _ "{#Neg a#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "{#Neg b#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "renaming_wrt
        (N \<union> clss_of_trail (state_trail S4) \<union>
         {{#Neg b#} + {#Neg c#}})"])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "Neg c"])
    apply (rule exI[of _ Var])
    apply (intro conjI)
          apply (simp add: S4_def)
    using ball_is_ground_atm apply (simp add: S4_def is_ground_atm_iff_vars_empty)
    by (simp_all del: Unification.mgu.simps
          add: S4_def S3_def trail_propagate_def is_decision_lit_def trail_level_cls_def mgu_same
          is_ground_atm_iff_vars_empty)
  hence "scl N S8 S9"
    unfolding scl_def by simp
  moreover have "decide N S8 S9 \<Longrightarrow> \<nexists>S. conflict N S9 S"
    using \<open>resolve N S8 S9\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S8 S9"
    unfolding reasonable_scl_def by simp
qed


definition S10 :: "('f, 'v) state" where
  "S10 = ([
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg a, Neg b#}, Var))"

lemma "regular_scl N S9 S10"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S9 S10"
    unfolding S9_def S10_def
    by (simp add: conflict.simps)
next
  have "skip N S9 S10"
    unfolding S9_def S10_def
    using distinct_terms
    by (auto simp add: skip.simps trail_propagate_def)
  hence "scl N S9 S10"
    unfolding scl_def by simp
  moreover have "decide N S9 S10 \<Longrightarrow> \<nexists>S. conflict N S10 S"
    using \<open>skip N S9 S10\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S9 S10"
    unfolding reasonable_scl_def by simp
qed


definition S11 :: "('f, 'v) state" where
  "S11 = ([(Pos a, None)], {{#Neg a, Neg b#}}, None)"

lemma "regular_scl N S10 S11"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S10 S11"
    unfolding S10_def S11_def
    by (simp add: conflict.simps)
next
  have "backtrack N S10 S11"
    unfolding S10_def S11_def
    unfolding backtrack.simps
    apply (rule exI[of _ "state_trail S3"])
    apply (rule exI[of _ "Neg b"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "{#Neg a#}"])
    using distinct_terms
    by (auto simp add: S3_def is_decision_lit_def trail_level_cls_def)
  hence "scl N S10 S11"
    unfolding scl_def by simp
  moreover have "decide N S10 S11 \<Longrightarrow> \<nexists>S. conflict N S11 S"
    using \<open>backtrack N S10 S11\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S10 S11"
    unfolding reasonable_scl_def by simp
qed

end

lemma reasonable_if_regular:
  "regular_scl N S S' \<Longrightarrow> reasonable_scl N S S'"
  unfolding regular_scl_def
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


lemma assumes "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and "conflict N S S'"
  shows "\<exists>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<and>
    (trail_level_cls (state_trail S) (C \<cdot> \<gamma>) = trail_level (state_trail S))"
  using \<open>conflict N S S'\<close>
proof (cases N S S' rule: conflict.cases)
  case (conflictI D U D' \<Gamma> \<gamma>)
  show ?thesis
  proof (intro exI conjI)
    show "state_conflict S' = Some (D', \<gamma>)"
      using conflictI by simp
  next
    show "trail_level_cls (state_trail S) (D' \<cdot> \<gamma>) = trail_level (state_trail S)"
    proof (cases "D' \<cdot> \<gamma>")
      case empty
      hence "D' = {#}"
        using subst_cls_empty_iff by blast
      hence "D = {#}"
        by (simp add: local.conflictI(4) rename_clause_def)
      hence "{#} \<in> N \<union> U" 
        using local.conflictI(3) by force
      then show ?thesis
        sorry
    next
      case (add x N)
      then show ?thesis sorry
    qed
    oops

lemma
  assumes "\<forall>C \<in> N. C \<noteq> {#}" and "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and "conflict N S S'"
  shows "\<exists>\<Gamma> L C \<gamma>. state_trail S = trail_propagate \<Gamma> L C \<gamma>"
  using assms(2,3)
proof (induction S rule: rtranclp_induct)
  case base
  then obtain D D'  \<sigma> where
       "D \<in> N" and "D' = rename_clause N D" and "trail_false_cls [] (D' \<cdot> \<sigma>)"
    by (auto elim: conflict.cases)

  from \<open>\<forall>C \<in> N. C \<noteq> {#}\<close> and \<open>D \<in> N\<close> have "D \<noteq> {#}"
    by simp
  hence "D' \<cdot> \<sigma> \<noteq> {#}"
    by (simp add: \<open>D' = rename_clause N D\<close> rename_clause_def)
  hence "\<not> trail_false_cls [] (D' \<cdot> \<sigma>)"
    by (rule not_trail_false_Nil(2))
  with \<open>trail_false_cls [] (D' \<cdot> \<sigma>)\<close> have False
    by simp
  thus ?case ..
next
  case (step S S'')
  from step.hyps have "regular_scl N S S''" by simp
  with \<open>conflict N S'' S'\<close> have "\<not> conflict N S S''" and "reasonable_scl N S S''"
    unfolding HOL.atomize_conj
    by (smt (verit, best) conflict.cases option.distinct(1) prod.inject reasonable_if_regular)
  hence "scl N S S''" and "decide N S S'' \<longrightarrow> \<not> (\<exists>S'''. conflict N S'' S''')"
    by (simp_all add: reasonable_scl_def)

  from \<open>scl N S S''\<close> show ?case
    unfolding scl_def
  proof (elim disjE)
    assume "propagate N S S''"
    thus ?thesis
      by (elim propagate.cases) auto
  next
    assume "decide N S S''"
    with \<open>conflict N S'' S'\<close> have False
      using \<open>decide N S S'' \<longrightarrow> \<not> (\<exists>S'''. conflict N S'' S''')\<close> by fast
    thus ?thesis ..
  next
    assume "conflict N S S''"
    with \<open>\<not> conflict N S S''\<close> have False ..
    thus ?thesis ..
  next
    assume "skip N S S''"
    with \<open>conflict N S'' S'\<close> have False
      by (elim skip.cases conflict.cases) simp
    thus ?thesis ..
  next
    assume "factorize N S S''"
    with \<open>conflict N S'' S'\<close> have False
      by (elim factorize.cases conflict.cases) simp
    thus ?thesis ..
  next
    assume "resolve N S S''"
    with \<open>conflict N S'' S'\<close> have False
      by (elim resolve.cases conflict.cases) simp
    thus ?thesis ..
  next
    assume "backtrack N S S''"
    then have False
      apply (elim backtrack.cases)
      sorry
    thus ?thesis ..
  qed
qed

lemma
  assumes "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and "conflict N S S'"
  shows "\<exists>S''. (\<lambda>S S'. skip N S S' \<or> factorize N S S')\<^sup>*\<^sup>* S' S'' \<and> resolve N S S'"
proof -  
  oops

lemma not_satisfiable_if_sound_state_conflict_bottom:
  assumes sound_S: "sound_state N S" and conflict_S: "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> satisfiable (grounding_of_clss N)"
proof -
  from sound_S conflict_S have "N \<TTurnstile>\<G>e {{#}}"
    unfolding sound_state_def state_conflict_def by auto
  thus ?thesis by simp
qed

lemma
  assumes sound: "sound_state N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>))"
  shows
    "(\<exists>S'. skip N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S') \<or>
    (\<exists>S'. factorize N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S') \<or>
    (\<exists>S'. resolve N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S') \<or>
    (\<exists>S'. backtrack N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S')"
proof (cases \<Gamma>)
  case Nil
  from sound have "trail_false_cls \<Gamma> ((C' + {#L#}) \<cdot> \<gamma>)"
    by (simp add: sound_state_def)
  hence "trail_false_lit \<Gamma> (L \<cdot>l \<gamma>)"
    by (simp add: trail_false_cls_def)
  hence False
    unfolding trail_false_lit_def Nil by simp
  thus ?thesis
    by simp
next
  case (Cons Ln \<Gamma>')
  then obtain L n where Ln_def: "Ln = (L, n)" by force
  show ?thesis
  proof (cases n)
    case None
    show ?thesis
      unfolding Cons Ln_def None
      apply (simp add: skip.simps trail_propagate_def resolve.simps)
      unfolding backtrack.simps
      apply (simp add: is_decision_lit_def)
      sorry
  next
    case (Some a)
    then show ?thesis sorry
  qed
  oops

lemma ball_trail_defined_lit_if:
  assumes
    no_conflict: "state_conflict S = None" and
    no_decide: "\<nexists>S'. decide N S S'"
  shows "\<forall>C \<in> N. \<forall>L \<in># C. \<forall>\<gamma>. is_ground_lit (L \<cdot>l \<gamma>) \<longrightarrow> trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
proof (intro ballI allI impI)
  fix C L \<gamma>
  assume "C \<in> N" "L \<in># C" "is_ground_lit (L \<cdot>l \<gamma>)"

  from no_conflict obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis prod_cases3 state_conflict_simp)

  show "trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
    using no_decide
  proof (rule contrapos_np)
    assume assm: "\<not> trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
    show "\<exists>S'. decide N S S'"
      using decideI[OF \<open>is_ground_lit (L \<cdot>l \<gamma>)\<close> assm]
      unfolding S_def state_trail_simp
      by fastforce
  qed
qed

lemma trail_defined_lit_iff: "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L \<in> atm_of ` fst ` set \<Gamma>"
  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_defined_lit_def)

lemma "trail_interp \<Gamma> \<subseteq> atm_of ` fst ` set \<Gamma>"
  by (smt (verit, best) UN_iff image_iff insert_iff literal.case_eq_if singletonD subsetI trail_interp_def)

lemma set_filter_insert_conv:
  "{x \<in> insert y S. P x} = (if P y then insert y else id) {x \<in> S. P x}"
  by auto

lemma trail_interp_conv: "trail_interp \<Gamma> = atm_of ` {L \<in> fst ` set \<Gamma>. is_pos L}"
proof (induction \<Gamma>)
  case Nil
  show ?case by (simp add: trail_interp_def)
next
  case (Cons Ln \<Gamma>)
  then show ?case
    unfolding list.set image_insert set_filter_insert_conv trail_interp_Cons'
    by (simp add: literal.case_eq_if)
qed

lemma not_in_trail_interp_if_not_in_trail: "t \<notin> atm_of ` fst ` set \<Gamma> \<Longrightarrow> t \<notin> trail_interp \<Gamma>"
  by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
      literal.sel(2) mem_Collect_eq trail_interp_conv)

lemma trail_interp_lit_if_sound_and_trail_true:
  shows "sound_trail N U \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma> L \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile>l L"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  thus ?case
    by (simp add: trail_true_lit_def)
next
  case (Cons \<Gamma> K u)
  show ?case
  proof (cases "L = K \<or> L = - K")
    case True
    then show ?thesis 
    proof (elim disjE)
      assume "L = K"
      thus ?thesis
      proof (cases L; cases K)
        fix t\<^sub>L t\<^sub>K
        from \<open>L = K\<close> show "L = Pos t\<^sub>L \<Longrightarrow> K = Pos t\<^sub>K \<Longrightarrow> ?thesis"
          by (simp add: trail_interp_def)
      next
        fix t\<^sub>L t\<^sub>K
        from \<open>L = K\<close> show "L = Neg t\<^sub>L \<Longrightarrow> K = Neg t\<^sub>K \<Longrightarrow> ?thesis"
          using Cons.hyps
          by (simp add: trail_defined_lit_iff trail_interp_Cons'
              not_in_trail_interp_if_not_in_trail)
      qed simp_all
    next
      assume "L = - K"
      then show ?thesis
      proof (cases L; cases K)
        fix t\<^sub>L t\<^sub>K
        from \<open>L = - K\<close> show "L = Pos t\<^sub>L \<Longrightarrow> K = Neg t\<^sub>K \<Longrightarrow> ?thesis"
          unfolding trail_interp_Cons'
          using Cons.hyps(1) Cons.prems
          by (metis (no_types, lifting) image_insert insertE list.simps(15) literal.distinct(1)
              prod.sel(1) trail_defined_lit_def trail_true_lit_def)
      next
        fix t\<^sub>L t\<^sub>K
        from \<open>L = - K\<close> show "L = Neg t\<^sub>L \<Longrightarrow> K = Pos t\<^sub>K \<Longrightarrow> ?thesis"
          unfolding trail_interp_Cons'
          using Cons.hyps(1) Cons.prems
          by (metis (no_types, lifting) image_insert insertE list.simps(15) literal.distinct(1)
              prod.sel(1) trail_defined_lit_def trail_true_lit_def)
      qed simp_all
    qed
  next
    case False
    with Cons.prems have "trail_true_lit \<Gamma> L"
      by (simp add: trail_true_lit_def)
    with Cons.IH have "trail_interp \<Gamma> \<TTurnstile>l L"
      by simp
    with False show ?thesis
      by (cases L; cases K) (simp_all add: trail_interp_def del: true_lit_iff)
  qed
qed

lemma trail_interp_cls_if_sound_and_trail_true:
  assumes "sound_trail N U \<Gamma>" and "trail_true_cls \<Gamma> C"
  shows "trail_interp \<Gamma> \<TTurnstile> C"
proof -
  from \<open>trail_true_cls \<Gamma> C\<close> obtain L where "L \<in># C" and "trail_true_lit \<Gamma> L"
    by (auto simp: trail_true_cls_def)
  show ?thesis
    unfolding true_cls_def
  proof (rule bexI[OF _ \<open>L \<in># C\<close>])
    show "trail_interp \<Gamma> \<TTurnstile>l L"
      by (rule trail_interp_lit_if_sound_and_trail_true[OF \<open>sound_trail N U \<Gamma>\<close> \<open>trail_true_lit \<Gamma> L\<close>])
  qed
qed

lemma set_removeAll_mset: "set_mset (removeAll_mset x M) = set_mset M - {x}"
  by simp

lemma trail_true_lit_Cons_iff: "trail_true_lit ((L, u) # \<Gamma>) K \<longleftrightarrow> L = K \<or> trail_true_lit \<Gamma> K"
  by (auto simp: trail_true_lit_def)

lemma trail_true_cls_Cons_iff: "trail_true_cls ((L, u) # \<Gamma>) C \<longleftrightarrow> L \<in># C \<or> trail_true_cls \<Gamma> C"
  by (auto simp: trail_true_cls_def trail_true_lit_Cons_iff)

lemma trail_true_cls_iff_trail_interp_entails:
  assumes "sound_trail N U \<Gamma>" "\<forall>L \<in># C. trail_defined_lit \<Gamma> L"
  shows "trail_true_cls \<Gamma> C \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
proof (rule iffI)
  assume "trail_true_cls \<Gamma> C"
  thus "trail_interp \<Gamma> \<TTurnstile> C"
    using assms(1) trail_interp_cls_if_sound_and_trail_true by blast
next
  assume "trail_interp \<Gamma> \<TTurnstile> C"
  then obtain L where "L \<in># C" and "trail_interp \<Gamma> \<TTurnstile>l L"
    by (auto simp: true_cls_def)
  show "trail_true_cls \<Gamma> C"
  proof (cases L)
    case (Pos t)
    hence "t \<in> trail_interp \<Gamma>"
      using \<open>trail_interp \<Gamma> \<TTurnstile>l L\<close> by simp
    then show ?thesis
      unfolding trail_true_cls_def
      using \<open>L \<in># C\<close> Pos
      by (metis assms(1) assms(2) trail_defined_lit_def trail_interp_lit_if_sound_and_trail_true
          trail_true_lit_def true_lit_simps(2) uminus_Pos)
  next
    case (Neg t)
    then show ?thesis
      by (metis \<open>L \<in># C\<close> \<open>trail_interp \<Gamma> \<TTurnstile>l L\<close> assms(1) assms(2) trail_defined_lit_def
          trail_interp_lit_if_sound_and_trail_true trail_true_cls_def trail_true_lit_def
          true_lit_simps(1) true_lit_simps(2) uminus_Neg)
  qed
qed

lemma trail_interp_clss_if_sound_and_trail_true:
  assumes "sound_trail N U \<Gamma>" and "trail_true_clss \<Gamma> CC"
  shows "trail_interp \<Gamma> \<TTurnstile>s CC"
  using \<open>trail_true_clss \<Gamma> CC\<close> trail_interp_cls_if_sound_and_trail_true[OF \<open>sound_trail N U \<Gamma>\<close>]
  by (simp add: trail_true_clss_def true_clss_def)

lemma
  assumes
    fin_N: "finite N" and disj_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and
    no_more_regular_step: "\<nexists>S'. regular_scl N S S'"
  shows "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
  (\<exists>\<gamma>. trail_true_clss (state_trail S) (N \<cdot>cs \<gamma>))"
proof -
  obtain \<Gamma> U u where S_def: "S = (\<Gamma>, U, u)"
    using prod_cases3 by blast

  have sound_S: "sound_state N S"
    using regular_run_sound_state[OF regular_run] sound_initial_state[OF fin_N disj_N] by blast

  from no_more_regular_step have no_new_conflict: "\<nexists>S'. conflict N S S'"
    using regular_scl_def by blast

  from no_more_regular_step have no_propagate: "\<nexists>S'. propagate N S S'"
    by (meson decide_well_defined(1) local.scl_def reasonable_scl_def regular_scl_def)

  from no_more_regular_step have
    no_reasonable_decide: "(\<nexists>S'. decide N S S') \<or> (\<exists>S' S''. decide N S S' \<and> conflict N S' S'')"
    using local.scl_def reasonable_scl_def regular_scl_def by blast

  show ?thesis
  proof (cases u)
    case None
    hence "state_conflict S = None"
      by (simp add: S_def)
    
    have ball_N_not_empty: "\<forall>C \<in> N. C \<noteq> {#}" sorry

    have "satisfiable (grounding_of_clss N)"
      using trail_interp_clss_if_sound_and_trail_true[OF ]
      (* using sound_S[unfolded S_def None] *)
      apply (rule exI[where x = "trail_interp \<Gamma>"])
      unfolding true_clss_def true_cls_def grounding_of_clss_def grounding_of_cls_def
      unfolding imp_ex ball_UN ball_simps
            
      unfolding sound_state_def
      sorry
    moreover have "\<exists>\<gamma>. trail_true_clss \<Gamma> (N \<cdot>cs \<gamma>)"
      using no_more_regular_step
      unfolding S_def[unfolded None]
      unfolding regular_scl_def
      sorry
    ultimately show ?thesis
      unfolding S_def[unfolded None] state_trail_def state_conflict_def prod.sel
      by simp
  next
    case (Some Cl)
    then obtain C \<gamma> where u_def: "u = Some (C, \<gamma>)" by force
    show ?thesis
    proof (cases "C = {#}")
      case True
      hence "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>))"
        using S_def u_def not_satisfiable_if_sound_state_conflict_bottom[OF sound_S] by simp
      thus ?thesis by simp
    next
      case False
      then obtain L C' where C_def: "C = C' + {#L#}"
        by (metis add_mset_add_single multi_nonempty_split)

      from no_more_regular_step have "\<nexists>S'. (reasonable_scl N)\<^sup>+\<^sup>+ (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S'"
        unfolding S_def u_def C_def
        unfolding regular_scl_def
        sorry

      then have False
        unfolding reasonable_scl_def
        sorry

      then show ?thesis by simp
    qed
  qed
  oops

section \<open>Clause Redundancy\<close>

term is_ground_clss

definition ground_redundant where
  "ground_redundant lt N C \<longleftrightarrow> is_ground_clss N \<and> is_ground_cls C \<and> {D \<in> N. lt\<^sup>=\<^sup>= D C} \<TTurnstile>e {C}"

definition redundant where
  "redundant lt N C \<longleftrightarrow> (\<forall>C' \<in> grounding_of_cls C. ground_redundant lt (grounding_of_clss N) C')"


section \<open>Trail-Induced Ordering\<close>

subsection \<open>Miscellaneous Lemmas\<close>

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


subsection \<open>Strict Partial Order\<close>

lemma irreflp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> irreflp (trail_less (map fst \<Gamma>))"
  using irreflp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma transp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> transp (trail_less (map fst \<Gamma>))"
  using transp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> asymp (trail_less (map fst \<Gamma>))"
  using asymp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Extension on All Literals\<close>

lemma transp_trail_less_ex_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> transp lt \<Longrightarrow> transp (trail_less_ex lt (map fst \<Gamma>))"
  using transp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_ex_if_sound:
  "sound_trail N U \<Gamma> \<Longrightarrow> asymp lt \<Longrightarrow> asymp (trail_less_ex lt (map fst \<Gamma>))"
  using asymp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Properties\<close>

lemma trail_defined_if_trail_less_ex:
  "trail_less_ex lt (map fst \<Gamma>) L K \<Longrightarrow> trail_defined_lit \<Gamma> K \<Longrightarrow> trail_defined_lit \<Gamma> L"
  by (metis (no_types, opaque_lifting) list.set_map trail_defined_lit_def trail_less_ex_def)

lemma trail_defined_cls_if_lt_defined:
  assumes sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    transp_lt: "transp lt" and
    total_on_lt: "Restricted_Predicates.total_on lt (set_mset C \<union> set_mset D)" and
    C_lt_D: "multp (trail_less_ex lt (map fst \<Gamma>)) C D" and
    tr_def_D: "trail_defined_cls \<Gamma> D"
  shows "trail_defined_cls \<Gamma> C"
proof -
  have transp_on: "transp_on (trail_less_ex lt (map fst \<Gamma>)) S" for S
    using transp_trail_less_ex_if_sound[OF sound_\<Gamma> transp_lt]
    by (metis transpD transp_onI)

  have tot_on_C_D:
    "Restricted_Predicates.total_on (trail_less_ex lt (map fst \<Gamma>)) (set_mset C \<union> set_mset D)"
    using total_on_trail_less_ex[OF Clausal_Logic.uminus_of_uminus_id total_on_lt]
    by assumption

  show ?thesis
    using total_on_unionD[
        OF tot_on_C_D,
        THEN multiset_is_empty_or_bex_greatest_element_if_trans_and_total[OF transp_on]]
  proof (elim disjE)
    assume
      "\<exists>x\<in>#C. \<forall>y\<in>#C. x \<noteq> y \<longrightarrow> trail_less_ex lt (map fst \<Gamma>) y x"
      "D = {#}"
    thus "trail_defined_cls \<Gamma> C"
      using C_lt_D multp_implies_one_step sound_\<Gamma> transp_lt transp_trail_less_ex_if_sound
      by blast
  next
    assume
      "\<exists>x\<in>#C. \<forall>y\<in>#C. x \<noteq> y \<longrightarrow> trail_less_ex lt (map fst \<Gamma>) y x"
      "\<exists>x\<in>#D. \<forall>y\<in>#D. x \<noteq> y \<longrightarrow> trail_less_ex lt (map fst \<Gamma>) y x"
    show "trail_defined_cls \<Gamma> C"
      using tr_def_D trail_defined_if_trail_less_ex
      by (smt (verit, ccfv_threshold) C_lt_D multp_implies_one_step sound_\<Gamma> trail_defined_cls_def
          transp_lt transp_trail_less_ex_if_sound union_iff)
  qed (simp_all add: trail_defined_cls_def)
qed

section \<open>Learned Clauses in Regular Runs\<close>

term multp
term "multp (trail_less_ex lt (map fst \<Gamma>))"
term "redundant (multp (trail_less_ex lt (map fst \<Gamma>)))"

term "regular_scl N initial_state"

thm regular_scl_def
thm ground_redundant_def redundant_def

lemma
  assumes "sound_state N S" and "conflict N S S'"
  shows "redundant (multp (trail_less_ex lt (map fst (state_trail S))))
    (N \<union> state_learned S) (fst (the (state_conflict S')))"
proof -
  from \<open>conflict N S S'\<close> obtain \<Gamma> U C \<gamma> where
    S_def: "S = (\<Gamma>, U, None)" and S'_def: "S' = (\<Gamma>, U, Some (C, \<gamma>))"
    by (smt (verit) conflict.simps)

  from \<open>conflict N S S'\<close> obtain C' where
    "C' \<in> N \<union> U" and
    "C = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C'" and
    "subst_domain \<gamma> \<subseteq> vars_cls C" and
    "is_ground_cls (C \<cdot> \<gamma>)" and
    "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
    by (auto simp: S_def S'_def elim!: conflict.cases)

  then show ?thesis
    using assms(1)
    apply (simp add: S_def S'_def sound_state_def redundant_def ground_redundant_def
        grounding_of_cls_rename_clause is_ground_cls_if_in_grounding_of_cls)
    by (smt (verit, best) UN_I \<open>C' \<in> N \<union> U\<close> grounding_of_clss_def mem_Collect_eq true_clss_def)
qed

lemma assumes "asymp lt" and "transp lt" and "sound_state N S" and "resolve N S S'"
  shows "\<not> redundant (multp (trail_less_ex lt (map fst (state_trail S))))
    (N \<union> state_learned S) (fst (the (state_conflict S')))"
proof (rule notI)
  from \<open>resolve N S S'\<close> \<open>sound_state N S\<close> have "sound_state N S'"
    by (rule resolve_sound_state)

  from \<open>resolve N S S'\<close> obtain \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu> where
    S_def: "S = (\<Gamma>, U, Some (D + {#L'#}, \<sigma>))" and
    S'_def: "S' = (\<Gamma>, U, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>,
      restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)))" and
    "\<Gamma> = trail_propagate \<Gamma>' L C \<delta>" and
    "trail_level_cls \<Gamma> (D \<cdot> \<sigma>) = trail_level \<Gamma>" and
    "\<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}})" and
    "L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)" and
    "Unification.mgu (atm_of L) (atm_of L') = Some \<mu>"
    by (cases N S S' rule: resolve.cases) simp_all

  define \<gamma> where "\<gamma> = restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)"
  define lt' where "lt' = multp (trail_less_ex lt (map fst \<Gamma>))"

  from \<open>sound_state N S'\<close> have "sound_trail N U \<Gamma>" and "trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    by (simp_all add: sound_state_def S'_def \<gamma>_def)

  assume "redundant (multp (trail_less_ex lt (map fst (state_trail S))))
    (N \<union> state_learned S) (fst (the (state_conflict S')))"
  hence "redundant lt' (N \<union> U) ((D + C) \<cdot> \<mu> \<cdot> \<rho>)"
    by (simp add: S_def S'_def lt'_def)
  moreover from \<open>sound_state N S'\<close> have "is_ground_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    unfolding S'_def sound_state_def \<gamma>_def by simp
  ultimately have "ground_redundant lt' (grounding_of_clss (N \<union> U)) ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    unfolding redundant_def
    by (metis grounding_of_cls_ground insert_subset subst_cls_eq_grounding_of_cls_subset_eq)
  hence gr_entails_gr:
    "{E \<in> grounding_of_clss (N \<union> U). lt'\<^sup>=\<^sup>= E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)} \<TTurnstile>e {(D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>}"
    by (simp add: ground_redundant_def)

  have "E \<in> {E \<in> grounding_of_clss (N \<union> U). lt'\<^sup>=\<^sup>= E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)} \<Longrightarrow>
    trail_defined_lit \<Gamma> L" if "L \<in># E" for E L
    unfolding mem_Collect_eq Lattices.sup_apply sup_bool_def
  proof (elim conjE disjE)
    note trans = transp_trail_less_ex_if_sound[OF \<open>sound_trail N U \<Gamma>\<close> \<open>transp lt\<close>]

    assume "E \<in> grounding_of_clss (N \<union> U)" and "lt' E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    then show ?thesis
      using multiset_is_empty_or_bex_greatest_element_if_trans_and_total[OF ]
      using total_on_trail_less_ex
      sorry

    (* hence "multp\<^sub>H\<^sub>O (trail_less_ex lt (map fst \<Gamma>)) E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
      unfolding lt'_def
      using transp_trail_less_ex_if_sound[OF \<open>sound_trail N U \<Gamma>\<close> \<open>transp lt\<close>]
      using asymp_trail_less_ex_if_sound[OF \<open>sound_trail N U \<Gamma>\<close> \<open>asymp lt\<close>]
      by (simp add: multp_eq_multp\<^sub>H\<^sub>O)
    then show ?thesis
      unfolding multp\<^sub>H\<^sub>O_def
      using \<open>trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close>[unfolded trail_false_cls_def]
      using \<open>L \<in># E\<close>
      sorry *)
  next
    assume "E \<in> grounding_of_clss (N \<union> U)" and "E = (D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>"
    with that and \<open>trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close> show ?thesis
      using trail_defined_lit_iff_true_or_false trail_false_cls_def by blast
  qed

  obtain E where
    "E \<in> {E \<in> grounding_of_clss (N \<union> U). lt'\<^sup>=\<^sup>= E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)} \<and> trail_false_cls \<Gamma> E"
    sorry

  then show False
    using \<open>trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close>
    using gr_entails_gr[rule_format, of "trail_interp \<Gamma>"] contrapos_pp
    apply (simp add: \<open>is_ground_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close>)
    oops

lemma regular_run_if_skip_factorize_resolve_run:
  assumes "(\<lambda>S S'. skip N S S' \<or> factorize N S S' \<or> resolve N S S')\<^sup>*\<^sup>* S S'"
  shows "(regular_scl N)\<^sup>*\<^sup>* S S'"
  using assms
  by (smt (verit, ccfv_SIG) decide_well_defined(4) decide_well_defined(5) local.scl_def
      mono_rtranclp reasonable_scl_def regular_scl_def skip_well_defined(2))

lemma trail_false_conflict_after_skip:
  assumes
    conflict_S: "state_conflict S = Some (C, \<gamma>)" and
    false_C_\<gamma>: "trail_false_cls (state_trail S) (C \<cdot> \<gamma>)" and
    "skip N S S'"
  shows "state_conflict S' = Some (C, \<gamma>) \<and> trail_false_cls (state_trail S) (C \<cdot> \<gamma>)"
  using \<open>skip N S S'\<close>
proof (cases N S S' rule: skip.cases)
  case (skipI L \<delta> D \<sigma> \<Gamma> C U)
  then show ?thesis
    using conflict_S false_C_\<gamma>
    by (auto elim!: trail_false_cls_ConsD simp add: sound_state_def trail_propagate_def)
qed

lemma strict_suffix_trail_if_skip: "skip N S S' \<Longrightarrow> strict_suffix (state_trail S') (state_trail S)"
  by (auto simp: skip.simps strict_suffix_def suffix_def trail_propagate_def)

lemma eq_trail_if_factorize: "factorize N S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto simp: factorize.simps)

lemma eq_trail_if_resolve: "resolve N S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto simp: resolve.simps)

lemma not_trail_true_and_false_lit:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> (trail_true_lit \<Gamma> L \<and> trail_false_lit \<Gamma> L)"
  apply (simp add: trail_true_lit_def trail_false_lit_def)
  by (metis (no_types, lifting) in_set_conv_nth list.set_map pairwise_distinct_if_sound_trail
      uminus_not_id')

lemma not_trail_true_and_false_cls: "sound_trail N U \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
  using not_trail_true_and_false_lit
  by (metis trail_false_cls_def trail_true_cls_def)

lemma conflict_if_mempty_in_clause_set:
  assumes "{#} \<in> N" and "state_conflict S1 = None"
  shows "\<exists>S2. conflict N S1 S2 \<and> state_conflict S2 = Some ({#}, Var)"
proof -
  from \<open>state_conflict S1 = None\<close> obtain \<Gamma> U where S1_def: "S1 = (\<Gamma>, U, None)"
    by (metis prod.collapse state_conflict_def)

  show ?thesis
  proof (intro exI conjI)
    from \<open>{#} \<in> N\<close> show "conflict N S1 (\<Gamma>, U, Some ({#}, Var))"
      by (auto simp: S1_def conflict.simps)
  next
    show "state_conflict (\<Gamma>, U, Some ({#}, Var)) = Some ({#}, Var)"
      by simp
  qed
qed

definition trail_no_conflict where
  "trail_no_conflict N \<Gamma> \<longleftrightarrow> (\<nexists>C \<gamma>. C \<in> N \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>))"

lemma trail_no_conflict_union_iff:
  "trail_no_conflict (N1 \<union> N2) \<Gamma> \<longleftrightarrow> trail_no_conflict N1 \<Gamma> \<and> trail_no_conflict N2 \<Gamma>"
  unfolding trail_no_conflict_def by blast

lemma trail_no_conflict_initial_state:
  assumes "{#} \<notin> N"
  shows "trail_no_conflict (N \<union> state_learned initial_state) (state_trail initial_state)"
  unfolding trail_no_conflict_def
  apply simp
  by (metis assms not_trail_false_Nil(2) subst_cls_empty_iff)

definition trail_almost_no_conflict where
  "trail_almost_no_conflict N \<Gamma> \<longleftrightarrow> trail_no_conflict N (trail_backtrack \<Gamma> (trail_level \<Gamma>))"

lemma trail_false_cls_if_suffix_and_false:
  "suffix \<Gamma> \<Gamma>' \<Longrightarrow> trail_false_cls \<Gamma> C \<Longrightarrow> trail_false_cls \<Gamma>' C"
  unfolding trail_false_cls_def suffix_def
  by (elim exE) (auto simp add: trail_false_lit_def)

lemma trail_no_conflict_suffixI:
  "suffix \<Gamma> \<Gamma>' \<Longrightarrow> trail_no_conflict N \<Gamma>' \<Longrightarrow> trail_no_conflict N \<Gamma>"
  unfolding trail_no_conflict_def
  apply (erule contrapos_nn)
  apply (elim exE)
  using trail_false_cls_if_suffix_and_false by blast

lemma trail_almost_no_conflict_if_trail_no_conflict:
  "trail_no_conflict N \<Gamma> \<Longrightarrow> trail_almost_no_conflict N \<Gamma>"
  unfolding trail_almost_no_conflict_def trail_no_conflict_def
  using trail_backtrack_suffix[of \<Gamma>, THEN trail_false_cls_if_suffix_and_false]
  by (elim contrapos_nn) blast

lemma
  assumes suff: "suffix \<Gamma>' \<Gamma>" and "trail_almost_no_conflict N \<Gamma>"
  shows "trail_almost_no_conflict N \<Gamma>'"
proof -
  from suff have "suffix (trail_backtrack \<Gamma>' (trail_level \<Gamma>')) \<Gamma>"
    using trail_backtrack_suffix[of \<Gamma>']
    using suffix_order.order_trans by blast
  then show ?thesis
    unfolding trail_almost_no_conflict_def
    using trail_no_conflict_suffixI trail_almost_no_conflict_if_trail_no_conflict
    oops

(*
The (case u of Some (C, \<gamma>) \<Rightarrow> ...) is not necessary.
At a backtrack rule, one literal is undefined in the trail, which implies that it cannot be a
conflicting clause.
*)
definition regular_state where
  "regular_state N S \<longleftrightarrow> sound_state N S \<and>
    (\<exists>\<Gamma> U u. S = (\<Gamma>, U, u) \<and> trail_almost_no_conflict (N \<union> U) \<Gamma>)"

lemma conflict_preserves_trail_almost_no_conflict:
  assumes "conflict N S1 S2" and "trail_almost_no_conflict (N \<union> state_learned S1) (state_trail S1)"
  shows "trail_almost_no_conflict (N \<union> state_learned S2) (state_trail S2)"
  using assms by (auto simp: conflict.simps)

lemma conflict_regular_state:
  assumes step: "conflict N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: conflict.cases)
  case (conflictI D U D' \<Gamma> \<sigma>)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule conflict_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some (D', \<sigma>))"
      using conflictI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      by (rule tr_almost_no_conf)
  qed
qed

lemma propagate_preserves_trail_backtrack_level: "propagate N S1 S2 \<Longrightarrow>
  (let \<Gamma> = state_trail S1 in trail_backtrack \<Gamma> (trail_level \<Gamma>)) =
  (let \<Gamma> = state_trail S2 in trail_backtrack \<Gamma> (trail_level \<Gamma>))"
  by (auto simp add: propagate.simps)

lemma propagate_preserves_trail_almost_no_conflict:
  assumes "propagate N S1 S2" and "trail_almost_no_conflict (N \<union> state_learned S1) (state_trail S1)"
  shows "trail_almost_no_conflict (N \<union> state_learned S2) (state_trail S2)"
  using assms by (auto simp add: propagate.simps trail_almost_no_conflict_def)

lemma propagate_regular_state:
  assumes step: "propagate N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: propagate.cases)
  case (propagateI C U C'' L \<Gamma> \<gamma>)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)
  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule propagate_sound_state[OF step sound_S1])
  next
    show "S2 = (trail_propagate \<Gamma> L C'' \<gamma>, U, None)"
      using propagateI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) (trail_propagate \<Gamma> L C'' \<gamma>)"
      using tr_almost_no_conf
      by (simp add: trail_almost_no_conflict_def)
  qed
qed

lemma skip_regular_state:
  assumes step: "skip N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: skip.cases)
  case (skipI L \<delta> D \<sigma> \<Gamma> C U)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) (trail_propagate \<Gamma> L C \<delta>)"
    by (simp_all add: regular_state_def)
  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule skip_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some (D, \<sigma>))"
      using skipI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      using tr_almost_no_conf
      by (simp add: trail_almost_no_conflict_def)
  qed
qed

lemma factorize_regular_state:
  assumes step: "factorize N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: factorize.cases)
  case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)
  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule factorize_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some ((D + {#L#}) \<cdot> \<mu>, \<sigma>'))"
      using factorizeI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      by (rule tr_almost_no_conf)
  qed
qed

lemma resolve_regular_state:
  fixes N :: "('f, 'v) term clause set"
  assumes step: "resolve N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu>)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  let ?\<gamma> = "restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)"

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule resolve_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>, ?\<gamma>))"
      using resolveI by simp
  next
    from sound_S1 have "sound_trail N U \<Gamma>"
      using resolveI by (simp add: sound_state_def)
    then obtain CC :: "('f, 'v) term clause" and \<rho>\<^sub>C\<^sub>C :: "('f, 'v) subst" where
      CC_in: "CC \<in> N \<union> U" and
      "is_renaming \<rho>\<^sub>C\<^sub>C" and
      "add_mset L C = CC \<cdot> \<rho>\<^sub>C\<^sub>C"
      using resolveI unfolding sound_trail.simps[of N U \<Gamma>]
      by (auto simp: trail_propagate_def)

    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      by (rule tr_almost_no_conf)
  qed
qed

lemma trail_backtrack_decide_Suc_level[simp]:
  "trail_backtrack (trail_decide \<Gamma> L) (Suc (trail_level \<Gamma>)) = trail_decide \<Gamma> L"
  by (smt (verit, best) id_def n_not_Suc_n trail_backtrack.simps(2) trail_decide_def
      trail_level.simps(2) trail_level_decide)

lemma finite_Union_iff: "finite (\<Union> S) \<longleftrightarrow> finite S \<and> (\<forall>s \<in> S. finite s)"
  by (meson Union_upper finite_Union finite_UnionD finite_subset)

lemma trail_no_conflict_if_not_conflict_and_sound:
  fixes N :: "('f, 'v) term clause set"
  assumes "sound_state N S1"
  shows "(\<nexists>S2. conflict N S1 S2) \<Longrightarrow> state_conflict S1 = None \<Longrightarrow>
    trail_no_conflict (N \<union> state_learned S1) (state_trail S1)"
proof (erule contrapos_np)
  assume "state_conflict S1 = None"
  then obtain \<Gamma> :: "('f, 'v) trail" and U :: "('f, 'v) term clause set" where
    S1_def: "S1 = (\<Gamma>, U, None)"
    by (metis prod.collapse state_conflict_def)
  with \<open>sound_state N S1\<close> have "finite N" and "finite U"
    unfolding sound_state_def by simp_all

  assume "\<not> trail_no_conflict (N \<union> state_learned S1) (state_trail S1)"
  then obtain C :: "('f, 'v) term clause" and \<gamma> :: "('f, 'v) subst" where
    "C \<in> N \<union> U" and "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
    by (auto simp: S1_def trail_no_conflict_def)

  define \<rho>_vars :: "'v \<Rightarrow> 'v" where
    "\<rho>_vars = renaming_vars (\<Union> (vars_cls ` (N \<union> U \<union> clss_of_trail \<Gamma>)))"

  have "inj \<rho>_vars"
    unfolding \<rho>_vars_def
  proof (rule inj_renaming)
    show "finite (\<Union> (vars_cls ` (N \<union> U \<union> clss_of_trail \<Gamma>)))"
      using \<open>finite N\<close> \<open>finite U\<close> by simp
  qed

  define C' :: "('f, 'v) term clause" where
    "C' = C \<cdot> (Var \<circ> \<rho>_vars)"
  define \<gamma>' :: "('f, 'v) subst" where
    "\<gamma>' = (\<lambda>x. if x \<in> \<rho>_vars ` vars_cls C then \<gamma> (the_inv \<rho>_vars x) else Var x)"

  have "C \<cdot> ((Var \<circ> \<rho>_vars) \<odot> \<gamma>') = C \<cdot> \<gamma>"
    by (rule same_on_vars_clause) (simp add: subst_compose_def \<gamma>'_def \<open>inj \<rho>_vars\<close> the_inv_f_f)
  hence "C' \<cdot> \<gamma>' = C \<cdot> \<gamma>"
    unfolding C'_def by simp

  show "\<exists>S2. conflict N S1 S2"
  proof (rule exI)
    show "conflict N S1 (\<Gamma>, U, Some (C', \<gamma>'))"
      unfolding S1_def
    proof (rule conflictI)
      show "C \<in> N \<union> U"
        by (rule \<open>C \<in> N \<union> U\<close>)
    next
      show "C' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C"
        unfolding C'_def rename_clause_def \<rho>_vars_def by (rule refl)
    next
      have "renaming_vars (\<Union>(vars_cls ` (N \<union> U \<union> clss_of_trail \<Gamma>))) x \<noteq> x" for x
        by (simp add: \<open>finite N\<close> \<open>finite U\<close> renaming_all)
      hence "renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma>) x \<noteq> Var x" for x
        by simp
      hence "subst_domain (Var \<circ> \<rho>_vars) = UNIV"
        unfolding \<rho>_vars_def subst_domain_def by simp
      hence "vars_cls (C \<cdot> (Var \<circ> \<rho>_vars)) = \<rho>_vars ` vars_cls C"
        unfolding vars_subst_cls_eq by auto
      thus "subst_domain \<gamma>' \<subseteq> vars_cls C'"
        unfolding \<gamma>'_def C'_def by (smt (verit, best) mem_Collect_eq subsetI subst_domain_def)
    next
      from \<open>sound_state N S1\<close> have "sound_trail N U \<Gamma>"
        unfolding sound_state_def S1_def by simp
      hence "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
        by (rule ball_ground_lit_if_sound_trail)
      hence "is_ground_cls (C \<cdot> \<gamma>)"
        unfolding is_ground_cls_def
        apply (intro allI impI)
        apply (drule \<open>trail_false_cls \<Gamma> (C \<cdot> \<gamma>)\<close>[unfolded trail_false_cls_def, rule_format])
        unfolding trail_false_lit_def is_ground_lit_def
        by (metis atm_of_uminus)
      thus "is_ground_cls (C' \<cdot> \<gamma>')"
        using \<open>C' \<cdot> \<gamma>' = C \<cdot> \<gamma>\<close> by simp
    next
      show "trail_false_cls \<Gamma> (C' \<cdot> \<gamma>')"
        using \<open>trail_false_cls \<Gamma> (C \<cdot> \<gamma>)\<close> \<open>C' \<cdot> \<gamma>' = C \<cdot> \<gamma>\<close> by simp
    qed
  qed
qed



lemma decide_regular_state:
  assumes step: "decide N S1 S2" and no_conflict: "\<nexists>S3. conflict N S2 S3" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: decide.cases)
  case (decideI L \<Gamma> U)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  have sound_S2: "sound_state N S2"
      by (rule decide_sound_state[OF step sound_S1])

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule sound_S2)
  next
    show "S2 = (trail_decide \<Gamma> L, U, None)"
      using decideI by simp
  next
    have "trail_no_conflict (N \<union> state_learned S2) (state_trail S2)"
      by (rule trail_no_conflict_if_not_conflict_and_sound[OF sound_S2 no_conflict])
        (use decideI in simp)
    thus "trail_almost_no_conflict (N \<union> U) (trail_decide \<Gamma> L)"
      using decideI by (simp add: trail_almost_no_conflict_if_trail_no_conflict)
  qed
qed

lemma trail_backtrack_0[simp]: "trail_backtrack \<Gamma> 0 = []"
  by (induction \<Gamma>) simp_all

lemma suffix_trail_backtrack_backtrack_if_le:
  "m \<le> n \<Longrightarrow> n \<le> trail_level \<Gamma> \<Longrightarrow> suffix (trail_backtrack \<Gamma> m) (trail_backtrack \<Gamma> n)"
  unfolding suffix_def
proof (induction \<Gamma> arbitrary: m n)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  thus ?case
    by (smt (verit, del_insts) id_apply le_antisym not_less_eq_eq suffix_def
        trail_backtrack.simps(2) trail_backtrack_suffix trail_level.simps(2))
qed

lemma trail_no_conflict_backtrack_if_no_conflict_backtrack_le:
  assumes "m \<le> n" and "n \<le> trail_level \<Gamma>"
  shows "trail_no_conflict N (trail_backtrack \<Gamma> n) \<Longrightarrow> trail_no_conflict N (trail_backtrack \<Gamma> m)"
  unfolding trail_no_conflict_def
  using suffix_trail_backtrack_backtrack_if_le[OF assms, THEN trail_false_cls_if_suffix_and_false]
  by blast

lemma not_trail_false_cls_if_not_trail_defined_lit:
  "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> L \<in># C \<Longrightarrow> \<not> trail_false_cls \<Gamma> C"
  using trail_defined_lit_iff_true_or_false trail_false_cls_def by blast

primrec bt where
  "bt [] n = ([], 0)" |
  "bt (Ln # \<Gamma>) n =
    (let (\<Gamma>', m) = bt \<Gamma> n in
    if m < n then
      (Ln # \<Gamma>', if is_decision_lit Ln then Suc m else m)
    else
      (\<Gamma>', m))"

lemma bt_level_inv: "bt \<Gamma> level = (\<Gamma>', level') \<Longrightarrow> trail_level \<Gamma>' \<le> level'"
proof (induction \<Gamma> arbitrary: \<Gamma>' level')
  case Nil
  then show ?case by simp
next
  case (Cons Ln \<Gamma>)
  obtain \<Gamma>'' level'' where "bt \<Gamma> level = (\<Gamma>'', level'')"
    by fastforce
  show ?case
  proof (cases "level'' < level")
    case True
    then show ?thesis
      using Cons \<open>bt \<Gamma> level = (\<Gamma>'', level'')\<close>
      by (cases "is_decision_lit Ln") auto
  next
    case False
    then show ?thesis
      using Cons \<open>bt \<Gamma> level = (\<Gamma>'', level'')\<close> by simp
  qed
qed


lemma bt_level_inv2: "bt \<Gamma> level = (\<Gamma>', level') \<Longrightarrow> level' \<le> level"
proof (induction \<Gamma>)
  case Nil
  then show ?case
    by simp
next
  case (Cons Ln \<Gamma>)

  obtain \<Gamma>' m where "bt \<Gamma> level = (\<Gamma>', m)"
    by fastforce

  with Cons show ?case
    apply simp
    using bt_level_inv
    by (smt (verit) Suc_leI le_eq_less_or_eq prod.inject)
qed

lemma "trail_level (fst (bt \<Gamma> level)) \<le> level"
proof (induction \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons Ln \<Gamma>)

  obtain \<Gamma>' m where "bt \<Gamma> level = (\<Gamma>', m)"
    by fastforce

  with Cons show ?case
    apply simp
    using bt_level_inv
    by fastforce
qed

lemma assumes sound_\<Gamma>: "sound_trail N U \<Gamma>"
  shows "level < trail_level_lit \<Gamma> L \<Longrightarrow> \<not> trail_defined_lit (fst (bt \<Gamma> level)) L"
  using sound_\<Gamma>
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case by simp
next
  case (Cons \<Gamma> K u)
  obtain \<Gamma>' m where "bt \<Gamma> level = (\<Gamma>', m)" by force
  with Cons.hyps(1) Cons.prems show ?case
    apply simp
    apply (rule conjI)
    subgoal
      sorry
    subgoal
      apply (frule bt_level_inv2)
      apply simp
      oops





































lemma "0 < trail_level_lit \<Gamma> L \<Longrightarrow> \<exists>n < length \<Gamma>. fst (\<Gamma> ! n) = L \<or> fst (\<Gamma> ! n) = - L"
proof (induction \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "fst Ln = L \<or> fst Ln = - L")
    case True
    thus ?thesis by auto
  next
    case False
    with Cons show ?thesis by auto
  qed
qed

lemma assumes sound_\<Gamma>: "sound_trail N U \<Gamma>"
  shows "level < trail_level \<Gamma> \<Longrightarrow> level < trail_level_lit \<Gamma> L \<Longrightarrow>
  \<not> trail_defined_lit (trail_backtrack \<Gamma> level) L"
  (* using trail_backtrack_suffix[of \<Gamma> level, unfolded suffix_def] *)
  (* using trail_backtrack_suffix[of \<Gamma> level, unfolded suffix_def] *)
  using sound_\<Gamma>
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case by simp
next
  case (Cons \<Gamma> K u)
  from Cons.hyps have "\<not> trail_defined_lit \<Gamma> K" by simp
  show ?case
  proof (cases u)
    case None
    then show ?thesis
      using Cons.prems
      apply (simp add: is_decision_lit_def )
      unfolding trail_level.simps(2)[of "(K, None)" \<Gamma>] is_decision_lit_def prod.sel
      unfolding HOL.simp_thms(6) HOL.if_True
      using Cons.IH
      
      sorry
  next
    case (Some a)
    then show ?thesis
      using Cons.prems
      apply (simp add: is_decision_lit_def)
      sorry
  qed
qed

lemma backtrack_regular_state:
  assumes step: "backtrack N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: backtrack.cases)
  case (backtrackI \<Gamma> L \<sigma> U D)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  have sound_S2: "sound_state N S2"
    by (rule backtrack_sound_state[OF step sound_S1])

  have "trail_level_cls \<Gamma> (D \<cdot> \<sigma>) < trail_level \<Gamma>"
    sorry

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule sound_S2)
  next
    show "S2 = (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)), U \<union> {D + {#L#}}, None)"
      using backtrackI by simp
  next
    have "trail_no_conflict (N \<union> U) (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
    proof (rule trail_no_conflict_backtrack_if_no_conflict_backtrack_le)
      show "trail_no_conflict (N \<union> U) (trail_backtrack \<Gamma> (trail_level \<Gamma>))"
        by (rule tr_almost_no_conf[unfolded trail_almost_no_conflict_def])
    next
      show "trail_level_cls \<Gamma> (D \<cdot> \<sigma>) \<le> trail_level \<Gamma>"
        by (rule trail_level_cls_le)
    next
      show "trail_level \<Gamma> \<le> trail_level \<Gamma>"
        by (rule Nat.le_refl)
    qed
    moreover have "trail_no_conflict {D + {#L#}} (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
    proof -
      have "\<not> trail_defined_lit (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>))) (L \<cdot>l \<sigma>)"
        using backtrackI \<open>trail_level_cls \<Gamma> (D \<cdot> \<sigma>) < trail_level \<Gamma>\<close>
        sorry
      then show ?thesis
        unfolding trail_no_conflict_def
        apply simp
        using not_trail_false_cls_if_not_trail_defined_lit
        
        sorry
    qed
    ultimately show "trail_almost_no_conflict (N \<union> (U \<union> {D + {#L#}}))
      (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
      using trail_almost_no_conflict_if_trail_no_conflict trail_no_conflict_union_iff
      by metis
  qed
qed

lemma
  assumes
    sound_S1: "sound_state N S1" and
    regular_step: "regular_scl N S1 S2" and
    regular_S1: "regular_state N S1"
  shows "regular_state N S2"
  using regular_step unfolding regular_scl_def
proof (elim disjE conjE)
  show "conflict N S1 S2 \<Longrightarrow> ?thesis"
    by (rule conflict_regular_state[OF _ regular_S1])
next
  from regular_S1 have
    sound_S1: "sound_state N S1" and
    almost_no_conf_S1: "trail_almost_no_conflict (N \<union> state_learned S1) (state_trail S1)"
    unfolding regular_state_def by auto
  from regular_step sound_S1 have sound_S2: "sound_state N S2"
    by (rule regular_scl_sound_state)

  assume "\<not> conflict N S1 S2" and "reasonable_scl N S1 S2"
  thus ?thesis
    unfolding reasonable_scl_def scl_def
  proof (elim disjE conjE)
    show "propagate N S1 S2 \<Longrightarrow> ?thesis"
      by (rule propagate_regular_state[OF _ regular_S1])
  next
    assume "decide N S1 S2" and "decide N S1 S2 \<longrightarrow> \<not> Ex (conflict N S2)"
    thus ?thesis
      using decide_regular_state[OF _ _ regular_S1] by simp
  next
    assume "\<not> conflict N S1 S2" and "conflict N S1 S2"
    hence False by simp
    thus ?thesis ..
  next
    show "skip N S1 S2 \<Longrightarrow> ?thesis"
      by (rule skip_regular_state[OF _ regular_S1])
  next
    show "factorize N S1 S2 \<Longrightarrow> ?thesis"
      by (rule factorize_regular_state[OF _ regular_S1])
  next
    show "resolve N S1 S2 \<Longrightarrow> ?thesis"
      by (rule resolve_regular_state[OF _ regular_S1])
  next
    show "backtrack N S1 S2 \<Longrightarrow> ?thesis"
      apply (erule backtrack.cases)
      using almost_no_conf_S1
      apply (simp add: regular_state_def)
      using trail_no_conflict_suffixI[OF trail_backtrack_suffix]
      oops
      
      

lemma
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S0" and
    regular_step: "backtrack N S0 S1"
  shows "\<not> conflict N S1 S2"
  using regular_run regular_step
  thm converse_rtranclp_induct
proof (induction arbitrary: rule: converse_rtranclp_induct)
  case base
  hence False by (simp add: backtrack.simps)
  thus ?case ..
next
  case (step S0 S0')
  then show ?case
    
    sorry
qed


lemma propagate_or_backtrack_before_regular_conflict:
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S0" and
    regular_step: "regular_scl N S0 S1" and
    conflict: "conflict N S1 S2"
  shows "propagate N S0 S1 \<or> backtrack N S0 S1"
proof -
  from conflict obtain \<Gamma> U C \<gamma> where
    S1_def: "S1 = (\<Gamma>, U, None)" and
    S2_def: "S2 = (\<Gamma>, U, Some (C, \<gamma>))"
    unfolding conflict.simps by auto

  with regular_step have "\<not> conflict N S0 S1" and "reasonable_scl N S0 S1"
    unfolding regular_scl_def by (simp_all add: conflict.simps)

  with conflict have "scl N S0 S1" and "\<not> decide N S0 S1"
    unfolding reasonable_scl_def by blast+

  thus ?thesis
    unfolding scl_def
    by (simp add: S1_def skip.simps conflict.simps factorize.simps resolve.simps)
qed

(* lemma
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S1" and
    conflict: "conflict N S1 S2"
  shows "{#} \<in> N \<or> (\<exists>S0. (regular_scl N)\<^sup>*\<^sup>* initial_state S0 \<and> propagate N S0 S1)" *)
  

lemma
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N S0 S1" and
    resolution: "(\<lambda>S S'. skip N S S' \<or> factorize N S S' \<or> resolve N S S')\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N Sn Sn'" and
    "transp lt" and
    total_on_ground_lt: "Restricted_Predicates.total_on lt {L. is_ground_lit L}"
  shows "(regular_scl N)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      \<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> U) C)"
proof -
  from regular_run conflict have "(regular_scl N)\<^sup>*\<^sup>* initial_state S1"
    by (meson regular_scl_def rtranclp.simps)
  also from resolution have "(regular_scl N)\<^sup>*\<^sup>* ... Sn"
    using regular_run_if_skip_factorize_resolve_run tranclp_into_rtranclp by fast
  also from backtrack have "(regular_scl N)\<^sup>*\<^sup>* ... Sn'"
    by (auto simp add: scl_def reasonable_scl_def regular_scl_def backtrack_well_defined)
  finally have "(regular_scl N)\<^sup>*\<^sup>* initial_state Sn'" by assumption

  from conflict obtain C1 \<gamma>1 where conflict_S1: "state_conflict S1 = Some (C1, \<gamma>1)"
    by (smt (verit, best) conflict.simps state_conflict_simp)
  then obtain Cn \<gamma>n where conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)"
    by (smt (verit) backtrack.simps backtrack state_conflict_simp)

  from fin_N disj_vars_N have "sound_state N initial_state"
    by (rule sound_initial_state)
  with regular_run have "sound_state N S0"
    by (simp add: regular_run_sound_state)
  with conflict have sound_S1: "sound_state N S1"
    by (simp add: conflict_sound_state)
  with resolution have sound_Sn: "sound_state N Sn"
    by (induction rule: tranclp_induct)
      (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

  from conflict_Sn sound_Sn have "N \<TTurnstile>\<G>e {Cn}" and
    trail_Sn_false_Cn_\<gamma>n: "trail_false_cls (state_trail Sn) (Cn \<cdot> \<gamma>n)"
    by (auto simp add: sound_state_def)

  from conflict_S1 sound_S1 have trail_S1_false_C1_\<gamma>1: "trail_false_cls (state_trail S1) (C1 \<cdot> \<gamma>1)"
    by (auto simp add: sound_state_def)

  from resolution have "suffix (state_trail Sn) (state_trail S1) \<and>
    (\<exists>Cn \<gamma>n. state_conflict Sn = Some (Cn, \<gamma>n) \<and> trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n))"
  proof (induction Sn rule: tranclp_induct)
    case (base S2)
    thus ?case
    proof (elim disjE)
      assume "skip N S1 S2"
      thus ?thesis
        using trail_false_conflict_after_skip[OF conflict_S1 trail_S1_false_C1_\<gamma>1]
        by (smt (verit) skip.simps state_trail_simp suffix_trail_propagate)
    next
      assume "factorize N S1 S2"
      moreover with sound_S1 have "sound_state N S2"
        by (auto intro: factorize_sound_state)
      ultimately show ?thesis
        by (cases N S1 S2 rule: factorize.cases) (simp add: sound_state_def)
    next
      assume "resolve N S1 S2"
      moreover with sound_S1 have "sound_state N S2"
        by (auto intro: resolve_sound_state)
      ultimately show ?thesis
        by (cases N S1 S2 rule: resolve.cases) (simp add: sound_state_def)
    qed
  next
    case (step Sm Sm')
    from step.hyps(2) have "suffix (state_trail Sm') (state_trail Sm)"
      by (auto dest: strict_suffix_trail_if_skip eq_trail_if_factorize eq_trail_if_resolve)
    with step.IH have "suffix (state_trail Sm') (state_trail S1)"
      by force

    from step.hyps(1) sound_S1 have sound_Sm: "sound_state N Sm"
      by (induction rule: tranclp_induct)
        (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

    from step.IH obtain Cm \<gamma>m where
      conflict_Sm: "state_conflict Sm = Some (Cm, \<gamma>m)" and
      trail_false_Cm_\<gamma>m: "trail_false_cls (state_trail S1) (Cm \<cdot> \<gamma>m)"
      using step.prems step.hyps(2) \<open>suffix (state_trail Sm') (state_trail Sm)\<close>
      by auto

    from step.hyps(2) show ?case
    proof (elim disjE)
      assume "skip N Sm Sm'"
      thus ?thesis
        using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
        using trail_false_conflict_after_skip trail_false_Cm_\<gamma>m conflict_Sm
        by (smt (verit) skip.cases state_conflict_simp)
    next
      assume "factorize N Sm Sm'"
      thus ?thesis
      proof (cases N Sm Sm' rule: factorize.cases)
        case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
        with conflict_Sm have Cm_def: "Cm = D + {#L, L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        with factorizeI(3,4) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
          using trail_false_Cm_\<gamma>m trail_false_cls_subst_mgu_before_grounding
          by (smt (verit, best) CollectI mgu_sound prod.sel singletonD atm_of_subst_lit
              unifiers_def)
        with factorizeI(5) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
          by (metis subsetI subst_cls_restrict_subst_idem)
        with factorizeI(2) show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using state_conflict_simp by blast
      qed
    next
      assume "resolve N Sm Sm'"
      thus ?thesis
      proof (cases N Sm Sm' rule: resolve.cases)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu>)
        have "is_renaming (renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}}))"
          apply (rule is_renaming_renaming_wrt)
          using resolveI
          by (smt (verit, best) finite.emptyI finite.insertI finite_UnI finite_clss_of_trail
              sound_Sm sound_state_def state_learned_simp)
        with resolveI have is_renaming_\<rho>: "is_renaming \<rho>"
          by simp

        from resolveI conflict_Sm have Cm_def: "Cm = D + {#L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        hence tr_false_D_L'_\<sigma>: "trail_false_cls (state_trail S1) ((D + {#L'#}) \<cdot> \<sigma>)"
          using trail_false_Cm_\<gamma>m by simp

        from resolveI sound_Sm have
          "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
          disj_N_U_\<Gamma>_D_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L'#}) C" and
          "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)" and
          dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})" and
          "sound_trail N U \<Gamma>"
          unfolding sound_state_def by simp_all

        have "vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}"
          apply(rule disj_N_U_\<Gamma>_D_L'[unfolded disjoint_vars_iff_inter_empty,
                rule_format, of "C + {#L#}"])
          by (simp add: resolveI(3))

        from resolveI(6) have "atm_of (L \<cdot>l \<delta>) = atm_of (L' \<cdot>l \<sigma>)" by simp
        hence "(atm_of L) \<cdot>a \<delta> = (atm_of L') \<cdot>a \<sigma>" by simp

        have \<sigma>_\<delta>_in_unif: "\<sigma> \<odot> \<delta> \<in> unifiers {(atm_of L, atm_of L')}"
        proof (rule subst_comp_in_unifiersI')
          show "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
            using resolveI(6) by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
        next
          show "vars_lit L \<inter> subst_domain \<sigma> = {}"
            using dom_\<sigma> \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close> by fastforce
        next
          have "subst_domain \<delta> \<subseteq> vars_cls C \<union> vars_lit L"
            using \<open>sound_trail N U \<Gamma>\<close>
            unfolding sound_trail.simps[of N U \<Gamma>]
            unfolding resolveI(3)
            by (simp add: trail_propagate_def)
          then show "vars_lit L' \<inter> subst_domain \<delta> = {}"
            using \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close> by auto
        next
          have "range_vars \<sigma> = {}"
            unfolding range_vars_def UNION_empty_conv subst_range.simps
            using dom_\<sigma> \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close> is_ground_cls_is_ground_on_var
              is_ground_atm_iff_vars_empty
            by fast
          thus "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
            by simp
        qed

        from resolveI \<open>sound_trail N U \<Gamma>\<close> have "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
          by (auto simp: trail_propagate_def elim: sound_trail.cases)

        from resolveI have "suffix \<Gamma>' (state_trail S1)"
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          by (metis (no_types, lifting) state_trail_simp suffix_order.trans suffix_trail_propagate)

        have "trail_false_cls (state_trail S1) ((D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
          using trail_false_cls_plus_subst_mgu_before_groundings[
              of "state_trail S1" D L' \<sigma> _ C \<delta> L \<mu>, OF tr_false_D_L'_\<sigma> \<open>trail_false_cls \<Gamma>' (C \<cdot> \<delta>)\<close>
                \<open>suffix \<Gamma>' (state_trail S1)\<close>
                \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close>
                \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close>
                \<open>subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})\<close>
                mgu_sound[OF resolveI(7)] \<sigma>_\<delta>_in_unif]
          by assumption
        then have "trail_false_cls (state_trail S1) ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot>
          restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
          unfolding subst_cls_restrict_subst_idem[OF subset_refl]
          unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
          by assumption
        then show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using resolveI by simp
      qed
    qed
  qed

  then obtain Cn \<gamma>n where
    "suffix (state_trail Sn) (state_trail S1)" and
    conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)" and
    "trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    by auto

  moreover have "\<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> U) Cn"
  proof (rule notI)
    assume "redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> U) Cn"
    moreover from sound_Sn conflict_Sn have "Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn"
      unfolding sound_state_def
      using grounding_of_cls_ground grounding_of_subst_cls_subset 
      by fastforce
    ultimately have gr_red_Cn_\<gamma>n: "ground_redundant
      (multp (trail_less_ex lt (map fst (state_trail S1))))
      (grounding_of_clss (N \<union> U)) (Cn \<cdot> \<gamma>n)"
      by (simp add: redundant_def)

    define S where
      "S = {D \<in> grounding_of_clss (N \<union> U).
        (multp (trail_less_ex lt (map fst (state_trail S1))))\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)}"

    from gr_red_Cn_\<gamma>n have "S \<TTurnstile>e {Cn \<cdot> \<gamma>n}"
      unfolding ground_redundant_def S_def by simp

    from sound_S1 have "sound_trail N (state_learned S1) (state_trail S1)"
      by (auto simp add: sound_state_def)

    have "\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L"
      using \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> trail_defined_lit_iff_true_or_false
        trail_false_cls_def by blast

    have "\<not> trail_interp (state_trail S1) \<TTurnstile>s {Cn \<cdot> \<gamma>n}"
      apply (rule notI)
      using \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>
      apply simp
      unfolding trail_true_cls_iff_trail_interp_entails[OF
          \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>
          \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close>, symmetric]
      using not_trail_true_and_false_cls[OF \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>]
      by simp

    hence "\<not> trail_interp (state_trail S1) \<TTurnstile>s S"
      using \<open>S \<TTurnstile>e {Cn \<cdot> \<gamma>n}\<close>[rule_format, of "trail_interp (state_trail S1)"]
      by argo

    then obtain D where "D \<in> S" and "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      by (auto simp: true_clss_def)

    moreover have "trail_defined_cls (state_trail S1) D"
    proof -
      have "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
        using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close> trail_defined_cls_def by blast

      from \<open>D \<in> S\<close> have
        D_in: "D \<in> grounding_of_clss (N \<union> U)" and
        "(multp (trail_less_ex lt (map fst (state_trail S1))))\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)"
        unfolding S_def by simp_all
      then show "trail_defined_cls (state_trail S1) D"
        unfolding Lattices.sup_apply Boolean_Algebras.sup_bool_def
      proof (elim disjE)
        assume multp_D_Cn_\<gamma>n: "multp (trail_less_ex lt (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
        show "trail_defined_cls (state_trail S1) D"
        proof (rule trail_defined_cls_if_lt_defined)
          show "sound_trail N (state_learned S1) (state_trail S1)"
            by (rule \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>)
        next
          show "multp (trail_less_ex lt (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
            by (rule multp_D_Cn_\<gamma>n)
        next
          show "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
            by (rule \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>)
        next
          show "transp lt"
            by (rule \<open>transp lt\<close>)
        next
          have "is_ground_cls D"
            using D_in by (simp add: grounding_ground)
          moreover have "is_ground_cls (Cn \<cdot> \<gamma>n)"
            using \<open>Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn\<close> is_ground_cls_if_in_grounding_of_cls by blast
          ultimately have "set_mset D \<union> set_mset (Cn \<cdot> \<gamma>n) \<subseteq> {L. is_ground_lit L}"
            using is_ground_cls_imp_is_ground_lit by auto
          thus "Restricted_Predicates.total_on lt (set_mset D \<union> set_mset (Cn \<cdot> \<gamma>n))"
            using total_on_ground_lt
            by (metis le_iff_sup total_on_unionD1)
        qed
      next
        assume "D = Cn \<cdot> \<gamma>n"
        then show "trail_defined_cls (state_trail S1) D"
          using \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> by simp
      qed    
    qed

    then have "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      by (meson \<open>sound_trail N (state_learned S1) (state_trail S1)\<close> trail_defined_cls_def
          trail_defined_lit_iff_true_or_false trail_false_cls_def
          trail_interp_cls_if_sound_and_trail_true trail_true_cls_def)

    from conflict obtain S

    from conflict obtain L C \<gamma> where "state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>"
      apply (elim conflict.cases)

    thus False
      sorry
  qed

  ultimately show ?thesis
    using \<open>(regular_scl N)\<^sup>*\<^sup>* initial_state Sn'\<close>
    by simp
  oops
    

end

end