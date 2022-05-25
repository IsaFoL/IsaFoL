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
    Relation_Extra
begin

sledgehammer_params

section \<open>Extra Lemmas\<close>


subsection \<open>Set_Extra\<close>

lemma not_in_iff: "L \<notin> xs \<longleftrightarrow> (\<forall>y\<in>xs. L \<noteq> y)"
  by auto

lemma disjoint_iff': "A \<inter> B = {} \<longleftrightarrow> (\<forall>a \<in> A. a \<notin> B) \<and> (\<forall>b \<in> B. b \<notin> A)"
  by blast

lemma set_filter_insert_conv:
  "{x \<in> insert y S. P x} = (if P y then insert y else id) {x \<in> S. P x}"
  by auto


subsection \<open>Finite_Set_Extra\<close>

lemma finite_induct' [case_names empty singleton insert_insert, induct set: finite]:
  \<comment> \<open>Discharging \<open>x \<notin> F\<close> entails extra work.\<close>
  assumes "finite F"
  assumes "P {}"
    and singleton: "\<And>x. P {x}"
    and insert_insert: "\<And>x y F. finite F \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> F \<Longrightarrow> y \<notin> F \<Longrightarrow> P (insert y F) \<Longrightarrow> P (insert x (insert y F))"
  shows "P F"
  using \<open>finite F\<close>
proof induct
  show "P {}" by fact
next
  fix x F
  assume F: "finite F" and P: "P F"
  thus "P (insert x F)"
  proof (induction F rule: finite.induct)
    case emptyI
    show ?case by (rule singleton)
  next
    case (insertI F y)
    show ?case
    proof (cases "x = y")
      case True
      then show ?thesis
        by (simp add: insertI.prems)
    next
      case x_neq_y: False
      show ?thesis
      proof (cases "x \<in> F \<or> y \<in> F")
        case True
        then show ?thesis
          by (metis insertCI insertI.IH insertI.prems insert_absorb)
      next
        case False
        show ?thesis
        proof (rule insert_insert)
          show "finite F" using insertI by simp
        next
          show "x \<noteq> y" by (rule x_neq_y)
        next
          show "x \<notin> F" using False by simp
        next
          show "y \<notin> F" using False by simp
        next
          show "P (insert y F)"
            by (simp add: insertI.prems)
        qed
      qed
    qed
  qed
qed


subsection \<open>Product_Type_Extra\<close>

lemma insert_Times: "insert a A \<times> B = Pair a ` B \<union> A \<times> B"
  by blast

lemma Times_insert: "A \<times> insert b B = (\<lambda>x. (x, b)) ` A \<union> A \<times> B"
  by blast

lemma insert_Times_insert':
  "insert a A \<times> insert b B = insert (a, b) ((Pair a ` B) \<union> ((\<lambda>x. (x, b)) ` A) \<union> (A \<times> B))"
  (is "?lhs = ?rhs")
  unfolding insert_Times_insert by auto


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


subsection \<open>Abstract_Substitution_Extra\<close>

lemma (in substitution_ops) grounding_of_clss_empty[simp]: "grounding_of_clss {} = {}"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) grounding_of_clss_singleton[simp]:
  "grounding_of_clss {C} = grounding_of_cls C"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) subst_atm_of_eqI:
  "L \<cdot>l \<sigma>\<^sub>L = K \<cdot>l \<sigma>\<^sub>K \<Longrightarrow> atm_of L \<cdot>a \<sigma>\<^sub>L = atm_of K \<cdot>a \<sigma>\<^sub>K"
  by (cases L; cases K) (simp_all add: subst_lit_def)

lemma (in substitution_ops) subst_atm_of_eq_compI:
  "L \<cdot>l \<sigma> = - (L' \<cdot>l \<sigma>) \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: uminus_literal_def subst_lit_def)

lemma (in substitution_ops) set_mset_subst_cls_conv: "set_mset (C \<cdot> \<sigma>) = (\<lambda>L. L \<cdot>l \<sigma>) ` set_mset C"
  by (simp add: subst_cls_def)

lemma (in substitution) is_ground_clss_grounding_of_clss[simp]:
  "is_ground_clss (grounding_of_clss N)"
  using grounding_of_clss_def union_grounding_of_cls_ground by presburger

lemma (in substitution) is_ground_cls_if_in_grounding_of_cls:
  "C' \<in> grounding_of_cls C \<Longrightarrow> is_ground_cls C'"
  using grounding_ground grounding_of_clss_singleton by blast


subsection \<open>Clausal_Calculus_Extra\<close>


subsubsection \<open>Clausal_Calculus Only\<close>

lemma true_cls_iff_set_mset_eq: "set_mset C = set_mset D \<Longrightarrow> I \<TTurnstile> C \<longleftrightarrow> I \<TTurnstile> D"
  by (simp add: true_cls_def)

lemma true_clss_if_set_mset_eq: "(\<forall>D \<in> \<D>. \<exists>C \<in> \<C>. set_mset D = set_mset C) \<Longrightarrow> I \<TTurnstile>s \<C> \<Longrightarrow> I \<TTurnstile>s \<D>"
  using true_cls_iff_set_mset_eq by (metis true_clss_def)

lemma entails_clss_insert: "N \<TTurnstile>e insert C U \<longleftrightarrow> N \<TTurnstile>e {C} \<and> N \<TTurnstile>e U"
  by auto


subsubsection \<open>Clausal_Calculus and Abstract_Substitution\<close>

lemma (in substitution) is_ground_lit_Pos[simp]: "is_ground_atm L \<Longrightarrow> is_ground_lit (Pos L)"
  by (simp add: is_ground_lit_def)

lemma (in substitution) is_ground_lit_Neg[simp]: "is_ground_atm L \<Longrightarrow> is_ground_lit (Neg L)"
  by (simp add: is_ground_lit_def)


subsection \<open>First_Order_Terms Extra\<close>

text \<open>This simplification rule is annoying: mgu would be nicer if it was a @{command definition}.\<close>
declare Unification.mgu.simps[simp del]


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

lemma subst_subst_eq_subst_subst_if_subst_eq_substI:
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    t_inter_\<delta>_empty: "vars_term t \<inter> subst_domain \<delta> = {}" and
    u_inter_\<sigma>_empty: "vars_term u \<inter> subst_domain \<sigma> = {}"
  shows
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {} \<Longrightarrow> t \<cdot> \<sigma> \<cdot> \<delta> = u \<cdot> \<sigma> \<cdot> \<delta>"
    "range_vars \<delta> \<inter> subst_domain \<sigma> = {} \<Longrightarrow> t \<cdot> \<delta> \<cdot> \<sigma> = u \<cdot> \<delta> \<cdot> \<sigma>"
proof -
  have "u \<cdot> \<delta> = u \<cdot> \<sigma> \<cdot> \<delta>"
    unfolding term_subst_eq_conv[of u \<delta> "\<sigma> \<circ>\<^sub>s \<delta>", simplified]
    using u_inter_\<sigma>_empty
    by (simp add: disjoint_iff subst_compose_def subst_domain_def)
  thus "range_vars \<sigma> \<inter> subst_domain \<delta> = {} \<Longrightarrow> t \<cdot> \<sigma> \<cdot> \<delta> = u \<cdot> \<sigma> \<cdot> \<delta>"
    using \<open>t \<cdot> \<sigma> = u \<cdot> \<delta>\<close> t_inter_\<delta>_empty
    by (metis (no_types, opaque_lifting)  disjoint_iff subst_apply_term_eq_subst_apply_term_composeI
        subst_subst term_subst_eq_conv)

  have "t \<cdot> \<sigma> = t \<cdot> \<delta> \<cdot> \<sigma>"
    unfolding term_subst_eq_conv[of t \<sigma> "\<delta> \<circ>\<^sub>s \<sigma>", simplified]
    using t_inter_\<delta>_empty
    by (simp add: disjoint_iff subst_compose_def subst_domain_def)
  thus "range_vars \<delta> \<inter> subst_domain \<sigma> = {} \<Longrightarrow> t \<cdot> \<delta> \<cdot> \<sigma> = u \<cdot> \<delta> \<cdot> \<sigma>"
    using \<open>t \<cdot> \<sigma> = u \<cdot> \<delta>\<close> u_inter_\<sigma>_empty
    by (metis (no_types, opaque_lifting) disjoint_iff subst_apply_term_eq_subst_apply_term_composeI
        subst_subst term_subst_eq_conv)
qed

lemma subst_comp_in_unifiersI:
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    "vars_term t \<inter> subst_domain \<delta> = {}" and
    "vars_term u \<inter> subst_domain \<sigma> = {}" and
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
  shows "\<sigma> \<circ>\<^sub>s \<delta> \<in> unifiers {(t, u)}"
  using subst_subst_eq_subst_subst_if_subst_eq_substI(1)[OF assms]
  by (simp add: unifiers_def)

lemma subst_comp_in_unifiersI':
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    "vars_term t \<inter> subst_domain \<delta> = {}" and
    "vars_term u \<inter> subst_domain \<sigma> = {}" and
    "range_vars \<delta> \<inter> subst_domain \<sigma> = {}"
  shows "\<delta> \<circ>\<^sub>s \<sigma> \<in> unifiers {(t, u)}"
  using subst_subst_eq_subst_subst_if_subst_eq_substI(2)[OF assms]
  by (simp add: unifiers_def)

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
    using assms by (simp add: mgu.simps split: option.splits)
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

lemma unify_Cons_eq[simp]: "fst e = snd e \<Longrightarrow> unify (e # es) bs = unify es bs"
  by (rule unify_append_eq_unify_if_prefix_same[of "[e]" for e, simplified])

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

lemma same_on_lits_clause:
  assumes "\<forall>L \<in># C. subst_lit L \<sigma> = subst_lit L \<tau>"
  shows "subst_cls C \<sigma> = subst_cls C \<tau>"
  using assms unfolding subst_cls_def
  by simp

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

lemma vars_cls_subst_subset:
  assumes range_vars_\<eta>: "range_vars \<eta> \<subseteq> vars_lit L \<union> vars_lit L'"
  shows "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L, L'#})"
proof -
  have "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L#}) - subst_domain \<eta> \<union> range_vars \<eta>"
    by (rule vars_subst_cls_subset[of "(D + {#L#})" \<eta>])
  also have "... \<subseteq> vars_cls (D + {#L#}) - (vars_lit L \<union> vars_lit L') \<union> vars_lit L \<union> vars_lit L'"
    using range_vars_\<eta> by blast
  also have "... \<subseteq> vars_cls (D + {#L#}) \<union> vars_lit L \<union> vars_lit L'"
    by fast
  also have "... \<subseteq> vars_cls D \<union> vars_lit L \<union> vars_lit L'"
    unfolding vars_cls_plus unfolding vars_cls_def by simp
  also have "... \<subseteq> vars_cls (D + {#L, L'#})"
    by auto
  finally show ?thesis
    by assumption
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

lemma disjoint_vars_subset_mset: "disjoint_vars C D \<Longrightarrow> E \<subseteq># C \<Longrightarrow> disjoint_vars E D"
  by (metis disjoint_vars_plus_iff subset_mset.diff_add)

lemma disjoint_vars_subst_clsI:
  "disjoint_vars C D \<Longrightarrow> range_vars \<sigma> \<inter> vars_cls D = {} \<Longrightarrow> disjoint_vars (C \<cdot> \<sigma>) D"
  unfolding disjoint_vars_iff_inter_empty
  unfolding vars_subst_cls_eq
  by (smt (verit, best) Diff_subset Un_iff disjoint_iff image_cong subsetD vars_subst_cls_eq
      vars_subst_cls_subset)

definition disjoint_vars_set where
  "disjoint_vars_set N \<longleftrightarrow> (\<forall>C \<in> N. \<forall>D \<in> N. C \<noteq> D \<longrightarrow> disjoint_vars C D)"

lemma disjoint_vars_set_substetI[intro]: "disjoint_vars_set N \<Longrightarrow> M \<subseteq> N \<Longrightarrow> disjoint_vars_set M"
  unfolding disjoint_vars_set_def by auto

lemma disjoint_vars_set_insertI:
  assumes disj_N: "disjoint_vars_set N" and ball_disj_C: "\<forall>D \<in> N. C \<noteq> D \<longrightarrow> disjoint_vars C D"
  shows "disjoint_vars_set (insert C N)"
  unfolding disjoint_vars_set_def
proof (intro ballI impI)
  fix D\<^sub>0 D\<^sub>1
  assume "D\<^sub>0 \<in> insert C N" and "D\<^sub>1 \<in> insert C N" and "D\<^sub>0 \<noteq> D\<^sub>1"
  then show "disjoint_vars D\<^sub>0 D\<^sub>1"
    unfolding Set.insert_iff
    by (auto intro: disj_N[unfolded disjoint_vars_set_def, rule_format]
        intro: ball_disj_C[rule_format]
        intro: ball_disj_C[rule_format, unfolded disjoint_vars_sym[of C]])
qed

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

lemma disjoint_vars_set_mgu:
  assumes
    disj_N_D_L_L': "disjoint_vars_set N" and
    D_L_L'_in: "D + {#L, L'#} \<in> N" and
    range_vars_\<eta>: "range_vars \<eta> \<subseteq> vars_lit L \<union> vars_lit L'"
  shows "disjoint_vars_set (N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>})"
proof -
  have vars_D_L_\<eta>_subset: "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L, L'#})"
    by (rule vars_cls_subst_subset[OF range_vars_\<eta>])

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

lemma restrict_subst_Var[simp]: "restrict_subst V Var = Var"
  unfolding restrict_subst_def by auto

lemma subst_domain_restrict_subst: "subst_domain (restrict_subst V \<sigma>) \<subseteq> V"
  unfolding restrict_subst_def subst_domain_def
  by auto

lemma subst_restrict_subst_idem: "vars_term t \<subseteq> V \<Longrightarrow> t \<cdot>a restrict_subst V \<sigma> = t \<cdot>a \<sigma>"
  by (rule term_subst_eq) (simp add: restrict_subst_def subsetD)

lemma subst_lit_restrict_subst_idem: "vars_lit L \<subseteq> V \<Longrightarrow> L \<cdot>l restrict_subst V \<sigma> = L \<cdot>l \<sigma>"
  by (simp add: restrict_subst_def same_on_vars_lit subsetD)

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

lemma is_unifier_iff_mem_unifiers_Times:
  assumes fin_AA: "finite AA"
  shows "is_unifier \<upsilon> AA \<longleftrightarrow> \<upsilon> \<in> unifiers (AA \<times> AA)"
proof (rule iffI)
  assume unif_\<upsilon>_AA: "is_unifier \<upsilon> AA"
  show "\<upsilon> \<in> unifiers (AA \<times> AA)"
  unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    have "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<upsilon>) \<le> 1"
      by (rule unif_\<upsilon>_AA[unfolded is_unifier_def subst_atms_def])
  
    fix p assume "p \<in> AA \<times> AA"
    then obtain a b where p_def: "p = (a, b)" and "a \<in> AA" and "b \<in> AA"
      by auto
    hence "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<upsilon>) = 1"
      using fin_AA \<open>card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<upsilon>) \<le> 1\<close> antisym_conv2 by fastforce
  
    hence "a \<cdot>a \<upsilon> = b \<cdot>a \<upsilon>"
      using \<open>a \<in> AA\<close> \<open>b \<in> AA\<close> fin_AA is_unifier_subst_atm_eqI unif_\<upsilon>_AA by blast
    thus "fst p \<cdot>a \<upsilon> = snd p \<cdot>a \<upsilon>"
      by (simp add: p_def)
  qed
next
  assume unif_\<upsilon>_AA: "\<upsilon> \<in> unifiers (AA \<times> AA)"
  show "is_unifier \<upsilon> AA"
    using fin_AA unif_\<upsilon>_AA
  proof (induction AA arbitrary: \<upsilon> rule: finite_induct)
    case empty
    then show ?case
      by (simp add: is_unifier_def)
  next
    case (insert a AA)
    from insert.prems have
      \<upsilon>_in: "\<upsilon> \<in> unifiers ((insert (a, a) (Pair a ` AA) \<union> (\<lambda>x. (x, a)) ` AA) \<union> AA \<times> AA)"
      unfolding insert_Times_insert'[of a AA a AA] by simp
    then show ?case
      by (smt (verit, del_insts) Set.set_insert Un_insert_left finite.insertI fst_conv image_insert
          insert.hyps(1) insert_compr is_unifier_alt mem_Collect_eq snd_conv unifiers_def)
  qed
qed

lemma is_mgu_singleton_iff_Unifiers_is_mgu_Times:
  assumes fin: "finite AA"
  shows "is_mgu \<upsilon> {AA} \<longleftrightarrow> Unifiers.is_mgu \<upsilon> (AA \<times> AA)"
  by (auto simp: is_mgu_def Unifiers.is_mgu_def is_unifiers_def
      is_unifier_iff_mem_unifiers_Times[OF fin])

lemma is_imgu_singleton_iff_Unifiers_is_imgu_Times:
  assumes fin: "finite AA"
  shows "is_imgu \<upsilon> {AA} \<longleftrightarrow> Unifiers.is_imgu \<upsilon> (AA \<times> AA)"
  by (auto simp: is_imgu_def Unifiers.is_imgu_def is_unifiers_def
      is_unifier_iff_mem_unifiers_Times[OF fin])


lemma unifiers_without_refl: "unifiers E = unifiers {e \<in> E. fst e \<noteq> snd e}"
  (is "?lhs = ?rhs")
  unfolding unifiers_def by fastforce


subsubsection \<open>Minimal, Idempotent Most General Unifier\<close>

text \<open>It may be necessary to add @{term "subst_domain \<mu> \<subseteq> (\<Union>T \<in> TT. (\<Union>t \<in> T. vars_term t))"} at
one point.\<close>

definition is_mimgu where
  "is_mimgu \<mu> TT \<equiv> is_imgu \<mu> TT \<and> range_vars \<mu> \<subseteq> (\<Union>T \<in> TT. (\<Union>t \<in> T. vars_term t))"

lemma is_mimgu_if_mgu_eq_Some:
  assumes mgu_t_u: "Unification.mgu t u = Some \<mu>"
  shows "is_mimgu \<mu> {{t, u}}"
  unfolding is_mimgu_def
proof (rule conjI)
  have unifs_Times_t_u: "unifiers ({t, u} \<times> {t, u}) = unifiers {(t, u)}"
    by (auto simp: unifiers_def)
  have "Unifiers.is_imgu \<mu> ({t, u} \<times> {t, u})"
    using mgu_t_u[THEN mgu_sound]
    unfolding Unifiers.is_imgu_def
    unfolding unifs_Times_t_u
    by simp
  then show "is_imgu \<mu> {{t, u}}"
    by (simp add: is_imgu_singleton_iff_Unifiers_is_imgu_Times)
next
  show "range_vars \<mu> \<subseteq> (\<Union>T\<in>{{t, u}}. \<Union> (vars_term ` T))"
    using mgu_t_u
    by (simp add: mgu_subst_range_vars)
qed

primrec pairs where
  "pairs [] = []" |
  "pairs (x # xs) = (x, x) # map (Pair x) xs @ map (\<lambda>y. (y, x)) xs @ pairs xs"

lemma "set (pairs [a, b, c, d]) =
  {(a, a), (a, b), (a, c), (a, d),
   (b, a), (b, b), (b, c), (b, d),
   (c, a), (c, b), (c, c), (c, d),
   (d, a), (d, b), (d, c), (d, d)}"
  by auto

lemma set_pairs: "set (pairs xs) = set xs \<times> set xs"
  by (induction xs) auto

text \<open>Reflexive and symmetric pairs are not necessary to computing the MGU, but it makes the set of
the resulting list equivalent to @{term "{(x, y). x \<in> xs \<and> y \<in> ys}"}, which is necessary for the
following properties.\<close>

lemma pair_in_set_pairs: "a \<in> set as \<Longrightarrow> b \<in> set as \<Longrightarrow> (a, b) \<in> set (pairs as)"
  by (induction as) auto

lemma fst_pair_in_set_if_pair_in_pairs: "p \<in> set (pairs as) \<Longrightarrow> fst p \<in> set as"
  by (induction as) auto

lemma snd_pair_in_set_if_pair_in_pairs: "p \<in> set (pairs as) \<Longrightarrow> snd p \<in> set as"
  by (induction as) auto

lemma vars_mset_mset_pairs:
  "vars_mset (mset (pairs as)) = (\<Union>b \<in> set as. \<Union>a \<in> set as. vars_term a \<union> vars_term b)"
  by (induction as) (auto simp: vars_mset_def)

definition mgu_sets where
  "mgu_sets \<mu> AAA \<longleftrightarrow> (\<exists>ass. set (map set ass) = AAA \<and>
    map_option subst_of (unify (concat (map pairs ass)) []) = Some \<mu>)"

lemma is_mimgu_if_mgu_sets:
  assumes mgu_AAA: "mgu_sets \<mu> AAA"
  shows "is_mimgu \<mu> AAA"
  unfolding is_mimgu_def
proof (rule conjI)
  from mgu_AAA obtain ass xs where
    AAA_def: "AAA = set (map set ass)" and
    unify: "unify (concat (map pairs ass)) [] = Some xs" and
    "subst_of xs = \<mu>"
    unfolding mgu_sets_def by auto
  hence "Unifiers.is_imgu \<mu> (set (concat (map pairs ass)))"
    using unify_sound[OF unify] by simp
  moreover have "unifiers (set (concat (map pairs ass))) = {\<upsilon>. is_unifiers \<upsilon> AAA}"
    unfolding AAA_def
  proof (rule Set.equalityI; rule Set.subsetI; unfold mem_Collect_eq)
    fix x assume x_in: "x \<in> unifiers (set (concat (map pairs ass)))"
    show "is_unifiers x (set (map set ass))"
      unfolding is_unifiers_def
    proof (rule ballI)
      fix As assume "As \<in> set (map set ass)"
      hence "finite As" by auto

      from \<open>As \<in> set (map set ass)\<close> obtain as where
        as_in: "as \<in> set ass" and As_def: "As = set as"
        by auto

      show "is_unifier x As"
        unfolding is_unifier_alt[OF \<open>finite As\<close>]
      proof (intro ballI)
        fix A B assume "A \<in> As" "B \<in> As"
        hence "\<exists>xs \<in> set ass. (A, B) \<in> set (pairs xs)"
          using as_in by (auto simp: As_def intro: pair_in_set_pairs)
        thus "A \<cdot>a x = B \<cdot>a x"
          using x_in[unfolded unifiers_def mem_Collect_eq, rule_format, of "(A, B)", simplified]
          by simp
      qed
    qed
  next
    fix x assume is_unifs_x: "is_unifiers x (set (map set ass))"
    show "x \<in> unifiers (set (concat (map pairs ass)))"
      unfolding unifiers_def mem_Collect_eq
    proof (rule ballI)
      fix p assume "p \<in> set (concat (map pairs ass))"
      then obtain as where "as \<in> set ass" and p_in: "p \<in> set (pairs as)"
        by auto
      hence is_unif_x: "is_unifier x (set as)"
        using is_unifs_x[unfolded is_unifiers_def] by simp
      moreover have "fst p \<in> set as"
        by (rule p_in[THEN fst_pair_in_set_if_pair_in_pairs])
      moreover have "snd p \<in> set as"
        by (rule p_in[THEN snd_pair_in_set_if_pair_in_pairs])
      ultimately show "fst p \<cdot>a x = snd p \<cdot>a x"
        unfolding is_unifier_alt[of "set as", simplified]
        by blast
    qed
  qed
  ultimately show "is_imgu \<mu> AAA"
    unfolding Unifiers.is_imgu_def is_imgu_def by simp
next
  from mgu_AAA obtain Ass xs where
    AAA_def: "AAA = set (map set Ass)" and
    unify: "unify (concat (map pairs Ass)) [] = Some xs" and
    "subst_of xs = \<mu>"
    unfolding mgu_sets_def by auto

  then obtain ss where
    compose_ss: "compose ss = \<mu>" and
    UNIF_ss: "UNIF ss (mset (concat (map pairs Ass))) {#}"
    by (auto dest: unify_Some_UNIF)

  have "vars_mset (mset (concat (map pairs Ass))) = (\<Union>T\<in>AAA. \<Union> (vars_term ` T))"
    using AAA_def
  proof (induction Ass arbitrary: AAA)
    case Nil
    thus ?case by (simp add: vars_mset_def)
  next
    case (Cons As Ass)
    from Cons.prems have AAA_def': "AAA = insert (set As) (set (map set Ass))"
      by simp
    moreover have "vars_mset (mset (pairs As)) = \<Union> (vars_term ` set As)"
      by (simp add: vars_mset_mset_pairs)
    ultimately show ?case
      by (simp add: Cons.IH[OF refl])
  qed
  then show "range_vars \<mu> \<subseteq> (\<Union>T\<in>AAA. \<Union> (vars_term ` T))"
    using UNIF_range_vars_subset[OF UNIF_ss, unfolded compose_ss]
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

lemma inv_renaming'_Var[simp]: "inv_renaming' Var = Var"
  unfolding inv_renaming'_def
  by (metis id_subst_comp_subst is_renaming_id_subst inv_renaming'_def inv_renaming'_sound)

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

lemma disjoint_vars_rename_clause:
  assumes fin_N: "finite N" and D_in: "D \<in> N"
  shows "disjoint_vars (rename_clause N C) D"
proof -
  from fin_N have "finite (\<Union> (vars_cls ` N))"
    by auto
  hence "vars_cls (C \<cdot> renaming_wrt N) \<inter> \<Union> (vars_cls ` N) = {}"
    by (rule vars_cls_subst_renaming_disj)
  thus ?thesis
    unfolding disjoint_vars_iff_inter_empty rename_clause_def
    using D_in by blast
qed

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

lemma subst_domain_renaming_wrt:
  fixes N
  shows "finite N \<Longrightarrow> subst_domain (renaming_wrt N) = UNIV"
  unfolding subst_domain_def
  using renaming_all by force

lemma vars_cls_rename_clause_eq_empty:
  fixes N C
  shows "finite N \<Longrightarrow> vars_cls (rename_clause N C) = {} \<longleftrightarrow> vars_cls C = {}"
  by (simp add: rename_clause_def vars_subst_cls_eq subst_domain_renaming_wrt)

lemma is_ground_cls_rename_clause[simp]:
  fixes N C
  shows "finite N \<Longrightarrow> is_ground_cls (rename_clause N C) \<longleftrightarrow> is_ground_cls C"
  by (simp add: is_ground_cls_iff_vars_empty vars_cls_rename_clause_eq_empty)

lemma rename_clause_ident_if_ground[simp]:
  fixes N C
  shows "is_ground_cls C \<Longrightarrow> rename_clause N C = C"
  by (simp add: rename_clause_def)

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

abbreviation initial_state :: "('f, 'v) state" where
  "initial_state \<equiv> ([], {}, None)"

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

lemma clss_of_trail_append: "clss_of_trail (\<Gamma>\<^sub>0 @ \<Gamma>\<^sub>1) = clss_of_trail \<Gamma>\<^sub>0 \<union> clss_of_trail \<Gamma>\<^sub>1"
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
    (if trail_level (Lc # \<Gamma>) \<le> level then
      Lc # \<Gamma>
    else
      trail_backtrack \<Gamma> level)"

lemma trail_backtrack_inv: "trail_level \<Gamma> < level \<Longrightarrow> trail_backtrack \<Gamma> level = \<Gamma>"
  by (cases \<Gamma>) simp_all

lemma trail_backtrack_suffix: "suffix (trail_backtrack \<Gamma> level) \<Gamma>"
  by (induction \<Gamma>) (simp_all add: suffix_ConsI)

lemma clss_of_trail_trail_decide_subset:
  "clss_of_trail (trail_backtrack \<Gamma> n) \<subseteq> clss_of_trail \<Gamma>"
  unfolding trail_decide_def clss_of_trail_def
  by (simp add: SUP_subset_mono set_mono_suffix trail_backtrack_suffix)

lemma ball_set_trail_backtrackI: "\<forall>x \<in> set \<Gamma>. P x \<Longrightarrow> \<forall>x \<in> set (trail_backtrack \<Gamma> level). P x"
  by (meson set_mono_suffix subset_eq trail_backtrack_suffix)

lemma trail_backtrack_level: "trail_level (trail_backtrack \<Gamma> level) =
  (if level \<le> trail_level \<Gamma> then level else trail_level \<Gamma>)"
  by (induction \<Gamma>) auto

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

lemma trail_true_or_false_cls_if_defined:
  "trail_defined_cls \<Gamma> C \<Longrightarrow> trail_true_cls \<Gamma> C \<or> trail_false_cls \<Gamma> C"
  unfolding trail_defined_cls_def trail_false_cls_def trail_true_cls_def
  unfolding trail_defined_lit_iff_true_or_false
  by blast

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

lemma not_trail_defined_lit_Nil[simp]: "\<not> trail_defined_lit [] L"
  by (simp add: trail_defined_lit_iff_true_or_false)

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

lemma subtrail_falseI:
  assumes tr_false: "trail_false_cls ((L, Cl) # \<Gamma>) C" and L_not_in: "-L \<notin># C"
  shows "trail_false_cls \<Gamma> C"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix M
  assume M_in: "M \<in># C"

  from M_in L_not_in have M_neq_L: "M \<noteq> -L" by auto

  from M_in tr_false have tr_false_lit_M: "trail_false_lit ((L, Cl) # \<Gamma>) M"
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
    imgu_\<mu>: "is_imgu \<mu> {{atm_of L, atm_of L'}}" and
    unif_\<sigma>: "is_unifiers \<sigma> {{atm_of L, atm_of L'}}"
  shows "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix K
  assume "K \<in># (D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>"
  hence "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<or> K = L  \<cdot>l \<mu> \<cdot>l \<sigma>" by force
  thus "trail_false_lit \<Gamma> K"
  proof (elim disjE)
    show "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
      using imgu_\<mu> unif_\<sigma>
      by (metis is_imgu_def subst_cls_comp_subst subst_cls_union tr_false_cls trail_false_cls_def
          union_iff)
  next
    have "L \<cdot>l \<mu> \<cdot>l \<sigma> = L \<cdot>l \<sigma>"
      using imgu_\<mu> unif_\<sigma> by (metis is_imgu_def subst_lit_comp_subst)
    thus "K = L \<cdot>l \<mu> \<cdot>l \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
      by (auto intro: tr_false_cls[unfolded trail_false_cls_def, rule_format])
  qed
qed

lemma trail_defined_lit_iff_defined_uminus: "trail_defined_lit \<Gamma> L \<longleftrightarrow> trail_defined_lit \<Gamma> (-L)"
  by (auto simp add: trail_defined_lit_def)

lemma not_trail_backtrack_defined_if_not_defined:
  assumes not_\<Gamma>_defined_L:  "\<not> trail_defined_lit \<Gamma> L"
  shows "\<not> trail_defined_lit (trail_backtrack \<Gamma> level) L"
proof -
  have "suffix (trail_backtrack \<Gamma> level) \<Gamma>"
    by (rule trail_backtrack_suffix)
  hence "set (trail_backtrack \<Gamma> level) \<subseteq> set \<Gamma>"
    by (rule set_mono_suffix)
  with not_\<Gamma>_defined_L show ?thesis
    unfolding trail_defined_lit_def by fast
qed

lemma trail_level_propagate[simp]:
  "trail_level (trail_propagate \<Gamma> L C \<gamma>) = trail_level \<Gamma>"
  by (simp add: trail_propagate_def is_decision_lit_def)

lemma trail_level_decide[simp]:
  "trail_level (trail_decide \<Gamma> L) = Suc (trail_level \<Gamma>)"
  by (simp add: trail_decide_def is_decision_lit_def)

lemma trail_defined_lit_iff: "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L \<in> atm_of ` fst ` set \<Gamma>"
  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_defined_lit_def)

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

inductive trail_consistent where
  Nil: "trail_consistent []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> trail_consistent \<Gamma> \<Longrightarrow> trail_consistent ((L, u) # \<Gamma>)"

lemma trail_interp_lit_if_trail_true:
  shows "trail_consistent \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma> L \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile>l L"
proof (induction \<Gamma> rule: trail_consistent.induct)
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
          using Cons.hyps(1)
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

lemma trail_interp_cls_if_trail_true:
  assumes "trail_consistent \<Gamma>" and "trail_true_cls \<Gamma> C"
  shows "trail_interp \<Gamma> \<TTurnstile> C"
proof -
  from \<open>trail_true_cls \<Gamma> C\<close> obtain L where "L \<in># C" and "trail_true_lit \<Gamma> L"
    by (auto simp: trail_true_cls_def)
  show ?thesis
    unfolding true_cls_def
  proof (rule bexI[OF _ \<open>L \<in># C\<close>])
    show "trail_interp \<Gamma> \<TTurnstile>l L"
      by (rule trail_interp_lit_if_trail_true[OF \<open>trail_consistent \<Gamma>\<close> \<open>trail_true_lit \<Gamma> L\<close>])
  qed
qed

lemma trail_true_cls_iff_trail_interp_entails:
  assumes "trail_consistent \<Gamma>" "\<forall>L \<in># C. trail_defined_lit \<Gamma> L"
  shows "trail_true_cls \<Gamma> C \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
proof (rule iffI)
  assume "trail_true_cls \<Gamma> C"
  thus "trail_interp \<Gamma> \<TTurnstile> C"
    using assms(1) trail_interp_cls_if_trail_true by fast
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
      by (metis assms(1) assms(2) trail_defined_lit_def trail_interp_lit_if_trail_true
          trail_true_lit_def true_lit_simps(2) uminus_Pos)
  next
    case (Neg t)
    then show ?thesis
      by (metis \<open>L \<in># C\<close> \<open>trail_interp \<Gamma> \<TTurnstile>l L\<close> assms(1) assms(2) trail_defined_lit_def
          trail_interp_lit_if_trail_true trail_true_cls_def trail_true_lit_def true_lit_simps(1,2)
          uminus_Neg)
  qed
qed


section \<open>SCL Calculus\<close>

locale scl = renaming_apart renaming_vars inv_renaming_vars
  for renaming_vars inv_renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes less_B :: "('f, 'v) term literal \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" (infix "\<prec>\<^sub>B" 50)
  assumes transp_less_B: "transp (\<prec>\<^sub>B)"
begin

inductive propagate :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  propagateI: "C \<in> N \<union> U \<Longrightarrow> C' + {#L#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C \<Longrightarrow>
    subst_domain \<gamma> \<subseteq> vars_cls C' \<union> vars_lit L \<Longrightarrow> is_ground_cls ((C' + {#L#}) \<cdot> \<gamma>) \<Longrightarrow>
    C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#} \<Longrightarrow> C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#} \<Longrightarrow>
    trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    is_mimgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<Longrightarrow>
    \<gamma>' = restrict_subst (vars_cls (add_mset L C\<^sub>0 \<cdot> \<mu>)) \<gamma> \<Longrightarrow>
    \<forall>K \<in># add_mset L C' \<cdot> \<gamma>. K \<prec>\<^sub>B \<beta> \<Longrightarrow>
    propagate N \<beta> (\<Gamma>, U, None) (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>', U, None)"

inductive decide :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  decideI: "L \<in> \<Union>(set_mset ` N) \<Longrightarrow> is_ground_lit (L \<cdot>l \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    L \<cdot>l \<gamma> \<prec>\<^sub>B \<beta> \<Longrightarrow>
    decide N \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None)"

inductive conflict :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  conflictI: "D \<in> N \<union> U \<Longrightarrow> D' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D \<Longrightarrow>
    subst_domain \<sigma> \<subseteq> vars_cls D' \<Longrightarrow> is_ground_cls (D' \<cdot> \<sigma>) \<Longrightarrow> trail_false_cls \<Gamma> (D' \<cdot> \<sigma>) \<Longrightarrow>
    conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (D', \<sigma>))"

inductive skip :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  skipI: "-L \<notin># D \<cdot> \<sigma> \<Longrightarrow> D \<noteq> {#} \<Longrightarrow>
    skip N \<beta> ((L, n) # \<Gamma>, U, Some (D, \<sigma>)) (\<Gamma>, U, Some (D, \<sigma>))"

inductive factorize :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  factorizeI: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma> \<Longrightarrow> is_mimgu \<mu> {{atm_of L, atm_of L'}} \<Longrightarrow>
    \<sigma>' = restrict_subst (vars_cls ((D + {#L#}) \<cdot> \<mu>)) \<sigma> \<Longrightarrow>
    factorize N \<beta> (\<Gamma>, U, Some (D + {#L,L'#}, \<sigma>)) (\<Gamma>, U, Some ((D + {#L#}) \<cdot> \<mu>, \<sigma>'))"

inductive resolve :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  resolveI: "\<Gamma> = trail_propagate \<Gamma>' L C \<delta> \<Longrightarrow>
    \<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}}) \<Longrightarrow>
    (L \<cdot>l \<delta>) = -(L' \<cdot>l \<sigma>) \<Longrightarrow> is_mimgu \<mu> {{atm_of L, atm_of L'}} \<Longrightarrow>
    resolve N \<beta> (\<Gamma>, U, Some (D + {#L'#}, \<sigma>)) (\<Gamma>, U, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>,
      restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)))"

inductive backtrack :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  backtrackI: "\<Gamma> = trail_decide (\<Gamma>' @ \<Gamma>'') (- (L \<cdot>l \<sigma>)) \<Longrightarrow>
    \<nexists>S'. conflict N \<beta> (\<Gamma>'', insert (add_mset L D) U, None) S' \<Longrightarrow>
    backtrack N \<beta> (\<Gamma>, U, Some (D + {#L#}, \<sigma>)) (\<Gamma>'', insert (add_mset L D) U, None)"

definition scl :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" where
  "scl N \<beta> S S' \<longleftrightarrow> propagate N \<beta> S S' \<or> decide N \<beta> S S' \<or> conflict N \<beta> S S' \<or> skip N \<beta> S S' \<or>
    factorize N \<beta> S S' \<or> resolve N \<beta> S S' \<or> backtrack N \<beta> S S'"

text \<open>Note that, in contrast to Fiori and Weidenbach (CADE 2019), the set of clauses @{term N} is a
parameter of the relation instead of being repeated twice in the state. This is to highlight the
fact that it is a constant.\<close>


subsection \<open>Well-Defined\<close>

lemma propagate_well_defined:
  assumes "propagate N \<beta> S S'"
  shows
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma decide_well_defined:
  assumes "decide N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma conflict_well_defined:
  assumes "conflict N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma skip_well_defined:
  assumes "skip N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma factorize_well_defined:
  assumes "factorize N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    (* "\<not> resolve N \<beta> S S'" *)
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma resolve_well_defined:
  assumes "resolve N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    (* "\<not> factorize N \<beta> S S'" *)
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)

lemma backtrack_well_defined:
  assumes "backtrack N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: trail_decide_def trail_propagate_def)


section \<open>Soundness\<close>

abbreviation entails_\<G> (infix "\<TTurnstile>\<G>e" 50) where
  "entails_\<G> N U \<equiv> grounding_of_clss N \<TTurnstile>e grounding_of_clss U"

inductive sound_trail for N U where
  Nil[simp]: "sound_trail N U []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> is_ground_lit L \<Longrightarrow>
    (case u of
      None \<Rightarrow> True |
      Some (C, L', \<gamma>) \<Rightarrow> L = L' \<cdot>l \<gamma> \<and> subst_domain \<gamma> \<subseteq> vars_cls C \<union> vars_lit L' \<and>
        is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and> N \<TTurnstile>\<G>e {C + {#L'#}}) \<Longrightarrow>
    sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U ((L, u) # \<Gamma>)"

lemma trail_consistent_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> trail_consistent \<Gamma>"
  by (induction \<Gamma> rule: sound_trail.induct) (simp_all add: trail_consistent.intros)

lemma entails_\<G>_mono: "N \<TTurnstile>\<G>e U \<Longrightarrow> N \<subseteq> NN \<Longrightarrow> NN \<TTurnstile>\<G>e U"
  by (meson grounding_of_clss_mono true_clss_mono)

lemma sound_trail_supersetI: "sound_trail N U \<Gamma> \<Longrightarrow> N \<subseteq> NN \<Longrightarrow> U \<subseteq> UU \<Longrightarrow> sound_trail NN UU \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  thus ?case by simp
next
  case (Cons \<Gamma> L u)
  show ?case
  proof (intro sound_trail.Cons)
    show
      "case u of
        None \<Rightarrow> True
      | Some (C, L', \<gamma>) \<Rightarrow> L = L' \<cdot>l \<gamma> \<and> subst_domain \<gamma> \<subseteq> vars_cls C \<union> vars_lit L' \<and>
          is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and> NN \<TTurnstile>\<G>e {C + {#L'#}}"
    proof (cases u)
      case None
      then show ?thesis by simp
    next
      case (Some Cl)
      moreover obtain C L' \<gamma> where Cl_def: "Cl = (C, L', \<gamma>)"
        using prod_cases3 by blast
      moreover have "NN \<TTurnstile>\<G>e {C + {#L'#}}"
      proof -
        have "N \<TTurnstile>\<G>e {C + {#L'#}}"
          using Cons.hyps
          by (auto simp: Some Cl_def)
        thus ?thesis
          apply (rule entails_\<G>_mono)
          using Cons.prems by simp
      qed
      ultimately show ?thesis
        using Cons by simp
    qed
  qed (use Cons in simp_all)
qed

lemma sound_subtrailI[intro]: "sound_trail N U (Ln # \<Gamma>) \<Longrightarrow> sound_trail N U \<Gamma>"
  by (auto elim: sound_trail.cases)

lemma ball_ground_lit_if_sound_trail: "sound_trail N U \<Gamma> \<Longrightarrow> \<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  show ?case by simp
next
  case (Cons \<Gamma> L u)
  thus ?case by auto
qed 

lemma sound_trail_appendD: "sound_trail N U (\<Gamma> @ \<Gamma>') \<Longrightarrow> sound_trail N U \<Gamma>'"
  by (induction \<Gamma>) auto

lemma sound_trail_backtrackI: "sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U (trail_backtrack \<Gamma> level)"
  by (induction \<Gamma> rule: sound_trail.induct) (auto intro: sound_trail.intros)

lemma sound_trail_propagate:
  assumes
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    not_tr_def_\<Gamma>_L_\<sigma>: "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>)" and
    domain_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls C \<union> vars_lit L" and
    gr_C_L_\<sigma>: "is_ground_cls ((C + {#L#}) \<cdot> \<sigma>)" and
    tr_false_\<Gamma>_C_\<sigma>: "trail_false_cls \<Gamma> (C \<cdot> \<sigma>)" and
    N_entails_C_L: "N \<TTurnstile>\<G>e {C + {#L#}}"
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
  show "L \<cdot>l \<sigma> = L \<cdot>l \<sigma> \<and> subst_domain \<sigma> \<subseteq> vars_cls C \<union> vars_lit L \<and>
    is_ground_cls ((C + {#L#}) \<cdot> \<sigma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<sigma>) \<and> N \<TTurnstile>\<G>e {C + {#L#}}"
    using domain_\<sigma> gr_C_L_\<sigma> tr_false_\<Gamma>_C_\<sigma> N_entails_C_L by simp
qed

lemma sound_trail_decide:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow> is_ground_lit L \<Longrightarrow>
  sound_trail N U (trail_decide \<Gamma> L)"
  unfolding trail_decide_def
  by (auto intro: sound_trail.Cons)

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


subsection \<open>Miscellaneous Lemmas\<close>

lemma not_trail_defined_lit_backtrack_if_level_lit_gt_level_backtrack:
  assumes sound_\<Gamma>: "sound_trail N U \<Gamma>"
  shows "level < trail_level \<Gamma> \<Longrightarrow> level < trail_level_lit \<Gamma> L \<Longrightarrow>
  \<not> trail_defined_lit (trail_backtrack \<Gamma> level) L"
  using sound_\<Gamma>
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case by simp
next
  case (Cons \<Gamma> K u)
  from Cons.hyps have not_\<Gamma>_defined_K: "\<not> trail_defined_lit \<Gamma> K" by simp
  
  show ?case
  proof (cases "trail_level ((K, u) # \<Gamma>) \<le> level")
    case True
    thus ?thesis
      using Cons.prems(1) by (simp del: trail_level.simps add: trail_defined_lit_def)
  next
    case not_trail_level_K_\<Gamma>_le: False
    show ?thesis
    proof (cases "K = L \<or> K = - L")
      case K_eq_L: True
      then show ?thesis
        using not_trail_level_K_\<Gamma>_le not_\<Gamma>_defined_K
        apply (simp del: trail_level.simps add: trail_defined_lit_def)
        by (metis not_trail_backtrack_defined_if_not_defined trail_defined_lit_def uminus_of_uminus_id)
    next
      case K_neq_L: False
      then show ?thesis
        using not_trail_level_K_\<Gamma>_le
        apply (simp del: trail_level.simps add: trail_defined_lit_def)
        by (metis (no_types, lifting) Cons.IH Cons.prems(2) fst_conv leD nless_le order.trans
            trail_defined_lit_def trail_level_lit.simps(2) trail_level_lit_le)
    qed
  qed
qed


subsection \<open>Initial State Is Sound\<close>

lemma sound_initial_state[simp]: "finite N \<Longrightarrow> disjoint_vars_set N \<Longrightarrow> sound_state N initial_state"
  by (simp add: sound_state_def)


subsection \<open>SCL Rules Preserve Soundness\<close>

lemma propagate_sound_state: "propagate N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: propagate.induct)
  case (propagateI C U C' L \<Gamma> \<gamma> C\<^sub>0 C\<^sub>1 \<mu> \<gamma>')
  from propagateI.prems have
    fin: "finite N" "finite U" and
    disj_N_U_\<Gamma>: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto

  from propagateI.hyps have
    C_in: "C \<in> N \<union> U" and
    rename_C: "C' + {#L#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C" and
    domain_\<gamma>: "subst_domain \<gamma> \<subseteq> vars_cls C' \<union> vars_lit L" and
    gr_C'_L_\<gamma>: "is_ground_cls ((C' + {#L#}) \<cdot> \<gamma>)" and
    C\<^sub>0_def: "C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#}" and
    C\<^sub>1_def: "C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}" and
    \<Gamma>_false_C\<^sub>0_\<gamma>: "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>)" and
    undef_\<Gamma>_L_\<gamma>: "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)" and
    is_mimgu_\<mu>: "is_mimgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}" and
    \<gamma>'_def: "\<gamma>' = restrict_subst (vars_cls (add_mset L C\<^sub>0 \<cdot> \<mu>)) \<gamma>"
    by simp_all

  have fin_N_U_\<Gamma>: "finite (N \<union> U \<union> clss_of_trail \<Gamma>)"
    using fin by simp

  from is_mimgu_\<mu> have range_vars_\<mu>: "range_vars \<mu> \<subseteq> vars_lit L \<union> vars_cls C\<^sub>1"
    by (simp add: is_mimgu_def vars_cls_def)

  have vars_C\<^sub>1: "vars_cls C\<^sub>1 \<subseteq> vars_cls C'"
    apply (simp add: C\<^sub>1_def)
    by (metis multiset_partition order_refl sup.coboundedI1 vars_cls_plus_iff)

  have fin_atm_C\<^sub>1: "finite (atm_of ` (set_mset C\<^sub>1))"
    by blast
  hence "is_unifier \<gamma> (atm_of ` (set_mset (add_mset L C\<^sub>1)))"
    by (auto simp add: is_unifier_alt C\<^sub>1_def intro: subst_atm_of_eqI)
  hence \<mu>_\<gamma>_simp: "\<mu> \<odot> \<gamma> = \<gamma>"
    using is_mimgu_\<mu>[unfolded is_mimgu_def, THEN conjunct1, unfolded is_imgu_def, THEN conjunct2]
    using is_unifiers_def by fastforce

  have "disjoint_vars_set (insert (add_mset (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>)) (N \<union> U \<union> clss_of_trail \<Gamma>))"
  proof (intro disjoint_vars_set_insertI[OF disj_N_U_\<Gamma>] ballI impI)
    fix D assume D_in: "D \<in> N \<union> U \<union> clss_of_trail \<Gamma>"
    hence disj_L_C: "disjoint_vars (add_mset L C') D"
      using rename_C disjoint_vars_rename_clause[OF fin_N_U_\<Gamma>] by auto
    hence "disjoint_vars ((add_mset L C') \<cdot> \<mu>) D"
    proof (rule disjoint_vars_subst_clsI)
      show "range_vars \<mu> \<inter> vars_cls D = {}"
        using range_vars_\<mu> vars_C\<^sub>1 disj_L_C
        unfolding disjoint_vars_iff_inter_empty
        by auto
    qed
    hence "disjoint_vars ((add_mset L C\<^sub>0) \<cdot> \<mu>) D"
      using C\<^sub>0_def disjoint_vars_subset_mset
      by (metis mset_subset_eq_add_mset_cancel multiset_filter_subset subst_cls_mono_mset)
    thus "disjoint_vars (add_mset (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>)) D"
      by simp
  qed

  moreover have "sound_trail N U (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>')"
  proof (rule sound_trail_propagate)
    show "sound_trail N U \<Gamma>"
      by (rule sound_\<Gamma>)
  next
    have "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
      using undef_\<Gamma>_L_\<gamma> \<mu>_\<gamma>_simp
      by (metis subst_lit_comp_subst)
    thus "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<gamma>')"
      by (simp add: \<gamma>'_def subst_lit_restrict_subst_idem)
  next
    show "subst_domain \<gamma>' \<subseteq> vars_cls (C\<^sub>0 \<cdot> \<mu>) \<union> vars_lit (L \<cdot>l \<mu>)"
      unfolding \<gamma>'_def
      by (simp add: subst_domain_restrict_subst sup_commute)
  next
    have "(C\<^sub>0 + {#L#}) \<cdot> \<gamma> \<subseteq># (C' + {#L#}) \<cdot> \<gamma>"
      unfolding C\<^sub>0_def
      by (meson multiset_filter_subset subset_mset.add_le_cancel_right subst_cls_mono_mset)
    hence "is_ground_cls ((C\<^sub>0 + {#L#}) \<cdot> (\<mu> \<odot> \<gamma>))"
      unfolding \<mu>_\<gamma>_simp
      by (rule is_ground_cls_mono[OF _ gr_C'_L_\<gamma>])
    hence "is_ground_cls ((C\<^sub>0 \<cdot> \<mu> + {#L \<cdot>l \<mu>#}) \<cdot> \<gamma>)"
      by simp
    thus "is_ground_cls ((C\<^sub>0 \<cdot> \<mu> + {#L \<cdot>l \<mu>#}) \<cdot> \<gamma>')"
      by (metis \<gamma>'_def add_mset_add_single subsetI subst_cls_add_mset subst_cls_restrict_subst_idem)
  next
    have "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma>)"
      using \<Gamma>_false_C\<^sub>0_\<gamma> \<mu>_\<gamma>_simp
      by (metis subst_cls_comp_subst)
    thus "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma>')"
      by (simp add: \<gamma>'_def subst_cls_restrict_subst_idem)
  next
    from C_in N_entails_U have "N \<TTurnstile>\<G>e {C}"
      by (meson Un_iff empty_subsetI grounding_of_clss_mono insert_subset true_clss_mono)
    with rename_C have "N \<TTurnstile>\<G>e {C' + {#L#}}"
      by (metis fin_N_U_\<Gamma> grounding_of_cls_rename_clause grounding_of_clss_singleton)
    with C\<^sub>0_def C\<^sub>1_def have "N \<TTurnstile>\<G>e {C\<^sub>0 + C\<^sub>1 + {#L#}}"
      by auto
    hence "N \<TTurnstile>\<G>e {(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>}"
      by (metis (no_types, opaque_lifting) grounding_of_clss_singleton
          subst_cls_eq_grounding_of_cls_subset_eq true_clss_mono)
    hence "N \<TTurnstile>\<G>e {(C\<^sub>0 + {#L#}) \<cdot> \<mu>}"
    proof (rule entails_trans)
      have "\<exists>C\<in>grounding_of_clss {(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>}. set_mset D = set_mset C"
        if D_in: "D \<in> grounding_of_clss {(C\<^sub>0 + {#L#}) \<cdot> \<mu>}" for I D
      proof-
        from D_in obtain \<sigma> where
          D_def: "D = add_mset L C\<^sub>0 \<cdot> \<mu> \<cdot> \<sigma>" and gr_\<sigma>: "is_ground_subst \<sigma>"
          by (auto simp: grounding_of_cls_def)
        show ?thesis
        proof (rule bexI)
          from is_mimgu_\<mu> have "is_unifier \<mu> (atm_of ` set_mset (add_mset L C\<^sub>1))"
            by (simp add: is_mimgu_def is_imgu_def is_unifiers_def)
          hence "\<forall>A\<in>atm_of ` set_mset (add_mset L C\<^sub>1). \<forall>B\<in>atm_of ` set_mset (add_mset L C\<^sub>1).
            A \<cdot>a \<mu> = B \<cdot>a \<mu>"
            using is_unifier_alt
            by (metis (mono_tags, opaque_lifting) finite_imageI finite_set_mset)
          hence "\<forall>A\<in>atm_of ` set_mset C\<^sub>1. A \<cdot>a \<mu> = atm_of L \<cdot>a \<mu>"
            by (metis image_insert insert_iff set_mset_add_mset_insert)
          hence "\<forall>A\<in>set_mset C\<^sub>1. A \<cdot>l \<mu> = L \<cdot>l \<mu>"
            unfolding C\<^sub>1_def
            by (metis (mono_tags, lifting) atm_of_subst_lit image_eqI literal.expand mem_Collect_eq
                set_mset_filter subst_lit_is_neg)
          hence "set_mset ((add_mset L C\<^sub>1) \<cdot> \<mu>) = {L \<cdot>l \<mu>}"
            by auto
          hence "set_mset ((C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>) = set_mset ((C\<^sub>0 + {#L#}) \<cdot> \<mu>)"
            by auto
          thus "set_mset D = set_mset ((C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
            unfolding D_def set_mset_subst_cls_conv[of _ \<sigma>]
            by simp
        next
          show "(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu> \<cdot> \<sigma> \<in> grounding_of_clss {(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>}"
            using gr_\<sigma> by (auto simp: grounding_of_cls_def)
        qed
      qed
      then show "{(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>} \<TTurnstile>\<G>e {(C\<^sub>0 + {#L#}) \<cdot> \<mu>}"
        by (auto elim: true_clss_if_set_mset_eq[rotated])
    qed
    thus "N \<TTurnstile>\<G>e {C\<^sub>0 \<cdot> \<mu> + {#L \<cdot>l \<mu>#}}"
      by simp
  qed

  ultimately show ?case
    unfolding sound_state_def
    using fin N_entails_U by simp
qed

lemma decide_sound_state: "decide N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: decide.induct)
  case (decideI L \<gamma> \<Gamma> U)
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

lemma conflict_sound_state: "conflict N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
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

lemma skip_sound_state: "skip N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: skip.induct)
  case (skipI L D \<sigma> Cl \<Gamma> U)
  thus ?case
    by (auto simp: sound_state_def clss_of_trail_Cons[of _ \<Gamma>] elim!: subtrail_falseI)
qed

lemma factorize_sound_state: "factorize N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
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

  from factorizeI.hyps have
    imgu_\<mu>: "is_imgu \<mu> {{atm_of L, atm_of L'}}" and
    range_vars_\<mu>: "range_vars \<mu> \<subseteq> vars_lit L \<union> vars_lit L'"
    by (simp_all add: is_mimgu_def)
  from factorizeI.hyps have L_eq_L'_\<sigma>: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma>" by simp
  from factorizeI.hyps have \<sigma>'_def: "\<sigma>' = restrict_subst (vars_cls ((D + {#L#}) \<cdot> \<mu>)) \<sigma>" by simp

  from L_eq_L'_\<sigma> have unif_\<sigma>: "is_unifier \<sigma> {atm_of L, atm_of L'}"
    by (auto simp: is_unifier_alt intro: subst_atm_of_eqI)
  hence unifs_\<sigma>: "is_unifiers \<sigma> {{atm_of L, atm_of L'}}"
    by (simp add: is_unifiers_def)

  from imgu_\<mu> have "is_unifier \<mu> {atm_of L, atm_of L'}"
    by (auto simp add: is_unifiers_def dest: is_imgu_is_mgu[THEN is_mgu_is_unifiers])
  hence L_eq_L'_\<mu>: "L \<cdot>l \<mu> = L' \<cdot>l \<mu>"
    apply (simp add: is_unifier_alt)
    by (metis L_eq_L'_\<sigma> atm_of_subst_lit literal.expand subst_lit_is_neg)

  have "disjoint_vars ((D + {#L#}) \<cdot> \<mu>) C" if C_in: "C \<in> N \<union> U \<union> clss_of_trail \<Gamma>" for C
    using disj_N_U_D_L_L'[rule_format, OF C_in]
    unfolding disjoint_vars_iff_inter_empty
    using range_vars_\<mu> vars_subst_cls_subset_weak[of "D + {#L#}" \<mu>]
    by auto

  moreover have "subst_domain \<sigma>' \<subseteq> vars_cls ((D + {#L#}) \<cdot> \<mu>)"
    unfolding \<sigma>'_def using subst_domain_restrict_subst by metis

  moreover have "is_ground_cls ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
  proof -
    have "is_ground_cls ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
      using gr_D_L_L'_\<sigma>
      by (smt (verit) range_vars_\<mu> Diff_eq_empty_iff UN_Un Un_empty dom_\<sigma>
          is_ground_cls_iff_vars_empty subset_antisym sup.orderE vars_cls_subst_subset
          vars_subst_cls_eq)
    thus ?thesis
      unfolding \<sigma>'_def using subst_cls_restrict_subst_idem by (metis subsetI)
  qed

  moreover have "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
  proof -
    show ?thesis
      unfolding \<sigma>'_def
      using subst_cls_restrict_subst_idem
      using trail_false_cls_subst_mgu_before_grounding[OF tr_false_cls imgu_\<mu> unifs_\<sigma>]
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
    is_imgu_\<mu>: "is_imgu \<mu> {{atm_of L, atm_of L'}}" and
    is_unifs_\<sigma>_\<delta>: "is_unifiers (\<sigma> \<odot> \<delta>) {{atm_of L, atm_of L'}}"
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
      using is_imgu_\<mu> is_unifs_\<sigma>_\<delta>
      by (metis Simple_Clause_Learning.is_imgu_def subst_cls_comp_subst)
    hence "K \<in># D \<cdot> \<sigma>"
      using gr_D_L'_\<sigma> is_ground_subst_cls by (metis is_ground_cls_union subst_cls_union)
    then show ?thesis
      by (auto intro!: tr_false_\<Gamma>_D_L'_\<sigma>[unfolded trail_false_cls_def, rule_format])
  next
    assume "K \<in># C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
    hence "K \<in># C \<cdot> \<sigma> \<cdot> \<delta>"
      using is_imgu_\<mu> is_unifs_\<sigma>_\<delta>
      by (metis Simple_Clause_Learning.is_imgu_def subst_cls_comp_subst)
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

lemma resolve_sound_state: "resolve N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: resolve.induct)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
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
  from resolveI.hyps have is_mimgu_\<mu>: "is_mimgu \<mu> {{atm_of L, atm_of L'}}" by simp
  hence is_imgu_\<mu>: "is_imgu \<mu> {{atm_of L, atm_of L'}}" by (simp add: is_mimgu_def)
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
    N_entails_C_L: "N \<TTurnstile>\<G>e {C + {#L#}}" and
    dom_\<delta>: "subst_domain \<delta> \<subseteq> vars_cls (C + {#L#})"
    unfolding sound_trail.simps[of _ _ \<Gamma>]
    unfolding \<Gamma>_def trail_propagate_def
    by auto

  from L_eq_comp_L' have "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
    by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
  hence "atm_of L \<cdot>a \<sigma> \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma> \<cdot>a \<delta>"
  proof (rule subst_subst_eq_subst_subst_if_subst_eq_substI)
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
  hence is_unifs_\<sigma>_\<delta>: "is_unifiers (\<sigma> \<odot> \<delta>) {{atm_of L, atm_of L'}}"
    by (simp add: is_unifiers_def is_unifier_def subst_atms_def)

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
            vars_lit_subst_renaming_disj resolveI.hyps(2) atm_of_subst_lit)

    show ?thesis
      unfolding subst_cls_union disjoint_vars_plus_iff
    proof (rule conjI)
      show "disjoint_vars (D \<cdot> \<mu> \<cdot> \<rho>) E"
        unfolding disjoint_vars_iff_inter_empty
        by (smt (verit) E_in UN_I Un_iff disjoint_iff fin finite.intros finite_UN finite_UnI
            finite_clss_of_trail finite_vars_cls vars_cls_subst_renaming_disj resolveI.hyps(2))
    next
      show "disjoint_vars (C \<cdot> \<mu> \<cdot> \<rho>) E"
        unfolding disjoint_vars_iff_inter_empty
        by (smt (verit) E_in UN_I Un_iff disjoint_iff fin finite.intros finite_UN finite_UnI
            finite_clss_of_trail finite_vars_cls vars_cls_subst_renaming_disj resolveI.hyps(2))
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
      using is_imgu_\<mu>[unfolded is_imgu_def, THEN conjunct2] is_unifs_\<sigma>_\<delta>
      by (metis subst_cls_comp_subst)
    thus "is_ground_cls (D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  next
    from gr_C_L_\<delta> have "is_ground_cls ((C + {#L#}) \<cdot> \<sigma> \<cdot> \<delta>)"
      using subst_cls_idem_if_disj_vars[of \<sigma> C]
      using dom_\<sigma> vars_D_L'_vars_C_L_disj
      by (smt (verit, best) Int_assoc inf.orderE inf_bot_right subst_cls_idem_if_disj_vars)
    hence "is_ground_cls ((C + {#L#}) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      using is_imgu_\<mu>[unfolded is_imgu_def, THEN conjunct2] is_unifs_\<sigma>_\<delta>
      by (metis subst_cls_comp_subst)
    thus "is_ground_cls (C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  qed

  moreover have "trail_false_cls \<Gamma>
    ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
    unfolding subst_cls_restrict_subst_idem[OF subset_refl]
    unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
  proof -
    have "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
      using sound_\<Gamma>
      unfolding sound_trail.simps[of _ _ \<Gamma>]
      unfolding \<Gamma>_def trail_propagate_def
      by simp
    moreover have "suffix \<Gamma>' \<Gamma>"
      by (simp add: \<Gamma>_def suffix_ConsI trail_propagate_def)
    ultimately show "trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      using tr_false_cls gr_D_L'_\<sigma> vars_D_L'_vars_C_L_disj dom_\<sigma> is_imgu_\<mu> is_unifs_\<sigma>_\<delta>
      by (auto intro: trail_false_cls_plus_subst_mgu_before_groundings[simplified])
  qed

  moreover have "N \<TTurnstile>\<G>e {(D + C) \<cdot> \<mu> \<cdot> \<rho>}"
  proof -
    from N_entails_C_L have *: "N \<TTurnstile>\<G>e {(C + {#L#}) \<cdot> \<mu>}"
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
        moreover have "atm_of L \<cdot>a \<mu> = atm_of L' \<cdot>a \<mu>"
          using is_imgu_\<mu>[unfolded is_imgu_def, THEN conjunct1]
          by (meson finite.emptyI finite.insertI insertCI is_unifier_alt is_unifiers_def)
        ultimately have False
          using L_eq_comp_L'
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

lemma backtrack_sound_state: "backtrack N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: backtrack.induct)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
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

  from backtrackI.hyps have \<Gamma>_def: "\<Gamma> = trail_decide (\<Gamma>' @ \<Gamma>'') (- (L \<cdot>l \<sigma>))" by simp

  have "disjoint_vars_set (insert (add_mset L D) (N \<union> U \<union> clss_of_trail \<Gamma>''))"
    unfolding disjoint_vars_set_def
  proof (intro ballI impI)
    fix C E
    assume
      C_in: "C \<in> insert (add_mset L D) (N \<union> U \<union> clss_of_trail \<Gamma>'')" and
      E_in: "E \<in> insert (add_mset L D) (N \<union> U \<union> clss_of_trail \<Gamma>'')" and
      C_neq_E: "C \<noteq> E"

    from C_in have C_in': "C = add_mset L D \<or> C \<in> N \<union> U \<union> clss_of_trail \<Gamma>"
      unfolding \<Gamma>_def clss_of_trail_trail_decide clss_of_trail_append by fastforce

    from E_in have E_in': "E = add_mset L D \<or> E \<in> N \<union> U \<union> clss_of_trail \<Gamma>"
      unfolding \<Gamma>_def clss_of_trail_trail_decide clss_of_trail_append by fastforce

    from C_in' E_in' C_neq_E show "disjoint_vars C E"
      using disj_N_U[unfolded disjoint_vars_set_def, rule_format]
      using disj_N_U_\<Gamma>_D_L_L' disjoint_vars_sym
      by (metis add_mset_add_single)
  qed

  moreover have "sound_trail N (insert (add_mset L D) U) \<Gamma>''"
  proof -
    from sound_\<Gamma> have "sound_trail N (insert (add_mset L D) U) \<Gamma>"
      by (rule sound_trail_supersetI) auto
    then show ?thesis
      by (auto simp: \<Gamma>_def trail_decide_def intro: sound_trail_appendD)
  qed

  moreover have "N \<TTurnstile>\<G>e (U \<union> {D + {#L#}})"
    using N_entails_U N_entails_D_L_L' by (metis UN_Un grounding_of_clss_def true_clss_union)

  ultimately show ?case
    unfolding sound_state_def
    using fin by simp
qed

theorem scl_sound_state:
  fixes N :: "('f, 'v) Term.term clause set"
  shows "scl N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  unfolding scl_def
  using propagate_sound_state decide_sound_state conflict_sound_state skip_sound_state
    factorize_sound_state resolve_sound_state backtrack_sound_state
  by metis

lemma assumes "sound_state N S" and "conflict N \<beta> S S'"
  shows "(\<exists>\<gamma>. state_conflict S' = Some ({#}, \<gamma>)) \<or> (\<exists>S''. backtrack N \<beta> S' S'')"
proof -
  from \<open>conflict N \<beta> S S'\<close> obtain D U D' \<Gamma> \<sigma> where
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
    have "(\<exists>S''. backtrack N \<beta> S' S'')"
      unfolding S'_def \<open>D' = D'' + {#L#}\<close>
    proof (rule exI)
      show "backtrack N \<beta> (\<Gamma>, U, Some (D'' + {#L#}, \<sigma>))
        (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D'' \<cdot> \<sigma>)), U \<union> {D'' + {#L#}}, None)"
  oops


section \<open>Reasonable And Regular Runs\<close>

definition reasonable_scl where
  "reasonable_scl N \<beta> S S' \<longleftrightarrow> scl N \<beta> S S' \<and> (decide N \<beta> S S' \<longrightarrow> \<not>(\<exists>S''. conflict N \<beta> S' S''))"

lemma scl_if_reasonable: "reasonable_scl N \<beta> S S' \<Longrightarrow> scl N \<beta> S S'"
  unfolding reasonable_scl_def scl_def by simp

definition regular_scl where
  "regular_scl N \<beta> S S' \<longleftrightarrow>
    conflict N \<beta> S S' \<or> \<not> (\<exists>S''. conflict N \<beta> S S'') \<and> reasonable_scl N \<beta> S S'"

lemma reasonable_if_regular:
  "regular_scl N \<beta> S S' \<Longrightarrow> reasonable_scl N \<beta> S S'"
  unfolding regular_scl_def
proof (elim disjE conjE)
  assume "conflict N \<beta> S S'"
  hence "scl N \<beta> S S'"
    by (simp add: scl_def)
  moreover have "decide N \<beta> S S' \<longrightarrow> \<not>(\<exists>S''. conflict N \<beta> S' S'')"
    by (smt (verit, best) \<open>conflict N \<beta> S S'\<close> conflict.cases option.distinct(1) snd_conv)
  ultimately show "reasonable_scl N \<beta> S S'"
    by (simp add: reasonable_scl_def)
next
  assume "\<not> (\<exists>S''. conflict N \<beta> S S'')" and "reasonable_scl N \<beta> S S'"
  thus ?thesis by simp
qed

lemma reasonable_scl_sound_state: "reasonable_scl N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  using scl_sound_state reasonable_scl_def by blast

lemma regular_scl_sound_state: "regular_scl N \<beta> S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  by (rule reasonable_scl_sound_state[OF reasonable_if_regular])

lemma reasonable_run_sound_state:
  "(reasonable_scl N \<beta>)\<^sup>*\<^sup>* S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  by (smt (verit, best) reasonable_scl_sound_state rtranclp_induct)

lemma regular_run_sound_state:
  "(regular_scl N \<beta>)\<^sup>*\<^sup>* S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
  by (smt (verit, best) regular_scl_sound_state rtranclp_induct)

(* definition regular_state where
  "regular_state N S \<longleftrightarrow> sound_state N S \<and>
    (case state_trail S of
    [] \<Rightarrow> True |
    _ # \<Gamma> \<Rightarrow> \<not> (\<exists>C \<in> grounding_of_clss (N \<union> state_learned S). trail_false_cls \<Gamma> C))"
(* 
lemma regular_stateI:
  assumes "sound_state N S" and
    "state_trail S = [] \<or>
    (\<exists>Ln \<Gamma>. state_trail S = Ln # \<Gamma> \<and> (\<exists>C \<in> grounding_of_clss (N \<union> state_learned S). trail_false_cls \<Gamma> C))"
  shows "regular_state N S"
  unfolding regular_state_def
proof (rule conjI)
  show "sound_state N S"
    by (rule assms(1))
next
  show "case state_trail S of [] \<Rightarrow> True
    | x # \<Gamma> \<Rightarrow> \<not> (\<exists>C \<in> grounding_of_clss (N \<union> state_learned S). trail_false_cls \<Gamma> C)"
 *)

subsection \<open>Initial State is Reasonable\<close>

lemma regular_initial_state[simp]:
  "finite N \<Longrightarrow> disjoint_vars_set N \<Longrightarrow> regular_state N initial_state"
  by (simp add: regular_state_def)


subsection \<open>SCL Rules Preserve Reasonable State\<close>

lemma propagate_regular_state:
  assumes "regular_scl N \<beta> S S'" and prop_S: "propagate N \<beta> S S'" and
    regular_S: "regular_state N S"
  shows "regular_state N S'"
proof -
  from regular_S have sound_S: "sound_state N S" by (simp add: regular_state_def)

  show ?thesis
    unfolding regular_state_def
  proof (rule conjI)
    show "sound_state N S'"
      by (rule propagate_sound_state[OF prop_S sound_S])
  next
    show "case state_trail S' of [] \<Rightarrow> True
    | x # \<Gamma> \<Rightarrow> \<not> (\<exists>C \<in> grounding_of_clss (N \<union> state_learned S'). trail_false_cls \<Gamma> C)"
      using prop_S
    proof (induction S S' rule: propagate.induct)
      case (propagateI C U C' L \<Gamma> \<gamma> C\<^sub>0 C\<^sub>1 \<mu> \<gamma>')
      then show ?case
        apply (simp add: trail_propagate_def)
        sorry
    qed *)


lemma scl_mempty_not_in_sate_learned:
  "scl N \<beta> S S' \<Longrightarrow> {#} \<notin> state_learned S \<Longrightarrow> {#} \<notin> state_learned S'"
  unfolding scl_def
  by (elim disjE propagate.cases decide.cases conflict.cases skip.cases factorize.cases
      resolve.cases backtrack.cases) simp_all






end

end