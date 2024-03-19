theory Abstract_Substitution_Extra_First_Order_Term
  imports
    Abstract_Substitution_Extra
    "First_Order_Terms.Subsumption"
    "First_Order_Terms.Unification"
begin

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

lemma is_ground_trm_iff_ident_forall_subst: "is_ground_trm t \<longleftrightarrow> (\<forall>\<sigma>. t = t \<cdot> \<sigma>)"
  by (metis (full_types) Int_empty_left ex_in_conv fun_upd_same subst_apply_term_ident
      term.disc(1) term.disc(2) term_subst_eq_conv)

global_interpretation term_subst: basic_substitution_ops subst_apply_term Var subst_compose
  rewrites "term_subst.is_ground = is_ground_trm"
proof -
  interpret basic_substitution_ops subst_apply_term Var subst_compose .
  show "is_ground = is_ground_trm"
    using is_ground_trm_iff_ident_forall_subst
    by (metis is_ground_def)
qed

lemma is_ground_iff:
  "term_subst.is_ground (t \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars_term t. term_subst.is_ground (\<gamma> x))"
  by (induction t) (auto simp add: term_subst.is_ground_def)

lemma term_subst_is_renaming_iff:
  "term_subst.is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x))"
proof (rule iffI)
  show "term_subst.is_renaming \<rho> \<Longrightarrow> inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x))"
    unfolding term_subst.is_renaming_def
    by (metis injI subst_apply_eq_Var subst_compose_def term.disc(1) term.inject(1))
next
  show "inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x)) \<Longrightarrow> term_subst.is_renaming \<rho>"
    unfolding term_subst.is_renaming_def
    using ex_inverse_of_renaming by metis
qed

global_interpretation term_subst: basic_substitution subst_apply_term Var subst_compose
proof unfold_locales
  show "\<And>x. x \<cdot> Var = x"
    by simp
next
  show "\<And>x \<sigma> \<tau>. x \<cdot> \<sigma> \<circ>\<^sub>s \<tau> = x \<cdot> \<sigma> \<cdot> \<tau>"
    by simp
qed

lemma ground_imgu_equals: 
  assumes "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2" and "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms
  unfolding basic_substitution_ops.is_imgu_def term_subst.is_ground_def term_subst.is_unifiers_def
  by (metis finite.emptyI finite.insertI insertCI term_subst.is_unifier_iff_if_finite)

lemma the_mgu_is_unifier: 
  assumes "term \<cdot> the_mgu term term' = term' \<cdot> the_mgu term term'" 
  shows "term_subst.is_unifier (the_mgu term term') {term, term'}"
  using assms
  unfolding term_subst.is_unifier_def the_mgu_def
  by simp

lemma imgu_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes "term \<cdot> \<upsilon> = term' \<cdot> \<upsilon>"
  shows "\<exists>(\<mu> :: ('f, 'v) subst).  \<upsilon> = \<mu> \<circ>\<^sub>s \<upsilon> \<and> term_subst.is_imgu \<mu> {{term, term'}}"
proof (intro exI)
  have finite_terms: "finite {term, term'}"
    by simp

  have "term_subst.is_unifiers (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_unifiers_def
    using the_mgu_is_unifier[OF the_mgu[OF assms, THEN conjunct1]]
    by simp

  moreover have
    "\<And>\<sigma>. term_subst.is_unifiers \<sigma> {{term, term'}} \<Longrightarrow> \<sigma> = the_mgu term term' \<circ>\<^sub>s \<sigma>"
    unfolding term_subst.is_unifiers_def
    using
      term_subst.is_unifier_iff_if_finite[OF finite_terms]
      the_mgu[of "term" _ term']
    by blast

  ultimately have is_imgu: "term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_imgu_def
    by blast

  show "\<upsilon> = (the_mgu term term') \<circ>\<^sub>s \<upsilon> \<and> term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    using is_imgu the_mgu[OF assms]
    by blast
qed

lemma is_imgu_equals: 
  assumes "term_subst.is_imgu \<mu> {{term\<^sub>1, term\<^sub>2}}" 
  shows "term\<^sub>1 \<cdot> \<mu> = term\<^sub>2 \<cdot> \<mu>"
  using assms term_subst.is_unifier_iff_if_finite[of "{term\<^sub>1, term\<^sub>2}"]
  unfolding term_subst.is_imgu_def term_subst.is_unifiers_def
  by blast

end
