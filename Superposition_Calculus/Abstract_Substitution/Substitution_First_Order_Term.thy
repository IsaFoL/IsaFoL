theory Substitution_First_Order_Term
  imports
    Substitution
    "First_Order_Terms.Unification"
begin

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

lemma is_ground_iff: "is_ground_trm (t \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars_term t. is_ground_trm (\<gamma> x))"
  by (induction t) simp_all

lemma is_ground_trm_iff_ident_forall_subst: "is_ground_trm t \<longleftrightarrow> (\<forall>\<sigma>. t \<cdot> \<sigma> = t)"
proof(induction t)
  case Var
  then show ?case 
    by auto
next
  case Fun

  moreover have "\<And>xs x \<sigma>. \<forall>\<sigma>. map (\<lambda>s. s \<cdot> \<sigma>) xs = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<cdot> \<sigma> = x"
    by (metis list.map_ident map_eq_conv)

  ultimately show ?case
    by (auto simp: map_idI)
qed

global_interpretation term_subst: substitution where
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and
  is_ground = is_ground_trm
proof unfold_locales
  show "\<And>x. x \<cdot> Var = x"
    by simp
next
  show "\<And>x \<sigma> \<tau>. x \<cdot> \<sigma> \<circ>\<^sub>s \<tau> = x \<cdot> \<sigma> \<cdot> \<tau>"
    by simp
next
  show "\<And>x. is_ground_trm x \<Longrightarrow> \<forall>\<sigma>. x \<cdot> \<sigma> = x"
    using is_ground_trm_iff_ident_forall_subst ..
qed
                      
lemma term_subst_is_unifier_iff_unifiers:
  assumes "finite X"
  shows "term_subst.is_unifier \<mu> X \<longleftrightarrow> \<mu> \<in> unifiers (X \<times> X)"
  unfolding term_subst.is_unifier_iff_if_finite[OF assms] unifiers_def
  by simp

lemma term_subst_is_unifier_set_iff_unifiers:
  assumes "\<forall>X\<in> XX. finite X"
  shows "term_subst.is_unifier_set \<mu> XX \<longleftrightarrow> \<mu> \<in> unifiers (\<Union>X\<in>XX. X \<times> X)"
  using term_subst_is_unifier_iff_unifiers assms 
  unfolding term_subst.is_unifier_set_def unifiers_def 
  by fast

lemma term_subst_is_imgu_iff_is_imgu:
  assumes "\<forall>X\<in> XX. finite X"
  shows "term_subst.is_imgu \<mu> XX \<longleftrightarrow> is_imgu \<mu> (\<Union>X\<in>XX. X \<times> X)"
  using term_subst_is_unifier_set_iff_unifiers[OF assms]
  unfolding term_subst.is_imgu_def is_imgu_def
  by auto

lemma range_vars_subset_if_is_imgu:
  assumes "term_subst.is_imgu \<mu> XX" "\<forall>X\<in>XX. finite X" "finite XX"
  shows "range_vars \<mu> \<subseteq> (\<Union>t\<in>\<Union>XX. vars_term t)"
proof-
  have is_imgu: "is_imgu \<mu> (\<Union>X\<in>XX. X \<times> X)"
    using term_subst_is_imgu_iff_is_imgu[of "XX"] assms
    by simp

  have finite_prod: "finite (\<Union>X\<in>XX. X \<times> X)"
    using assms
    by blast

  have "(\<Union>e\<in>\<Union>X\<in>XX. X \<times> X. vars_term (fst e) \<union> vars_term (snd e)) = (\<Union>t\<in>\<Union>XX. vars_term t)"
    by fastforce

  then show ?thesis
    using imgu_range_vars_subset[OF is_imgu finite_prod]
    by argo
qed

lemma term_subst_is_renaming_iff:
  "term_subst.is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x))"
proof (rule iffI)
  show "term_subst.is_renaming \<rho> \<Longrightarrow> inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x))"
    unfolding term_subst.is_renaming_def subst_compose_def inj_def
    by (metis term.sel(1) is_VarI subst_apply_eq_Var) 
next
  show "inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x)) \<Longrightarrow> term_subst.is_renaming \<rho>"
    unfolding term_subst.is_renaming_def
    using ex_inverse_of_renaming by metis
qed

lemma term_subst_is_renaming_iff_ex_inj_fun_on_vars:
  "term_subst.is_renaming \<rho> \<longleftrightarrow> (\<exists>f. inj f \<and> \<rho> = Var \<circ> f)"
proof (rule iffI)
  assume "term_subst.is_renaming \<rho>"
  hence "inj \<rho>" and all_Var: "\<forall>x. is_Var (\<rho> x)"
    unfolding term_subst_is_renaming_iff by simp_all
  from all_Var obtain f where "\<forall>x. \<rho> x = Var (f x)"
    by (metis comp_apply term.collapse(1))
  hence "\<rho> = Var \<circ> f"
    using \<open>\<forall>x. \<rho> x = Var (f x)\<close>
    by (intro ext) simp
  moreover have "inj f"
      using \<open>inj \<rho>\<close> unfolding \<open>\<rho> = Var \<circ> f\<close>
      using inj_on_imageI2 by metis
  ultimately show "\<exists>f. inj f \<and> \<rho> = Var \<circ> f"
    by metis
next
  show "\<exists>f. inj f \<and> \<rho> = Var \<circ> f \<Longrightarrow> term_subst.is_renaming \<rho>"
    unfolding term_subst_is_renaming_iff comp_apply inj_def
    by auto
qed

lemma ground_imgu_equals: 
  assumes "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2" and "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms
  using term_subst.ground_eq_ground_if_unifiable
  by (metis insertCI term_subst.is_imgu_def term_subst.is_unifier_set_def)

lemma the_mgu_is_unifier: 
  assumes "term \<cdot> the_mgu term term' = term' \<cdot> the_mgu term term'" 
  shows "term_subst.is_unifier (the_mgu term term') {term, term'}"
  using assms
  unfolding term_subst.is_unifier_def the_mgu_def
  by simp

lemma imgu_exists_extendable:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes "term \<cdot> \<upsilon> = term' \<cdot> \<upsilon>" "P term term' (the_mgu term term')"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<circ>\<^sub>s \<upsilon>" "term_subst.is_imgu \<mu> {{term, term'}}" "P term term' \<mu>"
proof
  have finite: "finite {term, term'}"
    by simp

  have "term_subst.is_unifier_set (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_unifier_set_def
    using the_mgu_is_unifier[OF the_mgu[OF assms(1), THEN conjunct1]]
    by simp

  moreover have
    "\<And>\<sigma>. term_subst.is_unifier_set \<sigma> {{term, term'}} \<Longrightarrow> \<sigma> = the_mgu term term' \<circ>\<^sub>s \<sigma>"
    unfolding term_subst.is_unifier_set_def
    using term_subst.is_unifier_iff_if_finite[OF finite] the_mgu
    by blast

  ultimately have is_imgu: "term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_imgu_def
    by metis

  show "\<upsilon> = (the_mgu term term') \<circ>\<^sub>s \<upsilon>" 
    using the_mgu[OF assms(1)]
    by blast

  show "term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    using is_imgu
    by blast

  show "P term term' (the_mgu term term')"
    using assms(2).
qed

lemma imgu_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes "term \<cdot> \<upsilon> = term' \<cdot> \<upsilon>"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<circ>\<^sub>s \<upsilon>" "term_subst.is_imgu \<mu> {{term, term'}}"
  using imgu_exists_extendable[OF assms, of "(\<lambda>_ _ _. True)"]
  by auto

(* The other way around it does not work! *)
lemma is_renaming_if_term_subst_is_renaming:
  assumes "term_subst.is_renaming \<rho>"
  shows "is_renaming \<rho>"
  using assms
  by (simp add: inj_on_def is_renaming_def term_subst_is_renaming_iff)

end
