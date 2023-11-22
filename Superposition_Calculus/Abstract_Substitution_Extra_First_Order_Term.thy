theory Abstract_Substitution_Extra_First_Order_Term
  imports
    Abstract_Substitution_Extra
    "First_Order_Terms.Subsumption"
    "First_Order_Terms.Unification"
begin

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

global_interpretation term_subst: basic_substitution_ops subst_apply_term Var subst_compose
  rewrites "term_subst.is_ground = is_ground_trm"
proof -
  have is_ground_iff:
    "basic_substitution_ops.is_ground (\<cdot>) (t \<cdot> \<gamma>) \<longleftrightarrow>
      (\<forall>x \<in> vars_term t. basic_substitution_ops.is_ground (\<cdot>) (\<gamma> x))"
    for t \<gamma>
    by (induction t) (auto simp add: basic_substitution_ops.is_ground_def)

  thus "basic_substitution_ops.is_ground (\<cdot>) = is_ground_trm"
    by (metis (mono_tags, opaque_lifting) basic_substitution_ops.subst_ident_if_ground ex_in_conv
        subst_apply_term_empty subst_def subst_simps(1) subst_term_eqI term.distinct(1))
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
next
  show "\<And>\<sigma> \<tau>. (\<And>x. x \<cdot> \<sigma> = x \<cdot> \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (simp add: subst_term_eqI)(* 
next
  fix T :: "('f, 'v) term set" and \<sigma> :: "'v \<Rightarrow> ('f, 'v) term"

  define \<gamma> where
    "\<gamma> = (\<lambda>x. if (\<exists>t\<in>T. x \<in> vars_term t) then \<sigma> x else Fun undefined [])"

  assume ground_T: "term_subst.is_ground_set (term_subst.subst_set T \<sigma>)"

  have ground_apply_\<gamma>: "term_subst.is_ground (\<gamma> x)" for x
  proof (cases "\<exists>t\<in>T. x \<in> vars_term t")
    case True
    then obtain t where "t \<in> T" and "x \<in> vars_term t"
      by auto
    moreover have "term_subst.is_ground (t \<cdot> \<sigma>)"
      using ground_T \<open>t \<in> T\<close>
      by (simp add: term_subst.is_ground_set_def term_subst.subst_set_def)
    ultimately show ?thesis
      by (auto simp add: \<gamma>_def is_ground_iff)
  next
    case False
    then show ?thesis
      by (simp add: \<gamma>_def term_subst.is_ground_def)
  qed

  show "\<exists>\<tau>. term_subst.is_ground_subst \<tau> \<and> (\<forall>t \<in> T. t \<cdot> \<tau> = t \<cdot> \<sigma>)"
  proof (intro exI conjI)
    show "term_subst.is_ground_subst \<gamma>"
      unfolding term_subst.is_ground_subst_def
    proof (rule allI)
      fix t show "term_subst.is_ground (t \<cdot> \<gamma>)"
        using ground_apply_\<gamma>
        by (induction t) (simp_all add: term_subst.is_ground_def)
    qed
  next
    show "\<forall>t\<in>T. t \<cdot> \<gamma> = t \<cdot> \<sigma>"
      using \<gamma>_def term_subst_eq_conv by fastforce
  qed *)
qed

lemma ground_imgu_equals: 
  assumes "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2" and "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms
  unfolding basic_substitution_ops.is_imgu_def term_subst.is_ground_def term_subst.is_unifiers_def
  by (metis finite.emptyI finite.insertI insertCI term_subst.is_unifier_iff_if_finite)

end