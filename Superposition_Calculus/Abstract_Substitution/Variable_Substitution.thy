theory Variable_Substitution
  imports Abstract_Substitution
begin

(* TODO: Better name?: functional substitution *)
locale variable_substitution = basic_substitution _ _ subst "\<lambda>a.  vars a = {}"
  for subst :: "'value \<Rightarrow> ('x \<Rightarrow> 'subvalue) \<Rightarrow> 'value" (infixl "\<cdot>" 70) and
    (* TODO: set \<rightarrow> fset *)
      vars :: "'value \<Rightarrow> 'x set" +
  assumes
    subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>" and
    finite_vars [simp]: "\<And>a. finite (vars a)"
begin

abbreviation is_ground where "is_ground a \<equiv> vars a = {}"

lemma subst_reduntant_upd [simp]:
  assumes "var \<notin> vars a"
  shows "a \<cdot> \<sigma>(var := update) = a \<cdot> \<sigma>"
  using assms subst_eq by fastforce

lemma subst_reduntant_if [simp]: 
  assumes "vars a \<subseteq> vars'"
  shows "a \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma> var else \<sigma>' var) = a \<cdot> \<sigma>"
  using assms
  by (smt (verit, ccfv_SIG) subsetD subst_eq)

lemma subst_reduntant_if' [simp]: 
  assumes "vars a \<inter> vars' = {}"  
  shows "a \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma>' var else \<sigma> var) = a \<cdot> \<sigma>"
  using assms
  by (smt (verit, ccfv_SIG) disjoint_iff_not_equal subst_eq)

end

(* TODO: Type annotations *)
locale variable_substitution_lifting = base: variable_substitution + 
  variable_substitution where
     subst = lifted_subst and 
     id_subst = id_subst and 
     comp_subst = comp_subst and 
     vars = lifted_vars 
  for lifted_subst lifted_vars  +
  assumes lifted_vars_vars:  "(\<forall>x. lifted_vars (lifted_subst x \<gamma>) = {}) \<longleftrightarrow> (\<forall>x. vars (x \<cdot> \<gamma>) = {})"
begin

lemma is_ground_subst_iff [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  base.is_ground_subst_def
  using lifted_vars_vars
  by presburger

end

end
