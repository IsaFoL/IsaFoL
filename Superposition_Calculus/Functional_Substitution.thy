theory Functional_Substitution
  imports
    Abstract_Substitution.Substitution
    FSet_Extra
begin

locale all_subst_ident_iff_ground =
  fixes is_ground :: "'expr \<Rightarrow> bool" and subst :: "'expr \<Rightarrow> 'subst \<Rightarrow> 'expr"
  assumes
    all_subst_ident_iff_ground: "\<And>expr. is_ground expr \<longleftrightarrow> (\<forall>\<sigma>. subst expr \<sigma> = expr)" and
    exists_non_ident_subst:
      "\<And>expr S. finite S \<Longrightarrow> \<not>is_ground expr \<Longrightarrow> \<exists>\<sigma>. subst expr \<sigma> \<noteq> expr \<and> subst expr \<sigma> \<notin> S"

locale finite_variables = finite_set vars 
  for vars :: "'expr \<Rightarrow> 'var set"
begin

lemmas finite_vars = finite_set finite_set'
lemmas fset_finite_vars = fset_finite_set

abbreviation "finite_vars \<equiv> finite_set"

end

locale renaming_variables = 
  fixes vars :: "'expr \<Rightarrow> 'var set" and id_subst :: "'var \<Rightarrow> 'base" and subst is_renaming
  assumes
    renaming_variables:
      "\<And>expr \<rho>. is_renaming \<rho> \<Longrightarrow> id_subst ` vars (subst expr \<rho>) = \<rho> ` (vars expr)"

locale functional_substitution = substitution _ _ subst "\<lambda>a. vars a = {}" 
  for
    subst :: "'expr \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'expr" (infixl "\<cdot>" 70) and
    vars :: "'expr \<Rightarrow> 'var set" +
  assumes 
    subst_eq: "\<And>expr \<sigma> \<tau>. (\<And>x. x \<in> (vars expr) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> expr \<cdot> \<sigma> = expr \<cdot> \<tau>"
begin

abbreviation is_ground where "is_ground expr \<equiv> vars expr = {}"

definition vars_set :: "'expr set \<Rightarrow> 'var set" where
  "vars_set exprs \<equiv> \<Union>expr \<in> exprs. vars expr"

lemma subst_reduntant_upd [simp]:
  assumes "var \<notin> vars expr"
  shows "expr \<cdot> \<sigma>(var := update) = expr \<cdot> \<sigma>"
  using assms subst_eq
  by fastforce

lemma subst_reduntant_if [simp]: 
  assumes "vars expr \<subseteq> vars'"
  shows "expr \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma> var else \<sigma>' var) = expr \<cdot> \<sigma>"
  using assms 
  by (smt (verit, best) subset_eq subst_eq)

lemma subst_reduntant_if' [simp]: 
  assumes "vars expr \<inter> vars' = {}"  
  shows "expr \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma>' var else \<sigma> var) = expr \<cdot> \<sigma>"
  using assms subst_eq 
  unfolding disjoint_iff
  by presburger

lemma subst_cannot_unground:
  assumes "\<not>is_ground (expr \<cdot> \<sigma>)"  
  shows "\<not>is_ground expr"
  using assms by force

end

locale grounding = functional_substitution where vars = vars and id_subst = id_subst
  for vars :: "'expr \<Rightarrow> 'var set" and id_subst :: "'var \<Rightarrow> 'base" +
  fixes to_ground :: "'expr \<Rightarrow> 'expr\<^sub>G" and from_ground :: "'expr\<^sub>G \<Rightarrow> 'expr"
  assumes 
    range_from_ground_iff_is_ground: "{expr. is_ground expr} = range from_ground" and
    from_ground_inverse [simp]: "\<And>expr\<^sub>G. to_ground (from_ground expr\<^sub>G) = expr\<^sub>G"
begin

definition groundings ::"'expr \<Rightarrow> 'expr\<^sub>G set" where
  "groundings expr = { to_ground (expr \<cdot> \<gamma>) | \<gamma>. is_ground (expr \<cdot> \<gamma>) }"

lemma to_ground_from_ground_id: "to_ground \<circ> from_ground = id"
  using from_ground_inverse
  by auto

lemma surj_to_ground: "surj to_ground"
  using from_ground_inverse
  by (metis surj_def)

lemma inj_from_ground: "inj_on from_ground domain\<^sub>G"
  by (metis from_ground_inverse inj_on_inverseI)
 
lemma inj_on_to_ground: "inj_on to_ground (from_ground ` domain\<^sub>G)"
  unfolding inj_on_def
  by simp

lemma bij_betw_to_ground: "bij_betw to_ground (from_ground ` domain\<^sub>G) domain\<^sub>G"
  by (smt (verit, best) bij_betwI' from_ground_inverse image_iff)

lemma bij_betw_from_ground: "bij_betw from_ground domain\<^sub>G (from_ground ` domain\<^sub>G)"
  by (simp add: bij_betw_def inj_from_ground)

lemma ground_is_ground [simp, intro]: "is_ground (from_ground expr\<^sub>G)"
  using range_from_ground_iff_is_ground
  by blast

lemma is_ground_iff_range_from_ground: "is_ground expr \<longleftrightarrow> expr \<in> range from_ground"
  using range_from_ground_iff_is_ground
  by auto

lemma to_ground_inverse [simp]: 
  assumes "is_ground expr"
  shows "from_ground (to_ground expr) = expr"
  using inj_on_to_ground from_ground_inverse is_ground_iff_range_from_ground assms
  unfolding inj_on_def
  by blast

corollary obtain_grounding: 
  assumes "is_ground expr"
  obtains expr\<^sub>G where "from_ground expr\<^sub>G = expr"
  using to_ground_inverse assms 
  by blast

end

locale base_functional_substitution = functional_substitution 
  where id_subst = id_subst and vars = vars
  for id_subst :: "'var \<Rightarrow> 'expr" and vars :: "'expr \<Rightarrow> 'var set" +
  assumes
    is_grounding_iff_vars_grounded:
      "\<And>expr. is_ground (expr \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>var \<in> vars expr. is_ground (\<gamma> var))" and
    ground_exists: "\<exists>expr. is_ground expr"
begin 

lemma obtain_ground_subst:
  obtains \<gamma>
  where "is_ground_subst \<gamma>"
proof-
  obtain expr\<^sub>G where "is_ground expr\<^sub>G"
    using ground_exists by blast

  then have "is_ground_subst  (\<lambda>_. expr\<^sub>G)"
    by (simp add: is_grounding_iff_vars_grounded is_ground_subst_def)

  then show ?thesis
    using that
    by simp
qed

lemma ground_subst_extension:
  assumes "is_ground (expr \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'" and "is_ground_subst \<gamma>'"
proof-
  obtain \<gamma>'' where 
    \<gamma>'': "is_ground_subst \<gamma>''"
    using obtain_ground_subst
    by blast
                    
  define \<gamma>' where 
    \<gamma>':  "\<gamma>' = (\<lambda>var. if var \<in> vars expr then \<gamma> var else \<gamma>'' var)"

  have "is_ground_subst \<gamma>'"
    using assms \<gamma>'' is_grounding_iff_vars_grounded
    unfolding \<gamma>' is_ground_subst_def
    by simp

  moreover have "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'"
    unfolding \<gamma>'
    using subst_eq by presburger

  ultimately show ?thesis
    using that
    by blast
qed

lemma ground_subst_upd [simp]:
  assumes "is_ground update" "is_ground (expr \<cdot> \<gamma>)" 
  shows "is_ground (expr \<cdot> \<gamma>(var := update))"
  using assms is_grounding_iff_vars_grounded by auto

lemma variable_grounding:
  assumes "is_ground (expr \<cdot> \<gamma>)" "var \<in> vars expr" 
  shows "is_ground (\<gamma> var)"
  using assms is_grounding_iff_vars_grounded 
  by blast

end

locale based_functional_substitution = 
  base: base_functional_substitution where subst = base_subst and vars = base_vars + 
  functional_substitution where vars = vars 
for 
  base_subst :: "'base \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'base" and 
  base_vars and 
  vars :: "'expr \<Rightarrow> 'var set" +
assumes
  ground_subst_iff_base_ground_subst [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>" and
  is_grounding_iff_vars_grounded: 
    "\<And>expr. is_ground (expr \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>var \<in> vars expr. base.is_ground (\<gamma> var))"
begin

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
  using base.obtain_ground_subst by auto

lemma ground_subst_extension:
  assumes "is_ground (expr \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'" and "is_ground_subst \<gamma>'"
  using obtain_ground_subst assms
  by (metis all_subst_ident_if_ground is_ground_subst_comp_right subst_comp_subst)

lemma ground_subst_extension':
  assumes "is_ground (expr \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'" and "base.is_ground_subst \<gamma>'"
  using ground_subst_extension assms
  by auto

lemma ground_subst_upd [simp]:
  assumes "base.is_ground update" "is_ground (expr \<cdot> \<gamma>)" 
  shows "is_ground (expr \<cdot> \<gamma>(var := update))"
  using base.ground_subst_upd assms is_grounding_iff_vars_grounded by simp  

lemma ground_exists: "\<exists>expr. is_ground expr"
  using base.ground_exists
  by (meson is_grounding_iff_vars_grounded)

lemma variable_grounding:
  assumes "is_ground (expr \<cdot> \<gamma>)" "var \<in> vars expr" 
  shows "base.is_ground (\<gamma> var)"
  using assms is_grounding_iff_vars_grounded 
  by blast

end

locale variables_in_base_imgu =
  fixes 
    base_is_imgu and
    vars :: "'expr \<Rightarrow> 'var set" and
    subst:: "'expr \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'expr" and
    base_vars :: "'base \<Rightarrow> 'var set"
  assumes
    variables_in_base_imgu: "\<And>expr \<mu> unifications. 
      base_is_imgu \<mu> unifications \<Longrightarrow> 
      finite unifications \<Longrightarrow> \<forall>unification \<in> unifications. finite unification \<Longrightarrow>  
      vars (subst expr \<mu>) \<subseteq> vars expr \<union> (\<Union>(base_vars ` \<Union> unifications))"

locale base_variables_in_base_imgu = base_functional_substitution +
  assumes
    variables_in_base_imgu: "\<And>expr \<mu> unifications. 
      is_imgu \<mu> unifications \<Longrightarrow> 
      finite unifications \<Longrightarrow> \<forall>unification \<in> unifications. finite unification \<Longrightarrow>  
      vars (subst expr \<mu>) \<subseteq> vars expr \<union> (\<Union>(vars ` \<Union> unifications))"
begin


end


(*locale based_variables_in_base_imgu = 
  based_functional_substitution + 
  base: base_variables_in_base_imgu where subst = base_subst and vars = base_vars
begin

sublocale variables_in_base_imgu where base_is_imgu = base.is_imgu
proof unfold_locales
  fix expr \<mu> unifications
  assume imgu_vars:
    "base.is_imgu \<mu> unifications" 
    "finite unifications" 
    "\<forall>unification\<in>unifications. finite unification"

  show "vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> \<Union> (base_vars ` \<Union> unifications)"
    using base.variables_in_base_imgu[OF imgu_vars]
    
    sorry
qed

end*)
  (*assumes
    variables_in_base_imgu: "\<And>expr \<mu> unifications. 
      base.is_imgu \<mu> unifications \<Longrightarrow> 
      finite unifications \<Longrightarrow> \<forall>unification \<in> unifications. finite unification \<Longrightarrow>  
      vars (subst expr \<mu>) \<subseteq> vars expr \<union> (\<Union>(base_vars ` \<Union> unifications))"*)

end
