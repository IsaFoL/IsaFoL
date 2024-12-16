theory Typed_Functional_Substitution
  imports 
    Typing 
    Functional_Substitution
    Fun_Extra
begin

type_synonym ('var, 'ty) var_types = "'var \<Rightarrow> 'ty"

locale explicitly_typed_functional_substitution = 
  base_functional_substitution where vars = vars and id_subst = id_subst
for
  id_subst :: "'var \<Rightarrow> 'base" and
  vars :: "'base \<Rightarrow> 'var set" and
  typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes 
  predicate_typed: "\<And>\<V>. predicate_typed (typed \<V>)" and
  typed_id_subst: "\<V> x = \<tau> \<Longrightarrow> typed \<V> (id_subst x) \<tau>" and
   (* TODO: Does it make sense to have this in a separate locale? *)
  types_inhabited: "\<And>\<tau>. \<exists>base. is_ground base \<and> typed \<V> base \<tau>"
begin

sublocale predicate_typed "typed \<V>"
  by (rule predicate_typed)

abbreviation is_typed_on :: "'var set \<Rightarrow> ('var, 'ty) var_types \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> bool" where 
  "is_typed_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. typed \<V> (\<sigma> x) (\<V> x)"

lemma subst_update:
  assumes "typed \<V> (id_subst var) \<tau>" "typed \<V> update \<tau>"  "is_typed_on X \<V> \<gamma>" 
  shows "is_typed_on X \<V> (\<gamma>(var := update))"
  using assms typed_id_subst
  by fastforce

end

locale typed_functional_substitution = 
  base: explicitly_typed_functional_substitution where 
  vars = base_vars and subst = base_subst and typed = base_typed +
  based_functional_substitution where vars = vars
for
  vars :: "'expr \<Rightarrow> 'var set" and
  is_typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" and
  base_typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"
begin

lemma ground_subst_extension:
  assumes
    grounding: "is_ground (expr \<cdot> \<gamma>)" and
    \<gamma>_is_typed_on: "base.is_typed_on (vars expr) \<V> \<gamma>"
  obtains \<gamma>'
  where 
    "base.is_ground_subst \<gamma>'" 
    "base.is_typed_on UNIV \<V> \<gamma>'" 
    "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
proof standard

  define \<gamma>' where 
    "\<And>x. \<gamma>' x \<equiv>
      if x \<in> vars expr
      then \<gamma> x
      else SOME base. base.is_ground base \<and> base_typed \<V> base (\<V> x)"

  show "base.is_ground_subst \<gamma>'"
  proof(unfold base.is_ground_subst_def, intro allI)
    fix b

    {
      fix x

      have "base.is_ground (\<gamma>' x)"
      proof(cases "x \<in> vars expr")
        case True
        then show ?thesis 
          unfolding \<gamma>'_def
          using variable_grounding[OF grounding]
          by auto
      next
        case False
        then show ?thesis
          unfolding \<gamma>'_def
          by (smt (verit) base.types_inhabited tfl_some)
      qed
    }

    then show "base.is_ground (base_subst b \<gamma>')"
      using base.is_grounding_iff_vars_grounded 
      by auto
  qed

  show "base.is_typed_on UNIV \<V> \<gamma>'"
    unfolding \<gamma>'_def
    using \<gamma>_is_typed_on base.types_inhabited
    by (simp add: verit_sko_ex_indirect)

  show "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
    by (simp add: \<gamma>'_def)
qed

end

sublocale explicitly_typed_functional_substitution \<subseteq> typed_functional_substitution where 
  base_subst = subst and base_vars = vars and is_typed = is_typed and 
  base_typed = typed                                
  by unfold_locales

locale functional_substitution_typing =
  is_typed: typed_functional_substitution where 
  base_typed = base_typed and is_typed = is_typed +
  is_welltyped: typed_functional_substitution where 
  base_typed = base_welltyped and is_typed = is_welltyped
for 
  base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
  is_typed is_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" +
assumes typing: "\<And>\<V>. typing (is_typed \<V>) (is_welltyped \<V>)"
begin

sublocale base: typing "is_typed \<V>" "is_welltyped \<V>"
  by(rule typing)

abbreviation is_typed_on where
  "is_typed_on \<equiv> is_typed.base.is_typed_on"

abbreviation is_welltyped_on where
  "is_welltyped_on \<equiv> is_welltyped.base.is_typed_on"

end

locale base_functional_substitution_typing =
  typed: explicitly_typed_functional_substitution where typed = typed +
  welltyped: explicitly_typed_functional_substitution where typed = welltyped
for 
  welltyped typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes 
   explicit_typing: "\<And>\<V>. explicit_typing (typed \<V>) (welltyped \<V>)" and
   welltyped_id_subst [intro]: "\<And>\<V> x. welltyped \<V> (id_subst x) (\<V> x)"
begin

sublocale base: explicit_typing "typed \<V>" "welltyped \<V>"
  by(rule explicit_typing)

sublocale functional_substitution_typing where 
  is_typed = base.is_typed and is_welltyped = base.is_welltyped and base_typed = typed and 
  base_welltyped = welltyped and base_vars = vars and base_subst = subst
  by unfold_locales

(* TODO: Would need to go one level higher*)
abbreviation is_welltyped where 
  "is_welltyped \<equiv> is_welltyped_on UNIV"

abbreviation is_typed where
  "is_typed \<equiv> is_typed_on UNIV"

sublocale typing "is_typed_on X \<V>" "is_welltyped_on X \<V>"
  using base.typed_if_welltyped
  by unfold_locales blast

lemma typed_id_subst: "typed \<V> (id_subst x) (\<V> x)"
  using welltyped_id_subst
  by (simp add: base.typed_if_welltyped)

lemma is_typed_id_subst [intro]: "is_typed_on X \<V> id_subst"
  using typed_id_subst
  by auto

lemma is_welltyped_id_subst [intro]: "is_welltyped_on X \<V> id_subst"
  using welltyped_id_subst
  by auto

lemma is_typed_on_subset:
  assumes "is_typed_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "is_typed_on X \<V> \<sigma>"
  using assms
  by blast

lemma is_welltyped_on_subset:
  assumes "is_welltyped_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "is_welltyped_on X \<V> \<sigma>"
  using assms
  by blast

end

locale typed_subst_stability = typed_functional_substitution +
assumes
  subst_stability [simp]: 
    "\<And>\<V> expr \<sigma>. base.is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> is_typed \<V> expr"
begin

lemma subst_stability_UNIV [simp]: 
  "\<And>\<V> expr \<sigma>. base.is_typed_on UNIV \<V> \<sigma> \<Longrightarrow> is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> is_typed \<V> expr"
  by simp

end

locale explicitly_typed_subst_stability = explicitly_typed_functional_substitution +
assumes
  explicit_subst_stability [simp]: 
    "\<And>\<V> expr \<sigma> \<tau>. is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> typed \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> typed \<V> expr \<tau>"
begin

lemma explicit_subst_stability_UNIV [simp]: 
  "\<And>\<V> expr \<sigma>. is_typed_on UNIV \<V> \<sigma> \<Longrightarrow> typed \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> typed \<V> expr \<tau>"
  by simp

sublocale typed_subst_stability where 
  base_vars = vars and base_subst = subst and base_typed = typed and is_typed = is_typed
  using explicit_subst_stability
  by unfold_locales blast

end

locale replaceable_\<V> = typed_functional_substitution +
  assumes replace_\<V>: 
    "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> is_typed \<V> expr \<Longrightarrow> is_typed \<V>' expr"
begin

lemma replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x" 
  shows "is_typed \<V> expr \<longleftrightarrow> is_typed \<V>' expr"
  using assms
  by (metis replace_\<V>)

lemma is_ground_typed:
  assumes "is_ground expr" 
  shows "is_typed \<V> expr \<longleftrightarrow> is_typed \<V>' expr"
  using replace_\<V>_iff assms
  by blast

end

locale explicitly_replaceable_\<V> = explicitly_typed_functional_substitution +
  assumes explicit_replace_\<V>: 
    "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> typed \<V> expr \<tau> \<Longrightarrow>  typed \<V>' expr \<tau>"
begin

lemma explicit_replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x" 
  shows "typed \<V> expr \<tau> \<longleftrightarrow> typed \<V>' expr \<tau>"
  using assms
  by (metis explicit_replace_\<V>)

lemma explicit_is_ground_typed:
  assumes "is_ground expr" 
  shows "typed \<V> expr \<tau> \<longleftrightarrow> typed \<V>' expr \<tau>"
  using explicit_replace_\<V>_iff assms
  by blast

sublocale replaceable_\<V> where 
  base_vars = vars and base_subst = subst and base_typed = typed and is_typed = is_typed
  using explicit_replace_\<V>
  by unfold_locales blast

end

(* TODO: naming (esp. explicit_...) + the_inv \<rightarrow> rename *)
locale typed_renaming = typed_functional_substitution +
assumes
  typed_renaming [simp]: 
    "\<And>\<V> \<V>' expr \<rho>. base.is_renaming \<rho> \<Longrightarrow> 
      \<forall>x \<in> vars (expr \<cdot> \<rho>). \<V> (inv \<rho> (id_subst x)) = \<V>' x \<Longrightarrow> 
      is_typed \<V>' (expr \<cdot> \<rho>) \<longleftrightarrow> is_typed \<V> expr"

locale explicitly_typed_renaming = 
  explicitly_typed_functional_substitution where typed = typed + 
  renaming_variables +
  explicitly_replaceable_\<V> where typed = typed 
for typed :: "('var \<Rightarrow> 'ty) \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes
  explicit_typed_renaming [simp]: 
  "\<And>\<V> \<V>' expr \<rho> \<tau>. is_renaming \<rho> \<Longrightarrow> 
      \<forall>x \<in> vars (expr \<cdot> \<rho>). \<V> (inv \<rho> (id_subst x)) = \<V>' x \<Longrightarrow>
      typed \<V>' (expr \<cdot> \<rho>) \<tau> \<longleftrightarrow> typed \<V> expr \<tau>"
begin

sublocale typed_renaming 
  where base_vars = vars and base_subst = subst and base_typed = typed and is_typed = is_typed
  using explicit_typed_renaming
  by unfold_locales blast

lemma inv_renaming:
  assumes "is_renaming \<rho>"
  shows "inv \<rho> (\<rho> x) = x"
  using assms
  unfolding is_renaming_iff
  by simp

(* TODO: Name *)
lemma is_welltyped_renaming_ground_subst_weaker: 
  assumes 
    "is_renaming \<rho>"
    "is_typed_on UNIV \<V>' \<gamma>" 
    "is_typed_on X \<V> \<rho>" 
    "is_ground_subst \<gamma>" 
    "\<forall>x \<in> \<Union>(vars ` \<rho> ` X). \<V> (inv \<rho> (id_subst x)) = \<V>' x"
  shows "is_typed_on X \<V> (\<rho> \<odot> \<gamma>)"
proof(intro ballI)
  fix x
  assume "x \<in> X"

  then have "typed \<V> (\<rho> x) (\<V> x)"
    by (simp add: assms(3))

  obtain y where y: "\<rho> x = id_subst y"
    using obtain_renamed_variable[OF assms(1)].

  then have "y \<in> \<Union>(vars ` \<rho> ` X)"
    using \<open>x \<in> X\<close>  
    by (metis UN_iff image_eqI singletonI vars_id_subst)

  moreover have "typed \<V> (\<gamma> y) (\<V>' y)"
    using explicit_replace_\<V>
    by (metis assms(2,4) comp_subst.left_neutral emptyE is_ground_subst_is_ground iso_tuple_UNIV_I 
        comp_subst_iff)
   
  ultimately have "typed \<V> (\<gamma> y) (\<V> (inv \<rho> (id_subst y)))"
    using assms(5) by force

  moreover have "inv \<rho> (id_subst y) = x"
    unfolding y[symmetric]
    using inv_renaming[OF assms(1)].   

  moreover have "\<gamma> y = (\<rho> \<odot> \<gamma>) x"
    using y
    by (metis comp_subst.left_neutral comp_subst_iff)

  ultimately show "typed \<V> ((\<rho> \<odot> \<gamma>) x) (\<V> x)"
    by argo
qed

lemma inj_id_subst: "inj id_subst"
  using is_renaming_id_subst is_renaming_iff 
  by blast

lemma obtain_typed_renamings:
  fixes \<V>\<^sub>1 :: "'var \<Rightarrow> 'ty"
  assumes
    (* TODO: Move to locale assumption *)
    "infinite (UNIV :: 'var set)"
    "finite X" 
    "finite Y" 
    "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" 
    "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "'var \<Rightarrow> 'expr" where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2" 
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "is_typed_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_typed_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
proof-

  obtain renaming\<^sub>1 renaming\<^sub>2 :: "'var \<Rightarrow> 'var" where
    renamings:
    "inj renaming\<^sub>1" "inj renaming\<^sub>2"
    "renaming\<^sub>1 ` X \<inter> renaming\<^sub>2 ` Y = {}" 
    "\<forall>x \<in> X. \<V>\<^sub>1 (renaming\<^sub>1 x) = \<V>\<^sub>1 x" 
    "\<forall>x \<in> Y. \<V>\<^sub>2 (renaming\<^sub>2 x) = \<V>\<^sub>2 x"
    using obtain_type_preserving_injs[OF assms].
   
  define \<rho>\<^sub>1 :: "'var \<Rightarrow> 'expr" where
    "\<And>x. \<rho>\<^sub>1 x \<equiv> id_subst (renaming\<^sub>1 x)"

  define \<rho>\<^sub>2 :: "'var \<Rightarrow> 'expr" where
    "\<And>x. \<rho>\<^sub>2 x \<equiv> id_subst (renaming\<^sub>2 x)"

  have "is_renaming \<rho>\<^sub>1" "is_renaming \<rho>\<^sub>2"
    using renamings(1,2) is_renaming_id_subst
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def is_renaming_iff inj_def
    by blast+

  moreover have "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(3) inj_id_subst
    by (metis image_Int image_empty image_image)
 
  moreover have "is_typed_on X \<V>\<^sub>1 \<rho>\<^sub>1" "is_typed_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(4, 5)
    by(auto simp: typed_id_subst)

  ultimately show ?thesis 
    using that
    by presburger
qed

end

end
