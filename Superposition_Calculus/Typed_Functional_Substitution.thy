theory Typed_Functional_Substitution
  imports 
    Typing 
    Functional_Substitution
    Fun_Extra
begin

type_synonym ('v, 'ty) var_types = "'v \<Rightarrow> 'ty"

locale explicitly_typed_functional_substitution = 
  base_functional_substitution where vars = vars and id_subst = id_subst
for
  id_subst :: "'var \<Rightarrow> 'base" and
  vars :: "'base \<Rightarrow> 'var set" and
  expr_typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes predicate_typed: "\<And>\<V>. predicate_typed (expr_typed \<V>)"
begin

sublocale expr: predicate_typed "expr_typed \<V>"
  by (rule predicate_typed)

abbreviation is_typed_on where 
  "is_typed_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. expr_typed \<V> (\<sigma> x) (\<V> x)"

end

locale typed_functional_substitution = 
  base: explicitly_typed_functional_substitution where 
  vars = base_vars and subst = base_subst and expr_typed = base_typed +
  based_functional_substitution where vars = vars
for
  vars :: "'expr \<Rightarrow> 'var set" and
  expr_is_typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" and
  base_typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"

sublocale explicitly_typed_functional_substitution \<subseteq> typed_functional_substitution where 
  base_subst = subst and base_vars = vars and expr_is_typed = expr_is_typed and 
  base_typed = expr_typed
  by unfold_locales

locale functional_substitution_typing =
  is_typed: typed_functional_substitution where 
  base_typed = base_typed and expr_is_typed = expr_is_typed +
  is_welltyped: typed_functional_substitution where 
  base_typed = base_welltyped and expr_is_typed = expr_is_welltyped
for 
  base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
  expr_is_typed expr_is_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" +
assumes typing: "\<And>\<V>. typing (expr_is_typed \<V>) (expr_is_welltyped \<V>)"
begin

sublocale expr: typing "expr_is_typed \<V>" "expr_is_welltyped \<V>"
  by(rule typing)

abbreviation is_typed_on where
  "is_typed_on \<equiv> is_typed.base.is_typed_on"

abbreviation is_typed where 
  "is_typed \<equiv> is_typed_on UNIV"

abbreviation is_welltyped_on where
  "is_welltyped_on \<equiv> is_welltyped.base.is_typed_on"

abbreviation is_welltyped where 
  "is_welltyped \<equiv> is_welltyped_on UNIV"

end

locale base_functional_substitution_typing =
  typed: explicitly_typed_functional_substitution where expr_typed = expr_typed +
  welltyped: explicitly_typed_functional_substitution where 
  expr_typed = expr_welltyped
for 
  expr_welltyped expr_typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes 
   explicit_typing: "\<And>\<V>. explicit_typing (expr_typed \<V>) (expr_welltyped \<V>)" and
   welltyped_id_subst [intro]: "\<And>\<V> x. expr_welltyped \<V> (id_subst x) (\<V> x)"
begin

sublocale expr: explicit_typing "expr_typed \<V>" "expr_welltyped \<V>"
  by(rule explicit_typing)

sublocale functional_substitution_typing where 
  expr_is_typed = expr.is_typed and expr_is_welltyped = expr.is_welltyped and 
  base_typed = expr_typed and base_welltyped = expr_welltyped and base_vars = vars and 
  base_subst = subst
  by unfold_locales

sublocale typing "is_typed_on X \<V>" "is_welltyped_on X \<V>"
  using expr.typed_if_welltyped
  by unfold_locales blast

lemma typed_id_subst: "expr_typed \<V> (id_subst x) (\<V> x)"
  using welltyped_id_subst
  by (simp add: expr.typed_if_welltyped)

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
  subst_stability [simp]: "\<And>\<V> expr \<sigma>. base.is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> 
     expr_is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> expr_is_typed \<V> expr"

locale explicitly_typed_subst_stability = explicitly_typed_functional_substitution +
assumes
  subst_stability [simp]: "\<And>\<V> expr \<sigma> \<tau>. is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> 
     expr_typed \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> expr_typed \<V> expr \<tau>"
begin

sublocale typed_subst_stability where 
  base_vars = vars and base_subst = subst and base_typed = expr_typed and 
  expr_is_typed = expr.is_typed
  using subst_stability
  by unfold_locales blast

end

locale replaceable_\<V> = typed_functional_substitution +
  assumes replace_\<V>: "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow>
    expr_is_typed \<V> expr \<Longrightarrow> 
    expr_is_typed \<V>' expr"
begin

lemma replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x" 
  shows "expr_is_typed \<V> expr \<longleftrightarrow> expr_is_typed \<V>' expr"
  using assms
  by (metis replace_\<V>)

lemma is_ground_typed:
  assumes "is_ground expr" 
  shows "expr_is_typed \<V> expr \<longleftrightarrow> expr_is_typed \<V>' expr"
  using replace_\<V>_iff assms
  by blast

end

locale explicitly_replaceable_\<V> = explicitly_typed_functional_substitution +
  assumes replace_\<V>: "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow>
    expr_typed \<V> expr \<tau> \<Longrightarrow> 
    expr_typed \<V>' expr \<tau>"
begin

lemma replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x" 
  shows "expr_typed \<V> expr \<tau> \<longleftrightarrow> expr_typed \<V>' expr \<tau>"
  using assms
  by (metis replace_\<V>)

lemma is_ground_typed:
  assumes "is_ground expr" 
  shows "expr_typed \<V> expr \<tau> \<longleftrightarrow> expr_typed \<V>' expr \<tau>"
  using replace_\<V>_iff assms
  by blast

sublocale replaceable_\<V> where 
  base_vars = vars and base_subst = subst and base_typed = expr_typed and 
  expr_is_typed = expr.is_typed
  using replace_\<V>
  by unfold_locales blast

end

(* TODO: naming + the_inv \<rightarrow> rename *)
locale typed_renaming = typed_functional_substitution +
assumes
  typed_renaming [simp]: 
    "\<And>\<V> \<V>' expr \<rho>. is_renaming \<rho> \<Longrightarrow> 
      \<forall>x \<in> vars (expr \<cdot> \<rho>). \<V> (inv \<rho> (id_subst x)) = \<V>' x \<Longrightarrow>
      expr_is_typed \<V>' (expr \<cdot> \<rho>) \<longleftrightarrow> expr_is_typed \<V> expr"

locale explicitly_typed_renaming = 
  explicitly_typed_functional_substitution where expr_typed = expr_typed + 
  renaming_variables +
  explicitly_replaceable_\<V> where expr_typed = expr_typed 
for expr_typed :: "('var \<Rightarrow> 'ty) \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes
  typed_renaming [simp]: 
  "\<And>\<V> \<V>' expr \<rho> \<tau>. is_renaming \<rho> \<Longrightarrow> 
      \<forall>x \<in> vars (expr \<cdot> \<rho>). \<V> (inv \<rho> (id_subst x)) = \<V>' x \<Longrightarrow>
      expr_typed \<V>' (expr \<cdot> \<rho>) \<tau> \<longleftrightarrow> expr_typed \<V> expr \<tau>" and
  (* TODO: Move to correct place *)
  is_renaming_iff: "is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = id_subst x')" and
  subst_compose: "(\<rho> \<odot> \<gamma>) x = (\<rho> x) \<cdot> \<gamma>" and
  id_subst_keeps_var: "x \<in> vars (id_subst x)" and
  typed_id_subst: "\<V> x = \<tau> \<Longrightarrow> expr_typed \<V> (id_subst x) \<tau>"
begin

sublocale typed_renaming 
  where base_vars = vars and base_subst = subst and base_typed = expr_typed and 
  expr_is_typed = expr.is_typed
  using typed_renaming
  by unfold_locales blast

(* TODO: Move *)
lemma subst_update:
 assumes "expr_typed \<V> (id_subst var) \<tau>" "expr_typed \<V> update \<tau>"  "is_typed_on X \<V> \<gamma>" 
 shows "is_typed_on X \<V> (\<gamma>(var := update))"
  using assms typed_id_subst
  by fastforce

lemma inv_renaming:
  assumes "is_renaming \<rho>"
  shows "inv \<rho> (\<rho> x) = x"
  using assms
  unfolding is_renaming_iff
  by simp

(* TODO: *)
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

  then have "expr_typed \<V> (\<rho> x) (\<V> x)"
    by (simp add: assms(3))

  obtain y where y: "\<rho> x = id_subst y"
    using obtain_renamed_variable[OF assms(1)].

  then have "y \<in> \<Union>(vars ` \<rho> ` X)"
    using \<open>x \<in> X\<close>  id_subst_keeps_var
    by force

  moreover have "expr_typed \<V> (\<gamma> y) (\<V>' y)"
    using replace_\<V>
    by (metis UNIV_I assms(2,4) is_ground_subst_is_ground variable_grounding emptyE 
        id_subst_keeps_var)

  ultimately have "expr_typed \<V> (\<gamma> y) (\<V> (inv \<rho> (id_subst y)))"
    using assms(5) by force

  moreover have "inv \<rho> (id_subst y) = x"
    unfolding y[symmetric]
    using inv_renaming[OF assms(1)].   

  moreover have "\<gamma> y = (\<rho> \<odot> \<gamma>) x"
    using y
    by (metis comp_subst.left_neutral subst_compose)

  ultimately show "expr_typed \<V> ((\<rho> \<odot> \<gamma>) x) (\<V> x)"
    by argo
qed

lemma inj_id_subst: "inj id_subst"
  using is_renaming_id_subst is_renaming_iff 
  by blast

lemma obtain_typed_renamings:
  fixes \<V>\<^sub>1 :: "'var \<Rightarrow> 'ty"
  assumes 
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
