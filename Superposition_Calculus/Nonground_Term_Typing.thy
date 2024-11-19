theory Nonground_Term_Typing
  imports Term_Typing Functional_Substitution_Lifting
begin

locale subst_typing =
  functional_substitution where vars = vars and id_subst = id_subst + 
  dep_typing where is_typed = is_typed
for 
  id_subst :: "'var \<Rightarrow> 'base" and
  vars :: "'expr \<Rightarrow> 'var set" and
  is_typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" +
fixes is_typed_on is_welltyped_on :: "'var set \<Rightarrow> ('var, 'ty) var_types \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> bool"
assumes (* TODO: Separate locales *)
  is_typed_subst_stability:
  "\<And>\<V> expr \<sigma>. is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> 
      is_typed \<V> expr \<longleftrightarrow> is_typed \<V> (expr \<cdot> \<sigma>)" and
  is_welltyped_subst_stability:
  "\<And>\<V> expr \<sigma>. is_welltyped_on (vars expr) \<V> \<sigma> \<Longrightarrow> 
      is_welltyped \<V> expr \<longleftrightarrow> is_welltyped \<V> (expr \<cdot> \<sigma>)" and
  is_typed_replace_\<V>:
  "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> is_typed \<V> expr \<Longrightarrow> is_typed \<V>' expr" and
  is_welltyped_replace_\<V>:
  "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> is_welltyped \<V> expr \<Longrightarrow> is_welltyped \<V>' expr" 
begin

lemma is_typed_replace_\<V>_iff:
  "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> is_typed \<V> expr \<longleftrightarrow> is_typed \<V>' expr"
  by (metis is_typed_replace_\<V>)

lemma is_welltyped_replace_\<V>_iff:
  "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> is_welltyped \<V> expr \<longleftrightarrow> is_welltyped \<V>' expr"
  by (metis is_welltyped_replace_\<V>)

end

locale base_subst_typing =
  base_functional_substitution where vars = vars + 
  expr: dep_explicit_typing where typed = typed
for 
  vars :: "'expr \<Rightarrow> 'var set" and
  typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
fixes is_typed_on is_welltyped_on
defines
  "\<And>X \<V> \<sigma>. is_typed_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. typed \<V> (\<sigma> x) (\<V> x)" and
  "\<And>X \<V> \<sigma>. is_welltyped_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. welltyped \<V> (\<sigma> x) (\<V> x)"
assumes 
  welltyped_id_subst: "\<And>\<V> x. welltyped \<V> (id_subst x) (\<V> x)" and
  typed_subst_stability [simp]: 
  "\<And>\<V> expr \<sigma>. is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> typed \<V> expr \<tau> \<longleftrightarrow> typed \<V> (expr \<cdot> \<sigma>) \<tau>" and
  welltyped_subst_stability [simp]: 
  "\<And>\<V> expr \<sigma>. is_welltyped_on (vars expr) \<V> \<sigma> \<Longrightarrow>
    welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> (expr \<cdot> \<sigma>) \<tau>" and
  typed_replace_\<V>: 
    "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in>vars expr. \<V> x = \<V>' x \<Longrightarrow> typed \<V> expr \<tau> \<Longrightarrow> typed \<V>' expr \<tau>" and
  welltyped_replace_\<V>: 
    "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in>vars expr. \<V> x = \<V>' x \<Longrightarrow> welltyped \<V> expr \<tau> \<Longrightarrow> welltyped \<V>' expr \<tau>"
begin

abbreviation is_typed where 
  "is_typed \<equiv> is_typed_on UNIV"

abbreviation is_welltyped where 
  "is_welltyped \<equiv> is_welltyped_on UNIV"

sublocale subst_typing where 
  is_welltyped = "expr.is_welltyped" and
  is_typed = "expr.is_typed"
  using expr.is_typed_def expr.is_welltyped_def 
  by unfold_locales (auto intro: typed_replace_\<V> welltyped_replace_\<V>)

sublocale dep_typing "is_typed_on X" "is_welltyped_on X"
  unfolding is_typed_on_def is_welltyped_on_def
  using expr.typed_if_welltyped
  by unfold_locales auto

lemma typed_id_subst: "\<And>\<V> x. typed \<V> (id_subst x) (\<V> x)"
  using welltyped_id_subst
  by (simp add: expr.typed_if_welltyped)

lemma is_typed_id_subst [simp]: "is_typed_on X \<V> id_subst"
  using typed_id_subst
  unfolding is_typed_on_def
  by auto

lemma is_welltyped_id_subst [simp]: "is_welltyped_on X \<V> id_subst"
  using welltyped_id_subst
  unfolding is_welltyped_on_def
  by auto

lemma is_typed_on_subset:
  assumes "is_typed_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "is_typed_on X \<V> \<sigma>"
  using assms
  unfolding is_typed_on_def
  by blast

lemma is_welltyped_on_subset:
  assumes "is_welltyped_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "is_welltyped_on X \<V> \<sigma>"
  using assms
  unfolding is_welltyped_on_def
  by blast

lemma is_typed_on_replace_\<V>:
  assumes 
    "\<forall>x\<in> X. \<V> x = \<V>' x"
    "\<forall>x\<in> X. is_ground (\<gamma> x)"
  shows  
    "is_typed_on X \<V> \<gamma> \<longleftrightarrow> is_typed_on X \<V>' \<gamma>"
  using assms typed_replace_\<V>
  unfolding is_typed_on_def
  by (metis empty_iff)

lemma is_welltyped_on_replace_\<V>:
  assumes 
    "\<forall>x\<in> X. \<V> x = \<V>' x"
    "\<forall>x\<in> X. is_ground (\<gamma> x)"
  shows  
    "is_welltyped_on X \<V> \<gamma> \<longleftrightarrow> is_welltyped_on X \<V>' \<gamma>"
  using assms welltyped_replace_\<V>
  unfolding is_welltyped_on_def
  by (metis empty_iff)

end

(* TODO: Maybe do with explicit typing?*)
locale subst_typing_lifting = 
  base: base_subst_typing where 
  vars = base_vars and subst = base_subst and typed = base_typed and welltyped = base_welltyped +
  based_functional_substitution_lifting where sub_vars = sub_vars +
  sub: subst_typing where 
  vars = sub_vars and subst = sub_subst and is_typed = is_typed_sub and 
  is_welltyped = is_welltyped_sub 
for 
  base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
  sub_vars :: "'sub \<Rightarrow> 'var set" and 
  is_typed_sub is_welltyped_sub :: "('var, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> bool"
begin

sublocale typing_lifting where 
  is_typed_sub = "is_typed_sub \<V>" and is_welltyped_sub = "is_welltyped_sub \<V>" 
  by unfold_locales

(* TODO *)
sublocale subst_typing where 
  is_typed = is_typed and is_welltyped = is_welltyped and vars = vars and subst = subst
  apply unfold_locales
    apply (simp add: is_typed_if_is_welltyped)
  using sub.is_typed_subst_stability
  unfolding vars_def is_typed_def subst_def is_welltyped_def
   apply (smt (verit, best) SUP_upper2 base.is_typed_on_subset dual_order.refl image_iff to_set_map)
  using  sub.is_welltyped_subst_stability
    apply (smt (verit, best) SUP_upper2 base.is_welltyped_on_subset dual_order.refl image_iff to_set_map)
   apply (metis Union_iff imageI sub.is_typed_replace_\<V>)
  by (metis Union_iff imageI sub.is_welltyped_replace_\<V>)

end


end
