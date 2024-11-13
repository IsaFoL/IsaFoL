theory Entailment_Lifting
  imports Functional_Substitution_Lifting
begin

locale entailment = 
  based: based_functional_substitution where base_subst = base_subst and vars = vars + 
  base: grounding where subst = base_subst and vars = base_vars and to_ground = base_to_ground and 
  from_ground = base_from_ground for 
  vars :: "'expr \<Rightarrow> 'var set" and
  base_subst :: "'base \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'base" and 
  base_to_ground :: "'base \<Rightarrow> 'base\<^sub>G" and 
  base_from_ground +
fixes entails_def :: "'expr \<Rightarrow> bool" and I ::  "('base\<^sub>G \<times> 'base\<^sub>G) set"
assumes
  congruence: "\<And>expr \<gamma> var update. 
        based.base.is_ground update \<Longrightarrow>
        based.base.is_ground (\<gamma> var) \<Longrightarrow>
        (base_to_ground (\<gamma> var), base_to_ground update) \<in> I \<Longrightarrow>
        based.is_ground (subst expr \<gamma>) \<Longrightarrow> 
        entails_def (subst expr (\<gamma>(var := update))) \<Longrightarrow> 
        entails_def (subst expr \<gamma>)" 
begin

abbreviation "entails \<equiv> entails_def"

end

locale symmetric_entailment = entailment + 
  assumes sym: "sym I"
begin

lemma symmetric_congruence:
  assumes 
    update_is_ground: "based.base.is_ground update" and
    var_grounding: "based.base.is_ground (\<gamma> var)" and
    var_update: "(base_to_ground (\<gamma> var), base_to_ground update) \<in> I" and
    expr_grounding: "based.is_ground (subst expr \<gamma>)" 
  shows
    "entails (subst expr (\<gamma>(var := update))) \<longleftrightarrow> entails (subst expr \<gamma>)" 
  using congruence[OF var_grounding, of "\<gamma>(var := update)"] assms
  by (metis based.ground_subst_upd congruence fun_upd_same fun_upd_triv fun_upd_upd sym symD)

end

locale symmetric_base_entailment = 
  base_functional_substitution where subst = subst + 
  grounding where subst = subst and to_ground = to_ground for
  subst :: "'base \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'base"  (infixl "\<cdot>" 70) and
  to_ground :: "'base \<Rightarrow> 'base\<^sub>G" +
fixes I :: "('base\<^sub>G \<times> 'base\<^sub>G) set"
assumes
  sym: "sym I" and
  congruence: "\<And>expr expr' update \<gamma> var. 
      is_ground update \<Longrightarrow> 
      is_ground (\<gamma> var) \<Longrightarrow> 
      (to_ground (\<gamma> var), to_ground update) \<in> I \<Longrightarrow>
      is_ground (expr \<cdot> \<gamma>) \<Longrightarrow> 
      (to_ground (expr \<cdot> (\<gamma>(var := update))), expr') \<in> I \<Longrightarrow>
      (to_ground (expr \<cdot> \<gamma>), expr') \<in> I"
begin

lemma symmetric_congruence:
  assumes
    update_is_ground: "is_ground update" and
    var_grounding: "is_ground (\<gamma> var)" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>)" and
    var_update: "(to_ground (\<gamma> var), to_ground update) \<in> I"
  shows "(to_ground (expr \<cdot> (\<gamma>(var := update))), expr') \<in> I \<longleftrightarrow> (to_ground (expr \<cdot> \<gamma>), expr') \<in> I" 
  using assms congruence[OF var_grounding, of "\<gamma>(var := update)" var] congruence
  by (metis fun_upd_same fun_upd_triv fun_upd_upd ground_subst_upd sym symD)

lemma simultaneous_congruence:
  assumes
    update_is_ground: "is_ground update" and
    var_grounding: "is_ground (\<gamma> var)" and
    var_update: "(to_ground (\<gamma> var), to_ground update) \<in> I" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>)" "is_ground (expr' \<cdot> \<gamma>)"
  shows 
    "(to_ground (expr \<cdot> (\<gamma>(var := update))), to_ground (expr' \<cdot> (\<gamma>(var := update)))) \<in> I \<longleftrightarrow> 
        (to_ground (expr \<cdot> \<gamma>), to_ground (expr' \<cdot> \<gamma>))  \<in> I"
  using assms
  by (meson sym symD symmetric_congruence)

end

locale entailment_lifting =
  based_functional_substitution_lifting +
  finite_variables_lifting +
  sub: symmetric_entailment 
  where subst = sub_subst and vars = sub_vars and entails_def = sub_entails
  for sub_entails +
  fixes 
    is_negated :: "'d \<Rightarrow> bool" and 
    empty :: bool and 
    connective :: "bool \<Rightarrow> bool \<Rightarrow> bool" and
    entails_def
  assumes 
    is_negated_subst: "\<And>expr \<sigma>. is_negated (subst expr \<sigma>) \<longleftrightarrow> is_negated expr" and
    entails_def: "\<And>expr. entails_def expr \<longleftrightarrow>
      (if is_negated expr then Not else (\<lambda>x. x))
        (Finite_Set.fold connective empty (sub_entails  ` to_set expr))"
begin

notation sub_entails ("(\<Turnstile>\<^sub>s _)" [50] 50)
notation entails_def ("(\<Turnstile> _)" [50] 50)

sublocale symmetric_entailment where subst = subst and vars = vars and entails_def = entails_def
proof unfold_locales
  fix expr \<gamma> var update P
  assume
    "base.is_ground update"
    "base.is_ground (\<gamma> var)"
    "is_ground (expr \<cdot> \<gamma>)"
    "(base_to_ground (\<gamma> var), base_to_ground update) \<in> I"
    "\<Turnstile> expr \<cdot> \<gamma>(var := update)"

  moreover then have "\<forall>sub \<in> to_set expr. (\<Turnstile>\<^sub>s sub \<cdot>\<^sub>s \<gamma>(var := update)) \<longleftrightarrow> \<Turnstile>\<^sub>s sub \<cdot>\<^sub>s \<gamma>"
    using sub.symmetric_congruence[of update \<gamma>] to_set_is_ground_subst 
    by blast

  ultimately show "\<Turnstile> expr \<cdot> \<gamma>"
    unfolding is_negated_subst entails_def
    by(auto simp: image_image subst_def)

qed (simp_all add: is_grounding_iff_vars_grounded sub.sym )

end

locale entailment_lifting_conj = entailment_lifting
  where connective = "(\<and>)" and empty = True

locale entailment_lifting_disj = entailment_lifting
  where connective = "(\<or>)" and empty = False

end
