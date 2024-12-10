theory Grounded_Order
  imports 
    Restricted_Order
    Functional_Substitution_Lifting
begin

section \<open>Orders with ground restrictions\<close>

locale grounded_order = 
  strict_order where less = less +
  grounding where vars = vars
for 
  less :: "'expr \<Rightarrow> 'expr \<Rightarrow> bool"  (infix \<open>\<prec>\<close> 50) (* TODO *) and 
  vars :: "'expr \<Rightarrow> 'var set"
begin

sublocale strict_order_restriction where lift = "from_ground" 
  by unfold_locales (rule inj_from_ground)

abbreviation "less\<^sub>G \<equiv> less\<^sub>r"
lemmas less\<^sub>G_def = less\<^sub>r_def
notation less\<^sub>G (infix "\<prec>\<^sub>G" 50)

abbreviation "less_eq\<^sub>G \<equiv> less_eq\<^sub>r"
notation less_eq\<^sub>G (infix "\<preceq>\<^sub>G" 50)

lemma to_ground_less\<^sub>r [simp]: 
  assumes "is_ground e" and "is_ground e'"
  shows "to_ground e \<prec>\<^sub>G to_ground e' \<longleftrightarrow> e \<prec> e'"
  by (simp add: assms less\<^sub>r_def)

lemma to_ground_less_eq\<^sub>r [simp]:
  assumes "is_ground e" and "is_ground e'" 
  shows "to_ground e \<preceq>\<^sub>G to_ground e' \<longleftrightarrow> e \<preceq> e'"
  using assms obtain_grounding
  by fastforce

lemma less_eq\<^sub>r_from_ground [simp]:
  "e\<^sub>G \<preceq>\<^sub>G e\<^sub>G' \<longleftrightarrow> from_ground e\<^sub>G \<preceq> from_ground e\<^sub>G'"
  unfolding R\<^sub>r_def
  by (simp add: inj_eq inj_lift)

end

locale grounded_restricted_total_strict_order = 
  order: restricted_total_strict_order where restriction = "range from_ground" +
  grounded_order
begin

sublocale total_strict_order_restriction where lift = "from_ground"
  by unfold_locales

lemma not_less_eq [simp]: 
  assumes "is_ground expr" and "is_ground expr'"
  shows "\<not> order.less_eq expr' expr \<longleftrightarrow> expr \<prec> expr'"
  using assms order.totalp
  unfolding totalp_on_def is_ground_iff_range_from_ground
  by auto

end

locale grounded_restricted_wellfounded_strict_order = 
  restricted_wellfounded_strict_order where restriction = "range from_ground" +
  grounded_order
begin

sublocale wellfounded_strict_order_restriction where lift = "from_ground"
  by unfold_locales

end

subsection \<open>Ground substitution stability\<close>

locale ground_subst_stability = grounding + 
  fixes R
  assumes
    ground_subst_stability: 
      "\<And>expr\<^sub>1 expr\<^sub>2 \<gamma>.
        is_ground (expr\<^sub>1 \<cdot> \<gamma>) \<Longrightarrow>
        is_ground (expr\<^sub>2 \<cdot> \<gamma>) \<Longrightarrow>
        R expr\<^sub>1 expr\<^sub>2 \<Longrightarrow>
        R (expr\<^sub>1 \<cdot> \<gamma>) (expr\<^sub>2 \<cdot> \<gamma>)"

locale ground_subst_stable_grounded_order = 
  grounded_order + 
  ground_subst_stability where R = "(\<prec>)"
begin

sublocale less_eq: ground_subst_stability where R = "(\<preceq>)"
  using ground_subst_stability
  by unfold_locales blast

lemma ground_less_not_less_eq:
  assumes 
    grounding: "is_ground (expr\<^sub>1 \<cdot> \<gamma>)" "is_ground (expr\<^sub>2 \<cdot> \<gamma>)" and
    less: "expr\<^sub>1 \<cdot> \<gamma> \<prec> expr\<^sub>2 \<cdot> \<gamma>"
  shows
    "\<not> expr\<^sub>2 \<preceq> expr\<^sub>1"
  using less ground_subst_stability[OF grounding(2, 1)] dual_order.asym
  by blast

end

subsection \<open>Substitution update stability\<close>

locale subst_update_stability =
  based_functional_substitution +
  fixes base_R R
  assumes
    subst_update_stability: 
      "\<And>update x \<gamma> expr.
        base.is_ground update \<Longrightarrow>
        base_R update (\<gamma> x) \<Longrightarrow> 
        is_ground (expr \<cdot> \<gamma>) \<Longrightarrow>
        x \<in> vars expr \<Longrightarrow>
        R (expr \<cdot> \<gamma>(x := update)) (expr \<cdot> \<gamma>)"

locale base_subst_update_stability = 
  base_functional_substitution + 
  subst_update_stability where base_R = R and base_subst = subst and base_vars = vars

locale subst_update_stable_grounded_order =
  grounded_order + subst_update_stability where R = less and base_R = base_less
for base_less
begin

sublocale less_eq: subst_update_stability 
  where base_R = "base_less\<^sup>=\<^sup>=" and R = "less\<^sup>=\<^sup>="
  using subst_update_stability
  by unfold_locales auto  

end

locale base_subst_update_stable_grounded_order = 
  base_subst_update_stability where R = less + 
  subst_update_stable_grounded_order where 
  base_less = less and base_subst = subst and base_vars = vars

end
