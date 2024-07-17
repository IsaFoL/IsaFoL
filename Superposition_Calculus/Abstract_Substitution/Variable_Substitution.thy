theory Variable_Substitution
  imports Abstract_Substitution "HOL-Library.FSet"
begin

(* TODO: Name + different file *)
locale set_spec = 
  fixes
    contains :: "'x \<Rightarrow> 'set \<Rightarrow> bool"  and
    is_empty is_finite :: "'set \<Rightarrow> bool" and
    subset_eq disjoint :: "'set \<Rightarrow> 'set \<Rightarrow> bool"
  assumes
    is_empty: "\<And>X. is_empty X \<longleftrightarrow> (\<forall>x. \<not> contains x X)" and
    is_finite: "\<And>X. is_finite X \<longleftrightarrow> (\<exists>n f. \<forall>x. contains x X \<longrightarrow> x \<in> f ` {i::nat. i < n})" and
    subset_eq: "\<And>X Y. subset_eq X Y \<longleftrightarrow> (\<forall>x. contains x X \<longrightarrow> contains x Y)" and
    disjoint: "\<And>X Y. disjoint X Y \<longleftrightarrow> 
        (\<forall>x. contains x X \<longrightarrow> \<not> contains x Y) \<and> (\<forall>x. contains x Y \<longrightarrow> \<not> contains x X)" 

interpretation set : set_spec where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}"
proof unfold_locales
  show "\<And>X. finite X = (\<exists>n f. \<forall>x. x \<in> X \<longrightarrow> x \<in> f ` {i :: nat. i < n})"
    by (metis finite_conv_nat_seg_image rev_finite_subset subset_eq)
qed auto

interpretation fset : set_spec where 
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"
proof unfold_locales
  show "\<And>X. True = (\<exists>n f. \<forall>x. x |\<in>| X \<longrightarrow> x \<in> f ` {i :: nat. i < n})"
    using finite_fset set.is_finite by blast
qed auto

locale variable_substitution = 
  basic_substitution _ _ subst "\<lambda>a. is_empty (vars a)" +
  set_spec where 
  contains = contains and is_empty = is_empty  and is_finite = is_finite and 
  subset_eq = subset_eq and disjoint = disjoint

for subst :: "'value \<Rightarrow> ('variable \<Rightarrow> 'subvalue) \<Rightarrow> 'value" (infixl "\<cdot>" 70) and
  vars :: "'value \<Rightarrow> 'variableset" and
  contains is_empty is_finite subset_eq disjoint  +
assumes
  subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. contains x (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>" and
  finite_vars [simp]: "\<And>a. is_finite (vars a)"
begin

abbreviation is_ground where "is_ground a \<equiv> is_empty (vars a)"

lemma subst_reduntant_upd [simp]:
  assumes "\<not> contains var (vars a)"
  shows "a \<cdot> \<sigma>(var := update) = a \<cdot> \<sigma>"
  using assms subst_eq
  by fastforce

lemma subst_reduntant_if [simp]: 
  assumes "subset_eq (vars a) vars'"
  shows "a \<cdot> (\<lambda>var. if contains var vars' then \<sigma> var else \<sigma>' var) = a \<cdot> \<sigma>"
  using assms subst_eq subset_eq
  by fastforce

lemma subst_reduntant_if' [simp]: 
  assumes "disjoint (vars a) vars'"  
  shows "a \<cdot> (\<lambda>var. if contains var vars' then \<sigma>' var else \<sigma> var) = a \<cdot> \<sigma>"
  using assms subst_eq subset_eq  disjoint
  by fastforce

end

(* TODO: Type annotations *)
locale variable_substitution_lifting = base: variable_substitution + 
  variable_substitution where
  subst = lifted_subst and 
  id_subst = id_subst and 
  comp_subst = comp_subst and 
  vars = lifted_vars 
for lifted_subst lifted_vars +
assumes 
  lifted_vars_vars: 
  "(\<forall>x. is_empty (lifted_vars (lifted_subst x \<gamma>))) \<longleftrightarrow> (\<forall>x. is_empty (vars (x \<cdot> \<gamma>)))"
begin

lemma is_ground_subst_iff [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  base.is_ground_subst_def
  using lifted_vars_vars
  by presburger

end

locale variable_substitution_set = variable_substitution where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}" 

locale variable_substitution_lifting_set = variable_substitution_lifting where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}" 

locale variable_substitution_fset = variable_substitution where
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"

locale variable_substitution_lifting_fset = variable_substitution_lifting where 
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"

end
