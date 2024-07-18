theory Variable_Substitution
  imports Abstract_Substitution "HOL-Library.FSet"
begin

(* TODO: Name + different file + maybe refine that also mulitset works *)
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
for
  subst :: "'value \<Rightarrow> ('variable \<Rightarrow> 'subvalue) \<Rightarrow> 'value" (infixl "\<cdot>" 70) and
  vars :: "'value \<Rightarrow> 'variableset" and
  contains is_empty is_finite subset_eq disjoint  +
assumes
  subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. contains x (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>" and
  (* TODO: extract*)
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

(* TODO: With set spec *)
locale variable_substitution_lifting_set' = 
  base: variable_substitution_set comp_subst id_subst base_subst base_vars
  for comp_subst id_subst base_subst base_vars +
  fixes 
    map :: "('c \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'd" and
    to_set :: "'d \<Rightarrow> 'c set" 
  assumes 
    map_comp: "\<And>d f g. map f (map g d) = map (f \<circ> g) d" and
    map_id: "map id d = d" and
    map_cong: "\<And>d f g. (\<And>c. c \<in> to_set d \<Longrightarrow> f c = g c) \<Longrightarrow> map f d = map g d" and
    finite_to_set: "\<And>d. finite (to_set d)" and
    Union_range_to_set: "\<Union>(range to_set) = UNIV" and
    to_set_map: "\<And>d f. to_set (map f d) = f ` to_set d"  
begin

definition vars :: "'d \<Rightarrow> 'a set" where
  "vars d \<equiv> \<Union>(base_vars ` to_set d)"

definition subst ::  "'d \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'd" where
  "subst d \<sigma> \<equiv> map (\<lambda>c. base_subst c \<sigma>) d"

lemma map_id_cong: "\<And>d f. (\<And>c. c \<in> to_set d \<Longrightarrow> f c = c) \<Longrightarrow> map f d = d"
  using map_cong map_id
  unfolding id_def
  by metis

sublocale variable_substitution_set comp_subst id_subst subst vars
proof unfold_locales
  show "\<And>x a b. subst x (comp_subst a b) = subst (subst x a) b"
    using base.subst_comp_subst
    unfolding subst_def map_comp comp_apply
    by presburger
next
  show "\<And>x. subst x id_subst = x"
    using map_id
    unfolding subst_def base.subst_id_subst id_def.
next
   show "\<And>d. vars d = {} \<Longrightarrow> \<forall>\<sigma>. subst d \<sigma> = d"
     unfolding vars_def subst_def
     using map_id_cong
     by auto
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> subst a \<sigma> = subst a \<tau>"
    unfolding vars_def subst_def
    using map_cong base.subst_eq
    by (meson UN_I)
next
  show "\<And>a. finite (vars a)"
    unfolding vars_def
    using base.finite_vars finite_to_set
    by blast
qed

lemma is_ground_iff_base_is_ground: 
  "(\<forall>d. is_ground (subst d \<gamma>)) \<longleftrightarrow> (\<forall>c. base.is_ground (base_subst c \<gamma>))"
proof(intro iffI allI)
  fix c 
  assume all_d_ground: "\<forall>d. is_ground (subst d \<gamma>)"
  show "base.is_ground (base_subst c \<gamma>)"
  proof(rule ccontr)
    assume c_not_ground: "\<not>base.is_ground (base_subst c \<gamma>)"

    then obtain d where "c \<in> to_set d"
      using Union_range_to_set by auto

    then have "\<not>is_ground (subst d \<gamma>)"
      using c_not_ground to_set_map
      unfolding subst_def vars_def
      by auto

    then show False
      using all_d_ground
      by blast
  qed
next
  fix d
  assume all_c_ground: "\<forall>c. base.is_ground (base_subst c \<gamma>)"

  then show "is_ground (subst d \<gamma>)"
    unfolding vars_def subst_def
    using to_set_map
    by auto 
qed

lemma is_ground_subst_iff [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  base.is_ground_subst_def
  using is_ground_iff_base_is_ground
  by presburger

end

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
