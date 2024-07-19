theory Variable_Substitution
  imports Abstract_Substitution "HOL-Library.FSet"
begin

(* TODO: Name + different file + maybe refine such that also mulitset works *)
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
  subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression" (infixl "\<cdot>" 70) and
  vars :: "'expression \<Rightarrow> 'variables" and
  contains is_empty is_finite subset_eq disjoint  +
assumes subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. contains x (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>"
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

locale finite_variables = 
  fixes is_finite :: "'variables \<Rightarrow> bool" and vars :: "'expression \<Rightarrow> 'variables"
  assumes finite_vars [simp]: "\<And>a. is_finite (vars a)"

locale all_subst_ident_iff_ground = 
  fixes 
    is_finite :: "'expressions \<Rightarrow> bool" and
    contains :: "'expression \<Rightarrow> 'expressions \<Rightarrow> bool" and
    is_ground :: "'expression \<Rightarrow> bool" and
    subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression"
  assumes
    all_subst_ident_iff_ground: "\<And>a. is_ground a \<longleftrightarrow> (\<forall>\<sigma>. subst a \<sigma> = a)" and
    exists_non_ident_subst: 
      "\<And>a s. is_finite s \<Longrightarrow> \<not>is_ground a \<Longrightarrow> \<exists>\<sigma>. subst a \<sigma> \<noteq> a \<and> \<not> contains (subst a \<sigma>) s"
  
(* TODO: Remove? *)
locale variable_substitution_expansion = base: variable_substitution + 
  variable_substitution where
  subst = expanded_subst and 
  id_subst = "id_subst" and 
  comp_subst = comp_subst and 
  vars = expanded_vars 
for expanded_subst expanded_vars +
assumes
  expanded_vars_vars: 
    "(\<forall>x. is_empty (expanded_vars (expanded_subst x \<gamma>))) \<longleftrightarrow> (\<forall>x. is_empty (vars (x \<cdot> \<gamma>)))"
begin

(* TODO: name *)
lemma is_ground_subst_iff_base_is_ground_subst [simp]: 
  "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  base.is_ground_subst_def
  using expanded_vars_vars
  by presburger

end

locale variable_substitution_set = variable_substitution where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}"

(* TODO: With set spec *)
locale variable_substitution_lifting_set = 
  base: variable_substitution_set comp_subst id_subst base_subst base_vars
  for 
    id_subst :: "'variable \<Rightarrow> 'base_expression" and
    base_vars :: "'sub_expression \<Rightarrow> 'variable set" and
    comp_subst base_subst +
  fixes 
    map :: "('sub_expression \<Rightarrow> 'sub_expression) \<Rightarrow> 'expression \<Rightarrow> 'expression" and
    to_set :: "'expression \<Rightarrow> 'sub_expression set" 
  assumes 
    map_comp: "\<And>d f g. map f (map g d) = map (f \<circ> g) d" and
    map_id: "map id d = d" and
    map_cong: "\<And>d f g. (\<And>c. c \<in> to_set d \<Longrightarrow> f c = g c) \<Longrightarrow> map f d = map g d" and
    (* TODO: Better def? *)
    Union_range_to_set: "\<Union>(range to_set) = UNIV" and
    to_set_map: "\<And>d f. to_set (map f d) = f ` to_set d"  
begin

definition vars :: "'expression \<Rightarrow> 'variable set" where
  "vars d \<equiv> \<Union>(base_vars ` to_set d)"

definition subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression" where
  "subst d \<sigma> \<equiv> map (\<lambda>c. base_subst c \<sigma>) d"

lemma map_id_cong: 
  assumes "\<And>c. c \<in> to_set d \<Longrightarrow> f c = c"  
  shows "map f d = d"
  using map_cong map_id assms
  unfolding id_def
  by metis

lemma to_set_map_not_ident: 
  assumes "c \<in> to_set d" "f c \<notin> to_set d" 
  shows "map f d \<noteq> d"
  by (metis assms image_eqI to_set_map)

lemma subst_in_to_set_subst:
  assumes "c \<in> to_set d" 
  shows "base_subst c \<sigma> \<in> to_set (subst d \<sigma>)"
  unfolding subst_def
  using to_set_map assms by auto

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

lemma is_ground_subst_iff_base_is_ground_subst [simp]: 
  "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  base.is_ground_subst_def
  using is_ground_iff_base_is_ground
  by presburger

end

locale finite_variables_lifting = 
  variable_substitution_lifting_set + 
  base: finite_variables where is_finite = finite and vars = base_vars +
  assumes finite_to_set: "\<And>d. finite (to_set d)"
begin

sublocale finite_variables 
  where is_finite = finite and vars = vars
proof unfold_locales
 show "\<And>a. finite (vars a)"
    unfolding vars_def
    using base.finite_vars finite_to_set
    by blast
qed

end

locale all_subst_ident_iff_ground_lifiting = 
  finite_variables_lifting +
  base: all_subst_ident_iff_ground where is_ground = base.is_ground and subst = base_subst 
    and is_finite = finite and contains = "(\<in>)" 
begin

sublocale all_subst_ident_iff_ground 
  where is_finite = finite and contains = "(\<in>)" and is_ground = is_ground and subst = subst 
proof unfold_locales
  show "\<And>x. is_ground x = (\<forall>\<sigma>. subst x \<sigma> = x)"
  proof(intro iffI allI)
    show "\<And>x \<sigma>. is_ground x \<Longrightarrow> subst x \<sigma> = x"
      by simp
  next
    fix d 
    assume all_subst_ident: "\<forall>\<sigma>. subst d \<sigma> = d"
    
    show "is_ground d"
    proof(rule ccontr)
      assume "\<not>is_ground d"

      then obtain c where c_in_d: "c \<in> to_set d" and c_not_ground: "\<not>base.is_ground c"
        unfolding vars_def
        by blast

      then obtain \<sigma> where "base_subst c \<sigma> \<noteq> c" and "base_subst c \<sigma> \<notin> to_set d"
        using base.exists_non_ident_subst finite_to_set
        by blast
        
      then show False
        using all_subst_ident c_in_d to_set_map
        unfolding subst_def 
        by (metis image_eqI)
    qed
  qed
next
  fix d :: 'd and ds :: "'d set"
  assume finite_ds: "finite ds" and d_not_ground: "\<not>is_ground d"

  then have finite_cs: "finite (\<Union>(to_set ` insert d ds))"
    using finite_to_set by blast

  obtain c where c_in_d: "c \<in> to_set d" and c_not_ground: "\<not>base.is_ground c"
    using d_not_ground
    unfolding vars_def
    by blast

  obtain \<sigma> where \<sigma>_not_ident: "base_subst c \<sigma> \<noteq> c" "base_subst c \<sigma> \<notin> \<Union> (to_set ` insert d ds)"
    using base.exists_non_ident_subst[OF finite_cs c_not_ground]
    by blast

  then have "subst d \<sigma> \<noteq> d"
    using c_in_d
    unfolding subst_def
    by (simp add: to_set_map_not_ident)

  moreover have "subst d \<sigma> \<notin> ds"
    using \<sigma>_not_ident(2) c_in_d to_set_map
    unfolding subst_def
    by auto

  ultimately show "\<exists>\<sigma>. subst d \<sigma> \<noteq> d \<and> subst d \<sigma> \<notin> ds"
    by blast
qed

end

locale mylifting = all_subst_ident_iff_ground_lifiting

locale variable_substitution_expansion_set = variable_substitution_expansion where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}" 

locale variable_substitution_fset = variable_substitution where
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"

locale variable_substitution_expansion_fset = variable_substitution_expansion where 
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"

end
