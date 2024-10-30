theory Variable_Substitution
  imports
    Abstract_Substitution.Substitution
    "HOL-Library.FSet"
    "HOL-Library.Multiset"
begin

locale finite_set =
  fixes set :: "'b \<Rightarrow> 'a set"
  assumes finite_set [simp]: "\<And>b. finite (set b)"
begin

abbreviation finite_set :: "'b \<Rightarrow> 'a fset" where 
  "finite_set b \<equiv> Abs_fset (set b)"

lemma finite_set': "set b \<in> {A. finite A}"
  by simp

lemma fset_finite_set [simp]: "fset (finite_set b) = set b"
  using Abs_fset_inverse[OF finite_set'].

end

locale variable_substitution = substitution _ _ subst "\<lambda>a. vars a = {}" 
for
  subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression" (infixl "\<cdot>" 70) and
  vars :: "'expression \<Rightarrow> 'variable set" +
assumes 
  subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>"
begin

abbreviation is_ground where "is_ground a \<equiv> vars a = {}"

definition vars_set :: "'expression set \<Rightarrow> 'variable set" where
  "vars_set expressions \<equiv> \<Union>expression \<in> expressions. vars expression"

lemma subst_reduntant_upd [simp]:
  assumes "var \<notin> vars a"
  shows "a \<cdot> \<sigma>(var := update) = a \<cdot> \<sigma>"
  using assms subst_eq
  by fastforce

lemma subst_reduntant_if [simp]: 
  assumes "vars a \<subseteq> vars'"
  shows "a \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma> var else \<sigma>' var) = a \<cdot> \<sigma>"
  using assms 
  by (smt (verit, best) subset_eq subst_eq)

lemma subst_reduntant_if' [simp]: 
  assumes "vars a \<inter> vars' = {}"  
  shows "a \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma>' var else \<sigma> var) = a \<cdot> \<sigma>"
  using assms subst_eq 
  unfolding disjoint_iff
  by presburger

lemma subst_cannot_unground:
  assumes "\<not>is_ground (a \<cdot> \<sigma>)"  
  shows "\<not>is_ground a" 
  using assms by force

end

locale finite_variables = finite_set vars for vars :: "'expression \<Rightarrow> 'variable set"
begin

lemmas finite_vars = finite_set finite_set'
lemmas fset_finite_vars = fset_finite_set

abbreviation "finite_vars \<equiv> finite_set"

end

locale all_subst_ident_iff_ground =
  fixes is_ground :: "'expression \<Rightarrow> bool" and subst 
  assumes
    all_subst_ident_iff_ground: "\<And>a. is_ground a \<longleftrightarrow> (\<forall>\<sigma>. subst a \<sigma> = a)" and
    exists_non_ident_subst: 
      "\<And>a s. finite s \<Longrightarrow> \<not>is_ground a \<Longrightarrow> \<exists>\<sigma>. subst a \<sigma> \<noteq> a \<and> subst a \<sigma> \<notin> s"

locale grounding = variable_substitution 
  where vars = vars for vars :: "'a \<Rightarrow> 'var set" +
  fixes to_ground :: "'a \<Rightarrow> 'g" and from_ground :: "'g \<Rightarrow> 'a"
  assumes 
    range_from_ground_iff_is_ground: "{f. is_ground f} = range from_ground" and
    from_ground_inverse [simp]: "\<And>g. to_ground (from_ground g) = g"
begin

definition groundings ::"'a \<Rightarrow> 'g set" where
  "groundings a = { to_ground (a \<cdot> \<gamma>) | \<gamma>. is_ground (a \<cdot> \<gamma>) }"

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

lemma ground_is_ground [simp, intro]: "is_ground (from_ground g)"
  using range_from_ground_iff_is_ground
  by blast

lemma is_ground_iff_range_from_ground: "is_ground f \<longleftrightarrow> f \<in> range from_ground"
  using range_from_ground_iff_is_ground
  by auto

lemma to_ground_inverse [simp]: 
  assumes "is_ground f"
  shows "from_ground (to_ground f) = f"
  using inj_on_to_ground from_ground_inverse is_ground_iff_range_from_ground assms
  unfolding inj_on_def
  by blast

corollary obtain_grounding: 
  assumes "is_ground f"
  obtains g where "from_ground g = f"
  using to_ground_inverse assms by blast

end

locale base_variable_substitution = variable_substitution 
  where subst = subst
  for subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'expression) \<Rightarrow> 'expression"  (infixl "\<cdot>" 70) +
  assumes
    is_grounding_iff_vars_grounded: 
      "\<And>exp. is_ground (exp \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars exp. is_ground (\<gamma> x))" and
    ground_exists: "\<exists>exp. is_ground exp"
begin 

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
proof-
  obtain g where "is_ground g"
    using ground_exists by blast

  then have "is_ground_subst  (\<lambda>_. g)"
    by (simp add: is_grounding_iff_vars_grounded is_ground_subst_def)

  then show ?thesis
    using that
    by simp
qed

lemma ground_subst_extension:
  assumes "is_ground (exp \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "exp \<cdot> \<gamma> = exp \<cdot> \<gamma>'" and "is_ground_subst \<gamma>'"
proof-
  obtain \<gamma>'' where 
    \<gamma>'': "is_ground_subst \<gamma>''"
    using obtain_ground_subst
    by blast
                    
  define \<gamma>' where 
    \<gamma>':  "\<gamma>' = (\<lambda>var. if var \<in> vars exp then \<gamma> var else \<gamma>'' var)"

  have "is_ground_subst \<gamma>'"
    using assms \<gamma>'' is_grounding_iff_vars_grounded
    unfolding \<gamma>' is_ground_subst_def
    by simp

  moreover have "exp \<cdot> \<gamma> = exp \<cdot> \<gamma>'"
    unfolding \<gamma>'
    using subst_eq by presburger

  ultimately show ?thesis
    using that
    by blast
qed

lemma ground_subst_upd [simp]:
  assumes "is_ground update" "is_ground (exp \<cdot> \<gamma>)" 
  shows "is_ground (exp \<cdot> \<gamma>(var := update))"
  using assms is_grounding_iff_vars_grounded by auto

lemma variable_grounding:
  assumes "is_ground (t \<cdot> \<gamma>)" "x \<in> vars t" 
  shows "is_ground (\<gamma> x)"
  using assms is_grounding_iff_vars_grounded 
  by blast

end

locale based_variable_substitution = 
  base: base_variable_substitution where subst = base_subst and vars = base_vars + 
  variable_substitution
for base_subst base_vars +
assumes
  ground_subst_iff_base_ground_subst [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>" and
  is_grounding_iff_vars_grounded: 
    "\<And>exp. is_ground (exp \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars exp. base.is_ground (\<gamma> x))"
begin

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
  using base.obtain_ground_subst by auto

lemma ground_subst_extension:
  assumes "is_ground (exp \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "exp \<cdot> \<gamma> = exp \<cdot> \<gamma>'" and "is_ground_subst \<gamma>'"
  using obtain_ground_subst assms
  by (metis all_subst_ident_if_ground is_ground_subst_comp_right subst_comp_subst)

lemma ground_subst_extension':
  assumes "is_ground (exp \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "exp \<cdot> \<gamma> = exp \<cdot> \<gamma>'" and "base.is_ground_subst \<gamma>'"
  using ground_subst_extension assms
  by auto

lemma ground_subst_upd [simp]:
  assumes "base.is_ground update" "is_ground (exp \<cdot> \<gamma>)" 
  shows "is_ground (exp \<cdot> \<gamma>(var := update))"
  using base.ground_subst_upd assms is_grounding_iff_vars_grounded by simp  

lemma ground_exists: "\<exists>exp. is_ground exp"
  using base.ground_exists
  by (meson is_grounding_iff_vars_grounded)

lemma variable_grounding:
  assumes "is_ground (t \<cdot> \<gamma>)" "x \<in> vars t" 
  shows "base.is_ground (\<gamma> x)"
  using assms is_grounding_iff_vars_grounded 
  by blast

end
                                             
section \<open>Liftings\<close>

locale variable_substitution_lifting = 
  sub: variable_substitution
  where subst = sub_subst and vars = sub_vars
  for
    sub_vars :: "'sub_expression \<Rightarrow> 'variable set" and
    sub_subst :: "'sub_expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'sub_expression" +
  fixes
    map :: "('sub_expression \<Rightarrow> 'sub_expression) \<Rightarrow> 'expression \<Rightarrow> 'expression" and
    to_set :: "'expression \<Rightarrow> 'sub_expression set"
  assumes
    map_comp: "\<And>d f g. map f (map g d) = map (f \<circ> g) d" and
    map_id: "map id d = d" and
    map_cong: "\<And>d f g. (\<And>c. c \<in> to_set d \<Longrightarrow> f c = g c) \<Longrightarrow> map f d = map g d" and
    to_set_map: "\<And>d f. to_set (map f d) = f ` to_set d" and
    exists_expression: "\<And>c. \<exists>d. c \<in> to_set d" 
begin

definition vars :: "'expression \<Rightarrow> 'variable set" where
  "vars d \<equiv> \<Union> (sub_vars ` to_set d)"

definition subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression" where
  "subst d \<sigma> \<equiv> map (\<lambda>c. sub_subst c \<sigma>) d"

lemma map_id_cong: 
  assumes "\<And>c. c \<in> to_set d \<Longrightarrow> f c = c"  
  shows "map f d = d"
  using map_cong map_id assms
  unfolding id_def
  by metis

lemma to_set_map_not_ident: 
  assumes "c \<in> to_set d" "f c \<notin> to_set d" 
  shows "map f d \<noteq> d"
  using assms
  by (metis rev_image_eqI to_set_map)

lemma subst_in_to_set_subst:
  assumes "c \<in> to_set d" 
  shows "sub_subst c \<sigma> \<in> to_set (subst d \<sigma>)"
  unfolding subst_def
  using assms to_set_map by auto

sublocale variable_substitution where subst = subst and vars = vars
proof unfold_locales
  show "\<And>x a b. subst x (comp_subst a b) = subst (subst x a) b"
    using sub.subst_comp_subst
    unfolding subst_def map_comp comp_apply
    by presburger
next
  show "\<And>x. subst x id_subst = x"
    using map_id
    unfolding subst_def sub.subst_id_subst id_def.
next
   show "\<And>x. vars x = {} \<Longrightarrow> \<forall>\<sigma>. subst x \<sigma> = x"
     unfolding vars_def subst_def    
     using map_id_cong 
     by simp
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> subst a \<sigma> = subst a \<tau> "
    unfolding vars_def subst_def
    using map_cong sub.subst_eq
    by (meson UN_I)
qed

lemma ground_subst_iff_sub_ground_subst [simp]: 
  "is_ground_subst \<gamma> \<longleftrightarrow> sub.is_ground_subst \<gamma>"
proof(unfold is_ground_subst_def sub.is_ground_subst_def, intro iffI allI)
  fix c 
  assume all_d_ground: "\<forall>d. is_ground (subst d \<gamma>)"
  show "sub.is_ground (sub_subst c \<gamma>)"
  proof(rule ccontr)
    assume c_not_ground: "\<not>sub.is_ground (sub_subst c \<gamma>)"

    then obtain d where "c \<in> to_set d"
      using exists_expression by auto

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
  assume all_c_ground: "\<forall>c. sub.is_ground (sub_subst c \<gamma>)"

  then show "is_ground (subst d \<gamma>)"
    unfolding vars_def subst_def
    using to_set_map
    by simp
qed

lemma to_set_is_ground [intro]:
  assumes "sub \<in> to_set expr" "is_ground expr"
  shows "sub.is_ground sub"
  using assms
  by (simp add: vars_def)

lemma to_set_is_ground_subst:
  assumes "sub \<in> to_set expr"  "is_ground (subst expr \<gamma>)"  
  shows "sub.is_ground (sub_subst sub \<gamma>)"
  using assms
  by (meson subst_in_to_set_subst to_set_is_ground)

lemma subst_empty:
  assumes "to_set expr' = {}"
  shows "subst expr \<sigma> = expr' \<longleftrightarrow> expr = expr'"
  using assms map_id_cong subst_def to_set_map 
  by fastforce

lemma empty_is_ground:
  assumes "to_set expr = {}"  
  shows "is_ground expr"
  using assms
  by (simp add: vars_def)

end

locale based_variable_substitution_lifting = 
  variable_substitution_lifting +
  base: base_variable_substitution where subst = base_subst and vars = base_vars
for base_subst base_vars +
assumes 
  sub_is_grounding_iff_vars_grounded: 
    "\<And>exp \<gamma>. sub.is_ground (sub_subst exp \<gamma>) \<longleftrightarrow> (\<forall>x \<in> sub_vars exp. base.is_ground (\<gamma> x))" and
  sub_ground_subst_iff_base_ground_subst: "\<And>\<gamma>. sub.is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
begin

lemma is_grounding_iff_vars_grounded: 
  "is_ground (subst exp \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars exp. base.is_ground (\<gamma> x))"
  using sub_is_grounding_iff_vars_grounded subst_def to_set_map vars_def
  by auto

lemma ground_subst_iff_base_ground_subst [simp]: 
  "\<And>\<gamma>. is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  using sub_ground_subst_iff_base_ground_subst ground_subst_iff_sub_ground_subst by blast

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
  using base.obtain_ground_subst
  by (meson base.ground_exists is_grounding_iff_vars_grounded is_ground_subst_def that)

lemma ground_subst_extension:
  assumes "is_ground (subst exp \<gamma>)"
  obtains \<gamma>'
  where "subst exp \<gamma> = subst exp \<gamma>'" and "is_ground_subst \<gamma>'"
  by (metis all_subst_ident_if_ground assms comp_subst.left.monoid_action_compatibility 
        is_ground_subst_comp_right obtain_ground_subst)

lemma ground_subst_extension':
  assumes "is_ground (subst exp \<gamma>)"
  obtains \<gamma>'
  where "subst exp \<gamma> = subst exp \<gamma>'" and "base.is_ground_subst \<gamma>'"
  by (metis all_subst_ident_if_ground assms base.is_ground_subst_comp_right 
        base.obtain_ground_subst subst_comp_subst)
 
lemma ground_subst_upd [simp]:
  assumes "base.is_ground update" "is_ground (subst exp \<gamma>)" 
  shows "is_ground (subst exp  (\<gamma>(var := update)))"
  using assms(1) assms(2) is_grounding_iff_vars_grounded by auto

lemma ground_exists: "\<exists>exp. is_ground exp"
  using base.ground_exists
  by (meson is_grounding_iff_vars_grounded)

lemma variable_grounding:
  assumes "is_ground (subst t \<gamma>)" "x \<in> vars t" 
  shows "base.is_ground (\<gamma> x)"
  using assms is_grounding_iff_vars_grounded 
  by blast

end

locale finite_variables_lifting = 
  variable_substitution_lifting + 
  sub: finite_variables where vars = sub_vars +
  to_set: finite_set where set = to_set
begin

abbreviation to_fset :: "'d \<Rightarrow> 'c fset" where 
  "to_fset \<equiv> to_set.finite_set"

lemmas finite_to_set = to_set.finite_set to_set.finite_set'
lemmas fset_to_fset = to_set.fset_finite_set

sublocale finite_variables where vars = vars
  by unfold_locales (simp add: vars_def)

end

locale grounding_lifting = 
  variable_substitution_lifting where sub_vars = sub_vars and sub_subst = sub_subst and map = map + 
  sub: grounding where vars = sub_vars and subst = sub_subst and to_ground = sub_to_ground and 
  from_ground = sub_from_ground 
for
  sub_to_ground :: "'sub \<Rightarrow> 'ground_sub" and 
  sub_from_ground :: "'ground_sub \<Rightarrow> 'sub" and
  sub_vars :: "'sub \<Rightarrow> 'variable set" and 
  sub_subst :: "'sub \<Rightarrow> ('variable \<Rightarrow> 'base) \<Rightarrow> 'sub" and
  map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" +
fixes
  to_ground_map :: "('sub \<Rightarrow> 'ground_sub) \<Rightarrow> 'expr \<Rightarrow> 'ground_expr" and
  from_ground_map :: "('ground_sub \<Rightarrow> 'sub) \<Rightarrow> 'ground_expr \<Rightarrow> 'expr" and
  ground_map :: "('ground_sub \<Rightarrow> 'ground_sub) \<Rightarrow> 'ground_expr \<Rightarrow> 'ground_expr" and
  to_set_ground :: "'ground_expr \<Rightarrow> 'ground_sub set"
assumes
  to_set_from_ground_map: "\<And>d f. to_set (from_ground_map f d) = f ` to_set_ground d" and
  map_comp': "\<And>d f g. from_ground_map f (to_ground_map g d) = map (f \<circ> g) d" and
  ground_map_comp: "\<And>d f g. to_ground_map f (from_ground_map g d) = ground_map (f \<circ> g) d" and
  ground_map_id: "ground_map id g = g"
begin

definition to_ground where "to_ground expr \<equiv> to_ground_map sub_to_ground expr"

definition from_ground where "from_ground expr \<equiv> from_ground_map sub_from_ground expr"

sublocale grounding where 
  vars = vars and subst = subst and to_ground = to_ground and from_ground = from_ground
proof unfold_locales
  have "\<And>expr. vars expr = {} \<Longrightarrow> expr \<in> range from_ground"
  proof-
    fix expr
    assume "vars expr = {}"
    then have "\<forall>sub\<in>to_set expr. sub \<in> range sub_from_ground"
      by (simp add: sub.is_ground_iff_range_from_ground vars_def)

    then have "\<forall>sub\<in>to_set expr. \<exists>sub_ground. sub_from_ground sub_ground = sub"
      by fast

    then have "\<exists>ground_expr. from_ground ground_expr = expr"
      using map_comp'[symmetric] map_id_cong
      unfolding from_ground_def comp_def
      by metis

    then show "expr \<in> range from_ground"
      unfolding from_ground_def
      by blast
  qed

  moreover have "\<And>expr x. x \<in> vars (from_ground expr) \<Longrightarrow> False"
  proof-
    fix expr x
    assume "x \<in> vars (from_ground expr)"
    then show False
      unfolding vars_def from_ground_def
      using sub.ground_is_ground to_set_from_ground_map by auto
  qed

  ultimately show "{f. vars f = {}} = range from_ground"
    by blast   
next
  show "\<And>g. to_ground (from_ground g) = g"
    using ground_map_id
    unfolding to_ground_def from_ground_def ground_map_comp sub.to_ground_from_ground_id.
qed

lemma to_set_from_ground: "to_set (from_ground expr) = sub_from_ground ` (to_set_ground expr)"
  unfolding from_ground_def
  by (simp add: to_set_from_ground_map)

lemma sub_in_ground_is_ground: 
  assumes "sub \<in> to_set (from_ground expr)" 
  shows "sub.is_ground sub"
  using assms
  by (simp add: to_set_is_ground)

lemma ground_sub_in_ground: 
  "sub \<in> to_set_ground expr \<longleftrightarrow> sub_from_ground sub \<in> to_set (from_ground expr)"
  by (simp add: inj_image_mem_iff sub.inj_from_ground to_set_from_ground)

lemma ground_sub: 
  "(\<forall>sub \<in> to_set (from_ground expr\<^sub>G). P sub) \<longleftrightarrow> 
   (\<forall>sub\<^sub>G \<in> to_set_ground expr\<^sub>G. P (sub_from_ground sub\<^sub>G))"
  by (simp add: to_set_from_ground)

end

locale all_subst_ident_iff_ground_lifting = 
  finite_variables_lifting +  
  sub: all_subst_ident_iff_ground where subst = sub_subst and is_ground = sub.is_ground
begin

sublocale all_subst_ident_iff_ground 
  where subst = subst and is_ground = is_ground
proof unfold_locales
  show "\<And>x. is_ground x = (\<forall>\<sigma>. subst x \<sigma> = x)"
  proof(rule iffI allI)
    show "\<And>x. is_ground x \<Longrightarrow> \<forall>\<sigma>. subst x \<sigma> = x"
      by simp
  next
    fix d x
    assume all_subst_ident: "\<forall>\<sigma>. subst d \<sigma> = d"
    
    show "is_ground d"
    proof(rule ccontr)
      assume "\<not>is_ground d"

      then obtain c where c_in_d: "c \<in> to_set d" and c_not_ground: "\<not>sub.is_ground c"
        unfolding vars_def
        by blast

      then obtain \<sigma> where "sub_subst c \<sigma> \<noteq> c" and "sub_subst c \<sigma> \<notin> to_set d"
        using sub.exists_non_ident_subst finite_to_set
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

  obtain c where c_in_d: "c \<in> to_set d" and c_not_ground: "\<not>sub.is_ground c"
    using d_not_ground
    unfolding vars_def
    by blast

  obtain \<sigma> where \<sigma>_not_ident: "sub_subst c \<sigma> \<noteq> c" "sub_subst c \<sigma> \<notin> \<Union> (to_set ` insert d ds)"
    using sub.exists_non_ident_subst[OF finite_cs c_not_ground]
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

end
