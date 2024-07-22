theory Variable_Substitution
  imports Abstract_Substitution "HOL-Library.FSet" "HOL-Library.Multiset"
begin

locale variable_substitution = 
  basic_substitution _ _ subst "\<lambda>a. vars a = {}" 
for
  subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression" (infixl "\<cdot>" 70) and
  vars :: "'expression \<Rightarrow> 'variable set" +
assumes 
  subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>"
begin

abbreviation is_ground where "is_ground a \<equiv> vars a = {}"

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

(* TODO: *)
(*locale variable_substitution_semigroup = variable_substitution 
  where vars = vars + comm_monoid_add where plus = plus
  for 
    vars :: "'expression \<Rightarrow> 'variables" and 
    plus :: "'expression \<Rightarrow> 'expression \<Rightarrow> 'expression" (infixl "+" 65)
begin

lemma 
  fixes a b :: "'expression"
  shows "(a + b) \<cdot> \<sigma> = (a \<cdot> \<sigma>) + (b \<cdot> \<sigma>)"
  sorry

end*)

locale finite_variables =
  fixes vars :: "'expression \<Rightarrow> 'variable set"
  assumes finite_vars [simp]: "\<And>a. finite (vars a)"

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
    from_ground_inverse: "\<And>g. to_ground (from_ground g) = g"
    (*surj_to_ground: "surj to_ground" and inj_from_ground: "inj from_ground"*)
begin

definition groundings ::"'a \<Rightarrow> 'g set" where
  "groundings a = { to_ground (a \<cdot> \<gamma>) | \<gamma>. is_ground (a \<cdot> \<gamma>) }"

lemma surj_to_ground: "surj to_ground"
  using from_ground_inverse
  by (metis surj_def)

lemma inj_from_ground: "inj_on from_ground domain\<^sub>G"
  by (metis from_ground_inverse inj_on_inverseI)
 
lemma inj_on_to_ground: "inj_on to_ground (from_ground ` domain\<^sub>G)"
  unfolding inj_on_def
  by (simp add: from_ground_inverse)

lemma bij_betw_to_ground: "bij_betw to_ground (from_ground ` domain\<^sub>G) domain\<^sub>G"
  by (smt (verit, best) bij_betwI' from_ground_inverse image_iff)

lemma bij_betw_from_ground: "bij_betw from_ground domain\<^sub>G (from_ground ` domain\<^sub>G)"
  by (simp add: bij_betw_def inj_from_ground)

lemma ground_is_ground: "is_ground (from_ground g)"
  using range_from_ground_iff_is_ground
  by blast

lemma to_ground_inverse: 
  assumes "is_ground f"
  shows "from_ground (to_ground f) = f"
  using assms 
  by (metis (mono_tags, lifting) from_ground_inverse inj_on_eq_iff inj_on_to_ground mem_Collect_eq 
        rangeI range_from_ground_iff_is_ground)

end

(* TODO: base_variable_substitution *)
locale variable_substitution_base = variable_substitution 
  where subst = subst
  for subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'expression) \<Rightarrow> 'expression"  (infixl "\<cdot>" 70) +
  assumes 
    is_ground_iff: "\<And>exp. is_ground (exp \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars exp. is_ground (\<gamma> x))" and
   ground_exists: "\<exists>exp. is_ground exp"
begin 

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
proof-
  obtain g where "is_ground g"
    using ground_exists by blast

  then have "is_ground_subst  (\<lambda>_. g)"
    by (simp add: is_ground_iff is_ground_subst_def)

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
    using assms \<gamma>'' is_ground_iff
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
  using assms is_ground_iff by auto

end
  

(* TODO: based_variable_substitution? *)
locale variable_substitution_expansion = base: variable_substitution_base + 
  variable_substitution where
  subst = expanded_subst and 
  id_subst = "id_subst" and 
  comp_subst = comp_subst and 
  vars = expanded_vars 
for expanded_subst expanded_vars +
assumes
  expanded_vars_vars: 
    "(\<forall>x. is_ground (expanded_subst x \<gamma>)) \<longleftrightarrow> (\<forall>x. base.is_ground (x \<cdot> \<gamma>))" and
  is_ground_iff:
  "is_ground (expanded_subst exp \<gamma>) \<longleftrightarrow> (\<forall>x \<in> expanded_vars exp. base.is_ground (\<gamma> x))"
begin

(* TODO: name *)
lemma is_ground_subst_iff_base_is_ground_subst [simp]: 
  "is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  base.is_ground_subst_def
  using expanded_vars_vars
  by presburger

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
  using base.obtain_ground_subst by auto

lemma ground_subst_extension:
  assumes "is_ground (expanded_subst exp \<gamma>)"
  obtains \<gamma>'
  where "expanded_subst exp \<gamma> = expanded_subst exp \<gamma>'" and "is_ground_subst \<gamma>'"
  by (metis all_subst_ident_if_ground assms is_ground_subst_comp_right obtain_ground_subst 
       subst_comp_subst)

lemma ground_subst_upd [simp]:
  assumes "base.is_ground update" "is_ground (expanded_subst exp \<gamma>)" 
  shows "is_ground (expanded_subst exp (\<gamma>(var := update)))"
  using base.ground_subst_upd assms is_ground_iff by simp  

lemma ground_exists: "\<exists>exp. is_ground exp"
  using base.ground_exists
  by (meson is_ground_iff)

end

(* TODO: Names *)
locale variable_substitution_lifting = 
  lifted: variable_substitution 
  where comp_subst = comp_subst and id_subst = id_subst and subst = base_subst and 
    vars = base_vars
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
    (* TODO: name *)
    Union_range_to_set: "\<And>c. \<exists>d. c \<in> to_set d" and
    to_set_map: "\<And>d f. to_set (map f d) = f ` to_set d" 
begin

definition vars :: "'expression \<Rightarrow> 'variable set" where
  "vars d \<equiv> \<Union> (base_vars ` to_set d)"

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
  using assms
  by (metis rev_image_eqI to_set_map)

lemma subst_in_to_set_subst:
  assumes "c \<in> to_set d" 
  shows "base_subst c \<sigma> \<in> to_set (subst d \<sigma>)"
  unfolding subst_def
  using assms to_set_map by auto


sublocale variable_substitution where
  comp_subst = comp_subst and id_subst = id_subst and subst = subst and vars = vars
proof unfold_locales
  show "\<And>x a b. subst x (comp_subst a b) = subst (subst x a) b"
    using lifted.subst_comp_subst
    unfolding subst_def map_comp comp_apply
    by presburger
next
  show "\<And>x. subst x id_subst = x"
    using map_id
    unfolding subst_def lifted.subst_id_subst id_def.
next
   show "\<And>x. vars x = {} \<Longrightarrow> \<forall>\<sigma>. subst x \<sigma> = x"
     unfolding vars_def subst_def    
     using map_id_cong 
     by simp
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> subst a \<sigma> = subst a \<tau> "
    unfolding vars_def subst_def
    using map_cong lifted.subst_eq
    by (meson UN_I)
qed

(* TODO: name *)
lemma is_ground_iff_base_is_ground: 
  "(\<forall>d. is_ground (subst d \<gamma>)) \<longleftrightarrow> (\<forall>c. lifted.is_ground (base_subst c \<gamma>))"
proof(rule iffI allI; rule allI)
  fix c 
  assume all_d_ground: "\<forall>d. is_ground (subst d \<gamma>)"
  show "lifted.is_ground (base_subst c \<gamma>)"
  proof(rule ccontr)
    assume c_not_ground: "\<not>lifted.is_ground (base_subst c \<gamma>)"

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
  assume all_c_ground: "\<forall>c. lifted.is_ground (base_subst c \<gamma>)"

  then show "is_ground (subst d \<gamma>)"
    unfolding vars_def subst_def
    using to_set_map
    by simp
qed

lemma is_ground_subst_iff_base_is_ground_subst [simp]: 
  "is_ground_subst \<gamma> \<longleftrightarrow> lifted.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  lifted.is_ground_subst_def
  using is_ground_iff_base_is_ground
  by presburger

end

locale based_variable_substitution_lifting = 
  variable_substitution_lifting where id_subst = id_subst and base_vars = base_vars and 
  comp_subst = comp_subst and base_subst = base_subst and map = map and to_set = to_set +
  base: variable_substitution_base
  where comp_subst = comp_subst and id_subst = id_subst and subst = base'_subst and vars = base'_vars
  for id_subst base_vars comp_subst base_subst map to_set base'_subst base'_vars +
(* TODO: find way to not have provide this manually*)
assumes lifted_is_ground_iff:
  "\<And>exp \<gamma>. lifted.is_ground (base_subst exp \<gamma>) \<longleftrightarrow> (\<forall>x. x \<in> (base_vars exp) \<longrightarrow> base.is_ground (\<gamma> x))"
begin

lemma is_ground_iff:
  "is_ground (subst exp \<gamma>) \<longleftrightarrow> (\<forall>x. x \<in> (vars exp) \<longrightarrow> base.is_ground (\<gamma> x))"
  using lifted_is_ground_iff subst_def to_set_map vars_def
  by auto

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "is_ground_subst \<gamma>"
  using base.obtain_ground_subst
  by (meson base.ground_exists is_ground_iff is_ground_subst_def that)

lemma ground_subst_extension:
  assumes "is_ground (subst exp \<gamma>)"
  obtains \<gamma>'
  where "subst exp \<gamma> = subst exp \<gamma>'" and "is_ground_subst \<gamma>'"
  by (metis all_subst_ident_if_ground assms comp_subst.left.monoid_action_compatibility 
        is_ground_subst_comp_right obtain_ground_subst)

lemma ground_subst_upd [simp]:
  assumes "base.is_ground update" "is_ground (subst exp \<gamma>)" 
  shows "is_ground (subst exp  (\<gamma>(var := update)))"
  using assms(1) assms(2) is_ground_iff by auto

lemma ground_exists: "\<exists>exp. is_ground exp"
  using base.ground_exists
  by (meson is_ground_iff)

end

locale finite_variables_lifting = 
  variable_substitution_lifting + 
  lifted: finite_variables where vars = base_vars +
  assumes finite_to_set: "\<And>d. finite (to_set d)"
begin

sublocale finite_variables 
  where vars = vars
proof unfold_locales
  show "\<And>a. finite (vars a)"
    unfolding vars_def
    by (simp add: finite_to_set)
qed

end

(* TODO: base \<rightarrow> lifted *)
locale all_subst_ident_iff_ground_lifting = 
  finite_variables_lifting +  
  lifted: all_subst_ident_iff_ground where subst = base_subst and is_ground = lifted.is_ground
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

      then obtain c where c_in_d: "c \<in> to_set d" and c_not_ground: "\<not>lifted.is_ground c"
        unfolding vars_def
        by blast

      then obtain \<sigma> where "base_subst c \<sigma> \<noteq> c" and "base_subst c \<sigma> \<notin> to_set d"
        using lifted.exists_non_ident_subst finite_to_set
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

  obtain c where c_in_d: "c \<in> to_set d" and c_not_ground: "\<not>lifted.is_ground c"
    using d_not_ground
    unfolding vars_def
    by blast

  obtain \<sigma> where \<sigma>_not_ident: "base_subst c \<sigma> \<noteq> c" "base_subst c \<sigma> \<notin> \<Union> (to_set ` insert d ds)"
    using lifted.exists_non_ident_subst[OF finite_cs c_not_ground]
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

locale mylifting = 
  based_variable_substitution_lifting + 
  all_subst_ident_iff_ground_lifting 

end
