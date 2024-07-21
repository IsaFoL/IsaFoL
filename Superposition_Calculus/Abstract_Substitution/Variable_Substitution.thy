theory Variable_Substitution
  imports Abstract_Substitution "HOL-Library.FSet" "HOL-Library.Multiset"
begin

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

(*locale set_spec' = 
  fixes contains :: "'x \<Rightarrow> 'set \<Rightarrow> bool" 
begin

abbreviation "\<And>X. is_empty X \<equiv> \<forall>x. \<not> contains x X"

abbreviation "\<And>X. is_finite X \<equiv> \<exists>n f. \<forall>x. contains x X \<longrightarrow> x \<in> f ` {i::nat. i < n}"

abbreviation "\<And>X Y. subseteq X Y \<equiv> \<forall>x. contains x X \<longrightarrow> contains x Y"

abbreviation "\<And>X Y. disjoint X Y \<equiv> 
  (\<forall>x. contains x X \<longrightarrow> \<not> contains x Y) \<and> (\<forall>x. contains x Y \<longrightarrow> \<not> contains x X)"

end*)


interpretation set : set_spec where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}"
proof unfold_locales
  show "\<And>X. finite X = (\<exists>n f. \<forall>x. x \<in> X \<longrightarrow> x \<in> f ` {i :: nat. i < n})"
    by (metis finite_conv_nat_seg_image rev_finite_subset subset_eq)
qed auto

(*interpretation set' : set_spec' where 
  contains = "(\<in>)" 
rewrites 
  "set'.is_empty X \<equiv> Set.is_empty X" and
  "set'.is_finite X = finite X" and
  "set'.subseteq = (\<subseteq>)"and
  "set'.disjoint X Y = (X \<inter> Y = {})"
proof unfold_locales
  show "(\<exists>n f. \<forall>x. x \<in> X \<longrightarrow> x \<in> f ` {i::nat. i < n}) = finite X"
    by (metis finite_conv_nat_seg_image rev_finite_subset subset_eq)
qed(auto simp: Set.is_empty_def)

locale lifted_set_spec' = 
  set_spec' contains + setset: set_spec' containsS
  for contains :: "'x \<Rightarrow> 'set \<Rightarrow> bool" and containsS :: "'set \<Rightarrow> 'setset \<Rightarrow> bool" +
  fixes Union :: "'setset \<Rightarrow> 'set"
  assumes Union: "\<And>x X. contains x (Union X) \<longleftrightarrow> (\<exists>X'. containsS X' X \<and> contains x X')"
begin

lemma is_empty_Union: "is_empty (Union XX) \<longleftrightarrow> (\<forall>X. containsS X XX \<longrightarrow> is_empty X)"
  by (meson Union)

end

interpretation set' : lifted_set_spec' where 
  contains = "(\<in>)" and containsS = "(\<in>)" and Union = "\<Union>"
   apply unfold_locales 
  by auto*)

locale lifted_set_spec = 
  set_spec 
  where contains = contains and is_empty = is_empty and is_finite = is_finite and 
    subset_eq = subset_eq and disjoint = disjoint + 
  setset: set_spec where contains = containsS and is_empty = is_emptyS and is_finite = is_finiteS and 
    subset_eq = subset_eqS and disjoint = disjointS 
  for contains :: "'x \<Rightarrow> 'set \<Rightarrow> bool" and containsS :: "'set \<Rightarrow> 'setset \<Rightarrow> bool" and 
    is_empty is_finite subset_eq disjoint is_emptyS is_finiteS subset_eqS disjointS +
  fixes Union :: "'setset \<Rightarrow> 'set" 
  assumes Union: "\<And>x X. contains x (Union X) \<longleftrightarrow> (\<exists>X'. containsS X' X \<and> contains x X')"
begin

lemma is_empty_Union: "is_empty (Union XX) \<longleftrightarrow> (\<forall>X. containsS X XX \<longrightarrow> is_empty X)"
  by (meson Union is_empty)
  
end 
    

interpretation set : lifted_set_spec where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and subset_eq = "(\<subseteq>)" and
  disjoint = "\<lambda>X Y. X \<inter> Y = {}" and  containsS = "(\<in>)" and is_emptyS = "\<lambda>X. X = {}" and is_finiteS = finite and subset_eqS = "(\<subseteq>)" and
  disjointS = "\<lambda>X Y. X \<inter> Y = {}" and Union = \<Union>
proof unfold_locales
qed auto

interpretation fset : set_spec where 
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}" 
proof unfold_locales
  show "\<And>X. True = (\<exists>n f. \<forall>x. x |\<in>| X \<longrightarrow> x \<in> f ` {i :: nat. i < n})"
    using finite_fset set.is_finite by blast
qed auto

interpretation mset : set_spec where 
  contains = "(\<in>#)" and is_empty = "\<lambda>X. X = {#}" and is_finite = "\<lambda>_. True" and
  subset_eq = "\<lambda>X Y. set_mset X \<subseteq> set_mset Y" and disjoint = "\<lambda>X Y. X \<inter># Y = {#}"
proof unfold_locales
  show "\<And>X. (X = {#}) = (\<forall>x. x \<notin># X)"
    by simp
next
  fix X :: "'a multiset"
  show "True = (\<exists>n f. \<forall>x. x \<in># X \<longrightarrow> x \<in> f ` {i :: nat. i < n})"
    using set.is_finite by blast
next
  show "\<And>X Y. (set_mset X \<subseteq> set_mset Y) = (\<forall>x. x \<in># X \<longrightarrow> x \<in># Y)"
    by blast
next
  show "\<And>X Y. (X \<inter># Y = {#}) = ((\<forall>x. x \<in># X \<longrightarrow> x \<notin># Y) \<and> (\<forall>x. x \<in># Y \<longrightarrow> x \<notin># X))"
    by (meson disjunct_not_in)
qed

locale variable_substitution = 
  set_spec contains +
  basic_substitution _ _ subst "\<lambda>a. is_empty (vars a)" 
for
  subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'base_expression) \<Rightarrow> 'expression" (infixl "\<cdot>" 70) and
  vars :: "'expression \<Rightarrow> 'variables" and
  contains :: "'variable \<Rightarrow> 'variables \<Rightarrow> bool" +
assumes 
  subst_eq: "\<And>a \<sigma> \<tau>. (\<And>x. contains x (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>"
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
  using assms subst_eq subset_eq disjoint by fastforce

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

locale grounding = variable_substitution 
  where vars = vars for vars :: "'a \<Rightarrow> 'vars" +
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
  by (smt (verit, ccfv_threshold) from_ground_inverse grounding.range_from_ground_iff_is_ground grounding_axioms inj_onD inj_on_to_ground mem_Collect_eq rangeI)

end

(* TODO: base_variable_substitution *)
locale variable_substitution_base = variable_substitution 
  where subst = subst and contains = contains
  for subst :: "'expression \<Rightarrow> ('variable \<Rightarrow> 'expression) \<Rightarrow> 'expression"  (infixl "\<cdot>" 70) and 
    contains :: "'variable \<Rightarrow> 'variables \<Rightarrow> bool" +
  assumes 
    is_ground_iff:
      "\<And>exp. is_ground (exp \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x. contains x (vars exp) \<longrightarrow> is_ground (\<gamma> x))" and
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
    \<gamma>':  "\<gamma>' = (\<lambda>var. if contains var (vars exp) then \<gamma> var else \<gamma>'' var)"

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
  "is_ground (expanded_subst exp \<gamma>) \<longleftrightarrow> (\<forall>x. contains x (expanded_vars exp) \<longrightarrow> base.is_ground (\<gamma> x))"
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

locale variable_substitution_set = variable_substitution where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and
  subset_eq = "(\<subseteq>)" and disjoint = "\<lambda>X Y. X \<inter> Y = {}"

locale variable_substitution_base_set = variable_substitution_base where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and
  subset_eq = "(\<subseteq>)" and disjoint = "\<lambda>X Y. X \<inter> Y = {}"

(* TODO: With set spec *)
locale variable_substitution_lifting = 
  lifted: variable_substitution 
  where comp_subst = comp_subst and id_subst = id_subst and subst = base_subst and 
    vars = base_vars + 
  lifted_set_spec where containsS = "(\<in>)"
  for 
    id_subst :: "'variable \<Rightarrow> 'base_expression" and
    base_vars :: "'sub_expression \<Rightarrow> 'variables" and
    containsS :: "'variables \<Rightarrow> 'variables set \<Rightarrow> bool" and
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

definition vars :: "'expression \<Rightarrow> 'variables" where
  "vars d \<equiv> Union (base_vars ` to_set d)"

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

sublocale variable_substitution where
  comp_subst = comp_subst and id_subst = id_subst and subst = subst and vars = vars and contains = contains 
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
   show "\<And>x. is_empty (vars x) \<Longrightarrow> \<forall>\<sigma>. subst x \<sigma> = x"
     unfolding vars_def subst_def is_empty_Union   
     using map_id_cong 
     by simp
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. contains x (vars a) \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> subst a \<sigma> = subst a \<tau> "
    unfolding vars_def subst_def
    using map_cong lifted.subst_eq
    by (meson Union image_eqI)   
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
      using c_not_ground to_set_map Union
      unfolding subst_def vars_def
      using is_empty_Union by auto

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
    using is_empty_Union by auto
qed

lemma is_ground_subst_iff_base_is_ground_subst [simp]: 
  "is_ground_subst \<gamma> \<longleftrightarrow> lifted.is_ground_subst \<gamma>"
  unfolding is_ground_subst_def  lifted.is_ground_subst_def
  using is_ground_iff_base_is_ground
  by presburger

end

locale variable_substitution_lifting_set = variable_substitution_lifting where 
   contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and
  subset_eq = "(\<subseteq>)" and disjoint = "\<lambda>X Y. X \<inter> Y = {}" and containsS = "(\<in>)" and is_emptyS = "\<lambda>X. X = {}" and is_finiteS = finite and
  subset_eqS = "(\<subseteq>)" and disjointS = "\<lambda>X Y. X \<inter> Y = {}" and Union = \<Union>

locale based_variable_substitution_lifting_set = 
  variable_substitution_lifting_set where id_subst = id_subst and base_vars = base_vars and 
  comp_subst = comp_subst and base_subst = base_subst and map = map and to_set = to_set +
  base: variable_substitution_base_set
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

(* TODO: base \<rightarrow> lifted *)
locale all_subst_ident_iff_ground_lifting = 
  finite_variables_lifting +
  lifted: all_subst_ident_iff_ground where is_ground = lifted.is_ground and subst = base_subst 
    and is_finite = finite and contains = "(\<in>)" 
begin

sublocale all_subst_ident_iff_ground 
  where is_finite = finite and contains = "(\<in>)" and is_ground = is_ground and subst = subst 
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
        using lifted.is_empty
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
    using lifted.is_empty
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
  based_variable_substitution_lifting_set + 
  all_subst_ident_iff_ground_lifting 

locale variable_substitution_expansion_set = variable_substitution_expansion where 
  contains = "(\<in>)" and is_empty = "\<lambda>X. X = {}" and is_finite = finite and
  subset_eq = "(\<subseteq>)" and disjoint = "\<lambda>X Y. X \<inter> Y = {}"

(*locale variable_substitution_fset = variable_substitution where
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"

locale variable_substitution_expansion_fset = variable_substitution_expansion where 
  contains = "(|\<in>|)" and is_empty = "\<lambda>X. X = {||}" and is_finite = "\<lambda>_. True" and
  subset_eq = "(|\<subseteq>|)" and disjoint = "\<lambda>X Y. X |\<inter>| Y = {||}"*)

end
