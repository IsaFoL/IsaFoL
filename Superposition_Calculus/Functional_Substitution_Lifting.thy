theory Functional_Substitution_Lifting
  imports Functional_Substitution Natural_Functor
begin

locale functional_substitution_lifting = 
  sub: functional_substitution where subst = sub_subst and vars = sub_vars +
  natural_functor where map = map and to_set = to_set
  for
    sub_vars :: "'sub \<Rightarrow> 'var set" and
    sub_subst :: "'sub \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'sub" and
    map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" and
    to_set :: "'expr \<Rightarrow> 'sub set"
begin

definition vars :: "'expr \<Rightarrow> 'var set" where
  "vars expr \<equiv> \<Union> (sub_vars ` to_set expr)"

notation sub_subst (infixl "\<cdot>\<^sub>s" 70)

definition subst :: "'expr \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'expr" (infixl "\<cdot>" 70) where
  "expr \<cdot> \<sigma> \<equiv> map (\<lambda>sub. sub \<cdot>\<^sub>s \<sigma>) expr"

lemma map_id_cong: 
  assumes "\<And>sub. sub \<in> to_set expr \<Longrightarrow> f sub = sub"  
  shows "map f expr = expr"
  using map_cong map_id assms
  unfolding id_def
  by metis

lemma to_set_map_not_ident: 
  assumes "sub \<in> to_set expr" "f sub \<notin> to_set expr" 
  shows "map f expr \<noteq> expr"
  using assms
  by (metis rev_image_eqI to_set_map)

lemma subst_in_to_set_subst:
  assumes "sub \<in> to_set expr" 
  shows "sub \<cdot>\<^sub>s \<sigma> \<in> to_set (expr \<cdot> \<sigma>)"
  unfolding subst_def to_set_map
  using assms
  by simp

sublocale functional_substitution where subst = "(\<cdot>)" and vars = vars
proof unfold_locales
  fix expr \<sigma>\<^sub>1 \<sigma>\<^sub>2

  show "expr \<cdot> (\<sigma>\<^sub>1 \<odot> \<sigma>\<^sub>2) = expr \<cdot> \<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2"
    unfolding subst_def map_comp[symmetric] comp_apply sub.subst_comp_subst
    ..
next
  fix expr
  show "expr \<cdot> id_subst = expr"
    using map_id
    unfolding subst_def sub.subst_id_subst id_def.
next
  fix expr
  assume "vars expr = {}"
  then show "\<forall>\<sigma>. expr \<cdot> \<sigma> = expr"
    unfolding vars_def subst_def    
    using map_id_cong
    by simp
next
  fix expr and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'var \<Rightarrow> 'base"
  assume "\<And>var. var \<in> vars expr \<Longrightarrow> \<sigma>\<^sub>1 var = \<sigma>\<^sub>2 var"

  then show "expr \<cdot> \<sigma>\<^sub>1 = expr \<cdot> \<sigma>\<^sub>2"
    unfolding vars_def subst_def
    using map_cong sub.subst_eq
    by (meson UN_I)
qed

lemma ground_subst_iff_sub_ground_subst [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> sub.is_ground_subst \<gamma>"
proof(unfold is_ground_subst_def sub.is_ground_subst_def, intro iffI allI)
  fix sub 
  assume all_ground: "\<forall>expr. is_ground (expr \<cdot> \<gamma>)"
  show "sub.is_ground (sub \<cdot>\<^sub>s \<gamma>)"
  proof(rule ccontr)
    assume sub_not_ground: "\<not>sub.is_ground (sub \<cdot>\<^sub>s \<gamma>)"

    then obtain expr where "sub \<in> to_set expr"
      using exists_functor by blast

    then have "\<not>is_ground (expr \<cdot> \<gamma>)"
      using sub_not_ground to_set_map 
      unfolding subst_def vars_def
      by auto

    then show False
      using all_ground
      by blast
  qed
next
  fix expr
  assume "\<forall>sub. sub.is_ground (sub \<cdot>\<^sub>s \<gamma>)"

  then show "is_ground (expr \<cdot> \<gamma>)"
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
  assumes "sub \<in> to_set expr"  "is_ground (expr \<cdot> \<gamma>)"  
  shows "sub.is_ground (sub \<cdot>\<^sub>s \<gamma>)"
  using assms
  by (meson subst_in_to_set_subst to_set_is_ground)

lemma subst_empty:
  assumes "to_set expr' = {}"
  shows "expr \<cdot> \<sigma> = expr' \<longleftrightarrow> expr = expr'"
  using assms map_id_cong subst_def to_set_map 
  by fastforce

lemma empty_is_ground:
  assumes "to_set expr = {}"  
  shows "is_ground expr"
  using assms
  by (simp add: vars_def)

lemma to_set_image: "to_set (expr \<cdot> \<sigma>) = (\<lambda>a. a \<cdot>\<^sub>s \<sigma>) ` to_set expr"
  unfolding subst_def to_set_map..

end

locale based_functional_substitution_lifting = 
  base: base_functional_substitution where subst = base_subst and vars = base_vars +
  functional_substitution_lifting where to_set = to_set
  for base_subst :: "'base \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'base" and base_vars 
    and to_set :: "'expr \<Rightarrow> 'sub set" +
  assumes 
    sub_is_grounding_iff_vars_grounded: 
      "\<And>expr \<gamma>. sub.is_ground (expr \<cdot>\<^sub>s \<gamma>) \<longleftrightarrow> (\<forall>var \<in> sub_vars expr. base.is_ground (\<gamma> var))" and
    sub_ground_subst_iff_base_ground_subst: "\<And>\<gamma>. sub.is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>"
begin

sublocale based_functional_substitution where subst = subst and vars = vars
proof unfold_locales
  show "\<And>\<gamma>. is_ground_subst \<gamma> = base.is_ground_subst \<gamma>"
    using sub_ground_subst_iff_base_ground_subst ground_subst_iff_sub_ground_subst by blast
next
  show "\<And>\<gamma> expr. (vars (expr \<cdot> \<gamma>) = {}) = (\<forall>var\<in>vars expr. base.is_ground (\<gamma> var)) "
    using sub_is_grounding_iff_vars_grounded subst_def to_set_map vars_def
    by auto
qed

end

locale finite_variables_lifting = 
  sub: finite_variables where vars = "sub_vars :: 'sub \<Rightarrow> 'var set"  +
  to_set: finite_set where set = "to_set :: 'expr \<Rightarrow> 'sub set" +
  functional_substitution_lifting
begin

abbreviation to_fset :: "'expr \<Rightarrow> 'sub fset" where 
  "to_fset \<equiv> to_set.finite_set"

lemmas finite_to_set = to_set.finite_set to_set.finite_set'
lemmas fset_to_fset = to_set.fset_finite_set

sublocale finite_variables where vars = vars
  by unfold_locales (simp add: vars_def)

lemma to_fset_map: "\<And>expr f. to_fset (map f expr) = f |`| to_fset expr"
  using to_set_map
  by (metis fset.set_map fset_inverse fset_to_fset)

lemma to_fset_is_ground_subst:
  assumes "sub |\<in>| to_fset expr"  "is_ground (subst expr \<gamma>)"  
  shows "sub.is_ground (sub \<cdot>\<^sub>s \<gamma>)"
  using assms
  by (simp add: to_set_is_ground_subst)

end

locale renaming_variables_lifting = 
  functional_substitution_lifting +
  sub: renaming_variables where vars = sub_vars and subst = sub_subst and 
  is_renaming = sub.is_renaming
begin

sublocale renaming_variables where subst = subst and vars = vars and is_renaming = is_renaming
proof unfold_locales
  fix expr \<rho>    
  assume "is_renaming \<rho>"

  then show "id_subst ` vars (expr \<cdot> \<rho>) = \<rho> ` vars expr"
    using sub.renaming_variables
    unfolding vars_def subst_def to_set_map
    by fastforce
qed

end      

locale variables_in_base_imgu_lifting = 
  based_functional_substitution_lifting +
  sub: variables_in_base_imgu where vars = sub_vars and subst = sub_subst and 
  base_is_imgu = base.is_imgu
begin

sublocale variables_in_base_imgu where subst = subst and vars = vars and base_is_imgu = base.is_imgu
proof unfold_locales
  fix expr \<mu> unifications
  assume imgu: 
    "base.is_imgu \<mu> unifications" 
    "finite unifications" 
    "\<forall>unification \<in> unifications. finite unification" 

  show "vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> \<Union> (base_vars ` \<Union> unifications)"
    using sub.variables_in_base_imgu[OF imgu]
    unfolding vars_def subst_def to_set_map
    by auto    
qed

end

locale grounding_lifting = 
  functional_substitution_lifting where sub_vars = sub_vars and sub_subst = sub_subst and 
  map = map + 
  sub: grounding where vars = sub_vars and subst = sub_subst and to_ground = sub_to_ground and 
  from_ground = sub_from_ground +
  natural_functor_conversion where map = map and map_to = to_ground_map and 
  map_from = from_ground_map and map' = ground_map and to_set' = to_set_ground
  for
    sub_to_ground :: "'sub \<Rightarrow> 'sub\<^sub>G" and 
    sub_from_ground :: "'sub\<^sub>G \<Rightarrow> 'sub" and
    sub_vars :: "'sub \<Rightarrow> 'var set" and 
    sub_subst :: "'sub \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'sub" and
    map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" and
    to_ground_map :: "('sub \<Rightarrow> 'sub\<^sub>G) \<Rightarrow> 'expr \<Rightarrow> 'expr\<^sub>G" and
    from_ground_map :: "('sub\<^sub>G \<Rightarrow> 'sub) \<Rightarrow> 'expr\<^sub>G \<Rightarrow> 'expr" and
    ground_map :: "('sub\<^sub>G \<Rightarrow> 'sub\<^sub>G) \<Rightarrow> 'expr\<^sub>G \<Rightarrow> 'expr\<^sub>G" and
    to_set_ground :: "'expr\<^sub>G \<Rightarrow> 'sub\<^sub>G set"
begin

definition to_ground :: "'expr \<Rightarrow> 'expr\<^sub>G" where 
  "to_ground expr \<equiv> to_ground_map sub_to_ground expr"

definition from_ground :: "'expr\<^sub>G \<Rightarrow> 'expr" where 
  "from_ground expr\<^sub>G \<equiv> from_ground_map sub_from_ground expr\<^sub>G"

sublocale grounding 
  where vars = vars and subst = subst and to_ground = to_ground and from_ground = from_ground
proof unfold_locales
  have "\<And>expr. is_ground expr \<Longrightarrow> expr \<in> range from_ground"
  proof-
    fix expr

    assume "is_ground expr"

    then have "\<forall>sub\<in>to_set expr. sub \<in> range sub_from_ground"
      by (simp add: sub.is_ground_iff_range_from_ground vars_def)

    then have "\<forall>sub\<in>to_set expr. \<exists>sub\<^sub>G. sub_from_ground sub\<^sub>G = sub"
      by fast

    then have "\<exists>expr\<^sub>G. from_ground expr\<^sub>G = expr"
      using conversion_map_comp[symmetric] map_id_cong
      unfolding from_ground_def comp_def
      by metis

    then show "expr \<in> range from_ground"
      unfolding from_ground_def
      by blast
  qed

  moreover have "\<And>expr var. var \<notin> vars (from_ground expr)"
  proof
    fix expr var

    assume "var \<in> vars (from_ground expr)"

    then show False
      unfolding vars_def from_ground_def
      using sub.ground_is_ground to_set_map_from by auto
  qed

  ultimately show "{expr. is_ground expr} = range from_ground"
    by blast   
next
  show "\<And>expr\<^sub>G. to_ground (from_ground expr\<^sub>G) = expr\<^sub>G"
    using map'_id
    unfolding from_ground_def to_ground_def 
    by (metis map'_comp sub.to_ground_from_ground_id)
qed

lemma to_set_from_ground: "to_set (from_ground expr) = sub_from_ground ` (to_set_ground expr)"
  unfolding from_ground_def
  by (simp add: to_set_map_from)

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
  finite_variables_lifting where map = map and id_subst = id_subst +  
  sub: all_subst_ident_iff_ground where subst = sub_subst and is_ground = sub.is_ground
for 
  map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" and id_subst :: "'var \<Rightarrow> 'base"
begin

sublocale all_subst_ident_iff_ground where subst = subst and is_ground = is_ground
proof unfold_locales
  fix expr 

  show "is_ground expr \<longleftrightarrow> (\<forall>\<sigma>. expr \<cdot> \<sigma> = expr)"
  proof(rule iffI allI)
    assume "is_ground expr"
    then show "\<forall>\<sigma>. expr \<cdot> \<sigma> = expr"
      by simp
  next
    assume all_subst_ident: "\<forall>\<sigma>. expr \<cdot> \<sigma> = expr"
    
    show "is_ground expr"
    proof(rule ccontr)
      assume "\<not>is_ground expr"

      then obtain sub where sub: "sub \<in> to_set expr" "\<not>sub.is_ground sub"
        unfolding vars_def
        by blast

      then obtain \<sigma> where "sub \<cdot>\<^sub>s \<sigma> \<noteq> sub" and "sub \<cdot>\<^sub>s \<sigma> \<notin> to_set expr"
        using sub.exists_non_ident_subst finite_to_set
        by blast
        
      then show False
        using sub subst_in_to_set_subst all_subst_ident
        by metis
    qed
  qed
next
  fix expr :: 'expr and S :: "'expr set"

  assume finite: "finite S" and not_ground: "\<not>is_ground expr"

  then have finite_subs: "finite (\<Union>(to_set ` insert expr S))"
    using finite_to_set by blast

  obtain sub where sub: "sub \<in> to_set expr" and sub_not_ground: "\<not>sub.is_ground sub"
    using not_ground
    unfolding vars_def
    by blast

  obtain \<sigma> where \<sigma>_not_ident: "sub \<cdot>\<^sub>s \<sigma> \<noteq> sub" "sub \<cdot>\<^sub>s \<sigma> \<notin> \<Union> (to_set ` insert expr S)"
    using sub.exists_non_ident_subst[OF finite_subs sub_not_ground]
    by blast

  then have "expr \<cdot> \<sigma> \<noteq> expr"
    using sub
    unfolding subst_def
    by (simp add: to_set_map_not_ident)

  moreover have "expr \<cdot> \<sigma> \<notin> S"
    using \<sigma>_not_ident(2) sub to_set_map
    unfolding subst_def
    by auto

  ultimately show "\<exists>\<sigma>. expr \<cdot> \<sigma> \<noteq> expr \<and> expr \<cdot> \<sigma> \<notin> S"
    by blast
qed

end

end
