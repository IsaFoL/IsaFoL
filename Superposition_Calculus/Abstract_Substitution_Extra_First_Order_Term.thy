theory Abstract_Substitution_Extra_First_Order_Term
  imports
    Abstract_Substitution_Extra
    "First_Order_Terms.Subsumption"
    "First_Order_Terms.Unification"
begin

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

global_interpretation term_subst: basic_substitution_ops subst_apply_term Var subst_compose
  rewrites "term_subst.is_ground = is_ground_trm"
proof -
  have is_ground_iff:
    "basic_substitution_ops.is_ground (\<cdot>) (t \<cdot> \<gamma>) \<longleftrightarrow>
      (\<forall>x \<in> vars_term t. basic_substitution_ops.is_ground (\<cdot>) (\<gamma> x))"
    for t \<gamma>
    by (induction t) (auto simp add: basic_substitution_ops.is_ground_def)

  thus "basic_substitution_ops.is_ground (\<cdot>) = is_ground_trm"
    by (metis (mono_tags, opaque_lifting) basic_substitution_ops.subst_ident_if_ground ex_in_conv
        subst_apply_term_empty subst_def subst_simps(1) subst_term_eqI term.distinct(1))
qed

lemma is_ground_iff:
  "term_subst.is_ground (t \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars_term t. term_subst.is_ground (\<gamma> x))"
  by (induction t) (auto simp add: term_subst.is_ground_def)

lemma term_subst_is_renaming_iff:
  "term_subst.is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x))"
proof (rule iffI)
  show "term_subst.is_renaming \<rho> \<Longrightarrow> inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x))"
    unfolding term_subst.is_renaming_def
    by (metis injI subst_apply_eq_Var subst_compose_def term.disc(1) term.inject(1))
next
  show "inj \<rho> \<and> (\<forall>x. is_Var (\<rho> x)) \<Longrightarrow> term_subst.is_renaming \<rho>"
    unfolding term_subst.is_renaming_def
    using ex_inverse_of_renaming by metis
qed

global_interpretation term_subst: basic_substitution subst_apply_term Var subst_compose
proof unfold_locales
  show "\<And>x. x \<cdot> Var = x"
    by simp
next
  show "\<And>x \<sigma> \<tau>. x \<cdot> \<sigma> \<circ>\<^sub>s \<tau> = x \<cdot> \<sigma> \<cdot> \<tau>"
    by simp
next
  show "\<And>\<sigma> \<tau>. (\<And>x. x \<cdot> \<sigma> = x \<cdot> \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (simp add: subst_term_eqI)(* 
next
  fix T :: "('f, 'v) term set" and \<sigma> :: "'v \<Rightarrow> ('f, 'v) term"

  define \<gamma> where
    "\<gamma> = (\<lambda>x. if (\<exists>t\<in>T. x \<in> vars_term t) then \<sigma> x else Fun undefined [])"

  assume ground_T: "term_subst.is_ground_set (term_subst.subst_set T \<sigma>)"

  have ground_apply_\<gamma>: "term_subst.is_ground (\<gamma> x)" for x
  proof (cases "\<exists>t\<in>T. x \<in> vars_term t")
    case True
    then obtain t where "t \<in> T" and "x \<in> vars_term t"
      by auto
    moreover have "term_subst.is_ground (t \<cdot> \<sigma>)"
      using ground_T \<open>t \<in> T\<close>
      by (simp add: term_subst.is_ground_set_def term_subst.subst_set_def)
    ultimately show ?thesis
      by (auto simp add: \<gamma>_def is_ground_iff)
  next
    case False
    then show ?thesis
      by (simp add: \<gamma>_def term_subst.is_ground_def)
  qed

  show "\<exists>\<tau>. term_subst.is_ground_subst \<tau> \<and> (\<forall>t \<in> T. t \<cdot> \<tau> = t \<cdot> \<sigma>)"
  proof (intro exI conjI)
    show "term_subst.is_ground_subst \<gamma>"
      unfolding term_subst.is_ground_subst_def
    proof (rule allI)
      fix t show "term_subst.is_ground (t \<cdot> \<gamma>)"
        using ground_apply_\<gamma>
        by (induction t) (simp_all add: term_subst.is_ground_def)
    qed
  next
    show "\<forall>t\<in>T. t \<cdot> \<gamma> = t \<cdot> \<sigma>"
      using \<gamma>_def term_subst_eq_conv by fastforce
  qed *)
qed


lemma inj: assumes "finite (UNIV :: 'a set)" "infinite (UNIV :: 'b set)"
  obtains f where "inj (f :: 'a \<Rightarrow> 'b)"
proof-
  let ?domain = "UNIV :: 'a set"
  let ?image = "UNIV :: 'b set"

  let ?domain_size = "card ?domain"

  obtain image_subset where "image_subset \<subseteq> ?image" and "card image_subset = ?domain_size"
    by (meson assms(2) infinite_arbitrarily_large)

  then obtain f where "bij_betw f ?domain image_subset" 
    apply auto
    by (metis UNIV_I assms(1) card.empty card.infinite card_eq_UNIV_imp_eq_UNIV empty_iff finite_same_card_bij)

  then have "inj f"
    using bij_betw_def by auto

  then show ?thesis
    by (simp add: that)
qed

lemma ground_imgu_equals: 
  assumes "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2" and "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms
  unfolding basic_substitution_ops.is_imgu_def term_subst.is_ground_def term_subst.is_unifiers_def
  by (metis finite.emptyI finite.insertI insertCI term_subst.is_unifier_iff_if_finite)

lemma the_mgu_is_unifier: 
  assumes "term \<cdot> the_mgu term term' = term' \<cdot> the_mgu term term'" 
  shows "term_subst.is_unifier (the_mgu term term') {term, term'}"
  using assms
  unfolding term_subst.is_unifier_def the_mgu_def
  by simp

lemma imgu_exists: 
   fixes  
    \<theta> :: "('f, 'v) subst"
  assumes
    "term \<cdot> \<theta> = term' \<cdot> \<theta>"
  shows
    "\<exists>(\<sigma> :: ('f, 'v) subst) \<tau>.  \<theta> = \<sigma> \<circ>\<^sub>s \<tau> \<and> term_subst.is_imgu \<sigma> {{term, term'}}"
proof(rule exI, rule exI)
  have finite_terms: "finite {term, term'}"
    by simp

  have "term_subst.is_unifiers (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_unifiers_def
    using the_mgu_is_unifier[OF the_mgu[OF assms, THEN conjunct1]] 
    by simp

  moreover have
    "\<And>\<tau>. term_subst.is_unifiers \<tau> {{term, term'}} \<Longrightarrow> \<tau> = the_mgu term term' \<circ>\<^sub>s \<tau>"
    unfolding term_subst.is_unifiers_def
    using 
      term_subst.is_unifier_iff_if_finite[OF finite_terms] 
      the_mgu[of "term" _ term']
    by blast
    
  ultimately have is_imgu: "term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_imgu_def 
    by blast
  
  show "\<theta> = (the_mgu term term') \<circ>\<^sub>s \<theta> \<and> term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    using is_imgu the_mgu[OF assms]
    by blast
qed

lemma bij_betw: assumes "finite domain" "finite img" "card img = card domain" 
  obtains f where "bij_betw f domain img" 
proof-
  show ?thesis
    by (metis assms(1) assms(2) assms(3) bij_betw_iff_card that)
qed

lemma bij_betw': assumes "finite domain" "finite img" "card img = card domain" 
  obtains f where "bij_betw f domain img" "\<And>x. x \<notin> domain \<Longrightarrow> f x = x"
proof-
  obtain f' where bij_f': "bij_betw f' domain img"
    using assms bij_betw
    by blast

  let ?f = "\<lambda>x. if x \<in> domain then f' x else  x"

  have "bij_betw ?f domain img"
    using bij_f'
    unfolding bij_betw_def
    apply auto
    by (simp add: inj_on_def)

  moreover have "\<And>x. x \<notin> domain \<Longrightarrow> ?f x = x"
    by simp

  ultimately show ?thesis
    using that
    by blast
qed

lemma bij_betw'': assumes "finite domain" "finite img" "card img = card domain" "domain \<inter> img = {}"
  obtains f where "bij_betw f domain img" "bij_betw f img domain" "\<And>x. x \<notin> domain \<Longrightarrow> x \<notin> img  \<Longrightarrow> f x = x"
proof-
  obtain f' where bij_f': "bij_betw f' domain img"
    using assms bij_betw
    by blast

  obtain f'' where bij_f'': "bij_betw f'' img domain"
    using assms bij_betw
    by metis

  let ?f = "\<lambda>x. if x \<in> domain then f' x else if x \<in> img then f'' x  else  x"

  have "bij_betw ?f domain img"
    using bij_f' bij_f''
    unfolding bij_betw_def inj_on_def
    by auto

  moreover have "bij_betw ?f img domain"
    using bij_f' bij_f''
    unfolding bij_betw_def 
    apply auto
    apply (smt (verit, del_insts) assms(4) disjoint_iff inj_on_cong)
    using assms(4) apply blast
    by (smt (verit) IntI assms(4) disjoint_iff image_iff mem_Collect_eq)

  moreover have "\<And>x. x \<notin> domain \<Longrightarrow> x \<notin> img  \<Longrightarrow> ?f x = x"
    by simp

  ultimately show ?thesis
    using that
    by blast
qed

lemma inj_on: assumes "finite domain" "infinite (UNIV :: 'b set)"
  obtains f where "inj_on (f :: 'a \<Rightarrow> 'b) domain"
proof- 
  let ?image = "UNIV :: 'b set"
  let ?domain_size = "card domain"

  obtain image_subset where 
    "image_subset \<subseteq> ?image" and 
    "card image_subset = ?domain_size" and
    "finite image_subset"
    by (meson assms(2) infinite_arbitrarily_large)

  then obtain f where "bij_betw f domain image_subset" 
    using bij_betw assms(1)
    by blast

  then have "inj_on f domain"
    using bij_betw_def by auto

  then show ?thesis
    by (simp add: that)
qed

lemma inj_on': assumes "finite domain" "infinite image_subset"
  obtains f where 
    "inj_on (f :: 'a \<Rightarrow> 'b) domain"
    "f ` domain \<subseteq> image_subset"
proof- 
  let ?image = "UNIV :: 'b set"
  let ?domain_size = "card domain"

  have "image_subset \<subseteq> ?image"
    by simp

  obtain image_subset' where 
    "image_subset' \<subseteq> image_subset" and 
    "card image_subset' = ?domain_size" and
    "finite image_subset'"
    by (meson assms(2) infinite_arbitrarily_large)

  then obtain f where bij: "bij_betw f domain image_subset'" 
    using bij_betw assms(1)
    by blast

  then have inj: "inj_on f domain"
    using bij_betw_def by auto

  with bij have "f ` domain \<subseteq> image_subset"
    by (simp add: \<open>image_subset' \<subseteq> image_subset\<close> bij_betw_def)

  with inj show ?thesis 
    using that
    by blast
qed

lemma inj': 
  fixes domain image_subset :: "'a set"
  assumes "finite domain" "infinite image_subset"
  obtains f where 
    "inj (f :: 'a \<Rightarrow> 'a)"
    "f ` domain \<subseteq> image_subset"
proof- 
  let ?image = "UNIV :: 'b set"
  let ?domain_size = "card domain"

  have "image_subset \<subseteq> ?image"
    by simp

  obtain image_subset' where 
    image_subset': "image_subset' \<subseteq> image_subset - domain" 
    "card image_subset' = ?domain_size"
    "finite image_subset'"
    by (meson assms(1) assms(2) finite_Diff2 infinite_arbitrarily_large)

  then have domain_image_subset'_distinct: "domain \<inter> image_subset' = {}"
    by blast

  obtain image_subset'_inv domain_inv where xy:
    "image_subset'_inv = UNIV - image_subset'"
    "domain_inv = UNIV - domain"
    by blast

   then have "infinite image_subset'_inv" "infinite domain_inv"
     using assms(1, 2)
      apply (metis Diff_UNIV Diff_infinite_finite finite.emptyI image_subset'(3))
     by (metis \<open>domain_inv = UNIV - domain\<close> assms(1) assms(2) finite_Diff2 finite_Int inf_top.right_neutral)

  obtain f where 
    f: 
      "bij_betw f domain image_subset'"
      "bij_betw f image_subset' domain"
      "\<And>x. x \<notin> domain \<Longrightarrow> x \<notin> image_subset' \<Longrightarrow> f x = x"
    using bij_betw''[OF assms(1) image_subset'(3) image_subset'(2) domain_image_subset'_distinct]
    by blast

  have domain_univ: "domain_inv \<union> domain = UNIV"
    using xy
    by simp

  have domainx: "domain_inv \<inter> domain = {}"
    using xy
    by blast

  from f have inj_on: "inj_on f domain"
    using bij_betw_def by auto

  have "\<And>x y. f x = f y \<Longrightarrow> x = y"
    by (metis bij_betw_apply bij_betw_inv_into_left disjoint_iff domain_image_subset'_distinct f)

  then have inj: "inj f"
    using inj_def by blast

  from inj_on f(1) have "f ` domain \<subseteq> image_subset"
    by (metis Diff_subset bij_betw_def image_subset'(1) order_trans)

  with inj show ?thesis 
    using that
    by blast
qed

lemma renaming_exists: 
  assumes  
    "infinite (UNIV :: 'v set)"
    "finite (X :: 'v set)"
    "finite Y"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 where
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
proof-
  let ?newVars = "{ var | var . var \<notin> Y }"

  have "infinite ?newVars"
    using assms(1, 3)
    by simp

  obtain renaming where 
    renaming: "inj renaming" "renaming ` X \<subseteq> ?newVars"
    using inj'
    by (metis \<open>infinite {var |var. var \<notin> Y}\<close> assms(2))

  from renaming obtain \<rho>\<^sub>1 where 
    \<rho>\<^sub>1: "(\<rho>\<^sub>1 :: 'v \<Rightarrow> ('a, 'v) term)  = (\<lambda>var. Var (renaming var))"
    by blast

  have "inj \<rho>\<^sub>1" "(\<forall>x. is_Var (\<rho>\<^sub>1 x))"
    unfolding \<rho>\<^sub>1
    using renaming(1)
    by (simp_all add: inj_on_def)
    
  then have "term_subst.is_renaming \<rho>\<^sub>1"
    by (simp add: term_subst_is_renaming_iff)

  moreover have "term_subst.is_renaming Var"
    by simp

  moreover have "\<rho>\<^sub>1 ` X \<inter>  Var ` Y = {}"
    using \<rho>\<^sub>1 renaming(2) by auto

  ultimately show ?thesis  
    using that
    by blast
qed

end