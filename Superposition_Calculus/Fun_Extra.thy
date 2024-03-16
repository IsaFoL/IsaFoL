theory Fun_Extra
  imports Main
begin

(* TODO: *)
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

end
