theory Fun_Extra
  imports Main "HOL-Library.Countable_Set" "HOL-Cardinals.Cardinals"
begin

lemma obtain_bij_betw_endo: 
  assumes "finite domain" "finite img" "card img = card domain" 
  obtains f 
  where "bij_betw f domain img" "\<And>x. x \<notin> domain \<Longrightarrow> f x = x" 
proof-
  obtain f' where bij_f': "bij_betw f' domain img"
    using assms(3) bij_betw_iff_card[OF assms(1, 2)]
    by presburger

  let ?f = "\<lambda>x. if x \<in> domain then f' x else  x"

  have "bij_betw ?f domain img"
    using bij_f'
    unfolding bij_betw_def inj_on_def
    by simp

  moreover have "\<And>x. x \<notin> domain \<Longrightarrow> ?f x = x"
    by simp

  ultimately show ?thesis
    using that
    unfolding inj_def
    by blast
qed

lemma obtain_bij_betw_inj_endo: 
  assumes "finite domain" "finite img" "card img = card domain" "domain \<inter> img = {}"
  obtains f 
  where 
    "bij_betw f domain img" 
    "bij_betw f img domain"
    "\<And>x. x \<notin> domain \<Longrightarrow> x \<notin> img  \<Longrightarrow> f x = x" 
    "inj f"
proof-
  obtain f' where bij_f': "bij_betw f' domain img"
    using assms(3) bij_betw_iff_card[OF assms(1, 2)]
    by auto

  obtain f'' where bij_f'': "bij_betw f'' img domain"
    using assms(3) bij_betw_iff_card[OF assms(2, 1)]
    by blast

  let ?f = "\<lambda>x. if x \<in> domain then f' x else if x \<in> img then f'' x  else  x"

  have "bij_betw ?f domain img"
    using bij_f' bij_f''
    unfolding bij_betw_def inj_on_def
    by auto

  moreover have "bij_betw ?f img domain"
    using bij_f' bij_f''
    unfolding bij_betw_def inj_on_def
    by (smt (verit) assms(4) disjoint_iff image_cong)

  moreover have "\<And>x. x \<notin> domain \<Longrightarrow> x \<notin> img  \<Longrightarrow> ?f x = x"
    by simp

  ultimately show ?thesis
    using that
    unfolding inj_def
    by (smt (verit, ccfv_SIG) assms(4) bij_betw_iff_bijections disjoint_iff)
qed

lemma obtain_inj_on: 
  assumes "finite domain" "infinite image_subset"
  obtains f
  where 
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
    by (metis assms(1) bij_betw_iff_card)

  then have inj: "inj_on f domain"
    using bij_betw_def by auto

  with bij have "f ` domain \<subseteq> image_subset"
    by (simp add: \<open>image_subset' \<subseteq> image_subset\<close> bij_betw_def)

  with inj show ?thesis 
    using that
    by blast
qed

corollary obtain_inj_on': 
  assumes "finite domain" "infinite (UNIV :: 'b set)"
  obtains f 
  where "inj_on (f :: 'a \<Rightarrow> 'b) domain"
  using obtain_inj_on[OF assms]
  by auto

corollary obtain_inj: 
  assumes "finite (UNIV :: 'a set)" "infinite (UNIV :: 'b set)"
  obtains f 
  where "inj (f :: 'a \<Rightarrow> 'b)"
  using obtain_inj_on[OF assms]
  by auto

corollary obtain_inj': 
  assumes "finite (UNIV :: 'a set)" "infinite image_subset"
  obtains f 
  where "inj (f :: 'a \<Rightarrow> 'b)" "f ` domain \<subseteq> image_subset"
  using obtain_inj_on[OF assms]
  by (metis image_subset_iff range_subsetD)

lemma obtain_inj_endo: 
  assumes "finite domain" "infinite image_subset"
  obtains f :: "'a \<Rightarrow> 'a"
  where "inj f" "f ` domain \<subseteq> image_subset"
proof- 
  let ?image = "UNIV :: 'b set"
  let ?domain_size = "card domain"

  have "image_subset \<subseteq> ?image"
    by simp

  obtain image_subset' where image_subset': 
    "image_subset' \<subseteq> image_subset - domain" 
    "finite image_subset'"
    "card image_subset' = ?domain_size"
    using finite_Diff2[OF assms(1)] infinite_arbitrarily_large assms(2)
    by metis

  then have domain_image_subset'_distinct: "domain \<inter> image_subset' = {}"
    by blast

  obtain image_subset'_inv domain_inv where xy:
    "image_subset'_inv = UNIV - image_subset'"
    "domain_inv = UNIV - domain"
    by blast

  obtain f where 
      "bij_betw f domain image_subset'"
      "bij_betw f image_subset' domain"
      "inj f"
    using obtain_bij_betw_inj_endo[OF   
        assms(1) image_subset'(2) image_subset'(3) domain_image_subset'_distinct
        ]
    by metis

  moreover then have "f ` domain \<subseteq> image_subset"
    by (metis Diff_subset bij_betw_def image_subset'(1) order_trans)

  ultimately show ?thesis 
    using that
    by blast
qed

abbreviation surj_on where 
  "surj_on domain f \<equiv> (\<forall>y. \<exists>x \<in> domain. y = f x)"

lemma surj_on_alternative: "surj_on domain f \<longleftrightarrow> f ` domain = UNIV"
  by auto

lemma obtain_surj_on_nat:
  assumes "infinite domain"
  obtains f :: "'a \<Rightarrow> nat" where "surj_on domain f"
proof-
  obtain subdomain where
    subdomain: "infinite subdomain" "countable subdomain" "subdomain \<subseteq> domain"
    using infinite_countable_subset'[OF assms]
    by blast

  then obtain f :: "'a \<Rightarrow> nat" where "surj_on subdomain f"
    by (metis to_nat_on_surj)

  then have "surj_on domain f"
    using subdomain(3)
    by (meson subset_iff)

  then show ?thesis
    using that
    by blast
qed

lemma obtain_surj_on:
  assumes "infinite domain"
  obtains f :: "'a \<Rightarrow> 'b :: countable" where "surj_on domain f"
proof-
  obtain f' :: "'a \<Rightarrow> nat" 
    where f': "surj_on domain f'"
    using obtain_surj_on_nat[OF assms]
    by blast

  let ?f  = "(from_nat :: nat \<Rightarrow> 'b) \<circ> f'"

  have f: "\<forall>y. \<exists>x\<in>domain. y = ?f x"
    using f'
    unfolding comp_def
    by (metis from_nat_to_nat)

  show ?thesis
    using that[OF f].
qed

lemma partitions:
  assumes "infinite (UNIV :: 'x set)"
  obtains A B where
    "|A| =o |B|" 
    "|A| =o |UNIV :: 'x set|"
    "A \<inter> B = {}"
    "A \<union> B = (UNIV :: 'x set)"
proof-      
  obtain f :: "'x + 'x \<Rightarrow> 'x" where f: "bij f"
    by (meson Plus_infinite_bij_betw_types assms bij_betw_inv one_type_greater)

  define A :: "'x set" where "A \<equiv> f ` range Inl"
  define B :: "'x set" where "B \<equiv> f ` range Inr"

  have "A \<inter> B = {}"
    unfolding A_def B_def
    by (smt (verit, best) Inl_Inr_False UNIV_I bij_betw_iff_bijections disjoint_iff f imageE)

  moreover have "A \<union> B = UNIV"
    unfolding A_def B_def
    by (metis UNIV_sum bij_is_surj f image_Un)
    
  moreover have Inl: "|Inl ` (UNIV :: 'x set)| =o |UNIV :: 'x set|"
    by (meson bij_betw_imageI card_of_ordIsoI inj_Inl ordIso_symmetric)

  have Inr: "|Inr ` (UNIV :: 'x set)| =o |UNIV :: 'x set|"
    by (meson bij_betw_imageI card_of_ordIsoI inj_Inr ordIso_symmetric)

  have "|A| =o |UNIV :: 'x set|"
    unfolding A_def
    using f
    unfolding bij_betw_def
    by (metis Inl Int_UNIV_left bij_betw_imageI bij_betw_inv card_of_ordIsoI inj_on_Int 
        ordIso_transitive)
   
  moreover have "|B| =o |UNIV :: 'x set|"
    using f
    unfolding B_def bij_betw_def
    by (meson UNIV_I bij_betw_imageI card_of_ordIsoI inj_Inr inj_on_def ordIso_symmetric 
        ordIso_transitive)

  ultimately show ?thesis
    using that
    by (meson ordIso_symmetric ordIso_transitive)
qed


end
