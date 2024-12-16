theory Fun_Extra
  imports Main "HOL-Library.Countable_Set" "HOL-Cardinals.Cardinals" HOL_Extra
begin

lemma 
  infinite_even_nat: "infinite { n :: nat. even n }" and 
  infinite_odd_nat: "infinite { n :: nat. odd n }"
  by (metis Suc_leD dual_order.refl even_Suc infinite_nat_iff_unbounded_le mem_Collect_eq)+

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

lemma obtain_inj: 
  assumes "infinite (UNIV :: 'a set)"
  obtains f :: "'a \<Rightarrow> 'a" where
    "inj f"
    "|range f| =o |UNIV - range f|"
proof-
  obtain X Y :: "'a set" where
    X_Y: 
      "|X| =o |Y|"
      "|X| =o |UNIV :: 'a set|" 
      "X \<inter> Y = {}" 
      "X \<union> Y = UNIV"
    using partitions[OF assms]
    by blast
    
  then obtain f where 
    f: "bij_betw f (UNIV :: 'a set) Y"
    by (meson card_of_ordIso ordIso_symmetric ordIso_transitive)

  have inj_f: "inj f" 
    using f bij_betw_def by blast+

  have Y: "Y = range f" 
    using f
    by (simp add: bij_betw_def)

  have X: "X = UNIV - range f"
    using X_Y
    unfolding Y
    by auto

  show ?thesis
    using X X_Y(1) Y inj_f ordIso_symmetric that by blast
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

lemma obtain_infinite_partition: 
  assumes "infinite (UNIV :: 'a set)"
  obtains X Y :: "'a :: countable set" 
  where
    "X \<inter> Y = {}" "X \<union> Y = UNIV" and
    "infinite X" and
    "infinite Y"
proof-
  obtain g :: "'a \<Rightarrow> nat" where "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] assms by blast

  define g' where "g' \<equiv> inv g"

  then have bij_g': "bij g'"
    by (simp add: \<open>bij g\<close> bij_betw_inv_into)

  define X :: "'a set" where 
    "X \<equiv> g' ` { n. even n }"

  define Y :: "'a set" where 
    "Y \<equiv> g' ` { n. odd n }"

  have "X \<inter> Y = {}"
    using bij_g'
    unfolding X_def Y_def
    by (simp add: bij_image_Collect_eq disjoint_iff)

  moreover have "X \<union> Y = UNIV"
    using bij_g'
    unfolding X_def Y_def
    by(auto simp: bij_image_Collect_eq)

  moreover have "bij_betw g' { n. even n } X" "bij_betw g' { n. odd n } Y"
    unfolding X_def Y_def
    by (metis \<open>bij g\<close> bij_betw_imp_surj_on g'_def inj_on_imp_bij_betw inj_on_inv_into top.extremum)+

  then have "infinite X" "infinite Y"
    using infinite_even_nat infinite_odd_nat bij_betw_finite
    by blast+

  ultimately show ?thesis
    using that
    by blast
qed

lemma obtain_injs:
  assumes "infinite (UNIV :: 'a set)"
  obtains f f' :: "'a :: countable \<Rightarrow> 'a" where
    "inj f" "inj f'" 
    "range f \<inter> range f' = {}"
    "range f \<union> range f' = UNIV"  
proof-
  obtain g :: "'a \<Rightarrow> nat" where "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] assms by blast

  define g' where "g' \<equiv> inv g"

  then have bij_g': "bij g'"
    by (simp add: \<open>bij g\<close> bij_betw_inv_into)

  obtain X Y :: "'a set" where
    X_Y: "X \<inter> Y = {}" "X \<union> Y = UNIV" and
    infinite_X: "infinite X" and
    infinite_Y: "infinite Y"
    using obtain_infinite_partition[OF assms]
    by auto

  have countable_X: "countable X" and countable_Y: "countable Y"
    by blast+

  obtain f where 
    f: "bij_betw f (UNIV :: 'a set) X"
    using countable_infiniteE'[OF countable_X infinite_X]     
    by (meson \<open>bij g\<close> bij_betw_trans)

  obtain f' where 
    f': "bij_betw f' (UNIV :: 'a set) Y"
    using countable_infiniteE'[OF countable_Y infinite_Y]
    by (meson \<open>bij g\<close> bij_betw_trans)

  have "inj f" "inj f'"
    using f f' bij_betw_def by blast+

  moreover have "range f = X" "range f' = Y"
    using f f'
    by (simp_all add: bij_betw_def)

  then have "range f \<inter> range f' = {}" "range f \<union> range f' = UNIV"
    using X_Y
    by simp_all

  ultimately show ?thesis
    using that
    by presburger
qed

(* TODO: names *)
lemma obtain_type_preserving_injs:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'a \<Rightarrow> 'ty"
  assumes 
    "infinite (UNIV :: 'a set)"
    "finite X" 
    "finite Y" 
    "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" 
    "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "'a \<Rightarrow> 'a" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof
  have "\<And>ty. infinite ({x. \<V>\<^sub>2 x = ty} - X)"
    by (simp add: assms(2) assms(5))

  then have infinite: "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    by (simp add: set_diff_eq)

  have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty } - X|"
    using assms(2, 5) card_of_infinite_diff_finite ordIso_symmetric
    by blast

  then have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}|"
    using set_diff_eq[of _ X]
    by auto

  then have exists_g': "\<And>ty. \<exists>g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    using card_of_ordIso someI by blast

  define get_g' where
    "\<And>ty. get_g' ty \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"

  define f' where
    "\<And>x. f' x \<equiv> get_g' (\<V>\<^sub>2 x) x"

  define f :: "'a \<Rightarrow> 'a"where "f = id"

  moreover have "\<And>y. y \<in> Y \<Longrightarrow> \<exists>g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"
    using exists_g'
    by simp

  moreover then have 
    "\<And>y. y \<in> Y \<Longrightarrow>
      (\<And> g'. ((bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X})
         \<Longrightarrow> (g' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X})))"
    using bij_betwE by blast

  ultimately have ys: "\<And>y. y \<in> Y \<Longrightarrow> f' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}" 
    unfolding f'_def get_g'_def
    by (smt (verit, ccfv_threshold) someI)

  then have "\<And>y. y\<in>Y \<Longrightarrow> f' y \<notin> X"
    by simp

  then show "f ` X \<inter> f' ` Y = {}"
    unfolding f_def
    by auto  

  show "\<forall>y\<in>Y. \<V>\<^sub>2 (f' y) = \<V>\<^sub>2 y"
    using ys
    by simp

  show "\<forall>x\<in>X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    unfolding f_def
    by simp

  show "inj f"
    unfolding f_def
    by simp

  have "\<And>x y. f' x = f' y \<Longrightarrow> \<V>\<^sub>2 y = \<V>\<^sub>2 x"
    using f'_def get_g'_def someI_ex[OF exists_g'] bij_betw_iff_bijections mem_Collect_eq
    by (smt (verit))

  then have "\<And>x y. f' x = f' y \<Longrightarrow> x = y"
    using f'_def get_g'_def exists_g' someI bij_betw_iff_bijections mem_Collect_eq some_eq_ex
    by (smt (z3))

  then show "inj f'"
    unfolding inj_def
    by simp  
qed

abbreviation surj_on where 
  "surj_on f domain \<equiv> (\<forall>y. \<exists>x \<in> domain. y = f x)"

lemma surj_on_alternative: "surj_on f domain \<longleftrightarrow> f ` domain = UNIV"
  by auto

lemma obtain_surj_on_nat:
  assumes "infinite domain"
  obtains f :: "'a \<Rightarrow> nat" where "surj_on f domain"
proof-
  obtain subdomain where
    subdomain: "infinite subdomain" "countable subdomain" "subdomain \<subseteq> domain"
    using infinite_countable_subset'[OF assms]
    by blast

  then obtain f :: "'a \<Rightarrow> nat" where "surj_on f subdomain"
    by (metis to_nat_on_surj)

  then have "surj_on f domain"
    using subdomain(3)
    by (meson subset_iff)

  then show ?thesis
    using that
    by blast
qed

lemma obtain_surj_on:
  assumes "infinite domain"
  obtains f :: "'a \<Rightarrow> 'b :: countable" where "surj_on f domain"
proof-
  obtain f' :: "'a \<Rightarrow> nat" 
    where f': "surj_on f' domain"
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

lemma surj_infinite_set: "surj g \<Longrightarrow> infinite {x. f x = ty} \<Longrightarrow> infinite {x. f (g x) = ty}"
  by (smt (verit) UNIV_I finite_imageI image_iff mem_Collect_eq rev_finite_subset subset_eq)

lemma inv_enumerate:
  assumes "infinite N" 
  shows "(\<lambda>x. inv (enumerate N) x) ` N = UNIV"
  by (metis assms enumerate_in_set inj_enumerate inv_f_eq surj_on_alternative)

lemma finite_bij_enumerate_inv_into:
  fixes S :: "'a::wellorder set"
  assumes S: "finite S"
  shows "bij_betw (inv_into {..<card S} (enumerate S)) S {..<card S}"
  using finite_bij_enumerate[OF assms] bij_betw_inv_into
  by blast

lemma infinite_domain: 
  assumes 
    card_UNIV: "|UNIV :: 'b set| \<le>o |UNIV :: 'a set|" and
    infinite_UNIV: "infinite (UNIV :: 'a set)" 
  shows 
    "\<exists>f :: 'a \<Rightarrow> 'b. \<forall>y. infinite {x. f x = y}"
proof-
  obtain g :: "'a \<Rightarrow> 'a \<times> 'a" where bij_g: "bij g"
    using Times_same_infinite_bij_betw_types bij_betw_inv infinite_UNIV 
    by blast

  define f :: "'a \<Rightarrow> 'a" where 
    "\<And>x. f x \<equiv> fst (g x)"

  {
    fix y

    have "{x. fst (g x) = y} = inv g ` {p. fst p = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_g bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq)

    then have "infinite {x. f x = y}"
      unfolding f_def
      using infinite_prods[OF infinite_UNIV]
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)
  }

  moreover obtain f' ::  "'a \<Rightarrow> 'b" where "surj f'"
    using card_UNIV
    by (metis card_of_ordLeq2 empty_not_UNIV)

  ultimately have "\<And>y. infinite {x. f' (f x) = y}"
    by (smt (verit, ccfv_SIG) Collect_mono finite_subset surjD)

  then show ?thesis
    by meson
qed


end
