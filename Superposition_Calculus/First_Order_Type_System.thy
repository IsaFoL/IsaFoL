theory First_Order_Type_System
  imports
    Clause_Typing
    Nonground_Term_Typing
    Typed_Functional_Substitution_Lifting
    Nonground_Clause
    Fun_Extra
begin

(* TODO *)
instance nat :: infinite
  by intro_classes simp

lemma 
  infinite_even_nat: "infinite { n :: nat . even n }" and 
  infinite_odd_nat: "infinite { n :: nat . odd n }"
  by (metis Suc_leD dual_order.refl even_Suc infinite_nat_iff_unbounded_le mem_Collect_eq)+

lemma obtain_infinite_partition: 
  obtains X Y :: "'a :: {countable, infinite} set" 
  where
    "X \<inter> Y = {}" "X \<union> Y = UNIV" and
    "infinite X" and
    "infinite Y"
proof-
  obtain g :: "'a \<Rightarrow> nat" where "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

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

lemma "(\<Union>n'.{ n. g n = n' }) = UNIV"
  by blast

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

lemma obtain_inj_test'_on:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "nat \<Rightarrow> 'ty"
  assumes 
    "finite X" 
    "finite Y" 
    "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" 
    "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "nat \<Rightarrow> nat" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof
  have "\<And>ty. infinite ({x. \<V>\<^sub>2 x = ty} - X)"
    by (simp add: assms(1) assms(4))

  then have infinite: "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    by (simp add: set_diff_eq)

  define f' where
    "\<And>x. f' x \<equiv> enumerate {y. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> y \<notin> X} x"


  have f'_not_in_x: "\<And>x. f' x \<notin> X"
  proof-
    fix x
    show "f' x \<notin> X"
      unfolding f'_def
      using enumerate_in_set[OF infinite]
      by (smt (verit) CollectD Collect_cong)
  qed 
 
   show "inj id"
     by simp

   show "inj f'"
   proof(unfold inj_def; intro allI impI)
     fix x y
     assume "f' x = f' y"

     moreover then have "\<V>\<^sub>2 y = \<V>\<^sub>2 x"
       unfolding f'_def
       by (smt (verit, ccfv_SIG) Collect_mono_iff enumerate_in_set infinite mem_Collect_eq 
           rev_finite_subset)

     ultimately show "x = y"
       unfolding f'_def
       by (smt (verit) Collect_cong infinite inj_enumerate inj_onD iso_tuple_UNIV_I)
   qed

   show "id ` X \<inter> f' ` Y = {}"
     using f'_not_in_x
     by auto

   show "\<forall>x\<in>X. \<V>\<^sub>1 (id x) = \<V>\<^sub>1 x"
     by simp

   show "\<forall>x\<in>Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x" 
     unfolding f'_def
     using enumerate_in_set[OF infinite]
     by (smt (verit) Collect_cong mem_Collect_eq)
qed

lemma obtain_inj''_on':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'a :: infinite \<Rightarrow> 'ty"
  assumes "finite X" "finite Y" "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "'a \<Rightarrow> 'a" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof
  have "\<And>ty. infinite ({x. \<V>\<^sub>2 x = ty} - X)"
    by (simp add: assms(1) assms(4))

  then have infinite: "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    by (simp add: set_diff_eq)

  have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty } - X|"
    using assms(1, 4)
    using card_of_infinite_diff_finite ordIso_symmetric by blast

  then have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}|"
    using set_diff_eq[of _ X]
    by auto

  then have exists_g': "\<And>ty. \<exists>g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    using card_of_ordIso by blast

  define get_g' where
    "\<And>ty. get_g' ty \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"

  define f' where
    "\<And>x. f' x \<equiv> get_g' (\<V>\<^sub>2 x) x"

  have f'_not_in_x: "\<And>x. f' x \<notin> X"
  proof-
    fix y

    define g' where "g' \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"

    have "y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y}"
      by simp

    moreover have "g' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"
    proof-
      have "\<And>g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X} \<Longrightarrow>
          \<V>\<^sub>2 ((SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y) = \<V>\<^sub>2 y"
        "\<And>g'. \<lbrakk>bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X};
           (SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y \<in> X\<rbrakk>
          \<Longrightarrow> False"
        by (smt (verit, ccfv_SIG) bij_betw_apply mem_Collect_eq verit_sko_ex_indirect)+
        
       then show ?thesis
        unfolding g'_def
        using exists_g'[of "\<V>\<^sub>2 y"]
        by auto
    qed

    then have "g' y \<notin> X"
      by simp

    then show "f' y \<notin> X"
      unfolding f'_def get_g'_def g'_def.
  qed

   show "inj id"
     by simp

   show "inj f'"
   proof(unfold inj_def; intro allI impI)
     fix x y
     assume "f' x = f' y"

     moreover then have "\<V>\<^sub>2 y = \<V>\<^sub>2 x"
       unfolding f'_def get_g'_def
       using someI_ex[OF exists_g']
       by (smt (verit, best) f'_def get_g'_def bij_betw_iff_bijections calculation mem_Collect_eq)

      (* TODO *)
     moreover have "\<And>g'. \<lbrakk>(SOME g'. bij_betw g' {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x} {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x \<and> xa \<notin> X}) x =
           (SOME g'. bij_betw g' {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x} {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x \<and> xa \<notin> X}) y;
           \<V>\<^sub>2 y = \<V>\<^sub>2 x; \<And>P x. P x \<Longrightarrow> P (Eps P); 
           bij_betw g' {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x} {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x \<and> xa \<notin> X}\<rbrakk>
          \<Longrightarrow> x = y"
      by (smt (verit, ccfv_threshold) bij_betw_iff_bijections mem_Collect_eq some_eq_ex)

     ultimately show "x = y"
       using exists_g'[of "\<V>\<^sub>2 x"] someI
       unfolding f'_def get_g'_def
       by auto
   qed

   show "id ` X \<inter> f' ` Y = {}"
     using f'_not_in_x
     by auto

   show "\<forall>x\<in>X. \<V>\<^sub>1 (id x) = \<V>\<^sub>1 x"
     by simp

   show "\<forall>y\<in>Y. \<V>\<^sub>2 (f' y) = \<V>\<^sub>2 y" 
   proof(intro ballI)
     fix y
     assume "y \<in> Y"

      define g' where "g' \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"

      have "y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y}"
        by simp

      have "g' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"
      proof-
        (* TODO *)
        have "\<And>g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X} \<Longrightarrow>
          \<V>\<^sub>2 ((SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y) = \<V>\<^sub>2 y"
          "\<And>g'. \<lbrakk>bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X};
           (SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y \<in> X\<rbrakk>
          \<Longrightarrow> False"
          by (smt (verit, ccfv_SIG) bij_betw_apply mem_Collect_eq verit_sko_ex_indirect)+
          
        then show ?thesis
          unfolding g'_def
          using exists_g'[of "\<V>\<^sub>2 y"]
          by auto
      qed

      then show "\<V>\<^sub>2 (f' y) = \<V>\<^sub>2 y"
        unfolding g'_def f'_def get_g'_def
        by blast
   qed
qed


(* TODO: lemma
  fixes \<V>\<^sub>1 \<V>\<^sub>2
  assumes
    inj\<^sub>1: "inj_on f\<^sub>1 \<X>\<^sub>1" and inj\<^sub>2: "inj_on f\<^sub>2 \<X>\<^sub>2" and
    "f\<^sub>1 ` \<X>\<^sub>1 \<inter> f\<^sub>2 ` \<X>\<^sub>2 = {}"
  defines
    "\<rho>\<^sub>1 \<equiv> Var o f\<^sub>1" and
    "\<rho>\<^sub>2 \<equiv> Var o f\<^sub>2" and
    "\<And>x'. \<V> x' \<equiv>
      if \<exists>x \<in> \<X>\<^sub>1. x' = f\<^sub>1 x then \<V>\<^sub>1 (the_inv_into \<X>\<^sub>1 f\<^sub>1 x') else \<V>\<^sub>2 (the_inv_into \<X>\<^sub>2 f\<^sub>2 x')"
  shows
    "\<And>t \<tau>. term.vars t \<subseteq> \<X>\<^sub>1 \<Longrightarrow> welltyped \<F> \<V>\<^sub>1 t \<tau> \<Longrightarrow> welltyped \<F> \<V> (t \<cdot>t \<rho>\<^sub>1) \<tau>" and
    "\<And>t \<tau>. term.vars t \<subseteq> \<X>\<^sub>2 \<Longrightarrow> welltyped \<F> \<V>\<^sub>2 t \<tau> \<Longrightarrow> welltyped \<F> \<V> (t \<cdot>t \<rho>\<^sub>2) \<tau>"
  sorry*)


lemma obtain_inj''_on:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'a :: {countable, infinite} \<Rightarrow> 'ty"
  assumes "finite X" "finite Y" "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "'a \<Rightarrow> 'a" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof-
  obtain a_to_nat :: "'a \<Rightarrow> nat" where bij_a_to_nat: "bij a_to_nat"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  define nat_to_a where "nat_to_a \<equiv> inv a_to_nat"

  have bij_nat_to_a: "bij nat_to_a"
    unfolding nat_to_a_def
    by (simp add: bij_a_to_nat bij_imp_bij_inv)

  define X_nat Y_nat where 
    "X_nat \<equiv> a_to_nat ` X" and 
    "Y_nat \<equiv> a_to_nat ` Y"

  have finite_X_nat: "finite X_nat" and finite_Y_nat: "finite Y_nat"
    unfolding X_nat_def Y_nat_def
    using assms(1,2)
    by blast+

  define \<V>\<^sub>1_nat \<V>\<^sub>2_nat where 
    "\<And>n. \<V>\<^sub>1_nat n \<equiv> \<V>\<^sub>1 (nat_to_a n)" and 
    "\<And>n. \<V>\<^sub>2_nat n \<equiv> \<V>\<^sub>2 (nat_to_a n)"

  have 
    "\<And>ty. {x. \<V>\<^sub>1_nat x = ty} = a_to_nat ` {x. \<V>\<^sub>1 x = ty}" 
    "\<And>ty. {x. \<V>\<^sub>2_nat x = ty} = a_to_nat ` {x. \<V>\<^sub>2 x = ty}"
    unfolding \<V>\<^sub>1_nat_def \<V>\<^sub>2_nat_def
    using bij_a_to_nat bij_image_Collect_eq nat_to_a_def by fastforce+

  then have \<V>_nat_infinite: "\<And>ty. infinite {x. \<V>\<^sub>1_nat x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2_nat x = ty}"
    using assms(3, 4)
    by (metis bij_a_to_nat bij_betw_finite bij_betw_subset subset_UNIV)+

  obtain f_nat f'_nat where
    inj: "inj f_nat" "inj f'_nat"  and
    disjoint: "f_nat ` X_nat \<inter> f'_nat ` Y_nat = {}"  and
    type_preserving: 
      "\<forall>x\<in> X_nat. \<V>\<^sub>1_nat (f_nat x) = \<V>\<^sub>1_nat x" 
      "\<forall>x\<in> Y_nat. \<V>\<^sub>2_nat (f'_nat x) = \<V>\<^sub>2_nat x"
    using obtain_inj_test'_on[OF finite_X_nat finite_Y_nat \<V>_nat_infinite].

  let ?f = "nat_to_a \<circ> f_nat \<circ> a_to_nat"
  let ?f' = "nat_to_a \<circ> f'_nat \<circ> a_to_nat"
  
  have "inj ?f" "inj ?f'"
    using inj
    by (simp_all add: bij_a_to_nat bij_is_inj bij_nat_to_a inj_compose)

  moreover have "?f ` X \<inter> ?f' ` Y = {}"
    using disjoint
    unfolding X_nat_def Y_nat_def
    by (metis bij_is_inj bij_nat_to_a image_Int image_comp image_empty)

  moreover have 
    "\<forall>x\<in> X. \<V>\<^sub>1 (?f x) = \<V>\<^sub>1 x" 
    "\<forall>x\<in> Y. \<V>\<^sub>2 (?f' x) = \<V>\<^sub>2 x"
    using type_preserving
    unfolding X_nat_def Y_nat_def \<V>\<^sub>1_nat_def \<V>\<^sub>2_nat_def
    by (simp_all add: bij_a_to_nat bij_is_inj nat_to_a_def)

  ultimately show ?thesis
    using that
    by presburger    
qed
   

lemma obtain_inj': 
  obtains f :: "'a :: infinite \<Rightarrow> 'a" where
    "inj f"
    "|range f| =o |UNIV - range f|"
proof-
  obtain X Y :: "'a set" where
    X_Y: 
      "|X| =o |Y|"
      "|X| =o |UNIV :: 'a set|" 
      "X \<inter> Y = {}" 
      "X \<union> Y = UNIV"
    using partitions[OF infinite_UNIV]
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

lemma obtain_inj: 
  fixes X
  defines "Y \<equiv> UNIV - X"
  assumes 
    infinite_X: "infinite X" and
    infinite_Y: "infinite Y"
  obtains f :: "'a :: {countable, infinite} \<Rightarrow> 'a" where
    "inj f"
    "range f \<inter> X = {}"
    "range f \<union> X = UNIV"
proof-
  obtain g :: "'a \<Rightarrow> nat" where bij: "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  have X_Y: "X \<inter> Y = {}" "X \<union> Y = UNIV"
    unfolding Y_def 
    by simp_all              

  have countable_X: "countable X" and countable_Y: "countable Y"
    by auto

  obtain f where 
    f: "bij_betw f (UNIV :: 'a set) Y"
    using countable_infiniteE'[OF countable_Y infinite_Y]     
    by (meson bij bij_betw_trans)

  have "inj f" 
    using f bij_betw_def by blast+

  moreover have "range f = Y" 
    using f
    by (simp_all add: bij_betw_def)

  then have "range f \<inter> X = {}" "range f \<union> X = UNIV"
    using X_Y
    by auto

  ultimately show ?thesis
    using that
    by presburger
qed

lemma obtain_injs:
  obtains f f' :: "'a :: {countable, infinite} \<Rightarrow> 'a" where
    "inj f" "inj f'" 
    "range f \<inter> range f' = {}"
    "range f \<union> range f' = UNIV"  
proof-
  obtain g :: "'a \<Rightarrow> nat" where "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  define g' where "g' \<equiv> inv g"

  then have bij_g': "bij g'"
    by (simp add: \<open>bij g\<close> bij_betw_inv_into)

  obtain X Y :: "'a set" where
    X_Y: "X \<inter> Y = {}" "X \<union> Y = UNIV" and
    infinite_X: "infinite X" and
    infinite_Y: "infinite Y"
    using obtain_infinite_partition
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

(* TODO: Name *)
locale nonground_typing_lifting = 
  typed_functional_substitution_lifting where base_typed = base_typed + 

  is_typed: typed_subst_stability_lifting where base_typed = base_typed + 
  is_welltyped: typed_subst_stability_lifting where 
  sub_expr_is_typed = sub_expr_is_welltyped and base_typed = base_welltyped +

  is_typed: replaceable_\<V>_lifting where base_typed = base_typed + 
  is_welltyped: replaceable_\<V>_lifting where 
  sub_expr_is_typed = sub_expr_is_welltyped and base_typed = base_welltyped +

  is_typed: typed_renaming_lifting where base_typed = base_typed + 
  is_welltyped: typed_renaming_lifting where 
  sub_expr_is_typed = sub_expr_is_welltyped and base_typed = base_welltyped
for base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
    sub_expr_is_welltyped 

locale nonground_uniform_typing_lifting = 
  uniform_typed_functional_substitution_lifting where sub_typed = base_typed + 

  is_typed: uniform_typed_subst_stability_lifting where sub_typed = base_typed + 
  is_welltyped: uniform_typed_subst_stability_lifting where sub_typed = base_welltyped +

  is_typed: uniform_replaceable_\<V>_lifting where sub_typed = base_typed + 
  is_welltyped: uniform_replaceable_\<V>_lifting where sub_typed = base_welltyped +

  is_typed: uniform_typed_renaming_lifting where sub_typed = base_typed + 
  is_welltyped: uniform_typed_renaming_lifting where sub_typed = base_welltyped
for base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" 

locale term_based_nonground_typing_lifting =
  nonground_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars 

locale atom_typing_lifting =
  nonground_uniform_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and 
  map = map_uprod and to_set = set_uprod 

locale nonground_typing =
  fixes 
    \<F> :: "('f, 'ty) fun_types" and 
    Variables :: "('v :: infinite) set" (* TODO: Remove infinite *)
begin

sublocale nonground_term_typing
  by unfold_locales

sublocale clause_typing "typed (\<V> :: ('v, 'ty) var_types)" "welltyped \<V>"
  by unfold_locales

sublocale atom: atom_typing_lifting where 
  base_typed = typed and base_welltyped = welltyped 
  by unfold_locales

sublocale literal: term_based_nonground_typing_lifting where 
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = atom.vars and sub_subst = "(\<cdot>a)" and map = map_literal and to_set = set_literal and
  sub_expr_is_typed = atom.is_typed and sub_expr_is_welltyped = atom.is_welltyped 
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where 
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_expr_is_typed = literal.is_typed and sub_expr_is_welltyped = literal.is_welltyped 
  by unfold_locales

(*lemma pred_prod_imp: 
  "(\<And>p. (case p of (a, b) \<Rightarrow> P a b) \<Longrightarrow> (case p of (a, b) \<Rightarrow> P' a b)) \<equiv> 
   (\<And>a b. P a b \<Longrightarrow> P' a b )"
  by auto

lemma pred_prod_imp': 
  "(\<And>p c. (case p of (a, b) \<Rightarrow> P a b) c \<Longrightarrow> (case p of (a, b) \<Rightarrow> P' a b) c) \<equiv> 
   (\<And>a b c. P a b c \<Longrightarrow> P' a b c)"
  by auto

lemma right_unique_prod: "right_unique (\<lambda>(a, b). P a b) \<longleftrightarrow> (\<forall>a. right_unique (P a))"
  by (auto simp add: right_unique_iff)*)


(*definition typed\<^sub>a where
  "typed\<^sub>a \<V> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. typed \<F> \<V> t \<tau>)"

definition atom.is_welltyped  where
  [clause_simp]: "atom.is_welltyped \<F> \<V> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. welltyped \<F> \<V> t \<tau>)"

definition typed\<^sub>l where
  "typed\<^sub>l \<F> \<V> L \<longleftrightarrow> typed\<^sub>a \<F> \<V> (atm_of L)"

definition literal.is_welltyped where
   [clause_simp]: "literal.is_welltyped \<F> \<V> L \<longleftrightarrow> atom.is_welltyped \<F> \<V> (atm_of L)"

definition typed\<^sub>c where
  "typed\<^sub>c \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. typed\<^sub>l \<F> \<V> L)"

definition clause.is_welltyped where
  "clause.is_welltyped \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. literal.is_welltyped \<F> \<V> L)"

definition typed\<^sub>c\<^sub>s where
  "typed\<^sub>c\<^sub>s \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. typed\<^sub>c \<F> \<V> C)"

definition clause.is_welltyped\<^sub>s where
  "clause.is_welltyped\<^sub>s \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. clause.is_welltyped \<F> \<V> C)"

definition typed\<^sub>\<sigma> where
  "typed\<^sub>\<sigma> \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. typed \<F> \<V> (\<sigma> x) (\<V> x))"

definition is_welltyped where
  "is_welltyped \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. welltyped \<F> \<V> (\<sigma> x) (\<V> x))"*)

(*lemma is_welltyped_Var[simp]: "is_welltyped \<V> Var"
  by(rule is_welltyped_id_subst)*)
 

(* TODO: Monoid 
lemma typed\<^sub>c_add_mset [clause_simp]: 
  "clause.is_typed \<V> (add_mset L C) \<longleftrightarrow> literal.is_typed \<V> L \<and> clause.is_typed \<V> C"
  by(rule clause.is_typed_add)

lemma clause.is_welltyped_add_mset [clause_simp]: 
  "clause.is_welltyped \<V> (add_mset L C) \<longleftrightarrow> 
    literal.is_welltyped \<V> L \<and> clause.is_welltyped \<V> C"
    by(rule clause.is_welltyped_add)

lemma typed\<^sub>c_plus [clause_simp]: 
  "clause.is_typed \<V> (C + D) \<longleftrightarrow> clause.is_typed \<V> C \<and> clause.is_typed \<V> D"
  by(rule clause.is_typed_plus)

lemma clause.is_welltyped_plus [clause_simp]: 
  "clause.is_welltyped \<F> \<V> (C + D) \<longleftrightarrow> clause.is_welltyped \<F> \<V> C \<and> clause.is_welltyped \<F> \<V> D"
  by (auto simp: clause.is_welltyped_def)
 --------------- *)


(*lemma typed\<^sub>\<sigma>_typed: 
  assumes "is_typed \<V> \<sigma>" "typed \<V> t \<tau>"
  shows "typed \<V> (t \<cdot>t \<sigma>) \<tau>"
  using  typed.subst_stability assms
  by fast



lemma typed\<^sub>\<sigma>_typed': 
  assumes "typed\<^sub>\<sigma> \<F> \<V> \<sigma>" "typed \<F> \<V> t \<tau>"
  shows "typed \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> typed \<F> \<V> t \<tau>"
  using assms 
  unfolding typed\<^sub>\<sigma>_def
  by (smt (verit, ccfv_SIG) eval_term.simps(1,2) typed.simps)


lemma is_welltyped_welltyped: 
  assumes is_welltyped: "is_welltyped \<F> \<V> \<sigma>"
  shows "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> welltyped \<F> \<V> t \<tau>"
proof(rule iffI)
  assume "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  thus "welltyped \<F> \<V> t \<tau>"
  proof(induction "t \<cdot>t \<sigma>" \<tau>  arbitrary: t rule: welltyped.induct)
    case (Var x \<tau>)
    then obtain x' where t: "t = Var x'"
      by (metis subst_apply_eq_Var)

    have "welltyped \<F> \<V> t (\<V> x')"
      unfolding t 
      by (simp add: welltyped.Var)

    have "welltyped \<F> \<V> t (\<V> x)"
      using Var is_welltyped
      unfolding t is_welltyped_def
      by (metis eval_term.simps(1) welltyped.Var right_uniqueD welltyped_right_unique)

    then have \<V>_x': "\<tau> = \<V> x'"
      using Var is_welltyped
      unfolding is_welltyped_def  t
      by (metis welltyped.Var right_uniqueD welltyped_right_unique t)

    show ?case 
      unfolding t \<V>_x'
      by (simp add: welltyped.Var)
  next
    case (Fun f \<tau>s \<tau> ts)
    show ?case 
    proof(cases t)
      case (Var x)
      from Fun show ?thesis
        using is_welltyped
        unfolding is_welltyped_def Var
        by (metis (no_types, opaque_lifting) eval_term.simps(1) prod.sel(2) 
            term.distinct(1) term.inject(2) welltyped.simps)
    next
      case Fun\<^sub>t: Fun
      with Fun show ?thesis
        by (simp add: welltyped.simps list.rel_map(1) list_all2_mono)
    qed
  qed
next
  assume "welltyped \<F> \<V> t \<tau>"
  thus "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  proof(induction t \<tau>  rule: welltyped.induct)
    case Var\<^sub>t: (Var x \<tau>)
    then show ?case
    proof(cases "Var x \<cdot>t \<sigma>")
      case Var
      then show ?thesis
        using is_welltyped
        unfolding is_welltyped_def
        by (metis Var\<^sub>t.hyps eval_term.simps(1))        
    next
      case Fun
      then show ?thesis
        using is_welltyped
        unfolding is_welltyped_def
        by (metis Var\<^sub>t.hyps eval_term.simps(1))    
    qed
  next
    case (Fun f \<tau>s \<tau> ts)
    then show ?case
      using assms list_all2_mono
      unfolding is_welltyped_def
      by (smt (verit, ccfv_SIG) eval_term.simps(2) welltyped.simps list.rel_map(1))
  qed
qed

lemma typed\<^sub>\<sigma>_typed\<^sub>a: 
  assumes "is_typed \<V> \<sigma>"
  shows "atom.is_typed \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> atom.is_typed \<V> a"
  using atom.is_typed.subst_stability assms
  by fast
  

lemma is_welltyped_atom.is_welltyped: 
   assumes "is_welltyped \<V> \<sigma>"
  shows "atom.is_welltyped \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> atom.is_welltyped \<V> a"
  using atom.is_welltyped.subst_stability assms
  by fast

lemma typed\<^sub>\<sigma>_typed\<^sub>l: 
  assumes "is_typed \<V> \<sigma>"
  shows "literal.is_typed \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> literal.is_typed \<V> l"
  using literal.is_typed.subst_stability assms
  by fast
  
lemma is_welltyped_literal.is_welltyped: 
  assumes "is_welltyped \<V> \<sigma>"
  shows "literal.is_welltyped \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> literal.is_welltyped \<V> l"
  using literal.is_welltyped.subst_stability assms
  by fast

lemma typed\<^sub>\<sigma>_typed\<^sub>c: 
  assumes "is_typed \<V> \<sigma>"
  shows "clause.is_typed \<V> (c \<cdot> \<sigma>) \<longleftrightarrow> clause.is_typed \<V> c"
  using clause.is_typed.subst_stability assms
  by fast


lemma is_welltyped_on_welltyped: 
  assumes wt: "is_welltyped_on (term.vars t) \<F> \<V> \<sigma>"
  shows "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> welltyped \<F> \<V> t \<tau>"
proof(rule iffI)
  assume "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  thus "welltyped \<F> \<V> t \<tau>"
    using wt
  proof(induction "t \<cdot>t \<sigma>" \<tau>  arbitrary: t rule: welltyped.induct)
    case (Var x \<tau>)
    then obtain x' where t: "t = Var x'"
      by (metis subst_apply_eq_Var)

    have "welltyped \<F> \<V> t (\<V> x')"
      unfolding t 
      by (simp add: welltyped.Var)

    have "welltyped \<F> \<V> t (\<V> x)"
      using Var
      unfolding t is_welltyped_on_def
      by (auto intro: welltyped.Var elim: welltyped.cases)

    then have \<V>_x': "\<tau> = \<V> x'"
      using Var
      unfolding is_welltyped_def  t
      by (metis welltyped.Var right_uniqueD welltyped_right_unique t)

    show ?case 
      unfolding t \<V>_x'
      by (simp add: welltyped.Var)
  next
    case (Fun f \<tau>s \<tau> ts)
    show ?case 
    proof(cases t)
      case (Var x)
      from Fun show ?thesis
        using Fun
        unfolding is_welltyped_def Var
        by (simp add: welltyped.simps is_welltyped_on_def)
    next
      case Fun\<^sub>t: (Fun f' ts')
      hence "f = f'" and "ts = map (\<lambda>t. t \<cdot>t \<sigma>) ts'"
        using \<open>Fun f ts = t \<cdot>t \<sigma>\<close> by simp_all

      show ?thesis
        unfolding Fun\<^sub>t
      proof (rule welltyped.Fun)
        show "\<F> f' = (\<tau>s, \<tau>)"
          using Fun.hyps \<open>f = f'\<close> by argo
      next
        show "list_all2 (welltyped \<F> \<V>) ts' \<tau>s"
        proof (rule list.rel_mono_strong)
          show "list_all2 (\<lambda>x x2. welltyped \<F> \<V> (x \<cdot>t \<sigma>) x2 \<and>
            (\<forall>xa. x \<cdot>t \<sigma> = xa \<cdot>t \<sigma> \<longrightarrow> is_welltyped_on (term.vars xa) \<F> \<V> \<sigma> \<longrightarrow> welltyped \<F> \<V> xa x2))
            ts' \<tau>s"
            using Fun.hyps
            unfolding \<open>ts = map (\<lambda>t. t \<cdot>t \<sigma>) ts'\<close> list.rel_map
            by argo
        next
          fix t' \<tau>'
          assume
            "t' \<in> set ts'" and
            "\<tau>' \<in> set \<tau>s" and
            "welltyped \<F> \<V> (t' \<cdot>t \<sigma>) \<tau>' \<and>
              (\<forall>xa. t' \<cdot>t \<sigma> = xa \<cdot>t \<sigma> \<longrightarrow> is_welltyped_on (term.vars xa) \<F> \<V> \<sigma> \<longrightarrow> 
                  welltyped \<F> \<V> xa \<tau>')"
          thus "welltyped \<F> \<V> t' \<tau>'"
            using Fun.prems Fun.hyps
            by (simp add: Fun\<^sub>t is_welltyped_on_def)
        qed
      qed
    qed
  qed
next
  assume "welltyped \<F> \<V> t \<tau>"
  thus "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
    using wt
  proof(induction t \<tau>  rule: welltyped.induct)
    case Var\<^sub>t: (Var x \<tau>)
    thus ?case
      by (cases "Var x \<cdot>t \<sigma>") (simp_all add: is_welltyped_on_def)
  next
    case (Fun f \<tau>s \<tau> ts)

    show ?case
      unfolding eval_term.simps
    proof (rule welltyped.Fun)
      show "\<F> f = (\<tau>s, \<tau>)"
        using Fun by argo
    next
      show "list_all2 (welltyped \<F> \<V>) (map (\<lambda>s. s \<cdot>t \<sigma>) ts) \<tau>s"
        unfolding list.rel_map
        using Fun.IH
      proof (rule list.rel_mono_strong)
        fix t and \<tau>'
        assume
          "t \<in> set ts" and
          "\<tau>' \<in> set \<tau>s" and
          "welltyped \<F> \<V> t \<tau>' \<and> (is_welltyped_on (term.vars t) \<F> \<V> \<sigma> \<longrightarrow> welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>')"
        thus "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>'"
          using Fun.prems
          by (simp add: is_welltyped_on_def)
      qed
    qed
  qed
qed

lemma is_welltyped_on_atom.is_welltyped: 
  assumes wt: "is_welltyped_on (atom.vars A) \<F> \<V> \<sigma>"
  shows "atom.is_welltyped \<F> \<V> (A \<cdot>a \<sigma>) \<longleftrightarrow> atom.is_welltyped \<F> \<V> A"
proof (cases A)
  case (Upair t t')

  have "is_welltyped_on (term.vars t) \<F> \<V> \<sigma>" "is_welltyped_on (term.vars t') \<F> \<V> \<sigma>"
    using wt unfolding Upair by (simp_all add: is_welltyped_on_def atom.vars_def)

  hence "(\<exists>\<tau>. welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<and> welltyped \<F> \<V> (t' \<cdot>t \<sigma>) \<tau>) =
    (\<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>)"
    using is_welltyped_on_welltyped by metis

  thus ?thesis
    using Upair
    by (simp add: atom.subst_def atom.is_welltyped_def)
qed
*)

(*
lemma literal.is_welltyped_iff_atom.is_welltyped: "literal.is_welltyped \<V> L \<longleftrightarrow> atom.is_welltyped \<V> (atm_of L)"
  using literal_is_welltyped_iff
  sorry
  
lemma is_welltyped_on_literal.is_welltyped: 
  assumes wt: "is_welltyped_on (literal.vars L) \<F> \<V> \<sigma>"
  shows "literal.is_welltyped \<F> \<V> (L \<cdot>l \<sigma>) \<longleftrightarrow> literal.is_welltyped \<F> \<V> L"
  unfolding literal.is_welltyped_iff_atom.is_welltyped subst_literal
proof (rule is_welltyped_on_atom.is_welltyped)
  have "atom.vars (atm_of L) = literal.vars L"
    by (cases L) clause_auto
  thus "is_welltyped_on (atom.vars (atm_of L)) \<F> \<V> \<sigma>"
    using wt
    by simp
qed

lemma is_welltyped_on_clause.is_welltyped: 
  assumes wt: "is_welltyped_on (clause.vars C) \<F> \<V> \<sigma>"
  shows "clause.is_welltyped \<F> \<V> (C \<cdot> \<sigma>) \<longleftrightarrow> clause.is_welltyped \<F> \<V> C"
proof -
  have "literal.is_welltyped \<F> \<V> (L \<cdot>l \<sigma>) \<longleftrightarrow> literal.is_welltyped \<F> \<V> L" if "L \<in># C" for L
  proof (rule is_welltyped_on_literal.is_welltyped)
    have "literal.vars L \<subseteq> clause.vars C"
      using \<open>L \<in># C\<close>
      by (simp add: UN_upper clause.vars_def)
    thus "is_welltyped_on (literal.vars L) \<F> \<V> \<sigma>"
      using wt is_welltyped_on_subset by metis
  qed

  thus ?thesis
    unfolding clause.is_welltyped_def clause.subst_def
    by simp
qed

lemma is_welltyped_clause.is_welltyped: 
  assumes is_welltyped: "is_welltyped \<F> \<V> \<sigma>"
  shows "clause.is_welltyped \<F> \<V> (c \<cdot> \<sigma>) \<longleftrightarrow> clause.is_welltyped \<F> \<V> c"
  using is_welltyped_literal.is_welltyped[OF is_welltyped]
  unfolding clause.is_welltyped_def clause.subst_def
  by blast

lemma typed\<^sub>\<kappa>:
  assumes
    \<kappa>_type: "typed \<F> \<V> \<kappa>\<langle>t\<rangle> \<tau>\<^sub>1" and
    t_type: "typed \<F> \<V> t \<tau>\<^sub>2" and
    t'_type: "typed \<F> \<V> t' \<tau>\<^sub>2"
  shows 
    "typed \<F> \<V> \<kappa>\<langle>t'\<rangle> \<tau>\<^sub>1"
  using \<kappa>_type
proof(induction \<kappa> arbitrary: \<tau>\<^sub>1)
  case Hole
  then show ?case 
    using typed_right_unique right_uniqueD t'_type t_type by fastforce
next
  case More
  then show ?case 
    by (simp add: typed.simps)
qed
*)

lemma welltyped_subterm:
  assumes "welltyped \<V> (Fun f ts) \<tau>"
  shows "\<forall>t\<in>set ts. \<exists>\<tau>'. welltyped \<V> t \<tau>'"
  using welltyped.subterm'[OF assms].
  

lemma welltyped\<^sub>\<kappa>': 
  assumes "welltyped \<V> \<kappa>\<langle>t\<rangle> \<tau>" 
  shows "\<exists>\<tau>'. welltyped \<V> t \<tau>'"
  using welltyped.subterm[OF assms].
  

lemma welltyped\<^sub>\<kappa> [clause_intro]:
  assumes
    \<kappa>_type: "welltyped \<V> \<kappa>\<langle>t\<rangle> \<tau>\<^sub>1" and
    t_type: "welltyped \<V> t \<tau>\<^sub>2" and
    t'_type: "welltyped \<V> t' \<tau>\<^sub>2"
  shows 
    "welltyped \<V> \<kappa>\<langle>t'\<rangle> \<tau>\<^sub>1"
   using welltyped.context_compatible[OF t_type t'_type \<kappa>_type].
  
lemma typed\<^sub>\<sigma>_Var: "is_typed \<V> Var"
  using is_typed_id_subst.
 
(* ---- until here done *)

(* Keep *)


(* Done 
lemma welltyped_\<V>:
  assumes 
    "\<forall>x\<in>term.vars t. \<V> x = \<V>' x"
    "welltyped \<F> \<V> t \<tau>"
  shows  
    "welltyped \<F> \<V>' t \<tau>"
  using assms(2, 1)
  by(induction rule: welltyped.induct)(auto simp: welltyped.simps list.rel_mono_strong)
*)

(* TODO? 
lemma welltyped_subst_\<V>:
  assumes 
    "\<forall>x\<in> X. \<V> x = \<V>' x"
    "\<forall>x\<in> X. term.is_ground (\<gamma> x)"
  shows  
    "is_welltyped_on X \<F> \<V> \<gamma> \<longleftrightarrow> is_welltyped_on X \<F> \<V>' \<gamma>"
  unfolding is_welltyped_on_def
  using welltyped_\<V> assms
  by (metis empty_iff)
*)

(*
lemma atom.is_welltyped_\<V>:
  assumes 
    "\<forall>x\<in>atom.vars a. \<V> x = \<V>' x"
    "atom.is_welltyped \<F> \<V> a"
  shows  
    "atom.is_welltyped \<F> \<V>' a"
  using assms
  unfolding atom.is_welltyped_def atom.vars_def
  by (metis (full_types) UN_I welltyped_\<V>)

lemma literal.is_welltyped_\<V>:
  assumes 
    "\<forall>x\<in> literal.vars l. \<V> x = \<V>' x"
    "literal.is_welltyped \<F> \<V> l"
  shows  
    "literal.is_welltyped \<F> \<V>' l"
  using assms atom.is_welltyped_\<V>
  unfolding literal.is_welltyped_def literal.vars_def set_literal_atm_of
  by fastforce

lemma clause.is_welltyped_\<V>:
  assumes 
    "\<forall>x\<in> clause.vars c. \<V> x = \<V>' x"
    "clause.is_welltyped \<F> \<V> c"
  shows  
    "clause.is_welltyped \<F> \<V>' c"
  using assms literal.is_welltyped_\<V>
  unfolding clause.is_welltyped_def clause.vars_def
  by fastforce*)
(* ---- until here done *)

(* TODO: Needed? 
lemma welltyped_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "is_welltyped \<V> \<rho>"
    "welltyped (\<lambda>x. \<V> (the_inv Var (\<rho> x))) t \<tau>"
  shows "welltyped \<V> (t \<cdot>t \<rho>) \<tau>"
  using assms(3)
proof(induction rule: welltyped.induct)
  case (Var x \<tau>)
  then show ?case 
    using assms(1, 2)
    by (metis comp_apply eval_term.simps(1) inj_on_Var 
        term_subst_is_renaming_iff_ex_inj_fun_on_vars the_inv_f_f welltyped.Var)
next
  case (Fun f \<tau>s \<tau> ts)
  then show ?case
    by (smt (verit) assms(2) iso_tuple_UNIV_I list_all2_mono welltyped.Fun welltyped.subst_stability)
qed

lemma atom_is_welltyped_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "is_welltyped \<V> \<rho>"
    "atom.is_welltyped  (\<lambda>x. \<V> (the_inv Var (\<rho> x))) a"
  shows "atom.is_welltyped  \<V> (a \<cdot>a \<rho>)"
  using welltyped_renaming'[OF assms(1,2)] assms(3)
  by(cases a)(auto simp: subst_atom)

lemma literal_is_welltyped_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "is_welltyped \<V> \<rho>"
    "literal.is_welltyped (\<lambda>x. \<V> (the_inv Var (\<rho> x))) l"
  shows "literal.is_welltyped \<V> (l \<cdot>l \<rho>)"
  using atom_is_welltyped_renaming'[OF assms(1,2)] assms(3)
  unfolding subst_literal(3)
  by (metis literal_is_welltyped_iff subst_literal(3))

lemma clause_is_welltyped_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "is_welltyped \<V> \<rho>"
    "clause.is_welltyped (\<lambda>x. \<V> (the_inv Var (\<rho> x))) c"
  shows "clause.is_welltyped \<V> (c \<cdot> \<rho>)"
  using literal_is_welltyped_renaming'[OF assms(1,2)] assms(3)
  by (metis (mono_tags, lifting) UNIV_I assms(2) clause.is_welltyped.subst_stability is_typed_lifting.elims(1)
      literal.is_welltyped.subst_stability)
*)

definition range_vars' :: "('f, 'v) subst \<Rightarrow> 'v set" where                                 
  "range_vars' \<sigma> = \<Union>(term.vars ` range \<sigma>)"

lemma vars_term_range_vars':
  assumes "x \<in> term.vars (t \<cdot>t \<sigma>)"
  shows "x \<in> range_vars' \<sigma>"
  using assms
  unfolding range_vars'_def
  by(induction t) auto

context  
  fixes \<rho> and \<V> \<V>' :: "('v, 'ty) var_types"
  assumes 
    renaming: "term_subst.is_renaming \<rho>" and
    range_vars: "\<forall>x \<in> range_vars' \<rho>. \<V> (inv \<rho> (Var x)) = \<V>' x"
begin

(* TODO: Remove all these *)
lemma welltyped_renaming: "welltyped \<V> t \<tau> \<longleftrightarrow> welltyped \<V>' (t \<cdot>t \<rho>) \<tau>"
  using welltyped.typed_renaming[OF renaming] range_vars
  by (metis vars_term_range_vars')


lemma typed_renaming: "typed \<V> t \<tau> \<longleftrightarrow> typed \<V>' (t \<cdot>t \<rho>) \<tau>"
  using typed.typed_renaming[OF renaming]range_vars
  by (metis vars_term_range_vars')

(* TODO: Needed? *)
lemma is_welltyped_renaming_ground_subst: 
  assumes "is_welltyped \<V>' \<gamma>" "is_welltyped \<V> \<rho>" "term_subst.is_ground_subst \<gamma>"
  shows "is_welltyped \<V> (\<rho> \<odot> \<gamma>)"
proof-
  have "\<forall>x \<in> range_vars' \<rho>. welltyped \<V>' (\<gamma> x) (\<V>' x)"
    using assms 
    by blast

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<V>' (\<gamma> x) (\<V> (inv \<rho> (Var x)))"
    using range_vars
    by auto

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<V>' ((\<rho> \<odot> \<gamma>) x) (\<V> x)"
    by (metis \<open>is_welltyped_on (range_vars' \<rho>) \<V>' \<gamma>\<close> eval_subst_def eval_term.simps(1)
        vars_term_range_vars' welltyped.subst_stability welltyped_id_subst welltyped_renaming)
    

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<V>' (Var x \<cdot>t (\<rho> \<odot> \<gamma>)) (\<V> x)"
    by auto

  then have "\<forall>x. welltyped  \<V>' (Var x \<cdot>t (\<rho> \<odot> \<gamma>)) (\<V> x)"
    by (metis UNIV_I assms(1) term_subst.comp_subst.monoid_action_compatibility welltyped.subst_stability
        welltyped_id_subst welltyped_renaming)

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped  \<V>' (Var x \<cdot>t \<rho>) (\<V> x)"
    using welltyped_renaming by blast

  have "\<forall>x. welltyped \<V>' (Var x \<cdot>t \<rho>) (\<V> x)"
    by (meson welltyped.Var welltyped_renaming)

  then have "\<forall>x. welltyped \<V> (Var x \<cdot>t \<rho>) (\<V> x)"
    using welltyped_renaming
    using assms(2) by auto

  then show "is_welltyped  \<V> (\<rho> \<odot> \<gamma>)"
    by (metis (mono_tags, lifting) \<open>\<forall>x. welltyped  \<V>' (Var x \<cdot>t \<rho> \<odot> \<gamma>) (\<V> x)\<close> assms(3)
        eval_term.simps(1) term_subst.is_ground_subst_comp_right 
        term_subst.is_ground_subst_is_ground term_subst.subst_ident_if_ground welltyped_renaming)
qed

(* TODO: Remove all these *)
lemma atom_is_welltyped_renaming: "atom.is_welltyped \<V> a \<longleftrightarrow> atom.is_welltyped \<V>' (a \<cdot>a \<rho>)"
  using welltyped_renaming
  by(cases a)(simp add: subst_atom)

lemma literal_is_welltyped_renaming: "literal.is_welltyped \<V> l \<longleftrightarrow> literal.is_welltyped \<V>' (l \<cdot>l \<rho>)"
  unfolding literal_is_welltyped_iff subst_literal(3)
  using atom_is_welltyped_renaming.

lemma clause_is_welltyped_renaming: "clause.is_welltyped \<V> c \<longleftrightarrow> clause.is_welltyped \<V>' (c \<cdot> \<rho>)"
  using literal_is_welltyped_renaming
  by (simp add: clause.subst_def)

end

context  
  fixes \<rho> :: "('f, 'v) subst"
  assumes renaming: "term_subst.is_renaming \<rho>"
begin
(* 

lemma welltyped_renaming_weaker: 
  assumes "\<forall>x \<in> term.vars (t \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "welltyped \<V> t \<tau> \<longleftrightarrow> welltyped \<V>' (t \<cdot>t \<rho>) \<tau>"
  using assms renaming welltyped.typed_renaming by blast

lemma atom_is_welltyped_renaming_weaker: 
  assumes"\<forall>x \<in> atom.vars (a \<cdot>a \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "atom.is_welltyped \<V> a \<longleftrightarrow> atom.is_welltyped \<V>' (a \<cdot>a \<rho>)"
   using assms renaming atom.is_welltyped.typed_renaming by blast

lemma literal_is_welltyped_renaming_weaker: 
  assumes "\<forall>x \<in> literal.vars (l \<cdot>l \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "literal.is_welltyped \<V> l \<longleftrightarrow> literal.is_welltyped \<V>' (l \<cdot>l \<rho>)"
  using assms renaming literal.is_welltyped.typed_renaming by blast

lemma clause_is_welltyped_renaming_weaker: 
  assumes "\<forall>x \<in> clause.vars (c \<cdot> \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "clause.is_welltyped \<V> c \<longleftrightarrow> clause.is_welltyped \<V>' (c \<cdot> \<rho>)"
  using assms renaming clause.is_welltyped.typed_renaming by blast
 *)
(*
lemma typed_renaming_weaker:
  assumes "\<forall>x \<in> term.vars (t \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "typed \<V> t \<tau> \<longleftrightarrow> typed \<V>' (t \<cdot>t \<rho>) \<tau>"
  using assms renaming typed.typed_renaming by blast
  *)

(* TODO: *)
lemma is_welltyped_renaming_ground_subst_weaker: 
  assumes 
    "is_welltyped \<V>' \<gamma>" 
    "is_welltyped_on X \<V> \<rho>" 
    "term_subst.is_ground_subst \<gamma>" 
    "\<forall>x \<in> \<Union>(term.vars ` \<rho> ` X). \<V> (inv \<rho> (Var x)) = \<V>' x"
  shows "is_welltyped_on X \<V> (\<rho> \<odot> \<gamma>)"
  using welltyped.is_welltyped_renaming_ground_subst_weaker[OF renaming assms].

end


(*lemma welltyped_renaming_exists: 
  assumes "\<exists>X. \<forall>ty. infinite (X \<inter> {x. \<V>\<^sub>1 x = ty}) \<and> infinite ((UNIV - X) \<inter> {x. \<V>\<^sub>2 x = ty})"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v :: {countable, infinite}) subst" where
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2" 
    "range_vars' \<rho>\<^sub>1 \<inter> range_vars' \<rho>\<^sub>2 = {}"
    "range_vars' \<rho>\<^sub>1 \<union> range_vars' \<rho>\<^sub>2 = UNIV"
    "is_welltyped \<F> \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_welltyped \<F> \<V>\<^sub>2 \<rho>\<^sub>2"
proof-
  obtain renaming\<^sub>1 renaming\<^sub>2 :: "'v \<Rightarrow> 'v" where
    renamings:
    "inj renaming\<^sub>1" "inj renaming\<^sub>2"
    "range renaming\<^sub>1 \<inter> range renaming\<^sub>2 = {}" 
    "range renaming\<^sub>1 \<union> range renaming\<^sub>2 = UNIV" 
    "\<And>x. \<V>\<^sub>1 (renaming\<^sub>1 x) = \<V>\<^sub>1 x" 
    "\<And>x. \<V>\<^sub>2 (renaming\<^sub>2 x) = \<V>\<^sub>2 x"
    using obtain_inj''[OF assms]
    by metis

  define \<rho>\<^sub>1 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>1 x \<equiv> Var (renaming\<^sub>1 x)"

  define \<rho>\<^sub>2 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>2 x \<equiv> Var (renaming\<^sub>2 x)"

  have "term_subst.is_renaming \<rho>\<^sub>1"  "term_subst.is_renaming \<rho>\<^sub>2" 
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(1,2)
    by (meson injD injI term_subst.is_renaming_id_subst term_subst_is_renaming_iff)+

  moreover have "range_vars' \<rho>\<^sub>1 \<inter> range_vars' \<rho>\<^sub>2 = {}"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def range_vars'_def
    using renamings(3)
    by auto

  moreover have "range_vars' \<rho>\<^sub>1 \<union> range_vars' \<rho>\<^sub>2 = UNIV"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def range_vars'_def
    using renamings(4)
    by auto

  moreover have "is_welltyped \<F> \<V>\<^sub>1 \<rho>\<^sub>1" "is_welltyped \<F> \<V>\<^sub>2 \<rho>\<^sub>2"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def is_welltyped_def
    using renamings(5, 6)
    by(auto simp: welltyped.Var)

  ultimately show ?thesis 
    using that
    by blast
qed*)

(* TODO move these : *)
lemma welltyped_on_renaming_exists':
  fixes \<V>\<^sub>1 :: "'v \<Rightarrow> 'ty"
  assumes "finite X" "finite Y"  "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" where
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2" 
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "is_welltyped_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_welltyped_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
proof-
  obtain renaming\<^sub>1 renaming\<^sub>2 :: "'v \<Rightarrow> 'v" where
    renamings:
    "inj renaming\<^sub>1" "inj renaming\<^sub>2"
    "renaming\<^sub>1 ` X \<inter> renaming\<^sub>2 ` Y = {}" 
    "\<forall>x \<in> X. \<V>\<^sub>1 (renaming\<^sub>1 x) = \<V>\<^sub>1 x" 
    "\<forall>x \<in> Y. \<V>\<^sub>2 (renaming\<^sub>2 x) = \<V>\<^sub>2 x"
    using obtain_inj''_on'[OF assms].

  define \<rho>\<^sub>1 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>1 x \<equiv> Var (renaming\<^sub>1 x)"

  define \<rho>\<^sub>2 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>2 x \<equiv> Var (renaming\<^sub>2 x)"

  have "term_subst.is_renaming \<rho>\<^sub>1"  "term_subst.is_renaming \<rho>\<^sub>2" 
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(1,2)
    by (meson injD injI term_subst.is_renaming_id_subst term_subst_is_renaming_iff)+

  moreover have "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(3)
    by auto
 
  moreover have "is_welltyped_on X \<V>\<^sub>1 \<rho>\<^sub>1" "is_welltyped_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(4, 5)
    by(auto simp: welltyped.Var)

  ultimately show ?thesis 
    using that
    by presburger
qed

lemma is_welltyped_subst_upd:
  assumes "welltyped \<V> (Var var) \<tau>" "welltyped \<V> update \<tau>"  "is_welltyped \<V> \<gamma>" 
  shows "is_welltyped \<V> (\<gamma>(var := update))"
  using assms
  by auto

lemma is_welltyped_on_subst_upd:
  assumes "welltyped \<V> (Var var) \<tau>" "welltyped \<V> update \<tau>"  "is_welltyped_on X \<V> \<gamma>" 
  shows "is_welltyped_on X \<V> (\<gamma>(var := update))"
  using assms
  by auto

lemma welltyped_is_ground:
  assumes "term.is_ground t" "welltyped \<V> t \<tau>"
  shows "welltyped \<V>' t \<tau>"
  by (metis assms(1,2) empty_iff welltyped.replace_\<V>)

lemma term_subst_is_imgu_is_mgu: "term_subst.is_imgu \<mu> {{s, t}} = is_imgu \<mu> {(s, t)}"
  unfolding term_subst.is_imgu_def is_imgu_def term_subst.is_unifier_set_def  unifiers_def
  apply auto
     apply (meson finite.emptyI finite_insert insertCI term_subst.is_unifier_iff_if_finite)
  apply (metis insert_absorb2 substitution_ops.is_unifier_singleton term_subst.is_unifier_def term_subst.subst_set_insert)
   apply (simp add: term_subst.is_unifier_iff_if_finite)
  by (metis finite.emptyI finite.insertI insertI1 insert_subset subset_insertI term_subst.is_unifier_iff_if_finite)

lemma the_mgu_term_subst_is_imgu:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "s \<cdot>t \<sigma> = t \<cdot>t \<sigma>"
  shows "term_subst.is_imgu (the_mgu s t) {{s, t}}"
  using term_subst_is_imgu_is_mgu the_mgu_is_imgu
  using assms by blast

lemma Fun_arg_types:
  assumes 
    "welltyped \<V> (Fun f fs) \<tau>" 
    "welltyped \<V> (Fun f gs) \<tau>" 
  obtains \<tau>s where 
    "\<F> f = (\<tau>s, \<tau>)" 
    "list_all2 (welltyped \<V>) fs \<tau>s"
    "list_all2 (welltyped \<V>) gs \<tau>s"
  by (smt (verit, ccfv_SIG) Pair_inject assms(1) assms(2) option.inject term.distinct(1) term.inject(2) welltyped.simps)

lemma welltyped_zip_option:
  assumes 
    "welltyped \<V> (Fun f ts) \<tau>" 
    "welltyped \<V> (Fun f ss) \<tau>" 
    "zip_option ts ss = Some ds" 
  shows 
    "\<forall>(a, b) \<in> set ds. \<exists>\<tau>. welltyped \<V> a \<tau> \<and> welltyped \<V> b \<tau>"
proof-

  obtain \<tau>s where 
    "list_all2 (welltyped \<V>) ts \<tau>s"
    "list_all2 (welltyped \<V>) ss \<tau>s"
    using Fun_arg_types[OF assms(1, 2)].

  with assms(3) show ?thesis
  proof(induction ts ss arbitrary: \<tau>s ds rule: zip_induct)
    case (Cons_Cons t ts s ss)
    then obtain \<tau>' \<tau>s' where \<tau>s: "\<tau>s = \<tau>' # \<tau>s'"
      by (meson list_all2_Cons1)

    from Cons_Cons(2) 
    obtain d' ds' where ds: "ds = d' # ds'"
      by auto

    have "zip_option ts ss = Some ds'"
      using Cons_Cons(2) 
      unfolding ds
      by fastforce

    moreover have "list_all2 (welltyped \<V>) ts \<tau>s'" 
      using Cons_Cons.prems(2) \<tau>s by blast

    moreover have "list_all2 (welltyped \<V>) ss \<tau>s'"
      using Cons_Cons.prems(3) \<tau>s by blast

    ultimately have "\<forall>(t, s)\<in>set ds'. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> s \<tau>"
      using Cons_Cons.IH
      by presburger

    moreover have "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> s \<tau>"
      using Cons_Cons.prems(2) Cons_Cons.prems(3) \<tau>s by blast

    ultimately show ?case
      using Cons_Cons.prems(1) ds
      by fastforce
  qed(auto)
qed

lemma welltyped_decompose':
  assumes
    "welltyped \<V> (Fun f fs) \<tau>" 
    "welltyped \<V> (Fun f gs) \<tau>"
    "decompose (Fun f fs) (Fun g gs) = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  using assms welltyped_zip_option[OF assms(1,2)]
  by (metis (lifting) decompose_Some not_Some_eq zip_option_simps(2,3))
  
lemma welltyped_decompose:
  assumes
    "welltyped \<V> f \<tau>" 
    "welltyped \<V> g \<tau>"
    "decompose f g = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
proof-

  obtain f' fs gs where "f = Fun f' fs" "g = Fun f' gs"
    using assms(3)
    unfolding decompose_def
    by (smt (z3) option.distinct(1) prod.simps(2) rel_option_None1 term.split_sels(2))

  then show ?thesis
    using assms welltyped_decompose'
    by (metis (mono_tags, lifting))
qed

lemma welltyped_subst'_subst: 
  assumes "welltyped \<V> (Var x) \<tau>" "welltyped \<V> t \<tau>"
  shows "is_welltyped \<V> (subst x t)"
  using assms
  unfolding subst_def
  by (simp add: welltyped.simps)

lemma welltyped_unify:
  assumes    
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
    "is_welltyped \<V> (subst_of bs)"
  shows "is_welltyped \<V> (subst_of unifier)"
  using assms
proof(induction es bs arbitrary: unifier rule: unify.induct)
  case (1 bs)
  then show ?case
    by simp
next
  case (2 f ss g ts E bs)
  then obtain \<tau> where \<tau>:
    "welltyped \<V> (Fun f ss) \<tau>" 
    "welltyped \<V> (Fun g ts) \<tau>"
    by auto

  obtain ds where ds: "decompose (Fun f ss) (Fun g ts) = Some ds"
    using 2(2)
    by(simp split: option.splits)

  moreover then have "unify (ds @ E) bs = Some unifier"
    using "2.prems"(1) by auto

  moreover have "\<forall>(t, t')\<in>set (ds @ E). \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
    using welltyped_decompose[OF \<tau> ds] 2(3)
    by fastforce

  ultimately show ?case 
    using 2
    by blast
next
  case (3 x t E bs)
  show ?case
  proof(cases "t = Var x")
    case True
    then show ?thesis 
      using 3
      by simp
  next
    case False
    then have "unify (subst_list (subst x t) E) ((x, t) # bs) = Some unifier"
      using 3
      by(auto split: if_splits)

    moreover have 
      "\<forall>(s, s') \<in> set E. \<exists>\<tau>. welltyped \<V> (s \<cdot>t Var(x := t)) \<tau> \<and> welltyped \<V> (s' \<cdot>t Var(x := t)) \<tau>"
      using 3(4)
      by (smt (verit, ccfv_threshold) case_prodD case_prodI2 fun_upd_apply welltyped.Var 
          list.set_intros(1) list.set_intros(2) right_uniqueD term.welltyped.right_unique 
           welltyped.subst_stability)

    moreover then have 
      "\<forall>(s, s') \<in> set (subst_list (subst x t) E). \<exists>\<tau>. welltyped \<V> s \<tau> \<and> welltyped \<V> s' \<tau>"
      unfolding subst_def subst_list_def
      by fastforce

    moreover have "is_welltyped \<V> (subst x t)"
      using 3(4) welltyped_subst'_subst
      by fastforce

    moreover then have "is_welltyped \<V> (subst_of ((x, t) # bs))"
      using 3(5)
      by (simp add: calculation(4) subst_compose_def)

    ultimately show ?thesis 
      using 3(2, 3) False by force
  qed
next
  case (4 t ts x E bs)
  then have "unify (subst_list (subst x (Fun t ts)) E) ((x, (Fun t ts)) # bs) = Some unifier"
    by(auto split: if_splits)

  moreover have 
    "\<forall>(s, s') \<in> set E. \<exists>\<tau>. 
        welltyped \<V> (s \<cdot>t Var(x := (Fun t ts))) \<tau> \<and> welltyped \<V> (s' \<cdot>t Var(x := (Fun t ts))) \<tau>"
    using 4(3)
    by (smt (verit, ccfv_threshold) case_prodD case_prodI2 fun_upd_apply welltyped.Var 
        list.set_intros(1) list.set_intros(2) right_uniqueD term.welltyped.right_unique 
        welltyped.subst_stability)

  moreover then have 
    "\<forall>(s, s') \<in> set (subst_list (subst x (Fun t ts)) E). \<exists>\<tau>. 
        welltyped \<V> s \<tau> \<and> welltyped \<V> s' \<tau>"
    unfolding subst_def subst_list_def
    by fastforce

  moreover have "is_welltyped \<V> (subst x (Fun t ts))"
    using 4(3) welltyped_subst'_subst
    by fastforce

  moreover then have "is_welltyped \<V> (subst_of ((x, (Fun t ts)) # bs))"
    using 4(4) 
    by (simp add: calculation(4) subst_compose_def)

  ultimately show ?case 
    using 4(1, 2)
    by (metis (no_types, lifting) option.distinct(1) unify.simps(4))
qed

lemma welltyped_unify':
  assumes 
    unify: "unify [(t, t')] [] = Some unifier" and
    \<tau>: "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  shows "is_welltyped \<V> (subst_of unifier)"
  using assms welltyped_unify[OF unify] \<tau>
  by fastforce

lemma welltyped_the_mgu: 
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    \<tau>: "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  shows 
    "is_welltyped \<V> \<mu>"
  using assms welltyped_unify'[of t t' _ \<V>]
  unfolding the_mgu_def mgu_def  
  by(auto simp: welltyped.Var split: option.splits)

abbreviation welltyped_imgu where
  "welltyped_imgu \<V> term term' \<mu> \<equiv>
    \<forall>\<tau>. welltyped \<V> term \<tau> \<longrightarrow> welltyped \<V> term' \<tau> \<longrightarrow> is_welltyped \<V> \<mu>"

lemma welltyped_imgu_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "welltyped_imgu \<V> term term' \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "welltyped_imgu \<V> term term' (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>, of \<V>] assms
    unfolding \<mu>
    by blast

  then show ?thesis
    using that imgu_exists_extendable[OF unified]
    by (metis the_mgu the_mgu_term_subst_is_imgu unified)
qed

(* TODO: typed? *)
abbreviation welltyped_imgu' where
  "welltyped_imgu' \<V> term term' \<mu> \<equiv>
    \<exists>\<tau>. welltyped \<V> term \<tau> \<and> welltyped \<V> term' \<tau> \<and> is_welltyped \<V> \<mu>"

lemma welltyped_imgu'_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>" and "welltyped \<V> term \<tau>" "welltyped \<V> term' \<tau>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "welltyped_imgu' \<V> term term' \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "welltyped_imgu \<V> term term' (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>, of \<V>] assms
    unfolding \<mu>
    by blast

  then show ?thesis
    using that imgu_exists_extendable[OF unified]
    by (metis assms(2) assms(3) the_mgu the_mgu_term_subst_is_imgu unified)
qed

end

end
