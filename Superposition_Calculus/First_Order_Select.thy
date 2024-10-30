theory First_Order_Select
  imports 
    Selection_Function
    First_Order_Clause
    First_Order_Type_System
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

type_synonym 'f ground_select = "'f ground_atom clause \<Rightarrow> 'f ground_atom clause"
type_synonym ('f, 'v) select = "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"

definition is_select_grounding :: "('f, 'v) select \<Rightarrow> 'f ground_select \<Rightarrow> bool" where 
  "\<And>select select\<^sub>G.
        is_select_grounding select select\<^sub>G = (\<forall>clause\<^sub>G. \<exists>clause \<gamma>.
        clause.is_ground (clause \<cdot> \<gamma>)  \<and> 
        clause\<^sub>G = clause.to_ground (clause \<cdot> \<gamma>) \<and> 
        select\<^sub>G clause\<^sub>G = clause.to_ground ((select clause) \<cdot> \<gamma>))"

lemma infinite_lists_per_length: "infinite {l :: ('a :: infinite) list. length (tl l) = y}"
proof(induction y)
  case 0

  show ?case
  proof
    assume a: "finite {l :: 'a list. length (tl l) = 0}"

    define f where "\<And>x:: 'a . f x \<equiv> [x]"


    have "\<And>x y. f x = f y \<Longrightarrow> x = y"
      unfolding f_def
      by (metis nth_Cons_0)

    moreover have "\<And>x. length (f x) \<le> Suc 0"
      unfolding f_def
      by simp

    moreover have "\<And>x. length x = Suc 0 \<Longrightarrow> x \<in> range f"
      unfolding f_def
      by (smt (z3) One_nat_def Suc_length_conv Suc_pred' diff_Suc_1 diff_is_0_eq' 
          length_0_conv nat.simps(3) not_gr0 rangeI)

    moreover have "\<And>x. \<lbrakk>x \<notin> range f; length x \<le> Suc 0\<rbrakk> \<Longrightarrow> x = []"
      using calculation(3) le_Suc_eq by auto

    moreover have "\<And>xa. f xa = [] \<Longrightarrow> False"
      unfolding f_def
      by simp

    ultimately have tt: "bij_betw f UNIV  ({l. length (tl l) = 0} - {[]})"
      unfolding bij_betw_def inj_def
      by auto presburger

    then have "infinite ({l :: 'a list. length (tl l) = 0} - {[]})"
      using bij_betw_finite infinite_UNIV by blast

    then have "infinite {l :: 'a list. length (tl l) = 0}"
      by simp

    with a show False
      by blast
  qed
next
  case (Suc y)


  have 1: "{l :: 'a list. length (tl l) = y} = 
    (if y = 0 then insert [] {l. length l = 1} else {l.  length l = Suc y})"
    by (auto simp: le_Suc_eq)

  have 2: "\<And>x. length x = Suc y \<Longrightarrow> x \<in> tl ` {l. length l - Suc 0 = Suc y}"
    by (metis (mono_tags, lifting) One_nat_def imageI length_tl list.sel(3) mem_Collect_eq)

  show ?case 
  proof
    assume "finite {l  :: 'a list. length (tl l) = Suc y}"

    then have "finite (tl ` {l :: 'a list. length (tl l) = Suc y})"
      by blast

    moreover have "tl ` {l :: 'a list. length (tl l) = Suc y} = {l :: 'a list. length l  = Suc y}"
      using 2
      by auto

    ultimately show False
      using Suc 1  
      by (smt (verit, ccfv_SIG) Collect_cong One_nat_def finite_insert)
  qed
qed

lemma infinite_prods': "{p :: 'a \<times> 'a . fst p = y} = {y} \<times> UNIV"
  by auto
 

lemma infinite_prods: "infinite {p :: (('a :: infinite) \<times> 'a). fst p = y}"
  unfolding infinite_prods'
  using finite_cartesian_productD2 infinite_UNIV by blast

lemma nat_version': "\<exists>f :: nat \<Rightarrow> nat. \<forall>y :: nat. infinite {x. f x = y}"
proof-
  obtain g :: "nat \<Rightarrow> nat \<times> nat" where bij_g: "bij g"
    using bij_prod_decode by blast

  define f :: "nat \<Rightarrow> nat" where 
    "\<And>x. f x \<equiv> fst (g x)"

  have "\<And>y. infinite {x. f x = y}"
  proof-
    fix y
    have x: "{x. fst (g x) = y} =  inv g ` {p. fst p = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_g bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq)

    show "infinite {x. f x = y}"
      unfolding f_def x
      using infinite_prods
      by (metis bij_betw_def bij_g finite_imageI image_f_inv_f)
  qed

  then show ?thesis
    by blast    
qed

lemma not_nat_version': "\<exists>f :: ('a :: infinite) \<Rightarrow> 'a. \<forall>y. infinite {x. f x = y}"
proof-
  obtain g :: "'a \<Rightarrow> 'a \<times> 'a" where bij_g: "bij g"
    using Times_same_infinite_bij_betw_types bij_betw_inv infinite_UNIV by blast

  define f :: "'a \<Rightarrow> 'a" where 
    "\<And>x. f x \<equiv> fst (g x)"

  have "\<And>y. infinite {x. f x = y}"
  proof-
    fix y
    have x: "{x. fst (g x) = y} =  inv g ` {p. fst p = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_g bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq)

    show "infinite {x. f x = y}"
      unfolding f_def x
      using infinite_prods 
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)
  qed

  then show ?thesis
    by blast    
qed

lemma not_nat_version'': 
  assumes "|UNIV :: 'b set| \<le>o |UNIV :: ('a :: infinite) set|"
  shows "\<exists>f :: 'a \<Rightarrow> 'b. \<forall>y. infinite {x. f x = y}"
proof-
  obtain g :: "'a \<Rightarrow> 'a \<times> 'a" where bij_g: "bij g"
    using Times_same_infinite_bij_betw_types bij_betw_inv infinite_UNIV by blast

  define f :: "'a \<Rightarrow> 'a" where 
    "\<And>x. f x \<equiv> fst (g x)"

  have inf: "\<And>y. infinite {x. f x = y}"
  proof-
    fix y
    have x: "{x. fst (g x) = y} =  inv g ` {p. fst p = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_g bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq)

    show "infinite {x. f x = y}"
      unfolding f_def x
      using infinite_prods
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)
  qed

  obtain f' ::  "'a \<Rightarrow> 'b" where "surj f'"
    using assms
    by (metis card_of_ordLeq2 empty_not_UNIV)

  then have "\<And>y. infinite {x. f' (f x) = y}"
    using inf
    by (smt (verit, ccfv_SIG) Collect_mono finite_subset surjD)

  then show ?thesis
    by meson
qed



lemma nat_version: "\<exists>f :: nat \<Rightarrow> nat. \<forall>y :: nat. infinite {x. f x = y}"
proof-
  obtain g :: "nat \<Rightarrow> nat list" where bij_g: "bij g"
    using bij_list_decode by blast

  define f :: "nat \<Rightarrow> nat" where 
    "\<And>x. f x \<equiv> length (tl (g x))"

  have "\<And>y. infinite {x. f x = y}"
  proof-
    fix y
    have "{x. length (tl (g x)) = y} = inv g ` {l. length (tl l) = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_betw_def bij_g bij_image_Collect_eq image_inv_f_f 
          inv_inv_eq surj_imp_inj_inv)

    then show "infinite {x. f x = y}"
      unfolding f_def
      using infinite_lists_per_length
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)
  qed

  then show ?thesis
    by blast    
qed

definition all_types where 
  "all_types \<V> \<equiv> \<forall>ty. infinite {x. \<V> x = ty}"


lemma all_types_nat: "\<exists>\<V> :: nat \<Rightarrow> nat. all_types \<V>"
  unfolding all_types_def
  using nat_version
  by blast

lemma all_types: "\<exists>\<V> :: ('v :: {infinite, countable} \<Rightarrow> 'ty :: countable). all_types \<V>"
proof-
  obtain \<V>_nat :: "nat \<Rightarrow> nat" where \<V>_nat: "all_types \<V>_nat"
    using all_types_nat
    by blast

  obtain v_to_nat :: "'v \<Rightarrow> nat" where v_to_nat: "bij v_to_nat"
    using countableI_type infinite_UNIV to_nat_on_infinite by blast

  obtain nat_to_ty :: "nat \<Rightarrow> 'ty" and N where nat_to_ty: "bij_betw nat_to_ty N UNIV"
    using countableE_bij
    by (metis countableI_type)

  define \<V> where "\<And>x. \<V> x \<equiv> nat_to_ty (\<V>_nat (v_to_nat x))"

  have 1: "\<And>ty. {x. \<V>_nat (v_to_nat x) = ty} = inv v_to_nat ` {x. \<V>_nat x = ty}"
    by (smt (verit, best) Collect_cong bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq v_to_nat)

  have 2: "\<And>ty. infinite {x. \<V>_nat (v_to_nat x) = ty}"
    unfolding 1
    using \<V>_nat 
    unfolding all_types_def
    by (metis bij_betw_def finite_imageI image_f_inv_f v_to_nat)


  have "\<And>ty. infinite {x. \<V> x = ty}"
    using \<V>_nat
    unfolding \<V>_def all_types_def
    by (smt (verit) "2" Collect_mono UNIV_I bij_betw_iff_bijections finite_subset nat_to_ty)
  
  then show "\<exists>\<V> :: 'v :: {infinite, countable} \<Rightarrow> 'ty :: countable. all_types \<V>"
    unfolding all_types_def
    by fast
qed

lemma all_types': 
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: ('v :: infinite) set|"
  shows "\<exists>\<V> :: ('v :: infinite \<Rightarrow> 'ty). all_types \<V>"
  using not_nat_version''[OF assms]
  unfolding all_types_def
  by argo

definition clause_groundings :: "('f, 'ty) fun_types \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> 'f ground_atom clause set"  where
  "clause_groundings \<F> clause = { clause.to_ground (fst clause \<cdot> \<gamma>) | \<gamma>. 
    term_subst.is_ground_subst \<gamma> \<and> 
    welltyped\<^sub>c \<F> (snd clause) (fst clause) \<and> 
    welltyped\<^sub>\<sigma>_on (clause.vars (fst clause))  \<F> (snd clause) \<gamma> \<and> 
    all_types (snd clause)
  }"

abbreviation select_subst_stability_on where
  "\<And>select select\<^sub>G. select_subst_stability_on \<F> select select\<^sub>G premises \<equiv>
    \<forall>premise\<^sub>G \<in> \<Union> (clause_groundings \<F> ` premises). \<exists>(premise, \<V>) \<in> premises. \<exists>\<gamma>. 
      premise \<cdot> \<gamma> = clause.from_ground premise\<^sub>G \<and> 
      select\<^sub>G (clause.to_ground (premise \<cdot> \<gamma>)) = clause.to_ground ((select premise) \<cdot> \<gamma>) \<and>
      welltyped\<^sub>c \<F> \<V> premise \<and> welltyped\<^sub>\<sigma>_on (clause.vars premise) \<F> \<V> \<gamma> \<and> 
      term_subst.is_ground_subst \<gamma>  \<and> 
      all_types \<V>"

lemma obtain_subst_stable_on_select_grounding:
  fixes select :: "('f, 'v) select"
  obtains select\<^sub>G where 
    "select_subst_stability_on \<F> select select\<^sub>G premises"
    "is_select_grounding select select\<^sub>G"
proof-
  let ?premise_groundings = "\<Union>(clause_groundings \<F> ` premises)"

  have select\<^sub>G_exists_for_premises: 
    "\<forall>premise\<^sub>G \<in> ?premise_groundings. \<exists>select\<^sub>G \<gamma>. \<exists>(premise, \<V>) \<in> premises.
          premise \<cdot> \<gamma> = clause.from_ground premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = clause.to_ground ((select premise) \<cdot> \<gamma>) 
        \<and> welltyped\<^sub>c \<F> \<V> premise \<and> welltyped\<^sub>\<sigma>_on (clause.vars premise) \<F> \<V> \<gamma>
        \<and> term_subst.is_ground_subst \<gamma> \<and> all_types \<V>"
    unfolding clause_groundings_def
    using clause.is_ground_subst_is_ground
    by fastforce

  obtain select\<^sub>G_on_premise_groundings where 
    select\<^sub>G_on_premise_groundings: "\<forall>premise\<^sub>G \<in>?premise_groundings. \<exists>(premise, \<V>) \<in> premises. \<exists>\<gamma>.
        premise \<cdot> \<gamma> = clause.from_ground premise\<^sub>G 
      \<and> select\<^sub>G_on_premise_groundings (clause.to_ground (premise \<cdot> \<gamma>)) = 
          clause.to_ground ((select premise) \<cdot> \<gamma>) 
      \<and> welltyped\<^sub>c \<F> \<V> premise \<and> welltyped\<^sub>\<sigma>_on (clause.vars premise) \<F> \<V> \<gamma> 
      \<and> term_subst.is_ground_subst \<gamma> \<and> all_types \<V>"
    using Ball_Ex_comm(1)[OF select\<^sub>G_exists_for_premises] 
      prod.case_eq_if clause.from_ground_inverse
    by fastforce

  define select\<^sub>G where
    "\<And>clause\<^sub>G. select\<^sub>G clause\<^sub>G = (
        if clause\<^sub>G  \<in> ?premise_groundings 
        then select\<^sub>G_on_premise_groundings clause\<^sub>G 
        else clause.to_ground (select (clause.from_ground clause\<^sub>G))
    )"

  have grounding: "is_select_grounding select select\<^sub>G"
  proof-
    have "\<And>clause\<^sub>G a b.
       \<lbrakk>\<forall>y\<in>premises.
           \<forall>premise\<^sub>G\<in>clause_groundings \<F> y.
              \<exists>x\<in>premises.
                 case x of
                 (premise, \<V>) \<Rightarrow>
                   \<exists>\<gamma>. premise \<cdot> \<gamma> = clause.from_ground premise\<^sub>G \<and>
                       select\<^sub>G_on_premise_groundings (clause.to_ground (premise \<cdot> \<gamma>)) =
                       clause.to_ground (select premise \<cdot> \<gamma>) \<and>
                       welltyped\<^sub>c \<F> \<V> premise \<and>
                       welltyped\<^sub>\<sigma>_on (clause.vars premise) \<F> \<V> \<gamma> \<and>
                       term_subst.is_ground_subst \<gamma> \<and> all_types \<V>;
        (a, b) \<in> premises; clause\<^sub>G \<in> clause_groundings \<F> (a, b)\<rbrakk>
       \<Longrightarrow> \<exists>clause \<gamma>.
              clause.vars (clause \<cdot> \<gamma>) = {} \<and>
              clause\<^sub>G = clause.to_ground (clause \<cdot> \<gamma>) \<and>
              select\<^sub>G_on_premise_groundings clause\<^sub>G = clause.to_ground (select clause \<cdot> \<gamma>)"
      by force

    moreover have " \<And>clause\<^sub>G.
       \<lbrakk>\<forall>y\<in>premises.
           \<forall>premise\<^sub>G\<in>clause_groundings \<F> y.
              \<exists>x\<in>premises.
                 case x of
                 (premise, \<V>) \<Rightarrow>
                   \<exists>\<gamma>. premise \<cdot> \<gamma> = clause.from_ground premise\<^sub>G \<and>
                       select\<^sub>G_on_premise_groundings (clause.to_ground (premise \<cdot> \<gamma>)) =
                       clause.to_ground (select premise \<cdot> \<gamma>) \<and>
                       welltyped\<^sub>c \<F> \<V> premise \<and>
                       welltyped\<^sub>\<sigma>_on (clause.vars premise) \<F> \<V> \<gamma> \<and>
                       term_subst.is_ground_subst \<gamma> \<and> all_types \<V>;
        \<forall>x\<in>premises. clause\<^sub>G \<notin> clause_groundings \<F> x\<rbrakk>
       \<Longrightarrow> \<exists>clause \<gamma>.
              clause.vars (clause \<cdot> \<gamma>) = {} \<and>
              clause\<^sub>G = clause.to_ground (clause \<cdot> \<gamma>) \<and>
              clause.to_ground (select (clause.from_ground clause\<^sub>G)) =
              clause.to_ground (select clause \<cdot> \<gamma>)"
      by (metis (no_types, opaque_lifting) clause.comp_subst.left.action_neutral 
            clause.ground_is_ground clause.from_ground_inverse)

    ultimately show ?thesis
      unfolding is_select_grounding_def select\<^sub>G_def
      using select\<^sub>G_on_premise_groundings
      by auto
  qed
   
  show ?thesis
    using that[OF _ grounding] select\<^sub>G_on_premise_groundings
    unfolding select\<^sub>G_def 
    by fastforce
qed

locale first_order_select = select select
  for select :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"
begin

abbreviation is_grounding :: "'f ground_select \<Rightarrow> bool" where
  "is_grounding select\<^sub>G \<equiv> is_select_grounding select select\<^sub>G"

definition select\<^sub>G\<^sub>s where
  "select\<^sub>G\<^sub>s = { ground_select. is_grounding ground_select }"

definition select\<^sub>G_simple where
  "select\<^sub>G_simple clause = clause.to_ground (select (clause.from_ground clause))"

lemma select\<^sub>G_simple: "is_grounding select\<^sub>G_simple"
  unfolding is_select_grounding_def select\<^sub>G_simple_def
  by (metis clause.from_ground_inverse clause.ground_is_ground clause.subst_id_subst)

lemma select_from_ground_clause1: 
  assumes "clause.is_ground clause" 
  shows "clause.is_ground (select clause)"
  using select_subset sub_ground_clause assms
  by metis

lemma select_from_ground_clause2: 
  assumes "literal \<in># select (clause.from_ground clause)"  
  shows "literal.is_ground literal"
  using assms clause.sub_in_ground_is_ground select_subset
  by blast

lemma select_from_ground_clause3: 
  assumes "clause.is_ground clause" "literal\<^sub>G \<in># clause.to_ground clause"
  shows "literal.from_ground literal\<^sub>G \<in># clause"
  using assms 
  by (metis clause.to_ground_inverse clause.ground_sub_in_ground)

lemmas select_from_ground_clause =
  select_from_ground_clause1
  select_from_ground_clause2
  select_from_ground_clause3

lemma select_subst1:
  assumes "clause.is_ground (clause \<cdot> \<gamma>)"  
  shows "clause.is_ground (select clause \<cdot> \<gamma>)" 
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause clause.subst_def)

lemma select_subst2: 
  assumes "literal \<in># select clause \<cdot> \<gamma>"  
  shows "is_neg literal"
  using assms subst_neg_stable select_negative_lits
  unfolding clause.subst_def
  by auto

lemmas select_subst = select_subst1 select_subst2

end

locale grounded_first_order_select = 
  first_order_select select for select +
fixes select\<^sub>G 
assumes select\<^sub>G: "is_select_grounding select select\<^sub>G"
begin

abbreviation subst_stability_on where
  "subst_stability_on \<F> premises \<equiv> select_subst_stability_on \<F> select select\<^sub>G premises"

lemma select\<^sub>G_subset: "select\<^sub>G clause \<subseteq># clause"
  using select\<^sub>G 
  unfolding is_select_grounding_def
  by (metis select_subset clause.to_ground_def image_mset_subseteq_mono clause.subst_def)

lemma select\<^sub>G_negative:
  assumes "literal\<^sub>G \<in># select\<^sub>G clause\<^sub>G"
  shows "is_neg literal\<^sub>G"
proof -
  obtain clause \<gamma> where 
    is_ground: "clause.is_ground (clause \<cdot> \<gamma>)" and
    select\<^sub>G: "select\<^sub>G clause\<^sub>G = clause.to_ground (select clause \<cdot> \<gamma>)"
    using select\<^sub>G
    unfolding is_select_grounding_def
    by blast

  show ?thesis
    using 
      select_from_ground_clause(3)[
        OF select_subst(1)[OF is_ground] assms[unfolded select\<^sub>G], 
        THEN select_subst(2)
        ]
    unfolding literal.from_ground_def
    by simp
qed

sublocale ground: select select\<^sub>G
  by unfold_locales (simp_all add: select\<^sub>G_subset select\<^sub>G_negative)

end

end
