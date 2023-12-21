theory First_Order_Superposition
  imports
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Ground_Superposition
    First_Order_Clause
begin

section \<open>First-Order Layer\<close>

context ground_superposition_calculus
begin

lemmas less\<^sub>l\<^sub>G_transitive_on = transp_less_lit[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>l\<^sub>G_asymmetric_on = asymp_less_lit[THEN asymp_on_subset, OF subset_UNIV]
lemmas less\<^sub>l\<^sub>G_total_on = totalp_less_lit[THEN totalp_on_subset, OF subset_UNIV]

lemmas less\<^sub>c\<^sub>G_transitive_on = transp_less_cls[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>c\<^sub>G_asymmetric_on = asymp_less_cls[THEN asymp_on_subset, OF subset_UNIV]
lemmas less\<^sub>c\<^sub>G_total_on = totalp_less_cls[THEN totalp_on_subset, OF subset_UNIV]

lemmas is_maximal_lit_def = is_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]
lemmas is_strictly_maximal_lit_def = 
  is_strictly_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]

end

locale first_order_superposition_calculus =
  fixes
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    less\<^sub>t\<^sub>G :: "'f ground_term \<Rightarrow> 'f ground_term \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) and
    select :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"
  assumes
    less\<^sub>t\<^sub>G_less\<^sub>t: 
      "\<And>term\<^sub>1 term\<^sub>2. term\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>2 \<longleftrightarrow> to_term term\<^sub>1 \<prec>\<^sub>t to_term term\<^sub>2" and
    
    less\<^sub>t_transitive [intro]: "transp (\<prec>\<^sub>t)" and
    less\<^sub>t_asymmetric [intro]: "asymp (\<prec>\<^sub>t)" and

    less\<^sub>t\<^sub>G_wellfounded [intro]: "wfP (\<prec>\<^sub>t\<^sub>G)" and
    less\<^sub>t\<^sub>G_total [intro]: "totalp (\<prec>\<^sub>t\<^sub>G)" and
    
    less\<^sub>t\<^sub>G_context_compatible [simp]:
      "\<And>context term\<^sub>1 term\<^sub>2. term\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>2 \<Longrightarrow> context\<langle>term\<^sub>1\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G context\<langle>term\<^sub>2\<rangle>\<^sub>G" and
    less\<^sub>t\<^sub>G_subterm_property [simp]: 
      "\<And>term context. context \<noteq> \<box>\<^sub>G \<Longrightarrow> term \<prec>\<^sub>t\<^sub>G context\<langle>term\<rangle>\<^sub>G" and

    less\<^sub>t_ground_subst_stability: 
      "\<And>term\<^sub>1 term\<^sub>2 (\<theta> :: 'v \<Rightarrow> ('f, 'v) term). 
        is_ground_term (term\<^sub>1 \<cdot>t \<theta>) \<Longrightarrow>
        is_ground_term (term\<^sub>2 \<cdot>t \<theta>) \<Longrightarrow>
        term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<Longrightarrow>
        to_ground_term (term\<^sub>1 \<cdot>t \<theta>) \<prec>\<^sub>t\<^sub>G to_ground_term (term\<^sub>2 \<cdot>t \<theta>)" and
    
    select_subset: 
      "\<And>clause. select clause \<subseteq># clause" and
    select_negative: 
      "\<And>clause literal. literal \<in># select clause \<Longrightarrow> is_neg literal" and
    select_renaming_stability: 
      "\<And>clause \<rho>. is_renaming \<rho> \<Longrightarrow> select (clause \<cdot> \<rho>) = (select clause) \<cdot> \<rho>" and

    (* TODO: Use theorem from CeTA *)
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

definition is_ground_select :: "('f ground_atom clause \<Rightarrow> 'f ground_atom clause) \<Rightarrow> bool" where
  "is_ground_select select\<^sub>G = (\<forall>clause\<^sub>G. \<exists>clause \<theta>. 
        is_ground_clause (clause \<cdot> \<theta>)  \<and> 
        clause\<^sub>G = to_ground_clause (clause \<cdot> \<theta>) \<and> 
        select\<^sub>G clause\<^sub>G = to_ground_clause ((select clause) \<cdot> \<theta>))"

definition select\<^sub>G\<^sub>s where
  "select\<^sub>G\<^sub>s = { ground_select. is_ground_select ground_select }"

definition select\<^sub>G_simple where
  "select\<^sub>G_simple clause = to_ground_clause (select (to_clause clause))"

lemma select\<^sub>G_simple: "is_ground_select select\<^sub>G_simple"
  unfolding is_ground_select_def is_ground_select_def select\<^sub>G_simple_def
  by (metis to_clause_inverse ground_clause_is_ground subst_clause_Var_ident)

lemmas less\<^sub>t_transitive_on = less\<^sub>t_transitive[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>t_asymmetric_on = less\<^sub>t_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_transitive [intro]: "transp (\<prec>\<^sub>t\<^sub>G)"
  using less\<^sub>t\<^sub>G_less\<^sub>t less\<^sub>t_transitive transpE transpI
  by metis

lemmas less\<^sub>t\<^sub>G_transitive_on = less\<^sub>t\<^sub>G_transitive[THEN transp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_asymmetric [intro]: "asymp (\<prec>\<^sub>t\<^sub>G)"
  by (simp add: wfP_imp_asymp less\<^sub>t\<^sub>G_wellfounded)

lemmas less\<^sub>t\<^sub>G_asymmetric_on = less\<^sub>t\<^sub>G_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemmas less\<^sub>t\<^sub>G_total_on = less\<^sub>t\<^sub>G_total[THEN totalp_on_subset, OF subset_UNIV]

lemma less\<^sub>t_less\<^sub>t\<^sub>G: 
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2"
  shows "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<longleftrightarrow> to_ground_term term\<^sub>1 \<prec>\<^sub>t\<^sub>G to_ground_term term\<^sub>2"
  by (simp add: assms less\<^sub>t\<^sub>G_less\<^sub>t)

lemma less\<^sub>t_total_on [intro]: "totalp_on (to_term ` terms\<^sub>G) (\<prec>\<^sub>t)"
  by (smt (verit, best) image_iff less\<^sub>t\<^sub>G_less\<^sub>t totalpD less\<^sub>t\<^sub>G_total_on totalp_on_def)

lemma less\<^sub>t_ground_subst_stability':
  assumes "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"  "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  shows "term\<^sub>1 \<cdot>t \<theta> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<theta>"
  using less\<^sub>t_ground_subst_stability[OF assms]
  unfolding 
    less\<^sub>t\<^sub>G_less\<^sub>t 
    to_ground_term_inverse[OF assms(1)]
    to_ground_term_inverse[OF assms(2)].

lemma select_from_ground_clause1: 
  assumes "is_ground_clause clause" 
  shows "is_ground_clause (select clause)"
  using select_subset sub_ground_clause assms
  by metis

lemma select_from_ground_clause2: 
  assumes "literal \<in># select (to_clause clause)"  
  shows "is_ground_literal literal"
  using assms ground_literal_in_ground_clause(2) select_subset
  by blast

lemma select_from_ground_clause3: 
  assumes "is_ground_clause clause" "literal\<^sub>G \<in># to_ground_clause clause"
  shows "to_literal literal\<^sub>G \<in># clause"
  using assms 
  by (metis to_ground_clause_inverse ground_literal_in_ground_clause(3))

lemmas select_from_ground_clause = 
  select_from_ground_clause1
  select_from_ground_clause2
  select_from_ground_clause3

lemma select_subst1:
  assumes "is_ground_clause (clause \<cdot> \<theta>)"  
  shows "is_ground_clause (select clause \<cdot> \<theta>)" 
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause subst_clause_def)
  
lemma select_subst2: 
  assumes "literal \<in># select clause \<cdot> \<theta>"  
  shows "is_neg literal"
  using assms subst_neg_stable select_negative
  unfolding subst_clause_def
  by auto

lemmas select_subst = select_subst1 select_subst2

abbreviation less_eq\<^sub>t (infix "\<preceq>\<^sub>t" 50) where
  "less_eq\<^sub>t \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

definition less\<^sub>l ::
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less\<^sub>l literal\<^sub>1 literal\<^sub>2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit literal\<^sub>1) (mset_lit literal\<^sub>2)"

abbreviation less_eq\<^sub>l (infix "\<preceq>\<^sub>l" 50) where
  "less_eq\<^sub>l \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less\<^sub>c ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less\<^sub>c \<equiv> multp (\<prec>\<^sub>l)"

abbreviation less_eq\<^sub>c (infix "\<preceq>\<^sub>c" 50) where
  "less_eq\<^sub>c \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

abbreviation is_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_maximal\<^sub>l literal clause \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"

abbreviation is_strictly_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_strictly_maximal\<^sub>l literal clause \<equiv> is_strictly_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"

(* TODO: Is there a more concise way to write all these proofs? *)
lemma less\<^sub>l_transitive [intro]: "transp (\<prec>\<^sub>l)"
  unfolding less\<^sub>l_def 
  using transp_multp[OF less\<^sub>t_transitive]
  by (metis (no_types, lifting) transpE transpI)

lemmas less\<^sub>l_transitive_on = less\<^sub>l_transitive[THEN transp_on_subset, OF subset_UNIV]
                                                            
lemma less\<^sub>l_asymmetric [intro]: "asymp (\<prec>\<^sub>l)"
  unfolding less\<^sub>l_def  multp_eq_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
  using asymp_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
  by (meson asympD asympI)

lemmas less\<^sub>l_asymmetric_on = less\<^sub>l_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemmas is_maximal\<^sub>l_def = is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]

lemmas is_strictly_maximal\<^sub>l_def =
  is_strictly_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]

lemmas is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l =
  is_maximal_in_mset_wrt_if_is_strictly_maximal_in_mset_wrt[OF 
    less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on
  ]

lemma less\<^sub>c_transitive [intro]: "transp (\<prec>\<^sub>c)"
  using transp_multp[OF less\<^sub>l_transitive].

lemmas less\<^sub>c_transitive_on = less\<^sub>c_transitive[THEN transp_on_subset, OF subset_UNIV]

lemma less\<^sub>c_asymmetric [intro]: "asymp (\<prec>\<^sub>c)"
  using asymp_multp[OF less\<^sub>l_asymmetric less\<^sub>l_transitive].

lemmas less\<^sub>c_asymmetric_on = less\<^sub>c_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>l_ground_subst_stability: 
  assumes 
    "is_ground_literal (literal \<cdot>l \<theta>)" 
    "is_ground_literal (literal' \<cdot>l \<theta>)" 
    "literal \<prec>\<^sub>l literal'"
  shows
    "literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
  using 
      less\<^sub>t_ground_subst_stability'[OF assms(1, 2)[THEN ground_term_in_ground_literal_subst]]
      multp_map_strong[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]  
      assms(3)
      mset_mset_lit_subst
  unfolding less\<^sub>l_def
  by metis

lemma less\<^sub>c_ground_subst_stability: 
  assumes 
    "is_ground_clause (clause \<cdot> \<theta>)" 
    "is_ground_clause (clause' \<cdot> \<theta>)" 
    "clause \<prec>\<^sub>c clause'"
  shows
    "clause \<cdot> \<theta> \<prec>\<^sub>c clause' \<cdot> \<theta>"
  using 
      less\<^sub>l_ground_subst_stability[OF assms(1, 2)[THEN ground_literal_in_ground_clause_subst]]
      multp_map_strong[OF less\<^sub>l_asymmetric less\<^sub>l_transitive]  
      assms(3)
  unfolding subst_clause_def
  by simp

lemma less_eq\<^sub>t_ground_subst_stability:
  assumes "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"  "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2"
  shows "term\<^sub>1 \<cdot>t \<theta> \<preceq>\<^sub>t term\<^sub>2 \<cdot>t \<theta>"
  using less\<^sub>t_ground_subst_stability'[OF assms(1, 2)] assms(3)
  by auto

definition clause_groundings ::
  "('f, 'v) atom clause \<Rightarrow> 'f ground_atom clause set" where
  "clause_groundings clause = { to_ground_clause (clause \<cdot> \<theta>) | \<theta>. is_ground_clause (clause \<cdot> \<theta>) }"

definition clause_liftings where
   "clause_liftings clause\<^sub>G = { (clause, \<theta>)  | clause \<theta>. clause \<cdot> \<theta> = to_clause clause\<^sub>G }"

(* 
 "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
      \<and> premise \<in> premises"
*)

find_consts "'a set \<Rightarrow> 'a option"

definition select\<^sub>G_simple2 where
  "select\<^sub>G_simple2 clause\<^sub>G clauses = 
    (if clause\<^sub>G \<in> \<Union> (clause_groundings ` clauses) 
     then to_ground_clause (select (to_clause clause\<^sub>G))
     else to_ground_clause (select (to_clause clause\<^sub>G)))" 

(* TODO: new section *)

inductive equality_resolution :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  equality_resolutionI: 
   "premise = add_mset literal premise' \<Longrightarrow>
    literal = term !\<approx> term' \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term, term' }} \<Longrightarrow>
    select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<or> literal \<in># select premise \<Longrightarrow>
    conclusion = premise' \<cdot> \<mu> \<Longrightarrow>
    equality_resolution premise conclusion"

inductive equality_factoring :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  equality_factoringI: "
    premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise') \<Longrightarrow>
    literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1' \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    select premise = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term\<^sub>1, term\<^sub>2 }} \<Longrightarrow>
    conclusion = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<mu> \<Longrightarrow>
    equality_factoring premise conclusion"

inductive superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  superpositionI: 
   "term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1' \<Longrightarrow>
    premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    literal\<^sub>1 = \<P> (Upair context\<^sub>1\<langle>term\<^sub>1\<rangle> term\<^sub>1') \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    \<not> is_Var term\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    (\<P> = Pos 
      \<and> select premise\<^sub>1 = {#} 
      \<and> is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg 
      \<and> (select premise\<^sub>1 = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
          \<or> literal\<^sub>1 \<in># select premise\<^sub>1)) \<Longrightarrow>
    select premise\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    conclusion = add_mset (\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition premise\<^sub>1 premise\<^sub>2 conclusion"

abbreviation equality_factoring_inferences where
  "equality_factoring_inferences \<equiv> 
    { Infer [premise] conclusion | premise conclusion. equality_factoring premise conclusion }"

abbreviation equality_resolution_inferences where
  "equality_resolution_inferences \<equiv> 
    { Infer [premise] conclusion | premise conclusion. equality_resolution premise conclusion }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [premise\<^sub>1, premise\<^sub>2] conclusion 
    | premise\<^sub>1 premise\<^sub>2 conclusion. superposition premise\<^sub>1 premise\<^sub>2 conclusion }"

definition inferences :: "('f, 'v) atom clause inference set" where
  "inferences \<equiv> 
    superposition_inferences \<union> equality_resolution_inferences \<union> equality_factoring_inferences"

abbreviation bottom\<^sub>F :: "('f, 'v) atom clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {{#}}"

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  pos_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_clause (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases rule: pos_superposition.cases)
  case pos_superpositionI
  then show ?thesis
    using superpositionI
    by fast
qed

inductive neg_superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  neg_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_clause (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = Neg (Upair s\<^sub>1\<langle>u\<^sub>1\<rangle> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>  (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by fast
qed

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>1 P\<^sub>2 C \<longleftrightarrow> pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
proof (rule iffI)
  assume "superposition P\<^sub>1 P\<^sub>2 C"
  thus "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  proof (cases P\<^sub>1 P\<^sub>2 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
    then show ?thesis      
      using pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      using neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      by blast
  qed
next
  assume "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  thus "superposition P\<^sub>1 P\<^sub>2 C"
    using superposition_if_neg_superposition superposition_if_pos_superposition by metis
qed

abbreviation true_clause :: 
  "'f ground_atom interp \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>C" 50)  where
  "I \<TTurnstile>\<^sub>C C \<equiv> \<forall>\<theta>. term_subst.is_ground_subst \<theta> \<longrightarrow> I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"

abbreviation true_clauses :: 
  "'f ground_atom interp \<Rightarrow> ('f, 'v) atom clause set \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>C\<^sub>s" 50) where
  "I \<TTurnstile>\<^sub>C\<^sub>s \<C> \<equiv> \<forall>C\<in> \<C>. I \<TTurnstile>\<^sub>C C"

definition entails\<^sub>F :: 
  "('f, 'v) atom clause set \<Rightarrow> ('f, 'v) atom clause set \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>F" 50) where
  "entails\<^sub>F N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: 'f gterm rel). 
    refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow> compatible_with_gctxt I \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>\<^sub>C\<^sub>s N\<^sub>1 \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>\<^sub>C\<^sub>s N\<^sub>2)"

end

locale first_order_superposition_calculus_with_grounding =
  first_order_superposition_calculus +
  fixes select\<^sub>G 
  assumes select\<^sub>G: "is_ground_select select\<^sub>G"
begin

lemma select\<^sub>G_subset: "select\<^sub>G clause \<subseteq># clause"
  using select\<^sub>G 
  unfolding is_ground_select_def
  by (metis select_subset to_ground_clause_def image_mset_subseteq_mono subst_clause_def)

lemma select\<^sub>G_negative:
  assumes "literal\<^sub>G \<in># select\<^sub>G clause\<^sub>G"
  shows "is_neg literal\<^sub>G"
proof -
  obtain clause \<theta> where 
    is_ground: "is_ground_clause (clause \<cdot> \<theta>)" and
    select\<^sub>G: "select\<^sub>G clause\<^sub>G = to_ground_clause (select clause \<cdot> \<theta>)"
    using select\<^sub>G
    unfolding is_ground_select_def
    by blast

  show ?thesis
    using 
      select_from_ground_clause(3)[
          OF select_subst(1)[OF is_ground] assms[unfolded select\<^sub>G], 
          THEN select_subst(2)
      ]
    unfolding to_literal_def
    by simp
qed

lemma ground: "ground_superposition_calculus (\<prec>\<^sub>t\<^sub>G) select\<^sub>G"
  apply(unfold_locales)
  by(auto simp: select\<^sub>G_subset select\<^sub>G_negative ground_critical_pair_theorem)

sublocale ground: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  by(rule ground)

notation ground.less_lit (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation ground.less_cls (infix "\<prec>\<^sub>c\<^sub>G" 50)

notation ground.lesseq_trm (infix "\<preceq>\<^sub>t\<^sub>G" 50)
notation ground.lesseq_lit (infix "\<preceq>\<^sub>l\<^sub>G" 50)
notation ground.lesseq_cls (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemma not_less_eq\<^sub>t\<^sub>G: "\<not> term\<^sub>G\<^sub>2 \<preceq>\<^sub>t\<^sub>G term\<^sub>G\<^sub>1 \<longleftrightarrow> term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2"
  using asympD[OF less\<^sub>t\<^sub>G_asymmetric] totalpD[OF less\<^sub>t\<^sub>G_total]
  by blast

lemma less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G:
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2" 
  shows "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2 \<longleftrightarrow> to_ground_term term\<^sub>1 \<preceq>\<^sub>t\<^sub>G to_ground_term term\<^sub>2"
  unfolding reflclp_iff less\<^sub>t_less\<^sub>t\<^sub>G[OF assms]
  using assms[THEN to_ground_term_inverse]
  by auto

lemma less_eq\<^sub>t\<^sub>G_less_eq\<^sub>t:
   "term\<^sub>G\<^sub>1 \<preceq>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<longleftrightarrow> to_term term\<^sub>G\<^sub>1 \<preceq>\<^sub>t to_term term\<^sub>G\<^sub>2"
  unfolding less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF ground_term_is_ground ground_term_is_ground] to_term_inverse
  ..

lemma not_less_eq\<^sub>t: 
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2"
  shows "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1 \<longleftrightarrow> term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  unfolding less\<^sub>t_less\<^sub>t\<^sub>G[OF assms] less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>t\<^sub>G
  ..

lemma less\<^sub>l\<^sub>G_less\<^sub>l: "literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> to_literal literal\<^sub>G\<^sub>1 \<prec>\<^sub>l to_literal literal\<^sub>G\<^sub>2"
  unfolding less\<^sub>l_def ground.less_lit_def less\<^sub>t\<^sub>G_less\<^sub>t mset_to_literal
  using
     multp_image_mset_image_msetI[OF _ less\<^sub>t_transitive]
     multp_image_mset_image_msetD[OF _ less\<^sub>t_transitive_on to_term_inj]
   by blast

lemma less\<^sub>l_less\<^sub>l\<^sub>G: 
  assumes "is_ground_literal literal\<^sub>1" "is_ground_literal literal\<^sub>2" 
  shows "literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2 \<longleftrightarrow> to_ground_literal literal\<^sub>1 \<prec>\<^sub>l\<^sub>G to_ground_literal literal\<^sub>2"
  using assms
  by (simp add: less\<^sub>l\<^sub>G_less\<^sub>l)

lemma less\<^sub>l_total_on [intro]: "totalp_on (to_literal ` literals\<^sub>G) (\<prec>\<^sub>l)"
  by (smt (verit, best) image_iff less\<^sub>l\<^sub>G_less\<^sub>l totalpD ground.less\<^sub>l\<^sub>G_total_on totalp_on_def)

lemma less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G:
  assumes "is_ground_literal literal\<^sub>1" and "is_ground_literal literal\<^sub>2" 
  shows "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2 \<longleftrightarrow> to_ground_literal literal\<^sub>1 \<preceq>\<^sub>l\<^sub>G to_ground_literal literal\<^sub>2"
  unfolding reflclp_iff less\<^sub>l_less\<^sub>l\<^sub>G[OF assms]
  using assms[THEN to_ground_literal_inverse]
  by auto

lemma less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l:
   "literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> to_literal literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l to_literal literal\<^sub>G\<^sub>2"
  unfolding 
    less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF ground_literal_is_ground ground_literal_is_ground] 
    to_literal_inverse
  ..

lemma maximal_lit_in_clause:
  assumes "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G"
  shows "literal\<^sub>G \<in># clause\<^sub>G"
  using assms 
  unfolding ground.is_maximal_lit_def
  by(rule conjunct1)

lemma maximal\<^sub>l_in_clause:
  assumes "is_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms 
  unfolding is_maximal\<^sub>l_def
  by(rule conjunct1)

lemma strictly_maximal\<^sub>l_in_clause:
  assumes "is_strictly_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms 
  unfolding is_strictly_maximal\<^sub>l_def
  by(rule conjunct1)

lemma is_maximal_lit_iff_is_maximal\<^sub>l: 
  "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G \<longleftrightarrow> is_maximal\<^sub>l (to_literal literal\<^sub>G) (to_clause clause\<^sub>G)"
   unfolding 
    is_maximal\<^sub>l_def
    ground.is_maximal_lit_def
    ground_literal_in_ground_clause(3)[symmetric]
   using 
     less\<^sub>l_less\<^sub>l\<^sub>G[OF ground_literal_is_ground ground_literal_in_ground_clause(2)] 
     ground_literal_in_ground_clause(2, 3)
   by (metis to_ground_literal_inverse to_literal_inverse)

lemmas less\<^sub>l_total_on_set_mset =
  less\<^sub>l_total_on[THEN totalp_on_subset, OF set_mset_to_clause_to_literal[THEN equalityD1]]

lemma is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l:
  "ground.is_strictly_maximal_lit literal\<^sub>G clause\<^sub>G 
    \<longleftrightarrow> is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G) (to_clause clause\<^sub>G)"
  unfolding 
    is_strictly_maximal_in_mset_wrt_iff_is_greatest_in_mset_wrt[OF 
      ground.less\<^sub>l\<^sub>G_transitive_on ground.less\<^sub>l\<^sub>G_asymmetric_on ground.less\<^sub>l\<^sub>G_total_on, symmetric
    ]
    ground.is_strictly_maximal_lit_def
    is_strictly_maximal\<^sub>l_def
    ground_literal_in_ground_clause(3)[symmetric]
    remove1_mset_to_literal
    ground_literal_in_ground_clause(4)
    less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l
  ..
 
lemma not_less_eq\<^sub>l\<^sub>G: "\<not> literal\<^sub>G\<^sub>2 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>1 \<longleftrightarrow> literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2"
  using asympD[OF ground.less\<^sub>l\<^sub>G_asymmetric_on] totalpD[OF ground.less\<^sub>l\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>l: 
  assumes "is_ground_literal literal\<^sub>1" and "is_ground_literal literal\<^sub>2"
  shows "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1 \<longleftrightarrow> literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2"
  unfolding less\<^sub>l_less\<^sub>l\<^sub>G[OF assms] less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>l\<^sub>G
  ..

lemma less\<^sub>c\<^sub>G_less\<^sub>c: 
  "clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> to_clause clause\<^sub>G\<^sub>1 \<prec>\<^sub>c to_clause clause\<^sub>G\<^sub>2"
  using
     multp_image_mset_image_msetI[OF _ less\<^sub>l_transitive]
     multp_image_mset_image_msetD[OF _ less\<^sub>l_transitive to_literal_inj]
  unfolding less\<^sub>l\<^sub>G_less\<^sub>l to_clause_def
  by blast

lemma less\<^sub>c_less\<^sub>c\<^sub>G: 
  assumes "is_ground_clause clause\<^sub>1" "is_ground_clause clause\<^sub>2"
  shows "clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2 \<longleftrightarrow> to_ground_clause clause\<^sub>1 \<prec>\<^sub>c\<^sub>G  to_ground_clause clause\<^sub>2"
  using assms
  by (simp add: less\<^sub>c\<^sub>G_less\<^sub>c)

lemma less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G:
  assumes "is_ground_clause clause\<^sub>1" and "is_ground_clause clause\<^sub>2" 
  shows "clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2 \<longleftrightarrow> to_ground_clause clause\<^sub>1 \<preceq>\<^sub>c\<^sub>G to_ground_clause clause\<^sub>2"
  unfolding reflclp_iff less\<^sub>c_less\<^sub>c\<^sub>G[OF assms]
  using assms[THEN to_ground_clause_inverse]
  by fastforce

lemma less_eq\<^sub>c\<^sub>G_less_eq\<^sub>c:
   "clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> to_clause clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c to_clause clause\<^sub>G\<^sub>2"
  unfolding less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF ground_clause_is_ground ground_clause_is_ground] to_clause_inverse
  ..

lemma less\<^sub>c_total_on: "totalp_on (to_clause ` clauses) (\<prec>\<^sub>c)"
  by (smt ground.totalp_less_cls image_iff less\<^sub>c\<^sub>G_less\<^sub>c totalpD totalp_onI) 

lemma not_less_eq\<^sub>c\<^sub>G: "\<not> clause\<^sub>G\<^sub>2 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>1 \<longleftrightarrow> clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2"
  using asympD[OF ground.less\<^sub>c\<^sub>G_asymmetric_on] totalpD[OF ground.less\<^sub>c\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>c: 
  assumes "is_ground_clause clause\<^sub>1" and "is_ground_clause clause\<^sub>2"
  shows "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1 \<longleftrightarrow> clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2"
  unfolding less\<^sub>c_less\<^sub>c\<^sub>G[OF assms] less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>c\<^sub>G
  ..

lemma less\<^sub>t_less_eq\<^sub>t_ground_subst_stability: assumes 
  "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)"
  "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"
  "term\<^sub>1 \<cdot>t \<theta> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<theta>"
shows
  "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1"
proof
  assume assumption: "term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1"

  have "term\<^sub>2 \<cdot>t \<theta> \<preceq>\<^sub>t term\<^sub>1 \<cdot>t \<theta>"
    using less_eq\<^sub>t_ground_subst_stability[OF 
            assms(2, 1)
            assumption
           ].

  then show False 
    using assms(3)
    unfolding not_less_eq\<^sub>t[OF assms(1, 2), symmetric]
    by blast
qed

lemma less_eq\<^sub>l_ground_subst_stability:
  assumes   
    "is_ground_literal (literal\<^sub>1 \<cdot>l \<theta>)" 
    "is_ground_literal (literal\<^sub>2 \<cdot>l \<theta>)"  
    "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2"
  shows "literal\<^sub>1 \<cdot>l \<theta> \<preceq>\<^sub>l literal\<^sub>2 \<cdot>l \<theta>"
  using less\<^sub>l_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>l_less_eq\<^sub>l_ground_subst_stability: assumes 
  "is_ground_literal (literal\<^sub>1 \<cdot>l \<theta>)"
  "is_ground_literal (literal\<^sub>2 \<cdot>l \<theta>)"
  "literal\<^sub>1 \<cdot>l \<theta> \<prec>\<^sub>l literal\<^sub>2 \<cdot>l \<theta>"
shows
  "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1"
  by (meson assms less_eq\<^sub>l_ground_subst_stability not_less_eq\<^sub>l)

lemma less_eq\<^sub>c_ground_subst_stability:
  assumes   
    "is_ground_clause (clause\<^sub>1 \<cdot> \<theta>)" 
    "is_ground_clause (clause\<^sub>2 \<cdot> \<theta>)"  
    "clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2"
  shows "clause\<^sub>1 \<cdot> \<theta> \<preceq>\<^sub>c clause\<^sub>2 \<cdot> \<theta>"
  using less\<^sub>c_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>c_less_eq\<^sub>c_ground_subst_stability: assumes 
  "is_ground_clause (clause\<^sub>1 \<cdot> \<theta>)"
  "is_ground_clause (clause\<^sub>2 \<cdot> \<theta>)"
  "clause\<^sub>1 \<cdot> \<theta> \<prec>\<^sub>c clause\<^sub>2 \<cdot> \<theta>"
shows
  "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1"
  by (meson assms less_eq\<^sub>c_ground_subst_stability not_less_eq\<^sub>c)
  
lemma is_maximal\<^sub>l_ground_subst_stability:
  assumes 
    clause_not_empty: "clause \<noteq> {#}" and
    clause_grounding: "is_ground_clause (clause \<cdot> \<theta>)" 
  obtains literal
  where "is_maximal\<^sub>l literal clause \<and> is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
proof-
  assume assumption: 
    "\<And>literal. is_maximal\<^sub>l literal clause \<and> is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>) \<Longrightarrow> thesis"

  from clause_not_empty 
  have clause_grounding_not_empty: "clause \<cdot> \<theta> \<noteq> {#}"
    unfolding subst_clause_def
    by simp

  obtain literal where literal: "literal \<in># clause" "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)" 
    using
      ex_maximal_in_mset_wrt[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on clause_grounding_not_empty]  
      maximal\<^sub>l_in_clause
    unfolding subst_clause_def
    by force

  from literal(2) 
  have no_bigger_than_literal: 
    "\<forall>literal' \<in># clause \<cdot> \<theta>. literal' \<noteq> literal \<cdot>l \<theta> \<longrightarrow> \<not> literal \<cdot>l \<theta> \<prec>\<^sub>l literal'"
    unfolding is_maximal\<^sub>l_def
    by simp

  show ?thesis
  proof(cases "is_maximal\<^sub>l literal clause")
    case True
    with literal assumption show ?thesis
      by auto
  next
    case False
    then obtain literal' where literal': "literal' \<in># clause"  "literal \<prec>\<^sub>l literal'" 
      unfolding is_maximal\<^sub>l_def
      using literal(1)
      by blast 

    note literals_in_clause = literal(1) literal'(1)
    note literals_grounding = literals_in_clause[THEN 
        ground_literal_in_ground_clause_subst[OF clause_grounding]
      ]

    have "literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
      using less\<^sub>l_ground_subst_stability[OF literals_grounding literal'(2)].
   
    then have False
     using 
       no_bigger_than_literal
       literal_in_clause_subst[OF literal'(1)] 
     by (metis asymp_onD less\<^sub>l_asymmetric_on)
       
    then show ?thesis..
  qed
qed

lemma is_maximal\<^sub>l_ground_subst_stability':
  assumes 
   "literal \<in># clause"
   "is_ground_clause (clause \<cdot> \<theta>)"
   "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
 shows 
   "is_maximal\<^sub>l literal clause"
proof(rule ccontr)
  assume "\<not> is_maximal\<^sub>l literal clause"
  
  then obtain literal' where literal':
      "literal \<prec>\<^sub>l literal'" 
      "literal' \<in># clause "
  using assms(1)
  unfolding is_maximal\<^sub>l_def
  by blast

  then have literal'_grounding: "is_ground_literal (literal' \<cdot>l \<theta>)"
    using assms(2) ground_literal_in_ground_clause_subst by blast

  have literal_grounding: "is_ground_literal (literal \<cdot>l \<theta>)"
    using assms(1) assms(2) ground_literal_in_ground_clause_subst by blast

  have literal_\<theta>_in_premise: "literal' \<cdot>l \<theta> \<in># clause \<cdot> \<theta>"
    using literal_in_clause_subst[OF literal'(2)]
    by simp
     
  have "literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
    using less\<^sub>l_ground_subst_stability[OF literal_grounding literal'_grounding literal'(1)].
  
  then have "\<not> is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
    using literal_\<theta>_in_premise 
    unfolding is_maximal\<^sub>l_def literal_subst_compose
    by (metis asympD less\<^sub>l_asymmetric)
  
  then show False
    using assms(3)
    by blast
qed

lemma unique_maximal_in_ground_clause:
  assumes
    "is_ground_clause clause" 
    "is_maximal\<^sub>l literal clause"
    "is_maximal\<^sub>l literal' clause"
  shows
    "literal = literal'"
  using assms(2, 3)
  unfolding is_maximal\<^sub>l_def
  by (metis assms(1) less\<^sub>l_total_on_set_mset to_ground_clause_inverse totalp_onD)

lemma unique_strictly_maximal_in_ground_clause:
  assumes
    "is_ground_clause clause" 
    "is_strictly_maximal\<^sub>l literal clause"
    "is_strictly_maximal\<^sub>l literal' clause"
  shows
    "literal = literal'"
proof- 
  note are_maximal\<^sub>l =assms(2, 3)[THEN is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l]
   
  show ?thesis
    using unique_maximal_in_ground_clause[OF assms(1) are_maximal\<^sub>l].
qed

lemma is_strictly_maximal\<^sub>l_ground_subst_stability:
  assumes 
   clause_grounding: "is_ground_clause (clause \<cdot> \<theta>)" and
   ground_strictly_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>G (clause \<cdot> \<theta>)"
 obtains literal where 
   "is_strictly_maximal\<^sub>l literal clause" "literal \<cdot>l \<theta> = literal\<^sub>G"
proof-
  assume assumption: "\<And>literal. 
    is_strictly_maximal\<^sub>l literal clause \<Longrightarrow> literal \<cdot>l \<theta> = literal\<^sub>G \<Longrightarrow> thesis"

  have clause_grounding_not_empty: "clause \<cdot> \<theta> \<noteq> {#}"
    using ground_strictly_maximal
    unfolding is_strictly_maximal\<^sub>l_def
    by fastforce

  have literal\<^sub>G_in_clause_grounding: "literal\<^sub>G \<in># clause \<cdot> \<theta>"
    using ground_strictly_maximal is_strictly_maximal\<^sub>l_def by blast

  obtain literal where literal: "literal \<in># clause" "literal \<cdot>l \<theta> = literal\<^sub>G"
    by (metis imageE literal\<^sub>G_in_clause_grounding multiset.set_map subst_clause_def)

  show ?thesis
  proof(cases "is_strictly_maximal\<^sub>l literal clause")
    case True
    then show ?thesis
      using assumption
      using literal(2) by blast
  next
    case False

    then obtain literal' where literal': 
      "literal' \<in># clause - {# literal #}"  
      "literal \<preceq>\<^sub>l literal'" 
      unfolding is_strictly_maximal\<^sub>l_def
      using literal(1)
      by blast 

    note literal_grounding = 
      ground_literal_in_ground_clause_subst[OF clause_grounding literal(1)]

    have literal'_grounding: "is_ground_literal (literal' \<cdot>l \<theta>)"
      using literal'(1) clause_grounding
      by (meson ground_literal_in_ground_clause_subst in_diffD)

    have "literal \<cdot>l \<theta> \<preceq>\<^sub>l literal' \<cdot>l \<theta>"
      using less_eq\<^sub>l_ground_subst_stability[OF literal_grounding literal'_grounding literal'(2)].

    then have False
      using literal_in_clause_subst[OF literal'(1)]  ground_strictly_maximal 
      unfolding 
        is_strictly_maximal\<^sub>l_def 
        literal(2)[symmetric]
        subst_clause_remove1_mset[OF literal(1)]
      by blast
   
    then show ?thesis..
  qed
qed

lemma is_strictly_maximal\<^sub>l_ground_subst_stability':
  assumes 
   "literal \<in># clause"
   "is_ground_clause (clause \<cdot> \<theta>)"
   "is_strictly_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
 shows 
   "is_strictly_maximal\<^sub>l literal clause"
  (* TODO: *)
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) in_diffD is_maximal\<^sub>l_def is_maximal\<^sub>l_ground_subst_stability' is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l is_strictly_maximal\<^sub>l_def literal_in_clause_subst reflclp_iff subst_clause_remove1_mset)

end

definition (in first_order_superposition_calculus) inference_groundings
  where "is_ground_select select\<^sub>G \<Longrightarrow> inference_groundings select\<^sub>G inference = 
  { ground_inference | ground_inference \<theta> \<rho>\<^sub>1 \<rho>\<^sub>2.
    (case inference of 
        Infer [premise] conclusion \<Rightarrow>
          is_ground_clause (premise \<cdot> \<theta>) 
        \<and> is_ground_clause (conclusion \<cdot> \<theta>)
        \<and> ground_inference = 
            Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion \<cdot> \<theta>))
      | Infer [premise\<^sub>1, premise\<^sub>2] conclusion \<Rightarrow> 
          term_subst.is_renaming \<rho>\<^sub>1
        \<and> term_subst.is_renaming \<rho>\<^sub>1
        \<and> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}
        \<and> is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) 
        \<and> is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) 
        \<and> is_ground_clause (conclusion \<cdot> \<theta>)
        \<and> ground_inference = 
            Infer 
              [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] 
              (to_ground_clause (conclusion \<cdot> \<theta>))
      | _ \<Rightarrow> False
     )
  \<and> ground_inference \<in> ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G) select\<^sub>G
  \<and> inference \<in> inferences
}" 

abbreviation some where
  "some f \<equiv> Some \<circ> f"

definition Prec_F :: 
  "'f ground_atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" 
  where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

lemma (in first_order_superposition_calculus_with_grounding) test: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings select\<^sub>G \<iota>"
  shows "concl_of \<iota>\<^sub>G \<in> clause_groundings (concl_of \<iota>)"
proof-
  obtain premises\<^sub>G conlcusion\<^sub>G where
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer premises\<^sub>G conlcusion\<^sub>G"
    using Calculus.inference.exhaust by blast

  obtain "premises" conlcusion where
    \<iota>: "\<iota> = Infer premises conlcusion"
    using Calculus.inference.exhaust by blast

  obtain \<theta> where 
    "is_ground_clause (conlcusion \<cdot> \<theta>)"
    "conlcusion\<^sub>G = to_ground_clause (conlcusion \<cdot> \<theta>)"
    using assms
    unfolding inference_groundings_def[OF select\<^sub>G] \<iota> \<iota>\<^sub>G Calculus.inference.case
    (* TODO: *)
    apply auto
    by (smt (z3) Calculus.inference.inject list.simps(4) list.simps(5) list_4_cases)

  then show ?thesis
    unfolding \<iota> \<iota>\<^sub>G clause_groundings_def
    by auto
qed  

lemma (in first_order_superposition_calculus_with_grounding) test_u: 
  "\<iota>' \<in> inference_groundings select\<^sub>G \<iota> \<Longrightarrow>  \<iota>' \<in> ground.Red_I (clause_groundings (concl_of \<iota>))"
proof-
  assume a2: "\<iota>' \<in> inference_groundings select\<^sub>G \<iota>"


  moreover then have "\<iota>' \<in> ground.G_Inf"
    unfolding inference_groundings_def[OF select\<^sub>G]
    by blast

  moreover have "concl_of \<iota>' \<in> clause_groundings (concl_of \<iota>)"
    using a2 test
    by auto

  ultimately show "\<iota>' \<in> ground.Red_I (clause_groundings (concl_of \<iota>))"
    using  ground.Red_I_of_Inf_to_N
    by blast
qed

sublocale first_order_superposition_calculus \<subseteq>
  lifting_intersection
    inferences      
    "{{#}}"
    select\<^sub>G\<^sub>s
    "ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G)"               
    "\<lambda>_. ground_superposition_calculus.G_entails" 
    "ground_superposition_calculus.Red_I' (\<prec>\<^sub>t\<^sub>G)" 
    "\<lambda>_. ground_superposition_calculus.Red_F'(\<prec>\<^sub>t\<^sub>G)" 
    "\<bottom>\<^sub>F"
    "\<lambda>_. clause_groundings" 
    "\<lambda>select\<^sub>G. some (inference_groundings select\<^sub>G)"
    Prec_F
proof(unfold_locales; (intro ballI)?)
  show "select\<^sub>G\<^sub>s \<noteq> {}"
    using select\<^sub>G_simple
    unfolding select\<^sub>G\<^sub>s_def 
    by blast
next 
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
  then interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G
    apply unfold_locales
    by(simp add: select\<^sub>G\<^sub>s_def)

  show "consequence_relation ground.G_Bot ground.G_entails"
    using ground.consequence_relation_axioms.
next
   fix select\<^sub>G
   assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
  then interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G
    apply unfold_locales
    by(simp add: select\<^sub>G\<^sub>s_def)

  show "tiebreaker_lifting
          \<bottom>\<^sub>F inferences
          ground.G_Bot
          ground.G_entails
          ground.G_Inf
          ground.Red_I
          ground.Red_F
          clause_groundings (some (inference_groundings select\<^sub>G))
          Prec_F"
  proof
    show "\<bottom>\<^sub>F \<noteq> {}"
      by simp
  next
    fix bottom
    assume "bottom \<in> \<bottom>\<^sub>F"

    then show "clause_groundings bottom \<noteq> {}"
      unfolding clause_groundings_def 
      by simp
  next
    fix bottom
    assume "bottom \<in> \<bottom>\<^sub>F"
    then show "clause_groundings bottom \<subseteq> ground.G_Bot"
      unfolding clause_groundings_def
      by simp
  next
    fix clause
    show "clause_groundings clause \<inter> ground.G_Bot \<noteq> {} \<longrightarrow> clause \<in> \<bottom>\<^sub>F"
      unfolding clause_groundings_def to_ground_clause_def subst_clause_def
      by simp
  next
    fix \<iota>   
    show "the (some (inference_groundings select\<^sub>G) \<iota>) 
                \<subseteq> ground.Red_I' (clause_groundings (concl_of \<iota>))"
      using test_u
      by auto
  next
    show "\<And>g. po_on (Prec_F g) UNIV"
      unfolding Prec_F_def po_on_def irreflp_on_def
      by simp
  next
    show "\<And>g. wfp_on (Prec_F g) UNIV"
      unfolding Prec_F_def
      by simp
  qed
qed

abbreviation (in ground_superposition_calculus) equality_resolution_inferences where
  "equality_resolution_inferences \<equiv>  {Infer [P] C | P C. ground_eq_resolution P C}"

abbreviation (in ground_superposition_calculus) equality_factoring_inferences where
  "equality_factoring_inferences \<equiv>  {Infer [P] C | P C.  ground_eq_factoring P C}"

(* TODO: fix P2 P1 order *)
abbreviation (in ground_superposition_calculus) superposition_inferences where
  "superposition_inferences \<equiv>  {Infer [P2, P1] C | P1 P2 C. ground_superposition P1 P2 C}"

abbreviation (in lifting_intersection) ground_instances ::
  "'q \<Rightarrow> 'f inference set \<Rightarrow> 'g inference set" where
  "ground_instances q inferences \<equiv> { ground_inference. 
    ground_inference \<in> Inf_G_q q \<and> ground_inference \<in>  \<Union> (Option.these (\<G>_I_q q ` inferences))
  }"

(* TODO: correct? *)
abbreviation (in lifting_intersection) redundant_inferences where
  "redundant_inferences q N \<equiv>  ground_instances q (Red_I_\<G>_q q (concl_of ` N))"


lemma (in first_order_superposition_calculus_with_grounding) equality_resolution_ground_instance:
  assumes 
    premise_grounding [intro]: "is_ground_clause (premise \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>" and
    ground_eq_resolution: 
      "ground.ground_eq_resolution
          (to_ground_clause (premise \<cdot> \<theta>)) 
          (to_ground_clause (conclusion \<cdot> \<theta>))"
  (* TODO: *)
  shows " \<exists>conclusion'. equality_resolution premise conclusion'
            \<and> Infer [to_ground_clause (premise \<cdot> \<theta>)]  (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> inference_groundings select\<^sub>G (Infer [premise] conclusion')
            \<and> conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
  using ground_eq_resolution
proof(cases "to_ground_clause (premise \<cdot> \<theta>)" "to_ground_clause (conclusion \<cdot> \<theta>)" 
      rule: ground.ground_eq_resolution.cases)
  case (ground_eq_resolutionI literal\<^sub>G term\<^sub>G)

  have premise_not_empty: "premise \<noteq> {#}"
    using 
      ground_eq_resolutionI(1)
      empty_not_add_mset
      clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have "premise \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G (to_ground_clause (conclusion \<cdot> \<theta>)))"
    using 
       ground_eq_resolutionI(1)[THEN arg_cong, of to_clause]
       to_ground_clause_inverse[OF premise_grounding]
    by metis

  also have "... = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<theta>)"
    unfolding to_clause_add_mset
    by (simp add: conclusion_grounding)

  finally have premise': "premise \<cdot> \<theta> = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<theta>)".

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>)) \<noteq> {#}"

  obtain max_literal where max_literal: 
      "is_maximal\<^sub>l max_literal premise" 
      "is_maximal\<^sub>l (max_literal \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast
   
  moreover then have "max_literal \<in># premise"
    using maximal\<^sub>l_in_clause by fastforce

  moreover have max_literal_literal\<^sub>G: 
      "max_literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)"
  if ?select\<^sub>G_empty
    using ground_eq_resolutionI(3) max_literal unique_maximal_in_ground_clause
    unfolding ground_eq_resolutionI(2) is_maximal_lit_iff_is_maximal\<^sub>l
    by (metis empty_not_add_mset multi_member_split premise_grounding that to_ground_clause_inverse)

  moreover obtain selected_literal where 
    "selected_literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    "selected_literal \<in># select premise" 
  if ?select\<^sub>G_not_empty
    using ground_eq_resolutionI(3) select
    unfolding ground_eq_resolutionI(2)
    by (smt image_iff multiset.set_map subst_clause_def ground_literal_in_ground_clause(3))
   
  moreover then have "?select\<^sub>G_not_empty \<Longrightarrow> selected_literal \<in># premise"
    by (meson mset_subset_eqD select_subset)

  ultimately obtain literal where
    literal: "literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    literal_in_premise: "literal \<in># premise" and
    literal_selected: "?select\<^sub>G_not_empty \<Longrightarrow> literal \<in># select premise" and
    literal_max: "?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal premise"
    by blast    

  have literal_grounding: "is_ground_literal (literal \<cdot>l \<theta>)"
    using literal ground_literal_is_ground
    by simp

  from literal obtain "term" term' where terms: "literal = term !\<approx> term'"
    using subst_polarity_stable to_literal_polarity_stable
    by (metis literal.collapse(2) literal.disc(2) uprod_exhaust)

  have term_term': "term \<cdot>t \<theta> = term' \<cdot>t \<theta>"
    using literal
    unfolding terms subst_literal(2) subst_atom_def to_literal_def to_atom_def
    by simp

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term, term'}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  have literal\<^sub>G: 
    "to_literal literal\<^sub>G = (term !\<approx> term') \<cdot>l \<theta>" 
    "literal\<^sub>G = to_ground_literal ((term !\<approx> term') \<cdot>l \<theta>)"
    using literal ground_eq_resolutionI(2)  terms 
    by simp_all

  obtain conclusion' where conclusion': "premise = add_mset literal conclusion'"
    using multi_member_split[OF literal_in_premise]
    by blast

  have conclusion'_\<theta>: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using premise'
    unfolding conclusion' ground_eq_resolutionI(2) literal[symmetric] subst_clause_add_mset
    by simp
    
  have equality_resolution: "equality_resolution premise (conclusion' \<cdot> \<sigma>)"
  proof (rule equality_resolutionI)
     show "premise = add_mset literal conclusion'"
       using conclusion'.
  next 
    show "literal = term !\<approx> term'"
      using terms.    
  next
    show "term_subst.is_imgu \<sigma> {{term, term'}}"
      using \<sigma>(1).
  next
    show "select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<sigma>) (premise \<cdot> \<sigma>) 
       \<or> literal \<in># select premise"
    proof(cases ?select\<^sub>G_empty)
      case select\<^sub>G_empty: True

      then have "max_literal \<cdot>l \<theta> = literal \<cdot>l \<theta>"
        by (simp add: max_literal_literal\<^sub>G literal)
        
      then have literal_\<theta>_is_maximal: "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
        using max_literal(2) by simp
       
      have literal_\<sigma>_in_premise: "literal \<cdot>l \<sigma> \<in># premise \<cdot> \<sigma>"
        by (simp add: literal_in_clause_subst literal_in_premise)

      have "is_maximal\<^sub>l (literal \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
        using is_maximal\<^sub>l_ground_subst_stability'[OF 
                literal_\<sigma>_in_premise 
                premise_grounding[unfolded \<sigma>(2) clause_subst_compose]
                literal_\<theta>_is_maximal[unfolded \<sigma>(2) clause_subst_compose literal_subst_compose]
              ].

     then show ?thesis
       using select select\<^sub>G_empty
       by simp
    next
      case False
      then show ?thesis
        using literal_selected by blast
    qed
  next 
    show "conclusion' \<cdot> \<sigma> = conclusion' \<cdot> \<sigma>" ..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have conclusion'_\<sigma>_\<theta> : "conclusion' \<cdot> \<sigma> \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using conclusion'_\<theta>  
    unfolding clause_subst_compose[symmetric] \<sigma>_\<theta>.
 
  have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings (conclusion' \<cdot> \<sigma>)"
    unfolding clause_groundings_def conclusion'_\<sigma>_\<theta>
    by (smt (verit, ccfv_threshold) conclusion'_\<sigma>_\<theta> conclusion_grounding mem_Collect_eq)

  (* TODO *)
  with equality_resolution show ?thesis
    unfolding clause_groundings_def inference_groundings_def[OF select\<^sub>G] ground.G_Inf_def inferences_def
    using premise_grounding
    apply auto
    by (metis conclusion'_\<sigma>_\<theta> conclusion_grounding ground_eq_resolution)
qed

(* TODO: *)
lemma (in first_order_superposition_calculus) equality_resolution_ground_instance':
  obtains select\<^sub>G where "ground_superposition_calculus.equality_resolution_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
          \<subseteq> ground_instances select\<^sub>G equality_resolution_inferences"
proof-
  assume assumption: 
    "\<And>select\<^sub>G. ground_superposition_calculus.equality_resolution_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
         \<subseteq> ground_instances select\<^sub>G equality_resolution_inferences \<Longrightarrow> thesis"
  
  obtain select\<^sub>G where "is_ground_select select\<^sub>G"
    using select\<^sub>G_simple by blast

  then interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G
    apply unfold_locales.

  have "\<And>premise\<^sub>G conclusion\<^sub>G. ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G \<Longrightarrow>
           \<exists>premise conclusion. equality_resolution premise conclusion \<and>
               Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings select\<^sub>G (Infer [premise] conclusion)"
  proof-
    fix premise\<^sub>G conclusion\<^sub>G
    assume a: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"

    obtain premise \<theta> conclusion where y:
      "premise\<^sub>G = to_ground_clause ((premise :: ('f, 'v) atom clause) \<cdot> \<theta>)" 
      "is_ground_clause (premise \<cdot> \<theta>)"
      "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
      "is_ground_clause (conclusion \<cdot> \<theta>)"
      "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>"
      using select\<^sub>G
      unfolding is_ground_select_def
      by (metis select_subst1 subst_ground_clause to_ground_clause_inverse)
      
    show "\<exists>premise conclusion. equality_resolution premise conclusion 
            \<and> Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings select\<^sub>G (Infer [premise] conclusion)"
      using equality_resolution_ground_instance[OF y(2) y(4) y(5) a[unfolded y(1, 3)]] 
      using y(1) y(3) by fastforce
  qed

  (* TODO *)
  then have "ground.equality_resolution_inferences \<subseteq> ground_instances select\<^sub>G equality_resolution_inferences"
    apply auto
    using inference_groundings_def select\<^sub>G apply blast
    by (smt (verit, del_insts) image_iff in_these_eq mem_Collect_eq)

  then show ?thesis
    using assumption
    by blast
qed

lemma (in first_order_superposition_calculus_with_grounding) equality_factoring_ground_instance:
  assumes 
    premise_grounding [intro]: "is_ground_clause (premise \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>" and
    ground_eq_factoring: 
      "ground.ground_eq_factoring
          (to_ground_clause (premise \<cdot> \<theta>)) 
          (to_ground_clause (conclusion \<cdot> \<theta>))"
    shows "\<exists>conclusion'. equality_factoring premise (conclusion') 
            \<and> Infer [to_ground_clause (premise \<cdot> \<theta>)]  (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> inference_groundings select\<^sub>G (Infer [premise] conclusion')
            \<and> conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   using ground_eq_factoring
proof(cases "to_ground_clause (premise \<cdot> \<theta>)" "to_ground_clause (conclusion \<cdot> \<theta>)" 
      rule: ground.ground_eq_factoring.cases)
  case (ground_eq_factoringI literal\<^sub>G\<^sub>1 literal\<^sub>G\<^sub>2 premise'\<^sub>G term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2 term\<^sub>G\<^sub>3)

  have premise_not_empty: "premise \<noteq> {#}"
    using ground_eq_factoringI(1) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)
  
  have select_empty: "select premise = {#}"
    using ground_eq_factoringI(4) select clause_subst_empty
    by auto
  
  have premise_\<theta>: "premise \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>1 (add_mset literal\<^sub>G\<^sub>2 premise'\<^sub>G))"
    using ground_eq_factoringI(1)
    by (metis premise_grounding to_ground_clause_inverse)
  
  obtain literal\<^sub>1 where literal\<^sub>1_maximal: 
    "is_maximal\<^sub>l literal\<^sub>1 premise" 
    "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  note max_ground_literal = is_maximal_lit_iff_is_maximal\<^sub>l[
      THEN iffD1,
      OF ground_eq_factoringI(5), 
      unfolded ground_eq_factoringI(2) to_ground_clause_inverse[OF premise_grounding]
    ]

  have literal\<^sub>1: "literal\<^sub>1 \<cdot>l \<theta> = to_literal literal\<^sub>G\<^sub>1"
    using 
      unique_maximal_in_ground_clause[OF premise_grounding literal\<^sub>1_maximal(2) max_ground_literal]
      ground_eq_factoringI(2)
    by blast

  then have "\<exists>term\<^sub>1 term\<^sub>1'. literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'"
    unfolding ground_eq_factoringI(2)  
    using to_literal_stable subst_pos_stable is_pos_def[symmetric]
    by (metis uprod_exhaust)
   
  with literal\<^sub>1 obtain term\<^sub>1 term\<^sub>1' where 
    literal\<^sub>1_terms: "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'" and
    term\<^sub>G\<^sub>1_term\<^sub>1: "to_term term\<^sub>G\<^sub>1 = term\<^sub>1 \<cdot>t \<theta>"
    unfolding ground_eq_factoringI(2) to_literal_def to_atom_def subst_literal_def subst_atom_def 
    by force 

  obtain premise'' where premise'': "premise = add_mset literal\<^sub>1 premise''"
    using maximal\<^sub>l_in_clause[OF literal\<^sub>1_maximal(1)]
    by (meson multi_member_split)

  then have premise''_\<theta>: "premise'' \<cdot> \<theta> =  add_mset (to_literal literal\<^sub>G\<^sub>2) (to_clause premise'\<^sub>G)"
    using premise_\<theta> 
    unfolding to_clause_add_mset literal\<^sub>1[symmetric]
    by (simp add: subst_clause_add_mset)

  then obtain literal\<^sub>2 where literal\<^sub>2:
    "literal\<^sub>2 \<cdot>l \<theta> = to_literal literal\<^sub>G\<^sub>2"
    "literal\<^sub>2 \<in># premise''"
    unfolding subst_clause_def
    using msed_map_invR by force

  then have "\<exists>term\<^sub>2 term\<^sub>2'. literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
    unfolding ground_eq_factoringI(3)  
    using to_literal_stable subst_pos_stable is_pos_def[symmetric]
    by (metis uprod_exhaust)
   
  with literal\<^sub>2 obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2_terms: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>G\<^sub>1_term\<^sub>2: "to_term term\<^sub>G\<^sub>1 = term\<^sub>2 \<cdot>t \<theta>"
    unfolding ground_eq_factoringI(3) to_literal_def to_atom_def subst_literal_def subst_atom_def 
    by force
 
  have term\<^sub>1_term\<^sub>2: "term\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<theta>"
    using term\<^sub>G\<^sub>1_term\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>2
    by argo

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1, term\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  have term\<^sub>G\<^sub>2_term\<^sub>1': "to_term term\<^sub>G\<^sub>2 = term\<^sub>1' \<cdot>t \<theta>"
    using literal\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>1 
    unfolding 
      literal\<^sub>1_terms 
      ground_eq_factoringI(2) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto
   
  have term\<^sub>G\<^sub>3_term\<^sub>2': "to_term term\<^sub>G\<^sub>3 = term\<^sub>2' \<cdot>t \<theta>"
    using literal\<^sub>2 term\<^sub>G\<^sub>1_term\<^sub>2
    unfolding 
      literal\<^sub>2_terms 
      ground_eq_factoringI(3) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto

  obtain premise' where premise: "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')" 
    using literal\<^sub>2(2) maximal\<^sub>l_in_clause[OF  literal\<^sub>1_maximal(1)] premise''
    by (metis multi_member_split)

  then have premise'_\<theta>: "premise' \<cdot> \<theta> = to_clause premise'\<^sub>G"
    using premise''_\<theta>  premise''
    unfolding literal\<^sub>2(1)[symmetric]
    by (simp add: subst_clause_add_mset)
  
  let ?conclusion' = "add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise')"

  have equality_factoring: "equality_factoring premise (?conclusion' \<cdot> \<sigma>)"
  proof (rule equality_factoringI)
    show "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')"
      using premise.
  next
    show "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'"
      using literal\<^sub>1_terms.
  next 
    show "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
      using literal\<^sub>2_terms.
  next  
    have literal\<^sub>1_\<sigma>_in_premise: "literal\<^sub>1 \<cdot>l \<sigma> \<in># premise \<cdot> \<sigma>"
      using literal\<^sub>1_maximal(1) literal_in_clause_subst maximal\<^sub>l_in_clause by blast

    have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
    using is_maximal\<^sub>l_ground_subst_stability'[OF 
              literal\<^sub>1_\<sigma>_in_premise 
              premise_grounding[unfolded \<sigma>(2) clause_subst_compose]
              literal\<^sub>1_maximal(2)[unfolded \<sigma>(2) clause_subst_compose literal_subst_compose]
            ].

    then show "select premise = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
      using select_empty by blast
  next
    have term_groundings: "is_ground_term (term\<^sub>1' \<cdot>t \<sigma> \<cdot>t \<tau>)" "is_ground_term (term\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term_subst_compose[symmetric] 
        \<sigma>(2)[symmetric]
        term\<^sub>G\<^sub>1_term\<^sub>1[symmetric] 
        term\<^sub>G\<^sub>2_term\<^sub>1'[symmetric] 
      using ground_term_is_ground
      by simp_all

    have "term\<^sub>1' \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t term\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_eq_factoringI(6)[unfolded 
          less\<^sub>t\<^sub>G_less\<^sub>t 
          term\<^sub>G\<^sub>1_term\<^sub>1 
          term\<^sub>G\<^sub>2_term\<^sub>1'
          \<sigma>(2) 
          term_subst_compose
      ].

    then show "\<not> term\<^sub>1 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
 next 
    show "term_subst.is_imgu \<sigma> {{term\<^sub>1, term\<^sub>2}}"
      using \<sigma>(1).
  next 
    show "?conclusion' \<cdot> \<sigma> = ?conclusion' \<cdot> \<sigma>"
      ..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have "conclusion \<cdot> \<theta> = 
      add_mset (to_term term\<^sub>G\<^sub>2 !\<approx> to_term term\<^sub>G\<^sub>3) 
        (add_mset (to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3) (to_clause premise'\<^sub>G))"
    using ground_eq_factoringI(7) to_ground_clause_inverse[OF conclusion_grounding]
    unfolding to_term_to_atom to_atom_to_literal to_clause_add_mset[symmetric]
    by simp

  then have conclusion_\<theta>: 
    "conclusion \<cdot> \<theta> = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<theta>"
    unfolding 
      term\<^sub>G\<^sub>2_term\<^sub>1'
      term\<^sub>G\<^sub>3_term\<^sub>2'
      term\<^sub>G\<^sub>1_term\<^sub>1
      premise'_\<theta>[symmetric]
      subst_clause_add_mset[symmetric]
      subst_literal[symmetric]
      subst_atom[symmetric]
    by (simp add: add_mset_commute)

  then have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings (?conclusion' \<cdot> \<sigma>)"
    unfolding clause_groundings_def 
    using \<sigma>(2) conclusion_\<theta> conclusion_grounding by auto

  (* TODO *)
  with equality_factoring show ?thesis
    unfolding clause_groundings_def inference_groundings_def[OF select\<^sub>G] ground.G_Inf_def inferences_def
    using premise_grounding
    apply auto
    by (metis (no_types, lifting) \<sigma>_\<theta> clause_subst_compose conclusion_\<theta> conclusion_grounding ground_eq_factoring)
qed

(* TODO: *)
lemma (in first_order_superposition_calculus) equality_factoring_ground_instance':
  obtains select\<^sub>G where "ground_superposition_calculus.equality_factoring_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
          \<subseteq> ground_instances select\<^sub>G equality_factoring_inferences"
      "is_ground_select select\<^sub>G"
proof-
  assume assumption: 
    "\<And>select\<^sub>G. ground_superposition_calculus.equality_factoring_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
         \<subseteq> ground_instances select\<^sub>G equality_factoring_inferences \<Longrightarrow>  is_ground_select select\<^sub>G \<Longrightarrow> thesis"
  
  obtain select\<^sub>G where "is_ground_select select\<^sub>G"
    using select\<^sub>G_simple by blast

  then interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G
    apply unfold_locales.

  have "\<And>premise\<^sub>G conclusion\<^sub>G. ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G \<Longrightarrow>
           \<exists>premise conclusion. equality_factoring premise conclusion \<and>
               Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings select\<^sub>G (Infer [premise] conclusion)"
  proof-
    fix premise\<^sub>G conclusion\<^sub>G
    assume a: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"

    obtain premise \<theta> conclusion where y:
      "premise\<^sub>G = to_ground_clause ((premise :: ('f, 'v) atom clause) \<cdot> \<theta>)" 
      "is_ground_clause (premise \<cdot> \<theta>)"
      "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
      "is_ground_clause (conclusion \<cdot> \<theta>)"
      "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>"
      using select\<^sub>G
      unfolding is_ground_select_def
      by (metis select_subst1 subst_ground_clause to_ground_clause_inverse)
      
    show "\<exists>premise conclusion. equality_factoring premise conclusion 
            \<and> Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings select\<^sub>G (Infer [premise] conclusion)"
      using equality_factoring_ground_instance[OF y(2) y(4) y(5) a[unfolded y(1, 3)]] 
      using y(1) y(3) by fastforce
  qed

  (* TODO *)
  then have "ground.equality_factoring_inferences \<subseteq> ground_instances select\<^sub>G equality_factoring_inferences"
    apply auto
    using inference_groundings_def select\<^sub>G apply blast
    by (smt (verit, del_insts) image_iff in_these_eq mem_Collect_eq)

  then show ?thesis
    using assumption select\<^sub>G
    by blast
qed


definition (in first_order_superposition_calculus_with_grounding) non_redundant_superposition where
  "non_redundant_superposition premise\<^sub>1 \<rho>\<^sub>1 \<theta> \<longleftrightarrow> 
    (\<forall>term\<^sub>G\<^sub>1 context\<^sub>G term\<^sub>G\<^sub>2 \<P>\<^sub>G literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1 term\<^sub>1_with_context.  
        \<P>\<^sub>G \<in> {Pos, Neg} \<longrightarrow> 
        literal\<^sub>G\<^sub>1 = \<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G term\<^sub>G\<^sub>2)\<longrightarrow> 
        term\<^sub>G\<^sub>2 \<prec>\<^sub>t\<^sub>G context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G \<longrightarrow> 
        premise\<^sub>G\<^sub>1 = to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<longrightarrow> 
        \<P>\<^sub>G = Pos \<and> select\<^sub>G premise\<^sub>G\<^sub>1  = {#} \<and> ground.is_strictly_maximal_lit literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1 
         \<or> \<P>\<^sub>G = Neg \<and> (select\<^sub>G premise\<^sub>G\<^sub>1 = {#} \<and> ground.is_maximal_lit literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1 
                        \<or> literal\<^sub>G\<^sub>1 \<in># select\<^sub>G premise\<^sub>G\<^sub>1) \<longrightarrow> 
        term\<^sub>1_with_context \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle> \<longrightarrow>

    (\<exists>context term\<^sub>1.
          term\<^sub>1_with_context = context\<langle>term\<^sub>1\<rangle>
        \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 
        \<and> context \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G 
        \<and> is_Fun term\<^sub>1)
    )"

lemma (in first_order_superposition_calculus_with_grounding) superposition_ground_instance:
  assumes 
    renaming: 
      "term_subst.is_renaming \<rho>\<^sub>1" 
      "term_subst.is_renaming \<rho>\<^sub>2" 
      "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}" and
    premise\<^sub>1_grounding [intro]: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and
    premise\<^sub>2_grounding [intro]: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = (select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = (select premise\<^sub>2) \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>" and
    ground_superposition: 
      "ground.ground_superposition
          (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))
          (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))
          (to_ground_clause (conclusion \<cdot> \<theta>))" and
    not_redundant: "non_redundant_superposition premise\<^sub>1 \<rho>\<^sub>1 \<theta>"
 (* TODO: (Premise order!)  *)
  shows "\<exists>conclusion'. superposition premise\<^sub>1 premise\<^sub>2 (conclusion')
            \<and> Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> inference_groundings select\<^sub>G (Infer [premise\<^sub>1, premise\<^sub>2] conclusion')
            \<and> conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   using ground_superposition
proof(cases 
      "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" 
      "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" 
      "to_ground_clause (conclusion \<cdot> \<theta>)"
      rule: ground.ground_superposition.cases)
  case (ground_superpositionI 
          literal\<^sub>G\<^sub>1
          premise\<^sub>G\<^sub>1'
          literal\<^sub>G\<^sub>2
          premise\<^sub>G\<^sub>2'
          \<P>\<^sub>G
          context\<^sub>G
          term\<^sub>G\<^sub>1
          term\<^sub>G\<^sub>2
          term\<^sub>G\<^sub>3
        )

  have premise\<^sub>1_not_empty: "premise\<^sub>1 \<noteq> {#}"
    using ground_superpositionI(1) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>2_not_empty: "premise\<^sub>2 \<noteq> {#}"
    using ground_superpositionI(2) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>1_\<theta> : "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1')"
    using ground_superpositionI(1)
    by (metis premise\<^sub>1_grounding to_ground_clause_inverse)

   have premise\<^sub>2_\<theta> : "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(2)
    by (metis premise\<^sub>2_grounding to_ground_clause_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)) \<noteq> {#}"

  have pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l: 
    "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<theta>)"
    using ground_superpositionI(9)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  have neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l: 
    "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<theta>)"
    using ground_superpositionI(9)
    unfolding is_maximal_lit_iff_is_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  obtain pos_literal\<^sub>1 where
    "is_strictly_maximal\<^sub>l pos_literal\<^sub>1 premise\<^sub>1"
    "pos_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Pos"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
            premise\<^sub>1_grounding[folded clause_subst_compose] 
            pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
          ]
    by blast

  moreover then have "\<P>\<^sub>G = Pos \<Longrightarrow> pos_literal\<^sub>1 \<in># premise\<^sub>1" 
    using strictly_maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_max_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_max_literal\<^sub>1 premise\<^sub>1"
    "neg_max_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using 
      is_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_not_empty 
        premise\<^sub>1_grounding[folded clause_subst_compose]
      ]
      neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l
    by (metis clause_subst_compose premise\<^sub>1_grounding unique_maximal_in_ground_clause)

  moreover then have "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> neg_max_literal\<^sub>1 \<in># premise\<^sub>1" 
    using maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_selected_literal\<^sub>1 where
    "neg_selected_literal\<^sub>1 \<in># select premise\<^sub>1"
    "neg_selected_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
    using ground_superpositionI(9) select(1)
    by (smt (z3) clause_subst_compose ground_literal_in_ground_clause3 image_iff multiset.set_map 
          subst_clause_def)

  moreover then have "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> neg_selected_literal\<^sub>1 \<in># premise\<^sub>1" 
    by (meson mset_subset_eqD select_subset)

  ultimately obtain literal\<^sub>1 where
   literal\<^sub>1_\<theta>: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" and
   literal\<^sub>1_in_premise\<^sub>1: "literal\<^sub>1 \<in># premise\<^sub>1" and
   literal\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
   literal\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
   literal\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> literal\<^sub>1 \<in># select premise\<^sub>1"
    by (metis ground_superpositionI(9) literals_distinct(1))

  then have literal\<^sub>1_grounding [intro]: "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta>)"
    by simp

  have literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>2) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> \<theta>)"
    using ground_superpositionI(11)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by (simp add: premise\<^sub>2_grounding)

  obtain literal\<^sub>2 where 
    literal\<^sub>2_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>2 premise\<^sub>2" and
    literal\<^sub>2_\<theta>: "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>2"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
            premise\<^sub>2_grounding[folded clause_subst_compose] 
            literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
          ].

  then have literal\<^sub>2_in_premise\<^sub>2: "literal\<^sub>2 \<in># premise\<^sub>2" 
    using strictly_maximal\<^sub>l_in_clause by blast

  have literal\<^sub>2_grounding [intro]: "is_ground_literal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<theta>)"
    using literal\<^sub>2_\<theta> by simp

  obtain premise\<^sub>1' where premise\<^sub>1: "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
    by (meson literal\<^sub>1_in_premise\<^sub>1 multi_member_split)

  then have premise\<^sub>1'_\<theta>: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>1'"
    using premise\<^sub>1_\<theta>  
    unfolding to_clause_add_mset literal\<^sub>1_\<theta>[symmetric]
    by (simp add: subst_clause_add_mset)

  obtain premise\<^sub>2' where premise\<^sub>2: "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
    by (meson literal\<^sub>2_in_premise\<^sub>2 multi_member_split)

  then have premise\<^sub>2'_\<theta>: "premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>2'"
    using premise\<^sub>2_\<theta>  
    unfolding to_clause_add_mset literal\<^sub>2_\<theta>[symmetric]
    by (simp add: subst_clause_add_mset)

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  from literal\<^sub>1_\<theta> have literal\<^sub>1_\<theta>': 
    "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta> = ?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle> (to_term term\<^sub>G\<^sub>2))"
    using ground_superpositionI(4)
    unfolding ground_superpositionI(5)
    by (cases "\<P>\<^sub>G = Pos") 
       (simp_all add: 
          to_atom_to_literal[symmetric] 
          to_term_to_atom[symmetric] 
          ground_term_with_context(3)[symmetric]
        )

  then obtain term\<^sub>1_with_context term\<^sub>1' where 
    literal\<^sub>1: "literal\<^sub>1 = ?\<P> (Upair term\<^sub>1_with_context term\<^sub>1')" and
    term\<^sub>1'_\<theta>: "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>2" and
    term\<^sub>1_with_context_\<theta>: "term\<^sub>1_with_context \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
    using ground_superpositionI(4) 
    by(cases "\<P>\<^sub>G = Pos") (smt (verit, ccfv_SIG) obtain_from_literal_subst)+

  obtain context\<^sub>1 term\<^sub>1 where
    term\<^sub>1_\<theta> : "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and
    context\<^sub>1_\<theta>: "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G" and
    term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>" and
    term\<^sub>1_not_Var: "\<not> is_Var term\<^sub>1"
    using 
      not_redundant[unfolded non_redundant_superposition_def]
      ground_superpositionI(4, 5, 7, 9)
      term\<^sub>1_with_context_\<theta>
    by blast

  from literal\<^sub>2_\<theta> have literal\<^sub>2_\<theta>': 
    "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<theta> = to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3"
    unfolding ground_superpositionI(6) to_term_to_atom to_atom_to_literal(2) literal_subst_compose.

   then obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>2_\<theta>: "term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and     
    term\<^sub>2'_\<theta>: "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>3"
   using obtain_from_pos_literal_subst
   by metis

  have term_term': "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta>"
    unfolding term\<^sub>1_\<theta> term\<^sub>2_\<theta>
    by(rule refl)

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast
  
  let ?conclusion' = "add_mset (?\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"

  have superposition: "superposition premise\<^sub>1 premise\<^sub>2 ?conclusion'"
  proof(rule superpositionI)
    show "term_subst.is_renaming \<rho>\<^sub>1"
      using renaming(1).
  next
    show "term_subst.is_renaming \<rho>\<^sub>2"
      using renaming(2).
  next 
    show "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
     using renaming(3).
  next 
    show "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
      using premise\<^sub>1.
  next
    show "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
      using premise\<^sub>2.
  next
    show  "?\<P> \<in> {Pos, Neg}"
      by simp
  next
    show "literal\<^sub>1 = ?\<P> (Upair context\<^sub>1\<langle>term\<^sub>1\<rangle> term\<^sub>1')"
      unfolding literal\<^sub>1 context\<^sub>1_\<theta> term\<^sub>1_with_context..
  next
    show "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
      using literal\<^sub>2.
  next
    show "is_Fun term\<^sub>1"
      using term\<^sub>1_not_Var.
  next
    show "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
      using \<sigma>(1).
  next
    note premises_to_ground_clause_inverse = assms(4, 5)[THEN to_ground_clause_inverse]  
    note premise_groundings = assms(5, 4)[unfolded \<sigma>(2) clause_subst_compose]
    
    have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma> \<cdot> \<tau> \<prec>\<^sub>c premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>"
      using ground_superpositionI(3)[
        unfolded less\<^sub>c\<^sub>G_less\<^sub>c premises_to_ground_clause_inverse, 
        unfolded \<sigma>(2) clause_subst_compose
        ].

    then show "\<not> premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma>"
      using less\<^sub>c_less_eq\<^sub>c_ground_subst_stability[OF premise_groundings]
      by blast
  next
    show "?\<P> = Pos 
            \<and> select premise\<^sub>1 = {#} 
            \<and> is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>) 
       \<or> ?\<P> = Neg 
            \<and> (select premise\<^sub>1 = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>) 
               \<or> literal\<^sub>1 \<in># select premise\<^sub>1)"
    proof(cases "?\<P> = Pos")
      case True
      moreover then have select_empty: "select premise\<^sub>1 = {#}"
        using clause_subst_empty select(1) ground_superpositionI(9) 
        by(auto simp: subst_clause_def)

      moreover have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>)"
        using True pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
        unfolding literal\<^sub>1_\<theta>[symmetric] \<sigma>(2)
        by force

      moreover then have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>)"
        using 
          is_strictly_maximal\<^sub>l_ground_subst_stability'[OF
            _
            premise\<^sub>1_grounding[unfolded \<sigma>(2) clause_subst_compose]
          ]
          literal_in_clause_subst
          literal\<^sub>1_in_premise\<^sub>1
        by blast
        
      ultimately show ?thesis
        by auto
    next
      case \<P>_not_Pos: False
      then have \<P>\<^sub>G_Neg: "\<P>\<^sub>G = Neg"
        using ground_superpositionI(4)
        by fastforce

      show ?thesis
      proof(cases ?select\<^sub>G_empty)
        case select\<^sub>G_empty: True
    
        then have "select premise\<^sub>1 = {#}"
          using clause_subst_empty select(1) ground_superpositionI(9) \<P>\<^sub>G_Neg
          by auto

        moreover have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>)"
          using neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l[OF \<P>\<^sub>G_Neg select\<^sub>G_empty]
          unfolding literal\<^sub>1_\<theta>[symmetric] \<sigma>(2)
          by simp
          
        moreover then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>)"
          using 
            is_maximal\<^sub>l_ground_subst_stability'[OF 
              _  
              premise\<^sub>1_grounding[unfolded \<sigma>(2) clause_subst_compose]
            ]
            literal_in_clause_subst
            literal\<^sub>1_in_premise\<^sub>1
          by blast

        ultimately show ?thesis
          using \<P>\<^sub>G_Neg
          by simp
      next
        case select\<^sub>G_not_empty: False
        have "literal\<^sub>1 \<in># select premise\<^sub>1"
          using literal\<^sub>1_selected[OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty].
  
        with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis 
          by simp
      qed
    qed
  next
    show "select premise\<^sub>2 = {#}"
      using clause_subst_empty ground_superpositionI(10) select(2)
      by auto
  next 
    have "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma> \<cdot> \<tau>)"
      using literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
      unfolding literal\<^sub>2_\<theta>[symmetric]  \<sigma>(2)
      by simp

    then show "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<sigma>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma>)"
      using 
        is_strictly_maximal\<^sub>l_ground_subst_stability'[OF 
          _  premise\<^sub>2_grounding[unfolded \<sigma>(2) clause_subst_compose]
        ]
        literal\<^sub>2_in_premise\<^sub>2 
        literal_in_clause_subst 
      by blast
  next
    have term_groundings: 
      "is_ground_term (term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      "is_ground_term (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term\<^sub>1_with_context[symmetric]  
        term\<^sub>1_with_context_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>1'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
      using ground_term_with_context_is_ground(1)
      by simp_all

    have "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_superpositionI(7) 
      unfolding 
        term\<^sub>1'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>1_with_context[symmetric]
        term\<^sub>1_with_context_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        less\<^sub>t\<^sub>G_less\<^sub>t
        ground_term_with_context(3).
     
    then show "\<not> context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next
    have term_groundings: 
      "is_ground_term (term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      "is_ground_term (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term\<^sub>2_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>2'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
      by simp_all

    have "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_superpositionI(8) 
      unfolding 
        term\<^sub>2_\<theta>[unfolded \<sigma>(2) term_subst_compose]             
        term\<^sub>2'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        less\<^sub>t\<^sub>G_less\<^sub>t.

    then show "\<not> term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next
    show "?conclusion' = ?conclusion'"..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>1"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>1_grounding)

  moreover have "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>2"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>2_grounding)

  moreover have "conclusion \<cdot> \<theta> = 
    add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
      (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
    unfolding ground_term_with_context(3) to_term_to_atom
    by(cases "\<P>\<^sub>G = Pos")(simp_all add: to_atom_to_literal to_clause_add_mset)

  then have conclusion_\<theta>: "conclusion \<cdot> \<theta> =  ?conclusion' \<cdot> \<theta>"
    unfolding 
      context\<^sub>1_\<theta>[symmetric] 
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
      term\<^sub>2'_\<theta>[symmetric] 
      subst_clause_plus[symmetric] 
      subst_apply_term_ctxt_apply_distrib[symmetric]
      term_subst_atom_subst
    apply(cases "\<P>\<^sub>G = Pos")
    using subst_clause_add_mset subst_literal \<sigma>_\<theta> clause_subst_compose
    by (smt (verit))+
    
  have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings ?conclusion'"
    unfolding clause_groundings_def
    by (smt (verit, best) conclusion_\<theta> conclusion_grounding mem_Collect_eq)

  (* TODO: *)
  ultimately show ?thesis
    unfolding clause_groundings_def inference_groundings_def[OF select\<^sub>G] ground.G_Inf_def inferences_def
    using superposition
    apply simp
    by (metis conclusion_\<theta> conclusion_grounding ground_superposition premise\<^sub>1_grounding premise\<^sub>2_grounding renaming(1) renaming(3))
qed  

(* TODO: Probably it is easier to combine these with the above ones or have a generic way for 
    converting the formats
*)
lemma (in first_order_superposition_calculus_with_grounding) equality_resolution_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.equality_resolution_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))"
    (* TODO: Create definition or abbreviation for this *)
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises"
  shows "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings select\<^sub>G \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in>  \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp
  
  obtain premise conclusion \<theta> where
    "to_clause premise\<^sub>G = premise \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, opaque_lifting) ground_clause_is_ground subst_ground_clause)
    
  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<theta>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    by (smt ground_clause_is_ground to_clause_inverse)+
   
  obtain conclusion' where 
    equality_resolution: "equality_resolution premise conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings select\<^sub>G (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using 
      equality_resolution_ground_instance[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_resolution[unfolded premise\<^sub>G conclusion\<^sub>G]
      ]
    by blast

  let ?\<iota> = "Infer [premise] conclusion'"

  have "?\<iota> \<in> Inf_from premises"
    using premise_in_premises  equality_resolution
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings select\<^sub>G ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)

  ultimately show ?thesis
    by blast
qed 

(* 
    "\<iota>\<^sub>G \<in> ground.equality_resolution_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))"
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises"
*)

lemma (in first_order_superposition_calculus_with_grounding) equality_factoring_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.equality_factoring_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises"
  shows  "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings select\<^sub>G \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in>  \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp
  
  obtain premise conclusion \<theta> where
    "to_clause premise\<^sub>G = premise \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, opaque_lifting) ground_clause_is_ground subst_ground_clause)
    
  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<theta>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    by (smt ground_clause_is_ground to_clause_inverse)+
   
  obtain conclusion' where 
    equality_factoring: "equality_factoring premise conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings select\<^sub>G (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using 
      equality_factoring_ground_instance[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_factoring[unfolded premise\<^sub>G conclusion\<^sub>G]
      ]
    by blast

  let ?\<iota> = "Infer [premise] conclusion'"

  have "?\<iota> \<in> Inf_from premises"
    using premise_in_premises  equality_factoring
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings select\<^sub>G ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)

  ultimately show ?thesis
    by blast
qed

lemma (in first_order_superposition_calculus_with_grounding) xx_superposition: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.superposition_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.Red_I' (\<Union> (clause_groundings ` premises))"
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
      \<and> premise \<in> premises"
   shows  "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings select\<^sub>G \<iota>"
proof-
  obtain premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G\<^sub>2, premise\<^sub>G\<^sub>1] conclusion\<^sub>G" and
    ground_superposition: "ground.ground_superposition premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G"
    using assms(1)
    by blast

  have 
    premise\<^sub>G\<^sub>1_in_groundings: "premise\<^sub>G\<^sub>1 \<in> \<Union> (clause_groundings ` premises)" and  
    premise\<^sub>G\<^sub>2_in_groundings: "premise\<^sub>G\<^sub>2 \<in> \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain premise\<^sub>1 \<rho>\<^sub>1 premise\<^sub>2 \<rho>\<^sub>2 conclusion \<theta> where
    "to_clause premise\<^sub>G\<^sub>1 = premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>" and
    "to_clause premise\<^sub>G\<^sub>2 = premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>" and
    premise\<^sub>1_in_premises: "premise\<^sub>1 \<in> premises" and
    premise\<^sub>2_in_premises: "premise\<^sub>2 \<in> premises"
    using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (smt (z3) ground_clause_is_ground subst_ground_clause)

  then have "non_redundant_superposition premise\<^sub>1 \<rho>\<^sub>1 \<theta>"
    using assms(3)
    unfolding non_redundant_superposition_def ground.Red_I_def
    sorry
    
  thm superposition_ground_instance

  show ?thesis
    sorry
qed

lemma (in first_order_superposition_calculus_with_grounding) ground_instances: 
  assumes 
    "\<iota> \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota> \<notin> ground.Red_I (\<Union> (clause_groundings ` premises))"
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
      \<and> premise \<in> premises"
  shows "\<exists>\<iota>'\<in>Inf_from premises. \<iota> \<in> inference_groundings select\<^sub>G \<iota>'"
proof-
  have "\<iota> \<in> ground.superposition_inferences \<or>
        \<iota> \<in> ground.equality_resolution_inferences \<or>
        \<iota> \<in> ground.equality_factoring_inferences"
    using assms(1)
    unfolding 
      ground.Inf_from_q_def 
      ground.Inf_from_def 
      ground.G_Inf_def 
      inference_system.Inf_from_def
    by auto

  then show ?thesis
    using 
      assms
      equality_resolution_ground_instance'
      equality_factoring_ground_instance'
      xx_superposition
    by presburger
qed

lemma for_all_elements_exists_f_implies_f_exists_for_all_elements: 
  "\<forall>x \<in> X. \<exists>f. P (f x) x \<Longrightarrow> \<exists>f. \<forall>x\<in> X. P (f x) x"
  by meson

lemma (in first_order_superposition_calculus) ground_instances:
  obtains select\<^sub>G where 
    "ground_Inf_overapproximated select\<^sub>G premises"
    "is_ground_select select\<^sub>G"
proof-
  assume assumption: 
    "\<And>select\<^sub>G. ground_Inf_overapproximated select\<^sub>G premises \<Longrightarrow> is_ground_select select\<^sub>G \<Longrightarrow> thesis"

  let ?premise_groundings = "\<Union>(clause_groundings ` premises)"

  have select\<^sub>G_exists_for_premises: "\<forall>premise\<^sub>G \<in> ?premise_groundings. \<exists>select\<^sub>G premise \<theta>. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = to_ground_clause ((select premise) \<cdot> \<theta>)
        \<and> premise \<in> premises"
    unfolding clause_groundings_def   
    by fastforce

  obtain select\<^sub>G_on_premise_groundings where 
    select\<^sub>G_on_premise_groundings: "\<forall>premise\<^sub>G \<in>?premise_groundings. \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> select\<^sub>G_on_premise_groundings (to_ground_clause (premise \<cdot> \<theta>)) = 
          to_ground_clause ((select premise) \<cdot> \<theta>)
      \<and> premise \<in> premises"
    using 
      for_all_elements_exists_f_implies_f_exists_for_all_elements[OF select\<^sub>G_exists_for_premises]
    by (metis (mono_tags, opaque_lifting) to_clause_inverse)
 
  obtain select\<^sub>G where
    select\<^sub>G_def: "\<And>clause\<^sub>G. select\<^sub>G clause\<^sub>G = (
        if clause\<^sub>G  \<in> ?premise_groundings 
        then select\<^sub>G_on_premise_groundings clause\<^sub>G 
        else select\<^sub>G_simple clause\<^sub>G
    )"
    by simp 

  have "is_ground_select select\<^sub>G" 
    unfolding is_ground_select_def select\<^sub>G_def select\<^sub>G_simple_def
    using select\<^sub>G_on_premise_groundings
    by (metis ground_clause_is_ground subst_clause_Var_ident to_clause_inverse)

  then interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G
    apply unfold_locales.

  have "\<forall>premise\<^sub>G \<in>?premise_groundings. \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
      \<and> premise \<in> premises"
    using select\<^sub>G_def select\<^sub>G_on_premise_groundings
    by (metis ground_clause_is_ground select_subst1 to_clause_inverse to_ground_clause_inverse)

  then have "ground_Inf_overapproximated select\<^sub>G premises"
    using ground_instances by auto

  with assumption select\<^sub>G show thesis
    by blast
qed

subsection \<open>Soundness\<close>
 
lemma (in first_order_superposition_calculus) equality_resolution_sound:
  assumes step: "equality_resolution P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: equality_resolution.cases)
  case (equality_resolutionI L P' s\<^sub>1 s\<^sub>2 \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I; 
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L = "to_ground_literal (L \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>2 = "to_ground_term (s\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"

     assume 
       ground_subst: "term_subst.is_ground_subst \<theta>" and 
       refl_I: "refl I" and 
       premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>)"

     have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
       by metis
      
     then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
       by (auto simp: true_cls_def)

     have [simp]: "?P = add_mset ?L ?P'"
       by (simp add: to_ground_clause_def local.equality_resolutionI(1) subst_clause_add_mset)

     have [simp]: "?L = (Neg (Upair ?s\<^sub>1 ?s\<^sub>2))"
       unfolding to_ground_literal_def equality_resolutionI(2) to_ground_atom_def
       by (simp add: subst_atom_def subst_literal)
       
     have [simp]: "?s\<^sub>1 = ?s\<^sub>2"
       using is_imgu_equals[OF equality_resolutionI(3)] by simp
      
     have "is_neg ?L"
       by (simp add: to_ground_literal_def equality_resolutionI(2) subst_literal)

     show "?I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
      proof(cases "L' = ?L")
       case True
   
       then have "?I \<TTurnstile>l (Neg (atm_of ?L))"
         using I_models_L' by simp
  
       moreover have "atm_of L' \<in> ?I"
         using True reflD[OF refl_I, of ?s\<^sub>1] by auto
  
       ultimately show ?thesis
         using True by blast
     next
       case False
       then have "L' \<in># to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
         using L'_in_P by force
  
       then have "L' \<in># to_ground_clause (C \<cdot> \<theta>)"
         unfolding equality_resolutionI.
  
       then show ?thesis
         using I_models_L' by blast
     qed
   qed

  then show ?thesis 
    unfolding true_clss_singleton entails\<^sub>F_def 
    by simp
qed

lemma (in first_order_superposition_calculus) equality_factoring_sound:
  assumes step: "equality_factoring P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: equality_factoring.cases)
  case (equality_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        trans I; 
        sym I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?C = "to_ground_clause (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
       by metis

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    then have s\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?s\<^sub>1"
      using is_imgu_equals[OF equality_factoringI(6)]
      by simp

    have L\<^sub>1: "?L\<^sub>1 = ?s\<^sub>1 \<approx> ?s\<^sub>1'"
      unfolding to_ground_literal_def equality_factoringI(2) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have L\<^sub>2: "?L\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding to_ground_literal_def equality_factoringI(3) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have C: "?C = add_mset (?s\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?s\<^sub>1' ?t\<^sub>2')) ?P')"
      unfolding equality_factoringI 
      by (simp add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_literal
            to_ground_atom_def)

    show "?I \<TTurnstile> ?C"
    proof(cases "L' = ?L\<^sub>1 \<or> L' = ?L\<^sub>2")
      case True
      interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G_simple
        apply unfold_locales
        using select\<^sub>G_simple by blast

      from True have "I \<TTurnstile>l Pos (?s\<^sub>1, ?s\<^sub>1') \<or> I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2')"
        using ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] I_models_L'
        by (metis L\<^sub>1 L\<^sub>2 s\<^sub>1_equals_t\<^sub>2)

      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2') \<or> I \<TTurnstile>l Neg (?s\<^sub>1', ?t\<^sub>2')"
        by (meson transD trans_I true_lit_simps(1) true_lit_simps(2))

      then have "?I \<TTurnstile>l ?s\<^sub>1 \<approx> ?t\<^sub>2' \<or> ?I \<TTurnstile>l Neg (Upair ?s\<^sub>1' ?t\<^sub>2')"
        unfolding ground.true_lit_uprod_iff_true_lit_prod[OF sym_I].

      then show ?thesis
        unfolding C
        by (metis true_cls_add_mset)
    next
      case False
      then have "L' \<in># ?P'"
        using L'_in_P
        unfolding equality_factoringI
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "L' \<in># to_ground_clause (C \<cdot> \<theta>)"
        by (simp add: to_ground_clause_def equality_factoringI(7) subst_clause_add_mset)

      then show ?thesis
        using I_models_L' by blast
    qed
  qed

  then show ?thesis
    unfolding true_clss_singleton entails\<^sub>F_def 
    by simp
qed

lemma (in first_order_superposition_calculus) superposition_sound:
  assumes step: "superposition P1 P2 C"
  shows "{P1, P2} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I;
        trans I; 
        sym I;
        compatible_with_gctxt I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P1 \<cdot> \<sigma>);
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P2 \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof -
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    let ?P1 = "to_ground_clause (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P2 = "to_ground_clause (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"

    let ?P\<^sub>1' = "to_ground_clause (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P\<^sub>2' = "to_ground_clause (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?s\<^sub>1 = "to_ground_context (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?u\<^sub>1 = "to_ground_term (u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"

    let ?\<P> = "if \<P> = Pos then Pos else Neg"

    let ?C = "to_ground_clause (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      refl_I: "refl I" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      premise1: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P1 \<cdot> \<sigma>)" and
      premise2: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P2 \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P1"
      using 
         premise1[rule_format, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
      by metis

    moreover have "?I \<TTurnstile> ?P2"
      using 
         premise2[rule_format, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
      by metis

    ultimately obtain L\<^sub>1' L\<^sub>2' 
      where
        L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P1" and 
        I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
        L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P2" and 
        I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
      by (auto simp: true_cls_def)

    have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
      using is_imgu_equals[OF superpositionI(10)]
      by simp

    have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by blast

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by blast
      
    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(6) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      unfolding superpositionI to_ground_literal_def to_ground_atom_def
      by (smt (verit, ccfv_threshold) ground_atom_in_ground_literal2(1) literal.simps(10) map_uprod_simps s\<^sub>1_u\<^sub>1 subst_apply_term_ctxt_apply_distrib subst_atom subst_literal(1) subst_literal(2) to_ground_atom_def to_ground_literal_def)
      (* Slow:  by(auto simp: subst_atom_def subst_literal s\<^sub>1_u\<^sub>1) *)
    
    have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding s\<^sub>1_t\<^sub>2' superpositionI
      apply(cases "\<P> = Pos")
      by (simp_all add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_clause_plus 
              subst_literal to_ground_atom_def)

    show "?I \<TTurnstile> ?C"
    proof (cases "L\<^sub>1' = ?L\<^sub>1")
      case L\<^sub>1'_def: True
      then have "?I \<TTurnstile>l ?L\<^sub>1"
        using superpositionI
        using I_models_L\<^sub>1' by blast

      show ?thesis
      proof (cases "L\<^sub>2' = ?L\<^sub>2")
        case L\<^sub>2'_def: True
        interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G_simple
        apply unfold_locales
        using select\<^sub>G_simple by blast

        from L\<^sub>2'_def have ts_in_I: "(?t\<^sub>2, ?t\<^sub>2') \<in> I"
          using I_models_L\<^sub>2' ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] superpositionI(8)
          unfolding to_ground_literal_def to_ground_atom_def 
          by (smt (verit) literal.simps(9) map_uprod_simps subst_atom_def subst_literal true_lit_simps(1)) 

        have ?thesis if "\<P> = Pos"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, best) true_lit_simps(1))

          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using ts_in_I compatible_with_ground_context_I refl_I sym_I trans_I
            by (meson compatible_with_gctxtD refl_onD1 symD trans_onD)
          
          then have "?I \<TTurnstile>l ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  \<approx> ?s\<^sub>1'"
            by blast

          then show ?thesis 
            unfolding C that
            by (smt (verit) true_cls_add_mset)
        qed

        moreover have ?thesis if "\<P> = Neg"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, ccfv_threshold) literals_distinct(2) true_lit_simps(2))
        
          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using ts_in_I compatible_with_ground_context_I trans_I
            by (meson compatible_with_gctxtD transD)

          then have "?I \<TTurnstile>l Neg (Upair ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  ?s\<^sub>1')"
            by (meson ground.true_lit_uprod_iff_true_lit_prod(2) sym_I true_lit_simps(2))

          then show ?thesis 
            unfolding C that
            by (smt (verit, best) literals_distinct(1) true_cls_add_mset)
        qed

        ultimately show ?thesis
          using \<P>_pos_or_neg by blast
      next
        case False
        then have "L\<^sub>2' \<in># ?P\<^sub>2'"
          using L\<^sub>2'_in_P2
          unfolding superpositionI
          by (simp add: to_ground_clause_def subst_clause_add_mset)

        then have "?I \<TTurnstile> ?P\<^sub>2'"
          using I_models_L\<^sub>2' by blast

        then show ?thesis
          unfolding superpositionI
          by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
      qed
    next
      case False
      then have "L\<^sub>1' \<in># ?P\<^sub>1'"
        using L\<^sub>1'_in_P1
        unfolding superpositionI 
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "?I \<TTurnstile> ?P\<^sub>1'"
        using I_models_L\<^sub>1' by blast

      then show ?thesis 
        unfolding superpositionI
        by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
    qed
  qed

  then show ?thesis 
    unfolding true_clss_singleton true_clss_insert entails\<^sub>F_def
    by simp
qed


sublocale first_order_superposition_calculus \<subseteq> sound_inference_system inferences "{{#}}" "(\<TTurnstile>\<^sub>F)"
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> inferences \<Longrightarrow> set (prems_of \<iota>) \<TTurnstile>\<^sub>F {concl_of \<iota>}"
    using 
      inferences_def 
      equality_factoring_sound
      equality_resolution_sound
      superposition_sound
      entails\<^sub>F_def
    by auto
next 
  show "\<bottom>\<^sub>F \<noteq> {}"
    by simp
next 
  have "\<And>\<theta> I. 
    term_subst.is_ground_subst \<theta> \<Longrightarrow> 
    (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause ({#} \<cdot> \<theta>) \<Longrightarrow> False"
    by (metis to_clause_empty_mset to_clause_inverse image_mset_is_empty_iff subst_clause_def 
          true_cls_empty)

  then show "\<And>B N1. B \<in> \<bottom>\<^sub>F \<Longrightarrow> {B} \<TTurnstile>\<^sub>F N1"
    unfolding true_clss_singleton entails\<^sub>F_def
    by fastforce
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> N1 \<TTurnstile>\<^sub>F N2"
    by (auto simp: entails\<^sub>F_def elim!: true_clss_mono[rotated])
next
  show "\<And>N2 N1. \<forall>C\<in>N2. N1 \<TTurnstile>\<^sub>F {C} \<Longrightarrow> N1 \<TTurnstile>\<^sub>F N2"
    unfolding entails\<^sub>F_def
    by blast
next
  show "\<And>N1 N2 N3. \<lbrakk>N1 \<TTurnstile>\<^sub>F N2; N2 \<TTurnstile>\<^sub>F N3\<rbrakk> \<Longrightarrow> N1 \<TTurnstile>\<^sub>F N3 "
    using entails\<^sub>F_def 
    by (smt (verit, best))
qed

sublocale first_order_superposition_calculus \<subseteq> statically_complete_calculus "\<bottom>\<^sub>F" inferences entails_\<G> Red_I_\<G> Red_F_\<G>
  unfolding static_empty_ord_inter_equiv_static_inter
proof(rule stat_ref_comp_to_non_ground_fam_inter)
  (* TODO *)
  show "\<forall>q\<in>select\<^sub>G\<^sub>s.
       statically_complete_calculus {{#}} (ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G) q) ground_superposition_calculus.G_entails
        (calculus_with_finitary_standard_redundancy.Red_I (ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G) q)
          ground_superposition_calculus.G_entails (multp (ground_superposition_calculus.less_lit (\<prec>\<^sub>t\<^sub>G))))
        (finitary_standard_formula_redundancy.Red_F ground_superposition_calculus.G_entails
          (multp (ground_superposition_calculus.less_lit (\<prec>\<^sub>t\<^sub>G))))"
  proof
    fix select\<^sub>G
    assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    then interpret first_order_superposition_calculus_with_grounding _ _ _ select\<^sub>G
      apply unfold_locales
      unfolding select\<^sub>G\<^sub>s_def
      by simp

    show "statically_complete_calculus 
            ground.G_Bot 
            ground.G_Inf 
            ground.G_entails 
            ground.Red_I 
            ground.Red_F"
      using ground.statically_complete_calculus_axioms by blast
  qed
next
  show "\<And>N. empty_ord.saturated N \<Longrightarrow> \<exists>q \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated q N"
    using ground_instances
    by (smt (verit, ccfv_threshold) mem_Collect_eq select\<^sub>G\<^sub>s_def)
qed 

end
